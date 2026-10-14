-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1831
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:53.873666+00:00
-- url     : https://prove2.me/submissions/1295ca07-dede-414a-8a5b-5799deb38937

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 329136690 ≤ n < 329316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 329137940 1250 329136690 329136733
    0x9100506120903190f1b0206040302060c0f030a030207031403190f0204081005010905130f0215090d06050906060a0f05090408091203091801060503070c030e0301061d07050a02 77
    0xb440c01c190381c240072800201d03c00c59019420058005559010110151604640300c40802600c4c1c141c0d840b07a02c4c0c10766010a41d075206502020740301c0c1c0343c08109040d00e03540c10400c40c80200c1c8038a080d60f817a00b04040d0050040e4100c990224041181a09103211403803064058a100b1600000741106c01010408098001c2c5000c203621800160200004280c5c15010040300c8050200408000b909614107000c0342c0450760b002c0c018441e00c60005000304042159070b1040c02e0802d8040303844c21882130001e00c0c00145445081c0d505500f10034040050024840342d90f0260384509500300c140c621580d100c0040000400309401440a1255002018821818040e444503802803143c5803003841e11030b0782c000007030307817040051819010f90780005154401424042d40b031252240180c80e0040065050000141c114007005205608200ca000754035403d06101d2141c444c280349c0d003d40200320150300c86c60714600e44401a240401c841d5071460120383c02c0f621500450340b8442c481d601400540b540018644003201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 329139190 1250 329137940 329137951
    0x50a060507030e12072001050a031a120303180d1d180f15010507030f0f0306030c060908060c09090115140d050603010f09150b030102070501020a0c020910050612 71
    0x1580e074222001400b10801580c441131144441258440c425841c00c42c10700795802e500c91300203000014101d89917036045801e0b10500d84c414180810040411320748040000070703080d202c5612541090039140510004002140260f02d40c1c0c80042d11080c011610f030f680c50544041400c00181c000c00001d0741840342032041180000000d141008040c1d42082803040030809580d101d1018403103500b0b11807031100303000440d900340e2002e007406402c1883c16100502001c201c10a22001e010510380b003404024869030004001d0740e40003a601d20f1643d210030f00109105428011501144103ca000c215400b080005a803c4041c00404040030340c0e003010249440140150380250074016046124000c64000c0710142032038810001e0000341e2450000704050a451403100101c021a140200c2800807c1818507041d803810014100801c2c2d402c81c0703501180c0240315510001d0082c0d440031038204015a4000c000080082c000c03544680280c40341c00070800031034994802c180d80841d007001085600c15282d4540355120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 329140440 1250 329139190 329139197
    0x10b09040c1e03020415080c04170a020d060b0301060603020c060414031b0d1b0b0703021e03132904021519090e010f081e010b0319060b010c050a060507 67
    0x10b0840310340101e8020000008400b10f50045403c2c484501a201005c00201040c03400e2803c0342402c051040d407620840c0510035a64a44081c0b80039890407c1010610705540a84a05400c00d040e0a11000914004490724800d5080c00070000349540f0074025a203c1e44c250201400a548503643c42300300c1d4485d031940c1071225003c01d100f100e1808060b24004600e0740d00b032030054040c690581c0001032170344909020342c11030080007803116004503804403104c07a44042d10742001a134805204000320181d40e1201d500300000d072000810000e402d2084501c0d030403168400c555844222506c00c0030304004000310070352464411a56070000d4094500340c0c03110381585140c4e41607140303004041000042c0000c0741105200c00300d086105c0c200b040c6a244110301d401481003441100b2204d00b403482e50f0b03072a00c1202c0b84080c100c00424510142d850360070350140d40395070001000c0f2082e07519038406441240c0a000b100382c075070a01e0700043c072607036502800c00c0c5d00c0703015800b030041c0c60301400c10366411006000191541e01017 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 329141690 1250 329140440 329140457
    0x507050f010314100303090509190c180f050405090d1710050d120806121203042118060c0f02040207050f03041d09070509040201142a0105060306010b09040c 69
    0x43c058010a0310380240340302c00040006030b0550902800326001c80d4041c50241c09094104850450a13040030207003000d079064007003424a03101c40c003210f01c2020000d8100d041400010002000440210000201c82c0142d40134401130740c1c1c10800d0344c3c461100c0c0e010080414840c1580c2040c10540b0000c0c0796018041d00c0c003500d00b00b500c0c0d0021410a4034000070440300f9000240d640c0c41c01030741000d1a83e91020701164816100100303140825120304c25107469806825001c40400c0c100040019102c10000048550000e031040aa90080c01e01200303c40311070941e44050b501040d041d02c182034584034243c01444540700b200340c59003800000e40c0054002d8542d80105404054819414802440180b140002a03c09001d804100a10398040a02414025845104100143c0e103603200b5065002d902402c20a84204108001c07442c40e03c114845840f000d43c0c4010301c00d01008501400c14107146404000304919503070785041c0b40c1e40f008203000780c480110090000c0c040c1c03032406411010311200c079803408401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 329142940 1250 329141690 329141711
    0x4031707021c050309010b0f06040521011505101d0108090f010c0f0306080303013c03080d0509062406041806090b01080f130f0b09010c0210090507050f0103 69
    0x200315030b003080418002440081405000c5000b4082c44561142c1150010790b603150b0381002030102c1c4280d215150140c26540350030680011410b256003c25034403007009102410045c0354420560925004141c8a0000380081d108402d2007a101c0d0200d0303452494640c90a0b90841005403060f40008000840a21a0030f51007050880300380220810550151640900380120060140540300150000034607584144010001c1f142c03450f0225000180144d08559006ca104180784c0c0c0380000a001c603aa07194898130004200401d00005003040c40c58a8800c000b1501c2c0c2c002c285495a0003a00c020900000c8100840400e5801306410170345041d006089900d807980d500020740c080c141d12032030b200d690750b0b44d80c40030401420613003c0e00980120074030b00030940349481e5110100a00380a03007000140c50744126141e08001d0b4908003000c810360849040c0c4400c1c6003604505000c0c00350f50500c000140030b105420000b420040c000d044184c1c1d031020140c11031030300301b1040c06000c000050070b0300d04042e2103031038215 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 329144190 1250 329142940 329142973
    0x60518132613210c1a040305070602100f0504020f0f19091a0102010c0c032303010b0c070f0b1209030d0504200904030905040207030908030316090e0403170702 70
    0x1402d9014030104803501460480040000c6914811050749000075514041c002010032515000b41d921402261203a1340c40d00440c45038502598100a0591261075030120f0001c0c2c0004a605840026110500410040d0059602654429980203400040241c1040c013a840d06c07201110200c0406031409402e442d007000d816611610342c1d4401d01ca560784e101c2c00344113100c0c0e1000c040c0140340c0007030009001003280b800c4014105101600082c04201c80c0e00e03101c591031480030081c01100e40e80083e84a48958507070200d440b056200760b014084d1481010340024103200341080160848007070492890810036081c40420030300c03400400c0d80055010030010b00c0380000131440307098026030150801520b075100f07202802d02500a040400c034843c0705e0080411002a500014000954405480241c1c0300c2c0e0b442d1031b0584100050b41c000c3c2100303000100404c05181d010703102a0840c07400030390750a08259900c50f6800151202941c1c0074001610700500719019090b02115190001264412941040560604030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 329145440 1250 329144190 329144197
    0x2370b072109020909210c0709060b04090b0a080d0c080423010809160501141201030b19020405062d0301032906010f0f0309060204090605181326 64
    0x8100c400ea40e030b00d0400950600c44100c0d907101d001e10340107004076400d4200e4514000c030f40f42207070040c1c0240042c4c8031080703a000f07200b0000200f08510007031041d103840712070100d0203400500642e54810b1410805440070326008001600729030410b0098204c400c04507100f00c03840c0c031804038152882c071003c0000040c00d040e26042062600800c00e58a1299400e10300018000c0c04090021449540b144005070380d40b00c0a101c1d103c0442d102400d00003034102c40208601e0050288103c003803640a01d0070000028004c107e005103204102e000030390520919240e600350b04902a40c000d60703401800510450040d40c0e03003008281070742d1071411480140000040c2c03000f00c1503030003608102e813001c2e25922030721211b00410321414003211040c844441d1901d0041e00003000f0100b040907110400c560704486046170ba010b039008800a6400000541d86c0c1e90716040f0740d01c0641070394481c090248010b01d0984002c0d10018050900584031019416030340386003621112103000c440080504042e0414040a1b100b46041e0000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 329146690 1250 329145440 329145497
    0x40501050a050f28060308030f04020103110a050403060518120a020c0d050d0309060605031605030d0c080f3414030a140c01060f0602370b07 62
    0x840c262400204080c1a1503025000700907141c2d0f010b0038042802c1320b103120744464803400035001a8141204440201030280b5034005032806100005001d1448060701c8842c4c4524001e0f03c0600c042001c1140c00b1225120307001c1c502d400200d050006100190039608100d402001c014410112001b4203108641410100011410261000a0361014240c1c06000070313411000211001d000118003070b102c05460b00441031400040664612400c801c00049078455009010701404441c001540340510180041c0b0f14082c0f544240b0844200440c074038031034602008050392000100d4200210b0044d0844242c10801c0003000040741c00817013041c1003401d6010300030042d0303a103003002040010754103041e0381340b00d0822201c9105400030071902822540011100882a010008540d03455421212103401403400340c0048600000305040000d0312039000801c043c81030b94010038250f00354001c0007421150800d42c5450350a8104a0340800c0115003541013096019400e820300074401001c1014041448124109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 329147940 1250 329146690 329146693
    0x160c0501090b091005100b0906030405101a010801090608030403020d1518060e010507021f09020a09140c090a05040b0310050a06360e070f090515010e0109030809010c0b0405 76
    0x421501c4d03210603001d6a0b0700803000c00854100d0300e00b0007207d07951922440001d680600c40010119041004c200603081450031010030800c600e808100490850720364001210340000d03014000442e100303100313206140c112104e403002580360514580c28884c1d03400341c544043c0c8200c95503907411201c044c4c1034010410030440755142041c61006618180c0700300c51204218421aa14250402072074a40000d40301e0360003924014104510388144062101500c0c040750001d410040d42c03500001c0020240d045046d000041d02d1525525581e190003000041c0245020164002c1c21854104003d0410b98003c420b01000642540c030f2903803001c0d0802c0291401522480d0a00742d403090308000030182429090103412000c214943c21900c18961240c10a21600380c00b01d071a0364461802148840c200800c00080c51800409521507550300751b0b00000300000c803458081d0a841078038040d210340c481c1e1410094801c0503104c0002682c2141c981502c15005a542d4905010f81207542c3c1c0d0104a07940c1032644120b1180c2c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 329149190 1250 329147940 329147953
    0xc010f0507140c06061302041d07020c010c08070206030736050102150c0c0106030f140606060705100b040b06040b07120c08041503140a0e0c09160c0501090b09 70
    0xd00180314400d0445900b0210398284601d5a03800c03404500680c2100c412540610b160745864000c034000c0c407581d4400d0304c140d040d00102c080700004072003000c4c0c032501d4035800703484c462001480192894905100c0c014400c45003044014014607149018540024031403424541c01b0000156079021b10000400a001801d010348002072440c862803801e00241000f03102610f44194542c09025055402038031050301507102040003170a903a02540720800460308120204908c40080c1804040c1d4048038915181e41d0161000049090406030b0440d180f10303030b0080003410001440400c03580100741321096198065141c00c9110825515200034002420000c064969280c05519002d80505580c480107028000351030700000101c1c80c0302c01544c00b02d0310f040c071229205131401d0380300314014224408003091400540c0140207403843ca9501c0a001c0d03040c21022a5070200300c100c100070191104841130301e240700c0b0002050119610a5138628807003841080082480680e03603407114910031301141c0e5001a5072101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 329150440 1250 329149190 329149201
    0x60f0611070603062108070c0b1c0504110108040c0b0a210e03041a090409060501081b2112030f0f130f02210a050c1002010605090610050c010f05 64
    0x1d0028070000c086a003002c000042c90110414104031140c0e1106046009100d4400c0a0111401c00c803141540c3c4108103480d01d54541c0d0340c034581c42e0044070494003821810031f120002503126108007030155802007a0060382514450044030b070004020700448181140e16000900c1c0750707c0d0710180c03c0204403600e8046441d082c40302c0041144003080c0040d136a41c0d00348101c9882c103e00120840e0280d5142c020030400b1052103040303010b03051042c10103085c0c03c1840d01c0c0d1a0303028041242e020905a414400c1070302c088002c208001c641c011400c0001d16400000d072000d0040344552100040c2e51007152200352070000805011000325904226010b45981c81400100b1441d51800c448040c0e10100a0340ea43c4045056901ca01c64200b90411f0000d008001300c846415145001d144d4201c8505402d008482490905281058407016a215003e006081c48000d9840c081d0040c0144419a1304c0a00b0000159944108003c901c05407141a1410721408004800a008083c0115070454034003440210f10780c03d01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 329151690 1250 329150440 329150443
    0x504050606190f060f1b1115090a0504050720060105011707141602031f0b0f03030f0f16060506030d03020f0d0e010f02120609060d03050a12060f0611 66
    0x21080034044120b550030b0900c0940025000c5034140c40c01898807842284070850305503180c281c101c0400d0720f0846240c10740002c20000c0c501d0307102c0d6000c05840000c528070030500c1e44a02c1707008099070710780d01c40c2591600b449182045d51200f42d2111f01490101e980041441d440904a0000c0c081b030f002c00c0e04840014020b03940c108000411042140080400328504040e00500400002d210240320200001c1c40802d0001012518000c4580003410755041091060303061a9810301200600c02e25030411046105d2840d045050500e0014007402461410300700542c5040254040703441681000c80c2404006140b425070580031300c48a104400c001110f00781407042600d024404004242018010044035070303003803c004103441000c1039070500030410041c8046158007501072400d81c0a210751000c6400411003500182c828040c900039031380300205450b8041444100c500e070701c00c05401b2507010403e0001c070310310507910500004014100000c00e41d4079900030440c1c5080d10b44c0000002914400c0502201a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 329152940 1250 329151690 329151709
    0x1303093302030a1b030e0603070f020d02010510030f081210030c0b181e1201020a08100803070b07030e030d0f0c11061303020304030804060f0f03050405210d0504050606 74
    0xd15000550800100b9034000b0031000c4407004468030b40040080000030140101124561840014442c0740c4034a08000c00034100c0082e80c0c08100144200b02d030280030f050042c4074540c01006010003489200e03080d034440131803080041340c003140c400300100074a207100034008903401d015440f044100c1c8040c514504200d1a400c00d2504205840c80d001c11440a4405166050745103039401a5584200c0281c080000c29151040d1032001d608404840c0030b4030300c86207042d801800c2c1801107495000e0191070b544d824003041041800303803031030582c400c001d29800b107503644805035032000c40d0340303004141090454800c03800d40e00800c10b40c0664907110000580c500d6564080d1800300d9149182c1010b00042046a0642d0f44a02034400c41c242070640b8220020b143c420303c03c540181d40c0060015503140d03942c920041015600b600e120002900d000c02c0d41503501d00c01d0041c6805070303401074001c1550818a0100100e00c161111200c3c00902041150106050040c0a4584600d002c0d001400c6503240248c1804007500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 329154190 1250 329152940 329153039
    0x60612200f04061713060c020c0301050c040f0b0c0307030503060a120b0a0f15270603050609060c0f0d050c222301050d020310080a080418020c06130309 67
    0x2420b41c03081000e402008064103e45030b800ca000407c0900303090310140d051480d4a0085605075081200300b081e1030440c000100f0441300d5918030059910703504c0301580300c240101c10340d03405160810403e03c00032a200700051a00600c0040141400681d0b6400c02059561003410469041e2503010400064400904c512042003540b03080034004840581030039000d1842502440c11a00a034061201c90043c41c1800440d0034a8403120801809480341480e50fa140400c49110420384500c200081500759681d00340c84455000704c0c140e42c04d05c080341644030043d2000070070b074a140c60b0007032041403031190b086c111b211460078203a5020700d0f2150030107400d105201d03032945008524201e15400c5c480035036845812100120094000162a500c400c080b0068038021580aa03129203c0d480440091107046002003080303c160828240d8a059803090b500c00380d0144140c29812504104c0c00502204036942a0b515250310901d0000d1409490b580350119001c2d80726580401c032005107041c030042400e261030005484 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 329155440 1250 329154190 329154227
    0x40e090c0a18050919060501080105090a030c060c0e28210f02040f020a120c0206070801050d050a0b13050c0604120807151107021003060612200f0406 66
    0x100d050501240202e074622a6110406564030001640c2c03000034403200f005014078001402511946003040d42c080d000030b0003001601d510302008104048800110030780b585034551511000400203885540083c014000c0d030b0f0040c4181c15451a550342d881c3c690701a0543c4421052000b3380f4042080d19120803441d1704480d02404048410a51500703050368402e0b0100d910001e110612241440814050b002a0803920411800450103102d0a03401507404404030003220b90420002e854490704070ba44000039122540030510000c01401142026440a40c04500840c00c413071000c1025620300d2002c0800b143d02e1402e121541d814441004014004078400040c1110001e0034039040c2034040c0000340c41840002c04100000030213408103c034480c586032016140c02746c200000c9401d0142c01d40290300c446030403449909605c0b45034031468060711640c02034500550f04c02045082c00303140d000040c031030074240c804005000712a460740b440035480100100c011025645440c2c5143c280b01400d02482103500d410070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 329156690 1250 329155440 329155459
    0x31204030b0610141c06090b1c0c031709032e0e0d0f02070e0c030403030e01150603050c0903010525020d2106030f2423060f0303040e090c 61
    0x3d60051191110244c015504c5607901c1d000e06503085814600614000036900b04040085c10007010751001c80d601c07400341c40c074044042004142c804810003828008000041000d401e0002c03482000b00380c0344040b0718100440c03a1402e02d200083c40c000c40d01c03003011001070315121400700301d0f10180914941c1c141c00b01018020211150343e142d8407240d01c00a660204a11840c003480014401c104ca00d008001c01c0d00340d031072241421a500b00043e0b208980940c0802e080c92809242224140b041d00c1c0000c0b44034401b184030509104d030840140c10041d02c4280900b009016094182d6001c0c40b0b07603402444111810180e0b8000b516440d29003100001c6800b0940d0095508445507640001c045540d207080e01130b02ca10046442860b4100500168001404180d0004450800c00c1840552403108001c03040d0301d140c440c44450142000d8506d12812500e50fa20440300d1585058101c41c8a1a08410001e00d081a0040f180340480e2841c4c1055012623100c5800c502480071508080c00364520009064650814 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 329157940 1250 329156690 329156719
    0x30a02100203040f0b0f06130c0903060c05040e0903032401051611040c090306050c0307020a120c06060b1c06060c0f020f031213060f1b0c1701090303110306150a030902031204030b06 80
    0x500700342f1024120f55141c01141c03100d54850340803034000d08110401042142031001086949030000c85d808030402d08000045180013070800040c0800540580d183c40c90400509072502d042c031110321048981011103100c1c100070b5980d40c0500b6041408907030b94040303070510b1410114250b44014010fa40c8845040081c03112060f03001c80c441c00303c0f0380c018a480640050700c1c6002c45612581205c0075141c04d00d0b00c0c4001ca41380820070000d014000004000404008164043c507044458511892020914101010000500450301c85a4090005160406010384140800c0c203009500310310402d14000020904028181540040301030643c5180a4040b0003001401410650003101c0b010003032101e1040544c02c200c2c148000358080c00d28a071007680c5030f60250800038060a440307001200801c1c1000d00308001e2940d0402070300d08c00e0300c0c0109a032802c40607000d00e2405507413081082c00304052300d40c151800507840401099000070320f9900c07183e641c0c5144d82816648000c000c1c0ca09031007203414214204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 329159190 1250 329157940 329157947
    0x30408030705070503070c0609151418030c0a06030501051504050d02060c01090611040812191b1205031602013b070b03011502030a02100203040f0b0f06130c 69
    0x390301c2655801c0c420f070b03030782c00c1810000d16501560000401c50302280c6400304103190312407444011940801c000c000104903411003642c05e81e070380c8042c10320301100074080c84860401642041841711005016201035002c0d103070104605040c0c903009440440c2e16503004120604000d002c104040c1480c022441c10a428000000d007612010715029101e00c0c1d0202c4c129001034006c3d4410701540d0f42c00b0204018101902c443c0e400c1c103401a20404416008424000c40c051a444c42200c110a88140d4000c00c3c40f259024251082030080d492519003000c0c0b0041540000c2c0c0c0a00003148058198440c10340300d180c50b81c0440c894030034003210181107904000d01c103149480d503401d45000c01d150ba96440c0030105440f030141c0e0681c0380c424030111011702c41e010000a441c07036003800450582e458071007004a44190402c0c00e0341d0303a2040001ca000141c1c00303c0450383d07000303401d40d015680292240c14a89844041d03500c540d4403407081552054192034082e018810ba903e0550301140751704107a00b600b805460001c3c84040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 329160440 1250 329159190 329159197
    0x5100f05121504020c0a060c022d1e0c150c0a021216090e0c01140d0903030b06190201240b070203031603021c1b03030b0a05030f21030408 61
    0x1040030001460114601c01e02d40200b4000c10103010344115169141554a103035100030848040d07074001e1070040c000b950796101003403000740316101380c010880d011191b1010704614981082e1000c0b0a00400464022800582070b04102001d03007403000340042c0000001300047c08600090600d0741d5142001f031480054004038410020540450b0780b124103401c582059420000122402000c441105c1070100c2d00c02c60035440341401c8070604086820820002c0015106240d002c02d450f240020188904480076419411214000c1d11038540460443d40e07000c00300d403440e0030140169005c0b402125480c50100d5092003500c804540d00c3c202a00301e2606c1c00752040500c2a0b40c012544000301c005050070541d14100110340c0000b00551000588540c9070500a44802e00c10340d00040842c03a01d0210740d011803043c00380c0422140180c2190703c644c134bc00c0c1c1d07056004000c000811904805c3d10741c1b00040994043c00050f03500c3c01444050928070122071100e0010052001006802c10740c24001d10010039590b0040c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 329161690 1250 329160440 329160457
    0x21180610140414010605040f0b0702060438070201120b0f040903030605091008060711120315030f030a02070b0313030f0903060501090b0a0503061504050c0702030a0c05100f05 77
    0x1007041035a500300c041406451403d07044409600e0350000019199071060082040316543d40d0b52041450300e03685071201034404e42c03d0280d40a0790a010921440140b105002d10303965100c0710001c2e0b00c0e2008002c0300c00344a48032152601f840740114505003036580107510040000640740f4108015603040000440c103050122180e4025a925060042014020350207400a010300501c40c1610b072621440c01c124040103405921400e001da0004a20000c0c0103c0510706000d10030342c05442e940840c03074181c05050300020721101555055410304442e54501340f20b04803410139107401541da42c0c00340c4080070307190224580c0000a0900d0400030044884107940b0b0300861581d15103003000c0316003840d20741102c07450020b41014200614040000918a4591340131011340300d0203403104240a99107104064491600b112001e4004180611034404d5140507400341d035018003107c81070303410702c40d06070007191034202d100f80e0840d0f6590301910140400d11705200f440c00705010610300182016202c00c0c0017020360081c4c032030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 329162940 1250 329161690 329161709
    0xf0e0d021c090e09070303030e0d0f0c0c0e0a1401050f010c060f1b11010501060e090f0402010203160b0109060f05100f2318010915110321180610 64
    0x7100d60640c1e22660900000300004101003105041c1310402c16220344c1c3c94070007100824508048043d0004004c40c2c1c02701414103544600d09100c802210a4070160042082194001500d0710003058075001c640d500ca0190300300344000202455030b5003498891401c1038000e40d01c606540510514207a07402044410b403254441004584103441400c81d01c09000d94804584510341c1c00000750440780e91088441c080c0d43c910500034420360340d8600c806ea82c0892001d5500c4d130800b4040300042d141d00c9140c0e00c151b0b0480d1040c41121b280045c0c2e0440d075807480101010440e07114440400410104581f405010050030131003110a40c6540740030f00143d035004041160100340f00024180741070b404c0c015104080b00099524202c41c800c01c208030744000701c0d80103010301511211022500c00f415482a04c0d1074050300d003040010b801c040c214100070b668407920101040003034402003065841c1c00e000a100c1110074001000e00c4005400d014032800300140007640e0301081503102e0343c10044910f010324600e2003151114407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 329164190 1250 329162940 329162983
    0x606040306091e080717120c1303080f070b0a0b0102060f07090e04150c0f091a0d0f090b0f070509040b01200601060e01090806060f060705010608010f0e0d02 69
    0xf81689940241a107400b03a803440181e0318105010a07040148180f92150240000f60004012013801d240100420300c0f96861030b0800044110080c0f00041481489001c00c02c443e2690300d6403100031039444029085682e500100b540c408105610f000c10b50421003c0c0014000807840e4030000355900001040b01080d030740303a540480c4045000710304003005001c9034160f5845510741400c10f6215001c81402444c1c1c072a10b07044458050920416221202002c1d82d45c600210340d01d0004201c18000403031815540e0307007004000360324201c11248a4a41100801d000115480989042100000754000e10398403800c000001001009580f0500315501e6407412540040c4031a4030b40012204221289024090b680d5140d819401d01200090003604a031400d6452211407204040112080280341c4101103480d031001010540514000c0700341045110090a004e0900081d9150ba86c2558829400000c46035950014402045007500607800c62000380401040c00e02440c0c50001c0d91016081c03e5440b502d0a1403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 329165440 1250 329164190 329164193
    0xc11010804080715020306120114010b0d060905090a020f061806031003060e0604020a050d08030a02251119030206030f15030106240f090e1f030609020a0e060604030609 74
    0x381c01d07900ca05402444000c407804c01c40a41e20001d6109481d600c2c464186101002010382c014094080d000b174816007000c0c0303664a07081c0b14404940003a00d9034080940c8174480401c0d80d41700781c4200c501c12004a401401605031030b006002090300070b001120b0040d0001c00103a4000100589801ca01072800d950b41c0e0354a9a50f00010703050741c510b0740c2006000c0d50422400c02c0ca04500010b04900540c000c50703481c5106561002000142e55980c40010101003091000034108409130740604644502c1031305000c02d0008021150b00e1145801c2000c4440b103800c00403505079414405128030b0384428000d44698018210b80005155000c0140068070228039040019540b020202c03400a000d44040c00a120a03a123031180320328800c0420a10105040d00000789d010414440e000d070310002d5030980c95a480a81c18510320030b00c030b131340000d01c040707460181c090002c500c182c140300c0c2c07060080d4041c504c0029030040610400070003403020750200e00c1d0100790005101d420340c0c820701103038201d03035020200049540c0b50703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 329166690 1250 329165440 329165453
    0x120e0c09180a150b0301060b04123c030905060319020304020102011e020406021b0d1b0e0f180a05100c14070305030106020f011811130606030b0f010c11010804 70
    0x8284003c008001d40080c0c4001100590050020200200c1c001d02c61350762242c5420645006a100350103075400c80c180c8000c0803843c2da6800a00c00310225810200c1d600d807246030320303008984410390394010004080d030040515078804600750103400c0c1101c1e801d2441c2851030f28501140500f000100480e903000000c0f50842e030003503000e0810212810301d040300c0c49514540203802900148908805030040ca0002445100101d01801a46000404150041106849090f5401c04010704414041c68589011030181586850a84138400e400e41005080c50083c1d0000500e203c003d0000f41c541c0e100a00c00b5000a1020802c0704680040741400140e4804191003101c111050058404154200103402024503501900543c16124a41c08652280004c42c40042c00c039483c80081c00340b4010903006000c002390081240b03014070a0014501e82408000b00e8001003101c007198040750101c1e680d40304078040f60400000e5600754001c242013128000206494900c0022508264281000b1607078000030200601e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 329167940 1250 329166690 329166703
    0x309010b090c090a050405010e041b031b150206070801170a020411040806070c15020306060c100506090603010e060613020c0f0105010303090b0f070209041110120e0c0918 75
    0x305070021a0610103040b5405a001a40c498015141c038040800c0a00349405814100c80000b50002e182e40d8894641c1d64030900c54508002d410381103124000081414500d510a00c80310352031803085203516106c1030000d41c1a84401c98000d542003a420415084d41119526045400f252407081c4c0c03030441c0303001707803030401c9150301000358441d192074046a40c2240780700207801178580c00011221180c5074100c090302c0e5821501d6004000e07405083d9201d00a0106401850301310002900c4c50342441c04bc0756003071707040a00e180700c0d0120150743c07402045864074010350025008001500200702074100500040d071294001000c950040070385415070080302d00d01d41d0407103400c00d0101c0d05035401111003410300ca010301402e02c01600016484403000c240f00c640d641c121050003400915144c07400b842c0b58284810520001c00548260350202c22062aa85500000c0d0845110907034a0041c0d86031404001000c4070302d50743c481c400640c49607285002c552207544441c1d8000d81003400c000000445807507443d203090f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 329169190 1250 329167940 329167961
    0x402030f030403050304080c0a150c020315010b0702012c01030e0a0228050406050a05190305010510030302060a0905070302130e1911090903031b04030c080d090905011208030901 78
    0x200000b0008107101010005c1d000362101d080907201c0010484042024649090140d1954074a43e8030685844601422020164034406803d40306040d255a00c0d02d807100c0e209a010398855400051039200b1076074010594070555051100c038810054044819100342144140490705160b42c82413004007401c400c00003400550b81c024042040c0860f50030360703802c0962a00341103442015840802041c0343c50107019400965a020707018840d0baa14210030828a1800c2010780380c8000000040440032a1080c042d4a00c0380410321150310050746140b07802031070001c00403d102280ca1610602000003500495880201c0e90125034802a942c01a0f103550f0040030401a074500520031602c07000d020300e1154000d642d1550145800440708010441403016603c000c54062250b60000c00009420742d2a45071500c880c1025000700e10b05050703d030b039903958030040c20b5000b80d4596408050303107440e16684030b02c51202a05028a06000c15450b010b1603010030103010000400089020002466000d803d600614445 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 329170440 1250 329169190 329169193
    0x2a2c12010504080903070602070e0a0b010e151c06080a140f060406050609010b1306051803030f031f03030e060a0e040c08060406061110021e040306150f0302010c0b0402030f 76
    0x90605107010f103a241c0c4a1250a070281c050b4280c00160540041a9407048810f9a01424240c2d940d0702e03400401010f40d03006079030600032001c44212280e1141c002c581c03142c42000c0300803940c0b41200001000f0030b028412801400a08200702401003000204450b54220b40c020407990081c1039220150f402c0840c62200709140c0d228500c1007005003d0140c0055014260994440790aa62500c082e080740b48a0030400c8142824540c1c0200070242c8610000c0c140c0f5400d8440f401c10724403600d00003a0440e40020020004100d02105000308000e03903028420b10a0400200c1c2d40e05145144e0300075011003407a0541031312504001c10b940170114041c944088400d14020002c21040c100d100001d0184081510024066440c098010580714000c48134508105148402894070300c03036044204010f5030240d250540102802e0b4070041d02c013110346000e003018500c14240443c3c1804118202e010094055001c8444840100810805030340c2207180945100d070001002c0003a07564900101c3c0c07810341d20b1050700c40345 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 329171690 1250 329170440 329170451
    0x3020a0206031015080c0306010c0c352103070504030c060201050406140601170c0403060509030307020f0a0b0a0905010902031f0f050c040b07060b03012a2c1201 71
    0x158444202c02d43c2620b01d00500d5001444000908480b00c0000b1520840050020004108650700400401104074840c2c0031100c455501c400d151a000c0e0b1005502603198610500c0c1c6ca4240c01404045038206070702e41000b4119000c911080300250035443c88511000807000002c2014140f156040b00c0242da00a4441861140e0315a002802048126000c2c0c0711245450362540d074200174140054001d10f0142d4a41000c206212205090f00740701400600e07540030100400000500c56000b19841040180d02458691034550b001a080c90808102300c0817941114070010300244103484c0d038a0700f158041d0f10010740c4032003a14056004248607040a540752082400d07001001c4a01c0005880080c2050b409101021007107043c00d060b18800e44070300c10343c07810600c000d00c0f0000b5034801420502e4003480303002c507c12480c070340400d007102c1007040750030168184000c20001d141d035444031090b00c001c02e0380b9040c104107165101810301661901359110036400003102c42d00480d41c60506d02c0c01d010000e08000c010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 329172940 1250 329171690 329171701
    0x9010f11160e04032c06090d05010608060105030d030501081e0a1403040501170c12250c02040e0316080c0f060a02090a050d05190201090b0a02011a0d02011b03020a020603 75
    0x2c0d40c10840f803c5002511849034503041c0c5001c01c00103000c0100c1c01e142810114106030420540380c122401480e003003035180300c0d001c01142d001d01800005082e500052b003250f5050074141805c2a646943c1201450308040041114010002d410158040100300704410420410030241c00e005200c4c4019008603406c040040c040d0002100a100b1910240c0340d09440901401891703041c04001c480e009c000c4002440342c0d200704242380c00e0300b03a03114401103401c11f15000603108040d12003501c0c01c0207034009900412024214182752144078007000340c5c00011410500310201a1602c1a01c12100801c854004030700b00410305401c100a00f0640a140300741d4941e03140c800c10b080000e40191a0451265024000001d0b03103080821400d00103039040700242c0307080e8144044c00140c01c020004100d04010114200060350182d00d00604002c085c640c0c0041545c4540240b00e000e15404025520302c00d0001030b81103001030f0780040c411098141e0b0020004078420701401d00340e04105440310044e4014400108010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 329174190 1250 329172940 329172959
    0xb0a0801140703050a06120f11130603020f04060e041407080304081609050c031506120108060a0614031009060b030d05131514031503121e09010f1116 66
    0x107101d1482c5507410406551140000c2064a003244036617000c2940b50703003d50340425603d6480402c500d000d207c0c00d000100e40040810034400400207140096079a402c010310840c81c184d41038844114003210244140350800b2059286908090001040c001646810028010003800240002c099007000c0c1c80d11a942c0798801d07a15290301c40039607501410040d4021494060a216290052804406c01400c540d9500390402c5c0c1c0c1560450541e074411410701843e6100d880700001e080c00781c121440034000900700014000141c4e2041c4e00401401c0d1096201d442075501c0000300403807904410400841d0f1000c050074100014480000c04507014003941040c8400660000d0080285024032020000401d64816200d641c50040c3d88450700000e400000902d02d50240102940d0002c0038894034442c1e20f050800064038160402c206c000d564003000c0342959100303407034080f4558074806100c0300d286842e045500080803604481048014007200ca0315000702c03100c040141042040c004181c481d181911000c071311 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 329175440 1250 329174190 329174231
    0x7020411030127020c2805010c09060809070602030f1803010c02150114061911010504110411041a030709030f05150105011d060307021915050108060403050405040b0a0801 75
    0x8051100c51000c3c03400c41c3e0300e0750f4030880c1c503505c00c95001741c1802403055141c0c903502000c0a1240e000d100c040c0b60741c000441c90a200300d044800d0a91140080d091520350082d124030001841c0e135030300e038112b04020403095401008442450704119429a545e80b0305006081030944040c001c02d400d9840c111900d50300031b400080c1c580d075081046d10824001da90750004005030b0000d40c2d841ca80c001c1c81c1440082c407604d1075040c1007000380009003048814010083d0405007198070881d82605c0c030803181400c86c2d8840c18544030710038400035080000c030319045c00d00e0302d40c4000300b101f46551029002c000000650036442480700360003a56000350f9810070a07219003441c1c1d40e0b80200480c243c8401454034000140c5602038000700c0c03a0700350000810001c8060710800c03c0400d4200425480070341c010817501c0e02310340a200080007550b03480ba60b2102100741020301c0801c12910143c1041c45258070480070f20020070b0701721050b03a040311011100810460502c3c03020904c6011181d0110241d07600f801c039441820744020200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 329176690 1250 329175440 329175479
    0x12112b0609140f1216050f01090c050a030b18120d0507170106020c04050705160311010e1501031401020405090a2910080a02070c03050607090509150105070204110301 73
    0x202581c408085a070030740303688240c01c4503c1c0316880320320580c120f001410042c1a46030790f0a21085407544158071a43e0806000d10440c0d40e169549001c0c1c2d03010421781c1e40651015000543d194079419055070b0f030b038444110000d0500400e1040400d03003c40500020040f000040c000c01000070344038038000701c00380f02604091310303114049105d0000b01c2c6a803940c8100120b04030f41e15503009100140d402003d100040c070020f401c05d0b0420004011807100540e03201e03007000d241031081c0e07aa0b400010f0880100380c219080d9500c06503482c0c0202603a41450001c03e0320441c152500001440d00400744491403600910803a8410368120300c2020800000781202e6001415003454000020141c003003000c28020050a55120a64000510740034820141d114125403503021460502c0107181404948841d10182e03040d41c005c5500380d001204018401e54407541c031400410007034800e03400d1070074400300c1c2c07000e4100050b404604201c004038400040d0350f02d503049042c60004040c10f41f540d95031038107074410310040071004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 329177940 1250 329176690 329176703
    0x3060d0203160e1609030303090515090f21030103031202040e10053d140403060903021e030f0c0c130b0312090f040e0a0b0106050a080112112b0609 65
    0x50b1009252181607191400940d84c0314041c07030547c0c0d0290024412034006444912645580040c80c03401002d2040c0a86090b100070120201800c580c00d251055a0302807411110018019050341d552030000d80741581d9242c244000204044100c09e0020300666004444484c8808140501904490740c50701c19100c041c1e500c88810f18145810040106691500c900c600300c0d00e100070303100c10040c420212400d1446141c0003c00d00d2124031181000e4115070020344800382d8920103982056010003a5911426001c000320701100c003030a0705c4d162280201000d4080790100080c900401900c2403008030008040280344155080c0c0103440a0001c091030f50115009110b0171100400034108c0c00141c40400000a12451804400100344400781004109200c5c451103280c0b100b000144c0001c02d0a030203002203503a43c075100c414114005003800030681c010714407500c0b0b81d05140c01041d07250782c0c043d0b090401a030b00400d5940e4250310f001301c441240010003c20084416200301000129049103002d01c0c02100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 329179190 1250 329177940 329177969
    0x609121b0f030a0507230d050f0c0108011802070312020d0b1921020a080d02010207031b0305190513120c05010908061306020d091407090c020c0603060d020316 70
    0x305040d40c038103d0040c0507083d98484d0320304210b0040b66841e01c24989400540100c0c40800c2140403560508092204407408d070412481601065020040980b6090007481c1c180b640d945041b1001071406d442d8184c141c58550002010424107000d881000c054610704e0f00110755891030440141c0081c00103d559902c41c0b24072030040100f155a40601c0c901b40c03a100713002d0024440d40e1511044030404904012078100e081607030000340051003446407200c1c0f00240d400159450320703545002018034080c1c0060b01101c0b0081140c4a01295109050712080350244800029040c040441517846000781090450078400c20840410641d02561180303220070300c100600080503448800540c0c03036121a000742103480d40010001a144403a00031643c0d001c602505006280c202e0510040301610f281c00f5041c0d40c1d18038500b2015410002c100804002004400d000700664464200000d407070f00d031640c0000e8403403c000300c007286441e6110b4003c400b800741d0003011100004c1c0c90803201ca500030507500c10381940741c0300c06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329180440 1250 329179190 329179219
    0x7050a09090b0109091d1f05060109060c0605070e03030f0d14040206120a06180911041b0c030504350312010b0d020d06080705121b0609121b 62
    0x900600d8900b4105840c0d06121605140000c001005030980c868002880090310407617030f28043c080401d80542c41c0400c00340c410003903940c000a0340d002800290400c0140325041007183e502c00d0300407038100ea110b54082240d40f50000102e40700d084115820360301d400001050300600d1000c0c00189000c154089050207403a100c1c410780c0b901c01c0c00485001c0d420907020405208a41454400e6690101d007d5900189042d01c4034828100031000a0014001950741c00059090090320600d24900390021141840054203104904d080c0da00c3d164100000c2c4007803c0340c400c0401d07014105450142106c41c510318034413011004407e010342c0c031300410300700c00c55540b40504840130404002c0728008a103e206003c1546d103858140f81d042d03401b034a4198609542401042c014003001e005038001451030740010701545061000b0842020381c005212815680300d40741042ca0003041640c1c03180b0344041100c400340c4410b51a00400e984d40035408580d9454018a0010340c040040c0703010000c0c8468041e1580c0001d41001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329181690 1250 329180440 329180459
    0x211b0706050a1d0609270a020403030e0405100302060f040e27070803031603021b060601090b120109180b0106180b0a17180312150904020105030a02090307030b07050a09 74
    0xc3c0607000d800c030604005110b4035007400f0140b00084106590903288404101030448496801034444e91000d03500060700b001070590008422082202c00c41d010001402d000e140c1c0b50b60080c6d6848000d01480d408290910249441c0090b10000e003100d00d28800705280045542d19520814940c060259408030b4008501e41070019090341951003000085103581c850b48840119003600c0100d001c10181c00f000700c8c41e1070070410001811850540e200620090410714000350000c04241c2008480160911407180003044803088030b41140c02550000415014110718009940c1c0d048002400c410780c1070700002141c03580840152000d003c00d60021060765118801d02249215056090000440d60310360034400e0704402d0300b140d40204d103013012046080318034a105800c43d00520344604500804400f0040d04050310302c20828809001c40d1000c0355480c0a80c00a0514000600f0801043d98089901c5180d07403820440c0901543c0c00c419001e81c1e500d0300003001400c3e58000c003200300001d45c01c182d0001d0101c62 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329182940 1250 329181690 329181737
    0xe090c0303031515120412030b10050903010b0409080408060105191e0e010b0d1a0105070825300e10050d020a030203010501020f211b0706050a 63
    0x2002005036103962156907228a800d24882925a440060001400520b8100c0c40003000751030041070b101100f61502d81000c52901508251400030305041101d00d82403680d03211084215401c85090040d100c0e805007010a00500100c9105a049032502489205010003000a40b04503218442101c90b1603072034400748403503824040c41200d90301c42d160400784040c420126a2007840040c043c0c440401554803204620070510070703440700500510005100d640c1c0f901030f024040d08000e006070000c6480b50b03150f0001b040c074400d002018100401c0410700f05038200142081070035030708849061840c1c50741c050501c0b640314402c1800e040c249a840003282c60b03200500d1742c44d00142c019030352503c501c003010000074041e2801000351414204102045181c903d04014030103041c0c544825500184c0b43c0d03040130f001a1609a02c170a1601d41c4d80d2102c3c1b82c071520034003d5810001600b49488500d51185a03141500d0304c813121903000c0340740c40c1c0109240032881035404009060700051580c1c898050301203c00c1040705000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329184190 1250 329182940 329182963
    0xa0b0a0804020d0311120a030b09040804170304091b08070e030c0405060102150f0907080a08030106050a030f091506091a0906030a0c080c2704020d05030405060703090e09 75
    0x306028001405880c02c084070346111406414441219001e4881e03840c20030951003680a039412021070300d14140396040c03140c88100501550140f1081c02c027a10340800c1800b542c0300c0c042e0303400d10240201d04400b80a01c250340c020182d40760140004401c0501c000c0d400c4c403075a100000001c00003000240214810281120032030780190180c02c0d07100c407aa003407001414008081d00d0541c419044101064144d0a0317505224402c0e80a094610b1f04003041224100001039100001d81d600c14100d90340814501f0040b2811203045040c17507903507203904810a802401c0408100e0511601c0c1c00610420700c503e0455000814451100401c030094903042103008039401c802400480701c0b454a406c00503810240c03956504140d0007011902c05031203135500d002000310b082d00420400e8000d01c80c40354441c1041c3c120001d01080081d0b405600c0c20200c981100d032200c0051010740305a010321b4035001800010720880c0c0103000d01800760b55540c2c0741c0d4140034103101c070640f10301305a0355600e00004001010101e10400d258 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329185440 1250 329184190 329184197
    0x20c040506061c061208070c080607080a051905010e060f15040605160b010803221d0403110303090102040302010e0d0f0b0417030a090b07092402030c0a050a020a0b0a 73
    0xc81d516403403404400c00c02c003c0b0303000d613561050042910b0301c0094034484400c5c40380c0301441c1e8440042c507041c80a002c1e1075208481607884081800000b942180400d0703409003040800107025030311404107105408408540412030307850440081400c00020f501d0512502c01901c1c0c003541e142d419001d0180342a80707100c00720b180c084244000e000d90b0703100b03a005001c03044036000d1800307a40181d82c4440c2d14144013070f40710100652002602a080c0e00c00440302024200b0400c0624041c40e00c0c0040c040884d0010004808045644030009810540202c281090780054001242c1c0c9a1500b1510711f03000b0b50040c0826400301e0103100b08218a45803000f44000b0083d80081e4114851469586d074842604004e071040b15440b40400100850351000e0014510861407c100891004068106540e43c0600500707250f0402c0310091040c031450340f0103030203040e00c41e03003403022040301c03180d030000c120b0a60084440440d0b145c09a00d80c44400e000000a96245041c000c031201c9082590704c00115256101d6800e280010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329186690 1250 329185440 329185447
    0x9051006031b020615030a06020a050a020d05040b030c0d0212040c05190b0f0304020105040909050c0405010504020c0601050909250e01061e0c0c0e0a05042001020a110a1e0303020c04050606 83
    0xc0d0262108000062010301126003030707d842c0e0b46200590708815144400520b0200306082000d904018216040c00c403400c0a501d083d0a0020310500c500c0020511482030100140c2c001c50300104c0e604840c14505000710407103003400d1525051401d507240b031103950b1042445030741251441e4040660541110345a600003450080c6690703082c0f1454000800c1a03040c45020301000401041c03034020034030f2291040c400f8246540300402088112041030700000e019500c1803246005240c400038180741540c000b19240c81c16641c807000300c02d181c89400d802c4213003400f0421020401c45d4030240403400c280d440103c030100342c0c0d81e201d08080b00ca104000100c0e02240e40700c00401e41c10f9134040e5601418403030040d6018029940c4800d801901c420b4203442c0c000e4000d5a410400090000340310b0000300c19400c100c940c910101d0711200007985c6586c41040030344103052402c2258003540c4e50b801d110008220a04a50702001e51607070072500902118072003a40036000c0c9003240142c03440e003071141c14414000207003031a08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329187940 1250 329186690 329186701
    0x7060f0b060c1504050c030709050601030612031211301f0b0304020a0b0307020a120801050102120c03210a050a1401090914030d0603031701030b041b09051006031b0206 74
    0x700e1180034200fa45c041c011210100c80a8609002010182421000c0849d29050000006003116601c0d0702c46203415070071040403000a58051403141d4810182074010032980d00051480501c1e1080140c542e00d1103030071860710b0441d07440c88203140c1244c00d111580d03122942d803181d0302070070400300c0000c1124020100c883d052003407169a40107542c110b4005400c0010b52a103401d07034091950301c2a10008c000da4000341c0c14908000e6148105568602240391508655241c81c0003c2d58502c6401a5500c6d0402c000c11107030594102041902c148603100c412583d01c003001080c811824542c107640b40b5500a05003c0002c03004e071028010101032070984846031015a180c449500010003c044080b1081301a00b64100d2615004201900043e40345050028265185240c05480000d0019502a102010030f00420220b4642400d40360320a401c88102c2c02c4004500180d5108022a0f80040c5141c0d4a00403c1c404003031001c0b038544056079800d4600b041002d48038540d001040e14000c0c0048010b0340203000040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329189190 1250 329187940 329187973
    0x301050306042612090c030109031209060f05010323011803030e0102070218011e0e060103020c030d11040e13020f042c01020304171903091707060f0b060c 68
    0x40703e0242407402c1c6180c8004542001940d01403801001802000c40c01d00070b20f2641848180540e400c114002c025031910740c0c0c0c4c09008450800340e60707408565a1150941031107090b800241d40600065410172040d03031249000c0071385600300f034082542c45003440c4001d0501039051103183c0d402510840700e010404556036089028000c404000b4070103540034001c550041c0c660126003035581100e4019600c440d810451a401e40c101c1140180020342c0e100c0c00c0c1003106244107034846070851028607000d0703540d142040407145503200d0341c25030314005450a01d030b0007440d20a442c013900c15244039110b410f01a07110714010f05103405480001a601050221001c1c0441c90968000c11a408c0e06080001c022614111003603182001040c11a0b401d940002c2000304121800c141d0b481c43c9014400742c3d500300080010140c1a900c000305d02d04007131554440381841030100c611005d40350513507803488080c3e8031000d40c030b0f100d0003034072009030f4054009042c030b41c2c2c0c1021850414140e40381c40f0614002091030080d00100d03070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329190440 1250 329189190 329189213
    0x5040506061204051507050a090533090307241218060b0901080604050715021905010b04060902030c07080d0b211b060304121e0f14030105030604 64
    0x2a81c400c8080204a40000a1040440c0f055000d1005407050b10800d1046a20300403000b030110003000810011030800541200e030510a64400b42d0700e11001c105400810265012603c0341c103440c01c0c0f89502c6449440c00d07460010000190141e040d030350842c2d40c9801181c0c10080c00712500c5019028080d01c01c840c14032039018603288809210020070b02256090040004d45aa41d000b62404e50701e614140000741401007042e40104821002413009251031384900d41c5a0019001e1204101072150390000c10920820800125a10115994101b4030031440c1c2030303000f4405070105901460910a00103109000d602c2600c1c81802c50030749040c50100b0603070799504075a002c810701c0c607802a5038005120040c5c81c0d0f030118100703070307030007007603507503644076013905401d00d081c001481111400d94107900d00903441e20340c0b806483e003040d401200e41aa0400804042e41c0c0d101100c03440c42c1e800180040210600ea03071000700b0444a18007512400303030102d85000c2801c0f0318802402041c1c0c0640c007501c0031600041108056 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329191690 1250 329190440 329190451
    0xf03110609030114090c01030501051f1206031a0406051506180103060e01060905180402010507020909011e0203010f0509150d0203150c090a0815150114130608011707050405 76
    0x1e504c00340854a800e43c200c058420328055403182200f44465600340c802d81e40580821154003e0b480d400071502c14402d040031456504010300903a030319810043e16004540030f542c0c4281c50301e441d40384024203090041800c031400e4600908100c0841c2c3e1001400c0c03040ca450705d201820003803400d80183d590680481d106040141019a5000700141282da00414103010309200e030303120070030700340380c10204500901c01000c03160130f0700e01420500c03005070380001c100c5100030f60541c2c60300034559440c0c0b2194010300008007041a240303602c0d080e5062715941d5600641c10307030340d4180c1342d140100c1c3c45d0800d00400e84022074089002620344440e003406868034061182c1c000f8801800c07203d41207000d2414005182043d1210b248003403011403121810300d442c16804014015440081c410b410300480540803701000d804d45030381900b01e580324400350b4416952450070403805661a80e64034100c2e0340810078a0390794403a4000040c3c04000103d0324200c01c10718500e804590100500b83d02c2d08120030807000b030901604 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329192940 1250 329191690 329191693
    0x6271b1808120702030c0a0608190b090708100f030209060411040b0c0a05100203070c0f030e1507120206010506030103060c2609100204120b04021203220f0311060903 73
    0x100040c1c0d070038100304007102081c8201d42c441e152803403813050602d48420800600d1280502c0001400305a80c0108900d61041140402c01c045500c0502290007d154250a050f00800082c0c10030a4043c4c010840c58011004000c0e02c0f50030a5480c0701104d0307404c1c003900008ad0700c060a1780125000703280c660080c0c20480502c01c0d03007070720b0280c1d14120407203180c0c05200c945140d60080c85204040c0702040c400d5500900d0021010351452421440080129140b0341005246003a003004210038944501d4032121003607005803507256800021804076607c4e400c4054100d4010141c140f400940601c0407440c54120b8401403e42815a403c5580b02006030600d0b0604204010000091400090308120401110001d4000096940c103200d0003550034030400f4a0948016030040104200e0b135030490701c145541d144c0040c2c454002e6211880010b0009071025400d030142d21001c14516400c15100c158441100c241c0072280c64460350b00c1d2200007080b140da100260031022680c44072002401c1c404020400766200a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329194190 1250 329192940 329192987
    0xa05040e0603011508100c020610150e1309021f0f1d06120f0603010b130b03031201030b09060f0f060d02010e1008160c0b01090c050d06271b 62
    0x5042c140a010b05c1d4000700d4250300030010442030b0401482003a0800941c1e1010b000c1d01d00e400807032040d645900d4441c0300b04807040040300041180c4610001100411b004100890340259a440c000142420f8441a4410000310348010a410924850404003980d580c40e80324030f02481c00d00035221000c442c42d26100001034100c0110080da40d003002020a1001c88842c40390605141e0040c0c000700030010107043c002c0e850031160b81c01e03030b81d100003110800d03c642c0035000c102c0c14002d0000c2800c6002e5000380101c662807817400401003041c00e0300344a00c20004082228003507071b582c0a0184a904080c0c6401043e440107102050450600299a04840d80103060075140480103001260082111080200c0000d030b292090085071f0185060107030162100340b5182d007000b801d40d122005001e00c18400e12420684d41c0e001011000d01030829502c44400e41c040400c03600d82c0c1e920700c05c55030800000740442ca040d5840400703043c082e214030034121102c0c4501c1c801c1641030001601030b1441c528503070045003025040da = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329195440 1250 329194190 329194211
    0x910030609060f0506040905070b030703140103050106090b010801120f020a15080703180302030f030703061a030402030d090b090d02120d090e01050a0e0c03070c0606060e010806060a05040e060301 86
    0x340100d05036944561000a0440c3d810300c0128210b0710094034091080e410541d16101080002844030252109051034075503945540b5401d0b0000e1002001e1040c4001110000009100e0b0640c802000c907022500c0034090660340310011103049409002d1a007005a0f07041180000c2080301d10404607240c03019040c030b40131580780c80c241c013050026805940c0000703c0340340c02c12101c181e15000780307024054250311a50794143e1a40c1c2c0a500c9004029074845850004000142c079a840b9401007802045410045041440301c000001700315401194183c2c001c0c450b0741c04822000f071203019060101c884105007181040e554408005200050388400e903400b155817204040d1808041c484403030203400d070b070b02c0b0322103214540b002c04814410142e00c8140329880c011004c101c040d000c4040c041d800003014610a0380c1781e86140040c0d55100b0140400b502c214600003003c40c005401c01d507080c41d140741c240c84601141d501d0204020551040100d00030010309c092104211031059030100310b4004100030b001003480d4422 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329196690 1250 329195440 329195453
    0xa030f02041517100b030c0f190b1308070302010c0f0f060f020904061202010215040305070506040c1707080d030b131803180302010f0c03120f060609120b06091003 72
    0x681082d103541c4442c51030307000c0e510400c110f0341000b401600c1e01484031401c1740d170009445003480c1d80103e00480307484144c80c070941d503010a000740a64641d903280c80c4882d10b0f80b4900c805900680c5003c081180001008260640c0000e0580204c03039050351100c400101607540c020b000c400d501c408030f03a1070100d10b8000b40050360f10300981401903c81c010040c0c448403e5404c0200340e680c03650042ca0344089107844007000d40d0f030100b4000410590500d82c246103446914084610713200c0c0050140650113903070184010000208120b004550031040c40d9091a02031421158403140300b4421900651300c01c0388500101d074003903081084000d04c001c00011418200640c02030030f42d1402c5d0814880c15074003c00328410150020703189881650042010b00d1582d0955001030289020540f40e0003c0c8a40c00c5440002c0600c08d0310a04c00f0700c0c00151003400842d5418142d4409007200d40a13050100b10321030360111f0049010b02014480307680100303013a0002e843d414280b090b02c40303001c0c065403003141c050030303010011980 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329197940 1250 329196690 329196731
    0x72706050a05120c09041a0a09090203030c011505010306050619030c0504120b011511070b03270f0f0d081f03050615090604060308030a0e031306120f0b0a030f0204 72
    0x1d5132113020366624a02010001191036000301c8a045400c03265001e102e9490b6483c1c4481940c440850010f0008220300000b4514003d10310525600e40c01c1101c2c0103441d1881c0662031040721001c1c0c034288007440d11130007040054000c21701c89216181e20300400665a501c6a0003e900c421100d040c411301e415181c01607102000300760030781526044030801c01000100440c41c010103c02d078007881d02d034490240104e10152a0f24451040115000000c404240592000c078190001e00c18804c69040c40701002c08000ba841e000030b00c214035654083e80f04200381c3c0d0240854054514401941c03841207030743d964240711400b203007240081a0b0b11110618040001017007000710700d002e80c0c100203800010704c4195040144860300100319500680c1014803c10010b062042540d070440f420801c0800c00b403407101c81d0149140180620442841d664231000245160404140126080e6591052060b11000c5001c0800d03500c3d2000404d1b04010101e104001107203240030341c081d80e00d100400c0131031543c8503103020521011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329199190 1250 329197940 329197951
    0x901031a03030a0314250c05150f150f030a02011d03010204080f2e020a0c0203100f051302030604021005040b04060e030c09280f020d05072706050a0512 67
    0x990300c1c0d2001d210342e0b05c0c90b1149507120a01d4003020440c00081010b4407055412a40c0c148240440302d240c00082000500001070700d01d04040304460710307242009040d03412000c1616040030044040784440503078240740840c0000400060018400c844459004540d00310304001e0030703602110411225400d03540c082c001040103050340002000903200031003119050003e01c1803d130000b0000b610421020915040c1011020341010000503140c0c5008841960005d802440c025410702403200181c0846d0f0866000c05041c041c002010411070340c0b160400d40b030042c04864040d50640c00030380020300514007010300300c00140304c9103011810b0542d0340702e43c040281c100f50802804a401c4440401d9079003005c00c407038000c01104807911040c5040450764071521900c0b022603150341d284d10b076001494000c4190000c04650a62200441d0ba4205015070140100020703613144000848522100d41d850162180d0301c100c218a410040d4041ca242a0003618550322007241a014081700b4881d01000c003d400b0351061040303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329200440 1250 329199190 329199197
    0x1e0801020c0f0d180e130c0801021903050421020a080406080f090a0b0a05100308040801061e0b03070c06060e07020d141e092206030c05010509060901031a03030a 71
    0xb0802c101c0c10f052400350801c1c0d80070070648051196804818140f000203d03403d95010060f2a21141c038044001200300ca40a00100182d801c00541031905500034102c46074504160b10b4001d6840b10f00b201542c0c4190ba000d07044507500d050741d1051480489540c45082620300440301c4140d1144d40d01d0105030001c1d4800b0700030400a00402203901c0e03901a0361940300388400003031b0001960590703801400c00c101405d8121003d64401c00203104501182e0f401d0099a005407c9035282c13940d40c0b01081c080c144900802e404050009007140c031103400b038800b0005507150686840e0441d5150307007044518a10380281562926100c080001e5a00b40070740d8094000c4250354007501c1104c0c0b000c000a00004000480070620a0081010074180400d0080c1c2202c000001d04605070780313070b041174001643c0c3d45094220646803002022000b07860b0f1420381c068801c036480345469900b101e0365a8010b440c140590800c0310741080c010881501c00c0e6110b54030481d298282c05050a130701508034030200303103903402c0700381e000010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329201690 1250 329200440 329200453
    0x6040f082a010f110c0d0b0a06050414070513030f11010206090f070b070213140412020102042607090612030306120305040506031012060218010f091e0801020c 70
    0x145000c11001c0d4036044102911070804840100000305122840200b09040280402d840030212505001c108064070006101c15101069400c3c101d40d20750b400c1d18094070813440d05000181c1400c060049210244030107075028000c1c4c0d66140c094481d0360200704100084922554080300180d810110020981d0080140f100d0300301040740003a29041c005040344101c1d51110403c0700b0000d00004104e426268141d80050700d40c20349102040521400c21541c0202a0401cac00e0b072501c0000c804103241c801c6000308400780601c0c40c8543c080e0700702c3c0b14500402c031300c04208807900c00c055414a44644540c0c0e40110407128116502c0e00e0309400c07540e098000e00303082500384040c070090552500030782000d4488070038840007018159901a0051043c2d1140e02d02901b070101c000f9403540c842d403452a004061196010b0000e42c10351401e40020b6022640c3c200100101501c0c20900d544280103554100209448040c03516090180f102980905c100e0000010b030b8110001160300c45c0c0a0020b803607210614801803a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329202940 1250 329201690 329201713
    0x10020a1b0206090402090102010b0a151206141c05010e0c041d2d010e101a030a0809030109050a060f0606020d020c010503100803120a0606260606040f08 67
    0x10a101800080c0c59a40d240c29a40c0c0c0907960302c804551003c1401c03100103a4480b50100141c0c007411001c1502d0360301030003110000131100c030b8004060714008100d0361645601c0c002c4000c05c2045403202e026080a1081a15078000ba07030500403084a86900030681c1e9010b03905950303a889007580c1030004000314130703081100708140508090003a540700c080100340c0072498981200000d5504d25900100c1c402400d242100103402c001162400345805000c000280801c0601c5150150784592402c180e000240c40c101c09002103141000440035010002006440d04003196102c0070007942106002c039505540c0e403000c81c8000340c1c0402c01d40011501c40e94000c05c131845101305813822907a49034801402d54000b84901c40e449540400c0075001500d0034280310b030b203c0d1100a0f80e41e003400d405030000d810b5480001021400303041c01c8400c0911603901d025007071111a45a500403201920110541180c0000300c8a008400804512850380d0008015045505007a6a8040c0158003100c42e80301e20401d8020340031000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329204190 1250 329202940 329202947
    0xa02070f060e06070209180f01020c0d0302270102030c0d120e19150b10110610080a150e031b0f120409020a0e030609100e071d100810020a 61
    0x7040c1c82c0c1490500440d1440116040340f0641ca0000d01c244880400a0358000d0102c440d00f240e01442e108654100200c485264000d40c010307080040c4c03510500002c00701c8140b0900071540712103000011500340001801004400004003020725056000c00d1108042d020010000242e02050300d9440c038101407201d280013000c032111590703801c5007034024201800703400c80c00d000d0341c420a43e445401038403075007000760001004001c1c03201000d5211850b80425100e560740100490b4060304510107503203568541095001c109011351103001002c2d0007a40c1c031400454078403c90541100385410300421801c103034060305411640300c0981e041d81c0c005120007444070300500708040200403101e040200704552003911907007a01d004d540301780c00c1c2103a0009491800340d4401c4407d05190701e405002c440c0300d07081502e6803d4542c640c0c009100b844a1400c4042488114001018400c81d0804283d0411038010a0148108004000c0903a01e0005420780d0004449004100300c000480d1300000041c0c03500e400b00e0009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329205440 1250 329204190 329204219
    0x306050f03010921031506030506090906070813021804080408070906050913050f0111030a2901030203090a050d0c0b070503090d050d06050a080a05190c030221030a0207 74
    0x240268500180b510020301d6002c020a5654102070280c5811801c13014100e000d805030f09400d0241d100544000100241c054000324002d0ba000c84580f01c0c2070340c581450030303a40c2030219070410010322240c0100740c000b04100c00c2d8201960000d0301441c0a084a1400b5504404007034070102e0781a800000e080200040521400e0050244488184103440c074041c0080c0c0c050801809541241242501840030400c04000144003001d80d40000e006046a4034031440c201c1d0412641808014146180781000e654680810244204e9101892030f50107842c10045000390002028116a4890640c401d00440c00400031f81075461910380e2000e100d0b03250740c585298400c00141c60170702072150a0050040003800401c025030350342d800e440c185840d034007031842e248090000b40d80b110b81c02400110002c140d42c000481c420075180c0c001c004035a0302601d5044404d031810340740032019006140c41ca805100516040010307440040c128008069640c003509080dd046a202e44107880150b44030083c20015a07282c4141d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329206690 1250 329205440 329205469
    0x40510020601231809010501050411090904170f0c060403030c0e010e1905150d0c020a1703280b090105010504050a0330020d02010f021306050a030f0507030605 70
    0xc0c1140b945481007540d80c0200084400702ca62560200c0310381280c9510860b0f5140c039412003c0da400c0790800d001660300a050a026150145052601da14a002c40250445504817400b6210030300907a1940c8441015541da8482022911820400b11507250b10640c0644501894400036104904051030301038103c5003112540d03000e00c107048455084a81e0066120f411898094402d040d40805c500381000482e2555040154420040546041020345041c0946040c09081c401005101903240e01a81c1d281e161803c02455008100e00b40d84c4070b40e032508051900300c0b003406d0040d611004003090310240c4200c00780b080c4000d1952070004804d80d2804603003160040100f030030600d2801e4104000700d44d031007519000c041c2c000c4004000351a1110032945a008501100720a001502c010031080251900f0491904600660a21401c5c88040c6614801c40780c002200d184000e40c0b4600d003007070640d10f035000600e07424241039030740342c441580000c84e0150a104095960300082c0041c1444100280c24519059 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329207940 1250 329206690 329206693
    0x30b0f010f050406030f02060a121b08101410020718020c100501141e030601030305130f0b070b0601030b040f050601020d1103040504050c07051203150d0201231e04051002 75
    0x8002043c0301c9402a400035030140e07108c65403900904801e990390808034a0807d030091030065510400a0b5840c0d505000c040d6941d1184180e40300d02d4803030703030551400e805071244004049134514440e2818880082d103003061401510321050f501c07401e41c000c0510785c514201400347c00040c0c150140c001409202a030005010041069504001c0c002c2102c503c505c6107640501c803030300303014840f01c02c1118440d0b0503518000e044409660b1603190090168220380c03405412501180c8021903401b03608580c403c2558189035481d401d101403512407624416020345024141556200c840e203454a9600496150480b11000841e15080002c002450501818901400c0013040e02c0780340565003002c0202d6089413011180030809403600b21808059118400000380648210141d0407071104404000e903208002c007400201c42c81c2ca1060078088081402000240000c80b5601800300042001c0884400c1130000c00c0b0081c10b2030340d201c1c0c000480e014115021040c074007011404000700e2410450682141c1400d20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329209190 1250 329207940 329207951
    0x618060302070317100b16060507020d0f030504061803020a051b01080114010302090306040b06010e090c1c0204080307080d0b060408060411031606030c0f03050108120304060204030b0f010f0504 85
    0x1103000300044852204612a90001d0004c11842014005e401c00030700302ea400e00c55614003007600b0074411030515050807100c2c030341003034009542280003140f1a82000c60795224450720b2899410100c0040c00001c0003101d0350b40d594001107403c01d61442c0201aa240300e0b4004084000003810704600d82500b03100c0030504c0034604000400543d9000c16040e044558000a0300006109000140d01900034400c510786c062240344100070511801c8260307180918403c9c6c8804000362483c40c148130b0700b07000c1203074034802c41801000700c80e0f0b181c842d59060755114000300b600103080c1912100318038155405541e058071504000b003600090440d079449007554541e003c0340c8041c80c0a280001d101d4840d1801040980501c0014440b074009403003e201e0440e030446d4a0b40341c0703000d031900c81201900400c0d50118000014000100103003003240203104d800c1c1a40c9070b0800510a07401c50020019069100400440300d444d0240f00000000380c080000034040c140300d00c041c00f080d60518030400c0d9889950f6008900c2241002d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329210440 1250 329209190 329209193
    0x8190f0e03030907141c060608190b0604020306010e0904020a03020a1503060b04060f0c0615090207030f031104170c0301020c0f060a09080403030e1809100e210304021207061806030207 81
    0x2401b1101616000580002103076401d05040c030007400030ba445000140034801c40c2c0d00c02c113481c40100c10740c031074400c6501030043d4495030f050204a00003100c01e180842d03208000321000d854249080c0358403901c01003503000c00b80c0c1c403980442c00040d86e81d8001d00009048400c1e15003c2501800360744050260100e01500702454500014011800c0603050030a001c41001e10400b80090340d000346450402e100c0c4034008083c1d50340840d400a60000d00c080c0e0010f5401148554141c1c070078043d00f005040c00401d0a41814140048158001c45a40300c0300418801c1c10000303034080c5c5003030000d06241d407100c40182082261121420381091001415024001d1400d94400300080740a0291421f0301c1c5c252620303d10f00d45207076000c5500c407003042208032003640c01d040402c2100d0600150441208054210038410301e00d41200c071a0b41e50050b506581e55290f2800c1c2003c414185c20750185501c140003c00500220b8940340c245400c1c9403c541182d000180c100c3c2032048030880700c20040004042a02d811450202d69 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329211690 1250 329210440 329210449
    0x4080306060705030427050702010903080c09031e010510060206010324090807210e0609090402030102070209040302071a04030812070e060a120e030a08190f0e0303090714 75
    0xe05841c8101c4001c603000e8103220080050b900609040b0300d15500b14a22520b049941c000c0714800c0b00c00103810030700080c400d10b106004188915a0540f140041a150004000040c4d0400b19800c0d800d07106076900d140142c189840d0b5007141020410001607141000c41c1c0015200c01150401c20039544071300d00410020301542c04041c154458081100e13806118505d1000207050b804c540078120300c001144417428000c13019041e4002800e05d8111100d9003400107001e58603101c503000c2c40750380904140200380050a1854140c0d0b0b100344020001454045164000b56250100303a4091700160701c840028041d14516400600401841d81240c6062078915514548103215501d5040300241007031002c00d0a4501815041e1900302c801820f150b1a004491801803000806100c090a010300300000c1300304000d400700071034001888903581e1042c955642c1c00c0318458081441c3c112188607542e480809081d100e42c0c82403213181381482c40915500d04100082c146400c149400c00c3d42e8401044117003a14555a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329212940 1250 329211690 329211697
    0x309060f150e090c150a1b030809070602060613090c030b010e0115022d150702030901080610020d27060302072001091a0f0f1c05102106060b1903050408 67
    0x40d03d0b24142e0ba501c500c02040b51280001fa540c0d411000c4480c0c2c40e101010381241c2e49134854a907100440d00c000759541000caa031180b003900e01c260040e104030a56803003000c036038106200403400b0b001040010760b0340b5038454010301002d9008107880c0b00c5060061041d0701300304500c10001800da100810059206440901000103006081440c0420042c038810380f0000501241d600b900007007016803c0c41ca003200d00a9103942c80541c03118006142d80001909616010b044030303541764079581c010105261305c08025605c0070700190784405c400790001c1c0c1c554035201d5440e0030340c000340c006035a0160b113319207407900c2808003540d45007070f202103000c01d0410603090741e01c505400101c0306c003503203243d0301c4010b159040c0e9030303a204070520711030303184000101d00040300f101c0001070150b07401c030030046844446140d10700d9040358007d8446082950000e40100b080d080454000c00e00440b0316102c00c2c460068583e10346040754429840b40a907240c010030422818030030b880c4285100c52590405001c1e91500d0340da0047d4512 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329214190 1250 329212940 329212969
    0x90807050a05040c0e040903030203090f070f060f0c082101050f0d1712130c0503070f090207030504050603090a0308090a030c0b07051905031605190309060f150e090c 73
    0x80d542d065103e440c5100c0d022170107240708042c108100030045802c0c010080d51085800da8850302c07421403008140e00e000660101122110020184118140348048030000b41581000041000340e481050205240d1401007001404c80c0c00809012000c2101038000c0384016401140718402d09510115651140b400d121181d55004c01d101804000b881451651801900103400003a58500300b00a43c0542e0250a0307640140683c2601c2034a0f540d68040540d0740d001e600503a805540400c0c420040411160040e240061007414281c1c1040d4480c1c0106110b500210b81c0307614264816581801819000703000e443d004440b20000d4561031030107031000341c03000b041510010012803042000540640c41842501d01391030380d21010302141b070303061003008000747c000303503200850b521412290b180e019028030125410300a041c444403100392600a403d8000301601e050560303000d83c41d1090100c0000f481e02c104454580031940e0310786141e0400d00e0400002000410104080d40a181c10001d50341d0fa4101141690 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329215440 1250 329214190 329214199
    0x60406020318060d090c030b09010e07090b0d080d0506040b01050901020309011407141c1b02090a0603120201020d0b040507020703020910030204020715180803180f060c0a090807050a05 81
    0x440c03000b0128900d441880031124142e480c11030101c04014400e1024421680107911b803045a4540e040c801d42281ca0f014440c5a083e486003030204800006e03504040031418005050015040c00ca884200c0e07250700c1481c03d20201540c520130845503203400c2c0318001c600a02071800ba802c014901001035a0781c4185490380d41804500c1464408019440045500542d4046400105546c1000000f5600c0a12240601c1140d0001078003008a6100c3c0400251610031000a000314840301c1c4c0910000d003602801e401c00b001d4980c0d4002c804240c00e005000014141540010398401407119600c08880520350200d00c254101400d00c001f80e6400506030f41600e80403918400d440d216401003449620003580000e400600204005062201c07241d02c0d62002e540b80582404000d040d843c54010969015800400102c000d10105401c0482800941038200c1c0e410121000c059040c40300b6442d00004482c1e160f1030980000d40040e4007981316043c3c0c80100318420040c52082d00f007000151464000b8050103025 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329216690 1250 329215440 329215477
    0x170a020d02090303160218090a031b0b090c0123250c0905010501030509160303030509010605090f011a1240020901050a030209180a1202010501030b060604060203 71
    0x44a40d903045995004005088a650720740e4851610200003101030182d2003403602c9000a840d1845400000e1300c280d40c03505c0540044201c5a8054481c0c07000f0702140003140b28003504070b6000484210302c09021740303d0b5000134079001c90f403600010a03940c4240c01100c0c20705840e00c401c5907124201410758810b00d078880d042d001c87e00400e1405040c00c208161000d0540c64003044002510700d0b0583c40035061b200e0a80c1c09014603a41c1541c0a40d4a00a46a038074160408148003000820300c03a84c84141c006410100104101e541c2e0390010f00c80c1070017580d0000b142039a00e401004042e50007001ca850550381705054138100b40100716070404000005080c20f80542c05040c2e00d610301c100b142540003889000e0724407241625003003401142c3d01140300504134001d124204c00880c16184c154036100841e5402130002d13480d5502e00660550314041d00b81c9102c810300c030706501c940000d0300110760046100d00c0d41d8000a0550300d1818160009580980118010700041101b80080c0da40031085410110413241208034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329217940 1250 329216690 329216707
    0x201020c0915030a03030506010e010f0503130213020a0203030a0b182a12092a010c0606030b0408070606060c0b1305070f1206110a08160918020705010c170a02 70
    0x41198814282d5503040c01000c00c0d000c101074140d480580070300b0003a070740c0610808815005442110540000b4004038105000041a0840305070a21956610142601001d81c1100c0070001c140e8124091850141e0008000c01507800118402d940180c101125209884a5038940c1c0718260301c0040c02c110707207116401c4141c2d500c0c4a407428003003042061031580755a4035a4075803e0080800426164262a40a036039180e8080f40003001e2074200784c4c290a1195100c1c800c1a40041d90300e03e814141c102c5106440d0b403800800305200f0101c061041d80a030090a0b41c0358a0343c500380b0f01325076180d00020140050054080301042c0e103910510340c42800f1018442c41c41196040c9940380c0102580701d002501d0b0010302c041848103110b0601006540308040910510034240201c1500c1e018601c4400001944031000804408600042002d0403d10b0b0078000201030b140c8860410718400c1e90b40d1282c11680000300e4001f00031092180208800f070340d103002d4504030108403c4201042c2c000e400741501a801081468 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329219190 1250 329217940 329217961
    0x30308090a0804092a08071d042f0a0207050906031504030207050111030405130c09030b0f010e06090601021f1517010b0a030503040504320a180201020c09 68
    0x14516034104a0b82c1c0c1d01c40741d40d205094080c022080d80b19048034010084180202407807825002002034984940c01ca036074940c6800c442c00e01d40d41070110842c00c0d8644103010142c90314070a0844601800e800520f00041207550150703140e99651200c0c84550040100d003e80c0e40e80418105c040d01c0c0120f0304240c0e6501c400c40024a030900081480d404910548140b008040c0c00066000c1198400c0c1c0707500140381c0c60b0041c442d0300c0780214424107030448131407132000c1c035054002c2e88400c00070784540c101002d0194603522a03140410086a120420010b82d00042c00b504c02048005036102c9001c56001d013540c60240d000235140c0040070000c003444540c040901c50100d9954102026000c1c9025003000e41580c3d8410388041680482d002c50900d502e4800d10001c0d038240080c0140c03d80350040007c500c1c0a1070f0100b4440200845800e15050310350104540a06124042d400e51000f40b01144480c5107042000d541c0044a242c9007885240605401140d001070b60041788145080700100e03140c28003642c2d102d4500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329220440 1250 329219190 329219203
    0x204020c010f06080d090509010e09011b0203130e060102100f0b030f1b150f030a0f0c03091104061206110d050903070501050606043c080a0219030c03030809 69
    0x141295401c00c0b40002080441c0c0d84484100c483d050101c6901c0651454251a00152800b5490704845000700503c4429802d0907056040001e100000407282c0300700445d0000101e11403040300050b040001d1414030a02100458000340007149102282030a00400203507841005070b034182c440c282c80f440010ba01c0e0300035a109007075040020741503880c844028614940c40c3c07048000340b6060b104042c2428462410a42c6007418030070f02d074920091402420071840249904000c0c02420904d803962620a1446481d010f200c3c14034a02d03845c08502055a40b50403192020708509607800345291440c1000b45070040c0c94218100342e041540001e400814500c00e0002d4810194805200fa05020500080850010007000e44a00500080103d03071030300b00c20080b0a100303c0c49480000240000b0300b00c2074421120646c9000c24070305000c1065401040c1502000203a03941c800705103508080710401c15418408031404002106030005000c1d41c0c10340ea5403d40d444864040a01041860000075840a5080002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329221690 1250 329220440 329220457
    0x80108101b0e13060618080a052505030111030405060717060616050d080610080106080c0a03091b1701061a07150f091707120f090b0309030310080a080d09020402 71
    0x140f20b9a910780b43c0c046e04034864a8140d041415000d000011441e402040d1050540c0d844006031a1144044018000c200f4a012101c00c10712152900002d460f5024403884148002140c1110784038500750034044d0030038000900c0c0304240700d240e420407008480840c0e030156102404442d00b544450520f40005203141c5c1d40f0200401d144201d00c1d01d8000140c01805c40c0e403280300c0840c4c40145401c24500102d56080d820712800c0086400030010600300c0c4401d602400e04000359250004581c149612a041c50f400c000c8003041522542100030320502005490802e0014a010300078824646084540c040c10307038044814415510000c01d843d003c000032080d5840354841403c03003d0064078682c905020003080404800c554025099215000da2581c0c10241c9005580050100138108203000302698540f88c245507501c2004034070300010800b13841603c00765000c0c0c4100c05c025526840e102403c201d6942d1150859819540f0010100000541c032608986510a10003c041101c032054030210b4040e0260041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329222940 1250 329221690 329221729
    0x203070c170c030712080d0f09030c03020f010e0703120e0904110916051b0106090e07051903081b010f06090e0705091b03060d05010c080108101b0e 65
    0x100051424401144825440451090b00c0c14640035104240d90ba100b24400c0f0082d2800c201200e10104014801130b01d030301491448081070b41e40040700341d801102d0318601c1c00c401091f0140640000d141d4100000903203032405c04000c01c03185000c110010341c1e075401403100903c5581c4245041d81ea0074412403d420f03600c00b01401e07459007410240780c50f608803110008964000c6011100140c008080c512901d54800d00503121145851120404429122400f2055680540d22400c0001310081148580925911701d0006826498184020810218410b0400806040b42ea88060000c41c0210b804c444020300904000203004004011726805054440e820400365464140d0000301200340360031081100c52180161180c0030384500401401c0041aa42030940c3d810300402a4540d00d144802540c200b8001441c00101c0c0441e961a0b5007511022010341c0c00040e40d074801040341000400810417101314950050100c41c1d400742d081c11303400300c003c14180108000d9000740505629181e0a481801d8000c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329224190 1250 329222940 329222963
    0x60108070612020a080711070305060a060e06060f16050c06040f060809010516140f03271911011e1d150711060c030403050d031406011707020307 64
    0x406032621003a1140e8000302e00900300d2140c06101a01c21101c1071000c0f61140101034640c00c2044414000300c5800000600c9820008004288104903451003201483c0c00072a0203400e180c075401c0b4240000d00803a00a2509000d1024130b004c941c001e031940032950070006c0c480300509082c698902500d800e07203103411610004000c00c9080192561006641042e12241240d845401086080350740484600300700054100702240024450440400003101e04481d050904e98680b010f004140d10540d4032511101e60101c4883d0302c040c41f07280380c1c1d07030440820018000c0441b03540610300000328941002080c048000c0d080c02916801174182250f00038454000e9101e64458000291480031210081903001801c8016031416161401c51020140080c1c0c003179908010140d03442c407601090b02c00205034056018402c120740c0400410162004500520041c40e00c100c14000c040c0032a1503041c025600d611056041010598210341e0b0408608900c082c07920a6540e4428200d08601034103400402103580301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329225440 1250 329224190 329224199
    0x7020102090a14030604030315090e010c0908030a080411011205040b06190810050a18080a0e0108010b16140d020c090a0615030902040b040504080a030522020d020d050601 75
    0x55024108500040d55945512900c86034000f81c601904202168560301c00800940040e100c0d4000c0380103103101c0f0030f41400e810b40b41c42d100404c2c2c40c140d07110300301d19a5503012820880d031351003100d01c0010303c115000303945400030600005015a4000700f000c1c0c11504c0c51807512040383d120f03400314120a0740e104801c110600b003903d00302c5060344060350b00d07a00c03d2150075000e00d4289c501d034840783e0485810b0401090303404a0746138540b000d00310080603446100c0e50f2f030b002504074207410a81d0041461040c2601d654030103040101810100660300064100305100c00140031002c1640101d48808807a2403c0390300180c0300d490505000280900b4441c0d9034051a030008206680000710740702e4482c002c0b81d506550342c1d14000420121030140c440c0c030910091200c41d80c4d8410713000398064905030780081c20104a00421070701103000d40f0170a48044803d000300143c8403a541e40e045c881c40743c001d001c04a000700300c00c1c0243c40820714065a484e020740b003004100e05000c1155034500c158408243d01400340d50056035074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329226690 1250 329225440 329225443
    0x301150f051e0717160b2a0c12070f0212070306020c0a111207030b090c180105090a0b010906050f19090602062d0718140307050f030d180e0702 63
    0x1c40307021207401211151000240a04c801540d613a0b00b1903036000c0b81c0100458aaa0100940180c03038031648560070302c40710960005100f5070f001c0046603810300b41da1722140e0540032807410f178007000245003103001030001c071000840750036880c0c180540441c0c1560710381840c10641c1d13041401c0d0b544020002403001503122580000422a6072700c4d60300941c005607612040406100c0740c401d204c190110300f07400c032000520001d142980b103d504401c0b07050459000180590115002582d00780303c211a26002d80010011303031a00d04101c0d640181840000d0144016040020709000388a002e0b00e02803000c003050081c120a0711005079540100325885540c1c0c005c0303490368007606406082c050000180511030020300940103c0b1380200c80949500c0b440c0b1010f8041c0c00e60b0505017400030b0001403c0150042d02c003038050040074540340103046010744610400b80b041d001c15142010036030003907002d80802c0702074240b030781d402203202004480142440c61100d6010312804a0442c21a00300102606a0f2024000020f60 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329227940 1250 329226690 329226697
    0x19050c010f05130302061303080a050310080c010f0e0d06020d0e010c0908030306100512091b1009090b1f0c061409030702040903030b040903050304050607050301150f051e 75
    0xc0e00e94401080c4001c0040300c50348110076840048a108000410041c1443d600425080c000d03144400c02e03282e01d03a60b8541c003640c17240700000001384020040c400800e810f4402c090081041c000182680300c4503400103400a02013007148010b0200444071409141c4480a54a8000e94010411036681d001d60309901c0040c4515000c10b000d6610f405196680d10703000d400c28200360b520a03401036003103603a41c208000100000c20011400c1040c24400c40103200c02d1003514501039280507000d0302003802c1e116141c4c1481d00d01e219103107120303a8100341456420b5030002c452600f135403550700022500741b8444c4081104661005080c014203800488841c803400d03072050000d42c1c298814030342404081484410b46035010300c02d03101100203400c100b02d41801803505d50b1104070200c0c400c1c00c022840d445110b00180445012560990204100000300010031100b844002d5000c4800d040c402e08550411004250020b01078001c1d005100c03180489004550044041c1c03100f509459032141c05813150700071081d443c2d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329229190 1250 329227940 329227963
    0x2090a0e030a05131502070905070c061103251d030f0a0819020c0105090d0201090b0c0f10091a0a06031b030203011802090a0917040e071704020d0210021905 69
    0x6914003007507600c04002d0312401d80c9021b900502d1141d0828000d480202809804d10090101e180c01c5100003c0341405a40326806145042c90303103d00c0d005040444808400400b1810711074069201c25425800141c03404400f8240c2090002e07825400c0c0101345002441024600c00c0e11401c007100d02000103040040408410902c800310103041855002e983e61408074111030b000c40c00610a1800c1d0341484403994412500500d482c1310341c240d0f05c9600384c0340b036032001d0900d803400d80240300301d017898007410031000c43c2c02c0780044410080d0f0452501d518201400010309c0c5051903070307070b43e000c5900002180c1100c2c0c003940c0c01c01240200441e140f03c0d540001e0b070b03003840120300035424074000b210001d104001c680c200c4d0703401500c00c00d4595501003800004120b143c0b411614000c44400c03000807010383c50054070180219000c0f4103203d0030080005090588101900241000003804000050b1104000350780e84590588018400c135076041d100782e041c1010404c48000c140b0505500009011b000560302200d40d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329230440 1250 329229190 329229217
    0x2180709060801060210020d1b02030d06060e0a090209120102040602010c08060907080a020a111f06080a0510180b04050a060e15011a04120f020405012102090a0e030a05 74
    0xe80c1d4520050b02c0c1c0c0e010074407503603000d82c0100e810303442e82041503002051250541c10001881c0881c5400100c100d186201c40107005030301c041f070b05901d002642d10030b17140602282d0801090f51829032000138848040c90048600454010412250301c0d01e030320003038410110010300299200c60325050300a008124100d42c800c00075540301d021521a00302103006500032000399440b07030000c0d9540403512002e07600c80360000041000010381080b00314814012440c4c0602403144000c80010300c140480140c0b0003c0d088180c20790000d410002c0001d10004e05c024070724005c5080801e41181220f403920102c180c0450140c03102442c41c08200c00c221f0302054484840c0c0c8524020481c01511850040d82c42c110390751803510020b034400043c03141c0f40030500c0000102c06000c1d5203e241a0b2251501ca00311801008116445180c15118004500d400e02800b40503100411010b80b060740081e5000d80b04400e07104019002e900c042c001708064402e0754029801c12003030082142d030341d00900c2000074030136400b0701040e103640d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329231690 1250 329230440 329230457
    0x1b0f281205150603100504150921030c05070f15020d05090607050414011809021207030b01030b0a090f0e0d0507030e15030408031005130c020d0f090b070f021807 71
    0x75414031040709400348402400600745e04021403c184000d2901a00aa451801216900041c5c031100d00541502c644500b00c26103c4111071410200480301502501d82031508103410110f00503402403d496880390890980c0e03075841e449090150346860b0f1148103040080c0001001f940003241500441c1c00b40408900300d801d0f940e100390040341d031405140103224101160810441581d0f206030055618504a9109441095651101e00040340e1121000d0990300780c03070300100424250144144141503400782800d0002e00c25190000e049018a4021400407503540c1c900c0644070310580e4008207a490300c2600300d8003183ca00e07200c09081038001c1c1e91304500090b071105000c41c903824800d800001444568070010300f141c451340d9403102d168100900350481c0b0446904000381035500c070700584012444c40780002401080074840281003105002610051000c0b081c044900690305c010080101c1c0c040441168407a440c034a000c8d103440e02c426202961103003011000300d60762180d05001501500840c0c0307840320f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329232940 1250 329231690 329231713
    0x7020c01110c01030b01030f140402031510090e150403030203010f050d0c0b072a050a0e240301290a0807030308040210030b0d050f1b0f281205 63
    0x108400c10724204403064120a0100030b6950290304004003040c1c0504011804e00c4a20701c0740070072100c600c900310070240c81c02820b000030343c01d0520284d4a40018107401159a2030300341c013810a00c0e460783c0f1481c00c00580c0d6890040d1486018010035000c4070b45002c5071142401c15040040207034000703001d41050360981c01c100213000d181001801c4001c0358054141041030740307006a08035403600010420b42d11103843e40c4101c2c9504842c0503544c81401c84040c1e0002c002030910040c05110f07c403942116802842e21001c1c0180800d000300b10482c2c0c0241e11641d150404603000c042401b4081d0201c001100c3c1e41c03210250301003042c1100002c1400d51f02950a0400c2d10ba8960403580d039a500c0b48005000b02d244035000c2005400c1415900c2d02c2035285050204204400101103110040040410b4400e500020604146900d090010340c21000c808800c107070450b2002e2001608109918110511495480d11440d13110484292882d60244141351002031407599061090070811540c6030455841c0201019010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329234190 1250 329232940 329232947
    0x9060305092103060d020d120807030603050a0b091c050304021002070f060507021c05010218041116050106051f0305010b0a1e2703020103050903070b07051c060e07020c01 75
    0x440401800b46603450300d450400c001c00a55102034100c1c0d03082020510750308050b8807605600302002e482451200e9030314032810b000501010010f442d603030405041020400c0445c1340010542e40f81500724000e8410307925a54001e030f2a014000009185076048001803170743c855000006548035600a840070910612a40012611401d46000e0419403c84050061083c0c42c8a0300150841a1014017980c25103060041e45020405481401301c034169000502001038400c0703011048485c0b80e09940c14071001e0541641c102080c02500008000350507000e60450500a0940120004280240c1002c0c030910f40750099082c00000b481c410004682000300004000903002e0803503a05980c0c9644030951600c80790761038038207007040c41401d208108100560340e2614000c1000400d2a202d5403081361813003440c1d031001600b0307104001c04503003060b0002c4c050040450000c482003030340401e16203001030396107045c00100e0301ca001c440080a400755241c04030120320803281e80a0280100510303001c55624a61100044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329235440 1250 329234190 329234203
    0x70c03090e0405060c0c030c01290d03021018060e0c180c03071b020301061815080a02091008030c030a0908160902160605101d10030b0402120303070906030509 70
    0x1d156034007680018917211028006414016001410380b881e200801d4901030070340c0c83c40c5042c0720100c80c10741861402203040c11421b0703082c0744058440000f04501c544019403544182000c25200c261200c2c800d500c5098035071480c0d183c2c0c40d4071400c10840c00d60741707266046e618050030313a11502a0030210042070544500c0c10311a803081001c070000c5451681c2d1f407401150a0041030038845074044070000c101006950a001e4403028010f0948040803682281c821002560881d601d00741c6115000e54090180380300120f603010166405940c200c4041c1c46402c9020010201d40c0d0ac001d825010102e4140a034490200040017484d800da81c41c2c101903500c64903083c1d248d01c6280c1c011810040000c80130420900c60f6009800c01000440c140440c034040d81e182c00c82071360822522040d10b001051400d01005400080350051000301d500b490445203024120502103440c0c03070001900705080900003504650baa60900d0881281c014207990300e80c00e141102800f03142040c05800c000c82d00307003000034a4160000401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329236690 1250 329235440 329235443
    0x1306090b04111303080f0f03130318030c1a04031712060a05060a0305190204080a02100e330f09040c0e0307030311011b080a0f0524010e0405070c03090e04 68
    0xf40e080e4510b95450200364440c4200500c0010305110710b4002e05284009140f06011010411404407240e184c01090001c03a5418400950321603802840407480111801050780c140100c102c078103040491541060b40101e0f40001c108038080408800c0c25034058010303200120ba503c100310b40b0f60b1100c1d0208003d4002a02620382c0200b01407040201c01442904410b8003c030394414181e50844440701c646060364000d412041e00342d0f10004900702142400502d94462001510700008920707104c000143c098a2088007181c00300341a26113005242d89507086841c0395560168500f43e1310303040f95218500a4100542c0c45125034500343c0c412003654007607000b1400058004002c6c01c0c0c5142540e400741c0f1402207050301d00d401c0b50743ea0300442d902d0096046c4020742014451322240c20500d132103140ca100392290780103418941d40c144000d00a0299820258244c0b04480c5001003411140c070000480d18650140083c503849030414060098142e0003c40741d0500902a0382c81212094580d01c808020711820f980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329237940 1250 329236690 329236717
    0x906260c100507031e0e1503070503070c051911030f07050303090d0507050a0806010305120c0709090f02221808030f07020304030510020306041b020606010e1306090b0411 75
    0xc10340c001e200e20010038100c0c2c441d061613503c404103184444104558480300601007186103858561611f064100b658141c10300c14912461440c104800624500014100f0001d011030b400821040003014040d01e608000b01400320700e03d03658182001c1541c840100c507100d001740545250f1141c018804503540080d644050000c51408083c2c070305003c8603030044082a16140211100030542e942c07a00b0b9014000c0001c0130052900d5410f5040403070030b0031201d242031503010f8020000c40403010700109981c400c444c0d00320000221140c080c200f50100003090540294001000301c2e1b20b032548508000b0500071207090000401003441640e80d00c158081c501c81000d02600e03000c0c00011450380d48050780c5640071047c0d2041e00c0c2055034070341c1c0e200d1500f00c4164034a900513401104014075400c25202c1c04140c0107020171503805800080e00040e4980300301401507030401c0f0200a00c0d40060711407400c0c2c01c080c0410300c10100182b0382d50b0840740c4001e01c242d0403090311a80c1000a0a995948908290b5028181060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329239190 1250 329237940 329237959
    0x1e031801081003110d0203100903020d020a03120207111c0506090a021c06020936070804061a12010603050c06040e01060f0311190801050603090c190906260c 69
    0xc440344c0c603007404009400ea10041c42c1c1c440d800161401c0c00146001404100003084060251501030f0800c000d4100310001c540c08600184040703a84406210f201389002e0200503a1000700b07042414000b0780c01400c1c2c640280b840d0314959048406001c0d0740030300f14061b9050f2100c0c0d0710384c1907400740c49501400001c0e620203503400900020050000a1132082445002d00500d08403084011035000302118003c0c030714400b41080b55030b114085401640c940000303281c035017440c0344c9441d14010b8040034014002910031a40c2d0803242400c01542c1c07074542101c40f002000030503426030f10300c440c502a00d081e00045900d03000c0c00104c013000703003441c07810f40d0183c40616810240580c20218203c0d0350007480150f1800300341c0c1300c481c4803a0116541d0003d140ca0050701c0d0035051108007144014103a8141030f0710060140c0302c10001c0120001e00407c0c1d550800034100c4804520341400c0c58040c00f080c3c0550801091245041c000059508100c0d86141840070030980124600301c044a0094443c2c10030f0104036040907204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329240440 1250 329239190 329239193
    0xb12010f060c24050106110c010509060d0e010914010f0b03070305030a081b0d05040210080411010c05070e09010509060a06060e0409061d010507171e07021e031801081003 75
    0x31543d4850b0402003401c0401d82c40e03904a0050242c9070280e1010b40800d00b1003601c1e030895070050050700c034050001c1c07c3c007030319001341c1402203060b6100300c4100e480201da032041c0c3d0005940080d0443c0a034680c0190003643c42c6800b04014074001c1050282c05141301d40b8100c10580c05c1c0c03e0200b8420308136134004019506001e004d2501b81d604480c001e1041011030a10312590742600403810181c902c07020b000000080c10b103081d106004040c105d20f40d044082c0f145540030040011102501142103050a103003904100e440c6103803041c0f510102d80c0240c1540703402c1c5c1d01040450300c0154411840f803a404000c40c4c1594036030100c000120394030707801024000703901015400d09606058000003442c907c2140c1c00207040071003803c40ca03458035448105160694440d0248907005500c0724402a00d00c0000e80340800c2420241107403821806001c01c2e2941811603040040c1d002802400b02c0c8200040402412628403280f8502c0d6440398030900a490040d00e00320418502548204103182c40b800c02c4a81e42c440003401e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329241690 1250 329240440 329240453
    0x315040302100c090320090a151d0a050c0c03032212030f1a03030909040303020f041212050a020c0103091b0603020304110619030c0e0a0b12010f060c 66
    0x10025015031150310000e07410044180702e00c0414194035a1229890f505501c3c00105000524410280706c1c0e0206002e102265140131000307411100b1048005a040c60b031490120408440350701117040c10810400d01c80c1c401e0f15034070342e044c4104841d01d4200190b58944080c40610700a001e034601d50f641c0244000380340c8148015210300d451000100800103840c0c1c43da1045072400c50207000d500000d4032345000c0034403d000d5008140039000c0900f0b0305c0310090080004a552400380c004064441c0040001040a042c080d90458040c241800c46043c1d58549580c1d01043c80801c20070116121700c1d200c5004503045210300300b07488008402e0b80c0601030310f40c40d03e001100500300d81d8800307842400b1400065200c03a07405098030b0000b08140c0d1409601c034034150800040e8214040200340c06a1401c104c2030b01c151300c0e100445021f0800320b040014103500d0411003252310040741c035440c540295102c2c901040048850000e0108200c00103840d44203a030701e803003010312144000d1203800c0c0802e52074035404001490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329242940 1250 329241690 329241733
    0x1103010c020601241809020d050903040b070f0804050a080601030311010b091305070e091005010b090f150c0610050f0103090c052e1e110c04090609051c03060503070503 74
    0x12180f51051500041c00318658003e08251b00c01b5100c2940000c401100d03601c1e5010300b81d40321020748041c41c1403500e4849005030034400d041c0c0081503403126018910400c0340007801d0ba0301414004e03002000e0345498550640d0707180002e0100340d001c5246003072401e04030740c41401640340c00c1d880038045501548690745485200502c5840441d564081d28001244035800340c14810710508142008240001c14030079100e003113600c180c004030b0070158108409483c903201d01821042c50402074482c50400942403221a5140c0680840c4001c140502d10074007160380e1007070031042e0590b103040b5400c0c0513030000040103504a8007401001095542e1508040002e480e2440340466000d44c110340700c022407840f0900c0c6244001c0d1080311500400d848141550103941441440e141d4049e00d400c040c190040713807103412960b980c26024070b144166240c58003030040005c0d50b003140d900e69521504450000d8060364a000031072011401d0940040d14100000078149000140c080c1242d001030051321402c900f5240b07160101c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329244190 1250 329242940 329243009
    0x4120f0213110301090b03060108060f07110f0106090b0103050405060426031602071502060c0f04090203130b0a0606170c0723060703020a0203090f03011104031103010c020601 77
    0xa4668007000001c09030240203190b14480d88a41d83d81d40c14440250100c0b811581c405000c1c0d4000d10042c007000d01d0004202c0c5e0085d0030850b00041d16079907124100e82c54555103161186a008a000079900524150840c1d0140d80c250300c81802010000001102180c40c211006003d96015202290100300581884203451041c002e40030708e07103524800c4420b190b41c030070341e80080c01800034403044451541c1400044050304440c007400100d00c1030310300003c2d03030b899016004e4168170500003440e40742424940121401805956025522440c10842035044034116100c15035841c0c40c28030000f00d2000e02c40c41803d054441139100d184000c1c2110307490540724840107100450301c1100b0802d15001c50507000440d04014403210040402e20007180c1d0950070840040c2009040c10b0051084220307054020083e00d0b1114401c3d1080c1c00f94003000b1001a0140881260441e4100d8001602106103c2950002e880302001580203000014030044d0032640c0c0e000c00d00c520201001414288412120000301c08000c02c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329245440 1250 329244190 329244199
    0x206090d0215130305010605010e060d0b06071202030a090b19050906040b1902010b040b09160c170a180b070b04050705040507030e0d090e06120114010609030b090304120f02 76
    0x1500900345509040e0f20000a068040d0076050040040100034007440015283c00c0c6400c2006106d04004102280251f400d440d101940300c0841070a2900d8034403e80c0c0b0541d0b0400e684000002c00d1120194407503000c45249000500b09200210780d003010071044640840c850080d000300302a00520480e46a0040b18140e540304008200000c0c00203202d1024240320016580510281b690000d8042d003191440d00c280f038041c0d42400345011143d5254800c0d2036002d11400c4510305000d070800004c443c0c00a00790340c024101c803122003000c44103601c0742003d09814a480d0321440d684015030f406103141c10800b845684282c6c3c00130884080040c3c2d0101865400900c00c1301282c0c4015280e42c001400d8400488000e80040d0381d40c50b0007a5000e40c10000e8111141c15801d001e00e4075805e140b00c820242d03034000d082c0d500441c051081034107000000d40c4480c0c2d02c0f85214032918a25616240c00a140c481700384010b0394402c4090021510f20740001c0704641c121158000b132015581016a10f529542840d00300a9911 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329246690 1250 329245440 329245459
    0x61011011104031220060103080304060e0a110f0604030c0504020f0d0603030f030615080a1820031c020604022106130212010e032203080d06030c0b070206090d02 71
    0x2205251010300b01039845030361110700b203c054120003010062901501200040c6010a034050010f002c21010305603030b0884445540e81e078031414480040e01c02c490300c1c4032540c4101c0d00000b040c0080d60101008880d0112407411810304940c0070058140a6808003800d07200000600b040a454540e0007442100c40901001d0f040640d07440c504011500980d100398085500680401a503940c03600c80e03103002c0c1245400340021018440b20003050690001c1c0591483c5507589101e00f4164941b403402c044c0b041d803004110965402046001840003400e001c0d0900900c00c40c5030782000c03030304d510b070071a080c000d0300383d004003410b580c0c075000c00000b840c0f0100c006200c405601c2c0c101c558100c05011a500c87c00d0441030f2034a10490398418030004a00c050718420481c2d141c2028001c4841d408011284917040010074040d10100f030300c0700f029055046903c010305550002410140112103034004408682c055544032182c01c0d071301c0030006964810308200a5000e201001030202c28a441c80180302c0c01030001d010090b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329247940 1250 329246690 329246711
    0x40c0e030a06060519180504020a080d050c0c090403020d0c0c0906091b02030309030f0f0f0403030206040b060109031104051e0117211b030f0d0e060f06101101 70
    0x5001115800b50398076601c880040c02181004914615010100c5c0005252503262013090012041c0e50406460020384034004103040d0b558480a41000c2c080101c1600d40720058604041c0c4140c3c0300d10700c4d070b44481c010400c2841040c0b51a030415407150390160050461617402c040c0445015010641c12218803907003040208032508144140b00141040c02c0000800c01205a440e50208644460f10021580700f0001c10107035100200560340700c240c51544850f1114001c010102142c002c1210580c4480d001040000500d607001655500560080d000500d594a6250045440d11224000540340c82c1000301c000265040950015500001400b500310220f0100c2d00020711480f002c0e44440030b00c1c0c1031188498140e440034403c24104580c100410086000b182d1144a25405074211702004101000b0300c9500401c02402110002980802c40725541d2641c1c072080c40c02403260100d0a41c05204020000300d404c20584d0170140511070040c00e00082400360710088900d02c03150340e10440309540302c041044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329249190 1250 329247940 329247943
    0x20409060f090b151c0c090314161203030e0307080a180b0a050a0318030e030f01140c0c1204030b010e010603050910020c0a0203060a091101210902040b0603040b01030204060b090906040c0e03 84
    0x841030000741c1d1f401c280c1500e50306125405103800240c200305508440b80803608080e8070f248070402c0701c091030203203040f1034002d06042e0010300303080350035403407502000840790108102d000040401d0292526450311083d504401c05441c001c441c010411503160401104a65900a501522801429190110300d03201031981071180c034007601c2c00813004500306c500c070f14019107028400e40c000e010080b8000c1001452241c003241e000040509140e12048000406024800c0240000182c0e00741c6140360036a01c55072843e0038072056809204c0c2c522842072141c00491554880e0144501504065000300208840384150340700940c452500e000146c4604010540161800c4c40480d228014003140000d503c003240c2070001000328448050360405c0101c10b10300307443c1080301c666030190780c110003000905018507101040041200b50ba80950288011040108000b61603080b24140c030b100751014004160b03101018503040c0510b03050303e940301746c5034000110b0a00740360703024110300e5100340783c480c40f200205030109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329250440 1250 329249190 329249201
    0x91e14040f090c090f0c080c160b070206010504060b0c1e07081e0d020d12090305040b042414041208070f08070507050306060d12020f01020409060f090b151c 69
    0x40750402c11511040240f24268440c500e280b0751710000070300c6441240d010080946400a2189822010210711890100c405409024485920040f150707440e0500b04000f96442c0d000f480740910a41c1080004141044d0350001e549480140d1401000c42c40107440a8003000181d0840070b2165109052000503000c8040118448100c42500303044c8180300741e00001c508000d402410a0195072042103c6006140e021340c1000c0e9241d2420000120030146107000c035058848c603889070860708804100071858031580e20f0000c02c404410a103103040852069816a05000f041d000032155020600003009003000032140b0480280c450340300070349000b5059031840c0c038980369090305945105001c9034a6080280070441d00b00130b80b900b00c00404041c54003800040244002d8003004040fa02c00301d1440e115603008004080d03005110f50f00030754655449094440c01407846204450302401000d20001c0c0c00480d504c20b900b01100c0151a0036403000e640c0c030303400350141c1c0301000f00d0654200300d0b040800082080c1c82030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329251690 1250 329250440 329250443
    0xc030303100f0807120201140d0c0e03060a05070f050a030603050a0308100b03040f1e0b0103050d0e04090f030c02031f05150f0907030c020a0605040c06091e14040f09 73
    0x45014181001c1001007030039010303002850b1540c03112500780a145e56480c00741e00840d034240b9080c1d50303a00400c0300410050056207003d48840c1e080040b65084113800509e00c58445005a00301c0e109a540c108207401928001d07914040456014031346030204a11035001000400802e046c080f0740d003641da07903c8a140449014007540011a10340a220030b04500102030001044620b60741800c1d82804c1d102c01c1c0004140e0040200b200e120701c2d603070500c400c5089a004042ca5000700d5940c1e03456a4034201641c540e0780d2400504000f501e484500b00c21841c1c20311621001603003241d040c400000455400740c4102c00104402d90b4944202040460380040070010391860b240004000b107031609080d0840c4c2d819042900303c1c503106040d20280d054050b2240454140e02c01220700e0701040c02c11100c078050f410580c40a2000d03110718240401c000a104a8607038903402ca0702580d54152005940b030b03d215414040d40c46a0340c1c5095400c5d00104005104d807406581201c200910009041e451407001200b21248400c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329252940 1250 329251690 329251711
    0x304031a1513020c16150c0b2d090d0207060315030b100e0c180402123d05150f0d0506012604020109061d090c0906070309030c091116050c030303 64
    0x70520040030010300185482e11b25040c144501019a03441640040b002800c1048084070031030314410703007100d1070001c0350140c0d10302e0140d0b400c3e0706024403280c0d2a4101c0c003489034003620900e0000148180320340b04004650390245110030803c0d08541d280c884242e23020304040031000c2050400318001644040707442c000e00740303003481a544581180000b1150000200c2142c401c510610800c06581302c2000c56035408000e490440340c0401f140394401100b085011036030102d2507400070540ca1100004d100b48000c0d1401252852904403200010940900c1259070103d6180d0742409030b00004400f81d048107400540504040207888144071402424084024030b8601c6080c801c1d06000c2507507006112400908130b640361254420700704034030440503030310001e2845015040b85400035600c01e14000680c1c2d602c9200030b00f1941d0340d2409040040005003a80019242158000e41c00111031030148158807036101034240150a0107107404103202d081ba590340065826004207410705d2143e80d800c2c00190700c50b601074071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329254190 1250 329252940 329252983
    0x9030d0c0203040f08011802120106080111090915011e0c020907120c030507141318020705060a09031d120a05280209060913080406020304031a1513020c 67
    0x44400390032a504d82d011164030307450040c5020400d00210030442c11680c040c1c0d485a242e128641403140140101c4d4030100179946843c480c6000c41c8105001416001001c541c502c2d85600c840c00e501172104615184c1a001c1081204807901d408600c43c60700016102a0400c04c1c0c83d05d0a46d000710b0001d80302203402c40d0001e0080d01813002542c81d90b101c3c0c0303040c020913464104902d00c2d0000d005010f10258102c0359251180105182803135000c1d81070150060b000c81c040807144130f200fa00e9203001070341250004507401e0240301c0015a0012003886003002594066450183c142e201c55600d01510100820f500e4004041d2559010310590802c0714003442e034400c50062201102c2c1c0450090b92104e031072180130307289452003110b42c05640d549070580d07000701044030f000c585071b103c1810700312a00881450003014928007050020b40f45801001820807240030300c4000f07443c4074440c8040902054100c82002c0303110078610100b456420446a080c04078a04800014940000c0411343d600e02a05010382850005018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329255440 1250 329254190 329254199
    0x70807030f0c05120c0313090f0b0306130206030a090203060708042109091d150f060901082a0a0909120203030702030a030b0a05040903030b090c0f040b0309030d0c020304 75
    0x2440d0032407009207030409000d4950303914503454001c844c01d000381e40701c030206034180b21000a1044800c025500f40b41880090354641c40361000d0841c61100c400703101d2070070800020038100825014803500f100155104408225820080184c1014010500c80c65890b5801c40050301e00f00403d50003071380980c83e002214901031a1000242c03002035000343c4500741c0407a120419940055090080d071380c48180c041345c00d04585402100f10311510021043d14032502c44a8420348400305005406201c001120714120342d184007e210111000307101f8102280d106481c00100b1032007010b20650500049a9401c882902490000f20b1000341608000c552656518000041010807008110f4505c10303030001d10700354503103910301a4403805821004c1080c551904c1466030b0a80d50302c142140541030042c02000f29031041c0c01c1c001e004100303551015002c1c9607410040341842c404e1b03000350b40d80340903801c0000307152a05105191031560405000a20030341700c140458014801980207000411031698029512940341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329256690 1250 329255440 329255447
    0xb0c19030c111516050f07032a0510050904140109020a08130804121103010c0504051306050a051003020f03010305010902030607030e0d0f050c0615030705010809030703081b07080703 80
    0x1840500303889003540340180e424030802c00c0c0039213070b10360100c4150304107108150802c41d08049a00c9000403035409a6103000c0200003402c0041c0d01700070328000c000f00c1c2203046448158a1100300d40612a40048814082c0c5401031040000b001a444054400724103004420b140c080c03e20420b8000d20031003500451100613031580081e170281d210200070780b020501609600c452590744030b2806010034030340c40742040c0c81c1400104644000c84c4100500200040c00c44030000400c6500940941e500c0380f4558005040c154605004031070136602c0013046003e1940c07810003003120400100c1070b0003041c9038003130145101c031400d42000f450003180120008900c20505104150401c0401041e540c189480c0200150f119840000c060303012074041d0401c2d18450b00100c905544e00d000b409404181c5100f00b0040080c4400c038559004440601076045500c401d07201c1d401944d46802c00c0342c0209203a8814046900403034031480c80d464102d0415028074034015410582c040c1e1a9005010940f55a5130000f0110100b551 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329257940 1250 329256690 329256713
    0x19020c04150e182406090609061305070c0c0b040e0105060c1c0e0d2102120f0a0e0607060b1503040b0f06010302130f170f070b0c19030c 60
    0x2407204070000c0e481c140040c8205007000903050845880d0445840030400000300240040d10104605402d40c4400c0c0c1e03401c1848002c0103c1e8524040c03100000403c00b2070405a030041d00a00c1d0081084040c0454114401c004050080c20368042050107104440401d00b10440500949035000301717181d5840c1000103450a211044e8803070b5029840c10001001c21a802280c401032100000391510100b40c40460308940040022a2030303540800700c00c2078030b4200300c10038034a003004817100e00404a8602c1c11101c00c1ea140c031446100002141750801100f6081034590000b03103004000d40c100403488000000c08940c098210080072164a41e072003000003118034010321024248000420501d00c0c0d49030554450207a240050694200c81d0404004242c46d070380243c041d01d00300c507607031130340c5101e256074840b440d0061113054460300e0080703401c07171900840010700441c401e204204120002c040ca2460700300a41000d61041000442c036004240001c2c0b09800c07000040140617001c0e42c0d40700030140050030203924031503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329259190 1250 329257940 329257961
    0x1020c0a0815251206050a1706090d0903020405061203041806150f0c2409140312060d03020f0d030207021906020705060913060b03041b0302030309090a0219020c04 72
    0xb00e04601c00d1405050090a040d603043d00b45040c03600c203503a080d0200050714950b000b80c1d5100c030350100b01103031b202ca154001500d035180c2001142c149485004c0450f407215018075599002440b0290184050b04164105a812940280071010780030340c0d140980342540c100d5086203503c04001e0070b2000d04c5994600401000e4100f02d5110403140001c9140504003e8030380c0421024007100300c11103814800300001c5080d030703043d40140010030b80e009040148001d100e521801c8607070440c0322900a0b06080004291040c015120851105540b02c090401984ac032446404404500c101d040d07030719203e20f0900c04510340d81e182da03d01580f00c03203d0b0700c10801c001d030644100c0301442200c50401c12075a58000341c81d0086440c01d03a00c256407407000300f02103409e41c400a40800074032801c2400005800320030381d00440c401c901503074080402d8021060310f2840c980c1c0510029606910034807030548185000c1c46a070307810002600006140c4080c6040e9564610307103c6081e0005070704a02c05171041402d09004610852 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329260440 1250 329259190 329259211
    0x6020d0c09080705091b070f030f03110702090601112b1b030e010f032003011415250203160e0a0e0604150603020904080712090605160201020c0a0815 66
    0x56040c038010891805c0020035200304110b100f44141c551441540403100403030f030415412240142c1608002d4020101c0680300d00000c0d250005502c1038810760b1050744c5903642d0040683e82c207526444011100da810700d008030061400b8030701c25900010407c1001071083c80d81a01d22102100d600d0310301a0600d04a410006440101c0b01c18190001394440ba008244a5007428941240c405d0054100c0041c200000c0d040c401c1c012041020b20703b80c181401442c125030403d104c0c83c400c0c0d4004000c0c07003107082d00002e090303041d81c00c00c7c0700101c20301001c003000010122000c64212006c5140e500040c0c46d19008402121400d00d041c4424040100c41c508410390201050406000f12882c0da003015540e410002d2001d001003e403c0b03005084024590040802181c005181c002181064204035449922040d02180c80703c0f01e04401220080c099800881295450740700c50b0305200b5140440c0c10010f288550890450003103406000e060364401040c113001d0080d0000502d01c081307001c00c804002d480c000e003c10000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329261690 1250 329260440 329260453
    0x12190b0402130e1e031303060e01110408070b0901050d020d0902010e040c0f0507020d050304082404150e0c04020d020c190203071203030e0715030510050a09021606020d0c0908 77
    0xa5040028661202d064220010040d201448003130078218001c6040c0300130368101c40440002441441e0300130500441c8150020007401001000c441d15610440c4a4000b0a403c088000c11031142690043c06c3d00400c1170400e18940720b01107102000b207900414001089a50329241c160543d40e03c00b44015441390250303020060b010000101512148112745170704100700c000510071045464044880130300a0784030017200c1d00d40d0307152040305441c0d8017074240a4221754501c51881000014440342140100d0f00400311080c1d0216103c102c2c3c2c06401c1c4400c548945201e1400407250540300d03403005090310810040016218600e035909039081c400c090b10b0450302031241c650040096500419103400b00c3e41d45070100c030815090fa160686c041c1845072014016030080071000121880403000760710002910b07582c100308940d02d80c565400c07085075034056190482c44514003804a0350a590081c224120b9080a9054200305503940d81d06a030321407468840501c2d15810038184043e04400034001800315040504030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329262940 1250 329261690 329261711
    0x1d010803030c0c0a0f03020d020f060f0c030a1b081009020f09010c031e020303010e071d060d0f05040c030b06030a08180a080f011e0603030c0212190b040213 69
    0xa990001510355100054009460303d51000e082109180c00c903404412040e010f519800c01a44032500700c5400d47c050300440301c40e21240c0001080d040e1050142c90b00d18952078450f41c02d00b0324250002052401b4850b51600642852000500d407540c01d5a005d0f0340b40301962810700800443d0001c580e00103100140140007800c408890307602a20300c40c500c01c4c03801610308034180c00c04686090030002035000490000300243c04480e4080010f6040c1e92005c02500344607251000100c886003840719802e0111140018421202d14005004010b0b02d440000c0204180e100010030500700c4005a40886a407042d254003002004414440c03e5400001100505541c007803d440b101124030450b40b00000f0142043d80c019403070b1317484001500140c201401128120084110b02a0003030500b6042c2003000406032103150800c0c034050107600292039140d5a0403180010340c3d800c1c092001c1d8030121000041c0510040c141603815808403452450307005a40d41c8805041c1401844022032003002c9a5040c42d045c06500d64 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329264190 1250 329262940 329262943
    0x307030317151005041e060e100212040803030a062106020702031005090307030305010e012121090f0605070308190902041503020a0e2701060803070c1d0108 69
    0x25030209100301c8040059451841c181c40d650030010366a540084002c42c2c2c2c9005540c004081d00c19143c00309070f8614040050a0046408000c512822000030050100042c65080401c808034821000c2d00480b152540c04010300100340e0000e4004481552010040214048c880d0003032344000c080b015800303407081c588540300101085000b04040c01e41038001030618119181080800300f4401c0b44c2004010500b4140d080396140d80c031020040c0c00207810400003180e840c00d00481c01381290b00c140300240654440b41e05840900441d041b003501c40c4084040781104000c40c4000804103c01d0316906c00d500030b0305003003000120100030340111041000c1130115500181d00100c0c8a9000407000061907442404000c80324060005151b009401a080c8060a85200360b45582407064070304c00c88038a8415a111020241545000c58000600c4010380082c0000b451002c4041260344030080f002155184e202c110390b038a103520450046442035280d100c204040e40c221580e0311078405c1c40210540c2d09500d02049213 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329265440 1250 329264190 329264207
    0x2180c090d08130b0a032003150604030204090b092a0f061c0213090e0d050a02150910110a0f0815150a0f05030c1204150f0e0c03070303 60
    0x1140152040e10707000e01444100d9040c1d4012881d9400d00c04049030311050940c0441d0041d40d4100040f0f0b052013480504549030280c80075505c0848842c2c0c1d42180d4841c03948004002100500a800220400010015880f0390203158609406030882c2861030030103009140c9400c3d01c000ca03200510166907250140517405130054a2034003011070301d041c2c0d441e09500010714544954410203403041004480340b950510f41c0e401410148484003c203408180e940d25005090b036644023211340d00d541140101c940018041d0740900425141481241c1c0d841242d03003100400c0400a0783e12907850b91103210105039008140c000c11a01d40b104156450604c1701b8040b000d82440c900c1d0b035a8509101551000983e2a0190b00b2644502d080003050034010740d240c0c100c034a030103034002d240c8080080c0821806104450103101180d028010480c00c0a04c0d086522a01c00e00518015004440d0055018544440d050f030300e020300100e08c50003e030009006400ca900c1d0520b801141079165010380c03c80d05080000c240c000011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329266690 1250 329265440 329265457
    0x203070f02010804080c030313030306270e0705061215120c01030903030e0a0f0506010501051c0e1c0e01020106140a170a0606030308070801140a03060e161202180c 72
    0xc000f05880c0e40c9030940e442c1c0030303001c1048450310003c410042c6a005a50003100d4041c000c0d00d04000403a103a0240c041100c0302180d0261030442c104d102a1420040c941c080076004141d101a1400240c0714800504240d0201d000782442100800070f2121700e07800900c00700100402102c056020012540001b81c0781c1001301942418155070b080c2d85001e05009400c03203000141c149003920090718040c0750008650b120410150362a20884002262550048080350701d8400d99800d6144140d190040640242200890155180c000c0e00b00038050100907080402182c01c0c2c03621050317074080041d0002401c46d400c503030200b02c5030341500061a12640f6103102d80f0040d2080061414002d0400118051800944020051085150890000616074055000c0b4010f14555481e001c407070741c2e80c0309038040d51030b1018107e0ba40121100710401c0003490651080440c58600c1c0140d4040945008001203044400d500407135000d04041245811850120b21101020340404005e000c2800d02962180182c0160350700d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329267940 1250 329266690 329266697
    0x160801090c0e07090e0c0d0e060c0702060f0f040f03060b0307140d05120403050303190e030a050918010305030301090c0c050c01110709050a0c1209050c040506120f070e070203070f0201 81
    0x4a656a40304420038805050305d00c4c0f00c8076860070102c2c41c0500c5944021030030308109240126a9007a214040b55031805407216041c2642801500e03008c128242c0d0004501224070b03441000460350000020300038000074405540c4100300a407440c20071000340c4038044c0c101c620980124209000140e002c0d80f900c60640d0f02590001a0300900d46052854110b14000a07688200c000c2030020821400000840c8244100400c4100108010058030282c07560384507552080d4200b807140000c2c1c80d00c51006000d508200610bd580050303440064145809808c1e0403d803000c0c1c00000040c0503248241c0074280311b420591900085100032074491304d40350f15007090054100403403041030308d00c40344080108002500f86e94000b0031180c100501c2080041c0100210a40860019144c0035400b01c61032180e1250540c2140182c0f0094425201b08001090003c084075445072202101c003400500800c01102490300c020001d120700c5040078582d00220348020024070031940304202820018007000b401018143c1d0a09 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329269190 1250 329267940 329267969
    0x17160e1921060608010b19032105040909150c0504030209060f1f3504151104080303040c090504023102070501090b180309090604020c0f160801090c 65
    0x54601c0d924158001c40500796900308040480c000307106510000102100b01e070040700808440100452034961440058a10b2131140300380c2007181062504000c0c40344030707880d10340e01c1c1079107820044045610b903202c01d458010078001110b0071445c3e5403003171503070340c1086040050a10b46558000307610900000c10250052800303e258000710346401280c8011001ca81c4045c0300ca40040d03000040c005500310b4030303034450203481003038400507158541c4110860a485848805c001c3d604c94542e1501c460b06080c2c510740c0540c3e07a0a0100606480308090806424084081d40da0380c107150500d0451032402d83c00c0302002514140a1200507038401d28000400c1c14109104009000084001c1a1a480c03640300c0d400204d00020b5a141081810b520079000b4034498010701e8419211040110303c028203640303034524a64410080d498252608022a80c0d01c514010005460451010022070030603000c41c100402030b41c081a411500010841174680c09821100002c10401200d601d0311192035841e4854aa0045001d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329270440 1250 329269190 329269229
    0xc20060105210a050102030f1509060619091a070c0806011d040303022a1e06010501030b0d06060609061407020105040b07021c0305030a110408061617160e19 69
    0x60140310310842d01300c1c00841d102d11341040c050400540c111503200d003c80300c1c0c500f1803041d840c054500a0040e272000e072400c2d09080b216031550021111404540050002482c000030b03000d24070052038140d20b41d02c00f01c100e85510151a100c7e52104c0c2d26040541250003540050201100100d50691800307901e088520850721035050680c002d20854030850303415007902d130b11a07502c4014002c804074030703420540445000b0145034041d000706019015804016820000040146610075041074550207801012110040b604d542c400c0308889040c0e1140010410f409401c2102c42e80041007060081c80c9800610300d48001035000820610560240c42c280c12400706000040d9101d039200a100341c409041c2180444801d4100a0000e81003101d100e000182000c1c0d1201030251940c09035400c9606950040c181616a0b00820340b03681c18582180c01082090107803507504801d414009400741600d0310201c074101a555000800701780c0d03003822403800b99114500c0355622001c42110201111003400711ba4803007007000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329271690 1250 329270440 329270443
    0xf071809050702070f060e1e031911010f02060403050403150204051201240b09040f241505030f0a0c05040504140f0105030d140c030d0c2006010521 65
    0x4603008420014500001c100d201500062200103a0f5100380469001c296900f601b1510b29642c9036505400c101e40c800c3c3c442801d40c02d00707546015900000c060764541c0d500d054504012400c400000d07615103010000c050200e5070402c0b0000c82801491001d0902c918144e03c010302203101d51301c00182032902510000b0104061681a50050301005185c40d4908001005450203029150585944031100080241100c1e4140110104442c0c0354070f851820100b2800c2080700500c4010f0039410342a403036402c0c1a008400c034038038901c1a9811044140071107402c2c010710a0940e92074072148801c1c440708205102c00d83c00101c6000c1d5020380c0c8400c0226903002c80600484090186a01264219080c9400c0e20f0408071441c003a50b10550300ca4041507826070b80e850405540d5010504107401240c0b131036003000601104600280003c2030000201c900d8940c0e100444822504010350b14030000d0000741e10b0350410500e5103c80d810845201000b085903504000c0050030000d0501900d04140f58840c20114401c1c20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329272940 1250 329271690 329271737
    0x14010902090f04060e0106050a0509090a1e05010f0212060f0a26061b03040f061410080105060d0308073203310206071103070602030d060501080f07 65
    0x6000d001c140c40303810b24850040700600e068904940c5a400c01060080c446014490402100c0d03004002ca01040d1500c000e0000700745010b00403540d24000c2501150103c0c2c1b031042100e1303142100360001429061907051460841d00d000452b580c10300e004024600940c00020415500041c04032461603098a00d003002038414000b9034811140b0302c40142c86204801840360f904124100b90324261070840d510700e052103c840c10740040ca2543c1c400288081000f1514140c419101c4a1203250300003080b0850b8120071034030440840b020700c98410321030004d01500d81c3c207000301608003100b90b812400003400340c0d8028040d080c0090040081241a0040b00e10710b903240c0c0350742c0302c6c151680d15841c14110049810f60000c2d500c01c0715154a90a100c0c402844800c0d40840010301905890030343ca42c0040f40f82d420401c03503601122003a40c8821420048481c2c40c0d41c14403191000701001e4009540d601000810741080c6c5465501c4541840340000c100001517800c040c056034000300615141c003044110010a04a628 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329274190 1250 329272940 329272943
    0x20619050c010c12061d04231002030a0c03050906040b091911030d08070207120c0321080c0901120905010e0604030807021203070f0e01030f020d3204140109 69
    0x40c00c01c584042e2407500729144c642c0100900200b03100c0d06444803980381080c551540e080d942c00304580300003404980d079000d120010251143c00050341100c869030f11032502c0c0ca100080210258000140914444688a0b0361445840e5081c240028500b5504003a110003005101030100c400000002c0c4042d1000d009114240c04840a8014980102d083c03111884400b802c2c024007a10440200218482c0545c208038454400c030f5008100084c1801300c040c03491845040226220320200001000003024100740e5107070400c510386818508510042d004000d072801a001240b00d0700100b050840b6640c3c00584184841e45880c800300d0055640d10b0f0041c01003034180c02544e00742c0260800d000c00c069200c2c00140c0980415401c5a034606180c4c62162000d00c4180e03002c42c04a0b2a600c060301980c2d000e42290300c12003805060008505083c00d9100041c0c1e80300d8401d250203680d4a04a280c0c210f0000d80450001403462a101c500c0402e0503500c41460000c081c10280c00414890810425601c1c01d4002642c02c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329275440 1250 329274190 329274193
    0x703030b06160501050109110712180b0408060603160f23030a140d03020310181b020a061a010206010b180d030804052109040c0905060708070b070804020619050c 71
    0x7680b2030f00b00315009220078042e1001c1c190510703107031180129900c8240c1c0d0b03249801440744600464560000d4401c03c00542075008480c551040009040b0b41e03030009440204800b0010b0862481c01c0d50030107040410381d100c0144001c0c00400140041e4401c110800c054600a600510ba1149024000c502068811040c240e040c803480443d28104a0320185290a50994008448507244140c000350207a0004840c0800c02045980d41044510003464414040d0f11414100103200446811100c802c0c600034018440580c1c80030744d462041000c00c1c45088504a10020410f8610240b040003c1d140c0300e0610440030345032408038807850003065002e54940034150042c000ca5041d482450080c1144074115015070703283c041c40c2c080c13490081003c800351240c1000700807100e00c1c0481940400000301002d2240604104401c280440c850329094014403c0368000c0c41000d07100c0205250040947c04010224000c10055409000c01612620140c0e03444000340024100d07180349a070000c4415000d98032050b10325 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329276690 1250 329275440 329275477
    0x109090912080f13061a120606010905190506031801020406090302090a020307080106110c031207060c020f0606061608030a0605030f0109050303040b06030703170c071a0703030b06 79
    0x2001201c0302081a401620740302e100c120b0f079842014451000f42240c0d030754001a0326240d44000181254007000416111440d0b60080c40c402c400401c0d01110144124401c6500c01814004a9070b080711000008140407030b0044180c80e2400c840005407925440361034001c0c0004004900200e0202092041c1e00b0860002151226620000141460360601c002d9000c1c4220310086000355448d402200c1c0704221540321004580d280c901e08980014012222445078061003229402558081c8605501240f0001d1456141c0c030050501b00708136941258500c00f5540544041c00f100180459688e5012104684513621003013200a40034000101c0c0f50020305d1424000108807581049078415401c1d600d0640031210700546d000300c094202d41c0b19003005407603588248001000100c0c81d40f07042c6d0b445100601500d414030b90303903951030400032482c120500c0c03154004214212440310801c003041c004d00d14030b00081035083c0c250503190800d1084282c051b00301030b10f6582c400301c6a00c929080700c1801c003034208180c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329277940 1250 329276690 329276693
    0x9090c060d1401060c020d17090a0e1501090e1807090f05100f0f090e010b030d110c100503040f06060e090a15050c03061002010e011802040b030a03050a050901090909 73
    0x10904045041e00482d9194004500c652103801d59400070741d0701804030a80c0f200c041d110308455104e946d01d1600040010041e194068445080d020700a00b0900070724141400c0c00c8000c00580070303031028620b04102550000300540c900c0b502440d42c00c020321030b130345040c004440e4805a0510b0f1840d08144290b50070b048001550722810380c03100b0310617100381d41e049010320785a40081c280f030b407060310580d03a108038040d100348851140d99101ca407014040200001d10a0701d820701103070030060740e4401d00010a441c4041030741000000c0c8001801b40104030381110a02840d0310000d42079000150005e01041d0116110800700201507220502408410304c0c003c80a1801d000c0c1c00340c0d1240c1d041022070741c00308110724403c02e41d052409024010003101c52111704540e6503005000041d20000c261204540d2204029403e2804c20310403040030400b0044030b03107440001c4e80180015942d01740040303402644441e00b1500400c4e401000d0f1402040e091608603030b41c800f014012034004c482030b045500c0e46841c0c80312071030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329279190 1250 329277940 329277967
    0xc0601030b04050c12070611010207020a060305040215030108070e041a09030d061703030c0a020a0b0c030411010806090406390e010c1e1a190501090c050909090c06 72
    0x502c41c61250044441001e804c42c1404002500107155805590002c3d406028160007025100c05c00c2c01c00700001400c02d24160000b4140c0303519a406000801c1d40e450030700c0700794140294440244c80603805020f10315403420f070000d65910083d1080c0701030003986c04049810044020b071000d001c000c04031102003241c1029600d4503200c1d404403d0040c1071901d403013000509120101c01d800d2411a031140514115524850301450950044449000b14001e0f00340c1e54001a1815244502804078062940d4a0303103800c1c80c200030012050840c450601019804000865561101c8103501c6031780004046120140352580c1d007200b440041e24581c8456010050b00b1504c07940030369008911335075907120460701c00818010b40304050f0140010303044003801c420002c800500340d03040c501c0700d502c02c1d40400710300c1014070005040f002003504e0011804280c00008031110925020f07580c09440300c020104100c11865001400c0c40c0300d0b61501d14003070289940000e0b80400c042c001c28a02d0000584215030b40c040284c0c150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329280440 1250 329279190 329279213
    0x90303020d020d05220c05060918090c0307050f031e120d0504060614010c0609050304050d030f0210061d09070e16021c050a03020d11040609060e191a0c060103 70
    0x4405c40e24107800071058903400104082040c0c214031104416410441400500e03440249103075040f68141c8050464080e440c50315a104100321001350200003070720030816050070610752200b8802c0060320745105203940c02107284214100006c8030020550020348140e402e00c1c4038401484400030f40030400071044501a00000c4c800c52140d1030401411f43c440c44030303183c00b038400c0180781d0000d500f11015800080c0281c0c8004070441c0039400f124204ce42d100d000524940c40743c2c5044000480c8050201030761340d0100001313003110046070805d00955003020f2512038804588030000070080d46410100f1640041800198041c01c041c15008841e49005880701810440380c1400400511415098a440d00084240446d19003416a40c15142c40300f403007400c901035007201c940211a103030381e0416603000030302280083c402415552903100525103881e50140540c0e4500304031900503504103040300e51030100300749505c00f50360f0300c24084a1150b64111901143c0e0107000c070401024414400040148040c0101a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 329281690 1250 329280440 329280451
    0x6150c02040b06030717040807020301060f0302090a05010501020d0509010509030102220b070201020d03050721060f08061e0c0417100c0201140114010509090f090105220204090303020d020d05 84
    0x41c4003000102c002e01c055480b08030f1754000000d070a694400b00701040d402103581c100340039140b00c1d0309041d121340002c1d003107400c11350015050880c0ba250400443c20200003140d840a03246000300090741c5000000703515040d1110303040c0100140002c032103945030300410075120b8050b000340c021500c42840c4800281c3c3c460406a01c054000d0350350800107992691041241d03921941a4041c00000d4030700001a0040d060181c0707963709000f4048685001d1030414001d1160100d8404c1c07011508601e480d100000c21a03858001864a030810010007000410003040d0100c0e07018100c0c41e01e404c95503036101c500c0d414000d5411503019a101d4a20049024031700244840d20710140d001c0400c00c6c0b51580c1c034260b080781c4192181c65501803a40c070041005c5054a07403555007444041c18490314288031180042c81071101105c075071003001d883d1801d0042c400c209101d050361109400e44941d440b40c8050180c061000c204040092141d511260344108051083d01500d524441e1020700395104c41014000f0409454111013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 329282940 1250 329281690 329281699
    0x40e010302040b030304150302090d060207050105070801150512100e010801020c010b0f0906090907092a0c08030f07090f0b070b0f010522020c030406090f06050a0e06070606150c02 79
    0x89034689000310451b8201c0300e030b00410800c080001d10302a8069000010300c107900240c10359450001c141e07d4002003c0280c032070400068036142c80c00010b0321030310041c0c00844681c00c0c86980258140e4110040700c1c1109204998080700c1e0307030f4002494014080c140c02245405200c41c0002502d02015000b5091f14074541e0001c0c40030960000c240441400b201007030b141d10240e4000402c125003410500303142c10100c09421f941c0c29584176600001624501c2c01d102501d01c4021000c42038406210040042241407450308090f1b615240e1100c03000741c000507101e0a404031b21040030441450203440080011b00f5000004a81169507074104200c81e044410192040b400400000b5840c29180703003000e050b29001002e090551115603886403030a0070b280d100f2407415508028010401c10100080c6c40280070603550b10041034145030346030024026a6200e00140201404984c1303049400280c0c4858001e41550f500380c0b10070590920707034090109940b101e0559850100c0e02e600095211403c9100640240d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 329284190 1250 329282940 329282951
    0x5060a1e03050723101106010f0f0801230a1509020307030b0d170a12050a0624080403030e0c0d05010c0e010203070c060c0317090a12030207020d0206130b040e01030204 74
    0x911410700e005036000b00150b04048141110241c1c075105c022840948100d2402c2160750140001c0d00d0b14080c4280c01c00c1525100003c81045942140581507000d044000c00a03c1a0f4601d0b0b03084940e120034403901842504076000000f0708058040e4041c60010340310f00240d100f8556955522070007941305603800030000b0b080c00c04202e85420501c124048603580729000d40c001d0b00581d105580e494002007600020440c4400301c1001c00d4800d402850b00410440c40c000811031301e00700b00d01c1c61403800221810400304c07401000b0000c2c40d0300000c0c103d52254060801095220350390500b01c4c00c0040043c9095840780c080d11500742806015400072524401031b440d11547e5010a0005980d81c0c02014002000e02140b9841484401d11415030b412800d0711a05218078061512402400400c82c00c858080031948041c2804c2d0500030350b98200004018142401c40c41d0a4064011600903105068003a0141c100090414804601d040140c4020282d81e841607482e03a44545110705510000e11007a4812410227 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 329285440 1250 329284190 329284199
    0x60903031a150f1e040807081b060307030b030a060c080c16081e0c06150a0b0a03090311010e01050f07210903021006080a0c0906080a030305060a1e030507 68
    0x5000d8400400040074040c11801480b84405564048920b1044007a02070000c51003000402242d0900c82100031030311501e03181007070345180c03070011103078050709683c0d0195200c5245c41c41025003550003101c0a80b00283d407641c0b1004107030702502c203420301e032501803148486030814410281d01061140203c0d5a4402ca1500c480719410581c0c01048440c2c070803802068803000c0007900c03207801405c02400e14100008030802408044140750440d1541c403001c0c2c0c11090402c60b0344031444a413801c80308021101c2c10072035814044a070703040340580801c40c4141540c81d00c0140605014112004046601d48000d0101c5454501000d018103130655500b2081105040890101030081d6054030139a8080c1c0075211907000d0113031500c406040c502c00103600f50b0007a0140044010098001d20025000d40b0f80102040d0b0450f1a100021100e281d01c980000c900e0103070140080e64011511078085501841c01103040d860346c100040c1c0002039680980d5104140040f802644001c100e0404100c07030058007562850780d501e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329286690 1250 329285440 329285471
    0x40510080a2d0e071a0705010b010f090302240c010209010e0d0f03180801050c04050f040b09010504020901140706060e09011a06070f170c07050303040806040b040206070602030406090303 82
    0x260301c03240300c0300b07004004920090040c03035000c848040541400c640390580d5412200d800044201185d81110600040101c140942405000e080c20703420b103040d42603100703208001007105582d070000070700c104400c407007140c1c0714044c0303d84c13003107403030266012156580d100810024004d41c08140ba0601045850100c2907440c03510355134035100d01d03030170009400319405103070f80c203d80320b654141d00441c0090108002146a180c2403081c244503d20400f4401c0d0342da800e1404200c59128007813621031185080c1030810031903072540000fa038110782042d49c000d40c840300b00500688128200381c7d0301d0111580085400810310010f500003a0445a5156080300b00f0b4503208645400e0700c0100d0b4981490340c4100d60700803803a00300140200442405407590300814030340d960700c1c3c0c0866250031507400040c1c071380840c0038098a8400c1c0013810042c2022001540341a00e4100150b468010040000d444081c1c010006425911603a04946600364443c100310f503a8035141c90100c1c01004142000e83c0021300d00030b0035080341001e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 329287940 1250 329286690 329286731
    0x60109020d11160b0705070f0c03031d0d11040b030115050406410d030206070905010c0308010b03090109050307031d100c02090709170708010f02040f031403040510080a 74
    0x101030140700f40741d0009488200000f0009402ca0040000400601021030100820850301c544030f483c3d61840e01c0c1c99824014181d07080301581c50324010450f40d01c5082551008000156540d102c0c100e00d9000c0454000500100605400c1e640c2650074100c04100f0b140c1480c81040948408450801c2816103506c1070302d40d0f028176460341c2808071441103002c54284500c41d00c1001022642cbd08203044217502e4a000c20b04000c022a000c40151b07110302e0901c610540c000011801510003807038010300381d07001520000c0c0050010310a54921000010120f00d0103038080d00004401d50b00141100d90314911458010800070b400700010556005400b40e644440c5019a0106c8150100340d07101d003118843e80c0c08202147c00301400c1038080c440030a40000b039065515845070301196020024041081ca061035890a540c01c8803d42c01000d0300c104420311500a00c509010b06807904003042000410440200910b144503907007003141e0020a4101e182e2045030710082103445140010014026003800d403022041190 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 329289190 1250 329287940 329287957
    0x30406050a05060645101d0904051603200d080307051812010207060506031c051c020f0714060103031b060605060c030909090604080405010f0e03060109020d11 70
    0x4000b0000980c58080304901c0307100e0403217a001440c050007003000040701483d04404c080e9489250540c030358941c0d480c250494000c010030500709041030200c039080381e9211410101d1414401c0e8080c001040c1440420011a0201d40390140c00382001a124140131038180001c0c042e0041058198810f900c040c1000f05420030880d0b0300c00717945405d545032510140c030701d90030403021105180340b41c0c12a0009079603000102c060b9405a00b000503605c61083c02c0503001d40740c00038406070099212501400940c00301200c0180d542905142c40c03500c0306501c0c8025041d43c070010882c01000d600100c0d0b5101907145070b03002007071010311814238240219103801c01c03151254424403001d4081140b40c03091041110514103100794082c4110360000c0c600303481d40c00090068001e100120102d03800400d00506900300200c280b90414000390061903245816a641c443d540305900450f41046000300840d030760207008a03902c1c80c16100060031746150350703151110700000b07400038200f07071032110305010100c100d00c60076008030340142 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 329290440 1250 329289190 329289199
    0x60103021009061e110d0e150c0d0302030603150702060f090a0b01180906020d0213050901030506190e060415150b1603050f0301170622151e02030406050a0506 70
    0xf6650b000707407200006549202d41c070a00080a41e19240c0030300c1807203d0f006079111038841c041e620038404140070084600002d049007423034041151a800004c0000c0c036569098942c980542c1e04ea0310078002c6400d10141701485103801e10000107100c0d4441c0c010038420710511094032801015070b1503008113580c418070420007410025200006000b001c0c0d0303c501d905c000910301000441c1c0e0a085a5400d07003264010541070300180c0e030114078404110314240842004107400c60f01c0a0a55045071200390b103d032070240c0600290f0718030301070b0700c1c40000e07554008006020103041510380918240c280030480024041c0034070901d6103090096911411550321030400d48184140c0c00b80be140c843e082c426078820744000241c00b400024850315451f60b075050700944c06401c0030780b030f030f03088025132a00304034a850005404240ca45003202c0894202c003c4803042c010040742c00c003138904003502c0b04104072801450b202541807808840d00c4140c44020302d10360001d60140d882403000b04003650b604000e050031030300150b401541c071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 329291690 1250 329290440 329290457
    0x503010f141b09060409020c10060510050d11030f0703140912070503040e2a040605070327140906030714060a0210020307031a0f091303090504020a0206010302100906 73
    0x752081060b200b8201c0d101d569001c0ca0728405800042181d007003940800c00c421340010710900303a45c00c284600b180058110405101c02401c0c02d00150f00f214810000008101021658a110003010381044d83c0f048140d041207a0369050881c00b092001404851041c046418840700049010a180389240f0070135140010300f00e216003172075200410b81d0001c5425070700c070320041c40302041840c0034114980c0070b1802c0b6405001901001d42480d01600580b20165840b04400d0008100a03034000c0100c500d503e0f45032801002e0085201d0094050f140d12000824085e9406000443c0d0444800603d00c1d1400041710181d0340c0d44c0c1c407101096a2803400e0700400b04858950000b0407840d0030032002510402d81a401a120b20500b8010704004076001155814002a00e4801128145c070070420740810840c801c0e207007a10040301c40008242400c1014044490440070003036080d05062159a42c0c0001c0d01c0000c0055640720f135010303c025511142800160b01c41d2582c1d1314400202401030000c6001c0704c8660b145e02e00c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 329292940 1250 329291690 329291701
    0xc06180b0a0e01030b06160309120c09090f0614370908040e272a0f03121b07121e1b09110403020a0e04060204030b0c03010503010f14 59
    0x250b5210340000c0a06154503410f01e074406640e0100030705801c1e03004c4080b001d4224000c2c10004e040345080e91003a004103050341c0d0b05101041003090740009035101c071300300820802018500310041c520448409030801e8501003012400000f20b0100078001e24543d20100c4504004400710404034030030b001e403540c80380e070394000c040014007140e084080c901d03004088107400c0076503880091406241c00c840d07d821050300021140030a89207626142800014140203113812004454900804901038044594140100040f01c41594076813080c0c0e00d4a00000d0160381c582150070310070302140e801002001401d244054503015000b1310000b500407c03140000c1030040400d120340c540b00d48000340301800400f258841c41c51540851204401150704a080c240c281c030300a0314140400048a04050f0007002541c400c01c01000980d4071500080c1c2a10020701e039907050780c0c80d01d2900c00300078415984010001840d010401050040c411f016504071001a0700920a54401d051803004980c01d40c030400c010040904045031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 329294190 1250 329292940 329292947
    0x91a0301090c030905031801080703060e0f180f010614010813030e0406090c0f08011a0d050c0c0d1d180411130e10140c0307140d0204030c06180b0a 65
    0x111049074a0a00013450509038480e1419603204032244044461111160341070341d6401606140e204e001c03440c081004605180c951105550701900d1411600a0403011501c0781c4c408050700014a4034640484202c00380c1003001340c1c080d185900c51101c5081c44280008a2540100c03c12031141c21503407442c00da00b010380e82d41560240c03140544d141e01b15a446802060a60356442005405051511000008009044010301040c4140c211030101030b10b001100d841c02e007000042c0c5484449010022555907681071a01d81d090194a00134450303446284421096250089600c0c451540241340c0245100001e0b07003400340c1c2c2a10319111056004c500070014000c1141e8104e404c10402d0010500800820f481c00d000c000d65440125059031900004100c110b81e0038a8850620798486024070398441707140c918200340e1a0301004040c036040c04084080c0740340715004d41084580c0201b61140864a40ea00ea04100a00700b00900a08001c01c200b04e01400860040c00200d0040340d030040c0900d45000b1080d02d049 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 329295440 1250 329294190 329294201
    0xe01060f110309040203040807022706010c02120d0509031510170a0c170c09060f01050703110319030605031603060c091a09030c0913031d040c0807091a030109 70
    0x401c0180030511001d00030366150b000450059018a510584581450040012500c074510410b40030f20304202680441e4804058120b1707020b0000d08104003001528008218040c06c40940f82205000d1020040c0c09960004040d0007451006e41c1101e55010842044080c02e4030103442e01d442102141404010109003c8480b0003034003448819100b10700d200b607450080304029600084071071030300b1510410349800e041000c45420f80c01150015001e003000408582491500210281000030008441c001e05004426083c01018040200c1c0c0c0c0d600b0f421403800c502c403958034030400000f0b820098009118900055614042c81c0b50245e1215607070324565821008082000c880d600380850514001021103c03400302c00c1a0710140440c5070350720700300306c000c01d41404011803003280300d06140d04c2442000946c035924030b03800651500b007041a10503005003449020a6541181d0784c498100800401c02c20351090b0402d010391034036100c1c80f40e4a516802a03c104020a04804030114014001001004801d0f00039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 329296690 1250 329295440 329295467
    0x20a0909231f0204181d010b1c1407080f1e0606041d030a020304090c210f1107050309010e09010810022a061006080f010314120409150e01060f 63
    0x5140175503030040403000c1d1202101e80d00d0040e559003410407658841c0203d4410a021280c001c01915155800050214030030380c40e40001060600001c1c01000b03d40440c1300c0481c514141180d080303550724124640d50340c0d00f010f9615600e008400740d001800c800800c0b030801006a5002920315036442000388001041c204a0301400040e400f1400515860140020002d00a9690165640c0e50074420713444e05079242e603442c01c0100f0804120310400307440c000c00500c6043c441e80d000804d4400302d00b0b450401400942070141c80c02e5400103080c01c20050000004c1241301701c01e80300c00da4036074421420400c00103400d200d80e80c1650045d00001c4c0c5680507035030080801c2185c40d102c1e00a40c2c3c50301c2000c02000040002411980da00c00c505118285446a5811000706158a0034407807a15010b034400145441c117103c010405a810085030380c01240034004002d0020031076800c40d8a0720703070302d16501000c3c1c44254410210b00303020007070104440100c1da20b010b040c1c4609440e807031000c16694130103c41584c00d11b0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 329297940 1250 329296690 329296753
    0x204050613060807050a0f050109120312060b1b1c180e0906040b100501050d09020616080306010e01140a0806060c06010605040f060e090106030b010c020a090923 71
    0xd214110041c41c07040d003000c3c00008000b8145141403006110000700182c05c07142d041e0b074554030108526a4407144042c00d59034060681d00a2000070b19090f40ca107610002080c680c1c0e03040401c0810710925100161030813031454003507079000c003110008054841050202203220400400701d2481c07858003500058806104850036044510380d6a214000880c070301350f0b160712581d0040801e000501620b2400c1c141c0110001d90b81d0182c662814002920a2113220049154180c07206003000c195a075001c2610001d615900810320811400d00d4000480d50040b5145800700b50070035515138080d48038001c42c0b0b03040c1000d009080c2c40e0400807401603032070703d00050807698454820407654505d2324051140714000c000c40d4403801c0c0c0303031800c02110322506140c9811030010007801070404012942d884414a0449a25007800a40340b0744c8070004841c030b5290844065002407802c000069000081c0d402006428002c4c00000c007440026012180101564201100b15520080c0c0c0c0100c0070584100981c82c030700da01e07032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 329299190 1250 329297940 329297959
    0xf08100303210e01050a05100b09151605010c020d050f0306090405030c0a030201060806010611030a0e040204080a032c15030601020a020409030305060312030c040e1b0f18030601030b0402040506 85
    0x6846000d4880d5081d8003c11651100240a018043d900a0315045050700301490005824804400c0050041c0d0342414415514003110b2030950b0b1140040f02c8480800e806003040000c11800c220b406020104081c1005110361126500e20750721441c140c070307608a40c00000a1464440001700241d80360003420a80b2603000c02c02c4100707005807040188020f040e01c40c2d00081101031600b000c240c14050140c0c003200521101008a520702e8001004460980d9040e0919a03c002040d0000c0ec0003405990000e9140f0300c110b003030502c181a04600941d9142d4004c03200c110751311241000e05940c00f4022407045401c40c440c01074030003050420002a5501c01c506204542c1d24210b42c1d00020709480040805038007080c1d032601400590f0806016000402c03c1c0034800c2e41c59400d10409138a01d51045100b2a00c00c15034000104410402c00c0341d112402888007001ca54070f036030b0320b001c04002c9680041c41e0440d641c2054900c02c07555050200711681269000010506c15680c4e40e0240005408000c0c441a401003808 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 329300440 1250 329299190 329299247
    0xc030d0203010e011508060105070602071b18050a060303050a0f02010b0d060504021003050603031e1201030309080f0a02090a09060f060e1f080a0305070309030b0a05070f08100303 79
    0x40c8090340c02031144201a5290313500d40090816001d8030b0b0090402004400004c1101d0750b42c00c00100e9140643c000741c016a0b0b0300c0703a03090410000486d044127038423a1036038640000d0200c0388001d201c4002c5c60b25500070421a111030398004215905480003e010550078001e000d0564050030500c12800124000401c1851205c4005107441528800441d409940c0b1800d00055081c0100307100000d4800f0f0504122600340800000d659008081c10b401c08480107180181c0300b688900140e4014207000f0100180551712890b000c2c00d0314860740100c80262140d0b1150070181d40d1300096240c5001d8010f81403a180c0d44802c208600504005030b002e413070350713600c0742c103207454190543c0708510050501c510508181d041c44844003000e120f8142d00411010900417082c01000d601060f84280c10317a1504105d543c0e00c0682c0780039242130780c82c1d5001a0a00409000b0408014402d4000a1080f8861340c3c0e82c0c44043d060000c213540345403054454178000c200400c01400042e0080b100703001800140991130440100c039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 329301690 1250 329300440 329300467
    0x60c0503040f030c0e0112020d060203060312030f0915010b1806250b0c07052a1f02060a06031e05010f09050a1b06021203060112090f120207060507080c03 68
    0x664000c48000e0103144c4200002c11040455034051324002c2400348065540c0e4000401c0d4564200d0041c0506600001240d0325540c2085000026006481d030b80703032030345130006814101150480e80c0030000c0c0031f0704580c1c0c048942e001c07603001d040c0e500e035095803801c0500e150440c050b080071391040b442c4c100d0b0003081030300110b842c2344a11446c407015203c079107010420b103403070303c60325520f005498000416000d2107070708000f610205401e0701031010000203444540610039449a0131101018141d00200b008407200c21078900d4600300da100380242e808031403160b201c08074000700300c0b20184000ba0240200c14090a414440d103e141c41a42e401000040340c42040400c0f040202c07100d20108983c15840a4003840401c41807104100114030b8240410713031001d00c0d14402a4a482072580801c400d104004002803a982c00b0300c1140b840350b00003110410008000d49800849110008401c0d2458402c003040030b000d0a10019001042d10f00c41c1d540c0508201856980004a07040b0a41050700d41c00240310113041c2005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 329302940 1250 329301690 329301719
    0xa02030d12090b0901050711011a011110050f01030314031006030506010e15040801060f140112060803030403050c151b0d02040e0708041e03050313080d060311030706020a020307060c050304 83
    0x9004c0000501810000406041e0140d0140800e200364107100d0302482d102025864606172a00a08208039190401d9200c0d505100041840780407441c03070441400f040d40c255030700c1c440c1030300d10a480f076000709401c88540c102c89010807180c030314440c2440182446224800e0b00020f42050f4181080300d586181c0400143c210b40304600581607203d004641008518024007500004150801c0240c2d0304a013490460040b420b800b000301410300010401c3c0492803c0240e04c024010581807003a26200d040c10320780201168840c5040c440c140c1b0801c040284410300182000b80a0200008145040300046200d0740c4907400800c01414520707800d01c80041c540900d40f00591003000b5a0ba54100c03149414030380898140800300d14030900b0100b10048100081d0031108503508440003c0a5a80e22215884c10002d5880303113885a191036400c000d0000208030f01340310808010081201035a403010303101c1e03100701e0340c40d911890017039070560203a8402c011b0180a01034181c03074240203404cc1c0340f8054075480c59003038240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 329304190 1250 329302940 329302951
    0x60e030c0129090c0403061d01090302010207060501050f0d02090912030108011d031e1810080613140411061b07091118120c0409080c0601080a02030d12090b 69
    0xd40d24001e06242c9204645840d40840381262104014100905400d02c40e002d14040100190358503030f03c04881100510a5900440300413008ac0a020b2091800038040c1d04804000c41e85281414004295441c0c140c1d0080c030107540c09043e4404800842d000c00000320405029451035000e030b43c2118100341700100055001e03150f00c03400818040c0284244800310803e01c094081c05410900141c0d02854620581d0107455104420f8103859412080e030a8500c6095400c459a100c1d8400303111591498001c824540f040804603195160505a0510b01c03050390304a0801d4128040e603100020700080560029200c22040502024100702007940209901424103007200c92a5001100070001c095450041e00c1c00c41151003840740c00c0040d80389000024200b80c100d02442101f526003540d640724000c10071510391000050083c00704031414200746803e580400a1610780b4041c210001c50414000989405c0c071580c06801000d0400001e070342120340c508000740412071580c5812401d00482d000484a50046 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 329305440 1250 329304190 329304221
    0x5160c170913200903030d0c020312040b0907050303190c06110703080414031204150e1f0e070807050d0c0302040f05060f01210905030d050a060f0602120403060e030c01 74
    0x4030b140d04000100d00c0320b80f20318201c5442d080020f0101c03500c010050320520b02150320702040034445104183d00354040e807509040d400c40c0080400082c08091161217015480701d400b955a061380321401c1c140c0703e02c80c079503007200e5208119100e01c400601c00c14040140c5801754400142d80001a0780c250456408000217500280c00c4200384000e01802e19444082d005455000394079228001c0c0914122032001440604401035184142d017003170140b42c220507000c1240030203480c04e40811410201202c0411686844442d1410b55a9509610001004803e680f5090010003960345088200914484140002c076901c0341700030800401611036001e001c00c220042d61010840345803178414403e41c040075210f0b40e81002440803200a54102001590495049840d408140d00d81c107414000d203140f0995803001c444070720304020012807419540c440070940e81c5060016032000d40e504c0007240d64807107245030000c402d403081008100240003a41711460440c00354040d20b0600f07036010259230846d030800c0e610364180e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 329306690 1250 329305440 329305451
    0xc06200723030d11070b0301030b0408092205070f21020a020a1212050609060d030f1704080306040c090b09040b0103060308130e0c0406140d06080303011805160c170913 74
    0x120041170100c3e1000c1c0031a5000d4070f065614645034000c0e03e00c80980007500003900040c91450b607407214132901281c051707180141030307410303c80d24a400000e0004480d01c4000070440040c000800c0d204103c030b40e141824200e4151807044188090340000d50000200100390300c2901403050025400740201400000207449003000304c0c0c148240003042d03440003405103102c2ca61203010041d0564901805809068252920441e00c6100c01000c0c0ca00380645500c10b0714045480c004c100030004850011840b642003a14103200c0161221000d90303050000b8001e814041009200c440043d0a06038032441c01c0f2a014940811817a0740c80e25421070a5009440d1902c03440890002172000d440c4188080c0d0f001145108494501460301d2401480c51398215141c2c120001d000402c444141584e41059001e06120001d4903500c1d40d4649007203500488101e65801c8490802002a034410460b00d5040324821050310340c00790218490703696034455115140380c8442c5403400c1c480d0304a2902e40d0142d010380d915800c240041e0b0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 329307940 1250 329306690 329306717
    0x6031c022107050a0b0a15080303061201090209070c03120f0e2a040902040f141f060c0201050a02011104060309020406140f090a0603020301090c06200723030d 70
    0x41c140308204001c20a81e02041628005031000581025040d0031020307456150f110b80007000c018000c03040c1c5608590005d803c01040b109408001140500c0c0201d50f00a00c07030320105e01103800d0390030550020f076005050314001201e036402035400012243c4a8a0300d110118014540282194050b040c001750280c0e031142030180c41401003003041d42a4410400c100010318105903e02c45911481d01d0b1107005903140c00100c003c6407200e8000f01e14020241d030045c0a90103240c0390342e00041c1c0048808402003040c3c044404500078441d0301000540c0d6055480c0380150b203054006480da80c1c03204005c441190750b50b14000c5d6043c0c072608090000307403445580206000c1c08a0040109032001030304049040c0c3c00c030400480241d56880020007d041040da44c0710440da0b28404034000800d003a0340041d4265081040300b40400c551a1221021384101c4c1e21640c0c0e041e441d5984000786000203078546c50241e0300c03406080c40300020840303da00d200c41d1300c8807007070b9162990400482d04081000070610b0104250308104407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 329309190 1250 329307940 329307973
    0x3150b0936060c0d020c06010b030403121a06070503090a030503040510051206100c1221020a0e010302090f130e150903041a0d15060305060301020c060f06031c02 71
    0x100c074845880310590520918200c140c0740c44000c2d03d894100f02d40000c1501300f01820350180d41e210950030060381c01641c0d6408680d200d03a070084804800017100643c0500da58500c901c9414054108412902600c084040c01d02040b9842000c0c00d580700d100c1400035504c2540d900c0028809188204080e45c0c907146403000b4002d45244281c0340030140702c0180000f030b032443c112404213980081704503210100c0f42c40b1400d09607092605000043c148551840d05c02c0c1c445500040c420700b0440290b0b01000184800c01e0030340041f0702413300c450001809544140c54150300c07a8000d09890341c1c000786521503082d26440005c2c9520300d5a034064050071b8540e10140e00d401000d0142c01c21300f034441d0840c0040c0c0e140059182d82c0f02d101d00c0c010208150320104052081c0c04c0e004082c1d440c540064141044100880341d07503140400c80074401c00000900742000540682818025078a0180003540240074030303100c041c56480c0c40f640060504c1e401d0310600d000c0c1070700302005201403480c100c42d90b006440031594102c0c00c01c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 329310440 1250 329309190 329309251
    0x10608010b010905011707170f061309020306040b0c040f031b05090708010909061e0e0105090313051212160b10123002100f050603030403150b09 64
    0x20342c18030503160070400c01071760400d05000801c8500d15030329100b540e501e00d0079111510104015500d000c8500304122100f4960925140151030480720310035078480c0c40010707005643c40000c00a405400c100e010a0010ba40b1031181c0f5000b031000c0020314206601c840030b414408405a1096800c4001c0c01018034030740c0e0082201c00094070301035440c0ba05502c3c01d0807002d0316101061180e121240d039140c030840b00b4000150f02c946501c24085104541d080d003030b02c0c400c10140100046002c16075103400d000c0350b15204000304503004600400811003415140c602000f01d15541144c6003000703406140380c151030b007501c600c0090914100806682440080b1420003481c1d00318003e01400f504403003030100f40035110524050124240e0300008138045410040341800030100c2c40d2070507090314200306c10700241058011601c0c4c1146080b20702e04100c520804a8801d003a50801c2d165250150001c0100340027160f0740d488138668104170014040713004003881c40415030000c01120313002a01000c0c0c8400440750990102003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 329311690 1250 329310440 329310461
    0x90318041a010c050102040306140402010323150307030b010306051009090f14012d0b090606190203040b0409050711030a02150907050307230303161205070b070201060801 75
    0x104680591800c11807250380101c00558107008004502c0307030412409404440140d68842d1050091500720074103101c5480702958101d02107402e201030501c0390441c0300401d050b480200c0c62401c220b92241701c03403400b01491800314182c050103506008004215929207a42c0294414480041d4518100075989403118103500a0000d9038108062003010411410703040754415008036502d0740010140ea142401003414101510080054403964914101d20a15420540c0c44006092000e0494a0208907407401d0441c0c3e115405202804110401c0307268500c41d0f0703580c000c9401264507140e110740c004071a0b40c000d136011000d0301d601c07002080801035100d00c1c2c440440c8404002113041043d21710003e52600c001612184c084c0c1141d01c0001c03001d880403c0b4000041c00080c0a4600d003d485404044100544a0407c03001c041108040007207803d0000c21100450700f0140e07100c80d88170a41d0355290219405500250030040d040c09180d0100710b00740700003406403503941c0001880303070710b420384803170a4801d00c500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 329312940 1250 329311690 329311699
    0x921170a0f0525051e0d0203120403090f14010e010311070b06031207030c020a05060405011202090d120e1302161e0f030f080127050717090318 63
    0x3403090510707000020a484108642012601c6210340a085004049003800842e0020078401c2c540050003400700e01040114803215049410180c0c1440c0d442e61145035009040c0140d20801050b019860f101041c60740191091078540d01c0d00e90313210303956a050600707071300f220030300710343c1c0c0109000f4a607042420481c92100a00707060015200f0038542c10860b0240040c00341001103401d00003045941c0603c624120b2400b400c030101cac0c03184924203005182d041c600703100303d0060300031031008181d620b403039010b540440d0416990490040c1c80c840d0490041c0d000515103035082040502034400040d180c1d1442a042c040756038a40c58440418400c1000c0e5085240c1074020080c4100103a44680c043e00c60500e1000341c00400d0314104850400d52201502c0c41c0d41d01c060814904003120f5410036500c919801c554440a9840300d803641d80303502002c0a00e035809119000703902410041e4041e070b04003a40003154001d14a09045142c5c1d0700003901d111400c1c138107d8007000d584e00006682290300080c1d021000701c0b050f041d40d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 329314190 1250 329312940 329312947
    0x90601141c0212030f09030f01092d050a0b241f020a0b0a02040e0703020f0d0e030c0105010e19110304061508011a09070c0203120901092117 62
    0x1c41d18440e07000400c19815440803076000300350340303488035900c0412040100702d0359503424511403840c09403c0207841328400d0043d41c517000302844050003086212070f0001051890002500e14103e102c04400b6803c103483c90562a41501068092050941d02c81c01484009004c1c9001c800d1004068404c6080384010b044840e6504016101e40340c001c061030f803c140041c0280310b228042a8a00f01c005074004052280c10810000150044e07000340c803c54500301c00e160303841c2d12008001d0b4181d0103103d07061070814906002400f0742d03c130160002110542000d0540b441c1c944914401429502d09800c0108440000300c20300a070f100b41001c031100500d480c00020045404443d904962511002c1c0003d0203058850348415601c4c81190240c400078445080204409006083c605c900705800c44581403244410000003069240a40410b03811258004c010f00103511054912048940090070000d041007620f60001c1051100355034040a42c0602d07007051200c8503c107142180e04440700ca85914143c1d0342c2031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 329315440 1250 329314190 329314229
    0x18040c080417131a040602210f0904060308070c030c2106020c03040803071a0708040210030518010c02071e290712081905010515030a0e010903020303090601 69
    0x404003211800d02c80d0302650350b80c9003003060000c08050a030030000d903008a00710307051200c1c00350800070803c079101c98003500d813202524819540403007603941284030051020000c14001840800091039000801800095201e88a40722000e41c0c1d000510204c0d003d0502070303024800c0c0803141c0b40b060300403c4100408880910385501032a040c411701c0f83d005211580110701801040e02c148180c40190880e4022030752256003605081140702045180805c00c0c240d070901082e4900d00c900c5ca01840385801030008500703000e900394100c00501c4002c010350031001c1c0032806070f00072102c00c0c040c195289041d54005e00350a418495178060255441c030001c00354400741c510030400c12041c1d41050b0020041c0d544807064242903505c51110a02c68000014407201035841402034003900800304174000c600c1040005283d80300308640c40304480c02800382e0f56210705510301c180c40e8883c07800001c1d0782c0042540340100311810030001c0c07542907540c48241180560004003c004079000300304107041c014400d4035410800c00095 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 329316546 1106 329315440 329315453
    0xb070c030e041b3b0306090303040507050d08040902030103140609012a170a0c08091908160b0901020d0e060103080a0e031218040c0804 60
    0x100d4010403400d203842061050003d042581c0b00d419481c3c181507030010609052400e40440080c00880204400b980220446841c0072105202140070001c0600b0190300a1410120354014400c10000c40d50000c2d1138070884500307a4003d61180d4090034060880e1103280c1003500c06900001c000000c0001c041c4020301000d01c034800382c40843c3c450b0306000d805d0b20425440d035509401c1504115185e14010f0b0012281c1d01c103176051481c104a8a00d039610000c4d0700480b03038282541d1383c514040f180240c01080343e540c01848030380a025010003440e20003414010842c1c003d820076802103400b00d840100360402c6003009401c0720030303440e0a143c0f130b0031140e01071352140c03000703110301070404030301224031200001c45905a0b58031480103420000300341c5045801d080c0c03201d04035525109540c008503902144500614000c0310f0140c004410025060503c0300703840c03213400d1003400c0001710420000403600 = true := by decide +kernel

theorem cover : BRFrame.Cov 329136690 329316546 := by
  have h0 := BRFrame.cov_init 329136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 329136690 ≤ n) (h2 : n < 329316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
