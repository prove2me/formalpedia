-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:23:15.150702+00:00
-- url     : https://prove2.me/submissions/30af85fb-c3ca-414c-8d78-9593742d6ab8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601079136 ≤ n < 601258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601080386 1250 601079136 601079159
    0x606021b0d02090106090501020f060906180312150907020102091e012001150803040f0603090c0b210603030f19051b010b0f061602010c1b0303091403060907 69
    0x103015009240c14075151140d00400c154140a800c4600004e0704103205002950301004a0080b08215074010180c40c60f040005c60384409018000c3c00984840620301492000d00b002035804102040f4002103007820b22440e225413044038070261502800d030300c20018600c18018429100800c00140842800e03403142d80303111010041540c41541444001c20f0114003c0700325180000100d100c82000180d43d190213420300c401003116503c1002143d004000c2441140f204604d007000710303803207410085186002c6180c907440310a115004000791002c08503c0b024181007105800c1031030b24640e01054003e440304001c0c90340701e20649403001c1e407040701040342c1500480081e04451909055142c12814204124428aa0098071a0034005180e449082d95503c900e80341d80c0d510b0411004490751f41c0741070050380d4180f0700c20300c002d80c010f4140138135604840c05000f10320300700503c003080103101950200c0d124540640210b60f24005e01030301424a50b101c1e1498240082c209000348031550080a030f191409130010742 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601081636 1250 601080386 601080433
    0x1c05120417041203020604060506030708070b0d020f0c030904061a040302060c0f0109051510060f12060819050c0603090303010324140106120504031d040b27010801060602 75
    0x20104000019102c03074600d10031030342e00b84258086c0c9100c0c142030078203409440029203441d200c0d802001c410041400001254000c448000d50304580303070030030706e542107009005001003202c149070009045490081c01000900004504903400c200c0da030f4440448082c0c50500205031600010200400c2c0090b19005010704101004802240c2c4007075000d1500c0e5003902c1c0c04860032541640091000a040034045840543c80b80e085123100d001c46161180060030b05511072070070320510001e113401e03002d861460781114000d001940b045a040516031300e1150b04141180704142e5403400f030205982c40d146400303c02c0324080c02444c0011804c5900710344841c40d014521400c1c41d01da0708140d072410750000485005801c0c0c41d04009660140d1907140c020058041c4640d1545000100c1c0380c901003000003608440341c00350204041d07000105040030b28020a0041400f14200350744400307091545a890920880d1803540980352007401e00700d6036600d80805080ea1a98020480540c020300b14600c0050030a18103030340d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601082886 1250 601081636 601081673
    0x200d232802040b0301020f07140d080a0207110d0b011401050304051b0102071a0a0e1f030b18040b15100c08030a021213050c0d0c21050d021c051204 65
    0x10f03950490a0000382240d0040d800102c40c5940414000c06200d16403910151104211010701402411503400074601040208003150850b40844e00c9828481e0070380c03124000354001b82c0400034034001418400d1781140700344141c03010300c810b0f8910540701e948510185d80c0201d5101006014031b4440c000c1c1d01e0b81c0c07801601e64880c114410705800140d07180754085001080211184220303521104640020804250784e80158007031101354174003040f1003020584038440c0a8aa10b00010804050030008941400030102028071260304c9007407000380600c1c1201c450049096503804501e08140e0400c0c04180e000c0c0c5149080414003400c65070000c24104402113030f200320407000052400d0300029244150441c10384158100603012407040301000b00801c801d84000034222403081001e0240e0b5182601d6481d03034000c185668030f05d010340380c1401420380040d074411903001003941c1d9070076101c1070300960301ca02900400d6407060039107061101c500c0c0100c049464040581c10000d1040d40c0b99103c0484c141000c45685 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601084136 1250 601082886 601082891
    0x90905062e03080c070905150d0320011d0a030503010e0c040b2106011d0126010e0709050411040902070516060c150204080a200d23280204 61
    0x1c0c8034201001c02440514441c40741d40c1d49030094402841d00e8100b180d04400d407081c0c9020140b0107080072950350700c02d03041404c41d6050211b0005140171980d02840852000701180c03204010a1300c10741c103403c506c94003811500342029020040001540c0c440d0f0325075006c1c0c085002040180002403074040d486901c110140819807401d6550960307010700c1e5016030840c00d1440c0c50b0011182c820078036042420340111003440c1101000c00990707010b5a241000d0030000d8103200c00f82803a038128000404c0e032850005281152002036603036521200e584d45504990b1100000c800710300200d500d251074031504409014a00d0024205410401d0310b00c02903000c3c01056407148128103096501e00c01c40c50400d0007801160ba60b102c2d501d40180744c1480300b07074207101e5084038a6005200038040343c000014200e2200350400110074840f203007554a0745990807101c4400da0042c0c180030300c213010300210350544809180c003824903100808080d200e00d500c998160344000c0c6807000d0103400030341d45602902021a69800103200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601085386 1250 601084136 601084201
    0x5010b0604030303060602010e06072007120606081c020318060706061707090608100203070c051c260402060901050c1b04060e011505030c09100206060a09090506 71
    0x800e141c01c01d51007200040d072910f1042c0003041d82030040347c0010404400503c0d090504c800c0150603000114070200001c0c2c0050006000c0880412964008050040c03400c1004480d40c100746d006400349008030200e521a00c9a480a003240180c02d0705c1001c816613002c1c5040030354140980d80402401883c66030700a00c2400104c001c81c0c510701c0b450b0003c04c02050030301e0700800e0f801e61341420040c8981c00400140d00d494801c000000300892804884114982e0040c0e40740c3c0c41e03100903151510b007608040c00314440c840e50140c000355035052080c91250252280048403961185852813901c05a40100b000b210080c0418014245140a4176490784141017090504050349080b80c0303070180c4140c8156002d07100c49400d28641c1407a120700c40180400d070400809a60500c0e03c00068000800380c06400c001d0000001140300c1100030541d101c14000810b41201c04e0180c4c0c0009507121001d43c2e40a2092000401c001500d003058483c00c2d111903404070160007241c1d14500b040c007071803070034214844c00000310307120 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601086636 1250 601085386 601085389
    0x806100302091206180a0203060a15030503040b071b05030d0e0f1806091303051b120d0504060f0605030a060b1201050415051e040609060f020f1e041a0705010b 70
    0x81c43c002181160000f452103250140b07030b26030056840c81421340746801c000780a90260f1404507105500000544010a0180003034400d94080c154650010b005804049004030303080b606200102201c5004e0100094110803c45040c4803407403e82c421540c0c182d01652075039044a0140c3c0004c4c20036900140340000110006002c50a1140e0f80c510714030b1180489010840149810040c4a8204004178084002c00090b640c000c3c01c1845800c81c1240301c4080100c0402c0300c07140070458840d004400c03551480e2110800c4441c0009801e0558003180c0c15800e00d204607408154510441040718030003001054841c03c261141b90040a85080c05900401d1002e00c5402d219424095507000e2841008010003418400c1c6c030f5001200c1001e04070038040443e07103842210030300c424099650401c2d045940062070401c1071420310001d048190340340e03940724008500003100201c00d038080c1c070a26600030154500d0f006800d03215500c2e8030840c01040300003c0c54108031080340803a007000e8076001d4820b0000155800c400f0f070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601087886 1250 601086636 601086649
    0x9071e03030f090b0d0b09240d051204090209040e0c1e1201050903190237060e061b2a15010b0a0306090c090510030209040f0207030e010f080610030209 67
    0x210002500d0f155030b014003460404406482d4015030000300c0715a908c8a0740b40c2c0b00e1081c00d00000c200d210b010700035110028401e0a1141054189109d032145685698644001010b500180b000328445c03442c0030340d14110380704040b43d400f0b04404000d144003150400c1c9456000c40d604900d210640040300d00e81010300c901024494540900e003014011600c4042c01185041010709082003007045400203018151200c200c0520340c0001e0584080c8455046403c10043d15180702c0044003411150a000c44e0302d80d0f441c00803620b1805542c0600c0701150614102d040740d988c2e03201d40c0e9812000c1031347c07a16a411521072050b52241e02402c90b58180c44a2120244008003080d1080c0c000d0000c80074001340200e0410340500c034032001410418414880800e601e080500402124030a0701d020b02c1e0000070030808648207604496000c58020410030000d85218401c5e4002c0d007280703008030b020489102c0ea54200b98040c1000816240d103a03510b0003a1580c511007801420301c00e1507071301c00038107400b03000038001070381c402c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601089136 1250 601087886 601087897
    0xc0109181d151e0106031e02070c030209010503010204030305090d0305041206063204050901180c03021005040f141c030503091c021e0c0306070809071e03030f090b 72
    0x500030000101c030030300c0c1c80b0600c92001c0c15090001146500c10380f503080301c0c02c10b40d41c111402410300085031061403007401d000b03c2c3d420085215041c0300160b02c008110000c5c14840c02d4900a4401c40b5180c0e803204145803c070f01c00d6010180c0460401d0001120614007220402002403003032034103d05040c0c4c4d901d03c1c000c8046040b40121206a124a003d120040c210707241c001d144008848499454010400b000303911088802305e10b0b0103940c450b030001382c0c581d04c01d400003503c0200620341e01000d542d40d41030020200d1010f0100b203100d407404485113490303680b0440580e400e8078800c421201085207454506410016444c458a030002c42c03446c60030100c2039100444488140c041e0700c502c1e81d00d2070700148060034541192103601d01c03400c0401204103003647c0016042c03a00c840b101e030840810085c000c1c02d10325000300502000d507d07108620400c141d155001100601411000d02103444003a08c8070310186850303550079410500c03044405010008240300d808150030040380c42c14a402c3c8035444000b07044950780038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601090386 1250 601089136 601089191
    0x307020d020c030a0308040b1b13050301052d310219080304090f0908030103030c12020d050f030403170703060f0501020313090c1407050109140c010918 67
    0x461a00d5031280c1d0140088541d0b804110050111340e0210f5030044e00000010b80040c5c01d41410038002010384825500750700c3e180c030200d00741686400c4460107050410200d03006281c040c0d424070b800321390344840702d41d1458115071909114a812515644002c07800d05402440c09213500c80340103142d500894a507080744040c071500b80c040b646c0010b15005000700011451140d5801e8510010704000622010050320159000c01402181034200019420041c0246180107050520004000000c041e0071840b10401940304010326101c0b0040c2c80000e0341c483d103107030100f4008601c0420008142413031280c001c5510038441c0c01c0c5285a407000403440741582808950040110380d4450040c01070030020b1510320010a4248015841d01032203010440d49803c1da4840d20320032a03194040c0c509402d0207800801c0301d50781c1503082291545200e04040b4080c110180055441034010742d8500a5084007180c04089031006844982d00b0501c0c1202d81070081c042501d01d110f00e1035a503003405501500011003c11050807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601091636 1250 601090386 601090393
    0x20d05100f0504021c03090e090709060b0904060807030b01060819050f0906090f0a0f02040b13020720030303070f18031b0b04030f06090809090406050709140a050f06040506030702 79
    0x1030500c10300002c2080d17a40c010903401c160740041000680e21002c5407094030350341504c029054079410412450141140c0255001d2410001c0c04a00d0400c16005411100030854051046540e01c444054440120f8000900864607000040c080580900340f402e40140d00c104a040b41c0d59803103140b0780d04440007a284144094004bc0078485a640d041100507000380307116014044103050700760041d0365035010a100528040a01308035506559072580711451500740500340b044442d00c040c180c0c5000354006130702102c20342400140240c482c1d03440300040781d10403800b4000b946140c50b440010f480e2081c54940c00000c001c0e54507a050413890100c905c110003144281005d050307201603d24007130544082908480b2507200140020404911802c91680c000c07608a10000340020b110f09110360b40744280100039030004062001d00c010130031035510a07481031846030780c0c0840389900ea00300d0015806010300201e03400405800e060003280340c950000c01801d00001c2c041882c2541d0f4501003041c07034101b182c240d8050381 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601092886 1250 601091636 601091641
    0xb0a0207150927051617090f0d02061008060106080a09020d02030d0e01021c3006060f0e03070506030a020f0d050f040506010803070b04111903050606030706030b0a03020d05100f05 79
    0x3004e015180e0003101140b9484e1420350741c14402004100040c5451809402d00b0000c1500304c8003e100085101d1801c00c203845456104081c06560380ca02601c5000a94400080000342504040703056030580e001c607610043c01340c49500e00300002e481003e030241d034080d8001d0010f07801650308001d00075415050b502c4040d0b0030070b4100000380c181000580428161001c1b00c0e40c4070101d41d40b202c0e070b088000d0f80c141205004080540c00540005c013a840c5c000c142245808800700305690801452074940580b80c0d150031145000da0189511003290b886111b400500a001064101d08036070044c040020761101e4050415000201e042c0503607900380c80d901c040c51040c0081c007007130080500a883c050b222400c003c620703201099031150b844d81c80041010f0b10003075000d80a01d4040d40c1d185140300c1d07401c0c003220340745915680ba4144292035007015a011403280c401d071382d00080c00318013a004110035043c009205a01107455038082c007041c00000304088895000c0c001942c00c1c9101144a0f036900248180c1000640d40b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601094136 1250 601092886 601092959
    0x2100507121e060905100302150712090906240320120a0e0703050c0d0c030803090f06010501020c0109090b0d3e032d0307030809070b0a02071509 64
    0x98000f5082064260301701703010030603121011080502107960558011070304804446030781009028248002300401d110003800081154810f140c0c40580702500b030104112556004086484216500f405810304c5240c40552081c0d4080d0303005002e05028043c180c5000080314090f48450740c0300021868007580c00f1024024106c8061240882100c0c42c000241201400c588545a40310152102a8443c0b01c4000c1c0d0441041440c4401e9801507a10812443d207e0909001745174660003030800e4486284112400041c01c0d41c40015990807200041e11390402403030501d0985c10244c5a01050550004d032076501840009908210031103880b140300c08003454240701c00b0005820f000580b1010180100104482c1055030b802081400400c2c0d605250100c0d08414210820303151300d10b0b5469800c841c00081002024590804820f0b80310308032707440548554944480d1320350102d0181c0f528810041e400030600340070903104021041c0344840079041c4803100d40d03905c0741c42503100d41e01d00c0b1030b8035841d80b8000d0140408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601095386 1250 601094136 601094141
    0x8011107150b010909020702030c0904030e030d0e0a0b030a150f0801060b0f042702190905060a050712090308070c050f0f0919020705030a0c14060702100507121e 71
    0x3021210704090081034000310000303204800600401880341e600103050f8046581c03c10a20800d050040e15203121450107040180440c2c103607a10700c8d8041e0250124804105110340c241008045004080021060408482850980000744410340080c0d691541c1c0f101c400c1c2c5e1054210060000300c4c1c004a400d0704100c107540c2554a1607010f404400400e221042c01704032008180c1e401d40d8040a00c03005161400440700114145244100019520015840c50040084103000345400301ca610f4080c500d503507a909015041c0f203409500d00c001407003809640c0c0001e00382c00741c0d6500701d11945030a01c040e648a4882035240e900c06d00701110206940401013010b07082221503a45c10b4134044585014100d03c6001195a1000c02072000062070b282011035440305000c0e0741569000d40c2c0100850b521403011100241c10204a5442620048071079070401d150741000241d018414000c0e6070180031040c041200c1c25016000c060524030901c15900d00c1070f074419441d84a03080c0c0340c204480d401e0a5031489281c1d680d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601096636 1250 601095386 601095413
    0x20d080a181503090305160b0105180432070e151c02040b0102070911040602012d1109030a240e07120c030b0a090314041d0a0608011107 60
    0xc03001d01e64035041015514000c0102c0c141c5101c0c0c100801c8403a82843d0898442c4500c0048412182c00b551602c01804100010507058480c01d46464990440d9108240e07811001194001d00303070418505040220300394a42d2442590354400e02c0748442010800d2031905001c001c3c0c01800d407040b407100800020104000c0003481101080ea00b1241c0702200b080d07002c4108030240e0003e4042c0d80c9403030a00c083c9074801c0011740020b00000e6401c01448080f1504c0030340c0395109208000041d030a00d6050707082e503081c006142095038042907035111491040c8083c1d00c00703132004019440c29032a081c45403564588052004a2080784145803100484035903c4507500044010000c00b200035207810401c1c0110300002482e04c0c15030340c0a1781c10004d882c8103880c000101c0d02036030308010500d907004e83c14004007a1490f0454240644261100303c40b075500c1e4809440103010314440c00c0840d148007024081c075107090160082e0001c00e041030120f101520b03100c2e503600390382c5219511100c801c0c0c00903800081c0300d0b000ca00140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601097886 1250 601096636 601096667
    0x9010603050403020c09100b0c15090c0a030f050c090a0203091501080a1104091a0907210303050402030f0303070f080f070f050c0a0c060905010e09072307020d080a 72
    0x1c820304107602d00070b580703e05480c038803406907400101180c0503040c0615510000d100c08490166142102d0740116122a80e850441c0c45007009100483c0c810480403d405d02000c2d80982003002c000d185440c0c0c2e01ca00960302d201034419008541c1c024140c0c0d01d400101901c01c000400001d84d0340d0411162841c03500d0302c1100480e509011110050040480114176000d00542052103083c02035045c10000c0c2c010402164001c14090960302c49902600300c01000340d12810780b0350161207900355038403800d01c8414500d22818048059211403140041d0090703114039002400030b8102c0d10304540d44070760b440c81c503801070710103502081d401944074030000d41c4039013904e6108100002c840b0305400c08080c040c00e0391819480304400d101d4040b40441a0240410540380403030341001061411581d10a00078007581c0b854042c007400a207244080c000030b400c2842e409800381600e55030307440008480303076001e03019082c0c0700d4030440514108014907405aa6440141000c1c140554091555006c0281020b44030300110003195 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601099136 1250 601097886 601097891
    0x2040c170714030703020919030c03030219020a05040c020c04060b091005070f06050426041505070b01060f0c0804140f1806090604020f0c0601030c062f16120209010603 74
    0x51151559102c00d0302c2d00054603041c05a11502c20000050010301140080d0b1301c20b0801480c00410700074441c40410441e0f000f074095030a092004011003003400c1c01341602a41040f03941d0170420071400c096202650420051058642c0c0500c080c0c001421b0740d01a900051800700c004c11010a1032a002c0080c1000216030309206107015500d903100d20600e20030400203001c403654ad0b8000f07800d02000b078401c8004c52603034402030344c00c0703420480000d01c85d0b0308940558146940400c2210749024007600444580d140c0043d0100f1440e0710b400000c0358032884010742c0c00108003042105070000f8000318003600190a204441580103c2a00706001d00402820110761181403070704c07016041070103034280c0960091025518152250ba500c0c000c24041c0c40f8030000300c040407078000f404152a4001054181c16644986020611580d0b0360700200c0354001c1d0032030160304400d01c2c803030509040c00b100b511200c62180b01e40203564146c40c5501c01031040004c07a90003502c103002016503510031880c05402050150800d130404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601100386 1250 601099136 601099157
    0x180f180619050c1c0b0a05100503040507122f060f0304020414040c0603020306061b010b130c0518120a080a0908030a080a02090f030706170f06010c081602040c1707 72
    0x1941403030039020601040d40d6a43d10032181d200e07106d07284c40f800a447e028250307400c20540410000c200380c5c42114143c59600038948c01060842140e01e03020714864002c06818112081411842c6c40080181d0114048400d0080c04c03200300c1d22048007816021803044203254480c1b40500502c425034184140501030f901da00d0b800c202c00211204e41c10020340b803461a00503201d0f66404003203003003446844c07100c02900c030b80041c1d0b14032402d40540184050401c02d440c1007030a02d010004000548541039421070111b541403241c00750000318001d0f0301c0d5404c03030010444030750f2400c826507403070405c1c00c444415181d500b00002c003402e086401651180041c584003005502d8a02c1804e40240381c2c0c0e2018002c002016000100102155611445034001d40300040a88218a40d07504c0c001c0c01403503140a46204085418000a01041d41e0964803881030006854008600791950744546043d03100901a0048200c80700c450b0016032601d108071602c0ba1140d4880310145112100f0449030380c440100301c2410000c0d41c824 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 601101636 1250 601100386 601100407
    0x60303021b03120a030b0a170d0f020c0d020a120803100b04061d040e0607050309010b010914190911040303030e2d071701021305180f180619050c 64
    0x1032840401040d28043c90b1030f000c9024045000d40b540c1040c070f40e8400000000420f2080003031441100c0704e5030307071400c6940d2000c1441050f520400421141d2000d45c0101c074800380c06040004040c2c907024401804004060303200c010314908074000e041d0584000700c000c010071041c0340b1078020310800b60136187d5000b8105031802d9401014400120f1451010900c40448000541c49a8100c00c0d01004100c050321410302c0c000c00300816070380003200d0b80b01c140d600344041d001855008200d040c09031240701c01c01c5560050004107200c810501d19038520254030784080e00141ea01c0f86485000c03004d01032110f5480d943d520358200101030f47d0780550b50359a00c0d0091014000b411503684075a62002480e04c40c1d0300121442000014240005544001800411a051607038540d0341075004201c2850051405051292901c2c18040740501260344880216518804200c011200e09101d075030007854100034620ba02800e22426040c090280c07150304441d0741c00b00b00c2920710000760007100c0d8010a2000360720f017004000701 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 601102886 1250 601101636 601101643
    0xd020a12030f02090d11010906030b0619170702011e110a0e010201020d060801060e15031e1c050a11030c0a020607110603040b0906010803180f01030b13060303021b03 73
    0x40d094050698810400842410701d40540e8040f0301c00404800501c03200e420700300b49142000382d036180010000540815514000d210f464880c00d00500b1087c200484c550b2080e40a01c07195084034180413615150b4481004000c50481c407030032840c1d0000c204400d1011a4a060000c9405000304050a14030303c011800000015501035549030f2070202e000715021001070380240b10302260145124101800132036601815008070702241c1001402104903504c3e1244d101281c1c1400c2241a4903170000a04106041019030721060010041801c0d03450f032100d40c0d6006035400241d0007900c40030400100702c294506030003c914141000510000c0c501d440b0102503c1511a51142402481580d01155840034440200c070320b030001c2a0003420301e0740c3d00c1c2001d040021402e0011150900d040c85500004190705401100740e40e03030942403402080c042408502080201c3e40a0301a0f00e040541d20800465941c0d202c124001c500b911101c03001030030a041d810001c1c14001e00c098a203002001d010519401d1384c4000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 601104136 1250 601102886 601102913
    0x11404030c030e03063903060105250c0e090705030c221d0d050c1e0c040617010b2e1404060504170604150b030f0609030c0d020a 57
    0x145000d041440301881c00b0f031024001000310380c0c1c040c441d0204110613070071800e00040c1d910030035400501040d41c46041d440185010404100f0380d150040c0041140365019070081c045281e100e141610314505803c0120b010041800b009440400c0d56090800075481360074030564004000901800055040c1001b1a545540326401d240c06803a10140a490380560840405c0442b60038a0003440842c203481c80740d0701141c1060215000754000c19a594074000d0040e0304407503002c14008007030a4841500081025441c20940400340e0f14001d42d880e00043c1ea0b034501c51074029003d24500149860318040300700342100d10f0001c1081c050200b40010000c001c07581c0e20f40c522803115075904040c050f42207840483e40301c2d00c0290440001e01c00410b020a25a8028002e0300070b480c450424108000c2c0300c51341ca070790b0f10a015103001d00480342202040c2e040004980101d8407002d00641280c080ca107203042481c0c90003104440022081d040440c840c07440c5401400628410300551000b40740f450711949a84000d01d00c1c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 601105386 1250 601104136 601104143
    0x121b02091902040807050a050a0e0a0f09050604050a030306090e0a060c02011409060402010f0e09150f1305010f08070e0a09060b0907030203090601050103110d020f0d020403051509011404 82
    0x808001288644194039407031140ca010728055480300c0e91141050365410030b0b4002d880c401c40540d1030102e040e081000c00c290464110b014800c40940b80d1000c1e540003002c0d402211403005446040310408582c0401145006030f220304e004010354407080c1002811035081b40c008408440c02c00c50001511400000e01800007038006400095142e446001a80142000b41c484522200380d0700c1041141400850300510503030003a02c03800c0b4400b801c82000c8940b841008481c3d0b511003080008104165281d0310241c3c8002400350004038400c2207000040e8040503610102ca40c44c0e5258001807184041c0248884000c02503100104070507401c2c140740c03600b50f220044c20400d4a9566803a9882804060f030071500b01654060400215400c10741c100401950040350983e56500c9040700010701540b091096043d801011501e0504203d42c9000000280d403240c558900310711307000d1280000032011440104000d42c420f0008202e001401180a081c015000b840001d15034500282d1810301c100040030345512036030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 601106636 1250 601105386 601105399
    0xb0d0e030a270f0b0c01050609060a0605030a0914010c110715081e070806011b0804051e03030a0207150c020a0e1806073621050102070b04121b02 64
    0x1ca142c425085040390f1165001c0c0481040008154091074000c2c114140c515000340120f9a800060061541c01543c1841e04100140c0d0204540f51040001d15003250390b00174042042c04250300c4084204031441300e4000f8595441104680c070320380091400b80c0c48800384001c0c02446142c200803d501c910794100300700c148a42e11002403030588031100f04a2400d0300260f03503030100e4100144000d000000848026010801d542003403401e01c0201d070f0300c0300c000c05c0d030206d5981d10300f0341070105000241f40a441503201102c4c540c03913560100da40600281ca2041400d40c000c05046262200e560303001b403014032503501880b000c4415040540c546900754001c1c5c0c2c10601c400f060f282c440110b16407a00880b051403582600825060080720740d400541032111030454036884030402e1021042d5a041c0d140e0b58010f540c0682006010007030007964403141420495241000b0340c20300721588900382642d000d21411901003000c24200b03c100403400c2503200c00403e0760b00d86001071800100c8000c0503c0050031300644102e6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 601107886 1250 601106636 601106687
    0x61101050c1e130602031e1612020102040f12050706050a0e0d020105070f06140702011a0d0203011404030c0b01060f020a030c260903010b06031905040206130b0d0e030a 74
    0x10140c04032110381091070341d0415000e43e04e80000b0345a4000f25a09100c015900c004420242000001e031441e1b0740141c1c0c41040c05003001c0da515095144007030311f000150b54090200043d030070906d1800d07000030100103443c00344512240c03030041e0400c5001c1d0412800e0082c00d00034910016801400c6003030780e20b400e1b01c0e9200441030500062301da40c05507540c000e08800c5400540e4003008060b400607282c00c2c1e002c0300d00c014280c0301c04030306a0907a0700444454205490003805038441c1d29000059a20f003a00190000a21041c520b15031615280f08440030340c00f0807280000d0600300309114030210700405591034100000161044000d445401e00700c006400c11004d002400706020754150390b1401108688030324080a400144074011642000110381d1180d460a4000d42150512800f2a407040301c400511400c020040c040134001024060000c3e03821140900504880d002d0080341c440c0a405000790080d210769200d214001a5008951005003035003040c84054802900400b08070f5420340c2400b40802d148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 601109136 1250 601107886 601107937
    0xe0d08070f020a210207060318020402031905010e150d02060d020a0e0402041e050301020a0804081e030a1416090603110d0f060623091509031501061101050c 69
    0x202820001e00034019952207004c802000340448894401c0c260280e50301660307901410ba080720101090f540c9201e801d04000f50040c5041d034010742d880b80103091501070358106002e0820881e4401d800c11052001c20000b8800c0d0742c141d81c1e010340c0c030a80d005c86100154100c2903012400500400b481007581a4000c221402420b01404000044000142045481e40d940c0d4001c502c209074550403a001d1380c07c03c014045081c0c01d040c022244580c540d503d5141c101d0302c890751036081c0f5a00468144d5000303241034031130200d8800c0389001140158800380001c104100080c03044240140c015144101e003020300c21801c03030603541084004046030003900300000d8200203045c80b211248510304d0200c03060f6180c83c0c0302d140c031042e43d0341c0b00c4002d80b6081d0340c030703141c3e40c0d0110041002000303424801c0620041040c41013940c01d1424509a02004000020003400c1c00c032720303402003031900325100849051228194010f21020740e2180180000000c4000280075605100c00050024800c0100c030022200c0c03942145002e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 601110386 1250 601109136 601109143
    0xa030201050c100e0304171209060705160e060f011704030e04090c0f15091a0a0c06020304050105040201021903080a0e0f0f061f03030e09150604180e0d08070f02 71
    0x1c2d42c5054109100e13440000940c2c0c0e13129400f9000b147d5413800c4c1c00c0308a900ca1800012203031407886595210a1522031890200802a00040c030200c0740c52051800d900d0718903048240b0840100070142d030303c80c0c031801c0481c00c1050200b01c82070400e04200b207031004400f501c074542a800e0740240d014140001c0907001d5001207000b408114401800c0c039545410000303400c1070a042d004080303903508800b01c500d03032042400403960201c3c28410910070407141c610183e28101c852009020681c40c1d801e00c05d0000c0c055a483c0703016070300700300c034113513640e0355140c040000b996010b100810318500083c90340d408a50656401400c0140301901800c0096030f80c09010951100401442001440f0301003103951018030114480d0b5515001c840030884841c803c0e41d1319049040d54515003081d00e41c140c88580c290744620017032010410004000302d00d500700c1d24030000200d84402d001840941003030103d408031070300c4200c3c118060740d54070386115060343d204205148880b0381c40b0392050b1700017400e072429841c600c0f08010100d19 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 601111636 1250 601110386 601110403
    0x71d010c020d0c0515123601060f03050d020c0402031e04020301110c06180a030518030a02060a050703022109010c03020f03190807110d0c140601060f08010e060a030201050c 76
    0x40045c121250f1417000300d0988040d000444a4038208071031991200d00560201401120303c2603619a10828141e803030030040010700303102d00c01d4000003420365916000c001c03520009500c181c0d09600304441110100ba41400381e103400032001d0340c09502c0e50400140e4001c00f12400e4403429080400320002c1030455130b084d0000190a20f500d88080d8a0b014501c2c0c0c240e407070311000c0d50103102205aa40c030b124420100451150952500f507244c1c9814584440d440100b204402008550f00d8003407180c5840040c0e9070700000d4510005580c0c0c80c1078580101c0c4c40c02900c1c000c0d513040110000c50810305142401c45003441100e10b00d2000303190a00d4900c01910b8148e28040b00903001800030301020031204100560090f0082614005942e007842c07580790001e042c3c6e002502c0510b40140c0360004048051100c0c0108007040045120304d49440004031004000c5081000030b0304a200000da00040b9641d1003584000c0482c05800006206841c9040040020b0030841c1c040c4402414858045a0102d0184c014040384a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 601112886 1250 601111636 601111639
    0xc120207033c0305011a03092b0215040c050d03090e040f0213090203101104051810080d02030304170405270a020705070b1b15071d010c020d0c05 64
    0x44407110066400b9503050400d5010404406580e2403461400d48207000b01070491b035080103250388150303c91001129076400149556004c0c070409002c000e0344800301c040f0044600c0110003403250380c501120003e00f0487c01c0b241d480c3c45d9166490600c00450180340c180d6044450440b00703c03008882514040c0c800c22410307803101402d0f104080402c803d0241116100414610031100410300800030079101040706c2002d60040d400d54091030074480380708030710f5114400020500301d80358105940d490008029118a482540d848100941803010940d24003400c680a41206005804c4001600000135038900008101404542048422844924020b400c46016141c00380809482440c29040307a55421a95801b9140c0340200400041303c4140500c29a09120f03400070280c2780880ca421440307555034100c04603402c041c405101e0f00002440381040310340212024240000460b24007520054542244102086d10507652004c11403000da0744002601d03115035044485111151503402c006520794010740020303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 601114136 1250 601112886 601112927
    0x100b0a14120c1906170f040b0408040510020109060b0105030c0a05181e01170108070b030405031207170705040b0904021b12040311030c1c1103010c110d030c12020703 73
    0x216500ca58030360030b00709130b4403103849403200220840340e0f01c085000100e4000080c15061000f080014440010903500540550f8103542442d88440005640d140c00140d90340260395112450810840a0700400c18a81c100342021404c41c6843c500c010801c2c8240d403071580821200060300c002c0c41041e014017541b5001c02400301034010031116410f45640f40203203c0e00d40440c0105503924000b008452034681a5031503070025261191400c0346021140d0005841241c60b40010b0100d4074080d158200c0491041c2c0b40c0b40d460000d18070f040c2040c400740c400c1c05403490b810030000300014800c040001080700e4060401355001030391001c011050540600c41c200c52030145024280f0000c1d04a44050090410740f8019041161252000000c06030b4610300022070907049488004c803c000d440104070748a0000d40158040d0241d09601ea0000b400c450303ea4070610003041030811681e0b0800c03810070000f0205049407c0070842005155806422008a44241c405050300040c2410400d8403803c2d5074000449601403a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 601115386 1250 601114136 601114159
    0x1e130807090f0b040c09060e0414090706110a050c09090f0f070519080d1b05100501031a10030b071107170111070f0201050d06080609100b0a14120c 65
    0x2440050b22503050350554503801c2070100c80301440d09206016001e55291134900c0c6140c030700a0165030320704a8007402584030ba59481640b02d04e801149030b00d07104a250300f0141081e1070030040c000d020003106a038950301d03650204c6801400640c001410154003201190391254a91755643d100c1e10701640c18502d14030320301907034088030003810740002c45400f507600840c1c1445142e0160703035407400c01600301d2084880960000c0c218444050040c050401c0311042d2414a60600f4030b40e172919480d01c00f4850320206016503440040003400104080410700c1034201c0300400720b074109441c5403c104459404050044940c950105081ca4001c0c07a4010700e0500315001d8817220342c1c1d1201d14013403403081c46404c84405d50900404000914840d012110038540c080800011443d4a800440705a080348245c441c4c00390303079494081560001000b56600c0f59402d800105405980c444d007003002e686060081500039583e00100b40044400c1c00381c030038001071054031421020b03503070301e00c00e10324180c50402150303080700381907a8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 601116636 1250 601115386 601115399
    0x19091a062205070210050c07033b0d0609200105091f030207051b0406060311031819050c03060105060301382b0b03070608040606030209070932130b15070c09021e130807 74
    0xb64903b4032040083c6c1d100c0040101c0c01075480340300b42c0c448180c0c494140d06900c0070380c144025070002c07081c50601c2d0040c10840c4681c0c585241c44c51080c1c1450320504481412480ca246c00e000f40d0024152070b150500608121070051007080c0400381c20342501c880c85e00d2640e55054000c021250196440d0226059603002d00c2c01d00c03980350000403040034068041e403c00400c02c0d082441c1128102c0301c502000780b1900c152991145180224002c507502c80c41102c00c10310041941e1030f805001c0700c0d090740e9910105072a030203040da01c4440041068005607801c003088035600d5a40401c1940441d2154200b002c1550307074a1034604020310741c9800007580500f400e810310030142c2c0d0040d000e2003a1010300b140c07000c00c01e119207103034421240320002d2054a8000e0000d65003044c10480c0f02c032080d46416400c0800c1a41d015000120f185031622105000d100001c1141c0c03091210962440004001c0f40074111f107810319880e40305206c044e10302c5e01202d8003000000c2030111407425a000c04024a17091043d10211a120305 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 601117886 1250 601116636 601116653
    0x6030703110f040e060d02240d0f0c02100605090a0b0406050303040303022104080601050d0807210216080a03050319091a062205070210050c07033b0d0609 68
    0x1840d00107550784c100081040c18159983d091554004100b112140c640c0583c3d020081c0301c90301c803901300e80c105201000704480ba5000b949001d007203103500820380d04020400249040b41821048170007a081c01402c01c5503031508500c2c560060b001c910045034032081100820007420141e072180b5090f110015002086c940d02065020040078030600e0715942c01d4940c0f0384a46030340264000d0301d2964200b440100450b00e0300c50605141544102012814601c1d1034590040a0044603607003503030f03075001c1d02c03113451ba450741485446161040c041b03c0f1100b6504002c01c040da1040b202e00c00809004000010506203e2041d145c2c040004468000780300f800803e280c40740c00a03c000c02d88000c0705c9600c0003c1740b410b2030004120a00f203001180201e52000b007800d40c0e540a40b40140075035080d402910700148586109000c4c21344601c0005020b95910100c1d07180c01440b44403880503100301d91410b070b60201d0482c18180f000e0384041d46100744c0c11407a010b41c0f070000b030000360b0000c000800082c44d01c00b480c0200030380071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 601119136 1250 601117886 601117889
    0x71d060708071b060801230d0b070207031202070806180c1207090b040e10050a271506080604030302070303140a1505090601020d08040c030c180506060f0906030703110f04 75
    0x105120f10307259550301003030b00c3e031550030701072510880c9003815400480f07040a9003005c10301000410028101c022030b2250655180c1c10380e0308a0041e00100801c2c001c0c4602e80801313000708c040a1001341310140c5001119920380790040c014000d032850140b10800341c4801000f2100400c90700a01e1440c070003c1d10f85a86d07640303900601c615010103043c19040da00703d02c1e10b40b1458030100300c610040d0914070f0b540c107482401020010f25000c0d1156a41c40c41948583c0e208548149041c2000321599210100381040c4022118141c06103441c07508180d000d01040b03002140083c0c00c40e0380b40c1009600c4078901e02e01034015203a01c0c0781c80060542c02104114180c146900203c04400c8205611181d0503103c0043c042000030803914503003d6480f0800c1c27015010b106180c241d074443d02810312880f100d501c03942c911030300c6050342c0d100b41c04d0340070b00985607140c0d2616480360035040b0404694042c6044c102d203035280381a00a00c00aa8411a8040002000d0324041d41104108480400720340b41d440c20b241c40300307213000e8015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 601120386 1250 601119136 601119173
    0x161710020f2502090106030c090b03071116080c0d05070902030a0f1410050d0c08061e0a0509070315140a021902010207150207150504080d0b09071d06070807 69
    0x9078012450700508a003103041020383c0142944200d42e003816000e80140c80c2c440000750030420300d1f10000500c10404006580103c0302c69a4007080c001004054500e0254051200d007072070b144d820303070400008070002440700c1014811340707801d0b03901c0c822818064248000e0764000180d541c000001c022541d0310781d60080c031204080501c100140e0701e21141a00c0344010480302141d084401c258140000e00d025003054640a1090b1107151550b51951a2a800d081058668603080030268540b0074000c24140d040d217a01010700720040080b8030341031210706d699807203620000d408401e500c5025000c1c0081e90300012142200c030f0301d640c0402d043c1092908000c0d03200006900e10004070300078201900744103000319074a40d500020200e1401c500d4440400095010040c02c84400e4692000d10305080428001e1311310075801211400d444450700501d5000381c1301c100c56000e220b842d40008201c21160815891000301094415065090000b803000c1042440ba90b9400740100380c0110303582c010402407040300ca0400c0e02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 601121636 1250 601120386 601120417
    0x607120816030504030e04020309010b04020c01051806040f02010c030512040c03061a06030103080d0e0a110907030608030a18080a0c0305010f061d28020306030c03161710020f 77
    0x10101c00c4080310015076004000442c00700003201c0701d20b1b241d0080c5400007481000082c585400000190403a4030ad118040500d94442c410002045a95141d295030880d1f4070018080e1464140c1d140406003000784002410301c00142c080400341031013201034076480400c011030700035035041908140707a040485100c01c40b4094104030b0701d60104403000a00d0000034101900c41c2d415070742103a49090383c90b00000c001c0c020481c2e50b00701503182400100001084540207008110a9a4598040c0720362004004d00f484145405e1000400458900100300c0b02084c07500e2031300844112440c1900000403110b40d00560f498440c2100c0302c030500c000001c0b198101d030310490007013005091000d810310556041c2e118410600e0400c910380e20034500c01c2c0d10501e6000d01220a07207010200800008040c85d008041c2c085075183d03000c0100061741c10108203244854004900910305400550b84c20384101b0b07083e004011403004c4445510802d69030400560384000303c03101e011754452642d5088080c0c20f8100076070343d203210203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 601122886 1250 601121636 601121671
    0x1403251a070203011a0d0f060e15180a0b0601032316030e151b04050418150908031503030f0705030c30090f1207080c120309090606071208 61
    0x80e103a00e84020420000d4190a90910341f6100d010800e00c1615069424070340ba200d001d180341c0400c0c0140d00a900b0008500142810203811111111140c04035141d099400244000d0100ba04036503000e5101c02d0034680401c8041001454000e540383c03010080740e203012100b040c8907029483d8451802c03d4800b03075808000d4004680651583c850301400d0049803076030320300d001c10454540040044441e03a103e0100f54603050b80c030800f29080768400d4124622710b100c42d240e86010000c25083c0c0d0701c4913012044050010150a071100010340c80301070418090020031403542e50803514107105860024014000480c0c07580f4041c20456126440002c1841850060100d8094402d44e010105015460301c6003d26020030071032030b514846588090341882d84451104034001881d079070807882c00701c0c0204000182c0f0440d81b41170303070386407410031981210740c815801038044034412540003040d6003107120202c41c0b8107055242d030b0740450707000d12508034044c000001100948003001d801682003030051902003611004c98 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 601124136 1250 601122886 601122911
    0x30102040302060d0c1b030810140108060f010c020301150f0b0c0d0302070336140f13060f08010212060405130b0c04050a1e1403251a07020301 63
    0x38030660000a501c400148202c004446a42d4040b640290701800c00080200c00c0f060b000c61201d0100724110001641350080121900e0407509000040441100040b82e80502d10700203440190000d181a00403240d01584903926845660784c556510740240081042c280c217444914103001141c06043c1007100740410010340e03a0706013000c990100044101410000c9002e1070100c2c082c2d4007000080d42042002100c1c0004803402c400c078816232110302d0301000c1407104032000c40307210321000b40d014021103541050109419225490801000c960448185a015035048020b8004011a410008041f04900d0300440e08200550042001c0f04460058030401d42d249420001511011100c0c5c640c10b2800203820400200070045054000c201c0712006401c20351100b0220b88208650340c4009440c0c210040703541200040b514011001d4282e1840051030350701c00e03c0219a0f10305182800c103410038844884c03140009211008017000c0d2003041c9040225244655943c4e88907002010164425441d042c004400c0d07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 601125386 1250 601124136 601124141
    0x1506020a0606120c030b06151603110606060f07061d070e280b0409140312090307020a030816020402041401020105100f0b090f030607171008070902030c070209040803150301 76
    0x606500c1034440f44d0142c150307621440d244030050407054000b18a1201d00d0f4210040b03501409039698164043e000c203c5170ba0400a10200031040c0f01d200c030b84c02074014001c1c2d079184d9034101c80c200b11890080d82d643c2d01140c0b40860041c4542c14a20402c001950ba180d4848840481d02d00100c44a1000c840c030b0301d4a910800700d400310450072881c1e54240b900c440c50603413404590002030340e070000180f0004982d000e9071142011040c03250b07000003031504001032241ca1113040440140e04a84104e00950818283e940400c403410f1490202070038005011444400c0040211482c9902c00c1d405170082d92125600c460074011325004298040c095400c0c0000030700f5006200c142c00c412141280c40c4407200030b10740101501654400c4182c603400c027039101072400c00da440c10044c0c0e600400b030f142c1d600c484212004000b824203030406000c03851005404201000440e00002d4000c00b56610100016600c1d00c40e01c1d0310503250b128208000f50031103805810802400002c4002e14800c1c16100e21072a411000c20b0f042608 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 601126636 1250 601125386 601125419
    0x304061d01123b010e011103040f0f1a0106080a0b0f01122403030f0516031d03060f060f04090203070e0604060b16030f0509031902041506020a0606 65
    0x4100d030004030403403801a04070a503941d0011003c405408000300c060081400c81c241d0000b5000780982201040c2d0009210302c0340a07858850003000368000030080410345202c080c0c00138101c2d2060200420903c07008140400c0c48a0b4001e40148901c00080d910f410040424032840000c40c416400007161004039004000c030740c0c13000800c900200301c11000152000c81d407100b5810301c00b5070b945d820b81c0320003448490b0700e0106c80004006140a05e00e1854000c243c0c41c03181c09140e003048824805080c1800070f40b10303c02c014036890309002c259001890040e0f0400148030386810750501c107010a0041d88140d40e442c050040e9000c2c0d4806942c0f10004043c0800e0300d860010094150340203800c10818000910440f0b500218002c1020400545e581c903020000c0c0c01c8442012040c1802018507010560810145180c00d0441c5c20028103040541d000244c5411900705056604041c800e184411969154061101008540c64186000380c0701d02d0000c0d5030b003ca814003221f001d4070300800071801c1540e4405581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 601127886 1250 601126636 601126639
    0xf01080402030307023304080f010204030b04110402120c071221110903390a030b0601030f050a060513020301031101050711040501060c0201170906160e120304061d 72
    0x51a092050382441184d04040c6e00304101c5885102d140c1c000c82c2d11110b6120020366104c81482d486d642071482c02030030084112841038407a84100310401c000f03520520915402a00540d16400c1c1c40d84401c00b140107840303407a22003031046070329404200d0706420941c05440c01c03a01960340c913500055041030030340e188200740380b4080c4102c2007030740360000018460300078807408030805140760b040094035000310b0310b171003010702d858404e07207901c0e03110640c030009121a81c032500102c4c1401100c05280d20b00c0820b003010043e00016111101041c0092103a90098202c5040c0901400d400c0000d0719140903044020b00c070501420348034481d6440c46001d21041c2d070003560305981c0c01c100490580c0380c0c118015100d80c5d0011000b1108075a000b080c0200580c1c0e01d01c540b9000b02803d40b500150548a480010321302104800f04040070302c20342090181e030000000c0c81c15031180030383c134a0000c800e0500405035039040030802911b60010554008a03005030003c8060011504103803900c0401407104880400104444802503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 601129136 1250 601127886 601127893
    0x15090e1005010e150f12072409030b0a2009120a081b0708070801020306040e030c0c06030c0f031303140412121e0206090c06040b160516090b0f0108040203 68
    0x8022040242c811074021038020544803441000402146c425100307503100f80e0380b0342c0140004000c040b00c040075040041c0c1c060548540780300245200904907906038003014244011b0076001a1000c04d843d8007402d4003500d6840380100d80131300e003400142c40380d11812000380640d000003840c0000550000d100d003007050340420001e06000091a0b0041141d10700300785185948607255000605103018032504c009000700c03000140eaa0302d00481400305503601160a202d1962080100c0b0a8100011034803080c0480112a4a60340b07441d149681240750180b401c03d100d41050000502c080000a600b0805499100783c4031170000400800c0700d40401c3c041e134422442e40030101e0302207000091a03040e51201d0982f090912031500d00408031100740b900215542500035a00034414012192000c010940f2141d00845180e80341608111611074140645000c0ca02040355103c0c014082280a01011980010b400f0350240855070310340403940545600301e5500e000701d00b620010f0519500c154040c40c400e0390040c009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 601130386 1250 601129136 601129141
    0x62006131103070e15061e04030c12021f09090617060609090a2904050109021207080c01030f0f020307120b09010b07110102010b0907110f030c070b0a020115090e1005010e 75
    0x70f01d4070030302c052107186c0e0289042000542401525918036007291182060720748580c1103180102c40b2403242d80103030f82c000c04004120b500603078174280c100007004602c030342c130a0102941c0e0700b06071070601d4243c11001000c1c0c1032210104114020030821002651440f084860b0342d10307405e06100581009a4450100360007501c0040d01080756000c110000091920301d10061900c501008682440701f0340d821aa26510341e0300038011b600d02004902055106200903008080c03034002e241781d5032074102d03240354185501c4102c40414080207502030328140d45c0342031080d03503a894500c1000b4610541500d105511502d000c2000401b4144020b92a050300e00c0078403054a880f41544854101d44c0002250504664032040e00d95201d0302e96900d4107000301d11984445c40c000c039265094505140b00c1d80d0081903594001d100e21a15200001120f10843d0740c100c010a0343c1d9881d88100302e001d4201d0000c9400d212040a400040c0815258003c8144019034425610000703500002030041c0c580c20300c100c0019103c503001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 601131636 1250 601130386 601130401
    0x2703021509030d060e0939060d1a01080a02070309051c0609050105090f010b030a0305090613080c1c05070e13050109120315060504062006131103070e 66
    0x540210708602207a0030000c1041c003200c00d480c9640c00400c2c440d610002031191a41c42001400d03060720360391030340c02240240f4040210300e00c1503041020041c5580c0c0403601e030060300ca04081b02d5004030040028451001c0440c0d003818040303c08250b0a0019040c41d0014040c16024400d503017844c1d5050fa02c60703105034a003400300030703046103400151601d1180060800c000510103108112a0702c3c81000080f50900d00080e08904000407410400701c2c0da410109048926500410b03c00e0301c0700d52505100c0e84440d00d15001c1180382c021a103003c0d00070800101c001c0b480c46000141003501d00011038014006103c4402c040c0d80c031451a0300c0041c410f48c08040180003003c00000c00c95030169a40c03034124407542e6aa101c240c203607204800252900c3d130303902004076036244c0d0500449201c0d400f1000580b00803494003100400611482c81400f00300003041c5940c0c0b440d10780e01185e40c9025130006007100d583e410000100740da00801c110f0100c41074900e0802c6d0070f80600340442d200f0115609800c1c02c2c0110b0341c452a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 601132886 1250 601131636 601131673
    0xf0705030a0608010c020d200307120e06180a0506070302100c0e0310060306050603160605030c190e0109080601121412030c120a09080a050d091401270302 68
    0x41c041c0ca48641c946001050400e424480d80c4c9001c40309600400411210002c003070421203881129801e03600e4075016280da10607000049400340c90380407150804d854851181101c1c240301659040344d00c03050001d00441d25a03c0e10400c460800c40807182207403800d940c7c200b0029103100b200303001405a01b0120700e8680c20034041d400103c0d6168a07090001030700700243c001178140007110302e400100c0ca075541d43c1802400b015209207a44000150020800701c190030f11120320314001849010b04004000000485054158050f1115100e861244070004501b00c1405400d12404280a40c00928150800187e540000400c4c60403140c0d4082c9a144543c495103401200240c0d41d2061984d5100d180d00b00306603c03160500440c4600f09105072151180000345550400c00806840c3d070040318100030000c40495102812640040d240781002e035070300c07940d480d0000058441808050a0a20b420950000c407031419000380148002c0fa68440d407850f5520120140051901030020700107078401003001c01c42a0402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 601134136 1250 601132886 601132891
    0x1506171e0702100516030e030a08010302150c0601030303090219060e0118150c0510090203060a02090f0901150f1106040201051b0d020a1203021206040c09081203010317030f070503 79
    0x1881030303c2402c3d081400b92010303903e0907128845045001280f00ba03c0545c14802c0c0e481e1680c0c1500075524000219500401c040c00600009e481810640a00b0303c1c40c4649100f294400450102541d01941c1e45e4140540148004c100a0303015201c58840743e0351600611a1087c103071205501c0301e0100311040e000440700500c604080110130169a4400319065244003040301d80d010103565811000091882c3c418141002d140140d9038190502180c41e005070b070042032042d072103e1804001a100c98040c4009204d0707840401c08681c0000602001080040b9a041340c988a2022621040c0342181494000c444001d0b072a050302e003040d00194003007001588075900a00f5084121628040382c0712044883c641045092907502000d80d1106054904004007900d0690480d011410f00f1410851611994031001078002d0600b071003190ba9500c02d80003140640b07900c42c0503103001c0d0110f50b00280100a41070b0150b00a000c03ea500391820070300b011041d6544c90880344201c0e082a4031880383c5c0c5540e58150740c9074001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 601135386 1250 601134136 601134151
    0xd0c06030c020118060c11060c030f0c0913141807030f0c033f0c02040b04021e07021e01050a050304030e22050601030b031e0307061506171e 62
    0x39015a00021000d04103003c44c414059007002903048031825001c0c00705072010444211603000b400400051508410550f83c0c00865101d16103165914014041d106108060844d584060f5100d182c407003030071855200203000040301d804210076858112020084112041a0310500d0f8441541480050000d00c00044c03564440c1500c0c4040310340340d90762120581d0544c201e0809801c64840c05880c0c0b01d02c201c44400740542c160125043c621007c3d2401000003030a084003038003440d21004659495100c070f0381214548403d0f001681c51001e090f8041d12403950025a059110359020340e0070801809021008040c040c0c016152903281c41c4d001d05040e900384d01300420075000c0c08041c890042060b11105803001c1e50048c00c58100c03a15035045100c42e0111000600390f00e04042c94000150000d4800052128180c440510626100314841142a103944150740c00105802e040052410724203400404103000d07100341c5e440700f8007603003240042c04040b03620884443d04407812034282c0c1c00509004440a503004003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 601136636 1250 601135386 601135391
    0x150306110f0a0f0f09050a0509090a06111803010203070813140d08040201080f06030606060705120a030b1219060f0b0315100f030209040b06010203280e0d0c06030c0201 74
    0x2480c080585071900801011404030b03036685490f1003240d03840340070964014001d0400d81041810600401d01e000c00902030341d4046d81c194000b007440c0b800104151045c03035a004405009800440701c840e8a81e801020005007040407101140c121403906009882c410001951444250b40d00d0449804405121010541340c90302c00e1580342014800a01c0042840c03406a151600e40d070801d0302c00103210050003004100015044820300c8207540d80856103c0d00b2130320494040740c0f900340340e00780107007001080f0ba0300c80e43c03031900021030b80012501070f000703090520300458000c808201400c800c991916002c0c0b14a01828402811070b5001034901d40c0514440c1d00e41c84400034000841401103443d1541803134015180035400820040342103505c078026000f40040e00d500c208154516400f14a03a050054002020780c4030042c001500340c0d00c20800e4403901d244d00007180c14402c00c03002e080d268500c81c1b800d5030700c00200070207214600d6040002c640303c15a540140992482c0b490044118018621490721004554 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 601137886 1250 601136636 601136647
    0x7171308010f020912031315112b180302100504120f050f1b12120f0a021b030c090615070b060f090603030a0c020a03060e100c0315030611 61
    0x9424450b022401c0100d441c0184d8451143c000c010002c0290066122154020811411762032030360711141003140c0140c000211010b500c82c01c10390f004862a8900140c5118803040410b044083c0c0150034030b25a10f424159800c004801011140001c04540307404890702e0a120800040c00d04c1980c1001ca01d001f4030b0f0a0341441d44070300800800d100f95003400d841c2c03092502c0031801441003e019107591291040e0041a8040b000c032030b5201901c111070b008500c203141c607500798030341001c043c0010000c100f110102d00303136161780c141d20702541c6070807102d034442c0184a040741190204103894020b88840c40010000c000880032041007241941d402054190014210651010b90098407000b0b490014415085003449160150034008003120340d0401900c12202401071000b283c07004001c43da00d03203991340740c00c1607162860300200d140030f595a44010036192500a84080c0b44001080148000030054010b114586034403200b14251618140020080f590304e010810000300240d00091180031089a00340c10724 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 601139136 1250 601137886 601137899
    0x3030804121709030c0c190605030a0b06191b033f0f1505010c020d06060e040308040b090a050303150102010906150f06091505030a0b1002071406071713 67
    0x10002540e10071415440400d0802c030030001400310f4030100da025100750f100003e9030208003041f0800c0e8801c80c0d00b8414008041000a6101e81152414001c00b07041c081ea070b80c80305030002250340c6503504e20ba800a1443c0001640020581d1808151590140d03034104100c071503145c404016030b03da0030b203c1440714048100300302c031070424691000d0071009070308001921034540480202600c0a5440003000745078103840510481c1e801100072030100e60140d541300d003040c0280c80c0c10b00c0100110781228019074280f504110400d94401c8a00e80700f207200340c28861040d100c0056050307070307411804d02c02000782d0018000203012145940d0240c0e9041414030001c11000b1160f161b10302100c1d00290050000700300f41009014851650042000400c03007860700700c60f040c3c0340a0402060840da101e81c00b04002c400804601a4034503a00300350a640781c0201624400d00c154078000c0d40d01c6203144039407140c1c40140c2e03925089500d480011b03100100c0e080b200800700d0031190075003c5900ea00200b60703400d020710440004500d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 601140386 1250 601139136 601139177
    0x9050721021005040f09021201140310020d0b040b030a1104200d0f050c0f070303090201210903030f0b010207210b01031103060105040207021e1f080f07090303080412 73
    0x80c2c2941e403281c1d40c0d100d00b0044442501da0080e0040e82000d030041095100202c1c240c8100c0741107a0b031200711a082d11400000290414030300b803030301083c0c5500203e8907610200300303680a03100441c012a0b04001e5003280500f071549400d18520081c1c000c1801071118a83c0303092907045600c0c0000340840040031504c2e5004a01c0a9400c1081c0c5149225030310110f40c802a0964841d09070002504921035003048000c0e2000081c1c0e01c0347c001c0007802c01d600ca141c032030308590183d9919aa00030311050700001c4e41c02d51160750030090441400c1170303000a0803e124400241c2282c4241c084076801039014040d0303213041c1040001407450004001105107281032901010624240c1154081e5100d803004146000440d01014503010060304150b04c1244100f144800503502c820300280580440813024007058070940c0080c0c004441d9860b04c10440c1010443d44450340d5024019a04c5118811505180c0e130f141e004044400c0009401b004011440f4a00840d012542e052600c80a1940342d05d4080d06011482c000d0084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 601141636 1250 601140386 601140409
    0x71502040801020a020a15110a050d0204050d031106010b0307200a060c1e170a050a09080a02240f18030c0114010e070804051f020d0e150a0905072102 66
    0x580229428004000071f026100e25140c148060500c040d40c44803003092040c0c442d0292240601c100010a0103011241390141c40090400514100c254a03031414060044100b901001005000f510000f04a840350441541e01820460b56200b0340b195109203080c10324820391720058080d00c20040803000042c110b00502c0d400c0c0c41695116060703034190826499440c011000201d05101d221900510748210021225602840f002804181911380080c00c40060540000c090b2141d04009400031506030001020611003c05801c1c290758030580c3e40502d00f08003020b485812961728000089010011120001520b02c0c1341c1009032442c0a41c0300c148142107400ca50411614414184010001c4849181041d640301000303007451081440c1568071039403200b040c030f10b882c2035421009001d041e185050f5410f44100144141003000703820b40424a9a9542000b06c16001968011000043d0485502d0090400035a0f0280c004c007686401c220700308804004130008900000e04200c1007a0150351080305030003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 601142886 1250 601141636 601141657
    0xd0e010501120b010f0315050402011701080322140904080f0408061603020c151017070918030c02040b1c0c05091f050906040e060c030603100e0307150204080102 71
    0x70100c2c14030b0900e04190050b84507511403103102c00c0800210351448007440d034915a07807a0000c3e01e582e4a20050b00d00c0500304a18441001c84400045100c8800100510300c1a5542d44a09042c0c0310703140b640540005540510040c400c02d055030004181041c000d6607401910a401050070b0222003414020240c00c19032080403180d000c54184090212250b50f80720b1000c80a2505602c0d00c3d1010001c243d59100046090b02da00303a00700c0004444001e013a0388000a41444490b806601408001c01a55261540a40e4541d21f00d41840d8003a0018a90119440c0643c15192030100003020b03001c0000828052030200e030400d01e803a042e8902c523007650f0300301001e8a100d1801d10070301906040902807100b200030a0f01884403100800501102c030310002850072240d0456400140b90b941c9000301d005002e00181440884c86110b06002d0080100380c007448c8240702c13380c1202d6240100c2e0408206a8050f44800e0361540c100308020404070b6055250705a41912910000d841d1a0790f50303032a903089074041c1c000310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 601144136 1250 601142886 601142909
    0x30c090616020a0b1819081207060c0c03090312030209060c0f062409151c0b0702030f03010905040302011d0d030e120316030906050c0405090f07140d0e010501 70
    0x7400310b15185070054003034200480524100090440844890002c01d00000c0c030910440c1c80d207001c40d5040d0002c1d0030140c0042d400b03403020544c650880c1e0090f0340220404880050030541d445214600c80c0d0041c03c9031036003540d00c040c00c0394a1911282501d42c00941c9a504041d001c0043e10720580b1030f0001001200d56400040240200c050b07190ba0500c0030282646900c3e0f1007000c8a66174545101e9400848407100320b0785000300d602e40109201004c0000e002d8150400307201d001002c03c00f4054456031030007c1c0144440c6200760703202c0380200d0700c0b44214500c44010301808d0005000300d0a00750300c902c0e8001c0c401c1c0000101a48444940c07590b0010000700d41d901944902140490031754140a034115038038006000300241100214500604d0000400021a801c0e036410b40ca60242c0c0705c1e42180011541101041001e400c1c248140c0603141d00c01d005490081407084040749070521302c1c0080a103d41000c1d0b440d45071302180104e900100b42c1c4031981140320360f42c6908001c41907640a100f09402000c011000c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 601145386 1250 601144136 601144177
    0x9070c29070206040521070c0e2a1602130510060320040e060d12020c010f110a1104060321031107032106030807031d0a030215030c0906 60
    0x1048400030080024045410190510001134030024408240d50ba0f2044100242c40c14581e00003118042c0c0f0201600600e0490030008500040a00440c042c40b00f25079014441c19650070716103001c030202190303101288802c004441103001108130901080c0d10003404600300c1080b103104001947e0059690f5110040d240004000030343e0144035002403d0325400b44040300945d215210f0942e40101d2050f0444425407400250842d0b40d0032040c402c9250f03122900c407042c0c0d908250b002390348101c98070810b0b010882008a50503070074064003c0c40010354906000b4100c00f0715558407104009015100507800a40340c00d4007200003448105000070b4000081d48c41440000c000790000d069480000820303114100810003000441c0e4032050100c01091a00c004c00c041c6169034804400500d65503101606408000c00e40e00101039008105039120446114155150880300701000a0b041d22480000d601c46442071142d601e41500b4000703154080b400d171a11a00b001404004034203641d012250201801e44000c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 601146636 1250 601145386 601145453
    0x50403030b0405090705011709071e05030c060702030604030c021201060e10050d080d0c0504150c060b0307081b06132409061d19060e030f0f0c09070c 66
    0x142da5001e44c40f8402046481d181c00000f030203840001f240b141900c092240000c40f180d200300501c2d00280300e208110f41140b950f40120a41d00d00c9035004891081c051581c482c009440c220040d43d02213500140a4005500c5907039054803e01450380e022a0031102c1c0e510f01103076504080c45603500521500101403000c1c0740420380403100b90304941140348517002503952100820621400e4aaa010340f074500040c90480008059035980141d5000d181040e5000508181140e80016000c0c0b40341d11842d400e0012a1005003090b131607483c10302460f44190700c440d000100d125030345414011240310280509281076100b1a5104c0100f8403500f2015200003038901150350f840400c400034403081c80c05d18040e01c00509066008103035046401002200d250700744941c010340d5854415852070100c2c1c281d00c256407280e54540c080d05d0b10618020040c401d000d0941004010300012450700b90780320841000d000030004c15030030009080400340c0042d04001109944400040c101d01c032250014844400310181e1a00006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 601147886 1250 601146636 601146641
    0x40617010513030c030c081e0423100302130302040e06091b0108160201140708070f03150303230c01090212150a0f02090a240c0b13020112050403030b04 67
    0x91407007180c4102d00340b400c0701090380002104d800300d030f051500c08048291410480c205001c4d00f01008506c5a8400d007040c03005500200510803500c010724202c141008042040390b00303403a84100301d50001c5071111001c58062080d4010403405000354009000c264598011908490858030030054a500000c240085927404103d2402c0350030744504418004501340e80000c1c601600503292050101d03000c11100b446600070740001017034107120082030040f480e015030020312884c03055540f20081860b5040405846109005481c1d9104010600703039000c40c81c42c1d030102c3c0c0080c05501d140b691030482d807024007507881000c0018540385112000101e5005c0f13450040102140100310340b01001d078001c1035102849804007a044d903104040c101c00003000703117040004101904c10f0f16072070341c3d010ba07070081e0201d200703203a415142e4a0301c108d04506856810b94030006030744140142101501b9480700600003503140e6034407500c100400e841854068114803500c03c43c0d1050707810581e4228042511807055131080e00303251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 601149136 1250 601147886 601147891
    0xc13090603051b1905131e090c060926030f0403110f040b0108180c0301090c15080106270e0c0306100201050606250b0103030507030e0405010f0b0a0207050406170105 73
    0x46401148101c140d290004110b00284581d5001e1b000c1d0076142190381c40301f0f0740b00509040070920541d02c510001d80b5108000c0005010446d003600c1202c1d0086090f5100c1c42c950025114007110400d08040d504209040b4100b00e213000b03045a103c00c00c159001425030310050001103108004801480c407001d000c02c54524000c02c03000d80164a044000c0c17045a0344480d4003078101082542402c1c004101c210346c24100038481100503055030805428400300701c03a140795001242e2600504600400f0340c110200c403c20420b110341d00000700302d881ca0f16550200301c0b0300091143c0103100c80f8124141c4d0303006503404110085550180005000c01045000d0038004140f01c031610503440200284e1910500054113030142018078144061461a20b005003014418441109a040010138a6541c0d4a1130010b00640c03040d18102c0008140b036040d182d45003454080c0030305a85250388109981c034101b9240002d82e03008412141c04500c1020130026068030f44e0301c21480900b1061007002c2103c070000390800d00b0744001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 601150386 1250 601149136 601149139
    0x7020f0118020d03030b03030f0405010e1c0206031009140403030b0102070e070c020d02031015140a0504241502010b0109030b060909100f091211060c13090603051b 72
    0x4060100c81c0802048140012059044589603029441802c0c202c0082106800c0c01d070b0548000207841071481340e4230015104a5400360b9505940b00443c0c01800b075403081c071080d4052201c040101410061a0401c013659204d16000b1845a1040c1c0c2c49102d041601c5680c80440403000d1180288030034540d02d4000c05103058001c0c0000d2003041c0ca4480040f5904400904242c10011002029811581c8411600c0101500182259072054000d11000000c0c0b008039804200118070190000342a070030110603c2d03818100402400c4617134034042c10f1001411018070307244511b100b80d88558043c2440c1c3d504d503102604807000c94240c08030505202908442c0c0c0c04801e94140042d218003040001c210f010419440101600d60300c100d9140c0c000749610306820300d802d15020311308126207141847d280c2e0f0701102c01c80c3d004e210340454007007000600782e451001007110b040007604032100090b1f061200700010440028184003001081c0e5881460b1400c45203690400c03107e6400c14141e441d01e01c4040020062040c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 601151636 1250 601150386 601150391
    0xf090213020a020718020405090405030a181d0705070b0412031a0904060902040b032a04020901020a061a0d05070906080105100e09010f06030f02040f0507020327060a0807020f01 78
    0x2840d00d000313560750b070051040711210750100100c54624616901a070f0010040500098051f040514000f13803240c0018800380001001054082110000101003108590861030303103140c4841001004261800001c1881007401001c11500c000500f010020342e100300e004035a0741d07541406a4100900f03880074905119030845000300c04082c00d580b0100d06a0300607a00070800500c80c2c01030b10204010340012640340c1e0741070140460304154080c0c541280c8140006000c0c60b80308864014013048124002c2e41d2006005138004c0580324006882640031074103401d0b01050302408110400009000c6902c006130407545900146020030440781c0900031000a0f00d1a03000a101d545404201c41e50302195500c1030654080d204008101056420351100d80c40481c4040e0a000c13807038403402c006240343d201d0742040f401a458182d03071080d0700c100340c0300d280d004507542d9001d503181011060400c00c0b010910900f13000940b40010811496a48030700085c841d840250711241c40b030b8642040c02030f0404008015228543c0d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 601152886 1250 601151636 601151647
    0x151e0307090b03100b0c06012c0a0509010e030a031409010605030619060e042109030206030a0b0307180605090c0406050a200f010f060b0f07060209130f09021302 71
    0x5402100740340985001d00d02c29a00c9503107550488400f0340050384804148600043c0c02c4d80501d03404256035044e41c4603a22007902c0b08051242064000300c180003c10031010360040030942641180d08900d400400c860008542e2800207660030342107500c80c40d10782d0042071350340280500314850500603036406260300c80200011340ca0940800e80315600140702c0c0c25140c16888580644c0304241d840040a031180b4840c09401340350601d0031070f130f200b1081a503001011040e0001134401034410900c80051300c0d8090156411501c074001c2084c00303003110340e02507503043c003603d140031807058882d0344402c8c41ca106205001c9030b4180350100f400101d030400303410302d91240001c1006009040d0070030f08403080e00d0203030300d8801040400000000c0080302180402a0240211641c80c0c05003081500000004440410704000c00c0c0c0d83c030750001c08103215443c40d0601e01c220501c81400800d440b54003816511300f015200e20350341200603004604a80714001c98030b18503951280e0f12020350604449904e4005000d0108500e8003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 601154136 1250 601152886 601152901
    0x100f290f030613121806020c210a02010e010302040305060c04090e19020f040608030a12050907080a0204020f090a030602030906010b0f1204051002040f080c060f160f02151e03 77
    0x19400f4002411140e107110506148a10a88001d00003000c071140c200401622100003d49a40c0c42d000782038401d03019070f84100503071440c820b664040009080000c0c048001c0707550040d180c1c5c8030a03840a0b810315030b0074840000450402c0c0706140c45600182070607503030b0350f0811210300112100314442e42c0362a4001c681600003001254041c80400d034048813804005003c480008001e446c40f6048400f02c3d00000c2982d070821604034102100d5452500000d0025030341343e1b5100e130fa8986e00780c402e07115194000f5074901c026040c164010004440107405840c5014105d01c040743d0b1000443c3e00490f039080c2d001040180760a0305118060241c8058a20a850080840003895241c0204505480081440da02080c00c1001c10001441d07100c40b5141c0c255143c0c3e42d201c000c4a20310100f07110b0919103002d05800c515042c68102c00b00c5203d411076030411401d01012000800046602104c211024140e07400d07100c000d40c1d1484091351190409500d903950303895030a0708818a00045600000701c0e21024024072100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 601155386 1250 601154136 601154161
    0x7020a090605180a02130303020a050c01030b060a11030d060b070b010603090206221a0a0306050907210f110d1514040903030912020606090117100f290f0306 69
    0xb12400380300b840001c4d150010294020300c1460f86420480e0b4896000008040d0041110b400c131600840c1502c0e020480300c0700640a544030000047e9000304e0812080100e0f40c003c070054002010305004a9080941c40ca0740601101c0c5641c1100d40c080b0408680c2c0310400c4503001314180948414a003c0c084004681c0c042000b9005146050928009000000c0c503030140f1100490010b20340c07503040602603504613030500c440390321400c2000300007800c3c079402141c0d504142c00002d001d060195190003600c84101007156108203d2054821015111000c11405200341c0c01030410b401d29008445942d0300c0c01c1c0c1d581d54100c810f5959401c0e8200003000040083e1f0401c040300c0e00314000280d4011aa400c500d1508500a0082800052051010f0000580c0c01d0780e00140d41c61240750152984400c51f42c07641c07003016410340d9080c5228076950240307608807001d00b101d420500302c80c0c0c410040414003c4041c0c520001c240920700403090b020198840000d683e14080e4008c05419809602500380c5007031502c00b0418 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 601156636 1250 601155386 601155409
    0xb07110303060d05192301050f0612070b030705190c05071505040f090504030e0d050309270708150f09010b0a05040302060403030f020d0801051e150c0307020a090605 73
    0x81404421016402d02c60280211119403030300141d141e04035175051070119021440000c002d5602c4c40e5103110240701007014880c0b2070140b1000403951100c1ea1307880c420401d54410043c80d000241c052800000b544203c0d0074061070040c8032540b180380d240c404520050b200c6100354104d0703800f005401d03c49240440d0001c9040e4098801101c01d000400503241c0041d1800d2040360702038816140d02320310000da0440658003040c000d9203c0c1d5a00060014100d04204050602c0c036409041c2c0e401c1008100042c2c9050024140802c40042504010030281c40384005c0345402200d242011416403030404c181c1c44000c100c25040403130100c40c00c4036070390000004648051414018001c14407400141140ca586c0983c1c141c80085500804090303945842c0e01d07005280001980d4200003501c961a01c6400050003043e81e14140c0d14003070320482400400c200f140302411980980c8a07000740362008500007841004004013a50001d000046a40725201d205101c070080345580480c09803460100184250350328448c2018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 601157886 1250 601156636 601156639
    0xd020a0f142d0403030909050903040f0905061c0b0a0509061303030216020a06170112080712170108010b031203090c12011103070305041506150f2a0b0711030306 71
    0x1c60740b60401c07140c0c0309034070150020840e609102240000030550b000c06c40c0c1c41603a01d030b68010b000544407403480b513030784c0d0140340904420703419043c0003400b6041c125441070f540044020080c040c40e4a8911852170005811300c010380b00d141402e4200301000a241c01025041030f54100200883c0c90300700480c0845580b0320030018100344d0001603241140080d80751a450068008264a81852351132a01a044600040608480c60a030400004484a100c0700c950110350300803035124503007411656082d0218180705c0c440404d0100c448040c003005400d00b10240e020700440400061855940c1d810186085001042c507000c40b4401c20410004200c0440e60b00c1004e0f81c05d58101e06c015152001702d601400030741d000d0145084002c0100b0041d50b0b07240e000580240c0c00744030682d220040400c041400d4610341d000d50034510f074095081c21880c0d4401c2e0485c4403541800e05c0c0c028460403500a500c205e030b64200741030003102c1003600540010301c0f0744551256080b0301a820030100503510450601e480303000c02001603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 601159136 1250 601157886 601157917
    0x2060f09010c0b0a0504120203030105010e060304150905100e0303190903020307060213060806030f1518070311040506120a030509010306090e060a0c0c05060a0509010902060d020a0f14 81
    0x148500c0c0d02038000050324590102d490443c030b1a007902030764000c18007290151092030a0400d03d001d024000700c201d9060324410795071100040ca0040501049900c0030b002107910100c1c807a0551100c0a0700d00c40d100465220301c000c2e00c48049a00c2040042e641c0d40300c0c44001607041002440074111580801b00c542c46007c140c0403441c0d50032824160b041d0b00445138050410717400007800d0a42d09070001a004181c9569444820882d119881030542d5500701c1d0030255601d6004d0440200348048844801c0d83c02a807001d1002c0b048007021140c4c42c02d044e0564812114022a038411079030301c1c40c0900030340b5405801640c0d0f41b2102907001c9a503554403d583d60018090210019100c41c41c0e0348207412260280031b0130503045c8070000c0c154255a41d40e20013246c0040074907141c9188100500e104064540c1242e801000500080d140d1f982e0382c000400001e450f000b0103650b100c40302c50040c1c48503005804210440341d4016114000105d0182040e05500b21803400c00c83c0d81350f1401050541c00c42551a0300c4030a400d031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 601160386 1250 601159136 601159147
    0xa081b0f0105160c060207060801060c0b090c0a0e0105090a110d020903030d0903020f07060f0e190305072d0303050313050c03010e030d29150d090602091c02060f 71
    0x10b881500c2241e1003100b0a000c810b010000384030001e008101110b1803a400c994401d680c03480c040f140200e081c00b8020010f82091581170100e0300740030500350018801400d0300c68810380e071000280f083c20954811440e41054000401261820110160b03001d100032206110b841c503041c869180c07034030856801c10b5a141e808215803809840400c00d0390703003074445944104040003607801c000e980c80354481c9180d4418400c0f054081021ba1080c070b031007808044540c50301c1c1c0714a400300c000c1003000c01c01004e1280381002d01080000101d90704000782002405424511501c0c40800341d64290500d150014035038242000004c1000000e61240813030758004e204a0440344580c00a281150520300401400395066080100c803a10020010000f80b5580e044044200568041040011181c4042c99140c140035104082d88217000c1c1008010b1011405040b5400d618100d00c4030318120860700343c00d80983e83d10303a0102e1001840e05040541200c109101c2c0b410701000e803401e0f030014004c0d02c0cc2907a80365108101061 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 601161636 1250 601160386 601160389
    0x7090903092c040b090105150a060e0102030702030604120f05040605070807061b0f0e040e060f101815050d02030a03030b03100501030b090c010804050705090411030d09050a081b0f 79
    0x100d0402c858100446041e45050a0030700710103415040d5001038055180034003083c0c0410f1144000d000c0c07010084c10000249180410549020311110040e0381540000c00410005170b8041c06960300c80d911600041590508241004100300c12450748601409001c00c02404126081425031f40442e90240801d5903c1c009440c004e4007038a0f00c01c02c0401848450140e81c4d80903a088001c17110120b0403950703041c0300a614001000141d5403058000390290700108085031401e081c0b183e880d517014540c40350b068034040c1c0e44e54518040b183c510490b900159502c6c500c4a1130320009068400c0108800c482031039501603c0e400082d04c488506130000c061541d00d8081e0552910240032500c007025001c0b0041000d0b41e903070700f0b0886017400112000501802140401580b6601440c842c80c010303078002e0010f00b640c84c1402d003403043d510f402810a945801500c201010196010010641c1e40c030700c0d96031958252440c100c03e1055118954000e5032498000705492081d080c041716028200001c11a481003d0903900710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 601162886 1250 601161636 601161689
    0x90305250b0a090e0a02130e040f02090703090b01123f020313050a03052a10050901090f150e040b0406240203030c18032d0709090309 59
    0x81c4410700403a07011901419840c1c00810301821201014450203c954070895028224400c8410916000c0341281042c4004c01a8120640e0300c18880c2c1d10003c04030b80d46800203121030908440e07010010b92200d49403c04c0242001d5843d0040210b80b01c000030040c80c90381c23401035413001007966103450000301c10826401d0303040d9400441d00b03492031754005240d0448514020b4990388021200d180000c07500500040c5810004022011684c000001e0000c600c10441c0c81000c080031249900240f070101c0f600c4e0401ca42d04c0703c840a903401c200b5101c040d48d54100c03000141c0aa0456803108200e21084081080302c054042500620b694407803030305c00000c1d05801d0000f001020061041c6421614244000c120240c0107491840e22481101403628503243e00c8008a9072031204440c201c40c0d0300414003030390401040d01040314031080c4005056960b5600b000c1344080101041d036444500c021908c940d41c0c5009002444010042c10520b00b091084143c0394801400e608040d00c030b282544d130740c800000b040c00706103031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 601164136 1250 601162886 601162889
    0x30c0f050a020618040525050a1413090b2e050d14010501180b04050d020f0d05030a03060906050a0b030705120c12070329040b1207080d09030525 64
    0x10700c560b84a00c1511203480d050904030751913070300940c580000301e0540c506440240380a6100da20401861028940040b2032940110f203282d0140804400b080d4441c001c1d2001400c0c50703280411005085601d0014090b040e074400542070f900a00b03070101d805009159104400307030410f403241030f1740a0281c144141200c0511400e12a00550781c94681c01144c039803c428000c60403214242e881d00c001c00c01940a800c400110341c425007003151700c01c020030092810015880010039000520b241418103c3c000400c0120083c404222507503080060110b00003a0144035810107412000c40030082503003004007040c0c1c44880d501404440070000b200064601f44140100c515100885401d1691800d08102048d004d400000070004c4000ca003100040880c0d220b480344603100b03a42e00190100c2554025100500c1c1c2d1b0401a074140c006880321181035094823145601d08904030184010300c0800d14140409041c030320501c01c00c01c204410400e08201140d80043c2038085280901881d030201c080b03041a00300c0c034102a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 601165386 1250 601164136 601164139
    0xa050f0f03190c0806010f1e050915040e070b04090515031906063623010e15010c0809031f140c1e0304020303040b03010e090c010c030c0f050a02 64
    0x912542418102110442c1c004243c4940806a1078a4031000c039552a01000d01070014138180b41402005075000070007461800354414501021501c0d2030b1000b04203a0074044a54510510f03240010400c282000c1c811082c9284101014010250601c030455110344158032404100d50b031504041038000008a0b03d04c181c080d030040841d00d020405a81741e08000c41940c8040e18201d141c004006440380c0c400c00f90030002c00300a0700d88039600112a000098581c040c0091030300c415602c1c0b417005a82c01039550461628542040409207540c50840e0340c08a0520040140c824003220b00c150854690b000b900101040d60b0001c2440d03220801c4501191400340540c80f6080113034007003034a4121380c0c0750b9a40010340d5000b60320000600750780d8001c80d940b150b109010070440d07058500164020703020300c0b0101071900f05200034156441c6c103035680043c2255420070382000460710440418044030000400180e9510a02070030560400c40315518040e181c4250104041c0481716803940100800200b407040c103402035030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 601166636 1250 601165386 601165393
    0xc01030b013c0c1208040f02010507050a2a09021905181809010c0305070210022503020319020604030806061b01090b090c09010302130b01050706141902090a050f0f03 73
    0x100e100000b0102d903806601540c4035154410100c4d1100d03c2241ea45104030b8201400185840c580e50045820794040309060b5003030300845010f600091810942950710040f01a04c401600018102c0b6155010090344079248051040001070041d0000d1524202c2c255018100f280d10b40b00b2800511503442c048502d0103a0050034800009100441102c680d8003d40c2120000c1045400ca884158102d4a0541d0b03043c01581c000090304401c2e140340e4000300907140a46200144280c001c01c601d60078180240c10032405600040b80c0031280c2400f41c150207540340d21a100030030560030181c40180003200302a00c0d603070160381d0001c3c5203801c0f40107400c0d0380c01c060300520008200003126820040c10000b815034140c4268028000c41e0500c515121200c50b050301d0f001010813200d0542010304c04005c011040d545070500074140107003000f090709449048414000d80e00f0350880d42ca040221002040c00b04e00032140040c1c8144080c0308581c94020307440055580a68150320700000317480c0062a141d4020582c02e52511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 601167886 1250 601166636 601166747
    0x30c0601060302130e0402030a110d0506010e0a0e0304060509010c0204060b1303050609030a1704020102071208071b03151a151314030a06150b030c0c0c01030b01 71
    0x40d81a8004c00c0d1901d00700c13035107000b5152200c3d90403600500c141e41c007035172580c000044c941c04a45801300046a03004024084111101e030380c1d44403030401c84268069033603008000b0400c4010700c182d0003428014038081d0082c606e807a0401d4006806400b1300c6021504121051a840c82107443d0755102c000a4007101c00c1c81c5440e9601110940d4420742a03010031501e0740102e502040300c07840000269007050300b0a0b140c51003407861001c072800300504010400d0741180b281041c00600440081c000b02c3c400b6015882695a416603803c007400d05148041d40e500b048000a1000c04c0820f80c141c0710003202c03013051000440d0000e0020500c4481c43c0384150003551004d0440c05103559091070380001d004801c2024011684140c1e5440340c200d1006410090503011b030802d034800c0b00001c00513440103c5425120b5280c13010180c6441e48811180c20407100206640400250300090403420032040381904003d00e810301c414107210000928500c106003202403e501076611003107034a00c00712040c5000014004400700000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 601169136 1250 601167886 601167899
    0x19060e0f04020a0b03090705040f0f14040b06090f010e09011b0507030e060403020a27020d020c2514010302160308060a120812070e040c03051905090c1002030c0601 72
    0x280d00c140c60482c800e00d00400002034000e501da05591150845001805041c1d217400c05102c05084c900c0c0e055840d040c3c0d251900c0060000320b100b01012008000e00807035a600d0686450700768040003400142c0300b18505400c010040507503904030760540b542607030422480c0d1031b4068100e0140175000d48040c01008001d0100e10b04903031000292070198040da6404280707680007814800b8901c0b950102a411150580c014004283c1000d5100c554022000380d42c40c1d9800121241030807078202c1807010000c0e54001a40c034412040401c0721400702c0f0301c10751410b2080d00358031030140800b107841e01c124001d0004002003201c1c240c0c00780d07041c2c4ac0400d440e05882d80c0340082d0707131030b004003e1001102c14620400c4048004506429081e03582c90126601c0203003d0321b42002499054109203008003001c007041401c0c4200310b81510b850040200742c16180c0c50100c0c29007000c052124200810303034112040a480c1608102400c0000111f16851080995980c4c280640342e80c001c81c114451805c0f201d03d1440f0f031800000c0e10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 601170386 1250 601169136 601169161
    0x1202040e011b18091a010c0507090203010b0304060b01031e1a0a1d09070f1215090f020301060b070c0504050606160b0702120a08160306080d02060f060303070b19060e 73
    0x1c22a011a8803040030313465240050407a0f2080c20701c2001d80c011456841c4595000e00d9041003079602450854165507619070000c01640e01c03d030070442813a00080240b00c2040158082d54140c81d609080601c0051501c84440080340b074101c141e40d0f6a9629003801c0309008407034401c0007441e0200a13124040e0540c079114098480504280e9449620000000007080c410012510b80305076450110b1009202d4641b58551007000410310b015208a41c5108040005911902c510304071948501c9042081c0c40d8a40101800c41d5903681c072019051204004407800604416030000a51b00107c90009944d2a80d00200301e547c001c003130030700d00389002070710030302043c002c0c001c401034458903a0781e085031075000b041c0010300e019026081f120404a401782002c01c1d0b642c186070040d01d040c040240750003c2c0b0603594a40306460300c0d15a4504102503044003080c03090050810008542c414000d80003185042030550b59072401a10050a8100b01518142108021411034024200412403603080700001d0411840a140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 601171636 1250 601170386 601170407
    0x411070317070207030201120f0209060309010c02060c1305042705061f05060d0507020f01020a05040509240d0807020a06030c0e0301140712090f0303050117071202040e011b 76
    0x70501407a001a011901c00a4088107599060f500c0c0c841e06804940c083c0041c00071020035040d201d40a0116083c40c1d10307041c001e54801c218a000100301600c403070300060300b0000083c00c600e110400401003030010b120100d501004658050f1b4000545030001074000080500e9030350449100c44403e034088041c07000000d800e40c000d5492480e8a805c10915000051498050344180d94001c101840b06801d00038041d4406540541d4500580e841d50310303001c01d034600b20303800300d00d09101180c2c0103d0280a241440f418441d0b10a0981c4003500c0320789003500a01c0d10010041c41050b12581d12900070008005038407080c1c4d90416806410400700507160310010b4094031241070400001540c40410600b20700d4140544180c403c1c83c1280307500c1c00d8940c010100c1d07070044021843c2203406c0d2185d0b10180000c01e6818480359040c0659800105541400845517010948100d04065a40010014015041d103404c2d0403d00c16070403940000c0c191017110105001d485a07040c00c0590440d01803981c807030190000b03607408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 601172886 1250 601171636 601171667
    0x70e070507020307240c14060f07030609110910050d061503291002071d1b040305030a03021308060405100e030c070315060e160210050601170604110703 67
    0x20f00c0552a81c0d0400d151802d01040245031449480d00d51080c180031b01034001c24240212021000451031601440c80c104050701c00b0f155807600c42c020050420361504c40e02020b4a80c5490600804000000c6a1003500800c0c00311441580c410101c1c05540b8060341c02c440e602e250318074007403005a0790b03041c00c500c17241c0c880c00c56403010a061644000b480022100c9001d1400400ad4100c2c4540c00d0200900849007490f865080c1584501400807900f19a000c08203075050144030b410034094500038094078035068503800c1c600000c50341130000f40000342d8003000355808078a2130703d40140c444c0044155110784034041da101a5050144c03000f40028000301084a481d00803126109000b00140c541c6404d607070340310740c0d1004a0785400c101c00600020344074445072040100711440204c2d419465422116600c0c1065822820605554000d1034109405204600000c02c1d0035104000c240791031000601900d00040c4490201b10301d500005441c2d5469074442444880b051101648807100791a000d4010401006841d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 601174136 1250 601172886 601172893
    0x41418011e0b010216060c120210090b15090702030304140709140f010e060a0509090c100908060a020307090b070507170d080f0714070c1a0a030f05100512070e0705070203 75
    0x1d1320444002c00280089a041e551240341404068681422182090703902501314003840d140ac0f200601c0c00e0242214440c0903080041c0a03003040b80407c02c17009080040c5034003951030f03070003007200043d00442900c0d4403580042022956400d00890700b810000340d5080400c02901d0700302108810b500458401d41300c0d40c10005000c00d940d07241c42c1d003c50042001c0300c040d584400083d9051005081051207203402c400c903002214044410a4000f0b0f11448410452701c0c0022a0038100f00300303d140c1081540e030800c01c080c1c0d0440c5541414207006020350190301844208203400100d1608014080103950020102c45c6d110b500403400068400ba01d43c003114100c3d0001a596030040b6684600c6240800d0180e0155158403080400281d02120142c0000340145c030341501c04000050300c184c44408080c0c0524204007455524018000d01408623418a051910080c0c0381008200200d580d80c2c00703103030650f00101d0b0104111007959844a103400407580041348407d6409003480b4005401c4405009450300c00c9065 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 601175386 1250 601174136 601174153
    0x9010507030b0f13060302130c17070c02040506060d05090607141914120a06030b1e22051203100501080f0c070f23010b041418011e0b0102 61
    0x7142a00c441140309a484009081000c40515042102c050401c4185070f010900300e40d01c0c1c002811064030746e05c54451040d21140304507c090303840104941e1014490170005464246994000c201d0344411500a000f140e0310000301d00541d490f402640c0603200c01040900003850320300000f60700c9aa041c0d600402085110060014a0401c10181c407801d0341d0302070520200301030b80f001c2100d84014030b04070900d00c50401c102c04007085240d1488113206d0f0400750f01c0803c0390b0f89036192107034040c0c00080800030346000c501c11a0850110120980da000007d440e60000200c0400b91540c1080b121460010322500c111002c0c00060310b403820145100d102e1107071881803043c2d075540055a03200070072074201d406000b9400c0025020328006010782210381c01f441c03001000d544c1658910840115081000040c010103001203101801c003400369903c034800540b001c0c440d040d0b01002006800401030101406c899294003500c901400951040740205056000042c400d401c0c000b044004050711044a401809401031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 601176636 1250 601175386 601175401
    0x40627050d020c03060f0a06080307030207050307091b030902031212011e0303080c18040612110402040b2b050c04061d0f190807090b03011a03060705030a090203060f090105 76
    0x43e90b4070b4541024018000036900c1d105c1a103607200c0028143c90f035140c3e58100c08144d040042000d407068920a800801d8001d00300810545003029a60108071031500780580d03229903c414005100d82a000350502044002c00d910010f0b050103207a01075000c0182001c259105400d1400321480d0407145d41015800c410801d001c0d0020080c030f0071380800b8000c07900711f1022070385140702d1800802c429800300321001c4030801001c00081c15108198016049070310b203030030900180154403030701041d038440807502189060324080b001c083c28003c0000c80031443c001031600c24100035080c8140520100340400c10080bd00e082601030007150841d00401d000551420b5209114000c0f5800083c1081001070080100c481c407002005030768068601d00b032103025010340c0e001034110001c112110142442c0c0002042001c003600506003125030342d041c8072071801ca289074189102c1e1800310303060750801e20740d2428580d42c0d0382d001c0d440741c00703040800c100035014403c1c80d00300f00990301b03141000f030f00074100c0070000d0005885400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 601177886 1250 601176636 601176643
    0x1206181009140705030f0c12010b09040c0309020f1903050102030901060e0a06050d0f03021f0516090b03010b0702062b1d0d080a0b030a060b01080705030c12040627050d02 75
    0x83d422400b00c3c10800c046141004490110740d401540c4641e86071403e8001820604280406c3e130107041103a1011a0041071403a0600944005c40558030b0108240d400c0c6400041c600016421800d004035103401c026040030045040e200c0107142c02c40b00940d030328140800c440e030080500d4407690251601040110710042e1850044d5000c80b1801007022a410741151661540b801f000c1004a00394810880002920b03081ca0080700c904042d1244001554030b00f119091100c0303000011703803100700148500c061140d102044280c905455010050644818280c070109696120f07421a0009001006109a5150070b81c00c030f40f01c04015090100348034000085c6030300724448055140c80c103125041034100b00c452034407a400059010008540210b00040d0711030100b403c0c03801140d01519083d413260300001701560090021354015000b40791041c55454141c80018050260750310301c059000098003c0b07020312155070401031005003d80c000c14a40801e01d181d409080d26201802c076094080c80c0d400741c00e280e0010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 601179136 1250 601177886 601177891
    0x309052b090b071709120705090106020a26070b1317070f020f03010f0905060a0e0303060a06050f07170c010605041e050405011b020a0c09050408120618100914 70
    0x4096460401407542e6450120300d03038001120144d01c5050203045511381d200d1048120420ba0315000e0100e00e401c0405118110740141c1241c8155030200c5020f100040c2c00611600100e4000a26048c0150907102d125400c0d104941014100030088010b0250010030705421030303070a074410144000c02200c5004040603074012070a0141808041d8130000015080c442484807403403e00500020300203040c40e04010841e01805010344080e80302400708801c07a01c080c440c000711035460358015070035880e1641c00071f820f981e11406070300200040802c41c0c59141100d42d0546031030702d500c2241000007182440040843da0401c228803040703582003400004083c2030034400c0d40c0d490341c49206002411170300c1e151090041e0070041c00858080d9038a0507900c00214a40e00004400c5500e80c1c05440b4420850074041002c80c0240c0080c08200d16020511001030700807021907282d480180020112039403034800040c0c030301d005010b081c100c0306084410040e501e4105000071041d10007211040020800c042400d00307011008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601180386 1250 601179136 601179149
    0x20d030b03190b040c030c0b0a1205010807060c050703051f140103020310022104050a210801260d0201020d2921150106032a0509010309052b09 63
    0x104002e000b0401400c02a540540140d0003550415a607031744100b040380c2180c1c419000c1c07800101d0070490444e4400c00c0340301c0c07030500881e00344465418851220f8842180707100380301c14031064510140c1004028880b1100642d009020342d45012103c0c482c0a115406e10708032181c4591501c4185e0002024502a080c140e0fa006401441c00581400300003009501010300340301481c0c221602c3ca400b00a038404aa4402c51280e000f03040452690310300a0745010307140020f5441d50501e29515401240e203d0100d0741147d1181d0007907119004024040102528400b01982090140b042c001d19071b40d4054004010074090301c002042015803400d03079111050241000741c4030341250366002e200d86117014490601460001000031680c403960454591514400300720104c821804000100705158142c42101c4000383c0300c220390820280c0040040c41d00107020b00410091000100706034206911940c803444246a000d001c540024464940b030384012042030f1040d9044030100d04a400c0c04511034804803045914 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601181636 1250 601180386 601180423
    0xc01091703100b0313021e01030b0306070c0f0c031b0317040b03010317041d01140117041407052101150302030a03080a090b0c090901090509070e09070b0a020d030b03 73
    0xa005680302c0c10b41c40905100540d0102c005c4550140e80e40039612600e0070401000b4103150421100003400762595100d1031807103604000100110650401e01d070300c0d0074650141e1103030007103100c0f468880701c1140d0540026200001160f103e10000341a40d044034140c1c1d005541d03220070703010101ca01d11030341d1003079004030000030800b07100410004078956038410038261310303051103420140c40d08018400440419a0154803404440042020307503620101e03400008802c0ca0b18040038905500d15400d050b4002d803004200c2e00c1070044803441d2000074800d510203028024040180c01d1122004c0d44560010407650702155407810070b14070306410b8050340c83c000f02c0394040c026041100302c0762000e585044005086c01201034844100740b0001e0f4100c104075228140908185032122685c80c00e11139038010580040c0e003e00c4c6440300340207038241d0020300f880c11541942d50031552070362110445820102a80d220074000180818000401a0080f40c410007600711580c08002a101e036004140c2e0720320100055842102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601182886 1250 601181636 601181639
    0x909061501110a050d09060306060905090f060f09070309140d081602031c09050606090402130c171006080708070c080a020a1506082b05070f06020c0109170310 70
    0x14080e04103030702c1c110204015129105556181c660034403005201000000707400c55403c2c0b02c415010320880c806003441e450034011090402000c030310505005440030819101200c0001c18558a0042e1500ca4040141803d40d503400e100030041c0c042c5c64147c034202d804401510007150004e0001440b10443c2d2030503030b80c0070302a880e861201c512902903026903c0450108110703130f1518003503c602e611070003c41042c00048801241c10b04608040000d00118410f4000109100142c1d403002032544000816110000d98040032030f505950f040c42901400034402810020450303490916075415041300c0c002d85070054280e40b6480d040391003c030129210381c08288a00d90501c0841d03069005000340c41240d00459400001a0b120005800e1229074141d142903112901401214002d0004100a00d0314000c00b0000f6a1091801c5001564a03501a01080008189803003804985280f8400c22500681e0031950f40c4120b039803182c003034400c604050b1411201505040c642d080400100c0e8032403014104900c403084d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601184136 1250 601182886 601182889
    0x6050a11030c0307111206070507031e02060a020a0302040503010f0b0f060c0d0c0c051206010602121608030618040515011205030316050405040f020c0105060612040f0c1d0609090615 80
    0xd017a1884503070400705802442c07012040c1000fa017030003100940c8840e91100224940100400a02180304075040304c6e4440000d400d0703400080303560700801c0101000d81c0300e0710980000c038024000c660040d035140d8203100c9000c040301980c2d40114000e8501780d810245009071201031045610030380006110070b034003c61801301c00034801c15075007040e01e11984e010b890040c2d0f1107001605c0301d031600240802940040004000d1241c0401102c9411403880c11601d080120b5000c091840031183c4070050140440000080c0d00da54440e4094014041e100d0409480c03800c15040043c1d440c0008242c0e0024050404004a01070540d81c0594141680c450700441c59540c0301a0044201154080e60b802803200c103100100711569503009415581e03925941c01600c828100104c0c50035a04042c010714042c00c0c0c20003200f5040c590008000390b00c02d82242c0516010101880e11001c8055a070b8490791401c071020009800680100303621074000c1100715007512127a1102c95001d512440c060300c024011484005100000c1d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601185386 1250 601184136 601184153
    0x301091e05071205060a0b030609030a030e190c03060b15030a0207020a0302040c0203070b1506041e120c050127050d02010302070f1a01060305040b07030f0209030706050a11030c0307 80
    0x529201e00e055a0030380d6940d145034031251003a4a82100c2640040040142d400d2181c4140c1242e900b04038010300281c00d1040226032203114120b0070004254807001107880c400c0040040404410322000070014071801810606000c100b94001100e455040258511031494804130400341da81c030051400c0d14580700d011818000f940049400c1b600303c1140c41000015940314443c005240c40ca680265030340c0c5000b842d018801201c0200000b180480e5200160b215455400985042c3c8a052013050f00c03042c0707103c0749000240e00f43d90002c20010b1600010404203d000c1f104081150400e03258003044081103a10750000b4a400302001500301f01401c420030403860407910000040d030040c1001450304103d610b451001d009007441c2074400c082500d0550340c900c070300e450100e8014065854204540d0400b0780e24030080c2c610245c804401c0580b561211201c201c05681141e0903100020b00701e520082d62110041e007242c2201075180082001800d445400a50200444103420206e00146140c45882c0d0381d103010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601186636 1250 601185386 601185443
    0xd03050c030a0b012105060f0a0b1b0f03032505191818090b06030604080706090c0e0a0506010f0f020712030509030304060816050403051b04020d060909050c030109 72
    0x100300a20000813400110001a03148012456038041001e1401c9000c0c448c05d42c1c00c280d50316010b071380010000c01400c8440d0041c0c80d148440030508000e0200240600d80c81c0c8070a800d152001e45c000042031207035034220b250103542001d110403015040c06415060583c0d10303000c0c9150004580361a801250015803240782081000384009041d2080309841e00280900808004800c1031038a542c0c03c2000b090040c54216a80d000380d048000744202e2525a50b000420300448600914954031500303607000b0045491a940b000d0b01ca120301100241c90041808000b41c0385c26540e541c045110071520b00340da01c0c03040c640440a110607400034142d091900e03001050201c0704000c243c00700281804849032a03a42440100014003492360340c10304600f080381c6400f40d200341070140c10301801800c2008000080c0701044c2c0d80070400190f050000030148a1300450042d100c4c4c42c10541107603141c402c0108032142903a004898041c06101244c84045005040c582220303903a1001600700103003c6403014281c44440500702 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601187886 1250 601186636 601186639
    0x6070f03031805031c020a05070b041505070206071805012a0f0b01090606031e0203070c0204180b0f010b0909150a0b030103020108090c0a05040e03040f06050703020d03050c030a0b 79
    0xa01090900031100c1c074000495400c882541000030780e03178040c605011222680c074107640350440c0340840f0401c0142c80c03840f582800030700c00c140c0c000c0014148200c0164440c00a851094144100c0c5442d401c022745030002103c0031130209086448480001501d682c4507825503c06031102a00e01048542810001703030041d2014400c20780e458203180000d0030750f907200c280030381c4201c04c201790701c1d410310850354140c80072a00000b0805160000c0c0c0312448401c011454500911104010703600d858401003140c0301c032500f130380294029003424022103d8442c004040341070315010301c0d8840c41c030707485540310070050780020321482c01070318000d105141041c03030003d00c1c2d0358102e40d40c00c9404514040302000305450f0305480e0b12070021040040010000d550308031910a03440f1400c100504046802c28000a020181d2409103c0c021075460f40380101c0901c0820448000e48504110401d4a56035118003c1081d03201c040220011f020b440644c3c42c0407802402524018024002211704503543c2c2101c11300100f0420120a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601189136 1250 601187886 601187891
    0x40303121d120c1c0203030414010b1302090102010b0d08030a1d0705010e06130303080109110a080a110409060b04090e0a050715050708030a0c0908071d1f060302090a050d0206070f0303 81
    0x1c4c81c281103003210000c1c204400360059901d901c0c0c81d0906c00c40402c4040c0707a40800b43d06009400c40c50341d942c40c245c1100031441c2000180c498035041d0040f4018064800402e801a86105200b4184a18007018621448000f003050007005189000651040041e0300c40d0328040d440b40005120a40c0a403001d0030103010040c0009041c801c0403122005610060b03413050b03010419100c01807007168010b0090032403103880c0400702880c000c4002d00013404050002e084503d0f0641d10039941c81d0026030181154010200b10300d0a00650752200e00b11021035100d4802e05814034175000da0719128003070104d141000c60307800c8400340240924264240504c00f01289c0803008001d0104045000901c0d2000a98010010b200c000035400c1d14001000c2c20010440d0440800c69120100801121500d000c003c1c80700700103002140c06a898244e101d03401c40c44902040c103920800c0c00c401182d2582c0c181c0c05000d000303100f20f800780e2450f603580d400c0c480310700348260300a90401020403e0f40f000c2880001d64203940c51103403800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601190386 1250 601189136 601189153
    0x10c02060c120a080405011103270c03030c010b0906040902030a080c010b0904060c090618060c080c030705150a05070c0b09070320011128030e06040303121d120c 71
    0x20440b15510006001020a07030440038841400401d200750880012040c01305440c6080c680700c02070445004601ea1403000203904507500e2451002c2c0900385007204050102c075200c8180c14071403800781c54210091800307070031083c0000f4070314030b010f0041e4040d1503005005000064440d0b10746d8040c2e41e0000074140320b99921501c00001701d0301c581c13000030f1141c0d0140000150070180301c00c0040c0381c918140e04c443c00304000e0100c40101c52001828800032243c6c1c6081002c0c1f120302c1c40c81c2401c1c441c02a00035808041c000842c000d010b0100203d130705004840104900c01171a501c04508004031a015a04030001441103e5100d00103907002c1506500040b2460864003540d94030360f5004003524000b00b4440301c0117288607801005580000118200d114520054240c01d420046c00320440a41c50021071400c0c644d10b1a101c0c10315008a0081d80d803080c019000d01c4d40c507074aa00b00607190710010005c0e0805146460380b607102070000c1c91603c446800d05071010380011401200e80c041c8a0700814003954641c040d00d600e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601191636 1250 601190386 601190413
    0x2090403141201092003220f0c150f0f1b0203060702010209014107050607020303040c0602010905060a1a120d081303120504060209030303240f010c02060c 68
    0x1800d82c518400b55100103a604241d02c41007a80d82da0080e051107240304d00b542010042405083d0b0b54803a03140b40300da03944650b4101c603080d01d440140d400a4030b0729070107104074828401010141d02c1a1809011103428071411100129120300e0141d0350320000612007030f0f0040c0e403548900c90b402c0745500f0440d01e19a0051940e0006410407070252901030140c0e500140000d95035070455244554036000300700171301e1203003580c030340d811304640c440940324000c0e00311150708014180e24035042d00ca00039008000c0340c0d20742c5044500071355280e005a50035212111424030007d0080c1c4140104120039510401030225030300c452078801d000d02002d0840340c040c10041d5010300d0315905c1d0010408a030000c2c5100410352a0300d840c01c044c118080290591000c5088550b40c0c0700400d40000381141d08005100001a0540d10341c00e0480007030240e070a0f030960500002043c400354400b8400c803c3c032032983c0c00c419004c0500c900341c10007000b04e0041d002c0d5408140007e5000c40036150135405000c000482c40203840c007413241d004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601192886 1250 601191636 601191677
    0x30118021c020d0510061b080702030f07080a020a1505090d02040608010e061b03010305070b13050901030f03300207020a0b03190e031e1e04151205040f02090403 71
    0x2020f040300c16030700e0003000f1445c0107208003800240181e003041e00a076400410a084614403410002d04040e50000728502192402c022181400080701301361020340707458102c0e08d0340320500d1002c1680b003009103a902051f9804c0e918403098041809840711403400041100303004668807860426030341720381e03600030015041c4004c1c00740031a580240d5000d8500343c500341110402000c54000c1c90000404c083c001800040c0307000900c10144c3d81c1d0400c89648441c41031510044011141d00030700e81080d09000000f003000110303110494050b119445451a00d203144030b02c940e030b422044246183d030720302400b0201a8581070386d000f44019800a00034a03120350729140718903030340d41c4107950007800e207120f420142c00d505640380720310200b803c0c3d40c2016500e8401101581d41081c0e018240c1e078005a1000154400c042100c5100815101510340c000c81c3c84a584861805000e80002c41c90f402007140141000e12a00640c8500c0e4070440d404030340c1e0500b00740c581c0c080c0701303100400410031001d01601c807015040914000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601194136 1250 601192886 601192897
    0x15040c091a04060908070302010c030c0609020a06080a0e010e0d0f0507060218150301080a0803060303070609030f200a1704212a031103010b09040c0801060506030118021c02 76
    0x28910380d0ba0791490480c00a01148a070b5000c9043c80d08a48801e00040c0c0e03103c0d9101070120b41601d081c0300d00b00ca050034210000c004401b0029844900300c4c40c0020000d40241500e4032400221000304141c1c81d4840119003660b00080f4100c00b2a04004150100d00340102e105507003294044c40c0489c2011110f5891800700e80c1301480c4100038680824240c941868030701c00720f100c50307052185480e00315450580d03060f40e100a00d01005000b0310003c00081c03c140c40c10001c0d601c0e580d800040034006240c2c5030401400901c101d010301400242081803c890b22181d03180c2c0c9603030b044020300041001124580300c8651500b1000d4100141110070400003a00c2030205804a403000d00c45240000c100c8682e1509401070303060007141003200200d0719400a01c4110041480c0226500080402c440d07070480000a801020b00d002181e031312040107410300042c0300440640030300fa60900c00080040da6190010000c0f580000d20842841c1400c02c001c25a811000741c0107419182491201c00d4426941207460f44240c1c1c112 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601195386 1250 601194136 601194179
    0x2c12070605101a03060f01050c0d03090605010b0703080604020703030e070b03010816050108190e070306020711010504180b011e050703091e0909050a020d1a010b0315040c09 76
    0x1e500034044800c460654035402010f5020300480d4407511840410814080108614450400c0c0e100b9207404c0c0c0d002e901207948920b90001035804007801c1c100d000c0c0c018890541c090b60a20b19001c008114030700d00404480300b098154175141e08581d01c0d1801c00c0f001e5405200120704043d128900448840c80820114026010000c16130b0f8a9605101c8010300c1e00d11810700e19110800c1001d002c20140c0d80010540e03401005074042c101450300048034400241211103c9032056200d108800410311090754060211b482c402c03004281c048451500440c5c4902031401141005283d14400e0300140c94942d00c803142d401c4060408012810280302a43d5505100982050101e0030001c0c0d01d00805501c0300d0707c1405009926243c20508404510000c901c000d42e00131503450641c2d55100e0000d01004000c0c0403082d6600808107000401ca1385441c2141c040721801c0c000d243c019100000c0303500c035014010341313114494601400c000300d00100c2c100f10180c507201c103650b030034400304600114101104004001e000001e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601196636 1250 601195386 601195391
    0x409061205060c0306013c110c0a0302090f150402030c09010806100807030c09050a0603140a0c08060f011106070e1e0604060305100f03060c122c120706 67
    0xc03400e0460811800030154984040c0070010001240e81089030451445002c0b00d098540040300301c2ca544e42400000508605062105c0d200c004080e440160043c5003a60b03001520b508070200020312582125a00000350f0060b114030000d982580c4a6a40503804080b0100c0d241040d0b244c0c10120302242c1c000c0e102540741e800005032020740d0b560011402ea400110903100c1c4200407089110090106001800d10820151100c8080c8981845801410082d010050012021640d90403010700103001d40d0310440c8140214100003500012079108012444010b910b40074050f0761001c082085501b96038050605014105d90b41290040c010040d640c4680840d88507860420070b0f040400105c0d4143c40b08000191540a00582942d110300082d0b4044075101d08000c0303400d4035001c0801d0451300700c54000c0d4a0001c0c0390100001808a07641201e9424610782d251003040b00340a204640943d480c2c800d1074400420f0940c0c07039540c2c0f4410a03c0800c9021003174400d40f0741911281e58011181e0344080030a880558 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601197886 1250 601196636 601196669
    0x20c040b1c021203071403030a050106080c04051026010911040518090a0f03020102031f030816061503080405040c0503270703080a02060906010504021c090206040906 73
    0x1024032441414110440307140038407041d408400401201c2259009000da04551070b80301a15000f0010384a0080c2d0100203000c0b406195049190341303810072542d41000c2400d05000160305030103010014010844000c5441c07500e03050009001c85091601084010465080c4000d0700324010092520f41c2c44207160210225545080310400554010ba06401c03400ca03000c020810050755448100f108203140804055407550318a90041d0130a458800050902c01c0c03420103c404155040d8010f500c540e680c2e041101c00c88920044008802e0071a0200a21405040011460740440c001c09489031030712030480030030b12925141c1284a0081076900c01c66860001040c02d10192a00d40103501030301e045403500c1800e501e400350000c03a41034902148885510055010042d05140a1012402035a003140301c00c0d41c0c0d800d200700000d545800480c1d840c50303180541d80012031b16280038021205e8034415113040e1310841c0f840c1400c0d1001405440c0c0d003240d000008100005510302c0c0390294100402c040304101072880d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601199136 1250 601197886 601197889
    0x80714180106080403020c0126090f070b03090d08060d1401110a02010e060112260720010f17161107030809150c120901050c0106091505010207082515020c 68
    0x194843d90aa8107100c403200c048411507800d5416180307140c101289c808010789440d00407d0600040200d0131400740100e0070040360304502000150f0080b2038040c125900c100b0842d50031980340c0e009a0b1102d80c00346042040f0302c04030b08920380c2072007990070160000600e4054901030508940c440c0e1700400143c1d455880d03003500d40009010380c50042901400500e140c2405540d8400c1e40132000c02c003016100d1210300c4501d000100c100c10360300042c3d03020035410700003280c00d00e80e90041c01b01011440c0c0003d00c4c1e0071a403803c552281100300b903801d1112150411585030b0b6806843d11104c0c612260082010004030780411007010421000258000c00c0b11540c0e440031442030040d003e10b040681410b205c401c01800d8102040000c1058200030364035855600d6a15540040340d061140d072039600d80c01d42c200344012868201c16401490b071910920212904199034100581c0c940c82d441c4640700c0d03240c00c081d60780100c02c21580300384220000c020340080038985d01c0e20034420b0a02c42a02201d0016030140070458410f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601200386 1250 601199136 601199143
    0xa0305071703030f07030221040305070b060f1818150103061d0a060b01051b01060e150f0f01110f06010911040e1501111e01050c0408071418010608040302 68
    0x5a0841c201961451801203c020b401003030144c901e9003015070000c0c2e000500d400750a503450400b0320b032160b480c2841c242414001d050350484981683e81c0700443d40894803034070b0108400342d001300020f44074001c403250007991501140001016401010313849810314194a40a01080d640c0e060035185081c4107504604020342103807589401c60920003241c2407136403650400016100003040d40b000000c5000640100103e0359030050f00f40d20b04816512a40b03440c0da450041d00314005550b02240140c04944d82c94480c00c1442d044500340d01d420100e801c1aa11480c1050b140c0c1170f2440106041030314813038000720113140c40c2c401c14602108083d08544010321941032640640d030030420603000c0290030127007441010410050086c010f07074001003003036484d117403564014409000d0940101c000e8415500c8007252421342407810781802d040b030354a000001480d0311164410740301900c2038a001042d0190900e201d0b84014458a1621a84450118440d003580030b0b081422078040e112075a01c55409081c5842c0203840d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601201636 1250 601200386 601200419
    0x904090f05010c0e01170703020d061202040c02190809120a05030310050117161e050a020111040b0703120e01020d0603120305010308180117010b270108010e090102090a030507 77
    0x800c81140c1c28880139aa000103035110f6802c40d05003491403500e640b001680244504540089a00d090510000305408810843c81c002c50081d03034144410f0070200c0c0c0490715806150028807070034007c60040000310380060007401c0010005441c2012171031088104a2810180e614102c0b00b552002042260300801c0102ca01c0081c1001e00302420131100c17417248100251030042c005808800300d0322582100ea44101d52001c4600703043c0e60340c0641001040001002c82e444100200c1c0503601b803d5440b132018405038226000c44000901da281424031907a42210b007040551161000d060300c03100039180020081c03005001481581e034000a101d89185840c0d41c80c544800381e003406151a000041000c02c0c0c1c024100c411001c2c000160400140e990700050b200da440064180c400c4860030070001c20303c024200010700d8138112014080444403207180881c1341616107c5d0100c0c1c0090151001008230fa040c000c41e40b500302481000150900e455a00410214170065000341c900c3d9200380410440c4000d06050050f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601202886 1250 601201636 601201661
    0x9090201170a0b180f1306090b011701061211280914090d0f2709020903060112120f35090d0e0906150406050c07092702060904090f0501 60
    0x3025140041c04102e0117200200500d41503084549808204001a40f0080707413664840c00d0701844d561202401c2445e08016030340c4030810744c40d10138081907001000002036400e80d44070391901c6a4400e682d05010000540c5241401210641d8420814108072106154042d0481c9980069801d0000640d00c2641902a1a210154208001e99290603070b01c050303000100c540e0380c20200c41d2851400e03801c190400f0001a4420f400c441d400c0089010400c680040007000f0040f4100c400b16621043c8102800725580001000b00c2c1f00c0c004101202d60094442071103850b400d0800f40b508985010458602100ca82c24a0710710685d030310010035081490780e030000e40207031030f0034000c01c0d880c40c034404098198441811818428860381d07002920580d00d0014400343c3e1406a40e005488607500d002c040c100e038004c2c4503120303e0b0740150300c8041800e00c43c610031401c40f5210708007000c03400b1a0040e13408044034100c00f07081e0b80041c02002102c0683e12640241c04515118030400c48682c0100c0c2402070031034040e4080c40c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601204136 1250 601202886 601202929
    0x213120204060923071b0605090c0f060a030f1e0c030614030304050d080f040602061803190c021813021203090f01050a0c23100507080109090201170a0b 67
    0x10136603a4021050550701c00100e91200015140c040b000d0b101c0d242070b051061a11035100c0742c070008200750398002d140203401800460304001c2041c020081c00f00c8440c100660001414000882264402d800604400d640094005080740010421118410751a5080c0c1c4d0301d6030300c52489068190b40b502c200001000b43d80c59618508004000094480c8164030440e84101c0b08280b581c0d0501c8811411208001c283c2c250550350f0350b07600c0e40081d44904088a480714204008203800e5100d40300881124003040c40400c0070b000c03c1c007071010244e406021041059800c007000541001d4003042108100f401407508201045640c07103207204000c6911585a02da8038150018400c000141d11006000800528242019921445c103032100315419041c481002d0140a5400c0c0380644161103420400c030741d84c00300d0303090b1840c6d40d41c43c0c0c181105403041a5521400940c10310010400325100b944042c188a10514086e50b10007071010052240d484141c545148040c1d03a0306001519140c00345602580001e41c40d5039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601205386 1250 601204136 601204151
    0xd0201021915090b010614090609010804030c140c040b01020111030403202e0902030607180801020c1b0108010311150d0c36050d0602131202040609 65
    0x3521500004200440d9011941d03620302000100349500c0000c10480030300f00a111518101024098402c0c850310002c40c568800c3d503501014918111403901c80013a02c0c0354a0b002400c0700449031800000c0003541002041da140e0b60000d0a81107034411443e05003401080c80faa084810042120040e9903075a0640e81341c0300c210303088038203240705a940c442e4141c1080b035481c40052131900e010903000c8140303150340d0040d048410b8405624218545400d09010864142481c015910700100d801c0500083d605a00c800d0008e1103ca00c290000120034042d4102d81c20001d40c1e0b44909400c3ea007210380008810f4008a008141d001e00712906140100400d10306103199524503122007058078049e814650284444150f4001d1080589080380ca0701c3c100c0c03000c10020200c20b00e4005151200400600c190b03504148102c04008001c03808000c0307001600f95843c201d07585442e08106810b01000811640183c00707000e5219461706241900e0020301003c08100c038135044074810403046a84070381020560300d10304500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601206636 1250 601205386 601205389
    0x40e0a05011b021c02210409150b030609220309050f030703120e0a0b0301060f11010507021f2c01061a0403260307050409140115050d0603120314060d02 67
    0x2410007111100c1130020007412080384040341029084900c41c10424040048010740d401690001d0046545e041d02c00c014880301c0283c80030400c9618815600c0008050011864070303d01640072726040300c0302d150364194489056107035440783d0113180b00990105185600402c02401d000b0b0300201580811005886240d085613202058422440207100030000b0060700ea00068855201ca103018040b04062140c07250384d51480141429480116076000803d40404a80c1000341402203c0c000d030382a8000c2c0c0005d20480000454004007002618070f0301d920b45044c203014000101c281401d000c410000c07008050004d82e00300c0e00f55165036103e0314004400241001d030b4003504600341d03400d8a80c00300c201c101806105409004205070200745d00108000041402401c680000c0204112880a8000c1c00064180c000715008090244540d410a2121200700200c02e0711034801445c02200043c40024090303120380700c07030449180010703219010999070404841000307001d09829030322940c11110301d010ac2c2a15070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601207886 1250 601206636 601206643
    0xc0d0209041211060a0b01031d030d020d140106030e06130c0e0903070501061e0501020307020a09020702190306050f060d0213020a1202030a09020a1d04020d0809040e0a05011b02 78
    0x14000b81015900300041c4118502c102c0c0400a86180c5004454550402084110041c0180908203012918201380f0100441d9241e10014181031340001440c1003e4031140060040d5026024039000103681e04065010340c804541514041e0049030360000b0740c400c00301006490001c000d031825000841e006010000a90030040340419034a900b460f072006134842c0d5540e0ba185006681c4014155400c0c401d01140320000850038a000900c1515501c0e0400da403400107986a1003044030181d04140002001e004541e9160010010144080c0040c507040591600840e2075442c660012506582c44d18144030202220075002ea8005074122207100302d4030081d90000c0c210078120140b000300c00f0340100e101502540176030044500003080391000d41d980e2034009854002040168401c0f4494040600049901650b010300050409011510820f0715215a020040c561800c4c41045130105401c000d1003503591118050348219140752170040c01598103c1c0f60480c2034809052112514000100052a0166002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601209136 1250 601207886 601207891
    0xf090703030507020f09070807090f0608130f02060f1e0a0e0d03110a0c180b060d0b060f04090f050c03060d02040e0c030d110705030307030909150905090f0c0d0209 72
    0x1810095695181440452000e880306034145511221b040c0400280540002016100d82032954844940035181e141242c8201d801d07000725000600960005101315214000d0840c120b0300628042c0c020609030b070b0028405901c03901c038920700c07602c0c003040303003408640030700401c04400d4980381c01c15042207001d40d00207050b098000155482051600c180200b458090140e250400822030103075050b820040c14034041d4604144a400c4140c540341440c1d144802d1a84500f1860300c000a100525004012403040060108103c050307031302c41c2081040ca000b07408250010402810704d400301091404c0480c840804480e070003031440c40c508a00300200314240c3e454108001440794111000980d0f801c00420080c40c202c1803621981e098070941400e40501760700240e0102c5a0f50841d01107035402d82c0c4a00900d03480740a81c10f00140032500c11801440480c042d50800c6450000240c1304201c0903a959070400e082c0c40081c0c41d03500d100e4000b400140c54410b02407102c458030f040d003541d815520300081d0780881c4031100c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601210386 1250 601209136 601209143
    0x60318240e0d05040317030907030f051c03050114030120071e062703050a05032e14090c1209030c0d02070510080603150c0408030f0d050f090703 64
    0x29003044411240c154080212403400304116007418400e010098426805400300b61200750341c0c103460715004110700781224415080c11010307040b40340c40c540e41c0c2404544403480443d464054180c801c0b580c0360178181c0215111405550101d0203500d400005803055000080d458000c0e410900c10342a035400e20b15284e102505149070f040d6480c2c0c1c8900b040d01c0c20001110b062102c0c0000700c0b01590600c42e603504168091030081c40d03100c3c00b41c0d6511003030034480250244014007149081c0700c0c0c0c4030844c0c010340c041c5a11a003c2050083c140c0c2380d491685840030410381a075003c80040803400c0c81550804030b8500751101050341c07070b0102070801040c0003096003e201c50784e22409101c00000749002c80d081c000c1c0c0f1a510000030896109400300740003c2c1d115607032400b440b0b00640c0088120490503200b00e00c910702861024000d800d1407046100349124801c001001c07140c0070b000c02c001c005500c0350104010702000d440548802c0d1101107420016054a9004c2c0844201d070407000b040c800401008107440084961 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601211636 1250 601210386 601210433
    0x309080f0d0e210d080f0f04110a03020d050d020609011e0207050a0b07080402100c08090906010e06070807050d02010c0512060f0d0602211e0603190309060318 70
    0x200c1e000041c107403030b409903a89000c250b02c03020000c00000f000a8044030300c9100d9101c0301c2c040d0707845200e801540d20045030044100d0b0182004200481e103021203022507101f01801455042d6182c0c0c0114140221404045aa540c043c02c410b4030015070603c945074011581030002d024003400162007000403414008009092179000a2030700811204020456409500015183c03403480d0081c80500903100440782a40544a000e8060884074850103108040c0382d800202d0030700b0400c034002802540d00005100c141404200104014944d4803040038014451041c003c1076078441c243e1928030304100200104805583c1800c5000904503000b400352031128404c220040150f0759013000261a0364883c10040b03811000b0604e42c1d009010141d0020301501e40c01e0403407800c88070803020418075105412150764490345030300242410700d04450360001d81c01c50700007000c80b54261507000e41000000070410040f0080740010100300300880e058029814110410a02403840d00c48a40b64600e110491401501c554203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601212886 1250 601211636 601211657
    0x7060b06041230081b0901080c090415080309010e10080c07151b110714060706020909130512040803070b090a060905010204051e0604030f02030f010f05040309080f0d 73
    0x40d00800d2040d10004088102a0391820302d020780803213400c0c1d450400030020004880401c01c0c07890101c0f920040103a494400070b69134000500d84e1030304025121980181c650360300c0c039065400802c1079006050001e002e10b5550a291001501c10480910407500550700307010102c03545900854074a500101030380c4215030b100c0540c80c1400200c1ca8982c0a480740034075204c01100c0c0e404031002c40001904807915518000f034840a100390740c1d42e6403803080b9102c001c080000d02030742d0704003a009008145d00c030317010260400c2d01407030005942c508102d400803c42c0904a0150050150400c821918000e00082e460f162904003c005520f903c0381c0b20380034000034942d0b0003041003141c0c2045180041c680122040010385a14540070b8081d52240c41030902c280c4080100c4980c000501022107a003002c002d01141c030b4903140d5a1005003003c0d802c00113a905014041518445050030b009210344c000748184005a149410324010b40002807940040003164007014080c14070007400506109a046903043c1140d021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601214136 1250 601212886 601212923
    0x5011a0d15090218010b2124030c06160c0f03031403071b031e020d0c02040509010209060c0109021507080a0e0a08010207031106010632120c07060b060412 68
    0x13103d495907084802d80e00800000e52601c0d8440940f4161303a00416411003d092038004441000c0159000a0344040701c4224040b402079422000106080190039942c1181385400040c9564100d030764861200391110101c002009440d80383c000c0a041d80f01520000c1d1411520010b1001a07007131007040031041e0000200c0e4180d4020001c0c0008806d05405122404c1c0403490010041c2d5600c01c6605501d800c0845e20414460000c9800d40c05900704c1c1c0c0e40e0601c0780300240c003000f0181ca0060590403a03954201319002c401d0700c0381700041c08043c48800002c00c00a041e4070505c030540415159000e1b04080501c031840000705203104555114074549450081c0b03210300800203220b40b201e5440340c0420340c0f00250407002c04d42c10445c0001840c0550054038216a0b807140241e0301c404100b4510350080c3c02c00051640b180407001900350b008a220a511420610700c0282641000300c2038846a4034044040364a01c1000028082c0074000b081c207035605402c1902c0d010020081c0317801e9410003440f10b580d00c240c04024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601215386 1250 601214136 601214149
    0xc05120d06031401020a020706030e0d1808010504032105010513090203010608010227180118060b0a120b01113d0c12061404020714070305011a0d150902 67
    0x341d81c10040749543e030803110450328001d510010070f44d000f41c01003c500040c558000c3c400c0c8241e0071155405408103610b00e401c03c8850180c10160110390600294000c1070920003407007464415442500c602c001c14a4110130300d0480b40903041e1079620310b402c3c100188242d403030381041c1e541100420b800c007103800c0381103100017409011903422481c055032001c00c0031070058282c0e070030400720041c03039004c0d110030060524140a01a00100030004610800e800104020000c0c0c909040c2c0c01042e5000000c1d00c29110900425103034401d10b10070b07000a074000900014981b031442600c080c21001d007000f40d171500d00e030003500c1e4aa900c4000c400c181e2219036802d07035441148648002200616602824080c5000e00d80345c0da0041c80c3c40c0301144001541e841e078041d510078542c0b242d8010b40c1d400c060340c01030002082042001039071120364219581840c0c0d42d41d40b40d4601e8100840c0001d140300344000320b915040b0301e1441480b003400401c414400c245444c415000300f8410380032080104100c04001c1813050190000c0b411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601216636 1250 601215386 601215389
    0x6020a1e05010c080a0c030506090c070516090f111908060406210b0705031e0c0405030a0501052401080a020a03110301080715050702031b040e070b070c060c05120d06 73
    0x482d50a00c850001010b81c81050f5502c01e1800b1355003003101614000048003207070021070344150424007520100b0441c10340e01014000e401c0c0700e00110780000c94003c602c0d1104104582c031546070251034109112035030205000c0e509221010780c5015091100005d45181d0111408003180300340440c4002060541e25982c00c94409070680215000e503000042c3d403195203001d00e0b84020f030f8a052807000802c0c0341a208000b124055a0a030424412001e17080c00300009106025140d200c140c80200710019168030f082c0004640c50703020b04000552464070b01551010080c1200c1d1102d02030007003501c80d00c110307a00301a510b500448506401619280180419801410503c490402c04800480005602c01c400501d00040d00d4171890089040f1160036000d035840c0c020078000035890740104e00d00350661607071500c15083c40400200045000d022a40450b4282001900101002d80b4002510410301028850381c000616051900c200c08109507150181c98a02c00c130101c80c104000014400cac0c102c02d00c1d820140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601217886 1250 601216636 601216643
    0xc042307051b21030f15010c060f05060a080705010f21090c061202250510050709172404060b06030720070e06040b01021c0206010f0f06020a1e 63
    0x71440d084090099510040c48031504070140f0600c003d0070301d0104000c2528042d0321007480040b0341e80c03502c401810000c80708440d8113040082280ba642d008c108a4007501d80f00d010b2540002800c0d08116040c0101d0541e20340050b911079020400411103640e014510380481c15291400d00080700f0041d80e9424411003061001502500b84807000007840b125013064001c03140d05841c0d038161400d4070100f2400382c3c0103507130324a4441036030007050740d00b0740302551212803a0710b22620559503c40d06c12000c0d881216000d8902d6000258604024400c290092a50714050991304005000c41e40301e601204220300388902080c40d811610102060801249400811415400500c4a616071070b140b0001440010300501e022503808401d1030307a041c0040b004c203448080ea080310740ca8044980d505014031000d41002e41c0340b1411441411400908495802d00318400068280d000d05000d5141c0041103001110a030400c1c81c421900300c004001480d0009030405c482980a0580c0703015001c000c0707803449401d11820014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601219136 1250 601217886 601217917
    0x30306011121120f070c030e03030913020a0906020309030c010c08270a0902130e1819291b0714010b030f0c09010905090703020a14030c04230705 64
    0x11420400c0101c040c112140c0b03d0078a01040d0764940c40d881d00e2114080d40c0c10f0000c620210440c60100b40301d1503003913651040c0074080b03d251414a03400301d01c00588484140013000d5022401001c0c8a6101d80c1d0309000b03011601c0114100504180005c0d00d4074510020241131104800d4050200001441550480c0a140080b00f0046031146e07404241682203ea50030702c00c0846810106100d44548251f4101c1d044048000b60140d040c6030080c1c46100001e040004154100d07114994450002c2084852180700c0b5045060082545d24003021075090108404400c6040c944202c003c1c050f0000301654440020403012002c680c0710703200745141c1d1140c040041c01e2080c4000701100804015081403c04c02402c0c0c00301d4000f2041103400e252940302c442d030741076030160422004104004840d045584c2140d51038041e44c3c0429580da0001d0140d85a9600800b8016081d02e502c41503842d081c840c00607625400e03501800002005034410360341c10268072041d0b0808083c0804219464070a07000c0d18030728041d54541 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601220386 1250 601219136 601219183
    0x30f1b0a020c01080708011211010203042303190b070806010e12062a0a05070c090905160509060a0302040507031d070810110f07050c0405010f1401110303060111 71
    0x80d01c07640116802c1e404980c060022454091082c1c240504075020080340341104151541c400380102c20199031281107100c241b0001c82c161b590b14200301c880c0300d1041030044a91111000b81800c0c400c6924020310741601601c3c460000c40c00c02c48580e68021001d00d0020308599a402c0162008011011100d800102c03d1020745007a220000e03039640248410002c1c0c02036504020501c1504410b4165254840982400b526114034041da0180c00c80c1e03407298080c2d001c0030b5200c140707450880d140c803c4191000e501100e65040354004006281c0c0203010240e030102c62038500750b03003c214a4945880000d010310342d074030002130f8040d1180d4000d039003100d0707035510b603d1700d031520548060b80d280013500400705070380520070810918684a120f00e6000d441c110f45018102034180e0b9034020150050703d0144c03101d0150b0594250140e885e0311615003e4501c0c20b140360a030030b080203031101c204405c2e803601905001c40d100001c41f9a02c400001c1c0c030760011092070056004114081500c2c00c01800c07001ea000c503c0c003003101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601221636 1250 601220386 601220407
    0xc05070e0103062721020709051e070c050a021302070f140f15010b030c0c0d0914010512041b0504140a0b010f05040506031b1b0f070506030f1b 63
    0x11440c05903088884043c2070b505210300311040c85061322402071480803000300088850190852402c09000c850050354101541c6980000a40b02d040f05c3c10041581a5961183c40e44801070026070040310502d01882e4150007036440566403114500b000c0d21a01d12401220703c68611034046640003940325000301001d814902d80b011000100e003105440b10300500090000d190b50000f900011000e407401c5880342d503442e02011382e0303c81c0c1c800380071903c41400801c91040b0041081012281c0840d55566030813140345010321070700403400e070700d022203041202c00c0000405d418281034200340c00c99007010b41c028103d40d03004081802c850061b8012604541400d40c00306c1c214100c491078510903002c3c00d03014842d4624090045445500140b180d0010030810700051117039040010156500012000e44003042d9004540104042d4009000354140000c01285520b21100c0512550886100303900003080340c641410000b8840b03000c0101721041c0c81240d080000c81c6103001103041c0000f0004000d95a42c2c900c80d070076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601222886 1250 601221636 601221641
    0x2031012121d0d02060702060f041401081b0d0c03021306051c0203010e040f03050717070302010c0518040e03090901060c0606050a120b060409020a060306091803050a0c05070e010306 80
    0x1c040c0004038412070021229241840a074406180c1c0042042d4641c00440c0d08000d00e680081c01c1c2641c11540500070022024051002440500301081c150101c00b00f0300d000040460000503d0009801011410384c4608102e1005480400560b15070200e10000f4284040b80240186400c4004260302a01c000501c560002c0090520018014030784013040c6145041c04103030b110070311a484044242400150100390034038441c03000380340700e860054070b40b580c2e03519140c160181884000044501c0002c101041540901c2980d20070045810801d0401200120030090070358000d200c03a00440d11880e09124004061007207442d050b10041c4140d19070b5031200720040401000110885002d450810017281d0361800d40c201800700c82988004014010070b0703503202c0044281c0940380780d400030786a0780180e0041e65442608000f82c8100d6500054051a00c4081015101100c4407e04403140070a002d802080d4003804846094103d13040c898000e45461170154542045648110240661000080304021458 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601224136 1250 601222886 601222913
    0xd0605040218010f21020102060115090308030403092103080112080d0e0a02130207020307030f0614090c040612020a05120708010912081f0e070306032423010902031012 74
    0x1c42900000484980017018001c001c03d0041d0242c3e0000004002e4003500502d882e010000514041514a550740e4400600e600103560032004550103401c02d0007105100041051010600b521031740f100304064a0180104206000d070400300615011206c081c850b0341401c8403030a4041100400c6040301c225440c40c1c960920003012440b032140510885144c803101d0003910600c0d40c005000d05209071540e80c407000700c507600c0e910032035900c0c1d103d00039003044610f8640b5691003050090040e214000c031030001c00040f6425a040181c154a045a0b40c04c0540c844e90070400580e441601d800030f4600000744030314900500381d4080c4d1074a609117109003040240340010240d0914003501e403042e040d2507650081200003086801410b280c08140c3c000c010010783c2019071900f100032402d00141e0540c803900e42d500641c1c8500454105014925032410b80c0304110302c00c0c56070b5603030075094a00e40b100c1d4000241500c010184a1096280d40100224025005950441005103640c0c80e0020010f001440d148140700c816 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601225386 1250 601224136 601224149
    0x9030a0f0b0906061906080709051c1704030302030d0f0e070f050102011104080d120b03030f0702032b0e1c1401061a0d02070816080d18020d0605040218010f 69
    0x254408038190317040111141844807444c024010826082c10021265564000c0008013041034901001400c0e481e907260302c0200001c50415030304540710a051045d080d42c940c211051034000e04001c1040820317408015a601007503545004140f00c070300d828203a4041d10a20090082c54050200000381c0303402142c1849080ba6000e8000744540621003207400000d00403849001e4068014113402440280300340d070007008422039503100041c208030310004a4a5034106a280802c01c0d10001507220640ca010410074a0407000c100c050f441103035280d1040380c400c1c003040c0c2c40320f42401015031401015550b40a801443d007440040803e500001c0750901002104a5903035544455180c2032010805950100c07001a54002c40c0c06042d180800c03494000000b0350004500340c0b0700070828072040217072065020030803070380d603000308640c41d01d8169441526040b2000c003050a0740c9218408624801a10b6400f403c2107210303041400003600e9035480c004503240c041481081c00710300b40304800119101ca002c0086400341c03500d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601226636 1250 601225386 601225393
    0xc030a0f02060106080f090a081c060b030105210c06160b070305010e010501110705061306020f0d1706031903020304080f03041d070c060c032003061509030a0f0b09 72
    0x503004059072a64402c0c025600051300f00030008004100c61071880350000403107001c41c1c03006280d80d201d200032034001d51005c02c00c10044500030701200c85203000302c8028201141803d407940d490080040c0d03017219280300d1700c41c40305034010f60140c5107941408030444060004d0b00959031182000b5104c0c0c0040c031820002c03a0300e61943c0e008500b40714030921800781640d610f15010000c60f402d041c0190713100240c00542d1ba02c80d104e850030100c1c00341c4418014221000100029410540c140100a0b00f080c002c800c10042580c003a0312000c1c401944000342101418010003425096114000800d050614048491141d0941901c8103010158004014812601301c80d040e0b80d40100f584c1030f02e82d04c0c3c2c4a03a100e0791800c6596000d41c504102031507000c0c180c1100140c00c0007400e81d4034a039281c80c142e074105d040f4280440c0d0784c0d0458280b000c1c428030440040203d042280e81c65440c3c41d10020b030010311054020f5209200c049001c5290b901d0030025160322a070041486440d02405250200498100f152943d03424003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601227886 1250 601226636 601226657
    0x201020304230a2d0c17121c06080a0b010e090c090c093c010c02130504030e18061008061810051003050907050f01171005060c030a 58
    0x2128108070000b0b0100c5005401c1c0101d00b41c688070001c00e920082c1c0c601112440b0205041198100c041d07407031107446418508405031910203074189114040083c085140c000485050070700c040001103a4000300c0140743d08903180300c464103003c02449644c1000c5258070480c950b0b90103010200305038504030340c80c1480740e03605541e0b11200da03900e0700c0b003454030240c2220034500801c0030003581c1c0c0050b25400c100a051101c07854990b00030142c0011110140c14030a03c840b401502580c522104507134641e000a081c0318003180519804030360000950705080440c00c1e0380d403011600309031061a80030940e4900404506003003c0d00452850317010400d8038814454246c042142e0502030241d100c06100c1d503001807900b000d20303815603c810381c031000003001c03684240040c00303000c15035a962400c4200b07080f0f0665000200341c50950f800c80c0c6420401d40040c1c0c450303103801444846583e8080c8400c4040a0b445a075000d0584601629441010441d04000e92104000c200000d40c2c480004c0606510034041c3d4604200f81e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601229136 1250 601227886 601227923
    0x1a03280f0e0c0d060b061603110d0f09030f0c0806100603050f060604031209081209120c09160216030602030f0c1315211a01030618110c06070201020304 67
    0x5142080000e600010000c01020220b245544171422411010f0066840c005144810010b01d400c00c5500300e011513005141d50481d103c00704010101e05455082840100340040c40207007400c82144401416401e0403819003080000640040c0c3c01440100d0403107061342046270540ca00e039070340790103804000b0707103000000b481c0b2007160030400f4001e000c060000c0c1d20f8107045482e25201035945100c00e83c207000386a400020200030412103001c58208101046840c0e900e04001c11104c1610344d10b46410307507440b050018009030b80700300ba659040303803003070f0191402031440500982c2002200c01824a54540b0b21200101b4040b00360025485100140880d022543c0d4003a00c0e0300711405074400c04030b03009070200c0c024070148401180d1981d030103810303041c058601c1804040c80e041448103040440da4058444200d078205440d60f80041c00302c040c09081c240b0855007000281d40e01e4907160304c2c00111540d20341000d03480c40c8800c80c0c100d8419040b440c1c00d03a001c3d45000080603010754000c1c0e03012258490044c0340034124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601230386 1250 601229136 601229143
    0xd031d1b221418161e030506010e060a0e151e0616030e010c1104050c0405040f06030201030c0c0506040f08070b091510030f12030b0409030801090c02071a03280f0e 72
    0x11300c556080c500c4454148501c2c45520300303e0f0500c058072105040804404207908122150003031050403581d01003807400c40b06003e50809a0351081d4414040f60091261070703030303907040c00c4176883c0402e45202c001006100d040d003060781c060072820740e00a000000c04058608403044503020841c002d8031403505000c40240116100520010041c3c11072202403040082803803c0c0d001704d034000e10501d2200d03003001c0d190300c0003030221001d081140980c940d90702010021960103005030160300d0541d007407130350040d00143c40f05038843d01c0080c0000c00d58158848810200400340b07040c0e51344c840d00154a20700c1464044855951402100c980b41c3c148034034000051004031032114201c0681c0e40c0b0503030f41340290403140d5800181c1038003240100d00703140d25043c2450b00e9460314803400d9680e41c0130b60f40e0000039503d4009008100c400300100308086412171841403005240c00344c1380e80c4280c3d40d1044d00a0f941c1d52505034440003181c1c200e403c103070107801d24100c2c0048120284c002400802c440d0700c080040c13140040401d0f56 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601231636 1250 601230386 601230403
    0x60303030f0e0d09090203040c091d060c0a0c0b0606040e0c0c010e030a0f050a23070b0105150301050112090b01031406060a0315020c0a050d031d1b221418 68
    0x14583c044c1400821950380165402502c100a030722040c58550320110141c03017104124441e440c0803142d00403130889003008220341000008141600d0300b40d4a42d0001c0c80440c04200240c8507805181c0404e103d5110002110300600c182c1c062031805003041d201194165110154681ca1582031400003282510040300302c4401501648881d44154080d490644260700401d0002042c0408070700c0f1020305030081d03d840360055044120791503542e08a85040c007002007041c3c01c100c0c01800e0300c0c0b8420750200d000100300ca054507401d0030f05480c8905040501405080594070082145400e10000420040c61418000700c1c290b401d400d441e40380e40c07110180010b104103840081c103001820075440801000650042030209482c1d8141d80403111151141c0d0320b440c0c40078100ca40001d0b5a40350400e484a1100942c985000340b80c400703030500d001d40941403141c6030407140d1501e200d0100c0812001c02c04482c00c581444804009505110410707003244e8100c04a44d00310f0f01e000b040c0b454040403e0240303001045054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601232886 1250 601231636 601231663
    0x22150c0801080d030501120b181608070b0c03070b0408071406040b0916090b0f0a0b12070207060f08060f03010912030c020c01090308070203030c0f010e0c100e010c05030409060303030f0e 82
    0x900303107d040d80f24082c1a4a0240051200055100c6030034200c1100780104a0443d40741032014072002d00d8648414900300090b4004161f00310140500c040d000404021a40d1883c0c00c2034502145403228145826035101c2c80000922813506004034403400e400100721540300314014030310308419a442d1694180c0341c9400012403480440083c6003441000c0040d40030842d0020060101a641e03410f203004101c802290ba0081c41c540140400e07126111104221041d5101c06a440640360303843c98480d0103000c4019000c1d6150600c848d950000c0d4940d01c510b01c1e00c10003848001c000340b10034030305420281d40032600c08544200090501190015141c00010280310381801070751402d400910b952645071f055006500101d81c1400304100007100e614040005500c0d09441c0000060ba030514002d0841c501880d03008014010785040022004d4150400b207203c6034042c080c01c1a1040c58050300c2e001d403c510070380c0c20403880645401d01c08814185d2541c0f040c0d141100c0302500f00881000303008490350f1080034540d0309 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601234136 1250 601232886 601232909
    0x30f0320030f101d0f1803270d030c060f0e030406080c0702040222091b11070315090209060405042f03011d0d0822150c0801080d030501 60
    0x740c0c01007510b078049074070626210000d0b07140c54642185945032040d900644a00c0c001d04018015807510100b8010b8124421613000300c06415491030075516406849071710035451075511007072001c0d64003110140d014000c0003440400a600c0c58900a0918200c001c0c0544229182c080b60704052600ca200e9410f4180c03209c4011414a86010811645d000000f890150411780c140029030068031540003034040b071050040740c00910404100e88116840c415404a00100c3c14101c1c20008440c80c501c0f0360711824800e02c3c00c000b86440900c2d02d10310303100d074650006068842c070b50382d00303c55920940d00621040d442100c00c0340c00340c2c440324200030681b003061f00c0242c000410a5042c1141e00d20000e400d030b07010101191007664034486040001d084800e4050100c10100507404484901482400b110301603802034286200780e03084c548a1086035100301e080e01e84016425168403000d103d6080d40560080b80b40c0c21052010000114008040d4003083c03052a076a48240303000002141c0c000e00409051b218000307040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601235386 1250 601234136 601234141
    0x120504020616050a140f1015060809030c0f03030a0c0216050d0f08070b0106140a08011703120108010b18010b0a120207120206040b100b070602070611030103030f032003 74
    0xc046031400901c8200d8103841144c1d00c840008480042c1080c8903074100e001780c03a0181c141c40025090004160092001614144114160f110031034041c0007500e0403441c1156855840071b01c214918806d031801c80c096031240111380140c4860000c01184140b5000c40180510010a030082e0707501c2074080d40d182e960b140420018001801c00c0d0500c01c0160b4050031401d54910000d48810242d644614404c0c1c50341c0e55482d00601150b6088117445111200c241402c900c3c05501c20402000c05206028050402503481c036401ca01d54000c00c00e9414022549051003082d503560120680240000001030740074082d40d406a0b2203800c2c3c41c007446030480b0a81c8500601d49060f400f005c40b800d407c0200e21050055003840008003080d14190079811304580754000700703040c1c10103003062818203c0040142016500f142c206000000502c000e6451465202c1c202580390b003002d10b045e03030141c001c1c440041c1c801c400100002044c581d001250b10000015030b01d0410408124010391014032082c840c524070003000c00c001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601236636 1250 601235386 601235407
    0x60615050d0b061b030918040203031801050d15050909011e0510181d010516030216021018151e0201060b130311060304050c063001061205040206 64
    0x42c040008008002e0b41c506144d001080300d0000c05080000815030010512503143e0400900703468409940c900414542d1400350300090f564400c240ea00040d8090150303201c182c0385d0042d01903803500d045103102800040404030075480080e00c0c0b4850940300341d0b10b000110782803039018410141c419015600c501c41d0288400010005400c01038030003541c0110400d4000354860f0b19582c0d030729001100180106010700707a030020125401400300003030b0841e4505424004c4030841c1c4030400b081c0300014240035840c1c0011301c0205503c242100006500200d0254000c000540e00010308609404545030140d1070741d441d203054444a00b100190341d00414000c443c44014074002072001040f0350a244004103807540c40b0000e480c0260001044650b040000200510820544000e624103024080e6180c0e4218030746a2205569480d14244d010300a080009510056000c0381d4003102000310901026052450580c000d00c541410034450703000041c00100b0350214002c52805018000d40c0c0050815003000078104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601237886 1250 601236636 601236641
    0x160c05040e0616020a0f0b0a0f110a0e0103060302030f030c0f0a022b140606040e1c08040804151d030a050d050a030b0301060311120d0503150103060302120a060615050d 74
    0x15003c50075031080c07104200c0061610590018150f2289200da0350604041a24006945140310074409940c02c1004246d4038241c44819501d0807059854480030345014100180d000384080d80004e9050b0061050082c1038a40000080402ea45000300310382404081d1007906071101c01c0e4400096001a034007034000b84032803422003031050801013116904292402c695a20410305040c0c100440c07550807510403c0020b25042c40b604458042c01e6010b00300c0303206044c010f103204008828480e82401601e00104062000030410f803800f801c800b403d60350440101d00c4001d4100a285078102042d0520340c81440202e04010402c081026444001030888000c10107081d11190826a03400d01016a66281000a941d007405554001c0d4050744406521552601c148505000c481650200c2a40f02e000c182c12695400000c60b5804000901381366030008541c00102c01400e001c2d4006036102031501840ea6800c50003090410300107100d03070010800507507607408200c2c01040c0b1140701401306005000d402080d020a4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601239136 1250 601237886 601237921
    0x60f040e030c0c19060309111305090609030f0d0f0204030f0303060f0512030a0c2a03140c030d1b0209040b0f090c060d0f060f0e0702061b1c060b160c05040e06 70
    0x460088d40200f8040780429920301d0b244081000b080d84800601410450500070305821030a0b81c80914540802040da84025204001306498100c1d43c807844020488502c0e4140c8010399806098540112030604004018000c00d00824423403041c002d000003030342d01d03015040702039003401c1202a40c28505001c81c1aa07100000c108c0540704542c50481440c451a1a84008038040e10940b10040540e400c50804010b5542c00e20b85903c500d074020030060300340fa5000601600f00170800c1c54400310007034070712290110319480950001e40000034101404200105520040c3c1f062024503140d0081d0750780d80c403d081d540c83c1b4111595400c10005c2240041314503080e00301d209034010507540458075035620240c0c20040c040301c0c0d020400603070501c4140020700d503040c042d45402001c49000b0340c02c100f0350580083c01500c80d4550000106001078444440721510f50000802410402d5141d6158040181d0b0b400c3d402000510842d44002e8440c000308482c64588284000c80340c0030030040c50700755110007404906c0c2c08075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601240386 1250 601239136 601239143
    0x9011d04110f0c060f0609060913051912090e0a0207020a0b030c13301a01031103010b0328080d0207031806110a030305060f040e030c0c19060309 64
    0xda0003030850310300e00c80700200052141d55155039900c980384110a41480c001038110344d4090084424010039981d40340056802600440b601059078407a80c0c05502c8080406400500600030340c14401380c88954103010b065890302030f14001190313103907081c1c3c102c80c10b41083c0030740d80e071610858000c01d04288003903015100f80381c80230f010120926140c10801d481e44d0011150001114000200222000340002801c0014026401500ca401050003012036442041c00b01c00801c0001459500080c89500708a0403c4a206002254180e50b106d051900d101040a0346485c003c0d030800344490080c0c00c0020b4034184150040b410b046248010a00c0c03e1381c6035404410603030b4031410a2081803040c109038401446084e10a80b613440e0035047c45c9a9100c802e07130242c0c0c0f15600b8404844804c02d00354001003000c85030f11b5030601d4009103981e21a00065440c8001800403900146000074581d484600000248282c0c3d1401c004c46407055044800c01040040744c4e01d02060070a0080d00800c0300c0f42c000d4200d031560038803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601241636 1250 601240386 601240391
    0xc0304030506040c03020a27180605041a1501081303020705100309050c0604060e0d031812060609021c0507171914070c032007150305070509011d04 65
    0x2a40c0d01d62a00d442e0060310252499140d104c800c004503c0d003034409000400f1010001e0000405181601d0f0070365011820720a0a43d417108103814000e1000da00000403903510800410560405007064460349041014a507003905001020070303440c007031070f031154800c4c480e0503903c10800750384210240c003c44410030800c60070b6205545000c50300d65104c031501210810207540001ea41e17143c500b000d51510100030585070041070308001c244046079002001c003143d204103488103c8400b00700e25080b2907000307844040f9001005024804611a0396221011000d60700942d018003810352103c4595049205500e600c0d41d80d03041440480702402000d40196501c00254204500c10620615200341d4a1201700c810a105602d00090030f20a00c0c814415041d0090704810b03d09100c2c81c00c00c8000c1c01c1c0c001d20240140c184140403810b0640598040e8603519603407030000980e0001641c0c1c0341300306020200202c000000c070741000d000506107880761042c0c0b045250141e4924652126800720f0025041c40160690713041078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601242886 1250 601241636 601241639
    0x315120f01140907140901030620190306090506090424091515030312020708070f080a0f0e0303070602090d0204290a1a0c1006120c0e09120c0304 64
    0x26428414070b2841d0300030b034194010380d1030215055820704195070040b100c0708124171000701468032503006442c192075001d0f00001d241d07140840ca84800c80d140a02c1c1c00340302440000c0103541c8030f0b10440401001e0400e80c80a10640307440d24154821303650100c40c0319401000f0480054007284003005012040b2a00c001300c0207658480041c1074040c1d81024600355904003240301c00f004028520720030400300d1300044141c40601415583d000340882080c8041407042c40d00800d0304014061194116501030b50701c101001e0446d0418641440d654002480740408a50755540b54218039005044d400f04900c8002c006c4c5260040d1aa00d47c40203410101c8440c0d0021140e00075040161030f984514441c091003d800600200d4a00140848041440301914025030948000b042080401141501d200344c11160064403450708903801c914104200380180030310350400b600080d01590007010103030340d50300840900d5042c0351205501d800d408800e8410901c146d01040215121341c1003c40030b0540000544140c9142c103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601244136 1250 601242886 601242913
    0x103090305040f14010f030b0307032013060f050d050a0f140307030908011a06090603070302090a120b0a111803070b12010e09010c09180216060c0311031512 69
    0x25603142c018213201e942d44111400c40350b070003518002100c0610f10b070078040b2100050102e529891544401009140b40c0000d4a841ca404210100407500024180b21200384888410001134011442107501d5106c401c1d1010a803400c2138200f10103119001001000800310316a02c11000101c504c000395081c0803400d6060321b41010520040c24010f0080daa100342c014100390b205400c4416010280e0741c00c94038428a05015110b0a050b17440d030035421645180c90f030383d4041c02940a0b116524082d41e000918800c042904000b00108191a80c001c5840a0165450f07880b10790880c4d4420385c0800b10311000784600440d03030f0f9090451a10525000d819140c4c140d42c0c4190000d20358112681c0c407008000c032200103011842100b0035071036000c41d4510082c0180c1c500b8807230241c52461a400390706400b50088900301c0340c4900d40c0c0c04a07021921498a184401c0070709040540c000c1c42c00f0f0a10300000f07814454440c104c01358003803e4034080c649908040c0054101e030810400030390400c6080c1c0046000300081507069 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601245386 1250 601244136 601244159
    0x306090f020a0f27060e100e03101509090302030d0506190b0a03090203030309031b06070807110712083006040b1503010e16050f0f0a020c150d0f0e0c010309030504 72
    0xe003d00d84481c031110302c44200b0409902417014440d010002c05070623401300360740c0014800c103202901d01800240050604002104451103400031007601381008101030405900100500441c0a02d02040004ea01d6117010080684092054410b400400b940207004500501c0010804e18005050002d43c002c83c1d54007180c250307001214810510b402c0885c800c0c6502d1101500c10303203144a844054002807030409006024950040c000d8020001d008241c3c2d04403c2040000502500400c00150720706031551400b60b01c264000f8040201c010045403020b0350720b1850100300c401500c003449038000b081c1d840105001c0204400400c07a648200c520707000341c030300c549090000d40c0600041030404e8a036142846403440305070294501c2400b002400c212500f2843c0038001a2109100c0141c0440d9a4200c2d00e04200c1c606800c0000242d44280c1140204038a844800c009005400ca40c0c0320a01521a100c0d064a04691030344044503d90742043d03140611940c4240d211400440c40303810f00c01d05158441140201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601246636 1250 601245386 601245389
    0x4020c010501090e010f0b0d140f0f013626040902040e061f03110c030c01050108011d03030c0304030912030207084c0c0306090f020a0f27 61
    0x3801a41c5404442d0600004e0140070201000200244007c0c008800401d95180403da4044e160b50605103100b8010ba009111800c844640d0300c0880b44d200781285100f0b4024119030000c284e00802a0807041c00c016544c00310400000300b0500c0014081109032035202207116615400d00c0080524a40401020540310281c00039000d1741200680b9030b8180001a4540c12029180910038464403900d85036042000b108070300814a5454049803101c1020b800404078052015101c00b140404940c05075200320552002e412500741c40003c0c00704507204969101c0a001ca50b00036441034100300005074089031261b00654010707100749840c2101541d01c1d4070f45204081c200c00f0450040c5c020310010000c4800c1000032020316075001d40c40040c0d020340e801d0b07035003a00d210980c2d19200000c01908000000b03c00d01c070818148100c080320038000c00c8a0004000d0091500c2c0c020621058540481201056028400c1d02d4510042d0380711320105082010b4169000b08901122001004c1c600601070044c0c525510b501d030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601247886 1250 601246636 601246649
    0x220318081b060726040902160c0b03090d05090a050303040617070509062d130602060c0f04050121061413053c07023406050904020c010501 61
    0x5407000000c0c0c0d200014411442030b88030303120a0058070081501110f40e880c0100c01c1480010420315101000e13011400707a03900036005184081041110311246c0781e180e10209205c1c0d01e500c05a5503d400040d1100d001c156500071007036102042c0c2000c0c0501410090000c50310003044c843c0b4160396400003a2030340d03209401a1001804100c51110707001c040702d280036007207030f0325050090800c42d100700814458090390307150481e01c03120304505d00c2c04510700850050001da400c81a80741c3c0e460301420100a000714901c0b034034005200346800070b0811002c00040d661850340ca01103141c40d003454400119200010400c00d891141d0300304d2802000700c3d425103d03107801040410211001c15a0740020400f0413003031510511403079070031709040104070342100c50520841004512408801038941c0c182c52410001d4a58a11010360504148200e490b000110007000c0b106400e00380007401125410818651030034a0300900f1810000000e0243c140204040d000c0c1481c00f920040c00c00c3c01c241c2a00e0300f90f8000b07a2140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601249136 1250 601247886 601247893
    0xc0f190801060e0907050d2904060c020f15070e1c050730060507050403060e100c0903030206040807060f1a01020c0a03020a05040b15030703050603010b040522031808 73
    0x400440415183c0340e0341c0720200300054000c80d4034145c04a40404c10500d070003400d0030031100d007940300340300019088601ca10075000c002949251034904640149114000ca801611402c0b840e02c1071402d0000e04401ca401640d21103104e00e444514058454403482d080041c2d0240909071020b101100345c4c011008014012401070030b074140b5100c944000d0104400780c0785640b5040c00c40c448031400000c8000141c103680014000340580e24104122142d01503a00f000f8400341c180b0380d0800e10400002410070355030581c504101701f451108031040c2d80c03081d145c2c48000c001d03800090020740801d0441c07003c1c0401d140034840210320306964010440444608070188903116042c1e003103075801c4c2c3d64104a58a5514400d603403250110313095800042505035a0b04c40d161184c0c0c0c8641c0c10171a60b8850089003038207448114078184d240d0920007030180c0949000c0b40e4150080d80b81c0902c1080c1c0d07180ca4016180a0707035200416501c03c2442e070031003074910041d03828180d044c00a4141c0e02c2c40c44070642d04c411070003810404050b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601250386 1250 601249136 601249139
    0x912020411120708010b030903071515060305090106090612030e040b04020c06100f060e12101b1b030e0f010c050d050d060e010807050111070509150907020703050c0f19080106 77
    0x94001380040e041502c0440c1c0c140104000d0400001c100c0c1c21642c1c20404880030700900c0c0c084000900061208140690510308000548079096045240034545005c024801162103002c008115229485240b021940008104002c24021715208541800281c0702003860a90302001c2001d80c1d00c42000102c2941c8420b040020185061500c0008ac00a400b40301e103090b40b815400400a0320704018082c40396210300b2540303070000800c2000851800c0c07141e50500034461001440c091030030860044501207074800080398101c0803400c840c0858103031b00d07032580600901c01c441404030f02242000c00a041c0300d4000300ca18041602002040b81e4014a83e0303902e6510f10040d201d10040e11595800a90442203100c01407040c0c0d18040b41901c1510f00a00c0c0000a01c40e084111501e0100c0c540d21582e000030150040c01640c9900c0b0010b0320f40c041082d52103c85d15120030400300d036541c0303840c400504681c00280c034880d024501021007001040000f0302c0e070301d509828001800e00b05801b035440000142e41d186c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601251636 1250 601250386 601250401
    0x11e140f040311041a19030b16140a020a06051909061a180c0f040e090607031103070e0f0d080f07020117010e0402040f060b070615090c091202041112 66
    0x603d582d9000b410340d8180800003910305d03019045071099040f18801c40a1540741502048a01c0c61000215000b03040415141445880303a07813560014140000094100104078210303462140441e14100d03d07d5000302030385076094680c400104005820929486811031842d100e24040d03024071015a400b51000040402c0d00058076900a60142e10907401004a0316003003400c2d4444070149580500c200e201c6503a1078850240d46d40851045404c04030000300e1030000d104000c240016460b11a5107030f91020001c0803d4003020480f14002106d18800003040c40241002c07506000003407032503452010b0501c0e03ea941c015501c0e844541c0000101685660000c01e850095603804a41c1d81100d90b000d07882202c031541850b2026503000402080680200e0b114a59030740130680c641d00c181c0040c4400c4800c5604c0d15030f585480b102400f03c521030065030a03206400415504494072944c0111016905c840b502146468103154a0858800d4103036802661030705d1019440c01607000802140c0b2004800c041d55250025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601252886 1250 601251636 601251653
    0x30906030c1403061c0218060907111b0604080307050a0c090917090604050a14090109021305041505040203040b01180204030b070507050a0206160b0a0b011e140f0403 73
    0x5034184100603042e020310020500312002c0383d07000311068442c041d00f403a900e180201c142e0030340d01000b0f420802d04250005c0802c41e030404640103043c1124022040d4545003811101c80300b50802528298110313103a01240c3d44484400b21000030380140000d4103103a50365102c2c42c00c50700f00400c01d41d41c68121003d40c10030412032680c0319010700414102007006040380d44a0035070710f41404e1144a0b600400081d04c00003507807190162802460000c0201c00000e8036046039805007282a182c1601600c807420000c01c0280450080d0345000900022940c0064901300400c000380015070250700941c02c2d460408615a21103000440c8501d004d00b9100f08654940b08180d10059002d055810030b01e4410710003840000d10380341e0040d401445600d080d81c0c4900090500600307103c00c210000b540202c00044480600d010041030714942c0780541e031140305540d2412050000c0c3da000301c1c50580011161101c40348520b074204541e50f580c02244c500714450a10b00d0486064651102e80342029000c00480c003042000b05e1309 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601254136 1250 601252886 601252901
    0x1106060307080706270909050c030c220204090203070302090109060c0c0b030a1b081005011803030f020f010504150f0c120b010c051509010b010f3903090603 69
    0x190000d019082c50909075540701c08090259104114100d040b555440540058019107240c5010340b81e2100e641e1403450f036004000a4034225818003a0384c02c1844a0301d404140c250b419100549041d0b1000c5d07000303450500d0650707881e4408170342507800e01020520052a1014510641d542d0300c005a40e4184240003600c4e0301e0a591211041220b8960040c00048610700c0f0f000440711115100350302c946500e90544042c080d8603200d440660442104c400540c0e600881950080d101568801d804d2600c9600440b088045a12003400e910000b940800c002845180c1001408140748162150071146400c0300e07081d91000c0e2800d0311a040501450b00c00c103007891050303017003043ca40c0200300210620f8000151217185458004540a0350752600c44016074090f1015040495005064885c8d02c21a41900900f5103810340b000c0c9215071a104a00901d540130300382c0b1140b40300c1e0903141c0c0038072420112411318001d110070095100c401d240386520130b000d140c141c1c41d40084a11985944911500b0407070010102c640c407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601255386 1250 601254136 601254139
    0x8060405150c0d0207030e040f0b120304030308060d06060305070b030a050c0301061e053609040807081303020a0627051008060409170403120c0b071107030b07110606 73
    0x16010b12420b10301d00e100300d80e1592920200540c0310003182c10161b0312481104529a00700d030404044000125040d80459203424049401554503074590400c02e50f6400b0310700004000c1442c09000c1081c030319084104045440c49481c0219003181c80396540c81c10a142c83c0c1c4040714a04011051001c0c4040134000c10354018420b100c628219807501e07600030040b240c1400c0e140704168490300341071240c61140080350f2032030480144c0f0005d407203c1440411007510143c140034080079403545500c0c1562600c070340058011030300042c00d04d061460544810b580c582c0080031540b05140c0f90300c3c0c0000141c8450740198014000e40d2254403412580d90041e12540400900c00740c078800c80c3d4032040c800c940d980500114000c0b410b1509412566441c0c1c00f00f170050031a404094500d00380e0703500c031510080860006105880c41843c0d60545075890003020b484402e044071004000744440ea0000d801d652046c003011008140704801c80d0b4040f6500e80316000d6040b001d5a07620006541003940140f611020008103811110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601256636 1250 601255386 601255423
    0x30b070318020609190b0c120906072d03050d0c0e030706030f0f02070c051e360a0501260303150a0b040b0306090a02120402090a0e060108060405 64
    0x741451180407034003400300092042c5400303d00070344103864540d44090900600c01414000c0303a01c910b01403d6581050603145000e03c41c104480d0a160240425110b43c0d0401404660174064075668142461f801500440102d22a03100103c9001e42580500c0000c280203454070f41d034440e40b014108065441e40c505000510000508c0f0040c0d03078400182d0314080703070b62034500094644070540223200a8640c0201c403030ba100d40007041c0a000c0c00000c0c10440221541140c5c0d400e20031200c1020140b0402e6a12545a48179007505c501d50b140c003680ca01c0101041d0264128508500c0c0c2e440d800141040c410780381422800e948400600042c29100003c51084000d00440c0c10b0b811503401140355240b03c014580f0442e00030a0f0421119911641e25110281c01018403c0d5242c503299081e420755a00100c0f912482405c4446c003103803044504d0b1007143e02c0c0c50b103c0d1240482694807a024461085000360038401c04c0350f038443c0d101c1400038040c4481070203000c800b4040c112a04250412900c0c0400546020042c1c0c0d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601257886 1250 601256636 601256651
    0x106030b0f150a0201060f1d071b0809120303041407093602060d0c0305070807020d230714010b030c01020d0f021f0f060812181c03020601030b0703 65
    0x981c2d10385500711448039501c82d5591070141c208100e014009030750229900700955003010030340ba1445840f04284640c1a00054080d0b038515800715010790a07140c2d2100c2400300300c1d09681c0400d09040c02403a00701c0015180c070140c05800b800541c61503000305d400ba140306a0302c240b04412180103110010041400c0c1405200e03200015480120b0b202201c132000080001d1182000c8071407068000c03105080d9002000c0644076100079031940080d1140060490000c3c0c50007000a00e0b65000d03041950142903e0b80c014242d045441f41d098851500000c1503584e07581d160584200545907000040c050680724010304920381d0404138400b030079500035000d00c038443d412803145e40b902c030b984c0005c03140c80580e550300d0a00d14609110605a040405990848206c91440202d0300050806600b24007900d10b0004400c00400f69514000c1351100154825071108081c1000741080034116a6984400240000d000f41c0d0b40c02d50124030510038901da401e049000d03820110041051043c18840c403a8040c40a050038050324 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601258992 1106 601257886 601257889
    0x15090b090c03070b0904153605010518250c030e032d19050a0c060504031707060902102f03031302010c12080106030b0f 53
    0x1d100d114808211070500042110491384c51a43c840c3c01d000e032800411000c4c1641074588440c80300c91000100e01058403190000035000403a00e0b071b42000e0440001540c6040141c0c0c1c3c60040203103130400420080d01d81e10350440f010107030140c0200607561401400d82c1110703151b000400c1070400700045819880d4200d5a50003045001c2e407a02201c01001d40c04041e030311040e40c5c8140d82d1a18103080d1090ba00282502e4441101480c0c40503201040c080050400c135030606450706540c15444000c0c804103006055030300340058409860424609821500c401c450700f00001a40618441c000035900144400c0d548030031805580103204e5840f02417014001800d0004003021810308203414018047e110b00041081c100c404070400c0550304540d604003100340310403441c4905a040c0404200c101c4001446401c1c400540605030300e072980c555041c040020308680f60100b40c140214030890465519 = true := by decide +kernel

theorem cover : BRFrame.Cov 601079136 601258992 := by
  have h0 := BRFrame.cov_init 601079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601079136 ≤ n) (h2 : n < 601258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
