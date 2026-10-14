-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1740
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:30:15.924978+00:00
-- url     : https://prove2.me/submissions/ab041da1-3ace-4074-953b-1ef81b4d39c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312769784 ≤ n < 312949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312771034 1250 312769784 312769789
    0x30f0b0610050c030403030c030e040203090607200303012c01080102041d0402030606090a020c0a0b06030106060314180a020406030b0a0b060f09011209050d050a03050105031c0305060a030204050c04030c05 90
    0x950b80700f030b11058011402c040c15030f902501d9192000700240d0a1205412803140c0d241d5884c00190700c030300700480c00b5000501301503101401400c0c440500740c1c2e01144160040d41c1c3c106000003a203045a100140181202c007021448203545401910100003c484200002c2450141500240106c44980c0759403450f00c44102030300f00103007509450095054001202260396842c054502039006440301c0300052070017808400d218504081218125072103009001003007031034070f42071050a004001300d00f020301190200781c15808002078010801604840c0c80d40d90600c03210010031800015645c003a00400c081e0351a401c202e00c400300226078684074241882002101030070510700b5a04454070700c054450400d0049001074491644184850000a46d10350b050800b06004102d00c012020198407050755405904000070291001600428000e82c446120100040d520041c07990b40a1660310340001c0c56101d082c0005e80c07042d80780c0c0c0081d60090500040c03140751703000b801c01441142e00c10013400492542d40c0e820b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312772284 1250 312771034 312771037
    0x6040903080115111c0e0607120f0203190509030c04060614090d0b04060212010603060608010b03250203210f130510021c05130f11010207030f0b061005 67
    0x80040c0000d0442004102d584490020103c00c95918200000340300750344401c140c6002c0a00c4550781d04030102c40006005039401894403802c3c0c6900382e030300624002c21903d4501189a0102051080000d240101035042c1d1003801614030715800c80000b40c0c01030b181010020680e07044503100d144240601002c1039070034913251003108101c80d007a4a40410340d07080c51110714959044121810b0300b06409921280008030705e180000c2c4190710032840162a0000b00482c0c003040135058001506052802500384030b03040d0050150ad0445804900d8190380703503664001e4882c845102000081c22070710000240c40010780200c0a480c4604007a5620f00340c4c0c48502c400001c0072101950303000d50903e8090042000f4600e0b0b05501000940034108551018000c03000102c03c0341d0006020881e0084c0c080000204d04005001d9503400c545e0701300304001403622039124191400b001480c01030400c0500886144907900034452034000f540c06c0416111880004e080070340040314112400352107050103640c56a4606d02400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312773534 1250 312772284 312772301
    0x714060c06060112111201030b0f010b03010315020702030610090c0509130b150a0914010c23210d0501090501150c031403010902070501060e060f1e1002060108060604 73
    0x1801010940c4662006451405404d4000c0103815111420050b0482400c0700078205076144403d8101d4940c5181010024000c0140c50109154000d0004108001014082d0b0f41985d801100c1540660740d1803044000920491100a400d802800104200082901e400e00f0441e07011407010300c102c409203001100d16110708200168003491502200440b408264000700041b400500007010860600b07880c01659000a1640f50015614810074000d0b04200020710810541c28200310000911607600c036000310b4803102680f440400801004002c43c4800c22054005007581041d045801c00d90420810f0366900400c05112003078100390000410409611500d4101c68000c1c002c1c440c120008201103c814100ea2000ea04000c402d00d901c44010607400015030080442c507000684e5280705180050940c2c840d0340c400315540c0100002c1201607214400c00c4403000c40c04079100440703240a01c000d07041540c4003000b4550015104512044c400d0340000706181070310700c03240480d9400ea4495040002703585200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312774784 1250 312773534 312773557
    0x20a06021b040203061509121501080d030c0507110d0803011509151b062019030c1407052d0f06011a0903031606020301061803082b060602071406 64
    0x1007110241084101c1b01a141407007004041550074944900605d01d040029805425000321000c0100038280041012f624003c00e181006d21403410303520401751081c061f0140103410016440c1b10031419540e00705258441c1d41e03102d210a87c595840d05e450301002c8202d202a20041007000d00081982084440c5411107502280e80390324020040240e10b0b015981e0140080b1109500c1d9580d0328070030002401c8480e040780404040980f240011204921001d0008950105162604020351050b6500490038818030606c000d807246c0d60551440d080c2c0c80c007002800540c0600c05603210740e00c0031000040d403400d5040855030403903410502040060341c40345400e10030b00180201c41501d8640c0040ca00380070304441f110007800e69080c1030300c5502e42110401041e504842d11940000140041c079009008400303554180e01070081400c1c00e5030340b40c01140c40750f88122900303950310510109008400c070742203501c0030005650510a00780d50b0031010350385001a028610680c0e00c1d140001d9070324102902514200d9110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312776034 1250 312774784 312774799
    0x130f180c0603020a051e0702010306150c0204020a140d0203060301050612060a09231e010c0203040315060b0d0e060a090b0a0c020708070b040e07020c01021018020a06021b04020306 79
    0x1809400e078000c0d80000200400e00c03009005400c5003681c202d1485d6500191b0000d05036440500e880018220384c0079402c18041c41030001c20152046920510000040381d056800598031003401da0240d4400c26254002e80c40210b0011b8030100b840c25603005140545000d4009014648400b000c0200d50480c0d004030300c045da0b0000700043c406a106801c00c009241c0603c030074001d907541c90314410041281c0e03c3c00307031030341c41e4000010300c07003e0501510071400c005d15002c000c119501091200a440303200f503110140180e1840c180300c102d0f0001c543d10840c02481e5180c004d07607039002658502c00203040404503160b0140600e500180d6145494003400034203690201610b2440d5035412003904c01021860111740c214824041d004c5050b10040003504041c0008a46507500c2d545040c0521311030303040045c030031402c64015030040145643c0008104201e0035418a010581ca4011000b00d1174180320200041c3d40b2803000d81d070021301c0070b40108500e030007421024440c0c920f880c03003d428402648410303154590060f01c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312777284 1250 312776034 312776039
    0x30c0307031a061204051501050d03200f1b0102010632120a14120708180a0e09010b0405090309041107050d031b0903110d060209130f180c 61
    0x4039511214480040041120009101d074000c600c00b83c03c20810644d448102c0e070180000d2190070010030580c5a04008002915818400841c002060103200101070101c9203d0900c01d0030341c5074020201d401ea141d0214ac003038108101b241c075611030f0f62a0701035062031590203207000b00c1d51040c0121010b64030b00001c01007540c61400002800002415800742401c1140c00f11502039603a1b04442c4d00324070801030b0052114402e20300700002481d020f1540041258000300310752071060500d07010342c0d01950700001d055403280c501c0d1040490a01c964119264400c000e140d004c11018589194140a103d0340c4000b000895041c805100c04c880c420390321210300c0d078810300400e0b500345030980003d5411f2007203d4105082c0750740c503668a450030320140c41c00404a0340300c0d104500f0a054981c881c0280c0c1c0440d20301070304583e181d9122824610f00403410a8012001c0052007028002a601101c0c104407016012100428040d04614020640c4681c002d5600c1c0c100001c0c10f5100c0c1c032440400c2200c80e00503000800151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312778534 1250 312777284 312777287
    0x60f020703020d1b0b04080106062609070315050f01120201140309211803060f130f020306040506070f0e091f0b040303050c010f0203090d1110020d06050a080102030c0307 75
    0x601003082140d0225035000500481c1a446403680d00030504100a90b41b2036080c00c0f40c0034292400358014400700482400e000380d120705107022450308007100800301c8540752500005d03242805107980000d0501140b200420100c0b00f026400381344240b0a4440000c25079884a418141c202e8640d100a400640d104d20417941c8840a600115000840881102e04640c0f4644102c0e21100b0f0304180b40c2030401c404104d48511522a036180760411030110060440303890559030fa2500410050042200c128015080784108903080300d820600d40d030024211901890700d4034181c0c0da034090417140400081c2181031120240b83c0107881d281c2d070020340180408400e03503411251164421204122802528041c0b86c0094107000705401400079501a55031035581c3c694090310742c1e00f92040148006007151041040004410380840d800002540310700d00b819003442444040c0740391050458604d80010320005195200c0b056990083c011520305882102071250f40d413110b00e080303000c2110100394545c010800a01000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312779784 1250 312778534 312778549
    0x50a0f030b0f10110f070e0c03040c030f02010203071403091f1d040207080705030c121204030309021306060c0215040f0b130b0f070b15030c01031e11090901060f02070302 75
    0x1c0594030706902807104d202e02c03071351030f15205101c00d20391600108001c4c0b26000104161683c0311001620843ca141402d0b81c07201c250003040d10021f000b0310b0840900703c0440e8824400c0316401a00b10020040c00c4a441e21115102e0b405011443d21030b90f04c00242a0307000a40e00c41070205d10040d0344607410075030015200350021a800070b10702e552040d400c01c14100001c00150180c0036090241d0002d54407104596030300d9203000d20880e100414404140f1209c0d8200145420083d4450351610340880e0038400d520218580079001c0d94000a82410000080740b1030b5030100901035054001c0f6641089a034091501000500c0b03a80690482d1601e0b41d03030184565400c3d80000c14602c18940d029400080c0c0c0d030b1034100d8054020200480e03040100213260030600900060090308901120300000e1003c40d801e00180c1e5458142d2032050505413214103c43c00100d032008820010802c001c000c2c082088050008080c1d40e100c4800d00380304009107800480c0701841a290200e9014540d0000c040030f82c216000c00440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312781034 1250 312779784 312779809
    0xa05090607201203010f08061b070302100501080105160513050f1206040602090a0801020c071509030209100603051e0705090411120a0c02030a020601090b0f06030403050a0f030b0f 79
    0xc040e41588142c500c001e0400c0a105510150070903282c0f40d5040c0813000052460075480908103502c601d09105103540c0a000380e03c14540a085516580e500307130324040e824503280b0070f07441c50000e151400002c0c100c203043d0030580c0701303c0812480c036950009020054501b4041c11884104120544006011508007841855061400100100301c8605440e00b444d1a1460480f0119001900031541c05041e00b080003c04014011200084d4109250000750300d0307a8a400e07210343c00d2080c0344d084003128003038000d0081401554002d006200c0601c0c2644120200e01d001d0300c14180003038a40000218402c190301104c840700f4845407641c04140d11008411611600800811036025656540301c0c400c0050700300c001c09001c440000036800700d2400481a8045449191030f00e001c1d50400c02465007083e40c0802e140e8151891038800040704a06c01e4085060221028020750b0404000814071040c5604640940340c140035581c0c44140581041c80f0403001d545401d600d070358100c2d51810280245207001c140c43c2c0e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312782284 1250 312781034 312781067
    0x1207170418090308060111060a0515130203091b06030a02070302240f0c0a27171e010b0d0f021219020a09052a0405060f030f0a05090607 60
    0x6003601d901c110448110701880c92a0103a6607602900101600829000c4e4030070000d0070502e0304040000320054071110001d05220200e80c0e130748001047c03040741c0b04498000c0c2c80c1c0a000ca01c0c100025280030350081d80282d072503100038071408a8140201c0c0348003150203203d2501905044c1581c40d8541c0d508043c1d008020300701c0070b60054407864140c442040076121401e185440200e5002d04000515588160001d01202000303a805c00c02d500049800510303c00c035520241800d04403201c2112050b4001500942000030a4929030b0841840c00c040000d034001003400c07080400d00d000003c0c216485c220b40544011541107810000d600c00411090b240c1c800b0024000350a5909852151020a090806045022040080346020541541000e0640304003a000a007401c02c070320b08015120401d0a00b034030084030039400e10800f01400540d121011f641c0182401b03040c0039152101d0380310f1020700360030031904c0f80e40005044001400104050080034020043d000c0a42002d80340c222041b0b0300106070300010392 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312783534 1250 312782284 312782287
    0x180c09060c06180c0e0601020105060a050d0203030f0d020307262410030606020c04090c0b070503040b040b0d11071101030e030c0709050402030f060f010b071a070e12120717 76
    0x40245802e2052110070074400e180c5402d000e420005c170720040e084090700c000d04681c940401c003d505d0b20f40b0210201a19402c40d4949508121807001a18501c2428140444c40c0408940c00a0038042d94002d140294040d840c0d11a014480314132400b00d2088102e1180e0301c9580c3c040203d0440c81e1b901132000c280b68258002c0080180c00b0102061074205041c400b207002039506c06040210a5048c00b03103030350b042c9e82242c6c00d0240c05a103440301c6520245a000b41c4050000008005003040303c10012600144501600c007510b0301d84c1c1d03030500042d07a041500d80c001181c0c14070010a6043c0c14040072203594540c041c003142c3c1004024401140200440340761100e041c8010800140c03c1e2800b040000c006162121011841d8038151040c9402d00d2b48031048044030341c0c13110003480035000c131100001c0d0554004c5900c01d6200d9806040406d13955052080c415402100700041c02820303544071080c00444074040c0c68001080b018254030f282c0d28041d001c2c0c0c01c030040784144042000903029611224040c0c1d0340c1c440ca00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312784784 1250 312783534 312783551
    0x10b0d081c0906180303150b1c020c0f01090c050406270609180611030403020723040c12110c0c0105070c0302030105180c0103180803070c1b180c09060c06 68
    0x200403104104c8030500784291429000c1d003010380c140120482d80021002c0303941610701e030075505000c900071a45019101d0401d0f8410710b2030000b10f0b50654805551040480700000b11030014107000303003001d0800351503072000c400012903142024012041241d910030072800d43c0c80c0b803140d800582c00c0500301c0c0d180c60080c2c40f1180014400b00318010060383c50301c00b0408810322250381c0f038801d0446001481c02034404006108200110783c011403201c0c21610170200482201203006000700741c4d4841c0108044c0d00900d0440c5103092aa480b90300c44100711800807040219001c05000d6035068010b400424a1650100c16900341c0c135482640075100c450b100d0f20110241c0ea8a0790f0000b401e403a000c03600c00300035042e14000d45211800c10802c01100600a08041001c4000d1312001900d60091100240844c0400800b203a0315520940e610654540c111256a9510890404010203041c0b10720809001c500706403440da8800c0780921801c99040c1542e100c03104d580303141100907180d180b0400c01c10fa80055444501c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312786034 1250 312784784 312784793
    0x609100306290f010509010f12090b090d082205030408030c0115060504030305090906241308010e0303070f11030a0c020901061803060b0f04020c0a05010b0d081c09 72
    0x40c0c40d90656142d46070603050b41c41c110448140030784121480e100380b0561282500590b0000202d075140a02031a02c1010600c5030b0000741c1e251244070144d504441e00c0c1c1100c2205000341c1422031805801c202003556860401d40c842100d54080c150b0f0014519459201944d40c0b403200f4030311542d99180300d4402e4a060a41d2842100c2c150303080306e404142c059459002c03040200c02d405410102800d2541045130421741980c90007401e501600031003d01401c0c00b940402d5545d56512220f0001d1070547c026003622000e00c1000c940103070002c0e0340e1001c0d0343d445218080380051041c00354080ba116079000550942e0354141c4200d400441e541c4466041c041c2076a01035442034070a00081030f500950b500c42c80e8031806c041c81400315095050380044c007080010b44000d4500302100001070100c81d0450030103d949500100003d5014803803041280d4017510000b21b025134000b000c00c415200d40d00500003000f04001e25000e20030400002c1d01c1c01042c0c0902003041c0f0807a080d9090058840e16200c500019110030103569 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312787284 1250 312786034 312786041
    0x601021221010806040b0f0604060503012414062208060702070f14030a150b0604030b01031a040b04030810151107090213030b090322030605070311030609100306 71
    0x41041e1004561254503121240085103801000c0e964010071041c549515540c8030014094151403d8500c2800810205d6882d5000384001d018020002c0005601e00100c002510810802c071500701c0c02d0000d400034001c1088101480100809802c039481e1808170068440700038241401080d10148032400841d400e6001c00445100d0f000b0741d0002c29149081c0b06001c0c0c0b03201e015a015901203044094138a0040d2004109086039550280031808030f005000c601c2c030050545c441640c0e41000020070000b040c0100d2504050480e4020302c13559000059071041d10309958001c0703c028220004010100300041d1207008200d62050194503200c2c00503480c0c2c0303410b40c1d821020524420005503c156152403210381405420010000320504514010f03030003176a8016008070788005072469004c44009010340c9010310840e4004010a0803440407401c020506540f1190a030006459080c40d140008100d0360003480f540b414003043c07202032421030756000100900d030300300102074aa100100301800000a0308900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312788534 1250 312787284 312787297
    0x1b040212070507140724022e0e011a06130306050c2107020705190e0a0204030c06020102040e060f01020f1c020c061e0903030708040b04060801091e0506010212 70
    0x40d1042c0d80c9400302d0078503051010101c1100801c64000203003c00120401203040d1082803010401c0e00494034602c01b090b0300780f40c1810581507006006080d071800441c060700540c464940c2d8134004004540106079502d00b2034031034005501445130310012228003850504081c1503007101c0c48808000c510340325a2002e003a00c0c000d0390341e005400404115092000c3c40b140910041c0c0ba091300080004d4a0400c0000355a03120901c038a80c09a1020744645000e1701b001c170840c002800e510404a00700c3d080003c5220700075031082c841030b1080320110310003245451040c000c03101290040200c40c561038a840d070404c8142d85882c45068194820000841c920751400c0c410441413020a9003040e401c01040300d8040e0614a80010503441494100b2071402070404003040103110b400ca01203c1a00c419615003c64514810281c019210030008240000d22140440007030055030a1070b51541c0c62a41d803000108103403120620f0400c4100c0200c4900b600200007584055400b0340144100e4031012640d808500ca2580040b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312789784 1250 312788534 312788537
    0x60d0c0f080a020a0c0b060307050a17160b09040c0516380a0c090807180605060c0307030c0c051801210b041e06050108010b120d021b04021207 63
    0x30314400c0a1140c00c00340503680180c90070b10540c64080d5503003006246059002c001041002c00c180801c071107481c10002a400b6003000b524500042da10b94901c980c100c80d040c440e0341d03c0d900c2049080c10150300c081d044c51080341d02004030982061100c004000292510001c14010401d00744402d44840d605030301d42c5003100c3d0060040548a030142c102421001d0080401e9100ca81a10031000390340011407140b45921410540c4005020032403500226404c101c254400c1c0300601c9000703c0429140b085280c00600d0b2030901000704405035860b82403000724020384e07000f000c081e00309000146c082030207442d501e40502c1c8a580e11000503a242c20000311a591a41c031554499100d00c001813105014290620340180114044062002101d664440c29400c00800081c22010781e550307801c65040d46020b4000034030b17500c80414801583c480b96110700074054803aa0300e202c2c914080030b58850b94000b14000383c4100265011f806840420403c070224805600103580d04aa4200003c07003440c0b010700507046c0103e905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312791034 1250 312789784 312789797
    0x41202010e03010e030a080612030309160e19020d06050307120204110f0913020c1f050708010807090e0a0c03080408070b0f120403050c0714030d0504180b060d0c 71
    0x55000040000340e111180d1400b030380c0f4124400803284000001d6850030261480c1c8540503598010200d00500b4006400589a100100c240301c60041c001c0b034198030007440c100784007200c5561040b03440941c0d00305662a00210074100324102c2c141507150003d01d06c0035a42000810003651b01d6001c60301c1c2c8105540714602d002c5900f6044402c5252034002d04e084030102080c4136040201d000d90040e06d80c4101f030601f42c42101018010325070b003030303494054074104021030064440b500c0c203e0804804040d090111903501514000c009610680101d110031305849990000306211810f000700c2c038000300718500011500d84201c1500c0b20000d00d03080b6900025500c80c501240d155403508015510b400015040780c40c5618080c0051102c0c40c2d024001c0d6000c40070380b00d40003041c9485904007074410b840f074209010340c42d00030b5820104140b0801d440d8a13a04610980c1250068040e05c50101d890380154020f1032022021705502e0b8401c00101d400c01d0b41040f02c0204020f02c0d10700344010540403a00341440c040d020908 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312792284 1250 312791034 312791069
    0x50f0607020d180b2209050109140714030a0b1207060f1b0204090221010b0a150e153c090904060f0b04020d0b0310020702090c030a1104 60
    0x6042c000e998201c441400d09000c060720401001c121000f1900500c003640f48041000c4817452030320b59100d8032901c82d843c02c1121498a810000001c0d050074051850440c1c10020b844903411518242c540c400e43c00f983d98007804e80c2106900302c200750700203481d02e90300c02d4031003040f640c00e81d84d90090603908110403001045054540040604180e680e00e100d43c003070183c142502e00803e4001c4086154007541180e00084444051000a88140303104211000c084001d5070100d0b1000e80540c49501e00c400e0407107030081a07950300c81c0481e6001d958540f042c00069240003140c0c40314144490f110b902400d06060103410b00d40304c20104d142c04401c00e402420103481008402107202c100814003030844454081c1c2c0e528081032800410921303c03004e84000c083c9540d858802c0e5048103554480d04000e28000c00645d030340c03802c559000c4041c0c6025a030043c464060b0640b0740d270311300144d8421504003950240000055503a04215075482d0b03000140704e800450344070001207002c00c1c0d0b000c00030320180c10120a000500e68 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312793534 1250 312792284 312792287
    0x9020f03071d010602010603081902031603030209090c18040510050d0f0b06010c1a090709020414030c0d05060613090c0f030b1806060d0302030c01090302210901050a0813050f0607 79
    0x410691001d005d69162400910200707004400310b4060240e0014003107043e0888400c1240742d8450405803202c040c1c1c0007031b0741c2d000f01603154006040340841210807070b046450b084615541481141c01c6060b00140c4408119244e05107604101d900c40d08468800d50301543c0e920102c0e112880000e4126080c0e844224914100b142c244035041d0050803c1c60134894002c1c2d5962081004110f17101d200d1030324a104400240d128104102d04800340810310019034071690303106105031403c0d41100b607880c8a405100224030481c11f05104031058260400c0c010070a40d01c40c0400d1120344030000101c40012078503481074501081c0f01101020017410340e00e451144051841c10800ca140a019203807007030500103030786042d141071400a181c030b40041040760703000201c285a1605074654890005140301c95400e1100c480c0c14150007080c07400020039582c0c4244260072103107004800c3c2d4411101024046001881a48842841828039a902c01081d041480e01540b05480341498010b82074440c07030481e840f0604024105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312794784 1250 312793534 312793589
    0xb010f0f03020603040221100c020c0102120d0207031808060106140903060f1005031507080702030c0709111b060411060a091503140f1f120609020f0307 67
    0x284851a54810901d007141d0018540b80710241001e0720890002100800c4542e8590070152040b0740c130411200100ca5401444001d020200d1049c405406200d80c440e03229400071404038104260a8011440d114519051344005d400103035050381044014460300c03043d0f0802c9902c020241413141e0080017590315050006060208620454003500418811903419440000300c07150400d036101458140c0e0f60341c9980d101440180c641c032a0707600d8420980c840c41f660005040f600c0c040c100300d076510152581e413450166920320a01088440c251701c0f08504006001c2c840c5e1001380300344482c0310010710f04801c1014039107002c0302005203550f40340c20040c103001c208a4204e1000030b91850036a001801c1c0800701c0d00242c030030145881061080342c103d031301107004a886544901c80c000381d5806c040700241017420900b05070341070460703500349204440c4008041f0b010030b6800010442d1404c140104960110340d6903100a4896014126042140070400354007607034040c880600a411014003655444c0b10000101e90300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312796034 1250 312794784 312794789
    0xc120118081306050a1e0e10030f1a090103060c0c06020a03020a18050a0b1b01240501050f03060d0213061e0e1005060a021006170f060603031b0a0b040b010f 69
    0x9028080007103c107640e0704130359070700c48050b00c1e06c0074442d15510054003a59580d00410945901440300c4040c4818560141d000001c080b4031030004002c86410340e051840d400c400c00c00c280741d10105444c010000501c140d00034076000c00705c43c030340a50501039560300d410590300101d00b80700c040f917000705014005642c0544c00c0300c0701680040d010707407140d032409011070f000196900682d03494040008140010312070800e01e083c6000e2901c0c00800508072400c2c1d004d0007000e440d540322030703a054040600148a62140095604986250081d94a0342d181c80c000c00c01f104014070400c030380069070207a40c2000700310284580d030001c002207134450300016a04035040c061081103401164896252074140b24038110450f4a207001d0319010341c3e100ea036600c107080081e446d10002c240042c0210742015004140300b000502c4d5002c2005da6003040f030700d00744010855203441e280200d60a540691040c40041d0301d8284245031014803526850a42c2d00d0540b072500da5070b00d0b04104890a80da1200da42c0c00412080e00c410b0b407030100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312797284 1250 312796034 312796037
    0xc0b0603060c0a050703230403050f12090405090f1006060e0a1203030203040f0f05010b13020a02060417070b010b03181b04020d0e0105090f1902030c120118081306 72
    0x2149000002d140c2180076030308056003007241c0415920308040c001e600a4100c50382d480c20703445004101c40016032582e8094001111540951240411032440c00036900b4079240321113100b6403d0084200602008100040883e034640c441d82c46a01c00c050310601000c180401c550202050030360420f48090080343d200c070300040c01402d420b18104400d41e2041000e80c411940341c50003582d20f88450510305c089000e01d078030142040420015041c01c00c58150b010350031a207003d444409c8400d041180100c01c03030040208000150b08100001000180310b0740c100001a040072916a040c04c6c140d842d9858070200980210351003030800814000a07402094030345030b4800e19080241340f1040114091504489684a0175004540106221101502c95080340c2e01300715040000f0805490800384144da00e0440002105190140070881012850300d5150601380035000380041110f07080d0101030065000d44485590165562611b100720b07172031420408036501601650b0910b444983c04141405011f61710b034000d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312798534 1250 312797284 312797293
    0x6051302060d110403021210050703020403021807051b011d0304180207020d0f03030518030310170c04050f04031d01090308071106030a2009090f0a0e0307030c0b0603 73
    0x10707a624811204809541a8040380c1c0300c007580700c40e40e042d0249800c002d502c00010340c0740e0710410400085400c24941c0244040c40302e42c4030003c0c2079049205600001e03400200c00ca0303003904003211040400390841e81070328159242404034210b4412080b07102a46104907512580c061018045183e07039030503110300d58006186001c4c40c100705110200001e03c0781d056a540c02003810020b65442c2c1d44007010b0203400c0110074510100030b2a00400404086820904201e4065001900c1c40303400001d89220340382801a540c090f40c140880029a0400f5006032907152142c1404951280c60314010f0502940c0d400203510708606003440e01500404612064140c403604000c200041ca81e848080201129008000c250340c410803410300031000d1008a00007600180700101748140c05515a216003882606284404446405d55040c02c4240c4505130243da802690f0401080516150b01c040541005116000048009520603524159040b500066000c00c03803070000c200c18001a030546650000c4c045000e070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312799784 1250 312798534 312798571
    0x1509030c1c0b0411130b0108070f080613090c08060f0a050f0408090d050d08060f0a05090105060c0f0a03050a0801091416050408070305010c030e0d093b040605 70
    0x4807007850720319102800500c41800070406200c400541c02601e540040c0640d50007110303010f102e02c0580303840140580024032160009901038401c910102c20381c040e40d610181c0c1c81c0c550004110745202e4060110180390345d83d1060000003452000c20000a2060700040c0c2502e2904510f42002090004c140318606418841041079040052200320760050740144007648031184240416003690341914000d0451048042154000742c100003514803900d01281c00143e00c2c0f00c0c0d4424000800164402c2c0c0390001002d100600c11807510001400e07100c0c00e00703003c80328006424010340b46441650002a4042203002a914140c50340c8400a2800b500341d90000348407101c60710032015039208009001c80329100d071110383d0b400c540d8400d604880c010003085003100c4c540384e10380c00c10314003d00366804403070013080c9410410740b85044041408401c0d00b0890701d49116051504645400e81d64904070110007511075a24000107070514041c082c14100e11342000c50314149042c1c6401c4d0200c3c1d01c05404141c400303139a0081d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312801034 1250 312799784 312799819
    0xc110705010c031106070903020310090b0a0c1b03030c030501230904020102071d090f010605010c06020f0d0c2c03030d020903070807080a030801140609011803021509030c 75
    0x92804460003881c0c074602e00d408606007150448401c0d8010071060052070103000d0749507032155540f019640220146c40b0050012061803089030308694000b00290003100c00580012002d6000c1c40d4801c4450800030382000d20200c0010340e601269a04401095448030030080882e81846202e001d0a80100d008880c420410440c0700056044001c45100c0da06010018046900c244180c400404007007050fa520040b24450007510030000311904212441803404a02192405024880c21204107031104485105907840b41d101a501c40700d0f520b010040700304035010580c3c41c188600d1260041c03c0d59a00560310724808030b010702c400050010308400e40071000340f001c203039404001c840882d12045401a034800f1801e0106c1e050800c0c40e444001e00380a40100002c40d0440800c240aa0620030b030b507001d085a894880715642d00402c003a001c3d030407000600045203e075010710202004446450001c0701c000d95030703a0000e1604440e0900c0c0f2001005d02007a203d00c00c2c00c0400c0031802d800740899900309011315940c1e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312802284 1250 312801034 312801043
    0xd0315050a03020415030204060b0a1128140d0c060e0106230f03010203090c03060f010602070b030a0219110c18041106070506070c020a0608070f180f03050f010c11 72
    0x2000c1d1049a545c980000aa518903030004000d40d07003c1d000380b00e070300d9541c1291907031900b240c00050041404628940700c03801000c50040e03820305a00755001d01460000e000306180c619501d034100d030720012111000800040422180101c150103665500040e00140b5081c01501c0c50680d078004e2580c10104207200e0003541c0708583c130100300e43d01c842e811203039024030002d40c15003030404100760107510020510048020100b102101e01c90207400311001a20354001402c3d03170b128240700e03802c0141c020300c10903c14404101d0007541c0009034002d0140c00c00c0150f031031007440c0201c0080800080741110740902d80c0c07030f80c0c01d204041c042001115050f503c02a2043e03203a0001c00010002000e02c8a051400c0c425a134031801603c01150b0844119299864568400b600074616946d0503032203a26110750026049100302038880c403c0c44e0940c1d40399004031030150140e905c5000d825440c00310200102002c580041910030716001140101d004080c1503400e03020541c02c41d900320007900704126030b1140703000903100c0010307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312803534 1250 312802284 312802289
    0x60e100f120f05071b0b06131503050709050612030405060315041506030c02010c09050d0201180e1b03040f0b0601210614030102040f060c15051305120a020d03200c0d0315050a 77
    0x8c500c0c980c4001c4604648008021f007501d040c00c6200104000f00c284440007070090243c1348001d400f0406520307100100008103501440340c042c03036407081109001500303090b0081c68208030060600f22280303074010005000d44842004141a08070400c000b000f40e150301d80207074061540f40e03000802282400303281c000d11400c00d5006081c020003404081c4011039104403000c40981c81c400104100f850307100c00303040d0751014055a250790203003c00003044c0d402c04c0d0041c04580c080c5602c8204030360034000c2d664840d0b0040340c0040c0276905001d541841d509845512085007a10440e4020340042e4090801d843d0003900c2640003160760281c2c0c8140024040401c0c403190500a40c2e00c141040030814500c0e00d4807010300081c440c500b50b1040d0804041c00301400300b00e2005070325140300e41c0580314808170008145034070b4014480c4400c01a4080d03061521440d00030b502c000d0000d1001135484003420b85540761031080d64049240745120303600014000c03030615030502c03d482246c20b090504260f41441c10700043e052a5190 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312804784 1250 312803534 312803539
    0x5010b0304050606011b030e180f0a0c0f170402130c0215090109030c0201080c0c070906050112111801021507051b07030201050315030a060603030207050109060e100f120f05071b0b06 80
    0x4003801d00d00d565400544403004101807512790b903490002d070701c0c8451a80a07665140c400b801c002013000070f075000350a0164002041d903180001c0c005d191080d00140b04000d002a078011001110884541c0c1c01401403c2070507038590000d20354460454540705071024010601030343c592408841200082e4070041c030900d0300c0e80904c0d01504a481e84c417050f018a104e4a0403450070b52180c014001109030351a0490720842d0026280c8d600d4000b0218244030548400710300885425004108210b0200340b040002c1669060600c12507a06411580d0715102c020f00940d0702d04007103440440d0250500121003001c0b00c2c10003952002d0940d40385940c1c000f8000b800090031203219001ba2410031210b03a2402c016010040360000c005004032a03a900f40a5140c414034014035002892054001c500b80340a0700a01c2a07a10001d00780e403c0c4540e5415085070b0209803100418200002c810b007030401c002c598000d149510704100c90010303443c10001005480c004480301550141061f00101c01e001c520fa113444140d011509 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312806034 1250 312804784 312804797
    0x1b0111010e101d0a050a021e010c03120608062e0303020604030c021203031e06030c03030405090a09021201020d05160206130c08030c071a070803130804030605010b0304050606011b03 80
    0x41100941d43c211400c500c2c041032080340081e401744540001e00121140c000d40744080310a04002c00c0c20800041d05580741d020441c14001000040d2123220b81020348034400400080b2503403254403080c00c0070b406403050080000301c0c09041d00071280d0300340e40034401000c044a46051030f185550203905c82800510283c103001c3c200c2c40900641d01c85480703900c00c1c0880341094903030f00e00c0c10100503101c580080004105401c0f4610005801d030500040f50420881c00800071420700d0311708401c002e0807d40080481180e1900e4006000040e02c1d201c42c1140c040b0300500000d0303140ca41d81e0304942c01300c1d81c0080101c0124180c11241c107100b03c1d00801c0d40b90300414496440340d05042541003041100c0f90303661082c40ca40c4030005036205140b50110340013050b11040005d41d1241d103a010040c000742e0040d10805411504d081000c1407440308910720b015034003841200f00a0602e541d81e02c2d000100c4400742c0c42100002c3c000030070002001303414400c00c4c2d4020001d00300241050400b90031148030102da4003004050010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312807284 1250 312806034 312806051
    0xc043201050702151c1b090603050907050607060605061c0f29030c09181204030b01060f020c030a060507020c09091b010507021903020a0602010504030206060d03111b0111010e10 78
    0x1c2072060500c08518148090100c100c841c561050484455003000001440c1081f0110703100b4480c1c003d041c05100c1a80050801c9410704080112540c40107000321070329030342d80c08000381c0760f210030300540220030030f070b0302000d00c1d0103140d001c10301c2580c3c200304805410518003c3c014645c15020344400c070103219141c040c2d00390541c643e0040f84c41c11019601c00c0c5c2d80013400604008410007440382c89005140004c0503607005084102036480b03d4000d90100034140c400480052024a1090400200310b00c440c0c8120384007078a8036004a4242095154180c1e15680c5550402525640411040d08543c401b503030364110b1480c02c0c4c5c4035103858041641d03011021044d41d00302040f8a030f1144068a0485400502283d071501c0107080c45000400c5501c02240518821400040d066006101d2144583c1d05900500460b81d6601c04000f20081c2c07481e0110700b40319201580d1f00406004001c095600740540c51150140301d880da00240513503020300c0643e5026030410041800154000c03901c8001d00c142c2c000003142022 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312808534 1250 312807284 312807307
    0x12040f0501090512040518010b0702040b03150403031b21110f03090610080d09090903110312010f050604121e1e0210030603050c01080c04320105070215 67
    0x2c004006002481010b131910080e8a1800050040311012600c0b00c0030500904058000e4042c00d00c01d034440c41c84140074100240c105600118403005005085e81c3d138040c0705850765034002c80103407802e40000381d59803241501100c0071702044130076603124240303c410801d400c81080c00c1c10040c0c684281da00c1d610340818643c0d240b80541510304803450094034580317a1412918440d03940d030048424040d48100d00d00300150a000c0030811041800059903449803481c180f0b130041e0050f100040c07040701000401c0c03492164103e02030000e44094015100020701550ad00303a80400d8050494001c9403041400f04402c10141200208800e10f2a500a40d001c1a44040304440e0810020b029000b406d041c501048084250600f081d86990366803085940300e000545a5008078104e4206010080190f403102089400c40c1d80103070300761580504034540c49881c007038481d414881c51620035098090000b030008101004403411144100c1608d90078070306942004a40d0b000268424200500c1903d0a0030000d241410032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312809784 1250 312808534 312808541
    0xf050408070308121003020d1419080d0506060307020d2f06010603200a1b02030d09050a080609070e0c09030d0c0b09121803011410051512040f0501 65
    0x1801a030080e18a4103640b400c0080460b880f20400d16520010140022100c0042c41c900106a03a00504071480405180d0b550440d01c103040324018200f4419001821500060302c0d8012404034400d003591500d4038002c00f61a4243e44000d8541c510400c2d050040145d081d9000900300001c100d945020488003c00c540c1c403640050b10000c0d0010031440b080d00d80d240700d00002440b60304030740ca15907040100800304038480200221070318004420210400030f0449180c071400300c0300103c2250803860520003445900103490500003a04500229000f040c1c1008989050f03440390005014500c00361809207811300d8580e03100c00d485e026801018130303840086031041048a081d100104005012204c0b540c00013207000d8060828064200d814051000c00900ea003c00400c02c012070b2003005901e0b0b81010031340070300501042001e81006401d99681e419001d211145051000e001d035044188078012079052200307110040038000071030312002c2c60800106100d044240f4032980d0060300711940c441e110b001c500c2c11a026 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312811034 1250 312809784 312809789
    0xa1518080d02070b0919032106080c03191115040806010801062301120b040902060304110301140112021009090f2a050306130209090c03061c080a0f0504 67
    0x105408140441d929400394001c01c9010b024103101161139541c40c101c940e540542903204400c02c2e90922008000034051b804a407800c40300c074202441c5110848411404032502e603848640e0940c00040b040c1d50b01d0606001192080000130741d41c040b203010035112518040c500071032641c028403440255100c104a284142e9010303169031815a940b81d42d4448506010700304078010007480c000148207810414542041d841c0b031154044e11441c0714042c2c107250040007041d00c0104282c00c240c555400c48016a038880c000c40c40f481c8240000002140c909041c5403c403002c10658900c075402410040c000d0540422054006a41c1200c0549071000c080c0d07011101e40e4810f5200d85956070030002804d81220181c1c1002c800c0c10842c0450110003021503900850700740140709a10b000c194100301040c0350341004454040c07022207030807015280201d8940071681c48203003203900010318070010040c0300301807030310302840803038031200789009003003d41161101e40c0d181c418031101609001628408400060044042d43c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312812284 1250 312811034 312811043
    0xe0a020f0705010609140702060403080a02090d0f060b0d08070f020609090112121812050f030a021f0501060503010519030507120b160801210c060914030a1518 70
    0x100c8aa4520b8024042c0c402c6000d581c40590822084150000c0780a15a512450099006180316111a1010f5a520501a0400400c05d40810102006440c0c50841c8031900d84120b00c5440d480e0321a0404100712014a11041c0c80740d0580c2c4e440710040380315075040e02c041d03641000c00b2205000180c80003031814030030100059006803c034400000e00b6a2070740c040588141c01030718800d80100c0340c200c04640c2c0b020b98001074640c109844000b40605c171404030324411910f00c110215000040e203415004d1454200c1c0314503000680c013901043d52400010031100e0b04240706984c044c040307941004001ba0840c0014025280a2070302200d6a000090129003090000d5403c141500c1030162a1041c18500001007002914007151000200380312002c98292030321821850350b1980e101e6401e00e1050b4606100300700314000b01d251b01d00d82020101e070001911100801c000e0325415105882c0085d40041c180d401d440c1148070707400461401f00422260f90f00c060b9061301c2c401e030004100300303031000383d12101010100c00390 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312813534 1250 312812284 312812287
    0x60a021f1e06140f060a0c110604140a080705030c040203070314010b03061002060103020d0f150c020a1e0b040204050a0609050f090c0d260d020307090504240e0a020f 73
    0x3001040c050348030381c003581ca8881800d003c02c2102c8003403281110409565a82004080200c610018840c0381d024680502c5204001e41c12070700300d800258180c2103034100c025006d42c43d12190419140c0600c03004001d000c000007421101e403038100043d407a50382c0c00180c513005a070004005400d0a1082e0f000001c654070081c101d8029507160040502c2e540c0044415034024010454602c10700c0e800000c4160480fa402041442e42000079a07865801c100015000c0311442c05102005058003070600032a0440c04690340240310700c00b0b40b4241001d00500c80d0b205400441109026080490618405998845c2e01030f100410320352198040d0344000c00e0355900407801c091400c1c05004444140e81c01580c0204886000c41c0ca20205082c00c03c0355043e01b0030002401e007410040700c0120f6031551590585882c0c819045981010600001c0300b040e41d00c11117116001840c85907050140703242900c2003000021051a01000303412108400d00359103d42405110440f42c214070008520750308640499200600941805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312814784 1250 312813534 312813581
    0x91a0403021f0806040b030c041a060307020a02131b2a05072405070303051909050328050412080d060b0d060b120c130b0a050a0905060a021f 62
    0x1191024040d0400b0b070000b0b1521808039581d86428001d112105a0007030180c2004174550707003040b000b1302500c00b94001183c045182e8541079521240654441e0b4015001b4007c01c1c496481004000780c046010744c682c2038942018251661580c0340d4070b070080340c03450070034141c4060007111070320602c1c403014a4120024241c01c0351000b000004203000d42143d11400a180c6a02c0c00b8140e2495500c80e04410316001900078848030020038030a0b0040394004400480c01051400d9035840d840a81d0592003054840c0d90000484245a04103550320740300c01c040c2214608590007140e035000344907214a20884d5091510201120b040c04607810444840000a060422115a80d010342500c030360000320a0300320b440e15010740003d9240c4507004540c4992350380002c84159980d80c0034141e80b940c1080010381c0f40b05411a00120307480031160018900c1c0c48160320f565450348007003040201200340c55000140110310601081500750f80004004c44503085151000414582528252008182c1000650f1744039900c10001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312816034 1250 312814784 312814819
    0x1e06010c0c090212010b04050d120c050303010e07020d110c060c01110307081b0309070e09010e0a0b091b0901030204020c0f1b010e030a1104020309070801110d050106020d091a040302 80
    0x51a042003008044c4589a0366440e0a1199002e0b40c8103041d0406220118100061405400800491a01d017041d02400c0c0c1652180ca1441e042600045100ba100c4000e2041c655010803d00000801c00e1428a52501c103c181702c1c0c0c0c54900c0d03101454011440480e2a00d0340400a4220700c6040c0d009030115601d83c6460390b402054001300751542e00309040e240d0000403c2d03502c54000c0f02c0c46408018000c090301880c0082000200d003006101c2100d1b5507079007100c0c2c40700417404e102d11050980640c052420604040510312304100101d03406d000c00302007080c4000b405807280c00c68681100c4c2c0455006840d48004207515091500301e4000a0a500500182078000c12044038030b110804020385e1040ca000c2101e5081c19900c8402d01d20150003c3e00d02c03092294a403401c0c0d0001d55212407864103644e41950389218250a407401e251408009000208400346c0418143c8500317401400c0920085c17686000040002d40900c0b090f0003028034030040b03240d4080101e00c806084800443c2d010302080c0d0b407161050320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312817284 1250 312816034 312816037
    0x1030b09041a010b03040803011802070f0302060712140105100201060e07090303030c030c0813062301150f0c1203060509180609010e1f11070c1404051e06010c0c0902 73
    0x204542c0c07000aa40010030b07000d01143c20703a4403950303200e4140e03841c43e400d00d000c420114400d113100c25441038003003110100103015154400341c054401c1c0c0042000c1d0400b03e00141000340b036440814100c614084041060303004c2e08800ea030440b4030944a00040e4810400d049001d02100c2d000740f140b60000d01c0600940f41e500030b0001c070440307009035420007180d6200c2d2001c509440314600d22400041081e80442c03600d260000b140d0f52901c7c0306000028410162040d240343c4c502081c449800c1140010300100111090103940e015098202e2030b10100c00c80300072a0141a12a20007409410712207081c2000c0c148038000e500c00c0000c0c1000404040349407a00890004081c2c04128921440b402080c01180d50700c041401800402407049001d0602c13042d140c3c6000c0b444900749440f00e0030380764039948e8101c0010404402460360303c3c05240000802410b00c0d10300c141440519145500503882c0c4020010955080d0444503101c64400341114401e03103134200100c0e03513800d07005409045c1c0050388a0006040d8800d60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312818534 1250 312817284 312817313
    0x80703020c0904030e22060b0406030e070608071101020403060207061a030f0309041515110706020705010503010909050a050d081501090b070809190303050d110304020f010e01030b0904 81
    0x608a6401c564008180012004165002400300c1c201e0a0340741041d161545442d1000e0040d000050103082500602409030342140d4410742c200040000c0610060750b140c0101e01440ca80c241c0101803503032903e0401440070380c00410000400442c4c4040d0b202002c1c081d0100d4000b543c200a00b90340314201420500002c00080080a22684030217801c100c460030081f0720075170f61042a42c0618140000e82d000e0001070800019420b601e40c02c000300100d000d8605103010840da500030307600c818a46a0505840b407a004980c0c00001c1554400e15040085a07841400c49064954080d40420903c40303600d4900d01d03154041030010101d010309842c4490466201241741d206003481c446c0004030700034210040d0b0703286400d4040e0800f08070003040000d010032106070007407806070030141c0380c90160015038071402d040000a8104600084001800c0002c03549140111101420101622803031800c1c81c0e40000c500a20b51054141403047c44040303001103030300a6012003035002004d401524a403403e13183c010340003038142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312819784 1250 312818534 312818537
    0x507091a041706060d110103060305011a18130807020103021215030d14091225060e040e0c010e060409020f070605071b030c050319030c020105060402160201230403080703 75
    0x120220402c0020511300444003c0d02c20b0241c13510170703117619028200004610381456200c4400000003a002d108500740042e07100ca41d0b181035441c00c0c00308002c0e645014281403081d48260f050140b01d0b0040301c0300c01803855202101599654040c80160003074090f00501c1c6140744210390410140c81d0640c05074290718507084042e1410b040c045101644d1610b901880b403203100b0800d100424840c240403415030341f4400b81030100d03002c404c0002d25180001c1620126104d800480440030420941c00c20785900c0c0218081720240240c88040d0103240c1e841c641c02450a0400c82c07800c0140307545443c2c010480f8080d00c4541020341d030324080c4502607052580604001c0f240303686054005201188034807108001202122410b503040001a2070480b04c80030b07100d4080d0b4490004000080e411044d51042210081c00c2e600d020031384191102c0080e08540000b0649405503004200c202844d00c40c0d5144071451030741c2402c1144d6284007801148800160080c0c00c9030321140001400700501072004050010140b09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 312821034 1250 312819784 312819809
    0x718230603070b13060c05010f020a020f15010b0306060711060414030f0601061b06020c16030210020d140a0e0a1413180305090d0c09050106020c120705040507091a04 73
    0x2141a0b10380030744038040e51600ba44100768410f00c170081c4640d0445036528040c0c0d0001c5034028010f01e454040b68170101030038025070721400e001c80e8084400d04c021441541168001650f41d858003529840074403000344503e00c604800600c681c10000d60f0407215041ca41c01410780ca89454980714039045200c00c030341d0014443c0c8180c5848800b901c034000342060680d421640c80200350000c0a030700301030b041c804200840d0342c00e40078403031814407400c100b21201203a2112210501300c0b616600502654840e5229078500319000302159030a416040641d0030541d00c003a019103071b501c2020800032100d45120780380ca039520034039441c0005070158600c6407903c26a031089030b807500300d251012907034011100422001c50910070000c49843c0800c0c02000909510000605001050000fa42d50200610010b42200203010755800045c0045507040111125095040e50000c02001c00b514a4a030b488815108040c440c4d6261310010b11024443c5452400500d40400c0080b910140110b03003201c00d420034002c1c80c507035204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 312822284 1250 312821034 312821039
    0x90418030807230d090c0b07060203060a0617071d0d06050a0c05040f05011d09041a06060a121515020705130c0c061a03070e06090f040302071823060307 67
    0x1003507441d4a040c6000092410704d01411005680094008a00305442c07505c480032000446c4020f0360010309089208100045c0da80c6402810004c100c566600304c20104030790480300b0450f00a8020030140c1058460030213680c480100c40e800701c201c1d0b4040780d40941049102c94040c0802c00c0503003006000e2200410b00707011b640800e440c100c4417401035218000040056981c10040d0303501903030014074400c90078883c281a031590000070407071020056408852030305001e9019030380c0c0340300c0c4064aa048841211090301e8800f0080008000c60401c034001280d084d9600080403038020202c8000004181400b2000c4184040f9000070351200c5092003024000c1c0340022800000140e50320500b074804d003107074a441460102c0303030701c440380100810354600c001d0a04642045800d0b1703804101c2d1000508800d03640146030301d040c5040c0f10001c0d4000e0014102d035903c1c1014007002030703004a014400d035070440102c4214010386041c0300c405880f00d28000500222030903074034000441c0050010f031040c00280c0440e1030665 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 312823534 1250 312822284 312822317
    0x1f0506010309051f020f071b06020c0a050613080a2001080106080103142a03010b040e060408070f0b040c080f07180b1909021209031608090418030807 66
    0xa402e02c8008059800040c600b46640c2510300307003803030f9000c4210001820705400840c820348035489144192031042607068400c2c5c1c80c228640403507010b0590f910260800301c03c40d4001c03950085050160704c0c410b04000c50b0030101c4400d0001560300400c01d203411030305160b65078208210707800750745503440044880c2401025255401260f84904841c040d949100a5a02c0d41c3c640007c68103500c55440800d010722041c50a01081ca80280285102081040c1c0c600d1a2007004040c01c49640464a9000d20704104000303111480214800790700503003000107140e88040d646444568400000d000502c80c407404802d01c4180110a0b013803809440505d0200c1d074100014403000e0f5644c10aa201e1143c40c1c0f0b0100b03500303028600f541e81007040b01ca4405030187ca162805e6a04140701c09100e0b0f048080010f0f400b00c0c000c40c01440c007076040d1fa0850561006907261440001403142c003201140005440042c000960b0381040c0c8031540308003410310700c042c02c4505843c40c2c1e26005190040130b58842c40045c0440c1600c40105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 312824784 1250 312823534 312823541
    0x80603030d0902030a0c0329010b16171804050105120a020f2e140a0905010503190504031205060a141005040b0c0313060e0906040911031f05060103 65
    0x15040140114140066141103101a0005001c101d805005900700304000410b48003c0502071841210852120780e05914001c100d10701c081100e158160028004111400e010011542c4181c1c0c1c0e05500c2c4828509800c1030200d40c101c00c071841610301d5000510f24040c2c0d040303502c038044940c82100c0500103641c0c1c590402044540c0c0051446081d0400d14804005107008184210601e6010344501c41000b59240301c0c401d80c0054114210080d54030421100301140d00c1030420850012000c2401e0902104031381c001c0c038249042c01003a06220300040030800c403e07001c2e0007100352200d02c2c030010f010324986403400070440c0380d43c5024143c00c41d05100100300340746001074403007060300c4404003190426020302c8100021a035100f200300303080c84010040070030009040341c01400806c5441d0019961000040030707604140f80c172940180c04000469141c2c40031660345401c0c0c0368000d030046402017a5018075003010000e402030014401d0341449901c00909107543c0001c2c10501c500c5880c281001242c0d00c0300019002e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 312826034 1250 312824784 312824791
    0xb0403150903030e0d02030304021207060c0b07141b210f031302101d04050c03060d11041e0b0a0803030403050a09030c03082a07050d0302120a030e06010608 69
    0x91008003400310395102550303841048114040d140215021402542e11400c1c020171080c42d20058000004000035820070101e520303080c4c262039008203122440c000004180e90280800100300107020310100300c00174800c13122901301c1ca0102e4605a5980655400c01e852520500d031b0004840c020310341d4010341c124030781e8010f0840340f1084807040d15000c00340c000385205600003000031a40030010a0000f000d62214141200c0021040d1a82c7c81100a4440f0f6400c101d0b11100d0110b2149007000e0400c04405448420349811050540744031501c3e190070710701240b070081c0154465400924246000500c4c245a010250070001c0502c000c00c802100c072001e0285a0001d0b00500055601c20000b150000348a40d004114500c00b519007000d003d600c0e0f039035a0340c2c0c00700c07140d00c01c1c2d4a0344000b145210010340b0010040b9101490318000080c0e40003d5128181c03204014800c072803164200310411002d05009001000a0042d20a0882d998070b1915601400070410901e9102c00c81c4180300021a409014080742e502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 312827284 1250 312826034 312826043
    0x1207170106121104030c0806091513021c050d030203060109060c051c17010803070209090c01020607350403140307050409110715050f0a060f03080c010e030c0f0105010b0403 76
    0xe0b241d070003040340300546500811103455a0040000101081c0c19100c807602401e10000030b040c490030201043c2d8546442c1d5445030799014071020078042040c1c00c5015a881c07199040d1840411145025504100c0d80b404c030601a00318050f854a0300e102640c10707401580704141c26210040342030b803074241c03c4414500c01c9000a0490303000105880780d840720080440e0b10048a441c168210747c801070042c08801a0aa000c40440c0e40b001c141d040452400301d402c16400007000004081c19008040001d55034a00a880103040c00490001001c0701c20120034000452030305401c0102c80007442000c110803e403c2104c06800242c074030b11344d403580d010f6034030100c9000e5009a5506400d050030032504200070205080c0d5129114810048000094035881101410f0300000b0320000b0140360012555801b0200181034210a52401c84140404810018007400343c070b402c050015228100c101d08580100b4420088041511001c6100060030000182680d40c10110000912099a0b554409070060145010040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 312828534 1250 312827284 312827297
    0x411010f14030f090102040f0e040b0a11070b060402090301060321050f03010608150901030f0317013507150201061a1b071a04090b06030402100c0c08031207170106 72
    0x501d40b1071078441c07068210404c480010318096950480c00510150b039803006031004c1d075110070401072240075503005074031000300c120900c40070324a607400e6241481907820042070b800c0301d1008a50a52140d0341600c1030688068005c101ca0f540700d0601d600d032985a00d1130030341c0c03807503980001101461052041e24041043d19100b0380c1142d00700202607540e00c1000f400c0840700b902c915050100b03955200c401e0340c02180142250b44100059090062a07480c001200c5007000d44e01100400c010f4514000c2c20089041c5101a440c8150385020b684200881d4030f6401c0300b1b944119000480c0680400c41401d0614503150020885165104620710003003080380d6006104400900030a02c0040c03003000c4102d0754002075000c0d1441e298a92400301e00b01031a0380c00d00d030f880000104080c0030301100d80c4601c00c2c3c022003c58205003185001d5001400034170340710180c40c04002c0741c10304107810400301c81d81e000c0280102c58191380d00d86400e030141062042045900200154990b01300880e0581104a40341c10703102c2550390351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 312829784 1250 312828534 312828541
    0x2010903030818150105010e0a050901050d11090901020406020f0a030906111f0605010906020708070b0c0a0c0e0a1d101505060408031308070608060f010c0602030411010f1403 77
    0x50b144514020050f98100d01d08030520828100203100041d41c001c00d000303440314107505250005220745100150309000300610366092006580d1081614111482204c0317001603848a440c10a580f8144240c0d41e80d00b03d6040d8060000c1100b042d00a002611b00a46c203d074515045c07443c1c10390360b8850f01c0c403010b1701048500d1801d1080354401c082c1822000410703401c58048181c1b00500c90001c5202110311545942c5d110014407071507900c035504100800300703031008060344d604069200d91560040d10541c14007540c00540060030784001d01015030f5460b0820110402c06555555440682508403080c0001c146006586855038050303030030348500c10f0505002455001040c41030003004109030b1500d180680d000d840001280c1d5a428000c1028004c2d0300301440e22444285c8507043c0818007a008a0a00c7d0040c600a00140f68090045540710004507440741d0054031800c0180e0380d0884a8030080c1c41c0314000002c1000344075040c800710b00c0c0041c1c00c1c1e0b075804804000010850b1140850850461140c6040020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 312831034 1250 312829784 312829787
    0x150a11070f030f0c02030610052110090c03080f040e01170309122508012d0b04020d050c0c0f031c150b04080610090b0609011107050a120b130201090303 67
    0x10f21160300314200003a901c0c1c10340d00017a2074000102e40c03030041005524028421424007050802e0051840d4550702060a101c3c502140c0740e4810005402070650390740744100030b020300825a40d006541000e54540d1b910500043d1011a80c400e015a810360030041b0000150742c0c0d10800303e028001e65001c09142000059810403810319020100a90a0b1241103450201107803000703034072511854010518180b003450112100d0a40c0c24801030444010707400b01c050700c16060205c01040c003881e050780c000508202031000050090141c5c8400300c0150745854104105078842c0c20050008645070f1003110a174070003d00203240e891041c41807180704036200c003190088405140c4c00c51000080241d11609c0004c0d16107800c000d083d00594025030803540a10207100b141c850f00040348010700100c0b2410301c945004000802c84a1203900600ca04200e0903120b12104903100f40301c950050840144035019207076403a15a02c80c103520100c41601c915010b14007140c081b01103152280c00ca168103848217082c1d607103507840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 312832284 1250 312831034 312831047
    0x80307150f0e0f07050f03070303020703020105070f050d050301092f18030a110a0806060a12110405160201230a090807080310090606050c21040305150a11070f03 71
    0x86607092610b4141d01200c8080500040144900410003840814501020001d4440100003c1c41c082e802c04001480813950104e8917900f66034081c03d1181d1f443c0c805240140003500d413804090060300410071213403082c9a10500460403964401d506020b00b04221082c10940e0240064080701044081d00d144100d40106024100e006d441ea403824205806640210f801c6c40712540048030000340030300d032400851420a8034240074041c600010091440e02001150005515000d124003030310050042ca8108021608250b00014016100303200038240500e880d000d0906460030702000d9401c10854048110f0a0100f02c0b5803080c0301980b140f9035803a810303261001007040740c40c2503418480401c08500480c107200d00440c001c41c080c80c0b048103210b02e00084603040306d515030886000c0050070080380d4070507800080c2c04940d40c03d2150201d10b058485003d0340800d846030360b10007051801040b120700b07014050f03030041a204042054041c00103420034103040ca42803080d80d40040070040160710184c08203100d40e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 312833534 1250 312832284 312832301
    0x6040e0109080315040608120a2109030216060f0e0d080906041206061a1206040b0a12110907021510090906050a0f0c0504051e1503010e0108030715 65
    0x780040c0c251100402ca038022107615083c01403446180500d414540b04030001401e111018102405400b5003000c894420ba428603410000400504407172040d40199914400780407100810165a581c507002e9129401c1002902c00300000e0440010450f008a180b03d0402c00903594001450b01c12310308010824440c9142510000403e203e03c81031f0383c845c1d4000f0005052003004492000900e407810038251340c0c298002485400003540900d41601c3c922003a0341c0c00c0002210303040a030356240d40110f8024000038101a5005a44100c0015900e2071700d03058084450098500450601c060010303c001d0013800d44400006034089100d08041503054207181d82c000000c8a40e03200c0e110b980700c00c020299611401c054503425078032030504c01c0490261144038640700400d41c1c184100f501d00b51003e0901d02840c0314840c01025400c507061241a25450070103500a00102001101c00100c6020440380e0070900030a0300c250030500000c1900350303001060300c061940c0250340d032854a460454950150807a81d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 312834784 1250 312833534 312833561
    0x2160b041403190818031204062901032409020909010e0402012705061908100b030a0c030e060c0301030308181c02190303020c010f0b0a03030509060f040602060601080601020f060604 80
    0x80d4505804021b00c0100303105403644000030400d06141c00d0a8040300e0501c0d0000e454918021160301c1805840c03110368603e102d0074240014078901e2580942c480014100c1454000c03c1001070104840540c0d03400380c9070b4480280d542540581e01c809030303603640c5072054401901040b00c070340486450b1030f0b44140105800e1004d4200854055640f80465042e8115400074074203a1720b032441ea43c401c1c50748030702c455034490307114541e40c64424541000f031005448041c0410b401191120003140d00540250031900d8032040c03036811a5500d10b04880041100c4d0828081280041c0d081c00124881041301c180d40e80f0000641c40180400c5244002c4104201d5600540001075000700140485030190035110401394034000c0d100542d4444808000508450450a0501d55a8a002107008098030340b0b00500055a5060410503a26882c10001a0712030040012920484600040110b040741d40440c0340c0b0700a44007a2a400703240c2e2511001a41c40710461611408154000300000b0001d1030990820312510340d02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 312836034 1250 312834784 312834811
    0x408030f0907030c030302031902161a040f0e01080f06090303070507021503040f050111070c03020402090d080708043f020a08030c0c0a0506070213020a0302160b0414031908 76
    0x884da0340032540c020503071050380540c00200e0703c0090350141c40c0e40d0142c6d603041c85c40a48003c09507621414240e400e9030140d010740c2280c920040002880e03000884000d07080d194820700c900769513100700e034589201c24018216180652442042050340000e07902d402900320b83c01a40c00d40e5183e02c01212190000841a070380401c504086c3c0d0a415a541c0085014902903425101e10800d2410001d003921451151100c98034030410800020034038110001050742d41c11580942d440c444640041d101101c000c9000d0000031000854904000c0c1c030344001d0044074034841c00e0a4a85a080241c0101c2000b00c2c0701c1500c100c1082e1080304440c055000c1c00007007040c070003030115a5103a1a801c9032441c5400001442742a6071042c000e00100b031400700c484a00500f0116509480c128581d404510710001c4030f1855103c8a402003010408503000342c040d40c10480340c000b10003000281608106a10480581d400c0d40d00c600c2c058008040d205000c03085070848009400d500416010241049800740401400a03601c08036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 312837284 1250 312836034 312836039
    0x10816111204030506040b1807051215160e0105030402060d150b0a03020a090807030203120d09151a15031302010c020a08060105030d020102031509151002010617060408030f0907 78
    0x20401c0900081c40c003a100604051420349044000c000018040280010701c0c000484c1e01141c0c00650a01a500b046c5d0340d1020302d07036035424200d00c1d00315110301042c4611080f03004c010006140d0700c1c07a0010360460b0740e00e0110040204c070055800b40f2080d58041c2d0084000c0002c8030340312255810802a82500da140b5040442d59010a0100307074011001c0240080d4001504520f981d90200c001c802405440024000c03179403071640000c0d40e5259441550114181c0455a4290381c40603621a07130100f0741115502c641e92001c181c201c0c008107040d0088010f40c0d181c40700100307003a04000000359415062904500d28503210b441400924001c4010201c1c1005011540d00d00180c440015420080c059030b40100311550515007050708015142ca260702c1103a2040c400c1041c0c030311000120300040030050b143e00300da0b0303258090b0440381082815080342d00040b1005142000582c1540f09100f19001e01d40143c4d150200000002d8039281c044e58041c1071450706002041003503514601042d00003e010b411a0764055 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 312838534 1250 312837284 312837313
    0xc032e02220315060b0906121f030503030a0c020a050d0302180d05010c03180b010603090213140a0e03090604051512280509190c08010216020f01081611 67
    0x70306034100325075142000200a0003184a801400e014003613090225003084420720200c0d105001d0400180d00d0001e200010940700307200e036181c0d17480000c1c480c400146920384a003441962640251940f003c1a0710300b03c40c010640b803011811701025984080686a400840941100603401180c42c094141066a121024030307a29400124034041c450000800c6101108001500b110420803c00107985030944650313001411070212181580c015040c0050282e050b800810000031807101c07581c2c600c07403501485030141d0003000040d510505903030381c090103100c0e00e0102d03e80c1c4074003901e40c1e1190060010722080c00140342c4450529a00048a104e644c181102c2010b426400380b0107031503151f400c2c80000b500000510082c0c00309019000c510354140300c3da00b0a5107000741d131142c141c1c4500c034442408400303a20402000312001c40c01800c3c010300030343d2038a6454620400d10a500b01c0101e00ca000c1e0512150500d501070b1001601c214005451420407060001c8280c0d04030f0303607043c01c40c001c600440e509400c110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 312839784 1250 312838534 312838597
    0x70609050313062001020913090f17130f1a0d091e0c09090f0209062206260d050a050c030a2a02031c0e030f0c032e02 52
    0x7450207940f660300c2009105083c0c144c580e40502801844d90041200041540700d82c20342400c11805580006095682e908044440000c01e1500030310707544145000c061011180b0000c0c00202809807005404290b9881e00000300104601c40c140c2c40e80081d40c000161200c0720005882c100e4094817001c01e20340025514810802c601040d8403400700219011b14007841a040c103420003134200c04104000c2071490351192214000820750003842040903a000070100d845801e5500d07124004801c00165071014a0700c03050180c0305078080c00a90075035000060000095010070980340500c080060700402ea41a20700b21000c0c0e106580304814450200840c0f250a4020401410200c45035680c040c2c0d8030250310049214890381b5900c1503014800c0c0c110301c0004d603402007103402100d041c111405124022001e400d03218030b8205908142d2600aa925000000602040100780c20900710140e0740000080d05014400e0401300700c2c498039520883c000c0300054021640201403031140c813039890713400007600480712400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 312841034 1250 312839784 312839789
    0x30201140403090305060a060b07080a030902120d0e040b060714070e0a0b0a0b0703090e1008010203090109020f0303030403090312050c010e010c1806120b0a050a090203151005070609050313 83
    0x703843c0320380420a021003070141c1c1b0b4001e01c2501c028840c0d00d10300107a1885901400402510600300080c105124501035801002140e50103001955181d4401c200310752150740c01e2080b00017040d0060144000361900e4030a0700d00803000101820300340b104507240c04554270024030040c0301c41d00c901c100201c0c070001d086240c14490303240741c8c42c04100c0720503040034006e002405610101001c0300038070105e00040e421075080d00503507140540c0c90355107646503c29810f10019561001c080d03540b001050010310312042d0850303250f050099801c01d203480700e0401490340e6807004890250000b0071340182403000901131b02e0702503246645443c1003810540c40300505401c480c030035806c4ea91180c0d074030205d40f5009908800031011100000c6400a0800c1c80c052000c6d003140707421058040415a1440e001025582e15580302c00039080c060427041a00383c643c0c4252000358400d843c1c0310b40b40300304501c0070107030392030106d14112903050250340700340c00d0078007640d905005003244c000b00302c80501060149071844005150f80100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 312842284 1250 312841034 312841037
    0x30608060c0a031b0203070b060f121c091a0f090405090d0206060a141201020f07080a091a0f0702040e190c090204050a12140105070e0f090103051207030201140403 72
    0xb03661101180142c100c6900011003130040d00c0c2c24443d518042e13004800d59190f6600b10f10944890340c1c0303c00001d00034800070766005038006841100448103000015024010301001d613401d0960186040c0300b030b2030f0513919100b44ac4c07090110040882c821a0454060001c0d0244004841e04082d07800c40000e094400c22589260aa8800c46c200e01400b541009a26004107041e10700010290406408d01849500074a049000c5d1101c080c001d024018254110361031000c0d0040341c40d850f1903045c5494170042e40803240b280000781540300b010075005801d070464666078005c800700034a0100b11662100b51600840400d81c1d0080d41d400c0c0c06480d449090010210b010311132041d1040c4038229140c0008550116080718881c1441804244500c1e103440508009980f00195801079100b144d1a000882034403058901d2483e5091105002089401030030f405030010701100d600c84004020000e010900d2801d1001608175440340e0300440705900404004c00205000384000304440708035084042c0c7c41d081c1035030202e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 312843534 1250 312842284 312842287
    0xf0b07060944030105040b030f0a080c10110904050a09170904150e0c0c030f04062006040b010308030606210402030120030105040c0e040c020708010f1104030b07030608060c 76
    0x105207000c444440c0380c000d444580307258040400303040e56a43c04140a00b90203640d0b11003801c2c555a400300b04000c1c8041d03064007101c22115580c54210002e401001004003e4894000c1001f41c0107028000c03c6c040b400c0c400c0c01613080500c074404210142074050b00c2040b41381d0707a91a20300081014001d44134110996045003d585610b55002c3c80100c036569042ca510b0b04041746424030524004484454000c250300c0780240d12160b042c0429810b52003072070002c00f1540f00002e000900a90000803c811801448901c10081c025807003200e9150542141c0c02421521020010300000e0407034800345070440700192125040600080014003800c000404400217001701a04110031858240541d040c00c1188500084d00034209a6400f4070702e02045c0a010b20030b949900d2015840c0340300e03042c54070602c0d0000f44144120703488424082d485890a0086000550a184200550b140740c2e00070030700078040ca002a2450985982c968888140003c0e040104260700c442000840240800c60b2038020041403820b103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 312844784 1250 312843534 312843593
    0x30920010f090308030402060a14070501060807350c0a03031d0616060506040f1406030111030601020a0f02060f070b0108010509190b04051f020a09050402040f0b070609 74
    0x5030118141c80400420404840c006200040004054030f42040e41034507000d403201d64000c4155030300d06018451504440000c24880103210341500041c5c204e401e11400d44d00c206031561000c61000700c2003005080008459150040803c41480003880d40131400310a4413940524040060722140c402da0054001800c04036440c0d211442c85000001c1e400b008840b0a841c141d000b05007022414014900608101c0da1500001d00e1600c4541200e840d05010f00020020405500c0b0151a80d603801d032605030180d840c2602011444549000b00c0b030050805030001c020854007030b6209085444c400701c08a03000030041c049810102381103c00361031601e2081405122a40c1095202804c40304001c14030340721a88181c0750030190422070b00d01d50000b02e230000075504030380d038440c103006280c000403040a600c030b0820b603070216a00100550151808580315620100004d80d00c80410082e40242d0080054060701030001300010400440240b080c3e61184101061fa0b00350340c6c4849250b80f00c110344440700c0703441d0b05000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 312846034 1250 312844784 312844787
    0xf03070b0c07170f0712060902040f0e2a19090f05061212030c0d02070b04030e0f010809032b050a0207060605030d0c021c02030609030a0306050109030803041203092001 74
    0x40840b41009030013803804005405801d42e60b40218031591800f6551100800240a515001805410340280c824054161484d00f518020f100d000003d403198015110b10101c1d90304152030504000b18009407031402c80a65404002140200443c484100c090f401c100280d100c0d0300d8000c101004025a50000c1c9915001e0140030204c1841420a22180c0001c070303420784400507100540303420019107901591100070080c0088000d00c503110300904034100100c2040105a400102e080231120161981d081080700c420046d030700c9150a071410852034206010301d80b102070a440450b4400030107000c10000103401044d80408a40007550300f052401d400141e00e106101c11070140c180100001c0c0c008000031200315070010b25140321280000d10030400c100d0610011080f071800c181d2860703001001e40f101800d1140c407031507580d400311001300d0101e400c14800140e55030003030310031404582c0c02640c80c0d89540c0c0c0d80c1c1d44140c0058020b480c01418540e03180c58040100d0300500500941000c850040b0004d599030100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 312847284 1250 312846034 312846059
    0xf0a03081018050c0d0e060118020406080406020307170106080618010605030a0e071802031503010920181303090e06150304060f050f0a290f03070b0c07 67
    0x40c0100d402003030388100040b00350010214208609040001070980701c44070003881d14070903000c544005c5805c040310002078400c04250035040304c002040030719445400003a210281d00462199502142c040386c002800719449400441d800304052a01400700213101182d580c0d925000e0300000c4c00651071004010301401d2100c02c084841c83d030244450b680750b1400100070f182d44130092001c2c100a8545103040071058040101c03d001d0580310441603025544801c00000139002200c40180014080400d900d4a08061003441d200350307009000408190025128160300b014014000c0e500001a210605603903030300e90001c2c43c0a40403a0b07650401030320131410001c000c284103801001e10f000e800c4040c46040c1d55605441650310b98950400b6440c4e82e1903040c0f84000308001050754242c02e08010810201c0c9a00c03e16551044d52882c01c100803407914003a824a40b0410101d04130f0841032110740d942c0151412904140c0341c8100141200c0c815606d503648600750360400600155298401101030008094244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 312848534 1250 312847284 312847291
    0x209120f0f01090f02010f030603120309020301060515040b0c0304030b011203030b040c09180e0d030603140313090f1806050109060b030c0a03020c0f1501090c05160308070c050f0a0308 81
    0x8020f22407400c05440d0030356010380c1103000034140308403401001c0b000c0340207400c180000d54012522100203030071044058050b18003500100e00c80c3d440c140001c0303498900650a400c02280741250b0904260034110f01c006550f00c5200c0c2940540f0050100200180b016040719010745003043d1a440407900310314000d0181c81e007002241c1e100300d052405110035070394021252001c5400422611000c41c9400d0a144010710802a9822046c060048800086074054012130102ca04c20f400360300307100d194101c00d140c40b405603c994208055a1350420043d0b032440307800c03440c0004105140000e84103005d480c2c0c01c951508040c0115507190f2a0001002030080070304c9804001d01200444600c0d624001098049900c41c2041c91001d00d60b020504a203d0a420410914111006800c5902c2e401d580041041c01c80c50034410159a282404041007580c2c1c440c070140d0b002140d416961103450030107564180d606140007070403581049401c02c850700110320108010f4841c650010701800e02501c55050003010140e008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 312849784 1250 312848534 312848563
    0x40f0902090402060a05220e092802040605030105041a010b092b05030c0a170403030e0d03020c1e0a1703030f090a080c030a09150e040f0209120f 64
    0x844100258a52280da55440360b41242e407550380d900003907803e07102c90144d41003506022843c0400c0103d401102c02918003070b034a0b06a94044a0f6460740740b9941e42b0000b104a8503104a071030503d01030403041340e40004800d24070042c8003103030250310341e000f00b0b0864030300300c0d0706a648020200000c1e8540c0e184200b91800341006400d0756160522483c0840d120001c03c4001c01e06846d401d0b60b104500b4001e140e03a06002c990701ca425207594118440582d03646d400603940541e9410982e007802540c003e0400e00320380440e076250702c562080d220041e0401004803003644c1e0980950144003001c59165403445150007640c0540e182d17113440c0041c44400c0c440e0300107035a0400c29030800d2480441ca1203820000170790780d00003840718161090741d403480c90b0241001c0c076101004040f8030004c100c0c88910040400603003002492070b41c6030b09400344c1e50f240081044003002142e01c0460050001c0681e40d04183e003010344034103100c900261520040f0320118088010b508891040c6070011491800040001e000100d00d40703015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 312851034 1250 312849784 312849791
    0x90f0105031512031624181b08010e01020706060e0709150e21011a0604060e0a0302130209010906110309060901170a05060a0602070e0f10030606080a02040f 69
    0x101105951208a62a909100c2c001c0e1000e00303c40410b08004681c8036056070b2807000000901c2e880c0c12540640724200c510055102000314510a01040c4030b04006010140c0492141241c0ca440303605c07c3d1f01e070107020155605030385c15000c41d1094003400744020b240e948000050ba6001c0c0b504006003140c120740c00403480d8848210501c02a15401352107042030340c03031101044c0016494500c064400c0c0c02c90451441d01b00c04012407080b0a10f01030000b407820f1040c994000e00100340349040003c01180401085680301c402130005200340c902c50801d400150302c5c0a4807002400d516500001d400206624819003000e030001645030041d644103840200401c454104205030654800b1034644a0281c503414500520340850396101c6684241d01c00a010381034141003501904001c84240050042100c0041c01b0791441240010301501c001110340071a03843e04132911580d201c003401410401406400011441c001342d20120114201c1c0c450307a0002d14404006000c0c0362041d02c14002a201a6800740421a14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 312852284 1250 312851034 312851041
    0x6020304082e06060804121b141e030309010b030708030405060702150d060305070b0c072310020708060717040b0a02040f0e0103020f04020c1b04110a05090f010503 72
    0x18001042d00301c6180d42c01102140c08a4800b502c0c02d02078a024000c44103a04100000642507084a22a409180540910460309220040940d40500803119040f070341080080c00314042008494a840804a20420b4903c0446403c1009168980241210344560000000d001e0300144c2403058101100060380508403280c9401c140030f0710b900076442103070b020300c600142c0402107640d108603d0340c041e801c0340c041036121580680a14028841800116002d1062190210303c115148054540450900c0c2c01040030f141400d224402d01400c0c83c0c2402e01c401e1034042c4c040501d07903903240d20784150082a8001c1000c1d5180c81e441a140801c09001c0d142071204984a24904000c0307442070550040c0c00028110007505e441a202c0000d101d142e001084a010110001c251184080c1b1954102e0303000702c0c1d8401200198108100803803003903201002296000120030084605468003240d00450020400115225180c4e84a1102d500070085000080e40002e6121200c0c5000340c1c241c142580e0030b18180b415481d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 312853534 1250 312852284 312852299
    0x310090605010918061a0d06050103020405060702040b12031c05010e040209011e150203070314040e1311091005030d0f0203090d050309190515030412121503050c0a06020304 76
    0x2e01500a1a1604070a01d228003080745403900910700070700c046c002050800c040c00907010a01e81010743c2d90f000c0c060030401c00180540c828001da400765500140390510b4407046508000082c80071011050b00070000007055882d000080c800b6144032030035405000b0190020b40d0a15040300c805030400701100140009010150701d460f2151230660780d41010700c0a4140a1500680d41140c51380c1c44550310f0544420b24500c603540c080050005144280c0f1066548120103540e59024081d9001c1c040e5910381141c00a038041141d202c2d600c2d031560141501b200c4040d80480461401c14080b00c5401d42c0085800e01000b0b030382010850701c1901052807508940b000c10182c002900c0f4840c03544000d201e80c40101100042c86014001ca80d04030000030019680000c40160381c3d2014482031040038802d0b89001901d066031040d003000c40b84103e41c40b031460b13140100703811419070712030030403500c1e0358062641c03000444110f08806080d800954041e8008002c3c82e89004104200b0716a190000c20442d08140010055803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 312854784 1250 312853534 312853547
    0x60906020d030203071b03030e010b0906131e1b110604120f0912060b0108010609121b030623060609012a0b070305061f0503041416060302031009060501 67
    0x1c1c0585809a52602d52210849030705039070a0710501800c160f004914100b5404d503100d141c104805400038803688210b0000c1101e01c00b0103c416a0700200d0501c001041503855601c082d407980c20341c80707029400d0010071802004444800d40700e82510002c41220320b0b00241c0095040d8004030240300200703204d03c1c0c00d65450451840103600e01701844070f140c1100500c0350003410402d0140030740700c1c0b0304008007070a42040e00107411884181c1c1c0c04150b9280020a54500c00c5544405880a070409d0718150300655581c444510704102442d059039034001f0010001401900a4510614003c041081c3e01c541c800714a10150402034002807050101700900d118698006038075003403d0000020040b250304030188004640e0140036401000d18124034100003083c0e4044d400300d030141c8002d884140320030910144041c4c034070255240c0394010030414800140024a074040900c8615151001c2e00c845004c0548000b1000300e4a4000501090b0003000300803003032048003640b4004010000d03003441030710310304030001c1c111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 312856034 1250 312854784 312854803
    0x714090103020121020d14010e060d12050a0507060e0f0d0e030c040915141b12011206090b010b0403030809010510230d030e03010c0314060d140109060501080706090602 74
    0x4004d0f404005250803240c950548003005010b80f401c0c05001010b01c2401e080440074002d000d000250700020620718241496410300e143d07800420403220801d400400d032100c0d041260008200613080020300b0000c4e4050281d0360175012744600610111094528107400c200071000301300d00700030314822142c15a50300003903140d0b0801c0c41501e0014020101c0d0078201513404545080014031342c10619600260307403816a500e8441c0f010f408081c030000c201c01103a50001c0c0700c0c840313800d600c0d80364040061004041c1c0d0190304001034420080001c0c80c03482070395a44a44e2009a05c01101004085020801e068200004c55445000000208110f19103606804802045409002c1c1c011030700240d0300c0c0ca804400440e501e101d2000520383c580f00d400d503113030090001c035841591360b010b9403c0100c24007625000340a14024440c01e0b030300d040c100341e50380000c1c0050104038203010745400143d031880940c5024280300b1002e00c5409110302050540c1050300c1149042c00710b030f01034000c0100d2180100b082036130100382c1c0700b627 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 312857284 1250 312856034 312856067
    0xf0b0102100b0102030d05010816120c0603050c070506041511090a06180807090b1c030c2604080c010f080f04150209040525020109020f1314040507140901030201 71
    0x42c00c12010700101d10318010402d160044d039240c1400030800040c0000c16a80d00c03000c1c548826121901d0355280101c103541768030005e00c1d0307048501051240c14002d4210aa000c415a90301d030741410082e4880c145001002e603415180044e004030380c12446503050140440000c2c070000c46a03c1c00c1084d4000c0b940c01110b502c41c61082100507031902c81c1142940182c01c0c01040003a088814958403040b010000f8a00e480005110f0041606181171019401c0301440140f50503403209414401c242c1c40300440301c80c00320074103402c0c0100c0500e8940000d007008050301c05040c0e0312008040c9591400000b505040300a0b64803020320060200300041c04100e0402031380d20580c030020b4040308180140c2094083e00400084640c480d040204000365052481d003001a0002642c1c01182c55036401c0005900300c50307881d200650000740c00c2c1d41c0c40b401410010b060241c008a070005c001020b0005684040c4a4030f002e442c100c802c0d4201da1010860070510040800d000e000441e0744100c6545994006454405035101020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 312858534 1250 312857284 312857291
    0x60712080622020f09030307152d1a0310090507080610060509030a0c0b180a0b0f03090c040603080307031112010501030c270e0a090305090d2a0602010f0b010210 71
    0x5008404d904195603c40201070100c1c1d44a0219142880c01c480b041484144503921b031600300040300080c00c61240100d0507000306420890764202e02c001c00342c0b46448141414100050003c05203032000c004040c1030046582000501c03401c9450400c0c286460340c0e002c1000b5074480c41c14090300034400f02d1240111071185c14484e944401d8040401c1c101800d080c4058000d01081c01c0024070740a800b0007c0c001c50010500071b449124140040000c00001802040b201503010f04c005001040b044000316000601b0341c080383c5a907142c401c0050240c41150300300300c601724000b000b07100d01c840c0c140c05034500010100100509151120f100100060030501c6654101601c0d00d0030021079a0040c001004850040144a205047d248140ca1030400f03039840740307103680c6951000199a841c41445440c11295065075001d14041d425020084018a142c0741a9141c0d080f210f17900a07145000344424107610101e1214212591030980c0107421255200ca003040c0030b90914681e211540e0740400c54911480c40e054000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 312859784 1250 312858534 312858547
    0xd0c17060f011b0606063b0f010903020402070807031e0c0f031224050603060a090509120a0f030f0e0d11070e0103110a06090e01090b010e06071208062202 68
    0x4940040e01e80001406140c45c09001203503003a03006196003242c3d081180e0208680c441c2c85882d56a00e85e40744420000700381809150045880d0503c49900286c405140c010384050301c031740014040340c0c0410801c907050070000481c0c00426800c64054040c0742c040a43d524403500c0304801c05080784002c40300043c510300700b60800104240c010b521001080f0300210b410480c00004045641e4081c0c903e0407030005280c4400c03000202132615504891080350050084c10245103000d6050340a0140640b0303002460150310042808804500050b051164803951668486c24252002030201c0742c031049c01398078107400c0000c216078180000420240c170300070514040c9080640390800b541482c140360007040a4847c1200000305201c51001e94090f00c0800312250a40550356803400d85018010303115042e102034080c801000400d03840d038080c4000300ba0605010304010360150000b02694001c1d00300302c90041c0d080400c1d6410039444160145d20060076110b4900c000341204045400038802c441c0c4039030858000801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 312861034 1250 312859784 312859817
    0xf0c2c0d0614040c030311034906031e0201020a150609090c0801060f061b1a0c2a0c090603010e0601061e0504031a06010c080d0c17060f01 61
    0x80c9084848002d104024103003450941d920040900c001da00186c80c681605ca803041c404403c84007400c8402018440b4441c0aa5100e5074014503800100701407111036944140c0103041c9500708540d5003519400080310350562070099002d0740c140005140a0302c03420420030040c1d03000501005210b4200f05043d82e82d1401d00c2c04000501400e070051480c040c14810200d0411140c3c0c0d49040640301c1120003440040d0b1600541d402c9842c0030300c03071040080c100071103034269454103059034040c0b940942c0c80242200700903002000013200a586d001441034000a14603103000c2c005070f010041200c1d40d00300703d0480c03060b000443d40d1044000b41080c030404039280412a10360b002d6201041c96110001a40c020750707951140501144042a540b60604000c0210301d91f000340b0582c105c600f52944100e041108208410402c1e449071401000c1034148004003031801d0104038070501030018403000c0d03000407404088110300106000c440c440c00c0a01d4003501000d1000030754480119000324035081c41c6c11095040222078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 312862284 1250 312861034 312861041
    0x30510050307090b01031404030c02090901060b030117010b01030603111e0901080102030708070e011b060b030f0c0114070c211704030303050105010f08042003010f0c2c0d06 76
    0x4001d506104107900003501c441c40c3d4001141441c03003602c0c20812140003109101d482041207034010300182003d0150b00041c0360a042c01c45e04000c0210000400036226880e001080d4400c1c0c0090318103000e40400120001d41c04d000b9036402e46428602030004500c1c60b83d0704020414050591071049601c070103241d5180c5001461406641d00c01801215556594050131703000b50301c00e485103030004060740005800140280c440404842040e0b44881c045040c01d600305d02c01c002050000c850250711901d549000783d4080140c51060307d542d00c094a8490b41e00000036080058a240c202c483c1507041c0006804107140000070411511914440d0101040203402d90f071412101d01d50082184a1114808400d8010b503406402901d00c0307038400f0006030743c072040196008403001814100281c02c0320300040005001c0c8910a000c0e0392400f18011010a420000900791007000e40c2002050342e41d8803140030400e500c000c1031004070801c0d442d11403c000928602902004862a1483c010100d2500704010802e5950 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 312863534 1250 312862284 312862289
    0x70b0d0905060f0406060f03050c13020d15050406060e011b02060702030a0b01050a050405040b07120608191b0305072102090a050703051f061404050301022b0219030510 74
    0x10b8038040d250888244001080581e021784941d49440004100110804032260580350014000e1950289003030400c0410150b550713074181d01680900294043c814180140c8444242143c01740306903c0c1414280001c80f12554404810000d45141902141c1d0300411803000610a1281d082c2ca01115400421034511038035400a425210300980708040c003042c0805103060302c108a07010502240c1d0360f000c1105498003038502801001f49140401e071039502443e040582680004004100160344100e0b05042960b500070501c2c10440b1606130384200300d05a50840e1100d4240051003005508603124155104124024a980d2100c0d50204200c3d6100c100364900c407681d4010401412890040c5c12440640015201000481e040102094034115440a41c441e03111b04c2d0307030144d4549460301d40d00710f43d0114032000b0b61001d48000c000c0400c5c01d44080c0001c10981414201011b0b1590001440703080000044803000419481801105c40c291100d42403116510124070327001c9240e4586101c40c0e441c3c10f2459 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 312864784 1250 312863534 312863543
    0x2031614120c03010314011a09060d081605071502060105010809010f050c070b0906150f13090609120509031c030e0a0c1d011203052208011a03030a02070b0d09 70
    0x81c800c01601003486001141600d11620040d840c400c48052100e007030b24001c048101e4818500e80b034824442c1444103866610450003000d9901021960716200300c0b42d44100c4e20648018140b00110060081c2004064020040310349140303101103a0107002904d9040c1806002d0410078044042024440250080b6604220800080140f800c114803805c00d41d0307104003421100c010040d4002445403c01280f030510440000c6000c00302c20881804202000806c5c04a441d40000ca4900d0092014040e20556050354469034001072601c2d110b0421079041c2d010b6203d0001089010084600030361804175220100800c00d080364058404849403e0740078008000e41c01e1014401e05001c103091100e00c0340d48100715809c104068001003801e61044100075000d00412002c043c0700f03000344000078070510003009400c041403954038240c990385051b800041c0035503110301201d03074480d20206100031000c0300e45a0068000c4000718a890702c0d010700030392520003070302c140e0b10210b401141061071101c90b41c2000c110a91710 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 312866034 1250 312864784 312864817
    0x6090604081c120c020d0f03020705100b0306010e160e040b090f0403120204081b0303040f0b0c060601051c0e1006031b080304051f05070812090c010302031614 70
    0x603500724280b6000b1160407001415a40c41c810482c5418030542d841440542e010b003152041028042e20714007800b540b8803040690800506004c80c60034400c94000440714107020991580c044c01b010300c0c000c3c040c0c015101580074030341841401200102400c11061709401c14042e0240300c0700001c1c000303000114106400c261070504000340134100481d41d910540c031a0b1030342c00b20742c11100d004030100c2c000d601504000c6e511110039141300c00700c000007081c02d014004088a26040d12260301c8103103550b495100c180714510204100085910038849107a00c15820301e0304904208641003032008500c500c000d000805a50b8442d0824008001d00c940302a4000d02541402155540e140400308802400c4100c040d00d022081c022a842d5404130852f011981d00515030000c503641004800501d0010702c58402c01c0c06410014200001d801c10083c08a82c407800103074140616241400909100c0d0b44800c0364105031041003001003104141d102c00d40011a03d00c0d00d80c0d589060386c807446460344652440050360780301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 312867284 1250 312866034 312866053
    0x30d08060a12121d03070e0406020d0e03270a0b13032306090715050c03040306110702090618070f050906040806010315110a1b02120c04180804050609060408 69
    0x8a15510100304400384d681d400e420441600c148280c1030010f500700307525801c426010000c4412031465140c2250150000615003214007141c4070440e50042d14001080d007000c2000c41d00c0ca4555031000c1a608520407440720742c45404400580d050f900c41c040d2000c5144082098008128030000a0b00034550042410150309003a9200d1750108000b8100641d4034810a00000c07101e6001041045c00c490240d01000303103644e2000000d8a80d43c20000800002c3c5c80240400000b18103640962420990007000303265440c600350040c88140c00004014602902c03200a240114206403800c0c03a602c10310b140340c2400c02040c0e6402c06c659910441e9100c0d540440d000c180420701c80c0c4049000c9040b0380c42200d06080605134241d480060f500b01112038000c4410901544181c540100c030310001140b80c02c4070f00c1030804c0b0141c1c001f642c0071601056089213680480081d40c0941418455600e407016011081e9488401d9656005202c4c40b803401130070302031a4040741181ca1074450138150381c05080c0c02400c0d07869541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 312868534 1250 312867284 312867293
    0x2101e110115150c050a0f0c14010809151b0d0606080601110c0405180102030702161d0402040902060405060f07110604061b150e03030a1a030d08060a12 67
    0x650400d440031565107800015440c80300a02420300860380311007104002d0002101c0e041d94803025588041c0c2e407034000c000e00c58001445003640044820311480041c1c40e41410301c00c20f006865200088641881209001d01c441074100013642d0190b00c12543c1300c085076954400104260045500911005c1d003000f0a0400791032035075170060380a03202140e440d01c8442ea1000d0046030086c50400c030103036481c4c011207030300321580c2400d4020710350000004030303907039004001480003038220782c01182c03004016000400684904c2c5c0740b401c00c4500500b00c401007005071010500f03c5849014020348002d09c50707070b81e0300c1c40030003151240c41c1598000d000041c80603444981e03040070051a40d210000440c1d44000600001d082848c000d02542e003683c0f8595070340c03041e80e0040c141407228040e03024419505ea1180201d01e00802e441c0d40150780440100c00d01640d1a400c120714000150303030581c980b0103940b0000048420650b14006a441c815400500d019401626a00701045010300d00ea000203400310303968030300c100502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 312869784 1250 312868534 312868547
    0x5090d050309120f060c03041e020d120c020306070918051f0303020f010f02070c030b04050a051b0f03030301140607030e060301090606080f010e0703020f1306020d0809070605030402101e 82
    0xc013022016242c0303035030b030b94051040c0d01c3c401140d0040c01403086428880c03071521444980d40d0158409486023010003429225107c101c41007201e2000041e0a1a40150843c1000d025083e0024458182a501142400c0c00703100b100000003001454250f07120b002034022010307448018260488402540c00094481c240251a000c2d02600240c1030340c00c0140480c3c0c0c00c0545d1084442e501c0d04500380c010343c64110341c0c601c0000300002c5e10a031402e1080090b200c000c83c00030700146084209580307451401154800c03d00c0b0b001e241001d102813003a0001d000412000300e1682d2045401e1004035071342036441d03c462038290b64405040314002d41181d804400428100100e070b0040c015541d00e51120034296880c00c554003c0b11100340240381c0880e03081408900703e903000c4e0b0054464444242515404c114295400c480000c00b142c3c0004010f901629240004a0300701c480300340c0110645000d480007905054000d0028170025000a0003031800c1010344ea1031301e02c00d500b100b580c07080d40700642c1d008640c05040202013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 312871034 1250 312869784 312869803
    0x9032004060f0623030402101101090b0a0203060102070b12040b07050f030411011202090f1504120506070305090d020c010503100305190c090603050705190e010b0a0e0d0305090d05030912 82
    0x1c036104d4003070000d0b0403100034040d0b038400d50b80244008146d00010301c08490354446090012225900c0d890090300089000c013025224509100c0011b07224980302d4002494402e5032340c03000300d03603d81c00c001032000c100c00d00c51040c3d070042e04082d0b0301800d525410021a074503c1049620002008040140820840c1030354122000040c260307101c0d01e5140781548130070100d2140c024050343c0242c000c040b0034540d0529803015081915980820f40c01c040d581c0d02661200c0b01c003010102c0790390f04040d00304180c030340e054803540d604003100100500d8400d0300398401030b58402003800c0c0700e81800700110006481216140401010b9075100040d15010440c035510400c8240d1190022118913080941c085450700702c5110f40c004a83d044401803503110710308010f10440d408030240c1c00d204921031300c0c3c02203402c1c4d90b00044680200545d0726080c0d81c442c40c8041c014258500c8083c40d034495600c0c5038903880420f502c40f00b61841d42c00c0c21907180700c441e021031406620b10701c03078883c1036074101101c0c80800010090100e80b02c0503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 312872284 1250 312871034 312871067
    0x60d050c10020c0910061d0a1508040b0f090601030609080d060e070f1805040e0a080f03042001050a0516120f0914030303070f09080604080403060c09032004060f06 72
    0x426164000114940384107400750000287c10704c0310304039048500c404180420080602840120741c2c171001e00300114520a1050004174035840709000c100101070000c2a4845140d240d032030b00c1401c102001a448902c180f0000e061540c540130301d06e060000000840d4400c5442440412215648000d00c3c450031301c089484402040600e007061104501800d00c081d650402201c0f8044140d013800c00f003000800540340d403011107105d10300180c00022203400c01007200070000fa0f8803035201d02d041c0c60407540840b0214140c40a21041040c4500566003200544401b03550341c1c01d18507180c941c5001d12842541c401174001d1300741a89140740e1040d85821080784013100460b652000200e0b6201d44801c22124204003580760980d0040000404051040b50011310304132062600d090507075950507405183c600d082e5016541001c0008040080100da40b103031424800840c14201c0c1042d00c3c6484000e40000c40240c100d0305002c0d80103d0b1101d0f0358881c0d10800c041e1240c4200880364940743c0c80024400c0e96007208000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 312873534 1250 312872284 312872299
    0x507050c1f0206160203030714091003020c160b030114120715031109240c070603051806042303070812150a08120a03020f03090c27060d050c10020c 65
    0x24004c0b004007048820400c100e40045166446d0104121f03603108190454400f005002c0c0320461040e504c034010792002c140d880d0382c0940c648084020b6941040c210000d00d4071850405513081009401d44000e80b41116401c0d0020301c14140fa002c04515001c0892455509900624034040b840401c4240c0c104610a0540c0e0b0800030f450501c4a002e403148a4496080c0d44581000d410302c071058001d4840200051409001320f0400d02d03400c48261400e5000e400030008207403640104550303065146c02610340c82200d540141030a0915032604005c401d0141e5071ba60129403124080b15440800f0400c4440c5154850556a501c0801070320300d1110f0a0103845255441070b856202040d58503041050005461824020701480a2200c0c40e20015070701514080091540074040c8050410000d40507520420030301019000d81002c000420556601261300761101282c4030510708002d204200009600240a441169911b41c90f41400c41c0303411240c00d410350f031149845210b25451079021aa403a01c0e1700050300d144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 312874784 1250 312873534 312873541
    0xc040b070b0109150812030403050c0a060632010e041104030b0609010504020702011b060f0507080601140c2107020303040b180102030702060d090317011d1311010507050c1f0206 78
    0x2840c1341c0b0301c07500c03403401d0503404011550480c0c6900307401035810501c64181b007131401a42d41d64060500001080945200e540c8400030004c00340c2d0012454140e500b600c8580c66078440d2520341d4001e200801900071304100d01425008419221640000c05040d00404501d44860741c0f842c1240d4031440854a03103004030404000006c0605082c026aa2520303170503110a07802071320b40380146159200d02038040d14095100c070a1124040030b103100c0c20b40207806a03a2403180c1842c00600242c070500401d4142c101c0100300b040481011840480c80f550054030003000c01c01c0313040041203d43c0803802040b002962600000400040074500c0700010506d0040140c940100c443c0100016a213a003d6060040e40002e003c05c0f048c0c202460030b610514a551107803c15480500849008441450090f040409a415450610060101151440b41d404050111120b4400409a840e0341c4a403c00210f202e040c010085804402c000051100740e450030800303040b00a0b40303144640403080c100741c0b15007040301601501010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 312876034 1250 312874784 312874811
    0xc020c130f0b0d0209070807030902040203010303030f140708060d06110406050a0908120403030e030f011a01020c04090f0303020310120f0b0c070314090418082104030801060302030c040b070b0109 86
    0x107003c2c0070740c0c0013025100340f691501e00903a04120001c19200801d59109603140044e9524070145019601980d0b0018140310710f5440300c800c0703424101c41265407049030350800a0b01d9134894401540120296800b80820b007140c90220043c0c513420120041c0d1610116000c542c07154090080c1c4030005407913440545065640d80b0041d1150300502c410b0412000410061003c280a410030201c009030241c200c900c41d08606034020300b100e04402400c2c0804d00c40c041e03003000960341000540e0f019482110100f110640640c2e4010304000c104c0c400409040d000b00014800002c102d0060300103141044039000c81d0b00e420315045040c02c006107001ca07500c1c1c40590210b843c001c030740b100350f5502d01d50507140c200310802c80d004442d0094003e034164590194466054524044e0030046001c1c1c818480c5040f40c0c0ca807401408400b080c410b50380307054183d2a10b00820080401d1303000d4031b181d044035080d0500582c0c9442d04902d03c10b03584200e070000300320b4000000b0b0304030400950592050481d000e0040401c00c3c07403030050f80d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 312877284 1250 312876034 312876049
    0x9030a0227010b040b0d0b060903010507030603030e04020a020307060905010204080a03090614030f041713090603120f05180a17100608061302120c0d0b040b0702011107060c020c130f0b 81
    0x1175000e030402c0a20002455402c298007030555000001c0c942810070f09080e00103401d44030308032841400a915440208205a0040d0303580ca10f0f1501241d007941816007680c07000303583c0d020300c00e4041c0140307840301c2001040c070001b90b040780c014100070025a280302cad541c1c0c2405002c42405218600008920329140412413102a0a4034060301d030410a400240d1100d03280c045411501604000040c03c0070040c0b1480c485011011030020604200d002c1f446a146052142817503018a5414003070000760010b003080e896009088500c10041a00742c0c04031180c6450214007040b1058100d060b6600403449000c000e558000303411068801c0e40d103010301c0b0140d00c1c8d0081c651070700020f40b50b0480f500c0504040b100180f800700c182c4504040000100c1d800f00315200002101d8003032070402920500d52110501080c08102100c907988404a80000c0c00709500c5066005030034410712401070a041c0d0307100540f881e864420310018a210000410080014519209440c005e0058a0511000340d240c0034103414503050194 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 312878534 1250 312877284 312877289
    0x40311030d090302060d060906060c0c090b060306090415020a050d05070e010206010b07060e011802030d0309021c02060904050403110c24030c071a3909030a0227010b04 74
    0x2503540804520b50703400c1c00300b280c00c06c409020180740c885501050340d600030b00c5882c00604090b560000c140b03c43c1d050440b00e410b510341000510340c0c1085095102511100d084070b400540603102c0072030399030f2642040e910484120a0b0492154000103186140036032020251a140f00140410000ca44859206494006030407c21a01581192004002002c8000f0140c03000038007514010840d03003594800707036007111040020320030f60400040341c841c1541010070480080c4002c504007008040c00ca500051113050760000b60600741e00388404618110346800b02034501c3c400300503006100f1801c1c44e107806003c03400181d8452115125490000b0000e151081111010000c260311030121040028616031856100030b00c94460248200203040003d810342500350404440100015079605004107550383c03040f4641030b00a0381008444202a01c001304050301c1c0070003425460042d995041c0300e40401d003030005902029500c900c51205451581c05500c0229034007100e40c0041000b05e80e00c551210746680580e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 312879784 1250 312878534 312878537
    0x10b07050709050c0c06090d17131e1203091b03020f0402031305030a0504060e01030507020c190909050c030d020607120902030307060c120c020d0f08061203040308040311030d 77
    0xa0030070454100b19030302483c1c110103045002c07481c1c443c001c2110341c0361600580707800c003090b0310040380700c070507140d00c03084040450010b8142182c150920800200700d50f0480740c030190003c2c601003030342030003043c00c41258500964800d190700d40c04080408060002d195a01c800d0307880180e0314800d10030b40400b410501054940c01003002e00000d0700782003840000c6d0001020079590a003412910b1012034400c202411440b40580d950560311810003100501280001c80707013a040c542030009029a0301e07004502c0c0800c1080030b0340c900c107158004941030300414a0650061011501c2d28110380706001c00855a06031501e0207a0840348180341c50002241d40340c10440e80c0400284c125040454594075940040c9007143c0000e0403039041000c2500c1c0e18045800318040003002c500000d1401480c40c20354001c143c81705e80640041c2c0061500440050f002c50031040042082100200000b0701556544240c89400c0072000700b203a450356200c1c80c0080b060760107804165003c04000710544a149400110300f03004040a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 312881034 1250 312879784 312879793
    0x20118051014070c08061501020106030206040303121e09051603081603090504020a0c0311060c0339070b0c0f190c0b07021e03120f090a0b1608010b0705 67
    0x1012040310500848112950100001c0010f4404202c9840403800500180c0014203214181400c030044900c1c5034015050559040490070005a80c2d480151011683c06d41007208546001e0b4050b0307002000c03c5508050b031205040090310507044560704c980b15080c401e8007201c16120508030281030205041c8402021034508100801c2a90071034064068080d210707080c003800c00d0361504001010303a041f0090b41d0b400640840400020306620180700b101ea0100000500440e05094500f004580f0006081c820200103400c00244050315a000d40401407691b8501d00000380b0400c42c541040b640440015a100540c0030f01040c0c071148040c04940c220881036900d94903180032000301e40201c5400480e108207005607030300701101003a880e4a45900c6103807268054041f8564000c100b41e080140504403ca0b594801e006020317150500500c07842e080300040c147c0c2146a03507602038451074221105c000400110aa20a21002c2c8a9505000c0440c0d5000e032500d84061b80c8490308503641d80110107001e40f4580c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 312882284 1250 312881034 312881059
    0x611150109021b0102181e0f01030209011416060c05042301050d0f0c1103070b0103140a020d05150c0901050306130209041a040b010e030601060813120c02011805 71
    0x250300070185190519951814000081d10540c00c81e0000c3c98014100c0c2c80d000c542d5046407422040b025132103402012617007c1c902a5801141002c24032480303240c10325a00080c101c0d5140e0090640340b040085400c482580c0d05041c01038400c4c4d28048140c2100d0942c20080310802081c02130741503406490801020030207020107001c850405031480003881d0305208003000854402001030161000d4920301100c0800c0341c01d070800004010f601d14203040055504240144000500418a6603045030382000c1d800d00d05010030b9014505100102030000c0d4007602503031424007040b40108103007807144004142142d1541c1c0388559268684078080310240080c100300300217078440c5060a040b265000020100505220310140894100e441c000341c8042101d24640d150039030741c07030140034482d03940c002840d20710070f0014240b0100b5a81c42d018040d000520040781d000849012038004a04007071900900d01d029082c020300c80203055619010390507030000d8204880f14420001104483d400c03944c014000003801031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 312883534 1250 312882284 312882299
    0x70302130e04060b0f09011202040e100203070c0b01060e0904120c171e090d020d050102070c09140f07020714060d06090209091003050a03110102160b0106111501 71
    0x521000302040c105a0100380801c0340d24040703000c00c0c8183d100d0040000d01039225000c009000c141460428803401c04000188040088411003942d903641c1550302040101e01248007504041122086001c443e201204001003180e111564414560007090046556622010304841c0100400c121603000700c100004900000c01200b207031507100e42c0c94508903512004c540d680d00203030380705620940c0c2003d0b0301213500d085103400c03081a2140300700010fa00500e000f040d05d002c01c00b1308003050400b030f2007105445c000ca0180030081d012605a0381c1c1c826409040c081c8c80784101e1006000221102480076041400180305590a142440c001e50541d0011b0070141c2c504845106100175200e160740c0c01030700601a045c070840c83c502421000d401c81090142c1c480c807052061001100008210005445902500f00302040002c5001e00344190185010070b48083e00182c118064801c02140c1c0c404c0c03a4407010000240044010310b241030399550750302c007001505400b480031f603203e6018444e0f2901c0ca03640303801048041c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 312884784 1250 312883534 312883537
    0x3090b060603090f0f1f0605030a1103030f1215010302070b16090503070b0c0105060d03050a1202040503030a020109061127031501150215090a0b040606050310090507060201050c03070302 82
    0x2030390f10898030b003c0f003540c4200d4107108070420028129803107400c0c009020b08035060441c4103c43c0c0c081041003154a40400240e4411408070054103007000440c0484171034400744100c840140d50902c195a848100401c191011a001c44034026039410f9070140804542c4603000f00c4282c0707500814040c170a0344448004504000d98122400d0501440200000c0d86440030b008560042218030811130325600d020030518251900188130a10800440c2440c100007900941510744035141c2d07140c211407180795042100000c0c45550001e607030502c404911340c4550380d415004400c5480c441e813414040250b010604881a00803181c2c000c40f6040f906000d590301010000d40e180010310002e0848110120260074100000400e0300652070041d1444022456150104075604104e0482520ba501d82e280c101147d503203500c1d03c80e500900220841c00030500f070003150340004020b40002000d4603010300d1030503070342ca0017403c5110045075903001e92100059442e00611550b841601280241e80c550f5442c131004a000b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 312886034 1250 312884784 312884791
    0x3021003021c05190905060a1107021f0203041205030901020d030b100809150708011a121305100e15010b03070206040b0403110105011805150105160809100c0c0603090b060603 77
    0x9004a040c07004401c011603014642d03d0a0141b005007906003407528a5400342e41032940000005441000104010f03220714080300105003011a05840103202d000040381903105541c003400c07805000b01055810b02002000070300302640244c085403500701849a007542500c1501820a0b88200050341d103c49580c019024154040342e000b05480c00c0c1d41042e0601e0302c0078641074600e00b00044c040c2006103c074819010b180e4607412090314000c0d082180781d1f508243d45000080500017402c0500c2c41810402c40e04000fa04000c0c41c6188060000b1144030741c03041d50790340392055901c8450302e0242c00024008015411a03003d10320707640c0030f003010755030340d407184440e82034068402c5040101004580c42c0d403040c2032084901070061030302240d5014480d07061110a40d80080c104a051600c840f032000096070b0000d08035800102c0441035041984064149054240074441225401806031400140d01c507a100740a240000e201d00e04c0d0501c119110b01048045681141c0018a1315034800c0108407940742c0704010b19030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 312887284 1250 312886034 312886051
    0x10061d04020f1308060901110417031c02031512070b21040b07110303070f140d0f050601091d0c070c0510030c02060703180803070905030d050403021003021c05 70
    0x900341c0e00102c0c0003050350280c0a499884420745009000407041030003440e410450f250000d100c403c500f2080d88030039118900c03a1020061840e191040448410b0090700d403c4101c030300d61021480030303883c4210081d41c01100c02c04007449440c1c03100c501e1413806c43d0b038450898a0b00070040480074285000b50110713070b120118007a6070040c1a0000310000441107402807055212300c910f400305080c0102e000e051944d007120b10301101d40082c401c020134503602c003d82001c01030961420340072041e4441c505611a11030a48950b2183d402c06510001c10600c44d04004d0040d0400ea80c2d000850fa0b450b04100b6500404000030b21b00014160302044550980401401046000341250314646940d4000982400103e030b42030004240c560b00c0e0040aaa014000981d00c0101c6d8141442400c40c69414800d0f00a141d000c000e0041d400400402e000d00d11a03010f101c0a8003018085640000044001810743d41103884103d20502e952850080761620a009881c80003d4000d0141c00f0b0002e03002000c405094010940e02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 312888534 1250 312887284 312887287
    0x2070614031b041203090e4308160807051909050406030b06040b030714011209051e0706140304030e01020c0918162d270510061d0402 59
    0x40c640c0a00003d2005110000c0d58001a0040340b50151844006503c07503040c2034002d0007080002c4041c6a1004481c200000c52800303443c1030032002d002d850210712081410700c40d20300c610064403034128100b140555405902002c5120041d0011140350078115044070009078140055820030107085060348014103a8181404041e4623100171908451a0350b00c2911000c141d88140324444c145031040c0d1030740350360503006040003904200c0180c0c4200741050a060400040348901c1520344066405009583e03407000607030b51001d02402c1081200e082c040c000d607200703000e182800506030740900d502a4401551082075811a070f555103050340d00f50b400d08025030560186038070003581070391600e0340c10b442482c40e003001103d01001c1c000c1180c5040442e019808050703800070781c18810803030f840301c50503509441080000d101040219200859903a035038802d6681c11949044480c0c0c1200c050a01407c072541600c2c01c0105640340006096062201d108240100e500300d101d2884c81890700e40b45020b051400340c07015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 312889784 1250 312888534 312888571
    0x51002031e19031d12030c0904090b0c07031803050604110409061b0f02010b0604090921030912030902010c0219050a080309010305070206040b060d03210506010f0207061403 76
    0x31859642c00d40b03039101c002561003020070105080b18251090305021400107054a48504c0259010340c800988a01d541d2640840e04400075585c030b81010400c03ea106d015050340e818011512101500803100440108031034101e81c3d981031200b11061800c8076000b600a200725141e0740c58000440d900111f03401d40064131051203d0102d219801920060115562004840300c281d074001020950755955503811641886902c02c0300360395002c282d400360b6040c5c2c41c000519480301c0c0f0b024201f030600f00f002e050b0303580855100242196015803050138443e018000c0d02c2e00c1460007076821000c80b40c0c0070710000c1c003203440d038002100907080050900c80000019001c681030aa1603400203808140c15900c000041e0307000081c04800381d41d050017a40c0e00400c460004010314105aa0340440f80319000340030750701600090003104103051040c004021140540b4400c00c00d2407010404900180408580b02408200d44081c1040c16501c00200c0c881219603994079411080344424185401d648081c20300c9480c6404400740e03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 312891034 1250 312889784 312889807
    0x1080c0c031c0912020715030e1203060105090901030f21050a351f0501051605010b06030c09040621030318020a180501140d0605040f06060f03020a051002031e 70
    0x180801540d45e001452110b24040d030102030160080719610825040014079445d000c0d0026030031a41060310000c0c50749999800f03004030f50318001c2d158450750081c001000041440348070b030b040782d4945000311700a10250020503100506c002489400d40000b88040103c4202c0500c9043d1a07502122110308410445036800b40107446525080c1241105501f0b000c00c3c01045803c03906000101850590000880391420002a11900a884004440e854407034500800c1000030f5000719000040248926206d0500c550726940c0d903044228014011850a0f00119444071164003200032408685c100c240034007465501100039101c0d458801461000201e00080140d076000c0703030b0b407020780f01e84a01d0a0036050300407020400d540e41a4040c04480d4050030655240ea15109040ae0300301d5046039020541da111882c001e020429884009000c0518111010407504102c400000440e8003c59410038501d0300c2e90304211604000e081c020015900410040666520a00c410010740202600c01030511031005803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 312892284 1250 312891034 312891053
    0x1111312110303030a1d070602120d020c06011211010e03030904020f04030501020a02030307081803070f1104150501030608010204050a050d0302120a030501240c03030b030f03120601080c0c031c09 86
    0x1c0014111b0384503c030400d00d6038240d64540116200307040081c818640741c144043e48a5842c05001607102c0ca00041c800c60505141d0100c801c5904042c01322155503035103420300b010007071b2030031012510700040d0f0290702d28541c0309442d591007025004020758038004070301041200a40c4036440d0301d8035451041c403002011800030300c040c1504980540103140c0c0c0b45041000141004001412a4803440300103503801c44040000003540c030b8031540079201502002c002e0416071190424008050342c005e090600e0381741d032100400c24140840344280c84c10302c03509883c0c02c807080c20b0303019501034160000c0e00c852041210b840c00d045403880302c41c0680140c8003052940081c04c11554850302c00d01c400f207030716000104a21a405440c10f14403492040d01c006600346440d1005200300c040c2d0390085e08250b01c410000e40140d60038080e054030340100e0022255035101c41501045960300c119401d0303010076080d00000704084100000c844d0101c41d1280958030f404091820101041c0c0b4082c030b040d50300c81e956080303040095003106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 312893534 1250 312892284 312892291
    0x1314010e030111040326030c090d390506070f0f0f2f130e071203030504050f010e07061209150f0507111519060b0c0111131211030303 59
    0x500c8a0350b00c40c29820889080e80412500b94407074802120401c4146c103481c4252a04040c1c920340769540ca4201d0000240c8079524050090401d02e400b80903030280f040d401d02401d400305000e5031842c0c902071a501c100300c0c507201d00e4402e5540280c001c1011200181e420703442c40320482d04c160154196820103855020480d00503050484401c0c0c1c4081920854501002030742051061311310301c4101c541c0310007020454546c1d0883d40b108000d600c40d49481c04554003031001d0009406081c840542c16445400c000b00902001d990640e62801502e000240302413040c0a0030a00280f007000508000e403a011040b106481074001d603404081c1d0720740d00704001031100464100301d03d0b40c280010800c074503c80009021254050300c01410f0040041c3c240c0c01811300415600051052003c510002e5a51500f040c039035a5407020320580030030300d00800400c1005c20b400140883c0002d5000812101c0480b0004e92602e02c680b643d0614070310103022040002c0f107040b0140103000351280c0e50401a920902020a00d9500300740c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 312894784 1250 312893534 312893561
    0xe150103031d06040608040c051002011a1c0f052b0e010e090114010521180f07090c021f0e12040e0a09030203120702211314010e0301 59
    0x104149030340005240302c81101c0c0e6800c02c40c4031540000141d0700b0b00c00c40c4100c40c20b0007001400541807200075420900141805405001c0351040303028020300800b01c074560868504031607044852141005005c40e00d20380b100d40b80818004406481d140355245181070112198400c03a0750301181044880044201d0308850043e206000102500141c107040354181018100301e1811000405544d40c2d901d4181101c02c21011103050415180040f656480303041c52043c111540261170441100711a00b400384191009040440d440400e414010348034086203d540e400c1c0e501442007840060002d9001041d501100d0044078201c80c142d400e400021041100c01c400781319034a03513902c0000f400500c844a1950644201c03180341c40d080c0705100d403200901401d482615642c800140301010b00800072100c4111030110011241e02e0b084000941d076600340a05038034100400d4203002c540b401c1c11410783d00049540c05030103101070705002204400c16600181541040030b81e181001c41504e0a20a00711501282c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 312896034 1250 312894784 312894823
    0x1140403050708100c03020313140a08031311060f19110d080103030207060e1503090106030b04050705180402010219021302040305030324061804020d06080f010c02060105030c0906040e 81
    0x40b104c0c0110780105d0445001e150040080003070b00082809210708841d40031018400440701e01c26101e103803000301070005000080001c103122400042269030709401e4418a5031402580c054024851f0324043d008000c0c0c1d41c5142409038802c6c003024010801c12090082c50401c408441c0d5400c0c140c0b40201045007140411901d00040c0103140d4180f014070068101360a00c025004007540109003102005032202600840c08000b00d18600029004180115040700082c4420b00b46400c2003130b105c0031940b1a0380d02c100c030b442c500301d00c40c202441c00b0207215a4050700544034280c80c03c4210100308080c0d0004a9005002c1e0803111280d03503940c405000554082e0008580300e250000e0104c20308007407003820b810507020100d91545141e4401040300e0704941c0300390750404000411008140a401400004545141802c0380490040f8002580502c6007106400a200d4414203200691300c4a10a0080d680c050f003064601c00304500705200f100e03030095000f40c40041c000c2c0b00941201c2c14100460310016180e0382 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 312897284 1250 312896034 312896053
    0x1503090501020d2d150e0406020d0e030a090906061e1e02010b0f0a0e1b071e03020105071e0302091302030403090e070815010c0f0f05010b1306030203070501140403050708 75
    0x28030039124554660b00d00030030800c10485c10940f40312a0500c144101010000009420001c1c150181c401340d014074001401441110312066842c0c0d0000b02000000500c06400012200524060740c0b003141c1d0aa2603406040055558900b02c80c580d8407040c3e000d00c510215030300d1075071200780841854000103a00001d070000004080080621a03810381901c07402130a0014080f014110308070136000511241e880c0c181d460107c0341001c7c1400ac0f000c000e0900241c3e000081c80c0e01482d0319249280714406c0e4006c00035683d8410003580c010000d4800c6d0f52540b5506583e0360300c5d050096005103111480109522003003a020401ca100341c2e481220200c0c00070340914802c00c403070b10401e003029401800500b0302c3c6800703141c0490b401500c40b5104030142d040292021180c000d03c0034a0004c0d03000b00360040340d2100d8481d20b40c00c281d03029100016800f8040c541c0c2e00e40c800310708042e0744070304030581e07034010050080c0d03904e400011a40c080b490f080042c0d605008100000014204202d00380061015401401310100b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 312898534 1250 312897284 312897341
    0x15011e030608010b120303060409390509100b0d09020901030503070c081c03050c04051f1103091c0c080616030c03022b020d020d05011406041503090501020d 69
    0xb0b841c4e101d80c0d4010402e170158401550350110660364490301c1030310005601111400c0904064005803012401c4400950300c19025003148015444120381003559000c8171a540c034148841808101c0d141c0f1003200040805025084a0500800e45190300c0c6c0c0c404181d0040315000541b9004080c0d00890f0207038800140750040080c0c0c0030400c001041c50101800000300d44003070b45482e52320b000760311030105542ca00c00a4102642c56055074050003016007400d440003016000b080d4450541803400c80481d8602c41d00181c08000042110010740c8040d144a02c1d42d0200300d400030b03200001000403034100764503080c0860306180401005108260380281e03404c020280c10070150880e0301f80c3d00d07c1c404241c0100030700d1000050114548405115004a0000c0a482601204024028103900c200302a0000480c0550402c0a411003410385212841c0825120010700c100202480707540304041c2c140750f1080c8641401c6020341c0c4000d0311140508000751420040b0030400e012920181910101c1c403410327580030074901 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312899784 1250 312898534 312898541
    0xd0c14131a070b0103060b0105041802031b0c120d0b1c0303051f03080325090f0807060912030201090516061101090b15060904050411240315011e03060801 68
    0x49121003031081c500b1555444446901c881400054110368030b41c50641100d0748075a00f201d0044c0f03003402c40c80b1040e09000c0c41c400e0103076105a80c0030608040580c0d40d00304115104048400c1d80c51400000c08245d0180700c1280c49a03046400040c1c14595210140107058407811441c0d1445003801d00c9248030a00300340350280c100c0380d02400301281e40d0300103004044030503e064100c5e8152034001c1c0c2c11315201e03540c01300a8114421084011103003c500c03000c2ea04060f0303401c00160300590340913840d1907a0094503200f445548940178800c15001480c451820800001c8800107583c6041c000c0c800030a810b1400c0c2c64882c607090382018540e0480c08564001c002080d400401c0c1518070603064001e116250041d00d038282c0101d400303402c041700d51114103061010303542c5040480300d65000240c4188883c0c80c203401c0042c44080201c0d034640c01043c01608524100424981c0b140410103090305490a41d1039407194203400c01211041681405040702111003007111032121500c4506841c0c1c1c000c50b940d0306007440642503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312901034 1250 312899784 312899819
    0x1c020415031b0b03010501020a0311160e0a0f0504020d0212120a0e0103050901201c110a030b0307030308010303140409050f09010608300f0a0309030e0906060d0c1413 73
    0x100f2007400180101d130380c0403800711422501842d0081c0c05d8051100342c182420500207815040b42401040021030b075103800407a91282869030710800c00050001101c405840040390000e500940c1c0c0350b0840018900201b22191a5a050701118240104080340740040c0c1d00034000080403462080408a440d070b41401100e0348003140c0d00c02444066030700810f1261503aa10005003d00d1a4040b072001c01c2c14801003409002c1c01e40e450010f12080d0004040340070240d1001050a0000e4100604403510f410001051400c076540350b940c821003680307107480840e5218030000401c0c0c50305404220014010081b4003d1601540140000c044d060400c840d489007142c0c0940d104900c00e402202280d44402002040d40a903800501091024201541d040c0c0030903106c1c2ca80400c12600340414105c1040d64154406905d1520030b481e44c14005460750200007141c1400c880c01c59001104001000c030740c04441e00b0076807840707500d1704103808102c0e0501c2e180c0c100b03508008000304030740a540b20700b001485005040d40c2030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312902284 1250 312901034 312901049
    0xe090601150c0210031a10050408060709080d1b060504062c1b0625060e03030f22020a1e0e09030412050a080d0b09090c1c020415031b 59
    0x10a0902e50303002c11003480c00b0360300b4403042c155070706604000042100e1440501d0b540040ca100310240c4200805020f5410500031040740d80b01d042c002440490080000d441601c0e180c10007041203000f040d000b1112002410102c4000760003d024007800100b5074051140039522402d0302041e0411043d020011084882c4040d541c20102c2d000d5140785610041201000b450401600e01b14a080f1400800d08620071000d0000c2c0c0c44200580300c000d20005a441c0394101445600705006080113808030950b240426a40c1003900c1e0390070301c04141220400034000d5215a03d444110850501310f0300028010b0440f0f5002c409000e0640005603e032140410700107001d400151030010023410506441c658a0003140070300c0c210303001d800b10103030700303000b410881122110340c414181543c0f0407186003d0006040c0544c4028090300c3c581c004601041e601007102c20325040054100d10501e0301c2010700a41c92180c401081e6081640c0740319100800d505806800c014500030340390450410040e01524130781031000c0d8000507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312903534 1250 312902284 312902297
    0x8031009020d02070203100c0509010e030715030b100504080d0323090708250b090a0f181112150a0f090914121603051605070e0c09010e0d0303060e09060115 69
    0x508d41d83e00041655000c06081c6440b60803a81300801080c0391a03a5904500154000c5104440255a054000f519000426111a064030500c8401a19540141c6c064105640c1000c44031002440c03007580200c43e002e120b5640451030203901200c1018030301d0181c4040895401200061000c440d0030080f8851054401c1d0703582d1070441112203400c0314844280210641c0e1040010000c4959540d08081800b62856034000954540c2c2d0b0841003040000c6a208204881d0810060144040303050040d124450002e4411800642d1800302c003d048080c2818255480200740700b0200704000c903049201c0140002d0703c1c0024034103940b8103180c0032040c001c42e003004032640030718071103c42e00c2c40310410b8400210706403905203510401031905039001c0c010050102c0307240001d409000d0038002c1c00074504084400c500c6030b41c0c0071038aa41010948601c106803c0601081c0764010034089404d0615031510024000c0c640003410030340f02c10400403c00740988410040707500590060201d503600b6245182e46003001c0c00e240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312904784 1250 312903534 312903551
    0x906090b0f030402030124030209060a080c130f060801150f0b07120207030210051c020a0c020f2b060b06031506181005040e090d0c08031009020d0207020310 69
    0x1540500ca07400491100d9880440070030210345094004041c44080d4030135400790b401c1001c04403c22281c02d03101c140d2140520501241c8542003c95031602590340350005040844010010700c12940051610b010026035100b01c210145c120758400d8501034440b1500125a002d44108000d40c0f41845030817200e124001d45000300703c20424901200c0c13400d40d201c5554410ba084001c000d80c03c0041d00da2020b500141c0301c640c031030700040d071142c01414150891100079031252181d182c100101d001c0d4000b44004160b00c1c0d41103002510740380310310320310100008201140c00f50564401424005031000715586289081d002001040352901a40c1d074150820780d02c007820b6113007504400155003250100e842c080c0c003001032520b56204180d0b44d680c00c0c18202a0100305451007814000341164041d01c074598000140901107201c411010440402c4116190b6030407040b074001791a90100303648090280b02c7c441144000002d000c00b401c1c00941545c1c01d100e00010388841c0c1500500d400c1c404011081b010721403615004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312906034 1250 312904784 312904799
    0x30909240b0414090403050f041401080a0605030622120f141312060e010c0e030f010506090703020f0c070b040e090d080411120316110909060a0f0b10030903090609 72
    0x2000060b160460304c0765403503100e0f41410fa42d1403186441d90f0200e1034000030042015102c80030745001c003542c00ea80d20200c40c1d948800200c104c51507030043c0c55064100401040f4403542d40141c85034035001d0700c00b400201c0c20386581c03003821341484c4021b038001065508950b0351400d604040c42a9410465502041c038003080030f210101d407500ca83c020505584c0c0c0d00d51140b41803181c80c1d03000514190340d0000800186030b000c600603103c185d0f000070f224428494074a81c00040541805071500426024007180e110707440e80d01c0294007941255120b2450b4800c10701141c90074650030030202e8021b003070780e031030450742c80e4109045100da180000f03182006d56070005801700c103400d9101460700c0d0701c81d41100e00201620b180c6400252080c0f094002d441962001051100c17240100d40031085050344038042404481d40104140304512808440c207290980010000403145296a001071403091010200080c01341140e1000841c110000c0120500084c0d07990000400c06420208410117450107007009211680f52440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312907284 1250 312906034 312906059
    0xa1e05012412180b040f0c0f03030207030f0503210108010f020405010219062004051809031204020d0f0302010c08010f3605010308250804050904030909240b04 70
    0x4580c0d0402c0ea41d080340c0340d8450f0382401480c00b181d4032024503000303401c1c14140151441c46004050780d140141160006a40b500b16901d0421281e054000d016240c2ca0740d1911418101084001d5585e400208041d01d40740782801c41031b1043c03c5050f52002019418500ca05013103541d0389400061003481000140030f181c0c2c002401c0c2c0d081c81101a94134036290950f00c0c0c0302c406044885111524034050040d555a1014004003500c19240261503101050b0917284603000b500009441041d03550f0020411807401410b020075983e480f07400030b4144004080c1956031400d4808a507801900140d640382042c80c14070364000d01d02070050002030340d45c7c600282000b02001c2b00300f01e07820b08100745640141010b5580c6500c2191004407075038103070040101d90380d01c0c1440000c60b402001d01041000f920040c244001c100c0c3c043c81e48109410070401828241040f0500c454114044c0c41541030100e540c1780007401600e20700038066089100030301c44410020100000c95506a2a000151051801d000c1400b030180d84c5403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312908534 1250 312907284 312907307
    0x30f18020609010201061a1b0106120b0c0c060408120609011503020a12020406030606021203010608180f010914010c02031c02030c04080d1d0f03060406050a1e050124 73
    0x140c280d56188004001130340103001d90741c0182c01ca19605801c01450710f8246019020f21a2584400795160b014458550300f20740c80c038003400c500b010100300c803480400c1c02d058005900ca024a0035251614006032200761900c201203404603481c160000303000d100518205071041c3c03c0347c001e403003100380ba50400c010340d01d10003144013407041015030215043e004980720701c11a41c4000b000c55021036603907481e40d800070003410003030040d00050720032410841c5058580600701c0c1d0494006995008460b120444948201c04a2119400c014403400300344581004082c030510103007600c40c0200c0303240d054000080b54251010540b025066400070300540c404c5000f0040100040c1000540040c0d9a035100d000c441d0b01801607800500d0346120b0f40b00304d03400c0150820010000c840130141c3c0e4607010410702041220706204e001036a5059000342010900283c2c9540006402c1840f0500c00300d8180000c0349100740392124040703851410350712800108440e0070541103601c2c0888441c48907009401d02900060712040205 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312909784 1250 312908534 312908539
    0xd02030c040e10060b070506161407030302040e0a0902090a1806020c0106080601060c0c0f0305030702010c17070f0209010806090304061107150f0917070b090f12060403030f1802 78
    0x45210b585202c60920282c810fa41031041c0811226844040203140ba4111000c11103982c80f586010522591001c01c2040c1c000d0f0366562400130603015142100030f26001a5821014550284030100f5481d25a21090b0711410703415034009851000b0740100558002d020308a24019840c0494582028071080105800b040e08480c004d80d135002200758450040c0082c4d031003501c3c0390150134000304601703078044501c1107801d00a42e104000161922aa0030081c00b9901c0010f1469108021724801540074080c2650018040c40810700c140c50800c12a00b41e541c4030f2102285e0607003007420326408510b03140780914090844040281024905030346040c0c0d80e0310a9020300d07030521408100c8060f90217010001c1a001d0499940e5844841e00f88000141803c840008240b0100342d00c09030101d03030016035901031491321040c440280982840c0000920459200d001d0003134202c0d000c41d58100d40c544400710b07240500e240100042c0b9031854181030040c22602c82220074080a81416030441c0002d101c01007694209404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312911034 1250 312909784 312909791
    0x20a020405090703020a030b0f0109060e070807090e0703090302100506150f040b13030506151f0201020c0d0f092108030a15060305222006070501020409020702010e0d02030c04 77
    0x110b0510a14003c100c1d03100035030250030044084200a03498000ba805401003091014040c1d88500100c2c007610864003403540c0c4100410300042540380301d2400c1b240c12a000b0305000722519211101d110401a00303d440c000403035103030b1501b0010507604011807800660880f00030040c0c0d05044000030030010983c01c0100e503907100850340e03102c11076450307040354001d00c00655481e030b40780b1415100034a5402d6a20058426015800c0080c8201d44422402034404074010300004400803501c00c00707495030b50000200800c6650a2051100c40c1070100300b1800181d085803901c401c281070000c2c0042001130343e40c009141d111001060a01c0c0d171000506218400ba600500d410344942d1510b201500602400b891094101c2405500080464065000a00440356490781901400302603036500c0c0d0321504090002c1081002c06c001150500e243c2000000c0d8100040c449460309080f52201c1e401d80e001f50700a0703584154001013000031581c0000d00103400701e106581e0f290f840b411940029444186100859004985 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312912284 1250 312911034 312911041
    0x16060206010803450a050603071418060313050d021f0903050d050a05240f040b180a050105030c180f0426030108060a02121b0712050d1a01020a020405 66
    0x1e00c0d11070900120482d0120b03250b481500074800c0c003206542da080c00b85c0c2c20000d02107100d0404030112446009141c132138140d8004081211007069101c5c024420019004108070741450760740c00d004602480004089500000042c00c0150070585a82d01c0c07041554001824000850501901c10440d625181c00c000303912101c906050740d1030f209038408035003103607c0c0a0030031031b5403d06d030b0340304502441441c003540750030206d43d04a89040404410307980798070000c4210700407404e00e4141c120f840c00c4d08018285492000204100350382d18041642c003482665105e9006010904040061140c2808110f0300d0b49040101c02914060116026003100480d001201c005018040100c4288030b07610b840000000d1504a04843c400140e0020b01802d58180900380c04594046401d000762104801808404c1e5042e864030340c9aa800340841c044120100c03201444490003082760310707521410306280741c0c80c0c0a5650700403000c81000c8840d10b071007088047d00b020400d015a641d00181c0154a00d5055400107000c1e103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312913534 1250 312912284 312912337
    0x13051015090506040602010911030d120e010612050a060e031c0b030f030c0109060b040219050c01150e011508280902040c02071d0402090705090613060216060206010803 74
    0x81c140c20054002200060010301c0a90551014070118026101c0b48085200c1504240d243e500340440c00700000c40c01810b4803800c07001903011803510b0740d0b03c0f4000100a95a080741744094401c041040d40c003904002d10300c4040c4003a81c01220000349090707000d50700d03100c4d4868243c02c624181e0340030142040c1c0e841543d00407070f4500b0481400460030420843c5d48030000d600e5218082c1c410b15400300c3d040f50501780d90b4241c6003000e00070740d01a24003005011a0302000700300d0403181d0742c204c0c00144126649a0045150226160101401400394402026815030400310203003120038808001f4010410f4403000c0146118488062801104100c2c82c00c40c2e1606030314a511002e00408d44001e94468607080c0c18034000e540010b482011589148070083c0c0108005e1040080120119400380d04180c034030b00000c1b5564410700003084801001000d10742040119880d00d44964a2504060013580c44440340084541031502028000c010034401001e0a605151845840b400390307010019030414041040580c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312914784 1250 312913534 312913547
    0x5060a18020306040804090e0102030417091c050610050f1e131d0d0c08030f04030311030f01091109010c231b210606090a06170c13051015 61
    0x1590010215000b0713080c07a040c0400350b03502a1180c403d0413403074610f500c4d401000600a0300c1c49150845411802c40c5e4100703220101d2940945a1954400150380c680d650300d5601004910089004400400700d514111074540c03c005d0294002602c1032041c41d024400643e18512048514a09001c040020890300004100501450400150f0050410b00b0f006001210104402e40c0088604110707804000c8203501951b41680104014202240400000720041082d51030280c10511910b40018032030340f038040d8855075030402d481c3d540008070514010800e1900c0d9025801c2d0100140d06d0703040c0b524058400207040103848180003040e511003002e00d15810b0403001e510307141c040c0448064034160380d03181040e0300f800700c9000700052140c140700360140c1c542161a03844403145143c900061041c1c2e1140000c00c071034001c0003480010400c0e02c6010204001658030916200c2c0340c0c000005041c0649400204040c1d1b03905000400c0d5105c0c5050308201c44030541c04894012102061124421a844007608a842 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312916034 1250 312914784 312914831
    0x1617040506160b070513150203040b0c0615010e030a061a040603030801031a0c040501080402031f09020a120203070e090102210604050907050105030a0e030c01150f0e0405060a 77
    0x81004a440380030440400c944800c1c00b40f00b041096119901d003a000d952900624040d180a4000f2201c01d105a00039a40c0306850312a03640100c4c0d06040c0d0303802c50341c01d02c0d900a88800d4a00e4014506000388100d0910703521240c1542424004082a44140400c0c1c0c0d9408810020b804140c8807a002c900c02c104160600d5481480030f0400d210072610ba00b40030b00f01c1242844102c0309000f1100000c100410744e5151180102c0c0003940a82c03034940340000458581c1e80240090364140258034444402d80302400d5054540c000f40000400c074452540108003a09169611100015485a40407c011303607022a80501703440c1105010681600c13106803241c02405420b641c005014907501a00c020304074a0003641d40714803030840b400e110640d1528484d54407450b59101301d80c003050083c808224002c1c6141c1026981d0582c09007104d040c007440c5060b090945001104404140c600d07001d051202070039014034440030b065003000e02051030400d0350f2180e50b03642c070040c50074201d00d0340c900009121100c1000540340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312917284 1250 312916034 312916039
    0x1060f020d020c0f0d020d02091305070b030c16140105070914010207031205030403051b060105120318012015070f080f070e040f020a03050f0106030603030503010e0c0f0a030905010501050616170405 87
    0x2703080c40c20207184102e00c441d480003502c10f44905640054200c2841042324810800107400f070f400c00b0765182e0b2a0210310b0044108071590542503080302c250b04000d200e15882003000356181c0000900d4680d0448042032009006411500301c9002800450000740c5282e0a5001c41d15045549a0311400e040310380303010b82a5009260541150300c110b8020000070254140d0340201c1d004800103103000c10b815983d12403408449000140c8400894082d8050050b140c01c00c901170680c1140807200300d00b41030074800c40840725440e105201092000b0340b035100488184250b45030410302070500308020039825204000b011a010440303a028011000c0d265604041c144456000065442e0544541d000d40034000840e00700136075140b400c0c00002c241c2c1c80384c010b01e81100c0e01901d1b40e524603403c0ca6050114420010312603d10382108120306607840c4000c030002d114291050390009503031061481c21a003540c03030607401688210405c1c025616450541544461141d503c1301522540300040d20032650540501e520144c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312918534 1250 312917284 312917299
    0x1101050c070314060c0301032003030c10091203090b130204140703020702121903050306031e0d0810181e1d0610030b04080d09020901060f020d020c0f0d020d02 70
    0xc20a00304002c10902c0f030940b081d640d440d569034006489030300007484050300b100081c1c0001100f1940101941d20514005010349140a41050000d8170b0302c1141103402c58000c0d6a82464030a121242d0011032485032985801d00403d1429240c2078000300c0082c011004942d900240d11045585070f078410384848400108103140d6203088180500203422822044e4000c034441d041420800c000802d00c0c14001000080400400020307031022110364000070045138051055241c0300c0d00c04280c50704006101c483c00d9004003501d00b10a01c00070040d000160041380021401c1b041404220313000000020301c941402c100040704802c00682c51042c03903c407aa2104543d11300108800300729412540041c91603807000803215181c80b0718580301488261444060304810104020400050691000b07018510180401099441164001800181e000e901c01808202201304c24040342e40c061002000c0c0001d20300281c04103141c8040030a0800301203801c5d0381d1049660142041c115540d0740321b900b080a4020309200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312919784 1250 312918534 312918539
    0x40222110c0610030804090c03020f030108030c0d0305010f031101360b031e0c1201060c0618051005070207091a030c190504020304110603150f0f0108041101050c07 72
    0x640d000188841d00c50040000243c0340502d01d0303c0c144220b951002501d1301d003515180c90040200001d8046a003010f03001c1104890490782c00c80a1406480040090f642d00c3c41009000c03450140d8000b0b031401030505260040010410588040701221380202000082c9803c01004035001200c070750710451041401da002000c12408020760380ca2561400090300a00794403001030317070a07030f0104588003040b240011800481c484e00c0b01d103000e5041140900705a0800003a07460180c0300443c00d80003000061305011854040c441a80240c2d40d2804804d4803081c5001c84030380382d564881d07103e0300115044581380d0b07001ca0340c400d208110b007030020510035a040100000303414503002071404040e0000d00c40d1151840307925403803808031301c40b01040c03c041070801c040318079050600000c2d4200410517200d40a80c81120001600c0d54002140b04460388030440344040c00300da0410038000c8040300347c0c501410a4a03500c1c0842c1e43c01c502a241c001340c0210803001e0500b15000121598460006240b07481d00034041c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312921034 1250 312919784 312919811
    0x11070b010609060203040806190b030304080a020405060402090603040f0804080d0806030d1716020a061d01060e070c02010503040f140307060c0305041515050402040f0303080a0b010206040222 84
    0x145050741c8242d940c01c0116666684101d83d01d0040380160425908800c0c00310300e00c40e060380c503200d01080c0c020303a0200720221098001b03411600710b40d0100030303a80c024182c001c0443c81c0510400b0780c81101294210b08152980010030103c0c000204010599114041103c007400480c070300f52002003008200320b512140030a14018100181a6800c83c002d10035500041301c001d01403c848000c411152012809581c1d4040100707981902010080c03080d0700aa62068020814038054203000d402217101d4009080540702282d400c44100e5440004850010002d2281a5502020348040150240303810b5450340ca0354280f58824040100c8000c041d696130340f4442c4c4103000c02101502e40e081c0200780c00c0042c2c41003035800f41d0070b80b00d084400400400201c5c5108442400f42e505c81c40c83c0081d2224004902a00c5001103401c9074003c0d00030403914490b04908104240d407140d0400e900034030018080c0700d0391040c107002075600c00d8060b00003881443c1c5841914441c4ca4404100c2e0011710354800306008510304e0304107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312922284 1250 312921034 312921053
    0x5010602010b04050a0203070f05070312060b0415020a03020705192103020607020d050f25060209040e0c060405090717040f1a06030601261006141203090d061107 71
    0xc40710f01642c01c0400083d0803080ca442941d100360010b4a0b6015640e01150048429900282048060040d039141406070100e9a01c40d40c0054103041182c1d66445082c802c2100d00c0890802058003150300c01e5500380c00103503012441c441100c42c2541c071250303a00382a050350481e05090360440c04440c84408180300c44a412180c002c403406011b038081d10342d5074484902c1241c64606601c1403c001c502c0420014401c00e40071801041b4071a4695001100d41c981c10a18100d0b070703400408140c64140d004241d122503031405114055490b00c00c1e00082061145090210b00306004a100e210b124442404c0050345c03807030159641da1a0010b0340c144040c4507180514007000c02441e05801a0741c1e0440c1d80103040043c900441c0a1405407400030b0080070380741c0ca007010030b0f061803030345800740c0035070b41c01e00c030036405010400b048081d035940c1303032041c021401e03504017607021080c07018542c00280301e510002e02c00b0b00c401c08040300f195070194064400c10141c0d50541040c00c09440008410003108000040c1c1d8428060000d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312923534 1250 312922284 312922301
    0x7080609010c14040e0403120b031e07060504081009021c0c030506010501080112140718050a1107020a090c03060b07060c0f030b0102030d051e070203030f06060a2f010501060201 78
    0x1c0780c10001240424420b6458004c50140ea0301c0361607a180072602081c004ca84500000500c2c40000c40c00c46240c102180c01e0010201c0c0650217624440c40281040c0818008080a0081c2d03280003401e10f480c1c45041d5039a0061115560354450355640700c081591a0180040f401116980c0d00c2081c02d036461621002550b624441603a4078011100085650341c41100341c5412180b0031201c007020300106440d1100210a00704060001f031240719000140140d40581c00101d035180c083c070019030751030000d01c108143c0300725203140011b4680c200701400c0160f44048a45043d104240d90009555180007000d074024400354001907000340c00411030504209594100701c515040c1d940d02d2800f0480280c00507810350340016106400f41c0c106114120260019a10140c1d000000c5480300308904068624041110015143e41005030000010804004407256080340c002906a40c3d0354504040f841009054848004501004400d4840c0c01c204080c0d00e00560004445910000c00c01540d440201070300824055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312924784 1250 312923534 312923537
    0x11091f030b101706150a03020f0418050d0e040f05010e07050307020c040f240f05100e130e12030103030f08073b010311030402012304120c150f050c07080609010c 71
    0x600c180e8030542030003101201120b80c050540b9482780c030520100720103408648801030032002541c0824010a0041102c00107900558941603001c4c1c2c21001400141c03103025189900282c10030004001412038a24841da2007900c03458030540740d4462000890400500c42003685d40103080c002c04089070354869003c08241e400c1d10500303d0f00c4800d01044100080c0c3c482c41140c01e1075107040020081c03070034051110030b11060940f9061075950325940000310060b1035908060b010b19503807804203111083c20000000400041d00c11542103600d580e800034003000b40340e0302810410100c071022a030018040c0005100300c1000d09105444009490052200d55910100c200345016081840c41040d502900c00c0e45440e1507200b401c14038550702d580054509008080c9644803000c2d0200d030014040d9141c50140025029620381035090250504044490603080c0c0c200c07403c40c1c403038501030b15140d9030400c0030020f0040341d5081c02034850901d40e01050501110350700049050040000308000c3c0c0030194081da480d42c03000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312926034 1250 312924784 312924811
    0x6060d0606081e060d080d020c01050c090307080714040f09150c1209110603100f03050105160806010507063c0e1906051f0311091f030b101706 63
    0x16100c0030030102c5415070752243c010005c1d011820120b1442401004140e50f1184d0240c035000b0360402c43c0303084030300485030900d01481c0400d10720400c1c513003885801c0013003000c00000d100e01070a02c94500050f0002d003c0f034910031a030b03400031022880c21135089102c2c035981055180d41c90790341440100e00075041c4030b40500d00041500032030f0702525846200701044503400410654004400405009450340064039481803200c01420000f4011426801d4101440c8901c001140e01d082c4003460714000c0320344600600034010000c007001a01e0b41c1c0321041d14003007608070f0000324007145010080310265259411001d422185c683c6d00c0c140d403400709100d490903801c04c000108228803c10f03000036250000c4428221464400189240100b451a001260800c3c011003481a01e100e01145030540d40346187d0048454442c10700700c0c8001c520b4220521a80800c0a0844003113002e00e82041143c0b102c1d0307601009015240f01c1d400724600c0d0280c1c1074400060900b00d0f07500c130311000c0d01c50790681c5d4826003281c0000e040843d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312927284 1250 312926034 312926071
    0xb06070506041a1006030f06080106170706050f0322140c0a05090907151806030614040506100f0c02060a0206060a090c021b011b03030203101a1206060d060608 70
    0x120110f800d10501810b10502901800c12030214007802140d81c4041100d03444031004070b4669000e10a910003401410009481d14064018240c101041c90740041c007404030501010904180100c01c51b07500192082e01401d1a1008601d4900242000800604041010f010300e841c0524000303407a04003600212102401b2079610b5040040305601260007400c16000400108114220441d5042c1c03101410b0410105507080d100f1502c1c000f41c040c0e481240041d031074200402800d114100b0781c3e103607103805540503c080e00d806030200e03800040b5140001c0c100622500507840951081411103500d950080c4003c1c0c0d20b254000000f036a0340800d8840034403070000380100084460071482082110705072034029085101030b0b044652040da0910007a10b061090b22403595032021100384c08401c9842c1309031001a1241441c5125007515003668002c880c020002c2149107500b00031034000d42d180c00132801802c400315a40e1001150a500414850307e60741828030201103180c503080503080c0d01c10601c815a0001d00c24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312928534 1250 312927284 312927323
    0x708060f030705030c37140d1a070c020409260c15060d060e01050a050a0e060a050604091a01061b120807050f0c0f01060905071d040b0607050604 64
    0x1c00030f108183d8550300800c400201c904203001070084082080110352941c82c85050b030b00c1c0c6103146079184901d13200f00c14101030201d070f5200e14800c0e10201e030944100c0140f503499034900c240f0b410070444d8524100703114400680c0551040c0c0440002c0e541c060014440e012461a001c510103a01c0c0054a052010040150310006269400c0d5401c02e0440070041c0120b804502118084160243c1825042929985c0410200d01c46019444600360000000956440c1088000c0229100506002e9919060807185802020005801d0b900007030030b5840003820b0307104d00e8002402000080c60007420030b50f01140d00d050000559507414102c403078544130589000619030382110034101582c0014107008480c141c4503681031040b01c1d8661300a025090031846e10810309400b0045400001080c50950b0014150801c00c801c02c0c01342800601d09404d0610480c01c190340007401964201100c5009100707600f00030b142940d03440d0040c2d42c4411000d003141303640c3e00840c105079484107001ca80036901201c1c034020040500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312929784 1250 312928534 312928543
    0xb0301022205042f0d0e030a0212131809020301180507050604050907030216021207031a0f07110a02040612020f0910090e01090b18121c1d01050708060f03 68
    0x141a01c81d00312903000513554144041c040a001d00402640081c4920010300103948a110201118100110340328525220000d180800b40f55150503020743c10b02102c140d810a2101d000700741c1e59080441e90180c01c0c8502d003d001024400c0010354191700380840c0d03400a540b150701000d801800f42c402c0d103401a4a0724148034240c840c601c913141e0004000000142d20714400c0d8043d00c080807400300e02c00600108c50b00004c21800103501440c255403c40302c410420003001000100d0440075010003910207281110b0300c612007640080c55141401008259440c01074428400c0e0141207500900c108682d984520715040c1c03000641008901034a071441c00130242d03141c07001c0c20500c503a042c4001d4102140c246031410b4086c00d010076001050b0b640b40c5901000040c611125075200b8011b4443c0c0c8070b4840700c0559502e2030103007d05020008a18100060a940b500d000543c10081d454448080f920b00760203c4122540f8212800141140d441c01085c044004e41c010382560060504841c4030310b041c1140002c00da01c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312931034 1250 312929784 312929801
    0x7060201020913020c1e010605040b0f0906040b010c06050f01142220030906060102280807141e070510020303040f0606180c0912020105030f0a0b030102220504 70
    0x10141c00110b070f45408210f60010500c90080005560700100e00c00400340c2c8880d881240c000080c2d4440809000c5800c103841000701c0c1c0c1500b11007030b09c500800c0f00d0104002250203040b01b4041c58950400e064240d01840038003228031382c07141007000549801810280e41007001e0082000e07160690380d0011040c980350442a050030780c02c205400c00c811f51881d2500040c13040504075100c0d8140f0f103c100102a040c440a1840f801d200e1000d4034607494508002400d1448083c0420742c0d03011250200c0c1ca00e5020020101070455205218540d2044241044001028103c581011510842c8861a540c88444200c541d040455004541d0441e88070001c1002c04046580b821005900c14000100400c0b9400c400100341e500a8070b0008a094407900541d2042c1d1000c45e003140420340320400c10309500d03402081c000003412004d5403000d1100895000034030038400505800d01c40c4001d40003148103102c00d540b0030600790344010021590358030810280c0a84804414808003400307400040020030341014041d8201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312932284 1250 312931034 312931039
    0x705060403121812030c020a05040e0d0815060c0109050c0a080d031a030303070215011a1c0b031903020f070e040818040c050306030d0e0102100e011b0908070602010209 74
    0x1015a800c00e04441c1d0009000c58043e240c05140c0b00020b07030a0b100c180c5210440d0196950344440c201034014060300c000203a10460055140c8071702156061000705541c4170140041c41c0151441e2103002603580340e04a9442c0840d4060360000340304003420300547c04024064450001d840441c0c6500080222486d110321a58100d40c00041d04003c0e83c61195001940301c00e1f071040c001d12100e445901207440c5030411034448000d680060352074280605100e107094014080c00000e00c1c031032404140f40c0501e6001c0c96408076500d65000c0e094140040450f0802c82003410044c08807a0000d8483e00807511184c56101e080e1301501548103484d007806008101c0405452203210114a00d44581d65080400d5114082034000042003400c1c5410503692401101d20a00d81c1d5622107480f0f00b4903900b014140740c444600901884041001034000d42d8000c2a084401440c10400050340d550710481107014003c5c10031070740003030403000d001c09004d140c0041c410000d0340d81201c00c807110651070b102c05038200d228501e034866 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312933534 1250 312932284 312932303
    0xc080301060309052406120102131a09090a02041e030c060e03030c03030106050403030318030807120209060c0d03060e151009150207060e010c0b04140c100f020705060403 75
    0x207000d01a40014003003d2141e030850f01c028001104080710440000100b440d500034003800e1003614644641e003d000420210000c501e4111000c5107030b05554118440c2c2c980190b8000c110112078400c0e036050300c0c60404003800b80d07010380c90003e00c1c9000951050084541a18111002030364624001201d40d040c0e9500112041c1c44504080303003569507100100002d81c0c07600c0200f00d01c03028000e00b80095802008152107560310b603800c515000e0140d0781c013810f201d0f032003400300802000030079803107400c1d603802800d00d003008100d210401003e50061301c94440c41d85e1b0010f40001e14500300080000382241e45118a0390100442c5846201c0701800310000c1d0b40e9100c5042d00004e03000010300c0c0c1007070040099580d50410801881d0384100b05003400020004c20b40c05604504010000246c220408054585007440c19514004a0723580d0f80402100c0a80040d09560742000314170f403012402c0000701d09000e001455032650388420500205171448410800b0014041c1c110001000d05003501594260380d4001400c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312934784 1250 312933534 312933539
    0x60905161712070501022106010912150509070f0e040c17030304060e0309041103100602010507020a060b0d0506040b0405010c0302040b0706020703021609060e0603070503211c050a0506010c080301 86
    0x8040a40000c0e03c1501c440d50b081000310200c10820780c41c07403c115010081074a41345000c0d0005840c80400e60700a1000b080c08046842c002220012001450b40c019071001680344c81c2c860015180c401107400103089042c52550220b161140d12151501c01e61250118007460390715620082e00f06140c0550950441e40184040350024416030050891625000200d134203003070b4030307500090641e800341c904107031014800814800c050700c0c400e10b241d0140646000910441c1441a002075407201c1110700a0079003039450b06c03214842c0d600d07a80c08018081e000422250707103061504004070740f040c090713500b15503540ca4030b40d581000c64064000d480131612011420f40c1880070329103612001c0d5100410840460103030324401703550307107560414110103011411000241d96081c4800d0308820305010b05498803a43c084001040541c1d00080c00c0c01846282482d0011200640005047da60013012114110382040000382d4001c6510f55001d24071482c42018148100c0e119540191650075243c1c0000c0c1c189041000103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312936034 1250 312934784 312934813
    0x3060510201006230402041a160807060e011b020615010c061b110a0b0612010e010f0506030d08010e04022707230307140306010c0b090a030f0203040b0d05130609051617 74
    0x12701b030317104050710a0070a003851b142d03204559079200d401d0441d03007a075850116064100c024840d03552080d8001016042d03c0c0071001c000b0395240b9008144a0303010525031a26080d41e40700b2041030a40355800785d0184020142010101c01b440d54140078080042d6413038444519640001402c81c0c4143d8101203510420b480328020b1014940b11400380c00655920f0b050400c82d140c209204680d0812030752200001c1c4c1e41414002c060a049d040204002008000c2006010007182c8602d040e4002d6030480f04e50350030380c0d1410743c811203907808128000c009000071410042c28981003140c106102e0705001584240d50034400340503150f40000d03101000080d142000c0c9120b001c0e1014001d640004050502c0204620182da034040024804c40f04c21801e60031900c03c20041541040007950104418009941403509152100e00c0714011284140c88080c0c0703440100340c01d640c040a60a14503500b18600b8440500181031041d91402c0a0b225501c0d403c0800100081031310190b1150000300c01064081e20020102111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312937284 1250 312936034 312936037
    0x160215070909091e03020a140c010509120a0209010303050a17190f0605030d0c020414311e05100c05090906060904091203060510201006230402041a 65
    0x2120140c500700e07401300600740240c01c0100c6443c460b034002c2500c80401d19240200c040768200c01051030f80020804050740e80c0101c10395032003800941c4c20750080c10060708918a411007032203020350408003000c0003205140c0d106000700b800104a0310790362108035281c2c1c95600d81003401c4620f034100000d031001d211380e90000d5411120740c003103601c0400f0130099240c400003400c104401c007480d00400c80000c82102141020b0045c06100c500211400790145090142d40c1200240080304052402e0b03104d80014400032001096502c858100340900d410000c6010b80c540400030b89030b0f050b6034034490340c0090103080708a801034103401d40d0a903440340e0818078248240030001740041e0989a00070070910100c02a03848501c0b13070034003a0740600d00c1c0c013400e42e02150300542200c6140e00400d01402501d407000a0715a00002e10b401c82080403541645840c0c54201e01c1c43c20680c07940007034a6164242023001540810b02c50b080b49408000200d081950104a01000200d1286125424101c1c500400c9034007140600300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312938534 1250 312937284 312937301
    0x402010c0809120303090a05120a0522091a0306091c18050306160f08010509061c02090f0709080703020a21150504120c020d0206030601050f03160215070909 69
    0x2007140d5030700410010000d00b590070869486c5035a51007010000140002000050090010b0844040c80c0c5090801d00230718a2003030700700000c10340c06000da0a82c0620400e402c1c2e40b0050a16200401486040b14041c0a40c1d18149840714803902c190b1020611030880841c91841090075200c00b61002c507421481607a17001d544044c009408600d2000029980d18140640d81c461907203041e8032400d108514030040c1401c412210b61034200000380c001440700340c4804564540010044440b16002c01441c04020b84070490302100a411034040814040350710030006880b8080d50103500c440c5440d40c0c51b40801951a4020721002e03505c20725800b81042800c417802241c1d015a4800b100c07404803100f1507114250000580ca001d048680e5690341088144200284001a4110745242c011030341c00168001985002c0141b0020344103403000030104103281e01400459103800c03240e03412030b41c072498015465410040c0c0301c080b0b240580074980044240700e2441c43c485125030529210080d00500382070300c030700041840d50b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312939784 1250 312938534 312938539
    0xb03010203070e300321090a1b12110a140105071506080d020d02070f06051c150b0309061315090c050402070b060a08160608061804030f170402010c0809 67
    0x702010b0401001c481e00007004107104d80003183d542d6407030380d50109100381c51401501001c03c00818044800d81c00b0a000f03800359042050040301c48007000100444428581c0884115410f92184404004004464502c004400c440c0700c109181d813410440c1e810403075400c0190025078100a810f0000710401c40c00401003082e10800102107445070285031070040091800310160b4080c0442c480d085604015031005008038034801421249044409002409038095507500c0c030340380c9403020f01100b0032036101410082c024006a070903a5a03c102c1c080d043c2d441910b4210440c0103100000c0ca020752213080300d08030b841d0700c05d115959101085040a00034175682c80211440c50040000140d5a940c600241c03d400d80540c41d181d145003008801c11486410603070180304030390000000760031420240407880302100c009007041445556401c3c0014058004140a4107805140b5810310061550280c410611050705880740441d02291213030100b152182110001e00292a00c01d01400003508000a8000000302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312941034 1250 312939784 312939829
    0x10302030c1c020c06044205150319060605061218010902040f140702070b0a0518040f0606141201030f06090b040b19060b121308130303030b03010203070e 68
    0x1001060a080b0103540c00d60b04a041d100da810354200300d0145081259241b4240d420070605018040c007203201407c2c00072511503903100e0000302c5010780c0306281403000314020705842c42825402d0110382052440342c01901c00070300c0c0520120303103403c0c44c804454a0300804200c0000c250794440041c80c1010b864152032600c1c1d5201da951000503102c4d802561480e01c0d80c00380100708045403100c81c82c0c0d008402401c00c1c08551068004004e01000380d422074000c0703803140c6001d40e83c03218140c5114044080d41e01c03106030414540342c8000d03c680c00c1d5a000506031001d81d501c9180b29081c2c3d12243c4414001c8000000301c528285004100180d612495040910b218160200d0200a0f60b143d4001802c81200c0c1521403009207004c00540c2614940c9a00139100050410044141015083d00b002e014541154100c1ca003a280030a01240012602c43c040583c000d03002a654004100c0a801c4034200d840118042400c3c407005500340c1c901802078a00c6000e0700d94981b0a60721840c810816114008520f090001d02c1307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312942284 1250 312941034 312941047
    0x140f01110105010603020d0b04020304020d080901200304210812040c170c030c060a0206060d26090f0a0302010c0f0c09060801061a03090d0e181503010605010302030c1c02 75
    0x1000c2c0102c2c1c0c0201825140142c81d82d0305400c0715015240d983c1111442507104004000040e5030b440b0b9040c983c44d400144054a9201190058654505d05501800350990251606210100010041003640c003801054203035980c4400440302d4603111b002008126507418060a00c41c005152201540140903004040010390344043d40b0212f188848864810360b00001e400b40101d0408110745610100203841480c50000d08100003920380030040c1055101d104410003010078866002d8503102d080001450b002c0c1c0303400500b040004203604c4030030f040d030003081f81d403141e00d0040c501441705608498060b1144c4101d10000d5071b07040510103502d10b080311300020a04000c13136030000c2072040c403010b49100000011a5820908244604040440c01c090f50450820411903408000b16031907070038040074241840d2440c03a80000883e1040b18070031031f103540c1058804016540c00c450200201c210340a030000c000150300c41c4011000d91100701c2c1c403010410700400503034562010035042201d02c00c8030307035074010304044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312943534 1250 312942284 312942317
    0x61303110c120102090f01140706021c0c020601060807080103020a060302090d12020c030c0d0f230a0c0e06040507140903030408010f15150207030818030106031b09020301140f01 78
    0x400b442c0303030802a07980450641c440382407941c01a89501800d003007241582d40c41444449151050031002840c00d600862254100e42d951010542c4540800f4000d01c07000e041281c00950b251001d214940024000070086070b8024010401181a25000b07031040c00c1d00f5003860380c150007039481402c0300c503000032036400c440c0b0100340a414132200d15081a400381088404013002c061800080d01c03000d40c480c10026102c00c000800403030300f091030b01303610040c10194440d0000d110340d00c02c0c030050704c02d0301c0d940103d03007002c0d040008088240087e01c10000d81c071100c0c0c0d01d4450512003200e2089604d00040307400d455010188801c0100030303102c1c411000b400c49140544131000e40e400d40d01d2074801e28200fa41c03100c80059020705180c1c103600290200074501121040504802540c4200c0e030b1001410303142e0000352024901d083d240c0c1c01003070640090001c1c05216600e190000c800d0b10a031081082030404c00201242018250007281c1c100d40d90422541d000ea80f01104001c2218180d100300c9060002011a459440707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312944784 1250 312943534 312943549
    0x601020606090423030c010f0204050d060c051210030309060806011d030a0c0305070e090a1205090111031c0c0c02030a020f010201060e0108060402190e040f05190807060e061303110c 80
    0x82c06000085c1d40c0310069228101d00351103003000301007000c03801481305010980b00c80c41c03a030419039004107000c280d0100d14081a40c1501c2010320000d4107580b090304004160b00d40c401b01c903045074444d586402113699102c900311403810040d52114005520030320784000035440c0c88900b0b03030300080041c1a1030140c003407540c40d10351588260344103d500381c102c80300400c00100c0091405900001180c040d00f8911507a540f030358155622103080406000c0e0114512819910500000000b44041821a65180c10301c00184c1c00074010064030382d124500f040304184010780700c3d0280602056010300285000b0555901300102c00d0741c50380c0c1180c1150b5980b840041d050400c500000c1c02828000c0280c581800c2c90700500001c0f03008904510410380200e501000904903a48055602c03540183c00c0c012500c4031490141e04008105c6054802c0007000c015420a20402c07034010094071748034a01c100031030f194401c2d403180c0b07520044400100106851150b080844e0107104025055104542901c040c1216040000e511 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312946034 1250 312944784 312944843
    0x12090215121b0703171302060d0920030c09041406010e0709080a15020705010b060324030f061b091c060c1403010909031e030213090506010206060904 66
    0xd40c001d2024000c0e02070320420000410140801041e10780030440e1009003200c1c0403000380320b200c010b825002900005000c00315040c0c10354001c06140e81d9501105100024119602060f076000701c841e400365101402c180c1c0300c16140340b00900503003c10740c1d101081112000c00100306660242440e040b091165400740302c2c10303010342458040f4210034204254014480c0d10b0a0b041600c0e02c1d40400d529101088107000c0454078400b00860161f41e0f084c032882c10a01420002828681010010050110400f04010f0961000c00744010340b030011142b0b001019a10807410004200603081100400d00103603111050076400d03440d08280030314004c0c0c00d002040304464440c0041d108102000c12110400c6894044c90121400600c0d160082c01d40701b0146d0034291106200da04215552000c80b5002c15004a2034054110f00c600016082c9014a05014001c0d42c011441590511212503020462204900c10640a0103042c2d00500069881c4414003a840d00d02901c107951403003880c146150801c04458580b20b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312947284 1250 312946034 312946057
    0x1119020112150e0a02070b0105120f010c0906020d03090b0a0b01090807060302030601030e030a0f120609050a20040f03081312060c02100b01021002070303021b01061401030b0112090215 81
    0x8262800415002d2180003a04121140d4010466040481c110062071810340307208a0720ac0c064600d200f1561454088448015a281c0d404d00d4522400c46810483c2d540c104d41d1982c0a654400c01201800c508450002000500d100300410116040c00e021b5484440f0076403041c101880e000c1c5d00c64406620702503c0c0d602040002e80c00004100955906001c0c5552200c0d6100085042800522010f081c4400701417242081140101c42554070700d080e034010f500189412003007042581000705c002400342c107050b0960641c1c007150500ca590050b40500880d021601c0000138401070500303541e07a00300554460b41c5042c80480501401003141e42c0c1c0c050a02080034814000022800b502e100d000e410003951540e1080014078040e201c11460340c0102e20301c8003080c40c0610040e61020f003441c081d0000c0c080c0e551600d81c40905010048407642d0154002d4003500c0c2d003041e1010002040c50011026203401c2d0004900185d004800d100784503400303400c103082061004000c12074005d00b001c02852190000f0703007040d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312948534 1250 312947284 312947321
    0x30f0703030c0c0203060402010305060402191d09010b0307080c09060c0a0b060301060b040608220302100e030f09040902031c051b0303010605220506070c0303030c1119020112 77
    0x108264142c820b004010049092190f484580e5800190b29000c0091000e818075440c0c1000490540d5030f079044a00041012091581884100500524810050b5124552095600642c4c68245000c9000c41d040b07504011180b861a5155681200c40c0c5c8806028031440705014400a4115643e07480900000d000d42d400802080c40607040c01d050b85200a01528000d915200060000b41030880840b401c0d91070904060100c0d4507640003c0280803104c10909500c61b0483c2200003c1540c08181d5007501c80c100d5409104850030f403c0c0042d128407903800070a0150034100103613800c0d0b0500741c104902150005081d28591515407c2c030f486080702170700000000920028911446d4028030803034401d80043e0700011402d42d0b0400302e010f4468850b080b0b9980003103e020b140404490064019500542805404140c5500f401d181c0b84000c2003003800203d011905040980004074444c103290124200b80c0c100800c00140d5101c2041d650041d10507040e41000000d1403d500100040d00660003807c1d459034204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312949640 1106 312948534 312948547
    0x1903090503010515130605090115110d030b032401030204020304021c080702040c08150111010e06150a0b040b0d1a09100e07020a08030c0912030f 64
    0x1d074990300b08810041d14030051103d41d105100c007500c101070074090100c3c0761006e8410078041e0a402090340401000825850f640c82100c140b403c0c184501001010317139005042040d240f249070701007038030750858203030905040000101d91000240c0c60b5100c2c10350301c0b548908030345040c403000c0d12868000c8041410756a07509240d40c5403051481e0514541001c61a010703402d900181d500345d120368508000400380c1d9014582d0644550403181c030301c0c507034807036a18010343c0e0012582c00e0080c1903641e1038407280e0f42d07d281006100d0040d0000703a40440c2c6481040d00f00300807074007680c000428035203003880304006201d11103056482a600c3e082d00414224201b01d4104007200d41d42e0007903a40140c1c4901408880b030241403003d01a00c000c54940111070361525816a0f40320780581c00240056400c0000502c00c803403101c05840e00c00e400030124485006c0f048041440c640001c00c01965100e40002d04 = true := by decide +kernel

theorem cover : BRFrame.Cov 312769784 312949640 := by
  have h0 := BRFrame.cov_init 312769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312769784 ≤ n) (h2 : n < 312949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
