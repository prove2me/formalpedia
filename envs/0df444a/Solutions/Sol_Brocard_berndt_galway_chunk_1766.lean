-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:35:56.483015+00:00
-- url     : https://prove2.me/submissions/2d3e72eb-f311-4a11-998e-eee80a2bd9ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317446043 ≤ n < 317625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317447293 1250 317446043 317446079
    0x524010201092111072c04050a080c10050412091d010308070201090902030c041a1222051e0c011107050114090918010c1803060b0d0506040506060a 65
    0x124480a4550341d0003040e080300d02990280e00307104c01c407998201d20000511445010b44540002d4240021817840404480002e00341c50b40c0c002080e41086c080407130400122034241640c003400036039881480000341401c21422605540119091605002c100712960b081e681d070240e4290381d224403aa45d681d0703032444001800c9200c000100240c80040c00410031503c005c0201500606002003c0d9a8500c510070483c0e20886010b485e03100c011405220032015080141c495159408016003018510401c2c40e410340400340045107100f8000300e0402e05150b54603040713490213400c107059803909010420040b0300e4a402d40c059140c2802480700d06540380d07000d00c42c4912010b009400900190781083d00651701070344006401c1e150702d00288807012840d5102481e00c0d00c5115020141081c01032600002429115480120b80500120710804420035003005d0042d404c481c2c00200104483d070320b41011848040c01c000300640f40340a213200f0481401030010b1b107140990805d0380c800c08021707519a907600c41c03403c0c019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317448543 1250 317447293 317447303
    0x150d1109060a05090f04060207140102031b0c03090f0a12050a050d030e0304060507051e0c1302091e040216030f0207080303040b0c0c120c010b091f05130906052401020109 75
    0x170410082a1680f841d50040c810f00b001890f0120a80760b843d5850000c1424550780d03900003080112003510003000c104852015226941441907440940d42c90740140e0b0b12090041209401c0b0070215a241c0700100001c1c007100c0701400d040b4045050031621120300030000d8800780301e56a000d0140318841c3c0b0848401e885404050340c2800d0a00b03404690543c0104810740d81c510401d01200c1c002811004240703508000d280c01002c44005040030b00000c003044c0300f48a02c8051045c803c499040d101c035030f81c061200910040d034500e4120410001402801907803a129440141c45004800301500180705400c58000e54085600301707a034482520f90f4a04c0202c0e8000c28030118807000ca00c0e003920280180503048038010907100910f080074000e42c00c0e43c0006001491580d19050f0a05190504440d050b81180c07840b1800503001c118806201d41001061181074015040500700445181c107076400110505c1d4810030500990500c28008034954512241d000804040c40c40c161141d51700520410001580c4030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317449793 1250 317448543 317448559
    0x108090703020a090209090c12131b06170f0c040b0706110301030305090a080a0807020618030f01020301060906080115050307021f02071103010221070504050a0b0408070f1d150d1109060a05 83
    0x803079100c9410300ac0450b003c4070100395182e0b5180b04000400100405003070035039140081910220600c0100c1a40900741e461451900c0080c071905442000c1114141c41c403000d04913030f032212140390690040c4042c1c92606101c290110020080660240081498020448224884a07250a011078880078030400c01448610200203070700040c185a4040c262011040001402d031100d108040303800d2200c2115004000c1e5030000052048075003142e0035034080c2040b40382419056041059070908500320011a00030b01c4800702c002440c84e07108000202810041640c251610107000b03005402940002e401100e088845607044001400c0c140b0035900d00014001c42101d032070300711071405409400d025003213404005003000b002c20180c54102440c0020030f91000f01035036580ca062802801d10300b254201c006414503e040810a01d5001400c0c0d00380410150303003180164541d6104420307406095552242c0005035143c1090034055005420156080c00b5a16041c150b5038000030090180807a028042c1e200303241c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317451043 1250 317449793 317449801
    0xa02070323120a08011a1b06040201021e1203100b04030309050103050708070813020f0d0f11030705060d020a020c04060b0d05010b0f04090b1206090f0c0910050108090703020a090209090c12 83
    0x245aa1201b54600c0703a1142c501017000d1010f80c8240306e00c45054800d50310200c10b000455a0401c0000b44103c685a130002d01c4040f080445520340149505901800d00007202264130b080c1c60004510040406140042e81c40707030f4030303e000303031496905101d1039021903e488009461031380100351951240314240d8940c01d0f140d50b0240d080380392030303509603051340c208240905100540c0c559142e8200250300901da8035900c000c84e0704d417412300081d4003080c450198101c102c04008036111034040e11010b42400c18050b0300d81c104500101d01d4140d290304d25a074880e0a040300003400300468002404522480384061180341e8035020000301c01e109041d003580c084c401c03c01041101a5550340184100b520007040f00180507218008246088001e5401ca90650803003030b0f171080440b03000c0140c924100b1081ea40b0743c6013840c0c04003441524100303901c07a043c1880400c4002079075620061001b40c016540c01400148110b0312250058025042a9001390194020402107031600c405030f000e81e121024900902d03905c03640c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317452293 1250 317451043 317451059
    0xf050304080a090f09020d0b043602061611120706030b010c0804080c03100e19020d0c0b0c07050a08060a09151a011202090904080a02070323120a0801 66
    0x84441440030030003c100c900400c0c401c6030141c01000400000d071015031100d040800783c90899048554403486245440440f84901502411090500c0e10700d2691262650060b02c688500c0d0360781c4200254071090014110007145404900c110101d0b0142e441041c0300100d1a00f4031400003c41400d002c42a8440b40d0f00b001014800c0d0005102d08a06240542003002d084c0c2e1100384039002504804480c5c0c00174803542007a8102003242c03c044100c5c03100103000380103680344801c1e1900d850b005580d0690244100c80f005544503080103601060b0f10102c03406196564544210396074009231220b2110740210300c0c00240610f841c1301c82c8000e4441c604081e212645a00020000400e02014200c1d594a1041c0203020306c50080c1c40f0320344080600088041e0315002086c00185200c000c502e4682803a03105011064854a881c4a1142d0050344002d0785692085540c1c01a072508240c2e510040c2500c0b211013881c03000402461030140c640c1e4210040f902401380300d580c061840d00404040030001020303031004021030b074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317453543 1250 317452293 317452297
    0x1e130b01030b0c0f180906060418020306060c0d0c0b0601020a03021507141303020301050a06031e03120c030605030f03190f050d020403060506150f040515090a030f0c060f05030408 79
    0x107520b05901450044013401c0c044044c1c000c9188081041201181c1c60121b08200008a510a00850321145000c4c10701d40d8022441503a5201c00c2100c50b80400083d078161102812207051070850011100e094100960003011a034104104560780410800811682d500010b0041d00b1103506030080c25071144200e40c044c220840003401c040400c101e0707054040200c2e01400081c440380030000c090410450550044c9801d4410261104159514106081010441d020700301c0300e9102038540c81c501c42c80341d9818110784228013112031308851441d00b41a2203000d505035024804541c0c0030340c15106c005801d594896143e01500d00d80a4068610400d00f20706035215140c203040b60042800d0150600341440f15440480e00140c20840d4107560394414014686490501c0d0a0740209048280b40782c405c1c5100303400c182d0b010780c0c4215805810b4041a0b04444912130081c1d45001d900070300701442690340d90610012503606800140e4410034038180203c0d90521030201c002000345030742c03902407642d2500e81c0e406c4416 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317454793 1250 317453543 317453551
    0x90e070b0f07020d06150303080708090307081c0902060c031308010b03030306090702210c0f1c0e0a030f0c031b030201020d0507150e012403020d030309080d02031e130b01030b 77
    0x103199101d103204252261b250714103000c3c50007565080054036011001904007100500118001d6100b4002302d00013071590001c81e1005104600d45005440c0c91100714009420003030002940001c0105286d44034100c00000f1307108100785540c2c90320300740e0380d924481c0342210307401d88005030182c2080001544506000308002d403c00041c4c4102c1d03440000840e03421425182c030002600540ca000500c1101c180010081702e82c1049010000e0324514100340d80915100700c02c541d10506100355409021665526001ea9100860b001541603a8110407440c00f0103021407a40030890300d0002c40b603203034044412010540da058a44c1030300240060040303903200b6107460300031950440d40701e280c17000c114402803828020003c85032645400441d0141210312440640d9900c0d41f8a094995110001080542d5034050302041264060038005841d202d0742c18421114031030b00c3ca131100c0060000ac14041292042000001039164403007a011064a484c41c8036100d060b8035403009444220b050f801480856881030703940e504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317456043 1250 317454793 317454803
    0x20301210c1e0e0705031e130f0506090114090307020f220b030d03092406030b100e0609190b01050c0d050d06170304032a090e070b0f07020d 62
    0x70380c1d036440808030550100b20300d50072400810881c0030440c1d601c2030b081494000d00c03582095401c500d0181581e0b8005084181542100d03503d41000c514840007483c0d040d000c10307801040c00800b0000b5400c10380e507a0501614802807541ca4401c009494400340d100c06030103401c60001543c07511250f5000c0060a06c42c141e00f25911015220342141605601c007030205204081502c007140050f04c0508150a018002c074440c0300381030a10a03031200184040c0c54400c110388610300702c00c2101d82c01d085500c0c01070400c2c0d04000d0900e90001e050040602543d0319a00858015a29281c1d80fa41c03200140401c044045c0e410054005601484000510381d0307402125084d0011f14000b81003d015011842c906140e12603800d0200318002907081203882c0324090440540302c5140c071006001c1420b03103040e99034070a40c1310145c02c03d0005a0105290450301440c6d0100b0710054004000c496180d240e840020248000701003800d118002c1c0000310b400c03031070042d036a0036012121000d00b4960143c007802200d104108048034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317457293 1250 317456043 317456063
    0x1e050d0b1b0c01091101020105190e0307020904140106060912031b02062a06070905151c1e0504150207110424060207050a0501140903060a0f0f02030121 67
    0x400d0540740080c181404071903001241503581d078100480c04215100050741164141000c010740c44030340c071040489482243c0360001c1c44a01490304a41140181030000b54004c400400744814040784100c10544400410b000308911030342e40c0d20642c0c440c2d1440c42421481c101c42d512400100c0c0c0070f620005041848107480f1080d66601c0d60008145034082d920754404054251401200384405202006204030400000c000900306580c010301041050f03c2800c2c0b003180d519500784045812102a0754004400a011070020381c402c00007280038040d45120001ea103400101440075035800c9004817030250b600882c0c520049500428804003a511403002903800d210f1052246c406511144503d940042d0380c19045540081442c0a110446c8820303440002194400581401259540d07a0068100ca01c2420802c5500605807003400e0b850041181265142c083c060400c640c004868014002004040100300403882d01c07041e15130100d01082c05480004ca40016800001c15a9405101c03d45402121065 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317458543 1250 317457293 317457331
    0x4060204331d03010f0c03150503120714070303030b0114030f01050906060408120307110a030206070302070f020904120305011d16020109200405071e0c1103070f1e050d0b 75
    0x1e017900e42d404980c164150350307451a4003120b51f06205002049120141c0607115034a0000000d0341c5062100c9020740801323000400c00200700d10200351b44610241c5100342c5501a503282006001000080382c041c1c0418050440c124188108004407846038610340e580020300e90a003070501410341d50051925411000070840030484410411202c03058400700d140f02d699070b1038100d90003010740c0d410040b45040341d400f00c003000c00000d80200c3e500d94007030850324005807a40b006040440b41082030401c0070b0f4008000382e040c04184140c48800d10801846d17500d05120a0f660340c850104002c6260107481840411136011034042c201ca0110390501042600c000b10f5102c0c1243c41d10050002c1c405034844d08013003a8681d9000c54107003030103441d5000103d428919001048442d40c6101c45441d02400420000314440c05000c00085100001100c1009001c42d1040b9440c2c071a05d4035601e07558000c2070504000701102c0c0c0c003180800c014000603590080c14191702e880051380c0e47d90700fa0300003070480647e15010b00e00d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317459793 1250 317458543 317458549
    0x6040b07110106080c1c0201140306010302040902180316140d050f0d11010b09010b0406050c100f02090406050a0b041505123d12020a08010504060204331d 68
    0x341c004e0080c510242500d1459501004800b44000100402070750b040c0000502603038119120145482c0444039441da603542d41270040300203210b540c014440036403000c0340e0320349030612262100c00b1410003503007101ca00a2105400c041c080c0c24901c00d010109a003006d100c6050309040a0095181d48500e0031101000d5060321994280070400c44c039000000c00c01c1c942c02980042c24010b402c548001954000015414611003c50354801c80c080c1a080c08400103c44030300e031000b0001d1640201c40c1c000c08110301d155a1100d4070195100450981c45942490004075980c0307803001c012000c5440c14410140741c58540301c0c04000c42a03e10324103c052042c207001d041c82d0a148082005d102d02000710742030004804d24001c40303001404161061070419060b10a540d00c240041d0007000940340d170a002101441010320004400b00056085100e0550a14060100704005500a4800e0302c1402c00c001705030342480c01c0542d6078104a142c00440030208401c00c2e090842c010001a64242c05030341c02014903403210004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 317461043 1250 317459793 317459801
    0x40f02190206070f03020c0d08041a0c0d06170d18080a0c0518101802090303270303071104020d06030519030905030102090d0809040b090f0907050d0506040b071101 72
    0x803500560000c0d0108108079601071040c58030f8100c039003402c500701901c9000007a500c4110230300070800e000407032022405011801c04154440040c800b0305030f400340b50107280119581c009904000741d0a08001022801961100c0805840381d180c00052040c243c406100b240d450244240304030035400d0340e103400714038000244800042e20380100c90404c041c900e04402d018940b2034000c010b000c0c4003513403030600001c01c0c0040c030113204813031001000c85003442c8000ca902e402840364800642d4948000210356484030070191603061000707103405518182d49244010f16450780f190040003070401a815240c0c03036071407415038082c1c410551403110000b000398807551400c1c034020392007140a01800c4003103049000c055020640c1005000194000d508148946011801480b44244014402900420380c401070f03844540c000081c512004008041a05000070440d03848007098031041d0140c040c41102081da03060000208126540c06030040c54280e4954803920003019014000b8001c020100d2500c45650000340a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 317462293 1250 317461043 317461087
    0x3090503070b0c0607091409040501150801051e010e1306090213092001020a0b2e03110307030c0918120e0909060c030c03070c0804180f0911040f02 65
    0x30069a43d401040d90345403074004001c0218040110040c401c2c4000c0b01d400420300009401036800782115150ba107030440c058451b8514151401001c1c000000c0c0c1030805412444c066001410040350a40c22404c200740d10450901800b01d20074050320214070080510030141221601400300060408503641c0094640940085d650481a844a444000f80300c00c003419200790090003c00040200c4070314002079201c032929100074085004d2000028010611680c80492512400042036010070440000d42c89210003400260342002680390079010900300000c0c8103081c2c1c1d030071640202026103442c000c00c01800b2010308031a200000c41c0301800018400300c201425001c030036120340072684160824420303011070007028503200780c0c010340902c0b2034a239581c0110b82d0040140d200256480d80c9071141594403d1800308020102440010000303201030343c55800030240c0c85408401d0107551800700c4c21106940340c680d030240c0f19030003034443c00135140707002d80c8103411038a08a1009400d19800c0c0c0700804c10061034807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 317463543 1250 317462293 317462309
    0x90e0a02160803150a0311010c02060909070c0c0b0306010c171e03011d0408090d020111060403031a1002100b0f09010f030c08030f2506150e01060903031b0309050307 73
    0x4014043c0c20000900350740c603c1c0300c1c20385d0343e80300c0c16240d600d40d029005150b5140506018440c070030b030b009648a100031142e501c500904803a03120b0070f0200000b8031146040c0c00980d030712404020045042074407201103e001340c41c160344000f42d660264580c0400080d01e80c18440008408200030205000c04100e050000d900c0c20031561340341d6240c40044060b400c0c0c0812000841d510107410000000d4051040d1034088130f041c0d071500d1100c040e81c4016140400c0511044020f441404100030401d5403580114810804da05406032000060390244410070700e40e1111107025070410f042c40540204c0c03650001c00c05100c01864502100d108002123680c490007038002c07640304042440d040c0107120500115100420004c001540742c06860f80c48021a4000c8180c3d0707c152401150000c0e010104861502c0d548903000318003080440c07140f9450515600a51041c160010751030740000581c0da00031007224040f07e400da1520321021010400c43c00725020300301000c409002d002e44020442c1e072010420400904240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 317464793 1250 317463543 317463547
    0x60103020d0e011a100c111203040801051f120b090c1302071a10030b0402031507020307050106080f15060d050307031205130c05010c140d0918050106090e0a021608 72
    0x39540213580040790340f001070040c00045504045140d11403500c2d80080d40120f070381d007522a2100700055446103070013940d0780c042c03001180c045100c12065103c24082c034204c0d558440c54045800d012560700d9a98499402500700304809800444c80013480c10754040340c4042035071155082c050015106800d03080d140c6002c25408640c0f0301c200030710300c0790030b036005400e1203084207007481c10309143d282414041c0801403c9148410110f01151010400003816007460341d50035040c2d2403d010000c1d136a801940e0301307552030340c08c00c1400a00300340d002c200d00320482580c0000d00790040140041c09103006000c4d00030350b0010a060035000c082001840a0000740b032096850720291401c00100c031007a100c000c1e01d06802c20340c800010f6400540c24168034011121300382000350003100036040200210803100701d400040d004141c2104100c42e8021622416542d80840c1c8003c40180400003504940003405400c01040b550300c030520102c800c1084048c0d01280c400c2c401742c6010200800340c8141184404125011480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 317466043 1250 317464793 317464811
    0x803150112182003071a040308030c09130908090d02030a0b071707030c0203070b28021c140411060408030a030203060f040924180b180601060f08060103020d0e01 71
    0x35840c8034285001030407240d90301c00040743c0004c2c0d115641c2d88a110107640c0d803205d0001010302081d06a50081d42c110105c0c60701e92500d4088084240e000703001c524403502c01100040d40803146882243e69064000d040c1c1d40c01e0a02032014171180b10303190b0405a0b0b25104030720403000020200d1001070f04c030300400e40d03c04860f14ac0c04003400d040300c0b60150a1300c0a240c100f40080d0a80381d400016100030540003c6488234945401d0312042d494048005200b820060501030414911003540041010892207661001c44402051a0004466516a401c140110403001040201d10903100610758010010456403410756940035042c5503510101910001c81d402104202407840c2013071070600c2010741590180700c040c6150f0740310940d07031003030403c02c4032040c5070b202c030b00ca200210326841103000004800c45084810040d050601880e10100c50711455141c030034980001d140c80200310141244e5180e1070300c054038134504000781c441c060f004240504255003400710b03207040034580c0039441610090b03900000b08800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 317467293 1250 317466043 317466053
    0xf090a020a030c08040312051005030a03020c0a0519260a030201050109060522050c04050303180301060b1c020903192103020406050409020906070c180b0409080315011218 75
    0xb8410071960140300804c42040086900008034000080c1040c80c0007400d9910340b951900106c02d5a00803030307014071614019030101a0002035290800b1012106020400e940e141004424001e040c40207209c450b60b20000c00c0540b10904041d8004c004c1d008112030b480c030b002005585040000d20701980180c1d11100100324010803481440003800c001d48e80000c0b2000381011001100400f803800c1031085689100144e541c020b60310a0324090301c4000d0649603503007441071000e809645910300141c1719520b04203000039103c109100312401c102e40d094010945d50494170501c002074001142036501401000d035140420b00812104d901c2162181c2026480c01042004c40f400042d80d1604032018544104410f200300d40c0c1260560f4100e407660980940e460007500042031140c011050014040f480c44040031415140c8034000f1088500d500c01c0410656152a0802080d18201d040c081c180420400106403c1c1103080c180c526500c0341810030550001400d1405401c41c1c051100520016000c5026001040b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 317468543 1250 317467293 317467301
    0xb0a0e0604030507080901171e1012080706020f1201141818070504050f01150c1208060409050d091502010203390a0305160305041703060f090a020a03 66
    0x2488002001945040c0e40e001e0802d104001c0054141720b0085459403050303100c0d08003070110f544150003400d21410b01c00341640c042c1e07030b02c0d0712241c612020300800600340704103025050080326164031814001c0401500c81c100340350321280701628190707000c10440b11645108002442009d00b401220f0b105c5624058030b05d00d50780f84100d0a00c1c410342d1561081500031103000d200366088030f110300c1502d01e5290040c44251800d0016440260018100740811010303a070f103200c03121304840b1034402d000b60411580c2d408031500c05110000030001148407031040c400522808049a220a01900c0040e5503000c1d51603051400e801d400c0c03050006104030005100712154209101e20b0b0f54072030700003507040d0304015101c0340d1505010034aa80c0101c580c031405404d800c2c00c0025000f8083c01c00310f02c0c20380e11b4044000040240c14100e6007200301000c00c58081c0003443c8a403040510940d0801c0c800c5c4042600410070700c5040d440505846d503c0b10010341810f40640e2449240d600885007101c00698031800c050000d0107031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 317469793 1250 317468543 317468561
    0x2040c0e010e0f03010e0604050a0c051002030706110c10090507050409051e1203010e0f0f040515070e04020a0e19060912082515110f0d02090306040b0a 67
    0x3006903140541266040090b0001e001400c41d18040d010203000b01090040402c00b04400c1a407007080300b48024003601254040245024001454046880390705000717690030414580d41c0143d01c2023115030081042940f084d0021a80712002629001c515030040d46042c14806440704810781d21402d4900b0440c2c1004035a004000c103132801e011080c800e0f2030300c60311016201c0f401c241030741c12226000c032040d03c103111001e001d032a2000e10076180c0d6120b803900328840304200c2c0c10403001d40000f40400c0c082141c0b008030720701c2164007000410885c2c0403080704c1800d80d5000b41c40c280501080100703003401503030b8500182a12089581d40c6400d00d448800c20001c0c0303080141c003140005025040d007401110303801041d190540ea00c1242c207000d040784514201240c0c0c80750200500c18400080032180c05805090000b1850f80c0c01140c8892080103944012412180705241f1406130407800c201c5c400490840202601d1400840d02005051403112004a401c02400326003c54120340c1c22400c0010a0346c4034030030410b107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 317471043 1250 317469793 317469797
    0x32d0103140f1c1101020904060b0403062702010f0e06030a020909151c030c020a12060b0f090105010c061d0a050706021f0506031c02030a1205040b0a0908040905040f02040c 76
    0x98901e69140c0f0480c01c460041051003003284861411403549001d40440c0d03042e60014100300f00c5280d40f203c2400705030b005070004039840740c00c0a41c280c1c042a9440303e5007a21800080c00c0d510340b41502d6006580301031100710b60750280300da50004010607917107060285101d80380f12031025a403004c005080005610b00101541002c42d5600c0403180d031b5482d440008011a4400c5198480585082c1415a0000070b0520001d502c20710f100b0f00400c00d00d841c00d440d894a244200b0050016550300ca0801c40d44034540d196080e00004264010021584110030305009640140c1c00014601c9152002c02c0c0041e249109040807940230440d07000c100141048044024141031026101c1102000100d4150485001a080e40c0c640c4400103c3c1e000d64090216900c20348450001c01c4ad9090242030207901d9802250b030030404102451503203044144180101031166610007401140f80e42c4400f4400010410b0b01d0381030f075010b0824032000c2101c4000b03105d0305009500650180c02c070f2003154410030094030220784850003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 317472293 1250 317471043 317471053
    0x7090b03060c190203070606080706090e16050a03230106091a090607020103060815040b0a0902090a181a09070603020c100c0216120b0f010605032d0103140f 69
    0x1140301d5a40030350b242007035070b49060214a0a40f490880c914001c0000c00782a41d45000000115020001254012101d20340c980081d20b960760224000385c0001101c10000103a2070110002d041b034440c4005043c0c140c00c070300300024850012400e03000702034401500e10322014031000040c0b20703458002d0030000080248400c062104802d01682448034003c8600c014064080490340b00e0841e03000750032000c01313045034508945440141c000c040c4035080c0156000c0e94550082d001050242465000d0200619005440961035440740c00c00c00d401014024901d200b81d040700c01d54980003401c0c0030707141d50301010031918000c2c56050103540c082c18042c05600c89801d0500c10040305048120124414424102d101d00014403c03054003c1030341008080c45000c89511800f10740400e200d94030507484c5030a1390148a9160080c2d8812102030b540070028002e6402017503080c8005116059100205914624003e540504064041c11254003402c0281c1040f14503400700d00c80f038944201e08010240d201940d41000340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 317473543 1250 317472293 317472301
    0x2190e06181003032a031805040e0304050f060c0106080a12081510090b040807180c0912080d02030a050916060e130b060c0c10030c092102030a030207090b0306 70
    0x10b00c805003144030007001c0c402a840c440384501c0c1d09a5400c8005114a12141008036881c6401445240e01110720311404800709004101401c052080418525042004520346030030b0030100003d024000c1c407019440300c1d0400044580a5003030058200501d2040000d01d4080181c4c070f08000020b01c000107010401401804010440d403045010f640c034420240c4140041450300030040302ca60809811801c80080c001800007410b805c00102c010440e00100341c080b18031015000310405980400901000040d84058180300c0c5e40c944d940180360075441070701c109250000c4400350368280d800c00c440c1030110a0f5242d00304100c5160502101c54080c20781f0364290710a50a10b440a0126804207010074090048145000c7c0c41c600b150348400c1415600030074039501c40303c08600c031544d500c0c24054560b01484003070031000360442c00780c01071590540c15a147c00040c0c90030165444c228003c0710005686002e240207402015860070701003151314901907400341800d103007460060800e86c1c1c0c44406060003940140204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 317474793 1250 317473543 317473561
    0x20a0510110301030f0f051c020f030c030306090717040c03170a2001061205030306030111030f0106030218100801030c080703020d060f0618020c122502190e0618 71
    0x50f81941c2e48101506520032250504201c3e40d030111600078002d2007480640c410b03000c1020660004031000c0d41c21140188450040562240101d0b81062001e61083c408200145003001040741e10480c1031806016041c1d0810220740741c00f10955041c0c40002c80a00c1c10300a01110814400c6400b4403002c4c0b035494a40c0c55100100400c091750041581c0d603945103174040072100d0a4210720300030b00d4054034a41a5807458144544c4030741c001d8402c01e100e03605e0500c00d00f20701c903025000e903840ba01c0c240982c140c942c0e180600981c06540205c5840c2c28600f408403401001d0b0391154036101e500e000a40c0c0710a01507041d490208414080c9400181d00e039071010208000594884040c540d280b98012808100382400d03070440e6010700b001d030300404070142c2c59150651a100856000d40b1240b90700004565800748580a214124480c1e0b00a0140d041103007401002092003c110581005102034a404070354014003821421581043e0031444426003404144035461070000c04042c01004800304842c12410b10b4814 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 317476043 1250 317474793 317474797
    0xb01120c02030d0903030f1119080103050d0f090320030d050913021606060312031401050a0510090f0609061d06071e080a03020405030118020919020408070303020a051011 75
    0x140f101007616219401d04061003908510100d078040c41c1e0601102c07900d400e00540c1c5401601244c441d0022581d401e0607031502c201505c03030403030780c0180203801c15042e0000f04031400c0b0205e80400061241c0c2c00710000009410003031500701c1d1310030f1862860b442d041803400c2504100d0b40d50f112004211041c80040096590420500100c541010b030060340c8009108201480d200800809044035280000000a0058800a85034810690ba038100310b88030049450a40110b800c0c0941500502001c03410700042c02d02800901065503182001c80b034403070b079942064082802c2d5400c10000205400c00c100250360f00f100400e129039600131044003a01d140c020110b134090050a0024000000f2000c50118603d0382034000d00041d80c010507400c1c1d488040c00c00c0034000e0341c400c1c419a4042d62a101000303504510010300321208940c000d100901644030b1410315008100a111660b544503820080001c480ca070811015004502ca40c0141035030501c18181907081c40c909580300741c005c0c3c0c14844c00400000174042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 317477293 1250 317476043 317476057
    0x10806070309150b030703050d020105040b0907080619090b010b09040c0201060b0708160b01030309030c080105090d0305060111160306050708010819061404060609180c050906180403030b01120c0203 87
    0x1070001e0313001d602400191030894180c2c405042409462041c07005254190012445603005d482c400c400c0e0346801100c9070b034a03026441f49140c81e801190205111082c55040c55400a03050b041c08200154030741c50780180d504080c1e000300c2c40008001080c3c80a424540500c40c820f01560008000403441c0190803000c078030030108020400000094540c0718402c1e120021100160031031902d141640c1c482c5000751021545000c10303500220307841c0f00055280014010148142c0d10000a458404c0341c03114168044d1030080d042d21305004c42c116a505107100304000c1158040032334034500300c0d801e2543c107003c01150009002c11041068060040c03192610000b00d901c4071240c01c0e564072001c01d110f81883c40003012100017036007142c00c0900034001440710fa908000250f031680c0100f0000c0131030030040b5140402610b08010010740818104200c546400b400703256009401424802103440e890303100248408003101e048012a1740c5042c002c00315680044900360015a1a004000c606d40029010355a030044c44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 317478543 1250 317477293 317477333
    0xd140c060c0306040e030d06030302100b01200304050d060b0a050301050f010b070602090a030f05070503010606090306021c0903020a11030307031e020c03030a0207090f0501050a0e07050f12010806070309 89
    0x2c980907441d02c0e401703004240c5226007a00d484405051406001e1301440c80103400512078801030681c04005841420000c01d01611840078440305070580d031755800c5500a41015a000c18000040c0a4584500c0c841e00c0d0392080c1e200058500242e0200201d800b410340146005c0d0b131500040048c920705d800809030642d2700c18103003582c0b100c0c2c9600d0300342c000c0e01c03c040f030f500d410400741640001008805502003040070302c80c00c02d0b900d80d691110181822202d403407103078000007058400200040380081d4001c0c07401400d00000810403441001044050f40c1510404a0060f80144810024480c022540c0b00c0001d0301200a10b00d07000703a40d01c004096068030000580417a0110644031602e40c02001201d0000302c01805680d113404099034041d480b280740e80700d000c1c038440c1400e0719803042d403c0520900d416201c00515a51080c0e042c00c1c004501c41c48028081300070302a080100342c030b81c0e00d030160241003540c3c8003c04104541d1f046c10300460404034081c00c0103081c1801c041811000031034003040340281040311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 317479793 1250 317478543 317478547
    0x142d040f02220c0f0201140709090b040b040c051b010e100f23011a030c0a080408070b0c07020406080c0108010611160806090712030207060c081b0d140c060c 69
    0x4071200d02c1515035000c01d00580791520484050142d00310846100424103600200000d215450f01203400c104211030440025410a00c188079000f40b6500ca00d40141b0060000940750300600c02040441d0600c0310444080380c00856240624204c44019031441c016a00c028402c1701d50194940d81d403412081c6003012110b84807003014224001948c004403c0c0c41d074003c45070722440c0d550004130700a400203000d00b14404c84050790f2071246891510440703005d0726441d210240f900800c3d5001300c458100250088426606c10056440481c05503843c6901441c8880c400f103581d038003c0d104100445065038000d580e142c2114141840703ea82003e090b03411035050b8281090340e5000740400f2820581c40d0025801e15031001700000c254207000056803481104a0812070300100d445920800c1c4810344a00020300603400544207010461140c0c40c0b40321828030500031107040a002c5100c611000043c0400181580e114005689006600803510303402e84c0f901120041c45d1440d1004590f44440000300704402c22100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 317481043 1250 317479793 317479819
    0xf0314071409190c0c050d140f0307022e150303050d0f020d1401031e050304060e030106170d08100b070602071514010f0501050a0e0112142d040f02 65
    0x4203040e814070401c20740e88100100c2418900c0a08244046003046e0f40e24400c1d01c03010741100b4095aaa14400000c01d00518240f40d0040740807420f40e48001c0c11b15086005034081c4400b910248010315005810b01d0324103003407541d00e030050703101110040b10161416110000e81080425008011518080708990340841c012900c20452000b920840d9402205c0c0780c500301784500515400404c00b17041e03d10481602070160502210703041080d1038480d01034042e400c01c001c00c004a030f000d0300c08030041d50400740010440c150307610f00101d014205404000203a4000c821542540c591080710542d00c840000907504e51070b03092004000090160405c02040b2a078000b40303a805122500d42c01001101c0d003201d040c0b0491503182549140b1a500707100d60300000b540c04502144543c09181940c000200b0395644246100c428401110285010440c98800035aa10004025a00446003051042075020f82111500800440400606d000071541052400048080c403000504441110030010f40440740e688002d52 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 317482293 1250 317481043 317481061
    0x6050a031a130902030111030f24090103080a181a0c03040509041101080a090b0a05070c0501091245080a030201060510050903120c030705070f0314071409 68
    0x21019460303075200b180d80c100e038a602d102d960002c0000c903100b90f00074499480f840032513044902058131400c0c101c9000c11300184500c116526840c2c90821402002c00000310f00002003114070070280c0099800c1d500000303510000307a411a10f003174813410080702d420710100e02d0303c42c0b001c509000c0600c07050f009110000b11800310314010416075014000c000d0941089042a10386480118101c00f03845000c5030003400000e8892070310340314842c1d10341e4100307020b00d40716a61454440c00a080040c00c20060105845001001c20030074894a1905880340011102a214540025100c2484107440c4491030200d60f403240400d01114000c8150300c3d8413114070800c0d0900107581947e504400b90000c15083c81372070f100390285541504801d0880d0002d40d00c04007440040f1008440d030303100320b108072609503014030950a81000090002c1c00d034200802e05403400c2c0400d654600b8280b69803a444600500002c00051090280003120100100d4046009050301850700042107080c15551300800c7c0b252041d40000340d0840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 317483543 1250 317482293 317482331
    0x100e0f0907121a01080903041d071106070e09010b04052d030f03071a0105030c0d0302010f02120f2505090a050a03050102070c0e090c0607110901080a050d030606050a03 74
    0x4503801c20180040c3c2c009118000d004040340e030520340040d0007800802c08040000c002c540c1039800380c48501944c0c03c0304c02042d0054003005001382c030070040454118a030a40007403091300c2c040c840540d42c614482104608121502d101070300039110302c1ca000c10041000395140682c200030314958440b403d15084484060300001c2e07102544e00b6805d8001c1e88000900140701200500890348188a4040005600392910325289000d010700340c5c05070b0104041c590749242c203404142c460340c42480089582d4070044904801d90b04440020804203051209000f1b01d100e0b00c100180d27018008204610400764260f1a01e0301c02541000d4078001d20000098608440e240c0c01d03004030140c440a802003990301c1d52454224000c2d0b000c890f058507000d64003100401d01461110245008070100001082c0e100c105508001d4542d1003241c4c100c44402e92002c00003103030789034205181c1c000c102840240c483c0c0000e03420154103080e040d045010400d440c196090115541020956081d11064a00040c0d02500040405c0d400c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 317484793 1250 317483543 317483567
    0x6030135191e0309030606080109110603091f062606060d03050d09080408010b0a0308090402250b01080f0c0d031101091703190603020f1203040f08030702100e0f0907 73
    0x82c49203607002c006040e0050008801c0b24851401088000d6231030504500703d80000800070320b404d6001d0b03c580034900cac1500c003458202200b101940c04000c0122140f482c5030002c1e030210b40d00ca0b0b03206d080c10400c581a008020540309020600172500400c0c5c1e00c00d654039800d00900892040c2d18110ba0035051500c600252003c0315607d1f50704114880f4181460741e9150058814070149608004401d0703003034104042c00d101243c2e0f0284c1803070b0a01c1484420480a5000b052a0b01c2202920110900000c2072030701451a4141c0100d02143c0c081d418120214109000c4103841e032440d0b84103808410844e25410380880041d43c26180c0441451440500079000d08400d0301c2c0980462400301c1500344020707a240045000c0d6680201152541801544e400155203091201960007101d544215055080c0042c000b100d003d00c890960b0700c0c10b0340b2100c00080c4200c081c2c200b059250f101080540c210308001c001c8858000d100d0138148981c40f0142d0001303094081c441e0208d401a943d00c400b0810307d0307002d40e20701230310 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 317486043 1250 317484793 317484833
    0x90412111204170f0a0b060607051f0b0d0b01050103050a020708070309060818031207020703020a0801050a06171c030b03071715090d14090603013519 66
    0x40a00409a19100354000c1c2c003d1041200704803901d0000044000b84403800c01c0350f03040160019048a4880c1d244d8410020f001303a8104004010035000100b0500241c001c0f03100210946524104503600c0070708a5818800041c05a9031580440b00400e5051505c43d0445809190218003030351550f01f4030010f4000c40e8802042007030085980f03420150805094800d651440c1d0f5441102d0780d4987c1907501c0e610ba49901107400d40c104000110702c0d8603601075250f9010100b8011075540f10f90b81d9001c19183c5555901c000000e03503460082c0501725115001c1d420080018407200708808540c508220784031400d130f84507049404e00300031121102c54080d401c41d0115020003800e40b9942503550210742c207004003d044184003070041c40400800d880040010f54058110b00340200142000081d042c3c411200d503405203460554240a4440707203503110070046020b440191005e24114030f43e8010050f004441001c1da881e03d0b40c143c402d074140c2300f10000d43c2e160a49042106e110a00819042500f06140e408400400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 317487293 1250 317486043 317486053
    0x10c080409050a050f0601090909051509151303050405131e020702041b230c060a0207150b01230c03070b060a080f0d0305190501090b040c080609041211 67
    0x40c401031503500651281c0c04802d004d00a541c2c9001d01d0025002085402d40d01245410341f050041103c0760f886006043d01c01ca0031612540e000c103901e42208901101d9030040d40c0e012180c2480c014036544496034120700b01030982c00e0800c210f95000f80041c00340740a0180a01701c034403c0e9004207849a089000f082c0c90241810301d07000240105600651700c00482a4022800d1000300b550440c2d000140c040c00480f04c1e03442914001d810204071140500c9204252000700060218500808040c8a814003621192a005a403907000f03107031207817200c2e8040c4130f140381d00c0345040803606040c3d030404000000300075801c0c40d008190020000b111130a000b81942c1035074a201c081405400c0040014041e40980022111089103599481b00701d551020101074981d810b42016000c1962030340a80c00c05078102005112014150030032034002e00485070241c0c4081461903c40498038107a00701842030000c0071507107241c25502440c24038040b50184801810090140280e03100f0004000c0c420f40211440100600a540b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 317488543 1250 317487293 317487299
    0x150708070602090f1807021218010302090d0b0a090c05030d0e01140d110a0306170a03030b0a050d0b0402040515010504030212070b03010609030c0f0311040507140f04080f07051c02010c0804 83
    0x1900c00751041b100c80015115203414822203c0007036090f140101154040041040c80301030044020f0342001420903000041c9803020310000d496000c50718802c0191400003d103800a80c00e1040c510140750b4000c034020340107902201041070340110012616a000e090000b14991013030403805440c8a0304030f100d0112450148090805002d0b1707001000c0f070405540d810312040c0d40b64198100b5800c001c2119202d95071082808100181c000d0f0400303030703038520020010f450840e0780b5004150000105141240d0b107070101020042146000d103c0c06401c208900c03840f50b0071504050020303040c0e214500020388034091101081d00e200408010ba030000d0400b16040381c0d00c0b965540d901a142000900044820090100c1c0105d807000418118008894001061400d44120782c1c0600005002c00f610703640c02c11503500080504000b82900401c5040a4024000d50b00c510b065152070803c1a1540c06d000141c200c004100680c0c3d881c041003004010028030015001180b61006031101c000040d00140f501034086400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 317489793 1250 317488543 317488579
    0x100909052a092811030f0a0605030c0904060e1606020c0108060604090f0603050f0a06150602151f03030e10020a210c0b15150708070602090f 62
    0x3203606030554940445200ca5071031024140d01004101c150407155081c0010380300b4540001c0150343d4100c0e01150480c03881c200c0c04200a5507040d0300000c202c1a000001d03c403116000880031a8003202030f0408103c0703181840002510740016050042c032502415021406100141c0d01a294602d1440c003101e020132092a800183c81107588211800740c060142c41c4074155008927002803082800a100c5c2e0b29280c00e10500a0040180d0801200704075618080800017600c2088100e0806281c04000c003071a0b0940d24144099400f0304c0c80030f4071b10b52070004c410170480d6000a000680c5101d103003a405440d50381d011510080c0c880c411302d01c0c1483c000c00380707000040c503800c8801104014802d41d6030742c0701c00bc0a0401a6603c1c0300044004000034240d1034072500102302d4030000c0c207200c03c0515100660240649806009003800d41d1181002c078045c208008142c9800c10010300d4441101120b1828a221500c41128500865001400c45a00010301302820340d42c0d42d11060600c2030040403803040031101070340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 317491043 1250 317489793 317489803
    0x15010e0105190f060507030509130203190e060601053006120f0703031209020d1a01080a1113090506160306080102091507060902120606101704020910090905 69
    0x555801903200c030b200508480c03001e0409074103036102c0800680f05245802c1044800781d00c0640e0035010131030140804e42c1e590381c640c0f95503030741c000c400d94000d612030500541203480130480000d10071030640b500744501403241c804285658440000d00340a0307200c62000720710404d4003407401e4444000d4100699031125072034514041500400741524582c2c03a01c80d4590305581d940c642031344148107541c49a241003001922809609042140621012902664542c081800f4124410702251841c0c40b06800c0342d04004644003443c01407081c480105910449610740303050313030301da180c0c0543e02540c408254201c00801c10f403c05e40c0c0780307980042180c04070700d0041591040310382d80409210009040007000180000c0c140207503001140300400070300043d4103405415a0540c040b02c400c484140d1140500341c096696600421f1707060301c500c80034182e6498190100a145007640240e9000c2c4190012944c4080b65800d0506034010f40c1a20811920f89a1074410520b04686a12031405d041c2808101e03000c00c000411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 317492293 1250 317491043 317491049
    0x1e020304060b010f0c111f0504031217070305040f021201050702010f05010605040902030912130e01060314061009091a0102011406150f040302041103070e040603051b010215010e01 79
    0x40244049280c01180e8070805016100001100c82c4900c0300402d590a41510a07101e0041882081c0b2080407c02000002c2007480400401c00c04903041040c4190900600b4107001c6500d00b83c050f1802403200c0c0d01c1c0c0314801403c41c200705a0b0351b000090421040394030b0440d100b0b400500a071111000c6c0f5030b041e4040e0008032074201c019424040300c15608450b1703029080c143c0b04241c45503030405040185640013900b004103000d9051140c00100c1602118a80080c1580c1c00f9428054610341d061408400010f001139114600b01403034500d213261071103501210260081000c03221a0000e002518003213503001000d40200d164131703103400c200c0100d010500a111080b010280c001307000c02214004d4a503582a0b00715441900014141c400035245011040101400062190b01c10b04154490300403c00300c40d41580c0c1d84852030070010034840d19682040000003191000c450030f0001038295610b554581c81503420b5006628010345c0f4200c0c844e07000b404007403403941041c2200d24141d80d50303c4c0003200f214801c0c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 317493543 1250 317492293 317492303
    0xa0519030e12120c0705090126030309100b040b040c09140108040803070e01020712080301030c09052403120d090b0601020d02070e06060702030d0e03010507050a020a060f1e020304 79
    0x424169080800d40316200042c200b020b401c07194003040100e03c0396444038600b030342a4000d41401103610f58030440e40741d0203811035110281848680d8149040c140d4484820108564002e108021030300c200010342440c0c020b01c002001c1200b80c1000041005009000300303c40d80b0600341420607210b981d001c1000d00480c0c81d2404ea04149004050054480003c15200174210540801c0000c01e02030142d01602050f05041c07048408084d50f450210302c41a0170840111006080007004000344070340fa180b424080c0c12441e40400c441c0c1000c24030300c824100035410700390716212121080b0070303280e038148201c0fa952018030300c030a44e40700d242d00d1901d4010143c02e48200d0340d001ca00404190694400160407906c0d8180350014040581002c0c622110070030010407140c0d018000304a090b005890600000160034216122508510902c81c20075080d1a030017850402008814402c0703503111076002800399800d0342c0044001030099182c0c3c590401030b00e42c2105c03980c1c010a0704001048507400700c1d4001d501c01e0b4010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 317494793 1250 317493543 317493557
    0x30b040b04090b040b0c04030c0303020c011d01020309040f0f1805060c2a1c020120031b16080f0c0607030b0609060306040e010e07080c03010e031b0a051903 69
    0x11010001110840035003d880c1c41d52400004000464641120360030680380001d090529a590361403110303041860300100e0040e045140403d40a581166001e58101c1c20041002407004041c0c000075034a01030030201c070f03202e1502c5640450380904240d100d4200031034070301c0060002c003842c9a6192070344c407a100011074461165030005124294801e0558620302d0749074903012550b150f510310520306c06614910502c194051020605105401c2585808140c90b454001050003a00e0003840300000040c40d02042c0c076040100100207098009000c89400000402001d5464448038201844001441100242444000184845032440c00b002034203c0d08100000c07507845a50b410000ca00390b030a0582100d80000090088090b1407a03c1c401450b40100054000a03003004d88001245c00d4928001a142c2c868101d107900b03200004040c020100340c52800d600030300880f008505066601e1140b556030108000b4540714190b1a0a003d10032214244d1300482143c541c9040c0410b66204a20703682c804401044034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 317496043 1250 317494793 317494811
    0xa022113170c03091e0409030804050c0d080f070302070807030311070609060c06050723090310020306090103030305040201050717040e0601022b09090e0a0515010f03260307030b04 79
    0x954421981500e40002c0a9410403081078140090070404174140c100701c00c0b011441c003a03180c840e80720380c0c801140259200c242c0c60502d03050450a041403100c0d40740c040c0044005417404190f0002c100c13000050580100b580d00d0905080032400c121442d049841c07140118000007047c1940000b9003181880e4800503551626030701c1c0c2040d07800a4070b903c21240030038042280d000216200398032565020410341052144200b00c0103028205200d2425076804881005c6010b030701509080000b45440c00c0300c500111306c1c5042c403100050507448144001820184c07140e00140459225000f516656548035000c01c028451114484111750002d005184031504003000041c1c00350305c00281208408040741004408160f42148600684000d0700701505000d15030304001441c1c400c42c07107026001e512102c00344c0301c0600586007590500001c0b801d4414a001c6420050001c2280082c0000c00c9034bd2005001814419042800400340c00c584001c45104002004200b8025016003080708084402ca0301048503141d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 317497293 1250 317496043 317496083
    0x6040b1b040e1e040519081210170a020108040b0901090b0901050406150303050307111608060a050a150e0702100c0c11030106140103020c0703050304030503070b0108070b030a022113 80
    0x22080750050402c2c0d100c986100c803407103040b0001624290184007803e15142e2040103092002d013040d208104610384032041004040d0054ad1034140d01c074184070103044035a0090700001c00c079090180018040b03400180200b180c5200950140420951000c0c1050301840c1c410070880c0200b104031801e0322001c1c203220041c2c43c080c0040da01c01043d07a5140e0ac46a0a580300c05204882c058120610485584161031307110200240e103003450402400b98400074503c41c902a00034005035a40503064802c5a41013001740300764404071400210581d46400070700d64403070b550980c040f8500103000440310990340ca04107006e0f01c00d9070b106440007640c03801112041400d401010905003250a90b1080307801000304503940d849250f00c241c000b051600001411a2038840d12508c4050560b4005c1d07208407060750000500c0c000300404078501d1401407a418000c1c1c0320240c84e05207441d91511008000c16601c90780050305405020041c0c0e200210040c0002c0c0402c910328290101c404442c01021050391190122001d1902d806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 317498543 1250 317497293 317497351
    0x14070212391b0603041e241104050a171f0e060f151504170c0a06050703050909181605040f0b0d03210513060b09070206040b1b040e 58
    0xb00508410b141d951680c4604038400c0441c00c03042803140c05243c0e20000b14229004924141d95028030701045881051282c0c0100c0340c1100410b0350300f54040c082001199240a203500441304065000e1503040d5100c0d486600300603030a020011260720103002c0c403800f52500e07480b0044902c0319004941040d00c0b449408110036400711058040e0b140b401c500d900701400d00d100c80d1100b24014030754013820180c440c02005400300150000f2000c550007100ca40220340b8092540c0030081c0071500780540f4101107620010094441d14401e030b4042c00240011405800f44c2100840d048034080e17055134040301c6050240c00c4c20442c5485003e2285080620041d03030740d500c0d0306c94444505402041c842e4418051381c0c3c10b0340d01e1446100c002450268041c05040c06101134002c65125148540c1c002c1000d4000e480c2c41c02c00c650791400707464001c002d400100810076130009072090700240c12450000d134950b5008140740195811828440c034251011a00041100d9101741142c052400c0303154400e0b01c0718104500c44110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 317499793 1250 317498543 317498593
    0x304141c030522150204171005010b070305070b0c190f08010b160f08090307030c0e0f16110c030f01020405040e011506030207021306030311011407021239 68
    0x100030201565000030340d61300c0a2844441300c6803005400d01e0364842c2c017451b0b00681c140c5c0841242d0000d03111164076510a01c41c0601520901602500b0800c880d01c00030109e0044a0004011110440100700100e801e1030507505580d0145502030418088080020241d00518440002050070340002180303140850042e2411559a40d0002d030854595031100c070100e100a400551302260100b2004001e034070140228005507000d8040070007001d10f00740c11228135074001000c15081720002002e01212103d040c2c07140210707038124900744a000c04070400761070070408011340c410781c14410342c1004011601c064020748102c5a04a03070400c00501e040b070a8900ba2521064103140801ca071100502c0b29a020764040c00005001400751900c000213909000c003201c46c142c1099001c40e848030103042e00341c5001d02800142c4031180754000d69508050030041d59031001c0705c400400c03400000c1049820300c0c8400031580c15060502d5600f0089002001029141050700c21000d0410700803520713243c001a036503410180b20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 317501043 1250 317499793 317499841
    0x10605180a0222060e060f030105010809070803031005090c040311090703061206290a05010507050a080f07030219030206061e03011e0f0506090703020304141c0305 72
    0x24a00d145000038000c00014100d03881e540d424451a42403400c6180403050903020030b100180424202007002d40b6150f0083c1e240e500c0b8a00400050703011030384c84419a811100c007070030306848507120200594100203c91f08480c00521021080080103030018411100b1a041950300c1d40745a01c81141a0b841c1d403081d804007034412a0710035501c0226082403880c0c0d9a004070700c2c1c50009241c0d80c86200e14014200741c0f117001d13504261100344090385014924003030208054812a911400c001a40204440b0f420034440c681c14004003044c030509002d003e20101c44001e03071203000d083d600c0c14144600349036500310240c2580148038103504400407280b844c5c105094680c043d001031602c0c0ea508000c002d0082d80e00307030790084680003e640402090b2401d02408005100d02081100f16210b4021118201c8041044031001d5034101014465035440302c0e02d41c280c2000c1d1500d0050394039038076401c0140002407003400d807840034820580408821580c5140310398550210390707001d00450702da81303c514100c01d880c0058042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 317502293 1250 317501043 317501059
    0x906050a0f14010507060606020a030e1c1509020a1203020706050f030a0506130c0905091e1303030905070315061d06010c1e0602030a0c03052205072105070602010605 73
    0x8100908a480200030b1101490700528014035a5284400d8901d50b511510140c3d101c80181c0c001c040d0080c5a568940f8829203806508040e07030f112480348002c0001015181090510074800071030070301e030000b0000b903801034815015642c1d260b0040142017500882640140201c0f000804c1c00c1c0c0c03103001110042d0203140f00306c1c1e08544804244500802c1c001e0701d01ca9100e0a4204131a8045180b80500803401c402074440344421840d0406105890000400c0e440e90685600ca20706a041d1031902c00d25000100005c0c2c85103495070500c0c080d002051500400780151044140000400124002e954407044040f0824030240d96036281c103622000b03151100206510303402000841951080740080001030256040c02281c00d56800100c5600b800340c6015a904c0382c001041000761182c078000c4000000305881c0070400d03813800e03804620340052210040402584120308031000d0020405c00f0b940904052410505005080140075200079141001140ca50090440025641d40180300d0b00c0c0442d040074100300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 317503543 1250 317502293 317502299
    0x324060d1109040f020a0201050919150b0306250305061804031e0509030c0d03020307150b030709140f06100f1202040b071b0b0f0a0203070611040906050a0f 69
    0x3400790600c1d5210074405101030107800c1c120380d61030042e0000542c001c040165106880c210003825928001d050310956400507412a048907240700000041940100e02c4945418070b10103400f0140c00028091355140c4180c4040c00445259442d0225120003140d454030700e0884410401c2e82911000c5070066802507442030800c4100070290007455001e8800cdc82d0000c1840151000050001410101000004d5000c15284204c0c2407c114440c0e040904442001c0700724403596000b5940c1c03141c080e00502101110700b04405260841d040715004110013801d85041580f10742c0c00100400103540301c40c6001d814000465050401d60308900e004000140006410034004541950310b9100704160204020119105110601452015102405640c59199030760326990601003100070111054400c86551082c0c20014442004121031415014a042d02d803201c049400c16405c500440c03802401b06804d12000d42e90514054000b0803c0d5608003004110031a1228180315040d83ea80c0252680318101103414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 317504793 1250 317503543 317503567
    0xf0801080309130e070e100e010305030d020a09090204141c02210a1b1508150409031101050f04060f0605061b0c1c050d050708090d0203031e032406 65
    0x415603c1c08010008641040b400554500c1c150050703200d0400c040c0c0c00720074000c4500e40204144020310050501585550550f2505a00c9118803100e0503c540d600040005c0312500405201000342141881191210b87c0c601120040c1c41803c454988500c132400c41c0009104034400003105090f030081c00f1079141c40d450803040e2030004180750f03400781c00c0e1241058a400141c00d90300c2c011520801e04e10394001041c174121007029048410b08040c4140304c0e0440800052003243ca00320f406040c4221800708101035141000c1c3c6090360703e1200c1407482c2d400c05040043d5441c0f6140d00d9805144100e03020000d10300507072010421145a8051950302030001c10804102c0580c0061264000f413802c2c058902141c465000100c140c0da007080035002c01000020080c003400b400344480c05c0d4001140c2409031400d0340d01e0751625041d100700c00c0e0152003540b5036050801907480800984034a03541007408408080b4500b1a00d44254008032200c01c820300200d0100c2c0403040820310a0080c11a01610366400c03c8110040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 317506043 1250 317504793 317504809
    0x405210f090112020d0e0a0515010608040b06061201090e0c010f02030901122d0e150103030f02161e050a0e01050d0f0818041d030307030c0516080306010f0801080309 73
    0x1c2040f9582c090290343d082c804244545145420810010710700090f85107080340c248002100d520704203540f03050041003240d410210003680264407200716000c95490100040031802061040c69544c1c0c00400042240203840d07001c840306845820484801c00ca0180044403480300d20040f0400582080c461424254043c0c40c01f8100c0494605020510b04503d110310041401c01c20044200f0700d0305000c0178004052103104241c116000c035000313003005d85480d8854051400040c4001020001c103200c040070307101e10030701c100c110711b9000d401c501984603036640c0301c408102c07103030020b40500c10b80c011400249840c010000780c003101c25213031302082d80d42e1a144c10031203800d02e071083c10360300e24484204203400100301034010f00c00740e50707005c0c140391005600000344003c81d41f1600030441682d40205100c440c1c06000015203911298030316000c1030340c0031144400c80e890b000d00104003a05c0d00510070003000304803521000d944125001c0e0784804400100c0c0000300c460610a1003111455001000302c810241090a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 317507293 1250 317506043 317506067
    0x19180f1701060302030607080f0907230d0f050304050a090213091d0312041202060420150f0a030507081014060919080c030d02191a0405210f0901 64
    0x300004400ba0350381c0101c1e003040c504590040004440c1020402c4031141c0400c4207411003079150040c002c0b0f5003004003052100da00d000181101040305407500c105548c4401507561004d50259a07e0103003c054541196290030500826210707550144003c01c40b00b52510a03980e05602400c0d01604091900803c0030050800d0194404601008810300da80b00000300002c140307001d1581900e003014a01800e01000800346d010307241e800c641061041c08003203604d1584002442c80038a0082500c03442a600240c0c1055011514442040000c40c141c07812b80000d0b0054031030b0803003a40301840281d480700c0c011505440126030b480c0c01c03016822424007481410940c0c10b4580c1c140502072070319051a1800158056889001c2d0210494481c07074140042d9009101c0d800000c4026002416800340c4600d0194540c880c10802d030304000811603c540a001030071800d00c4450503c85404209030400d8105143c84000514005070124440056018101e141c0070440b44140000030720241800d40c908011038141032144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 317508543 1250 317507293 317507339
    0xd230a020f0d020d0f0e0303071103070801061205060105010e01080109020706060e0103060c02010605040204060e12070b03100602070617150103110c030711040605030a121419180f 79
    0x10318a200190310800c0072614882d1150001c018401c1c2a2500a04d440240c4c80030004108042a1311030040e1800425511080d81c03203119000384141844c08240b5044c05503000142944c01e0840c00103043c80055120018035016030213807034860380c0b650015154202d4040c009030006518100410030540150b0141003801e104a00110351503982d100d446883d03400a030401e807000d603a2480760b21002d40d0244520b0008040a0f6010f6007002c3c80d08074081c04d20701e000000b89004515420100500304020301a817400b40400c107580c032f52a030801d6500c80e0034400740b90250384090302c100c0a002c1481d601a910030034507000303d0344500303c031982c4a19042c02090381d00340c0e00728145a12802032000310f005c00c034040d10040e0382d103000560300c5080d1400c0c2201c41c5056807485500031481d001052006440c04031b0412411600041c94081804140004544e10510310711444441000440c01e092007410a51000c141c100385d60f0754417541c0e50704a070114401c580340c07413088040c000020142040aa10514080217080c0840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 317509793 1250 317508543 317508553
    0x6011101090b160206100509011a09031204050909030f0313140d1e090503031803070902030907030c05031c03050c040f14100f0206151f020f0d230a02 66
    0x1e9070721489000c1d4143c0728010494101031999101d01d5041203042c0d4086103400c411032a90380b41ca004208050018000c2601d421250300c04403e1418014040380d008060140460301c20003024039104e5190f82141c0901c6100e00c03108000f017541c1450000c2030700c08600c035200c4010701d1501c0304125000c805890031821518583c0340c0c00120400e079828404c880041a06445244124501080e49402d07050745000180900940c40001c4c45152000401d40e40c4002407030400c401800c1700100007a24100c40b95011704040c0d0300010401000c035002095541c11079100354800000e858482041688440500d80d440b0b000c80800e12500340600d100e504000e07000780d4081101d500c0c0c0703520768421600c903e429801c020401140207080700b101e0305010390001005891483d08100d98503411000945170328004e1314040c01c00074a124903102d82c5c4d90b4100880d603070a031080b8400e0360341d21495001030340f00c6803441c254909601400b2002c034a218002d03c500c0190070480d0b581100000e0038000402d03480c0d00104c400e48211301c15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 317511043 1250 317509793 317509811
    0x3180307031d0a0e191b09120303060b0a210b0d061505040e01090c0b0f0301060806031204080606030d050c1005090a0c060809070602030414060318100605090f0f06011101 75
    0xb8401c8414020001e0320305c4010020101c00c1d402060783c1c010984410880c0346c0344001031109030b00002c0442910000d01e15444984081c1c00c040700541110740007900a10400514600c0c01178000880943d0a001c0c40c1e1080400c208100e41001100d1000c0c0640f42c22826501240000503841c0e03102e08119202c20780d0b0b0043c495243c1c00810300721844c84443d290181c0d0745511020074070000c1e0f14002c0c014134004450038a040300c0540402040d01040c400d24080c840d840c40890150f03541800360021500c0d50888250301e82e96582c0d416a65000d00f40e0f120780c024020142680701c281d200c0c000700d64042e40180002d0940000e0b000400d001440010300045450254184e8100040d00c140b002c0740040034070b9921100103080c80c000a50411525911003000d65008000c10007488050000481e0031801c211012510b0355900d450300002e14603004010390090058030400704612010ba0722000035210301707650101c0150b541e61949480708000b511000310103054000054520340c8034a4032511208181070001c00d01c105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 317512293 1250 317511043 317511059
    0x10150216060c0b13050a0318150306090c0f09060e131103100603140f04020112050403080115020a05031207050705030c03090f10170604090503040b03180307031d0a 72
    0x4a15040480040d6000d0084010701a0252243e60408240c07a10000e15070302a9a4403a07480703402000090900c5000500340d50030702140ca000d80c004040c05c02040719041e605600040040000740650b007109481d040006074018482c002207a90001944c680010060030840203407106150389442650100381c0700a064100702e001d00641c040880e50104040e00c0c0d05200000740c40754411078000d00101490130a0001c0c00b13074050514941c2040300400f5a111544450004035045c0140c801e408141c5414141800205a4010a0a4100c40340031031655440020f4500403070310340388040d070301911b0f540c01884015a0040b0740a07149030050220700300f00d0700c6c21400359252401c40c0c006050420b0b84d03410100f0b4880460906e40400c0484074800c4511444208049001400e90700c80307003410b41400300040c0d0000e16582c0f202da1100307000c5508a012039899641d24281d102a90f4001c80e9000340300c0c2e10900710007440141c00000d560f59103615803228400c1c52210601c417104c20220b2004164400858503001910360 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 317513543 1250 317512293 317512333
    0x1513030507170307031e030902101d0a0b040312050415030915050405030a0c020f130b0f040501030b071d120303270c1302070606081e0105101502 64
    0x98030500103000300030324040c20a07000c0c0b4030020b95000d20760070030400b03200020f60041204040f070a18417440d040200d03000b08120f0091031047d80c001c0d00281012000c0f00300d20b03005101000890901e00e42140c00d0707003544050202d6031485200781142090300b0701040c0009030980f15041e80840382072409500f8680c0c0c2d80c0c025000500b0200030000429628a244e10a200c1038500b00742081012030410310460a0a641d07103603480c4901c1107100d0403c002030000804550f58a402148041c200401c145041c134840c00c00000200f40401e0007504c035803001c0c010044141000d0003424107c030b0700000321100581d07035030030207480350815401d0210584000040d2107481e680c8245a141002031100700542d1a460724041c64041c09007071a8207404880003c0c0700e18080c079200018100007550003070350340c226280561802c0070040d000e010340c010310742804c02c840444d030800002031051615205401c10840f90311016542ea00301e45003034908400781109550305020415024100d480c03547e4140c411903070f00088254a140b854 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 317514793 1250 317513543 317513549
    0x902091534060e0102030c0a0c03030609060f090f0507050316020a0203010f0b0108102301170403020129090f0402010215101401050c190f0c06120501090b0f1513 71
    0x1c030240d094040180000c602c1400c250100407002180380d42811540a441401001c860300104064a2125010507101c3e822540051000010a11480d51244083e001860113030003100026450b24540c0300c200126409032074098911510380720314540354034251000c244501c4810006622070b00051100580f0244a4020300609801c030018508410b8000106007400180402c1c0d03290000a0041c441c55480d190b20300e60030b0301440304440303004e1085401030340c503090642d681142d084140d0b03041109268044d0031002c84e44074075040f442d82c0703480c0c6004071032044a01070718050340262021000400283d10751941c00d03002170050044550701c80300741c80c010b41c505034116000e080100007003208220b48244444078020b811000d09000d4102105810019541d1015234a914a12510b044d9038406100c290702d4003d00c0c140d08088200207864580c0c901400c8800314041e403001591402c030002407581d61621500170490001800360104030a0b40c4100031145409144055a22000304401002d00504520601c02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 317516043 1250 317514793 317514877
    0xb071704060c091e0b0c0a0f060b0a050a14090712020712180e1303030605030d081509010518070905100801050325060f0e060a0e030709020915 63
    0x10800b0300e00b60081040010341e10aa0b030f00070a04c1d0700c0e542c1c844810349407441920080c150660f00c0721b0040d50031610704000c00300040c0c9440c0c402d06440007800160b4001000080c03095807003407041a038070010301101429070312a800c0c56000120b01000e29140c0490b0207600b202140c0b91251032840c5c00c000b020100d901034202240c085640c50b076a080000d0304400301c40007070b9451100440c0720798900a4204a0004000c04805002c20743c2d40c100c0c42018080d9115402611303001d000c4600350001c1010140050b401916030342080c4844140c48219490440c0300c480c140c41028140328400c110041914101c1c01001e0000f10510181c02d030007180a403510200000c543c00f40c2e965000b00d030351605060600b081402c400030081d03c004c1001f41220200d10020031404c8034110702e80600e0454045c1402c4824003c44c0b00c143c3e81c0101c000400c00c05450748030070004006003046003034441306030343c81300540120321418107041c0d0440d075044080040d0010318800707081d007141c0c414071403003459840704055241c041403180e020030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 317517293 1250 317516043 317516051
    0xa09020c03040b2a010b0a050f03030d020301080f06060a12060911040e03070605060607030804080a120614030d08070f110f060a05040b0a060e0112060212010609140613030b07170406 80
    0x581e900c080700c1c0c0c412102135100803c0084605004145a211300d4040c05015520f64102c020b120b0300d08008595891180d01070454980d42c4607402603498040c00302c1e0003c114403450010544601d0003442d5201101c4202041040c1c001040c0e0700e20000d0a001d03203050300c001182030071406d81c640741d0303010342070800ca915006540d5549841c0740650803104040c0c0501d0103080c00340710b03a100194000d03169941180d08481c00e0b80c0c8501c84100d08403809100e010302c544c3c501c0e040c2480001d1051101d807a1104120302102501c10081086004480f0844210f4180700098144100380c4001805070880d0b61141070198240d03840c40301103580c04d61034581c3c2a100003a440780e5030720401c01440701208940f5000107094100340002841d0002c0022601d03818081e03a1200c1118215007410090290304592a00301c6840300c0e081b0035a5a03250113000d0038041d2040400c0b10309151055449460250111580c066241031003140803421900c81c0080000014504028840030102c3c3c1940c1036405010309100d540716040c042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 317518543 1250 317517293 317517337
    0x30e0102070f080a0b04021507050c100528030209040e0303040b10030305030106030b0a080f0a12093015090501060501030209090a0e0c120106170a020a09020c03040b 73
    0x24039103280350b8007840c0407030801c16040c030002c00c0103d12140e0580c0c0002c410030781c1d0784450002545050350700c440f1860b88000040c4203001c00031301240e011001d5070211111111101220010344041c4035041e4140d114000d00e5011003062420100300500c1d11035245001130034268540042001c40b45248100503c0794804010081008807181403a680412100c036000d0183d891503078041c10758081070042c007050644810a241c290b80b1002d00b0340000308001400c0383d01e8407a03030840081e1203a50895040e54100c0400200c0b40c0c2c0c0600030412141141d2800880062020700d40122604006903502c150003c44007800c80800414561001d4519000783c8480c000342c1140149810342c2180e256600440c1814014004000a40d940943c90f0354400c540c8880402c0a40000061a04003214403032002d901c064141040d07440c0390015848901a1680000351f00d20302400348100540e076142005000b5482a0340b00c20038011014190042c10345a2440b0f0200d03418244c403000c0c0c601c2650031030034601c2c42c1007911007020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 317519793 1250 317518543 317518547
    0x70b01090501060306050a09020f07081b060703060f0b0705030c01020a08010807050a0f21330e03040b1b0102030406020d0f11030123040c050702011e0206190b0d030e01 74
    0x140e005100500b02004110321b040c022600b5046a4030690814030740c041441d90111038180c04544c402c40c0e0180c1825a20b41d0440301000052801101c641140c2c4280400195414024401c40c02590200c40707403003500034030b000d01c0c244c080c0e803110b001107400703010038000000350190900260090700d1043e11a2429503050000c107524100c034a0340624403d800803c0e04000e00410308440906544c8040d2210241c41070004011080702c140c3d00d0020504002c00380c41e0b880700d00004c82035103000c1e00d4800100c541034280000711410f541010f800e00c811500308001c200300ca8101c44000700030400708410742c0c51190402840385400c903002200c054400c10f23000582e41c0c0500b03040388a0a496841d0b501802c01440303d0007001018940014051181d0242d5010400b40d014006916030186006006006110381041c7d08002010f540002c481280400d0320218141c5080b0f104103248589501700d98020000c41e5540300040f4104401e682c4044540c40d030f0b81646c1542c5454864270b102c02240661503081c41c24041c4800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 317521043 1250 317519793 317519801
    0x315010e0a050708060108070219030e180408040b210408091f0e10030b0301020d09060b060a05190c05240112030905100905090114010e10020606091b070b0109 70
    0x324074030340c5000200306100340c10a181a400000a282c88580da54648100743c3c9044070103890441582010360991040517030024034005941c1d0142d50949510b0111219280c05640543e8002c10300b80f01448207110300760f10140a44404441058410f15805107402c0315440c143d816101136400c107000082401c80c50a08044c0c0c07841c5100c91203200391110090403c01442d00c03107064011032041c000c40242504d150322a0f0020100d08000500031542d03182806054801003080f0700080b50140e0030710300707451007a150101c140ca44145c800c0e03c605250020560241d080c04501e17000749030a200c04000721001040040024aa1400c41d18031a600d10030250042001c40c0c4030164010421004110010b00000e98490a03c17000c840003a1642c43d408140004156421607085e008141c0104015000003000301d076035520b102c507000d001c0e21080000d2490320244100030b1100404040540c0c00a80030800c14186904820b0303104619400040303500b55148800c124036444400181d81001c822401030102c1511445 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 317522293 1250 317521043 317521051
    0x1210050a093801121b0518010806060d0f0207061103040308010f050d0318171005090106061b03030b040e010b040b060405090414010b03030f0a030b120304090905010b0315010e 77
    0x40b41c0c004400d0030b980c000340c19011a440340c100850a403054202c0e51158020003c0c01080c09030b20301d5501c0703081a00070306139003060754503c2911404035101400d55001e411072900030070000d0401403820361000c019101a041d400c50f80c210007907003041000e01245052080c01d82881078a0030103580c074200380c00c0050591406070007200041d40d030340a0403c616940c0700060921141e040c20704424040d01c075108042100300a40c000d609031032240b140b81e1081c010104011404000c00d5504000b940c503006001800c0301d00a000c0c0b28041007803036100c0c40385a00c00c100d1440890303109280120b010381c00b03900840c09448510701601041d0391280c2c2c4040035440c0601420078121030a0714058202450704001441070000030300041c025240890042118030000c0d0045002d6135400750842343d850086030b4901c001c0d94048400c0d00d001900c0d16181e6400d034070b07091100c00d0044035104000c604090810807000010642d10b2011900380d0b68a0946090b207031001d00041407040d03000d0980908643c5017285050f40004010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 317523543 1250 317522293 317522351
    0x10030212070609180605120d02160e0a2708131202030303070807090815010f090b0f010323040c0509090604030206010320030f100e01020a051210050a09 67
    0x10180710080c3c1c8030000f88115001120300768203150f45501004010540c0c0d402c00d40c0c105000c2c0302c2075809401e00180b00b0020807001c0d822146041800075001d10102da1f40d004500781003406001244440500d070b00100d0410300da1500c209100300e00e6050210001030131400803074003680042003203a444503004184400a15402c00310003003030100c560000e0b4907848010891000c0c0486100401e40c15403003410b400020f84104411104c0041000301180c03010f0f0381c244140200849440c00102d0050514040ca184030308019140780200175038140154003418103a501b0b0b007280d203c2c0b940031410100700180fa0030f0080740a120b00b18131141c00c0c074042c0704480b00010110300c4070f84d00100c2880002a4000340359411241c10600c143c400c0c640340042158446a911580b44d0b1600c68503a50b8606110081401072040c102d4100c100040011054010300342d0240400800200714103018100e41d8030078260701790390b1284000f146688180d490700c0000707000c100d01e6041200b0341d41d5160600d00311003007400c1002c00350740800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 317524793 1250 317523543 317523553
    0xa020f010216120611040303110106090902010e10110318040b010302030601090b07210f03060608070f05030a0207050a0302061e0105060f0c0c040c020c0f040905070e04150510030212 80
    0x40c1c55640003003100d5200d10409500d03d941d0410a0007020b50046281e00046442950346950b01d0030b00800218800024107480d500c0e200c1c000602038900d220384404541d060710344210b084e01806c108403001c01c0e01c601d01401d03c0300c40260070044130802d10003044120010000c413011082d0201c1400125400315403040d05040c410401d11202e6030300030142604998100c10030030758a95a902c0c1000c40c030450b481d003030321104d03880143c6d0840d0b1981186030041c22980c55501006600c0d40d42034125142c450558940c00400ca03608440900f0038410001140d0024403501c004d45482c40e10b544640c036020315000700b5001a0803800034003549900b4000c00c5c1d1103809190305c1009a0394101800100184170f4075060204d00c40c0000b8008910f84006c0c8404000480c008000b0800010000b401035294400410034510480c040e44069000d842d0510400e015550454020103400381010032071038000c28068001d0300e00b48a01d0795034002e000703010300545100340d81e10401c0001c1e907413851060140a08400d04582d000b9002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 317526043 1250 317524793 317524813
    0xc0b01140604050d0c080d0e030c0103050c2d1303030215010521100905010204090f1b11030712170c070203100b060409050a0203061c0b06151207020a020f0102 70
    0x40d03030165019250121813542c008034451506660b614a9135005203524010910071803000f0303401c0030320041520401e400307547da8135508500440440d80c003165001c614031420b001c08120b00c5500c11070000b10303003000180310179284400e0b4006050ba0304a000c0038041d02c10042010300030550306001029a80e4042509001994100000a0041c08044a0b041c612120101c051200007904211400c8502080c1108010740d141600f00103001c4c6d0f00c640100040c0720705050302c444805d5154410303002c540e140e503c038640144007104001c40340c40700480781e000041c0c802480703403c021420000010138445066228101d101002515201c44c0c40740007881505800380a00c0b42c0c1001d602c000c1440040d071008104001424681880000c0c000d000d035401081441d86010200f01804a10f07a0055015850403111700700d91030008001d0030074503c0d08240c010914040b41c004140c0a061001c010343c0c1200f004800f2900b460702416000f03500a004403254001a800004800c0c25820002c11040c10f51600384058444121 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 317527293 1250 317526043 317526049
    0x8180f0d0c0509150d260403080f0708040b0c060109110903060403110102040f0b070b15060403030305040303020d140f180d0e030c0402030f01090f0606080601200d0c0b0114 76
    0x8910520740a4528000080c0c040c041041c208450080001c0c86030703507a202a410002c0c0c60312911b520444c078a000c41040111881d04481c107031411268804500c9103840110b0f0301542054002480448443c48144400301d0040708200140800d01c1c650360003041c0662602c10300c3c3d004d0345c501141085150740d017006048403507100814076550260301414440102d071182d4103414024851a80200c01d08011130002080c000c042800a240c5180910001492a00c85d0b110641c001340c1c1c141c0701070381d00090070001000003d0007500010741c010f0180c1401801d1500003000c602c25611105402d0341800071140c1044207140040d2074007a006002100840d405008002c0619a43e007030b80c030020301c10f2204c3d4410902460381d041103611488070026200f50b4581c108912510240781c003e01425117550f0415964010104242c41f031542121502c1ea00c003402d030f4841d1030056070010012303850038018002d00c011481c6004000c1200c08840002035076002c0845084d030038020308081041e08030803001c05500c2c060088580d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 317528543 1250 317527293 317527313
    0x2070809060306010905100306061706010f1d0913030f080c1626090a06021f0507110105161704020a061b0c0605030a0f05060108011403030708180f0d 66
    0x280a681c5140c0c2c0b40c0319540140c410342c2d40d907070245501207034190300c0403102c540c5070300084101d400644813007404400b000501c0320032060031070f40640043c1500d0880442c080c4144003512a141c860450540415103000c046221504129000420380248041c8801050350241f00d9644030103c03460600c12908155000c0a4184100d06500261094110344e800c02e0114100c3c115100e900c0b82d580162000d441100387c4012600542c81061080c1e83c08800010b41900104041a109039548081030a0a00c600480001804098440c00030401100f80440135482c4c240720716401070b51441008241480d859400816000007030713040d1100d00c0b031440f042c000180c44441c00d0307100344c80290078401800450421502003800c060003024000340c003a0a0009079107600a4001e50242244200a020004001d0122000d981003950710030300050000c0d004010400064003108107018004050303924059031602c41c04c1040e000f0303c0c8036083c03240341580c2c855051305e0310070001d0394104030540d2254040011a01c0e054803003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 317529793 1250 317528543 317528557
    0x140d1e02030f0f0604110705011505010f050304150f090501050412030209090115180e0103020a05120d03090c0504020f0d06050a0608130201120e1c111b060403080f070c09020708 78
    0xb2040c04003c04c07070640d0f60b80c0002c0c0c500603079002130a0f10340e6050300f4200e001e0200da400340300c40000340034004255540706682c0c0f0250b12409855651440d1a00d0307480c0c8289600f154401c41c1c90503138400000c0501c05240c050101e0307150007040003040e2402c15080031950750078280304003014184104041411500e03040c04860442e1060101940449807101d415500d031038450240c5221020404808509500c90b0321441c1d05030f034000d03900340381d446480350f09100008916280064003544480c00280100e032017070300a000014860f80b20382840c035a440011a05a800072000c00c40b14540104050107000e1803489880000c22046505420240c41c00078050030302e0201410f13038900c0480f220000d80559004038050b803068460301c1e03010460b41c850384410b240c43c0c2d10800000d09001c50029104500c05100e44140000d00d000352010341102041c0468190030541e010028a422a10510000021481f00c10181a0007100002d590366144e01c0752901000124454119802c4180b060010074007140707501080c0c50b11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 317531043 1250 317529793 317529811
    0x91a04060e1c1d04090c03050c0904110409021f050d272904030903051029210d230301090e010b090103140712020f060307140d1e02030f 60
    0xc015110f0707004542d02024510b000381c115040c20200b1040100c0c0c07102c8070044a024078280c5401500000c10440e00f40340540d009480d401030501038180f05d16050b0720140036140300910301010030310700b07001a40c0422040d20307824020072401b041002c5084280d0141140480da480b1107110300c21001c08a660a0810200c030280c43d640e40141c0b4a2100700c01d48030b07401041e90410288125a10345450002c1c048001400201c03018001d07a40311145000da81e01900c420070500d8207014036031003031040c20b0341c035031400c0840410383c000c004224040e110101c00782c0004880c83c408010b04080d0006980181a06101c0c010b4000300d00c41902006a1450300c0c071041d0390559494041c040703200780c4080280d0303006d01420303074100345c0c07040b44c0d00300000800a002820b0491120400c00391510159a461a40c07845800040c02940050001c100004940b0703180c00250307072022070b6050410701740b26a20607448035600a40168503131140e4900e41c02a0100c00d16010090861100b0030543c510f00c5c0c4010340c900c040101034103060b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 317532293 1250 317531043 317531057
    0x151d0106080114160305280c031802030c10020102071b05030c060f030f060103060305060901060e0a0905100b03031204080d1a01202a090705041512091a04060e1c 71
    0x844100d20700074039110725418002040300b1f804401c40f81401081d2011142e0003080c9400c1e80d40d0001c1c508080ca50400c80e8004000d01090801c04d0203010b214411208010115542000700400060b448404410700e00c0d140c0c1d01d40b894890404090601d8100e07191102403048205110340b07101300003014200c82e44800c07841c582d0b440755180d030001a000341c042500014024003803101000b03840f0505500510480700f00581015054403619a0711085031000320001d40103030805980312036213045580003951115000750403030307141424410740588401c805032403c40302c0c90000075a240c034007080781c0a40e0790501a07214016843c04c4000001074100035005001b030340e2560b44c00406680e1010144407009071981d045a61164000c141c20642106d50f0040403514800c003600c03800b01c0c054071301c25404e960542e010b00c101d2108050520380203685c090b4408800032480f03a01d40d00d034200014022154621101d481c220040c16608082c82e0810640e6a0420102060b5004105000900d240c2810354825103c00b410642 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 317533543 1250 317532293 317532301
    0x50a06092301050a0f02040f030305070c080f061e10050910170d091a09090405102a030c08070f020f030708220b0403151d0106080114160305 62
    0x421144242503100c0c00c1a007400e03104076002081900079a10820400c0000c02c225045010040128011400340b03116030701e1200b40a10010f8090001040c0d6280101040020195100301d02403403c2c0c82d5084041d8130703402c044180001011500e1071701e50102d2414100c140145440300040180030002d00c07030940310302c48400101d115516103107192405401c00481000b03a440c100c2c401555512005440000010125003002406a45202601000c154003070f600c2450000d240082124508003d041682c4500500c03003403541c400e005114111561810002c000010030f002214050346410b00500c010038107040c0308019044561151600364014410308041000c07203040b100482c03500707aa207014040c0d40d00c80061400188003961001c1c3c580d1031003965090822104016800300103903141e2007a00c103500030a100030720010700707002c07020011548a003900042510b202c0300078220500401c024180165900c0f481844030354400c2c0108200084044248011406e114612a01002410101501b0550750798046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 317534793 1250 317533543 317533553
    0x51503011503021c0528200f0408010f051905040c050418020a0f09051008060a110d050403110601140915210607080a051e0408130f080c010804050a0609 67
    0x3600c05440c403110400c0070f0302c3c0c0920444951046d86649000070100c0a0400c00d0300c4500303000e08905c40a08450b941b50342c8080c6070b8800400c4e000390000c0c20110000f404041980482440b616180c25004400843c0904040e030710310070b0140a84100c001074a042c80204004110501001011a80c0550340061900e80c86600300c001e071720100c00c0c001e6020010303080001c1e4038141a4410070039540011020803407600c0b20400400d4003240c1d07101d00c0409d9080800000d40300b891701c0e0f210b01d0f40707026401c3c10146866055014002191400c4600306c0118500002c402c5000c0b004104040c0174007070084150000c1d070781900004941c80300c02030034000e48420788500c90181d5160a8440900403001c44004120001140e29003030302c4103001c035004070020f82c4042c0040e4910485000e02c40c0a400040e9a180065030b0f1000300b8031062000030030585000c40104a5a00c2a00704864114001c0460780d00b03803a8170a00340b03107456082030a00e40d10907041241007814000407070b0000c560600070f150700c1075000074200603074605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 317536043 1250 317534793 317534827
    0x403020f010c03030b040e010504050d09060c0f05011d160b090a050409020406080601030f200603010e07090803221d01230303070b0405010c18271505150301150302 72
    0x19981160a20810b44413900c41500924007a2f4442d5081c4c0d0100d0196440271a9202014440c280000e07c030780008602180c40c00c2c0e10310300a00e02580011501c040502c0b0740303500f8403c0c1e0841b10122548445d100c0f00c0100c1002a1032070203046594001803900803140000f0b41d109985024051281d42d65070b81c100d0440d40d89902800040c001241a10038039030307617401c0544400341d0802c03094801882d0403c8130900442410404216008010000350450342003402078152103600400820a10465280204039990100098280c10885040c040c0c2a0b004c079800c259201d0580f40d004908545807041d1540b01d0110301d00015040d14400317041711404040d58080c044a4100118880d605030100040c0c04c010322141c06842441980103070000c0c40500c0068408a40410104100400180840c2300a120f20b40300024a1160b24072403600074001030102d0703010380e0304640316215030140f40d00c1d40f07840c1004541404000f1083c50042c860915045602d401e240901107108903148804260f8009480c042d1710707012000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 317537293 1250 317536043 317536061
    0x40512031308150a0603021809030c120406020f01050f040f0f0b010e04110303070314031017070f05060c070e0a0f02190e03030f12060a1d0a060501050403020f010c0303 74
    0x140c440c07501d969581d201516440c41e00301d1000f00042220004500c00024000c50049030f030302074440544940c001030640314440010f00340b0704180c0420071100c100c110b400c11240d06030401d40c0702072603502d614200d40030380f50010481f074400c250303414a030410200176005096079500c65002542200b0031402850300d80c0700c0180250000f0850382c0d0180001c982c4000b10b04c44580b0451007107000c04513401a280406036030740a4103078020001010541440380140019014580089044000d6850280ca80350707480074194950080e88003907440080308218103440d9040d02d900515080c0c80b61440c1c034010045950325021180501030b0750728161000b1036560310072540011112980d5020071500d401c001182c460b546226942400002001d440c070385101460080126020341e80c1c103a0002d4034000d0160b00030703111034000400040e48250030441c000340301d0f1084110a440c000300181541014506145c506088910942025040201c103020600c01070300c0303401207a400d500c0242803a200780e41c0c1c1850308030003a01c3c600f5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 317538543 1250 317537293 317537317
    0x2003061203030903030108160e0601030e190f0203010531031b05030702010809060c070605040807060c0507050d02030a09030303050a0f0608030406020106090b0f1215040309030210031104051203 85
    0x100701c3c2041c4040080e40c16140684161488828201c071941d42c0c0e11064043e014201802c080030074501e60107a4098500d040c1d40c1019299000d50840c070824444440010544489001a01000441c07a0a20035030b075021013078441b548142d41ca032039075601000300c010000c010342e0120541e201c010705000303120250342101d00400e44507900c2c90510700103840b90040c0384101e021034800808950026004a5061304c10f81d00200d0f1181000500d40342c00e8054078000d001507586401c00c00c48100820018010304610410300d40311250b8a45161406910b0640c1c1e034441c440071034000748106821144e0141c0031004481e094540411035071a03559221000302140c1140c020414500003000501d840702002610440c1c90640003001340d42c0d42d0b401d406090340c1030f498503240e00240c04005941d4919060404420300160202142c3c0504080d842a258240c1d00340c0b0142d000c40e403822030410031403800c403a4440c00300c2c01a19051287c845605455a06030040d4080c00d4071400241c06281040342c802c105542410000c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317539793 1250 317538543 317538547
    0x14190807032901080a0b030309101713170403020108060f120d08150d12050c03040e04080909010816060807180e0609090a03020709110408060411132003061203 70
    0xb00800201000ea2244007a021600380f900107002011039103d810800e81010b40550b10b0581c4100c00c0000c40c031304403072442044c404400f2480000c213401144a0780302c3e004414000e4240c034602d044c000107050140082481e0050308010600050364080a203540264040da800d01820706400002078041024404000840c40750030700309000c0550055096009814005402d00d49001e0340051059800c40000e0180058901c1d4003031043c6607102d0300007030500c0140d040559040507201c4911a8090009076801d54042d040401c0f003544600d00510f050380184401001021040d500700c1020200020600c2510305012035100040c24641c060520b802000d600d44407503961035621000b001403803180c281c9015010703046c26070004036110400141040f405405d9001020024a40758241000e090703903c002440d0200300703000004064108010b0540100d12520341c14450440324824010902c42c3c09201c1000182402c030503559110800b020203080505900d00c0a0b90f9070742c1c100100e44600124004103900e4400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317541043 1250 317539793 317539841
    0x3060b1f030c08130f17040e0702010e15040f0b04020a180e0105072c030a0c090902030606150403150b0d200a0e070302070609060c0e011419080703 65
    0x7065120441c2c03010396441c1d40020341c50781103031200b0407070b1030b01c000420411015a41e440803945030389810591044802c0c04525050311501d01a014076001d40f46000980e440d8445440590424040300303020441d4a1600111842e082d00c44441c000b030006005412141000045419174660303000c54405008220106003038500c3c4034501000410050403090815403900303012071f80c05482008950303194280780052000e4500340039500e41c004d8405c448441c1d410f102d40708484c00040d40d0101c100c0000c00300428000b5201c131160060509001c401400305106002d4040b0b03480b8010b00900640d03094980101c41c49202c0c03050340300c03800018041c0440300340d408203212010008001d10074010302920350a420a07070385c1e20084082880100c1c021340c066801901c00b2500080c8055120354040d00050b401500b000c990360300e29851f580704803825102e900380000d040b1420600303996000b0b1141c2400021100d1440e02d4551907082107000c01d40d540c110382c41044900d40104444902c00d420283d51415a00c180081c00701c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317542293 1250 317541043 317541047
    0x22a0a03020303041707080a02032508120a0206060f0a1401030207020418020a09090c05150d0603080a020706021204050103092103050f07020a02010806060d061701060503010b1903060b1f 82
    0x20400310211305c3c03440f4100001c40c421402080031123540f68050001c0440ca10028134030b1800c90200d1045201c034854101000400b0601041700d146200c440d07004180e500c41e01c8080013030070300400802c2c0034002c80c00b07610842da164031060075038011130303c2001800c02034103c10700040f070285c400d941e000b075442800c0c11449401c0d11000710346002c00070b20071034030103101d555280b5002c0160340303410101a049050041301045241800a5861602c41d00d1040316440c1a5031109050125505c2e80c105030750040c00840c04407880b9030108500c40c0580310300e0004044144a00d981300e2042e208501400b0f0405480391a044e0401102c0e05c82d00c001152000c004644c078450085000380240400c0f176021f40820900008034a41038004241c1c4800c0540694448901e603442c0400c1c03000c0c0d540503820743c001c643c3e581c9030009090785549001c0050021540008140c041c5890704240c01c0d1034001e903082d8803410402403994851514080401c044070703400140850064042d500042e407804580f13005100741c129620080349126 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317543543 1250 317542293 317542319
    0x16140708090910060e040b04020c0318190f0b09030102070507061107091103150609030a061a0303131502030d06142b03080406021b06090706022a0a0302030304 70
    0x6400e03125500c0c40c2d511246003940510f12880762002041041d401c0c9241030070039400c030030b6644c10050805031604c0641e2625903d1503000c0400c1c651186500e80d081582450940781040b0304ca81c000e4950403e45040c6031a25140c18200c1c4100c615096001846000c0d13501d080d0159101c030b9420906444600f80d43e800c000d464840c540c220b1400601034460085200342d414803404d602202245c84080c00c40d51800b030b000d602d40442c100ea43da402030080c46400003da40c100304a500f558402c11000c94490801003d013420342044240c9103101340c00902c040e0150f030018503202d9080391349002c00c401d03244129810503815845802818030815040c4100461548104c0c12039030386507a03055030300340740307500001150f804080e004001c084811040d025200c00428802c00c50342c5d40042c091034005181c141c00254240010400702c00f41d0800d6040303c0100306509505110040080c5034600280c40c07052010075400300c0d03003c0da054006c18460381182c9004030a03103031a00820003465002c1d080b40e58842c1c0302e5100003824 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317544793 1250 317543543 317543557
    0x619080105030111040506090316090603050c03060903070b130c03030305160905060313020613060906112805100e100b0109210f06110d0b0f030616140708 68
    0x20809510000866040c14410a55032034000c10809007007034104410010f0640c060000e00d81c3c1481203d03180300743d10f40b222860000401118200003039117441c5141880c203100d0502002c1d882900100c2c208406440c0200803169005c1d0b00c113101c5501e81da56501c10940c8641c102801601000a1b04004010036400d0307880340b80500d078041d65201c218540d400d0112410f1140e8020181c000e01e007400441c04c50202d81c088002106e00c02440c96081c18400820200b0b6407e00740e00c00c8000907002d1070104005500030f106400682602409440500e40c6014400b5060300140001600400c10a460b03c0a00c90203000c145d20300c03441c025051014120081540741d48800e01c810301c0303002c18513003510480a980944203841c00c503403003841098905154004046440001040c05460703101c24180c10000081261007003401c944009100e03940c580c204545614100c8000d2000180204054042c0070415900081d10980c8400280100340c0c2d400c50640c0200c58902c480b00b0401e0309104040750110130414032401401139 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317546043 1250 317544793 317544797
    0x625020a080a02101b021314010501110304180f0f091211060a0e0f0601080d030b04060b0318030910020a0203060c04240e220e0d051209010b0619 64
    0x5039071625901030315040420720081d4809140191407a145001d64030b8484582c4000592469005142c2c001c181842d01e42c284c1c0142071b40c0d441d0788008280c0c12040f0994050102032810340c001c03200500c01555280b00c0ea000300e00783d0764448800c500c9219a13982003a072841c00f1070f14060048902220f83c4d000507042c803840454045120719100401c3d42e01c10441c1c00720903070001c0c00600c1e064894184400c0100520880d000c0ea6001d203d0401005210030000580200380c1c14004098140300050300030b00321903280c416148614145a02048000d0250066a420100c0c0c00c001c8410943d0040940f440e5102c1c084046ea002104a242c42040039000700d81380d41c9540c001d506550351603a4421411025100d2409018203003030016080d80030002a00810001d20a4103040240742088002e0008022607024007022150f4001001c40070b1440400c2d0003418802003804000300f10303500400700301a001d0700600825180c40010b403c0080e030500c070700b500004141a4007410b499a200e912180d9040149c0b54a092200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317547293 1250 317546043 317546059
    0x1b06060411090a0e04110a060f09060504030b0703230a1a09010e0103030c030512010b071401052206020d0504050102070c0608150d060b0901090b130b061602062502 72
    0x104405907007114034000c0028a01c1c0e0350f05007407250100503500081e0007501c0e07402c050f41c0d070780c98284c40c1c0903220300107449651a898540e0000150040141c417980c0c02c11000c000060001304005480a02020380103405801d022609400b1070502c003c1041490758030891003402e1038140000b040c000c1d400f00c0c00e2003500603411081c0c41d4002090115240081c40361600c0102d2500041012a124038031007030519210f46041440c11003002c882d0581224285c00c144200400014a0010000d0700e104850303089007180001e00c074511301040b0130381521249003503803540c0b110003420034400c100702541242c0c039044001000b00818201742c10458000c2d0001102203c0d1070880c40808030b8001c0c000c0483d5403061006003807050340c452015051040084801508648164450704042107942d20344215902a00c039032100040c84c2c5480100700081c0708007080031922494070301070088900d51502011142440305460340c0c9507008031248045030191048069010508030b070034400442c200305042c980880c280c000c0326602 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317548543 1250 317547293 317547311
    0x2d060105070203070b0c0c01050702030c0103051f06080105010e03010c0f03050901020403060501081b0d0c1404060909140706090501091502071e0e070302030720160b03040c06050702010507171b060604 88
    0x2740d1148244c2c080a0340c1503000008248156100390001648031034035006203900f01c680d01e4941030b800c8103c2d8008201003101c0c4401481a941c0c003540c51030341010118020b0001c10031404c0e010b020381050600241c1015107a400164230700c2c0d0b00f501168025544000c00304660340c0c0d1590201c1d1240c01560a0b08402501d10f01074a00c0391825010101c429a04400d940e000740345414400201c2d00e0007071584642254442a001605418910030645140c1c054540104540024001716040c41c04c079401080601c860f40105000d070742d0b404401e007001c0d51a81000384d51000f082040c00da2911056030300c000d020400e03180d2280718024074002030f0400c40f8111840d04929841c0c0c404150103074042101c2500001d980d1200482c060300c910514030700303078126100656085003d804001e54030907125070424158040e0000600c0308004034078804c2e1001b0200e6180050502c8070300d5000810900ca84032000c1d2841c00d02900b072420070a902d604507001c250343c3c402e9240881e00c03030740385203a181c66045540500c26890902d002c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317549793 1250 317548543 317548547
    0x12010807050105030f041106030103050c040e0d020a030e060c01021c150510050318030307030b0a051804030f02011e0b12060f060411070f080301030b2d060105070203070b0c0c01 78
    0x8030988205856090540e0b55414070403641680082c8180c65003501811070310025118000110b020754091000740411541c0407051109491800c0b40150441d4010402c450780e2540c00f08951000c1a498a0a0401c0c0d040031400943d05000d1541713080e81c0380d4800541403c0403008080e05040305802d205d42409582812014028900094030881750032100311a800c604d07040c030401c011540301c0c40d1001001e0414203002015841e54008880b00b501196444400e42007a00d88044454020a821103c02103400c3d5580e10802b031030f540141004060200007444104258000e40108210002c007080450301a005494460064a040c29070580641c0540c00c141c50004404111a441a601110200d600713888050600004103185503c211051000380b2600001400b0721070140d80550080b0f001b15165410b50a11808502e4040c3c1004603102e011100f905461103084040010454a941c28201903a1ba920060340c561085510096140c000d800c3d020a050080d103000d0441c0c0704814049980080380300c401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317551043 1250 317549793 317549803
    0x303031f0e010305120f070c060201051503011505010311040918120512060f060903010f09120804050c060a2a03020106080c010518010c02150a0807030b1c02030708030a020102120108 80
    0xa400c45d0880185051401c49074070082881c40c0c60300503914030700240364880030664203040d0050341c0141d456805001000d4071415103190280812002001046040420344c01e8101710751160505260b01d41400105507140581030310300401407801c00744442280c0ea1651512003c406a0448584c0341b03c6404c1e0404c0f5110750306943c5040e8405041c50529124141004070780400cbc44011a485442000541507640b000c1c040c2007040316a080d40404d01d0f40043c9841c109505c1002007020411501f0000c00010540000f400341714010305440ca690b9401d06071008841c8401392010381c550005d42c045000640c800380c5105910598002d82c000c00c1102e88604a00b40c03111459100503000880910154080031007485000785c1c06141410007900321140c0c2d03030104055910003507201e0f1043c00045621110107801900300340d031041851804100001e042d0000a20b031a1b0010381c0141094450b80c0031008648003003040c100038001010460b902c8000c640c8009000c0d501034a800701c800c0240d0400040c0041e80062 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317552293 1250 317551043 317551049
    0x203100b1309031b210908012307030f02091509010908010c0504050415081c0e040507080c031e13110d030212250809091f05010507110303031f0e01 65
    0x500c01c10b08981042c00b0481d41d003840101a120106105c0d8206444c40030f0143c1503480f80b010742c4866800314a449107550071594210500500210801c8443d03242c01c0406c1c2200c0e51155072824002400100361040900900918100c02d4100070507601c94003c000d805170103416504c0c3c00f6a10224800c1c0c030380e40054286e81d000b442000c0403502c14441441649029004515140343c3c1408141a450741c41c620940781c41c00b1280c021482c10140d500c102c200ca07500004d01c48144905690070300ca2400e0007080100f1105005100d0300380030201102051020710b08a861601c100b010960340b41d001c2c1015001c0405c02c001412003142c1c11844c40e9081141400c04064440e000350300764014100300c01c00384000902d180d20450540c9071080d2280324101c4150305091b05c0900003402411020740f203001500c1030081c184400b0b0920407054a0041034601020040741d0880182c1d8800e190842c1c40e00b00c1441c041626080180c2d10307a62500020080209a404090603054541000006004da26544811080c100030082c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317553543 1250 317552293 317552297
    0xc06210f0b040e1c2001060308070c0e06010801060c051606030b0f152208030409051006021c0302091908060405251208091306080f0c010e0906010c0203100b130903 72
    0x80ca0550103801285100d2003003041a0b1400071605040c9417042c00c40e01c064004961902c000704000c020b000c01003c0e2000034207000d00914656003860360010340000014801c090402400b030710b6030020044240078817007512070060b81071101161186405070252400194450054588808005241c039042c0d010560280501900ea46000c2c0038805a0215442510100a044800d4480040e9803403081004000600020700300281d2802d103007079220420030a56101000719444005049004004820911404807180c240140d84000840100d481080213070203140c80d09070760440010398020041040351150b4491020307520303014252408218044044002810f20510b00c9109100d11414009500304460240740d0040c20503281d01e00003011501c80303601002265844007420404010704110b100c1402c03080034050700ca00c00d05040000e020071454500d481c8201c0b18400030958990080560700509900501911000307000d0507511800350846044242c001c0580280c0510b034032000744100755880340c3c15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317554793 1250 317553543 317553583
    0xa03060219181a0c0f0601090c020606310f020f0d0c0f08160306090905030901030e0706121d0a12080a02030c041401030b040e0a051005040c06210f0b040e 68
    0x10f100040f903160001039042c007607889003003c035940c124000c210702402401d29650104841c121035100034100f11000c4c041c1400740340c003004194420030031010043c60318500840580401c0000d4000340001c0c00f12a09210f860910015100d0500d01d0504000d08ca2580c0441040c04a4016030404503000100ca480c4200003500c00c00101c1c0320b0001440c1c10403e201520300d00420074a44400c2510116148c1100490f8194000550341505503018000d0903041c403120406000840d1600f0340c0a089007400e8011400311550f610058010791180100c04001c01c0b1050003140d85113001454024103007400c800c159004560301c44000b408510250003101d1044200c5240107090070f01d40324440c8030001120024505041c7ca0f85c002050700d4072940305480d48003840200034012040366040950a00418440300d4144c5403c3c08204008500314119074021a001442c2c0f24800c603800800789001400500d07100540036081c110528080380303154020002c04101281d04100b10078165803402c0da10301036030308441e0000940c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317556043 1250 317554793 317554829
    0xc09131709010c0f051f0b100305090303070e0a0e09011e200d021b07091d150606070804090203010609060c0f110a030602070b010e10080a0b060a0306021918 69
    0x72280496400501c03500c21540c01040010301610212101d102030303810540d0355440c2c1c1f00103151111040b40704800342e003010405803c003168041e0f141e1000030701144c1401211501c0d00070540750040150010000c002e1103000706d05043c0540ca01802c01d4605d603046c8940e043d403810803068564400c2d14406203c914206400c504042c00989040d0406070000100540c00c5c481880030007001c05440c1c092038010b030701400c01c2c81c0c2080c0c101c408841504401c81c040600001180000980019400140ea042d84c1185280d507510b80c00040c1480c49401801090b035900418002074029454005d14169840c9465403560291918022540c401841c0d9003e0030b074114140301c0d403000c650410344503000544050700da0f201c020380b243c46510581c6c2c8407403012a05c068000d00100640c8010094150300806a184c90500140c90422a10743e6280d00d548007501140307000021076850380d180115400115030016003035450f040d010304060f501581502c0c2c01d0000c107555204000c0c0c0621480c2c0e56000381c5810841d1302c100944 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317557293 1250 317556043 317556053
    0xf0302010327050f010f020f030103060e0a080f09040c110a03030b1c03090311010c0b160e090103030e030d02070807090e120301122001080402040506030c09131709010c 74
    0x207144511811144140c02c40d081032035180c0100070390301401a0300401100a070381516900b1148009400d5803000d10601c00f441c0d14204036801caa04480d00600d010940200c2c4030001070816840d468014084000025a070000305034071005043c08076402ca030100810040c00605580160110551200c03541240c103480300042d000340d125222000c40070b0620f030381d4050908491132000702c460400390040f40c0c0140b810010400e410003201c520200030318100d00b4065041d079a9106000010b80802422603205070940321451050f0070070302c4021001040d50a035960740b41005082201304c0d80348039019009010100c2403607400007955108075030f400401400306a18089202c801032144519450031400b404012038003100d84080514080c145500e900700c28040d480c0340c0f05100c80652445a1036a4052050f840341580e0411101740d40b154050700c01094a51300c440000b0306042800c0e240380d41c8403c48100b807141034110802131204281c825040c03001c51184207800440d450045251807400525003000c1200096 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317558543 1250 317557293 317557301
    0x504031b030e0907090e09010c090e04060b0414091e19110406090524090a1a0d03020706020c010804050c0f0a0306050a09060c0305041232071208010f03020103 70
    0x41d0091034180029454680001c00e001015203994001070000130303041c003600c500d1032040c540040340503008101002d0070741009000d02c0700c02c1c0b19030f6a809401000040511046800109414100078020040300940c01b02d43e08101000f0340301001a842010380c20168404404c2c4180141e9400000034005a03141244203040c0c1002c10070121040c1e84c40c82c0030f030080798446024490181401c084085074910340100c2008944000150007403990207540c0300604141c8602c3c0c0e42c260480750318000490b5800090654160503d800d2400a4004400d280208145039011803107205858041c1d0940300540041c02c0115036a00044d0b401414540241004850324034217200320031800c5a015101c19038442c0e6a4a4020846d02d049411a400b55100c02c010300400c803d51040400720b8546003070411040c1080d807140300b48540c02c071128800340009401803017004c6140c1511700e407000d00700e09090f05080b0b08150316001c17150400c0700c04442080c850103e0440c0709001c1d401960596030f005003100042c0d49543c00440142c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317559793 1250 317558543 317558597
    0xf1d04050a0b090a0f15271b0207030303110c0606060703021903020f1203040b19020405040f02040f1d0c0307180605070201080f06060d020f0f160c09050403 69
    0x3203075107502d000e41c1038450404892181500d14000901000c1003a10075042e203500d1001c803894100301007403d0200c00c4c2a81c40b500100e000301c528103061032200d105008001c2c0b403110602200410210101c0c512250300041403019a4440c1d40c1c14800c2000ea8400500103014219458031030f81c104200003140c2d828450007414095020744111101107910025900d04915059003e42c01600282c4020300d100c5420011043d1402d100007401e481c616041c0c50b0201941c001038284143d802d20580d003900100c0b0365805646c041d0030010010005c02200506240096100f441990341d0748803009000181d05590110048178100c0759a101045a03130b8041140803e9480140040180a000070204070118050b4110130064015078803407543c3c5070414000907180203c01456000d11030312040812817142c130342500383c4034001d002140160300c40702241c01640d840c0c0501400c0720f00604010955191714240030040719201c6007e440c2641d409a255000b02007a60030450300a808114411142c4089289421201e201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317561043 1250 317559793 317559811
    0x20c0c06040e01140906010e0d03021c020f24010303120204030605010b09040509062502030c0d02210708070b0405031303060e160311060c03040909050d0f1d0405 71
    0x40000800002a02074110360404010b0a08840050021880004c480e00303498a00b100c0441030740c540000002d0139191903884c414011034203940c4030000c160082090200842c00022511403641d05c196000b5920101201c610b0202d01c58606c01e1010000f05503807005c94007d003124003441981c01c58805031001494118400c040f15400c010002c0031403039500c60a030103031103010903041e92103110404000a482c0041c00b031003240e030071800502c81404103695101c1003000c00350400003139454060354160b003503004848040c5114002c01030048003041d400f0410035140011800d11044252150007420240d02425200428030502086580c001c00c0b081444250b205100b881142d241c04444000440e9100a070781c0100c0741c0603110080140901b00030303c000780c0d1220303504207546002c5140d512400c0248450124860080c00c00180b004c684e140300b80215005801c0e5442e0501c8041c13035500e401555005201240000240c0b00300c0364001c69841a144044000705010803620f84004040c1000700a140c05415090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317562293 1250 317561043 317561053
    0x7110a0804030606051e030706080712060305060f0106081605030406090213050403110d0c020d0816030203190504050f2814040e0109021003020c010603021302070303060621020c 78
    0x1120003000780081c52040102007016407610f401e22034009002c44010a4003400c50090015640340002d00c04100d488034684080192508103003601c413022200c04281c0070504103900402804400101382c3c0c05a00300007003c8111340e0343e41d001119400000d80340c818405104600492000d4402e4024641150250f0f03800075000d103050b07001a4500742d5051400050940301d0042200341500810241c01c45000e880203003d1306202d000c0003d06003c07040d1402072007804007011010501942400703039208000030710044c8006094505001c0d540e900440100132403402e020750381800d410301c03900507103003260005001200f01812400400c4660101c41e00300c440c50b020041c4808400c100054182402050140180601e5000d80402c1c08155502074201c8042e503070502c001c1e000181c450140e1b05102038518074005840b2580c0b000440d01501b038942c00654815001d07030848500c0c0c290340e03005140d680e120741c030200446aa90b90003600c0020840400c0c5040a14902d00d42c5c29560360b503002803840c5404182510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317563543 1250 317562293 317562313
    0x216030f0909140702070501020f0a02040f0207020a03030908010b0d0308060603282004030305070f050304050d060b09060a0602030d091104060f03050f03120105040b1f030c260711 79
    0x1c442d000c01d01d6900403c0001c2c140100307140c05108000c0500740070300c0502540480000d41c55500c001540e0001d00455440541c80f0b01085140d0569068960007007110123a1036413403c3c0140340604a005002181d480c0070058900c2d03251580342c60880551540b6011240e42c0c40c42e0800c0019000240900b05c940c5130250300410708024441d5241141c20754000010307155100c200c54881002640a004010190030802071020036041020b59101c82d80c40705880711100c1180c0ba149040d40200d51200783c000c030515540d0b400f005103d400444c03802100303a40410403a0390f55010010301801510402c03002d0b80040101a18084081d008044800d0003111a48140004078000c038080b141c440e40300c04490405800c040c01080414050800042d10207002035081200c9d400094540e000184560303482180d560f0080b4100340c0390707041251210015003040303d44503a1614806005800000291b1001030070b601c82c2c0c140e04840781a85055403003001c1c00c041c0015529004140c8113100704000d081c50320710031101d0032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317564793 1250 317563543 317563559
    0x120b060d060b0d05160b040803041412061e0a15090f240302120f030414010c020301021b0111040e0f0403020a1b080705100210050417070f020901090216030f09 70
    0x4111218401e1008210003e0304511030040766100c1d4006e800b0812041004000d04c503800016a821345070803e109030b0001000c000024040c044908540345140a00b0b070410030f010507251011218440c402d02d01c20217960707030904210100c6000240c250f0500c1d15040b020f2005040c680c2c0305c10384002c5400b0002810744184001d076410400c1803030205d01e2103080500d05004500345011002c6007400d400005140c5100c85048003a204d0050b805280010200503060341c01c1a8411144005030a801170021517540820500304444c40c400a1014000d40d820f007440d0b080995079901c1141c040b240c0411255000b17880d8011814207440d0040c100760b045115050881c0041410500c404070480e245200e0009840d1501140314104280c0c0d03444036108427148480c0102041d00810001003454030045d0001c1d5641d1340c0e03d04012074982e00500128070300340208131b038001c10000c1060542c54900844030391324030307a81e0b1f0342200c0207900c54523100103804e50b5001007110000707000c1c03085001c600034207051282140c1e071110304c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317566043 1250 317564793 317564809
    0x60402160b040213050717090111040e060a0e01050105070f02061b0d0801060306120f1502030109021209121c09050a0b041a010807270c0206070207120b060d060b 71
    0x10640d0300d01030201c180021407030020088032100c811801c040c04a0b14008502400d84004070003e40060b4004c400001c0c1c101d0002e40c0314580000d40c541c5815140c41c1c5607048100c0d4908100c034001e00480c0c4c6944081100b1080e946001c1c12244d0580d40c0d645011400c0d640c005c01c01120080891b0464000d000008600342c01c602060300c034007540c10090004d00110980140300b4081a880601171500d001814418610011800384802d0b40003106421441c00300d00d800f140c007028400751258100d00c040000b00740039086030001d0010001800702060342e620f41841032a1104180040858035601c10803081c0303505818032840c0420507100803c000b600d0282600c0b03803801c1101480f422200407035510108000c1100380700c2c01c12803220040180780010b60406d110341e907941c4600c0c01303039100100b904518420900d140c80d50501441500e440b05000c940c10380c00c4040e585800644290026025a540c0407410101094110580f0f03900311b492404070f621201c05001ca40340014200740c0e076058440340f4070134054942a41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317567293 1250 317566043 317566087
    0x60405130b01080c03071707121109011d0901090b120303010e0a381903080703030b030604030f0e0d0b040506040212010c0905040e0703150204050a06030207031205060402 75
    0x140801c1c0000060001064480000c0561003031010030300c00e11400030303482480c218074a00c00c000700c00c9554481c400d0603142d18142d01c0300b1860341030078a4111540303840c00c074010b8a094442070700c5d200c4001c192040c200e00c101038011001d0340c0129400004100038681c9400613864204060200050610210b10a90442d4001d801108404021100707114420348036200b0404d003890701e158065400d0b0901144101001d10302080030400781d000000065151707868030031004225500b41e03010f0a2103650303890040f016800056003074002c2480c1a40e250090308003c98254480c0342d0513030f1b807c00c010205040070f03521200092140da400200616282002502c4070000e81d0042d0701a41c000e000720700e0b0034030400c1000340c03e081c41d08040e40d041c003044d815902e0f08070a440c0c05558003110040b07910050440202e160a060380d01c0a03000603c3c4070300b203440b4a0b403291700900075100184d401e0700e0070300c1c0c0380d035425002e0b0302c5001c0005002420140703c4940f8103a156001a40100c1c000b00050f1074104803402c80101101084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317568543 1250 317567293 317567329
    0x30b0a2d1e0f0905011203121104270b0a06050a0203043203070605070f02030a05030304080415170a05090705040c0908241603091a06010206091506060702060405 71
    0x46424414412140341d0b80c002000d8054040c80300750705091090b0001c5000c0d51008050102c0d40024045c504895003200000c0040c0302e40b201c1c0c90780c1e5900420240f800082082984200c5481c1d035503c802111070248002e0807074050440b0782500d10741007044815174415071002045000030301010810304407204805496448105164a4000a95891180341500c0c14469440790317111004c104400c0da00482030f104219048591800800d089001080c14070005280c0101103001c00030411040010364000380c003d0b64402804040c501e10100e00564004160748a8501e610041c40f001458442d5150802503000c0818819600895030321000724069910044801022603042c560600204108110038080b07803ca80c8a518080c0c481601400c9030f1a40103805200c0c4007920500c4100024080d4120032010769001e1030007283c40b03264805049600c00291440b50040c0a20310202d0140f01f070014034200d0101c3c50883d03c0f800c64a0303407010000b0310392010740201e800c20014000090655a141c0b052403891180e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317569793 1250 317568543 317568599
    0x4050103030c0b09010627110706020714010e06060d03031d01050a0b010503060f120304030803041b0603020711120f0f0309030f0a050a020402130504020316030b0a2d 73
    0x2501c0c043c0c0b03100d0001050611241c1c985642081020b5502e03a0306500000e009440007669207001a507240a001800c444040440e00010903504100080d40240007290107400820504103000e0002c0d82a941c0d001e8009000d98000008100b0390718009040300c0c030746446414001419000030071014480c01c8070042050319030755640200043c1980d00c3c092200600f0003441e000e4918500a000120444082100540189a010061040700804100303c1d405950020120380e100e00e803524140b0001c59030503424480122400d440010190b000e8001e40c0c05d43c40c4d00c01c0c2811260b518001c00d0007049000c00e280360525104c1c44c0020141848144000500204228051540c491401c13040c03518207058140740d8001903000a103420007241c3c01103500342d40b013a4101e60241c1e5950302c910a0180100c11600001d03400751001082c00041012883c02003d02200d60b1024480c3c20061010495084120311500341182d5004c0204e0030380c8170700200100795800c22444400140c0e900e607030510300c003013000b05100203072007600e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317571043 1250 317569793 317569817
    0x90b240d0212070c140c0102120703020c06040b09010e0603041e06180308060306070c0c2108040611060c0f0a0c080c010204030c061e0509210616030e01051605030903090405010303 79
    0x2174803143d030240d4551004024038030394400001c2d0780d0384c0815041000c0c0c03d008510a0304040c4280041d2100140c000c20540c2c60783d0300c07041c0200c015408131089502203103100101c2d000c90305101c41620321560b00042c6400c2c1100c14100c01640d07a0304134220465403695204880d45000300c82c2c1c2400039000b4080e0b901d280551810750141440d05030007509090502480b1880302000500d0403088a041e64022404425000382410b82c8524066060b4801400c1d01c9000c9004140c4940c80315818200607030250848005c0e0315500c010000d0352050b1045c0040c018003c200b8500114058060290700b0f80c0700d000b0301031034005003e4925089030000d40049510000301c880420150358443c0800c08035802c0211401e80700200001e01a00910400c0c1c222401054403403c02c0309100100824410900d08180a9032410320704054800c0c0d65160502d43d410220389009a1080d50720302c14828548035111550780c7ca815121407003002da8481d04000c0c111303461031004000140303440e02d5500401c6e000310304ca52504010000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317572293 1250 317571043 317571053
    0x72a090b030f01090209070f03180b04050d08090d030b0a0504050a05071706060304060c0e031f200a210c050a0807081b030606041e090b240d0212070c 66
    0x51200c0b40b40c2a5a041190501c013680c0da11003041c2e088903541c10861072460700d03140141d02601011074841c1d98802054a01401c2c000c1d01c0396141c2c401c5101d0340941b8540b0210202c01e17100d6580c00c3d504c034551640000705940f903590013648492803500c0020a240c0e0a15901d000141c142c400440303090b0103031901d9030b00b0700840c19040140804421030943d004802c6250000c0030a480d400020800741c2803a45840d1034000e0f56000d6602185070b18005019507503e012800c000104503680f090001c0800fa20700741c401c410000c9510750210703541c07801d000c9040c070700400000101d0b101c002d03030b5044102008118845070b14003942c500c516600050b558582c0d48d12105d400602400201c1c00500e12403c1c41154010484c02e00d601d81e00102c6880e5003e51120f440751601c034041005070041f50022580c0e10072050740350041107158020380085404d110410f01032004544184107500b464079001c0003c10b01c2601400788420500d038040c282c3c50103038550041c28199203100e00c01802c0c400f43c8503600802d40b24072505080c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317573543 1250 317572293 317572303
    0x1101021c1218021206040c060203040305060f07030e030a020c0f150307030504031215031101030606050d200f090415060507020d050c10050316020c0105072a090b03 72
    0x18810100840940c040d00c000340c100c201e91a080500d03265190100d900401400d00c4410034550080d00d420a954101c0740c10a07034034101500c080c0c4000100c001c0010715503100104485c2501d81c4507000c0d040c83e80b202c003030300000850003800071002d00d92a01c074a0480700c0c0c020409041d554486034014003400b0850402e211040bc45200c2c494000d40220214030701e00030582040302d1700916145000142c2d9030301c0d4102198256074050b00307603a81a040c02d6400c1c09880c06407078800140c0780100015602850030750019401c440d030701d206210100340244107282c3c898009034068890107803d14180b8900c1c41c401501d1544c540d02000081403000c002050a08103803c040c400d07003070780e10358010800c1085824081d01a00c03602880030000d10803007882640b002000001e02000030200c002a150082c040d644d0100034100350411521010b4611170400b1449105100203091201a01c06840d141d00c3c01a0310b0f10707086680240052000c480820780b1645003c14002220030000422804000250010318001054101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317574793 1250 317573543 317573563
    0x4030909060803091c0501111b100e0a0201080714030c19020a050309100302040f0e2e0509090f060a150803040e06010804050f010c03021206030a171305030a110102 72
    0x3d5209000b48040d903141c4800300450b00751150310600034101a45445800b5082008030425a004042400c0090305001c80303000289807035400a0716452000050681704840641c4805030142d4041000340f00594001d480c00c035000030903480c5c00301681d088100d0030480c0f03034402d490110b005040007540900803c030a2000500010592000d03026103001034480076a2400741c500601d200d0000704036106616030081d4101c40041202d5025a03036015174888400c8011502190404170102031001641000300400142a8061040c1c980d4001054100700c144030100c02c00a00ca006c4c507208440c0f0b184803d00080019500c615a03403880410001540c50204d480e0688641c0040a01da00501051001d400218100e5070311440c01c0c40c08040d550f9a41c03e100e468111000c214143c6940b030302c20500200c0da45500200300382d0000303080035080c0345c0f1a2420306a0301c0d0b104c0c01000c0c000048030b0a034580c0c2c0c0080d841c010200200030003030380c00c41d05840310000f034200b1f00c9042045802284502240503d560188038900348 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317576043 1250 317574793 317574809
    0x30c08060d080a09180f061e0b18040504050606010e0117060d03090b0c070501030b100c020d080408010c27050306041e2405150d030c0203070e0403090906 68
    0x11030400e140841c0c025010000014401c810109055807480d208000440003030500030040e9055101440b40040244a003407030f1030000c14204040411840c440d03203081da0000d80c0c0d5080311030105103840e418816941103108103500407034884e8020f4420740d440380161400b0740e00650180140b402c0003c005020f808550100d1414403500c14107016205540e828401d60265050350242501801c07450126800f11030340d004400d41c03045c0803031843c021503030000c2c0f0b480a441d42038a0400c503861114080200d14580000034500251070104050700505100c1c014041c96403041141034281500c0303050603800d58001903011350005020085408802d80701d5424030401d204003158149016007441e0100392244d900030406010000d9140c011003d03c03604200040ca09900580d02030f120422401c003009480440c0741000c1a40c2c4d0400c40407541d11405800f00340d041d2200108820200d80e02586c058030600402082a40c2c54000d02130005400e4008e020918400d038480c2d9900d0101d40c0c200203881088503400e07080284 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317577293 1250 317576043 317576057
    0x20105090a03201903170705060c03070e0f1e040f0204090b0306100302010f08130c0e0426220503010e0f060a05040c0303050c010b1e0310090b06091e04030807030c 72
    0x40342e10400c0c3c1d01c0350541e80c010700e80c1c2040250040d01e4002c6c42c0b02e001d5000309684500020403002241c928003450281041382e541c541e1003000c100401c807403100da20100550010100c46000208003460b1251001810081d10110b54003609007100d00c12030b040b0381c0c04000c000362100b1047c1010b1405200351607018416415002106003107800080146030207005109c00e014803640450030f807070348404100f468150301000307105000743c8540903030f40490800e45045a0040c524001003041d080c1200002d122400c1048059041000f5a205440301542c1c0e8034040b45240b107550740c007040783c0d01d003800b40e84001d00c01d81d002808880004d03100b4a00c0c11000030500d03907059103040d083c00b000030215010001160780602d0100c3e03d0f0f0042c1044240104003000f202c6521500c0d2a141416035009510f00310040c80089050b00c544070a11a0540c0560300c001c14020045038501c8000350207481c00501082c2c000c070174070a03500f032450041001c58820101c291030031b901090002c0c040140807076040c098440c0145103494408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317578543 1250 317577293 317577319
    0x403140309031b011e020115120b0103030e010c1202071a0a08190204030213140c0703090e040c230102010c0f05090402070516030803060306061815150a03060305061b070609020105090a0320 83
    0x84c10034ac20601004040200e0201110b180da84620131030010541c004454911803402000040c3d07550030316202f0751701c10005195000c41403a01c1d010907a454800e003501c4448240d900d080151610150899070303010320036401d10020026071907070000c07070007040c102d0303400000c032443c400071000c018890040001404046c1004601c000a9006501d01d040b21340e090260303030703903900c6928003a15144500e8200849400042c000b0303800760481c041040c0340307040f82030b002044031422401c02210110365441800c00400c00401c40002541403036030082540c280a10280c03540400d001115602d5465164001d4408400c00f205129036490284410b0380c011000b12040e040640c4070381e148203800d640042c641e500000c3c030301403002550307155080c1d924041071070b0408056413401846000b40c000c000e41d004c00e80c2d0768441c400000d200003100019080c03218510101041c1083d00756900c5401400c040349080741003020500c8a405103444445040029612806004ca081c0145414114108032140b0b03002d4414038031802c0034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317579793 1250 317578543 317578553
    0x152d170706050d06120b061e010c08090a0f0f03060c030902181005030d1206090504050c100201020405030102070c03120e06040b160213020403140309031b011e02011512 74
    0x5003048403218203040362640d00c03007000c0030020300c0a03a1060040ca44014140010401048002407260004035510201c03000f5501c4c01c80c1060021001e0f4901190b8401080d401060b6440c0c09441d83c0300c0004d00440c182516041c03203003401e11003a1701c03d450b01c2c0783c4d00b0801d008000e503d00410041102926081000c000c09400092248001c0d441030b15440d200e02d00402d060711010400b9002605002d422100fa10302d079680c000f4401400c1803140c14249140000204403460680503c0707000b20340040c0105140051102003041400140b812038041d590300b0040065151400e0004d0102d02c4e00444414440c280345050800d006454002c42c0c1e020880d281c4509929a0740345001d4a065800600900b521340d01c0d101444103881001d54030103540594a40e08a41d9a40302c260018400c0d82e1242084030481480c1f403911039517900440f24040c2d81600190b0031140c105c0d0780d180c0d100c001440c0501d0709031491100ca0340c0e1143c07116140460600141d441d10003503010300d40304070f29001c000c001e140482d00010f03a0a81310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317581043 1250 317579793 317579803
    0x306140c1207140c0d0807030b0d0803060411070b040b0106080708090d0e0409020d0807140a112b03031407020a030509040b03150901021206010e0102030d152d17 71
    0x9030b1050003100540d0000f00084001601c00182d4032008884004000c0300020309850000c035400c0d03001a003005a192581e0601529070035003541e121200340c1c210b44a4000b0030005d404032280c9026000030a0207014042070303645002c1c07070151380507106203111541001401080301100408a20521a040040c8100c0500010704040c14103410b250030170280409000044c06000f0aa501a500800d41c117860390038040540001c101c2c130b9103d0307020710040591081035107843e481e81d250040c3c1840c2025038269020f081990707009420781d04441000200d03080402100014650844003640025a1140740329822848007a480d40c0160090000740b1400743c1c1590000c0c110300c2489000b60045884020030f21540d1400c1150083c80081412400d10b5031034801d078014001d40100c40c1e001c400120040210341030754010482580c030003a06a01070761602e104000c00d240038054505264074500000c2c9800118440c000b000001048003100c0c0151081c41c004228034001007468001414214520525841150340060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317582293 1250 317581043 317581051
    0x30c0f08040b06010f0201060b130f090e0607030509010603060f0b0102060702010b102319090b03060937020702030c06040b120711070306020306010810050919090c0306140c12 77
    0x20b82000540c100315001c038050231660380b00e4200b8800220305042c1ca950450052005e840c0001d90320300055588408140695402650300c0c0c11913040b9401143c041c0740310b500302690240c03450b80046044c517507a544100c1202c1b0002440d41800c2d40d0340f05103c0003507906210780c94000345a44002e010320b55001000542040a200400c0280140d56203100b41002054182a03100080c40058035240c0d1940c031525001c01014826150020381000c10114600e4500e17000d0742c1c001c0801800d201d160b5650318058000400c400600800d034441c40e01361190340c450084101d000c0c01d0350041000b41c0c0300c060f01e206051034105004100c40c40303040d00340800d0007031042000c1640d142521508203c08103480380380e0140c1e09110443c40b80429802000008024840c0b15001540151421782e0742d0501e42d5102c01c03c031171300405240541c0c0c0d880342e0600041a15404101d8280701250040140007070554025529554401d50540c0102c8845807268641c103441d210507030307225034024401c0302054640f11200300c5810781c00800070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317583543 1250 317582293 317582297
    0x91a0901060c03180803120108010c0c020d0201030f06061805010518090414030406030603120503060102070b2a0709050105031207030f090b0d06050a090902010c080d0905030a030c0f08040b0601 85
    0x140541c1c09042c0b003113401c00a150110003d10403400c0d140c80c10316403039500c03c43c10b0071006a4940e000085001c0148138117100e100340c0e03075550788d070340c5807960f0800500310032006081e4101a19602107103d0500c040c03007010014041d5031a240290103102070180402841507004905101062040b4882e4032000703104d9103880c801c11203581310981c2d143d01c0c3c8080c800000c184e121040340f0002c0f4000c12016099400300090764081d071800c454941644070101c9851204039500c44c010b8000900820070192003401030442810246002c0340780700c20560300003080078910a6860b80c9984100c002304045450761250a01502c000c0d03024050107122810b0300050f91042e1480101044100190241e90510070250b2001801c0001000c0ba42c650052401001500c400c0c040d0754032554041600081c1885203102d980800d581c180c41d0b1040b40c82031921b400159810624010f41d10b1500d503d00500040c0040c0002c240c6400d85440008811061040c02407080412030b2112051006072001c2c0000b184001c1d408651101c024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317584793 1250 317583543 317583557
    0x5190608041e08072901060e0111030912030715111b0c040e010c0201050711070b030a0f0905060f0105010903080d0228020106050f15040b070303061203050301091a090106 75
    0xb000d00460810040c02c0080c01c8014041343e8101080b14140c80f02c44d040c03c445d43c29205611404005c40d4524400b0700c6084042003404002d03040341d501981e0340061070180902078074108180d40c0c001c20b101003c82c04403059150000900721040210f01078214145500007541042a2148440b4003a95803142009081460300303c85000c1c020001c00f0803000e161410702900511002c41e00702090781c0a080340c41840f10240d401d120000b0b02a0380305084191300e03240d000c4014895a490803180e401d8661018115541050b1101c1000e1401d1080d8010300d400715200b80024102c62500704920147d2072010703080941040b50381d0300d04001107035601060724001001c000c0010f03518003010000f80c80303819008401d18858010341200d803401030b40660002084800589014040d403054200700701c03044481d04c1280180c032900f84800e00c04000d810b0b002c0d106040c482d090015005803140050102e89411040440c0080d10000c010f024960f841d0140f8110a1180010701d040d0382c8581c00002e00000d014001c5008108003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317586043 1250 317584793 317584823
    0xe1e070522061e03090209150a0305060f070f03020304050d1101020915090f0301020306090f040203031b0705010e06070c03020103150e0f07080601051306050d0f14010519060804 78
    0x100300351605000c024105401c40640d80302c202411002c03c004101140300b049108280405029001d10304090340e004150000d5541c50004443d4038000c1c0c0c0c0142908104484008000101c0c200710541c09100d031000c480c40c5515203140c2c010584480c060401c030405005205100005400290010301500c05003005030745114842c0840d4024010701c1c0007d40c2c450240115003082e6100c400c01406480f00688404801ca6144070901d401d030b00c0141c40064205a00f1400103213031501c59000150454801006e5078900004010120307901a00102c000d6910340280b401000710f981c100c02540850b0b0f20903550303982401c485840d419040392040c800039050640b0781403d20341e030394044103000003c1c1c00c46003044101410038240e42c0101890850740c101c00b244449000c2241d56002d00142c4200c40c1241003000c0c0f15505040701110750344c00103121038480d03945035803400c00c3c402c1c268044c2e5001072481004120132503240c03004104540382259041c000c04825000c040c44200d900c4a40194050f812001c400d0490305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317587293 1250 317586043 317586067
    0xc10021207080906070c1503090c0b1806030c040f0f030803180f010f0504060b0603010803030412030f02030106081e0c1e040906080a030909050f040b0402180903040e1e0705 76
    0x12840e00000e6221000181703545c2007244c0c0807603000c107440424140d142c2e0b0a04046041e030484c0c0c1c17481070103440099400d204005400003400103000080b001c4410f0b08106c62480c1c0481c40c607030000c0c2c030701d80421744000c40c040c003c01510360f480e41c00610034a0100001c1900c3d40d01c070b0901910001e05281101c5007005d4410960440c1004802c3c2c550b070440d0000c110100280800303800400d025941168001e02700741c44112a441d288007680e0594940070082c4d46581c50710307541c4000513800d0328a81d600303042d19103440c46440b510701e2015500030701403601c130102d0902d00200400300d966604629001101c0266051042224614040e20501607840c0c40710194140000d0032240d0354003e503441145c0b802d0a045021800d65404240380780d02601c42d48400700c0381e81c1c840328036205031041180c4450b4031a89210024000c40d02d070480e483c0d00300303001400076644481001e10802403204216403003001503000041c03c21404504149135503000c0c220300c00da406404840c80400c40b80d00c4c40500110200034000c185e2800080b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317588543 1250 317587293 317587297
    0xf090c030106230f06131d010602150703110304060b03011803050301271d0f0f1203041b080105090d03020315191d01050f060a02060106030e070902030103080304050c1002120708 78
    0x1010040c0070311b840b041000c210480340c009901600440d81e2a6124200044100c25a014140c4d40182c0240084403550004540768a00c001c0c21101015240c1c07100c01c018015903801075000710300400000c985103498405143c00e503001200e582c0c410312441345290b004a548401500d066034042c2081c0200b9051100b80100040c220b14201e070441c51400464140d034030040d0180d4801104d405003518450040221429124180079000e07400f0340d0410b048240a001181008590141c4603007280030300384129201003034100d07030142c0020145a55032024080a4041004880760000c5c02d860250301d10310740a001d041540311824400d6002e14100311200d41d8448144240c1e0000d01a1007000c9a222003522140d0580113a0138030075a4080c480f01d203220325070360400c00d040384d44051b000c4e0010000342c1d1800c40100e0092200d10001002c50040443c08210007600c2d000440c001c50241911b1500c0303081c14102107040c00380091940d4880c001e100640071007180c002c500392080b80d803112200c984400e128140030301c00d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317589793 1250 317588543 317588569
    0x41415060912161a0304200d140f010b06280e0603090105010f05010504031109180708100e06010806010e06010203040e090a030f1407020409020a09050f090c03010623 73
    0xb4042d40c0c20500c28003641c0003c440c101e500743ea00b4207041a034001d500300b44a2100342d8020301603081c00484040f00c4103000d20400ea111001901428002c03041d9203c2018501210f0442c80150300201e100500a1009000d0700c2141d071340c2114082d1818943c6103a102503416540000700752607034423204400e80c45000b08580b401d0900c0140c0f005540c0e1502d108154020902405841c0e1201d44009008c45c207548200203840550f40c0c001001405c0e10491010000d082c1401845103040802c03400883c0c00f00003081c80320600a04404000f000c08144103004a02a2943c3c03c001030041c3e405503004021164000900c241116040080c68520303032100b40c0102e08510554001010003062441400b0003a90300003080c011290080e0780795103102c10542e204648107021030310440180f40040c03209601503d0a54803113007900e840101054503455958242d0010f4039000c0b0340031143d0340e01500c100104684203100310300944000314000c22005041a101d0200159901061140c2050403103110b0350036240c0d5131034100c0c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317591043 1250 317589793 317589829
    0x2040e070906120309150525020402040906090b040e030a180504020304031e0305070e01180e090a030f0807090308220305033007080705040918020414150609 69
    0x6290b201c4600d820f600b10030600450000c0c8440100160f01d018100e0282c01503541e550f1280d182607841d002d02e07031981464030107030340c0001c900001030070040e50381d440148014841c1d0381021034171524000d8100f04840f40b000f019406103007071900a1059400c04800c640e0300e0f007424204404c0c0c0b080070719502c100504542d001203030494130000c01d100c14550040c40c07080e48414030003070001c0d24602d001d10860664a05550400200d0282d02140d11203600079100d40c00000203d02040d80c41d20b50703440b101b28024009607001141c1e5003144c1468001d04d58001c15002c010304181c20548151309010700d00500202a921000d07005680c0031940101048100b5204200308910030800c0c2c103c0d03916800e00d10384a0b40302200f6900818046512482990510088101c030006444c070f42100a68030b07002c7c1907030904801007080007002010000802c145540b40309202c00b28802d0700c2d660204110300d00c1030008a60403012004a034002113400c01c0710039144c290641c201c10744240c2c4c803241c4900702d000201d208500c60444c0100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317592293 1250 317591043 317591051
    0x3121e0f04030309090c0e0d0605091501092414010c030311071b0914040f02010201230405060f010e0a2414041b05030a20070b150f0102070302040e0709 67
    0x83c1544a00034a050f43d000510401040b5241d18059481b0005281c650750410102c0000700b0104217a94031085e40a8000002d803403105c50100a1001c041000340c010241c400da6a00705c10100312002c03409460485102d030000e4444505106034081c1489039203107071504004010030301e04d04141c0321b0f4118195030404030b407c0d81d865806514180c24140411848503071403403c00580045d0b500a1030042c89608003484a41a03002c0d110f030b840d08100d5110f5188164155906c079500e59201030101446003000001180200300a0300b003520740b02c8d00704100680711115000c0058018045031014890880c2c10841d18000043d0b2508081000d6204441d6074824020f660141c1100003801164450501c15501d000c88081103101c0c8070651250a0020711000400050018000036032403624941c02940030744c0318440380c0e40701f524103003503000c00c02e40c45a0b0045038208840b409201910745202d0070080031a1089502c15401c4000d900001d40d14400c51002a20031500c800199000355401e120400c09000318090602c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317593543 1250 317592293 317592299
    0xc04030b070f020c0a0b0a120b0d0b190b010e0111070f060c1106030103050c090a09080d090b0603071a07060209040e0106051504060903080705030c0a05010506030c03121e0f04 77
    0x7070155844203041d8005402441d44011492400419817020740e135002000c1828004002022104914107032003203561581d90b110642e0650b0f49911f42900d2283c4201d51a220b60b00c1d143e0040c144840900e40780c20750311420081c0c810003582c1c00c038403e46801182886d0074070496103051009403503e5034a034030032001039665000109006078800ba00c103403010302909584a60031904028010584130034400030b0000c1d0030000300060240350038a6001d030010604079020030020580e8441079100d501c0203600c01005070760b4045c08000c1064124000743c4c84030049004c0d00e41c2134070b00695010150700c16510b6410b502400140a402c11202c1d82c1900d0b032000c4050400c00c443e140a0384218001c12640c05100d1190048480700501700003800225400e540d143c1d60340700c21403880c0d5071300e19880f50001342c41100c50f400140321440b5601000c020700516117004d04008203081c1060005c0c9420110440c07040d074040c1d0415980c00318440c01d58011210300d02004c035100501c003803c114042056001e040306d485180d0303074001800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317594793 1250 317593543 317593547
    0x5100e07030b1e2a1216020f0102210109090507050105090406080f060405011d120a09120605160905150c190602030403030b01080103023106030c080c04090b0a050c04030b07 76
    0x8007403411100004181144c0703102c080808030b000b90031104207103544880008040d190101e8445010303401034011128018060260076007a86c01c80084081c224160781131100384103404c1c2c5c01d00341c014100c21404006071521519440d03203c00c1c25001d46814000002680d50361612594898001401200180c0390301c00d2613188a01d44441003518240c64a41c00c040190120781c12581d0311503c00c401e00c03c002c080441045596600b950040c0071030005000784160f000030030400c0c80610a80320361140034001014904890602d03620b4410001e144104540404140441d480341c141d0080041d002d4051246ca64010200082c604100c0f5248c3c400c0d0f070490f900c001410041550050350040c2d1007901e05100340b030642d0004503401402440081d50011018010384005248610030210f00300907004070b6000710030988000c806681c0703264000c40d90803030001c604102d140b10600207002002c1c400c070340503c0044207940321401d2694001e0050686542c0e04c2c03000c210981c0904080710300a5034481d18255180c9064840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317596043 1250 317594793 317594821
    0xf0a18050f090a030c0204140c0c07061b0206130b0f072a0b030415060f031a040803010515070203010c0e100801061d03030405030a080705100e07030b1e 67
    0x454040e00300030201d0128032102207624800e10100004060082c01e6032421202d207180043d0980e003182c2e681c001e081c194a4020006171241008071800c03580c0d00710407100180f03400d0315070348032504000ea600064840f125080044241c1c60f50125240c80d2102c20440311441e800000c0d920001240700001421120425000e028ac41140d00480054010202030030281410000c0c1c421030320510b0850070018489a50345d90301139500b2a0180c0c0c4155a191100139002d0101c0303040e034019902ca241800c100f0001c10003601c0c2c2808000300504a400c032182015500e622190106000d050702c5203122000913281001080243c800c01a0018001e0105104195000d08035003403030301ca281c1c001c143c0c1c1a02004898020202d240c121511581d0b40b24246000f240600071908a1640d01540f40c003003000005442d603400c114140015002e007544540d51011460302c1480c00c050040d844180320308048902141400110380d50007100d8008a08403540c0d81c407c0203801d520824010072030700805681341485a54074003802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317597293 1250 317596043 317596079
    0x10507090b04050f01050c0a1202031b19020409050307050105011404060501030506090a0c03060e0f0907080a030c121416060e0102181912050d030b0a05010507030c020f0a 75
    0x1194080252582207000a52086004558104583c0030b800401c0d0752060004100140f001e8056840100041d9149040da40820b5000c034016800407508055071440b800f2040808142140108642c2891100700a02407003031074006032180c0d6445c6042000e004c0d00b8412150040c0c2c2c8500200709641c2c60340b50714041a440f1201c910301880c40c001d404581540644180d5004940050001240e0f40e52007a039980605010300343c0078105500d5103000240346004090f914002c024481d04040c852074165941c502c4d080540c1d0000d042039000507081c101003a04030b8410051607800c09898024414414000e9418294403101c4500e0380c0c0c0005082d941031144404032400c41d91003008207001004c50203c00714240d025185150008201c0440e642c2c40b075140006804200d0b4144038030310800c260303950007002c88580000d10241c4a40d0050f0401c0b41d060b03a414032520030003103001c80d0780280c002d0901d80002d03ca801a4607008040c000015488010340d80d907442e5403e00722074024500c910035074417940300918820b5925 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317598543 1250 317597293 317597297
    0x815010303020d030e100f0b0a0305010203040209100b030406020d0204170d020c19050402090f09041a010608070c12020718060602060a0e06061e040204031109070c0308131b08010507 80
    0x540c00401034800d0244e001c0c084101c0c001006c0900d07080400038000d00000c0465148595510171a08003511441e0288004600402c0016143e143c58018000c00820081c20b10304107920004090020040b03d60036642c2082c2c20480061700c600074003094400030312560308001c20208071500003c000807030000e807854050b2116801d40304510000e00034028402c0031058503103031800c84088103118074107107a8098940c00400801040ca02411040450b0795130009540580301e100e504001490aa0281019103004142c246004056894140c100500c4180b215000912003e250b904c0040c80ca80700b00001c2003d82445100c44103055502804040200f595205280c00341c060100051205000b40c414803002da501c5a0207810244ea4109c01c0001204245522000380300c403400e0300710a0342c0c45502c0540040d51280030b00300f18003000742080100014006240f1002c010b0440240d10000340d1101340d0540182c1444403415810225280c0850041c0c0030106c0081c040b04039400003da92001500600d000711856 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317599793 1250 317598543 317598553
    0x13032003010c02060105030303010b07020d020d0308160c02090403050307022b02010f0603021c03140f03060901080604030c170c061609080d050703080711010c0206010302010e03070602120c0304081501030302 91
    0x1503000f661035000c24800c45506030070900c0100850740c00c0303000516599100902001000250b64009156200842020342c0011000010030200e0038540c80d2442c801c9082c0d00301414a01c0160b40019074500b0002d000604200c800f0011501c018020416005001c0e80903a101c140002c8003c400080402c400741180015820a01444500c0d0510310502c0240d980203480084204e6000106001c2011a298120108250049012503200440000d003084880d080086650b905005c7d080084040068108403115040203040c000001e4204c07001d900310941c0032a1101e015040d0842d441301030f0140410042c028010740d820000d40c604c2031506040507058540300c04003002d0321064040c1e900c0c0082ca0303c0c0e402040c0204200000300340a030140c0e6034801b005181458220b801c0c04e40c82e80c00d440648a03508050b87c00400140308642c0c0005403490800c40070f6009048280c1b50540095903036005070400100135000190ba2441c190b028800c540c0a003901d2011960340d00b00d16030710350700081d0302440306030018024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317601043 1250 317599793 317599811
    0x10906030510020a090503030a020102073309060612030806030115080d140906070f02100e060406030e03090613080c0109030c0e07170c040e1003171303200301 70
    0x1610412040c0d9030404020b0021030300301c540d070b0320003580011003603c1480043c10000a1a41d010401005a86010350016131100c4092620414040302000c203040720082c00300090300c0d94610181c884804102941b00414041c4090520000404254204041c0103810313040b2002170641141d9040c0c0900c8003500204420000703440244d4030321240c3d01440a10b40c10410b807030440c2900c18107040342a0070001007860300c1e01c12034a0002c0e83e558024001280d0f410504a950011341c5403041050800c05182c1c24180c258007048000203a89202e0f03802848240b55035407800ca044440208143c07140b411007e0129540d0300783c4410303070310340f2408184140c0340c1d41e2142801d4110300754803581503c002c42c0d610400c2170a069013460700e64103010740005d10702810003c0d04440c1341c408400400c0068022100035a40d26070351800d100740d407a9182e20041502d02c4180c00c1030020030020b9409117030001d030b0030016488141c842c5030a420a2003107190070751014006c0c0c000502403030b0121600e200b40180b0700b00120000c102c0d20700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317602293 1250 317601043 317601059
    0x6010906080604080309190b1f05061b070e0a02090901060c020105071101020f0106030606050f0109140f12030a0201141302010f200102031006171302060d0603050a0b090601 76
    0x10060282400c0e50b0000b030045000254024041e507006190842a11580712103804400780544d1103440665500986206102c04080120030070100b810b40b0b0305101c4452810540400d40e14481c0c0500c00050030301c02004c404030414244a403a0103040e0a880d080c02c907060a04164000c0d4000a21051007944d0103400002e160b406007006000c0c0c0e50341a12058200040e5031104090f040618000310f040d402600f00f16a9502001c0c0b1074000694131a82c000141c060410041c066100309021285051245901d070902c49030301c0b1031034445c3c01d0903405c0300d0888444801d14003054031045654040b01f1540320100715003c0040e010f40100910b12000020b00c00c24bd80c5081c0502942e01c0400c8019020454207131b60740480758440c1e81881024003211940e4824120040c00044c00c903802140c0241c80c40b01c000700140a03050b4490000034001b00244582c01c2c1c681000341c6500242e40107401c0080c450341c40020840045001da0b08030200540d040300690f8070400083c10f1501c4409001c40e08140e250181e44004180c0032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317603543 1250 317602293 317602301
    0x610080c0603040b15060c0a0507060905060a1e0c020d140105250c06020c0a0606030c0b13060806130603110a0b03070e0f0609091807091a3708060109 66
    0x1a801c004100c500351550ba21001c0c0e10200d45e2819900b01700100405070507440c0400001d050607200f8401482503d1810400074a550040d40001e8400d050400c0102509680682003a907411208006071856004080301540c400ca14124025044490208c0c050f042c00752179031415043c035210900078092543d444c1c00c41c0460040c0402d00c02e035110403203085050031a02c01c103c1401d12034440d0703030010714001c2140135491400414030303c21207409031a48814000c014490924030014001031b0352a500b061f44140082c200b0901074080da40800c0082000100165250b02d580201244885c0d000c005158880c10107200c10601202440d0142c000c03d0000030b81881c0e070108503481400c083c0d545280a014100c1000344003005400c00c1c0d6403140d002d100d1000d0796950400c642d4095000640c1c034000206074000303214241882c50740a00c200038540400a01030000b010b03a141002c1e841110f95641300958004403007035649920401c0800d803a00d06400303064030a04000d880701900e0001c801c4550710f1b0303650b0004c2400d90b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317604793 1250 317603543 317603551
    0xa0501050d0305070606030803010b0c0c090403081f0b13051e31180b070e011b02060c01050108100b030a0f240c02010c120c02060403080a0b030610080c0603 69
    0x2120390786089022910400c0a000e0503842040d012907410b90b2a00c41c0c2c00550000c0e00f00415401c000901c2a101e05403c115440c490781d07044d00d01440501e0303d9200034044c0080181400c2090100156400c2c280c00c80c409a02c018040513425107494000382c000d050140086030040c14054003902108542010a0054404100500906880200508068a521940e004054412680d103e0000d000464060303000c0c845000d20b003d44551104070b41d85c00c150811800141c5001c081c03084042c000e583e45d9034001100401c21425200d90710b10040b0364130100700c0740d100ba42110401780d46420000300b0102d4010a0142c4007805150b401d1140c035450740101501c0c0c01c0302d40ba005000840056003400000c26221020300114140c074022295154101c100e441034074081141100141d65a0600794a07441e0002000342c2c100396600000c00820300c0e03ca001039980c0c400908082c0074003010302e0000320107403840d8005000c889400303826901d160504985031000c01c5028018006039000d4056034036198240741080e01d01c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317606043 1250 317604793 317604799
    0x9080c13020c0c1f02070f0e220605070c0b0c120105040b2101090b13080d050613140105120c03190c0e1e01090618020d0e0706170a050105 61
    0xc20003111104000940c40a51040c1850003070412040c000d6403100c408103000320100900e60912a00b600000341080744542102d081200e120310240301280ca82c01d0990392140c40c084074240d0300d99040351590224482004000c1c6450308103001c10604c5913002c1d00184d48184200740440e0340c2d443d000a170607690702803131114441e9400380400401191426412800005e000a410400207821003c03841d070001062145041003a034403002000b00300240080c00e0b035801822034100300011200c0b580c40e46c8541c480c072480003480035229400b0812580d948030341f0050075801d1240401c86092000050050080244a420300c80c1c115008000c2c04104081003810b03480c9001005024001c0100c0329010722042c15000c10b4400c8420200c02150f60010660342600814000140c1c0c01491403242d2480813840d0142c01070741c1074a09180c801c2028140b02d400004503110b24800c00750f183c0160f558800300402c60507000c2c1c503081c400e2002c0010307001c0d0403411504e007055000c2c41d002010303a40e0800900503502d0038422030350 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317607293 1250 317606043 317606059
    0x30d0e0f0d17120603010204050d020f04060b040f05010e040c080c0f0403050303011710090809010302070212010f0506101d06032203020106060f0207050a050907020a0602160309080c 80
    0x14851500c8034005405200051400c08104165252845000161242e82c03140c4100003a00107a041c4805000a07405081107000790300c0c041c00c142c085900460800c0c4000d0082c00c076030781c01c4e20780d80d51260856000f5102580403903450325500d07000c80c5407980703083c030406000c14102001020242850f001e11542c0032003507100c00303041c1d03151281918060343c010704c2008440ba10a100120010307c09000a50007000740711480c11940c002c81000c2401c0204040d40c0c0a038003864002c0e003000090402e41512181102420016140d10300390001c05c16201000070001d4441d468181d941c2c00642050307004502070070090300d108a6000c8001000d83d8401d07110007014260b0210720000254500e425070040d5481110034507240d1110300311456200210718500d0b01180503035100c0380c0078003440b03a2002c20030805801310f1006007621840c220203d48011018040c243c041d44940000908142c000c0011240160307125400315661640c1030f800c042814103029045000940a4000040c8064005901d040c0840f004000760 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317608543 1250 317607293 317607317
    0x10618060f0b0f3901151701061d0a0e03070302030301050607030e0d0f0314131a12010303090801110309030306090411030f0714010c0507060302090102010212160905030d 75
    0x2d00e41108811001c008800c2082014460f2101c803002d04005203030018015400b4203082408640c00c182c061100c80768541002150280321000c40d890403140352083c41030075641c0741d0001c0c41c05807441e81c201c00d100042da00c030704002c0c150303100307844078480c18400300200080440e18080680303d120b44600500113900c00c0c0010b10251038054010516103109041c0030a100d0300100100d207050441960654801700b01c0c801007014140c00111240e05480b001481030302e040303100c507040c17400e41c1c2d898061103034b0810282c400c3c65061442c11007120300390045800880b02c0c80da52440d0040c40301312580211640c039420020111026820741060368050140680039604669520f030a1040300100200b094803120724001218900351014040b40c061465203501030100f640c00e0504031213405079180082e40c108001d0000050100d04040340c03113800e4401601d00960b0b1034100b070700101c2c0640520b96200001c00071041c248146801c0c00201c007425401c141c1c071034110186c0e840b0101501c0702e204a17109400b1542e020051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317609793 1250 317608543 317608559
    0x909130c060509010c021002030702010e0604050a0e1b1b100903050703032f09010e030705060702090a0b190e130c05100201020d05090a0b0f130305090102100e010618060f 75
    0x1803c007207407040c0340400c1902e1403a0001010403181800d80030240e00001100000c0d0359100107250100707682521007910349443e020210b81840105c0c0300b05510300100b10007189080d420102840c02d5103c3c008000c3c1d858020500241c0400c109140846866201d00314409500201f1401900015905502c60a00b805007540b003d90281445c40e00006c3c1200d120070301040c07512000c03101c902202445001940c1c503400030070000350030403035103500c05403080e0300c4a8020880e0b940c0701c00071220756070b905036041291901c1350541a0090844d190642d13078056030741c1113402c03800e1182038881c0d81107a4444a01c82d825845000545900340c48030030025054030300030700003407005003020821038128250501c001403a00142b40b03034407421180301f940c0c50446600f0a09000c010f108150b880c0c1c07a0840c2405030840d55500b440804100784081911004040c0800815090610b0313009001c80e00590b509100d040c04210400c0912600800b400d02a090303d0032440001c00c81c04903020b100304410703514200300000c03e050418401c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317611043 1250 317609793 317609797
    0x609060604020d0e10020a120204030819021005090a0201270b1803030f07060606050a080703150509100f06030b0303040e0c160f060501060c020102030901030c0210110909130c0605 79
    0x51592510058030440c1c01c200710700340305c040303040c00c0c0140c441021a500429000130300385c1910b280c2e80184028004030f00316900b15001c40420b15030901e0540b81c0303d40d00360b043c9207049a0706d020303c80c9000c0401210200126241035401d200340c1c1d5207012814101c00348043d103500d10304d00c3da000040310b980a108404400004081c4164011640d814045410001a281d60300800c401e140c05500460301c00e00b000b003903001e030b5406458103040450400c04102801407924000a1203402015200d074127440540c0c0011210350b010b44005401d001403483d05411020391854984100b10182c2003400e00080c406200303100320b0100c000010042c61a092805170006101403001e88500280d1000700b066802029584042030fa445115a5000c2004459800c2007422103005038040c81c1805482c00c000001030780c1c04011206119000d00380000c034048014401c9161481c0c1030680f2480c1868200030040f600d0884010301040200ac4821000956a42e0f0a40d1483c00c08404000c103611400d0f075061240c5405140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317612293 1250 317611043 317611057
    0x30703060e06102106090f0e010b0906181312180f060e090405070504090f0507210b070c02060f091e060a1407060920040603020906060715060e0612060906060402 71
    0x500801c40d146c4904000040360329010204c1051981c5001d505052102805a65400b010844100c6054681140803601c489104242c410704455600001420301d008940d107100f09540140d070303045450201c240058105200c820104000c00c10124000a01420040e010001d45505640d2514940c4506d8144001640c000d003049682c0d001d2120701003441e40740e91103400b900c0ca005045200c1c1003281360414905100d61600001e4004604607010510f0204107078401c6001740e0711101407810750f622081c0c1200c1c000c0400070000e620110000d00025148090000307460481c0d800c540c402d09030405a0320340500c29010003030702a04a00d0900c40041031a000c3c804070b0360120b0704511498030f0130107180e403503a0860b40340100480c0c80700118180800d500346040406804118241c42c1084041d007103400103a01740e070340140401c2c8034503400140d1000304a0001480101420741071014003c00e501d030315100b861000c0407150f66020701401da03190410854000388050117020000701078180d03070b1a540c3c03c2c1303c00303988111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317613543 1250 317612293 317612357
    0x1401141e1c02061909031b050108060f040209090c03010f0801090209040b070c050703080301170a0c1401020c19090c020a121b080c100b100e100311030703060e0610 72
    0x30010b141c0401d1915509443d28000e83e80745017406080d480c0810b59500f81c551035000c1d00001940c1403220ba42c0103890039030006421140c2c0d0791610074520004001c1c0c401c0781c295a41102c4210244040045d402020314141c3ea003003610904c949031a200301c1800c9588800000c1d51250407030010501007a65032803501d0300000c0901d41251550040d8986510340384076a4021522464000010003114000d000301051142e01d4801401d070032020350f00e600c00240503e004140c1812180c00860603181e0080080f50402a80508075451010104030000c1d0b06074050f224100c111400c01e0001e6070802e101180488006a010080c1d21781c4180014085075900c5915821000320a464036042d00401c541d40040d04070b410031400205582c0b0b81508070038054a400c000342e9800f80c0000b00d01003d112344c000b4241011044241d031825803790103a4070407800390207056880c13604100000140859281d1541001041e42e600071303000714141d140d40c400e1103201c052000344c04000170031001e0007100c10b1418480d000118402d031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317614793 1250 317613543 317613547
    0x3060a0305031602091501080a0c0201060812040801050603190609080405180601030c08090a260712090b2106030f0601060c02090a0212191401141e1c0206 68
    0x1c0d5a82459a0701103000301d1003140704500c1c948114517060003032603406500d003005811340151041c00a40800800b5100d060301540764444a4a0f02d031003540800018101d8034111030794140900320380000c0e98810700880a440d4207010001c3c0e00d604001980c60030417004c69503c002031a075144c039900c5c010441400221498002040001490355400045080b04c60403541c4400140c204a0009012202d0b2600098144030226042000081010561a29841e0044100d031079601c020131a00c2101045d9604006640d0404a10130080c800c442d2400101455551a9a01e100d81c40d1200440d44c2c2c028035185082c0800c2800c400e105040c5411001c1d0741000010381122541520790140d0b90601400360000e10008080072494004d500d8a80600358200380d0028045161007034040b0208000d8000034040410080b41d4007900181004990150210034181e107221809c65850340607000c2104c14a01a5503c50b440b80000e0408070300081c10100705100c0000e146240383d2408040715000e0401020301664800c1003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317616043 1250 317614793 317614799
    0x12060902030a0219020a050d030b0d0203070e0103120513050111191212020306032d0703050d030606030209131503051606200c0d2a0302011b08070803060a 68
    0x40c005540501d0800e070000d40c80c0c1040052120a0f91079044980c8215842080808003265021a00d41c8110302549030100300c000303a41000c1450350890702d40c004d4042c031440d84000307589456404000d040e80c0c82150f801c3c4e0702401503501103480d40110415001c040241103400c018075801500d0380c2c40844040b0381515440d4120481c80e810101c030300c540c10f860328a40e100c510f10041394094038500880480c44c0003182142801c00104c0d60310040101162420480303a246540c0d400d0100407900585001701040325840c40c3c89151040d190740b020269140030901b0000d0210749180640251142032401a0a05003220003668400c8007800b01c4122890000041c0382c00803003c00d4080c41202e60000b0254030040c409441c00ca40200960040844102040e42030100102541c1d0b001c80c5915030304030110f508140d0001d2030704011041c005501c07122401c810640c85042d00d40558403401c04101d9001740c0b52245000c0c03a00d180844601c280d100d00801403c001c020800014085801458110201902a420642e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317617293 1250 317616043 317616059
    0x8060d061410030201080606130e0a0b030d0314070507051b19080105011e030b07050d0b0a030501050f061009060809070e0c070b06030a0c05010503060414010f05010201200a1206 78
    0xd03a5400740c0751041c0742c0300740155604070294a4200c04180d98103842c2090542c0101d040540e00e009075851044070101050510050fa0480c03000b0303600c0241602d10040c0c00510203001400211100c84140e001f0100148000c1c1c0508181c440c0990090041d09170094041903500240488129196010481301181c01c22051078074140310281259000000343c41d41000469807030f801300b03084030344c02045a410050001481040e00950800c44509095131681010603100018000c2c621070300390054015200001801030541085014404489807071030540c440304103100100240d00c000001084016030b003003001c02e2181860075400002101070311003881e00e442c0c1c03009048500b070303131b203803114503800728214081c01101c00603079400100860040002c01e1480c0d0700d50300d500445101e100d050090110000c3d1458559400500070301c019040040c19968655010000c8503210380a501e00541c6000c1399510400203003908102451003d211650400c0300c400002c5840100c2c50010700c2d411303a101c1500084280c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317618543 1250 317617293 317617331
    0x6081f0b03070210060e15060706061e090e0a02060307180801050c0c0f070806130201051c02030702011524090b0a09051002061e060d05061914040308060d06 69
    0x90382e02e60203084040c008032280800c2d102140c02600d40505503405101410404461044190b80700340c44071601c585260900b07100400d41d99000000a0100d29210600e40843c05000b03000d561100c0800c1110b004000031061340d9254580000750005000c01c013040300d0b58090080b03802d100343c05411916103a40c56a417070728250341041d02c0100e55800c02240222141c0801e0086a01c0d400f1144010a1114540301030aa902c003005011525095a0f061105056910400807552010034803da0100840b4450050701c00030b5008444541c01075207403a0111130061001d4603014110f41070302003102c26817000d031100510b004100601d04008d0000726540021103100d00d1014000c070140750748500341030798030b0001030002e03d1841c3c00300d510131900300d1401c10030240201c0180c54142850401d120081c3d44c1d5500126500b01843d41002d002441703007070b0802001251000954004c541006802c0c4024a030400d40042d10980668004001c14002c40008403181046000951741c180620408510b80c038489112084a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317619793 1250 317618543 317618551
    0x41505060c07031106120103030f0c061a190506070618050d0c1506060215040303020412061d03070f03120924050702070503120f0903060c07060b0a06081f0b03 70
    0x1e60001c00c410014403004071410100f000f0195900c515000c240d915103a050401404010140202c03010ba03560418481c80f403402c01564001400c01460080030300000c0c0c9440e003041001e1043e45c81d5262501d0821004000004961000e07112a00780324a65890b10003402d0504155803d84040c00200c601050f820802508a07400a49074a194001241004024041c04400003148181420b10410507075500040d800c003141640c0900d09010f4486142c11000b80c400e983c41000600c10a01001d4140300e040d51141351140c000c0b80680c840c803484000301c191240150003014007616404e19402d40070a014141e01031404405810008440125607228a44540400c0e01c0182440360303541a0602c42400d03204450304001e890004001591600000030380da0030342c18940c40e0500e400460b20000401200c0c094500499000302a038029180021002c14660890001503580c035080900e800c0c3c40d070401d80341541c1900e95650f5206159603810300f228030202007100c4c8019080d040d11500151802c0c10704099809 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317621043 1250 317619793 317619817
    0x1608071b0602060603010b06030a0b150f040e1006020a020d26090102010b0d0c15052a120702010f0509030a140c030c01140a0305040c0806010305031209150604150506 73
    0x10103410310750002e00e041c40080a1a00a0785482c11003d02ca03590030041d81c1d844a828a40407031000742c05404180b40055a00320f01d4001c3c07401091024194607070a000d44282e402d9021118582d40d11844d2480030032640b480780d40f0150300f200c0c0c81c2101504180b01801c0c0028051140500103400700d203d117400b041344040e40101901c90105000841c1e40c1d0a00070b800039070b101199801164146626002c16110311486010000c0c6401c0e0542c0c44128050410b0f1154502c001445440003044034040100f54a0342c00c070f201b000c0b40609082140b80009140c243e8200a406956601803146c4110781a11a42d00034500300f58544120150140012124180706401e10050400340100300f05940516280804090010b412322a1039446800d000788103e0070f80d0405512480d0204094031a4107043c6004161504076020501600c4008014000000b00400303603203c02c1c3c0d050445030341c4c0c1e400c1c2d46500c610f05a1882c945040d00200070440624003a000a260f4109117454a15019610700004106d83d1118040d152 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317622293 1250 317621043 317621093
    0xb070f060f0209090a0f0e01060e040209060a0614030c070203190308010f0303050706150e0112030f05040e04022407030c110303030103081204050c060a12050705040b160807 76
    0x802203240100d0022000207841941010031041c0080c010180c01044960215541d0303144918003c0300f070300058001c00d6601c0c0208082600c44680c1218030750115001d03402945500085030150030081a1581102c81507554030100080c120170340000c03944081c045405101e0700340071390170160b43d061056120340307400c3c800c000040700100d1801809100c4140d100d46c07450702000d40e041000c0b13038114045404150f40144000340c14140d06070104421081030f0008000c8d0b40d4260004110000d01c0003c50048500903101d01c4455196500d04075001c2c8241d00401400300002c03c0481d0050500032004c3e90445404824000714580fd10a0403803690405802500002c41540085082c85204030406030002010307000b5500e59030441e00d81030050b114056803030308101071034400141489014051008604030003400c841e0703103140e0140700070900403030741070030048003450080030413410360240045404607000360a800e03081034954400c102d00c03582034100c00d4441d51820131140300015201010b0700b01c03003454469011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317623543 1250 317622293 317622323
    0x902240c0606240d020d020c0307050c100e0907090b0f180a060c080304060b040227010f120e03120103080a120204060804020d021c03050c0f150c090a0b07 68
    0x5840c0c01c00c080c000394010800d031010440100381d4011400c0d03451400500442d500d0780343c4003070b80c0000d215003400088058404500d883c5000c10205c000c00748207014808031060080d00408201020034000385060101d00410317250551400d0000351580d1007220386c1001c9200d9a95540310f40300c01d034040300300d547c80880c0c0081e4268205400e440c0c2c56060342025290320308c0450400101400401000c2030141040e4400b00007d020450f1981100c9544203001c4c00942d290b424142120302c904071002c0100c50648480000315060303500c507090364107038402c02d5915070544e42004421600240401c2200503510b0104020b0188405d00c0c80020b18002c1d442480c403256540410700000b000c0d0b032404010b00786207900403c020400c580d03102000b140c21507012601c0389030031100b510000c2c120404551480460500c44400102031540001c06001d07103460000a86403100e198010031625903045035044005a1000f50101e10031170842e80c05880d42c50310203031044140d1521170240300d40641098074200c41d00c401250fa00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317624793 1250 317623543 317623567
    0xf010e0d03330b0703021605030d0801030201110312010b030108060906090c040c090905040c14060703021b01020109080408060a1109010c1104020d090807020a05030f0a0303090224 79
    0x140c0000030039441c040001c842415012030846102508580d01e401049540d04000e02d0540201402021003040c0240e807a107240c50007a44074445a00762103c014440356000546003804074007514485402e5455071901ea0841d401900c01c0301441d40c00201c44c0c4400d2100000c108001c808181c0a8103614071429280d6140030850b034600712009083c0c0c10385401810903c00e440000181da6101c1490450b4082240705080c101101c44441680c0841001410b0505000030700402d0300b0010241d40380f10403248a13000d601c8081c44114420a00c0003401070380010140320b001000c1d900c9480c0c0c2e000c014800800c50502d0398445c00c000b0380181d00318400e603401c82000c0c040d4001e0a4407030340c101030b816400c03501d04000f48600064645140d03810003500421021940721110b550f1981100d192048121082082d034240d0b0500e488650410242280a0000c5040c00700d468500025142e00e900c00f4503006001010265404a010f0710700c5000c120381146400c14107107298001260800d0070000e6120031107841305250340300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317625899 1106 317624793 317624803
    0xc06010e0618240a0b0418090c0303050c07060306060e011805090c07061107211202031e060907082202060706020406081005030303040f050f0f010e 65
    0x10445256604510f404401191450320107070140030800344642d200090042c0000c140b4140004c00036554210700003e500350f000000461018401c0d6103085048540e504214046138011807440342d18141080f010780180254602172011a00d1315102600301c00340d01000c141000400d03aa05904160006a410000c08000c0c0003030070980b0304440c0201c0180c00c050000c980b4103007850443c1c4149550074081d210f02c5500701002d2a0203039400e030001c90907506032082000034000300c412000126101d62007e503100d00d58040b080c1582d1403070903000302d4a1050013004d070740c0f14818503030078000c04a90000056030710007011140c00550302e18a20161850058801000b94400c04c00100302d42000342a4025104440094841111a490711282c202c801c81440c041c11344c15a00510000307000c075a0000305610403501501c00d5a020f1401200750340c0c01c0a190046a031407603034640140008007481001 = true := by decide +kernel

theorem cover : BRFrame.Cov 317446043 317625899 := by
  have h0 := BRFrame.cov_init 317446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317446043 ≤ n) (h2 : n < 317625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
