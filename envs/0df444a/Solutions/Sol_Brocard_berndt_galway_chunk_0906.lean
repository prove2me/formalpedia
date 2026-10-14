-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0906
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:40:52.622356+00:00
-- url     : https://prove2.me/submissions/68c45bdf-ba1f-4430-9c50-6b4b16807739

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162769784 ≤ n < 162949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162771034 1250 162769784 162769787
    0x1401151b02061b07090618150b0c0303011d06100e01091502030c0607030b0a060c0807020d0b0a110406051b0c060f03100b0a0e0402070606031725082502060406 70
    0x44003910b0f8030b60f400301e6049036641e50210090390114400d01108415592001c10254500d8028404c0030304440720310412150b0728898a10305d54082c1c3d640c500d040c2c00120040c040250707206454000c0031034030581c2d045a408c280c030011b01020081400e100601c06d8990004c109170f402611140005c1c800703918907080503403149001a4890b4001107000280e40501d0b03000403811170084c49000b00c81600a090302c8035050620b44182c1e42040136031000c0c0c0b46500c0030300000006030b031521900001c013841810f050200303041c11828a800c1d03c5604070000c0a6890502050040d554000190340241d55001c0c141e54070000c1040d0280c0c10302c00c2d41e14450380c100c1400260300d5400c07a05400254043d40708106190240c694440c0010424040d69488800003034490248a68501c0c203a0003411030540a0500060f003d592a551a0b100210710103a0860203407000c038450141e81840302c00f005054010034401411080c40e80c1d941481c40c82041400c030b00c2544000c4030381e1500e40060348400202c0e540039044542c0c55444180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162772284 1250 162771034 162771067
    0x30b0105040b090a270f140103030804060f060605040312140f07021c050c18070804080c151006120504020a05040507090b0a020303040c0501050a020627011b031401151b0206 76
    0x5c0352501c2d00c4c2054010b0032114083e105507103248940c8014944c099082d03a60031034440d17001401c2500c81584600348001601060702c5941c0080000b0b031030f21941c42e0701e54a803041302c490f804108501032100c0307010984c1103020603008a5180c020404005a56a003291001900312101740c0351481a0529280421042000008000e1050003044900d04210410345220070003443d070448016000599203c04100041d02c070f01f020b88030000c505e000759484141c1540c10a482540110350082c6034046040080010307541244d0107040364030103424180310340d00c0c064020a0348076105121700d0340120740e0303400040c00c018815044070300a0070402500680c1c0d8001c12134000c5d560380080e9003e0f10201e80c1000d00042c590b01400c1280c8a9240c02c3d009002a5541c03c40641081c1e61200c7d10100109000a44440d07903c10a2050071040054903045524017500c1001c010704030341d400341460b02030b000d031200180100c0035100540307150440d0a103030448681d41a528500c0360740e1000000250800320118100c0e1078a210344030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162773534 1250 162772284 162772349
    0xb090109030e03030403320105040b040209090102042108070206040e0109060b0405090621030a0206181f0509011e0f0e16061404050901030819030b0105040b090a 71
    0x15202d82041408908064982c421484000c0413001c0428000d2005840003032130f0801040f449a05030403100035a081035003911412035040b80c003281c0c0d01040004502d0603085040e000034010000318141403e10810300c00d080704d240d002909026030020300b1402c010b50310048900e5541d01900f090346940da20081d1140802081c011011749500b8540003281003400c900a84048800c002c0240401e43c40b458180102080d414807680c400d444410540f02c401d5600b0002031240c48800da005080d18030307001102c41d420702c5058150700181e03000040034000c0e2483c0e003003030101001105000000e0b941c5414a00394010454420400c03500c4050009020b0001d034103030320200e100d002d10107041c445214071200d100d40300c008210b001c4104601d0481c00340000340c8600700c1018400d4122200c103107010749410028815400c260300407074060f40e00042d01c0d488428413403800c0d00d40001070705052203994610300010340180500c0c00b03402c4400342d0104042c5881c0e55042641030042c10006200203150340c000101092090005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162774784 1250 162773534 162773537
    0x5150108010e010b0604090902030c041b11150f10090f0914060106140f07080c012901080f0903070c08010e071e05101808010506010905031f05130b09010903 69
    0x15070b2158260010b002d81c04900d000142050f00c0d260403d4004002003c9039602a07070540700744100105140c48a1041804090100314034031450b6002090003071030880c2c00e59192029401c1803088040c1d004180280c2d0790400244140c241d49a034800783c0c0c084d03c1080551110080b20300300300c02c6a04800503035001500e445c0c011000424007109420392a9581e030030a1080030000fa10034461503403001c0c0080081c2504a0520489610304103940d140c544054029010440c21070751344123405c1c42c030b490803941c4985c5502c0c011080348040d41c02c001c0000c1e282c5440200301868007890b41b00082d01c80c41d024011503461540c0b0100c15500c1e2615200b0304ca00a02d0b034618021442d100e680004141511914a251010040c007242e81e00c0140c1030000307000d125002e11280100b84104034000c1c088201d4542c50030400ba1801200008292600c0000140082c003143d000fa4000e4220314401450701d01d50956a0502480360744c008902c85c0c40f15140c00354860a2007030064102072401c0309200002c0c070190001a642c0c1e009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162776034 1250 162774784 162774791
    0x20c0307060618061d070e03071e08010b03060c0a0302070204090f0605150411071205041a0a030b0d02130b01020c031b040b06040f1215110903060a0e280515010801 72
    0xc880d031072803440010148104c030211110000403901c80c410381689022500c00780030b690092b5552003212500c8860a0320b03400c0520307186141841446000d10402c061010128001c0c8010f040c585144025031081c814103004164001455000395140c0750403450200d070380421104080c0a20f030611800801050320034000400da10b86a40043c1e140c540600250b1403914002e461401c8241e42c1d800341410355041808040c40414403000494014801d14415168100c1e8021540c502030814018211900d07010881d10400740c1a005a0150701d0706a45c010300c2ca485204000781c04031b10b000042c0d280c9000c03580f50640c1841020180010911068403400045509031018400700ca8600200711650041c0d0181901307444040340100031010018140001042c01040300001035644000b102088c0d031003002c40c0780c4016000160004050130200062680030038240410015400400401034442c4a5409060fa0524510780d140700c4c04915610081c44481e440030444941c0d0b50f8505490240b441d007441241d0f000d500c3d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162777284 1250 162776034 162776039
    0x626070503040b010e0603030405130b0604030819080c0f0d0b06030c070209010509010e043302040e07140a050d0e06130c09060303050405120c040c020106051302070c0306020c030706061806 83
    0x5000d8840746c003441009018608050400d000c5c81921403200c0c03038601c419038440007a2045511040000c0001d1400f46c00002c1c0c2c0d8a8100100c40210020724448004100c08441004084008507050394580d600b50304a01d507440700c8031084140500324080d01c06030f00020000a1040542c80d030310040500501c03c1d150b2040503030743c420801c41d050310f003481880c0340341150000080c005000a00442e03001e1103104444400d20030481064a1003000d00640740c2d45c4160b00203018484a424500c1050380601720389004002a4480c1c2450222401100b403104140400483c60071511340c0303503030050282081d80204440940c5818040d50b14601c175445010348560294201c04641d40c03c4900401084c0d81d01529003a1816103400c0520044815aa51250150241702010140796540e40906c00300c0f80070340d6002003821070902c410040e02c0151100401c3c0420b00c104403250014007107080c940103c9030040b0b80140c8505080d501e1500b0351040e180b00411f21441c0a43c003155074020202820710780c042c0303140200502d58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162778534 1250 162777284 162777299
    0x3050c1b0301060602011107060506010c0c0f092702060310030f0506040b13031e090305010e010c0207060f23070209181209011b02040f020417120f040626070503040b01 74
    0x840c13007c03001410200802031180416403580180d6082001031411102a81c5252202007a1100359000440b0900c0313440341c1004404c0c564021071a1000b400500d1041d0403041940c0c40c5005029050000d004020100025480c40c0b00c0c000070301e0007503030045100344d1910601c1c41e10f59103c0b4012203040716185444004110000c00c40e007400104943c1c0754070741024503200c4000385607098115050000400403041e4003c000101c0071700400c0c8000d00600c2c000700702c03890002e40c041d0424050750414010001d4154001c8900d40e400005803c00c400503035044c20406160281070301c5144110300d0041e410071075100501100c0005034404414030000e010503141404d1003640c90300303564030801c0007440c0010303c4051000f6101c061002c0032818184001c200040d001c11100c0800282e82043e4071154001d100010003014101003030000d01000100318030443d240000c90f500c08440b0780a1400b130b2500300440410000310f2413030401440065003400c1102d40340c1c0c903d403096009105034401c440491310b05e0440c4000050342c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162779784 1250 162778534 162778541
    0x9080c010c020718181401090605060105090112020309010204080a0f03091e1401120f140603062a040e04080a11070f1505130b03042001050703030903050c1b030106060201 75
    0x8680c0d626440361a403881c151303074402a080c1148040200d0305a21060000101483c01d0508250140000400d81094a090503422102c0040200781488420070221176560782c401c040801c0002500801a03d03504d4240c1450300a00494001241038420700610905000850301c1640869100703554400c5415120950034070100b01503141000c0f84c058042c0c00303114080466080145100062400e100d141c28504c40c0ca400707071610689040b041030347e2103281d81014000c0100c82c07648000c094000748021309120f608000d050054404a0048450b28a4004d01010000c2c0456001b0001240100a40d043c01e0410f42220740c000301124010400285042011440108400c01141c070210003010311949000705510003c0201c407580020490100042002c24001d9618100030b401210780c0c0319168034151500b083c0c464214900c14001280340d2030312008030780e0700c481241c030002c1d41403902041c01a00d07031805507607074029090084014090300350391400d6200e0b82a00e10440010842c02030120380d40d02c07003043c1d088 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162781034 1250 162779784 162779789
    0x302041a040510050304020d0b160e040908032a0a02060711010c14030c0706090803090f06011a0d020c06091f02070503040b070203121b0106140916030b0409080c010c0207 75
    0x40700c0e07000f292003e0a4041d00c0510f41c07250018101040514060342c911111090440310b10b5050b000c488001c104203580300c0c0b091846444152001c210038191615050628080145801c1170100c2d01c0c188007064001e080411244588506205034503031144881c042d468001c03c85403100000c654140c0408080d0301402094168500d503111084c400105d030840d001030b80d000030b1401d16071140401182001501d070744202100341d030080c1c07400364683c202904a1030411070f6002c00c00080d07034400401800916000c10321100c030f002c0c002020070303529407d0381681d50290050b90440c2001e1b004800400082d01000303d0840c48900081030944e0300501700180c0c4004a0140c0140030b091035005100a200301694400203156903400101266403800350a0300d04036041e80714800d850786881002007a150691400d00900015011107500303554400c52510114079101c100500a1451082c284442c41025020740d001c2d041c6448058003d001040b01401d156091742d01c107184400d01903103400700554400e840490741005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162782284 1250 162781034 162781039
    0xe19050105030403080703022106040b0103090506071d04090302060402010e0306010f06080603120408071a0a0518040e010606090302090a05090a020114130f0905070c02010e060d14070302041a0405 86
    0x21520b503a1000c403910b03c17000300600e0a0550820000c8100d0700c0e100c4c0d005001a43c40350042c10145440c0081c0f000350fa20417120103040c1410f11803070000203200810440d81c883c0c075500c0c144407010310050040c02c43d4456002d6458100d482c052500d000c0c180c1c046003041c801c1c0e000381ca4440108150381e00345507407200e09202c1c1c9400c01200d44c4007800582e04c00c1021542001e0002c0c116403e8650380e9680000703650059121074186e5100c460304120900f4440d1a40503140c0301001e0503401e0290825028282d0301c6200203d150703031103628810400503a6a5440407000ca0248002086400e485420150810445001c160721aa142800180d84108503002e410b10640c040400380c1194189640103542d0b000c0621400c00d0660010301c01030080114040540e001030182c80046044146803016480468002501180410100e03502c03400c0135076040202e18103031481c1a1000756030388840030102802801102d01c201540c0c0070103402c0c880001c0e410b4001d0400e44000000d40d000e0202046040b4481e403180d4803600b80c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162783534 1250 162782284 162782287
    0x403060b120d030b030a05030a170c0405030604080a110a11120601290f030f10050d030c1707020a0306020307110a03090b1804021909060509012c0306070e19050105 72
    0x5141a01c41c0e0044030304c11a000d01212a101003654406046401c8600b40d00000307240709021989a0000706034458129844103c254030300340c10000440d881d0031004001400103080029801e6220344a00301000d811144501550f01c20012850069091800703689414880c2c0342c24030700d103040402c01103600b81c12540e0f0000090301c2e80c440b5800054080d0741c00789440703c040700e0038841c0c548400200c2000f1f500c608400300c2480c0a40c82c001041b03207191a480d412a034000c0740c8282105001a4015200561141c2c0000313264010075183c0c04814058440c140c0025006140c072800001003009680180d4010040c41e155665400080c40c07078260341b030356003e501800290112400300700c00c020351801482a4a51445104020103214011070f082e80e0000700807040c45030045042c8404a039104aa5501400c8c403032504030710b4014004c00080444603107000d03418202e51454005200400781940c1c40c810f0308005001ea03040ba10306010040c04892020444900412a5402c61046900303200030103401d40350140c407002d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162784784 1250 162783534 162783553
    0xf0f0606010e1c020d02090f011d010806070815030f0a0c12030c060221070e0103110c0c011107030506011701060e130f02010c08191403010807050111070504110403060b12 75
    0xb03c07100314015400366008094140d0050158580d41c9003280300e81340e2010603c0e5254500005035068856003000f030700c482c0c84032000601c0b4801c80819900d41108007858009001c0d12201c001005400082015a601d4400c4414402c0454800314180a0081c0240b1800b1031107540c2e5a0744800314100c229005000401510440300041c40700e078090100e86441c034550850007200160058450041642e20314081110300b20b40e03418035a40b41c0544000b2011105d151402d0684101c0c80e40e54690300c001e61036041c00368102400380d00f40c00c204480360045400030211111540c0d40d90122a036040540700c8107485500304940850301090112a841c0283d02950515520a0064031448031800b94040700302c0c100441040d010b0040752613000901048204c6c056141400b0f5070708000503282000c55095004800f00038401040f44910100c0c8410440f40300f0300b45803950202d14000b99003028401e41001d6803181c5002d00510a018040e0042e00949200d00c17070400207070061808000c0f80b44191211042c0c40e07401032080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162786034 1250 162784784 162784819
    0x21e0c011b11100c0203100e0609010902090106050903010e01021206030d050403080f030411090a0c02010b0102010504050727021c0f090b0402060f04033801180c0903050f0f0606010e 80
    0xa4162402a00d048488130005900203410410b00b40d11701c0926984400600106543c244400b0b07030030020040080000410341e40c00f08202c05014070640c02800404283d01c040c0b91001e4000d1130354540503000856403086203c5d400c0058180a0780c026000e803084200d2411198010720845080e00c1d04000e80e81d0030318844810314015903000400c00c4907902c814038240e10710398941c848ca10703002d50a110804285e55610410080c02c484240200c41d046a05010034000444d201142e120f065850501001c010501c0e045010b00340550300ca011003850500c00200b50010000c031211000c0030030030030b04081c051034040324036071010b480f00c0042c003503c401c01ea040403800510b483c0e001051001040c0440ca420140c3e41e85840d0410000e01c1c041d00100300501d1070411986008400ba41211000b513030300103c05d54184203407100c6922421902d0f000403651038202c1c030030243c040c00c1d0b608001e55002084408502c61607040a40303070f01e40d84078009114801d4202041a82d030003083c5aa5560501403d1004e000c001c41d0352 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162787284 1250 162786034 162786049
    0x70e0609093c0d120b010813030c0203060c0408100605030624031f060503030a0c0303020a09050904030c0c0b0307020a0b0a0b06121006021c0e01021e0c011b11 70
    0x1005491456502280ba004a2511503500d22100d112014201020328050068101190409000007080c90180500101d82c2c010b10515013000d01072a02907420500e901e419a900300d21050081d43c1841840100510a2906002001519507800564810106007043c0b0350580f9168003405525402000004040700c1034a0100d0301384600c2c1444414011844a022a0414422a00601c60b9901100032092000490702440c00284020781c000c500c0c24041d02c4000b401c40c600e9990050426030001024215144644502400b810740281408821f0400c1c0c680540901140324080320310082d10040028040c908400341e9200c0e90342c40c1c0151090305102c0e60391030586d41c0000c0c180e0421542d1074804564580300e040180c0f040c403210000f0542c0381c0c1450201c0e0950120b03241d1100c0c045522442c903e108982640d00c00003864a89802c00c590401601e00041c1d080c00d130407192020088034400f20b004c52101d000a00010400406c2c2c940b40c420003010010007020078400d000103407a024000742d644225061044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162788534 1250 162787284 162787333
    0x90604060f181d030717090301020a1106070201060602030406110f0d020d0206010b040501090302150c0d02010f0e070f0b0a020a060213061713020f0409080c070e060909 74
    0x10000658181c454110000070003040d00300d80300501c100c08004802c21124460140041e4401c003000b02d26680103c60700c0d682c0d228101008051042081010702002ca0720010b680e4002002402503464a107140760080c0101615040c0c17520a1050b01c2c0440d00041c0107118210607a401c682c003075031034103007401c02c1900d0b0b136a8003010148440c81507200700031541000740704001c0b0140c4658090b04c14a402520001e113088010b03009903490140c10002004640e80141000044070742c1a02c0003043c05100c600701c20600c3c0951410810306e0300811102c03818155041d031101c0744200041034204904013111922541e2011a40220792070721500150600c1200c11007030240c015184544102d800b04c02d8103980301010b0ba00009000990b245c2801c2c0184a10b54000100f0048402d25445155551a02420300e01400d0b000410103401011050b440c203d07680ca0300e0700142003040c0c100f40120340c0c80100003486076803892240304450850050f8000f10b0320501e0481c1285018120780d0b00102454030b411b64a44d41d140407442c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162789784 1250 162788534 162788539
    0x2090307051207050127050409020d06020a030e1212040b060f100c03030b01030c0c0209070905121b0402030c040e060a0302090703050711120d1e020f1c09110906 71
    0x4030000189036580c295408a08035480c0080c00040786040300240140c0b001c4040c40117124018082041c12501c101c3c018021507004542c0494007201a0001c9182181c00030380c054031240c00012070003000b0307400d604032001030910003003261490481070844054038013031205200c00ba880c03d032002c074011a515050950308450018400445990800c000561540c4001c0744600460001e907039400603d42c05202c0d51010340710a090034009202c0281c8000c0c0008600c2134003e01c1b03501000d006ca482a446510000080c2002510b203080d03450345080650340c1c0300750208100468924140c0160001d0078607000380d03030066000583c000d051500300090344c410513000800590300500421000000340c0d441141403401071070035072000641424005401000d19640d4151480140c0c8101200820040c0d00303022203605d41c052031000201104003410704000c0c0211003220441642c00801c00090a1094100900c8031400100c3c10040210101c03c1e030400b83c82101c14083c02d605020020041c041c00d00504056010000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162791034 1250 162789784 162789793
    0x8072f0f18091014070f020c01050a050a1101020c01020414040605010801030f050309030307030f080f0c0307030b0a03060e03121e010b220f0807090e0303070c020d0f060506041a010e0103020903 85
    0x4402002049444203403038188184481801d010f00a1307040003400d5546d0140744007034611481c0040020301a40300e113001442c1044000287c018091b0310400701c40180300300d614025561040ca501c4228081d401038080c0380e0100306a542944e1603450300344144000c50f10180c41d844a81d81c81c5071589070b00d0034030b0f545080c0d40da0b000800511000e50b40910085c01c6141c400e07252501e40101c0480d0003011a100180890a0000303140184040c002e90503050302c0c1d010070149404662480808081014050241d200605143c00c00401c5050303100088064401031107218080b5071599074807952000300d0540044102d02c00340000c00140880c401d20402000100302810781c4500e15565150042c0240b081c0d64090924066040b10602090304140800750050030041070601c4503603a04402e40f03880c2e00c0003a200c10300b8843c51851503070854070341043c00d02c1d5a9030005041c0c100d44105040590140c60100c94091240e03141c4503841003034000303140e001e241414040c0d444c01d60500c020001900294850521140d05101d07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162792284 1250 162791034 162791053
    0x80c0a0b0a09110f0312031503101b0c0f06050a0930170f04030207050603070305061c150b0a0b0a120b0105040303081308072f0f1809 59
    0x48040003500800e41040300003020b90007420610b50240005003042c1c440c840b0140c14001d555000241400c104880000c0b06560340c681d013051440040c3e0117200b02c0e4041c042c444626400107c5a403114100d01045d44c1d0808525480b80c0080780c14090010f4000c140340d011848100110305a0360150390301003c40040003e865889817518030842d40c41c0807034403581c40362118090500c1c001030701000b00340c50f08608000c00d4040213031145504040d4020800804081200c0c00902414401c01000c2e00602002d404941c1e68101700e00300801800044403218002d81004040349070b11030f04104c20404e45034211b94666460b030640c500110142c0300c94101e01d80e1040d0f0941010540e19030036402015580c9280d01d43c0b98000c20000040401d40e0305550b20717241440402c0c1f1080002c0385d0000030301640411841c0c0249454080c0380b40080307060045078409400398110400009100600b032403041c00e40714034000c400c100c07a030030701e4100603526030200a0700e0b42120203549402c0049150b043c0003a0050b008400b640d11444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162793534 1250 162792284 162792293
    0x6020c1005041209050307060504030f060b180406060816060825050703030b09041e030201020f0a030c180b1e12040308061306030305090108041b030302060a06061b080c0a 75
    0xc2042e00d080c0c40b50302d0b000034680c5440e41c00001c0c0300001c190960141c040b00b854420094268059884050144403050001000b08107840d80308039070541c0010320240b900601c0d00c100111001003120101c4015280400209504000080455041c3c00c0100b030139180d04e080c100c045544940203403010a04181c4407107241103078400b0725498030085c511655001d80340c50300c0e401e00809070384001107118051110324041c0000300e41078220210514044440e015071002861900b2030091245040325500301a012070340c0c0700320960681107a80d0095a03592040700d100c0e600c811000d1100c0442c070030507001403400c001c106545809445030340590882c00400500b004a00140281c464000b02ea007103002035052020000e10340b4050b6416003e5041c035020800480341143c1c1c014000380305000445051210250000e001c00000b0403990001118652010328a06d95915020356070f401c0130740e0030aa8603800e051011800a2084003125400b80340b070021508000401d45a44606503c00b030200740460144200d1030f1f0209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162794784 1250 162793534 162793541
    0x803030f13030c171c02030c09060a120203090c040507030b030606010e1201060801020a030c0203040803030105090a060306020705010b1509030c060304020102010e0d0e040609020a20011e1a0d02090406020c10 91
    0x80c10303504c6043c2d40c0c0c5e2845d103880394100901e100b145005501c10300501180038892420f452a00105071021903540f44005401d49103542e07c2003581803e03500001c10840703040004070308000d42d505c05580501030703174844903010f03020303a06524005030300b66010742c000407110b6124212322070300380c1c0014100c031031002401300f21071b4290b40c03940d0840562603400050f5100c0c0700e50300d0321582c10550309600c09075080c40d00341130003c0e4803407006106841c41026588042440f040056101c1c0d401540d201c07030215915240d03458081e02030160700c0c3c0c001c1e01c2420080315502c00c3d000e05004503a698100200641b6102000c1c41c01c202107504041d10aa04566071075070065143d10781084281c0c0d6031107189d02d604920b103c0300c070100010340d81940c0018401600500134055a1a0400c00e40b0810031035220f021100c18104c940650300400701481901270700c940c03101c485200d21a5a034400501c8004007512481102c031002c0a01c032440380101b8009400080c084000380102d0503070350161581d9002c00040d42c2410b1810000c2c0010f0303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162796034 1250 162794784 162794813
    0x70f021c03030e070609080a03080606040b07140c1507020d050c0603040c0f0501030c0806041d06011d090a050a021c05070b03090d032a090509010608040c0803030f13030c 75
    0x32a03a03400f019500141c04008410051242d45030140c00c81e070a140580e82c84444540d00142484038500202c0d5803036417a4001c0e50060951007903c00c1d143d4096090040c00752000802c9812240500b51036103240e07003003142e44610960185601203240102c942d0030310407224a1600107507094001c0c000118915510f034402580201e0240b04403510700d9080000c0d61203901d81c5503014905044c0b40110074030002c0d80200400c1d40c01501194006410300c0603007010380f0b489428403010b07a8035010311400817034020003c10208500c081c01001904d1a50754588005a4505080744064002c1d07001c031194000511f0310401c0c02c5950914500701d1302d42000c4507981c1034640482c9030000c04641c003000c020040f900c01304000e80b01104a0034036082c484402110914140450303841c0114040c58004909501110300a0a0304002018094203800d41580d4544c0020501201075504490a0048040008a00e2400011340307000e005000c000d0002d0340c6800507050700c6903000703000480074044003912070404518541810f42c407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162797284 1250 162796034 162796037
    0x1e0212030112031205100905070c021809010e01060b0d020f04090510030227041e2001030e06011a280c0632090c09010303020d080a020f070f021c03 65
    0x120b10398a4081c00c0c41041411082849203418100700702000795100c802d0840d1040800024070b41c440000441e1040d80c41400a50000c80c1c19100c06200c41c0d10000852050548500070803080340c400718001d0a0310410321407050340c1102444041031030481c0b43d005140710342645214034a01680c0d08441019184111940325034904092010010741c180f010010034000155a03650056019860301030b000341310040c101a05510013120a12241c03a4000d096035030482d003100a00401343c40c001c03c5070045180d413443c0c83e1300190419000c10818940024264103a80191545a280003841920207504d908201555120841c01100070070b2040008507490100d10150766032001c06428508210060398000005600c3c034141c526003a141540020b1030700301616121480b000c025031140d84501c0d00d0704900301211070b840f00002000008064001a44c40d1a40c0c205442e440340594801d01c25070201d015509480448940400c4100c00241d038110100c040c1d1440140300c5080b50f4030250b034103101c3c04542c80c011030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162798534 1250 162797284 162797309
    0x4080d06081f0614030607140d06080a1407030b0a0507090b0c03180303090604090f02070c0803030906010801060f03020121020d091103010612140a150603031d011e02120301 76
    0x28801030f02940019280800d000d4250001c12000310340d40d010300601e103200700003511340464610501c5604441c6005284502400070603200c0017403541b03603400810101e403008180d01e04010050b502044600480307810483d0340c0d11980d9001c04910140c032004020804012241a02003090721540f4003401003595030800541c1c4460661500115280d013004c0542d12980c0300380800e40041e030780c3c0d008990540f2441603002c60807040715010040030740503d04004141d404030300c0d80815084800000b4611070305c041d07001c5440323603646c0b41701e140d08030390640c01140e288900f0002c1c03e0000d0350180c040c85040d81f1882030210f10402501100a04a801c00641c51000742e48864141052007000c030007a0044950480081203034a19081c0d200082c0620102c005120b6945011b86002c600000d100e00380c143c941109403410705003011f5041a0081c02103000850200348d200c50f462010000303900209078440b8060b199004040ba02d00000400810000081b10440c0301e04070140c400c1c200307030700302441c000d099525006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162799784 1250 162798534 162798583
    0x308040212030d050a051501110c0423040f050d0314060f0303070c08030315040b030a020d0c15030b0a0905040201120509120708040905130b0c09010e03010c0806030f0f030304080d0608 81
    0x400004047c80c03082810001184004443d078480851965039203a812207000a028804002208000c050704240c00350584a0008010078840c2210941040c2c511417003d1745e502c3d84011102345c04680804c045400c803140d01e01c00040750b03030074032442c01031072030400508a90414015640f000740b882404d40106036250404804d02c141c0842d9260442e0500c0400c039820321620700d6180108e0355440d03020f240030b03216000212040d01030040d40395848000d45080350350300034854001980640039280b8000750602a8a48100008100c8002d10645000d03640c165120250b01c2e2040b1501c1024041c05041c00ca140d004081c7c12282281d20301c0700030b081c990b1007130780c000d600e079450228160102c41000b00a25603100c12846828001800b92280c1d80d404144216441e0700c460385880102c641c6030401e006c903a010362a1094800e00580c11004040c8038103070442c1128003042c00c2c0c01c0e0050300c0e0783c90040008080d074414004240081d07082c0740506800c1201d102c0000c0c04a5030b4144d450724044030607185106c04528403107003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162801034 1250 162799784 162799801
    0x3210c12021e0904021308010603030921060c020c1804120801060504120503090604061706030f2805070f0602010e03040b07200a08070f120308040212030d050a05 71
    0x100d91005003a800118201200014410b41000c062102509003000001c0c1120380c0b03035104d030b050398981a0883c690700c0c140c907100d074540d0b0700a0410f40415404100c041c480000c0c2c03480101c401d00681106c224002c040d0340040c2da81c1c10041d11024107014107601174419100b20a8031640c0c0d0b103414400c034201841580c1d04103410080040703014142e402c0b04100f1100d005204d515080411201219448042407605000718103080d4194016000c9170f59025070300041c009082640600e0521801310407042c0854141c03901c0040558030007200700504010740204504243e0720340c481344954a58204c100800b100403c09036946800c10403560082096602c14840c148242a03091040f40e4030680740500640c80c1c18184003034806a4000c0060042c09608001045402200e4040c0d4090802d88044c01241c4d4082d124500c050b1a00410b02449010581c2c1e2000065403480009100e0300e4190141c8031001c16403100e03000d2241111000005401c9403008020448001000340300700e620561008000043d2400c6c000364 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162802284 1250 162801034 162801047
    0xd02030f030a1704030804080a0507050723010c05190501020d0507080f0a050105060304060903020f2b0c0b0a15080f071706040201020d030b03010e0a0602030105040501050a0b120403210c 82
    0x60003002c0741d00c9500308130009410010b140d40150f08100500d88031f40150004030784511030000d000b00903001e59080050343d400000d84191801c03060070b02c2081a10725001c01100c106543d02400383c030940c403200300f10081218501988100034014000503180044040c4000280e03007040c1c0c0c1c0302000861401c10403082e15840342041b50480c0c58800144600c1d4501000100035000c09400504810341d21440c240801d802007002c18128204602514515280c8942c1c1c1500c89030400b000c602808807100030809800d11a0a6410034140d01c00448511925101c020760000c118100e80c011003038514040c04100b04d401002500003015006008000d00703400d144107484d5114401702e0780000f55000b0002e01005070b0300854a03400721665850000380a00d0b10000190140180e41e034644c1b01c5000342e5180600b40810703a00194180d400564082c401a45d0700c5040c861007114034840c002c03034100d0a100320702c8990b0b001c104440c1c00c180a45048103400c2580305081b4011014682d400c0720b20f950b11800002c83c641c0040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162803534 1250 162802284 162802307
    0x1140403031d0601031e0f030c0b0901060501050d0b04150902180409352206020a020d08070309170a020f12030a0e1f0504090f23060d02030f030a 64
    0x1014010b02c0700d076440e00c0c0e0f42c2e55401800010880302c01c1540c85c00101c81030601250b00d41341c1105451851126605019242c500001c00135100c1c24021f90008540203014003172a41200c20680d078440c40d00c0d0a40c1d2914009040121090390b12948605080100c4030004204001070101c50400503a110b03001410740c11f0500304904103038001e50a00030b070701000c112404041000d901613142d9040407858001c820010517840d1800351403d840000c189500400101c500300501a0b02400c1e1103150300d41c031558180d03079924000c100294090100000c82002400300409844034a21908285241c548c03211402c1c160051400171804440c1d000c03a07021005d40ca080c040034285804140c440081c00c0c041d00030416202e03c01c3c145000c00317004861150b20125100d00c221221444401018606441e09144000780241d01c903100c3d41c580c0600308000c42d80002094881c6a00c2070701e2500d070070368000e01c902c00e00d8001000002c2ca101ea11654075049500507840c284002c1d190064550302540e03440c040410060616501b01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162804784 1250 162803534 162803561
    0x90d031401050d0209040f060e010b090117120a090e041109060d111504030803040b0402011112040311030f01060303111603120e0d080c010911040507080106031d0114040303 76
    0x1100108103d403202000020140d40541d201d11480d139942c1044c00080300003c0c03005041501c0c200d40c0f215a480d045d8042c0e2004041103176100c680e80d0769402440d40784041d18060404513001a035544001501c0d4600030b01c881150b506200440c1c83d900d616106040c803040320140d030740d1491103c07089054a40700d20b01552104084844940001554481442011130415158066040d0301240881c0404000941d0011a403180c0e6150b524606071a04182440040c2d034201d011a417842c0d41d4003800300d00440c0c03800600d1803541e500c0b4106455034840c0168803001c1a0b0346030305400b43e44102c000c0c9007c20300400c00a0343c02030321584203015400801a14200383c1d4203681584015411040c0000740310000450246621407030940140d0801c0000101c1c00b64000900a040c40b000045941c05080d06400c00640c050148180658000140d802d0000361081101d0280000f15002c0c01800031501940c000c540d1003002540b04841c032003c1821250858203070f03e404440d0240b454041208041c3d25020700d01098625 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162806034 1250 162804784 162804821
    0x512040906092a0306270501060504030b060d030c141f0605010909020708091207090c0318060515031005010e0108150103061107021519090f05010e0409050303090d03 73
    0x8038407008482400f0f500d020305001c82c10100008521981002c00540342c001c1a6030b196030603030b102900d6081c0b0180c13005546541807000001d6400e000e1030940d002c80343c222191007229500d14080008041003070341e044061100d01c201c00004201071765a034001070512400200320703030704540300030101c8100d0300c140030351285040c450144403907640b1800b107000321540320f880544c03aa9081c0c50403040c540146d510250b00001c140d00b40c6509014006a42c608458500800b005100d0b05200124203483c803034508802240031703500603c1c001500c141d000540c0000c0c0b05405902d5041d090000a0800c10755581c0b42101c1510f490060000c1c200c04d050050042480b04010806c1041070800c02c01c1c032900c1484040d00d00c59031160517a14060008086542843c0c1c000c082e40904201e400514803e5046800e03c501c20801100e40200304500603070242c401c0c0c400d01031204440c0c0d481c1000456141154915007a001516001d0080000d403040000e540100d100380042c142d6440310450080444101c05001c40862030f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162807284 1250 162806034 162806051
    0x30c0a030f060620030405040c170906040b0622051303020f071d091207200f0a05060c030c0d0e03060f0403050307030c0c0506040804091d03090402070f051204090609 73
    0x804c40118400000840c00c4140c00f000003412042c11030045900c400d03005070502d13000401032503000d545846001c641c018200819110206202e566020846004040c5012a40864507914142030b00e04000710800000a0030036032400d0f0010143d8606407200102000d100391104101501404481040318600004000c143c0c80c1c88c8085083d510080c0f21585254500c50105c0c00c0d03a441800f00c81900301401140995451147c54079004034a07207400ea50090b100307441420042ca2a1413090007411100041104041074207001c1040355552107403600305030610041005480b02c1100703201109030240755481301041400648181401e00c1d00c011700b040c111012038410400080d03003081c103480d0031014901d400603000300010402d0b01d00c41c40d1000c002d03001d0b01c1b81c0303010802040050030090050b40c0e28a0740502002030008010b41c0d84035404041c45203580c0081c0f1190482d401e040e4041c00c01e16000d440280308a4160740c4a25003040b4801c4000d182e01d450002e001e100c100114040d0000400b13240703204000c05074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162808534 1250 162807284 162807287
    0xb01030e06150d05030a08010905060402090d060b04021303060912050c060112030c0209040b01081c020a1509080403030507200d15111303061a1302030a020f030c0a030f0606 76
    0x4000902e1915000315008908603961242001d511005034481c0072290355602c0210081d2005000344070f0325104c00d003400001061401d0500a035021140054031410f1044495a900c001034860035007201c1c1c210354203204001880c072000359004000d5014140000303901c08942810a140703004680200e00740a010010080c409000017a85070441c0c000742c139281d20240c0107142c00c640c10f030f1264a0196012100b4010b000070701100c50b40150480325208201c81841940e00e042d003180c46200d500050158128601c41000310b036010120015403c00306000082c1381c8403655400c4800c8d0000d41068001407004100c001c200411045410a40080202003080c84000a00061071601d0f010400415003966045040070141c1c064006110108007100708a88407003000421104562861009440c00f6090544e102030f0091443c201010410018211801c0c2c1229408800d01a41c40a007450129503400c00c111054802280c0140d4050000019029500c108400b00201591032092240071315514240d002c05c680ba = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162809784 1250 162808534 162808543
    0x20f010302031009050618070e120d02070b090a08120a02060c040e011202010315140f0901080c010804080c15010905100524040f2402010507080a020705010b04060603020c010b01030e 80
    0x5130034410001c2102e581d038401280390b03000f0f140611010701c02d0719800d00c10216009149003002001c15106140200c1c1104081503460307866603410030258100e4001071140c1d500c001c00611425101800301c40b0403d0307070788010300e20341008501c25604003000420802c051070b40c140300c02c41d0890740e40340003581040d0901140519480040c85403d070b82035044c8880c03008590103500201c41010100b409420302641c0d40c0400004600b910164a208020030700c040e07540c5141085403641a2882c1174014005400a940107581c0c4140c082c000740c50041042c403068802c103004001000150b103c2c64000c05086d45005410001d031440580301da0005020200148031940301d0680d41344100d83c16990306911000500e03d042c2492240b80c01c29030000f09010400302d10255050100d000070580c00c4014015600522400c07401ca803401c1d40c0c01c500003901e080104a2640068014042c0c641c094800010781c01e00600006044075940d50044001c281c000c1940c0002c06801e2040c0c01c4440028202446184c030040386841c0c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162811034 1250 162809784 162809789
    0x80c07120509010e0409060501052e03050601050c1c1b12050a12060e010303110a12080a140a051009060b070602030a0e06040b060f0f0102100c03021312020f0103020310 74
    0x42200c0401c142c4080e070710481c600c0c0700780b01d40035008100e035501e9802d0010240c1001d008603405402d0051640440d40d5039400404405101d500003400128030400c4202c004e400050002c0b41000030502c400b0f640b880b800c1c4018040005400c081e800090050391002d0900900c5818201c084800640c500740800c0e0519080301680110781703000c0b17a403003000a10603a144031003400301c10b45280c5010710100c1e0018600b80094140e90007a100c240440d4130f02c001d4a544d0700070059000b440200d40e00e40e21320304d40740144a41d0350085601074011400c004d0300c8034003e0342c980c030455030308a800b0380303803400e00040c00c02c0c801c20000038040c0614103001540c185454280d02e4070948100030320f55640040091030705440c6502c02213010785150705035000390a250410810a13001904c510780300c0ca0741c1e00c18070078141c90110b007074299103030041c1c000d050070b10403122902c4000c004c0e41070340005140d020000e080ea606041c1800c072000d08040301104480c1e1002d40140100110303001c00e00b9040c1072041080c4140c007450794488008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162812284 1250 162811034 162811037
    0x60b0c0c1c05210f210606070515040614160e01021b280303090617010510031814070303081806041211030a0503040209060901051e0f030709020307080c0712 69
    0x443c1da0341c946000392248550f02c0702055800308070b0891910300d0083e040003c1000011011082e10f0f03140410440b44106400203040d41d004400b82440c0031201c461041e40603000303000c00104c0d000d0380c9441d041071031b50842d00e21540102040e4440c0485410813404001074001388002c04045100101d90180c41b000d18042c01c3c0305045903811801e00c0c2218001d41d880e1017060200d84801181c0d28a800f40c102186401500d01080c10122141100503c0442650403540700030003c0030b071004101d0041d4000c0030b004000c003407042800d60301d0b800456450022008026816001400342a146060062903000c0180000c03815000e180000708103440300007151600071740c1040800e0b00502003d0403d6425400b41884c000d007901020500019041e040b802030740c0314600a880b448055940ca004011505c0401d01805038011030701700950400c0c80000c08100c0304032a01400500421243d400001d25280303a5a03c4400300d00d40000812042c6070b07220110741c0e00007054205180c140406c80d5900501b04290300f00000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162813534 1250 162812284 162812323
    0x117060603221401140a09110d031209031e0503060906100207030507090c110102030603060f0a0204090f0207030e120319090b1314031b060706060b0c0c1c05 69
    0x2421500070300a1560000e0340012050749a0348600f4403280a81180e6903030030041403003a00066010152802180004d941c1b004881907510b034100108070601c25018015810012103842d06003010075503110310308816010703444040c9400c121207081c00c00319081410b0134081200a00501c0a181c584244142d0006012181c004043d03005a404a103811095400981035118a040c00911001d040c0d0090040c01c81035611114000b5405081703500342e100c01d40782e0a0300356200741c00003421140d4002100d500f122103070101516040d610601001030b20004a800d10000b940058172804054101945108444d0f06941201488030345410f05070306e030f011b0103000b041c1a0015624042c5000d10402c62800600450103843e51501042c61500c03841c07010038015104030a1507003194420307901d40004c180140310f440b00c030f034405000c03c80d4080c00445c2d04040400c03070b03042d030301c80c01c01203409807120003d440100541030003482c1412104040000503c111260b80c10010a08500c000100b400840c12207104160b512100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162814784 1250 162813534 162813571
    0x30305190207051011130311090f07020c0f24030a050a0c0807211409060106020f0a020f120a0b0a0c030902011403090a0b0a020c070f0f05280906050117060603 70
    0xe0f151803041024401c0b00c801d01d444040100268024025160748003600d5429292b540c030f50b004041c4060a840160142e8089641c007885850694000c4004120141072801c50000b601900c44007054034040a8400d140c0c0401044070502452244591001513560240405c2681010103413000b18064120020445054140564050b4900340031080c5000c0701c0f0300304550340c41000c88003211503080e16a039191b40661800050640e01c005840c0f4010100c0314050715a4080503400c00c840c186500c24141c0d08602d0484650300c1e000c205200f6841c0c69800f45410310554945441c03100101c88600035404249803038500c00343d001d41d80c07100c0340e6840c40992a940907540c0c0c40e03031242c081c50042110b0740200400401000c011008036190003600e1690f40002c111403c0d00d465401c0740703445811601500c014120203900c10045441c110343d5240d6040c081d84111400e002300b4100c007142d030b550280c00c59500203403241c8c4200301550b03100d9400200c4080c6d03411500c8460404a00092007440b020780000f000850b2264032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162816034 1250 162814784 162814811
    0xc010c081b03120a0515150a02150117070602030301080303010e18010509030c010b09010509130c080a050d0e041e020c01111b0f0a030f05030709050303070303051902070510 76
    0x507020403090720412280c4462102e100031a40010072110320310342e281000040f45034a48084e208400c4800010600d54032201402000c1c00b140d0000390105003140314409400140034102114240031b044040d40e106007001e03d02d5a0f40707190002940c441c104550040004110f1420040705a07419149030101640d0301e034540a0070b00343c82007807002c5090125440d000900a800c84000000d204901c076440c02448400c5400c420820240c00034460381d50828500000204a0310045441001c0301d44940d01076140580c482c01024074100c05800c0440f941e51010842000494200c415450441012101800b10b41a200406502e00041004000c0c1494000c2500394039880d0070340100c21205201c1c3e81603034032510141000c0c0c65074804000301202c44d002c0c0c1c0700700000401e400b04440303d02d207402d0b890301440c004038108201c8060380000d0500c420002640c40100b51950301f8402000800c3c0240d402007003e00305074000c010045039034501c0110144c810003000001420126080001464400c800111b0b042a002c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162817284 1250 162816034 162816067
    0xa030c290a080f0a0c0c0f031704030806030106090204150c02040e010212010f0e0c0304030c06060b04031208010b130b0f1e070c050105031e07021501180b030c010c08 73
    0x301400c61800c0414406405584603055a200303060240307040c400c985a2203840400c903540000b00e0000220044075440104644c0031070306030383e18405c0c80d00e809940302ca5440d95011f50402e40d000c400095003c404d0180c645024015070005e0541c000003145024a02004c001000803946040c405109101c13051005540d565480b500c00011000c00039540d80c09070321080070015109000e21101c20501e40340100d03032210380810403403280340c0181100345141c680307840c00d4403041c2c5d8200040300c5082d150040801d03c82145001b41005610900d5286046680402c024050041c16080242d9415040c420701d4652401c0040d05011600e582024540d40c62803800c290001c0e01c6079814851000c0b0800d400d6412a00201006010550080d034420301003030740340c034011186440260380d9185501c1008009000a84442a4164200c035450040f40c20124800c0342d0448005403d0b0300019402c8049a81c2c8003000038540a4000d504000b200500750101081d00040c095503200075024201850200707507d020742d0840c14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162818534 1250 162817284 162817349
    0x30b040b010e12011b03020c0f0c030703080d0e0d08041e050c040c020c190501020601080a02010e060c010f0905031e03010e0a050c0705010e1b0105191b060509070807050a030c 77
    0x1700049100340b51040040c010b9486904084698881c008008980e284040750f4425400c400070042c10510746107444110083d0001034a41580c1680c0e8000171009450802c11040010015100c0001c5031a09042800b07402c000318800c04820745003035090100240307000c9812104d40c0412580080c0480e0900c80407440c04600c0540d00340c11040001600c1d0300302d003030300c070600084031400d030700b01e801d1603807205402a198040c50030002e000c11501e9400d01001c0c81c00801500d0a00600301c000a249099180304106035082d1000565840d0000602c866108408443d4410b102c42d0035500a450343d45001c854400342e07040140708040c115540e0b00880c801d0804101200d80311500a40284641040c01410b030780c540300801e495041c815461800c203859540142c05640407840000c1400400310200300301900c02c0031064409028007814182000300007030040c8516801421540001c004090505020a190060542010b8484c0140140400001c1e8039980c8400a550354000345096452560007400300504504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162819784 1250 162818534 162818561
    0xc1f06050d080306150a080c071103060f0609010609081c02070314030307090905072c0d05011e02031003031d0604060509090106030b0607030318080403030f030b040b010e1201 77
    0x300558030038803803400043c5002d03a50413150300031121040f030b031642418856020b0f1640407400c254000f072000710314035000c0d14106004108544060140c1c1c1d0000382050070845000c44d0388294481400098103100c80c14030302600381810310042c00b50424072101d40d1040030020755800c00000380c00f80c1f49001e1082c400880250340c041a001500300c0001e08041d1242c2044030810000307281d20f0000284c4004034060a4000c0c001902d9020542c0080a41240000c07084503641d5840d03207503c0b881e0045925000000180c06020320300014074140d0003084034003103608021600190034018018080140d81c2c020340b0348212503241c1007403021080b07100c52000f18600d007045c001c1d522034000700c2d0018074607030000300800d28202c003100c2d90101685c0f00c0301c003a0100e451980000740c2000c41031103007800180c000c1d400b040c01d00300c01d501c4207407007034241c1da40341190f0341d015800032400104102030032051075800d0701504421160032103041c0180f001c40c6000030180c5181c22103442c40b8908964904060a50a40c00010340c80c448 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 162821034 1250 162819784 162819799
    0x2040b0705060f1015120e07090b191409070e040903080402040c0c0c1701060513060806010603051302100e0901141003060305030f07021302030703060303030608030c1f0605 76
    0x3a030922a840760001c4a0300d48001034000006150b010a001d2070700291410b0344050361161300013410498400304c001110080c004e82d03512800702e60b04820002d400040c064808046a603ca6074001d1054a00401d585206000c03500710043c0700310211002d01501c0c804064880982940d248807040350207180d1b282c481a0030503d88100c45090540c81901c1030300c903d00079581400714900a44085584036a841c5000c1c055800f00d010030720052500c4115148441d62603400400c2c41a1140d0024000610300640d820300980d5556040001c0742050040500500547c1001c00403403404294000040f80d02c220000c2c41307010180702c901c1085005e01c259040460018101d2401980c55404680f46c200903648030610910b00c00b0030300030050f440390095009803540407001e135040800313103408204944c0004800300c2e80190b0203800301560080510185103da410fa0341c002c56614074506004d030480d102d0b9081442c15400810000003000380008560031418100702410446032001504200200340c40e800407a0701c45032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 162822284 1250 162821034 162821047
    0x40e0103060b10020d0806060c010e030d0509013e52060504050316110f1c150f0c050405130501030f03080402030a0c0801021b0607090306090602040b 66
    0xa030740e4001d4004a505981c01c049040300c803d0140c0c0e480c0c515030540c10000b07100700005061030508001800003402080008034415425400c001c1c219040701d513002002c10703a607404004981400740503000024441c1d0742c1c8031103400c074103034401c003c5508806588a5a1000c8a84607080c050081c000c9601c4101050f0805540381ca191640c6c0e0b0040c251400280f85140782280c8040401d00008a100d0844a52920310b0507202d2490707940c0d2000d42001081594507000c144446041803411410358003405100d40c003507808092003802080b015003006800207004005100ba4280c491085074200c09000350014403010701c03000240302d130310060981001d0101c0454209040c050305540c100001d070013521030481344030002449184a01d000c0350000d11018082226040f04c3d05c0100c1c2c0030710701254005002505490291402c0e8440003107042860b0300c45600c5a60004880c0c109200d030399018410780700070202800050500c6174005000309103500000e440290703140354440c00c112a55044400504654003884d4407a032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 162823534 1250 162822284 162822293
    0x5040311011a1804050106080d09150f05030411130e0723091b2107020c01090303021b0d02090702010902090903040302090c0a2309040e030316050906040e0103 70
    0x840030140c1892940c00c0030395040440540b214812104500541181009000e401c8851400e00d00030f80700f51150b55a4240c0456810800e20140c251008640c031081d14552070710001d0448000000a403d04200c110342c5d00c0100c1c45d43c4074013140e801a030031030303030084081c02c003040024041110a240d074094a403074041c0712031002c880407a400c0e0440d46030b00700e0708040c200760508140c0c844a2070b080c4540c2c49a91071000801502c401c0b6005110480e0150102d401d2000400095201d260801d9101c1e544510700d10402602e00e42c10446001035040a20702aa44a440c65030041c0d9554004c000750070155590f41204062a1a01080404144e4000701701d441ca07400c00580180c028201620140c0c000c207004400a8440b080000c01c84003220750180210070035682d004200985074202c3c08080302040802501703441ca50040310074100d052074480b0b080540e251019030030481100c0e2201d1803045644c205000300410701e0540f0000d12030990460518650b00c0c02008002038071842070b40c10800e111121071002000740b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 162824784 1250 162823534 162823547
    0x12090c0a15020c03071404051e0f01030606060f0e0111030c010501031a07020a1a0604090203060702070810180809060c120d06060c020d140c040908030603070e0907120c09050403 78
    0x1440e6502983c911140903000d250b2542628003450f12130b0a84901d0740621400d00ea401243c0c062060019407a0312140c21002d078650706800c0d28180d42c0c03181008018000c1c07040b5840b80e00c2c0205854240460100180540a40101c80c164004da0603ca000350034a1600b00c0184222440c4a044000802075984c40f841c0482e482c0008046c0c0205010300f41e40090710303642c00041c0c209001500526915100c40c906d182d0210400d60003400039402c9a00c404240380161002c1080c603000c2e20464019003103242c00d10084602d841815028118500c3c1085000303108484504420492075800c0300301e60366640407010200d4200e01c6210003814030381c49a02c4d8400c0c107110a110207400c01d160001003d01c08140d8481c4200d0700b10fa00b58501070b50002401d41003200240441c000a001207501d8400e0350841c04055000a040b22004034082e5450400001000200c0c079003808201e014000500d003000e1a03061440140340d075540349000b00030000b001400741806000000745001c0040040d0785003031055203410315000340701 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 162826034 1250 162824784 162824819
    0xe1b040915080609120d0c020a020a080604051b1804060b0a0f0305070605180d061416090503070e040212030c012d060605030601050a03060b0f04030c080f0312090c0a 73
    0x90241c0c0c03000c03507141c44010a11041143e034490385c6508045542207100c0003401489404015841840c1c05800141c46260b480c0740100403040103480949490304107c0d050180701105840b1802202c4000d41c61a560044042e810801036191034145603114a40301c00141a0a00e0f51640310042050005418500c580104192071041d000d0385c0002d0354a03007045e50b02d401140b03034501c00d031000302c0500d0b11b85041c6843e1100100b130007110081508802c0c100d01000d282c0d4180e030300300c1281140e6100c105c01180c000700001d00810080e4000c0858a141c43c0300d24400c041c02130f1000303100d512080c030203500e4240e082066440c11140e820003040302c00d40400035806041e0044190340c11403418000ca41c2802c642c1803013250304483c240d40304c00380b4590300c4000455565104101c20402c1c96030712440031842c28107040240c40300780c1c641180c640c2c2d100c0c02c6042041c040f554907401105c86522011b00c02c0059034008c41030b1015407600c03205203045600c032020282d00b040a500c1000707821644500d000501100e2174030b0080c00c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 162827284 1250 162826034 162826049
    0x50606030d0201090807021c021905011b05070506030c070506070e1320130b03010b04030309051e01030f0209040c020a110d02010c020904060209060c0304050306100e1b040915 77
    0x100a0004042e8280c0e0588030002c2c003e84400d000389005800e11499400f400750030400a520700c000c0c01d60028108940308401e10740c04000501040c0705039600861080408000000c2c4851440c0f4a59075030f650390070290180c0380c09082d011001c42d550240c82000c1d110945d074013000f901c0315842d06103402845410311000c21849038600e001d6100010300c1e18411044050b044a15030380440b0304010542540b40d1250080d113140001042000070311841c400027540c007920b44000034994891131414010f2100d1b01540290f403040c0640ca4983c03511206000d42c4020a0b203081c2400300c1c1448292100d080203000c1c00130015081810404e0030041168040340b125804c034400c00c001c1c5210100f020a0000b44011510002e02180d1428940800752030b0012240e40e109200b280098948140314010688582220100410a5101050500030741c50180f00050748908609842d0521a01c3c1409041110102500d082c00c990b50105070080749480800441d005460b64000c00c1c0b000b10b8000200748111181880780d000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 162828534 1250 162827284 162827293
    0x20a0e040510050906070c050c030f15060303041d0a060b03070e120118030e0d170c1c140c15010b0706060b16080a031803050307021608031602011202040305060603 72
    0x10420800b51140c507000d50f1803d4024801c40e611140107844584803e407081d507091092200b050305030b50307003001081c039009071900103820a0040d80c046448182d05c0030784100c0c0702c0d8000b404141b00310700c0d002d075a0281409005070191100d45401400301e000b41000c0e008a104401d0000820520a400620b104200749007640d03aa00b40400548065088906640d11004a222168004400701340b007602c1c0c0310481070000305001945001a910994500a0b5145441000c000443e580c040102c09024060a011071005858003074030070544000c00440e4845c08640303816a001c81c0301c0311210b60803c02c3c02010401b1907420380040d40c582c40aa1031640100c40e0480d0064144500410300c04403480c01d032440d030510300d00310500050b40399980a51580280b07058208050b0368254046003403c0b4480f10b410140d0281c1c803503d50341d0510100082c01c010301070300d00b18012610b4800c20040c000001044461540418144415031180ca100498444100c0552108114001724000c801d1200c0810400d001c1e00085046030b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 162829784 1250 162828534 162828553
    0x3050c010c0503090d03110d0911030307050a1b08070e0c120a1e091220010906020d060e0601020706120b19050a0503070f030f170a030506010305060a032a03020a0e0405 74
    0x11825504407000d5070a0210042c004880440c0d041d03000685428402c2b004850440c0301c65020902c0d58201c0e10b425141507100603040e07400d01c0280c03c2101003032200b240c115002607050ac0d010a03652142c910643c1e1300f0034001400540080c001388241d0381c40320000c160084003400c0007000b12002c2d0200245d400a08c81303a040b03d40510101901c2551842070384002001d50b05017400005641c455900c085181110f5106d951055000200b0b2140104a6119460068403442008200d01c1121056000030690f01c54035030620030300d070b84c000500e01e00301c588519106c4128100400000d015046040e103840d00f01c0c10750004040d40c80c1c200c85a40042e12002d0780c00c0d0122503600d81c1010b80d110240c0c4140c0d600f2120303001e02072020500201c9450304a90040400d440031400b0704554912940c0034450b004000303070f0340d04103003c5290ba00d030080035008201280c64030074450464840c41c45e03030700b011503901c412801e4004000c8103000b10141504025500113007400c0354a0b940d0345000d4036140701124212014003600c083c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 162831034 1250 162829784 162829787
    0xd05010e06100602190303110a0f030506060f2205040e07081203070909090c0e011206050106050a0e0405100b041203110106030c170c0a150e0d02010807080403050c010c0503090d 78
    0x10b0000c440540e0300030805208500c0c071610035418120720a80806450303080e242c0c00c401d4180000d01c0d6408499440d01d0080307803101c00c01802c4507000b03411584038107020007884007110030b01c1060302d600d01c010b030702c200c0f604009800e1000941401540071030707001410300c00520032030130000c6060400c039452078040c1d40041411300d09050051000310354000c08241e8040003800503447c42d500a1032818030030081440c200e51100420501140309a0140c6884403a03400c00f0320400c0f09a01880b401044d05d41482824408640d401401d00011503a0344c40c000c41d81c0f0b0340000d240c00d03186e00400c0020200800c8a60303560742c85240d090032020304940141c01080e074042208401c00414440d15049a40203180a04a50306140c20b2102c080106051841c1c41e11414660600594903035444174001c0c800007002c00d0b02d04990041c00f8282c102c1003190540308140401000f400350340c0000710309a00c00f2051911001c4c41c0d54504d0192000c1c01103d0302c3c40c0056113002d0550008542000c011030040402d40122001c0d0140700c1e90 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 162832284 1250 162831034 162831061
    0xf03061103070c080a030213090504120201050405060106050903100608011425121e021b03040f0504050711251e060e0402070816020a060822020402090d05010e06 71
    0xc0540018281601c2c1c00f010401400c003a1030641c000e13103805454455007003100681a40e40750040512242e55000b131108001c2442c8094000341c0b40343c0001d200519003529040e885981c1441400207000c000112041300359014040001024546001040a01d44500d5024002c01d60150503585181d04480400c1100d680110b192100120030084d20401c03050b080c0084501e1090071b020004101d88941d168420820b40b80e0488800b05d01d2120700580320300410300045007440c0b61a10001c2d079a013040105000010100141c10182d0b2000d5034081150b490700c0300122000d840b59902c0c115140500d02625407912111008507000301507800e0030030301c00350300c0e00303a4041c2191030b050303003a40d165000f650704001082c080e052003600d102000b0030050a00840f900e03144a00e50040e0001ea000b400c0b000201c1086143c4004144003510b100d00e071007080c91903e0a903a05140036981c00f81c5008034283d04a850856403281c0403600018005440000c680c2c54070f1602ca8064124275020850718021840001c4940c141e81c2d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 162833534 1250 162832284 162832291
    0x1b010221010b04060e0418050d0305181009020111070603020d0605180a0504051915050a020705070603152103080a050903070f050309090708070e0a0f06080a090b010f03061103 77
    0x2c1949207007030718103442900c28075464003080d40c0058840c02401c0030543e021200062183c0250090039401e40300c80802001c599004184024415280d00b5021040d50001141c4141a00c42d4800040b29440e600040ea00c125040600003031922820314007181c819490b8014240e032030071907401400210303164000c100c1e4100c100003214001d040110000340d07134002e494102e2500036000740c06507003415107a05109030050010070070a94160151215040400a680c403071180e000b180103004604102c0706554840d1240c03040d00c5107204258841e011040903006070f0502d800103215400c2e13440501c001c000380b4060100031200060300400c5c201c0340015041031440c06440d00c1081940060752400981340d4841001d42c2c02040142c441c4d110503c00c03011182c0710301c405123003d030815031541e92807803500b030200600761408a0741c0c25014029081c0208000d43e0b40041c203400b5101e090622075155a205035a10f8000e024851016001c2c020b40d00c00080e2000d68044443c5c20b4034003130541400b5012421500c600c243c40184c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 162834784 1250 162833534 162833549
    0x3010b191e0503100e1602150f01060c0309050a030f02040b010309020916050c010504030305090d0f050415180e09010609060b030a0b030313030605100e101a1b01022101 74
    0x1c071500c2001441240203503070008004480c0c0c414203403503240e07841141800722680b29025558150850004d90100a144948100001d1503040e9103403030451150213880611400d014440201d43c603c041500a262413005820050645407010741d03242440300c100e00c0c1c0240264007642c82c2c6514a80154481d00500e194183c002d803400c080c0361544003850500314000c004110410509009400b0486000c1c0184d601990081d907011505c1e04114030310740d00300340c00108000c0c2407082d401080d204c0541c100050f1811030f020000820110140b2040a547c903545a54102c00003100080c404980c034018484180e020b078000100030006203403209016000c550b00c034010020745c07030028000503600da00580c011420300c10004c0c090b241003142400010080c2d0321250802c850194568042182c0008040d424000404c080301c106000c070f0414480c00002c4c000c00b40074a9042d0200c50784150642402d09040303c64008040303130030201c9543c400c00824000e4000d51211206000492108109140e6607a299130598068 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 162836034 1250 162834784 162834827
    0x20703020111030d0603060510051804020607030e0d030f270909030c0f08120f0606030403030b03030f0f0d0c0203070c0e0a06170609100c09030213060b03010b19 71
    0x85400648048890468038202440200008402c030748460080c4002180b03d02d0002c01d650030a030401c0817401300d85422003801060007401d401c0c00c0000c6500c8858200c1c0e01615503540d101824141120315510f0003202640040321480d903401010350080d0040c1010034166079400300c0410f50701c0c0d001800c0f04524020b40510b400300b2400d10044206500030805a40f107070420b0701c10300106644103001c0c2500104180c90564010a445031b5105c1c9500120381d1040ca00d4803aa401880c0410000340305000c080c001404165440d4180c2507103440400131590500300452072503171600f0100024000c6030b40400b0402c1480b501b0001500c6500d400081a6001280e0050a110801c1c0c1807d20420346500028481505180c5949000032424052104400051021005400545000c07405146454440d000916070320380f03040c103803024a039800640b510a5a038110780003000c4441240172140541000c2d0000886083e0000000078581d0007103000b840800040d06070100f030900855010340e2118200b140d00c0912030b00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 162837284 1250 162836034 162836039
    0x10f0501120209041506030b01020109030c12090305030c0c0103110304081b070302060a0507020f1539010501050321091309050106090609060801020408070501200d09050108090d0207 80
    0x600d01c607148808865200500701401c210009041d24000c2c030380c00b0100c19540d00c040c00390350380c1801019860a0203000a0000700318980d0001e01c40d090102026041540891641d414144651072a100450b0488100c81d21203d41e12029901c0d10350303446185000c030b49404d080d402c14548070b000b5203125a030002c00b0207090550f1141988907a00141851026501503010084010303a0f5090240c10450275556403da00c545061060080d1510700550583c8a086154041109003801000321000040880d071428100c1280082480d60990100100000c08403040d2101c44e41c44e00551059040b07490031022103c140280200c850701401e0039410014004000b0001c0e0382080c1010a0361800f80c2c10811400141144141c80f000e00b169026040140c17916100c2d4800c100c86c900d103008050107400c040e0b000318a001d01d000f00f04da5403400640b01c0d05044c400401c883da40008031028440c151803000e602501d40494010f60b0003402c00c00c2d10b0240c1d60200300c6820100d01110000554030070700c904e02c1c1d00181201030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 162838534 1250 162837284 162837287
    0xf0801060e13021504080601030618050c100302070c080d0201060b070c0509060a18050a060605040e0f040f0c060804020312090108060118170703020a05011b0611040b03040809040c0305010f0501 85
    0x1a00300c2002e0303030000851340450300c0e640340440041c802000060050415541946014000d43d1038030401413060320600e03103411007ca1808a03440010720011520300400d0300340c041055019018819000d0403081d4030150005501201240c0001b54844560007000311503224520703a4030f60b0241c0d10000d03111240e07500d014001070a1600211b604044020305041100355101d000303048426100708282c01558130388040c07001103503140c02108040c01c49402c000e0308050800c60b05080280004003800c8240d100100402e00380100d41c15404070345038100030751110f8540c41e0f50700907042c030720140d60481c024400d441070b0071102030780c18080d141c40c144169a403d8a40d20b071400110b0320b00c400d81045c4010b01460602c0011014480010302078549103400140035500e181d401000600405940040d052280c8a0380030141c8491040790418019440500007461030b10050003c4807a0141d81c00c0392080d000d00105000c14011814045c240c03001e41202e0600c400da10000c021400c5d81e50a00c0341804a4500361821702456 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 162839784 1250 162838534 162838561
    0xa050d05060303091c02120c46060e09130f02013f0207030203160503070f03050405040e15060d050c0901030c0e181c02031c05010f0801060e 62
    0x248001c2c201ca0400000000080820001c9600c03181c00251850403642141000305604416201d0003002c0d2401e400c000c1e010910103d40b01c203118640c280d18154403006132130003110400d0034440002d05402c800d6030304169240407209070300945000c82c0345443c01c15042d14156400c02e1052801010098001e030701580c6810300f24020020883c107200d050814041c004240c0210200c0e0f21604101c0c81d000004028840342c413141807404140126401044503030003003600041140c4c0b8444003a00503031380e4640641403850840c00342110040c45840301051b16030926074894040c005a400031942000f50012100c40d0310756400c0120100102d051107c0d0003d0001d10700b81c1e8000d02518020340c25904550154800100c0800c0240c00c115504114000e0030b00c030002042c1850f40e4400d00318480a00f9250880c00c00c0c81c1ea0700c02d040019140d44a039000c418100310310034001e6496249009107950309800c0700f20840f9001d0314007400f0742a001c1c01041d00c000f404110501820044405040b403103211030f1904a44c07040d41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 162841034 1250 162839784 162839791
    0x30311030a021c03090222060602010203040c050d03090f180b030f060403140409020f0d32070306090c0903120212041406070206070303050906070c050309091009060315050c0a050d05 80
    0x107140d910351780380015842d02000160848542c1100030a8000c207550f600003101d18540107101103a205008220000d01c0740e040e00303800d944045400e10806d048601d4203c42811003600000d140e07640c03070040080c0c24144d803544000c501284001c00e1140f00001d106141d6512180d6100c41044c1d80f201001c580407070300505058803c030031565040307494662039050840a90b440a03111084401001516400e011080d01c00d10000a900110f250051003242410b4070104403c00031103d0310030264008124040d00030340c4601d00404426106101412000c0005020b81c0e00c10321050380c1c10480f103082440c2d0544040b800d0300c1c03078001c02c0c0201d03401c00d4100761800b22441078204280e5000303034003045a04056a00c3d031015008181c800c1d60089018134000000c0d40c1042c030060142005d01c908811401e000402c080160b0383c00480a440d541000e40c0d8680e001c00030203945901c003201091801201006116408010003c0c010120400340000c0d00c0d071078480c61451040a0443c0c00203401400207050502550308810341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 162842284 1250 162841034 162841037
    0x80d0507020612062b050714060a0f02011e053c04140a0803100e04080f03090a02090c0a0216270f18060e010506010203030610020a08070309030311030a021c 69
    0x741d400020b0f8500002c081402800700c2d428170404030102000000c01a0001070103d1030488965000c3c0e982c0800c9181c003540350b0b08000d00042d1001743c2030f500d200758000b110703140c465008500c5000180389100002e2000781c9200d4556200581c8500c02e500c0400807580700040320014802c0c0d80f075080000e070000c08030054001c4500c46424010044c0d410800c04c07041c4460b40c0030307201d296078030b04007020a20b0442c0301c00d03400120010070752010400441c04040c2a6540c081c14018590394a6440741001800c25401c1e01c0020743c0691048140041d001c1d0035405082c03194215000c071080100c80348801c1601c154680724200c1a00b01c4590009000c010303004d101d0102c1d0400c14004168a0310507440c01c3c050352901108001d05626007085034040c0291030241c1038041d172154000700691300f08240000e45902c0001c102078000e1003015621000c0328030170481d0464071600602d0003511001941b9004100c03921a200541c0055082d002522046002100710f9180380415001008104030025003080b40e0042c1c4140c110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 162843534 1250 162842284 162842299
    0x31305070317040503070f0311091801050c030a0c020c0f1c0602040605030a06050f010c0618051e060106021212070504090903320403080d021b0304080d050702061206 73
    0x38a60241a007000400302e128036848904280526150040941c0f01966000200400704049406145000800c0c6016154050140d5030f1101d201001c4203000070356001580703040100f00301c40d00c0000c003131030248524940501c070b00f4001650032a07881860607489540485020410f8049180ca00e41108083c5038048401800340d2042c2c0385c0000701d8005610020104100004012090245224110182204640300c08914424a0008110441840c0c0040c4140d98440440000c1016134481e00d03101c550260403900c82c02038001c00c1040d050403c5100034050b104031000401c2c103d0001c01d840b0611000040001c0c1445140f00344503c0029014110009002c000c00011a104c0740750b01403811014001d850b000c03c00c0da0034a141e0001d06440b088600724550010300003001c00c881500c200c404072070f04a500719456040c2c040084000340b08410700c5070000001c18800c00d2134641c0100c0508200e881d2801903030380c403d070743c25002d98180c0302e000c2c030080d80514200b04541c12000300f543c80340d400482c0a416403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 162844784 1250 162843534 162843539
    0xa0e060307020c0306070801150e04020d06120b060904051f090b010b03090609030406020a031103210f06060316120615050c1216030c0602360f010503130507 69
    0x6000340e00540710140141c0103142c410555050030026182c0102062034009495031402500020f980800c400b008100140409429215a202e0b0191580c2601d01e0104000d070315518103450122003c00c480440e01020b1050010320545840820a440785401c1009082d0060b0051000d50303a2101c1c0301c400b811495940d110110100c1e100012250290040034042940e901782900740900e400e030000e02202c0d0940c010041840441c2d4085101c40246074503003001200d500800d80e1150a50007900d00c000c0d421a65000f80854401048552901a18011480c0c0d0400d4803032000b80981d0f44401c44940011800d1041a1020941325207918909515034040c00030f40192101341840c4520529020035002070004511032030700c002e00b4000e06582914800c001441c0c50101042e00008a00031075001e000d008071880f80c45e041c0080350f0100c52409026071502c80d5504501c00505000e1030350f2005a80d10a80315031a45801801c1079003254040e860141c4440d41140d54010951444143d0004c00301c40c503010340c0100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 162846034 1250 162844784 162844789
    0x1141909060617010f0c02070b0f04080f010b0117060f06070203011506020c0a090905070b07080c0a060c0f0c020d020f030a02061c05100f0b0d0204080a030206060109050d0c05060a0e 80
    0x32a00600a07160741803c0341651a5015030a554401e1a5650401d1410f09041106500060103900300c03030030544c0c165140ca0140b0150f2203039024a60121525000344041042440010351044450443c262129104601d483e00c144540e4141103c2c0e03207400800c058500305281c81c0c800068a140c5200500109180394501019000c2803242c3c1e2002c2c003d46e014945120481c54289800b0000e001d1030310041240c90001d45a240d0364000c42e11401c200b2100c001128400c0c00707050402c4030302c02c24a070310480308044e1a91804200410310941003400141e002c1070b480c0300305031103880408919030b002002c003800803030f4607020411001c0e518031300142e041c405d0259000060700c81702c01414045042003c6a409182094941029204010142c03401d0440ca0181800800a0b120904d0181c6a40034460364541030f03108a030b44005e20075a048460340703101b90b0a1080800d540041c640b481740000f80c0e201c1460076680e03414480c00d06450200201a040804814402030602a02900700a1082d140000030b80700658003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 162847284 1250 162846034 162846041
    0x2a06110a0804060e12030f04020a24121b12020c1002040504060b0304021005180a0306050405070b0910030209061e0d0501060f05030103020d14060c0901110114190906 73
    0x1404030206071400c041105000c220310810f056801148054031003544074214009845c4001800414002241030128080d5203844801c003010340031402003100c0c50141401d1241c01c8401901803400012519420094103407218000c099120205045d001829800c0a6069900c2c0700e000344101080b90b03090141200342c800420014400c603400c0c84005a031241028180015140a030304101c040c550200240130040e100c1603424030240c041860810384814882c20014440001da5140300da102c505c50b03002105002e120361203280207900c00e00850b100150380700d50060684c0560305115034000b405070043d50801d40039400074903030a100109100c1c54140340008203224640a800300400300b120211300c0705400d03140d0341301c0e180c050544c1d810300c801080340c42c810040c00c0744014000280240780e201d040004000600d241840c0030402a025101c583c58200f1401e01240c1040e034110b030025000e1130042030021410b100b89180401d4079140f800ea02d54031995110607000ca080c0c003020304540e0320395501c80480c03042d22 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 162848534 1250 162847284 162847297
    0xc09150d0207060f0924110f0904050f01031214090910180501121101050915030a1404080406110f03270f0307090b010212031f062a0611 60
    0x3000585070001400d0000484103586500603c2524250300d10021800030b1a0041c00d244000ca4401c0c103a290018111000e030078007015103d1604008105c00c5003413003209000d4500868155000c001c542d445031400d80c0c0c189028880500a107075005092424180304241e60906200040e0b0043c0c5080e1001c40441e641c2c0c0000c03070748016000404074050041545080941e818809490802d100b1541800070084c40f44440901c0108590080b4407181d242d64001e5090b180103440042045490342150100200181d0040740d4004806162041c114006540c2e40c00c214002c9800c0380c9564141800d00c54290b50103005805d42c0351941c400c00c6841c0f20000300400007401c050b0010101c0030550080200b4404450308100b09040c030429810141c4c400540b80003c0381c6c0c02710b541049000c5002403c03140180e003031030402c3e8072141031850000204084182458a00c0e2404081c0c1d8050b041407a55070030040b21803020b891810b019850002018004440480c940304000310700411000811080010390303032400e54881c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 162849784 1250 162848534 162848557
    0x3060f060108100b09010302070c0308180a0609030302030715060b040305010915050601120b01050d14041104020c0a03110c0604060e1011030405010518040e06041101090e0c0915 78
    0x240100440381d603211420540044244030707916942414800245000c0c040d080615040542c0458101d05201c00004004010f54209090aa4032000c10140c4101c0500e04400d150065500d002c0c00500a441081e10741e00300d0750968060340c00c2007910340c0d5500c0040d044a64510b1055101d0502103180a44040108010b600c10000011424854901f05400101400720055080d14200030040140d03000b50a00d640400c1603440000d0072040100140c4060062900c00d401042c5042a5245207040b4080840e01403406a00f14608035450714081005030320901009051a800c242c01e40340000380a0a03042d900c0d0307082c441c10b4401c01c0540c00d012a881d50420360199000400024501c3c0c01c2c0e08114601110300c80f0189407061510400c510420707501d104500c80c041c10000000740c0c1c80c0b441d042610380000c09040040040c03124521954840c0d58074170051750f0681e07445564552186c50382d0b0040800b4800c232a54002450b42035680d10310503c4407034014244150300700d80c851040140e040c641c40020407024070308 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 162851034 1250 162849784 162849811
    0xb0d0206190e01030b09180115140f0d030c0b090a0b04030503010603151a09060c030a08041a060f040c030b040f0608070e0c030a02030c040f080a0b0603030712030513020306 76
    0xa06800074a852402c050980c1410300c0c0120071800b50b214008883e5214640124044043c1107035801e040c0185104800e0b5214050a141c0100c1e05d45a216010000ca0074101ca1410050000c0c3c0100030b4034801c0c001008000ca20301d0b03031605001541c1c0001c0544e015003803500342e030704000d802c0e112940f01c1101102e0031000240000b0051001e541c1600c50381c268520f4001810300358900781912910716100f006c142d140c00010200340ca4540d81e450030115404198584240c03901c401720084081d10340381e416101152040203c0c60090501c01010800301d2159034020503108240c00354030240002000001035100405845116502440c1c4980c098800c1a800c21900040c0702890460940d04003002174000520601c0d9440a1020900104040d650011020880140d40c0d40320301445104511a40d88007984c2c1d0103035032030000780d400c42c04901d0004081c091a1400d4999648400301600c1b4030910500038001c1240c1c1099600d05403095002550104022400c1400c18845400180c942642120481090300700d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 162852284 1250 162851034 162851077
    0x6060b120a0b1302090a12050708010c0807050405040903030b21120c1b06070b09010203070e120a03120605310213060c0203011407080402011409130b0d0206 69
    0x80c0300203a80e4051849101000302c002c1c442c0000c0c0740703030800e409002c41040e0049401e11040c0d0751411400018100c0745055042c90540785031494407008944500c1015520706000294510300410580d032141c10300755500b903d800d00b410b0410004000c4c00c40e082d81059554690390000e81c82d0210240e0b00b041c0d8607401e46481d9401c40c001c0391300e030803d80321551007580300600c041103003100d000a0f0390002e0300c4801801080c2d018890089a0b00c3c1c0074042001c0c10405442040c02800281940214081c1039259544000c81c0402018004018508414400c15601520000703001ca4880c1000c4007100f03588500124415580e480040c50300a20b001aa42902c01305100c1d045003c40759404520100001d00700547c184020560058504442440b0320801e020010340a01c1c11981c0a5100012420b0151800b40c2c3c0c50408040c003d000c1502114202d0200392400740022510101000b0f03201440c400800040c0e089880d5101c0f07e025241403000726401c8240f0044010040c1d94420142102040d044007a642911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 162853534 1250 162852284 162852307
    0x1121509290a060509040b06190c0303110702060a0806040f11120a06081c0216030b040b07020105040b06120c13050402190602060c0a120507020607110f0a020d03090306060b 76
    0x8a8041e980d11518030b416041000c1d503000b4054030410002100c001440303010000100d000341c8130320240074007074407102d040c0c080728a078200008032403060180c4d41c104464004075000314421b110303810b07000c1d60010043c810412450f104462080c1c0c003140151003c50080c807c03003440c0d4140d44000340441c40b07060b004603d0340c5000f0800d052242e8400428001030107100d01e0030140944400c203503107245a042400d200c2840e000d60003042141c011000c0e070100b60103169a44d00340011038040684048070188405808581054414040d442c0101c0c1c0090070501c19894200411602d662440803888407070013000c500031410358504000c46010a40c84002203603a2401e0710400001c400c03500044864007803061414441154000f90580d40710030034851855440c040c14034190b48100380b484008841034100010003003444d5000c034185026104503110344800e0750001c964182c90b01e01ca1051a030013503108101d14005480c140c3c1007203240c2c40c080d0800058031070702e945806083d680030390000b1280003000500d034a80326 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 162854784 1250 162853534 162853601
    0x3020301140415090207080403080d060504060e070906110c03030705150c0a080402010c081213030305070507020d02060f040803030a0902010e0d050d08040203010e07080c190501121509 81
    0x18603084404200760201e0f20300d601142c8010b40100c1c160310703a0120f003090800c644941183e010750307003103000c4940381c4e03408801c00009001c1c6406410301460821f040001d160740c1034420b9a0003900b0686462486501b0a102150701005011514400c1c0c1701c0c41050078815101403000b0700140c3c0c020350150652031682581030345041006403540d8080003041090540603544022085d0b040b030790918241c240c1500c142004d8909010300c104405440301d0316428450301d07102c4040b400305a075100392070900c07403642c1340c89041e1800c1c029000065045140c5e03003265001840c01c100102000005800d0717140c207103502e59041500d113400440c0c03d0f581c50750341c8104c450155038001041328a039401c201c0d90f880031052a0340d1095140c07003d103188001400400008a81107580a400008149034400100e50301d0580d036421403560b413000c0280540c021107095621582030000e105051059490603180d407141c000042c0c0249000b04020142c2c0e9400f42c49014011503c800c4a00991000e40201c07092810594480f10400c00c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 162856034 1250 162854784 162854819
    0x506151c140618060d1e0c0f1406030c0c06090604051516030c2304060e0d03020309010809160b09040e070e0a0b0a030215030108070b040e0a0b040b09040303020301 72
    0x680038454104845603032043c0c42d10b0540003220304122401c3c0c46180104074072a055050040031070649a4011075401c110100d00180c00d400303546100441a6140750329444081280201c4c6030004615828403403a080c1007000f1030300701551211852034070301d5a00e02141045015076100d030080c1c00110034441444010088164a0548071100130181d0400390b640c0311005088a80f41b505254441100344415802540e841c0c580103914604418010000d0544c0a070941c41801840b020031602004003080b410500c602040c0d440c1d054004502d0000c2c10170040d107004d403006080060740c1c8250000101146020701e0310fa0f000307140c254270039900c1c1d81c0700d0b00070001035412400c4114819031017102c0401621500441c990703040b214541c00091030340390040c04214000269003000e9082401100700800d00085200254102d40d117210a80302080e44907914003a10f88100d11848100030000b45c040ba032820450342c812030920b05c2c001e00009203d2007640c049078140d07004640c21f0f40070a5010004014509454691416 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 162857284 1250 162856034 162856061
    0x418050708060709060819090503030712020f03040221070905040b0a050f0403050c032b0c0c0b0403032a030e0606040c050301033315051509040506151c 67
    0x2e680c9410a0300410000080c0f05030420031128902142241040c2c40e2041c81c0c0c5c05914105104076a01810050399070b500130380300900040c001d0002c598102241c1d00c20ba424141030381740c84614603119030b001c02c0000813101801440396150b1a40c0740d14803500402c2118000e00b80a240400c5c3c1d031419080c40880e80d103000302198256410310080100d088034240307515038019490b04204d0744840d0300c400f1030f0f482c40c010f031506070030b03201c001c0200b5900300000e1040d5040340081041090200b5207256808031100040745030f00130448185103012a002034025040307000080300944061204418400c00d0321400224000c0d60070200e0b03900e00700c00c0710190382071003410340c0300806403018000307070101c1c2000404c0303440305100150078402d40c401000ca203c00c0020007030302980760010748811499805031007000100061140d505011456000001e203d0a110950004003c01003c1550402c00c2110501014100c02000598400b41c0000641c07000190503002d401c40c02140300c0d8600380c100d11080d5400407180d02c50b401c0c0e007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 162858534 1250 162857284 162857293
    0x1309060e06060702040905030906160506090f060c030601170103110405090708070b09040e061e311103010c0e030c030a020609060706140705191812020f0418050708 72
    0x841c40e11203400316966643e058400190507503e0342030030b038118000d1940381a40402d001496170300714060404981e11442c020001d64031540c540001ca95603501e001c007aa1310254002c0c0f40010b04104000001c3e43e07001300181007074600c034041100a122514402d030001c40c1e031003401c4034048082c0d041620a0030f5206c2d221000910f1403e08280b6403a030f80d0421403041c140200c40c0007440c0c0d05151150382000e64403803041422030740141408409650101040e074034284264502e200020b5041c407418192400715400f104644000900c01105115030107418402aa100501005650303d1074170240b04001103c015660342c141c106072258201400e01004a1030303036100354016017500000d03036148401c9500c40071040f40c40f00d80d200140c0c542200940600201541d030030480c041040540e5070840d0060911401c414020b031000c0442950941d90310410710154080c0c00c0b44100d05010141410021840711800102410b001c285010009011382340240107c031814800c12098104110040280c1e030058031001c1c003c0d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 162859784 1250 162858534 162858541
    0x5060310150c050c0409060b0303070c17010c0e0108070c050609061b030c040e1905071806030e070b0a09080703110906030303070c0204090f06090b04030807050c03031b0408031309060e 81
    0x100c0d5500b111101445c4110f0351a01100700300440340d4001e8070303188005002c0c0c135241c3d0802e09203500344840e903114000b04d00352028504181041d062040000c04100e54032400d494603400c0004540010004100d10148143c0242d1200400c2c2c0030080c3ca885091020002d041380e16261440390010340c8000e40c0200000d070300740f0a0016454404081e01d0a88004c11001da03c942d488040c2c8104000c0401940d440c10741c07515003840b407030325800100300802c8103840d030b88840d410b640c40104070100c0d006010626040e1700182018860b4054600090800040340e20780145001e4459050a00b0609143d00849042c203030fa0100c0040790400c00422503100ca41280558194540101e01402141d051700c802889a80e031464002c040043d4507001ca405140c020408101e801007a00d00400413540039541940852080e50000c1e041600c035030200c410126007403002e1801c503114000d254010324007401d0a071000030001d010209017281d00300007400030205c040b07000c482c0e00c0e80392209007003c5401c1508016145e444c0042003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 162861034 1250 162859784 162859793
    0x1b070605180f01150b2b02091302120609040f0212010b031207020406061403041202150403120e01060602120309012d050a020702061c0f0e0a02030f010c090303140405060310150c 78
    0x5903012088928981c3e9046c800e08180c060007485003004c4907500c04059182501402c02980c0a00341c800010010510380c0d4070745500f0001003c000303c2d0001c081004010301b020040c2005040da02c8180c042000100700403145c900040e0403c40409a010411140428906c0952030a401010020501400c26882c101296910050305100003000a014405440c044a090b20b00c2041000050608a019400181003038503008002440310300c852482c1c20300701886500142e4041c800c0e181101c5143e0000d10b48003906269400c0c841c0c000030690042956541d5880c0c07030344915071082580b003000c03904c4402607032102561107000300e41c3c2c080c01c8500101d20511004005813110b4048940228517981102c00f00304c0c102c80180c2c050142c5e078800185403820510004620f200000c0c07001c80403842103080d41c80740100c1d07010a500300e0b10a0780703100000582940003000424010300030181141550b849262916440c2d002080c0294070507aa03004047c54144000c120700032001c1203410452010f8900100120b801c4d448 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 162862284 1250 162861034 162861067
    0x40b010c02010f090b0a03020406021005010806060d021c050102130807030804090207061e200f0313031b0b150105030f01030611090a0b040303081b070605180f01150b 73
    0xc0081c14040340c2a4094907090007040c0c208001c2403100580c5540f134440d000c00a010750040d2040c3c3c0054070481c0c148880c40150790081a050390f110000500302c07543c0c4e5404010603603c036684141e8000102e12031326021100d15210100c105401540007513540c102e00d00c3c030b0038840c0794140d00c05000f5400000c401e000042000b001c84080725080000582c03286141c4c05d184000740201d010a443d01d09003034240c402c98280036002840840c4924290f10440480d04003140191301c1414003094442d03d040001a6007000130b0711018031110701230314204850366280da0109200d60002401500e0a81d1800c04008000349680c07180749084000307113451800d6043c480241c8503171b141c06020080456454801140b022080c00f416610710a400a200010312542c1e440d107282d20380c0c070500003540020040d0000942c4a040310030140d00c001450070119240569030b4442400520b8090070512000d4004107d620100008200301c41004200000000307110f41c0050303420000e05c4c000e03801404040c80c148203481c0555032810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 162863534 1250 162862284 162862307
    0x5030403031e05070e090c09090109090305310605072001030e0a060213060306050d08030403090905010b1305041112090304030203010c0207060306050d02060f0d110c010b0f040b01 79
    0xd0110b14021208030805940c56884070b4035004514020030041c20315441402000f40c95404c0d5000200398a030340200c0303403491164004060300140706000402c007000c0c844c0e000d901c8003402840c080b0b0804075116000140005c1c0c00100e0400c0e41030b01d00001010b1454a90550010446402d101d85400b034942c2c5e0f6a08440703001101241040030b03400340c9541c035074013a811007110400c02c0c1064075480304242c90484001c0d0401e0341d1250b10280f021070086605400fa10585080d103c0041c4001c07185e110340e40c3d9000c1550300081c011402c008508100003034011540c0103541c0a0a440d140f81070f02c03a83e403071604c140c4082042c3d0180d84205e050000d5005106a00e0f070490382c11101180d01003e10fa91034401180c46d40c800e540c8001c4d0035600e40840d962442d640400c0d907005990565601b030012070340c1c0d6410000c1ca201c1e800400f07540400108482c84003100307030a009101240905001003029490320410610680200f242c200559449003d250b605107410380c080070550904803001c0059500c0d10000801450044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 162864784 1250 162863534 162863537
    0x90803090a0302121e0307030305010e0402150c12130303030b030d2708030d0e0d02060709090507200601090c0c0507050d050307060501060c0308060d110405060402070b0108010914070605030403 85
    0x26071103001d13400d02400900e01c2e00002810f0000c444070000ba1090f940d44c0518015000203151400100380e03a800c143d02a40a83d80040070090890601d040e40003003503101788400c21072480741c03144a0b8024a1854081c04060b10051031020102c0d280d418040d083d02c1414107194461b40250507820a101d41000c620030490b251a11a001940f0601c01903a03551012038002e030040e0320010590002203115500904075800154080d541c80e41c00d0801c00380d80d04c0c44165800d202081d41c1c00c00074080f81c14584c0c05258000c040345441e40780c4001c110006a90030742030042402098001100510451401e8022000004d0b05071806000c2814a0784582c1c3e2110901c0c080d80c0d2142603844514000c1c010100140c5071300300e4000d00200800d503035480002d040380c02105412030225400b20002a0b40b40b5101e0403004006030418036041c4008121020480107000c0242180c1e446a404e00800011607441e08100d4060306e03c1c00c00000c0d0740c54043c140440d007403004000c00e1682d60300000e0180089640700342a41c0c1c102c0d80c035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 162866034 1250 162864784 162864799
    0xf0c120b030102040b07080d0e07230d140a03030b0a03031706030a02091003050615060313021f0207090b030106050d06050c0906070b07030506030f07030b09070e16090803090a0302 79
    0x980c00090280c030403a4046410f240c40821140140a04d02004014403064080c0400004555440c041d40342e1005100d0008440c0c062041c5158040759411034003040b02d030040060005580694504002c40c80701c540388189640041580010103804d0b00c2900b25070002266040805861650700410500d101024480641200000301d2010f85040285440c556401800041d41c1e14258401d145e5000c200c0c4802e440314840c42001c114108003110070143c0002c07001e050307079183d6030381c09080394680054000126046a0f041280208201810102010700c03805a07010740030076481c1024840580b0140305e1518866494503a041003581e40d0303e100040313841c6d80080045241d0fa142d07081c014090240d251400c0d009140005e8100400c40d0f40c0340a54400c034203c0d01c0400640e1105030901d40d035843c00cc4080c940a0780101003e001050201281301c0d84007070703100100d410240d280e100e00c403130303a135400e840001515402615124560381c00114070f07000781100d58003d40c10310400e840001c2da000200d1002078000c820 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 162867284 1250 162866034 162866051
    0x201050105120a060e0f0f0d0207050f0108010509090a0203011a0406150804030f0207090c12050a0501082d030a020c0a09020f1804020d060f050111030903032a0715030f0c12 76
    0x140700c2d0021000791b04080d074042c4c5400c950199151013040355040014028050041024507041c19100c10100c010303507842134280c3c00d010501140c0170016240c52418414803031110010303074090003051071015010303031403444040201c0b080c4800d4503007a4000310300154040c034001030300a50054920b5407060700351420b2000e070303040840c0907404c00c1030b0740c1c00103840641082e403040d20b0703150003481e0f04100c007000d480300304900c1d0b4501b0b480d5030449100f80200b1180790428920a8070425580190010b001384540e420040406c0e290070310761550380200e0030040541c0040c04042030707518000018000900f401b450540c5010b03125030488000e44030b1501c01012400d0111814413594940398150303040c0c40e00e58401041016100c910304001240706228031780c00254982c0300094007000c04410f80c0d49000f40a0000d604102c02d0380e44100041c01c85840b444041101c801703d1140102e42080403000402200d00707046007049609800405951303111095103442818a00c0140c4180e40c41030f03280c1000c0740030110010f41e03a02e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 162868534 1250 162867284 162867311
    0xa0e09071d030a02130b190f0303090801181416090e010e16051c060c0201050f0c04050a0e04140a0b0f070504030506060d08040f06030203060301140c030403082203020606010201050105120a06 84
    0x1580780003141d8100c407c400b0110303c2c40303058486181600c0c040d4481080305559905920301ba0f41048a880c0725200c03201c8020000a260803004a60300d030b00301401d4421744110420203290048259002c021030540f16041a46a2102807280080a00c158009044415061500411060100c2c40344030700406600c01004454815280080581d81e4080300c1400700c1000040001e020380410703921503014401c13080100790400080303c221000c0b22070140c00e10000314a407001600725580000c0c401c0d1850300703800601a01003442032100c42a40340c883c000710002420103412408484800405280c10300c42d0401060011810008045074040c17001c032110400344509162060080c06150702580303030b0040b10f09000c24802d400d5005540b01e81d0082d8000c0001c1c09c0c154940c0308002030166101650401c0130004280400d114243d25076002d01190214009890346441030241402140340980041e0800c8051042941c0e0a000d0b0301c2c0100002c41d40c51203000030a0f041aa01c2c2c0342a004001d207510740c1c5400b90b00c03a64 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 162869784 1250 162868534 162868549
    0x1091503090b0903030403080106020c100e04020405040e0604110603040b0c09031623031b0d050c0312040302040f05010509070507110a080304030b10080a03050a0e09071d030a02130b 80
    0x9540c030501420340c83c10b1280c0055500e42054604601280c100c40c00403131a18800194008a25402411982040d26600003580e81c81c0c0d2502d03000d42c000741c00f00400f040c1e940301d0340919442490305d1401800140b5040c1010700c1c0c52860384010f64842c40c0c04105000208020140058001c00307a091200d54481070080001d2030300c490a402c8003410651148002429484171242c55000c410000040d8496203181d010140c80d8187d6100e05070507034151000a40c0da0b4207000100301c0c1c400e403050f0308944440d0340500000745018800038211010440005040c0210700b4280650a03109610804c00d00070f95040c42c000500404000306200c0411001054003400d0003c0d0440d00700584230040c2c00c2c080c0d100c0d01c540890b41c890b4040d0105490758144080801c41035109251610103c03540c04018040c0002e00b50b07800c0300c00390b100d45040e404100d007400c40904e4556980803280d004170003588030341c031000a861645030340c40c501038164148203412820a21015031070b11503401e003001444080001d45840c2140008015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 162871034 1250 162869784 162869801
    0x31707021b130609051b090d060e1603060204180e1c1205040605010815130f0c1d0117160b030a06080a0308060117060f0d030e061804150501091503 65
    0x603500f8900001000211076101501a60228801c02c042144011083c0918030420308115000b00c90080000042030f2180e200300300b40140102603400034111a42e840c01c01036010b40007a02c055500240c1080b04844200034155458200c040510100000015003501d03110311001320306620324007642082500d40f1905405d209030b00c60b001c04200301c3c02c0070b05102008100c2401544400e203e100059203d0401d0b8100440c460800c0c50000013000342c190303640300a000f54a03c0c0840e0000d00281000c1001c81e900c10021240c1c0903202e0301035002e50b02d80140b41e52803040c3d05401a859800c50700407180e040181d55500d00654062058041d41d944440c12003074010405a1b010b540c050040b41d144c10100b5a1003101c00340034010076030324000c1070301001e15180106801a16103c0c0d01002c07020341c010840c2404815841c0c40da0003410301c402210780450101f03800d58441c84a240c42000b11482c14a90351801e8802e07a1030700004a05411041801c01001a000c5240c901800300c1c01300c0a003040e40c00d061303c660000c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 162872284 1250 162871034 162871069
    0x70c0b0c040512060f01050d020307090b040f05040b07020d0503090706030b0a05040c0207031403160b130501060f0503070f05100507050a020409080306040507030905030d0914120304031707021b 85
    0x1a0390780c55001940c4400d0103640113690170600c0400010240307481c401074030405400a000d84442868056042c1c014820004004e03082600e802c58121406110f10800b482140514082c24040c545450003d080c41440003032401030180920034480790003400914241911414240040d800407041c00203180018241c1c02154824141070030a4201e95010941c2030480c7e00c900001000e110001c00000c2d01c030f006000303083c1208a000c0d00c080b404900281070241c0c0050b4070b42c01c40340041049440e80750035a00c403a007104d00030781c440c15420006030808106040080003804d1040c40080c1c02c0100181046944c007412100700400480c10030b00b4000305201103241e15034007d200300706407440c0e0315000d00c05403c00c68003640b049160800203903080b4000d0203101c1c07030954488040c502c4c045c91615120001c009401c010386070010b00f6950b01d28221001c000d60302812204c2100c00c1c0d282d20b018074004080c4681561032115082201c014081079507000580c2d0303414240002511001800440702040c040f603104980c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 162873534 1250 162872284 162872299
    0x3091e0503030c010c110111030c03330f01020312060d03050d0e0a060f020c071a0f0f031006180306050703020f0d0b0307050406050d021005070b0a0209010314070c0b0c0405 76
    0x1008000543c004121701d4003a8980c0d403aa9407401c150b403400c980e424020302c141d0710b00420008a0541250b40116446600000c1c00c100e4540703010840000b1034a18294000c3e0894100c10400041c90110f40104103080701748025498030030051011904000c1c0070b040c65001d418088001d000701030080e01510b00803000000c0c204100c50101c0d9600b59260030115064521b5890301200902a91060003200c441c0c0814000030102c0c540340c1410103e5200d45a1814030404074140074520250a05900400d04110b0001601e500c1b81040281c407918591994002010f01210551101e0210161003000c02204d8029100040b690340d02103090b0083c0c0309030080c0c000d0003040022054039408072640240042c400c16004c55509039159407c4c80300300d0312035010b5594003000e00b45000d001460f294100c0840c0000600e02a4240000381c0d135134081903502903404a411079004544407209591620a0007402000400c44d95080e0800136000b03001c060300300c14080d082001010010302c401e6003c5c4119130081002070a400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 162874784 1250 162873534 162873547
    0x10050d050c10110a0f0308060114031f05060a020303010906090216150f05040302030a090e07050d0b0a030b040804031203060311060313022701080109020117041a04080d0509060403091e050303 84
    0x9440205c20040c214007051640700440c541d0f52058041c0800301c44400c0f003092564880e4184140c201020305500c0d88444850391000ca05902c520015241500854004503182c1d41010101030988501b5008031500910500c12540481341030880400884d4111581714000040d2040f1100035100303520120b039500741007034180704c1003540c004001c0200001c0c9584d90302481d52944003e0002c000155202030010360280403c40d111031071b541c03040c01c1214008042d81e001e02d54070781d00e4414602040b0f60955841c080864100140142c1c0401c4411038242d0b890204804c90440c1d450402c21510500c9890262002000245002c01904524016640c0007030a0708a071882642041440344d40c01d03080c90091141403000081e08030300502482e981e00d54140c44242d0307540440550324083c10030092090f10189a2200150304107540803c019015030b000c3c3c115650340380325a481d00b00c02d40720041c001c134519610003004c00c0082588010b21105484205014141001c2046444442c100f01038001c40e078180000541c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 162876034 1250 162874784 162874793
    0x30203010510030501050603060124020f060907291e07020306010b03060a0512030924030408040603050606120103060209030109050115050312030106080a02030c04120b10050d050c10110a 82
    0xe070b41260b02c070308000d001994515080c90b03102ca1080c45115808201c914019014000704083d120340c894280c812203c40c001c401000c24903001c401d0f10040c03031641100350180092552540029040e00d00d540408050760310840d0031040f00c0c0329894505480000c2c501c08000104003190840e5082a0004d04840301c558680001c40e4140c0c3c020b4484503c201c0340da000c0042e00b400c0c8680c00d2101101c0100265050841c1c0c070b010701071041c56560301c07040300322403907004443c0011245024600a80c01601d02c0786c0c440c3d041c2070001d41160b0015200c544206000c0c03040c02c514044001d0480c0c15240c0c064405078035a41c413500424054022220000c15550a0502460031050440f8102c82110421402c8545008400c1c80444180c0310070301071070b000a1100380019140781601c3c1c00858004049001952900355541a00c0e0580c0c41d4201d012a0781c20b440005212029140100c1500908011211041c1007103c0d90307241303607440c460006400d01030688040d0503001c1501601d003084030750001c1c0080d03031069546842d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 162877284 1250 162876034 162876061
    0x6050301020d0b011e020c090601030b030d08040606141c0309051c0b010e010e04030e01090329060108130f050304030602120a060e1618091109030c04020f070b0a060302030105 77
    0x10b101e00017025a0140f0402400c0074559200c03001036a0084d01c031400020b0244440200000e1600c1e051503115120400755440400400f440700c04540d070740645a0a0a00d05101916459849404501044100090b15655256144002c900ac800b10f1019445241c0b034280c45020440d0b0042c0e6012100c0610301440180380030050403c14401d0084590703a80c5c0315150309002c03540a004101c1c9141003800007800203805a01c0c85001c03138005041c40d280b02d560320f90b0f50b0421003a0609111307601c0310f10000f0007a0008981c1c10059003055090a062219203407001c01d6905401d000400500310222511100b401e01800780304450140d50000d5055548095244c13145130509816100003000d00e140030780000700040c100c0640c5002e45010f20b0785021a240c001c0040351075503680d8030320b0801489185800a0f141c0d0071442919821700070140500c0d210700c1c0c2e1408041c14070461368806c0c3d010701d004002c044400e2510504030b8007000d40c400008440340d1992085c1800900e5a504000e406600c1d004c140101c00b24600b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 162878534 1250 162877284 162877301
    0x616110a1202011a0409080a05220b07050c0f03060c210702150a1401090509030c010f0c0f02070503061b040f060c02040c03090c0311010201090f0c0e0c040b031906050301020d 77
    0x1000030040e070614090104a0343c11604c0a05040700901c8008d40c030b01c0c4500d0007040034840405042c0000c0b416003c03025040403e960045003940b000240c0d507010400f080c86881c1c40440b080360b03140742d2502c554002c0381c0c54810040990b0b8050314000b4801d0509110350715940488604030781000d07007601d010300300a5903c000a60380d0441e401d000c140080c8041d0104e000c3c0c0c03c101c841601c2e41000d140d10f080421005410080c01500e0076010600041400e80c209100d80c0d803440340c1084012400350440c94000e00000c0e18001c640c811500440300500c450f0714001003950300003030902c8140c1445d480b20104106140600c2d0041c03080b800d50200d00040540c3c2c0f01c1d4009402c64000c4408028000189100744c00725021800c006203c0c001040080001c688020b0502502c43e8041c000840d84c2545603403844035201b0b401d00101d411008080081c48001031074120650301000001e12140303024146045500180401030200c8034004200968246141c2144c00031001810003030002c0d51600800b041000140c24920b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 162879784 1250 162878534 162878561
    0xc0c0a0b040c080f0307080a05090628090b0711180403080f0c0304030c03030504021c0803040c09230603120c0d0f1b02060702061e040608090616110a120201 69
    0x30390003c50790150110b210703900d100d0050010f52034002950364010b400c2d00b15a8094040c044280310101e003644801d00105400c0b20a00004003010f220004150001541959600e0401c01c443c041400441425000c0781c001c5c42e00420414a41d8102c840010b0100c0843c41843c200389520b0740a02c801c041e00a020300380108443c0494403503545d5a0908101304e40000c460280008460708050340202e8080c0d4005034100d03001a001c1004203420102031250034809000c105c8018000200700001e12240041190182c07512507028402c0542c02c0040c20502ca100301072000034004074501040c1c1035075041160112140682c5030b4241c480741c004250a0311000e080ca07400c401b103240c0825822200d84205480390700980400881c02c00d44901c2c3d001c2c0003440d00107c9007260004010411008101c2c100440764208003940000550340340e0138400001c040d0707503019000000b5076003c20148010440000c09609a51240c1e01d070a41c0230300c2070080002e00d0148404005001c0131800082145580ea041d00000200d1008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 162881034 1250 162879784 162879803
    0x1205121c06090c0c021314010602031c09260705120406030b0a030b07050d02090604080610090908070b041a090106050a050904080910020708070e071d0f090c0c0a0b04 73
    0x22491018140c440d501601e400088010710138600516000c076099481564802e000170340b50605601e00d1300b4a2000781c000201692021030018101808803803807a010f500643d00a0000121541c2c0e82d2814103002c10440ca042e5400024000111441c2c6041c0d694107034200003118040b9140440d40c4500c0c0d030183c05030b0301c0040c0c2840980c0c6458180410750008a13948041448100d603219103049513030b40c000306040304296808004240d119a2003c0c0608003900000c0082c100b2400c4c1a000100d2a80040c3c1c0041c5d070450802c4c0c04400410705200c15074070300d5a085540340445503224031309141101c4c103911030803c103030402d41c050141c1404150301190545c3d000307417500852543c840f4100003100000b1940140842c4040007000e010781408010030031000c4803801240c101645654102d400c050742500080c1d92042040c0410502d90350001c1c03500c40441c4207a00c44083c4a42c0480407443c44040201c2c030354020328059004c5503209c40c00c0c0f0126901404071005070b030343c400d04602d4884a255000d46054948001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 162882284 1250 162881034 162881039
    0x50f030a0801090506030c0d0204050a0e070b13060207061e090e0421110709090f151515080609071b0501020c0c011106010324060816060306050a1205121c06 69
    0x1b40010002034043d801803854900c02c07102d0b0308020203000d00905081030541c4804d945220702c0c0e010441040909110700206403a085003c0000c8030040300e80d40f003001103611500080002e281c1100c000310400c04400c01026101d011300c0801d440c03040c03a40d44014840f00d519070411090203004104640c9194140210020011461400b10b03800c030221000440540c201000c100311030348180e88a13030345070340c45540d9284001203603480c0c07850380410401500c02150345a404088203002e24007200d2010b41013074050080c1403859101c6c01041c0b440c0c0100032034028144540482c90840c0650b00d80c141041901c0c1c2940318109051074141d0203500040031540c036510540741e840740c5540c061032002008001c603100034403d0381e186454049446480050300b8032100030f900d21800c110121409000050605800140801c0411250003141650740394480401c040c54010140020340e02c1c209140115404401c41d0390040e0b00c207080080c140300c141101501050000100b0b00c2c0142c607a41c10b8440040325100e010840c040d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 162883534 1250 162882284 162882289
    0xc0106091109120c0303030f010e070804120e03071a120a0b0303070f06090c1d060306070207060f02030c06010e040212010b0120150906330d050f030a0801090506 71
    0x7940c0c2000504007010501549040b801c2200c07046200111141c102c0d1003504800b00481c1c15a4800d440d006010400c6500500040ae07010000030780010840c0351802c10b0b480c268861004041c501e18140b410040808298a0150741c1008000c020f450146569859010151111300440d4421004010100c0540f000a82c829580d031068003120748014000c2d515000d8556511030001e00048000ca40d910758840c0780c1c60100d00b40d80010000b6200b0260058102c042e44540a2640d00d00144850711070f5001504001c01c6a502044007412900f10381824100d40803855020b07030840c0904410745042e8440c9100014a20040d43d40541c0200c3c020707540d904480c1848189982039450140318180841c00c80c0c4c03090754041c00400300742c4980601040036030300404c001900c0c265440e40c05403000500c6074013a00c2441740700400d40c0481a051645841c1c214688048200124058810b500540348540d0950300403d06100d818042e11611000801c01d0300e42e40c0c01c2c8080058211002030080503d00c03440e000004800b0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 162884784 1250 162883534 162883541
    0x408120304120e010203040e09011e090f03180e04060b04060b07050303010e15061810020304050f13091e051006030b0612030c070e150102060f2a0a050c010609 70
    0x5030b8105002218030844910107451a0740319203006811440104400502c920256003980d000d80b42d501d00104580641d0525031858171080c00010740164034118520b0001180c103200d08100541c90b040411008001c1500446038665540c8044c549503991b10400040240e036034802249140121070820429490780d03141400e901805100400c00c0d0701c00c000601c82000c0601d030203580207010442c00c1c1c2c048143c000c0410300c02d0300308031085a6464026a510021407401c2003408807454414030041d410949040c1c00602c5501c44010401d015120601198612900ca031300450a001e030010407103520f8049142500c00b103480d117000c041d6110300465105441080050103508112504001004882d4484004100d030000401049050344d1000b00b0025843c018240302c101c008081d4020001c1d1035183c020706c5000e9085c10880301d030741150401810000d400040d012003a400031f40a48160100c0140300f04c80986e18014407500d03550b160004030795841c87c982d005004284004c1180000c0c000143e031645d040040c3e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 162886034 1250 162884784 162884791
    0x8070b15010f0305060f060415080105150406030b040e0106030f050c040207120503060d0b0a02070201080f040c03080708070f210f020304270203010909020a0e0702060402010c14100204081203 84
    0x42c0075448a0010038070940056400c444010003000038800d0407000120035500c40c0d031203e00d20440e40c082200d4001d4100c4210b500610f000c6d20b41405400d0f07107000b035004910940c0554400d15550381150710141c1c03555071182c02d088460308020807446849040016820080580880d454440c188243c0303058105802600c81c1e6660050090f51500c2500e00c0a079040e800080240350880b46028440001c18088513441d401822000c20040c0c0d82c0c0d0f20fa0000510b2058020403605091005400b4040002c1d510103504085036000062280c4429a92421104074442d410000c1d11020200180c0000d1010340010081c00d4a0040c800007552280518103541d400c00052103400540c100340000c02c802c0c0145801200c42a0b5600e02c44828a0015803814040742c1003070708546d80c3c10780da61600e0011810110041c001400c0c2000c1d4031030b028a04168025696803004100170f040090440c038130020400840082c0b50408101e0303095179600f84499104d40000c0d04244607582d030707620490f400c1c00d000d0302e448802c41c1d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 162887284 1250 162886034 162886037
    0xc06050a08060d050a0605010b130504020405060301050d0309091b080601020c0a030308070c0503040f05040b010503090d0507020a03050d2c21150709150323060103060b0708070b1501 80
    0x207456491004000183c0e070500420340b2903016003a100c1c4009842407103424040c1408450395038071105841454102c0b80956003000e40a140704000902090303a031320003560304480302141c440700a400c051608542c03030100c40e03110901140c2848217031103003140c000080d40c0180005a4440d5010b41c0c49000482e500d0b0500003c0e280c000b003000c01d052010a11480c025075002c0d41d103007040300d00340c015580e0310b40c81c0d54001d91010440c40c06441003441b50f4a4030b806080c606580919241d0b0035800d080f06d4403602c48041001c01c00c18080002010811501e803200648000d58210080d591003a4000ea40038003001046902d20664600c52030341c0f01741014030518007600004024100094911609810352000d6944d401103541e248600e0344c071081c06107440c10030706200304501d1380c031600954a0468103107038910018110109050030213000000e0034034180c2c42182040c3c46801140c40b291200380041e401420a60080c0c030f00300e078000940e03c0a2000030001071103035512800d84c1e69200c0e6650f148040000c500b1000307890 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 162888534 1250 162887284 162887297
    0xa05180109050f010c0201051603030605030c0a0f0b0307030605090901050a05100605040608150a081e010507050f09040e010606050c16050105220e0f04050c0f0f0d05070902030a06030c06050a 84
    0x210f15485160410200383c07040c1803003850a904c4105124900d0101007084001a45a07201403140c1e06003881883c166000907262040542c0c00d00c3c05000051480b40503814290303030088006104948240c01070300060202900040c418206085101d003e0301d82150300740742d000d09090101d8885010590003004a40859031001c0c101400c0520407200200007502a03000c858004543c9284d50382c0e100c10081c0100360040081550230308030404140c284000a00340d42550340351004225119070440e040b01c5c0002c0040c84a0390b0b0314090440042c00420104980584961a00001003107198100c0b000b0032591400500f11410001780c24111000320301107000380c07400902c2c01c0c000707001c0001e40036401103048072504101410494992503c2e0050400480e01e40a40e03050b44030a21060040510a080382c0150070396603100514411004a00d2410704008410f00800860b200e19003030002c11312418020b0826000195524103000383c511000d048a40010fa40b121129440007031a64014401c44514400e2a200c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 162889784 1250 162888534 162888559
    0x60e1b09010507020103020405120307170909040209090307120203360f060f0a031506170f1e0114090f070e09040f0b1303030605012d03110a0518010905 67
    0x11102d036041508100d0501d5002c0c000400c05642e41c1940c400c0d50040100116118029424000000b8102d90790102d581c50003081140040d1321490aa40c0d807198060791205015107541080c949503100782d180141100c0b100c44607070243c0640c040001c03c0b50742150100181c003200d860b41e0180c00e05900c001800b40000b00303050a0021410003c01d802c000d04001401c41d81842c8003d0002c1100364011490b03140029510500c0200b6008a800d00d02c0c05803041d85041e02140c0e10061101701c3d4070201a2801c0404040300d000141d8528441200721000150008c04e1201542c0d24015011012085400140b240c115200051036109170701e0781c0580300741c010b40c2d50045201200418044a1f01d00030f0401d5400d441c4040c982c102051120070082e00480d401e480d0100608420f0034000c2c102d600319040981080740130920944450111002d0203403500007512208ac5034054090709800410441880854200010074404500c81d00000601100a401010030303018441510044801c0c54160050300d90020640554 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 162891034 1250 162889784 162889787
    0x10e061510080a09080922051003050a140f070e010f080c0d06090312110d050604060503033907140103052e17070303030f0207020303040312090315060e1b0901 70
    0xd214a0f000d46891843c003402c0c600404ca00300c40f42050781f17013400c201503420384919071140300b02c540c482565400c1e1152103056650740c0d9112800d85802402e00812148007440384c001c2841411050300b200d00072200da190781ca041f071207000a42440303150780d015442c20001a1845012075041c6200340000c014a1001034103030340340030040c01140380c19410041411038000b45400c0078480c13103980360415004281c0301c0407803046200c2aa10001d000900650400030308000d01d17140041568800c01c1c00e01c0040c102c041c1500304521300075102891481883c25800b0003000c1150700030076103400f03540380c20b2a08106003495400650549030300b41d5002c110100c54a240308050a2442021060700406a6401c1441955252120400e82d130f0080c080ca400d41100e04d08204054141c450010b81c03400404007581040966000240c6900643c40007401d040c42c00d0049100562140e07003580d003d50341c040168220007807114000401130115004a4050156210214090032410300c0d91825100f820030342c0600e004082c400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 162892284 1250 162891034 162891041
    0x1e0714061b070b03090f0115090209040b0d0303050f100e0a0c110a0510061217070f12030504060b0306060904150b030a051c08040503040501050318010e061510080a 72
    0x1d205060741001010505010300590005241c9180610340303074100381c83c0513030030f06240c90a903002981c50704000c2c1d421a24175603200d10840306980c200507256044400420064011004274690044190030010201909940081d000303403140910192503135900c600001c1055010300802420419100000c0c5c0340c0c0c40303103030819000c2046502c0c0040842400c1c400e42868446025002c50b01c54000201ca01e261a020f881a44010100107405241380c0348151941d601c084c0b801400c95054100000c0d0800a00c040380317218030780c003c0d80300f200c3c90100c03146420700400418080d07404596072410300c001d209542c500003c801e8099000180090940c3d100c603030314414021b14911242e40380e00d844041800c400d0f40d0600c4600032450054000d8022102400008041c501d03203072880c882440108014031010071000002e860a4075421700f4820f0792a111040c6051001613821a0030303c02d90300b41540c907103143e0741c042401d90094141000000030307290000c08010700340071209241c1c0d0000342c480380010089005c540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 162893534 1250 162892284 162892297
    0x120b0c070b1b040504050f04051c0e120c10050c0c300c031603060e011e051f0b07050c010219030315080d0801080f0d0e0904020415081e071406 63
    0x20b500d1074581e9800c01314054800807a07101043d2880301c010130080c400f0601043c00f20300400350204002d509200005080c080400c0f2000740600700c203040034618140c2c20000101003203401031000e0021042000020314692102541c00d005000d881c0c0c54803058101050700400103000c40203500c1900301402c0d00078148048162080000d849024010b0030242c4080c010b0b110303480300602c4854085070030f505015003512a10b24074803045070300d400d190070b4190fa00304030201240c5414520109283d2209200f02c4100c5454140c900c10390740745560000b41c03800c80740f0000c0c100c0c1841070b000c0e51900b00481005a0b25902d01140c01080060040c02c0c00002070701c42c0c0e002210608501c101c0c01642d54540864501e0010941c3c644400309000c00018060054208a507042c12a00c480081c259500345600040a141d04116010301850510011404540e83c5410240c02c40201010b01d01d00c255442c103205070f496851080c0521801501e85451400340f40c00b00d0b01340142c4810202c2d403650f802c5d18a0a2154030f5100d0f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 162894784 1250 162893534 162893581
    0x105040f15120209011403030a0c0c0b0d09110d0c0504090203120d0501031a07090612021e0a030f0608070303050f0f041e06170a021602030601120b0c070b 68
    0x3510348500280203801c0c000003030000242603445040e00c520502c04ca640060704001e05580c0d12440d512400d0740e00100300c1e004241d03646480801540a0b00d4020782d11800b43d000000b0324440450202c4441c1c12690000302c0150140001d604480605018000340b14061880602100404e040c2881182056080400080d1025080701e5450081010300304041e0060018101d0340c5da1100b0040060105414103403075110181c10580b445801c0400028207030541501c02e442c1800a13550403203480121546c190745252080082c1020004103098480405a0100398208046407624000800c900602d00c900f005480d05000105542820f581342a03e00350819040700c1e103218820800c0b03106ca4004100640003c0c88980343c0103040401c5000b04445d01030880e00440700f00701004d03a0b6040d08100c0c0328070103600040e000500581e540c1c100c041c03440340b1000c03910000c2c0d09481410000648000e00e40d400c015440e02520031018035440c2d55048021511444002030b1440724500c01050b1858104242c4a0300c20420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 162896034 1250 162894784 162894791
    0x5030a0f020307020d0e0d020d11030f030c15070c080a020106030b13020a030b040804030242070f1104020a0528050a050d060e0c07140c0d0f0c1d0a0f0b090105040f 72
    0x303507800070b009c0c00203051080b25040000c0300504001c0c182040800c940030342d098040c505000026090560310300f480420300c240240801c2c0802c903800d0042600c400c8031a00842681d0782d0b280881c8001e13002c0c101d107200c2192441e00200009620341c000082803036545500a04841c0070511b5034940c54290180a44240d4040e01d04002c0040140e03108d18480844090702c0031201810340e144034445494042d010584550081d01902d00708804903141d00b25202a41d20140350441070a1a00f0301d07150480000c810507410510016440307070b040c2c1d0001c01410f03070b690200142014820f580070b103d07100400c5604071000810710602c104c1c510749000c3e1020b06030b045040c60000440035640c2d4444201500281e408491207d070016030501400740c600c0d80c501d486104e28008208003241e590124034520000e200c0030340117141e04d010301020840c01042d900300900f000701284142800300f0098200d10041904c1842e50640b41019900c40352844bc01801c1c0380d168018040b019a0f860710003404058600900402e5841da0b0303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 162897284 1250 162896034 162896059
    0x6020309070f06090303090b070c12050a150f05061002070605030901020c100b01020d0801050310021c02030a0c090806010b030f04030c1209060e030307050309010e03030706090305030a0f020307020d0e 88
    0x18004072190080038940d850007a1305256041c058007e803500d0b00030750604203081042c50701244824110600701c07503403c00801070400315400c04500300800800014101040c16602c0c1c042c0800e2a0400509e03070700c0d2401c041280b0b032540410000c96503040910440960818102082080c1c02007004d1580300009000162818110f4444541049202200c40003d5079842020310440d580c1080050826403107802c0154665041c040001c0d0f40d4148030325400010f940000b08060400285050f0404002014000750745a007403c800200150140c6d0260034001070700360302d0015004d00c0000d4805e04850420840e9891038561031209621103200600690600c1094840c0800140a4100051142240765201c581d41e40c24030324002c040f03024905215129a0043c018007020420100440d4028102400d100421124420229045008100c07014240303e03c2c0020200926800000661059400110800581e040c4400740802c9000584044005078041e102c2010624050560000d04402c014811041000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 162898534 1250 162897284 162897299
    0x903061f0b04030b221110020705120303060913030e040506010905030a0506070f0302250204060b1204120914010806033c06011d040809090108030c071a070602030907 73
    0x9120b40c1c41110600c0f0300108010022505c40c18602c1c0145095520290990407615014160340c0c4041200e8070501c4030322100c0d03030480c1c000c000c1a07004080c044c010060100c21070315850b450340c10841e103480c052040100042c0c030f0b1000040d41400e001e603164a90030388501645052000502008010a051005009000c2150398082012403911485640100310134a44107500a00401459079080c007410700520400e40070300c41c002401100d540403080200b521480500001e00a0042c40d800b6040750180040c0d10211450815102c0d80f0031405090503000034100b054040340d12690621401d2990308178517074400c400358416024103401000040c03c0f1a442d0074480c52a1480c0401e500240d2030001d008900522600c5851203050740325446807019044540c9055044e45004d031071002031203032452841c1c00180400111400380d0741c00801c0500400d00d070350f03100d006556580d0f001907220242c41c400c40400040b601a40c0340c208a50700411004917051000c207a55100194001600301a501d0084200214642 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162899784 1250 162898534 162898537
    0x7240f0503130f21020d140406030209040b1206091b0d03030f0906020a27060516060e060106120b0a06020c0f0102070314031e190f02100501090e01110903061f0b 71
    0x1d8004400d07000c1349041190029152600386008070040c480030480000100704090180c0e02102c070a4203000d6074072061500058000d01c03508011940c06040c03090008500b40c070000b1000d20440c03200049a0140c0100254140300034107039031406034800055004400041d12a40140000c0e070645070000c60402a10340e20042170760081301c52140010001e0158038101c0d802003485856103d880310200c000181040f40041261207220307010f12030b0422000000040040e1030317000840051040c02542d04950311940024248114108000103003414004807a80514204e640002201e0b610b40041003000c81e10014412510034460704241075005405000004c0f03801d20f000e80a500d0041030140d41e50741c0700e0400440c0e000060342c2c22294050700521104855250000162020511030300301011551030b460b00c12450056540011060ba500700000042c002580e03810000072704034030310028001c0c4074002c030141c074247c0503245c4041d9043c2e0041012039295a100c0310001101000c041034003050b07644400004003103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162901034 1250 162899784 162899813
    0x105090d111003050c03010e041703010801050601030506040b0a0501120605090a05010503010c0206160c150213060f11060402131b1d0d0305071401060807240f0503130f 74
    0x41c914622000e901c61400000c590680b0b003540c10b041001e03081c0b4184c0b00c101c5000500540b40c103a080103021a0520255010088090103c029415620342e104c29015000c1d04c41518202d002c20b05040128038580341501403104041c3c2d000c2c186500c0c02c0d10304001103408184a00780c012443ea0390700c1c0040b4554440114031440f401c1040b5000c0340d01d500d01400c0c5070849a2043c00b090464110800340130344e51421f41c80604c004105458021030038001d605220544490402c11080e8072840003807005800114160000c04440e03a035107a4013852a507040099a078001a050100c4482d005000002d00502d44032400c5c10803034190720400100360b0111404c000c00d89094280c1080070507a441c150352008044010f203850b00c2c00381644d801c02502410355010308075000f014802401c4070b440c4420221181d2007540b043d0000c1480f00200c2c9d510b1a41d480b44005024031151400c0c00c44a180300340168494068681c0f030205501a82c0ea491071540c8940d0841428182d8100803201d1400c40649000481c3c21120399801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162902284 1250 162901034 162901043
    0x70e150c160b070510020f0f040905040210230c030d060308120a091502031905010b0a23190302071703180c030c010c05210a0909060b09010c020105090d 67
    0x5a44485400658032210715501c0414031507010402200010408181803180a05510700541c4545448003c04c0380b038011107001ca111000c003c94000303458101c64010501560080e43c8003c44401035043c115040c0410708040090071f0070b08041c48841402c000001e104440740b41c01600e042032552058941a2403140e44242d90780800800c00642d0030702114038654208190b0902048282e1041d80c540e9000c0314624548105d4981c040b000038003c102190b0150050030740c8241c20006c5684840c0ca02c4010f0300704034815000949008002881441c40402600c011002004854145018090425400b140c0b03c012304007056020300010f03001480b80b9240c189041040102c86441740f07052040c00c0e094800000044085603c03100342e01300152404121084c0307090b0f0230701c0c0c6948000b04a0034007904d044985007100b08034281c090040c491002c4924003800071000d42341e07103250060780d48000880940c1c02500403588884800c0045003215802101510109403041c1800c1d82041c100000041109442000549 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162903534 1250 162902284 162902293
    0x10905210d09050a1502100203060f0405090d14070203060c09130203090d110a0b01090f060f2c07020c0105070606090f1401090c090308030606070b0c0a081005010503070e150c 77
    0x91610000740005051150701030b0702c51385210794001f56111144622a010302c0e500001142180d01e4418450380c0050b800b900c00d00090030300e8008641d0f81c4902005100000b10f0750b055003048200c1c0305048880e0303640c001700144200e45440b050b8006d1548079003103281e8030030003411002c80400030310300155100303200400140c03016550824005d0202c4c0502c1d400307621360750085241a400500c14103221410f60384408000a482030414030395400030a2513420001008000102c0000c4100880c09150020300301e807006440094084e03d6000213646040c1d0f410300140c1c02601044081e94485c502810605010320302c04115156180015000c4481800a086030305803030b0040c602c2d20007881d04000d4010f00100000700110b10800d4002010042e080c00300600b03555001011880030707a035000c10764101a41050484c40d0a0409000e01d52043d8084c0c40c442000c5030b0381c0e9000428084003072006404581040e1102c5140d5561103500305c40e61450540d145070f010030041c44695140020101034000c00c0041b80041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162904784 1250 162903534 162903539
    0x1050403080f010e271605130b09040f08091c031e09030201111203010605030108010c0201020711040213171506060301080703030f0c02090a05180c010905210d09 71
    0x805445004103460b12003009034004114902d103d608144d805081010b0119080d03444004840d507a2250030120ba581e48144a01105070915408824003251400c4410003960080c420010007030b00c444e000540e40c0f1622600c001008906005015400b00e84506140303443c0c24040c2000802c5204244492071010107210070003030405400144205280030402c81081031003003040e1008140c4c480b54000207040040d00414110041400c1043c4180410707034a255685968607118020140c1d0800d201c0e1b00020b601b0845689400c60040c070894610315080388024482c40d441d901800b010b540038100240350723002221000100307500c90300540c991090400025000ca0004502211181c0c075000e480c0302e2284008000411100f840001d940e01240d03410f0425500700140e020058400541e4030038065082214181000451912588100e01c144110000480110000e2252035650f981d1115200e0200f1082030b42401a4505014a0800d1030307c14944065a01301e07055446003804041c600c030102180e16500b00b03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162906034 1250 162904784 162904787
    0x1b010f0b03010e0c150c070e09010b1509030325050f1b04050f0a0905030c061e070f230705010f0603170a0203030103060b0d050f070303140403050604060c0c050d0201050403 76
    0x26a03407100554001051100c4110b0005001c00d11060740310224030a0004081001e08010700408004188c500280c282c41d10b844201c586c060251444441e104d255490040c0c0c1c1c61501030000e407881c2c070b08094015820301c01c2904e810f4070240c0c1449501c0000c1ca000c489042d00240c020414040300c80130103009031a40389504c0c000a0075061800c01300034416800c000402400840c2c6610740c40d8054690703400411161940d0400904500c034810080d0f500340550b50400403061203942252082a40e4170090841c15a207192044401c1e44101d00385400103124401d0355043c90b0741c00003100d2141480d0300040d0b8174082c000c1c0d40b96800c40300c1400034000e1251b1075034010820302503520798407808500e1510703c00d8a443c000c860025128401404001c010ba90344028495207602e611101c044000c3d031100840342e045515440c080d94484041c8021400180e010210240350880b0000350b90840e94050b0081160741c13a155120806040003c096804128072400c1000c00300e401040010080802c0307800001d064107103400c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162907284 1250 162906034 162906041
    0x12190e0d080705160f0b09210a0c0501020601060302121503070807170c040c120e0114010e15040b030304031e06090b01031406150d021203040602010f05011203050406051b010f0b0301 80
    0x4007081c05c1450220800c403070018030044171a00001143d070fa559501144c03201d0076043c41140d5400c2d40f288252003140007008583c5a0010598200341c085840703e81e0784500440c00d0344107482c2c000c1100e911542c0483c00300c006440c0003600e21b40c07000f000c0c1d441c15903c030b5075403614124565001e8507841c04111080c4c1c0403c8014401c00880303101c10396048c001000c0d548805414405003403103402a441d5078500c40c8c51540002c2d400461511640c1b1010003155039118a070a01d020001e9400c15007031001c034004485d072450309105081c4800c80290117541070a103540ca50191100105420781401401b500206000900900c24818481c0c8281103440081d410350409203c1800d0000c2492000c0d8484020311103440c0c0104911000580121240800c04801e4404903d80f4814030440c0215403001180205450b60103400c0040641d400b1181003010b83c3e44c62114881c0001110005804191304100034060f0354803920042c181041b8902c441403090400160050848085441c1b02e0980ba82c0ca074014a060701e420f01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162908534 1250 162907284 162907289
    0xc14030a051609180206070b04050705040207030c03030b0102060103110607030908030a02011e0b1e0616060c1106100603020a09030c0e07300b13020304060e12190e0d08070516 77
    0x1211180740910702c5c1c0c08100180318070200a440c081c149000a01004020004075000e050054030540d06d603031151402502c075050342cbc0011000300e030a0080900b0035500c0010307914100c035000304210540e0780302401485074580c01080281c0402403490004103010303e003040140480000d0f9400001c810909610300008205a0035a01506e5030400c1208010343c2d9403410403141040505da070b032096149d4490009031030b42c1b0403140344058001004c1a45001d020060740a4020035501ba1244400d100700b00034a180c454104543c4046c0c0c1d0a203025060141500c0380e03001d0144200780741080d17101c0c00d0302c0352a00c10100d03509501060445032420100090309a119814020359111040d5955034119a1b2085110078298040e190079000da846c16004910f40c0c64131120110524150801c41d501e04050814802a00010382d2030b09040c442c1a20b0305000e00f03c500c007125200f038003541c0703026403801000c40e08507a045003680c549a44030940c8144900441c05002c01000720b2480b48004059048000c41112050103865 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162909784 1250 162908534 162908561
    0xa09021e1f09060e060c0a15050702280c0e01171209031009060b0a090e0705060307050406110307170a090605040501020a020d26120a06030c14030a051609 68
    0x1c214801c556811503422000e9410900f0415012071401c0701050390380c05101c12518561040c00c1c041d405200244100c002c2d41501500d080c001030340c9a40c001e0b030b80c0d100a0301c0f01105588a07610b403600b69102c1d843c20070f80307120f2184114542190b80d51054410980080e040314220403100803040303004460801c8849039185025101030b05280d101350000c0d46459130f01060101164842034460104109a4801082c012006024680a540ba040607000070402d207140c0603500d110310900840c1d03914041007500c0c8124055510f035031409080000c12036034200040c0f9180c050b0b200502083d4006242450b001058a06a0181d2070b19040c1d509002408200c0b264040000d220042206210701c0e41d001c580101219010788001c1c4918525140008003660320700302036007a40c0491030020f042c00c03203010000c00880c000d1115012103601d4612181c404c1312043e00c130040062008580030091913500c917160b60707e52000101a6082e2a110380c8504d4104808005039000000344c5000502a140d000c0c400c50010030800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162911034 1250 162909784 162909829
    0x8150a0303080408032511010e0114040f06091a0906100303051b030d090507030203060c130303120209090103060b0a06050c0706050f07050a0c03020a1502070605030a09021e 76
    0x541d00c01504a660107400a81a4180080001c54540c00683d0b100c030300168019136095980e040c0300000305800040c8441d03001a500340582080d120300d050141480140d40e841042480d900c2c0c030360b85e5004c504405401100d40742d40718588800400c40c0300c0921001c0400e0f4069030905485c002880505085004200c820600480035048c804294058180c070104894082c0700301e10310100c1e1001510358019031a40e0550356003058071390300c2000800f143410402c0764030950071034505450b0081d00036107600960141c0d4040721720f05401000403d1040040c4402a80e030101d00502d418961400300d03140316826001500c1d1592a16801240e6080a2462000810042c50b0140c18003202418050b03c40000344522810400049508815825501d08840385254840d049840291192030420160380c5180f00984c400c015210000a60000c020b06e034942a01d010b45c003400c80641010720035200c0e0342000d07050b01c04c001e0360380c0080c000507110302e400c02c0d0403100114100800142c40381d040203041030000d0f0010b00c5259070f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162912284 1250 162911034 162911039
    0x60209090c0c0606061b0618070542070506010302030c010c0203030405040c050f0406020f120a080703050a0204050d030903060f0e06010e0901090b0f190203060303120a020c01050708150a 82
    0x70a40d00c0d040103048440306d6443d51440c2c401c01164800c0a02d212240c001c9200380801c2007440d01e41c00440c5001001513562580c2c7c0d400411100801d0110340b0003400384040ca45111041d1690b854480943c0c50214812102e818009030700451342110500310b0b0345500800c0140158901000980c1c858a000d1034801d403c1c0078541d0110340c69005900c02c16008a46400140c6410b600034004c3d202641d4590840c0f5031681e40c1c9081c020740c1d600341c80c0140100b074007400c03161002c84a6644200d4090303509503100d40c140c54890341001c070010100103100b40c40b465824403002c41c01c0d03543c12520254482c0255201d550040c1141404801c0381d8000ea10032030110314100c42c81000e03000c04200030341100c1a00804000c90b98440102c1809400c600c100240100440400c03c1841082d4000c01c1d4081c400c80c0e00025440043c0c800c0307060480c0301c10f68500c1ea01da4420b0100d00d2065a2602c040c55102c581c4d21009418115054030207070950701c05840a40103d149842041490700100c9041c1d440700c4408c842580307a892 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162913534 1250 162912284 162912307
    0x20c1c020405060402040801090b1e0f0f090f01060b0405042909041b0303031a0102010606050d090f050d020c3102070501020705061504063c030b0103060209090c 71
    0x84090900074065030b110400a011940d40d0307030607200106a000e000b8001c041c030f1803400050b40d80b011142d1019090440e040010030480419051780b04224040810301903454540c0c80c24084240181241a644140009501407020a0145c3d00081c0440c003640354a8505110400c000d58584e801042550b00c40c01d04d42c420b20000c520b09000b8100c5003558204641e4446e824034108072070b515240000a05049140001015803543c0301c01c0c001810701020400d0408800012800d882043c811071001600502607055a0340f141c0c0c1c0007008503845900a01c3c221803482c0d0301c42d406c1001c6a204140942c20000e85440d540c03d00206402190040980c107800201d0300103c0b103404600343d1000404896800328002e02000300c25030454003c3c4e5000350072240c9900e040c02e0000405100f11095902460801500040c881d0010030103415601801000130646001c0d00741c0c040c52440c0603c19121098034034000080460002600c65010f5802404050b0303071400c103c3c003441442e00024026900f40081004075107081c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162914784 1250 162913534 162913579
    0x60503060610111228020309011e120906020a090b0a05030103030c02041d10180309120f0c0b04230310050405010609020f091e010203030c210403030903020c 69
    0x3035025081100c007248500041e1494140c084041c5030082d5800158000c1142c19045c5480400e09403460007003480c002504100e0300da008031440300d030210307841c00d400e00350416004032940700c045081d251405141690030020400d0342c40b04c1d901651040d9000136580a0140e00110b8440034011161416141031900c242c0240284014840a0100452192a801155a07540240c104100044a0011051004000640c65a10404090441500e0301001200624410358035841d5140c068441c60141490900e5144090001220460742c1408140c100c0001500c00c54040e0003400d00060010f81b51410b0030310140000102c880030f40751214117441c0290340c40d500015100d04013600c400c004215600c1d80c2c64024090f186c1a0004003500d400410a0f40c1d001d0b80c258058400a4012160303041041d0101480c0b48140c4184c0f071a080c0140c00030000105624645001001e11504e54180e8071a58260804c90700314415065600303c0003c0c3d200d103860410715504000240000404560002d0796a10350300054100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162916034 1250 162914784 162914809
    0x103120305130206120f06091003031202091002060103050c06070b060f0a030503030901020702041103060a0b310306051602060106030c050408070e040507060203160f0f050d030606030605030606 85
    0x42503201c90004018491040051107402e42c041d09403901d907080c4850b041800c0303004681d180e440901d80000130326186403041090340030351403504850700100e01b9910111240030010141d2220f442e000c00c0044c1c81620b44c500307040c81c01c03120f5502a203007950540c60202e040070f038010003051103480b05100d4038002c40c15214441c5e4108504642d10114104504042201d0003010b5001410718080801001700c0d0007010340080811910883d010880303050a0580041c0380d01050b10541c0e00181c0100044c4212028140100780c003180142c2d0f02561000301800e01400004491140c0a00800310f10082003009000c0c087c507a04207107007821500815081080095461a05109403000c254031040c0c0c6181c014000c4c000c07500506400c1e82a111603648846e10302140007002d6800b01e6484c46642000201a480817054507007003d04020560f201c0342241c0c0702c40090803a00202960030034640d040c0c0704006401001a4a015001914040f81c594542030300641100c07201e91206000390402e50410440d41d8580c041c0340d60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162917284 1250 162916034 162916037
    0x509090105040b0d1b0f0609030803131505011202040f020a0e090a09080d0516170106080402040b040e01090209100605370c020423190b100809060609010312 69
    0x212041c8400c0000c102c8440040e000d082c0000c01c039030212a400d140d0146001b918004a079200d44556900401c9507a0350040c0b0019042a105001045021081c60f0403588080d00942c3c041142940ca10001400c5038000e070300442d84d11000591000460810340541c0900c2460241700b1800d285c44940d0190001d105004424400c82c41c120008034400c8640e40070100f106d400080f519240d84000008500900080c0e038500c00716098003040812891050a00380c0202240c0c05840b40c1c41c1c1d107827140c00c0c0c5000d0300260040b81c1c0692252560300c415212445801c101c1e42c0034000104559680d4018800c0395440035109640c00c42c0603000501c201c98210086030300e4076514010946000b400c040a0404d403003880c90034505c00c2c0760501039211041d60300054158070300e802182d0411031000c0440001c03044525070320040c0c0042d901100040c0c082142204203007001c0c1c5c0b105001240c1d00d80507400042c03000c844100e1400200b00304000340442c3d0a400c201e00c5501100c140e840700714a50468807200101c4001d140348a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162918534 1250 162917284 162917291
    0x5011205030703030c1430010f0603090203120f0306040b060307021b120a0308070809010c0e040905010908040f0e011d06090916030311060f04030509010c05010603020d0807050607050909010504 85
    0xd1041b480b5040301c0c011006280f18564988410340308564034004e242046030500c0c0c090901c4030b884200b061012074100c03004074200e901716901e004820750180007400c1041ea40b600508241c10700e00e0b800000185800c00d81c808809603685071041c20041101c1078401c1300d5004810a104000015800194a58006840200381c400510034680054940040b00f03c00c24030f030f030142500340e008041e00030a07810b00801441e1191800d907501c0d140128204d0301407214030000070302c1ca601c0d00070440c1003ea00080c03169010ba0000b05181e60740743c4850f0220f034000e60000e100400d00c031a04100380c200c40c44543e80540350031000080d022034843c06101c4014009004240701d440070b03d011075030b00340c020030003801e800c228943d002407200c2c1c1e00c1c20b01070000c0100040d42041400b4400020360805140e84207140b0550b89929502c0c1401003400c0110741c03034240b180048455642e915004030250b40c405d1502141c6503c41c100300365849001c0c2c03503d40e08201c00640300d44c05010050100d5601641c80700c3c3c0d100d041d1a810790700003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162919784 1250 162918534 162918551
    0xc02010630020a060203030403020d050702010f0c02010c14060a06050103060b0f281205070c150509031e04050a1a0d050703110a0908010e030c150703060f060e040501120503070303 79
    0x414540002002503003c0d40e1500002802030b0080b0140d48143d0007034081e20803450324900c050314140706960000b400100144210710045019805a017840ca0040c5010000d200300d5680303414400d95000d40c03291613944641d00300081074210b40264030180c0003c4c0380c140001031500304113621a004020020b415014082110382414103268030320f16900d28141c000d008041e42c00c644c05814480c0d10013a04081c1c609080c0054000c1d40103400f1400c0c101d40c80300702004010f00351001d600080c04080c0054000780005c020103280f40b401080340b02200c04403038645c07503070700c1d803030103042090441e850741c031112400d4a164050b455489000c026a0b420f040e40380790104441c1d5940b2811401031104007082d0845e0f69000c07440c4091107a010301c400f829107051030002c10044a01c0004141d9038061202c400c07a03d80c4c00a500c0030900c944d8000b8a03034002c800c90502081003610ba000300c0003d0060350300204005444264000e003a0305d0180102030040019090018580c14107460342c64980c419510007805242c3c070364074203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162921034 1250 162919784 162919859
    0x604090218010603020403020a05120607031122051306050306040f020d0803070305040218060303090609270901050106090311010e0f06030901021b060c0910270503010c020106 77
    0x81050707189909218620560b183e460103402500240000c0c2e009600c1c511000c1340c18142076106d21500c0261034010656540d80410850107001a10460b550b03c527400d0160342c4903841540c15550000110f80e1941a00c01d081a003403124009040b45083c05050502504000c951004201660841e4204950310604810350010541100d0b0510006140b241e00004100708070303030b26071300480c0030328401c80c1e800030340000b4001c1d2200808010340390154143c00c20410000c480c03030440010680c10601030604654482c0175140d1400c100c04a034661050810004200403500d070080c0300d400d02406450600b0111a070464031440c40403002420064180b02f45143c2c640400d81c4d40d140c000f41c0e442d00042080fa81c074500880c225010b500140d010502400c0316142142d480d200c045804c0d44a1800c041c112410400080c0c02c0003284840c0d0941c04052140b00f07682d4620030401c4c041154190b8009002d20b40125260006140c2180e2100441900b103916000d818003254009500c000c0038070681c04103086421030354100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162922284 1250 162921034 162921049
    0xa0f0513081006031103061005010e0a090606030b010f0801030c2601060b09120304180209120607030207031407121d03011a01022107171606090210030903050306040902 74
    0x840d0782a4400e05a505031030003069001007082c2c911888003610301540c0001856030707442064510040c80461001c040c011548205030b4062800002014001000d50f1440d0001c00c80d826600f02400094481134080801e580040052480d84040d290500480d89552240e400d0041d00d4052050444030f01030a040340c0c0c00c0010a10841440400c0082210a559042c001041c0d4041c1e420715010300403c1e0606241400c01005507070885040c2d12040541e400c00440403030007548044048c9510014096005990120400105124003401c0d01c00503641c003003038100035140b00700d40c403800101d002c3c00b040850001201000c010500d040c41c6e081680090180303204621001910001c041e801d9882e00184c0e074912000c1c2119849008000e03002c0c2c1d000d07011242c2070710380c2042d190a020b540c04401000b05d000043c190707001c54000c5c850014240d50030425211118400345207002415540d15440b10010000d507d40f0f050000c00e240114142001503070300c25030300648140030040009125a07a41d032411810b5449460 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162923534 1250 162922284 162922289
    0x70510030e2b0e0105040b0a020708031b0c040c0c1401230109060801150311010507080d050906060f1c05030909040c0e0709050a0e04020109081605150a0f0513 70
    0x5050300c448981d2001c0341500d00104030719500414680c05121516280108642c10543c84107070340700380c50070381001c104821682c80031200c44210312560300002002802803001d000b100c414425a080c003e06c01c800c04526200040c04203902c90362134844010038154001242ca00410780c06090988954031007561940103040100102c40f1620544010400c81c01d000c510280c140c502c410010031000d03884a55075401c803945e1440c8403901510940042c00461300954100080b200c0c145001840c0c4401030ba1000130507001001c4501440f6140c2d024041e06840c00d0000d594860401c0d01c0400070914101d000403003101040c81c00d0200000315040c420706004050045503690724020300448482d00302442c192102403468031680b1183c0d951400130580d42c03071107106100100da5009004c3c0300120f0814801d0740120001404c02c034184a149000040c1040e014819002d45100705454041c3c02803420052120840c01c1d0340c0b100410003403c011415611b42c203d034600419046a1078041d45a00000404000b8218030780c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162924784 1250 162923534 162923561
    0x50a020a08010c0215090601050910210308090d0503060f060f070308010e0708090607050f0c0109050610090b1302160f120f0807140901090b04031209050603040507051003 75
    0x10304001c110004150440d030582291a030840709401503445030a1049501034408031081d0708440c004000c40c3c60440c10041d00310508001448002c0d03500d1103a1004000c3d0340c000c41410340401018813041c990400d00340340c1e0003048800030f05040c0340c1d54a40200b083c840100001c0c465811003c1690154a602080e16880d141040b40a9540d0312281000307003a4160921602d61000b072b0700c2002400892140d80c01174000d024410007420291a4640143c41942002c03242da61150310601c160b030020103090040307100040c06000a4849802c1441d00c241001086401594002c5d00340042a00103442d5a028820092401200143c0b03903d001e82c0a0300c02c07030751034240c0a403281052071025020700c0000751086034040300395260980800302d03034482555001822500c1c58045184080e020715081e03141e000402103601c0525008104a880d00c4001303c483d01720b90410350311a440300715001c080f03e802c101004090001110b540e030451805503102a074900702e41c040d107405142501c0c1c420300142d01070380006a082d40031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162926034 1250 162924784 162924799
    0x30513030605040f0501270b0a1812080109200705010603020a141c0305070609030909020703080f1503060103060f0923060a0204120308041506082b0509040504050a02 73
    0x1400c044c1c032000314007041618154070340400000c00111180c2c038139203c050780000720501004580c94003042080020142d200c9261500b0150b1501208511801ea40500c00c604074400544510700041019030140c00261030300b403410302c000783c22500030b07800940094801c1001c03d076100d00b0b5241450241c400340c0c1c40290814004070340860030b90002c1c4e075100540c1406985100d0b200140480004008074490b41c0900800c0c001c10402020695a0300300d803000718082e05000802658401d142001c03030380301e00b000b41e00150b85035003481030705625100016080f002c100120100c801c80000000d8079104107100040000303a480300d0311121100740340c00c1031002a4001030815441880121450040d170b10726403051280b80100e0000801da0300492080d9826034070402e46070f80f44001d5075601a10440c2c405003007550100d5280300c5031045080d040c00344030060032030680503058408803010520088071011180303030007170b40c51030300154001d40e80310080d1030820404540201c0d183d261810b0181c201b440703c1c4030181d005041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162927284 1250 162926034 162926041
    0xd18030507060b0906132f0406140f120a060f0b0408010b0103140a09020310090c06091203050a031d0105071d191a1b0601090c0302090d030513030605 66
    0x4005015040240c01a1400e0045511200070802020400c490b11130303000a100480720011211b03544111012107044042d85c0c40d185807890302600c02200181540012030000605220280d8172568008500c009004480c3c14298040440e02403030150040120b10003041030005003c0c1c4a0700d03040b41c2c0081060304007000030152621044000c9034414020b41015600303098442000e544280f090052407102540c0b038142075191901042c0151400541c181e0f410b03c80c4418100c240c1055100c3c4104891040075000070701c0d031800d00040c100031081e51109031503403206003002010070b810408a0311142110701e000184c003440d040d2002c000500c01c250032001c640c41e00c8100148641c0006449642c02e40c1045401d840b041010200300c079440306448a000301e052001000c201142c41220541801d5840c40c0400d03040c5124403015164030444103000d03a0741a0b00c85801000f5400c03140c8240c0c941ea04581c6002c1d441d02c2c150700040b0388800081c0d9001400c05c000008c103158510b45000c1c0010185901000600a07800c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162928534 1250 162927284 162927287
    0x1140c0303071704110906010e150304170c07030f0c17062a040506090d121713051905030415020102030103050c01050405010f05030a140c1306090503030f0d1803 71
    0x10021079084003c00e0502c0310030b1100c00040c0110307030320072940b00c0701c006410798645041c0455030fa0003400180c180225030240100650341c480844e03801203000121962203140c0360402c640d8226008050a103071440030040d80c024854049021015a41c103d00848182038171458403180714940d5600003044c0d050710070440d03812100c3c0481c48074018500000090500380036007019091102c02ca83c0241c8180d03200700400c1005090120142c105120002c017010142815606e5460000101b0f001030742c00212440300400850b68249006d941200c0012080c0d0110f9400c1c1c1c0d602070361078003444540403101c01050f2164040000400c00c031000ba1a80140210709010320f040041e010b0340007030000701d6140c014403800b1903503075101e40f06031001c80d40d050b500e00c1600d000c00301003981d00b41d0001d000d080e80f050715000c06649811507409030900a400310b68180d540c44280c0d45142c8016040d5400000412070400010010b135600082640d006846c1f080c21265a215041c2e20740b401081c01480510744450b1f07205500c014103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162929784 1250 162928534 162928537
    0x60b0f061602030105061207060305090102071707030311090a0902160c060201060e06030102030f130503041e03031101050c04090b011101060e18030a09030f0501141906080304031101030b01140c03 86
    0x34820f400074130954843d5001c1140b00b10700c01040b203840d907100306003c1103110f01c29040160081440c1300018030b461001e03140d41d00c02e1111151502d410000001e026410103605102d170701c11015443d0b003414100384100e80060042d0240303100f40c06d851900496442c641d00c804c211440441a40b102c40d0f4058540d40d150040e0180249120303504451080c90001a041c0c24180210f070302c508030303008002216030345034800c20441c1940c9641c01e0781c0e24441407002081c051407592040341c0b41e01c4100d54842e041c520350300e801003001d500452043c80c181d04110034021140030440c01d07035050350b00300d00000c120512030307900485c0e00c2044403100003860340c01d10030005002003054440600540c81040ca581803810023540d0070f0755034865015103200149e800301302000400d285004100c2d10500c0b40c400030482d0380e80d0400c4050f601b5030a86d0714051410500c00c3c1c0b02070b41c1307400c1e10401d00103060356800f41d41814a1500c440c256501e0240c840c034141603c0e0311040c00e141c1e00c500d0f941d40682c82c8000b441503ca2404121040d074a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162931034 1250 162929784 162929827
    0xa0f030222051201090203070e04140a110406170705150c0709060501030e06042a0815010513090b060f030c12030a0906170420060d020c06150904060b0f06 68
    0x180f6018841e280d10034206000750705500343c01400424402d85080009861010010010343d4404c03007030082c04040f00002d03c03200c45c00900a00428075004802020082120390030390041781d41d094038441e45607420b000400e1480807250202d4525903008280c503500042c504c0b4154003803981c0c1c0205440401d060f181684034106650081e42d007041810603101009680e204155006807074002503400d008143c500e941c8005040c1200400e002c0e005540d0380805c2c40c54820707400101d0021031400c0300148101d0803e41c3c0400529083d40406104203500342d192035040f01c0000d005c00d40260324003241c0404944080000f80e002c082c01a20301002c503240084100d40b00d400c0070f55240f0015030641e03c001145440b54800010700c86020382400c42c1c0ea00c83ea640ca40566010a41c00c24494407402c0000a0542d02e0202428080349404009a50385400e040c00328209400104615080c880550381d04515444400c070300c582c4194030400c00203036150180c0c009106034560546041c0d0004002036500c00d05980c00060b00817 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162932284 1250 162931034 162931039
    0xd020d02070c0509040807080a0c0804120515010f1a070f051506040c08070c1a010f03030305160203030711100504060902031c140d3306080105060a0f03022205 70
    0x39030946880800926130415540039085100c02e026800200d5806001001d040d403080c1070207130003c0e8440c0ea4200990708168040751500c0c0b40c20400c40c040c00350a004000c0001212082c2c11015810880b03180d00554250041ea04548405e01011001d80a0302080b036940d217800c991155034a004c00d2408a680c0d410281e41c4e08501c0c5140000300310786042c14002c07516104550f403562803d60713031500011140c03c0300c640703406e85106440c0c080304440300c003601d8001c6001e040003017448241d103415410041d054a01c05040c40399041c0c040c62204005540c08802c3ea5080707615441c3c2180c0e00c0f050121940d140c21808c1c6080041d10740384c00103000c00c10603264008030b5014402e03415905060741c140400880411110407400104400102031042d20301c1c490014000030005480024156240d41009400401001c41001340c0100c2d03d0702c07804852400800a6000b09182d00d04140550f0508000c500790b0b0080807083d0050040002c4152481130003601581c55050b5060f1885030820f00c000480c0e044151076204403070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162933534 1250 162932284 162932303
    0x10c020708010204050a0302130f0e01020301080c01051e09060c01050c13081504030e12100b0108011a0403030302030a0608030a12060f030c0b0d020408060a050103120e0102210d020d0207 82
    0x41c04800c10b000740c80850f0002424004440d20795000d1180d109041016174101a0752840c4420500b0b5881c4101d4814086130800141c03030358100100d8501e003c5144907002d0501509010740520540011541c080c201170f9901002d0302c0700307201c001092543c020710341703c7e004550900c01009014001e4001401c15a0412a08604416030300c55041c0d80726100b400d5010300c012905c00005001c40c2c00740c1c0307001d001658090703c071500d00302001c0b040c0f504092180c14429200c179100c0107410995a8004209405080700044136424854143c03451006845984801800e00d500400015000f46960348408020196802602e503602103400300100340b50500c110f002052490624007150401008200c90305403940500391340301c01c1c1c0c100b440720805500400f034080b9080d0303002c00000c1621901804283d01541d048003001c5840e50440c50510317000a079201c0342100300306a80240d070007a030b07030300003070624003164640c202c501c2e0300b50300d604080c0f01c81c41002c040025240c00003c907100c03154104c0c0c0c0142001c0d80902d2040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162934784 1250 162933534 162933539
    0x8040905060910030b280f02090909070605040e071e020d020f160308070c15050714060c0906030403090302060301180e013c14010501110f1e030d0608010c0207 70
    0x2034085000f24000907051000368030000301c8032048000c400c100644031a0400361590040c1e280e0f14159041031400e0650145c000c2000e207142e00740201e80329044802180036100300b80c2018001080c40c0500d1103110b03213000c40d5001140146001300e20414601c040701c0014142d104c0140e001942d14442d0101020041c480c010406800100c003080515618100e9100300d85128030355181c0c2503064200c460242c4000c2407050b8005039000303c1c0e8600343d07002c1b19070b52261034480500d8180300d42f07090145c040341039198003c0000c1010007030000c422030380b9054049902c540c036500c803810115510703505908020b400c04d0000001140c10b18020b900c2d1554610745110038040c011031103580074280c507400d400d10381002c0c2c0400390a010320328181c0c1f00b6400341110f40100f0741c0c40048110011007903809000e0500c031011203820040c4203a590207040181c01c251008000d0541c1210500b84681e21008215100d0030b12000c3c060000c8000001c2c4100d41c102c640301c1b0f50500409481b182c105000f000d2828451000d4400d52000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162936034 1250 162934784 162934801
    0x90504111207060e1002030f13050310090b0601080a020c012901020a0c060f050c01110d0b0618060306130f0203060301061e03060c0306150e030601060c020a14030109080409050609 79
    0x4509442c81541c0d56128100e100d41401540b1445070a1171055000c180310702509550701e00007404015a0030031103001c030545018140742c10f0000d84c0c0c02e00a940c50a102049012a40b650919600000203203003c1c2e081c0e59480d601c4100902a151a08030702e9402c0041044905a0100070b49210b08020700070028480a00340040e6910f10101c00010310041d82e00d0390401800e0b0041c02800040200c9050262074803d0289406085582c24030752060920000310340341036040454400c3da40a00000d440d0b071450882410012181c000e104109075114510001c0020b0860321805035101405002c00400e1040b4958140100081e4104031891800707986000c02c002101965425165445c07a90301100304c1c0080c0c00c548a0602800c0d9880061301810707110b041c005411400c2c508000d000600c503681700445428500c0030141064010380c0480100038442d06080007596a82c51840704485240d01500040712940000c640904120075001d00b4548002c034000078001910740005104004c00c850165403a030745d1052 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162937284 1250 162936034 162936043
    0x90801060503070506090609030601080f01050705090d060f0b1305041104050f0a0e010605090106030c080105040b030706120b06041e090903051603020a1b090e01020a0c0206130905041112 82
    0x30142d040d8440c1104202e141013490082416810181540307180040e0300010a26100c020ba0102c1207503804034140d5004c515003031181ca50840000e2912511380b0561500090040041c66800381009036600340f01c80c17594200303a0050340c1e0640c014040490300a162451a070007400111030507100003200c0440c108161404c1d22402e80b04070b80d034828048494071500052001042008903002c01c030766035120049015901c030b81c2e440c2e000300f407196404100e8500c0c2160042c0a4141a484680558200410b2a265980c04180502590310524000540050100f0000050000107000300c3d00034100250208030785510001080103101c08481810030a82d448000c00c08480d070000014000560510034015030a8903202c0c040081e50003441148c100709020b440300d03240c80507290082c20702400710f98410800c40c40c45024284410f140c0340d00171818907101c2d00e400f40c10300d1280b6100a108070360010b50b03254121941c1e007030b07a0041c00c0c2980c000c00c06842c180c64808146601040f2803442084501c1481d482c1c0000003a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162938534 1250 162937284 162937289
    0x22b1b0602102c03040b1b0c090115030903031407050a08011a160f12030b041107150216060e03090a0b0c10050702150f040b0c0403170306012106050109080106 70
    0x3d1000403c4886524900b20141c3d001e0421003540410400024180f8210001c1e10051001c4140d801c0101c0d015040c4514141140c1c504234092100080104140300c000c2082c000c005445080c0400d813008180f0f0110000c101c0380f80d40c4002e00004000303018102d030b030000203445900ca00341c448186030390300d8802001020860f206548040c00d8104a94140c1561500c000400948264034002c640c040c01e07a0762481203001100720000080d40ea020001442c03400e80038100c80d080348211807504e088029202c0030b85214500000406868002403c480c00c0510310303405440b01a007010007044008248481e10f5141c0e0711004203e8480d600381903010501030012011941d10b00201401010803015040589014140080100b8113500881810710a10f00410680900c50b0300008550703501450603140c100d010410140103c07020110a000610000d068081d81e4207051184240c003d480e583c0307403001201c6c10501e41c20764031f145003101a0138004811a50b08103c0070b890098850404581c5c403541024202d44192 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162939784 1250 162938534 162938561
    0xe0f07080c0d0207110301020a11011a130b030c13020319060b0a0c020a1701020d18030807180f06050306010f030b0303040315020f0a02030406020c030a022b1b060210 73
    0x2080b51024032800c541c010104a0701c151048251310041c1340010782283c00c0f030b0002c100440e00406407e000c200c0284503c134204101c45860308844070030741e170109214508840351900c01ca40d446110310080c0d60f04020003001c90800a06403000070a9540801c0085e410139102031482c604059180440c0a000740240c000b03840c0100d000604010740701c20201c43c260401c09043c1d0f0803403001c6e00081361801030350383d9420391900b44400160381d50b90a05800b4040f660942c2c0c00301688007c40c00e40340c00081d0f000f008940c021907580b601c1041c0499014500c1c1851010750b10420700e00d00d51800015032540c001c00030354456039003601c4241e52110800d00907019252404001070703042e00300300302c02d2001a0717076851355051078000c0c5480141007003d030f104116032580c02031051b100581c0c0041020805d40ba410807800b00da0000540140c00708540d60b84c0401e4518001140307581207000b03517801c1285140418840b100305180c110b24221030340b81c820800c0140f100d005004a10040c050f040ca0421500481d005540400141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162941034 1250 162939784 162939787
    0x50c030703020904021012020f042919020c2101140906071404080d02030c06010614031603090209150a0509010b040e04020604030f050619051302010f17010e0f07080c 73
    0x21317982006103030961301c0b40354014000414113244074400d240c80980b4512030810f101d1580c2c0c500301300c03040429180c48120840c1085185009120404480080d03d120188180303040d04542100401a801c1900700440e041e0041c42155110b1503280b0500b00140f00103031900020020151807035520314000c10b08507181c0046510202c040750516200d0916450075201c4a525103003010384841e00325081211106840005a0002ca130502c0c104005000d02401006203040c080d41411082100c8407181c0001040e403031259002048604500d400f9070426040b081e4000d20b00703403640c503110800140341035400400368000ca030030680c04074081c00c0210300541615040e5131500c0c1403900d801400a0b02242c0100f040742c014000340310000c00a201945041000c0748500e01178541450089500004104560b90142240d81442c091000c0031040300c0d03940b40441e4080c030341200b202080450a5030420406010a00a240c5501c00003911500060300c084c01406000c0d14480c0c1519200001c4807118001e480800c4410700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162942284 1250 162941034 162941041
    0xa050402120c0a0201060806010b030f0105030a050a06090807020d150c05091807050c060907081023061903030804110103020909130609170714030c0717030f070f050c0307030209 78
    0x8200090b003c04241d0b44008503005403211030301ea0420800382d002c820b00e10b20200c24808654010b100c624050401540100b4692160341c0784c241d07990043d178101801c516980c444500c10b00001104860400c0e030040c2c02c046a0301403d2030401d01c0102c05e000300c6040c40d0b1400b10060685481a0202d5130451402002c16a2000e82050741e0850890060003841c01d201c0d04108000e1401c1003480814810048080034000c114071f080f003c0f609150003040300718076203032a002200002b14400229019041000320b8040401c0d034230031000c5240c0014000700070a042c10b985400008140d03000303083c0ca10a0340301d94049583c803181d6000550582c0109803030a507004001600280c8002100c0c07c81000ba10f00422000c59080310a844844941d00e400c5081855180c0000740c050601c40810329029688002d50021803806840303100355a1a40400e02035007031800b0924010002c927450170000d42c1c2d900110f210850f5551000c6203401c0c0d00c0c19400c0c4100b140d103409401107a40041c680130a200e011250050145052644c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162943534 1250 162942284 162942301
    0x7050906060d020c010608011d0111130306020c2b021204120b090322061814040c05040503070603020310120b0c0306061201030c0602010e01020f04171213050a05040212 74
    0x4028200c103513507070740da40ea02c001084d0109008000c29800703600a094803010f03140c00355500391001a02c0504000c18104152040800086128000c483d0024070050312180c0000e42c45080224010031074080e4800700450800d1108180d021414580307040c2c08a500d030300460300702c583c55030041d44110310b03001c1e001003001c0380403a004c9010143e0149104003034901d05050f50b4007041c0880207807003040981966040c0113014040d0444280c4601e01440c0d00c0400c02586400903090f0005440c40e0307814001c6894400c1104a18011810341e0083c02004050351062603c40000030000d402c1100d0309101091466400a007003c099840c40d807182d0382040101e031381aa5410080c5902d513102810702a0410340c100084603500030300d01c04550203140318048130020f80b4904000213017900c2003a0172800701c2e40d03c10445e14000f6010341c400c4504440e20402100d4018070102405030522101c3c68108482030000590003070241c801d4076128040d60b20031500d0009464031401488124002d4821480000c13180350007252545 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162944784 1250 162943534 162943537
    0x5060609090c071407090e01020c06070f180b090108130f0206070f060c02060415181103120a021015030218060a090207150515100c110d0f030207050906060d02 70
    0x2c4111a142483d0441d1550380b0483d1a1454042c20502c0c0c10081c4203024501c180d0207003d00240c040c034001e600b0000c1c0d034491543c50f000050011070511030400000116070f030280006100d104901034941c2009956228408020780c0201c41c480d0001d11100300144000000d2401c0d21400d54000000c8000124980d091042c80e902424050700c0e21001c01c0701d40d40000c0c891340500c644a0203103501501241c00e007468403100340d6070146c141d0070019041240f0008200303032004101041e1a0000c0300b50f9a4100d140300400d080c101102070041d55074800180390030f80c01e60000780204108040d440d0800004040e1400c1e40010341c00c40c04000d41c0100b071120161251540050182e4000100902010240e50307544042e10407a4007184044400d00280d203204101001d2920443d0f1788412160b07107902440e000b002c00140200b64464189040c01302d843c1340340c03040c440c054000202c62480074201030240403080c20444003040280101302c006101c0c10310301003003c1c24165941801900041e002d141802449070313200c0c1c003a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162946034 1250 162944784 162944791
    0x70308031b0a02010f0f02041508060d0f0507080d090b0901080702011b021501090903091a27031b010203030705091c0305091804050613021f05040f090506060909 71
    0xc06615002180c0c003001c0d00001007040c4400c2c3d400001c2c1122800c2c00c07070380035140b9503600e2080d440d106200800403071405d4100103030b046110346049500c6a69080c0000c819486170a009001c25020b580101c0800000040c100c06903052082140c12415100c10700310b400450900600140480a00c000709095008890302074229940c0d000102d40740740e903a200441420580d841140050340010b030b02000107002c81901602510301101c050040b0301460301c0c06040981281305103c88000d400903100d40c1c40701185c05a0340c50403a84402e6000103061304000180b58506860a140b09004095100ba00c1412603c5908070610068020b5030943e95400780c00d031010b81102d003050b078110290600e03401c1400035012010a06500c26110a6100c200c0d0300c0c1880b10080201c0c10040c0da82e200002840301054000502c03030352042d280d0180e038018002c81c1c800b0440840102480c040200c122102c00800c203034019010300240d8202c0c0d60b0030058980d513180d41c5820750388107a580c560001c204100310a55420a103400a60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162947284 1250 162946034 162946051
    0x90b011b111002010b010e1509100c060911150901020a08030a020f04080618070315320402120106050603010e1b0d0204050103051b090409021c14120a0207030803 71
    0x400c0400080410a01d100b980710020040c0d540300c030707880155038000d1050103c815060716514452840d19441000b54402c0d15140351040c545109141c49051154140c0c003201a07100c8804e01031030b12685050404090078480382403007002c4026140c0364610007501555052601603006202ea0303c0c1c03d4494200b260300103060300c44415004c0100d0648440204000c100174170311440104010314010f0030031889804011800c241e01d4200e02c07001c00100781c0030040510000c00d200c0c400504140c2d82e102041201261030106000e400d001d158022081074104104c5104d1030007980e400724114428a550b03402c079429070089591044007840180074044400d5038441c0c0c0f011075408071620149000b881c0e070318983c0164400000060300000c00380015685402103907008140a10600c598100200716490381e8041d04e608140116a19a00103040d551041c80c141e15907812000d840010340010b0501c100c1c04142c0e00d602e1a030611699400c142d4110740340741211440c100b981e0181621b14215901e4480300e030b0000d030030b40701d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162948534 1250 162947284 162947303
    0x405060103020c031812063d0b0d0b240706020408070308030a15051509030a060606030e010b0901080616170a0e1615050c0a08070807020307090b011b 66
    0x1059401c000511742a00c07610310094034561a0070400c89001000c001015881c0c01520a115000d000000034401d00404241c40e80d071711240a00791903454001d4504034084956824000007034612084000b01075480c0a010203000c00c980c1d03e010312035203001d03032a00c1400c81d0102c0400310043c030130003001030078009225200140c5000c3c0c0d43d9400c24a041b0940c3c105480380a000030506c05003402500c100c0c201c0b00030341c603038001000f0300e003c0014802050b840400d4041c18000200c01440e542d0502ca80c010701c5500c140204107050b00d80303100800420711407006d18019031178030090030540d01d402d0708194101e5903114001c00744c46c2e540e41c3c07450f165070303010075007c0c4103000d92a24030201c00d10107104203501c503071038440000501940044440f403612003c03015002030840da900e814001c8003c0700005607088682420042c0c2d444603042a03241c03821445503000f41070b880010074107400308064000280240e9000b00c0c200c038107140c0c503124884100d40d0100c0311140452103040324603204801c20903139403030454040c1d140403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162949640 1106 162948534 162948547
    0x6050f060d0207060e030309010f061206020c07030803012c040302120f0d15050a15050405090604110c010510060e0102061f080a030f0e010305090309040506010302 72
    0x19004080000d0300007440141501107070850b95010303400300a80c060180486859810981c1c111a041d4202000418000018040d40d01070b20030307030300510601000656502c0c00a42c061030f0a010f99020300340c0700002280c03091020758000d240b200300d4030300b04407150142c8090b07101303000f0025400101c2d078006000c0826400684000c0c1c0c0040c45002c140c0d55000c02040c149a0b0007050141d075242420000207180400100007080c04440d01a607152650503252090b0b00148041800c1c0d880011350309010811007407400310840e0303402420107840099000b10003000521310740e0203400201100d03034545090041414441d11680018252031074041001d020380d47c0000d45a0b00041c009024010a06801c3c0031019a0041440010501103080314492400ca1801408289581640700046041440d00e140c01c1d500a0040a1154085902039843c084450081000405010b04454101603017400303813 = true := by decide +kernel

theorem cover : BRFrame.Cov 162769784 162949640 := by
  have h0 := BRFrame.cov_init 162769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162769784 ≤ n) (h2 : n < 162949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
