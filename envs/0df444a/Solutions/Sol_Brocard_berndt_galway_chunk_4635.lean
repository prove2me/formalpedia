-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4635
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:15:17.297982+00:00
-- url     : https://prove2.me/submissions/85afb747-fe1e-49db-93f6-119e74c2198e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833453237 ≤ n < 833633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833454487 1250 833453237 833453251
    0x30605090303010e0a0c0801140a080a0c06030e0a050a031d0d12020f151b0708120a0f020304030e040f0e1e01050601020109030903030c240f060605090a121115070b 72
    0x3100000030541b0003482d03008140b1818000305a4209603000b142c88603c07500015102e244243e4400d201c1d1420201002d11f05e61090100080c5049007940c00040b01044400140b584200035102c03812654500721a154407000f40e4120826810002100c0d650310070301e010b516603224280c54500180c039101c019040007403009102c05503070010301d400b0341140740b0707a511f0359400829500500310141c85800ca001340c070300810304d004115440000c1c506100c442c1d00e20044d88034004205042c412440b40104a2060f8002910014007042d0500c00e21100d41c42c0940040d0744140f81d4000014011114084040c83d02c0300211110f49105246180100c038070a00380101c690008081c0028070000c01d1580c0c1c018a044583c0c40007130108a400607900040100d45c2040d000303c0c03800c48000c407007401c14201c40000100204080c45048130b2404d040026903d01401c2a0343c55000020700310b00b4091314100300781690f80301c0000e00700c509828201c07152142c0c0d91031040542004404001c195200c814a1070103801d8500007500e04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833455737 1250 833454487 833454491
    0x60e030d080c1b030c01090302062a04060f1806260103030e100507020a030308181209040c02030d02121603021c0e0114090d090905010f0302011107030605090303010e0a 74
    0x202ea01040b00080342c0d409809005808000c1c0040e00019055020380c4040e000340e0b50900e0320360010b069001603490b018020741110100c00d103480070040100341000341c170b0341c80003590107120030400f05005490b4a0881141820818050160003004071099081c07900700801156804801ca07514200c2c1118040341003505281d1290f49504545010340300c5400a1403091280c020322941014542c030640a9650304c903030280c1403400040e1245400707400b4420484070642000b02c3c521800b4034030140082d00b6081e061000401a10708142d90050001030616907503c003040d80f10810060036a070101d44000c1900c01d05404d42040a41401d010b245c00c20b6130301c4400b1305c00701070042c0100150020604240b0034800c07601c03540005e03140d82000071213016210702c500180688140d541000381d080d03004928560307450030540d110080c1503103486003a400c0780d40c280142c11440f400d503503089c801075008201403c0d048514000700e1340b000d541c0e039444100307654045504800c1a040030004125003011622407640260202e542 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833456987 1250 833455737 833455741
    0xe160609030b0c0306150309010614030c010801050f042901020111040608060906130c020d2006060409080909010f06090902120f190212040b070206040305031501020313060e030d08 79
    0x540d802d0103030041c00020050000102190043d42c40c10605880400040141502ca2400e0081d0740d008141500c105400d0326460b9082c0b0074103160110f100181124141c4a20141e43d08010600c8034980c2444000e580140c0e544000381d0380300707034800c4029803d229446543c0384c1c01c00001000a0a4402200140c241c21100744028400e042c1c00100b2668006010348000300d450b524000000c1d01003051b0302040240d240342c40803c0e0381241d408101511001c070561215401c440c09280d900b05e900c00c0c01d00312a07006402907008502646080e030408910103000b03100d001d0800188000040d02d00300282e000440180450703900300302098100c0c441c00020400401c1c118101103100c0040f80002d64000c2004071801400800940c1352094507411192800300c1000464840c1030080751580044003d0700c0540b0745080c808002030000b0710000f6010310550345a0740b0241182c03500b0600d044010503030358103035043d8001401640c2c10096480c601c60002c200030758441c102c0200e08824035082442c0380c0c0d00b1074108030714401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833458237 1250 833456987 833456993
    0x1230115021c0c030507020402030112260a0c1a0c040f0905010e01030305070c09022a010c0f0f03060506070309090507110c12070504061202090901020a0e150d0e16060903 75
    0x80c10340440b60260900005000301490200d40070310864100960192003c000803c40025884030364600600c01c0c4025440c50a800d90a0300c4810300c0c03503002c401122010002038491a2180c1b03003000400c0c0c454103030030070400c2100f0340c03800504400b01c81290321a24041000c02800c9160707400e440c024001507000700901d50514240c41c0e5580c40500018060000014018040210100320710740208081d08045440c1d060102403070302e4003070341d045182080c8403504101e4482504103100c0c4000ca80e00c280c840c0074007504100c1081c4d071048487c10100d014196603100000b43e40d1260710061610a10130359030f0351400c90402100f0011240040c00244c10000c1d03403d42c0810414001904901c2076504403400c0440010700340100c2d00d03090158008603001400c0041c00038146200200a001e41803007141c00031030580d5840c90250803401600445800a600007910b4485800c00125000c014025003018501c1d1445c0203e014040c0e601d80540c08160303502103a802c03040105d461503844080c110074602b200500349151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833459487 1250 833458237 833458273
    0xb070c020f01050c030714100c030204080606011404030804030b0a0c0c02030a0318050406090c02010b01020d1202031302090f060f010c08190c0515040501060b2503020123011502 78
    0x8041d03281031200005001e419100700300141c59a299201d04002030f110342c14110a41c4a0281d00742c0c404101d418141a198468041c0c000d035030580d0070880c001c002c59500c0c10b0044070108280c0060079103800e0f0400011001c41d081d45d000304061800380c000480c00d070500b810001d00b2a500d0b8495102003100e124040300051340c001c038407021b40c1a05490001d07010141d0f01d02402807001c260340520340c85071405a000920070240e03002100b500d001334001f080410000001a80c40701c0d92140b80304001124081903507504070b08e5901558200d0030032458186a524180c1c0410303a11141030341d6900148203d43c04101c094030b460542d07203010b18001c0c40d03d40c00c4040c40780d81e00090750241070600343e41c0304100b2a0182c15103105282000d90a034029080b204151400f5594000800c0265426182542004008a10f800c1c3c180112104d208260041e26400c0954111504414078000c038200c0c01c65407118031b00701c81000054000754852341061a58081d9515055040001d410b00d0341f02401503411001d0741803900f840d01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 833460737 1250 833459487 833459509
    0x20609040902060c0106060c020405090303060d030f18090f0b3f12040f0803040311060a02070519170f34090b03010b0a03051209041d01090b070c02 65
    0x303031004120a215032000a8160092050b840840e618082c030020b0403640c02a107a07a00715000380c0c0c080050352100e041c069203c0c40102c2c0c0103038200540e02e070b18600107441504041400f032800d1600c006804d040e5640d881e004e4501c0d0780502c0d07000b900c40523030840b01c0c0110311800300301c2c0c041181d9901f18075000c40301640f52441c5455100301102e042c0c6207a1001c0d90080c45007004003041881c1a1486081d5031124180550018021136884035841140410050000000c03102640d030020800e40c6070418a8040003e01d030f210b0b9401d00114081d8600000e465102c0001c9900540d080b9548200c11a04100135110308080e41c00c00900190b000d040c242c0b102400119940ca08031000c0c1304100c07500301ea9400b080302d000c0040c4013444001c0c000c4403000144035070144d0080a0482d0210001d0096400f50b108010041c5002c0c040070f403150304481110100e90202e90002c0c003c5100c05400403800424001c0e1484850038800c00e0b01129944600e03040c8100040391580b05c1c1e01c000d440c10901a03804981d00072a0402c030310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 833461987 1250 833460737 833460739
    0x14010305120f12010e040c120f060f3801030b060403110117070804020406082b030b1c0605011d0c03060d1217072a02040e03040b090a050d020609 64
    0x5010881e01e8003040032502079080c44000c3c0c5940d5659080700940700c903000c443c2554046500c0344003141100c16600314100c12500710a4180d03c0804584070369000748441615a900b60b961904101040091140c40c140f00d05c180303c80300501070703405501c078400602c005220641014903121100c10744d039032070320140c405580c3c00c960b0342289918070380e0050b00d80c4407016001007031003030074842049601d40d4007500492141e0320030340e01440100d648400d05641ca60381410706880040b00c11000081020b10041c158083e01d04500d07020446070041c00110308008944103580072810000301980c02404941d000d03850040c00c850200c0c1c21004440410380d08882406040700d0a9990000042909503a50918421a040d04024041d8500341560006442d0181802a40710300881c4040069442805501030006c0c07880b2010013010703409244901356440d02460601282d00542e50801144070270310820241024012400d10750355030f00044003c101c5070381c40e40c0d440f0300c0c49500710843d04001070f01c0c1c000a554610030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 833463237 1250 833461987 833462023
    0x1a03121309150b0f0301210f0605091c030905011407020304090b030a080309100c1b0308180604050f0723040515030f0d26010e1905010b0306030114010305 68
    0xa00510216078003254400403c1e4080030981c00344c1507002c1030085049400940d401000c244280041150840a0100140011b00c144032201c000c9005a00800d03444000003060301c1488400a140c10b806104101030310001a0781d4175600e03410010309208a03c51170f512592801e00300d01c0c003103400039900c0c4214081e1055098a5119001c2a9141086414600c40d840740c600e0740c0b0382c075000c1e000360340d40c01003454082d02c40c41c24080302070200c034021440c5010007903040024004141e01e0351400d48030440003500d0116030040281c82101c10b21000e00203035000320b00c21006001c10b86840c0d0031151070000701da040148410000320020000600d2030aa060544d40169008034865407403c903611014042046101c1d0180a0111542e50180340070582c206100800d0311482a0000e1036003501d21200c01000b2404070710801440140009021081c0c0c0c6c42d845480f140e406440000034188800c141e480070b0f070100007206030203c01d00c15280b4080c010301100105120380d04101b907242d41c0b80d20381d032400c030229600003083c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 833464487 1250 833463237 833463251
    0xe0606031311030709090b060108040206160c0b070c03021e030627120a030f14040f081b01050105090c03040c140a1d150319021e041a03121309 63
    0xb01c9400303400300d00c400202078825003030340e444c882000340151550484043c200b40380007900641c01020401c1c01150003a01003410101d010082a400c0800d6440c241c031001000e42c80040c1c070303031590001004880d100340d4146a80034a103105120f03242e02c54040c2440454071810031075040740c41c0050300d01d40c04151400143e413200c88403190400e1001110040304100e0240001d18002c035100c013030051891035025039080100d44c002c0380c40b03101110715490b0341c92422460b02001c00d000c1904007074611101d601925442e450900e52801082c0c011030002841401c59440e8801045985004110654080c4404030b00c28518038282e0748140e0480614000e140103882191645e40c00c0d601c07455018000b80142212210244121010400b04d11104440241d05071039021307001141818041001850019040144000300005600708003082124443d880919031181960410564580c083c40700400c80359010080da01c1e00c02014182402086451109018010446907480c0190040b4030790848000200c005200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 833465737 1250 833464487 833464493
    0x50a03240b1906020705150d20030a060302150f0306150d1112060102010204030308010e2a37080c040305030a2d0804060f06030b130302070e06060313 66
    0x38590300e000180c0004101c4000345200c0c0010620105980058080780c00842e03882c1e00b00203c0403030403d404007044405019480e13004040c2c0d040300c0d45089e0608004001404c003c241203150707070000c988100003d03898207070070420350030080c5505030364a0914640c00c0c504804c03082c00262a00c005860140560003917055002d09101e01010b485048496020501800d82c0740f0010400940142c03042810340f20145000c184190700500c00c481c100e075815100d01820340e00c3d260110010080041103042403021141c1d01b013248048110005c03254001050040e41c448824002440c45454a42070300185000000c500990904900c44a22000c10359890112003c5d960000004514090383d80014010322010541c400d0300c03071700003c0380e102842020b4004e000b0903034182018112000040e00e039101080082c0d0100740400c0c1a0341052081c00011080828000d40d80d80c1c880c140700317104070f4103c14010180d510071400c241d414800740c1d0040000840400c2e881c02c3c0640040e0541c07101400080403488602110010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 833466987 1250 833465737 833465741
    0x40b04061b020c01110d171909080406020c0a0302060409180803011205120f0412081c0203180a02100e0d0f080703031b0210020a0c0609060b0a050a0324 67
    0x18a0241901d24079081c0011200650748145070a0701c2404034081d200100860b0750001080701001296503074210405070054240300c009000034040c11403800203025203216818403030044d200b6461085807050b0b42d5030b00e00300f00241801c0380d0b0039440c1e1040c118500c042015a070781005950580c4c10b01c140000360010401c0c0b42080903000c00d8002820280f01100026201821003507100041d4010000da981c10303100014603200340d220702008455a2403051206004984040442c070008a21502c80d42d8500f42c0100c843c04c4055040203a030307000c1783da000001c1008048011004603030f4549101c004002d4410f07940c1c00189001c1060424804006455030044080c2c0d03612900480e070150400300305002100142444021076010302c006801003070900411802541d6403184040d4a0005035002e8070340d4002032810384010f5440045000201b101e4000002c0125247d03104100b035941c0300c1d1800080800b1214284918a43c440e80524810350002e85c003000421a0703042d0703006548402c0c03c600302c182d00502c0e440d640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 833468237 1250 833466987 833467001
    0x10c0b01080a0b2a031e0916120507150e1e030c040902011409010e100201090b0f040308181002041806120305180301020d02040305060a0e120403030804150c0f1103030103030503040b0406 82
    0x4596114102409031815002c145041b203c0201e41c01300c0c040300d8940127003c10348150f10764000d185900a2000f0800c040d04140c030000440d006180c040740031700c3e080b40010f0702e448225005201e0f050701c1c0c584080c41440c1c100084001c2c020142c030144481000ca40018004061110040040141c0060500126842940c41400c1103078000d05070115915081002030082c041014220746c070900400201d40300105102d4400d10541d490703514080b0076540c170514403200d011a120031100a100303464124801405a00181024020492101200c0040d004c0f44109071100341d8084000322081c2a0700c440031950140031200795280c81b81c2c040040024100101c0c2c02841745e50300d50001e282c0301007808010000040b5005000e1090600140201a445441580c8034548c8100b11400c10078200303c10000207018a07249036006000340c0c03c200b008400500b07118150744c18102980001a021401306400580040304a80c2c0d003041d01c0c0043d401e660460780c014010344009030001e084549010300180402a00ea00524 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 833469487 1250 833468237 833468281
    0xb0904110c03040801060e0114060d09060e1f02040303020d050c0f0703080304060e06010b041e09050106020d08091513050c040c0e0301060e090d0806010c0b01080a0b2a03 75
    0x6640e07041c4000166100d40250040300095400c01d41c2c0000c1113103c0981c0e85058401c00c07000000000802030400995070b00c1002a14115503d885248002c0f81c90780c859003810343c00040142c0195501440ca074882200262401001d2905c1400103001003503002511502080301400d20316075480015100345d01d4400100103503205403041e55400b0041110407005140a144206418800303008171031b0010740ca440d024001d8110341007041c007081008015002c407440c5144c10f600000c00d0800d0b210207100041d10300981010016900c0740446103a070303035840b00300c090384940078a02030414404000d55003000c2040203001d800c101d010410300403041c02030034407402c90b401d94024010000700d01c90601c040d101204c2d00c00c00078403a500c0c001e0700203071000e032a4001500c1070182001500b40f0100c0c03040309951124001c0c100c10704100c69082032600007508001aa8041c001500082925041c5442d2521460800502000c05288070000806180c10042d911220000c11086065120b43e0703045d01d2008981c00c81a0aa = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 833470737 1250 833469487 833469521
    0x180b0915090706032702190b0301031208070908070b030601051c0515040e0601030b040f0804060509100c030c0605090c10170f041e020f0603040302031306020d02070b0904 75
    0xc0300060760001101000c441c410744052004400107100c101d9802e14280b0307915000d1a0309985180140341061900000050141c010341039203848648140c0031b40c109070411140307000d045090460f0a60009442c941c400d031145004070005041c502c0243d20307580c4902ca910f514040103c045400c580c0143c0035620010f40080e80f07040000882442c00e400b601c001d03540d804584140c1c001c141d40c54241801100c1e056200340c402804a079103180e40b40c00b0b000f00010410340301c0819890014000604000042c0000c01e85580c0c0e032034849039507104100f50582d0704e04140c014440826980c0b400260820481000a9003041d4005196560f50301d01070b00304184800b485600c04290031618400b0364105402600d0740c10400205605641e5959500310b0005040e10b02030511140465141100c40d104041034110b2480900f05c0712a00c1c4aa00100361150001e031411000760304082a60403100300d51000c0c00005088903c010050303c0480701c000f0303484034498007640040c41c41c0040e15a145840e150000b440030300e0380381d500f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 833471987 1250 833470737 833470741
    0x3090907030c080601022a030307021804031215051e03070b0d060f05030a2a0e181c0e010c0203060f09061f3b07020c04180b0915 57
    0x300201480800540403d1a41020411651001a03101c0d500a00309003100501c80b188843d80b4440c0c005801a5a8035100801081c4010b071210000200310b0883c0410202941c1414078005d010009071500c21180e0a203032119145441e040380c0040301c2211410354941691075603005944418981014006070981300e2503400103108000c590003032204500041c1c00b00042c0c1c0d2200704590110a00d84125581903201c0c00c100d4000c00e071248003140003005080d41804a40507013884054010149600c46e0041c02d00b50790400c10201c4030b101c41441d10015000c060304540304483d200c0c6982034031480704101005010000080300f0b0340116801d03020241c0040031a4518035040103100180d01d030441d0111a03d0040d01c0c08070b0f0898941c003010301146504140c48004c2e86041c20740300d04600703050307105030701c00c4007500b0003c02191488104035208069121076420028a017160001c1d01d44482d542d000c0d40a0b40c1750003400c0d010b07201c03c6101401404d9000c10b00e4400c2d43c58089001d4901521401c862014086802c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 833473237 1250 833471987 833472001
    0x1d010e030a0509130501080d121406151b2103070f0315080f060601020c12060a0f060509090c090c1c09030509030303070305010e01050f2223091612060e030909 70
    0x428903548e103000da549441c8031480d502c0400640d810b05503c90229107801000c5001894108044030030154418049414601c9041807951702e03102841d00d0742040e030040c0c1d02e40d1000b030000451710311601081007596861800e121000803c02800b443d80c0d001011b503a00180300400b07030358501030030003071481f0b5048034016001c00c070180307844190030346c2c50074050b1044001c9000c1505040341408070700c00544001d08103503903624800704080c0500055492210f583c448012920760780703240555001e415044001e01d0f0001010080c0881408042c01c003000c0140c0a0126000f42d4820801e43c0c0c4254a00310340c082200001d43c07a0648041c040d501c0710b6a49800044200100c00d641903100d5412210900354443e210799039502409045010341002d030350454074148050380c2d56140a404040280d491810004201034000721802071140b090130061054000441403020900c3e04004d00714100c2c010b80035143c001385c035140040c86910b10000d0010701050300c41743c03182c025140500555900d010042c10003907103850555 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 833474487 1250 833473237 833473243
    0x405070203160b06180c040b0f1612030509030921010f090b0412050403080f090d080f0a09170a02120c0a320a09150504020a031d010e030a050913050108 67
    0x240d0641c0228150f017200418100900c0c1414090201c5408140c60306040845407003075030344144107800003614208510300030b404100d010100b903103014003103038003002110302c00c0181500c10180000c00203910030303c8603142c0c1d940e580103810000c0c0e902c04024a91400c0528905014010145000346000d140c04d81000c1440b1f01850554400c6104143d0f502c0400b08000c0700b600c82d4065402302802e091410700081000303000c00740042808180092610b2014034040d9907200e1190300c0708008030795481002c00c0c003103030b0b035500048110003500e20400c0c0075020282014030180d48011503a00640700340c4000001002d1150184800d888101000e81102d84054070f9020101079660929802d50100307001c0c050f00401c0d0b511481ca888481e8000810610003140b501c00098040e14080400503030505994900150b07d9689100818203510300751004645101a1030255540140c02100020b0507414050035140014000c0100c6103404c60b2400d00545450303c0c40007240210ba1003080c4042c910b0728000011607816800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 833475737 1250 833474487 833474491
    0x1060302030706170601050903010e0703080c1e0a03260907180203040c1403031c090318030305040306051008010906200c0a020603041103030703090e010b12060405070203160b 77
    0x1e508480e8501d03a80c0301c0032603403403d03040b0048440c24002c9004c1816580324400810b98010014004103c403895001c0ca14108100b560049962080000c1c5801031a00240a801c0c0034184070030300008003c1c60b01015075220201d40d40000d01300301000301100540c0000c110100515610109030381c00601e080101181e4501d60b600035454046802d1079130714030146043c0201c034400c55124407070b02046c9240081e09900c10b0407466038554107020500c403221801040e10340203101454241c0d00403450342007509016041549890f0000c007619241d40382031010a4100d004c560850b0340c0150001010340d42d8144920040c079441d081454954244050740c4d0a210458004803c0448025212103c2003c40342500da9244906082c0c0172850300820500005442d09101443c0d1150050800c1043c1c04524000203040d0390001100706d0201d0b02d00f40e8184550912159841c1c00761214051042c942450800203003446540100400c0c411751b115000910118420b100b44d44843c1c29001c20b420380a103013480c04024403142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 833476987 1250 833475737 833475739
    0xb16021c1a0f011410030f0c0806090606120c0304020d0c03051c050301050102070608090a0206040e0f060117060d0c030b16080606090d0213020f1b01050709080d0e0a1701060302 78
    0xc40c0010503602c0504400e01412102a40c41c2805141007250512010340c20b8040c841050568815001d015070385c1a004003060058159030300c40300d52400d0820016241d0010342514018141072018101d01e4030010745075900f00040a102d191265544c3c40000c107151105c94000340360800b0b088000080040004410712611099803040d01d0800341d403401150903000c00d11030a8011317030000004001081c0a00c16170b9802044540c03c1c1c41e0481495004520280e0113944600307002c0000300c04014103100845401c1d0b42080091a00c080d1894949013801034801d400350485110f8000b00009004008065025500031540180307603040a1800e00282c000f0150300d12200ca012070120380c00140607140940441d00c100340d0040a4003d40122502881701c1c1f60004810b80101d60703420021100c0d03c80d0600f0142006d0609507039051510b0a0300c590075425164064028024003900550038848041c0100c0d0445202d02c280c0b514041240002c0000b1b05601440da01c1480224801560010343c41010340249003902c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 833478237 1250 833476987 833477033
    0x109030f0210050f01060c0501020d020714120301030f2009090304080c0f060f0f2b06061701030602090114070b22030516060605131509060b16021c 65
    0x414040740e4801e80380110707000c1c44c0b15202d0000502040380141080c91501d800380c0c00050810380304d640c20340101d0b44500019140102c6800c04454041c07010000035a01c0308106100c14210752440c0d540c0e0442e43c800030001009440105010301d150340b00750003d5111100024003441131400c00001481e280e51007805070124500402c07149240b01c0c00c04c21000c0d03d9001c0b014004910f480c201c0c3c0400300c0d40d9041b259004204000c10086404a03040c4044806075513280504007460b4206002c09030310031202182e10007414032001c0705a035845a10700036450b50469800c000050303554100000120b03940e510003000b540040030080307034840a00c105481d445100d0118a42c00c5840d40b5510f00701c6040d08040000002c000500801c44241d500310344070b0500021310305c40c032030100e40320740c0301c20005400300302070000c0309900c503510341801141858065880006240d640820014035052014610943c1300d09001d09120030749104012045440700f0400b100c0ea0680d031403941700c1d402407a182007a441d00c074410040140131 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 833479487 1250 833478237 833478253
    0x7081b01060f03111306030210020106090f2a0201021b0729031609050d0302012a090b070f02090f09011401050a060e011106010f061d010207030807080c0109030f02 72
    0x451400b01142c243d0f90840d1124a000516204214842c105414081145601c6020010060715800069901c0d5815500082009030600f00c1070411501105118503402d420141105041c0070000d0603180c44100151030503c1c805490003090703000e8452b81848200440701c4c1c0c40403012072030003c948034003a030700308068480000700c0c040300508410040d0a00d5903c3c0d10b004102151000414003900313010000710781031042c001e03903072040060b40d00f5882041c2500580d44410051014107039602112172002c204203091a61228103a0700144910058050441d1410b0000b0b8810140110074907030a816a9000b81310118910340b01740180e8200c07000b035629400640c205006107405006070070b03025040e500d026066022a52a0601c100e07201080b0300c041c035050050a1080305441c441c14801d0501a21100f5500c1081c0c034500390f0003c0c01e00d0404480451185608680342202c0c0e81d000c03c005088903000135109495404a0a10324007501c584a007010066280c40c03030310000c01d0303004420300d00210742a07000d5442c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 833480737 1250 833479487 833479499
    0x1214090a050613030509092806291902010902030f0a0b010b071e03030209181503010e1e0708030406020d080901050f06010503151203040509180d0c060207081b0106 72
    0x2031121103d009012920074000d80341a0b04000c0882e0b544030418807201415040b020ba04296031941d200499840c0c152548410321101c005003c05044004c04402e10364111001c0341c0d0482140d000d603000f1150820000e507640013165100750013808199400800741c808503090711605684c1c0d4211520100d0345903110800000d840e1031240c041d00d01d1035401821103d590782d0041750112200203101c4044047c1542405001c0e01520740d11130b4101400b40c0c880070200c00d81001e1400c2c500031b1200d04151440b0743c1c145402a18042c03c01300f00c850000c1640c09004549890b403204503414006950019640c2e0711003c01d0004905500184170140e400042c1c0f03034008591220102d19003039820456858404500d200c0110300d45d0351007000259804103498188040c01e1406100141820a40c40380075100e42d4004a42403103545800c100c190380100740b988206003004100c0003042c0d102d046500007002801901000c0c0c05c2402800c3d01240d00c000d43c0f0000c1c40303603140c40c0c10140403940c40740c40c0744a004540c6000004550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 833481987 1250 833480737 833480761
    0x406020c0d03092709050d0305130c17030c030706020405011e0c0b18010c020a1e030903030c0f0b011e0b0a170903210f0f1302011214090a0506 63
    0x121542541e02c4682d41c81c10850840c104044c118908480358049401000d0740d81c6482c0700303004016100d030000c0d21062400303400c000e0aa40000d4442c51404000125000c00600745010031001c5500c0c1d1050012307503901d8403601e00c1c15402001030000361400001152800c10006074000c00c2511800d0322255054000b2926a40401000307466120202c0c0e09250b0500c00b00714000301050303002600c040589a0308510040c400e00b03540200301c041003d43d00684500d410400d940301007410302d03075645a41d42075480e55900c009140143c03d200280503c12541800070501038105004244550000c4a10b03401c1d50755a0b00303a40116101a20449802110507804120502d114085035041902c3c0c0da5017114210381c02613a5001c07850084c140070921b01c0100440368060080f909009450381e140e0a2400c0585095650900d1081c00248200c1a103400c0d10208a0300014100c0f18070b40940c1c082c601f0320383c00b602064001c4028001e944406207011074150411149040000d5001c4806106034181c95403a00c9030705050507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 833483237 1250 833481987 833482009
    0x3110a0804030e0a151115090304030b1801020313050f1c0e0f03010c020706080f1306020a021603210809100e070f0902040f050609180901110409020406020c 69
    0x90800e201080c0807030302c610000307401c44800a142c200e01c540d88546000401807a201c040011440002d08400a5401030280101c8110140e0482515181000007142c691041d0b0100400e26480784021511500c3c900c0540c000b0104120003c564904125182c1d4110860301c550895140c03040d50801c6c9011600800d80082d000c100c800c03c1d20201e0042e540c02d980c80e140440b150303504104e42d18030b00c81e1542c1e82401640c1800c1000c0e009045041e040c00c3c00100034070f100610b88a01c1780ea03030f2414801314126521031071050640101c0300503120081d04404a08008600e000210b5403003280c080402801100c0900500f0f2950300078124100e481c0c8404181c400c0e000895001c0656040301c407103000000c2c401d03080440c1480307a84058a00c00d50700c55028500c602c4e1250020302d0829800710b818081660311280391070103028100c50b03480c10300006d0350000f502c1ea04820040820450207034041044580709401c60488104201181c1c2e031a00d031640c82050080d0014402d4600520a0740030b510310394180540810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 833484487 1250 833483237 833483257
    0x307050103051518010906062303071403040b090f010b1804050a080412030207050a03051009080f0d05041104110a050a0e0d0311071401051c06030f0b04030311 70
    0x40018a850019001414000d10302d40541c0340007880841590303035540107201c8103038100d0388104440d41410055800c58105820102c1801001030680c0c52812070b550307100780d075040d007850710031341d00d0f42d5030a0101c0d0b18854101d81e5024440c008020301081080c2800c13282c1c0301d48040030440d03142c0c0c8803c580550030f1710000001103070040c4c00b0742a1940d51011304075905600c01d020301c04686c605100707603489620552056001c040c0348415039002604155040c01b00a005180c1210a016200d0a41c0c8520761105080601010110340c0d4070103044c208440f01c4196039243c0b0082c4d64080c1c81d800d4108000000d0501268122069a203840c5540107504e031611072150362001204c0c1e860704000f000f08060301c559104603060014040c0400c6031402640d0740d442e500c200c540c40b07550b81650308040051028a442100c0c3c0110440502414101c0d1042e41d00c03000351071086681002c1540c1a40d01121400010406a00040e003865003061081d81070210681e42c2d9030140b48240d130104161008a5404038060061b1340d080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 833485737 1250 833484487 833484493
    0x3060a090f021306090e01060507030e09060103110301080309040e070e01050120011d0624011407060f0e1b09043009061d0d030809030d0504110f040b03 67
    0x40c42604040d5201c5155030080c4000140f80c01d4400c034041103065900d900803000a0107680f001d2200c43c04910f0704070300410183c240b0310300709061540d010700051036910300c0700c1c01910781400090300340c1c1c441c0c0c1050513a00c241c1460300e41e695848440003a20ba074807500c52036003e81d050213100000a90002604000c03240500f159050381e9003800b00440d0380c409032000100c0c1c0104205000d5148404c01c1c0316840d845003260441c40040620010001c0c200a001440f030614400b107141c85882c000320725607440442c140300346071041841180c4d00b1504030b14012600e0207480e13146445111a10130f0f09a50250250308010030031900d140400040b1400040300d81320f00190400504008100050074400b040c1c03240e041344031044016000700700302e480c1e829a4203140340000038a814404000d82c0303410003840320240850000306242e01d11000041740000301c80302c00007000c00a01e0f1300040ca1040060003a68811418000c0600c101d04040c14903100500640107000d11031200020116100d281910540d00e403404003a007d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 833486987 1250 833485737 833485739
    0x503030304020616150c11010e06041104060e0a0509191e02060f161b031a0c2a060106080624040b131a0310090e0c060a05071703060a 59
    0xa020503604606404918001c01079030100010394000701e05104245d00e83c400042c0d08264101c0208a0110003044101e40e900d0010003281c40ca40210b10f0b282c0c03203a04a241c210f1001084d4011030000c060310750004491300300100602c5507103003058101d18003906210702101c2d0b500c2e1a12004001d40703038110900814403101901006280c2d0307003e0161403d04c90004010310f00304070081d18480c03c141e10040c0d602c1514401290501c0401182d01c0c1c5141a102c140d42c0b1030741c0326038115039411600b01c0c00031021680044038a00011811080201100c601112101004d0000c0204643e000d440300c0074003160301814041c0c9400460314a1065a00b10302c240c00040c204041f003184010391074104036241c11282c03400141000301044400004000340102e0b0132030b81c82c10700001d1904980c152103206001407030303084480801c240444441044810801c1d40c805c01400113031414503096507840d00840c1e406240c0c01c4100850068400c54111014010301401180001119200507104058a10040714516030025040030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 833488237 1250 833486987 833486989
    0xb0c031b07170105040b090c0f04020c01090c0602070807090b01050a030209010909150e010b0c0d110f0d0503041b0b1c271214090907021005010b03100807050303030402 74
    0x8006080046041034941c06034407040d000349a07540444640340396a4460080c4410020140d0750194800e8060300542030040069002409a03440c808050b0702c0703235401050000c88a0303420f43c0221015944420600e40a40c0e4446029482c1c81051281425070700683c3c000080302200c034000c107803200300160f40b8113180c101644030a800a400840f0304a0400105c00d00124210615200c0c01e602c01003e803010388000b03440c106404c148178005800c503008146003071140706208400050402103424480c140702d01110b00343c9040c90314041c03a0080480c81d510540c0d0b101107240703400170011801036004a0703130a0000c0782d03491014858001340344503201088804118505100d6040843e04020304d05410000c54442c00c04c0c2403840404000e00000626020340102d08420404036801100002e00c179402c001e0011440c14800340014012085030030701039041d040009104520030720105c0c1260b207407a1400c01155845031700ca640305800031120071904055000c0e012038403680000e41681102d4000b4011071959680394 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 833489487 1250 833488237 833488267
    0x12020316022205151c1203270602030a050601020c031c12050408091f12050606090d0308010303020d052a16180c030506061803120a180b0c03 62
    0x8884055404241c8070148180a281c0c05540e00407215405040d04c0d10481ea81001512185019140c0b0344546a80303042c0e0000318804604140300b61942400244004801104841060000e180e5003040d8180c2d03000e0410080c496010f50300940d941c6d002003140d5aa6140103aa03140c5020703201907410ba01030060301240103540400620035400b11715105150002031150002910f8003901c0c121840000810800303140d042001040244040c803030014400202941c0e4084c15102440d60010002c03520740c800501e15448110071100802e00180c02d901c40f10119086c0144644401c0c007086006000700090182040e2156003540c40c1c207104800940d041c2c00031001110020461440140c4482c050f21888070310b0300608860540091002c0c0e6000c5081c2c40c85042c2c581d0451748440441024945840b09000740754540e0b806680341200f01c2c1643c13110f0040404002880c00060403800c00c80070500081091096034014003c1c02c0d4035a821401410700794544410240c10300070b4003000d901c00c1d0f0003400040040c0c0400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 833490737 1250 833489487 833489509
    0x140f1c0302070512060f150d0609020d240e01061a0d1b080a06060c030c150b040f020403030201050109050606120714070614390f07030201091202031602 67
    0x1a0040b100c90b41c0d91000850310301e201d000b8400d1819004841040641a502c8440135030110500b40c0b481c0d11300038031100261481e01144000340010b03a4862081d030442d11108180402240c01503103c0ca450050059004034021111800310401800c1c2040820a60700500500043c0c4810b440300550040b4404119241a00440040c1200ca61a010001c030509000021102204640e03940c1c1101403070081840019511298440d100300400c880000c0c000c00e9002038625441540200c0d5168866801c03c10b600c050032400035075a91243c6813152008c80d01b003e9600802c21a03200ea0001d00c07540c3e03030ba88100d2089510446031250031000c00c00050071011550504c081d8800741908200700342640a4205d02440e0b0440c080889071203a4805004c50003854003071a0a520000c00301c4120000010400e00c8001030000c1058400701c441290040f5001d00750303030002d40e0a043c450a800b070f03480e0381550034002d020341140a4203480702d410b01e58603030354510310200c1101c48287e0f019a000b2421021607080c03040020398 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 833491987 1250 833490737 833490743
    0xc01110601122d020109140f040e01020d150f05032d0f0105070c061a1305060102010905010f2013062d020d0e0307030c2303070e01140f1c 61
    0x341500040c40483c28012000c005244041041540303080c80c4000750141300c0035081006c00c400303166042000359450b58201045610f040d1030105d5095080810b5034060300481350000310190814080540c99a142800344040722440e003009210555988241030310740080d04080580d01140b0b00800d000340d1100b80b80f05e010002d0791011070740c0000150705d0950031220107032420f00020724645240b03010300123140605001e03802850050044614401c0000d05112210305404820907260000600b850f8000c7d40401910b80d00480207220200e0b601070300300003d04980020025201c1d030241c90034518408241a9500c00450034691060f09040540c1511030302d01034007001d0800a85403408043c01c01404c00c910050100903002404011000c002c0a014044c001580d18040c1d80b2100e000c101248510503094102e50f9150600208a0703000c0c03820040300c1041d103180355050711601c0000a8030709060741c411070490b10641141405603019504100c00d4030320740b0054540c8500c0040e20300202603107400e01d0340da0842c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 833493237 1250 833491987 833492003
    0x20060304062012010509010504020c0303070c111003240f1206061802031005010f0e1203071b06020111040b04150e030f07030b0a0603030837050403020c0111060112 72
    0x60300e00802d40b644040004a1400000700040000b41015018140500000c0300e05504180c10240029502d00008011600b00922000a0f0f814448104841110f0040150410801c0d510115024001e403400c10307002d40c0203424046c0b07042e600c5500e040020702900c0c007001ca40351204c0e02d4012000001d0380900019542e2640d80c8600061b9481d58081d60394007084c6444c40580c4914000c29100f500354101e50216040c403405521290449511150101851404a41210700c2aa00160003407660144050042c103d40c2c5003107090340e02003c1d07074629070202d5105500910002d0081c4200354940c0c01184641d584800003030000b40300241c400200d2464810344c0f8074100040441d01c0c000240340c03000e041c0d43c0f969207820120041c01401403503400603070b0281240304180400352541c4c0e0024800040140322120704100720300c17a030740164842c1640c0010700c980c9442e0b402c41e005440030716600804007074900300d000d0711030340a444c1d500d54001d040112041120102401a0703030310340180341c900141c0c000c104a132440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 833494487 1250 833493237 833493281
    0x1305090304030b0c27040b030703030e0d0816031808030a0f08190f020307030b010302090a12050a0b090123070f03110423010818210403060e0a2006030406 68
    0x903003c440c40d94054100c0a0464266170210a11088540c2281007030b0080d040688140086600a01c0c07440c61100141c034142d4140c0c0c0030381846003490080001705a200c102445480d0705140d40088920402e941c0802c114201c0c0781e85c1d558107940c80c81018107520115050001c0709048a02540c070499200c0186a400142540e0700c2c00310108a406450700704d03035619804018811000d0389885540580c0b00c0130b003411441c0584180014090108510900070135011118040c410000c05114030340c0c00560041840c0190b090096016001e4092120782c091110307c0300c10032411b12042800c5881c016016a1202244020010300c12400b03082d5000220f07154050400c000602c1c5d540312500e00c8042c419004410130416060b2000501c00d00000c1e00284000b0144407498440c101c01086400018500c0200c3d03044c020000c90b5690f495025a44c00505028508034201c0d40c0c85c0307000b10340030a00303901c200d1005078103050555407104c00b080319008940d00b0a0083c000140029561f602211880c004514000084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 833495737 1250 833494487 833494507
    0xb181c0905090405060a05060a08070b03090102161410180b1b0a0e09070306061403040303110a0201052502070315090803070207060f020d1b020a0902181305090304030b0c 75
    0x4030100b0f44049031294802010080c0792001841041d402000c11034901804515200003d656100079000320f0801507070000102d02c1c2504258100d4000820300380c413a611004c12410080c2c51200e9020302e000741800b5610308517085141d02e2250b80720900d007607500b410207c011610340e881c0944004015154800c042042490100b21000140c1907050711a96010603015805c0c0c103002d080c03240500380c10245403c0c42c00c184000758100b480b0400c440c001620b00c6d5140d51755402c0442c040c00a10020916202c030006024103500e5064100a11941d034a011003040200008224865403595042400c01a003281c001030001a180c105c421075110130410020402d0b41040e00c9840c2e141e40280d80120260307112080c100005a000354141100031742a00141c54020000c4030060100e0030107409003400200c40001d400115680d51000401402c0a150300715210362442ca0b030018801c0c40e41d0702c0c01d07200b03050351003000c040c410141c000d0078400e90b03034078000c4c509291465440380e0192201402f02c00c500c0c0010701030031840b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 833496987 1250 833495737 833495749
    0x1406030a05101a0c1501060921231506030d030f020702030102030a090203210901030b04140108010c1116030305071e0b0708011e0b0d09020a0b03040b181c0905 70
    0x80110500210303036580c4c10703401591511410b141d01d040c0d5040c00c1c900420a05420070348001c200d50a4618210100903c0c9040d003081c180015030085c1020080810440d040301914200207074501c8020440d00c3c3c9440340c03058040c80c84000c50f042681a40304000400c0001d1298000c042100e00500c0c01508000c6181c0c002420382e003003210190000e956130301d01c001c10b43c60304100500c240003003010260044105201005690310030280b02f2070505464040503c12500c440c0e001010000016451012958403989040d0107403005000307440006200c2d01e114248154049960341e024080a012101c0151459a0070f480d00e400800003a0340d4082001c0d800081c000c1c3e00020415200d1050b46100c03090f20300070320301601c0b031841030704460240035400041d0420760300d1482041080e50454030140352915601c4507502c4c0a00341e1801e0094005084140006101603284042c50240c1d01c42e1005210540d00e030381c1000503250380d09c180d5542c2ea501410b0200d15845035042030321044211443c10f901c01d5030b224408952 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 833498237 1250 833496987 833497019
    0x10918051e160815060910030f0212060403030c020c03240403180305070503011112060f0a0812070c0e0402030a060b0d171c0608031b0f0f070e011406030a0510 70
    0x35070743d04140300142e4036a003413095030b642c06041112104080d0070100440c1c500000325000061050010304420410340d5210410440b00000c001c0c116a100e16183c076008000e44401554034016125124181c1e0302450081240d20640d095000e1518002880410740d5110480242c025820300402c05841c031407282440441a000d140035400918a603031501083c90b00f102c84c4000820288142445a03841c0b40140002c4030313400c100216003800c04988420000303141181d00d6400700e6020311842881c080391540b00341c040d00c03681780518a03610485039911810f40c00c015046900940c15041620f002000407000e85c80b4403a00312002c0c0c0a4a0190480d0350303603c414071500080c1b00040c110114403048964400f480b44580d83c01246030a2045500e42891a40d69024041100c504c030300c0641e030070b0fa05c2d0030006c014858414401ca411249003601c10f09000d529056203000e0309c130511803440004544641000c14004400d02e0283c41c0616654038115868001d081c094511100055460000203150081c607217030032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 833499487 1250 833498237 833498249
    0x1d0a0b040f0e0c040b0703111507210905120c070e01090518070506250c030b04050d020105060108010b180d08030105130612022107030308010918051e16 67
    0x164075030404011090300d074401070140d1203e81c82000240918030601c0c2c240da000c940c3c18101201d20b4807200b5402e07806c1c841200c1480c1600048041003007241039021088041410000740e558200545480102080d180000c001901d5031780a00074100a400da00030042c0038003030b5840c05440301980c48905500d1280e500f030348030b4400d42e5250020321114401d552042c9683c00007144c01041e0243c50030000c1106801590345c0e098102500d20302901f400c8840c0d000c681c0c501030f80b14a01e205034070f40744c0c601480003120a40e4107507050300c10403104103001ca005201d11401b404050b1914280e036880c105200060754000191052964040003209032907440c1c1c4910f10741400d2249441c191658107003070512060140c6d12030940307178450516504200307840d4202d91203000a070301598006e080c0110705111100301009031075a0b0b045440b41705000000d260340b080009040c0d4242030701c203100102c8000e04c425034604038860080c1c0b07140c02c480514590040c003090007100802a1000f580e02c1ea00d00c01e12a800d6902ca44c1d407102d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 833500737 1250 833499487 833499509
    0x50d050408130602160e15060403060204170d1d06120a051602010209010525050d050a090905060f0d030306091e050105030607080c0a030f050411030c060a1d0a0b04 72
    0x1080034030740120600c000742c055031000302114009420703120001c1c0124454a50400482c40128908a18002001c80300300340117010107627119940d24004000b540035120b07030030f000d00030302c02e91400440011501c20000c1400d59034001c3d610324103000900010040300c0550394459810040303500c5c241c8d10101560b2055058500c00100344c42d040780c400c0000c21880a0030011a4410800700201d41c0e04003040d190303c069074601010700255804440e4211500450014160384209811070b44491b521000600c0c0950280c0c2c0d5820362075a8940f58441951801d8444550000c4445070440c06800d1030481d0420301e034000e143c003152040d55680071004440c00001011080400c02002d40b18065890003018010402600200014a80039500a281c004043c104180c03800b40010f24807180b0740f00c2d800032107007003501c4842041141001e2425409072000030841c28028000d820305e9042900d0001c0c10b843c00400d05844101c00d400c010350715110600310f410512940b010800300b02088588020b03000d8006003090180c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 833501987 1250 833500737 833500747
    0x1f060305090709060617090c0a1509140f0f0103060f0602070503071a03131505070e120109020f040c02070305060903070b0c0f0d1e0e031b06040c030b0601050d050408 73
    0x8042c10311140d5003007440e40604181c810480300c1e6021007030b032510381500c986444061320764850f9507007010099490603601006900d8013081c510461b200d40640380280d51984808260380340c800350030f050900b45084d070380a898075602c14000d04244141610700e08052500083d081d0320307001100c2d5408a01d4100c0b0300140c0c0142d00c18845414200040005403004484640003c10748409e030103924800180b803140c00c0c10202503128200b0072807078042603000c500d45500f8411494000c00080c040c1140298440c17041800b07159a41c900b410620583d400c0d02e40107040c107d0038581d280300740006040700e800400c00310b01c9080d00c00400f144061004074001d6111202541d5180340c0c60400c0000802c2c043c0c086900560100507458001034201e04690103c00c0a080124030400160010300b0310403008004180141e0800c0403903506408007000034450b1740d0105024074888480184800c1d0380b96801c81c0c1c001c000e08444d8006201080d611051503500850500d801841c29642d00b141c2e90940c1d000351012600d40002080c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 833503237 1250 833501987 833502001
    0x20d050403021015030f080702010c051002030a2d180c17011409151512010912091421032205090f1f090c0905030114060306010308031f060305 63
    0x10303002d00042c0240d8641c00342400d6446d8420903003011640184410300020f040401c590040c0840341200b40c1001c03e80b000c1154900401d001303580100c942c40d590518100034640b03103400d80c0d41c039840f01707000381e004ca110426104003125008214000304007902c2c00440511000145c0303094070410150032003840b00380404035000c40250950b400a400f505114030343e40200022a00c0008590441d008002c064403030f0b60311408901100c0701ca84241064020310651019a03038907005410507480c41e44030f05002c00b452010940700301c1b020440b6005815148500c420860001d141030981f080001e0101e8241802040420000c1392841d4802c1008201c0c042d44a134500c6000075070403400400406040d1520965860560851017819500520105400c00803000c00040341000072080c1c40a8810340034200040650b001001d07100094921aa5202c2d40c01c00c19441c440a042c0c45c0c58034043c5601500030041030742180d43e02d4115801c010030006080010701d000d05510012050800d000303101e103807000995400c0200f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 833504487 1250 833503237 833503241
    0xf0409110304121b0609050309090a020c0c12010b0d140114010b0a050307201b150f030c0906040905040204290f0105090613151803060c03020d0504030210 68
    0x680038840310024810403000c00c4240116007440d103000d14040308492aa0140482012144040544090310302402a400c10200200505040008450f4400196105540d02090348103441940c6481d41120a14419030f041c00302c03641603501d207144004a4640c80c640007040300f103010442c01b03440f0f000c04080e500186a03020321404c800ca4400000e207030a503604101c10785242e44243d070207d004111001000801030352007030100100e16005612140945445495440e9540d4070222000320f48241c1c00d90003202c18505004a410301a00c055203181c10b200c0b85080c4c1d407286800007000303c1010302d401c01c00030140b55500da000b0006031000920000300c1e070270a40180401c640780074985000c0d00050104140010712403002980a0702d41c02c0b00e0440100120100481d41070080c0200d0b141c12482c0440e555411009164501007503900190a40c0020300700c40d0021541010200440169042c0c4200280045061508025182d46980c1405031900380000c0140048034800c0718150016000282c00484429180c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 833505737 1250 833504487 833504501
    0x1020f04180905070605070501140901050712090b0105062a010f0606080712020306060c030d09060b03070e0a0c110f0c010f0c0b0c030717041b2312010e030f0409 71
    0x41d60411400c20075541d050b0b62002140034160a00501040d00b204203c2d00350842c2c00d29000c000003402d40c034104000164041c1c04140c50f48404580003094a110131381d11845040c0c0920f4005014076456443c003000d2100e0b59104951141c1d0001d00f84960900d050081d141d11809035000f0340002483c280380d41e03608801c43e2411f402107010003108100340801a80e0042058820390740c81c100059603502e074440014658441c0032035000382404003041c4000055450350000800340e00844040c41004020000c1586603456809610104204030010442425107036100d40340319611401c02294081e0b0300500c5520f001240d000b919141d51000d024011156400340d41008203c00b10b0601082056480e0b54094440c0002040e481701182c000c8001410a031041d00480c40d00c03801805c0c07410090600f4142000980310900c3d0001c1e40d0044042d00042d0107a40159401c58030b02022103031303111401e00d8001c01541007880340900c0a40d40d01e80441c01442e92081c002400e40800c01ca990642c0d803447c215051007031382c1070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 833506987 1250 833505737 833505779
    0xb0d0b1f17060709081b03030903070b070203012a030b04061706070f1107031103070e042006090f0d050a060c020d11011a31020a0e040905070b09060c01020f04 70
    0x884c81d02040b80c0040050240f1402215440f90348040c103c0c170780800d15601600050940c10702c541280080c81244000060001a009400900460b000b11481040c1080b030800b0b011984401141c5522407644070741e000e0024a40014000300344150385074070040049101000c80c143c3c0e500b06009005c00c01c3d42050745200c802c40da0f030408081d0b0500d6880c545880304040d02c0f010b030059203824244aa66902448004080d080220440034035081900f042c0f03440c407203810a03c080c80321104006030300741e15040382990400a40180341c603011a03885028480c0e1001c0c040412a1148201040d500c0050602d00038070f1807010643e4000d010704c51041c507004042380d000014004080e454451000030003030900d0701740d0071020b4080d80d6400507600301461070311010b512500d010500e0380c0d0714070721503032488850f0f0000c16003103d04c0c0d913074280541144000c12040b10340c4174000a196a00419003000242c103c24045c0c8912040144414207061850030b5a07400e9074804034803120000c1c400501449070b09616261481c070800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 833508237 1250 833506987 833506997
    0x503120a0b15120f0c031614040602070e010609050d02151215042a03051308070818180106080c2a07120305040b09131803030f0b0d0b1f170607 63
    0x30000040c02c85c030310000c0e00300d2030041400000321011a01800502c01c0240c41c045138aa0380e80d954203002034a6403610301400312526005c0c3c00000c0c910b0b00c50100030054070740003450a03151011540c01c1011307000e910411001c00d0b036400d1104011003000140317a24071960040c01442d5450101d101080110380004125144407209441402c039224101e81884500002c14240003031a0f0303c1d1b400305081e00c0c950441c8010402d10002500100300150725002e8280081e0b6412041001c165450400803694890110b0301240760301e007001044144d01c244490b54200c45402692480c00384000340d08120414010924100c41600c400098100342c400c00c1040c00505402d040d4150302d50b440c1c1e47c001e00c2482603210b00445000d012800c80ca155550340100300c00c05100050030007008020901c24400d50050b088140c010903e050403442c2c00c20001d000300382d4565030051090141884554400d22145800351055400c5501c0c6c1d461a040a40110503110203440c2c01410801690704c1400bc451a00100500400c208a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 833509487 1250 833508237 833508241
    0x210a0608070501140d05040c030b07020f062203030506060d0f020c0f0a08030f0712051501120b060403061109060a2a02010f050304141b01090504090503120a0b15120f 73
    0x10a14059594005505c1000718051301d40d03003032015203a5a95003025000d081c0000520204a40009808440e00c44d50010350704142c0d5a9020f0a0703001070740314800765203618440020000030f486580070f103510800c02010f413818401c81043c030b4011520503107204180c1d51b80c0003030200700c880010840c0000800c40c00004150344034490303540c0c40c21404003808413042040e03844d0224461078083d030300c4c01c4669005120100400d145c00700005141c00c50010801340454407850300a4a4030020340038090b1000c5004e01207a203010310f10307910000140058200001c1421085c8052141641c880c0010502048960b49154200b0260081c448814400129842e04002d0a05060300183d801106403000c942c01818402e0712540c55040001c011010310108140c0d0340111101e40034540eca003000406200020b07070f521991b140d181c1e0b041c442180c43d07a060240403548240a2487c02c81602c9071031a60141d0b0b203030008a404a26a80070800c010300707201010b450110f01150168021042480d119804540050080c1d001c3c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 833510737 1250 833509487 833509517
    0x90806012606132003030a05090414060928020406050307080f041a060f1008010f05030a0b0a02030603031204030815100f180509010806060a2702210a0608070501 71
    0x1c140c2c1c414000702540440000400d00c84c0c09440c280e402490f01030266079440c85c44200c010035035030000180c81d1281d45030440c2140d81005900800703108103800340c81000b268407900402000c00106450407080310388040c00c8455184000e002920003410640c491685074208090064480346008203a0350401c0860800c21002c100743d420003c884655203c000c01141d102c05010a040f04030a0440c42d8101c4020312a40c1400e9a000390001d04840010219409003600c9400b09600c991a4050107406015110003203012298030354002d5820000007000c07245000f504840074032540c074080f141940490702c201d040180101042100703110503002121160a650240440584010341816030a400c000c50b40c22184204038148500c20041d00e4020440c0100350303540c042d0584e603070744219080c83c09049448400107245196001401a5080c140c83d1054024101c400341c00003074002222380c211b030000501c2c222170302c024483c44450140411900218105003006041e82c40c101c00380e8845c504200e1190a072410b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 833511987 1250 833510737 833510761
    0x10804050a030e0409241b08060f030c180901051e190b030f010b120c2101020f0a0f0f020304050303070b0612190b01060f0507060c090806012606 64
    0x20181c0c5401d000d0a100c44282c0410300030302d00706400030196002d01d4a8510702044882074400f81c00005042841401403004061301d00341f0320405100040b500c4400400c2c0540782c00002c92660400141c200d940c00307800e1a001407500740104e503138072140140300c8052190780303542030081c5607006d4400f900c5c0c1000c072a462081d69421900040619504141003c0d08414050007a0080a003101c40281103a80e1f48145420050007024159104d41c440d54140c4c41e480c1031000045601100e02c24010b0038081303980c40324200d24002815444c0da81d965550b00304414032041c0030f00070207004504c3c0f140d170310460f1081c20100081c1c0300c591052004000d41d80107010801460b9000021a00110350040500b07025403039280125082540d9030050465600400300c07188e4052422a07004080c8038020380d5185800d076a2a41705803009190322081c480051401c0190201062040d04245003002803407402c008501ea403200c3d440d04041c000e80000d0105100e4401d48584410031004010182003008080c0416003480503104c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 833513237 1250 833511987 833512003
    0x20d02030a05030115140f0a1b02060405130b0d06090b07030908030105100302040806042406050102070608090f0f030d360f05030a200a0510020d0e0a0b1501080405 72
    0x540d881020624401c414450341001c20f0709001c4c200303e40d4845890b80000b1f02560401c1e02e0a400091015920908036112810b15200150700503010350b01e030909280500c031884c848060300e41c005c540c0f00c02070081c458440f50b91401006004101c00600c102d854603001800484c050000070400d410000d9850110b01600d080300e0445130204c9095900b04600301094000c0d000e5640306841c0e03030082e60100404e100080b00c905035544801014000b040c3c603440920421180f05008913401a07000b04024800c10380201c1d52030340c120401c84100d171124460480c20620b03024a0b9003501c1c00caa00049500c54401c0d146010300c10b40d44101925520054600c100f030f490485d6900c402140391041001220300900c0f0303003001c9008040b50003c0c00e6130360b1000001c1018060810482000340d4000014455211020300841d0001e142d03a406005082420f104540103000307900407110041c421913541e00c10204c04142040748070292842901d803281c0600e8106480d0461a02600000781444000c10803c80003810214980f5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 833514487 1250 833513237 833513249
    0x601050a0e10090308030c0c0712050a15020405030307030306050103051012020609041509021c1806150b04031109090a0b070f02070e0112141b040f0f090305030106020d02030a050301 80
    0xb40c041c400c0c2c0c51003150714828036400a81031080000c1445a4107840d400182001c900540c1119041550307a80000f0600d1050354019005412030003122001404d111700b50140717111200409814640c803400000c0c2540d018081c1200442c1c1c0d1014100b040f0f580600855030300c01c0080c1034148035a450201e00c2400b100082034001e11803980060381281c16902d56000c404010000c0040c00700c034586600040c0000c1d031240d80704d20200202d443c581e840c0062140101150409940e191070f612007295914a0041c1c800c40080020800100f00085401b40c80c0780d018000843c040e01800c0324140c200c2050046c81400505840a650040448580800e08610f055500722140c0d140c085540f00104a0032401d00d0070a40000b015074400c580005280d400490305115128010700c0d025400050940d00140d407031450316600a0b01c8021914259554030b06903100d1800316801c42401f1520b6042140b90030201c908d01c00040340410004401404426410840018801800e0004610b0140c20400103841404140308207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 833515737 1250 833514487 833514499
    0x605120c040207051903020f10050124030b13090204140103020f0112020712080405060a2f31171504140a062423180a0c03050601050a0e 60
    0x88100f144c100040e42c0b8842c100c3c100648071446a01d0000d40314647c04400c401544503e10305454452258411141220349074100c02801f2407108049a00b0080360660070414540d40e40da9628503511100d0659260680e101000128184035204000403100740704192903062481400500050700c555100483c0c61009003482d201d0b00c10310a410b14040d100701c1e00300814024030050468070180e041355519029511410503200b50b551840c03941c5e41201c0b443c803c5a4070301e4040c400c100c1e24085180d142d00c08003400034051140340c8000c5d004c880410f090041d01e04501440c40303607d130311044058400700d040503011101c4080324a8140005190307440001c11841c40704102000c7c049410001103003c280c00c502040c40c250707034180305039040a0008120428904041c105146512800380301c0d40d56241d4240d50019083c40e85131300e61100783d1803154400503100d98200b1002031a041402c241030813990321540400300c01054001305920001c040e00ca020b060a8140310050128400b0703145c10946404084800380c0d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 833516987 1250 833515737 833515747
    0x924090c030f0c0321040605130f0e04020111010912080604020f040f1509030c03023f07050111030327030414010f05040608060904290402040b0102070e0a0b19080d030605120c0402 79
    0x700d40c04946040d8441402c0d07035484e446c00a182f50111100034401c1c3d0007629940c00008404550b036083e070f8100c0100402e540c071103d4403107203814026203601350840000b80005040102015805a4690007034000480b00300c8440f408210040c1c115510001d80c1c801031520050b84d80c40e5544884519506000080c411607010f0b00b0643c1402d62982120032141c500001c03501c0f203900d0100c0708000080c20040d0000035004074031000c1904d50060038010031132580d41000b0340c59980c42881030503141e074000c031480307043c00302e03581e220415540c040014001800300e82e000300c1c8441c150388002608000040310010f042c07040c144400c0003880d400030081c1d684900c082d500068260b83c0c900c4c1c000400e403140d06810a140341850301c01007000401080d0705104501c240c07402c1007e802c00c0d00040e42c1e507805c64860074450060000c001003203c030f007503049200004c502400f0620b00103a4400c1c14041d0a440d0741010019501500164501d15410b005010082034150f581c00c007100d8582544549520419928601803070b00060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 833518237 1250 833516987 833517007
    0xc0616020102281d011704060e06040b07090e01060f0f110610140a05210c1c0302062401050913110705060924090c030f0c0321040605 59
    0x4549560102000442e40080f1101048400040015045000504000702c81c041c100d525404451800d10584552290f0000003015101450000300200d80450312000c00e0900e600c010040d1b1405130b44070746401406803801010007095540c9540c44204900500d00041181e15040384180002441c241303402c0041c44819001a941c005685000f914940300b54420046e06000c902c44000a441e5441800401215400204907520070f490040b1607015444c3c0c03c2c18412030b51305d500d52401e44855023064410401181002610000d800014040610b94400c1c40074109a410711803250b0001818803a00f0048907072050807491301021100017410700100140a12440d6030340c247d91008a80404e4090000b42c0c07050703242d5410b54010081c22a030030310400d070120700c202c0000f0540d0340c24600e0070000242da515007829400d68216018202e21800e0003a034101c108141c4003030000041d800c10b80001024200f030b251040c50710381400b0102140400340326500c000d00b8110500c0803501190987d2038807984424a0350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 833519487 1250 833518237 833518241
    0x1503010e01050d033608030f1b0715021507020109170c01060b041d101a0f04030b070305070e12060117120d091b08030d0f021308070302150c06160201 66
    0x91010704405044524040e0200e00240c1c004442d545c625581002c0c0c5940e24155a92401450f13501e0004003c148444c040032400ca58a008018401d00d085451140c2d8030031041c82c5405c078541c800e0005030440c141006001302c00e02c44060700308100d44001c1004d014951100300c00c004824030244c541d4a00040d0903001100c0940101c000b8200c0282c1c0e49685075541e6034009a8030031049070303105c0c3d004100740010f54041220001042240c440150901c2c245800c101d51000d02c0c1d20110281018010a00011010510300c1c1150781c803421161f20300240b1401c140310058020304225202d0b5100d07900c0081050041100424443c1c111100000301e07214900640741c2c202d0401d0061151032004c4e603000f003224401040c1d66000503043c20302401c00c14140000c030a00110210030280100c01c2d80b640100b200e5200000140e000e0020944d10310401801d103568032a8052242d0074961150032203501c0241c080c0254507029901c1030080424000c0a0710f800700da105072607200c80d4002d01403103600048510310b0628500079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 833520737 1250 833519487 833519507
    0x402030c091c11060f0d0902030f19020337060f1806110c031c0e0303040803010f050a060c0f0614011d060d0507060815100f020d090501020c0f010e0907030203061503010e01050d03 79
    0x2030ac090303610100c0000b00149240c88100411b0b8442e203d61015521044100140080100710306100e81079052034801c89444102c0080c002103400a0b503032110804004043c0c4240d100015641c0c1050400d0340c4581046002e5546420141210140400501c0d080210004c22201201e44240d014420364032711440c50300c010042440d0f010742c01e000010800080145100055050b102c0c646130041c015501d98042c042205028010040440d2140c1360382c101081c521650b8554580c4100e40200d607880c0c008c05528580300307007a1b009804a0a40c01134403c420341c811202603900060a94400c0816001038851541d00d020f04e1250900b444041c101003110b0074581d010b00000360402400c92140010030400003000e269450001d140180180410840003511441610301100c405070300500d5211a80740410007642130844000b418005442d03401a01501c1e008070b51803042303c07603032401a147c2c03401c01c2c2072000044003007400061441003000180800c405920810381559400e0307524480300d140f00e1030306a03814964 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 833521987 1250 833520737 833520763
    0x111010906020d141506031803091f0908030711040209060c1207060b010507030c03080a0f1b021e060c0a1209050105060f03011a0402030c091c11060f0d090203 70
    0x280b0140454030b507048450481d00c40c0010130b040b41d94007512840704d60a00d010f41ea81c41031003000480c1c0b1a00345140c0030f80c0404448410740e032900d98048002620441c00711031106851122500400316542c100315040d00900e015005945007007015a1420b000489032041280301e96401314451109865003810340c0c0d40c40810ba0101c0c2da42c0210740030640310581140ea41210000c0c02e250010034594480d005540007036601d91076031003005282d994291071400e070040107035002c1981e890404084100344c0c002d0f000d070780080c01d0a458540240841c000d0070140b0844c83c1d40c9414410a0903120800740001ea6564400580d180a0b501d9040740c610031034600700e0490350100e0460510051405104066000ca4094503040310b140000c6d0000300285400c0e101003a1420916101200c03414400c3d003082c6c0c0080d41e10614150045181011081c002900104074080903680d1200917200481040a00e0240c600c190b001110316034200801c8031003682c0300344a03403401d68003880d855515071002c54800300325854507116 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 833523237 1250 833521987 833521991
    0x503010c050a3c08042603131b180e0c01020d0807051e0c010f1a041d1f1104181d0601060f020613030207050d050304091103150a0f050111010906 64
    0x80390f050042000c48190341c10b803076080701d611940c44800440c0c0e504045040c2210080b034110b50b00c4050508080098000136181d0b145400060078170f00c1c804a4005000d08041000d40100d41c4103070100c0d4048031503d1004603120750001d00724441316a0002400c3c0c180e01c0301c0d403800c0340c9103660300c40c02140c140c0a048180c10340740d00028080e0328102c600b1800b80c20030004140003001200000164042a02d000005202a213000c80b001404e25080075040900f66854480c10708100d002260100f6140900401c08140d002502000d10104e1400e06d01600c0c1c181c000c000c0b02203003064240441c00c251141224880744e0400c0c2e4652201d290b42d1240516132154220b06815104250303985c14002d00b5000c2d010320004014080c440010310410025480110302d075800d6402031240a080800740304c0240c8848a0603961448103000c0020111094040c1214003216120440c0e00d13400e048840715030b40c02500c41c55510410281c8002d0080e540b0140109040354004d02e403050424001e03071145e40c0140130b50200600507034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 833524487 1250 833523237 833523347
    0x90a020d15030506090d0e04090317040804060807021507080a15061d0a0308090402090622170604030f14070b011235030604020d0c090503010c050a 65
    0x191004030765a040324000e4056501c540c0c1c5010804d5121920f01030740c4404900307404006051410903501840c00135111f0b050a07a54034402c1c0d50840c0380b00c04110f604a80880c00003c0c1030118541c80341c0081d40010b00c5000408181070860195070702076000030100420451a5400140d11008541180c2039054520340011410390311040c0050080d0f031910301c80c8078002a0122504001d04142d58a081100e400c00003070750a201d0080f082001039440050200c2d4071000500c00041c4800d40d080912082c21110401044050b1824560888611400d44403e4058001000300004260880c8003d0714101d030904e400340300042055265800703400b80c440b011700b8a620100001c2181015600e00f100114004c0680c2044105401d1000041901c51142d44408038021803200c3c003803110640c081d5401941c018009401c1c0590300c4c0034130301242d24030211400040c41c402c0041205050a03c9058000c88443c07800c2440c015820101070200309031214a549004484a5601c55441c0ba5100d0564207418840c0030803802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 833525737 1250 833524487 833524511
    0xf0c030903121701050f030703082d0d0506060a0516020613030b06030f010903050406050711041407030c02010c090605031015050d0606080106121d120a021b060306090a020d 76
    0x28290910720b41d0f5035443c895001103154a020140c00d0705044005004041c5141184c0d1214115048400c1d0402031182d594071442c4602e5102c1d400f2040041030460103625800c144081d00d09940c0c0c00380071347c2d0040c002004840e20003940003088440e402940040003206004e20301c003080300f510450000e140c0011168401200b000406186140540011022a088015601c01d8242280c03411440200861020802082058020400340142900800708801c624040e9408038083e42c94503080760290251940810488a815200c0e414851460784020070000a0041000d080c1d07500b0b500500b8213000300400045d00000c55850144064400712006410701c01442001404540044080210742810f00b000410f43d07a100d0300143d4100c941c950f070b07902d14101c0c1d940c240384010045c1408001040b0300c1e42c0318060b040c0000b00640880100e00000d5141e5404030f4042c000d0925a500d41900c95244940790510043c0d61078a00380c80c0c22400403a20a071250f10381600e2440207100300d560a1407118180140c0c0101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 833526987 1250 833525737 833525747
    0x20a050607051e100608120a08070e0a030f050d03050123040b04021306022104060305180114060a081b09090a050a0b0a061403120d02040302091003060e06070f0c03090312 75
    0x12604c3c1c00c020501c510707074440f0031843e10340050307400d1021014414407840381ca103845400010b410404d00d080c0100040c00580c04030304d540b030306500b00b954440041990132082040c2002410310b003c206140401c0554144500d0302c50801e031070102c0c959400c00501050407203036035036444130b0104c00005108550300c2d070004c8082400c2040078410300d0094007500546034400c803101c1c2600008455080000d40c0f40500f0f044080e001440090720304004015840c1000719401c40900c42c0f8034004c070000c0080b420503d010010030840c0307046500035126542110041280050400100c8903411500f141c00c0d895540c3d0781020f092404540860240c154072030000240d00344485441c0841c011650a0402d000068940000b07955030790450407400d4142d4030803201d215800074140c0103080760800c1100003500c0c2540d00d800103008901e09813a0070300d014150020400400003144074455641005002410749490700319809013801c496030007900184150361100004052080c030300c0071b01441d80b0180300b5603040c00d40a00101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 833528237 1250 833526987 833527003
    0x9050705040b060a0e01201506040c170c032509050301050709051c0204061d180109030504060e06070c06022a03070308180a0303120f09020a050607051e 67
    0x100441c60715110b00503d080c01c1088460002c0c1c0f9440300749240306007034011a15410044184022085c4402d224040e08506000024410a41031841013090403d003013040101d03907001c2d65110500c0840c104210510112520541d407094004201c1a2207a8521414400501200004001c1c0107030000148140c03d40101160098800543c001c210513950588141d8404000340900b0743e00410074560100a84000040102800c0c0f01600104205030744052200e01400f00d0300682d0060300c003290400141c40c2c0d903800607008403003640000303116401803501c001e003091150340111020070407001d0541030140c440c4000c84005a80c0a442185000d03903941d40292554103400300240100c0444c9400c0341c0040c102c8081211168000340507112280c91580d990305550321501d1140500c0c06800c821010660300c10310782400860081c0c07160030880d60034034500812900840c14850300c1c00d01d011015005622000c510500351030303090301c07850742d588220705001c0e1800c00700081c02150b0b0f925009081c0400c10340030a28070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 833529487 1250 833528237 833528239
    0xc03190203030702101509050a0e030c0109170f1b0703321501061107080a110a0806070e040b010201021c0e1005040206070605100e0a090c0605090a090b0402090409050705 75
    0x842c0d104150f4105810380b59065124010101b10340b0040c880320b8030070352105402052042d000207658480740191801c43e00061074480b42c0d65525000700091059440513007604428190000345004211170301d06009000d50301115042c2140041b001010060811190002d10380103402d40b0345044855407144952010b280040140703000c030621580d901c1c1d80010f501c1e81c01d000c41e0f81d2405407580c2060812540b13100d06000f004200d02c2559400200200140466620240a024a03091515445051103025417442e84200380c0740d40110b041094856104500640c0b02100710350100d040800080100e019003d5200c0c16960795600306081490061560710500007080c90310140c5000400d5800072504946040b40c0c06900702d0400c11441c0d0000300550311056104610141c0300c001c46448442803038440e50215003480486568000c1c410a1000d02058400200460b00d40385281806070008585242250b204441d205505c98140301a9507a83d501620041e800c0504100724505503406d04a03039985162150b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 833530737 1250 833529487 833529493
    0x9150306050408030132010305060d021f021905060103030c060e0d0206090c0105070c05060706061203080604060e150d1401020f0d0b0f0120030d0e0102031f18020c03190203030702 79
    0x102610404c5070345c0c1440c0f109403032180006e046e01040d005401602004040e00c0d1b01c0114296072400582d2041c42084000c14840010740b50861104030191400640110320044840c0400041001600c00140941543e515142c0020b00700780f14a400405803d80d190f80040c180a010030700001603900041c07140c400c0c0f15810440780c00410401c01035403e4842c145000d8814100100103001d5818600c0040424034410000054100d82d500c44014001c41d00f200200e00240403801480420314041c0104005000607011105030b500702200000d00216400301312600034401c003038400007803286080050200000e51002955039046080750000039501400c041801d4070302d005091030003418100b400769208d680c10b85640c650741081a25403541e0443c0410304255500c01048620765810b158010000d204844130000f68a9081c1920344412400b0a41c0c0d00040780f010441080000041803181406c040c1103800300182d80382400d1301110f0851103000000c1030b001006140008160380d0020086204141990a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 833531987 1250 833530737 833530769
    0x1d0a03080f0910021e030c0307030605041a1009030c0f030605090102040806010303050708070c0f08150411060903070f080a0b0a0b01020a02040c0302070b04050714090f01091503060504080301 84
    0xc0240c507081030303030603081e00c0c2d2000300c2ca00082c2905a000b05482909020040c64010f0071084140c550351040382d104a0008011080c0040d49401d402000301501d0100c600740a15041d000140205110121340380c0d200300285060f1109982c0941c8144003d07640140b2040c03000c2c0d40380c2200d1580b514031031000302c035110300d00350018a500c0c2c0107109803000e4070300ca40302402071030740b940d02c0849003900100c0f802c0d0340200040100e000050704c0e2940c40c038010715001da00665410301d0035100d0f905180300098094038808130b0000300030001c2c8090309001e802540032142c054580d5801c40201c1d140c5425134005590780e03084010040369590b000103042e81507038820f008040b001d5469445450945490380f40807400359120503105030051030141c0011074000c10910b401400c05a940e180c10116280540307007914a600440c4c0203010744102009800c040d48000d9404c84964104035610300745001d0144200f82041e035481b012443d02203884041c0d10015038000c101407140742014203207a9060341c028880d45144968001e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 833533237 1250 833531987 833532001
    0x616020303091e0f01050a050114011d211f05100b040b0f0f0a0e0a08070b0d180212150708070f0e010203090a0608060f04060b0406050d1d0a0308 64
    0xc582c400c50010020b01402c1c50b1681000075036820555641215006410b101ca1006000340301d90f6200b0040d04001140035450701241051a40d56480c0642c100030a404a00d030648400740d00040054805507500150400e41410403802c2c1d040b001c040d40d110340510004408601070742c1c05458501004114100840d460b0f40440c210071500c01e20504020320700501c001c10040704003001600e12280c0307081080385000260301081c14940d0140b00702d6000310700d6945142d20242444101e4101615594000705030032824540b48c3c80c071038002e40001c5503005842c0d80c002c80285100c241d8100c245640a08180300800506c11345c02d84540d541d04011700e8480c0450000348203144078030f0030709005541540303130101000b000750310484070700c14038210442c1548000c22a1801ea0f454400c0310100414840e0340395807403400c10600308070b4040d000c0010301d0b11850030300b60280101b0266004032401c41d4401d051880c1d0720f101c0c0c1420352020744040405002d03da008004601243c00000c21110300c05031007680c8040e035980e540b403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 833534487 1250 833533237 833533243
    0x20010e0f070518130f020a030b010602061006030204081b0402070204060b1207030203040b13110a0909050f0f190f060f0209010320031315020a09080609010b0102120d0902030f061602 80
    0x150034000505013500d0f41d402240340328400d40300840c009810151126141c0d29501c1038088280d00040040c0d000d030701003050007601e0441400c040c01851406614203490001d0f0640d841c40b035001c01d0207003011058440726007a40c50380c1c1114044c40d070191040c031189170f80e02005411904103030650480e04411400140c172a912910840b44910341c04940041952600070b140d030b10400c420007080b10404207081004034a41e0350392407010000d10030b0001c007046503480703481d100c0d04100e181100080d80303034060303180c00c2c40091b80800e56010b44880c25449505802140c240307010a000b00610141549140484078000c090660f0014180d82c0020b032018040030040d00820544484464050700c0d0328034007440803c6107200da0107002000c29000703500c1c0c9079540103c3c40c040003c0340d01418404000c02ea0b40c01c41003000e12018403140764054400002040b5001c603c40000c1d44072084040c0718080c005000a54810b80a8507510200c00c0940213022544019540000031b81c0c0c504090b2007920401054454694000c2e05c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 833535737 1250 833534487 833534491
    0x20f0109020102030a030e2b03061d01030224040803120c03060a1e0302040e01060501080c04031a1801090507061b151a13050402130c20010e0f070518 66
    0x10f078000e51038035111240c2200101104003000d0a00d000700119400801c1c056003600c942c031030f460340d611502c5050b41ca10140c1110300a81c0000700740101070084d01103490070404640e044071b405036502c40849501c080c1901e0b440340420015501160013090215140f440000a00700c00800f40803110f1580d00c5402160225000884c3d149911000a95040c010065440442411a50000071881c0c2d902e80302d6001030305a50000901001980d52120200310030340e445503086421100c40c1e2021450035085858642d01e11070b9401e40c1700c528407400d50100d06549003179074070a50700126000080003012001d00e01291150104e2040e040083c0990007540901c030701c1038040c0c0790341c550f211840c5500340400e0800c190141503106040e016480b010011174050781c48001c04404101c2d200a4005910b02e02441003100e809040c44199148a141a50085400b031300300c1c0111f4500c1004882c24000e0b0b0391410503a502625180f00c9120b0316000f00f04c200b040129002030048107544003241c4011402c080d10048158045007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 833536987 1250 833535737 833535739
    0x7170604090804050301140f070504030b16021609021b1209040f0212100609060c0c090e10020c0c1302090a2603120114310e010f020406020f010902 65
    0x5040045005450160310000000c0c0c0b14030366407401d040e070741e42c0040e0071104188031094120b00d1910400400010090b40244d201c0d8090400c00c0c24541540c0b120b405e164001444c10704041035243c48034030f0307a90080260081c607480084462a0450b01d403050440a5000304c02c503542494055032000c98500c50100d41c40c0b04409440d4129070501401908002c06070200c41450700f003459081003c01010107038214103038403c0340400c1101040601d070042c001c141940d903a1018003006401d000c0301300001c050000e410308480103983e010502034140d03980d00f810460743c0d2640400303103840010b002078100f402048052204404544609000801d4002d420a82c82003070301644d88444000001c0c4a6003000c04904002d4540d42d440c0e1345500c4c0749140c5414915440301000b01d07400c4052400401c2985421521184000713004c0c2d0f00742d114990150f03091180320700c84000f0307401890000c030001544403505600980c10004060000e101b801e2004202ea4001d500a02418005001721000d44e220080305019041d40c19038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 833538237 1250 833536987 833537027
    0xc01031109060d060f03061e140109020711031608071415031305010f061a2a0c04050412080c07110904030309050105040308070306120c0b0318060c09040507 69
    0x70004041000661102011003240d07907940c40080303040303540c3c5d200c410051480340303130000b44000b000d064100620300c4000240c04880d041074040c000d600034881041d81143d030189005605d4800c80d10b4480c200e8200007200e10340511904030855144029840070b0000c03a0212010350301c01c6510b4043c43d8050400c4030004c5034001410448405508884400842c1d000c1b02040c405079070703140c403951124203440c90521000e40c600e0300e0740e0003800b41e01a105140310188841802591810054458024000c038041c1c40da1482d02100c844a43d207203080a01c0707c5070310804000c01c1001140f4251601401080f00d102080c40000e00070400030748844a40400c03180c2054100c102d10404000d00343c10040e03055001030044041684507141440000c01c01d00035180038a1080d1a501e900b40750900c0d00608030b0b50300d544040c19082942ca0480d01169505e1b29542c180d0b07100401c0c2035034903aa45803801d00d80c000503030550009071046d0340810039600314003800b400d41040d046400b40010344074840111410f1742c0c400d0a40210113 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 833539487 1250 833538237 833538247
    0x40b0f060301020a1b061401031a06120c010807021002070c210f30170603070605180406050d15140f0718031e03020c090c030c130e07050c0c010311 65
    0x510000c5a17615014403c580110700e0f42c10721110440e807144203900458016100c0091100c1020f6000c00259120100351400c220074000c070744400f40e441c914145864140561400402da54500c20b00154165603845202555900002d00e04180030359030912951f60781c00b040240181200852280300b6403c250002e04150420442c1d40301c1005d150300e10680d800c04c260b803080c14510015001d04078084490103030b44400a65040603828000000c070300408061094008403003d01019800c031094540701480500c0850200d030a00002c14000c040680000754840d01c4a8007820404c005111801858144e0200500c20607408160000402e98155400d114030700d210400116190f20801e05507440d41d01c00c50b07000300002d40d20744a44141d500c202180c045002940da00000a01da010050600f25641c140c03402d00c06813a06000410039408058142c0410002c000399950242440e400031314050030414030101001d0804e08806400f80c1e1104c1154010b03401030f0049108290302078415411100e2030303a2181450a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833540737 1250 833539487 833539517
    0x120a030f02130b180306040803040b060a0302010212160503040803040f120c091e060603050121050606010305071416060605040b0f060d0e011a120601120f03030212040b0f060301020a 80
    0x1074200703038220314860751008134911603541c08002482c00f45000300d00041d0340741010304142407d820014074040c05203050190800c0189da00040040c04c0000212030203450310110350740c00d2424004660090041e11001c01d0200c0c0004000c4004d0040300d030800300c0c460342203985100f80781c40d47c0d0140c90b0203040111504410482200b0503042012035406c840004450280c4000b000411034800c2d07080301001035650001404408018a00d52144014a52442c2c84040b0596252030ba0f40750000c007903a04040e01c4501261340180196020710740c210918455544418038081e42240700c0075003840c20354551b42000d00c0014282094030440c44441d20103001e003610109a401446078544c044175000c00b91561b144c462500000742071044410824000001c40045142c1000300581c1c81c80440d210301c03007500000c0c010005419106120105203a001c50100b20f03182082c2070541c000d008605110804c00340400401c410010024000b52007030700c62040071203143d21100207041c00c1b40985040302000c500e00c09468440307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833541987 1250 833540737 833540759
    0xa0e01020d0f1b021c1707150b240a0e0a050102030313021906050304051209010801060c0c0b030a020a030c0315060e0307050402040e04031101110301120c0503120a030f0213 76
    0x1903016490303180c10903600280d02107180322440094030041a5a45e81080c82008180340301e80d0100b0410580701400c2140c030307840b0342d00041d944040b03841a403680c84500c194280c9800742030501c00c030595203220380f03503068404101040c0e41c81403102c400040e02441200c4554900313091242c09480041e4010360850380e0b02c2d00b50080d00d00010030300740c4c4d12502c04210840c032a1404178018014080640d40d66844e4106071501c945050390403041c00e5640c000500c41c030151a6400400c060450314546055489210141090000c0e8100b82d00300c85001f513400410040800c11580013040a81641d54003007082003104241201210389080b0702d10700360700341c0003401c1040038401d862090030504020117580047c1c1d5207000050480e4010b0b403103804240070f03600400041c190064214442c0c105040003c0c03080114094040c0c08500c4140201202501c1c00108541445441042074018102c09002c0b5403140d03016180070f480030380010301c1d4400080d003030082014074844103009903a4a41409114040d006040090500d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833543237 1250 833541987 833542007
    0x1050306070f0e150a0c0201120905030307140d0f0603051921030b06071b1e05270c0c101505011b0c060c171602040c0e030708030a0e01020d0f 63
    0x2d44000f0340c1032407401c0b8132001c3c4005c000c240c03419101c00741d040503070780b00240010200c1404219103c2c64204ca5402140f400710031264030608c20300e04a500607032040300c070904034003c8030143c0f588a450b0040c00c040d010741a40c00003040d2400b6000b2110746100d520042c00f80e128101e280102100e84e400c10105000d1420b05013003a1405140c1400300d07070400300101064250b00080310139900301d00d02d0385840240d10311040d6441d0260441e0000b0100c080c03a00205400542640c1c825180140050404152a10b03409442081043c18940d0100710a0403e4280155150450355006140c0d0080c480c0e00f41c518030700d502c5511001d81e00f00f0009400c1d980b42c0b00042d1080041003000303851100b188030041c0001000c80604a024100c030340c8036840981c040b42005540c0e101080c0400740e081c2c8040103901c100038801f00d07416011690448005c60020448141192440580c400a5800d40304080c0d003c00c0d0580044042c007102902d03035440000740803800004a80d00e0012040704000f02c3d02d00c00140d1401c5110f600303526 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833544487 1250 833543237 833543239
    0x906060906030a020a0315080c0913020913060c0e031e240709050a210213110d0e0c0904120e0d0809150f2208060c0d0501050306070f0e 60
    0x1410182034002040c002d50044460141035a0f00080c00030303266801d03204009003180b220030070760803083c180006140e036448600e600c0b902c80c0462100180034803141802c1c100b010741d4040c2c113050f61401d044c1035207110010400c004403541c034184425003101512600411150600c000c004007014134101404803521841c42250b00e01a0040c0601070010310724000d51400c2c440d1900c2803542041c6400d25000301503d07890b40000d485060641e5013004004200e8540280c01d91485642d86110049480000e2901c242c03030703150300050b9081c03211040c1024040d20142c9012800903c05000921022402548490340070840c0c0354080120008113010035010701065001c030300d8901700134400c0021900020020b41103100c2c00c640341900094200e500d800c0404001c144207001c006028100007940c4512001402519100790a80c405040101f0340c0707100f03031600c01c0010494617060300c00702d040840388003141c0d600031014001214200000010786080006409204030000e41e01d1004804c442201295040c01034910030f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833545737 1250 833544487 833544499
    0x11b0b060607050f0a140114152101290105040312052701180f05010c05010204030f0605010312050703021f1526070f061b080d090c170c0906 62
    0x480004030100080340001d5280401440d0003080c920744000e406c80c00032500441b42e418060244106600060f1264028421341c07020503c0c3c0d41003401040c00c035400421420384038240c40e000302d40b10960641c0055158880043c1c1e0742d4054030f01c05a51384650600d0001e5900280c410803042002c2088403251181002203032030018034240612034031b4909070f06640d1011042e1154904030031f95540c1c00190844cd48034501010000282c5042110181c95080744030b59410300601c41618402c1000230b42c1207034095540821140b0000c00c01d8101100242400d00040350036401440c2d00c15113071402102582c85003645940109a121b01d131a121a081d9101c50340d00504c41601c4202003403110900d881044064060a054061805070100f8082e005e46c2c06000900d40c260030218040c49074541c0c40b90b0110a6426901302410042003401180308410b1004101501000001c500b180e204401034100220b41406a010b41c00025142e1410026000040e030407118582d00c080c9140416081400f0794651001008084d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833546987 1250 833545737 833545747
    0x180f040f0804061e110d0503070c0507080d02010b031c031503060c0e030c0d1509032d02150609040204050405010b04020a0512091c080c090a0b03040302010605011b0b0606 75
    0x810710990019080440030450100c840322400c2c01244005111084515107004601d0340500801d0b110803170041c0140070804d0010009549600a003014070001c3e5010007202c0c001556403100e00d4503108140074280c01035003000e0000e001850f00040008050440c0d1110400c00060060140c0c02040104c1024511000c440000400b00f00740f440366044a074102c1d200c00c1800c8407144101410451110b21403072040d4030f500d4048000c10000110b00c2121804c180e000243c4003110305060714020085824030311119442844000880c8501415600034202030f004c903440e1180d9803595903030039102140c000d0340017a10760340040d000d40750075006640c00034021000000c50400010208003a64048803045003c2900080c0950b502040407000d1a4011509405002c520f01c1d0b485101c103e078200222034400304196070f00440d4401b03c0c988200d84144500a2144000540e40c1c1c4108115410842c2c0903400b552801000081550040e443c0240a05400325840c00800e40341e524400030200140602e41c01c4042401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833548237 1250 833546987 833546993
    0x314301f151e020102030708010b1e0d06030b07090602100506090712060504020f0c1501061709010b1f080601020105010609120807020405280b0307140f030d030605030c180f040f 78
    0x12102c201c400d80c2c00542c4d0b910b092040542031110690000043c80e40810550155040b403810110361860000821541c40c00507059181c080d080540000d40141c019005000545401c1844481150890b4080c2c44604d40242e2690044500440d20381c2d400000c0500041c0c503241c82602400d0060340760010000303920f0f440b003004c03c04a8001949000c0030f40b10001d02c5110015080102151018110000c0d080540c10442d00034200100403411820180f950b0b8081108810300790448141a100039000064460030520762055211119418001058068011840551040c080ca9050b41c00035102c4804291500d94180c000c61340d0b00000342c41c01001400004010790b50350080314021800365808114080884a10800c1c040369085c06401d4a85440100d0b034031600c012510030704441e14288100001c0b9078001c0410003401c0300144840e414000d01c40141241a0507a01520585030117030200c9250a00484c00d10840202c00e038852644112108000381e9000d000341c0300c0c0307540315114500130070410405603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833549487 1250 833548237 833548277
    0x20c0f01020405010e03010e033406051e0f0f100909080909010807030b010e0c040312020a1202120d0b060702030a0602091017040314301f15 62
    0x28052555036500028100302c0f0f5a03000034600801c40044000300040654a00b18030341e02d20900b0f0080d240b1240c03000c00404000503010000e0000c40141d0b0b05426006214500600181002c035040052a0392583c400103020100c0c0044c0707489410a1041d40e00c4944a28181c1d50010074000c1408810468800012640c0a102e00407160a144540d5001c1d8940f0307508002c000d0041c40503002080c66902208040001c2580042c4850450b0041c81e02042d40d0b44030120101020301c07640e08044c0003000011903258100d40c1c00202c10080ca40241c81c07482c0c0161540904030384442c0201c05091810a0a00c104420007031aa4403050031441c0061001d440c003502d0740e0100c2c1c00c105000000303849103039010072404c0c0c4906001c15002e0a03030f100d80c608a6190603070360b81103d0700620b02600c041c04100c03000100c030326000d1901040710544101d040145a8502001104665030007804040849641c148008070312460206609216203404840ca030101c85818007a80810b000c010129400c05c11021390040066a2940d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833550737 1250 833549487 833549503
    0x70f0b120403321b120a2a081e0903120d092922060902220c110c01021c021504030306091506080112230303041a0105010e13020c 57
    0x4000d204c1c4c03a01803010b0300d446618041e0030500d69a80114511032420040d00b022501000303060300f045011840b141038030710b108540701e117500d1040886810310041480401d0018080c48001507070303c8041100100250995030055a8019030154084040d40c100040e01502810760f0400d50040014820b10646a440380c903213502ca194102005c034248840311083c0c00103141944004d61800c0e088241c11041e90100f480016248003506842d030701c4901c0011551030001103680d40a240300a455400d10310300d244e100801c10580c0803004251030941e42c004115012581e5030001c1c1d4140c01510801c403907502c0e1100c900b0500c148503001c500864170f03007500b4810340a048034080d03070203036900082450601c02018101c6421040843e25001117010801586078042030f818150358000d48600d40069007480c2142598030810200748c1c110004404500c40840000007451085000c1d0031030161340d4843c02d8440115003020701401c0c3c0081d046507005c175514203060105919a000c140001031501203a00403241c2401c0c01c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833551987 1250 833550737 833550827
    0x16060b03060106031e05090d050a110d022406150703120207081b0628020706020c0f0120090103021806070b06091e151503010602070f0b120403 63
    0x502d240981081d08800f400c0d405050171010100311600b0701a00480d80e2301c030005541000c0100004040519900c50061b1183e131030050011151101034100001c0d4442441248541150078401d4000d65a5080d10750aa13005030406880404582d0741d01e2006034203940404002c1c0c09203d4414420208500140f004080c40ca0042045588441c11000642400ca9900070b86401c240d010900b4000e000040540780354003088425040e6040b8180480e200c40039001e101005480180301081e04c411056012408a00d003c3d0848020459001d8841c10781c036401c8030701c3c80e95920b007080620002c03005501030340c003c0c1040002e5074191142010321000040c026413001c07404541c2800000309108003030a0000c0c81c2a00495180154100a0032418208003c141c0080c0785846201801510b5031282d1038417640804160b51107a4403550329a144c000183d44c481c070900c2440c030341300007008002488940b04001d139070742202103038a40041c41d00d42d6201218003010301c00700141e0b0b000c68483c14504201449500e01380318a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833553237 1250 833551987 833551991
    0xb0a06030b04050f04031b05120d090c0b0c0709020703091a0730180e010303110606030313090b13020406030c020f0c09010315020d11042916060b0306010603 69
    0x10381c4280000d480780a0b00301c1c1d1401c1c101205000020350000740c0e0303c2119080801c0c005c03030400a42030032841d20b4541d840500304007000240b901e00c00310241e001102c503640101c050031015540c80b1229183e40c49060300c80141500070300c00034481004940c005040c002d00a10300510126102c00210420340c40d103404011070300c2c40010303034482000740010200f0700400c03030441c4007142d002c0000200c02102c40e0010380801044020410070110240e4082140d000d461711100e003001540c2c4070710b0b002d003090100010340c02c400e108280c0040d015140010844450000005020180300d241950303042c0a0314010b01c103203520000400250359503402d64400f40c0001d04580c0d4022803940c1450354040e0400d00c0700395600d080ba0b006021000038980300d801503907044943c4001c4401800810702c1c0007400274080c03404a0604681011101900415044060b00580d4880d070f00d840c1c03242480b41c0b180c20b452001c0c00951480c4403028041c1c011135951180144c03c0352030045001040c140d980c00002401e20800742c101d040071a03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833554487 1250 833553237 833553251
    0x40303020d03060b0301090c030608030a1106090313090f020d0f021908090a080304140304030c0509070c0b010e090c092e1208090a0905090703021f120c030b0a0603 72
    0x16904012014055101e070404121807402d00502043c5480140584103145e501c5081039130015200e03521010007010130000313403611a503c080000340103290407038480780d461040102203003880101000b22083d52a44502c8082c006141004081c050b00c0d0441c0d26000f0190f09100d003400b030b0405401950f070704c0c002110740143e4501858a030185000a615030034403c0081a0f810441080c05c0002c4035507e040c1c02c080b086071241c0d5140380c05041d00c000c1c40c0440b034160002040000821210242030340a89408440c03418142e640c4c4c1c0400c6507940d902202c00350100404800403c240003000a415400400c050240c07200c42042e40049550b0000503100311110300b45079a12441c03e190504c06002e031058004481400c01890200c1100c40c0814000c005800ca8800194a4266503100511000200425032044c80307985804d003a400d442e4881d03440160301400d04103214561012040744a503000845944842085980180a1100902102c2c00b5402410303910302100c030b103544e0381c9400307034005018a6401003411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833555737 1250 833554487 833554493
    0x180b0c060406150b0d2c06090601150507022806020c0f04020a02101509060801050603010c020304150c23060406060e0705090d020406030c2c07020606010507050c090c0403 75
    0x12181421004007418101005000c4203680030221000b209080fa0003050418046d05400c10165038178980d09420070040c130007444108004a0114855039443d400e81e0043d0b039031480220f000141160355030300022420024440140380011a01120003408000c00602c07000622407801d14000e01e800107000b40c0e024019a490034500034030301c11a02a400e443c00d40c2088030020020396502c49151001d90413a80b909207054807256aa1580c170001e040703004060140035a1503101e540205801e07903403a8025403d184084425500000880d02101c100e00071075104080c84880445943c0008001102c46070b0078030031221405501124084445583c24001d4141c0c0d0409203820812075203940d1091003e0f800b0803003041449a000702c203842c1da0800540324031a40815920004004000d1038000414180c28401d000c00c080740c080203092480380100158149103580920030801046003145c954005030f10140004216501c50800f5103210381c494000c440d12030300c0500000f00c0c45002194100744110010800f0014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833556987 1250 833555737 833555741
    0xa12050c060f0c06010f1a0d0905100f0b09040224070c0303080601020d020a080406030504020f1203041e03020a121b0308030609010b0c1e031e0306190e07180b0c060406 74
    0x4045051044001c180f500f0300c900354011110b031341ca00c0410004070f0380344900d08c041e420410015034071600b91580c1020095407a0000d280c440c3c80b600441e0710f0002441043e08068250382d000d681c009100940721241043d805807100d014100607445000148282c10000b884d0f5480c03d00030318800e0702c6050442c41d10f80300091410b1803100c01801154420300f0308034041400c0070103d0b0141c0f5140d240100301991140081107100c8180c080c0d0540102c42419803c5800c44044050320a0301c16820080400b0f00e20800c1c00c620080c498003000c0e50003400100704000c45514001c1a0071040e201c0c60303510640d50b0015048811941199205913004000041004501c0c607003000f80b2409806816291414801000201c550711040200f002d505500d00710a022111202001a140810b8821b000d0502801084030b4901c442e400981f45a030080c1c2d00812509482080055102c096400c0ea1041c0941382e1f80750f200c2181e402c0b0032200039100510820002145440a11004155803140340b4020032140c00d1900d44182 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833558237 1250 833556987 833556989
    0x2040e0303040b041b15031a04060608011503090218190e210d0e07051203040602211b0d09060305361f1107020a12050c060f0c0601 58
    0x480d0410400c0000043d0b070000c0c1140c006400000000340214565851202491070b03803c5075050f62116051072002550503000401344248095500300c04030500d00600054858074001e5001283d0100014086100c0c451781c0c42481c403080e4035000c51035800980200b09442140c45805d00754081c454204880401c400080001410182c203040082e041c00c0d02c24aa1680343c0f001c010f132002d0640c2c0c8148441030507a0000d845140541030b40800903801007031800d80c3d559040b80314545c01b0f0200d2421302c8258403030110958084800303a030051312200c400c00d160390343d185c0224107108030b00c0e64041c492105609050030254035400c5102d401030142c0c400000001d084000e2582c030403c00c0501740410800b44044505c1450034420040e2119040c52688900b50b000f1102c009030b10380ca052084c24589010a200c90005110ba4113080c40300300280c482d000e20990b5140310b8444007a400c08406a010405c09040f405600c5c1080d0090041c1c407810b50350407000490a90000d401d104804401244d44d01000e002405414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833559487 1250 833558237 833558261
    0x6030a0807051c17070c171813050412120608071d090f070b1617031803040f0b0a0512010b090a0815060904050a08030f070e04020702130c05070f0f0204 67
    0x429500d54028a00700045130041c4031104000d4003c0b0581c04200400c4440c12800d56507442a940791444881e10b50030801007100c01e24459219900c44503100c4aa0788119406150400c00070444030230310410a481d003c0b00e01c580c00b440c280d43d45c10700140c440c0c014807418019044605180c001d10b030503205e14401c070382005440781c402600031800d1691144070010316281264034169542ea19001400482002841001c8001d001d030082c814000c41d0101c0d400005512641d000208800110901e9603101e40e280120300440c04410001e00c02408001e040601a02c42c0301181d02d015460001c05100f0b4226200003a404940c3c18280850418070618101083c040500240303001480310140500c010f5074001e90141c030481c040d9191002140503c03000744030030074407a41c1000d0400d82d41c0c10072011512001c50120741a500290f110802e168140c030300350003201c072001d4004104024031900c03114900c00516000800c1d100f40841004064002072502210711580360080381d50941e141e445005000585500c400b0714 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833560737 1250 833559487 833559497
    0x307080601050a0c0201030c09170a02031903020a0809060c100609060504020a0804110402190203070201090f0e180c0a06020309040b0402030c07140c090a09030e0f0d030806030a0807051c 82
    0xc1000f0300d912800403900390b5024a00031038890200201651441e00c0c9401c0010308070003641055030448800146648a144298201e64100d01038003d01450601004030080c0141c100011800114500402401701c25400800c0f99291140301c40303d65103000c50801882100c291554030170407801c0710030b202d048002c2500f034034150b10b014140c0d040100180c600400c01089d12411001900154035164192207002c4124000f044e4610104040a581c0b41c00c4440d04a001a103480700224112400d41c4807613086481002404501d03480c1d10802c0d40645c40c0c42c0110000703030720981c440349880e85e861841c84030040c0b9880d009940d03500101000e11007a201d023810a14000d90040040c0020381c00014211801b240d0400e245400c905003a0b40414105040c0500c00744d4029405400d0000399031580d400611201d00caa218907030401001024480c100c002c5101c9990310019071074481000c240220406540404020142c820310750380d542c0c904034540c000000903200e80c0d1103408000320403560603d01861041180c180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833561987 1250 833560737 833560747
    0x50f0a0f0f0206011401050f0d15090b0d0f0818100c0525030311120706020301090b0f0306240604030302030403030801080303010f0b0d1503060b030c0105070819090e0c030708060105 80
    0x1080e44d55184d190038650410400083c0e00c40783d144a40c00703449d8901c4108409002c00513a03100b1080c1800309a0003030354040e514089111076145021110710b4171060380b2440c4100d00c03014940f5010074075080140340012422050458400a90341c400c000010300205465960300201c59050880c506000c40c8414040302101c503161400900d1002240c0741141e61511700324591060101c00b0508200786084881a030000100c2c42404202054010703606035600503804120641c01417003040041e8007200b0f52240c240e084180481c46c410703000c004041c1070380c1031031112050418030301002c1059030b4080d9100380c005030000318091041642c031039030305d6004100c0d07003000b1415541083e03101c026003604c500c600c280c0480700080691080e07081341c00504500c400d0440040741e40d503590600101030201c0f11150341c071038000c54203080220342c05402540d0804e80c004500d0f60a2116882c28800c400c1503034009c1b1000d020b8000313000105c0036a09808030f480741c14407802e87c0d07489050400c8060301106016007414148401441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833563237 1250 833561987 833561999
    0x302031c021501230d0b07050d02091324030b1609090507030e12040605030c030603070e0901020d060b07031707110106030308010f060e060409020a050f0a0f0f020601 73
    0x19003810410108030290500042440e0607490034408071400032601e20800d0000135103558006000080e00016410240d0848680c0c0400240c42182c083c02007030303010148046041240305030040c1120155985006180008042c00120030f4103103080640c1805490307c0c0040030102d411035001100c0303007406040171805e80c1940d4031401c12100041054280d1304444513461510b62180007800000c10f9910340c200500d05040c60300130042d000c083c1165240703115000302000b40790424011581192003980d0f445c0e0031030b22087c18030070490f071001e40346940c50301c90140d001c42c600942e00d04050080e40507100041c2e640351303280b810505a81480d0301403102c4001c144044400b094001f140c2c00c1d104103040351180c559580d05103060ba00d0101149444040e90310384130010040541000340300f4142c40c0c1c805112041c1e00c0d0303105000c5030009011050150059000c0c041084480b07141d130013900e114003807400c0c8182002e21914020440340c00581c0c0c03100018201400e804802034202c3c40b90100ea19491003d08510741c1482 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833564487 1250 833563237 833563243
    0x1317060709030b0c120c0a08091204091109090c0d05070504060c02011b0c1d06030303010518090a02041b1b1e0213090507170f0c0108131a0a1104030203 67
    0xc40040c3c90030b0007040008503408480c0c0d04880e0070101c0c14010038090f040c0b070762440d0f146402c4000c0b20b40c040359044008c1001458001048070556041c101c10314a01030401140401030040380c0d10714201000180403088007542d0380100c09104520310300c42c10384ca40d40001d0101f0300b51240030b4101c105120b0200400e01c001603100c0c0d105101c0d95020b081079a049100b07091950410131966001900418031141d010400e070441c034100400b0b0700715003000756840c0c1e15142e04054a03031100f1b100e802e6000e15160f804000840c40032400584c8114104160303202901c080e00880d003510341ca884550684211240c0c00c860701500850b101c0006500700e1001c8861825940d200440849151041d00e0820b5500c08040304564501d00e180300d990000c5003051052a680c2e181941d940c4807607004d400f4103109032032101e49030701000280c10761900743d80e07600410540610100650310101c010300409680d041500c5544041001e80c00410711196600340c2c0040149030034410074048030000410034070301c0e2204000c100050390f000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833565737 1250 833564487 833564489
    0x30c0c12030105090f09030702031c11060114040c02030d02191106041709150f0a080708090a1203090206131401050c03040b0d090c0611150705030703050406111317060709 75
    0x4100b885405469011b64285980074400740250304d0302c9410401041070140c0a00448109410340340c40c8801c0121381041600c810003401129564a0180160036040c81c240d040502c0d4244030b401503901d412240c01034141a0382c03200b9130804d00043c0404410028030b5214044440010100010385204d09003541d81507203c000208050505041c08914108590364030220048040040300c03589503615000e0b03150000743e8101072101808500740c18002070300f460059042c00e2140550328081c01e0410722654405900c03807900144002015503071011400161111030003040d024180c00e214209207450301e241032441c070280c4030741c0d241006410f00c8044144440041550b00703550041250320380700c00911003000c00520020310050489590701a000a80640284007001d56200c024203440241203030000c0b400e1854001d9940b50009201040020800c5109a001030b800c00d20481c404a120440c01d61280c5040c0c110721002064540160000c200c091208940840f040b0104400307882680362811000e00389000c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833566987 1250 833565737 833565751
    0x906160f23090406090905010c090302031507031103090616090f06110c04051008070b030c0403020f0d0606060504050102010e0d1b0c09020d0f050a0b03070515040902030c0c1203010509 81
    0x120800920040001c10640700e806002902c1046407564036104080580705046081e102c0d9481d1020302c40956102c2c0c0c09190903a070300500104003124029043d6111542e00426083c1016aa00c582c20500343e00711005602442600300100b04504100031380c801001c1003e1508070902c050710a0420407035021500e040100c0b0a81d0a10303004c030406950100d400d1052070608079a1040c034160400140f880200604030551301503400301c80b1019100d5400500b13511054908070000507082c071040006141509902607284009090341901c00074641d41e0310180d0300300d078000d080400e1000c242408556824031442500240301002400505500c20000e4842ca050140d00d044034400c1e89207150034000440c01350001000b03101001c5580d00c07204041a40101031110090804500f403074085100c02013680039101890500038081d1040500d00f0301084006402181e02c1084404284000a45c181c0a031020303600c1607216028150361011003101843c01d08444000c1c01d00304203000c0c001031143c5d40b81d04142c0b9a00c112 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833568237 1250 833566987 833567027
    0x3010204140f01023013080d091d010e0a1e06063002090619020105061804020f01030e011515090f0b03010b0f0405060a020a02041503030509040b0a05090906160f 71
    0x4c5004030030f040340c800c50b105103100b03a800c100c000810040001e40b51590b408640c1c0c03166041525910880042d0140806200c1801188ad00603c0781806181c0e100780c210300401c40003d400342540c0504601200100c601180c042d50302c04003003000542080302e65003a60340542800c4c15040c03460804c03650f8100100d114184155002c40c00b800c454136403004817115480a030308032000c9604080381c02801303071200729101406290700e84040c080d61074010605030700466004080421000481004500600d88501b40420340e64950440b5810880103070904005480801c0c42e00901412007440a41045860ba012800c0440900001c010b010508000e690640e01420109582c494204071a40c5050140350083da0780580b00040c0d00d8030f6a5000200002003a2094400780701c008104100c1d101d02c0c1c40701c1d11028010500c00c00000300b503864168040041d0000c002c04648149845401041d940b040031540c080081d44000244128007040022840da48040c0b854005d4010321a0b079401001c0750030443c0036200b810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833569487 1250 833568237 833568313
    0x9260d0209040605090118060603020304020609010f0315170d0c020d0b071211090a08010b03030406050708040f0e1b04050f0f1305130218090309010c1103010204140f0102 75
    0x981c0d0b42d00008010140180700126a50b1107800d413180225142140605051402000058041c00389c02501e10445d0001e005074102078151005641c010199000304040640c2c422203010040e1028003010041d03c0102e50303014440c442183d40e20320380303d041c22403041481034501c040401603903450842c0035072552040c82205030b515080c0c070560320a090341c03040340e24050070f2500c05050f41081001900705807000311410221aa03641e1030490880d06031300052034041e0010001445140e0083c0001c144140c400c50b8182c1c5040d95130310303000f8036194003a04441000b9041c0b41c1801684000f404694404212040034640f0346031515001400351b042c1482c00070b004070400d45e125410791791000503402c031301802164280310610704643c0e41324101a445000f203119229000003c0101c04c06486203e00c200d032150000d600e810090001515440c034503c50880d0038005011828500361001c1c005000109020000302501d0414841007000340d04014100e0742c1154000f1503200203031240e4a1201d04a42a2000384110704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833570737 1250 833569487 833569489
    0x1406040f1a09090a0902031b01082220090705040f0302101107080f101a090c0d140a0b06070203060a0b010201060909141e060403051c090609260d0209 66
    0x10300030b405200e5804030440c1d0422000c1881d44c1c00080903188220180c035003601c0c2e04103008001200018209000841c01000100b2912070000e0501c100c00302c400f4810f600000541d01d8a0f4040031100d6a00781c0140810412966410b00040300780c0c10418034200030382810304100311003c0500307052001034404c1048103440031085004030280002d03104030600f650080794035511440e507a00c2ca9030082c1d050314855054016009102071140c91001501d1001e42081400e00c082048013081c07002e410700000d00300810818007110b13038500c14885009000d5502520510300308250104440300a00602d0080e40e003000880010b036400725449500848600c00043c608000100407401000c086c7c001791038141c641401c040038464400d003800d1f2290b03c007070101c420b0145030140d40b1307032a00b00d0303018000a50341c40f030004a000240038002400ca03040e1280203034250040070304089000e1300c085203401d54040d50780741e4650007409a05048030700f01c01105441c80c1074140e4100c500b40002e105405001080390b6021402c0011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833571987 1250 833570737 833570789
    0x30c020703110d2d031413030b0612060f0708072109081e0301031b03030c0809040f060e060a0609081e0c03030408060a050603060c0405010804061d071406040f 70
    0x3401c0340006420305050b00b0130070024070728009071003900881c0d0360000d00541c2d5280b4504907034100703c0e40c40c1c00010007840c544d82e20300c40e03a0300030303103031540c0084051030301442e101e020080144600300c298000084c41c105100d01412006020780940c08000310b403003a81d010f0310302403001e00c1400f100300100055041c0d0b484c06e28000b0b501580d003000400046801c91682d61020a602440c184c034002d02d0324034003410f151214404100c21a10004010800d00026180071030600400382040c6180130704040f9450708841a40320803101c00ba080240044489004d00019003009800030000c0c01d0076042020780756042500c0c1558940780034040c1c0b40e000b00e090301c0306000d030722044c000030502d2200501200c0e107450310b03032040e16180c05040b5201d0640610b004002a5546000241e00b80600c0311601c51a203404e041100444100383c005000b03072185510343c640500c91031405a00140c1a5075560090651607082c0b8075003450481c002006244541c00500c8140082510124154200d0f03002d041e00c170f01101811014014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833573237 1250 833571987 833572013
    0x306040b0402221d0c0f070b13110d1725030206190c0e0607050a44030105010e0a0f0b04030b01080d080604050711030c03040303030c020703110d 64
    0xa0031a0000c83d1664030180c091041d10100301e1040ca03c0700c28503807506004010341c0078989194281080500c00b152000742550005c18101403020702d00c83c9420030030b41382c003003018000752000b030504c0484c80440303014000c4400062440c030030300b1141b201c140f8420f49c031001300b404500d152000c0c1154002440c000b8074075025180001204090108445061312814060344400007100c403402100804804000c8440355441107500b840d00d103455510f00b544100060244540100d042101c16108111520300407659030380200c00c1c2a0703440c6070034003400703500001105444000c43d001c42826000552841c00c09054500035241500c0c000c1c070f0004203954280d00041c80841c0603900640c0b4001d80e00c500410011001c1c070061003580d02405011442c1e076a581d0205540d4010ac0c0d00701c40000d60400013041c0b10346055007042d50049480d161040c4e08446c203450250640d44004459101540009020000c2581500030036448003924005000203d1454035030072180d09210040c1c2c0d1090902481e6981080ba031800d40345 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833574487 1250 833573237 833573239
    0x40c0902090f121906020903070b0403050304090b0109240e0307050a0302060706110a030b010e0f010f030b0301020c010c030207050712020a090e070b0a03140105060f07020d05190b0a0516050406050306040b 90
    0x4032400d000d45c2441c00003036120b014080d0003806201d00c042801400c50080310200c070362050095260034603000c100c078024414069014104400350704002079007011001c40401c45941c080044621368000308014210b5616145558001d401a001c100065540c8181240450390195107a65545403a8030b0514020300102110104144000c141c6510290740359100501500d402c0c0c03248258a801441003180c0325804e01d054034001481e090480205074841d40182144420150001d418520140394403800d441102041d040000d50109424084c004204200c9000749041c400030407003420341c2e4010440010303940c0903902ca1903894020b10003001c072040000380028144c1020258894511610040240c0a4010703c0b44e0409125000401c491900c40125158480100d03011480c000555083c40101400603205841e6030040101e060101344840e0707440007605118a00c11515490b1141d07081d0120744020f00303103219100810072a2510310390040300315025182c00c3d0502c0e6442e40e940400040c043c200b20341750301e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833575737 1250 833574487 833574523
    0x501031806051303020c01090e15011e0c02010806040c0c0308091c080105040e1f110f0a090806070903150207230616051602010302160f0b040c0902090f12 68
    0x104441d4100c003000d403c80e1190342510040210b04004480d105910300403841070000d031502003005508082c10740c4d074034039006040c203c01d068100d41091045000151010b40440d610b200340008560340050790b203600400840b07082015001e40040242042503c410050a000c0b840f004141c0340300301001030079900c98000d8050b0090801d55800140410000c0c49a113000f241013820001d018800811003a000082c9410007540e1349070f4010700034000c2e00280e00b084130341e203a040200510b42c41d1204000c002c0f001880c1c455a030120701e820080d925000000b082d203010400710030001d01c00100030a00c68500c0390b120400c09a161080c0f4141070304075080146900d00700d10800601168007040104003a0b205100b018040840000030703610980e164030074110454503140000b1041d01c01507000760701520f500b031401c00e00c00a6040441d51042e40f495440034003a10441d0461081004000055002c003001e0b00428200f9810104c4142c0841e030b502d009110702e10b11074001000d10070b5441100300320201d05580a00d6007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833576987 1250 833575737 833575741
    0x60609061b03120c0a02060708132319330c021b010c05070b1b07080a0c091815020d090620090d080c030415031e060807050103180605 59
    0x400707075282d0141200c40b080f4030302400040d24681c40f8006845c1e8030250740e0060081940c680500315144000140741e5441c00400c101c0c1c20b400701e1550088040b0700c484c108040090b00768a03815071464283c24402005003003d0004030400014036074070082c04104a4640752140007004602c07000e04a00000002c440310600c0e05286070320865000821082c1c08220341c4d840e5440c0420100111120160290081c010307620a450400451104800400c80b80c4007021201400600500704942007000d264441d0f031460b03000c05248020b204080c15403000034801c80c03600301b00c00d65a40399910505104070300041c00c402c500c83e5140c1c078038482c943c049440d006030100d001c10030402c442c42c081e401000b20383e0300d9001500d84108030440100400c005c07030700c46140c0181040100c6045039110500350b40010744400c00e43c003003403000042e084042c0d55011410080c948001c20204100d090150040c007012a954049605121080100c0f03800480c1b60410b840b000e181c0840c41c0c9000f041c0c2030158000400004007200e1030441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833578237 1250 833576987 833577037
    0xf030b060f070302101a06120c041716060305160e030c0a091409030306060714070b0703032405060f0a05040f170613020a06030914010614040612050606060906 70
    0x280c0740c111520320aa0400c1224007091280341b071440e031504102c1d0801c50030806100203601e450084d5600954003440545080d1720b407100d0801c602c42080d00b14540740d0103030740580104051040c40802400b060300d01000b0518000160792401c2d91035200348401e01845420a03400c6403030501ca0755800050252a0341103155454070a800208a80d00551149100c14070214a96900102c212400f0b900010501c1d403c000c0300e51290f00c000036518000c440b040c454094005060b454020241072454020f8400141d4043d44030b0040c1c0309294010181c0c01d203512004401d100540e508402d98403401030030942c840c1c44540140043e01d807031290750008008900702200004089007448602da07403441c40e0b03900340c0d841a181c81c905411800d64006009500c114460380900c4050300c80d52211702c03224010702459000114401c001d0382180ca0541141040d01819500c6100504003801800000d0104450280903103159888940d1150310283c82035210300400a4054015038036441a40c43c138004050300e403021451004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833579487 1250 833578237 833578243
    0xd0212090f0106090510210605090102090a09200d020f16050d02072102010917100b150418060b040f0303020115150807111005041109070f030b060f070302 68
    0x14840030829820040e001c2050701045c06401d000b280d0802c41103880038180318040045041482c1c9800840160008101c0880c200b8041c250146950b0f100041e41e40f016641446484c02e45904081c29050600c03029007408511820400c001d0364103a102c05071110116002d1001a1007411b0742c03050700310408104020000c00c04ea40b1000307a41c1c0b0501c02c8643d00204d6510603078480029104504010545015040000c403402400110745441490002c2e030240e1284c0c4030004611605201d03400036842a042510414914070074940030440440d07000c0314451502c090b5000e94030035806445100c00d01000007180b00e4503d41c00400c0074107100e00c500d5403115110342c0842d1486116100583c010b6091030320700715200031924802d00c15079010b80c8200440703c1d007c0c2c20a664145003d801c0e00c042004c10f09408140840508c0581c105400201e00801d80d4180f500702020400c0b10888086e21580201c402d000c034054001160500404c01d6040c0070401e4100c03d00021028050380b410101c140800084507010982d001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833580737 1250 833579487 833579503
    0x405030d06140901060801122405150a0801112a12070510020f07060c12060b2802150c09090f0901180209070e0a0b0d06060f020a0b0c0d021209 63
    0x5443c0042c003607a031140700316000c8200b0b201e000b03c6580140e4400c80880c120941c10011903003a821407090a00c200550751040302c1084840038041082c96011900a10b000c0e8060001000200d00901282d0a149000c010030310a400707184181019a1450947c04101000d44800d10141c10b4141d511083d0440c2003400d41d80d00ca0603084945000740780c41c02d24424030700e10a4a410a503001030050401c0b04656076540104280000795043c4100f029082600707030540d024990141c40787c803030290f88500118403080c070803400b4404c0b06102584403030604040c01c1d40c0040c000b000340301c2e0b2580c00313141038440c82a8040d0900c114080c0a03040079901040010010942c003d51703010b652108000c104400140c10513400c80d208440d00298070440d18004aa9100d00c41d106071550107030010300d125201503680c41c45005941c8402046500f445d11500100011508002a40d61180041c005401c1c403080c00e03500d181001c0700c0209103031101e00000c103107603c65540950540e40300f204140382000c41d9041c4000b0440daa822a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833581987 1250 833580737 833580739
    0x30f09040f0e010516090315050a0b090a020406110a0209160504080f0106051c03020a08090a091e0b01050304050a03030f09080c0105061203120105060a0c0507090b090604090305030f0405030d0614 86
    0x5045d0030106151040b91954112074014a0045901da00342440c8405003002810000500741c075a00c1c591100c1d9103200502c1d0140042d140010380c0e40c2e1401034040c040300500d50780c814240e0030000407000941c0b5001442a400480c9041001002000c11019a45030055800958041c40b61b980c0708a19190158450000d5071403c6481d41002d174030f150860042c01c542c034007000b8010381120b842140081e130290054145031500401c030402e400d07107a1258508031000950301840b0000520004102c0890307911500d22104000e1810515500d041e0b110750f43d81d000801070050815517520121070001107594025040306034481149560b4130072643c03066003e1302007581c030b040c401c12841c0c1418000308000001c03103101c20007008100a40ea0320308020040039030050714010003444440d95054000617400d1181c3c5001d019801400151614180709100441d00001c0442d4000da02d801c541c0c40c0804d030010b082c0d0b0360180780c41c80410095601d078501a81140900048403009608081000c0303612f145000031140c220310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833583237 1250 833581987 833582011
    0xf0604080c1227060f1b0715020105040611030c1c06051c03030b09060a05010c0503090a030c1a0a09121a1602010b06031b0d060b0f030603011409030f09040f0e0105 72
    0x3100c070100084e0784120451010310321000c01160003a0f20186000c509006030200580d20119502e51800c000c4407239030704402c40141d641e5001c00007042054407a0307811204200b01014214a00610300c0c10880c41150311040000c0c3c0c0c014500c4c1c1c060042c5402550140602425025070000d1003554030b00c01c00208281100800d045c1a2a02502c0c2401e81d500c0e40305800c01011a1000d9260400540d0070303101d894000e54590104010312025911035405101c002c1d4440c010400c6241d24204001080c03590f201d030188942442041202035480d0f000b1848002d4a1039900c188215503a035203413560300c3d034038907261044001c601c21003003010282d54846c094503c0c4030b064000f4400e03007100004220701da1200305c4095003040307a00b008407141015404041c12005041800005103680c070f62140c0b814507001302e9207a1a0b06c8000004110301410203000b80c3e107201e0440c68459485081001049440b401105104c4d01404004104940036588542000c801211082020002800c1c881d1145001e0b000848103c0c074111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833584487 1250 833583237 833583307
    0x81b040f03230d0818030c010504050a0b010b130303081f080309100c020a030f1407030b0601120e0c09100e090709140702100c05071a0103060e0f0604080c12 69
    0x60104591082d8156a03580e4881035855454200c4645c4144540984601c4140410140302900b4070680e80664061402030a4240d00b51038082100c3c1c0c8140c07c050700c01c0200740f0a108186002003191010b59905040000702c030303918010741242101a041e02d000f00f140064900140c2d11101000503e0040c1081d00e0741c00c000c06260409442c440a40c20000350005a10340c001c102060002600503000c512070312850385516a82c403d42482c00d0302a800a6072a40801800c0c04800e40e04a41440d04140380340c24240140409220640e4440e540050b01d1402100740e44002021030502c11440c2c0050030504196090750f040003441d00d42e8541445c001e0780c885c240740224070407444c0c0c00782201d184102001c3e40144020070360b10400001401001c040c840a029040c03100c0750004190141001c0d0002e030301c80c42190258503505211040d50304109840590343c1000e140e0320f420100c041445a4016001041075503a8194504c80307515100111940c0314001001041c00a0001c0c410f801240b01c515024240030400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833585737 1250 833584487 833584553
    0x4140a061d0621043002030d050c040e0906010f0e0402030606101103071a1b190c0c0603020304060f1a09090f070803191d0111010b0418030206010f030201081b040f03 73
    0x400c1c5c08400c0b80035078028042c0c5081e4542c90b4000d41d0740f01c0da00224450409a46d01e2903009001426652040e05400100041c41a542c4460b8900e0003072400701a410f0030340c01d058010075298800506024080c01034014805140b40c020306401c0e011304410030449030b0322030ba00d0030880404010340700245007001e1040046040300d411000c021038601080030720549010300c00164402480c1e0f2403605502400b00070f002c2d2002290f0303c800c2030b9004041e42d86015070ba81c81e1030301d040b20071200e0050b804120382e880c1c05a290800c080c40c03101c3c3d00c0d0013081a01d050f40607450f8007140c0c601c3e100e01703041341d0221441001c5001c90010340c088003802558000c1c01030345004000e505410f440c20340c209080113282c0910b03801c20101030341c402c0303075882400c68ac03031000091683e404c1d0000c241a545d030340403841c030642c1d210620b035410076504000c21801070101503055040f190442d03000030500e072005800008032018503101c0c8901050808200c4009015444800300c40035a00d10b820803503030028084600224009840c03407961 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833586987 1250 833585737 833585813
    0x80a020c030c03030a080c0a11010f0218010c0519020612160212031909020d0605040803011a0313082203050a02040e030a020a060e07050604140a061d062104 69
    0x172100c0303143c4440303010340c1e50743d00c03010a140c1046c507180081242c0360000b8407511800384100142440640b02c0940d803401111092110b0352507186400d410050052150340118002107505605480091488110b400d0540001201d40c003030801550003040941c801d20000004900c0c8280850038140c080c0ca00c40c8003460007640f101d01041318201000709040b003007000318072803175071001a070345200034050008000b10343c440c03104540d41100e0841f900800040140105407095904c0410f4011040041d495843d0081240c102c442d01c05400070f015000100744a0010001e13030003c5620140c0e42e03210610102d0744d80c00c2c00341c2d0360b070004002039019529064115000e080040212021816990010101907400ea52040001c094201c5a0340a0780200300b00890030360f5410009000500e60442000e00480c0d40d1405c20213801403e920000a01c0500e401d800d100e200900500e001d08002180e01035117031901c600700d844080c000108415648441c05d0100401c2002c07401468445a1003018568051003a110090340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833588237 1250 833586987 833586997
    0x92202180d0f121403090c01110a020a03080f070206070b0411091302010e01120e0f160e0c0c07050616060e06011202090a0f05250e2b080a020c030c0303 67
    0x8200b02c155455020404014180f005001145040340380310300e111805040303682081c3c411525540100301010003541e4880099032490068001a00204403580d001880420300e6201c010a01d00010903040c042251000c11384880b075802514569844100b0b182c03901e00e0306070031070b1300f1105c80c075480660306160709185000c0707480b5034031801120042c903615400640b2090a0b43c0d61407410081c0800e00842c02000038010050b46065103002031401c0702c582d610481c28800303a03440107124040311503820401158040c40b96a0004980c032042ca9485550007103075400c05900760800c179008000000c1c2000d851800400d844540c50140004110040d42041181d0321843d080c86900d419440d0f01d0301724009403034504c1c0b84540001c035070340300080c0420810715042c017a00e008031082d000c10100c00404c9a9000840e21061902c08241c1c500b4001a0300c1c50701c00164a5200d85000c651143c0008200300d1004241c4010000d2080d00000c0c05904c41901c9000290344605018070302c1e000340166a8032050394100002510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833589487 1250 833588237 833588243
    0x31404020f010e03010f06091508030304120c0c0515090916020d051819170309150703030b04110c0c0103021204080903150106031a010c02010f05092202180d 69
    0x80304a515001c011a04507102d40e01582d4103560300c0c102842404202d100e003d000300340c0c94601250059591007000303a605500cae4010080340e0000c00c1000000b800928070380c0403170100783c100300c0000b900c14240180d600010b40c0101c1c0c1c00a1040b46424114201c0d0000743c00807150407691441c840c0d030380e9002c0d03850040000782c5c0e02c0c1c0940d010340825814a8000d001030f06c01740700741690008800c1c8800700082c14802c0122418089581c2e01c210602c81c00c000740786007880c032507140001035107020f01d048049040c50411010403d4403600204000b0205880b0b40c07c1005100e02c010401e200c80c601d20484030002e94408604007100380700340c100700420340d40240240ca100030308912076102070b946c0340e444c1c0280550004403101c0d1b150042140381c4800c80c155a514070f019050903640003c80f034807400c010828491005c00ca02d4103020b01501a030300181c0c0e010b1046000b42050386025030706c903507600c000701c0e10081c501040c041e000075020180302750005503940940100704040c1032103600284010188194404564409 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833590737 1250 833589487 833589499
    0xc1006060e0108070819021207030b181303090305010509010506010e04090507170708030c030c06070309020904060f061701020c01050a0b0a0b03061309200303090a1403030f160303140402 82
    0x1030012401005d40d19486a05240000c0001ca00b65158030101c0c0c0c04018030f29580a410411300403a40d03414414100c5400041d118001c080031514035280103024000c0804400c2220064500e0406110301c00c80d07002164007100903c20b03428120702140c00390800325070701800111070700020001480c00b8054500943e800c42c020304000d82c10000c141c0d08554116140c986240f04180001480e040e0400082030100c1c140d0703000e5602c03903000714001814440d0180c800c0d4205420141000003580c0c40341c9441d504540d002c140001c42c03410f0a8130101c043d015583c044682c01c160262071b09803005064008042403280000200003907a258410941180c074945001d580010a10f00c0c18451041d8040c000c0d608068020407000c00c410300c0051520035a6204001224412000c2c410466680442e0500509101046002d181480100c40c080b4610b03000307030710034042c01c0b42d54503407404001d4800740100c03030420005030002c0780c1e90061183e842050420b40202100003d181020188001a0113914103009942c01068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833591987 1250 833590737 833590741
    0x15060b0915040e0103080a0914100e04061511300d020d050705091003051b090a1d09060c040311060c0c04052d04020604050409170c1006060e0108 64
    0x5001c00344848042000114008000214070360001e0700005000f90710451100da40d41101e10002096000c6a03401a5003da1400081025130341e03071030703890310450b000c6c500d0190414a000c0e00041c0190049034002a00b4000480c68840003503031040300ca0381c030f0f4408601200c229544042c41e4154071300d0b40a44058501c290394590540041c4210000c0c05a20100135015050030381a811400c100c5405880000102e2070009540209040c8403202c0007200003141410841840c0206003503241d40c0420b1910b41404100144001003646c841c0c10240c041c00381d5116101c03084403803c040c00d1502e40c0c03d603041e04180c862a40090000f011040403581600da00c08030510fa136400c00e0040c000240c0000760501c010b030040c84602d428a40390ba00c2110712820b400385400c80d07440c8103100e205c0c5842d01c2012116803040b402c2410000561124800c4070101d44040d640040d0ba1003241c2051812807000c00802400240009001001940002450321280707401d071400b0010f681e43c4813070a43d048010343e800c3d0390225641d400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833593237 1250 833591987 833591989
    0x30b011106040b040212030316110a030e0405090a0602030a0504030801051f080c0c0d1e020a020f0f01020109080c0d090b2a010e030d1e0204180509161215060b09 71
    0xc0c4081c0c04c640301030100300b180c10090b04003a080d03401c221800202c040c00346041d000d07103590015400a0030240040504800c0700c07140c5004040450061140b401145c0b01c10100713250304070030040d524800382c0010045490341001c46646010704420746080c3c000a0002001040500e8486c01514401401c00c0d08481c003440902000c1c3d0311200e00800d4004000f10038071072002018410b1026002c01c4515540d200c00141c2c2a0980300d201192030050401103601084003100140c43d82a10340360001c1085a01c4948840c410f00103d004d8008018002c0c1001404600b000059000041c211a03101c01512040c440130b0311544100440c1c09280c00704c0b1360004280c00d0100c0300034035101e80e1042807013900340040307105442d20151515550001b01c8101000d070762942c4000103419101a0601000d581410540c5040d180c182719000c03000c0054000c40702c0070340c3c40b004601c1d06c6808214401142d0382590101c5c40704c60b503d03010001c040c1d8500d00c090b030707081c080c3c10684c0500300c129101c1d507403e544130070950b2410180b41074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833594487 1250 833593237 833593253
    0x815030118061503021002060405100c051b03041505030109060806070e0603040309052d03010c020a081c050f1603050709140109091a0a0b070b0c0d0f0903030c030b01110604 76
    0x421190300740ca0f210110241e221400b43c210300e189160010721301414140342c09468003a00c40b00c0c001c3d5440c80d000ca140011580f00b4215620062081b4041c1a40d43d00d81f0411402c40c4116440040800b05030782c1d5600c0301d0b0f600070018504881d0040c00821070303a1380c0e9030301c000c3d00d032441220f107074001410100301031115290401c051904140030f46850003030309440d000800c0c101c445401180424a00324001d082c05528080810807844070290f009104800c43c03040c0c06940c51541d02c0c0005e00090740451031840d02d11110248a03100c0501034401d00850500402c44a9500c03400c0c0c07180401030400300c9051b10f1700d60207402038034000c80642d9107540b00076250400c52810090b903140440e041000760200010071102c98050305800141c1c8201945150424038104144a81d082d807020708180c03824881c040c040740c400b0800c140d00c0700c80500003039034030b900701c20a0200420000e071510f4203c2d0710306070000b0207140d49030307001d401c1d601d0458070200180502c0c00c2c01540c01451040130103005a0000000a001541d40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833595737 1250 833594487 833594501
    0x601050904151148150c0703080606072d0503180a06080c07060203060409060e0109200d080a03020702030703031112070b070807021c081503011806 65
    0x21000b91100349610740d0700209480401c4082800c1e0040890220014500c1ca45034648203c08038800c4514080842c1800303c6040d80b0910401c09501000040c00e498a81800b00c16165083c1e403103101064070704a00507490795008140203a0004000c0b9001400303504045045890300b41e0490304000c0c0d074240b0740c40c1c81d110307003c18109040c00e02e060750100711000136010005000d00408011304034050720360304d10070701c20109915845a400c1060542c28412074246d900c040f680c60a8021300c0c0541d40f40e80d9800814090700040a000f07150780c0c980300401811020640c0842c5103644620034285d404400703040c10744068480c0e08081e56011400f000f0003000950004020500001d40b41400340c202203941d00000d06100c1203500035008100412003002c8940e00c117100c0c040e040d80403c0c00c00e03402e02d14291034013005030750001c0c1903405100c841c8011882d06802001400607003151b91203500c1050ba154040101604020380f42c408000c0c0740c0411020707551030180144a00e900343d1030b540b501c84080c0da0b201c0b407020303200b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833596987 1250 833595737 833595743
    0x140a090201030f021323100305150a0e0702070b0f0a03020705010b1801030c0501080411210102040f05090105101b080f070803061c020901150302040b0c06070207090e0601050904 78
    0x1e030340c60000c0303103c00368005020038841082c41440c4081c60300302011124655465800701041550301d2591165a80458200000c1164540000d26545a0405420407440d8840041c2c0c090400d80303000a4800580442600c1034500c0d03400e035811241d0304c0008910900070b25030041c40700315042c840c121030184246e025041c0980640c00100d60100c420740428a0300700c032403c41c0360800307240e08010300034081c000c441d03c0c0c02058280303000310f8a0b1600c1d0b101d0b921035040b400d4440e03114111001c41d41c2d00600455800542919500c0021507441d6961460900407114030722500e400380c00b29100020f21890900f1400c0c0000200e07403034003000b0003480c003100280300106250440b030408040c841920011140000ba0440c1c52044103050f6032801c0090400c011150403907e800c20031004140b0300b40041c1c5031500103074110303451145040c149284d001d0045d400b0780200c0e005052685d00c003250001c440e010000c0c0144c042c0c0ea0f030350240ca208503100c003141402c0c1d9a540000d82c0c2d903640413000400407030034146400c641c00b0780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833598237 1250 833596987 833596991
    0x1a0601031508250b1620010504030605040303021c0f0b12250305030a052502032e090c030b0105100e0f040b060a020604060b0d030e0f04060512060901050a140a09020103 74
    0x2484d400c0b05a42c5400c049018038200d91501924401c100d50903104545201404100100018142000800074443c6020081540f03449602040c20507000c0d80584841442c0c0c82e0801d0451442407420b48004d0074081c29101c0824280150200e5508100208190504250014002134224144950400010010b031860906c1e4030850000116405002034040035049549440e6184640743e4020788038400082c120301003143e841003920040e5000a010401c101554034611014010b028404000201d80c2071801165811b1600000800c40d100201c00b095071b100d54000300060b42c03508103100940742550b14100100d8081990710407a071401c400c12020600300104082200441c590110f04aa000705451101582c000b5051204110141c059280e403041c0940341c3c0301d403000d6141c40040036004514403140c0546000101a00c050315660402009410302411104d81020540c14944d600c01c8101c90b59002c40d4a004c011414103841401403909184404510103540d80303034140484001c040d03107902241419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833599487 1250 833598237 833598239
    0x5041a06130b0703090e07051809040503270319080d050c1b010c0806060a12020906040b1611030a030e190f0632040618031a060103150825 61
    0x7a01800041483c140300e540c1d4010351601d00550080500800350584050040900090b02103142c103c21240441c00d0841d10900380e9120f5041940c00c0d84a040f21b8140c40d010b2076140084d56043c95804043c00b0201901180c0000d1002241d0003000709000c14020500e000070446292070681d1904419002203191000918108420340d90344250074004038907203c2c503511741140b24400c58103ca910307a40160f0a9076114541344081d18002c0c80080d01500c500d10b941d601141088154441000b520060480d40079400c8c0d840340d4400c016170002071031800440b40c135445241711540c4c0e0304001c2044110164561181c0803000c0404081101d900204040300a020f50fa0381c0740014002c9040c24680010081500c84e881001e07030001840312a0310440e10360b25610030266100c280d109000d41c0c103c904494080c98085c401d02c3c0b030070a000003001d015503c09040a40044041c8180c41c0c00030012500882d800d8808100c4c003100b000703030b8040884003849419541d4010440601d06101d203e03400500035031708601c2410f061 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833600737 1250 833599487 833599499
    0x20d0504110103051f060f09030204060801061a0f0706050a090c0303110c040212070309050f150717091c0306081e070b04080606061c021209010605041a0613 69
    0x1a00111416034000e0060854035440d560107205207a003003c0c07145c407154405c005103403030314042003014482c107002c02400343c151280e0903209500c83e0000e594002c1044c4013943d034074504640a444103002e00803d84002801c0c1000911808048810f41c017000c1000f103087c07070002d4941c04010030009060769411522a40790070b00046445a4a9014601c641c41724841800c40c5550145007148105c4c0d2076000c0d5204000c2c016070a03081311084c9a00c0101454040390152061802e02c3c102111450301c01c00d50b01c41c1210618800c081013070070901ca081c0c1c580c1d41d860303203440f43c01140d2480601030f2114603494001040e402c0705081c0f070041c41e4080d01a6802d010604941d1401c4461501000c080901c0d421450b444000032810414400c400007800c00f40455803c0c1401c10f0f000c141c48060140106208003000102210300d020b0006280140d1a1400c0b011900d900603009480b40c160340c125011130385940b07020404101d520f05880b030103540500100c0c180c0c00d000c0d01c80052089a071302c07148452f1407a902004d000964 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833601987 1250 833600737 833600741
    0x609030302100b13150e011205061302120a060e060705040b070b07090b1605010e0c01082a0a021b030607050901031d1c1107051309110312070309120b0f0703020d 71
    0x3042030300e55844007a1034905680d120b06c00300181c00030640080850400d801250380041c4150700401011a421000d0340c15200003582c071404104c01190341c1c007440a080d020f01801e030348409003072001039094400355650440c1c111200d202d14094082c281000384410400b00b14100c13003d607481002401c0c40b59000b03444000380503190300151041560240281c010004100d030a01503020780f1343c0102c000300f15041552002030580103006098104044010140403001000c10201000b85031650f051070740c2d91400440001d40340c20103168183e065050709452075201341000614648103101c2651aa0b04251540d00110050180310300d192444604041e4503d01d034140c14464048441480c01032600840e05c4040c0151003c4405024000c06400038842040b1588421264181045000100058000b00c618002c1c0039401d41006080d0580b240c030880c12091b1405034000c0103064000d4440500080d035501c00d9502c45003010100424081d0310501245880034054809a0080814103000d400c0603d030706901e0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833603237 1250 833601987 833602001
    0x2070611152419051e060403080a0203070c030c210309050f0f03060106050a11070305030a03090501091209330e120102030709320f04060b1b070609030302100b13 71
    0x1c4040c10300020890307442d050750902984c101c83d1798015080d403680400207403640214032014140d18000644c50314514424021070725181d500040c0700500f540c807802c04524000c201d008120406007841031030741001520a00c110325060b8165030b2440755605050902c540500c2e204401c03038000d20020300711546554140001c901038400c90741c0c0e00c2d40740c10120000820b95180b141e030040c00c0d600080824004102c020040700d00e02030340ca050100311411107140c00380c01001e03c1d44010f82040e03860f00c2015041c40d400320304001201c00d0400f10400c15815203900c2c490740140607505d0384403800b003002038202c8640102c40849642d50000c0c220031040300d8402ca0642a42e00403a0040005142040d0a01144800d41881c43c84840c1d0907050551014484d0241d1303454404030081107204204009140807240c1e035a1300f003203016100c003000441e169810045030707034240c4102a80c1c010003401a15801309001d4415840b038001c8030340503402072032140b00360b80308400240301220b10f0542052028002465424840c01020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833604487 1250 833603237 833603269
    0xf10030c0c3011070614090d05010603030f092304140907033c0611040e04110103090512030c091e0102010e011a040f1803020706111524 60
    0x12204200c441d42c905180c46005002042c0250403034002025a00052004c0a64072103007040281d1980d110300c80c0e1070f1406643e51031a4400000202c2204014040d001082180e11a403a000700759950440161900c8080e0f000d1255507a004d6402c165402c054412900d041060107440042c000482c1c08801ba0f9003042182e950b2030301d90020408104010b62789010000801410003515184200340f08500d0340c000b1204860070003206200c0303190f001d00075640e1103c1e40c510072108800e40da03580c1c0c500408840b00400c640c1500c0450101c209400d0390b50107170140c0c00c0342c1c96114014010b8400082c0440c90b050308003030710030315000500744003003a01030319124036002010200010162948141e01c00084c00e681014600788156410403420031036013100340b030420111810482e40407a603a2500083d660044c6a0389001c45191441c00c0000014140c000c125641030303800555680009920850101e65580c0c1d10160040c0034140c09400158101d0341c03032101240d0203117180380c14107807100130b10300050141e20440f046c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833605737 1250 833604487 833604533
    0x2b0e0a02060f0d090f0b0a0603120c030e1003060906080a02090402100e0d030c230309040c17070c17030c190c0c2711180a0e0405030304020109050f10030c0c 69
    0x254140214200015480b00407c081170001505658039841c1d10142c2821000074840c80d0740b8601e041500902507254800310280c601181201d0060008014007041d1007801181c40c41c001001ca1891004180074410756005060410707107845035800c2c08001005250040200801d40d00f0540c850b80da1402404079550282d034500300309101c0ba0030b107596804501518000804004041204500b00200680740e81c0340044800003800c40c80400291b6083c0c600c265201220b01c00242000000f81e08032140d0075000d4003031080a001c0c1040444c11a4542c07005581820b03820a06002d40071490080d00c8030340e9400409858140031038200c9a0380c4010640d41d6820805406520701c031424414804021000001c044504050151030303904a191075203442032850360540188041c0383c260581c0c84100380100204055038190b5814507060404940700d0300140c404a0005050b82c0c0c00054516041d104c07031140b080d00802400001e150b000c03090300280480c10340b0805101d01c04080030040b07020002107082548144c800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833606987 1250 833605737 833605763
    0x3140d0207060f141b03060103200414030607090b03060a080d0309060e01060f03121e05091c1a06040f0c0c0203010b01020a05060c0c010f022b0e0a02060f0d09 70
    0x30420a4508000c00080c4c43c268a00802c0380d40265400c4010b600900c1680543e0707a5202c40b0012000303802469122003d08011012180b81800100001c1003200c680b4190009419a418201520360000381c62404c001200e004007070040104d06070045030840b40007000c50b03034603e80e26240c00303041c040d80a555001283e6240764100a00071f0a0103030403190103616000304182c4e424403802ca80d218649000161048456140c0740b20303420b01504a4400f880c08070651a0f0403e409034000401c1075001e8203005002e001e20002c1c001c0020305501c9201c1c6c0c030b0740e07008101d81c0380301031807081c0e02800440083c1420340c042e0711a405180c1c035403120710031113500405a58601446201c01d005050940b0a90f04403a411940803020300800700d03201080c1c01d07030810064a40342d40d9030400c0000b2035014042188003084240d00c0069445130540001485604032210711001e841d0001c0480204d00450342e10030340b40c03201600040c00100061a003036004203482442d000c0380500b81010b6460311400c848031403004035401e031080c5d0340d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833608237 1250 833606987 833607011
    0xe0a060603050313090b10140904050903041802090108040f0c0b0a030b030c15030c0a090302270f0105100f05070b0405010510170d08070e041113050604050d03140d020706 75
    0x1d1443c05441c1186041c1b244441c1c1d100030070a1030300d01150134000c2004010181c6c04503108a0111658410003e000340524284440c400d80c9a5209100d55020561302d48001080d42c01c2600035107079081016106c007046940d0300e0300c03007400390140c0120450300d520044001060300f070346074800b074803a10242e80c2e030002c0e801044000303044c5010105564140b0641c134106c40201040034140840e5403105003498105c1d20340506030000e0700c00c2411600020743c0516201156403509084046038049000303901c41c190f400b074440c2c4010301c2e1020030030f00600380c000c022004d480081c02e00039181540c9569407171904c245403803802c2c1c032072000100049e1400c45c1c07265168400d124203d501c4a003100043c3c05149100510b40350201c440640c2d80c40c890180000740182e45000484403809010503481e00640940288202c44d144080340230a940f100010403400b0300d8005c000700e100e050000076581521009052900f203003410741c5080da01e080310400c0480c0700c000200f05640b440c50041c0090304007140300d404040340c1c98100300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833609487 1250 833608237 833608267
    0x2030307020c0301090c031b0e010b07060b120d050f04090504080d150b220801050f0f0705120f0c1303030e030c06190f050d060e090c0102150a0e0a0606030503 70
    0x140b549100343c0c1032184c05c0300440e000c0c2205d9804c49a21003601103080844140843c92800c0d194815480c01c034200b0000145129804014510710744105000c01c031844a12040014082900881510035400400000350540c0101c00514170107401d1b0700c409041c15980c40000c01640d0040f02e044583c4507012824040c881c103070f03000d0501c280303401c4980c500166051800041080c05108142c0e802c4200c144604045901000d80b92005040804024005440d0014004c01302c40000c0e50701f1000020a540080c40c030034401c006540c070711080042481007a413111100000820006444008003403801c20104a031994910900f00086100e03468002e4048004410141403080c0c182d8400c1c01040208222000503150212450519080d070800400020b80100201e406025403442d4a401c41d14107400426074110400c0c519204561000442d80c0500c9440012a221348040717000c822510307003035004642030381d001ea00310300b0200c104c8104854680008d901c900d03041c0e60907940144c8254000094110004d9049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833610737 1250 833609487 833609503
    0x40b031006031415011208090402160807200d030804060b060c0a150603020d0b0703112d12061203130b0309241906030602192604230d0203030702 64
    0x244003000c4d03040d0314140700c008044404030802000e95000045510300c1e0758031941940d81c01030741c1d03682c201c3d0390341c0c241e02c0c060a065120200c00e03581100085039015861396100c1c01c90a400c20050146046090640d40545009030003810480d8510340340c1403915442e44504000c0d01d00088010000d03d44505030341085100c0000c03e000403ca118109102070003d038032810340c1e61003101d038400d0700d9030816940c642c0201e00038040e4040d01c84044200103111100c94100c08400c8a81d900c0c0700c841494811209100c040f81841804030b0503440c002040002400382c0b403c413480499141d00b4800703507860084d603003e564900c2c40142c0c101340281b15000c010301c60246800c102d40c044268002c5801244a41081555003507030720300a20b54419010101c84045814189411103002198400415510391034003060130819888524191400501c00d46594401e541c08a200c060700a401d00d2000310281c0c0311038507a41100f142c0c403200c003003500300c3c2c0f00224884c3c510b04100b03a00300008141e01031900d9080000d0000d0829000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833611987 1250 833610737 833610763
    0x170c1f0f02010903020a03050a020c0904060c0306080a020d1b0306150f080d1e030207060e0a1205040e011a2a06010611030d0b0315040308010905160806040b0310060314 74
    0x14000b003003c0041e8000070101c060035010b040490b15905200c0c000c900e130032403172031034180c0014411050204003c441d4000103070520158905100403911000b503159180c1c00100003235405070f03400300d40c8401b044004580103907000c480300408500988980741c0806a85810400055003010a84208500840701c03840740041e140b201c01070311491001440c020071305815801500074160344982d030349030041e000354100ca10140d80200700344414406480c03481c0d154a00810250750350380c0c10100c6103003c18491411242950701040c07200c15564208600c8560403143e1441142c10104200600031700b000c038401c801510b441d0315901c3d00d1102001030702030a040000681c424402d00611833900002c061022003602c40024200134002000401c040010349000740802140003030b10180d40600050541c844280e505a9000240a011544070800740200072510741c3e00071000140700f50f01142851030250440d0700072900040c1102c40126036a881c1d002281c1540e80304480a0141840822004000303209907900c1002e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833613237 1250 833611987 833611991
    0xb0910140306040506043b01050106021b010e09040609050c0609031005041e030807180608040816140c130203060d0b0a020403060507120e0d0207170c1f0f0201 70
    0x1100c120030003640030160a00d480f0755103c0c0001030180d1182c0d40821000101c07100c2d031583c0c2418400580c0c800f074603480351400c200c0401e1256170585020500400d412284a84d005011714400c036592483d0550b40e07140340d00e041020100420400d0350391911100e001e01d014100c0020040b801d032400c10f161181c81c0e40042c1c0175240c1800185038035600070a0030041c01000f6040410031750380d81c1c60641c10301291041c1802c11011480082d405040d40076903003521900d001d881d51400a095210b22805402141c420000090802800200010b41c2c0f40e0140601907480d01404003110310566404c0c43c00a90003555020340e0384042603900c0c2d02d241001d82d0544e0481d64100451450a04030041224051482005818540791001081d12044958100c82c02141c2084d801c014600b0103000082c52045101d912005d5542010041c01054030007141c101d91040f401c0c3c004026052600802c0b0040e881c46020070501402404401e400c1c6860707815551031442c0c2c020307000c105019001d00014100082140d0010708581c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833614487 1250 833613237 833613257
    0x6020c040b1c0314030a02091903020604031103030c07080606040c0809100e120c010614040212072a06230108060f1005030d09030b09011e0b0a0e010b0910 68
    0x10b00c1d501802c0801501c040700a4441e08000d0400b9510201c00140b02c20241c3c02c0003082002140b41036018102284046407100e80ea6924100780885040d09400081e6000100f084200300003110307c00d40c42400900a020f4a0806415038805400c042090b030214401783c004004002c1c0d149032074882c184080351181040b0f4400d080c01902c4540d142042800c0c2d04800e41d6076584e040382210308114040000444403250ba40d90b42c222504c19000e000c4521802110706403009004110b441c1c140280c400321160005180096650b02c3d0040b22004003641300540440c00e002c07005003191402d0318400042d40d00500300030950f99018a09146100400200303106241c00703160060120140215500e500312220030384e01d04aa0b101c10200c458166502d50069601d80302d103500304403280d60414076000807203004080c280e09075a51072000b01e00381c1d05a200780c0c4c00c000c1000c00705000c0c4060243d02003408014040c0422583c170f81c6601c0b07082c960300400e82201c041c070310003c242d07002c1c2c515020030100e1007090b203460000410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833615737 1250 833614487 833614489
    0xd03060602030723160b040302010207091b0e0a0518220c03080901090b03010e1608060a03142404060c031a010804050109020907050a02010605190e040503090a0f06020c040b 76
    0x103144e0303030f0010300c0c601072244104135541c0c00704000ea6114100c07100141d03c441599801081803590262000f02d025004100c0c0000c4d07429a1303840303140791016110381128950103148508850541c00c0111569101c45010408a416150820341c615240b00e01d2412031214201031745007000e030840014a0070030321410300c006400003070301035816141100d0b440101c15455404400059805031102d40241c2c00c0030340e012000003980300f000030341c4600a201d0700d80c172000e0301c0c100c0c404100c4205c642110041c1c5c004c450510100009589000300408840c0440701750346d00f155200300c6c0c0c44c851040c0c0781440c110102d003000c10300092040502c03034460a003690341000c1140305603034106e0400320b50500648906002080d0001030a0007029044190001e50050039000f007403400341700150540e0403030442d41d8015031901c50080f4060a141c0e4030310501210312010052041d1901500350043d0030024421100c40c0014050703800d6135203400980001400c3c00d00c502031021403e02c0c5e0000c0c9480310085d03030b80b8419401c0c01c49030121 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833616987 1250 833615737 833615753
    0x9051c08040b1303081201140f03060106050c0f0a050f0d09060f050d021606051e060a030b090f1605120d0e1309051207020906241305030f0d030606020307 68
    0xc5409001c0031540303e494220b4000d1200041e030384050943c1a00041d8000f1380b00c0c40c02031450503030b907104a02c10220301c1d10200f840303c1d0032101181d0b590150f2001d80140042170040c4050041c00d100141124020462800e00b2401c0104c81c510131521544500f101d548181028007861140080b10301c1c10b1014070380341500060010b501c8030000340501a00081b05520a403440d0122520b05440007241207030b01d12245030110040008549295a54616038540e0710b0300350710742800502469000703021901080c20340e15171610041d80a008a0a0361184c01e03002c094401050040d244162180c40f5036941d05440c1c101800a2018035001d890080e4008030b4580399104d42000800c0b400f110281e036000d001191400246000341070b15080980f041c403c2c1c0d0401218299900c0007480c0543c42a602e816841d03d914083c048500c3d84000040305c014102c0a0f0302c2e2020480c5005031841443d4014281c004136035807004207040142c08076030210590882c100d5140c290350103009413001084988000c625100190b15031b0345c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833618237 1250 833616987 833616989
    0x1006060809100b0a030516050a080c011418180a050a05010302030d080903040b1b0f0705010c1119080a030305152d04110c010c030212011203090306050709051c0804 72
    0x82c88503541c140c80030a50302c80d81840e03005507a100d400c4070301100140135914440410303803141c1c602c580050310011800102c0410781081c25001a142d03860034607142c0d402801183c0000100700184589040c05419640c1c440400d0001c0844400c4086514209020f01c442580c100600c007210550401c001000141c4000410440c0510355152049203511360004081c00d620031030303110005100c0082905002140103103051084110070000b100c0d034404400c4100c5495092610843d404074400d0b50320507011079082c20b10002e00e40701c01045141001c03440e1b031a11240080365000140303140c1c03004801c1410581c243c450103400401401c0034007252290900000c0c59106d46002c860305400703001030001c1181a5140200d50f03041d000402c180010002d4a106013003541000416000035070a0228054000380240300700c03149a540418104491307820700780107803011a0601c070110200206101d000020883e64400d05001d0066951680c05140ca400304100124a0031850003d45c0008200803000044011084230 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833619487 1250 833618237 833618263
    0xb0a051510030f0c020f07090903200f0106030804030b091209040e01020c15041a010b0901050f0702040507031a030c0d062309010c17060d03081302121006060809 71
    0x5401500c814030102c001c3c000c00c0c200c288655091050514940e6008620445540180b108a5100da03903a000c500007583c3c0110805000308440f4448480359001200c18100c114030358a040f11300c0010151403090840d5401d6209440e580e80100c2e05104018210720160381080165000b403c0ca50707101c1c42c401016101d521107007481603540781808900c0f21001c0d0140c3e042e10140100769203030100e8032108a560030408440407207000c40d20401d04a118030b007254031681698010381c180f41c20a0b5a00c40192220350101018400521341400700900590710b501070103105400940e00420b0031102d0010341c1003d24a040d442c20b00c0703070308541c040b0303122506c541090303100c11a0003620119003c01581c00502c80100c80f02583d0002083c20b90422820700d4054000440d108a00c2c1d032010050f880500d505040600e055502642c40100c542446020a2242402c01c1d0000381d00c004600c0304200560000311002d80c036a10030342c615006100c8002c009501d501c907400060a0504010b061440e2140391a901c50000276100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833620737 1250 833619487 833619499
    0xb0f0607030e1c060504050309120601030c030803060409061b11070b090405270307021003050106050304020904060f0207110a0b0f0d0e0703140102190509060406052d070b0a0515 78
    0xc880c102c8400280f000d0721a00810200482e082c2418140e480703074030807002039009204032400e401c400c800014545048030740140c103048001f81182d598482503800904a580d0060310740000390041a1648541d840300c2172071101503a050151020041d003804000c0010504a40003a1030070803004500c031048600b4198200d03000112075680081c0c010165012802285904401c0d03014840d0301d83d0000000e14285000b19450014442040400c60686000340a21030005e20140085801400d00b48221500248105004031314134000d041c3c400100e0300142c0054a4110680c0c070004c455040c54000d03070001c0d11406503868034110144a0014240c40740d0301c0e50303560050340c9502000140e02e080c45034802940d0300548408000d024508454041d401507680c50703a95100c0c42e1201d0028901420845105c0c07100078200070f080a00e05042901c454008000c0180da00c0000c00752441009402d2240b01e540e8401c0440c804c5d00c0e0b640700e040159005000820880e003142c6090284890f030208408c9200c44114100d0300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833621987 1250 833620737 833620759
    0x113c03061009020904060b0a050d11161e21030509060708040320011802030606040501061b03110304060224040c051c02041103180a080a03050402030a150b0f0607030e 73
    0x864000c041b20391040f580d0700c2c030210b00d16a0741a40440200b03910300d2072900c144070040070140e4060710f5104415400d100308190004000020b0b03020600301010b00c800d201543c10000107030300c84040410603803840d05110f1240c02d10034240c194151081a030410344200007088103103080c4101400c0300d03401038406414401001200701000d154032640da1142c482020003805503001ba1f035210b440d4a542c41400701d1207401040300040250402e48038090489045541e03048120b02c074001541783c2d030301007078000750700b08800c0140700c1503280000c00c011703c02886143c0c02841110182d02400100c0089908214680c8011200340401b054107411360005030b80381140d01d0250349002223512a03c100b292a0002c0d0054100182c1c903114080b00405584116020300184c14580c0301c40d81c419403944035031000245092030601011410f14481c0d3300403517009101400710b40c5004007588441c510b41c923845032481c040c45d4483c41d0303489041c185444903001d403440c142d41c10b07420620030b95400b40511030926035085c041c4070702c049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833623237 1250 833621987 833621989
    0x705010c0213020d0b040f0b0a0e0a02040308120610080108060c03072010151206050901090b13030e013b10080103060522113c030610090209 62
    0x30450203902c10608660350500501c90901800c8511041486207152042125040c41c1c5c9000f20300d01414020702814425062001c00d0b08100e0004d03184060665003800701000140740c8400920902c00c014586207460300d401c004002d1780540b140304810070070a4076001080a544005102600940a25600d6890b540e801000b00d410144e02d10383c400c01041054080c540e90302001c01c0d01e2861840344d000500c205503a4480800c1440380512402c1000d40e03103a6200c00c003060f0300d907015940110032034002086449180e100d010408606031203461070006550101e1003095006105225900c1084c00c040e4030800031a00b03c041200c0d03205203139418850700d250046e440d2908260f49010120402040d007003081b052102d0042070000c09000840ea0301d8a080c001c9003540301440341e080850030400025500607100b9a90741002d1030b0300311002030b81008907030951007200c8400b090f0800f10351083c03c4000b44c03412941d84107010302440da485214040c1e0021810300141765000c050340c01c01d49000e40800760356450b041e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833624487 1250 833623237 833623249
    0x105040e070309060c0f090f06050414122a09010302222406030608030f0406051608040b0a02060f0c1b0304030203070b1306031806050403030f1b030c08090705010c02 73
    0x10b8005104a290060245011b41c100c0c4500d00f810300c00c1da82c1c004c8003e0b11100000b0301100103000384004500284820042410703250040c043d1340c1805066440c03000b007480f9080b40381072002a4880d00002c00c0456100400803020025000784600311808020b651543d008600d131400d0600d1b402180c2c2005013455a17160b030301908a800054036540d00046c500151007403091703096080f400791100090134864002101203000040d0390135641c081c140545064940802542c896215030140300122121810b010301103440080a07000608102c4140d03036644128600003414406d004010b00b03060260341c02031102a4000c80c0648210f0183ca1b00619015860882c1c0d00703185003e2580000d5151007901c1011980420710b038003401c2c0500c082c1103000d28042e145d00c4141d0540d45500085ca10541d007980400011a00b1504203e800a0080c18005802118a0380e00b41c10750b00d40c007483c240400d031081981849290b05201700a00c8000d207107440138240c10006e140703a031556610721980781040106208101555104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833625737 1250 833624487 833624501
    0x14131b0329010f0c1a0403030b040f0501030507092409090c0b1303080a0219050703020108090f030a05090402040302030a0f0203060112080910170f0f060d0519140a0812060307050105040e0703 84
    0x5c804031078070310720701803800402030200c0a01d0640550b0901048441c0490b0038041c143c181c0b640b00d005401818180001e0000516080c0051a020b00c29503000c00741c04000320100300c0250903610f0003c10100d90074105060320000907407205046002c1041210b5510551882103020390703034010004e654591140c141203241c59102c4502401e008c61400c00d080401030001280c008491003030b21201c10302c0d554814140d84408001d000c0004c02d400401c101d840ca80d01c80d43c0101032060008100604040e241e4010070315040c0d4508013200d0120b014040507041d0f00d410070402c0e00418079010511038031140c55940c10f85501803155501d00400e10b44105c0c28200d401040303101e0721006c06426004043c0703040002d001c0c4040c01521205400e841020120b0039a0500c50780c0040c00a030000018100440c4107070f11480007000302c66056900e91800c5041c006001c5090248604a40c050160151101000c05030703d0101c09029002030b10030b03801708408100998100c070a6070100c513190344c020961a0b940700700a401501d1b030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833626987 1250 833625737 833625773
    0x2101d010204090516021513030320030f01050a06050706020d0204030f0f20061207020c09090f4c020403210914131b0329010f0c 57
    0x442c0220ba09000769001c54451264521601301d100d0407901c0036a1140e02160b000740d1441088000120401c00c5a420740d1703c41e511914000030401d10780c40042c8130754006511030a181010000500c4848035080810074090082110000403007441c02801070014440c11f00c0040106802164a5000da071540e4156802580c2000490000e6a8280380420002e0307120801101c2d04490b007180c1c407403519004202c0802544001d4402c3c0d10305013400070001c80d40c1000400e05000c500c69110200382944a05074140c0c007039015580244070603134454a80d28242503c03010841812220001441d80142c086d201d420302c1080c0e085101ea040c80c2501c50301504280c05031104901c1140001400010006411050324005070b48815518402032134510031076150340984184d0080c07190507140c10209182120340450341401c49000055004020b0400201e0030380c0014403000400d56580302d8043e004845d040e503025010300b080c003504281c8207802c0060035883c0103041c10002c10042241c28000c1051100c805520a24 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833628237 1250 833626987 833626991
    0x1d0f01030905120a0c0201020f06060f09060d240b06030f180f070e06010f03020313020105092106060a0f06050328090501090311011a0906030304030c06020f1c02101d01 74
    0x100d0f2001d40b005c4076500049006100307121026890540c040382160107880010109800e070040702041000c10300c0044c00c0329622070560180e08000550a1a00c80c83c04580c001c0381542c542130324042c42c1c04441e45000618044c141c01c208002070aa0204029540007018500c89008030000401c0e880c0303081909123407404180301e031417000b0072400e020f240c850b480386800341c0e95200d019940703680031820b030f0000b601c01b0f410398200740401d94019801100546140d145c080c0c41c081c00d0900c0c21503a01c0c1c441c6100004140700d508200c090162504140f0f0401c005041c0c410300c0100c6841c50a0780040480c030005088440c08210903420301c828200c1440c070004407a0803808207024480007030900710300034510b501c811004128499a902d81007441070245019007402031020001440054060040b070300c40042846605020400c000320024080b00b171100090030391603000b072005201d419549842c1494071440303170011641c80f40b100e6a035144d0005903003401c105c4a02000c84c008498901c00040c60080202c00d1601d54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833629487 1250 833628237 833628247
    0xa060c09030b070306080601050618041e02070f0c05010203030f0a2705010b0901090b031b190e0702060702032530090e0610230301030303020a1d0f0103090512 70
    0x169145d0485810341d903080b410303200113036681c00c10442103105030301c00d070700400383e4118004486140c0f990240c04c048551618080d43c4d420840480301c02c903401020300300c8070003c0e10014402402906000741001d0942800114a141001c021120300380f140141140c0d400d0f510780881c820306c007241041560100325010100f0b03484101c00d1a00da8023130003030080140c3c00745034844000a6194600d00904283c0c0c840507020304001a15894084170302104000020340281c5603002c0b003070000e0111138003500141b03d208903000850405c41002414002c01500c24002c560003406014006034020a620010040e08208003440c0c400e5440c03d04003444035482c951121003000e2001d02c43c8a0f29442041c0011403c9546680c46151119901096140148c4404d50002c1c4007a50005189000e20484038500c603504103040da82d0481c80c07801d003066a00076001100041e13008284210f25603004141c1c0102c24440c1e034110032050700c0d5840840c4117658008945c0d41003540700c40c0c058040c0007040c411841807a4100401c9a071391 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833630737 1250 833629487 833629501
    0xf04030504080136020109061d0d0602090112060803030f060d0f05010b0112020322020d06020304050307141f0f1d0d02070617070309062d0c03020403050a060c09030b 73
    0x90034502d003d801641d4000d03400d212214104c44002500c45a05851780803105050400441d02d040c54080300c425041c030503801d10b444030350702c124080d81c056100c1c03d00941c0d200c60050004108414090031002582e09001007804001c601200b980d0380103400d22150744560f03031a00001142e41208040c0a000860382c1c2c40380c0c00a0000642080704100002e0300e82c00198008416514200c0c40100c0300703000743d10410300d10f080c070303005841c0110541c060004084040c90809612440100d030300603039040f542da50000802c801000490300c3ca00811003860b00c05400d904498402c0d920000b020954502661a51100010384000843d4042c210b406104000032001c1036007540460303503900344034804001601c02e0301d00000d46180b0450344004403062050071003006854842003030b409000b0340c01045604c00e03101c092a0044022408030950141d4402200c41043e00314000300b4011502c0300211300040500402081c004111300007090b110041d4009800245a05108011550380c00107410061500f0360a10622041e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833631987 1250 833630737 833630771
    0x60f020c060105010905010e03071502030f0f0c061b2209060b0403020333060d14240c0702090c0403061d0c010c02010915090b030106020703050c03060c030f040305040801 75
    0x603124282c990b0381c0141d4441005562481200e512130398192b0010b581440909004100c414028a807401200e0802c012008101d50070307005041d440c0c4040d04042030b4050038070740c10403541d43c1100a40303020403840c1880c0b44030328403030b886803203d4070995008060300a01d1301c412b07254940c0700a14008504008841d2500c42900040c0c1c410310099119205400b40c01420b001d0740f00612030881503106920034450150002c0b8080d103400104441d42c41103825944d0030102c0c90080b40710403a0101d2501402c0120740f202c0da42c50600c05920003a100d0003140c40700708020703103002404640c09546c044400090550b1444644145032103144c10040000d030411141205051240160039052200c040507203600040a100440304c00c0300304c0e000640041d0460a003040520310a440c000116840c2c1d14080310100e03103a24401010368800c0c0c0c0301c0001a400080e040040c444140103105000104402400c490b01301112049080c1c04007030100400052010085410140508100c8008040b407078001e1012102c3d8000000d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833633093 1106 833631987 833631989
    0x90c0d060e030316120e100902062106090a020f0306040504030c020d0503130b0906030408250614060306040209071d19080f030304120804060f020c0601 67
    0x296441041c80114401d441c0b0030041007080c0d031340110040c81a088042c95092030b030b103000740150101d0b01c081110b0014012880d804220f104450000411070b228000071044100c044c1310440000b4050800014820b4108580000e1503584091408c410707071082e0445500061410400181c843c5041d40c041038000380240342440c3c0c1c112380e607070204001412520301500c240c0d2000c0f54021385140740c10b1500f0041c00c406075065040c8480a03000c640540006400189955404902e2000d800010f2804c90407070740d080744152021000707500f03000004200071501944400c07901000500075050000d5064000d55000e00980030940d1400d200700c840200c51000e481180b01540500303900c0c0c0e5200858440c038010110300c2c3c1080c036894003184a20302440c09a9210351501305000b00400305051000260000280d42000d01199603649081c400501e03228185090751880415405c50840000820314 = true := by decide +kernel

theorem cover : BRFrame.Cov 833453237 833633093 := by
  have h0 := BRFrame.cov_init 833453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833453237 ≤ n) (h2 : n < 833633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
