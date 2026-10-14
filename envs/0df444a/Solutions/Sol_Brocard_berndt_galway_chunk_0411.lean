-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:40:41.856992+00:00
-- url     : https://prove2.me/submissions/3a630acf-1f73-4a6e-9358-e2e423aba080

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73741009 ≤ n < 73920865 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73742259 1250 73741009 73741043
    0x60601031508070603020318010509030703030b130f021e03150d05191115070201020703080904060506030f0f0c040303091e0b131401020c091306090b01060c0b0a0504 73
    0x5490300c0d20307986a016081c0040040e54400a10440c000707460f990f94096502d0514800c0d1401000d07800e000948180d150405006076058004215440c1d02c0c0e041c240441c9401d002c4c000181302d0854420740082043c1401104c010054440c1c0c000d20a420907114038071410611001c4035220b07030108941e25040501550403425840c9882c048a000c0c184c4a00100c802511040307030741c00f001c1112a00c04844121401004075020300e88698603260346401d501800e801c00307000b900004d5441600d488090503091000075000c409480e036421410141001502075980e83c00c190b24014884001141c100810301040c1d00410129612401100e044907055925151198200344031400718143d000a0088101c140031000208000c3d0540680301403a080d0040b00700441c44d10004428600751048038904540104500800030390307030980429013040305000c02c40940e40d0306250210060400c8103018141c10090000011044e60206500c4032640c41440d42d603101e501d0700702c442810b4a00c141c0700140b8805c3d4402c00d800c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73743509 1250 73742259 73742261
    0x105040918050307060504170c031804020d0204030c0e010b04050907030f090b09010c170c0a110703140714041503060c090e07050d1109030c060d15140f0f010206060103 74
    0x1d140c5060001940d409040e540d1050703d50b40c4125401ca825540315000c10061103915400082d82e541c200214034502035410300103a480c0c1c404d2101802140b02d04010101b42d94032158142c6042d8015010b0456a840d1a414001c3e00d2201038451109070041620000c2494a0814103450888402500001041c0c582d80025800b4003822403001a00315900c81100020401d503105090041c80300340000250900a25001092041c0410010344c0f622000010700c4075030070a071011140d980400380741817040c2c3c0701002c010f1800c0105076440a000c10803284000d1a5014001c9000c0d400c88004440c0302007407884001c280825103003200142c0d0413940300b41000301b001c03502c43c0d000501441a107207070421055880f80c0b6500017800c0181e03001c0700090004115040c0d5203030b036441103241890003e40e401d400c20b03050a000a07525200c40700c2c600d00948011440242c00f404030341105083c22034030051000700d9078898407580d080e6500c013003003284103c24041c681001400c100048042104060707010340035640c1c0e8040198 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73744759 1250 73743509 73743521
    0x307081f0b0628080903090f030c04050406050105100c020307030807061e06060f0513061b060e010207060c0305061e06090402040801020703080907120b041112010b0a060e01050409 79
    0x452164540c902200c1554030300c802003803000c2034016080303241c00304401d00143c92250525081c00744100c11003401655000001500e0003100c0c00c0341d21102c200c0e40300380400e080000c6403201f60741181c01d0000b400304100c011b80182d4160340c000e407600303900c1c0b0240d860100e806802443c806900745d04140414004a04040d004021042c0503520104402e81850062000501b05148410103e692041f060008662000700c0011100702842c0c010304104016200d14440320a9110300380620850020091442c0a004096424540c1040c0108203041401d001c9a002c0d5000003402c440e998a0552007518480c007a20401c0e000d003101030711380f03c1c804442c24592049101250348003640010180710f0702e005941e60740010405040408000b41c1c0303902141c60094001e94003d001d0314400d030052141030081e454100140c1e0703045034100ca07070201c07a034456040c8012450f088d4a41560004041080fa1041c08015080f012001d001901e880b80d01075a1020102c0315411000d50490000d0f40810041100c0034485d0408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73746009 1250 73744759 73744813
    0x110601030314090616050105100b070b0a020d1d0106030b060108040302031204020402190504051503010803070602090a091a030d030c050f09040e190506010b041a0307031b02010218030708 82
    0x980352440c030003c503913500d058885040b44c6c9603441c0c42c200003a81c280050403000901d210003d40703040c8806039460120000c801810f00b04c100381e020403e0384284015810a030180701c46406504110300707580700c1e6640038240720f02069907022000b030302241195221340c0300c551107260190b02640c00c0517400c0034011400040680180d91154080c8280c600301c03143d20760543e13160122503c8950343c4e20728040622901c110760082e417405459050004209003c00442160705030743c1c0c001d4005070341d03540d2040060441c880c507801c070b462a01d1401402c00d018410b0074698000801c0304a048034980c00080c6012015205074802c02d100040d0288060100e0781e0303040003d0400c44400400200750340152840180c03034034104000d002040c518451b01d4805104043c0402405015581c0c030961500303080c0402c909010082440034600300354000005940103110b64468114504100080d05142880c1c0000a001c0e40003011006200c84a07801860958500024000100c4078044003418004281800c0722a944142440d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73747259 1250 73746009 73746019
    0x50609060f040f211805030c010e0108070504031205040303020f0706090b0c15090102040303200a020f03010f0501080f0f010603152f0a090605030f0105120f0111030711060103031409 80
    0x10006013100811240300382565565106030821302521450102d017250b5121500a030080000100540d82c0701c0806103100c1020709002c01142c4501c0300031540c0c0c1c0710790b50001d80355155428090300d080354000001c00480b8000c1e42200c1074180105291a112000c9109810100b905848100984201000a4038203500072000b0f4845000c40f11902c290881c40031903421640e80d5000409100309a04041110005450000703490085004100056aa0743d243d41003c1d11034115043c081400d66825080300c3c0300401040000d00c200e50b9617450b01d40daa041c42c1180c11204c3d000d0010642e003802c40c14400c860460740c108a02412017150070305203034003c02c070b0b449018a40640c5c2e002066003450255900d441d590a03482c0320203940702c6800c10002c01000e0f40b0780143d000c01c0390420030300000892010300780d41903510448410354030420007150b241c074004030301c5090706455080106040c0b41e40e80860145120f024641c0b22600c0a0b0b070306402c09511080c09010040101e440390118050485800b0041c0000480280c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73748509 1250 73747259 73747283
    0xb040207050601120c0806010b0319090f030c0605011a09060a030b0312132103110c15040305010f0603051509070302060f0706060501021b0f060405090112050609060f040f 75
    0x41c0c0905100c800d8015040f000c1c807080c2540204002d02c8003481c010500d40024000e654181000724442d48009014281c409094000118a55015038404180030741c1c88a40c00144419924010b0b0445000c41829940f4510b04400001c5913080d9018040d620901d141105240801c00300c1000340341d4115142d46c0f0304160380c40c5114100743d1810401144500a07280c1d17141c1e1038095084100a0001c01034016100303048500c0031070420f21064a0002e070507035603d41042c00200d00c400032801c0c50207a10000d101d502a2003210110820a012070040080d01d0090b8024060b4081c1110043c05441851000a01e61781c00512401d04800440c464260040c202c030040e0f0f000540d070b83d0005922600002071018800340001032000810400344900c4000305003c1c006071103c086000e069000c003c1000348054007031400c50340c1051569070380300d044401802c0d004122112650b180d50801b21010310046d03048a00e4271590f0080366904800141035481911f59418450740c50f960795070790100b868580030003200c0e4030615132 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73749759 1250 73748509 73748513
    0x9010e071a1b0a0c09051f03022701091e090b01030215162a0f12050c1302070210030b060910020a05010507020c010906140a0e120f0a03080105040203190b040207 71
    0x801030901150082c0440c2d0201030400f00144210b420261030500b161351744100c8007007e0f541c001071540440e40c040324004030b0320340d9189d03100d0b00040600964034107048540300003203024a1180c0c4003518010702c00404040741c583d01400340e01110003080010344200a030034010001446c103e4207941c0c803504403150310f504004d0311b8003000004481008044661403a810707240c65500381030040c501d01c0c1c8005407641c40300151601444104640340c1380213890601d603a100801c2c00740601000b2580c4c540030040c0100b000c5500400e2070070000d40060b0803c0b440341200085140001d03210b401021b40003400140154a049800c10400800d41c0e0003401140540c05000390b40c4010039021f05ca00c500c192010f802600b01d03290000700040108009403c641c0900041d20088010b101104090700d00ca1030050030710200801d03001001903151410b22034861801d01c580c2980000c02840030030090074451080d00c55071060790301c03081084268042200d126442c5441c1d506590104c0c0800d82040908000103440103151003440c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73751009 1250 73749759 73749763
    0xf0f0e0c040e07020c120606130507020a050613120f08190e010213030203010c0c030203090f0123120f13170d060e0603060c03061e13060303020609010e071a1b 70
    0x3c40744a40903802c0258980c2c05418026071704419540104082c100301d14142001a0000c8424081c100e001660b81c0c00181a0340d0082246000c500d8105084622901d00441d09200e5400700450444040220f195025549805101000f0503507007591038140c55a03852a00d800c035140445403150546685901e06c0d40503501c028401025101d4030141440d403e6070541c0103140c255800000e8540c10421f4250382d08010030b0740481601c0554608440d0140d18013100740040f10071003000402400e0219020301202d00d2542c804004240b0803c5021082d807041d81c1c0e1038021840701c03800b280c040340d400d41503c45880000d0700020b104401c4107400705600e07040100074000402110f5054105800c0162000d060069030702c0c0030044c00d98041980300e105499071070200d002c112400c00e03030041d000c00038184850307004603981c498840c409500003540c4104441942e0741002540d031101070350300c65525403030440020794480010602c0b01c16102401e90b40d22408030b03403900c04142c56000800300f0a0041004401445500b01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73752259 1250 73751009 73751011
    0x5120a050306040b06040b09061305060a0c05010e010504030807030905070b03100501030e0109080f0c100207080405190503250807171005010f0302040f180c08070f0f0e0c040e 77
    0x26038869440e450048103001c221002c0796511886044140030400003000c2482c1100c1c10f619042e035001d03031a04456003040044030216046540e11203004a0260000c039031010290100900482c0240450144281e0460803104180c40c040c0010340c1c82000100418002d4200400c5a8401c03011201d074603580700981c0c1000e80040d540c0c504040308001d000c2029607898011101c11301502d20003040710740169039407040b2600c2228030f500c104031004140101140d5081c000c1c1c1c0c80d040e0700c443c0d0a5569010358900741725a031b40240181441246c40b0f10040c481c143d16855240d00741d0360041d00130040140468105680640c1403100100b03100c03000f10f0046550700f000d2080b003009041901d00e41640c85a0055110304011800c004d0442c0c01d031514004014008024100d802101c0c0c040e500000d0380301201c100d00d40641a0304d5060000e00c0102d0b50340c281006202280b000445055405944402d500c0301503100f00d0841510540042d08104001442692007000ca4107820941040141e403800c0e0741c51b0f11083c43e4000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73753509 1250 73752259 73752277
    0x50a050d06080607021612060c05271201020703080f060307032a050102030a0e01030c03090b0f060120100b1f020c0405070c0201050d09020609040204030b0117010504051203040512 79
    0x144050100d405c2e01040a80313071086002840846050404100b00c2c2e001d80c10700c1c0007070725064a4400c10140360f40174008a4982d8000c01120005034501c0e50010f89403d0448410b950081d02001c040103100d1206109462203207a04d6512070b0301d1034648100110480e40043d044030750500482c00000b00050103150401e034070407000c560004100c5014005440a0009584807130b06541003000712180f5203500c0642e003c00041c00b4240002c004140140817801411175000060000c07150780d0602030910b4258010a02c00c000c240c0e0742e145e00503003218030030b511030b811180d1a42c0b580d8401004800c80d03244030b41101010712b8010b030030030319042e1420380c603900c09442010306403000d80c0150f1514400c504003030091130361000d0241020000c0495540c0028024810701050000c52503a51031031740c0855071000304444584034014825900e4540343e0605500402080c81b03945010040c05440200d03128043c044c2c0c500c941d40080180c0b4000c210890a50460742c8010002c0300c003401541c11717161900c1440c1c40642000c80b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73754759 1250 73753509 73753513
    0x106080a0609110910030314120408090306060103020a0518120321060303070201140a11030a1107050f1c03020f07030c08060f0f0109020a02010b0a0801090c090209060901050a050d0608 81
    0x182180c10120340c80007402490f68010003082d0200f11289010303003007007422254903150040700f50b885154000702d68051071000005c0d5198510920051042500140000c080c3c00c44c20389034691140700041d4100c0c428204044049801444003990240007142401d2507404090032010180c03001c2a812030440c0c2c0701010310720b100c8400e101c4001c104151036925640c0948194019803824407035400190281503840489086881c0004401c926507214105000c2940120400c69032a9600600040e203418011441c3d2466407054035800203d526100550980b4050003500303442505242c03440c0710800c41c004500075010b510507500c0c000d402c0181000450002d6000c4d060030800c060500d00ca0360b0508501408071400a441c180c18400c503408020709642c11150860401a9900004039040c0d0141140003085a404140c2240018466506401010101e44501c4401c0709840c0c0b0f0703030840003c074000c4c104101c0c0c1204003440301c0c0b540c0b940590b00030224031056081c11801c1008010b108800da44141e0031184030b40d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73756009 1250 73754759 73754771
    0xd081c0e07080d0203070809010c020d05030a030c180e0c0708040902030402100309051018060603050609010b010203040b1905040302042306010507020d0f1a010e010303091a0d09050106080a06 84
    0x4140111006400d0b0580900303042244500002e40c3c038050690050503460300080e41010b540c2c0540080c210007640600741d285c04100605103a5140c0d00044050004241000d081c5210180314401e842e030380355001002c284065041c5080c0c4070603c40b00a10b1160440c0c1c00f00400c0d00030a0b5400c02400c000e2810140260350703442d0078814007121550704024081494104981e60001800100714692088400b810026020105422800d005900300401820a03032400c0008400e110001c1156445581c2c0c080c001c4c08075000c1c240c01241c1da0b00c15446941c100c2202401029090400b100e00641d6042c414680b243c1810b4594001408440080300100308004a0103954114210030190195200009003001814250703a900401c090b0308ac0000c000b803001011128880030484800d03251100904140c0c0f40c03041c0f035a1940e0b41c019920000303020a60100d824510000b410400d5441020140e035038030500d20703050100300086140a4240540111404d540b5084081501c03402001354000d0706019500200d86 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73757259 1250 73756009 73756031
    0x7020102010605060406120f1803171b040e0606071208070e010503060604050f030114130506101d070309080a02030a080a060f051009030506070e091e060d081c 70
    0x842e4080d52015000714000c1c030003000301d0b0b0b070070020034030740c2c0407600388040754020350311860400400c480e400c14101a5008060ba40a1690180700b900e503010740b0340803e08031070b15102e06007183d84124082e250241d031000c1005010310940103450a4128030003800b0716040640e1603856020304000c54030007100260962081080d010351180503062011800e0901d41d20714107000001c07810f40c2c851405101d0140c00b081d900e00d80076403001d510841c0d0340c15080128803001e0030044d080360407a40018000341d8003072045802140920304145405230485443d5030600d80354914070f8544d4011000c00501c84000d0580d900c1c0c541d40030440343c40003032420541c55409580c0d5019006000b414071480a001106214a00380050001e4409000300c001542c02c2214480c403070310b820000c00c8412003020b400041840c00b0328014801e4540d0000d00c917440856040311040c10a90f12040064540c5600021000646600c4004100c017030606400710040a4040e44500b403074003400c582012001d109480e502c0038201c1e940d0000402c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73758509 1250 73757259 73757261
    0xb07030e0a050a12020f062101140306010611030c070f08010c020106121b081005040b09010504030f140c0102031807060c050a0303050c0d0c0f030e0a03020709090618080702010201 79
    0x3040440e500d0600a0401011464030034050043d0303004541103031405425507407032006180c510000185019038039140510034217015030351201800707102d015400c0003081c010071226811725403200240040c140c0b40e1804800311b48040c007141004c0503a0104020340c1450b0712060001c0400342c1610250030705036071300c2c4c103489900311000c44150f0f00c1164501a810f0004003181001c2c0c1d010381d6008001e24420850303000c01c1440440342d43e40003800a03c039000e1503c4030030580307400c6144101e028401c855200d5071260141070a0311403c550080c0090802c881802c1ea0502801a60300d8aa4801c0307261070a02a00e901000e089034010f0301c40e95191010500d61035003100b42048108042c0660349003103030050035595a500da85041c1030b40d00809060325040011403824021040c1c0d51f100402d107100340801c101e40d0340080c01494032140180e0000303003084051010310200003503036850310350b0660040045c00d280100d8a0001c061349181240d81d00e403180d20000e0a070350740344800c4030400d006e4082c1c0c0d40d440b501c5200180c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73759759 1250 73758509 73758527
    0x5040c0f0b18011e030b03061003020f09091e0f0c030102070b0a0b010c0602030a051f0605040608090c0904050607090602011b0c0c08030d0605090604051315150b0703 73
    0x1800c1640e009040c0485003002099844681299104078210340603080141d0b071004c0c0844c010103904c6941e200c2580d905a01d83c0051420a03015000d0758920b8952640d009003050440c04040e4000c2d040081a01c060300740381c450141d018400c0000c2e0f0384280301c000c01188140712070707040904031540801c950507401441441000e107440d0044000710300d00b01c0c1e20350380c1c6106007000400e1406600e0307070f4010101440e4000c40305000b0540e40400300b15135030300e030500072100140415a0010f00c516222070f40700050600c401040400c0d140c2c2501c071581030924000d012500c802c4010b20807051402101c2000000f82c80300701d00903020300c0c401c10280c4546d1802d040002d010400301e602500071603041100708850904541c01c0f05810b001341c3e10302802c0c81d2150303040c2641e0084090340007444911000a440d024440d203a4003070760030303244203c810304010784440e42000305403603060b07803004021000803014000203156040c41c03001c12008828086400346a9044c0c0c0000111a0361000c1141c020014181d810150711075960 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73761009 1250 73759759 73759769
    0xf0f031e09020109050f0109030b1506030a02042102153603060f01060e01080c0c1501060f02010b130e07030f080316030e060403080a021b03090a05090705070204050402040b0d0605040c 81
    0xa411560080003c08c0340180e07100280c000355006011820ac018985d000300800d860140c511a500d08100c64501c000f50701c90310424440c480c180d103940419420b1041014109500101407031440f00e07005044c030b0510307032001c0a4000d01360680c90f49051540c500a00851720440290180d41c02c900304c0760185410080001c021000c0f4042d00c000501003250404007070070003108207180030b28081c7d0354000708000d6403081c601f0411f858070891190118150490b4107480c140ca81c2c5640b00c000e9040b00c61402d07800d841031030200940c8001c150030060342e002e1060340002c03d54100d40d02118110380d5261908a4000146d4009843c90703030001041042d0500b414070b09120b14203d5240400511310140d540985841002d0030040c20000a4004a040d81c01660151040340400340211000c03040c0205000741d8a511028000d40660103152001542e4609600410b2040e03819890b0f1b039180031841c2d03003000010300c00213104070f9226035035003002102078540c1c051008686100c0d42c0c0014036410941030000000c01c040e445 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73762259 1250 73761009 73761019
    0x105030412050901030902040f09050706050a0503010e090312070509041d0c010c0510061706070e0a1404020708030717010e0c1206030120070303050601020109030f0f031e0902010905 80
    0x601002a1074940340c4400d50701c0500c1c01c00e88031140200100c1c09059a5400a903000742132008070048512141d2002405610036000c96410700d64525040d0b4190003030000000100700140010403003a01e0700307401c00b030b40161440c0a0b02d10b0a210055051200c2c0402c0ea10b0200245012416090720b08041c4500c800e031002c0d405807c030100d4121030502d513540d88400b8030306041051401101d03042000402401c5241a4066014040c003501e82448080e083d40c110700e10503031441440041000300f4081c2d5200031450030003030904200a410a20800c2e0f810b41c0390703884d42c1d41041e401c00c484804180044091801010f0366500d40c1040a400302110a90000c181c01582055041c44240070083d8850411161810082401c2c0c880e140d44640000c0c1c01042c032440c8102d500d01007650500a0014880010b010591181d24100f02540f10900120f00722140140000c01145000495541c018016112940b210140b17140c04640c81a02581c4864185c60b060301e075003841625411400115a0044140000f41c0f1096413 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73763509 1250 73762259 73762261
    0x2a0d0e0a0302041509020c01091506080a23010518211602030703051207021306060824030a030906020705040212060603041a0906071b02030a080c01180c05090105010503 74
    0x2604103881403100078480c3d569120b03a070070307100055280320000f402e4040b81152102004002580a448103c1d1304aa206c40b070041c070960480040c5c03203100305885c40c403c002c2107000f5265903005426001d40248840060315a07031485e0707115000b401598032441d840c4815846801c840b141c0c242c60704120007910b180c86c0305610300e0502c00c8020002622845400b035024002041840d001181c02c000e410b81002d8954000c1840b41030003c05404000c08815100381c076a290350ba8550038120040b10186c0c000d407000516202c000c83c903602034079244000c40060010300c038042000760200080c940b05000030103c010030307010041000041e4050211000074241070701c00754904034031115400701c6e00c400100114494080400441c0501405501e038003056110100290380a007407000341030740d50302400c4896400103491900109151850804007006555001d0020021405990391300c20943c0c120510749503041d940c40f040a039030801342c404c3c00e0551074010303100703071600f541070409000700c16805070011410311800300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73764759 1250 73763509 73763537
    0x902100f14090406120602040e0105060309060f180d0903202407080a0503091002070f020d051606030204231302030604110423190501080c2a0d 63
    0x35021246107544107500a55602c10780380024000c0c10581c0010700150003911440c0c04200b400c0d8000c2040d12a10300d10514280c2c1e8403010032441c2d10040390102040c1e00500080362240070005803c0f50000304c88140c9213922038440b00f04901d4540090f107240001440c41c5400c001f40300041903405580c0c0c5000785e01c0e6252441e1440810080d18a01080d0100c071020250301e400c012480303400f9503401950205e0350607614940c034400100300790400e0f5800c880d14091000030300d00700711321031080380d83d840d0340420454540c1e80c080c1c0801c09413088842095500d405594030215600412034100780140800d030301d0058803103007003a61560030910b08950328074200e0800c0000442941e900c0624107402c80940d84056925030301d0b44003050140803180c44e0860406408240071400d10510440507041110010f4001165903801007004810369440140d10400c944141042c4400c0d4440d072020341e885100c02000714500300401d80e41d044080058a011070070a514618038440c1c0340b0003482981080e108034540b0000c241c1e124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73766009 1250 73764759 73764767
    0x712020301081e0a0503270405010303080105010e040608061e090105252715031e0e0304030b0c13060e060f030601020a050f010e010f02030f012d090902100f 69
    0x39200c0440c0f5208107004030303041070ba010006080070a90040a490b02c2e21201961800100071031001c520314012241c00102e0b0604052140d18120ba030548e13101074003646414015104a10407903505500192503201c081004401081000d000748240041060400c0c1500c6000b11903040c0034041d158582d043c00248414000c0c80344050b96002c0042140803400301990800760b03044118041c0403103142e140c01805140390f5008008403800c0b207800c2c10207980c500b0000c075002c80071103040b041030303040084000c0c2c2804100030181d4002c140d0010020101d034985616a11a507012400c101d40420728041c002a20002542101080a008209505103280500030340740015456008205042000c2080480010070903031082002c3e0003043d400a05440d01e9425003c61079020300000ca1080704290708241d803840c0d98140d1807084038400d00d03a01060225903400c092110b10b8954010f19880070b80384050021285440b08480c4480003015100e1000442c00d409106004076915a000035406100e1000b4001c2622904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73767259 1250 73766009 73766023
    0xf0e030a050a03050901090e040b240d17070203060103060b0f0a12030c020d080703020d03060b0c03120901110c030316050c1b01110111040f0f050a1509051008071202030108 76
    0x850704103180c0740d0082c81d0040300d4075007d40d813103520f00480304014007080c801c511426500820044038000728204560031554010812032007907d030002c2c2c1820900340400d100c444041045030f070080500b4505141d5800180c0380250a070015105941d440f4150000c42c0380c40c01e29644411400d880c084030603072904407840703216241241c020b0217103c20004030108550321101d40c0c0d60000d03031103480961a09060f041c025078802840200e840481d28180020500300c8a100907a1582910f9600075803804605001c0078001080c050024280b40d0340340c2c41c1c082500c240d28409400d0107001e500045842e49040394081186031210003c00d82400004c11680140640c0418420710f02040c0020741c040164079400100c03000d41d4501c40d03c4c9915441c201181e210003032610b00400854031740502c1d0f02d18007502d80c4940e40080c8000d201e2264080b009507010408501046007148204510f0704150714003a603140c0200741c140000b244d0440000f030810082020742500450885400004510110700355030400104035512a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73768509 1250 73767259 73767263
    0x3010b0a0e040f080403110405010509060f06070c05060403050307030801061d0d02030a0605071d03191202031309060303230f1605010c020609120a02071802070605070f0e030a050a 79
    0x10718540002d050041040c1c000101e01e80c07203d4220b5440d5582d091401c0800d202103400c5106a092600010301d524020700101d00547e001000c1c46400e081c00f40400030181d105a030308942c629003008c1c0c000340c0d0396144d4019000443c0518060341d03a031680c40c41c0c024040c4205030028424044000b030100005100d0485038008120140c881040c0080e0034000a403410011042c018a01401c0c88104008654407000c402e940441c02d41507402a5818241010b841d0307039403590190100c0000c0c15000c80400ca2000c0c00308907219060050702c0c41e220643c0c980d104000d07145d400c0300d5035194072007030300f0401c140d8007003060850072154900c203440a20003c00c0d0b0003a03601c101b0500791428400819020035464500409000ca40c1c0e0040082182c0d11071108081d44410085520702030600a11a503440800d030290f0480f03000300071945c003070800541044000c1d100444c00030000c0750090390900900e400904030380705140c024101c0d80c40d00142d03418011801840303c1041044c0b14040d4001b0b00d800e400049001822a960039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73769759 1250 73768509 73768529
    0x1140c03040b0d0b041e0e03030402030604060902120a050106170a0f06150e0f070206010614090405280516020a0206041203030b0607060b03060609011203080a020418061403010b0a 79
    0xf9901c00110000f400400b24000c0d0321070300d010081034030311044908146920807008030a00c0712950049400d612800100c4011b90940c1200c0000340c0044d80e164080c595045c8014405210043c001c000c10740b62128402c012903040e0340d680750074044c82e054084c0401d1b01640031b4008040c400700a075650b125030514120010200d64a03124001d000321082850800500400e20400c1c20702d11b40035030045205c0ba07065980c0c00140c0074000021407c1c51168880c100b03808503803d0458580301d950340c14030000700340003050502204007680702451445500302c10b01c914891030510205141c242140c0d0485c40040d100f5a80d800d65010484540c0180c940310160340889030281c204801034201800c0550140001036026a07114000140b050200300680d032200c00040b0040d400c40c3c2c641c1d6a80c2c01071000b800020300440a40307000202c050300000307204070607241d8042690040541455640c4030300e02420340070100080b0310340d0385880703003840380d04412000003e100c8e004070001e0042c500b0b600e02240401a460140382c0e090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73771009 1250 73769759 73769767
    0x14061303230409020d092a14010309120503070806011809051803040b040806010608040c12020312210c04060801050909120a0309060e010b060f0a0c020405130201140c03040b 76
    0x10300300c0e0401c2d500140b842400540d5140c014110481c001d142120f01200c00d40b145202011841500e0712004940049940f0710030000c40c00c00020602072594102c140b81010744592181d00050344c901c002130100d5201d0388410343c8030704081e00007600b441d20060056040012140754000d00368440150740c0c044881c46400060759466081e9200b021001c280100f11040c4000a00010f1722030040300117104580000d8180c640c1c698854104684c4040203890160040c4000e54044c0800800703403140807141d501c02002c5446480c0a503a5070030315904045016000305a00010084103114200d000075803000050103440c1c43d050810300042d01401040c00b41c00c0c001c007103c074000743c618142000345110301d215080c80315407030300882d40004010301081c4108407034a90a00081d8500208140141b80031040010300150808010705442d90494001021210400c01016078910241e1500d107e454040c5042c8245035540c480580005001b0841901041521003c1003050464000e0088151426603210341b6000c0d43d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73772259 1250 73771009 73771067
    0x609100e010b030a03020a03020d05070c09050601030f06090515040e0a11031e01021810020d2304030501050114090421030914010b01020d17060904020604030f14061303 74
    0x100b180340c1495400d44200d4120a051540000d070039004a803007942166007e50980e41c007241c15004280006016030002c2c2c005100b002800e0700403a90002040c9000958020851025001c0e920903030b1054044641e00c1c01805021106d840b0706801c00401a1802e0001c41408110182d40700801600a81240d0a00414800560302401180d07030301c055890001e11820301c2e50381c1c0315000307522041c1c490100b0200c12251202ca401c00d1080003070310245a070003502d4100340848081d02c5000000303003561004140702c60b2070b40303503001c8034006000994055030000819604004a015221104103601c034800c1d01d0801c00c010000c1d0f68030011008041c140750070301c2c10041040b03005030060f0200c584028401c004015000600d00030540c0005882c0c0f4007642207808448030710700180c9146800500001c952100d0704001402c5040c00700000e80c2151010348070750b14151b92910364140c180b140c480c040758044641e0149400140b01000142d0f00950380c114103001c0b40c1d09a41e800703011011200b60030306268010140c0380381 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73773509 1250 73772259 73772261
    0x714090109021b0f030309011802030d0f02030c07140a050109150c0203012901080714090103020c0c0301060605070b0108010c050a080a1d07030b18030a0c06090606030f060c020609100e01 82
    0x5400d034518400c8900344d54882034400d0310b0b90811035910205629000c0c2c400440e444e640342250445030050080c0120000d03031082125612402d0800000b5072104225088032030208100d080000d040c1401410703105441d41c410400030100c1a4170181c1040340488092061b40c11250407040007000c00d003800140d0081c0303403010034003401107007030344444c401c030342030b806e124048100b8030107002641003641d40c1034165641800981b080e12080320100340740343c010300981d64194003030381c000c1c0300c09105074044404060400d03000070b081d50707866003014000400c007003000d00810440c100e04034050130300b500003032080141c0480c004003c0d0003481c604d8810043c0c50408150081001d91001c444c01c0b000e0718908030310200070580255107000611040b1484818400003070200702400507030325039580848014510f04280c0003004c880c00c11020b20151035a40da01c1c4030391000103000348140d1004500c07802120820810300e040880031680c3c3c200514044d5080a010400c2041c000300b00028540d1100340b00040b00322508051034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73774759 1250 73773509 73773547
    0x20316050712080307030f0510061103190e03070b21192c0f07060e011e0806040c030b030601060809120d0b040510120f0311010207030c05071409010902 67
    0x2606411a640d0050501540000a6205c1c0001751418441010101803a004844085440f600c03007800340071041c000540714ac0d441c800d4003140f84c02100d007000300011101d645030791088207020208004141d601150300f810b01c43c280061040c41c0200c0d05110400070105030b0640c0321299807030b2410300d201c0000c2ca501501d042030801d551341c1c40003c0001e0310440700d074059a004406000c109070800d89001042c41d0b040051081101103448000d0001c1501c2e0020a51b05030010328003603410b0184581c121140402c0044085082841c15641e800390f5050003030501040b202040740307040070141040c40d4002551800500d25044400310b1030030b88515610b1028045c02c141100280a0720b010300014000c20240c00e9812512406104444c1000b032501c5850784404801610b100b000900c0c440c58517524041401000d440b50098080d050801c604003481751590300326401510104c011880511006003840310401c41c91000e82607136441848a000360000081c081c1205104407072000d07400041c0e002c080142c0b01941 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73776009 1250 73774759 73774769
    0x50c010e010903020c300a0b090d09120519060b040f02040f0806090a08030a0212010305100e0c030703060b030109020303070c03061a0d060c0306080d030f0605030d0203160507 77
    0x2004011464480d80d4080c104a91081d00184a041c40700140e0b440d2029029450200c440c10700141503904201448074204040c6001c0c000e8010b55060401281640c00c04030300c68102040a80615400c80c2c9000e0403080c000c0d080300c0c0200c40c9a4058a000803070002e00110001d06003180101c40401d14900078020b01588101c541d00141426610301800c0c0c03880d0081c2080da02c440d105140e045840302c1d00c4036507440f82114480c07042e901040b900c801158a40000750740080b86654054600058403c182e0076034002a03104a070a07610840025030703489a10712511120041400150501e03006000003e43d940c0f20750700024bc800d41e6900380c0c01500d1340c3c00b5445014141e0740a001d403500c3c0d41c0c460410800008103888240c4046003081e80da8401c21711414501c2010000044c04217241504c1611044020b010881d441d909140d44c8540c00b0440300c00401888007a01410780d004100e041d81d40c2402c00c140c0d611940628041d5204201043c21140c0100954003d010607031004803880d80c8a0030054a1b0188503031007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73777259 1250 73776009 73776011
    0x30203040c062102040b0a031b05030f0c04050307060815040507360f0302010f08010320031603230703050304031212020c032808010509070201020c030d05040201080105031c03020307050c01 83
    0x1981b161003102a205242e110b84041016214180305212010402154900000c108000080c05606011825900841d40440b050700700fa40701c00200b491b00000350003240c0810b01d90010001c40f0145200c0b03607840f403a41520f0510440c101440050543d010040c40e0702c5c11041545440c001309502181a81c1e00205072003a581060340e078500d0820116825400245d0001d150003540c02c3c0c1150107160840e048039800310900032500380003102a900c80c8150140c040d454020742441c6412015110a1030000e5401428100c02295906800006220007204a910550410542000030800210903102100c0d00000307601300c00e5425440895614222540c46005176101041c02604410000040c001071903c100d480c101c80c1101601e8942c8881d4444034090000d50030100500079420b207003110940040312400050708100d020450542190456808180c0c00383ea1241040b06544c0e2254140740104003c2d0f0203414400421030350340c0d88116030a42e80c4024160000b010a02c070a20410445001e0303200200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73778509 1250 73777259 73777267
    0x60f0301150f0302100804030e040902060d0e0d1b02011403131205030115110d0f0908030a03020c07090e0607050a09050603010b0c0706030b01120f02130e090607030203040c062102 79
    0x3421a52401d043d02080e8000d500030b03544080d0140c0100d600500864060701c50320000e0550904100c040c04c0410703002c0f40c002100340070840008002c1c1c040c540040c19801d01604941c0a00c0700010540d02300410322094269015907072901513600507000c5c840100307003d1600d40c0c5d281d4407241380d0444070840b21001000800400e094003012644100614180c940e40c0c20703074500f1a41ca0503c02c03209090003243e19038041c1c01c42d50f0842c80c1c080c002c001e44240b2900030f040c4444803558801d900b6085400084080021980025000348010b20a00281c006806011020802680f0b0212040c0c0d44080060445041c0140000d104605c540034001c0d08000b0306008203580d03982d43c1c46442040e201d07001001c03561118400e00c440070803210b010b801080340140c4182d5407030306107000785100c00020b88040400e036000385500700441c3c84150044142800a4191404803240b5804c020000700d00c0c01c94004d05003020544148144000100c600c041c040454959242611620700d81c4900707103008582410b80c90b00c00034030000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73779759 1250 73778509 73778519
    0x6061a0304050111030f060603060103060803030c070501200f0c030c030703030b0405161b03270303080c04060c0206031e09010501170304050307091805010207060f23060f030115 78
    0x500250301c614403400080c41311403401c03504101140800d031100a8580d40c440300103562410b0060295a00c0f220524020500c195a07498150540d4000d4a103003654200001e4003000f4414240202e0f403030001c8042540c4081503611801c1062405500d40402c1c245200080390b1110103410002e440c0ca03060201c065030380d0b03101a8070303001e03008100c011001c07400b40c0d09240028540c48001d01402121180e540c583c0e0258183c8480080c40103071000104030140006007101c02c0501074800102208604440d0510100d5030441c1009821030500512140c58035038108030900055138468034140305241d0503940343e61039440b0b45601c0c0e090103819624000904003406c04000e04440150862030403a40e4004030400d00c07410254402c1c1e180c0c4558016223815078420313501002508815032014003075001354400c911070300ca510380c2c850b0301b664031140054030f095441d0401c0e8114100c8a125901e00c410325800e0300b01200342150811100c03084000c000c184030f000c003080f07000000c2d1030a40007803a03114102c0c2c240c0c0000326112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73781009 1250 73779759 73779809
    0xf0305061609082d03070b010302060c07090e0a020a08030c070306020f0408011e060603060605090907140a020303070801050109031e0c0b070f0b0106020a0c090b06040504021902011a060d05040606 86
    0x240c8009a54a9130240305040110004412075840c142c100c034440e503075030303086400f481041e910910079255607200d061000a05600a441000d0324444680d004c2c1c20400362900420407a0040c0750007165030307908104051550421b0009103442100e031300c1000941c41b8580012008514020365200c4411542400c00c00c07007859180e2021861240000d00c0c0810980b911014100c0c03c4508074003c05000c190708000b19141442c0612040360300c0001d500d4030011b1211100c0c034044041d00401007010140e0f0000c01848011508030a05c0c60140038280303461603046140d03413140458140d20030046d02031098001c031004207202c016550800038200c9001c0c4107584003410307d0910001e030100f01041e03514030a02e40005c21043c0c408100d00c0002500300c2d401008075400c1844400041100c41203c66011408101c0040e464950740050400d05a61440e504107d600841c4003a0948190425640300e005c0001031010103691220309488424a00b82c0d40041c00340d50380d01c4c00c01c00404560304940000302180780075107295410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73782259 1250 73781009 73781053
    0xd140601020709051005010c05010f02041701061a0f0a020f0d020304030506090a0c030219180606031d0607030f0609020f030610030501031707080d090b100f030506160908 75
    0x801e07800c4555a5942e04002070403103006880c030a80c042c40c860020440b9600c1a1702c0c1881803805400009101035005010600f248d100c1d50200100840f12124064088020b214040c000d082170024070000b1584110440e83d01c3c8110070000c4003507807022801c01d2000c0e10070400314090501c4401102e410403043c0d000070b03540c0c3d0020312044402e841040b00003001440080b42844180c0e41c44032600b10018255420400d201c115111107294074100508009040c2031580c540c0c540f0710422020008080341008402410707200c09800d0103002d01d40c00512403000401c002141039200000346000210703400a2003d400240180742d00c880d00c0345002040b4110f050207028002c1d4060602103d50402901c1c00800035020348000340320140000c4004000f0380d00c00c0606000406281e4801c101300340c5000010b0b080d5508484480c1d50a51b001c058070000c1200340342ea00b000901c0602000004100000c0c65a91050f5440d900101900f654a9103603862035900c0c1e001e02c4206020f004a041911241303c0e80b07107628044110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73783509 1250 73782259 73782271
    0x207050a141c08190612060c050f030a06051005160204050a1503060c090e09070e040c05061303020f0f130b0307030f030e030d05040303020d03050711010212060301141311060d14 78
    0x921920001d40706504c4c1d200c1c9004031841c40c0e083c450f400b26180c8402c1d000b8440c4000c610f0a011082103a8564150110011881a080e0b500300040302e034245018404050b10030301030300c1c050110810141008429544001c20100d604681c0401c0c00e03607420444002908403c40030b10540c40094401008000c03154103d42080b0301242c3e1690580c5548040e034102c070100554080f00107410000e401e216480201c90b280360302c50700403caa0000c075644c40006c1201a44003180051b00300440c90024411854040e11483c4021170484204119070050400141415045c0840005080c1e90f240000c2041e1418044200115044190301b1001c14203414050003056038038a00500c83c1c021405000d10b120301402c180c41c2501d070076038014600d8082140d8241c0c010000a44800107100340c0740700b12011220240010113481c10302c02000c58141c01c2101c241070a4504065200014420480c01c016110007141c3c0c6c44140941c000e09044040300c582c1c80895a24071400c070a0789050307403c1c031354804000310a080c07480303004031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73784759 1250 73783509 73783531
    0x50c120c0f01031404140309060a0e04050f01061b020d060905030d06050d0f08220b0406120506030309010f110102130302030609010515130609020412150207050a141c08 74
    0xc9082004504982100184c0b80c004100040030038040b40d4642807280c0040d0b02081281c2c50b00c03007500009140c41d000098035400003130801c80707440128107140c0941500040c4c0300d0341c1c1041c554101807000e031040100503189600004c2c1d1003111004e558502c6260b265858102d4410008004ca038100113440341c2c40008070031645800c0c10b100259506100c80382a001d03c1d0004041100c0c0821550f03080c440da031007400021300042070b80e45084109020f4500c083d00425030082c400e540c5902d00341002c1c1c40e41070700240c40c00c00b26107044200704140d14080100d515400c800d18083d10344d02d400600c1500c2c90b044a0701c2c11640c9602c003045041a400d0720000300401e41e4022402c42d800c0d075403000e09003400d0303500c201c41c5100281c100c0d444207001c5013010360381c1c901903500c0740c040800d10036280c00b405000c03030300700750300c5000c004121a072044140041c0074822003426940c4442940f41000586465684043c400c2d4010081581003480c83c01100c414005a0104800100700f0780345645502001410352005030f480006003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73786009 1250 73784759 73784779
    0xa0506030f0706021902030f100203011706010b040303030b0a1205010504031209031223090102090918060c13030b1017010c0818011b02010218040504080d09050c120c 73
    0x2481d03000400c40b00720f40b41c0d03600070901d060000b24030303c403810700c3c0c00d4049802d48582864a0404001070000e0340200046600050722036151001c03404c198285650410300c144c1044d401401006001421903044da03401d42030104d103c00c410008274032200060750214416002001c2c04d54100001900800d0060380039981d01c141c2c10200f491100300702d40d8103060040204908003031001c42507d082d0000544040a9003500c0400c001d103102000250748225034004e407036580040d5071400c600e4046042604006070003524609000000c181e00c0e40e901c40a00341d078203c9000030484d84155050520503101855101501d1241c50415405080030194035004a4010800780786110100480501c41d00f200c90509654076072903a156154041c41003541100c554086540f69480c54000c2101c0c015044613030389170340e400165113005d00810061308204006d400da114604020902010401030010b440c0842c000b010300040d42c0049e0f24015290a080245032908181c01203003020391028081840006094203451a401da = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73787259 1250 73786009 73786033
    0x20c120703030314060f240a120515030706080c0405040e060403090501030e07030b130503211e01090209030f1c1112040b0d02090a0b030105040f0501060e15120a050603 74
    0x1080c41140d4040d00030301d0030001501c0910301f2403c0301c0d00940c24003001c1000181c2010300c1c280181e02018820780801c21715511b081c020303903140c811544e004000030101300c0084191000603464080c01e200f4481003104040201e031f15507220300100c3e001400000c204200d0103080c40045500c41c4000c0741e0a0b8007250781320b1000203031035010b800b0310200e2500e503102a040300c0342980c0d2080c00c1d00344060304034046000d040c480500043c030100010912200598070450807048490790070070040400034000d440c40b100103a100c40c01b8481c41141113040d90b440c110003503241e103642000700780340840035001d210640c410010142c2101c100320a0b040041c01d0700703644060000105080c82599010b40003a03540c11070500f080108900d111401c080c19110035414000b43c035054940001030b441a5454000c00c003480c2d0000010401e030319040c0700b0080301c004244002c1c003180d03145c080054002c0d10442c3e20103000740074001c3c3c2c01c4480c00202080300c0201131520303402c0d0860b0600181450040c030b0103c0d4251b001e44110002544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73788509 1250 73787259 73787291
    0xc030105040305160602070b010e041203140103020103110903070b09040c05070b0601050a09030c090515010206060906090c0d020301151b05060c0d0e011d07050a0b09040c020c1207030303 82
    0xc407464050721158601000c5040031540440003640948a00c1e03400c2c840b010000e101c03c1030240c02890801169601403c09003010110440c0c0c0c02d01071000d251030002800c001c0013038a84064116502420000781c004441c50502c9000e01c03405030030f50381c14040c40342c0125a200254000d0040444140c80400140c80406c500b030385d09108143c80030b0310490411001411642c4903a00800070880703145026a00e2030f64036511000000c000b42c0248041903100c070104030341000d060000700c828040901c01007125060020200300b805c000541628001d282040c002035150070400111600b41c1d00d8254119603035a51131582e00d5101d09050321020001d4906d41c14a441c5a09004501d48900d410001512003600c40d16401c241503808440030045017903c40441b03419a00083c4560001d580c2c66074045003004465140e03c0d070a280450300120b00c240c514075014000c0d000c810054600101d41641c1c002450707443c034401a03140c4065460041c4e0701c5802d040250303a22030800704845045030b03c20740703007449000c01c4450885 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73789759 1250 73788509 73788511
    0x6050103050606031f0c020c0307030309031a040b0f0a0213080105100e04080f0304020f0604030f0201090801020a270503010c050712020102160f02041b030218060406020a03180e1003050c030105 85
    0xd60050710042040c5a81403442e0311034100440ca60045402c0090001c0201c1d040003400d0f8402d0340402c400c1c1c5020000d0107986800c0c01c0440125013f03480711403a10740d845c0144e885000d81400e0304c504800000541d840d0300c0c0d81c11180c030203813079150782e0010550f03452403580a04000c541d039503040b1341e15400c001a0540088800e50155078064005401d00b00e00b01e80d01491900001e10a0364400083ca10842184d00c500c0000d0000c0d600940c001442509a03000161900001d50b01544c0c0c60703881003201480c596401808110038842c923100c00155155000000f84a0343c030283c00c4190b05520f4280703c81c00d01074007c0c005103c080e00c10500030000301c0ba450b41c00e23401c0780140701e00c98003228495000d280000b8032000c00003081c240700070b00c0042d2600c0d601c584400551404000000443d90000384500b44000707800403549610402c07501c8038681410400001c1d260103158400409022009200b801700c0b0216420f180054900200d0000c21454142c00003402c2850500c0152040e0207850781c3d45941d414107000d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73791009 1250 73789759 73789783
    0x201020c090c1c0b120d0912060b06120106020d03060f030b1e0903041a04031104050c0c010903180e100303120e0304090903080c07031b1703040605010305060603 71
    0x1034406030258109011081400800c000b036803580802c9400407464661014454a903888a000204c20800c00c0510601c81c1440d841080194400d078160a28207a0000241080d01e110301081c032401c0020f498500301519400800e29400200422004110814070021604039002503085509a14a140043d0215951802505614074200340103101145815170259005103085003008192013994000001c03213642070728246804e8000190030007402d01003c6000b85441c607071444e4140360503e103a070ba0080500028054600564807180083c10b42c004030300035aa030360f15944009000180b92464002e05600d489080120b080b642400086681401107030464480d24080d401d0411460464505442c0741624a007068806500e40504107401c3d5014000b61008040010003c60000580e1401030100301006001c49080340f800c4c0302220200390700c0546c0181604507050340c118100003d0a285003440e49140030130000140c0001408100040384d0310050403280150701384c6040b034032100d0030035031204202090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73792259 1250 73791009 73791013
    0x606040308070b130f0309050a051912030903050601080303010e0a0501080c12071d01080f01050c040b1818040203010605010207060215061801080601060e040b06160501060b040b070c0b0304020102 86
    0x15400081d4500b0f03209504041001004c01407084c450b920078444000c0024110001161860100514100007443d0f8019203821640f0600e100f41e040e082c024900b03410b02c505540302c400710700054107060080311158040d40e0400103645180da1104801943c80d0b000b07100c3c030305540e80300c007000400f00e01082c0324440c140c0e510301000d440303d0150b16041000962207032051440a00514200091400920420812195005100c100c1940c0740100b803505103001484125400e03410f01d010000f01e11140006c45d429285002c407410b40b5404000d084001c50440700e050310340c20000190240c2c046001c40040301784124800c80085c0200f685810049072114003500c01e21016034410003664100945140030603900c0400030b0312201e2640380d014500c103000e01080c0d001544d541c00503401840110342c0714400039100d09007030b10203005a5107020049806480f41000c4480c80c19444081201005400c0d0440e100400c0103980640d00c95403103282c240f0550340306010894007100d80c000000348195503601540d10032601600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73793509 1250 73792259 73792267
    0x140906040203181b03011422030306080712020301231b070c03030314010906030c0302131803030b0109080601031a0c190e011d0a09110d020d050604050606040308 71
    0x1480082c0d0009050792841c1c03803148041c508402000c026202c0e074280008240454107544005042c2124003a090021481c0c0e90f038403c120900b0f401c0305081017a05500c0c01e15011350030982c1401c90040460780c2101c0d8a42c00350384000909203201601c8048198000c07002003101d510032888450110303402103400d00c0d00a011000056016050041c0025941041000c1901e00360b6503070388a60200c1d01c9500100c012a1362510120032100d10900001d01501304210200301d0789081d9151900700710140e110003403203072444105020424504d9041598254940380b0310108501ea00d29000c1c0c081e10345030007294006290324400003005040055810b0403283c2040c0c96007540d40c80444c4103a0303510401014415801d40802201c40b20506011024009244981c1c03a8030200043c4400100b80455005011403240c401854a0040380d44d00c001c60740483e400480000790010410100f2552030054030205151300380301055980c00c000c000c0d0415403041c001101e040100e95242c60810090f40a54040608070070030903c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73794759 1250 73793509 73793521
    0x3001050103030905032b020f030309061f0605030a050c070b1303030f0209010e0f060702030d17070804150b0102190b01080c0102061608060f1201020706060e07050d091109071106011409 81
    0x6446c41e45c8400380744161070300600000390240c9140d10503118100c0a500250412036403482884044001110f1488400007a600c0c1c030100030a1400090210221aa079800104102c02804d82c1281e0040e90b000400c44898a01034070301e003140342a1100280c0129040188550100c04648204d8105020503100c140944204a05000032482c00301d0100d60003400410809015a40c02c00ca0f020341c602103551440e010301d010914103082c200d80a41086c05021116081c000050300032400040c0318411a0800542c403644040100e203032204103956041e44642e05a0020b09201141c4106d6050760181c03021124600c0f403860049907940383c01c4540e880c1141d001000034101c640710303404080d00a080240301c921007283e2080026205507625000d0340140e903001685400b00020750068000a01342d280c81d03000c49191000006e4101d01c1901d04030650700350341d507a403a030400100051007010500c02034007106140c80c0c014005030891000e1900850785215010000442c5104007407014050f040c00b40404005840320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73796009 1250 73794759 73794823
    0x51b030301230607080c0303040606080a110f150a03090c05090403080f04080d0609090b1b0d0221070201141815071b120f090b0306300105010303090503 67
    0xb02102c0360301c010100140808601450b014250811288000d965030342030a00d862130490b440e80d8442005601700244200214810451100341c3c5a004d85108000030b1710351000030380c0e0500a01814520810204003010f80ba036141d0b101845851041c44200c10780c0392640c00700001e150080314010009606c1d1400121402101d4500c1c0da041441127121606101a0715100016680b007504021006070f81c8103022014050b15107070068029135140310900040f03001c00050503080c0718100b40300e030389a50009801d6411441c203650380e4040840c007401d000c00606056070000d0181132050380c0304462007400d8000c94981e5001c003070700c85d9039001244001c00341900600c0980800800061204d0240012200310050300500d000f000d107006403081c1d10b2000e4541040c82c010300455010074400040188000e018040300c1840400c40b50403400850700d4030202c00300d048110f002c468044050b0105400305004c01e005408054020506881c46500d070036540540f100c0505a4079181c03900e00c449a1104100810111020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73797259 1250 73796009 73796069
    0x1a0303030109110c1b0a06112104080a110301060602030a0c1b170f0d09030302190f0f0c09050f041101031d0102120a05010603180605071806051b030301 67
    0x18402405044ca02c1c0103450078140341813481402c1c41c0ca601e24600500c06c0c60f00300380d1080545500d04041034005280c1001c595182400c180010045503142507010f1000245015203008202500854060140701d240c1000c0c07a41d84008020f02070760030f041010800d00d0010058981041d05a40c403c4101c290b2038481310450b00308030070000e1135035881c8480451400408c000e101e00e2040320130014810706d451070040601d42000c00e48140d0070030051840500029030701048170f0806084140501c21541d4540c1080c0b10341c0340d42141c00a0224803107403a0b0808100c0600f200004070b0700c0030380c2c0130070482d940c00c038041540380b034101c0f40103008201c44071415120350301039800f8a41d114120082a00f555104100003070881c0d01004c11a914280c0203001c121100740d4900a05000d00242e28043c0036445460400c0250500401002171425403540c0c0001d500c24410704c0d44407501e004d40070401c03c6166440f0f101600b80d62040e09402400c0c040740d0740f03c00b150302c000802c49040b10030185280c603403200076240d2001c1090f5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73798509 1250 73797259 73797281
    0x210519031205040611070b04020f0102010b0f041d010c090602010b09010302090406020307140d0207060b0a0b0304200414040b0f091e12030a061502010905150c120108010204091a0303030109 83
    0x35481e80c9080900c02440c0c046c01c140b504c06c46180c01541454010040d42254a5810724110381c1480000c02890b15400743d0035201c40c2e0180e0f4041b0382c007644d0301110102840083c080c1d082c99840c0411408059511450200031100560001c1041c0741d0501e062040c03003138003404003a400c881c7c09400b01d0009006940210b81c80300740c2c3d20748000320184910401415a12559000401035000f1030344200344519031240c0c403d505401c40d0f0382403010749080d0940481e4000100080c1c40c600524045103032201124001c1c104010004000300701e0701c2c001d0f401c0929401420344090790380380303c0c4400043c140005064114010200c0800901e00120350b1407181c91001441940300106008614012051140f01b01c0610b01800311044045442428807012410034454540d0138011603042c454403402107000419201c01903c01190b92186070350f03070008115518400ca450500e5140591000010b41c02d03010741c050826142801c20610403d8540741186400c1e040100500c0c1d4507801c00c200400801c03455074060440c180e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73799759 1250 73798509 73798511
    0x170613030e041103060f0402070b0705031b0703020a110f0102070302040203070507061404121b021c02190e0c0414060711060c010209150301081e072105190312050406 73
    0x3907404045410b40303080048506858102000b884141d26081c4070000c0d17000c0e003c2c0c82c2103090810350744071507a80c00405082c00052190020200c2d090035600c0c05a111140362104803d070380e0b40400c0c5002540d071419032406607622000040c600300c0a2030290288100024140d0041c0030180c00c580800009500140c5991b0030300c08204000d00c001070150048400d81180002c00001c207203003605011403103040c4207400508100398501201043c00c440b2030022081034042d2441d2180c0c1c0042c204000380380182010107035003d801c07c0301800c10b109071b00602000380c0310241895107090301c0d4903244e00c451b80641d01400b01c48020740504001142860b2001d011842c0c050308810103602c03904008170344140d0100740d00045caa50001100e50b07107400c080f05003008001122000502d190b1501590a0301c0340c04481c5a020b00e5070038001c0c162074001d400c0004802a0100b1040b0154144e1140c10200785080c802070221861300414802800c110503440e4046841c40c4c054550749034225000d0b00e038800401006100300e44503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73801009 1250 73799759 73799777
    0xc0d030c111c030b0d05010b0a050303040b0409050703060308031f05030f07060503090a0606060f020d0504050a03020405071206080705120303010f060503041a0106030203061c240603050d090f17061303 88
    0x3951112551645c0c03601032800041d1111800e010302074070300300540201e800390340204420450118900122001c46040c00c00000d130341e40b00c141d030440241c2816400540798050100920078040d00c4690b085a07c00700d9800c05007030480c0da460516032154012485003249811030f40041001c02d004100856106100005072004403051b83c1e030b03001c01c4a110307411040c0022403030301d2040c0416404200300c2041660600b0000d04103031420f80002c40441070b03400000c3c011510340c408510454043c551003840c3c40c0480c001400040c2e1150100307507981078280b00c1d051084440340c4484006510100c2282e050305c605044075100c0c2c40c01d1180640715984040c2049455090081150201107110700e240c40c01303003104da5400340c0e9038100031007000103c400804040380712419000c1d207100000c0f01c034100072950900b0185841990a01c11b072080f8010090340c2c0c00a040c81c00350350160705410354050760003807c0d90f01d01c0c0c80b1242e2442d105c10302913000402d00070f540d4017582d200c14042500760b8041c140d00c10101c0d11034030f451611 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73802259 1250 73801009 73801031
    0x60a020a05100e0d0302090d0204020d0b0a150e040e060a09031101020304050304051201020a081605040e010e04020405070503040c06050d110a030606021b0901030b04020d080c0d030c111c03 83
    0x20b0074042d051070715500e681d981c00da000c0b0142d00344401c4284a8952401b5401d05200200040c0d0340300203100b00920072540001c070403812441d203810249a503040149503416003a50b5401008814903001301001c0005e0824400c42c0326131034a807141203189184040280703540d80d07460340d6800080452002c00e9090106103000d410200ca402d000661240c0c0c8100d0285841c0d51a01050202c3c0e504484d1a00103513034010701045c0070060340449042d6010f40d5540d030800030310f5030340d03a030994644c451034121070440c600e82400801c1c20051021482c1c0100c1c4241c03410010f03540c4e4201308842d180001c0d5402011031205043c03c100d100e21030f0b8050800040119000140401148802d02c1240e01c452007800c0429183c680c1001540c2d0140002014481048000450300d00040d0018040c003005010003054440700e2008a0103544031140d00c40181d079845a00c2640e19100d080e9200d90f9444c0c83c4c1040c00000342465080c0d44c0349441380c054402100d001c5001400c5001004c814210142c020250030b408066a440d11509 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73803509 1250 73802259 73802263
    0x91203150303040317120f190b0f031b1005070b070e1504060305070207150e01140705070b03010f050307050901140f150903120f0702060a020f0601030b1e060f060a020a05 75
    0x410840c2505c009175610a2402c0448a0010003804944004554020003c252000c01c0b0a10300c90035074503c4c00903e0f5152080060f9411750072100c40c640610507105950001040e214992403a007104507447e148a1200c070000b110144258800140b003001900042803555000710f001000610f8014680154015200005210768229a003c0c400180d00d032414400807031f40600512015110b02c001403041509200000703020301c8500c00c9007504201440020038072480820f4103440e0071035401001d6030a010b5860007400703103542083c040d00c0442d400c01480003940e480c000480b0350407980041c200014a0b840c0c00190548615400c803066000701403080f5089090f518201c070403003003803901114281c8402022051500c3c0c40201c0c0640311032074074108403420b8041410030584901c00c0d41100d0480d500c1c500004200d0034001d8181d060303000c92148800100c100301a807007180e032082e00303000070319601a000348040c080081010b50740c05801a8400840d11400d04001004002941180c011590151040d40d120380c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73804759 1250 73803509 73803533
    0x30509090c07020f150307140405030604050309011412040f1a07120b06070b0606030c040305070605030114041b03020306120f01020901030513030212180d0312050912031503030403 79
    0x41000107161421071a1034440d1346070154007503821544603034882d105002180b0000d0840781c1030184c0c0c048094a55078801007120080c2101905070b030101d04040c0f074002d50340c0d0001c0c0500c5000c00c204070308000b004078915041e100c0a54584030012059107a03511030301903407003605205680c041c501c505503461024284001c207014203001d943c0c054141550341607882c1290042000030741f050004001150228418084454124100710fa1082e0341c1d443e0341c08002c02511840d0710003003503401214000180123801002640c121a6060010040608070100f0001180c40301c4c00c0307080210075810004001030344203a010703641c4460f000d880441c2201e00c404490f031922000c1010480d5980d0002080703229542c0c103004950f000305258400300e400d0085079070060345643c1c0700c4158100710710700414102d1400340540c0b41030b0181ca401806088800c407803810014441154101a9074146007440040f0741c90f4007002564400300021285858116100c00507840b50054424508950520041c800803000c40d0b20070180c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73806009 1250 73804759 73804771
    0xd0c0306020306012708010609060b040308090d050d0f0e040603150c121401090605030d17100504090f031d03031b070f0b120901020708160501060e091e070605070f03050909 76
    0x92500d525003400f043c203623109900100007075400d1060402c500704140098a060700e40c001e500584801304800400e41100c800344001d000340c40780e42e40c02aa01034102c400c0320701c00f410030780d107031411800f03100207010999007940320003842ca95886540c5050000264403030a8540c0141c9461400c15417212045e40a0301c107403200140500f503c0c0d0f001081600100d1144100828094000c5c000d01403a5900241081048106007203050301501c0c00501440c0704071403060007401c401481000241003500b400241400080e03801c60100301180010391401202d4a440b0001c400020001c44c03411508a200d04441880750344620080e11800c0c42c082a51041a1007910141c00e0903a2a03607103d60031952405c0b000d19001c3c06040d2280d10400012000c40e81c03003003c65002c00001421014540c04900c1e0540c0103040d20361000960b00b44190511590741d001140c003003109620481c520388031074120a00d464449503144200700101d00c1c104010000240c0c020313208281d10b4080d0400508000c82d1401007403025804480c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73807259 1250 73806009 73806077
    0x51306020d1406030106140618040207080a02061e0601050714010e0c2103030606071109090f0120030105040e3301060f0819020c010e010b0307050d0c030602030601 72
    0x2840d03205007240b40b102540040300718001c3c0704c103034038103811500d0600b241c1003084c1c040d0000003800031102e40354019450785d00742302400441d600c601c241800e00d441e801c03440e4000014020380c8082204c4a9132000038480817001c40e41022100c0d204d480054072180e011030b2045882103003802440090510038480c182560030300c0e002401201110008008580d0742c40c0c0c05d40c1e100c258015250005041000041da9407160050364010b585001c58280b5000400b0302d51440c9a0001c0c14070100700e00d031800030074242d240d03042c40c00c000c1c4404034400308a00440600045540348007403041c00104100c1c5040d420600036001c0001c26540c0502400c8520700f0f002c0b85000c0d84a0658001d104219801014004814014802483d103503149200c0a8402017001c00080d140040c072021620032040c0e1004c082e07048448566081c0d00800100c2c0c0500502d038044c102c808025031087c012900c1c000350b071b42494071059140552141c13490b0380803030031555840004c1d00064007070703410050034400801c80b800c0080e2000b070302c0540c1250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73808509 1250 73807259 73807271
    0x16080c0a110a03030203250b04150b040603020904080307110601030507030c090209030a0f0501110417060601031806020304030e0604090203180f0a0308090c0409080d11130603051306020d 82
    0x18031200c0807903580122401160108001c1010982c01b2082e10004601c16072506a500e01c0054903101e41c0b154a00c020303020061180500040100310000c4080301c5003010380c140994081e000c1000215a8203100194006100500003000940e03103200544d0721820b1030034500d0340c03070444007946403824100740c1088600341c0c418101401800303150b9021000505090310300750310b4114041c01198403801a0140144041c035604100c50401c07100390496044404012034035616580e03100c1604840b080d010081004034003c680115500754428082c2103a101501003509030001219692000298002401a4100090b202a505103503a0b0321700200300030600118050307240c0c18941d041c460701d03a07904003c070b950a60000031008040440462000030507074043c1040140c0340c0d9104065401c3c100c000e10307901d45c020300c3c01c0c0c0028204080c60010f40007050400c4030802c081581c5170840c50680c0318800c0c4090040300c00380020805a44207410082d444800078040004804050f0749510990f04444c140307005041e20b41e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73809759 1250 73808509 73808513
    0x1a04090903080f060a032103110309030a03110304020d20180405010e0a030207091d03190906051e0c01020c010e1b0a05101b0c0e1605030906010b16080c0a 68
    0xd106038004c0c00803120641c10030f01d0f542d10144420b00310b408081081c0342c0f48206034902c0340640d1105502160b0f40000d01d640c0e213000210705071268414144400441c0c030b030050b406080000441a80c0c4201c0d409001d88000005c2500e408003141c2107040b40e440380f81400e02e126801601c1d21410310655014415101080341444c0c42d0407400d461041c4d10400b03103a442034030210b01003540003402c40120740d0030600002d41030b49000c507000d64007094520604843d100025410300b030701000e020000c140094951b20040384a88079a001c6039507101e8a161ba1001c1d41c0f158041484000e58100140b5103440207400040c03a01d10b0041041e403d540d96124094503c0d001262701011424480030541461541220300002c55820000041c94505103419038000304402e010700d10820101000c4026a1182c00000403d019507030b03075481d0f01e8007a41c00ca4250851304408014040d405000d441902d0203031050382c0241405a0820b20300c8082600088080013030400740e0340e14a408038100c480100000d1105202521403c0c5281c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73811009 1250 73809759 73809781
    0x503040e0f090d030b060c0106080609120a080115030b0d060e0106090618020a09030506040c091a030c0d050102040b070b0109060b0c100c02100606051206030d05041a0409090308 78
    0x30310007481d0700030603420000074440102d51245202154100001e850100c2c101155040c018150043d02541c6001c90214001000040007441a0350600403505030180e1280c80001a004e880d5441d404105100700506c452000ea642c1d040914195240c009440703001d450005065410688007035508a903102044034518a0030300480d03004d824412020700c81c2d50300d0303d1800d40f00600000f043d01d001e5940464000100c034072038030700c0c900115044000c0703c2e00c9092900300307210968801d100e13986149242500c0c22140720007120301c410151a004000e03103009040f07802801401c0c01030304400c8846550800012481800e5503024210b494016114680158100a070701d82c101c8e071558000d140d120805014000e150707100010780850007101d40d00003040b508585002a0b00d04407003c440d4000c50350815401144196100010701620346601044800c661260360a0580b590760402c1503100080023007100348050001043e4107040354008081042c50302d030fa1001000b04452824804030006100c00f8140305001082d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73812259 1250 73811009 73811011
    0x9050601030e01050601020a060f0e0d11010f050112320705040b0411071203020717070203150108030406110f030705060603070e061e010318030806010f080c09010503041502070503040e 81
    0x8110b00810407402c0c5107001079038070f60301584001e15445e102c50007030804443d00c0d0050504041080e0884144040500d4060017140601e0030114044d860518028001d282038001c0707604a50300c40b8031902c1d00e02000d40f6110b203401112040400703250301107800c0007007502c0310300b0340300030301d0844040902400d42c00c1508100c10b03503074032042051007907040401684400000100720b40c0003942c400300198140740f65010680103409000c401402d00c0310684070040758081718030024a0600d20031415503c1030118085407540c1e00782c003800384c3d01a603401800240f002034080c0d0034880340c070348050049601c01e0b4003100080e031640c0c0c401391040f101c0790440305c03d0106c94101000358a0140400105c82c41c0b40e440c250002c1080158420a44010401d050303608001503400f03680002d43e00c2c00302594440c25510b07103040c06004076109403803840c002022000c1450000344070f11080e9020780609a00e10345460308500045400b500050020fa41d984040f80a41310ac81c03502d4402828a2031041c80070399190703468103030181c01c030100c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73813509 1250 73812259 73812281
    0x703111810050409030c0f030503010e010905150105030603010e25171902130e1501060c0b130c15030c09050103060b0d0504080f04030c031104090b040312150905060103 74
    0x2032108244140700585001d07000940d003041d1400286507000d402c045883d20400c0702d0151080700441c040c4000d00da481002181a982503803409416039030b8440c01e400440e01d084661b1080048232102106940d031090340215085900203001141201d1220703420340c149141c00210404100054480030441d201c41a0039400425043d4090030703010311a100c1454444403541c20555101c030500c0038103c01c541d11078084990714102e8600422507880405510780c0d694a103180005030341404c050001944910613190441c07002e5111000340196100e9226441c5034283e0321404036090346042d0004a40c400c2051048055104242e034042590f245507a40581014401d410590405041c80800c1c401007031400c08580402c2c680e0300001a032907580d8144400030b40103030000d1080303d50740041d00200b80301c03d61b401d00c0c0c2528000e08100108101e00000c120895a844a005144007484400940801d015440300c20034100d81c01d80c0440e0340c24400c141b800610b1402c0c1c01154519a440d0144095541e051040b012a11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73814759 1250 73813509 73813549
    0x5060f210c0f130b0c0109030306050603060d020f1203072f01080408030603010905010c090503060c13210c06090e0603060f0109020f0d0207080301031b030804140102030c070311 78
    0x1040c8a0800c1c0c40700c0c416000d40d16462807002548003820311042e50488000c0080213449912050b21580042c064011443c041d030000c1c5c201080451149001d400700d03402280010000c01c0844c3d165420701c0210245000c44e16400078a6080302c0d11103001c01c1c40203000c0c1a2051141007580d061103464200007458003412412459280c02d40c0240036600081c000b178005821505060b140e07030310000000e0140c4900d940080055080807003488501d5000300704d00302a5182141900c0c0250743e40c00c07442559000d4801ca988120030070789010050300d00b9980e1001421011240c0084902c20581c5800b005c1e00c403c0d0388440700240d507944c002c001c81005000340682206085000c0d02c22402e01a521540300601070190313440c3d90b507000400b450424100b900300c03402e144481c0c0080d03454900c3c50901c40026002440142e5228030b04004000000800e00c010105070380e44054030905007410400745400d41c0c20041c800606520040100766000c203000c000420085115020404164000d0410300c08200c4880b800c20101c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73816009 1250 73814759 73814761
    0x90d050408030d0923010507112d032203060c0201090b01050f03070504141005030307050d083102010e12190606030c0905010303020d110a02040905010605060f21 71
    0x100780100c11141c0500c1e0030384000c107000420b8249503074210601d540c4000400080041406003c40641010340305291644860140c404001030321601c03603c281e800305c1246150307030121241c42c0c0e00c04013034038405141c618222801e010908a130955070044450005c1c07401d103000c180800400c9124080e00700d0b00383c0d19100a01166400d0303130301e41143c46418004c8912075004801442c4060b1810801d1b08024140204180030114001e181d204158409481d41354035141030103004119404c0000448001c1d681c132030001c2405152403401142e4581024042d6003c181002043c3e0b02d0070303501030a07101030403500c02c0e02640b4819000d00c0050804c02d4050b2026003d0804030700001c0d0b600001080310034410000d0f13a407040c0d001125241460041490303400c000c04643c0c07800b0003c110103980c0da001605a901c60b80071682240c0391103070180d8421022801c4021154040140340005040c1f03600b003001c10b036218000114040ba11100010708940101071b40e00801100803a01010301c80082000b8030704a003008060203c0303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73817259 1250 73816009 73816019
    0x70507020306150904022209060516090f09020a03060f0b090405061e040203040206070501050f0709060c0b0601050912071409011208090d1b0e06040c020105010b030a09030e0307030b090d0504 84
    0x204403001700082c0c40b03100c21000301c50702604c0001c0c0c071001c1c061611400b00504031151034408020002503c840d00e221100300b407000b5000d8024103820054803001003407085c116140101600c00ba5003c04201c034200341d00c40c6800212210a5820a805050807100c13103505c503c1d42506000c100ca80081442d031044440a0525002041c21000d001c0c858a09070390259603944d403400401d10794401c0d1700c8002c003070b0341c68a01000402d001103c07140c0e00501899071441001c135a1b03030300c0480756400710400113001c40c2c54640115400b5800307400182400313900604a1b01d1151480080a410a202903000c807901c1c9800308044841440c2c00c2680a016250000d034071911440d9544034038103580980c1d03a5150182547c850540240320010b0300940d21400d0316040141080c0d16800c0c251490030081d00e5030b5000700e052045003401c2c1070042c01464140c805c6070112a040da17855240c039901408160f901981403105014852520f510103000e5440918002c2020110b40c0c105101001d00d060420704080c01040010300080c40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73818509 1250 73817259 73817269
    0x206070f0516030207031e0302070e06011d131103071107121e0b0c0d140708071b150b1504060905041104080609010507030b040e03270907050702030615 67
    0xa11004540300070800610f4501030307280450310340010317144640203081c4001c036406950b03076801118440c0d801e443e0000da43d000b203038401c214240c442c02d010402d540805580ba11030009403030742078040104801c029000a45040c070803a0205148442d401c0c0c00001002009a000006aa1101020300042045d50f203058840390101040c904020915611a0045400b40103628521002242c00c084902210b060140450450b0b03031007041900600e030f08002100d0305020035054441c1c8140c001d40c440080b5a903c0702d1040360001469000e540040010610450205800d400040720b070a007810000a664000e900030014034101c0800004501e0904000a000d40d07540800668103c0d1070a07503010403190446004000c1c14083d6400c941e583d441020100700440344150011402214203442c10408400d40c0014001a10526107440c0c00a520030400040c1d03120003204541001210014280140e40c914400035802040a0b229500058000706801c415890103004d07094011154104125103802e00c000032503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73819759 1250 73818509 73818517
    0x1090c0c05061602070b0c060702010c0305010b0702010c2906090a020f04140102120a020a03082409100504150e0106080f0103060b22060311060c060c03040302010e100c0206070f05 79
    0x200010350b011a4482040e4001c001711030203000c40000e90b0352902064060984d54440c01c440510042d800c0141644c030886c064440c6905990080700c500386000110340054510116031502140c2d1066101c0800046483c040044c07075001d003114013140285d0030194100700ca41f42d4040c0510341a00c0c4100102da54285602d012a802c40e404c1182100c3c44802850041c0c0c105451b200d15144d101c040050120383d081e03030200d00d00700c0c0c081c4240c44a100c83d0f12079015540341926608040c0b150040d1036181000c951902140e0154000c0203078181481a030380390000f01e8103650b02512403030003200c0c00c00000d0122640f01300909001d80711524244010340b030500c0c02c02c4035000c011300c8064503056540e00344500383e4407801040701c0b8010038104175094000c40d588100d001411503101c142c9800b81d00341711103a05860200111042003a400000302626111078815030b0445c0d0025000702d0a40d0f6031901001c02d10030041c440b012282a00030000a21407001d5a006820580e0080240d000c00c00300c40388003041c0940101c02d403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 73821009 1250 73819759 73819771
    0xa05010c0507030b010308030601020d0903030f2f030301080f0a02090103021302071205040519080c04110c0a03080a05071e1d0901090e0c01051606020d06090e0601090c0c0506 77
    0x65400d140041c103140e07003015040e0308041d109025000010082c01a500b000714050b13002a403c441031041c51765811618030009010080028000d6900341c0070b080d00c2003001070200c1d00310031030702c191003000c5144502e18480303112021f00c0346420100040161000611070130b18009100006410280141e600164019005004c0244126229000300c81c1044007581034031082940441030032148040c0580c0a410781e0001d2142901c2501c100d08198a040700720685c01c81110441c00050080c07100040800001d4510300840714982c100c20320080020070000c0001e086090b01035101c201c2c40741020b1500500b40d450080011b07082c0071040342c240d40356010488129956542901d00145880c464034016501610441034160303010307260b03c00101d810051540b003100c0102900040302d0140c0115401511140662000d060303080080c01c04600106510f50010200d415050134009642038071002d07035008407140582c50640030340c841c0c00148846103c82c480c2c130a10202500b007002e6910003e6072055170702c25000b40b02c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 73822259 1250 73821009 73821017
    0x201030b18041509020d0c05030d02010c09090509030f03040609020418020d0f020102160602100501140a090b1309060f05060303030c0f090a0302060703021606030504230a0209090c040b0f0a0501 85
    0x440d04040f40b540b0408019500030840c3e02c07410414144405846d2580c01100c0c4070703000e00c142031860580140304e10300890344d00ba1144c61032a450004c0c20402824000d1001c2d0f800e010400c1480c03e03d07078510303006500c01c51103101c0c0000d800000c0e0040c0301c00c0358511030008850801b072407051000759903600c03212209a540401418040101440100d080524800c0c2280844400d10030219800d03170041140c00701208030342d00400c15680d9038040c0c08050042e05140743d0704010040800e0140b142c0300e800c04041300d140034250001d02e01c4160320000480d941010300340c03285941e81d88031841001850003859002601200214110b007010640300c003051040810011127054000759462303ca4980f40034035002140c000300450384a0009080107503d03111007802c1c210202c3c2000f800031504500921955004540000b400c01c690f40003c0700401d0040b0108499400500c01c03c2850703001603988481080c82211150050301145420b0302c00e0105541800391a0380c800d1070f41c540a1403480d19444008800c540007403038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 73823509 1250 73822259 73822283
    0x506030604060509010f03050f03070c15050c031c0b0909030f0d06080a051507020a050a062406180801060506070204050601090909111c02030a0b060102030c0115030201030b1804 78
    0xc1c001c040e9640900d0700f1084200c000610380641c24200c01c01c90340940241ea003040c0151074034a413130b4400c1010082282c01080301c01e0284107400001000c44400c18103006103071203100c2c1507062441d00000100c1d6566504070b1a0200c0c2c0c00c0480c01013541ca00010345140345103017440d0310080c0e2240241c05220404101c003149030b01031091643c001c60700030400001910348070703000350801544448a00d4501800d07982400b002ca40c0c59440020307001d01c22034000d405401403440030b82d41c00011748261200c2e50350480d00c811848100c42c17809031100004095503100c0c482c0041a41e09500c035851100d51007903000d41d14180041142d07445180403292840d504031800965596a5401a904004a40c0241d903c040c40c0000180030000420200020400308036a108010340c1c1407920303e0780618003c1030094158208149070700014083d810384503084141401600d051241c0c142c1342a0844003a00054012061485402c106550300351045003410351341504c100c0e40403240054400421000580005c00e800d40d011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 73824759 1250 73823509 73823521
    0xb06011b0209090706080610020c010302070c0e070906120b0102031903110f031009060501121505030a05071d130f060605090c190e010f080405150108061801020a0801050603 76
    0x18082184040c1c0c01840700e04242014100035903180614000d80c00402c014a012400c2880d050707421801450750769000340000b0780301d000110701035040345c80101c50f030300d07052040840c0c1884250780003440345070b15980302d40303c4078901000100030816aa00801c0d21900d40034a5101a9901000b1560072400004013680c0020b01510201c008240784400d880050307001180301042031444000a60090305000c2c0301108850300c40b10410210b40c2c292041d6804520550a18529120590404540c07a80740e09441d10341c183e51000484d0910307071050700407071f2147c010030b03014040891030040110b41c07400701e00f00d43c8640340b82c20101240741410301c482c0a05100c4004400c2001c102c0c1c3c0d03030850800380001602190b401d007014112106c0303035084105120694200310a030a0166480b0b8141002524816505d101c021031014006036a96100038205407030034081c022020000700c820750741003402020058018071079803030a04491100a4113815145209074010051075910cc0d5200b0b8600e815035104860a030343d292a01307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 73826009 1250 73824759 73824797
    0x806040b0a05010c050304080105130c06020601050604030b0414030c01090c0e060109030311030c01020a05040501020c010e011b1112060105010f0503040b07050a050c0708030903010609021e09060c0f06180303040b0601 95
    0x7c0c0d03008010175824941007000c0802d04000030b08145100d1350480303031100d44078501030b6100c6c482402581e030040d401340030400228800840d410b130400d0044054950316272142c40d086086900450f09103103070703a464800050820243c0c00c4000c2c014078010050b4805402c201d800240207904a210180030044070696400040406204a91110b809080210f5849159000c003602581040c0705030f501500540d0400c000d103501a0710fa00d0541001659103000d080b10415429107401032450096504030040c1c0301803c005c0c2c899120301c038911a03480c0010306a40d0b26103000100002d828110444c2000401e106101c0000c64480c00c89802030101d013029903c1d41e5299804481a000d288449469842090300019081d9008802003246020075002845955150320a43c4207030b1050100c0c4ca01d590504000c1c00300000320000c0030b04100600100100d01d042e00c0794910a16060100340c8920701e68002c07c0a01a1541c001c0c0b0b2940c589140080c0514298981030b11019200400101101d051000007035850141c40030b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 73827259 1250 73826009 73826017
    0x5040f110109080607020606011d0102060105060a050c010204030c0f0605281b030906120e0a020f0a0b03150103060e0412031e111305040b03100f06030f120806040b0a05010c0503 78
    0x1441c404c4403040d203072445009580340c405030303212030100b0540c0f105805007034000340700c07030303900302c1d410b800a064903460310040c42002c0d40202c0c0c1c46402c20100b8840d41c03e40720000c0c0000c00046015902e05d132001c6051018000680c0210303880a0300b804020800d1a00d507001f0700d80c210104041383d40010031050300c0395105a652400c4a82640c000710403c4840c08209030300228410180c0d0656500d4149802c0310300c1d4a542140c081082d2030b0041d90004266500600e44a18401d41e202006401803510300c0d0390b5102010190001d07524114500000440140d0341c0d640b5210b0070005110f40401c51039282880d8460500140710041031408154891070061f84803030980e21803016885814004000040d5010101507103a080101051082540310000140c9407609014504c0441402000f604a9200e9003004800600c003007207508118130340315072000010907402292303804018001d52552404606040c0c00400308503005080754812803510540740b02588512400f4404c2e40c1c000c4c2401c1e1086400c0d41409032030350003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 73828509 1250 73827259 73827269
    0x30d02070213020a090e0c19030f1b0c1709040c0f180b04030b0901060b13140d0c0b030a0e10050f070c240b09040615090c0e0f0103090b0103110a0905040f110109 71
    0x280e40040c03c5440d41d041d4044184162b40c2e100c10003020200864170300ca490042014080015031400c0c0d01400300744410808031030810201e070400d107007072100c00104050355988000c00300458030f29480c0c0f06405400131007040301d4400001c1050201820002c00003014013581c0005004500810001203242e01c003584048050941d139149291566140315034800d86a005000b1000c566036a800942001e05003020050455940a039003011031a0801d900170f0403039000148076280c000d0301d65444ca15015000d100c44001d030301c283c4d900455140307000c000358020b00c01c01505d03200801c2030740c1c05d800c170119030100c40c101003040944001440311020303000c0b80409031680c1c0c040168004101c00038001001101d61007070b030f0200c0c24080e80c0c842e44c07955401a803048820030084100401c04100000d9868580401c100007000014100050f075a91076131680c0107487c509800c00c03110303d00c0e10914040e051030724a03080b00003000c84000a01044c03034540c0d00c070804034001c50780c01490f044801c01c131490300768080e0007140040c003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 73829759 1250 73828509 73828537
    0xa090807050114100e040807020f1503011d0117070603050703091a010806091203060405040f05011a030c0604050105120402010509120124051e060c030d02070213020a090e0c 76
    0x1040c0740301c5007004080103a80c0c0042c4d802d401440000e10b11585a1018407072604400d80c14102450364090108103e032206156070700941010396021310801000145004c1d012942d0f0290030380e060701441c01215078060304060540040b140112030506000620102510810320780030409480d22001a4080c1030310000040003018010102d402204108101ba41290600b000b00c40ca29224000e105460311150701c40340d01c14030340420015005040035042070350032610071031204140140036140c1c0c90845c1c0812801c11600745880c50440c80070b1a0811041030184812036616141504c0c0000103005485254104d00390812039400013419a8064002d0f920f5503c4041c029490b61401074040310700038200480d80800e41141e4010155042d02545110700644002800c80b2640c510041013440510700b410b0580c1c1c7d40004104142d854029050015000e1741010390b0000d612400103104200c140c00c41e204c0000f1180b0320500030540d0003a8490810411129503480800c196180c542c21040c01d88a0000c40100701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 73831009 1250 73829759 73829771
    0x3030f0b060c01230f0412020a0204020703050c0c09010f090f0609090b0406060b030f060402031816030b0a0e061303020a050304150809010b03062205010c090303021011030a0908070501 81
    0xc001904180910440444011303421641003540f00079120040d2408101c0344490f03800100003c0408550761458126401101e2281445030b00080599000b040128000760020a00e202c20380d904200148000c4801c0303c4184480d03040c4401040c0c4081e05110312a0200c0e21140e0940f40e8900a41c84440030b00078071801800b02c1c50442c00c00c211001c000351400ca0303a0610b0140001480201c00c81501c0c0035551811004010b0313103031002040041d410203800c040c2034420321280c02c001c02204018200760342066114981d61140b941c242081c65003001000c0034a014206104c0345000c82010505c65332080d19003202c4100301d606420100d2910b406a040101948000540440e00b48030b0030100302a01c4005591b070720942c0d542c4641407400d0794401d642c140e03010b80c0124042030311446803610b082e024100074440140280c603a0340780c0c642990503040740180443e81c409403d00c14182e0500403003103954800d01c400d1252160880e00203c0d103200003810f540ca00d81d0b85a0950b400c2010085c202c40c84590002c00034400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 73832259 1250 73831009 73831027
    0xb01170c0a0801090204050f0d030203090d0b060102071205070303080c0d060602030418090203100f09021302030106020c0619050901030f050a0e0f0703050705061e070609050607030504080703030f0b06 88
    0x60303030703104440c1c1101140180740005050080390003202c003903460142409103910043c2d810301c4000340711400e044044d800180804c549913100d01d18038065a0b80200380b004243d0802030006820300802d0741201c005644110740da8004218005445e4044a5061500c0307a0f550740c800d004039169002d00f0342c8540ca500d0400d080000d44c10390000c00f503c1034403000001c048003035400d09240307011a010400002e4060b0030000c1d004030100d08035804100000341d50f00010901281907400a00301100301d210b10a81280d010005100f65a810003040d03100950564803a4035050400141003541ca60003807044040100000d0412803691280e000381456056105003400b05080081c20240607003607484260b9024032030f0a000503000c0c44001000c10440340c010300607007860b82c00e12051110941c010f601c840d800c0d401c0301ca03102440da07a07440c1c01080300901031040024580c145140041c103007c0c01078481c108043c01e143c203020104014000f04e03060076500d414001441105110410043c0c004c01200c03545c410800329200c24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 73833509 1250 73832259 73832281
    0x1140f1003050406111c0f0605060c01050f010f03050601030f060225020306100b0a0c060209100206040b0c03041a0601030e190b240d050f030f09120a0b0a0b0117 71
    0x4016031189000303010791702c00489941814082d024101749000310000e034100703406403140d2011071200403500b008554191581c010450b0f40e403000082d0480e5a65a000300801040c4007803400340900108042c00b00b08514507120940e8852040c000075260300740f1000d0100400845038100c3e00004441c500c20740c800c0c8c03510b0f100d00300c00100c61081a80603004003000a8104020300c0c0a02098a20401c8085e0070042041d10443d8503241920040301c00b0341d07003004500600c0c6d5980030000b560500903401801c9070702d8140741c611031240c030152031490318140901c00c5c4000980c2d060001501d0000c104210480d580d208801240501000851084107010701500b200e140345445041e022070a0041342100b2150b111050f4a41c0544000d0384485441c50388038140840e50302c0c2003a0810540d03405036040310054514080440e003198851000780c2e41810002400307900380d00313001c02c1411240504001074090b1820325141d81c8032416004050b484080c1e40e6420496081c3c0c066141030030700610740c11a0044a00d005e0002c11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 73834759 1250 73833509 73833511
    0x3060605030c0906030303150a18020306031c05030f130c180c0207030c03080714010230100605030901090b0c0904060509072f1006030308090a02010801140f100305 72
    0x180603008000c240045801c26040f00c40c0a281c0140c011480d5a0300c80c074048501d0300410118950108008100107080d824085e0380c1c07074806458160050b540c0c18040101854a5200c00703007110b013242078580a0700d5203074202054a030301240c41c08241702141d540c5001c0310111613001c00c00900c10310310517501280c01040313494403c3d00301e074440504201903c1c811a0990703032140740f4800104821001c050074000030701c000e405400c10a125540320109468014071060036600315134000420086004111811900304040d901c2c1400110100340285080200d54078140480d607008000c01e004000011130100c803000d500c800c0c00c03143c104403881c0c3c440c01c20742c44a20545d8000b5828501c0742d0704103140403426150409205d4000c072a1034644464030005070306443c0040c14014201c00202c148506a0706d4850f07014032160501198000002401038154940902480c0300030300002d03c0f651044108030300607600b000080c0d054035002c99511040e642d20b00c00090b0070315002400580c000c0c020310f5401e41501d4054202d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 73836009 1250 73834759 73834769
    0x60302040b010e0a0302040b01031103090d08010f03080a0c08091002030d0f05130f0305190c0b070203030c0403030e0307090c1715010c021c0b1617060303040e0c13030606 75
    0x1d1259080d004011108118800c070090f82c04001c0c2d4408000614007544801c13002ea8060602041d0512612038408050b001160091002d410200c0b98003a41a440030000f030150243e950100320540c00c40c0c079510031a0003121039000c00c0c04000103a400600884038103a0310180e0340108030b821080540d2000940341d03003040c03516100c00703070501c0c2411000d009103025a82c420b81801d034000380d60003400d40f40c582022410100c10b4003030010400140c20020742a442c800d2303110300b4035101c0031402c070418a40022201e80c000e05160441d0424801c1c44148903034801200d0172641c061400c440c91aa407400000c0c240034007030344444100d03442c3c0354019207402d412200d65400c40080e400f0074a26070b0350b40b00b00801000d101c60780d00ca0004040d1141d03900103203032100d0b6002e07001c0d010032401d02100702203903074560901d1030039100b00d4001c5411062140103142d001c1e094403049942944082404d080400119990703000d9409401c031120034000c005401c42c0b22800a840c00c0344170002402c0f00c1503540c2c4c24803100808060041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 73837259 1250 73836009 73836011
    0x20f13080106030b06060d02040801291815062a0d0302030c0304030c060f06081b1207260316020f0603070909050a020f0d0615020604122f0106030204 66
    0x400284480103204207070460750003004d041d5159454504100590f400b04001542403642800702140c9010240300d501c02c0c411201402c282d05035855020103408403450003030288034800d031149840b00c841c10985402d4004908248217050100c0200000f070039405060700110705103900002417100c00d50300b8150501c0c4100350b50282c80d0b8030540758008a042e840304071b070700001d801410408038000a103d00b1100145900540e400160380105c1c072014015035000e544000f50760f902036030b001800d00001c4e848202510004690048245808100050301c1b1010351103001340808955000c80c01c0e0001011241112500040549a0b20302d20340303100311092454102c0c264050642d40544810508180c8100ca00030189920351440d520b1a00b0b00410207445c00801610b100c1d60248408003021043c000502140038515801154150510a010341c480124000c0101103621180610010843c1000c102d01800c2c030926000010590408180c4004c0300c0c29516000201003507000ea0000c214194040c00a90b031003190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 73838509 1250 73837259 73837297
    0x20c0c10080903030f04140607080114061c0b0102030403020a03080d050c030601081f15080406050c03040f1b03150221070e0d050705061209060106080f04020f010909020f 75
    0x1045620300340490b282d0b44141c0c01000460741c6101000612039010f4070611255030380b65840d2040900b031010549203180411284401406141d001c404410400348041e54464100180708401e082103108180c0b2500100d6910035030b01d41241d2081c411070340990307000341c0b003010440da4034500580c5550044503910201031800020546c400d861008032402254165660125900e802c604400c1c6125069500307170314026000000140d466841c4c0345903801044503124181c0764907043c00c0940a503000100340ea030b131341801082080002038502d030038103003150341001c800c0e450710070074a03201311050b44507400c00351110320038888201c403042d4280c00400c80c3d9220050301084c50802010740d2044034500380e41e5000030600b0b913001e0b091242000c0041803201b500030740c02c443c3c10a80e2507001c1500c1f5031000e034081904100b00b0381003101207071040000754010042882c0c131a0341e500d8800e0342e089189070041d000910500300e00c4e08502e8107a1041d940c0f04045e141c4180304654030728590180410580c00442103a00e401c5d81c0302 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 73839759 1250 73838509 73838539
    0x40906060b0d141b0c0120070203010b10141602090f22210318050a12180302090402010210050703050106030e0c0a030318090608030a030f1a060306010c06020c0c 71
    0xf40914060344c032031912855401d408103007402c07a98003d45d20041c250b66a68101c0381d00c8075040038005000708003d02003684c0e0b07061140141400d494003200814012105c0080580f41190300c071001c1a0f200c82e56005070307600c4144540f205807560021f1075001e03500200c101c05000422100c0a0740a000b9914035292141c4040c030181d1078071440002030805031104004199203d20500840718410381c00c84581341c001030100d0380301d401c401280c400e54010394103540131054100802151030011200305031103060407002010b5181070b0100900701400000d006c0d001174008a011a4007c001f45080004d0704103007800300e45403a100040040209104000001c0c0c180a81c01203c8800854800715248000d40908406421500c1c00e80d0078040141c00c0501981240300c002501c282648940c5018119401c0036690780c03021040024195880c00c200355914034a4040050000d90300c811119800000a6450719100d5941c000160b45d01d0703e000002400c0789000140452641001084200c400c0301c04035807503000c00c0c84c0b01c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 73841009 1250 73839759 73839791
    0x2040b0d0e0f0c010302090d0f11040606021203060409030c05060f0f0a0c170603120304030c0302060606031509060105090d0812180a03080c1c05060405090c031209040906060b0d 78
    0x6110303a02c40d260010045248954401d4000f4125540c01a04105008a5507901c0c0001624120002d5410645030040f4480c0d0307180a001d004002d0072684010942c4801e0b10f0161041c6100183c51548900d5990310000308250080c2c031232881440c0c1003800e440e961b20b0700f61030300d1900b2a01114880c1004a01c0c074000b86840c0c00500c6400040c90703180d85d580741c0001c0380000081c0c00c01c0c1c01503c140c0d49841402e928641030700005001b544150b10a50741d0407800581440e0281c60b201b00074061501c541824400c001802e880010030115a4500f142ca44807181c13250401070710780e8800d6181ea203800c04804845401801a840000c050180d41c034082da00d0706503a40003011107a00390080b4100340c150801d4841002103032003650610740240a00b02c2c0c0300d190000c0c842594914080c62014038883d0780d03c6204001c1c4a103072510a00d42d200020300003030000e40c11801c0c00640c50705079034000c0d40030500300841c108880c0d0310f6980c00000b800d9032000c1d0030001d01d52120200d99407604820406c240e518204039006083c80d4403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 73842259 1250 73841009 73841023
    0x231503030c0c0f040204170f0c03010504021815040c03141b03010e15090a05010503011505031e0c10021612080304020609010c020307170709020f0406050c0f0102040b0d0e 75
    0x84640502040705080d4100700306466040403d40d4020303020b200c003060410010300b20502901840e801440700615402074541801c01c003aa6481c42645040c04100141c0c91b20300050000ca40151402526507850040f0505804240c24505421500d00441c2c0074009030541c0c010340c1241040130300c207401680d840c04c07038004056190342d14102500c2d050004204c0125890000740d0045440b003582220252517038007060001e0411614500859110760041086060070310640c0150080c80e04035400321802c040209590b090301c80762450054655400088890400b44101d141c003d900521008a000b05000025640c90101d90000a081e054400020b85c82103420211020254000150381c15540c540c0c00b00407064100e5074516051000d000038420041c0d0f414000351000e8890400b080c0c565818019640c0c0c5012010341000100360f00c1081003a000d00241130640d07007200c2c0c507850155a0b5030a545461070a10540c0ca400c00c082c1d41c00450042450240321001d00b1440044080030031043e520750860301d030b4844e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 73843509 1250 73842259 73842277
    0x110f1204062a0605040606050405070f050a02010605090a090b10120611070f050109060b10050301140307030c061e050f0306090403110a0503091504052223150303 71
    0x108100c200201405003034140104002d4540c800481109854246141c1000d0101200e42694510411081026a100700c0c03000d000180e408211030f01d401c01002d000301404500c460248040843c2031000c45100b50098406030001800c10300e842d041080940000d072412080c2110403103038000c0043d10318488800300000f202c200b10b48010704094503440c0c0c0710052010580a03008004208103850201d119500040b140c0781c031820001410002a040c03150495040e0442144103847c00c180162143e0303440800c0c0d9041d100d0804220300400035040021386081d100d580001d010880340280017a0044e0800b0008034009080b00c9110520400100c088801d40305440d0703024108842803022403400c0c24028501981305110b4141184200c080e01411442c000c10100101c5003079100066102190400641c1c600a1221641269060609160000c1c03065581c54002032800d03409500f00000716551508426808102c03410303001c0c8600c03403101c500b0740c00751800c84031102640006140c42089041c000101d5200f8a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 73844759 1250 73843509 73843543
    0xd051305010804030522090203010605070507210b06130516080108060105060a0e031612031205060303163e011107090b01050403050d02010603021806090703090201021c110f 76
    0x181440200340b221b0064000c8a1564242180021908003c24401140a06150f4444540720700700e514200e85030200c0c5800c40388084105003243c0701b940da140d00a41c40038640c4402407002994410012811010103890b01d6080e4a04100500401d80c80004c40c0740c855003080c1d84c58407003584c1c94211469847c5001e1051a8014804001d4441400e22403810041100c030018240c407402c14400c10340c3d00003a400d80c0c00140c0707080f50802005003015003180d401061043c00d42c0003403085103041c00000351680035803240340994007106008030041100611403a05003c1101020f02e802c00307000d025488642c08108052032220410301815540c0e507004081801c00020980c0051801c00d0905400002a01d8079110789414024280004030001e0700900510031256100d0740001117040c550300400c010728103401000c0e100001c0c10f40500206881762410313150300c0041401c0205401c140d901c0102c0c54244108000054603500048510701c0e6684952a0030503d9035102c1114005107401c041d41d91240e400080c030b0b0350f4007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 73846009 1250 73844759 73844767
    0x60615020d02061305010b0d0b010f060e130c02100203010312090503010b0d060e07050306010e0a0606050a080406050c0c0d0906031104050a03140a05060a020a020714010806090c04080d0513050108040305 89
    0x1e111301000551014402c1002291026400d4081400c1e0091860701b141d800500c040144402419000200005c1540346052348070880f0300d0020a50761045841008101901c035560744140900810002844a0700900c003150307a5a03481c1804400d03170100e0031188000490314030000a0500d4140030301881148002c240d00014180750355030100501a1051154a9014500c8000390301c1d60f0501583d4020000805000c29503e4807412000454a55410020500c0010b00085030358591040744550700581c0720b1000501303511600042100790180800d200130710b2003800030080c1c2c0160b100b5824022980c0e5510103121100d000c003028106801380d801100c0e04030301d441c6010404902c440c04c2905602c00c0e02800c0e50b80d608400d450382800d04000300ca101c1c2402d5000181c1c11410b9504204010040143c1e4186449107100140001c0400b40042e0400b44201d11000c0410030f00e110b50f00071580180080300c102e07100c4080c841c0303018225800a811100205410b0300d0001150f501031140035220303990555400e8a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 73847259 1250 73846009 73846021
    0x2040b12150303070c0801050906090d05181c0b0106051e28020601080d020d080a021e0a170a0218010807020a171b1f0b01020a050a060615020d0206 65
    0x90220001d05201d00a200d50302000c0c4692000e1008190b5180288043c80e0500d040070992401e451000c2e00a16569006d90300b081451140840e140754a01440d1030801d903102c0d042103036200100c104004283c0d01261b038610031080030034103298141c42070740b2030b14003074000e42c0e81c03403005451602449850f840e00c0403640c5840341c0040c00003401040d03542c220341e20b8003020b5016554240d1409040705260400343c6d0100c4014040b9000c2080990440c0c0d16900c0100751902c0384080041c45100e010b810107840f1074001c90f500704d4500e8920400c07112000d190381416188c540f5004001e00107421140194000108000450854051402100c080e0b01c1e840700b03230550b68602c403001101c22084c000c0919085004070f0b845440010160308440d5400300440d00c400da2182d900d040c0622810000345600902c5034481024545d60381070026200c0010000b4240019048403513600507803c0001c100c07401882405118040d5082240652121040e103d1074952107400440c050407d80e5210703241b003441c03000369110000042c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 73848509 1250 73847259 73847287
    0x131e050910020f0d0914070e070e01030e031b030415020109080306090c0705071401030b01170c1303060e010501060f020601030f02040f1d010b040c02150117070e01090b040b0402040b 80
    0xb003c4400f441d031040c6080c3c120b1303100808803040500704603003907140e48111542e401c200300046805481e041040c104142130400015062122090200e07050544601e0554100403092061700c2501c40c0118141421001c44a40702e6281c1e84680185107110300100400c005152052141c1c05246034400c4100c1d107162540e80030481641e00041041d0704c400420401c1000142d028080030f4000c0000380030300900e0010f03003c005800d80d4036003580c080c1004820302821071406c030340d811040c2d0040c035100321380359a91800141c1c014821040d904054411030418000c4020041d0540c410390498007030303035203000c602e41d91554102d884600038030000e06142c00b1000c0200140c60f15602082c0840c074125000903800001580303411000e02c01800b508c94a9541d072400007410f05060084440c080704520180507010202c480103540007070b06014510041c0f9441401c07601700340041080d1009032040c0041c6044541e581c200c201d02030600303090420f0203541400e075002a0ba061600a580c1981c550316103c508201c00040404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 73849759 1250 73848509 73848517
    0xc05060c091906050403050c09040209060d0627021c05150604060f060c1a010602030f0306120105180d0f0503060f1801180501080703080304031805131e05091002 71
    0x1551209048050b03000745401680c501000b402240c440f262164650304100b4180301e025004035014402c44400c00c00180e035000ca0349a800101110840c080310514103080000f844003400e42002800b05280f0400c4c2c1d403529018a2284600c21204184266550120880c0717001f24071200810607031200e002748500101c01105241d1000d0060000254195620078000c40906036620071f1001c038508680c0e84051000c0203408265000300e004c500710313503545400b500a540303200e90003030200d5407840400490071680c2c80c03140014941050b10300a01c020b0030409000c40c206400000b03440c1507803082078205e10f607043c007407000d8000c2c6643c3d98941c03c0c1181d44030b10038001d80030100030406522504087d141c4444425020303d003800307406409030018118884124180c11a00b0680180c2107580c0304480c100001680039045a500a603d85407014003040740320f040c030080f6103031500225400704078204810400c3c140d540c41906140ca081d04480c1030080c807a5220360495006885e00041900121a889004181d82d0010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 73851009 1250 73849759 73849777
    0x180105090c0c060c040806090c01081306060b07030e130c020705090601110607091a03060a030201052a03071e03020709020307051e0a0e060a0c110d081b07060c05060c 73
    0x1d0b00d46496410300c2814240202c9210030041c03c049020b1000c100c04006aa500c001e00174002d003022286000082c050701c80080c101000810f1941d0341204000c0e2940100000705049080e0985400241c03601074100700d030100f056801030044100700e0741c1c000b60b43e00642030b5092036a00a0803610f424007040c0510003400901c154107100c0f504401064044040010780e1258115031740b12101c1034240890301e04200d15400ca5040c00507002d0040c0883c5a550010b107104507582400c0407503451680340e1071010403447c00805c10303a111000720303040e01d2540000700040a40c1c81c03290300e60200880884042502c1101403403070160050380480c2043c84541903940c01590001802d00f0410b00f0010a92804407107160a0341d03500420480c0810062040e40c1c010301d01d081c1e0700000307c0d000c1e420a001440000c0440c0d45620000e450805078900c00f4941e030f205e0300b200c517124a0304404040e648010811a01c02d00c9041034038400d645100f21a0001801d520900104a070f01d42d001b005040180c42d204509901a04401c0d91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 73852259 1250 73851009 73851031
    0x9030f020f0d0212060f0105060a050904050a0e0601080102030601090f030b131104060b040305010608010c0f0318060204121506080d0c0515070908100204060e040c140d140618010509 80
    0x4102c01590722069050070303807580f40c4001c10607440d004119403d01d80e81a88880c0c0144005d10111020b19041000d0311603180080e1000140f503511a440e1001401c910642071800340036130000404c074514190004c40c804c40d07080c2c80d2001c1c0d456070349059542c01c0d001840040c024280c04000720300400c9640d2030000a0500424000c1950028030000078203e42580d480303106140710001302002040020300642d001042c81c84003c1090100680f40500034500940d1716000701541c4807503120307076800c408049084968200c80e003151900e842e4014070b20041c12200d030a480744d50b500000c02d6140f1035a03020303c000307490041c0054160860b50003000d4034820292035044581c0d0103000240b000d202da8074041c4910401c9141e80e0300c6c0451b403a12104ad800c1c03050340c40c801106140100400c0c0403072034201c480321940240682d00001c00d00501001203514496000c0948403034940040e1809520079070360414403509580102003003d9807286c008004c42120080100d582c4154030b0001004685012166180c1c04007106113 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 73853509 1250 73852259 73852279
    0xa050c0403021c06061a070201030f020c12160b010603020306030f0106031104020c030405041404150b0f060d020c0a051b010801050d08030705041503050f06090402010c1b051207050103050709030f020f 88
    0x69020381c6e000003021141c5010204028056691501441404032441e840440c6044550f501e16078817880e251584005020002481211407004400d11420b41c036040350161210303503140e1800402a50003070711660701c2485803038103408240070107100e0320301200d43c1700c000003084118100c140400f940020742120490300050100040b9501c56010b00002456010f451401d1803425140c0002c8444c148809294603a00d045444822394842d1034500c1c4140030111400381c1c0f140686044003000e41b00b0401c502da1607026006010040040014440c51442c1c01c6000f00886140c00c6c03001107500d0342c0244145c60344003214840b0500800c100304000e5800c40900d2910360310b0952580401a2490011000100007954400801a071600c03440c5065401050881d21a2040e00700703500000c0030800300360800b80201c032070125040c00040301c2d4045c4400070301000c4c01c80e071701110030034420f681c0b40c41c514440c2602090900340040c500ac1d200740001400d4035400000300c40900b00540a110500308111012504100442 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 73854759 1250 73853509 73853519
    0xe0111010504080307090803030108060103110d02040e070e0705120a18121d090606030411030c0d060608010b01020601080a08030a060b031503070605030915090a0209010305060a050c0403021c0606 86
    0x70091074441c0d8091240d240d070720b0403c61001404004903602c408450742090005108105000c40d08504480d001a0800e55084004000554400703450800a5000349010060f00301c820b400f14a00f021200d0458620100f5500c15800355440e21806e0300c190a001008000150100032542c002041c40400307221810740300445644801608481683d041e010901ea540383c1c5d504010758010b5237004407819504a00c0c0c901300540400c1283c040603100400b015480740903005241c41c00c20051400f1792000780680d01003041400c00c000140010b001c0c1e02229400c00704459410350001030f61504030340140e4000c280b44080340c1c03a0b03681c071500040c2030028019210071000804c944800040e50140440c68843c0132041c03401c0301014078240d200d5100c030040c45424010420020303400300d1a104041e52100c8280e49030790722480000e00702005024002e501042c014004800c0c814000780303840c801c4a019034100a03985403665003004d90b02842c800203501c020400f012042609460020640542c440c02000c20b240b900e40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 73856009 1250 73854759 73854761
    0x907081003031101110f04082a0108040f0203071412060c0708030c0409050703061409012d051504050306090606030a03030c02010e010603050d0e0103091716050d091401050a0f0e011101 81
    0x30301b070b0383c0400300e8041404d00c41d0b07040a1010601d0201e4060b031294504011a00504400318000d0a05062003058000501484070080e42c0f0080310b45d00600769200d59840d0341032851503c140903c1c1d103000da0000d00d420700240c0130008800b802a108208010f003810400c0da61b0044a46c00142050b40361801131100188000080c00f1306030045a250720701040c5503080c14030340e480e21031210407454814010b260041141c50108018140032111071242030721005a841c054400705481c90b44000d403c010b10003045100a1080000b0b032054801c200c0989001e5150440c1d41e558514050703031069851340102405400182c0240d10180d80c030103250001098400c0b000e035419003100c001382d106403201d40014014992269110922424130902420300300010101c544455030f40d2012014040b03080c078800102402040b502c0f143c0203007110350102c02c0722061032401c40c000b00307918080d1091140d00c05041a00c07002c80d60041c0305548026507550341e48030000b1403217801141c01794911850141804503d10800c010030900b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 73857259 1250 73856009 73856017
    0x90402060d060b0307080a05060a0b090102070302130605031e061620010504030807090308120901060b0403080403030e01050f0706200708130611070303080a14010303080402090708100303110111 85
    0x10f641e8555201e00c0c00000140404000400307030340d00d203131500c8100314860f41c420301000d00340d0360382c0c02c8a551500c4c0c0e503200503880c0880c03d40020750b2220104240101d501f0481d08840700b941c1c829015074048004658980c0b51030520f0a0200001c2e40249000506420f040c1815100c00c10f07640c605080400c20b0701c00583c00240e00d440e01c902c5140d444101304014590004012500810300c2d1404518503483c6489000460040d00d8800341e21115040c08a60040400d40010015202c0b503107000b0b691b0b41c0c1d01e140900381c0380d2061104070085040143c54600660160040c1e034841c0561074441464100141d6034040108121044400140c904222048524103a41e000d440c00c41e11982c10b140d651600030040d45000102a07021204100c114080341d21008008540c490480364103040009103500c400c08040007900c0c43c0400907a00300c105400020525a00424007070141d8002e81740f0b18542e854441048503400e008454128503285110004c100083c4100e454208400e01c4e03400014003c0b44420002001c1e0344 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 73858509 1250 73857259 73857269
    0xe13020a0314010f05010203120a06080d2102030f01290c01060f05030601080715030204080d0305040210140f0c0c040203010312080f19020702040e07032009090c090402060d06 77
    0x1603540c0c5000303250b080c10709400303014050f8205881000c0d0301d8070000070741d40d1060542e03003058203506c80702040e0380000980222002d440505c00b601c0c1c490300b00034001018101e14441074284524200402c0c0946041c620840f405800101c4410040b82c0c20440d03802e0545140c041d00f4402108625941c100754a40d00c0701800c1410841c0c000464843c0c0f0f080c01ccc0354405103003034000342c8c481d80001c001005200d200194910407122400010b40d4030a4907900d06800a0003194003c0e2801e001c0c600e20300001940c554087c9118502c02c5541ca0303540329008100701c0310b61800000607190002c00b009a4640a5050409404200c000c01704540c142041e0201040aa030400c0e401250365041c04100036205581004a055108000c60081c02061070070f4008244400840d00f83c02c141264002080b40554036a504594030110060081701d84641ea20f141c2020203051003c600c050805808940c0344891406d109400e0040716074000605060740c410003004040c560152040340d20200070450321444000754041e10000f86 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 73859759 1250 73858509 73858511
    0xe030d140108010606030b130504031e030c08010603020703021e011e0203040507050913021504030602120105030c0604050105043803040b060109060c030c02130216060f0b01020d0e13020a03 83
    0x7501d0508042c0c00e464454210f04245070902410342500d44079440390540484142d480032885860724142038540c04441e41e035205034016000c0c81c2c40207854041e00008184505541e0b90183c03683d85440403822030044900003401a0850142040590481040010040443d2000242c505106900c0404c841450140c0c0050144c011040205000f810312100008100075108006285400a22004048241400240b181e0319403060005800444d009660265900c00ea00b10740e211120787e04800070030800d00c80c0c544a0f2150b03000c00c1d040e604021094070301700c4a041e1205411306040c00340c01c45880403a0024070b4500200d82d40c075190301210101c2403c0d00000d100c0c0b02c0700d07604c0c1081e040c41071420310014502414003038015000c02c040d170f5001d26100c3e440c070f0b0140b8180b00d29941c42d20009200000d03410031504840d0001c40d21700c00c4038050510300c0d004540328003810014400703408842070079600030300040c0f4056017001c0c8031600098001d00b481d6040d001c005110452100280720380008903006100c10100207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 73861009 1250 73859759 73859761
    0x318082a030a1110181802090907121104050a09020d02070203030403030f020622060209030c04050727060219081c0902090907030803010510032007150501080703060e030d14 76
    0x50920f1a08200003031800c0c64503e031760809204846000e804c0d035200c0ca41e000404400d0500c07003501ca0b58140d5000f000c00500c0240903003480c0c1d100411408204005000b664a0030191000e0401e00d1003c40d0f040b503101400030301060b172800001d40002d420150264807401d07020460f90006a0f001c0c0010006180b09440c0c4100001000c04000d00c0c187c0001c14904c400c4944581010a02c46e00400d4500001c0d4003030009a81c601030a004241011585400d66420034201400d2058807034201054961201c1202c11240039010305034085060041c0310320800015800c1200c04807042d41164036800e000d2401002c0305e605c0d01c8499800b0041072000c220400d0fa186a58070380060861501c0e80001c2d400c86001c074014071080c2e0441c1c43d2a0051720062003400d114801c817804002d00c043c000c1d00440380709280811843c1c0fa0044441c03c440450b40460f0044942080d08480030810241b24450181079aa00400404001741141c0d9400001d1115444821041c070003401a030314601c549000d201d5011080c3e0400c1c0381c1c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 73862259 1250 73861009 73861043
    0x1621020c011101061205032115040b0301021b071a090a0302041d030a0905040b030a0b0708060d061802030111030709060f03020f0a0e15090f150705030409090318082a030a 75
    0x110322351403440c03560348e102150610405413082d0040c4140f40000f210001140b500000000303009100d0301a0000b980305400608450200d07000c5540d00498a004a04018460003800d441c1420b03c01e940c2400e03800344a60b44140003508050748140c003c0411041084220f14001c0c60080c40c42e0000d014040000d0a401c00500039810030b40100c015100055000703003485c6000c0e07030300c1600d52140208044100889100003495036038540405014a5030000c030100120104018880c02d4403080140981c0a5824a0280070034110303040f0840e489801103a445003092420b114080f22a00c00203951002050740030b00c00c0d2682c1808540040580c00006d4840c130394403a9002c001c3c08050084d0b00b5084811149c00e003c1d921980d1202c500100c5080d100700e40f41e0b1071004110445540501840e403000c2c00c948000319000c2046400c1d03500200e040d90007501c5021341d200135010101c2c000c224500481c1643d4104180c540d0410b907078480d810b076008016480030b80048481402003441d2403640b25003901d14911800c43c100d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 73863509 1250 73862259 73862287
    0xc03110c061e01030b191803050310140607030e0102010b0604080c01081605090603040f050105010602030d060b03060d020d0c03060e1e12030c160203031621020c01110106120503 78
    0x201c2d1005248041039851501e07000000903000301032541d5249100d010421041c49548846040c1051542c0103009600e0784c14000c203503070822190742501c02c0c100240440c0d4000caa840b11580f590000b041180341c042140e404071400020b032103006040d9921408048055078a104c00340c8054007012004191000050300010002500580300358161000b210100003001d0b8803c1c1110400c4c0e00c25201c9035542d44407464a00148035080201038565440c04c03001240c8a0f90100047c021780f003000d8030a001e2540c840d0003150051200303803040c035442080011420b00500302000d51018090040640d0998251359483c0d03103060780d5080580c21001d40244040404074810302150720181400c00c1c006203d0401d50008801c80c511020b8882044014082144884907600040503ca42c03030340070781601c1d2240c04120a0a500f03840d2000d04036901980040403216001c0804912100c600c081c3d40140364004031740c401590144240801c54566548400d804074000c10b040c10207041c203600c24002966180c04100304070b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 73864759 1250 73863509 73863541
    0x5070c1401031404030915020715020c010f0f0801050d02040b0d030306050111070e06010e03030f040603060501030e06100902031003051207050f06090607140d0c0306051201090f060c03110c06 84
    0x20320340b08480004d01c80441e070b0060aa40650f020340e03111580109181c0d02c1030b49010409e500440c40482c4201c4d0b41c50309280e0101c0c000c0201c50b1f003a254012100d10109045c3c803404070401d00100004d81b01c8004000c0c0e0300c3c0c10341880c0e2840340080c05c000b6010603014007142800c040340b2010b4001c45d03112401040725507840800c180c10349280b80040c00b00c0314240184003081440140030a41080b51780245a01c0d182d405000302c800300032120150580ea681c4e01d100140185c00b40e4490540840e2804020b400107480105446108540348110303505058101064100203400141c00c01c44004024240480040d01c1004064890f0210513080c03510f5501514010745071080311858007080340c00603800d1003940080041c445803c0442402d01490a03584415813000e6401f6083c45101d06905200c074104801d90150b000c0c600303540c000c0d14002c82244644041c60b09a45c403001000300b0712521043d081e03000c106940d102c11040c031340e81e103000319410780d038410705206076080703030030404030365040032050000c200e4071400382c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 73866009 1250 73864759 73864781
    0x409141605070213020a0215100608010b070b2415070b010b1213030e0d110a060206090c04090c0e01240807050f0901031401080a050c0303090a120305070c140103 71
    0x41460b00016030b0218802071800c0c80c00545040d00402c240e00340b98020702c20300903180d211444e160b0b0180f0707003c0e144403110603041c0700e8000812001e4002159030448074007146c03030441e0400842601919100c034549100c4841490703000c80c4602120740ea54040d60b0700d8420141403081c07003490b0b64540c0c0d240d00b4106c0d100001a801507421f2482089814400c003c0070b045150302c214114510011052603040540d42e61121030595540001c09204c0407007040b900008403a40c100c0c050300c0c0301400c941c072841e0a030303500c0c2d500fa90985020b070700580781350009191179040103035103900c00c02480c1d80599451407255078440d000c1e08000f444c8280649081c01c0c0d01a4400b20001e40311062803d03040358100400040c4c00c4d0711903014455002c102c0083c02c0101a40070b60494510050042c440d40841c0d030392410b1454840f0301c01002101c00d8002c07506503045178600001940d803041801041000080e02e4810456038403241c51208805201c1c0501550021401c0092410014a000f25541c600520464001011a0b0760baa002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 73867259 1250 73866009 73866017
    0xf04020a0201200a020d080705040f0905070206100302011b06060801020f031b0304020109030803150d050f011a06040e18060726040f081605030304050f01060f030302150c04091416 79
    0x244c9034000b0b500290690300708081d810b080328643c0700c02e8012078240c80f854012164526020900180c0c00e900c503800248104826400c0c0c0e01152101c10360380d00707841524070000e8000390201000f100d0801d86402a94035003440390800050099076050f0060990300120702c080d030912004010040324031150001401e442115440f60707440d500e050360020380385e07001e1400041d00140000c0001100a10301c408200c040c0baa0040030040342e05050701d0003036510b491046141d44154200240c01507041a0900039603000701005100070700305802d1610310110554014030785c01c500d1688103d6810340d080c00344011405014295186681982c1c0c05201c208212a242841003241ca41c042c1007102240d407001200002662212026a440b203040c032410500c01109d01c400342c0180000424070040000006001044580c0700009100d420b55860310607082c0c640c40e20010340540c01503801c80c40d0b83c2804a44565001030000c020274201521403803100101c0320502903508103200308100340700521260906c5c95501c200c0300d281c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 73868509 1250 73867259 73867267
    0x306090a080301060806040b0d0f021201090c090509030922060f0501020a061d070608010503070e1303080601140f03040c0806070e040504050c09160806010c0b01140f04020a020120 79
    0x10301c00310780703201c144550780c10420b02c2c03000724805a1b920740250700000340c0284458040c4000e41003145010103000b40492146174484180007096206024910709140c10a054541951500c2c10003000380a008104d0501e501042101085a0303443d800d058080d540300f8141c2220403005281c50b02c084400c56042407080b000c074075070100642d0b88c1c0095404000ba44c41100030a01105650195044420308000100c240c01400c1021038426807010f060b41c1224000c030100c1321107039a1009104c002d401d0555008107011020044840480d00a86c0c0003504002c0c180340070411044a200e0f00340140e08807044074826018000240001d0008a44012003c0c0c1940c070090310749801c04410182821040ca81e0f0240165100c1e4009424403030180000d0040c0040a4a2030109240c230800030290600d140c1c00701300c042401c6d980483e0713a039481200c070850250f03481006090144d00307203051880500040e28407160b100a410303003280702d41d403664000f030b060850716a00041828801044d02c8048a800e40818240840c0148 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 73869759 1250 73868509 73868513
    0xf0d05030a0f0e06030412200d050c0c0d03020a03110c04060e07080609060604062610031403040302010c0f020d150b120c03060f0601050d09030f0e0402031315090f0b04020306090a 79
    0x807d1004201d24500741071b2010041c408220380b004004c01040c0019000f2074020b1612039800100404480c0c18500956041000c01c100300b080109842d040503005910076580030000901810721089504002d00443e00309080c4180003400366045504002c2c0c0c4140000c0510603190b4001c0c000c1c68010304200d9440760245070400100e503041c0594412202040348003956040b460340d03000040c079126440b29107218041d180008040450381814841260982450050464241c1c800f205480070340740d05035140b418400303042c1c03250040c51400b07050aa0707010079842000380001d0030318087d105040c00c10070008280700717122200b041800c0340445400d03a45c54000007031000b09682c020170f0003680040b0310403001ca06e0f51a420b00490301d9002d6010944030340f1b46000d01c0d94040c1500300c20b0581902c607140e51107690030b040303e41c140000d901080c3d43c513403003000c40c4510000000d0b4440010045009044100040c80c11040e15900d0b80b4900244017a45c8070003010043c441982030a00501d41d0044400d0003c0076030f4107582e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 73871009 1250 73869759 73869773
    0x1050411010314090a060f1401080d020f0f0d030f06080d030e0c03010c0c02100207030506041a060409020d060504081614060702060618060d020d030807030b0118050f0d05030a0f0e060304 82
    0x803500003404a81e988548819110065200c023412100c80711004481d5030f11030030300d160b54510080000003d48515070204204c0d4400256580c20030301c1c03003409811000310b4150182c0c00352003400800c4030391645038100443c03062401c00200802c0151942c001c14020080b10f00345040030503207071a075030180c0d060083c44105207070810280e4400c0b69065030400ca00c062801012410010a50001040c0f030041100b884240072180d090000407402d1800e0104540e22490100001c503295500c0003074009488151130f00101c1c0d4a81e00499115001c0c030043c1c0e00e0008204603282d0b00000448088a00f44900541c00d001c602081000039440324103800180f81908001d00000c044218400240b05440ba000d4006a2640c0301d503075120031003581c05007500880c40801c0c900640001c404a0707200300000e141c0081003096601c61000700da00b01e00b0300a840741c41c5a042a0034008a203a415410320340200c1c640c4c15450018100700010f2440002590b43d540180048100060444914000c0c4a03c903e0042c01800041060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 73872259 1250 73871009 73871023
    0x11030d020c1b0118120501110403030f110a0c0302040e01271106030c04030b0411090708040b100302130c031b080f0a14010b09031603210c08091504080105041101031409 74
    0x61541150345d40b40185011801b601901e1600c007102e03280410000101a00454250502c00e11615595098903441d80340c0c0c3c0d503a0405060140ca24000c0758001c0015080503031000a40800301400441c52145004080202c004891034042c440181141e17801d080c080000c0d0000c041c01001c803005455800c103102d030000c0c9030256002c0500480d440102280c02c0140344a81c054a44802818850591500e004060300100c801c58080c3d6110001c3c00020f4142d0a82310550f2003600d0f802400c401c45d901c089c01e501001007410704c44510600d66158038070400550807600c41002e0702825501d10f04146020305107041e0442029180349d0030b5905145000852100e00d248450540d0070003c3c50a4840f86c0120002e8036007014280003080c034018500c004000d029240121008400d000b01d10304900381d003400412034020829200161030104284a851f0580c038020030603034078140004034201d00309919020080d003151801d40e0221000d40c42e4205441143d601401346249812440511009610704151400d03180c00ca = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 73873509 1250 73872259 73872269
    0xb03010306020f0d0c05090418150f090b0408070303060b0418020702060f1303030305090a03081b090306010b0d1104060f030914030a21020405030d11030d020c1b0118 73
    0x500403e0b100c0c00d03482d070b05082e28002c058074503042c043d5803176408002d0714a03402045d495014608143c0514103100310300d1080200d07158045582245003a40200b0b0000400061554450082c0c40c2c845102c0130541041c011402036008614203981c4440a28000d002c40c0d0142e4064181c004003403004001c09540040d1071a0b00c0811aa0b01503995a41480014120700c203000b014109074001189420050700b03681504d0007920320985040100e525194a6140d580446481c010002840c10000815007400c23010f024010340f20424103541881105d0000070704241c1d00343c100140c4800b010461800035002070083c0703004d481800c0407252809060030001400f0266100c001828940c17241d00c04020410500d05030500d419000c02660380790000341200500b107420f2950181649241200039540a0540e40300701c404854000380140110891340c2d1040d0b40000200c9010041400107110000703200c00b0301c0c0001c043c00010040502000d040e543c0c01800d07803111a01c52107040040915603400c000b4000101c81702950b03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 73874759 1250 73873509 73873511
    0x509040803131a25050315041e090b0a20040603020c100614130b060910020a0f0b012c0106030b0307080703030e0a08060c1204050a02040e0c0414010b03010306 70
    0x25041c1000802080300441d180700b03c02e412400c000e500e01030b103901c201aa1090192003031480ca480d860403030f041e0000b0b982200d4809030020b204d10342c600c2e15504c107960a540284244400700010394030700342226032101d070585907020040c08219613000184210041241c0e034178504420300986e5208281c1600842c0242000d0503400203a110b945a0204400d81144160b001e05100054842001d1151100d01d65034140c040c510100d002030991072103010b41542100b0284c40c45080c074090504010380c40001c4001c0d801980945c100240102e200c0210a280381d038003c071480451545054071000050801031410044a03d03602c0407030801d628882406811030304c0c946070100e051400c50300001c5c03e190081e0300c503002030301c44c07d0000410036810840000d5035070001c540c074481040d034820a2540b0b4540480340000141000c02001c1c1144c0d0b0031000031500a4060380031610040b10740ea0200c0c04030f0392030515561030356000140121949c9828019508141c209410041c2d15502d40420b107841c80c003040c00000d08203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 73876009 1250 73874759 73874791
    0x50f070318021002030a020d1b03080403090b0c0705011d0f090603030f04030c0609080d020d120f020c0601090e0a030c080a050708031515030601050307030504020a1a0309070509040803 81
    0x220260742a80d00560020400e141d4011907850180d600c1e07012518a5000d4013540301c060003158052204003405100d1040000b203940c08940c3c08a03010080240201c00348030252102042c0060b45c800500033104030380d0010102c1c20b0030b060014000c0d0003402c41d682e000b414240c6003483c003034860740b410b0030980a040d14140450384400f00080c0c154001c0840c0700c01c2104000c0b074000f05120030ba501e140110313800c03529200c403e5034941076070a07282d0300403800d00400741c4e00c02d41c0012107183c81070101d0b2401e10303800200013818180070301000082c6e0780212981c607000e921000060041e0306e102c0c0700b50100304600b00020075031620950b401405400303220340081c01a06020400e0368400b0f0144d0102c41c1c140794800101d03980ca15050104a104803030014000c0c2c068902c2c00b40750300010001070210b03030150783c3c16102c0c03a065a550000442c05000c0043c03040340c0000d0300c42d400055000540c0c140909100c4c8681811340c0703d02d4913000c41c51034000e03258026441004101e052001298100301142c0d00710313002c42c0205c801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 73877259 1250 73876009 73876031
    0x2090601120903030b040606020303010b041a0702040227040218011215150806040c05030a050601090b030a02040302120a020906130905120a1107080705010f020c0301051e0a050f0703 80
    0x46210880d01c01461241000c084400300340d807580c0400b5281e03504880401180e031300c4d40b4049070749010034001e44280d4102080144000551103045101c1d03050b43d05080c5140003103c5d80850242e802a0307044000642d103560401c408038400d0740309024140d4056408504100e52070016038081d2003602002414860040071801c0703150031a030800c2814156030021516510340d609100e00301c524540b200340c3d00040408011403054038040c011000700c49195500c050658030b4100c9004000e05001d0000c50510213040d01c00542c0030240b5015500c21850204016140c0340b031801840202c1c07400c1100720700b864100c803130075500598801d092036803c520b080c3d0741c2240607104400c0304001440c0c26074000c1c1980c811490b145074509240700042c13683d0b2101d5a110070001001840c41a035491480c02502016001800103000b1548030740041a040d00181c0b0403140c0007440c00011900b1280d00b030307a00219404901c49a44021589c190200360802a102400c01aa180040701a90b4121025080c4002c054544200b502c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 73878509 1250 73877259 73877267
    0x1c05070302190506071416110d240b0109050a030b04170d020417010209030703030f05040306020301170c03070e040618020402120603011505010905060c0708120408120f0702090601 79
    0xc1081004200242d10030003504000360349800440f40300c1c0004548403840d240c05091a003d4901c684150980d5045140596840d900c1528000720516001307644500c50701c01051040c040d12001c0c90050705e0805100c0c1e020034007034040c0e4000800d52410310800c0d135003c004035180d80e44454102e0750072944208103500c96141030700038100c62419004880a02141e416086c10655006200716030344801c08030000710003402c40038280e0082d01c50ba981e15410132202040031900039001620700b02a18503015142c2910f90390740750700700d800c01c0c0c00540c403072108100340380340748002000f01c156088012001030540c145840b08a2420000042000780b0f00c03511034a6001c1420684203a1103441607001388155154044910395500360b040071114184a5820f10316949007032901e0640a906407501079641e01030b40c600346000e2200c0c81e884003d5081880c8a0024001002c4a040c05a402c0d989480180c2a076110300c0c2480081ca040a68450342c8080801000f10341101c4112000303e0b124107a041e200160181e9a580c0144c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 73879759 1250 73878509 73878523
    0x709050a02040b130f0f030b180c100e0901050a151d0907080402040f0c0905010311070203070e010305060c030610110c1011071202030c12010b030a0c03050c031c05070302 75
    0x1141c0350030301040001e6083c20030b06104080e0b90380300c5205d440c4103554240c0a41c444019101c050b00e5110000080f40c20003c07604c65840340500502d044412a580f020003042c1400c0b280b124a03000500c054100d03426a02c4c00500f201e0042c081116012892810859480050385480c0c00d500b00b4030901a106000c1c51032203104000c0051401002c546072450300382c10140032074401b02d60803440b035860044180d00c1215184140b0150303200590310544c0b541e0510b001075000701312513611000c035544140a10320040e40e041100c074010b0150041003481030351451078000e180c0302014000200d040380c00e2041040b00e07140c180c8141032008051070008940000d106409041001d0906010342003104108620910758001640300380c3e540c94401198016640c803405402c5500340325000950540100650369298603141300000ca00700d5000c0f00028174079034108006450b056034240103c5503035000280070800e1002c240442606c0f03503404c2d00030b0b00c0b40300946084080501c0d10f10120100f1300402244607820b1610030030900d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 73881009 1250 73879759 73879769
    0x50a080301090b010206330406030f05010903080703050601081504022106010f020105010503030301090207170403050d08090d200c04020d0f0c230a050c06071206170709050a0204 78
    0xe0303036561075001e00005050f9510b00c0d035025105407004030b00c070892202c4030340364807092058502e584400c90034102c1d8207603c201c18240b079120b91500c40110200e529a82d800007424030070703800080d00807180c2c81c000d064680000c0102c1c0615242004002440c0d070070034a02d9a02c41180702d42c0351a40001100020300900804044440f4404030940c1003800102c03416903130b4060360003603ca00c002009040d8003242079038401d000d03154150304140010085440190050039100e442013003548028040038140f101c00740c04c950b200792041d90165601541090700400f1190300610503d002d0020f4448a00c0041c02401c849610011190183c0b07498041c92a400d000c00c0004500c0140103541e1100000700142c09441d190030700194562520484130f0010703004203c22407580d8421031201c000c1c601c15a120008640041e01c0c07107024040b0420201e04004001c0c000d03a0b01c980c5860315040b0603465004242c0e401c440d6917801c4a4803103501d80a02201d8140001402000c60311840d00200e843c0c0e45a41c2210040e000301d500c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 73882259 1250 73881009 73881023
    0xe0a030e1212031b0a08180d0909020d060506070501060f090e0618160308030108060a0204050901060e0d0611120105040b0114090a080307030504060e0906010507030c0c03150f050f10050904050a 85
    0x80074055079800010b96014030300400741402d04414041c1c01f50303100c4000c1500d8501140030120108060100d903005800138203085140041c4090307071500070485691100701c00b00c849940d610307005c0c000c00340e0641a800241152100411001702103086541c0d545d14080c00360344c0c0b90040c41041c81c07030030b80c0c04001c80c0c003401c0490150350030410795030315202000790001c3c0038150181c05418005517843c4040c1c0b0a50b000c41d14002c041000716440c0100c140c8415800600e01c0350400103901300300c0045586402a41007803031741208030701c0d604d990410100c4103107407040c1c1046120360300380500c85501d6030340100e0017229002030788241030baa0014030300003401d4422640e10071a080d00010541c4018950070801038011148161640c2d41c00407946420030000389021181d15000c1481804800b0101b4416010707500d065225000e0307110f51585039250800c1c1c0304948140e1811090b02d130614080e6000e16030040c01c1d00300f5458170000e041c80c10103400d00318007144c1c00d021f001d006607042d000203003d000c0d0030040c04a040d500200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 73883509 1250 73882259 73882267
    0x6010f081f09022202040602060901090b19020706050c0712020c15090d2010020c0102070306470d0803010e0903190302040f0501210b03010f0e0a030e1212031b 70
    0xd0200170b90401d10401016000d0030340000c14000041c000c0903522a4040c00c604010f9403000f0f4406207161242d200c02100d15402d000480c0001e070984100c0d801042c0c091080b50f200e0381d00d883e11001c0412030300c6981c0c046401c20541c0403070381e8031075142c07125401c4192a5519100c04400001c500c86400c603100103424801c00321401c52410404801c9880d2016055a40c10300c1503070000030980c0e61b039800e0f918407401a48800010000301d011548000007500ba21441d503d4441c4102500d10214151441109060001e606103a0f02030203003a4405400b80205035002141488162601c180038003051180002c24481940010001d040c00d00071200c48169802c8240000c1010480080c0290046c0c041c031040c082480c02c006c11590701074446840c40380d83c0d1030b50f4190807a0120200c08040c04001002c1e540641d2500540042400766004001c0b0050745140242008591401c000780801903441e500e500aa46901d4004440b600220320303c00a000110780d011b640f0b44a071f50103603986001030352403c640f020003c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 73884759 1250 73883509 73883569
    0x180102120c09040b0a1410090e070f09080c01140c0106030f060f0b010c0803061e03030705030d0f09080a0302030c040b0301120303060614070b06060d02030906010f081f0902 76
    0x701415042506907810443d800444080c007500d90350342e001c0d80001c00004044030103c0e01c0d1660300e42140002d289040344407195070700b20b030481d840310030307035034031010541f03002268003550b51000b00c000c010a00d801c000d110742d594400000e444d03c1001104480d0184000840c01c3d84c650094010400030b44c1c4c401d030448603484450514a000b03100724003420000300d04200001d60258456009503c0b030301c1d00140624603589410017001400548180d6032807582d100d0100303e80d1540c0e800d001600c021800340e00070310341e03864504699800711020b1010300c1000354030300700e440b8002c04d454606030382c003007211420016900e80380c2204120803401650310111044400100110b024100a6a50b400c40c0d4171a4500303201313054075110207481c00100000049150301017804107501145000713452a40012024100741d18200848110780f00b40e0340111010501544098010040a035041039501c0040410002400700d08102c40d15480415035071001b040041910781105000b5965a074a6000381c090a1100a0311031130707031503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 73886009 1250 73884759 73884781
    0x2103040608100503030301180203060f0603070302090102071203051b0c04020d02070303050906010b1611040f0507080c070b041515031401060b041503110c010608010b0a170618010212 80
    0x45410000a40c260000050f0b50b042c000190380c182ca000e0f014a5265030111880d000c02500b0040119900011034240d040041e101c3c83c004500841346039501595400e090000a49400d20a62004000908801c01007002c641d000e001e481c3e4491240c944403801d00c4003900081d19200754804000c0e03000d031001a010351500002d50013441c1382c0340b01b500c05014541d200540c036615440c2c244980a8020350421012a0211808034070035400d40c400d441054250300c031a0046011104603002101d00b0a075184140b00c65643c1010b10b180d1f00512240c02540b80c101a81d603903032031400016100034400b005680b42c85001242d60b8024840a40c03c10000302c41465407424541800f031107445000c040b41d482e103400072810400d010308079020344812248c0a000f091080300c04500415008003c642c49600a100b20180c0c00000e000c0d200c0248240b00000c2140d03150101000802c50355603100180305920703540b2480404c0c40114040707502c80f0791031203404034003036030385009070b01920a152410718074485074410005140c0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 73887259 1250 73886009 73886011
    0x1050306030a0b010e040c060201020c10110d050a050114060304030c0210110303040b07090602120906070203011d07061d030a03030b010e030a0510050a0209030307080d06030f120201150f052103040608 88
    0x5203450b1f84825584a0050b0300700e00c12401e44500c0c41e00480200d5a000b0200d4004034403c1c06c1c0c0707244051400c0b221040840440d4800da401c2064a0b4650004100200507011724001c0c400f41200c10601d1400c150344c5c00fa0000d80d40190003801000c080000c40052801803182024190115058a9036441c243c9403200004008668500105034091000f00312903200280f01e144010000c2410361800c103284040090310340108000b03e80c10740d00e485103140c02ea0070305000c541c44422980000c240d058200a4041d203040c030000180d003201900d4098507c902d030b40015012201c5074041c03c0c00190380090500403101150f100b504150944a00050001080b13000910840150a548810401034444154280c180d1081441c0c20f94140e1081c0544070104070020300034000c1031407800c00014a02d60301e560785501d07440c02140c1524101d80742042c48036410713028050300d10380c48490060003118508203181c0d4031034482c43e4000c80780255203081c81b2524020071002048500c080c04822207840d00d9542c5001451040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 73888509 1250 73887259 73887263
    0x30702030a121a0607060204090221060f09011202041d0c09010f030506070810030c180c0e0307091d01020d060303090f080c060319050c031008030304080901050306030a0b010e04 78
    0x50400c010200200144111001044041007510081d840038007002505d400000301030700c51644c20000051328a8a6100500b000b000f030302c06940d24859840420181304000400c602d006485024910400b0b07540c032440c40d41500e006200405003404140042001000c2e10342c41624401403040784981201e40005200b280400c00b00c901124a0303890302c803464102c102030f110091007a071000c00414200390051341d41e5580103a20710040f0300d00700e649844000c03851131907030f202d41040385844214200900c030318043d500c514000340c1041030140e180f80307010990b42e110f41e2040702909542d600440c1000b5941d600146c01c1e0110860080d5260600d04900c04001c29840c40f085001c08d0240c0e8000603a070a400e09400112170318000a803004002407000c0c425598001400b5003803280340405c0d40010318a03503104140c000c94454542e07603124a003d8080410415180c1c000c80d407654018420400090303d01403c40301c0280d42860220380f00d440d24808289852a000002400401020300100348541090543c9d8481d41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 73889759 1250 73888509 73888517
    0x4021201090b010609080d05040302031c1103030f0708010506030403140d140c0a020f1203010608070504090903090602120408120f09030703060b03010c0c0b130516060c060c0311180d08030702030a 86
    0x800c0701fa4003542d40d03110303030712000303415030015059501a44904103030548640d0041c10310703802d002100b282c0682903a004581c080b01244400c400e10070f03050703402256240504020f80e40b06156050a0310040c010a804c510756010313504000640c40028280da40001801c080d00707500a180901306190100c45541000001034010f11948980b9410000002460b194400c0c0f130380d00c21031859003001012110198002c1c0440180700b410800001c0c041c5041c45907400090080d50390020060410790000d05002e001d00008100803401d000174800d1040109900740390001c403800300d582d50744801c1e4000140c0c0c0148800940d06000d9a400001841000e40001c0001d090440013004555003107807040c3c441d81d00c091405003214a0742c4c800507960100d403c03110242140250100c0700c0d1101c0c06460140103a43c141c03c81c40c002a850003e007010030400e405100170009041c2024414000d264001031018000d80728090040e80e0040c2d5072001d10303220342c40210101ca810041c403c3e900e1510308006952030344081c3d1a14002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 73891009 1250 73889759 73889773
    0xf0b1209010b041d10060b0d02031b0708130501090506181906080702070e0c0313020102100e0a020307051206070c06020403050304030305091906080a0207060b0a03030e01021b010804021201090b01060908 89
    0x7041c402d11440090f6550b410760320f808e000b401a280b4000b03400003004002c001d039560f500300003000341403405005618400c41c006640c883c40a001960304500c1c50f44800d060181125090019035560010b403071014404602641a6200800000d000b99a1011043c0d0446080400201d4a203501c400c00e41e2240340c0356000c1b0f0f482a0b44d60261548030b035070102c03501c064400050010035031030320f042007400d01060b00500c100e03060300005180060480348880c0404490394082c2c20340c841103050900c9540d004110803160030301c00b41448030440c0d46800009141000300201030414400b0490a541035074040c64000084903101e41e187d143c06455680040d0b03501b403081c3d000c2e034945410f15109155800580e09196150040360300c0d6443c94102035008040b00300c1c2c00546944a42540b900c0c4c4500b0180211700a0755820b0301c0080b2a40060b0400e400d07007a0340c1c2c0412503080c041c00d1151341c2007440765420030b23070590f4182c5446403104038480c010482031400501e5910000000607085511100d60025201103409071498 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 73892259 1250 73891009 73891033
    0xb0c040608090c010203070618150615020114060d03090f0f0e0c07050a02090703090b150910030308070f09170a03090b0c0a0807020a0509010608040c0f0b1209010b041d 74
    0x107a000032121003130040c5c0c03080100000058058003c00310400c004614482a91016640c031503000e00d2440581c4840d55445c0000c10080c11310341244203074a103d90000f04200090f01d000c2a54019006040a019414044aa004052088085100030001a48440c1d040d580b01c00286c800843d17a071150a01c4c80000a01083c10003540c40215032080d40c0c00401044012440d60a01a00c500c0c010310140074542d4405590300070070b4450701d401380b0a00c003803143c0442e0f0300c0b5101e081217075140300a00007445c968540601400000d4108060a81200703031810030805c100307010402101c0003c5540c200101140d5030b03103407200d2040400103504200c14803d8440b41d10017034550031284054000e007000000c05038022039181d808904988006e04c1540d002420500b0031603107507008107050301c0003a84044002040001040180300d043d2100704080c0040700c0c01c06806501c2c208485200d8055010b4200c0c00481d1034000c1601e00f24254440201d504002c1d02c01cac0488021074841031610614401c550740240240880768803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 73893509 1250 73892259 73892263
    0x60609090703051510080a0c05040504020a0908011d0d08040809040e15090313060e0310060e010e0a0c08010608072c03070801060b0403080a02030405130911010801050319020d0b0c04060809 83
    0x250040c161b55441c459540d00e1000006080012600350601c9010080400d44e500c0b00d00007800303480b1550311000c034035926000c03820742140c2c5156680c0d48030002020b165500340c0004103d4440e000e13200d14050505803210300b0300792858401c03400d95951081c40c0c0ba0703142c1d01c0c070070001c1608440c076149c2c0395121580d0364698491a40380e2003251210724900306482c100780700d044d000f0300d00d101900801504881030b2082c40400075003111001c4d04120000300401d00100030080341001100d600180c01c21062240300c001d0036000c0d00024040c0a00424015050f00181c150340c400c06012208030b000b0312084c0074a0b040d10365030042d0b585144008070300034003c04d0300c081440d40c81406448101e503020030348240352518580b40c881e000d0f044981c0034000c50004000c006269030311948100c443e21580700c0002000b0140f0300d442581081003010b074505006680004122655010a10140403426200706024070916031001039142159590002c0c01401c4070300c01e008840c1c0d9050003034800d44000d030329440700d50707154080c20075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 73894759 1250 73893509 73893529
    0x1032009190e030403050a03020619020406080c071a15010e040203091b01021e060703060e06031e0c12060f01061107061d06030415061401080a050606090907030515 72
    0x5810103070401da1a219224155000d012103101020640303060136160b9032014104500c1200650042c0e100700140048204660894800402d04410031441d19141c4040034007032110040030541d18180224207a401d01c80740365122000010200b5500c00246000e800f0703000902da003c0d0113940010714a03040031780541000c0c42103030301507132141700102190781240074021080345100c80e42d1411401000c5020080300540a00340c1010007080c2c0150105180562005044417201d5100850680c4054180300b4a81c401203550110703e10f080c4a80c001609520950902e05052000720710340101ca1090580c0c4504008a2142d001d8100e2000e0f445c1580d0380e03040110f5076240e082c0be0701031182d000007504020180c0903e02021981c09480140c07030244414134005035407500204c9040c0d402140c11041e400708017810b44140405803000311030079520b520400340000c021040060462024960791004107002c0e80d58034007680c65002c0300500a04e00d03450001d0004014040c10f5415541a0840a4940019140c469008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 73896009 1250 73894759 73894771
    0x40b03010b07050102070b04050604030206070323060307180212011d0c03090109120c05060109150302130b091017011b050901030b09070314060f0f090406110301032009 74
    0x2419a428290312040d10380c0b104108407000e41d400c102e582e0006030411207a40c0700724041e001411484c9002d0030041c3c05c040e00180701404141c03502d40002001800e41c0c00c0d002c13040307091400d414819a1210082840d100f80c0c2e82151038001d020700c160a806130144d07002000300d80f42000c0b0900e940d0f44e99480c1a101c1101e08585a00c0909100000a01b031003600c0d00a103a010000380000300d5004540d0300c0b00f100074407440e810440000d81040b2034006100003000800c1c0104400c0008010074100c1c00307a8004028240d01000b40f1641c119104800c13500842c1c0c1154482e070710010031344100c1d401e0070a800c0d030a8150070700c03807200b980208030780012282c1c00c10302c18020300210b008d40c520560090198100c4242c1c1c0000007407414555282c46002003515880baa2610410780358600141d00b1240440500c40c220b00140010b1141070060402c0c110340d11560000c544159090f2400740300e90310f541c075101001d0404200940007401012000105111005245080714642d078000c1059451004d81817104d007007011034103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 73897259 1250 73896009 73896029
    0x4061406070f0c0509100905130302120c010f050a020301150c080a05030603010f0f0f0e1b01050705030f0304050703020a0b0327070b07080a080603060f07030b011e080f0a0204 77
    0x150400705800b080c0c010525885981240b9815483d6400540302c000300740c0d0004642880920709209402c080e108154010740000038038102034106aa00035990700785000c01c00000e04005c03a4804d20003c00f50803484c61928a038909100c9464800d01410094000f407054100d802009000c06507002c1c0680e81130001c041d00302e4105407400c44841400d0700c02e03901c00b0f0101c07a00740d940c40b02034411006031403203001d801803180c40c404035000856545e81001e803011520030030900c0c4c0003001498890380402c03051381a07001e003c0c2005600c41d99942400c1c0c0c1180142c6110105000000007008104400411284c01350381c03007102e51031000d075200c030000310150108803003200d441400c0c0c058002481c2810407094080040d140c04075005291113021803079240e0410780d012038080c0130200e24840c0b0a5080805140d1185003034004008500e040387c5a10700381031025110310281541d07081d416505900c04c021a00304003203210036001c00c2c2e0030341c40c02c0240880400c84802009100704070105c0d001d032030b0b1402110101c48254035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 73898509 1250 73897259 73897267
    0x906020304090510030803041b14030303130503070b0106050306041b050706090c050a0b0d0e0303090a0f02041b11010b0f06070b090709050c0304110303120406090201110601090b04061406 82
    0x5040c0003d2401800001c0080c110700c4002002a00c130388000c6102d02c2c42090801034492910040c0001c8003255002000022904020480c0a40700041078a0b80600c080040000b41c076440e040c4903095108000700038000030380c1c460002c101c0a4020300114010001900c04019070300c51440e940d43c01c01c100085a40000728104101d001203038030368002107442c5000e0903c500701030750759000050141510380d04c4222000c8011402020030502407007103d11202500020394918500400980d49920303c550f401801000003425000a64031503030300420070340605448990035019501805400403546c0b201102080d8284003040c030b06c078100108150b80c034039405003459040c40e0890355a00c008000090034440c4500c82e9940014402d00d00740142401000714820040d035a08050030300030480caea4034040c0240203500c10444070210640c4041c003140e11642081d070001c0c26900d02d10040307800384200081c10700684580f10012030026050790009408910841b4100600c65650781a035824085480d110703548070318144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73899759 1250 73898509 73898519
    0x2010203130b0916080a03021c0509090406090c0902030a05100e010510030e030301030c03120f050f091c06060914190e0f0a0602040608070509031f0b060c0a020109060906020304 78
    0x70090703080b8800030143d811303038110740120409414060b840030065900c45050340e0103164041c0700300c41c3d85122055100850212104019100348641f0624600900100f00040c0501c402680030042c130300c0e4015a281000c560b981c403050042d40040c7c411401051625003c140310348203e144000440311040141d80740d580ca810200301481131031a80140c10315885500b0044010800d0004601840c40744049481030303815410030b480034004041100041c0000c80c40e07401c02c1d494000c410781d018110036500d02c65842c42d801c40881e164141442d01601121804002c0404207c410f401030340c159003034010f0401266042d02254a00caa10070380761803042c04094a440c0f1401001e40c1c0120640520a008542c80107045070a004d1408041d460262450350b804a0305120703150b40005095049581490014288020341c40081d07190304c544020310702ca20341c01c9c00c40d4940e40801504003140784500200307444d031620011800e00741c41c1c201442d41240010304054001c58042e000300b2a030426584a83d008508181c100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73901009 1250 73899759 73899773
    0x10504020f060a0c020d080a08010f18150e15030607030218060901030b060d050103050705060f09121e01020706050112050601090b0312040311010806040b0f090c07080406021b010201020313 83
    0x590f80c01000360300d100d0780016807242c0c403e022000e031107000c00903510460784c580100510030603041240e180503a41c404205000c41a0f0751b001c2c05490320b036000645c0c1c0c80321446008420140368010344040c0100d0b420010310710802080d001c0750020a4082d05e81300e070303100403003101280300c4e01c0f08101e41ca6100142117049820304c1d06c06040101410b06001981d4150340740024001d401081c0300300c1e07070303152144c3c010700401c00203100e00b0006002c00d50355a4184000a0013403186400b40c1d5804502a07105402d191814900411003120b030a02c0340e02c40a10400c00e540b03c0345020352b010080640d8290b08100c0001105540001688540703138014016168990030704200f14060311540000da0390511400d800d001c0c1151501000f00000c42c800d02c3c503503640003a5900050102c0308001c0595101b50300d4100070b040c4d00c0d1101040024210011904d000403a56a00509901e40c0922100603100403008200070a013503400003102e420700012a80078803090b01c180b000480c00d0b48400c6481c0d0308185a00c041d528001000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73902259 1250 73901009 73901017
    0x50105011706032b020d0f050d090c0f1e0b04030308010b030c040510050702010f0c03050f09131506080109020c070501200d03232203090306020f0403060e010504020f06 74
    0x42c250307000015050300400100301c41c3d2895411412003041c09000c44c40c4c04000c000d203e0725031401c02c1c00d5812030f01c0c0b0000c0d026000302c04500e9241a100c81c0392100308411100814003900e42c000300340026a0315803410800da0299045403401140b141800401e100f1802003d41c2d00301c0764196a1a51980c1c03c00406080d02e8102801e01a84440d0902000ca03541c0da602c41c054054150300d03610300340c89641500004042d81c08145041060040610040011a0340072040300c01100c2c030310a286540302c0941c0045a40c0c031390121402e002e100c0c50708001903042074a802c4c2440403261b040d91030f07203944d90701d45055104902c20820501c4240d4060b01c01002154000e00e440d0880601c90086180b1904001c52001e003424059040c40c400a80c0c0c51304080b1400d004190504d6508480c0c1d200e6846074606003d04130284049115000b000c142c502000d1010141704802a10113180d108400b591149808509601d1580041c0012110340741400c0d42c40d84042c105114082c0300d01c5e0000e0802014044030070034412180c0c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73903509 1250 73902259 73902271
    0xf010c0309030609060504020a240e03070815090d09080a0314040302041a01030e0102070309092403030f09141806130e030301140f030a03050a02150a0e0106090501050117 75
    0x105460000b0103c0c51510841038414020f4001042c03902d024810408158026000b4010300010208035607401801c245143d020b07081ca07401c0414a840700d11001929000380d6030300c9400140f16068003820740750303851100d0502039140340046804110000000b41c51308801d501510040e036200400410200c0d10034140329022040d9501654a820303100d4001c20181c0d1071054005030740705010002d014103540d02d4131410500f120340500031802c04c80e00703a500400c030246600c90706c1e41d895118403120b01c25010156200d040c9032116144101110f59034070300640031810b00c216070780c0414040000010000307200d20703c00002c00c60041009000b4040c02c24102d80d0a20b0207409941c1028902640e01108bc00c14441c0d001e064070b20360025a10b0f58940f680b02110070320703843c200c14011550401a2940750703c00241d40041c065040c180107459004081c01286802120070182d204402c1c44024400840c249502000c03d0380000070083c00b03da42c1764140f00040c0c4501303212301340c005a00d081c10000180310000c100d0307811103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73904759 1250 73903509 73903517
    0x30605100c11040908120705032403010608011d06011e0b1e16060f090b040209040809040227010c080d0905030c030c03091819050606070b09060718050f010c03 70
    0x50041400300d0308945140c4d0045810000001e00780550007060b00d000c6a1000c0c151501d6490b505d0401c0c1c13640320134000c3c2c0002c00c03100c200340351000d0040d680a40ac100c010341079280007000756901c043c540d880303580f2a40e90010750324011300001141145600c804100645d81500010145910702100c0c00040c4e031111451800081d2090010400d0002c101e004000c220543c4190032074125060410004031020061f010304c0c1c662400c0300703400000b032088400e1350b8000d404131620811070740c4600f04a0220704c80e443d089548a840000d210b580029000f000c0e440e140d110803448484003200100564281d1021000588400c2042c0a8004a002143c110841c4240b1580549060005a9503000c0ca985c10142c050700450f00045010401403c01d0301680e100c54560403100211400c1040000d001c1082030340a24440a44410000300c1c56202c03a0100c40e601ea60041002d400c0c0c1c644060302c00d4540000f81c0f500800502070182040d01d07002159030000581d5030051080c90802d20000c019641c1c081d01c20801c40c144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73906009 1250 73904759 73904783
    0x105072a06020102030a0e010510051002100203010e040309060e03060f070c020a0305010e19111003140f06030f0a02011b0614010e04120504060e0103150f0810050106030605100c 78
    0x81030a1180000200500c0e00090303161304102d503005045d5060a2644400760385080100311045000c07020000c01c80c5c01c10f40e400060494000012400c08083e4081210400d00020000500d5190206001d21460180d9649142540c03158003ca0b50340540d4040c4079455804140841e03d49020160000c4c0c1184450800410005181e408694400030650040d107480c0d6480d2450244040144034440e064240850401006c40d05642c0300c00c0e0304885440708034000c401c40346900600030301030317400400444040c00c0042c0142c9800b0000d0483e41d1803c44085000b4059030044075064036000403001c1c4c00307d0b4161200605038849c25000d100f00c3c1c02c4084142d80b680d46811120684840b00c2d00c200380a072a862003500079a10f03290406401000b041e40000c420413800f0082049155400b0700161200c0b0b0003442c1c0454802402d11050f0054240ca4204007940007800c41d000444140000d80035010700410300c010b10450783e9640040c0d04944052141581141460141002c13280c800c0303100740a40ca01c034000d20842 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73907259 1250 73906009 73906073
    0x20c1507030c140f0a050601030c050901051e150c01050403120216020105030c07140607020610181806020409020703030b030c102001140403021b03070b0a0302040801090803010e070509010507 84
    0x5003045055003980c46d60001ca005005000280600d00f02410041d15061015494003000c9042903140e88000382420540417000000c550340c011880c800c042c0c008000b2612100c55039840d034020002548e00300d0110f003210b142c04003198414001c0d58910300038490810364504103a00103407001e90004042c2d4100c45010040710b000207100c0e40040007050020001000b0500e40100081e02e03101020b002444011160401004215021603100c08a1651a0800b0511203c0075a4541ea6040c240ea40140070900118010441450135800303007a403140a5030b001e00990403004281901c8aa01110b1a0782107820341090140060090422848504040c6501c0035081ca020410f503003151900c000c02000500d2210500007419410040004446075201c1040c01460725500025542e03081c40c4504900800c0101d1948401802075040d28000c02c8018024480c45880b4500802154000d004070805d0701121380204040b20300c0388087d1448a01d042c2c4880c0c0c074010036512061441c0d00a11440d20080c1d0520920b008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73908509 1250 73907259 73907263
    0x20d02030a0905060c07050307020d050a0203061906050a120b0c0c10060302040f0507092c010e040204111c0207020a03080d0b040c030b06190e0a06020c1507030c140f 73
    0x8850711403201d00042d1012589425814040003510f1880300300300078400600440d01c084201c1d0400f0f0344c101c2c3e006400b04481c0c034040b8204415018081c0d1315026003020040124a411084e040060f1000b00070080681c48808100c43c1e991a400351030901c1c101001d05800007100d0a5030140c00c1101c804040b810040034a00592822800e0101081c0c00b9480c3c00c020821420240240d8440904c3c81400784400d24001100411284991181a403c02a0320580c1d82034840f0204516480c0004007240d47c03007541c0c542c0808500c00c2420f132001c90003103242c1390b01c2c190300c3c800c00e1050b82c4d040c81413603000d10744503120080958003a4001410690344568103400010004117084000d04440e05950804100c1103811010802100d10b01100c5509041c140720381880c042d55030174110b800381c02e00740c85e84140318500580d045803e50459005550007810320f040101e109034000542055280040752042c6a0f0f02d40b8068004850040680040c049141060b110000075014201c1c00200344000b0201c0c0c0c00390a202c071940b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73909759 1250 73908509 73908511
    0x3080420151806030c0d050c160c050a090c0207120303060e0406150b03100902030a0b04050708010f06030b010e010c0609021905130209091f050d12030509011a0112020d0203 76
    0x10540c01c000050841c200b0000d400c181100701c10868a0a04505e0504040ca809208050895080c5540c07200081c0c10906070703205a80222402100d02d0318940901d25092216006a004c0d0a20031002c000000849052074010203100d42d41039405055680d280c031300511410390300080100d0a15451700e1000c40d90402c06481e4920441c061000450b460903500e00602d80103495420840c1045c004000300b2102a07007201d012801c5502c0a440140c2ea42c2d40e110400006101c044650359029045c41d0601505582c8010403078140c410600b0800c102d42c0d95501c0545c120380450007500d000c281141d616a2056000d0b14003100603034002d50012a40410550024001f45001c08485040b11380001d010f02450a2114107510424807501c82180780003070110014580c090020b0441c002040c000483d04842d0b580b503400440104800340c20b1400c801d0042c50040d002c241039111120000c0d14020004025003014000d0801000b4440fa90381021180e420046030f88220454803140310f5502000345800d80c0e46584011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73911009 1250 73909759 73909789
    0x7050d0809070e1905060307030b13020f0a030501020703140301031208040609060c03060f0605030f0103110a18020d0c0f080129040f050108060a0e150418030e010f0c03080420 77
    0x604d410700740701e81500c200c480140c0b140b4007031340c864002440001e038918490f03500800d40030780302244004c01d07200041e10705041031102c039001400441c001040000540141460394401c1e105d4070400d10044101d107149000903c4050800c642013441800814041e100c45600700e405808045402a12a120340b02034403404506400026a82c900800c02102c2c0440c209001d8550342c6491071541c1000c2d00f40d28070344d02060001416864022100c2c4100d66a030700072180c0107021622504140e1020904010001d42041402c640e105040861050189100d00285002d418043d01e40301c10390b900b4090050401e0079403161502c0b400d0306442c1054030080058018000411500030080052410807000418000c3c0c0034008a00410104030b05214464100d038000c2c7d40302400c002c0690005981c03500080c050301c0841155504020500a000c0078550303c014a8043c9100c01e889903803550034490400c540c0c824510402400160019001c600003c140b0100300c28600341090010243c010304000060843c24407040b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73912259 1250 73911009 73911031
    0xd0f051302091b0306040b0102030c0d021005060906030d1404120f14010e030a0c020117010611150702030a080615031006080a1a0118030b19060b07050d0809070e 71
    0x60411450441c4003150701c50701481c4002014a107203002403d45000141c48184102e448550500140e48200b09a8504a07501d10031160059540307000030b9101c0c2908842c03110314501f403100248040c00c00f0a00140070305006001000c1824080c541155050107000a901c2c520b0310811000030b541e000300c6d010103110cd006090b0841031544901c0e201000d01060b50480300c0690401101a5008e4004404c0d03900d143d80c40c2c1402000c0c0da030749200481e102d01d000600c101281e130030f41c000890050343c4500d5000c42c00a10400700d60000040030310711840560102c0c1c4070401603204204a1104500c50b0340380035000200640004540380031040c803da0150400c82e440c800744a010401080000e0748046090b40022a000041003008522200002003020308802541808460084001103c0d110ba01c050003e40d0006500c440c0390802d171040c40e00c0b000000903140740031401c00c1c40c0855205074100480c4d13441a4070100401c2010140c803019500c0003002001c003101030042c400c0009040d100b82e05018071502d1030b0344ca = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73913509 1250 73912259 73912291
    0x5040501021006030f02060d0f02040605030a0c0806030705060d020403020603010b0316030507020a03111501031101030b0102030909010e040305251e020a061d040e070e012103050d0f05 81
    0x2441c196003802c515090505012040020a00365404114442e8050342c90954511321501d02d2005824000c0c411000035200140010300c155014000e180112008141804492808442103c83d460b09580d500c1d0305801c6503104100c6031500c14010b104000d1841005820310790380b50000380c01d41d0400d03488128010000000c20480109000381c00300d440325141020446428903080082d0344040600c0d00500b40b000c0e0b05407000d1038110802c010030381a2040d1040041541c0c42e40341a194140038002d01502183c10002074504540c0044282c0d600042c024064100c56881d20116036070a50000e00140c0a10004001c08903070b201c0303000c111940c1040f2080d4480da00140f80d1030501404a108410341140004102c01440103941c2c443c4800700b00c0e6114500107034201d40d001000c03100030501170061a0b01ca403030100320040441007c0faa200440b0000c42d0340c040c89030b90b5019000301124942850107260401980c000001a0240d001fa04019400c03640015480401400000c11110305891040515624007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73914759 1250 73913509 73913519
    0x9030b130611070503070602070c05040c0c0302071508040f0215160b0a02040302010e010f110a0c08010b0a0308120705070c0311030c010e0f0405091006180c020c1302090112020301060504 82
    0x300969050350044840b0320314140941e211507403640100e1100601098002540100340065a108000a00001003041240020303601c000f51030001e0f0200110050700410000043c0003460101010803002103885451150342d5a41c2c424100005600040340d0102d0f5200c2295102407200002c0e0102c80e5500b4501211002e2034104031400e22001000d6100c1140100000c1c40143d0313000c403404124200a08144000c00314030503090b100440100b1002ca141c5c07044444100074811140401c00840b8201782c020441240c0040500003501180d00014103e00c10821a0074040201081801c5d40800c0030700d0054204421942c40d03007595502c5600c00d4030045030380c80c06022145814490101101400d0801c0f4032240d17a40c801040500c00f2550807588030fa070352040019901c440600003000082c1301094100308561b01da40000c0803a0f8500017810680d5450300b025882403d000040c82c0c010326000038a101e0b604a403064000010f5403245401c1c80c10004c0003200c66240401600180d4043c101c1529290740b15400d203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73916009 1250 73914759 73914761
    0xe0d061b0207030c0509060d02011b17070308010801090b19060519060314071d0d120816020a0803010312020309030a05010e0111040b0406030e0a0b0a0603111f0f09030b1306 76
    0xb5030412441075000e0000d00c401940c4904c007a01a482d03081c00c001c18a040c0307041e840025040208000790100c41e101000414100c5e04000801100d032081e142c6253f40c3c1d803a014860300300c4581520080c13406d507503007000c40c000d003182a401e415981002c18020820340d485e0404548000c3d00240d04613502501250144103041c2c15000e10b55048030404910a40c40c40c01c3c8000400800a01403a0380f008a851a00c4002c140c845005c03466800d90051a50032003c5031b0100001d14104040300d00010002030b91021160451003c5890500c40784c002c0041401c503400c5403186401590828225410340c03100700243c500782e0310140f00e080a00c5020324000109011107566940c00d40d244400c3c0d0200514003000140040742c01e00e0140d6064840c140f60000340201900101440c00e1050500a42070300c080700c00700081c03445507070425070a0340d20401402100750841c0092120681a060040b03e10800c20303100c0707a009512511040d501d0318003e283c14254190f90f6114050304100aa4043c003402d02d07440d041ea0240012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73917259 1250 73916009 73916033
    0x201090602010e060106050a140f091f0804030302030612190506060103021c02030403020a17030603011b0c1b05040603050606030c0d08070807020f06030a0207170405010e0d061b020703 81
    0x10a000078841d00d8500c800d10f81d00d98005006010522401240e90b0f41618440d131500e604404000303c40c0c81d031381c0e020303058841e81c10740103000145d102d03c000c8160070300301c80e012620000710244c1d280c4a003d9251601c0c4c3d82940a07400050030750303400c450400360608401404200084560900281503580d40b0241d042083c00c120b4000c0a0a040c180100700101540c09503a208900d04124120010b8498985d440d00300d041040c010000740610300010b44c1c1a0703140d1000c40041d07001d914103c0081006c03d552a03001070400c0c400d50144800700b1040b107042c00100c0c01c60304a4541183c50100c4c0c03511010303224400030782110000d42050700c2645c0903030100807460600f0030208000d01001c440c2d06500d62030680c1c44e030005d8444c04500800d0b44101084610454a0740d8a05054614000b882c0341e443e490220b000100030b4005104c280d600078403c81c500490140e88004032815560181d40c0e10200c80661001d001d48006180c0c801c44509940f040f058282200c0c0310304140f280e50890b8080c08140d481d41c1003203004450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73918509 1250 73917259 73917269
    0x30e0105130b041104150f05010309020d0221011104030b010e0603120a0201090213050a05060f090a09030c0203011401030b09060115030e101104051206040206070201050f0d0e0a020109 81
    0x85840240030354850700d045030145442c0c2c020800d840c207565514280114a5000324410340007400e000c1c007400a044080c0d04202540d205915000e09039560394011402d40300203450181d00314030b48a0480d4054103040d035a10440034003018034801c072005102002d50031210359030090240c1203001b01e800d00810a400d11104d0040a020107101d010f810f1002c00684c43d140005800e189000b000111410094002c0d008603c0d0b6940003004104001c01d503400d0380d0080d0804a8000c44a1840c010004103240b60549400c501c403031010b030650001d5510848001d00401280c0015402c1c00307400315006005035000d0045161010748920140202d51561038504ac1143c4040c021500d29089240180144580700c054040652007501d00490000003804001d4100005060003040e818105a43c40c4091142500200708440b020303a5001d030f1061042540c152a5039060354020340c0314108002c03c5002d50b10880261040305110b6803014a0038404003140310071904d00e8406030f03a0782c1c0c000d080014295038010b80020001c02e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73919759 1250 73918509 73918511
    0x12110601060905030d14030c0a09030503030106080103140f0a02060a05040b0409060303030606080702060615070515240a0e060f0d060c030b0105091c030908010e1c050c07030303020705012307030e01 87
    0x280451b10f00c5d100902000300301c0003000301d011030078910461281203103000458000e800d41c2e07500e50f10381d9802440400c00340019507002020b1507101d100c440740001c180d010000300c103014145000260f8200081c50b8800030441d0100002480b01003040c01001000340001c14280c60000b80c84e914514000c2d0039200d91ba808101400320040411491035008296154407010440d980040200640c0014070b060090f804d01400758822024040040312121407140c1c0038130003111007810180407451801e8a0890348000b82c0d6004019180100940c1d410b821056821480c01045980d9400400000c01c40241c4120410f44550f41c80346045503606805d13100e04050000280303401440c01d20103002180400c404015075407115144400a030003418420b034141006402e00e0301c000d000da44008084242e8800400441350402ea10007806503039801c0c01001111462040c80e4041d080c51440e54030f0607030082d084210191510b5482d0700b2641c002040ba03180c492442a040d511240b4a41001c2070010101c600c030340e8a858041e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73920865 1106 73919759 73919777
    0x90207050a0209060303090a1707091415150910030f05011403100905070614040b0d061d040201021e0a020a0b0304290412110601060905030d 62
    0x1030b000715191509510707480201510307841000b02490340301d048040d080100c40700300388440000025417015112030960341d411140a03540c259402c103c1000004040000c0c52504142d00c00361088207546408444005a00c0800984140034080e441403903050003081d5018840d030010a03943d40784010038490341d40c0d580c8034889001e01e40b0f0070280c801d02400803800c20440b128402ca00c40c01c4d0b00417004000341c2d490301c502a60054004480e074665248200400302d015240600103060224481c1c1000034010702d0700c03000d03800d550122051030240f0709001c414000583c0e800100d00403460301c10514200808004245a031919090040080d0402c140030720000c2c01103154005141305a004400040004c40948444513040c41200000341c00c240c484c0001c44c0c08aa2a0010803000c0d007118200400e4000d00c07510342d103240c20b802340d01120008500784400c1c00b16080a004000c4002501d080c11100 = true := by decide +kernel

theorem cover : BRFrame.Cov 73741009 73920865 := by
  have h0 := BRFrame.cov_init 73741009
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73741009 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73741009 ≤ n) (h2 : n < 73920865) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
