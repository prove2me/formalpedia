-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2930
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:46.415982+00:00
-- url     : https://prove2.me/submissions/64241233-528e-4030-96af-86d07d302d26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526798561 ≤ n < 526978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526799811 1250 526798561 526798639
    0x1a0d0b06280312030c110705060a0e061c150803090d020a0305060906091903090e07050f0415020c0607020603040f052112090d021207061e0203090c 65
    0x11001101c05940c400d00e5400361600706602da0409548450100da80d14020034206011400ea040c8070b032182c1d0900e049240050004142000100000c0c2e03400030801008012100031082c007541e49440040012039042440346104d1a6400e00600c161010040104070113108036008004039407001c401c490641d1b00407039109030039060702e1001031001001c680010f003091180d00c08001000b80001803c1c2e0061580b0011100c41340116450b14545d207251140050000704582001c01c810303103442082c4d40c0c200803107081050500550420446098016600c100000141c000c50300200c19010b100c6411080d50550b215442c204040e00810340c0c0c1d210280004001c07940076140032042c8001440008a4142d00992500120840311107000c40d03900b03c1510703009800302600c0811f124a41c00104d00b1b401900f2500606458400d90901e848030303801c456015a155500da00180300c800b011002010300000700d011005880b0300b403020425241c06042a0564000c610109100d0b0000b9828020803028800c55104508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526801061 1250 526799811 526799839
    0xa05030703062309010203042604090e01060803190f03050112020603040309030b07020a0204050609010e041416030c08210319020f0414030d080103080d020c031c1a0d0b06 75
    0x9210f2400c000b60700b03900d4a2806110710b110040d001140698040d5140d11403492202d5102d00580c0750031044d150207807400704030400440003642c1094400001c0400002012962281501d04582c0042c942c0710480003001015281d443d00b150b00c4044181645c501000035605100d6031424210a00d00040c1c407440020000908240c42424a840510361100c0103040908140201a60b1003054100c01c80c07145041400264070390510400d10707812100e50003284080e41d16203440d000502d5000105820803030043d16500304650608501d10b40085120711010658113181c03400c803d0519051440303204180c420074081f48104800e80e42602d41081c0955001003017010b0308000702c402480790758100d4240b001d0110780052004084800e0384084c0030290150350400032000301c02c565498003400300070014402070059441c0790300203602400f42e4440d140b04403864440e5180c00b08040c40a005040e9203913030307100c1c2d00204200c0c4100103100c4001005403441d03501000259034064200000520460203071a40300c0d8045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526802311 1250 526801061 526801091
    0x2190515090a06110f010c110d020a08090f0d210801080f0a0308190f0603060b0105120106030b0a05120607140a0503011517011205061003033006060e030c0a0503070306 74
    0x5c002d03182d4400c000c00030403080040140940d141a40d4196403401030080c02c42d03805001240ca072558980c01103e0a00e421028000c210a080400c0c110710380080071050f000340020001d10750f0180160840c0340e0294071192564005118900503044070b03103650040075100b00b50960014051800950500348607040b5a00c5182c4070043c40810441c9001c240d0401aa073f00c4200b40340e90181d41601d0045030300f4000c03031510384d0043d202481081c0c80d00c004c450b1800010072107940700b40c1c042d48401c07074000c0043c40300641d0744001070801407101c10410304903080101401612504803406100c05190041c0c0c03107040c844851800b0b0a80d020501c91008201d007002242251030344503030700032030b540305440d01c034055203503168007501515040301181180c480c480c1401140105a080700380c0b204899059444150b0302c2055006c9c002800d041c0810b80ca806900700002c0c01300c20340c03039002d40d034060134003070b41c0752038080c601101018039148203212800c0c062500b880082c007031a00c0100b003103015290452000f040c00803450b2242 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526803561 1250 526802311 526802323
    0xb010f0305030a0c052a130b011e17040302010c030c1806180b0a02100b1903020f130c0f0207090903020606060f0408010c0507030305060f010813050a02190515090a0611 74
    0x1e2801c0304208011340e07540034154144031b800c0d2001a1141c1c59510107075541c0c0d00484d04003a01903030120700700c0c0120541705103080c2c10211218045190021070220741c0402e1100901e000d96046001d030f519600703003103000d40e414440c05000741105c0c900844080c030300c5a010031102c1014001c042c100540000500e1314444406000d42c01083c9000050b40c0e030f04981d8000a48070a540c0204180003400c1c100b48400d02d00d8508031040054401c6881101c1061035642041000c03184070021a0b003005140c0c0e444082070202e48540c600245068480c4030700100d098100030309040c203e800c101c3e038a600c3e002e072440220340d000900d036034413201c15104960b440e005040c030305c0128001c550181100b9820140303040c02e203c0e0b10801420b2954402e490910064407542c00f08441480e00c0d82c6201d00141c1c4084c00100401c20280d44612494096402d8400002e55a008200c460b000075403810b111900a039000c000b1403e10142c0c01c21445011585141440440070005007440c04501c03401d0200308812101c0141d000046c03040e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526804811 1250 526803561 526803583
    0x21314100e0f120f070603051f180203070e0901090614150711130f0c08070f2705040f0504050c03030304170918070905010f03020f03011811030109090b010f0305030a0c05 75
    0x8540c02141d1b91000200070301400c40c1c2070724401070200b2800c2404030072204030b0410f80b100c50350300e41035070071043c0742c0d0b1402500010003850800c41300070702c030210a0301d0b1411124040c1001520100b1520b05140d28030101c2040094003a003e41c90240c408030302c3e4989d103416283e207184c1c00b01c0206007080a00c0001550b065a48403611845032030441c81d0307a400561a40401c845410640724400c1903640c207502070712007643d81c40e01c1e0f0000c00da4030b400d00741400c0300d0aa69114800c82010500c910346455001003401c03200491295100c0d595078906210034420104003484820a00310002c5145d85010741d07442c01c0103454090030b13003010680814109107a0740c0e03810840c0000310000030340d410140b4020800030810182031050780d0204000c4020360208500c40e00848040c00440e0144500d16480c043d100d4090121410010403000d540f40241c11108404d240210700030000254040f40483c0181814640404181d11048545c8640f810410020b2804800d43e084101142001c08550000c2e041c07890a150034000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526806061 1250 526804811 526804813
    0x100608241003020c031602010f211e1d0118080a08070c06050901090c0f140f040207080f1806040f09020c011b0c050f161206021314100e0f120f 63
    0x50310f9050351090f0b034102c20207c2c001da0703412480d82c2800d8001d4403070b41d607400e4000d03c02a0501038100b0280d095a04034441050543c403025001c02c0da1110481c0c111040b0407414a0400d5140302c5441070300500740514210002180010707084145540d5441c407540c8103241d100c0c8107019040c40010aa140180c95111590782c015509012070300c0d10280301c5008284c00441119403a104520106202e41022414800d50b168403420f0181042460100401790342031001d6594082c1d003c01043e400246220064002d2410840c034081d103030350711240c000c41b0302001201124041c400502c030803c4805013483c1060102e0300b4074400180c0e102041d040e1035002d40390034100340290951006284412580c032451203a0703040d0140b41a0b0782c2e4102038100a64865209050074400000502014010002507602c0100910721814005181003140030f541c0e5640500c50b0b12500b1560b1440364814510300303050103101645491480c000750302c041000c0010710320b4514a0802d030f004030048110311500f110300708106040c49902d64 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526807311 1250 526806061 526806067
    0x131d01180b090a0b0c0a1d0f120f0a05070e070c020f2101060602030306120c0d02062d0a0e0409050601091104170f0f070e01051003060b03100608241003020c03 70
    0xc4c1d245170030b5800030204c2c0c400035042a9400f85d100200392103000d0301c004001d0000942c1e010003810401c01050f00380d00c4040d607004244014035550810070102000c107216501808040f803410552000c80c001c02060700c400d201490580e20016510040440b0748a80116041c11850a00c40100480c1540c103818034491503107807050100c0e401390000007851050340d08881034412014208811600c6038100024141c00c04548480c01b401460440050011901040700403011a111500000040c0078606400000c40d0300000d482c0b13110f00d900001509041d0030035501480072840598440e907488005200c4c0c184050341d520881001801400100c40040c54030640002c0186941c110440c0c0f580c1d00114411000c1c070501608000442000c00c070700b8100d1341400c880c12960307840d08080c011241c031401101c0c0708051781c7e1800410310a86540245008140350380d00d108920381401000b8140103030140c0500007444155203100c01d0810b050354060010003007640c6014414034140c4003a00a40118490218540004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526808561 1250 526807311 526807321
    0xd020712080a0c1d0909151302090709060206070c02061e04050406050306040804031b0f0303020d08070327050307061404171206040218131d01180b090a0b 68
    0x1110700e014410114003004115032048044d608030150492050280ea000d9150050340e00d800f84c1180c2c1d000748928151649860714110411440e0b1044548030b45200c0524507200540c00d103111000d500c50740b0703400c00b00311040c00d11101a580c0c60f8010030b06010410070314141c1c421929200143e4200c04580716001c8024942c5140165179034000e4010b260269180040002da41c4c41d00240c1c4e68004e0740c0241c3c006140908540b51280001003428104112800d01500020094018240030700194002e6004c0d08000400c3d4400130032030500070b010710041608108140c103104581c48c0c0c964618000c1000380c0a040d00480c036110b82580200c60001d80780c2c074980002e485c0f00c40d000d00303141c0d031050b4400c80700424241c0c030401490300240170f454100c0b482d10300c1d43c1000a500e800c252b401803070b40d903101110f600d8040800c1000248498a5000c0032604240c0701e250030450421903a01c1d1144461b2100028040c0780079080041c103001e1241f41c005002c021003e00030402c245d00910002a249800480d12001480c107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526809811 1250 526808561 526808567
    0x403082415040905390405091e09011b0c050f0304150210020408030d091509080a09050d05030703200105070c03080c03071205070311160605012403020d020712 70
    0x100780f249100041c100307400241ca9148504c560b020140005980341c2010b6440c041400c08040050f240c20b40146080001140a80d60040f1003881040c4a9000442e0407a00c100d11341e40202000d022026240e042c83c070400070700000f03644030342c40c45c00a524280030014098140340f4940081c491072480940000100441c40e1003d00d64100d06120154085841d8410000000401c034403880c843c4041c00d4200380102100104190007401c0454052004112510440c0240c2402c40d100340100300d5075000c0c0011b1081026410141c25401441c08075050701e945003131034a841c0c3d100e00c100ca500030100402d428010402c1c0c004405c042c4081091200200030381d150400003d0455150301e6003d401207100c8c900059600c0556204991251035159258040c1e1242c0d40e43c41c0c1d010b400c01401d40418107407501d0a000020b00c218018111b6009002801c1c400810ba40c24030600b00c0d08180c10048040c4941d802c1e6488500d1641c2c50085a003178586130050352a03034038080007002409200e400411003940c882c94070030a01d47c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526811061 1250 526809811 526809817
    0x1603051e2220010c0803010902031315051503010c0801090213031b031a07020307030c0206040815010504060801020901021c1e05070c0803031317130e04050f060403082415 75
    0x101d200c03028002c16040c10019104d00641c408000d2a04c681080103125825064010350340200904054200103250b66488441c002d00d0000c0e00360086a8480c208081d036041c2d00c15070190300ca02035008100400c56500d0080c04a1414000c1c54426a0000303041101401e042c4440c82c02135070800300100e0202442d4a030250700e00954030081d5032503103402000e1200f5449801c0b40c903009468079002949001416913081d94212002c0505903071040701400002107a40c402d01203414030709801d6135402c080d0342c1018104001c032055508204201d80c4144140700d05660000307006000780e01ca201800044d042d45032000c4544460ba802004e007070b1003802100b400c071aa000800740015500c038813460220719482d003d6295036400100c9005a40d0b0455100e400007103610320508182c24944103d1580c90715a01e48034010031010103500c0f820055404108001c1408003c1c003400c2d8078141600050062800c064800070900c04000e409214581c4080000352448440703c02141d6500c0c9001d420040000c081c50341ea900503030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526812311 1250 526811061 526811093
    0x6070c080f010c08060f040e0d0302071b0f1707080706110c01020d0210091104090c1e050109090c021e06060301140c03070e0d0611031603051e22 64
    0x100c200350354400c00c1501070041010454140d0744d1180580d5030a001c104200c158030411540080d03650100d065800360520600d030307405195440150b40c2d801d1515198110300580807240304c50840c003400c00d000001c191901c6100b01e5090031485034016903454551420003005500000491040309400650340750800c40f0000040f44120a580010341c1e001e005a8480c41080300e01c0b80180c201d00c0d0450300d03002c030740d0748005400d50040d05c00b1556011070001007021520403a005440003018503c01300700440000c500c180400c140c46030500d103210714210010b080b014050147c4004a910f5025014415100304200301e823107002d5002d4203640004660900d40c030340c10300341c50150281d42424400242c0b0880000440c0c052503080304801d00d50780d144c0d517045032031a9454403a41e034003c1d221300080380441e4807400341d03002c0c080f03800f40c006649041c0121030714440030840090300701f490304000c00c2000ca24041002079020140e5a0401c040995859414181c0344419241c0d800d501c04510918001b0f0141c1d0f400144201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526813561 1250 526812311 526812313
    0x702011806020c0a05030105040b0c030a0608010603050c150a020c01140903010213090c1d100309050f1006090c020d08040305040b160b060d02030d0e01090504061e061b030c1106070c08 81
    0xf017a1a00d05060036a201114050007508030500402c2c8000315000086a0048050000103030441e2683c1856080d00ca042e8000e4400b64031561209040d494401024011030b01d030000500d14007040072801945450351603289034144401c020100390348960210448040c410010021580c4850b0850080300000140c001d034190f26140a4644441c1030140e680d100c460301c404d148501100c030030b03141085280140191080109034481200314000350040082e1081100c0340d00103403014007000085281150550ba11a1444c40c0c00e0018070103612b500072420071464142864440c13080c6e5038605040e10b4504c51079000340000c120001e14010a00c0c101d0080e580b5480c8034800c1d0920640f0354004004005a5100c0060b500d90400008801040e00619200c5407942060501060441d0b44100060444d405c80e40200d030142410940d0601c40107001c0340e030303c0c00380c0144e040c00080501040000801c11034184801004c0c0a0384000301400c1c842d4a14000040c440c000700910b030f030362501e840c0445d62080725120300310351 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526814811 1250 526813561 526813579
    0xc270c08091605130902061207080906070c03051207090f060e01120c0915031107060203010923011e08030f090901060509030616030f1406150c120702011806020c 71
    0x2070403480000c071403c81d50018808101c1c40440c00919005250f02d2a0807a80040c08106442c0900e0104031810311400301030312051004c0c035000c86103c0c1801401007659041005051001000a0304a0180d071000c00d02c1144601c2140c1e1080b1060794442090340002c0010041c0000004039107a0202503c01070703080030303614441242461501e5005881c621a0380c0303000304001c11001e0044045980315800c00c0c10f076524021401540d1040801e20607800343c2001c0d107020342c000006110a00380f50103200c5514000c10400300c0e0481c00404019250070040c066074a003591406000c0281c0d1000b040300c440a02280e00540f035a130341030b000680d5120f50086140354007071034410300001607150003042074a6540c840030f0050301a5a944c09801c2d081c40d4944003501c000d042c0e640039071180340b8507540b1802042003207180003182c260815004200041c0c08220bc1d40e01910002c10036000203040206010b100005400e00d00c80d11030a86100580e0900ba96080e00b2940d05003101c0c00080040d800105000d490206480c40e01c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526816061 1250 526814811 526814833
    0xc0c041a0a06020106050d030e15030a05040b06031b0909070302130e0c0a030f080306010302040b0705010506011d0d0f0201020a02090a0605010e0f010c03140c0a030e04050a0203040c270c0809 84
    0x1c00d0345d500d8440c00354480b8441d01d40c400031074010b8101e076840e81130084c00034510801031080d45600303030001e031413070695540d40e081000b080098201040350041c03421002450310a840c8001c0281c803e0150507014001c0790031902154410508104044c0955130042201d0204803402c552003005081e0030711000b00600c103510180b405800d00c101c215040da50032102005048040307032500c03074540c0d1014000c1410158204000603509114034082c0054910420020999050120004201c89021000b0022007640889201065a030300c1407207240c6168801c4100807028000d00040c0c1c241581c1c1c00020707400c840c11404201101120f580038005551090304c0f40303c10b10786000144914094010340781401b050f45007003c10003190048200da4551203090029a2610301d00c413441c5800e2104490080300800c0b482041040145028000d03503034403041d4a030045003507180a4440c03081c442c0680c80350009403180303241128440004003814441c0442007100c00d22182c4000394004110040486420005001d8081601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526817311 1250 526816061 526816063
    0x70603060509040b041b030f0201020d080118050903070b07050d05070503012d0506040801090b060d08070807080f040f060219032024100b040e0403050c0c041a0a0602 73
    0x4056a0000d030448482c1e54403a0307a500400d0341c001c0d1060b0317521508900300f1541e0b1200d0102460103984291442d40c070481d118030019143c446020420024040910010700c202c6c0f40d403904040ca1504000404540c070b40741e101140341140300d81d07400504006050400c100d669030f08040100100315000c8410416079669030380848050200707006113034584c0038641c0614152501404030710100ca07440310000c145990754500041e520b03800f66005c01a541d44401c0d5203000e0003000f002c0150f002c1010b80b41c00400a00c603954410701e034070988800520f2158089013101c203000c0706030242d03195000502e221581c1d9607100c18008d1544d034146c0c4681001842845142c2c82d0010700f41c0744c002252989a00c030006040001058400728001c5d100c880c41c014401d403c48070f007624000045200042c4c0020300d1f0355840b401c1148858034880e215800c800c406c103000704400c1207840c03441346e5000e5015400d032030b100341c45605405146c2c6c1002810002690b105090101100561640e8542c60350300c200c04603118005c40e50b0b148401d13 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526818561 1250 526817311 526817321
    0x31106011a0304030503041b1502011415041518020405040e030c0d030b01050d09121e050d0c03090209240d0b0f06060714031e0403080313050c0a0611070603 69
    0xc1c04500005002040000e40540080c6400501c03404640341c1d0300d545503092041c41d56a50b4403440108201c0c0c0b403048a4960284901d11002c4000f034500426482e04101c40600c0c42d40c1c1501007802196203105000000e080d40c51103c0140c8543c002c603122144e0340c0c503541c03800b83d0400e00a5a10031840c281d4101d43e02ca00c00400c0760b409404002c0030701200541141d082c2e00810000d003010b410710000f00303c0081002c8040c40781c404c1180c45030000320940039660300d00500d46440340e00c0d40308056140482102d0071682240c00c3e40c1d15401040e0700406c84d4500140128094000400003c0d00300c3c201500748900201d400e5510003007030f05c0412000c280b1860003001c00c9102c4004d5100504000c0c420404242e684015610465203e18098501450101a580c9016489005416030051500040742160200301d54200c1c4078060b040d0307221464105030075500c8010144c407016050710011044030903c40200103003441003070620007008050803450340c0d54203c090026088088084007a010f881400b142c250b00a01c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526819811 1250 526818561 526818599
    0xc05030111090d0f0606150302041a03060a090e010b1c06140606040612110a0801030b0a23090f030a020c01031b02060408181e01022e0902060f0703110601 68
    0x200340b04100c9244c43d00d12808095039403d985060b266640881c40d070340c4c10358030b806003501d582c0e070016500c41c03502a440ea901200114100c45442082061048599600340150140c956002e00000e182c41c01100c40750050102d0222250011108800e444101201139103448115004100a01031070101c19400d41034a6812503540394032a20501040c0f02d15072040700340610010004000059038401200b5161032500f1124040001441000041c01048003a8502c030380c201d00303c0c09060001955408181090031961002d1070702c05400d100010703060140030400c81c1d80c1300302d46a059907074609100400a441d07400101059010904144180300b110b6000f000c48000c1404503409030080342c490f0307a0340d1620780c0c1c048100c1403841030584000204035074078842c0c5050703a58a2031002600e0620307548000790070b00c0c0e220003a220001450000d55404c011040b50040701c100d40e1854001000d070901d1000401601078045201003414000c6490410150081c500d0f181076112182103404980ea95600c4000c941c541c0f850f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 526821061 1250 526819811 526819819
    0x40506032a0a0324270303150905070906020102030c071e0b0a02030631050c040e01080304030b1303020604120c0812040c0f060e010e060c0d020a15090c2603070c0503011109 76
    0x5103080d004610484c0405c8000d10928000c00c4041002080600070504d580080503001c2d603400c207112620360440c0e00c010080950380000e50030b40c40e02c90984807660043c6940030b802e81c141c000000070307540180103006005681c06148400301e406c01c07810700b000940088826500400001c1c1420360b184940810481001c01c8030002c03050400c0e800b140d44005000040c0c00804070203001d0001041a05040752081c0c00307000f01000450701c1741d00e9030402003130580000c1c0c031840300c4100c00d56031400825404a0f030030350721507009054400740952802c030445100e00e0070100607003540070108004400500c00c10701d2034051805110070340c4510361141c1d04503291084901c5110082100b0450600c0d695005d070740c14005042005004038205010403001d641010b090403400030050300400710740001c00c00d048200c2003154504034400c22200e1410354480d1510017482c0034009100710701905101d42aa51943d2711465040b00106881c0c862913545440b903000502401880d11a508009115107004018400d941d14494020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 526822311 1250 526821061 526821101
    0xe0d0303151d011802090d060902040c05031e0619090506031006080303011206060b030a02070204110903030d0b0d050a05060405060a0b011202090a08010203010b1206040506032a0a0324 81
    0x46228290b100440b415074600c241c0034411b026113640c91900101c10300b0b0041e00007007007003a1350348104000c9654000c2d07540306006051080c0711501c0803012110b91100c00c0101480c80641302c200c0000c908211150001440d0744800101007000c8000e0b4000d0340c01403000b034080f6243c5000703031500f00d01071300c440740280035865005100400c82c40c07000c01601006180100c10001e515900c82015040942c011600b036a400c41c0c000072000c003181494404c01c14448000302103641880580c00020f5200d01c218030790ba8816940308d42c50040c099544480046a0703c0d0301c413080380c40581203032812039180c001c200ea05132118001d0f4800610317000c4a9000d07050442005a5607444003588042e080e400075001110b030507070030041840001c070f2002e00900c01140600159451540c40e0007045030000410400103000d030f801141003100703005150b24002005101c59031400e0203c501d400302d008000034044545442640e2042da103031000400c5c0400c07900c200110048506170318400c008000056420f9500702817401e40030301241 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 526823561 1250 526822311 526822319
    0x2070515270d0e27070302180307080601060c1703040c03170c120d02070b2403030f090904150f05060f0319080c0106051e03060f13060c0e0d0303151d01 67
    0x313a0000c60704044c4000d030400c8a68695031890038003003000c58610020a0340010748030785030030680701c12596140c0214001c216450500d1a950b48420f4103100d070f002440808121002000681c042c182c400d080e816180d5501c80ca000e003440d00c101c030140c2c4015241030f06681c1009110755070f480e0483d00104802d400500f072084103000441c1955000c0030340b600d402542400154002411903040e2405108241011008081c80704101c42044089104182c801e40c0104105080f5014901c181d845c080c000311180440f55640f41408a4000d0070044107940da076181c82d66110b1103100540c405801045e00343c40c0d001c046200d190906585503c01909800500e500e00178203400148048018400c0158060001c41c0b8507a69001042a405040c002141c1e4612401c80044041c10104031080e8042500c81b0046006c2c108444401028034001c000501096264400720003824020303000742505060140800c185d01c4110304004000385a04401655601003e21000454007112054010b00ba03403841144c0304a40d00e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 526824811 1250 526823561 526823569
    0x6040507050f1c0e0a03020d0f0203040e0c0d060302060c030a0801090903050306040f0f140a0c1817120403030c0204110f0d020310050a12121803020402070515270d0e 73
    0x504098078a80540b1130400c0c034680c0100b031010800c218881c0e0000c10854401d020045d007100250b0b885241154418013041040b00782040f80560001130072601c040d910300e40e039102c010280c1411740001c4e4001000260b04c1c003200d40004002c1c042022140d0740d0b43c55030b90320b4000840544070342103000f8000503024030100f4458942076000b202d040e9080000050310b001000000e10a442c0080321350000072803100104040340b103407805885150301d00f0745080c0001d24070303040d0391240b1462140901c820041c101c03001310380c50798800c100101100e40317201040c989031a80ca180040008108940c102c4c06142000d01400f5410b10010685076110f03c20021103040c202c0035809403000750001001604c10380a0194002145d454008c0700101400428840d803141380280d00700b40c0750100031110b030b24003041003c4894036200075079000d040c0d05480d81100c0159948105051540c6080c42d10304a0200d11000381c800d002604030b031003441c0308007500340e410096100814100c101c0e4540b80c040c0c13210004180038039034a101501d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 526826061 1250 526824811 526824847
    0x70e090604020d0b09090307030215160c0302030c03120919050c0d0f1707050625051c0c02250b0904180b040305070c0e090a030f11030d020306040507050f 68
    0x10001030f00144440030034000400000090b15000303c40c2d0030000358042415410302c10700c00280d030b2a00080d0054140107005441d1100d40c441c164081214880d0b8000400d13100340708a44da10780c0c0700012a078440080350341880f0a4202034410080600c030340c1d02c40c0c0c4c1661060040c0100780d030b50001c0c0500144092601449403101c10604100c034020001254100010310b0302401c40345a44060b0b01d425110700680c41c00520b0818080d01e000452070440f0006041d030700911220034102c180a01e000703920390302c0c020152007100d8014405040c0050501c0300d1034040c103500080036006603d90581d6000c0c420752041c12404568401d009620010341c0030011710303a280c14941c102c4c00304003140780d03500200c01010f6110456030200944044000800010700e990030f224004050501510034101d03502caa90034070001c1203035281e1500320010148042c0620304c0508a00452074618155034050649540d0182c8074602c40c025481180d060b0311407031600c3d003c01c0350b003841842940c82441030754a103549800101e806001da005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 526827311 1250 526826061 526826077
    0x610090c26010f050a03080304021309050d0c12090503060402100903050a21051c24171e03161707080702130b0a1a04080106030c0905070e09060402 65
    0x408811400c504214010800300c407845010000c040d6503504101c2d501d0700b00c094692181c0d205034052031040c0040b400b0481202e4115504483c11454000d04e0341d0b0350400303404000805041805000311340c6022503040105645142d118200d0410002040c0b00e0a5030221a9401119010303800900000c00600305680881403160756820610700c03040ea00d075506171a019850742c085075007040056016012001c200c0110514698a040180c20500d0003051480400004151590300648500b080c011f0204000342000c0407000c4095008601d640b2512507044a440143d0b580d00310348034104030181e0030050740301032000c580c482c10043e40c40c0c0080f01031221200a0707001c400360740542c90782c507400364100f405400a1442500c581c090381d03103610860040000401c1341d01405082a81847d80d03e108543d10011f102e4140c801c2881d25403d03501424020701900d00560b0000c00e40e540c81d01801100340302906030910308440740c054080c0140d9696940c111004a144103980e5084203540c80070500d01d02e0507070090107101d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 526828561 1250 526827311 526827317
    0xc060702030a0501050c07150501120201121517070e0903030c0c0709020703120b09060f040c050403050a0c15260c07020d12230d050403140c07050a080610090c 70
    0x445072900e0350f600b115820b40d20104541c200040c20410400488031810301c001c80c1000c100302d690f02d0b0032582d00c0041134400000381008240c1d04d5100c4079103a107902070030014004415004415844000315034802c1d00543c090507261240080004400404198561103225190f003d5411b6440c0c0000420680e00300d0031070892a4046c045020078403240d0741c405000c1007402aa2503c40b1131141d128408101c1d10440c0650303002d18520340030040c0c103486102c1c04406010003a600051040c000d028211424001c90b0001005406140113030018004ca10300d28105a4cd4848010007412a608a041d103d41108003005004555011900748042c2c1041580715802820f40000f00d10b4551150b000039441080707410100d810200e1100c03c03200711580700039548002248009100505080b00f440c2c5003a6004e512081100c49888000040030144214070301440c0d42c200b00f4203251140c21003a03101391201240d000c1c9a0060070004800071321714400042c164010344110440d042d80c2400c1010240c00f801d0040040d07818 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 526829811 1250 526828561 526828573
    0x30f0a051b0a05031e0c07141909021b0604030c06020702120f15070201020c030708090a05090a06050f10050a0e061c0f0608010606023406020f16080c06070203 70
    0x70200601141007298030840246640f4101406401c2d4440001000156035840a1282d1090410001080c03020748040c81c2a00305801c907201d0007c2c000c0220700783c034500c0002d00410005921a201d4025001003180c0c1001d103540d0700314a0702c032075030744000c02c80f405400602256080e00128071168001c002040c00030b004d044a40d00111140da00c1d003c0111004051030303001d840c8842004400b104c9664001d5500e01c000d52900700034807807440e81c9001e40000a00440c00009104405980d107112842c002c2c000640200c002d898107500103401030410744a40c40c081d103820682d000003403400b02ca0514212400d5200e003410311480c41d400300c5004581112003600060200000d42c691180781ca2540441d45450001040d01c5102013030b42c50035142e49610841c401da041900030703c44540c02040d0072440b00d104090b50021100d01c1303c06259940b03102a1100d02c000c40c00400811500d81c04a40b080003200680100c502100f2043c80c0141d142007203114641683e00b00c184c0040c010b2070008002d1004600050072504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 526831061 1250 526829811 526829857
    0x905010204120b0f060f131113081b06031e1005060d0e15040c031b050a09390f03270c090203070f050304062318030f0a05 54
    0xb4900400120079149081280e080049541191403091340c810425510083c041e8825404540f403a152401000100d9450302c0c0c1e45d070405003486c0d0540d403808d405107072850341842d51600030359121400c034611219085242c480840590a041c82140c1c041c03500c12101083c0c2c6c0110394299000d210f8050840304229541072000582980c404d40501402c0281010008413241a0301010340313044c440760710055440d500310b0100700124a50350080c4085036001402c0700d102100e1100f0b03000050b001038102c02da211080701c0d03011540c05444da00141070304180400c048240c1e0700481d080d0701a100c00f40a2070449124480082107401d1144584e80302001c610708004c00c803000130b400718107040326017251044041c0400c15011b00611114011180007840540350031451070070607840050128611720f0921040c004000081001c0080302c2d030107503151100d00b4a6050401c1415211481d500078151185031200390480c03940c424000000c402c84107088140c186861070410b141e80184e605412280d6136000320880e07128114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 526832311 1250 526831061 526831079
    0x60906130608011418060904020109080709060e070519050d0f050a0b030105070822230f0105060604050906090a060f03031214010e06010818150108010c1e030905010204 74
    0x340601400e07142d1a500703604280c0801d40118408600621036001c04840fa07146101629001b81c0202d019240030740d507a561400142c4441c1c01030b5120602c14816020b0015120203164002c40c150360085180039082d40350802c040310705000f00783c18510a40700c0184048810b5003e42c0007040107000070140414418803003951241125012a1010302c41c03500c1c0c00c0490700901c1c003032041540c4200d59003030002c07580c1011801c041d8150041000c003410b0b040c0b00c240d20814454400e29405c0900c0a94011501c6200c98000f95074403115104110345641d82030402240007498038006a030240c48014082e100e065460a04109002e00c025040c0d039400e40e5504030115814190748200700c05075010f602c415101e400d07100460011695803211007010340345240c0041c0480c50055014a070450024a000c1510b601c81266a498044200d00c0c4101107106006040c401513002103c2c250407107807603900030000001420b600307403010004c142180d00401c0c250503100c00c0281c0240e00410155000d1070005060030344a00c03a01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 526833561 1250 526832311 526832347
    0x3022d0703030309050706021204090e0c04020711010806030d022e0e0d1205010e0402010f020f010608150903040303050a080c090907050301090b040603020a0b160c1203200c060906 79
    0x70b40000e900c6000342c0703061180410102c002000c2c60303c0144044034225030410800c2c0258000c0c0c1c144107031100340c80e080c40101004541f5075410024011562108a440d01ca50b5000c40c001c0300b82d000c00d00980002750b541c500446d51a00305901c80c2c001d80542621000303494044042507100304103088500002035034003c42441010201a9004000c200d55448504060410400c425585130180d040c40018020708881041d0760342c01c60307420300b050303c002c003000c41c3c003070b0f040c89010a91010300b5031030071030005801100000e10b2400c6525903d220075142d118040c0d440d03124807036070002030081401040380300c4a07188290992540401d6042280341014400c00008103001000d40380070000500200050000c0c1500c0e1080d5409284110f03002c000311803842d40801d2a500080c42880c26040c4041200105200d1040400306407551040c1c0c0b20362400e46a1010948503840014107a00084a650240528002c8400c420401c03d00c5031009155820b0200100104e560020414a4000d80203114802d40d2852006070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 526834811 1250 526833561 526833563
    0xb090606030a0e160f0e0f0613090602091e0103060e09030a0f090b0c10180c051e0d0515090604210309060c030c0f0203160602030a0e060a0b1c03022d0703 68
    0x803d4170024a01560794140e440301916090a10301018140f040c59030b1104603501c00d00081900200e540320007402c0c0000240036590b515500881258480102109100d00341d03c0d0302d042c262810005070b5140c0020102c80c3d90700300c0e4600c0044c0c0c4200030101c03170b690007030800403035004d1207182001403140c99810b030300e007260441c510001c0d40364400f0305400020300f0780b8001e9000041c8903110b070002d030500e07030744600e00c65400314850310340540e030710040307007000030100a0720f0160307501d005083d58200d54083d01e0040c5d503c1144e4008060035820540100326030714408207000c1e00440d0442e10401c0b219045102006034401c004040900b8155641c54400001d00640980449251140c50005803850302c0080605099007103202e800131900100071841311002c050482a0b2282d822020041c1c803650b442c00c042000340401c0f841c1710805e12401007084000c10507a00100110f46043d00d150079585807042c140070b40003e200c2002005a000300e83e6580c0040089080e07411003034002002e00f1181c1c0d8002c0c80f21800c200c0c903900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 526836061 1250 526834811 526834829
    0xd08130b041b0b120f15300102040e1905010e01171c0816260402040b0a082413020906030a060c17010e0603070b070602070501060b0d0b090606030a0e16 67
    0x8108801105c60750134031544507024404a803c03003010200055280000252501d22072002d440d42d00801c09505003410b41c80103001c1c0e008540c1c854035420b40c03400011040300c05805180109201d1a00f07036085005460480b1603003140110580d01f0244a01c55002d905024808a441107840c50000603815031910060038046403190b03540350030803401c2e40c00e4801d1916408010310a01c100b07200c3c480c164004182121001040c3c0c042001c1e1182d10000d0702410b0300072071042e40036030100d41c04103184038003140d0a1070180300040b0f01c403940f4419001030040d03214101e82150500c0e450804000260a0400b0740f6644480c009096403101c4410b81d13035800803641d080400c4c0000449444038805004401c0741c8007070240c844103041500500d04100040d695035040c1c010385007100404075541041144a4054580b01c60703200d0001d02a132070b100c030411000394104815003013a05052031042d040d5420404a070600510b000782100d441c69540004400140011001e250b00c903100f00540d00d084011102c0c01a4042d0040417 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 526837311 1250 526836061 526836097
    0x714040f05033c0703020a03030e0108101404050c090d05011d0a0b040326010b030a0f05160518030f030901030b0a060c0b0c0910020d08130b041b0b 65
    0x40c00e151408481d8208104408a201c4514203a4150210207400496081d8081100c1d01440358103c0c0c2040750301e80c002504116001c1021040541100340c90f03c01107001e9070381c2070342a43c89429000000c01c0303600c10040c800700512190592420960082355000c54440c40d038514050084000c6241044010b50584031a555000010f103c10b207400c040c490210611070081c00c1c5600c0c1c0e51511703411040083e100500b40500f40a401e80c0d0032203040032100c0c07484610366090806607981d40b03440c1c5140d030084428a00c0a0328141103094030000e00d10402d4003e4101145403074030f000d060700041d54540c1c002460110040e1203134803400b0240c4d85c1084005844c68000c0007460711800f002c40013605442040c03400f0340c03103410b0b040b4040c000c090f4042c080d0164141c100986101c90f880300060048607120304c001c8550001d892883c110300041d00000c665040c031800c0c5d03507100d916a84549522003011101e0100500c640403410118010400342c0c100701e420305250025a00380e03181e03160309002595015038003441d2854025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 526838561 1250 526837311 526837319
    0x20613030309050609090a0e0c0901140108010f03050c040b040e01090c0906080c06030705070c0e0c0a090e010501020d0e04062723060904030c0c180b03030406050708030714040f 78
    0x110003400000d103c00d039011814400000d0004188100c01009000c030941d41d100800050007003081074044078480540794489950b1200b4442000c030040038112408241003600028081c85901001070481e500700001c0c040c010301c5441040043c02210660a5004c0d4581303542000e805001c1c0705e1032004a00c903010f6800b07800d103000c0d0310340b09481d110341c03140c5410b40007001009140e4590508880d4055864a0b101e5079400b5145005a40701c0559000b842c10400075000b00b011230101000200b1204025031690700e05191f45802101c00343c0000d0045e0b600603040b6040c80e0000303a000b0a00158580b50045c008250340792a42109108089004080d1000e460420b46406402c002e0b84148a9040c0e000d9640301c10001c0c4040c0105800c03c0094a801e00900301100064207241c81002c4121005900144c10800f0b55500c0300a2000d801102c0880001c0500d03120100b5458a400000c440c101c60702d5446140c1422015100d01700c164200800d400c080c4010400300035850309a03000244082c00300010b0f014021410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 526839811 1250 526838561 526838567
    0x8040c2c01061706030a03020705061c140f18120f19080103120206061c0203010f0c020c03010609151e08031912150506090103110d0b041401032006070206130303 71
    0xf0240c01c06000c0e80100300200301003940451000241c4400b50f510ba5520b02d045607410840098488420180c20300d8500c4501c58000b21030031240c0110320310b020701849503d5070321901c480120b544144c0c61207948584140b840501c1900090300305d4202d4801d0050800400d01240702c0004410b03420113000910610040c010016425004c05c1c2e02c04c02c034401010b403458401c0c040751090320724070003041c81b011410185404654094000740011600bd61091121800401c0c0280d1388000850900d4070039400e080000c600034204d84124209d4981d043c4451880601c1c0c8800044039a90000351480340d55803505010a02100400040100704541e0802d6000c440000341c0080000110485810319a8140740d8040f401d40310340c10043e400c0d240c0031141c9039500e80c102401640200180d02d076908401c90042108812814030303900880718580240c0d800c2c06480c0c1d0b02d03098900749542c08d020042000e6a040c06ca0030607140c807002080d001c1c40b40900003510740f00f200d40001e402504100d540309001a0310303000138001c25074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 526841061 1250 526839811 526839857
    0x1f0e190906030b0115021009020409050f011a06070b040b040c030f0308010303090f050d1101032702042f090102011103130501111306080c091909050708040c2c0106 72
    0x28101050f0302030341411700000c0d10395845c107003569442500d440c440c400359500d6511003640c95034003c2c1180c070f025004240c0d40c0d029103030344c404904401c120751082804500780b0204031030b413840c2d003c1c03100744281c3c0c5c0740da072100d02e00b180c094420b440d280704030b000120008000d010441107460103a2240c244540c590f1800030101401a0049001c1135001c2a0420181d280c50310b02c01d0300f065008c405406000d00c4000120010311f02083d035492140090713984204c8004101b400070b01814001ea4007400300484d0485104034844900d1135415059156001030707141c180c003c9029280c49501440040340045010042ca9070b0780d0801d944e1060314410382510401042401d00c40c0181024682821500b40500b059010078100c0c1548108000d00c0b00140002d4404a032100842c0c1c4400001000004202c52026080308108100e02901c0b800a20f820007090696010b0712a0500c240e41c81f50341c00314400d04000b00d28801114084030022741c18030b0300c0400b00c0b1142c810b003200d0b40078194580d03880312140c1c0c0082c2040e540ba8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 526842311 1250 526841061 526841069
    0xf020d140105060f150702011205070c03020f0604171803010603080d0507020d141c0e07060801060c0c33021b0604030804060e01020f0a080702010e1f0e190906030b01 73
    0x101c0030044c842602e0720b800f440d00c0c035000c00ca07882e8207455020900041e9002203081030310012040c07501c0100044581c02000d407100e011300030741c2152030783c003601a443c940d64002030b0340c00f60210352484038103900350741d0400040c461030003060030075004511044040b03402d44040781c008030f8a505010540341c211809910481e503012600344024009081c00d014007411000c131390b80c2000f21501c000101500c445011011542050807000020000000c00503a0907483d0b01e284c1c0100c5c800520358000014002d4450800d65500c1c0d070700080c0240320702d0300d440300c800310700e42c400e40440c0000c414000c00c00f11035070365800c1d0b0801d000f011a000b8101030540700303132188604841040b0152050030700303010910201c0d03880c00c20340c0d0558140d800d02e242402040030042c1d151110881c400802480340c1024282008001e0b0003601600e03100b170707c6101c0702a42e000704100303030b04284442c5c1c80000c007a24117040001a21400c0b4400484030b003d0440114944e05469001040d0f07065003040700031544508040041142400f8098014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 526843561 1250 526842311 526842319
    0xc0709090b130b0a0b0f030f06090f1c05090d0b040b04110a03051015080a0f1506060c17040506181503040b01060c03120c1110021905070f020d14010506 67
    0x41c104560b100d0508074400303410b4a61451780d820a081d0035445420414500b80802400c0310b0500c000e05080036030b00c1208990004d02d0f401030001104504100144c01034480b942c0b50fa01c0c00c00c1400c010b400311026006410b00075070000c208034820000c1942160320f1030040340100d003c0351007841c050420f070b22981400940301d0b000c0c0420300d40130008500c021801c0044c0305051a8081025049280e6180f144001500b049050340a01e0050100308081004003140541c0301f0145c06520126006140e81240c2d034034411032002c14004040900002c01b01c0a0b03003550301e800000c2140c189511100422000d2700404020052840b4a56083c0c00c07501d0018844030300e60070001685840c5180c582d440215121040c2328000c10300c00609098000c150046543c40440c04140c0010441c55151240c000d003071504841008203280200b0111400000d0309008848040010b0700b01c0d00b4400f55150740840d282c0e400070fa015070f8210444000c61005960308503800a031980580704040074a008403409a00b1600013034401c44c80703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 526844811 1250 526843561 526843591
    0x601050303040603020f0c030c030703091e09050a0623010318081c020720281818060b03120c07050103050606210702210301090209060c0709090b 64
    0x45035900004a400766805440c0150705ca0005009214003801004405100e5000100d0f030f02207180000406442070381d01940d00c0000310395950920b21070841d10101c00105240c0800c4083c40001a2904016000b01010900290403903031520403008160b01280f02240c54540c040740781d895581e05000303002040c260310030b400c043e188066550b44680c4c0704075414170000c01400c80e1900d9001a10790b042c0c80e1049c0d00701d0608410390b41c0c1758804071000a40380a04074403550746c1800c45a4100b4010000c00f820001401a41d051f0f6801c017201c5003070f640e200304040d841c041e440d5007150703181c0c141c460180c490480c81100c002c075041e00038000b05400c0804040e1b05a8071140144190004000c0c00104102151b0003824009172a480341004101e1610501d16040e1031a1a08070b6018642c40c820360b03006110304503aa00b0354944804d03c818038031304070131a090100d2100605000500642005500404200e10300500780362514685030883c03070601006038000fa034601c0c0c1e5460940c003840705007100b07194171184904801c18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 526846061 1250 526844811 526844819
    0x708030c0604020f0109080a031e0201021204060b0a08030f19050c07060311070605040b070f0c02130e071205010501050901050f030d0c020f03011503060c052a1e0616020601 76
    0x7a4404000344040d100740d00400003c0002d0b4003038006a03000e440b50000303607580700c0c900d81409032081080e5064070803400c080c0244a6000c5206100341c031840f03400c40e0301804603a02e032501c6020140c03481d404141c1d4806044580010802d004000414900c2c41c118802a00d9030080700850b9440028005001d0910508005003e0a0744001c2502d100703072401814001890600b034000900d1034004c0c0c0c000100704a01d0b01043c0b10501c00e041001c030f442026942c0d91481c00078407410b4100c0d00b110119000039086030701c0c450407050248268010070582c084020403140d071320340d6540c4100c24001c1160000e4035245d41d40c00040c025400c0c44c840c0540900400d03200301d81a40940004250740c0d210510031a01000b100964800071551290300880041000074000d209142d04580c0d00317200040740348001c4030034524042c0f882141502580a68010102d540b0204502c2e0180800d01c040c2070404040f03a0b205400b030f031000c0e81070015142d034030a580c144404c1c005003841d00c0d00e009a080c882000c03011010940d441000104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 526847311 1250 526846061 526846063
    0x10e0607050706050a110705151609030605190507110c030d051206040b130b0a12050c06030a0f0f1e110301150903060204091e02030c09010f0216080d020708030c 71
    0x9080e82d5400710300040c1541e40e00203010003c00c240201c61140000015608081c0f000019034101c03800000d03525040140c45c1c54600f103040e40341c0104c10343c1c042849914100b002c180300380d011960200071044840c90303492242040350110340e022100c510101d6100e5000d5002c0040c20442d000300c075802580280100c112041000e081801101c1200c10b00343c10311400280e194840c0e1b045040280805050b101403a400c0f00c0e1038401502c8104010342c041c6030084000140742c200c0c400540741c00ca07004009015940324050600181b9800204030345c015544410091100000c24440c00301e00040020000860000307110301c0043d40a40c01d890070000905118411588003041c0341180e04484458a183c00c0301d1400000035140d0b86102d40c00a000c061003c140014000c11a800c00602011900760010050041003c410200e010517903034042d58140a104203401e035406040300b099004010300480b40140c00c00d809258420107550014a0b00f5085a248240c4d010380422001c006020540091030415110702e0303500d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 526848561 1250 526847311 526847317
    0x1c05040e1302090412230d0b010801210507030f050a0c0e160e01091205011d1908090103020405040f0e19023303070201020c160302130506030f0f0c03010e060705 71
    0x2e0480717480c00000c41c030b4082c003030319020401c03100751700c0c140c0000b4103030f40c0c014040f41c0c00a4400c10f120b9401d10f00e60181661092051a050360a500b04c06641038517020028589054412021a001d112306180440401c0c804c0c1c9030301c074200740302c1c0006010807040303454a03900720134040d403100300c0038200a010f001245042c000c40303480003022072808000c10f1000d04012203640c0140c0d40710740d00f040c0c200d503000300a0007819080622696100f518604440b100c19400c250b60b10002c105036000840074240b840000b031103001c001d00d00448140b60240c281515030700002d048500154a01a055076219170030203003a0414020b4411560440890300805601600807485102c00031441070076400d561001c0840b840c0802c51909450701038800c9150310780c90f000074041e000f540074103081c404500c2810921040560181070b044140c03507003c2c043c8401c409503a018040a048040c21450740740c0078000701d203042e00c0c000300290b031040da601c500201105c800c404141403c440a11042d90920b0300000c082001240d000021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 526849811 1250 526848561 526848563
    0xf09030e04090201020705040e0f010606170c030601020106031a0405070603110702040b04020d090c03170310120609020405090309090f010303050a120b0405010b030103022119051c05040e13020904 86
    0x400301d6000b48910040b410516560440d42e0b00c00c2c42c1c48a0030300c43e004001800c0c07100f102460000c2010549420003694007404844120a100d40781000140d1101c1000e0b01a50f04402c0c103000110b61a510f80d952405049801e08248080e2000c0f0402c02080c4a02001480014016410100f01c1001c03d68941c40192042c0d240107400f03076480d419100c056450720f60490300f6018840d0020001001e076485c0580c9050701d00d2000303884070380f070b0741a04807451810001224002c00c44004050015880d001914228252248064a032280c0da000c142000da207560250911810040001e10b0f43c030350300c0004011001c0c40140200074100c09803001800025000310031195200c2450800d070751f200e90b1403540c140252410301003140c1c101317090400009607000c90a014605a030310031a401603015079030400c04181c2400b080e1111802c0e90005450140444e468400941000d00070000c1d00c203c031500ca5480f044d461070f50664240028030005081041c0d02e0001c1e0980d4020303c3c403110180c2c40e06c0a940001c0c10503200584 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 526851061 1250 526849811 526849819
    0x507031401050a0909150908070201112b050c07030b1008070e0109050414100207060b01030c08150612100501020f0a030804030311040825060f120207080903070305100f09030e 77
    0x2d2100c05020a001b6036014400400c0010f0003800c6583c40c2203209600301c6a0200c0c00308200d500340300a043d80200e00e50b64100c80c400000c10b00c0104503148110031041d403e01034010b20604000c00070f0003400c00e000740d4024500403d10551542090070f07070300000725a2030740040450780180360203000220821086074110703054400041025143da00300080250304510800301c6500c0340c81c400a40f00d982c580c000c5d05101c0c1c026003080081a14800054003540c0c0402c41c1c0c200010540c80c0020400e031b489620112041034043c022a041c5640c800d10340000300c2d4140c9203a2581d24552501b048103680c10081214240404c0018100001e0035a402402808014000a00b0b0588408408104120b80703030541d0300034070048089824500d2481222100100102048503d03010f0094001ca9410b0064151009848455803030080c10b152000c449030003500541c001f20f400c602c1c1007100700d480340c0c1e0401251003e140214090160440d1400b12031041701e890141b14507a540c00c00f0a00320100e500002c5948d10f9000c192 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 526852311 1250 526851061 526851071
    0x80601090b0d0c201605060c06060904031b0f0c0801022b0b06030a091a09070e09030909180721080d110d0b031b0f01050703090510030507031401050a09 67
    0xc44256500b59010300c8480740844201004c03540072400081c010001c03c503000211241c10f4551052008a206186402125600c0500452103905005800e60340c054028039107012040307103201005002000e0b03420151407540080079000c0038030100c07451000081910800031071910070107100c51290300f11101e013001030080030515060b003201981d0300b0450034004c00810f00c030380d6440c0c020754120040c00e401900351607103a010f015925500c07800c603032914002c2c009a40104501890442d10741410f441c0203081c001d0030302041c445600300c2e4449203246030240740c813001000902c4550102e01d914040a0b0b91241100708070000780c2c1881c001d0b0b680f404825154010403000e60340c004e140040710181460790400341c030402000441040601840d4086402070f00214160b402c10100342030f40b0803209441d000c90551181070075860345031382c0d80148003c1210b1071103410422102e50f42d4100180c1070f400400c2c05980403a455400304201d10350306208070569144090300320006235040a0200307410f01d1150140c01486591a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 526853561 1250 526852311 526852331
    0x1170717031e03090613020105040b0904110a080f1005100e03011506020309040609020301050604091d01090303020306040f0e0607142205030f031206060703030228080601090b0d 78
    0x140300300c4840407140c10420000400c12142410660703c2201c0c0d004840c007840d004182ca20f100032415102c0c0e01d805a44240c24181010140442d035404103040b00c2c0d00c0b580d6140d010f21603607041c1028080c41400c5840b480d00b1882d06d10101e408000c4000c02c00d030b6181503031704000d00590740c9076049040708a0180c07800490b403242c040080784c0101007459180d00002020080096100d50010081860b41c50a58080c003000d035440000400703900003809610f62208040c04140142e182036445000382c000c03885400a21071192081c45070858121400550000e0740000402c0b05a0900d07015032030480c5100320b0704102543d40110915240c1034080c00b40d100704002d10000b66800302d1300c81c0070f846030040390a41c8103235840409900a0744001141c481c06001e4002d000440d94020070203c02d40e40703d040c0452605c1143c0c0e440004000c4079612100045082c10303824030a841c0d412040d540800d01c4803084e800c604072030309100d0601074200500106150b041000307110040c003102d504081a107120412079440400c00742c00c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 526854811 1250 526853561 526853563
    0x306050411120105151e060f071a0a0510150305040c051005070506090f0a030302090a121a0a0e0c090a090b070818010b01090e070c0602040f050901170717 68
    0x49001d241c0d2008101d1000300391410103601c294018904c0c442c0000c01110f010060092180002103110140d4003210759542481c10300100600d01a00015949458068140e9402d48403104440385c1070030036442c0d4400c0160039020f522070241c11182e4850801c03c01407801c1040c600a29030550f11008241d150800b14081080da14900c40103488004c1c1864104000361178000c00c07a800c1020280c0300c510070100072841141002c9280101c619030f41c40a03210903501c9031000d074041c0d4010465103411180c441e000151001c5480324021580d445080b46184411b068848421801009040780302410702d000d59145508a0005040092071001e8a103814140d0f43d81c440c00703006165140000e403070507240c0740c1004079007544003c02e02c1c07107590724560349180e05894030032190884d00401480d5010540d61b07902800106021407601d6804582450011609082030381c400081c3c1c0c0260344211918102110103020518040c10740c0c41c0902144241c25000450b140308171651100c50b48142d00b0040540114441c1c0b440c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 526856061 1250 526854811 526854833
    0x9120e0a090608150a0c091703130e04051501050123160506040507060c0b0402010c2402040503010e01021c0b0a0806040f0b0f100e0624040302040c051303060504 71
    0x45414041002c169590203030f54070790303038450010000c424250001844816082c4610040c9081c941e481d8017a207418002220940501c040e800c8215201c00d00c0085880c00031301030b12070040c040707421f071002e102d0506281607071520350464407142403045184014003140e41d0050068a05000d42460101407085415071010301e40b051180380e42c181c05001c40340105021780042c1c030a001303034800d80c201e82030560f4034401202c901e2100440141822402008240558400d40c41c000e4614018038000902c15965909140440b00340c0e11412411500401c08110915003071088002100c0c1d82c80c02503103071146100c003003501400302c00d0940050076510301e418203054580b0034405005e130a00d142204e2071410f0905021003d40c401001c00c99000c628040001c0a0402515015019080345281126101e05206021070b1080006101c1500304040d4418000c24009da090814040d8801c050581e54440c01c2d0b00500003551f444400c100103104080050690a141d0850901c2c2201d40141d0700060b0341d280c138641400410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 526857311 1250 526856061 526856069
    0xe10261806010f1d010b04030305090406051c0507170c0409050a05060a1506050403021011160e043e0f0604090b0a050f031023040b090106060309120e0a 67
    0x111841d400414001000e00c000c4040da850389000b035060b14001c10510080900074010302c580700c40f0500c82007000038002c40240803a032200500124804d904c070000b2540b141c01071880c1c02d540b507103d040c40805108045c00140d016110300c100005030000f502040c0c44d52100780303114890081d6134552458003800014881a00c000f0b601038183c0f000e90421611020141051443c403170000358152a0000701c0e1800343d0200c608a03607001e06030403840300244005a4905100c1c0b645200d8130f000305a06080d24000014031100130b44003680f941041c5003014104521030100080712031503070003c0c4602903000c2480142e260364180b003900c10f0012010f00301e140482c9003080101c540c2070b0850004100800e080340d00d50000c0c08240025222010980c1c2d480c81002005650f54014075016086410224664040c9811403450003035240c0000c410b0402103c01407640c11000c0f20183c440003103400910a10074002c3c041d03640244182d00d400d010600c0107895140404280b5100034082c890400b01202d840e450f10000d40000b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 526858561 1250 526857311 526857313
    0xe10030813031407030f200907021513110d05012a030b041515030603020312030405060106050309060106031a181b0f0d1e0c0e102618 59
    0x1d0501412142000c0d07000d0000315070380701c01a03096000390f443c0056454110b80e0462a10100446651070b00844000d82645800540040c000e580b8901d882e164041e9006e080306900402180810707800da1000c40382d02411040440380d0160650300807400c1640020442d10b021174202e482000c8a15040e401059003034606030006d114031034090b0450613445d10500c1b00d121182c4041c000c0d191031404020440d10f040d881903002141e482021f01c00d40e5010241039803210f095041c00034003142c403a000a85030049082680d101041c00004100400000344061401062542000b5055090050040313446c2c00e8140280c2d0201a951380d0a114200b013910204032860070f026140101fa184609080494800122550700d118110400c060402041240484200b100283c0741e03581018420351036840130b048202260341402c500d8107005800b00d09e640c8298445a6400e031196030356000c821060200c0c1071100008003045c08813890590045202050401c59410244034a100703a1b42e582041d10a86680740031114195 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 526859811 1250 526858561 526858567
    0xc01052206260603060c0a020307020a030b01090606020a03050316090510090303031505060d05090106030818011407150c11010218030c03070b0706050703020f0a360e100308 76
    0x169003015a42040c11500780304000d1240c4148031012100d201a60083d0705a17000000054000507020050f00c2c0411441c41501d103411403540001c2c1025003180c00590b20b4110341030041004885510820b40100b800b40040c0403095000d48000d00340b400000c0075218010950070703070306410b20320856500700a8040181004032100e0f144000070f004807003d00040b40480e20380001d1a00107101044040c0482e900140103c1c0303080c59140c0e80c0b84c041c0c0310103811300500e0b40d01e0f07600c040005640d07070000d010342002c0300c4850404440c0141c001040d40b66000a8504502c0d4200040400b00302418443c0c00b90f00101f940114480010690882d1a510700090340180d9502c04120404230000c080c4542c020350340100c04a9010500d40810036443c2e181d20f21408401690410202002076490303003007154804868200113003051080402d06e034443e88001600000110040d826140c807010801001101119404031405503101003080d00800011600600d100801110b001a40300c450202070080996445120b03561 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 526861061 1250 526859811 526859819
    0x13020904060b100306180e0f03041203090905060108010b07030905031e15010f031b1d06180105060f07060b060c0a0b070302030907050925091403030c0c010522 70
    0x40107106110b00c581c801c2000d070b40102071640c4a03020703c109684a2082d003481454450824030014110000c00061a000391050401c02d184180082c10080200d9a5202c0c45d00c0700701e203030041410556401c5505004e00d03000600130566030080042c0d06480b240410143d58001d82c0c1000d0780c809034140d000f1649803050345d602018003e529900e0b40030380c0903010115925081d41802400c0687e5090252070440000244100702150081d0035425884500360394880c1001c0c1c0b80d843d1420103180074052228008400401d000c0755050030214503a00c00300040c1005060350401000071000d10441e0a281d145c008042542c00603c061580900321141c00103007100c2e030300d008003594643c64005900c1c043c1c50420010001132070b01c6000340202d0b4030400e10000946242e5040504001003000007400c1414004003081c60f0a100b640882502440c1141075280d41141514000b80820783c003180f5030b00700740250018042d4007501440040c0030862076409007400c54454069220305076203070790344041d58041c080402c01c0000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 526862311 1250 526861061 526861073
    0xa06060807050301021602010c1e0c061e090303030b0114040e010801050c2d0c01020c010e06090102090105030a0506040b18072c0d0203100608010b10090501050a0813020904 76
    0x400311a00c05090341c503a20759032000c0608038011401c0d420070140701c0038125001584500200040caa1090181001c0030b101030b07120300c0603040101421100b2070403940c1c0501c1400c4c0c12850300d0031030728940c2400204c081440c0c80d0051680003948401402c2c1074440c5d010350b078103a004200c400d0318030300c0e840e50940d102c036901c1c03d0342d0300d49000a100d90001c551801e80412070400320002107402000e03104151003200c61108291980e911b00b8414658407129051001d070140715000c0c0010001c1c00c001000104451500c2c0300640d041400282220322103a104000b807031000d0f600301c2e05882d0712845402c0005055554a0041400b03840746074641a40b03d01c80f0747d010710403109807040090050490340e4614003020090084a0920480030800b03914080322562103000c1c9203006034010104620180684042c98000d00c80c050664840350811125079444038a8000765060011110a04007a00d25204003c42d1404001030a81d2241003494810070100400050a07200f82c611445100d0368042d044240924107070800d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 526863561 1250 526862311 526862321
    0xf070303230f1b041a070302011b0c14010902060f030106080604090f020402090d0816210917010209030d08070e030f0d0c03030e072403050f270a06 65
    0x140200503a42a15100c030700d1a81a001d8400c80c0c6000c0d488009441d985000080448505000c943d651410040170403c24200d50000c042c01d90f00da1001c42d12070119103030203803d40d500f6503010805803803860100c0e102c4c2540040740c400303040e0f0801680c000d01780002c000a400b400d02c00e040a904040001070380c51020120000650407075803103554008031900c90703200700000d8805840c4003510303901070444654090716107580140202c90303005111201e0303110940d50318100c6820805142030b5104490b0040c80502c02680a0313640008000354150142400d540405440c010543c0901090300e958203a0072011409c09604403201010018215007820300009030040501804449100014610400881d140d04001496062505851000d410b40d00c813880412211301c4d200c12803e40405403182d2002d5198801071111201030300c2e80a9100da10340700c43c0c00c60400610307208141da004040c0b4140402c4020308003001442d4104a01b0390010104403203280001500d000c01000e00c00250080798210701c104083d990103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 526864811 1250 526863561 526863581
    0x23090a030f0504030c0302090c1b0c01140702061e070c0f050f031f02030a110301170d0908060c0a11060709080106080f1509070e040311100b22020f070303 68
    0x52240244481c4000c0b58a80a140720083c107100100d40d003480149011034080c0d92100c125800c80f0f0500743c00d100d8100f080900c0841020726600312001003802540c0c0202c4030440d000d2080bc1031494101c0ca980401c071248202c21003201c45442501c14284048035030402c54414542048411030140e8840782c810040ca9110702c0744921405031600038403014200450881521889110100c2d1600c1445c0e6126000e944010008080d007507031590100940d1501340044c501030120140c00c1c400038205551100c1c60501808004010f00407210410850081c0010307806500128403408503840d101854820b507a081400501c40c0c840f400f034007003080100c43c1e019407400100c40d6510002d2000300d9558203000c1e2a00008110b00601d07030001200100c00300c0840c00256000394040d021601010354030100408208800e8a0450004078020709011a48008014200249010301c60800c080c0902200003010414001344100f07125456000b00000b240060341554407040000c1a207035500c0d901460020010940012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 526866061 1250 526864811 526864817
    0xc030a031415030307170f0a0e0907050903030d020d02091c0b160207051e0d0515060a0e150301090b0705091206010501050306150c030d0b031c020d0323090a03 70
    0xa03410b42d00140021a41c6a000380107586070061588450680a8550800120350300003007000c904c0400e01d09005040c40c2c036043c1c1c1c881450040000030048440c0016040c4410400f0502401d80f0b0ba60b0040b0403030f00d00340d01d214001641c840100c81c040c8041d00441a00ea580700b00710412640300c0d00086909050254800c80603032199554062017245003110f040d088100583c4108014001d504000c0c1418490f00b44e40038440d0302440d00c035000284030b0701c43c1800444464005c42c401d03108402c0e044003610740108007140e102103c40e040400c0380580a40c002e00c8133a504241e803000181c0c5450a61001d8641500300c0d01000091038440d102504550040c141c49000307054070a400b0168a8001c98418161a4140d40c0c2601d162241001c1083d0644081c20546070306608001050412400304010304e00c908802d030012a42c00c07014010141448512031410b4102001c01c200c64100341c1c0c4c0854003880c118040e00740003408407001d40740003013032820a5444594900105c824090300301c800082642c003661290b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 526867311 1250 526866061 526866101
    0x603060c020d02011104051c02030609030c1006050102030316030f110414040203090a1b08070f0501090608060f040e010b04140a0612030c0308070e03030a0c1103010603080f0904020c030a03 83
    0xb000300d080b00c080b080a080f60000c10b00c000e01139481e205842e2503869208050308501c14003683c0010341440e60994500046a00018a0401420b0203000300c0040031400a01008468a0040080d4907480b0013032050715403d0304059580041e90080d0301c0307848000e4040704204041030311044801d40c02e80c0140240c0034113850803440310003645424002c403481200135602500b10f00c2000d1340d40058520900c2800c00d2446d80300f000105618030204244002000342d0080c043c0030520f01400501704801c1a00720504011407001001100c1e12002107040c9440c03000e071000680c801400520b2401880c1d155030160b84a800d00c08011040105601d409005446218080120b2582c601d02c501c60101c20060081c08542a104583c011a0003601010f0380441c060401c41420803444001038110352050000d400414080f00038030007413152000c050303582c411068008125031801c5488150302d42c001d04002450411001501940703603150398040c1e4004404420440351074000c0060003a000d09980d0185240d8400c4030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 526868561 1250 526867311 526867333
    0x90117031b0f0607030606080709030b061e040e0703020f0a06140a17041a0a05090703020f03030412031d010503040f0809180703060602250e13060603060c02 69
    0x145188048a0000000840c6091100350340d030250140404107041d500c1c002d40c5070342014500305014440c40350415641c002005800c00101400c0c0c10005003201c402c02203082810720000b0041180d003a001a400c541c5a8044140c600300392261040000c54950401d04040b240a404800012480c09413842100c80c50803090344041840079902d090b219250009100c2c000c501b1119204130014142d4100e0341c6007014404102071806c0b826280159070446807640d0400e0045c00c4000c91081e4150400c4c01200c0a0066080a680b51580c0c1c1c03115001c007071300c0fa12401c9440691980c04104850090030610900a4541081c0c20040d288242e03500741d001005580d4030b480c0e10701c1e6100764216486541d1010781a96154036540f5603140360782284600f603800007214005883d00056252070030b4070441580c0c0c2c02040726400c0100c02410501403c190b03a9003107516500c8404103071040741c2d105065404060f42d0304900d1340d9082104002462007130b0068903d528129001c03007880529000092901c05c41d400302e841902c44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 526869811 1250 526868561 526868579
    0xf060a090609090e07030813090213080f01061a0c031306080405210d0e0c030703080315010e0312030903040f0902040e06010f09051201020d02030f071b1515030816020901 75
    0x2400c9a01c4c1d4200e5281400001d03400c001504052030b4a620604050b0748402c20030040703038800340b540c3c7c3d594071546d04c00700050b00f400c211014440c13007000002d00640c1e02e0410914024844c018800714040070100d86541081d00c1002510f14131341c1c080c07450b4a8a0340d0fa03038001400740b06050b01c0c1615103000b1443d0038694a20644044d088800405000342d03c2e0140b07030301c00f0f48014007100704110514080c114004500b0380d0100070035009103000c0c50b0800e03aa42021410508030080014886050143c10190130303826030740118850010103042c07100749540b541c9403c1c082d4254400c5401180185071015404034103d42c55a010b007007a41d421030b50f190181c0c4ca1701801076500d0300c0e0b07403160100011220b900038840e504042031008610314203000090704095105200c1c100341d8000712080803a4848080170450728540c000c1c1c80d0949454411403801e01e00c0382a44560940100704107034010f1154441d4086038082095070004c00c0115044000c160f10303000b030000615600d41540c542640f06403440c90000c614040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 526871061 1250 526869811 526869821
    0x3041b0611030a0f090305010207200f090606160c031202010c03020c1903111504050d050a0807030504020102070e0a0c0909060506160204110c060403020607030203060a0e060f060a09060909 83
    0x4195000750f080c00040d0008580d030303c208070010001c000e00403400000180742400540f544900c54203286c0304104252510f400c590040f9014507200d41c0c0001884052a00c40c6058141c000d03000f61400c540d40d05299010300c8031200358540080079001d44180c00001d102900c5003403a200f0b00f1941c0240175440700c00ca4120168080d09005d00035503004860680d12020141101d8a41148030f8141103c0d10120703050040e041841c0310155001c140100e400708410840103210503031003201d05051150a0600c845001070800c0c400601d602d003455aa0f0b408181076a00804c109401440d0040d00144c403854200c0191014020300540000480c254400100350341445001c0c1000385c590140c0400d051034413000004461012900040e07070042c1d5a20030142c1103101c1c2a00400001035091300401c0207007000d1500034500b02008000904043c8188240b0800741d4030f1900140480e11403202c46149525800b00050080e01c0c5c411280d54404000144265003d400c038054108803500c9840d140031266440c1070340c0c0e040d01c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 526872311 1250 526871061 526871087
    0x6040b13200d080a09050f0607030516080c0709020705010b030109020f01121d0f06070f08010302102d0207140a21081206040c030236040203041b06 65
    0xe0351071441c601101001c00e031400d004071402400404000a1900c0d00003055000c003841d00c000a4460000b480319040c81c0301030111b03107402030b01d140c1d1801009450042c941d0090340c50001d1010203000710740c010b1107010002d59120399440815180070703640e51900c05000354007c140c212659400d09116a403a480c040c032500f4a0b06401800444c0102c170ba04004480c0d13980c0e0078041d00621951291013850416001100f5031181c01c98000501032036011810705840c000000b0030303060400125652401c46c0c1c1c1c4d03010480504482c1d041e0341e0081c0c01d1040880940e0710941da0103c40c180c3c989401916070001091528903031403d50150255021643ca94440e51400c0c2001c45c2c40503040140c510303040190034030301c0c900c41c4441007944100c20403840fa2541c9050031680107003005003200b510740341407004514291048030340030400ca080031031034051f80f030480c1442c2044241ca4410880c100907082e00c02c02d62160300390384c907809006001310340c0ca1400f481d160744032411320700c44c0600000c43c48102040311b90040900003c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 526873561 1250 526872311 526872323
    0x515040e0606010e03030c060f1e0124030b03012a0207060206040b0402040b030709090b0601030902030a060b150403060203040b06011115150d030509030f03090f090406021b06040b13 80
    0x7581c0d0707100040d502c110b14240f8030703074142c0700411040301d40800034040710340a00040644940d0030304008048004003075150b0b02440000c0041001001b05901c4001d08024007844002517080c0030168403820340042c141e611615405500f0141004142988960448817400406a0300a110118080b040f660703440280a0900582d12010200d000314044d086680d90140c802840030134081d50300c0d40400d0520f40030740d01c1807504940b034a0f0740300d013081210401d06078054002e05c0c08100446032900026a00c0c000310401804940d900c0c0c140d180540c8036050325a0360014100545a075413a96803030420b00a510854040d20003003080004a01d56601c10078450a12110180080c540700000e045151031305203000d81140589003ca8400d07055545a25420810345800b9407950340c0c070381141c001850f0030f0071201968462150030401069505a031076000303044101078203881e4807001c2d680380d2800310000d01c01c0813110a82000000d01c0c09104080c0010300300d21941c804c1084440c240c44089400400401e4100c0003030403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 526874811 1250 526873561 526873573
    0x3010e100e1b0c07170303070206011d04080a0e150d0501290f1216030b151b03040b07050f070b03040503070b07210c2607030e070807090515040e 64
    0x265000c0403014103d4a02c084003681d8015079294030031403560f400d590801845810120070040904e40620445004020240070a0005800000c3c020801c0000030002441302c6000301d1000c040510502ca0884da542010702001810301c2e819400e003010742c2100b46032003011420040049500d0220b0071508421041e005401c4c8140581072110340c103640c10925030180d003c0b20034017400c026002321451540c0078103070010180c00c141d40c002600400351841c0e4400c0c03030702850390300d40b100e00070f80040811075000c2c9900580900b09041480100d40c190b218030360140d04240302c0812181c00317004010401c800d218085d0001c843c60f050f40c40b051802d003404125800b90032900240100744c0405c407903141c600e0b8054030518003200510894400d514110320342c1501c1c9c907400c546c2c541d002c04465400101c039038024401c05588001e40b070303808090135500c01001001c80041603100c910f42c40c1d60500800161014004440550300402d4170341002d200200030844540e00b030980c3c10380030203c0d141000d20030b900030303000c0041c0030b03100f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 526876061 1250 526874811 526874851
    0x80904090302070f1d0c1c02041805090c1f0c0503040f08010b120307020405040206041205010f05181e03040f030302060907051005071115070821071b0203010f0203010e100e 76
    0x10030344c1c07c0b030345103808281040701009071172400c180700a1000c0c1002e40000b020a8507143c26000464000130505c80065000c6c00e2010307501d42e1000325502031400d209000d150741802001c0111011100703848000c4c4940720124010034035080441448040d150350b000200710340880d150030230461051b0700e445029503400801044e0702500706504015449030000d0310030703803400b80e55600481c2e41c1d203e00c1d00c0a4405940d101c82c00364060300d1500505401c40022404e8003541101500c180e6201c4100d4060a83c0c01d1001007190110075405100341d500614402c0c02c00c0060980c2d03400c010f9265981200c082c29140519807010600b40303068981d0b020401029a14070b8182001983d4051000ca035011080e0b84c021a00240d10100c00794072401000c00c00d10961a45032a03032114044001541d502c60b40c4245c020b48098208010142d02200b2002c1040c50304518151a04d03841c00828010490458030301085400080041280750805800d00e0040c40e0303440300c2840c1550f592100d0440d18a040e01c01824107014181c0d095 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 526877311 1250 526876061 526876081
    0x306021b010618110432062511030105100e0f040807120c020418020a05040608030f070f020a1205060f0f07050d0b102007050d0303020304080904090302070f1d 70
    0x100200b000e00c01c1c013925003600c1d809003030f400300d529500d145031403070034010002c000b89950b8050004201003600e032075040480e1600c14140d0403d01402d4800702a109440e00010b000280810400c1280003a00030491810715458621110007580a80c610b080302070008940450318801c6841d20668128445070300b003024581c1d491460f004405503070010000c03050080400f507642e84c8604412410320441078a0507840b240b0500c5909156580302c5841207191640802514502000300e609044660541d20340e19078841c64010302c0c007046c90802a41015414502051600303500a4226a00d030103201150200d90319840c1003110180701721000e940c0c01d6a28804078007024004c0003c1c1c41440504500030824403a0400405c0c6c509200c0c00c0304a001070b4800303c1000e02150080b220003020744c081d00c0034094403070800d8041200040b00340b00c002d042543c0040001d0070b002000c41034440c1d4240080003840025a00c0c10020350301d2045004000c407818004000245001f41e010f040c1d20b00000610741c5190b25a02c0007921 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 526878561 1250 526877311 526877321
    0x60212160903030f0e120706030618020309100e03041805071403040201020a32010b0405061c02100c020904030c1b03261b030301060e06040521070504060306021b010618 74
    0x240c0c0c00146c0144590480507041c0000009007840ba540021400c0c0b800c011340c12002c00c404d0b1030642041c410400c0c00700540c00443d5009492500c07200c04504007810080652440c40349511401c0b20301080840006403083c00e0300085d0084610760b40704c141d00c41c50320480085620090b64000c0c0541e0004480d0000240308002845c40825118419145035401c2061004001006900700c40745956640b800c40b1649040c0c418150099000d50f042e0104481e114200c00f0204240e41e4003a124030341c0c80a009004600c200f001c070110a9020704006000d007802e00d40600301d50090741044501e002c0c40241d420b0710010500b54441100c0e0022008048083d402c07045080740f0450003940004231307400304094005010740c003002c4040041c907200195030f20340c50958010101031031a07512510034001000104403990340c990301241c50350140007007191440c441841d0b1510300312203a0700154005003824800800e00201703601070a841c50b0802c44010381300c22111344480c22038002e4050842d5010000c030307a091403000e00342d01c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 526879811 1250 526878561 526878587
    0x1415010b0d2d0506040f0c09090c17010608190207030215220206030603010e0f0f07060203131401021e0d1707170406060306110712031a1903060212160903030f 70
    0x8001162a007000c0d91b241504c400800c1200071030300007003081105201030701c034544900400d80ba2488072055401c010254800c01881404100440c0c840407079030000403040398190700c0d05100307070455a81c0121306c2c0c080d4460400b003900304040c80c83d503800201d02040e01580391881030180100e1002e52107031a4208841071300082c04050300b5650350500440e00ba0810021080d0141e0361100403c1d5540e07040c015280740110b150400c81c1150814020413949a5001d850030b0290b0f880d0700040c0c1c6d04c507050340380104d140455807070401115000c00c08a080c400c0901083c074403403950060303031074424a291859401d4080c001c10798040c5c000a02210250049090101e0402e80203481007001203500380c0c2e82e465000c1038842624024018040000c1c0520800942281e40a078210480c10309100c0008811410f127110740208103410b002d90314400c070482d00c49111104001c00385a1148e001c645982000f44003804110045138032062551040c02602821805580108201c940c1a610090200380380e0341c0c101d80075050943d0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 526881061 1250 526879811 526879819
    0xa080d0f0204090e0a0c12030905120a05070f09061d06010c0305120f06090702010504050a020f01050c0106080705010228080d020405060304060903020607110303041415010b0d2d0506 80
    0x300100301003d00b801890801551240203081c18001402e14841441c01380d801090321141905c9410002034002584004a41c4102c0c0d20740c80807408940c200b1304100c2c83c1c000040250250000114845104c081100207645500e0402c0207816102c4d000350803103802030031401e4429000307100040c0c800c0d03101c1c4a0010506110349011801d21000d0340e40303a00450006d0750441d49c4c20340c0351420444035040c804a02540101544024855420903480302611840402c4000c0d00071500d5201035521070340100111942000a01d00030051299200c3c0e0603916844140520b90060040300000c1c03070030701008030403004441e25418042c010b42d4001d50b1090071a0340035000003007025800f484000303000d941e134001461085001e2140401c1c1c005040c074000f4100003004015900740100b94508004a00d80001520780c0b20b54010031903030b1280b80c0d0b0b00c2d11078a407098446880452001d200c0010840b1811207000d8440120009000c0c00134252600300c20850400384200c00340102c48242a00c1c000608a03085a600000050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 526882311 1250 526881061 526881067
    0x414073b0316080106080c1507030c1e03030902030d11070905060a230a09050106020304062a14060a1e0f06030c12020a080a080a1d03031207110a080d0f02 68
    0x100000c1600540e90f005801ca039650310384c1046070000602c4042d550100c211481d04401c00e850300c0104e030781c0c014010050b0401c19154802410403441400b9010100340d03450000401030003034600240038040c6060102c0c0280640000c1c00d0805000d2220b944032007030f03903101422011307040c12400002001c0041220b030384480c43c040001003080645d448036030321035418200d50450b81c1c040b500340203440d82c0c55400079160314a09001084504c0c2c2c0481a90203031883c0e40340c51118140303001034405031811000d6401c4904000398200710200007011035100e10036041d1100380e4806950320144d0300104c600d48081d1100d20706e1061494114289642d01150401800e2480005c2c0b0640369160075509000f10b8210070307d02c0075080c00550551500d141110020444000240404400703591006800d005404c8003c0a001c880e08490090100440301c4c10307000f039006000c480c7c44200f46080001c044a040d10000089181c2500101384000040b40b83d101260300b20603160f19240003540e40c1402408542c1c1d003000465424 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 526883561 1250 526882311 526882333
    0xe1005060616081303030503070305132004060e0703060302011d01020c090702150f06040b09040c1202150a020312090a050a080c030405030106090b040c1b060513020414073b03 77
    0x4184c0c64020710b0107036a616031285800640502200c0e40544440ba10b0518440504001101d0049002255280702654820740140c2d40c049405070025410201c16142c0380020020043d80c154800000c4034000d80c1d40f0011982604c0c5000da050f06461050350050700321209980300c500303000406a07040005032045420a071181c05540c548010152440c48551030f5a400744100361801c1c0c054200da584007100c3c6181c540c14955518400310050348110f04a84800e440e60806640c1c3c0d804c1e03d01410420518140c2c0d8541035040300945941c00780803c00d81141c4010041144110009070200d00c06038090700424a41e40c0648032070720640c020700f20080301071104002c0442c2646003030144500801c0a51000708a00030030303004020a90f0100c074030270820000208402c82c6500002130b03088240c1600440b0004054a8120802001100101c0040e420a0410503140d422a40342c0c070040f4441c61099545140d00103405010900c4402001c03200400c0d4030511a40e9500c049084000e0195a0070040031606500d0403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 526884811 1250 526883561 526883587
    0xb0d0911120d0e10021c05041d0105090a020c0d0c020402042106050a0507020604030e1521010506040803090f0a12080403110102060105011e031e0e100506061608 71
    0x2000801c1c1e00118034224000b5002812001c01d46011548504251200c00c03009558100580d00042001780e102c2c94901254042c4041360044c1034000c004190110600c02403624541c420f100d2280160044d10018410309000d200365101660003101915018000d08000c60300c40c228046e099074059420080021031610302c0b4000710f4140800841c04d0340f20151800c0010440d18001c280764072903400c00c010450f9496000c80c265a02c180d06040001c4001d40303100220360307500c0480919090306140002c1400b0040508058840c41da61588a401102ea80f180127001140c0a240304840703031a44207211550881c94071005140f40d10102030020102d0980d200501541ca851403141a01c03050b9001074180140015865140040302080c00103240552524000828070004242c41e009e40040403a81010340602c2900402c500c00c42c031500744081010840d0441c0000d10390134440007094442e4000d10780300c18a150140b50f1140c2c200915603418050010500c94410f13082243c1254041005c004c4401d41c152 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 526886061 1250 526884811 526884829
    0xa120605060301090e01051302010c0210030e030a110f0a08040512010917030f0a06031104020d0f111308010504080405060a09090906050403110a024b1008010b0d0911 73
    0x51350301800700e04001214041421a5405448401d00b200340c20b04280160b604a0003490456605568400010300388034021002010b964003482e0b014040000c003100301e603034030029070300a00c000d0000b6641404c0207a2031180d510045050000d181503000d1104020070b252549500d80d40301c07022400420081032603503800c0d4811b0310652a500114101200f030201001104004681c0060090b00801130a81503444181d0160b11105603d841590000b40c1c0302014205608190106811903200348481001c1319005047d6800140881000401030a800900702e141406003601440c3c001040514245c00c000500000d40d101c12000000d200e034910001480c88958030075048090f0140e000020135080503d00180304a040603d51a016030000b030300b05c0d000d81d940e00d0021403040f01c10030700c07024040c1d240900c00c40341c0c0348840d545000c1390142c1240c00651000941d24001c2c41402103414007000411060107698201e0203005603200d00205000030002c10801e5071041403128041c0307880080b140c110b0400690000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 526887311 1250 526886061 526886069
    0x9060908340f0923220c050d0c06180506040b0f220e0f271c080906010b04060f03020924070b01090c052a010501170c0a03080a120605060301 62
    0x9942e080d18101072848142283c003110301c1300d4480001d0b07040810f41c1c14a241150341c1c144d101103003021942c1c000c001d018030030700e4000e0001a02c4141803003a1418140e129104a01c50000443d03c001d0602182e1070840c6e40c40015503000070075a0741000d09000c8000465008105400c842490030010b81c100446e00c2295403500c5d21498055080250400202800d008009040484614904000c2c0300c0008810040800300343c1c0308900440e0103030f488151030352419030030a030a50012002c1c50035034400300e6400b4255034443d0b01c40408880d426603951307a40500c0b500c20f51082c00001036600c0700c07442c0c40502ca600200310b6403038020f0520340d0014090701005100505c135034000c48055030000d0503004006014200c030f070042940d90010885200c504401034401c1c8030b05100c030002c0408910016030390106400c802048001207100070487c0d50303114160f0450300c00700018401410300c6101c0c82e201c02c80ca040d01d18041170342e503c0fa030681d0900841600540795241d1202c0048038040d124000481d441e103480c40134500030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 526888561 1250 526887311 526887329
    0xf0f0812180c0f010c06090b0c0702010e0306090c0111072112020615061606050a0608070e01050102030a120b030d030b1302030606040e0912030709060908340f 70
    0x2070405030010449070740a80001d01403500502440c03105541c2e180e0042c10480c1c400e0802e284962001d00c1c18000400c4a01306c010644501801448602d00300c110103000981c0c03003a00c481070403c180d031040556502c0211a05001540441d1032441d055220303409035060626031404a5500548070840c1c810005916044140f010749405070400601c0303402000310700c2054060015088034180010030144c0c6000c031047c601d00030320700001d45c20790310451045a85861030300a40100140c0c00cac0154a13a001d4019032280c0441440390540c01328416140300100b504883e0705070000c616004c0051270513100e01d803001c0206c0c02c0c5640c1e181030b210307402c0e202848081200392555a0000b11842200c013048501c102c00429030038007503c14020440c442e1a410100c2e42034880c003c1c148000c503030b500e10321289080c125984c0d44018040100078405030b107412801100540782c1307544881e601152a0b000440e83d03409103402c144001001501e05040c009104607060580300d04c000b841c0382c0d00381d440e080034242c2c00400da40801c1c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 526889811 1250 526888561 526888597
    0x90902010c06050112150203070c060b0f0d14010608031c05070c052b0e01090911091309050606041b18090905030c0601060c0b012102090c0901030e010b0d0f0f08 71
    0x200f06c034413021102d002126600031401e41c14509070040250003000001071200340e80300b91011f411341e514200c201d10a5401841408454450310300946041040c1e08410b03038540c00e0070f40108140c0700100a8420713000c0344000c083d080542420f01c07100603050292600080c0a03010024202080e010720240310b0154006140e0081d01d42c032141905801107000d1a620200100210102441c2ea8410070247c1210714005001c2620058a262103206205591280c1d03440070001c0655000d000345504910740c100d0041055a83e5a9503030024001540e0940c2101070060a006e0040704185002d01450060b69111700b002a030b00c9501c0781c035400e0403200c8842c0b080c2c80703541c4085081c0c0c0700c1540401449000d05070b507280c04c2500401310340d65000c0880c010b00401082030f1800c0b504220050003040703d42c0038140c0041449205041a9022103001c0c1d00c40c840541c00607080800340e00000d68140503128200101a007101c404103059282c0c01040c0326008422101040c42420702c40202d50724401415400b40f0324250101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 526891061 1250 526889811 526889813
    0x60c0102120a050106120504061b020f07140d060f2004091512080d23010305160321020307051c0909051902091201090c050f19090902010c06050112 65
    0x1500c0a001400c000406083c0001888802d5102c01d1301c01041100c640c010404c0d8440d45810f8014011403034044021110120010748050b070f00054200b000c207a035100b5036440b1ba8030b5500c28058483d00d441c056400c0f140030395040300080d20a034004052041080800949800c54040314008400c0440c0038860800001c5418810002c41d0700c04c0380e14241c0c038103ca0a101601c1c14110b05002e082808003c0c00e0341f4000b044400b14411a50001d500b0b6000d0a210364401d403081512001040c071007804180c9203031150448141082100170510340580707400503190082c1042111194003034140c10108041140002c1c001200000c0d0100284ca4110324600f0703551102038284440100381c868954000c40c02c1c141000180141040303682800148803280e00000f40c0d031200301401040007a0011600c84025602c0c020200040c0809105054207840e0300b21a28036a0031a840100800801000c80d0a031300d03480200742c20401413026a2058411502c18100000c0007074654a480d000c481e0300740d000c540780c80c0a12100c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 526892311 1250 526891061 526891087
    0x20c0c10021006091b23280f11030a1403131b030204111c0506060c032d0f03011503061d0103050d0801140d05030f1c0f0203010b030708040c0302060c0102 68
    0x1c603104452071b00c450302c0b11140c008459813001ca044d8100f0054400103180c8100400301e1100000c1940340c070b074131003003204101d00010a18036148002d0000254003015071002030304080121000380b012547d40107a566111003401c140c550000c0c00c800581e105074030b4003400060351007020f4542d00e0201111014040d146006100a88072202411101c407081049103070800b01c4050344040345003249000006599440704041102072041103920072044c440030071030503040c1e108000304044909002032800c000003681c203002e00075401011807180030100144011310401e90000d80c80034500540b45008035400da51807803442498086a11250286007071031006000340001082444544101413400701c02562500c4030403013006800035100d0b40304091041c0c40354148030040090326030018090b4a0319035100c050445c02c480d4080003540750620300b4100740e594840c48445109481c104e035541c010b450300c0e542d00c40d603007103665100c0200200d446181150010000d6107400010b04650300060780010f0755102402c03120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 526893561 1250 526892311 526892351
    0xa030503040e162007030b16030c1e0503090c040c080106090f030c09020d0f0204120b0f09030421080a08040b0a0c02071509150e0112020c0c1002100609 67
    0x102d40c1030740002460203106500c101c40007a60708508034501004c0c100c00080c6810084c2c80d500c040d120680e02d03030500c86141c25038201840c0c07508141d201001000300c040c40030354100301c440c1d881c4000308210201001d01d180c0500c0055900880000503614803c00d02c40008044480f540c140000040302d400041c8045d41d08071a06e44003411910702c60a02a61966883c064105214001d902c0c5403078000c660300d031801d01c0c650040511030030b5411044d500c8503110303c135141c0d401109000541d0504800004110b602c0c94282c0080c1c018005030000d9440c013400c040c1d800c0c0003002c07402403000090b8000e0a000c80465104006000d06a015507034040081c2803604010101250190041c00000e240c0146200703a550002401c00443e1030320780c000f00c400240a901035400841c154071484255405102d00890103502c141c0500c210360003601d42084226411104000b20301071000d001800d50310280c003101032032420421a69440324144111040052800000c07007e0710215489111116150200105114001411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 526894811 1250 526893561 526893571
    0x110607180b041a0a05090d2402130e0916060315050402090d1e050313030b1812070206040801151a120c07060902030a050a02030616200c0a030503040e 66
    0x4441c141800d1584074000f8404012902c40350f0704000580310100d500620a803100342030028009202c146031428002e1034030100002e080648a140c01900c0b201c01060320a690000700f1070000385405a040c0b0a00c000900302c050180c02042c460200d104860780107801700c0340050324483d40c0100d2680d142c3c42031300f2400c52080d00440c2c890703401404081499107881c0b00200403983c0142d83d5000c69035100701c0b145544401400040c0c045e00000803060281410190b085045910648050318241d5488420360704c00104900e0710240b98020000000e561803850001d411a580020f1980d0301d05a40d6000303403400c4810f041000c03101091021007c110074100d00d140901000c0115140c546040006100d410a1500081c41c4c10341e51031002c108141406110b50144212660140c100c8203011740c0b5082140c2d03205203040040348a4031840c8000780c0c10309200320000300d1911031f40d195080180c161a640406400c1140310101c4503200d0511160001d540301c2804000550045019503a194109203040c20340c0080106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 526896061 1250 526894811 526894829
    0xc06010b0a0c0b060f03070b0319050108150703021201090507110304060e0613030512070c150516020102010b1905040e030309060402100210020a03020c0c010806030303130311060718 80
    0x1999100d01d4105040003041c6070b200b11000a1079aa01c800503400c40e0700340111503090307c907012021072080e904000070740c01000c1c4110a2040c03e401103038600240c90342401004003076080820103c0007049416005508200c40781005410907625250b01100c158007680500509602c600600061a0700480c0103000c41c41554055468039081a0010701700410700e400c01e60243c0340008035109042e00390f46110300999440001c0e955006503407150501140c0000400740c0d241c17514044001403c01da408110100000552a002d040010036081c42a40b408440d200780d040d55290301c4580c038a66038114000e6400c4104101400d84c0f04d0a10f020b210849640b43c1003c00750f030307004000b880110f00002844591250741103031000c1c0c4900c00518109c0c20004150302c2da1031320300c2c0045042402a42c040d0060112802d13644200c0e003420040e40011a42e000c0250794041c0c06400410214014030010038484120a000381070140750655080c201c507140220448424001521100d451103607000c0c84141c05001b400d4a41d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 526897311 1250 526896061 526896067
    0x30406140f070806031501121707030e010f050a0912321b0a0e2509090b04090c031b0b030a0c17040b0a0203041109070c150c0c0b090307170c06010b 65
    0x200b000c041b600018090050740303076070344104181002403074030042202d03002503285903888280030300e0054400659000070b54041084280703007100c1c0300d10400c1512020307003065462800103443c0c03460191410b40c2c0f00e0300540c0c4080c84681450f0b1300c500003101e820780707508903041c0d44c80c22007404001c941d040072000c0d9460303003140d2402403054059031b650120701ca09544a401032903450791140c49a24201c8210f2035000d01342d049401c6640d5954a4214000c40102c401903001407000718100020481100c915600003410940001e0702400464032450f0b850b0740b011504800a40030030344516221040350002c5942c00e4a041d113030f402000c1c20b26400840e00c0a04101a108075070b035401d01d42e844010b001c3c0c008003420714180c0d0200028081c484a4005200a02e0010380701d10f4084c20a01002084143c1a500503070b00b4514030a224442ca82c40d520820f512074003144e40c0c41c0c034101d200b42e4803141440d4001e440014288400c0c8440c1707010811204036200c040106060030340d03848924942c0d150800d02c05034840b4103008414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 526898561 1250 526897311 526897333
    0xf0605100f03150e060f120610060909060305031e041707050a050f060316053f0606160212070b030907140607020405072a05010e0d14030406140f07080603 68
    0x892941500403104442d1a11001e542101140350320840c000d40600600c114014031440700309030703141c00c0705540349503803a042060343325040c0300d054074610700c0f0080c107542c000c00c00e1201d0380107406568602d0b4140c02c0e1180e850160f03070386002000c4810507020528641c00681042085180001051000742801e60326969980d0720fc0c4001010f0b07020081c80712211151b200300c03e02e8218032a4045440c550305500d04080544460b030b80000f11041c610f1224240f00d6a8140f1081154080883c3c3c58407030b0034002c2c070307544c5000d40842c0065070140030034500b2604111001841070344403500344445000303405000c00041c1c591420840e0b4620b030200d294402403c0000c48001100641c544004803200141c043e81c0104441e100e190086030000307075842a06101e1401e40d80d0490f60079080070b800c00d440324003650081c40446032a9240541f1102e41180c03050115065800c0c28145080c2d0801940e401030040000007144100841c01908104085130100d81440003141045201c80d040a891a0010400d900800f800c2c404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526899811 1250 526898561 526898579
    0x907050a33050702090c040b04030303140a0608120a09030c060224040201090308090609100e0109060e0f2b0c06030c0e010c061e1811030d0c060f0605100f0315 70
    0x241d107001390082542900080da6158540101c0380140550b42c1501d0341c40740e9034240100100001c41c1014880052a404540120101d00038141134500e0790015080d444a20644102580d00c550310140502c1606c0c90000003080740b40d40740c1170042c203460b0041c1c030018540640d16855410003e00d45003144003d4014800507076031219001c0280c07540200358580d280348002c000344c070501a081c500b0394441d000c28004011143c0c0681501c0f900e1400780c90b815a4191900c601340e0b441007928401d1038005a41d901c00107258a81682201b090118043c18140d1b0044903c06040c8800c075190400d5800401941081001c5545841141c5034803900745442040e03500c800c00001c040d80f410000207840b254444410519803a0340b00d44450101010510401101c5410002d591203004840c40c1511041c1107980c02d444a030802140d4042501015aa0740002c1030441e61140d0040800000c0741c1c0c0b29a40d20360010415850f40144440d2480c0142c41d486000c0180f80001003e842d6901c0e400410480034100030080518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526901061 1250 526899811 526899817
    0x3040c060806182a0d090209060301090807110d050f030306090106050a050703030c020705030d030902030607020f0a0311120d02131520011401170706080f0f0907050a3305 75
    0x80d00905949040c400000281c4900040045980c00c4d400026903800751284641c04212041d200f6602c101d030301e9640008143c2204c40400001d4078402c1d04204000000700c00010700c1007407500003000c200310315005440e000c1c82c09200b00003000c82540b000040c080030740783c4440070301e005254500e004d61405030035500c01070540c0074803000281070548400c0c04005260080c40080090400503003100c10020321854000c0c090546281d05074002d01032107011800071071011683c04586c0c9440f10090034180c5041d81c00b00c6070070103015500d031a0360290040d00c0e040c42c04d04400400c03002c80e03410405a1507100003100d45401200030350010494000b50400f0166031900030404a168007120b050900c002d191010040d40541014080c0c4c02d04641c003800040380c401d00d0309080317010119020b8200e9404986a210076103d40405507001e8000f0b001d0100000c1c01400c06c0581c0f5503100e0070450581710013640d100c0206440003a00e802c014a609c581d1182a240200229603000034410300340d00d0f11031201305071000070741548 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526902311 1250 526901061 526901071
    0x7031116062010060f050904080a1404050907080403031802030607050711040c091a0406050f0306041d0f011a134b091109061503040c06080618 63
    0x4204040b680032810110000e07118981000000d0354205900140b040e030003044076002d45245500d8919001c07580b03003014003c40c0d100302d510034080341c50140e81c4541510080c2c200210018800c004010120751500d503512000e00826090301d420000742403501d40a070903903042c2d43d280e0300d0b90709401d40080c000d40d6002441d15003294035401c01541c1c5808605248045c0c44007603200d83c1e0024245504c0c074002d2035000b0031640c2101d011449400100d402d03104103030720600c02c40c40348c280051400e004015007945504003c0d60050700003000090301a0504a030011049015001e001041d0081283c50b03410007000c2c02510540402c11321100381101c034520001c0c001080c100c2e10842025034405983c0642000260840e4a00c046540b1002c0f4036140d1800f101c1c81e40c141c040c43c40b00028190b400700c11041c6124015901030640c40302c0c0c5d0140071036085081c01248240203003e640e00100200b0300c0060160050010750040d0b020782050590700b0705143c000341100c04040c0003a80030300001c00303c1004403281008015040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526903561 1250 526902311 526902317
    0x6110c0a140423010f060915050a0c02040c030e100b031f11070f05010b0d0807020d020103062706050306040503030115020309060c030306040b0406050f01080402040207170703111606 80
    0xc09104008035009000c451094580c0b40c01c11000c42e41100120300c890f038100d44104281c20341311500c5190440f440f004500c00c1c0c40c0e000300044001107003140508060500074186180001405400342c001034242c848014211010942d940015000e00f0340501c049400600003880034480d0f40b81080100c1d94454a080a000101c0840100d80300002c0300c540102d0a00e401e12140710791110203906200c6640e0180c080121069841c05803284540d080000c0003407c4135810404507814802e41e078003445280c4000d14801c0f81050768980d4080303420401900408451201c1000143c08510100c01000450354240c1190380f0940c0070804201c00140000304803419100d2442c1540074800c1c024038140d2a50082180c960b03031002022408889400c4000302441c0309000c1101c041c4041c900201c01c0c0411110725029690b08a483e4110041495002c0d840c59074025202030401031800409840c0d140a40440b200042e0028800013a0f000a242d40180d2500d0f000348000c01624030030a45e9010340a00034080c1c0300c0d075024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526904811 1250 526903561 526903589
    0x1217031618081506060c250609060f050309011d031e0721050403061a1f0225050406030f170c0303130501021309060f09061a1c0f050106110c0a 63
    0x141c0c0303649007901d0f1402084800c4405c142016141011401d804c1e10b0409449141f03101e00046007031003031111400f20b81c501d8070707030700c0901580320011a40c50340020084003d540d21100c001c401d101032990030f007100b01c05007000307151152445214400240c01070402d000d0f0301a000d106c80d002103082461001c40b400c8070290446d4a0030580301007a40d4500503540054011444c2025000300b000c16040155402803048885281d4980504040170403890629002001680558000d0000c001c0d00407040c54042d01c209450724045940344000350968031075410407520440c409040d9000c0012030519460111101850381c0e080023482ea61203a070704c0c0001444007041f003040d4540541803080c01c0d0704407140108558001089151201b1800b03000c0c265501c262001c04280c130000141d0f880c101d00c20305080d1403916602c12a4544040c41410940c1c124148010b8481c408500820205225101e165600a0020400b24007503140c007501404035078841c1036503109074100c082201d149966810100f0306a5080201da158 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526906061 1250 526904811 526904821
    0xf09040902011407060209040c0309150c03140c0c0118120f0c020d050a02120307110f031f1a04022b06050a03050f06090c0102060112170316180815 65
    0x140351214000000120300000500c4d00604c900383d00244030b0080309480902030f401400104400300c1d00c0d0307050f001e070900c0c045940001080d00e03203411901044025190101b0040d40540f8484103c41c400e0780c06030ba041c0c01c005202000c5030700030300a42600b0504681d8900901d8079517100c1514252200c1040d204110310120000d01700d90081c1d01440d0425000340013a02d010f03c1030b103021383d40c401300e1070f034168400d60a0201030407050718000200c40c01e540e807003014a100c5003001c00601450031540052254580030f4540f851091170704c2100c1e1501c11a80c3d0300804644090401d00102408844000450083c0c0c0100941041a0520485142d039040c1400c0e90b034106007111a2208000d08450300046d902c085d030072100200740031000854000040041003925481d441d6029640e0f961640f803043c0314050303040000100a6216151a54002c40e4081c18050440f5547c00d10740c910654400c68203415400d48901990351560f030f011070700c8024000d107884080000b50602043d10f941d9031124030100021540703880010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526907311 1250 526906061 526906067
    0x20303011a1204030201020a020c090c070204020304170c06010f050105041d10170c1318020618060703031d01140a0b0a05060307050a120203040c2d08060702010e01020f0904090201 79
    0x5090381c0506000703840742c0c03d040c58002d000c0e520090121005214003031100d0310b0340c03820303100b541d010789010349002d4540b40d004d80c24070010303400090040d43d6100d24005800b512070b80000003000c1611010340500015810198811030600c2d4a400007410040c00f44000e000350a148200b40c4182071454401d0416a5101070300d03420400b44c140c100c90381ca543e040407205c02661000409801e0154100d540c2c0049080c0300f4101c0c001ca039141c003010010b10041c0714282015081c960300a0480c000303180c1224004090340c0d0080390641d44844011400070b59510700c0280c0d0401365114800b0b900f00300900a019030784254a980741c803070300d0113080101c03074035036906d03003001d0959030040701c0d100512004c3d04058803850011009080ca4018201c0f00010905203003020419050620840788aa5840000c8910450804004912a0155908552034600304a10041c6550f5858000d04000d16030301004141030310309a00000d007500c44044141030740d680180070313022880c1c0400060b5591800300b0b44002520358890f000403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526908561 1250 526907311 526907317
    0xb071812030818160312121806090302030d0e0703030e010815220e01060501021c090e0c0c030c1b120705122d0d0809060a15171510030201020303011a 66
    0xf4006204c141000004010341020b40c9030719030000303880e480780010b28880041d09984406000c0c1c0703d21800e406120f0001481c95110788070300ae001e44100c906000516224408860f4014035030180344e0310a8000700200b542c0441c0100d400c1400b864541c115007000c0344102403104040207420311a400540b40000206114040b50003a02140e0300184071039002200300900a222501540f401801284a4031011039041c90014280b42c8060741d039010740070302e800d06001c005140500701c0b00c8030a804001c21000c2031400c2010b400c08400c10ac019050f0f030b482043d1404c0d103104021224030b000d0300c1203a00c140c4030000701050b0002100c80541d180102126103540340c0b0700301050040d0501400080e490511215004114018042c6410030211120041824000c0d42d04403411507404010758000c1c00000d9106039940c11141c0307404508a40c11005c02e40300c0440c1401d0a40300c5600c40800e034040b1401d0100c844000704002d40007032496080101103811a00002d4032440140246030000121070b00d540a05440c1c03200b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526909811 1250 526908561 526908583
    0x100207171219111204050d0e090a0b03100906051f0b040614251704030c05040f0f020c0c01140903070506070503090306010b070b0906070504060f0c0b071812030818 72
    0x109a44c2e60000c8001a01c00c98001d40c3e05442c1440350181d65075410740505084820710074014004000da40d281c5000c1d4002e0701109110b1501801807100880c4206400d01030030380b00d10721840d40492945040040034a00138800c1d140d01114661044080000086040c11030381610524600400759090f1805801080e1040352000c5000144aa40742540d0304546070811039410321514041c0c0280c5030911000503240510700018080d0b90411400300418030b041c1d03022440b0904025004540f1240e0341c03034030f0f0302240c014202c0340d8030a4108501e0a001582e0018020440f900120300d9542851048000709a8030642c0740141c6001d00c40c005001c1040c094100140d8400b902d0050454859603142c40c0c0e54201c3d9049884c0c22594403ca01001c2407600708003107070052050285580d00350600389401021110056100380e510240905404000d0215840352122071264105448035000c2913140c90600c080404241d02c021200225802c10384c000941c054402e903080142c4520030003602507a242020b08004140b60 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526911061 1250 526909811 526909841
    0xd0f1b020a053c1003180c0803180a030b04021c083601080601180803040b03072012180603070206100807050105071211100207171219 59
    0x21481049410340410765504490141c400c0f1440c0102c440b00469070201d000c0041d4040e41000e6403d965912aa010284400d0003002d404a00c26007600c038400c2d40d44040d00503c200303400016244034580e5010451618013031094500f00c041c6403654654200b03a040140000b4480d403401102145400300760b280d5210441d400040c41680c0e80710208008405c404c1d0061214000c0c0104031641004130004007280721010302c182c407003101c0d96840070011100c400d980880000c0005805001140300e4504102400140400580d0300740d5901301400040c1441130000c00480e10003244c8003400200c1040440c400484051070110180c0390300d88603d034900800c0000d0225a0442000b0041141150740082e42c0350168401c803046004858503041c1c842d4403084103000d0310b408030750100924000220011001d003800969072038006804043e0440440c00c001002c0c00f00003429402044203000c1c0308203441407285d0600c0311241c0794903182214645070401000145141451080c4215400fa0a4515000f641e181c0c2c009072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526912311 1250 526911061 526911079
    0x602090d1b1401031406090406180b06030c0405010305031603030f0203130605090c010e01110f0610170106060c08090d0c0b130506040806060d0317010312020d0f1b020a05 75
    0x2000c1028441c4502c114406a02020700104481d4028485c3e07000c8081e200441220a503a1503041c00710307a800c081c204691080e6140da07100c80c0c41c808040c444009502c108510319503414900304040c54044203c46081c8a83e1508004000241000040700c1c0c8400007580040d07000615428183c0045c183c41c80040741a500002c1006007151141140803000342c80b40d40c04010340c4d03d60802043d40c40080e1400305011507600b003c1d40a103580584811002d000c0444210740c0340d500104039013030803c2e0341521020141c803068002406000301c03044d181c03071894143c28002c000d40c0b450f200d4003c00c0d074052890090041c2e0400140b000041e1605d01501c44407540104000c111135956048411140d400203995004800c0c00240101e100d240c11022141207480c110000d2006456003010854558088a812000e110f40e1040c0d0316407082c2e001642d21b00135401001d243c000c903000d40034040d0400e04107010603003c0051039128449120380061306105481c01c00c1281111030700b40c0d840407072403401443d0405a480171140d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526913561 1250 526912311 526912343
    0x910140301030b0109240528030803061e0d021002011409030a1b051e0304030606090923100e011808070629101e0e100e0d0602090d 58
    0x41d401c490483ea00301800b04404e0b00000c10130600c1100e0508140b50070700c6c64000c100810b1404941002100900000501311171341940e80100d0403811f103600440341040c2c081704102d0107152448524a030040000c40700d2a07820f01311030000e0030440ca00540240700340c16408004000e24404d521070040401c2d1a0f03c0c100380382c10b107954001d0381e0f504081000000502c0081e039a4480805160b017200255500c08001c0802c081d0350040300f55001044041c40d40035110600000010031924010752005107004c0d000002c8070942c508081c0044010451185404404c800c8620103441700021070805443d4500c50001c0c2200c1881111802b40aa103000c0c144001015002d0406002650f8018500144070710740400688005d8007601051020100c1003002c0c4c54682c0312051201d08203440300400c070a031646040c80e1000c003980e007043e401d4950744072894005071007084440380600b4116030650b5404642c0c140100108810b1000600c8002920802446960085070380c3c00c0c151140da010740c0c40c155008003402040c04034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526914811 1250 526913561 526913573
    0xc06070206150301060b0d090203010b060f22060f200106060503190c12020901090e010b07020307050a08030f09040608150a050a0c2a170a020f0d0203091014030103 72
    0x200b42d8040b1200d161090300900d05240c140f0960702221585511242420b41182d45c0c0c3d0000c1014410070307070f0195210701480340d580c0d85400080201445140c0e00f140ca849048032003070440c407000c040b4400c0d24612003000b80078507034015203995004501d6143c020714610300515942d050001a4403000350540c01e000b0042542034102001d1413044000c040e0b103d04034030207020108146d820100030107000c05c620307447c0031015244940080400100c10b041001c41c950341c651101034502d40c00da0003070007945d002180135800c501d42030200703000502c01240d00d80b1000742080720741d035103d102d0700310981c50741200018030b0f030345a46468220130014500c42090f54004551800c001c0300b8803404841031a01e0300e1a0000240c070800307061068107252091551590b08000c00f2040451100b502919041031920542602800040d41803a91401704501245066100c40488202910b0003440500007100b0740c0000d43c44d144240e81c00010f132078401404441c01c030501e031104002030300c0001e2524000b0084010020002c014002c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526916061 1250 526914811 526914823
    0x9010902040815070912050a051b040e010e0706051b0a06051e010803070201030c0210110c160518071e0203040f15120203060111010207050705032b05030c0c060702 72
    0x15020040e100729080c1c0c010b00945518080344d01c60080340c4801005d05c42c0701210050102e04074402d500706c6400d044a03850342440d00f504542c0b042d980c0f03030304100d00715142d0a15004603128000b40400a0014465035080691140c84038043c6104101011030740380c81c2e400c0d44140028903583c990003640c00e08402070800c00b020300411248444101d90a02c5c1e1445003031b85268145041315002c2000c0c60920394a9401100908400f8205504500c50040081c0b804a11403041c100c8450002c00b08580d02c00c01701c09a81d0508a141c00704040c4980540b4003008651201c1c3c00c094402440003541035495a06c00c5410303121003d001c5452041c0400071031300400800d80000040080e08c8030000c9079000c8503500d04025890740b09070a000380004a410454100da22103940245401c84414100300b100c04610f1300402c0e0882c0c21200c401e4072039602c83c883c1000f050806124060001442a181c081054903000e02c00c104088034050305010004000005a00d207254582543c42c40d03103000e819500d0b5410318002c001d580302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526917311 1250 526916061 526916069
    0x120d060f030524040f080a05070516060207080c21012403050615010c020d02040b1903060c0302090d17040b0c030a02070605030610030b0a0503011506080601020c0f041503020901090204 81
    0x1059200f0945480e8201c0714250340310365071120350301c401112103a8400b403464021030280000d00c541805288002001404000020807154120301005440c2150007440c2040e980d20400503500100d030360303601a40341c041f1103001e1500d00c904074079805200703650307182d00400c6202c0007424404800c000c880d1810300e602e41020112801541140c0540c3c40f200d0201c5100d84442101c2d60120784112003103001030501051200c015400203100258904506001c04e0304581092017540c40415445070610402c04584240340700b110030761504500348042900412801080000040c00b10008008840e03502c0441c50201c8002d09010406c040c1c40e548031440d02c030707030720741203403428101501a0302c401044803441181500c1c0702d1500101485440c00a0791401da00034002c051070580c115804072070205850310240120003404090700d9040503210700d006401002d002001e004181113401010282d0081d9440500948006034121800540a89502100c0040c2e89003540000d401c5022440000f81c20521540504100e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526918561 1250 526917311 526917343
    0x303040b0f0c0d1805040948050604030b09100204060c0201270b0c15100e070f0c030807210b190308030408090d0c091d030705120d060f0305 62
    0x4900c400015982c4c690304c48601c4212808120b8104524039040d0401c0300580c0c06982c212500d11800904946082d1041030340c103a1407800c0e0300082c41b1024020614035001c48040321207081d500e05110009505105174480a004101032602140c0b0fa01000d200701102c0302d0078014115900e0f66030703a901030181a4444003ea0102da00d4580c6920000780494a0701100c4c2c2c00c0519100310242005410710b011303080b6143d03003131a41c425000d0116064881e03072a180c0c001c110340f810403400710b0707d03122601681010081c800402c10580c49400711510b034111182180103680f504003030005070384001003102e08840c01c81c5048001c11510079008030000855101c1040c0240a450a026000620340083d003a13030b01c24440100408020000907011410f001c0241c084020014843e8813120416100e0310f00d060000d4124068441d5102030900000550840094000101030040c41c01c06181d502c81a0711004581055032400200203040c0d54404038aa021130040c00004004402a54481c01c18030b0760340c450301c0311000030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526919811 1250 526918561 526918573
    0xa030b31050c0a0b13060f02030408071211030d081302011b03120b010c0206071205120c1c1806050402011101020a050c07060504081903230a030f02180d020303040b0f0c 74
    0x40550913021a80c05240c0a581512814500082102c40c0c2d40014410030450209010104502500f03003c0702c2c000300051280314041c046582440d00314403680b45252880b950041980801c00d42e0046c0c42103a001e003010a80d01c2d100506400161420480012451440a80c42d0800340801d074001c19045882a03003404200a6403090348015162005110000307580101e0a00410f000103035442002c81424002c1d01c0c09a0500c031010003086407451055911011000010034004c074420789007221200072402c6290140408006c824020f00b00c011031420180029880e000004c0659000310950b01b109403428000f1562028080d10040c01a000001e0348003650044c800001291481041903d095800c4080903108140710001c2601484091700c1c402c41c2444601794403502a595031440c0034440d88001208244d441c0280c00e0010100da2150928086c41803040c00404002e40b000c019413000c10809175101030360203681c2d00009181d401194010840c103000041c0754808201d400c0040c202001c40c0394120f540c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526921061 1250 526919811 526919819
    0x90f12020f070812040b0304050c04061205010e030a120903030b100c0c0506031b0a09050307120302011d1902040b0316050a0e0c0a0c080d060b0a09050a030b31050c0a 73
    0x24031051303006902e02003441c1c1130205201e41186000107507000707841203049490500600b4080380a172249540051040c80f038140500e02405000c1c06482c410703801190240d45454030454000d003003802c140d100395100640c3c4503e4442018001c0d4001c40010030010186000c4400c4031030001c24650702a082119003111050001489017458170941740582582c135403100044141140d6141c0ca500018440e00400c5481039001501361028080d80001d03012000c60b0004503c041d040103400d40c0c0041c20b000038095051491013005000100303618034443d45034041d403070011026000180140c00413105480d41030080c540c840e04503180741054081251010b07241e480600396100914070f4000821660405034210402030042010f11802036110340c284503410707007410450390f828945e0843c0c800c0c0d000715008800005200f505aa00900c1c240003d02040b10401c4166003140c0c0c9a04170f465000c0d1945044101c2ca144020580c541c0ba440d0101982440150a40a040d1800c010383c0d01c2c12845c280c54041c032003100d0085 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526922311 1250 526921061 526921063
    0x207060f02040f0506120403081b0f1e070f020105130918050f0a0807111f090e0a020a0507060b22020a080a06080c010e2101050402030c090613090f12020f0708 70
    0x40d074024500b0076010450387d207a450642e041c000c01083c40d025003046960000d1400b4090010b42105650006d000d612140461445104000f4038502145252818071500001600074810b4045040d428038149440d40c00303090002401202a4121004107820314a0740030312150140000c509081c01581151000c08a45007019207039a08007034040e0194800304200400700f0070b040304038100c505028000101c64240d04582e01d88130744186428a0000303070028000c0203240c50480781c0b01c2d04000c040100f145000c40c40b44c000380c114401c3c9500142083e071103286003485659588180c018102941e491040000803441d00d14000390b21060040b800309a034040800c0c243e104c0d0b445180c06603135102d4000d1040e00500c400654525181391209944074000481c42d2180c040d150880c214110380080010800f030a0501c1050304002c035111a00b4044c107810010840c0c0ba03500c80b100d405401c040007000150059131410100e58205084501070004844010b954142355800a840040e0098000c140d44034541c40320181 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526923561 1250 526922311 526922317
    0x130f0c08011d060a15020a0b0702062707030c032a05090a09050a02100207031511090126040b04030e12030d0b01030b0414010608010806070804080d0207060f02040f0506 74
    0x945000b80080900c8000c0d0840e0020003504900020440c004d00340d030f2408001790180d50100040010b0b040780700154100030694030a542c0001c014000b80c0303a1803420111484429180c00d07141c01038040e41c8110b0411820701408644041c607041100070410980b81d04000e0034105210000f001c0000707800d1548aa00743d02700041809032a002454031000d9101c0203240d01c050030b2441170a6400d805000000001a512808454130311409500641941c0340b66042038101c4501e9000b0000515040480000c0c1c4044600116001c0c40380c2401c0c640c1e600001070b005685668144002190030440040034001031000c0340e003129220300e00c00c1d5280c002e00c0000c10144610b614040345641c2d0250b1003840500034102668021a5041070103140000340c0c00c602c80e000400341c51040d280740d9000c040c43d40041c80700b940d00c00d4011740500343d030341700400f0142040300e001030010000800240c181d0b207011a9030484034009804440301141c01c59010700c2001d20b03100b00e010095025101c1c80314250740c0c1b40c4d00060f81d0704022050b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526924811 1250 526923561 526923569
    0x9050103020a0311010e090f0711010902090f1003050d0201051602030c1005150301020d050105030c030d1b0c091b0e0a0b0906030903070c03050c09010f1401110705130f0c0801 77
    0x200d441c0034950f0351481040c0413109038950500c4214030714104585c44c0e0400a0340303d4403170021601400d051075000680300c0324040140e00c8150b4101250ba901607128051066003040130081c0c0e40669a9407000d1400803c40542c000800c5400380e1090040c50690541005000b0302c180c030034101c00d5608850040c0c0c0e503441968041c0b9225000204000b5403c031245d4003ca42c0880c40030301c0d003050b1801142c0080d08a0f03100c6941d58040341c0d60f45c4018030441c1002c209554038498190001c241e078040e1030a010385035a4803c0e03080050482070b494400108030318500fa04000b007400240c140607040c404210700e2411440c0d80541f0000070801c00c040300f100e1404524100894440492007460440b094050203e5540001e0500403941310030410000055a1003086100960007800901038003110001000140b080603030104140d280c501005000012040c8a0140030140034200304030078140700a222820002c56a1026521000e842913110030740b00741da08404500d009601c000c025482802d207060300c001c00f0a000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526926061 1250 526924811 526924819
    0x60a111c0f021605070f1e21020402040e090d0203040f060c0f0b040803040624050402070f060c02100509030f2a01060909110a18020d1d010e06010905010302 69
    0x200030000324540d1003008003201c030300c0c00546000c0c2502c404904841080c4012141d56000c50001c01ca03166605840302c0c0903203c01d02004140707070850602d540b82440c040c02180710144410300d045440480c440e4001d06120341c085e205544455030b4004076180f5100c100d4620340a40642c25180090920200c111420b03521007480401000d42001c0040b5015801c203102104c030b00e1041c000f00801b1403040c1c00080e110b03a20580c0100d0766447c052030b248098400000030b5066071004c5c13507000705d03412134995425030581308251401a110341490800c480c084140301c4000e8000fa10b88464058401d0303020407050104650090180040c5e01d50709621a80e0744500480031071051410700c005008415a811000d0602e0506111207020b4604170701d615003102d9055101c50203031552100b0840c1001910300302d40420020441d000c220040c60980800c101d11700013010700307900c0da90009150315010704a03440348804103980c00d600c00a008504003954000c04c0c800b001a809885001c0000807462518000e090503a54094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526927311 1250 526926061 526926097
    0x22020604090905030f28050a0903030e180f0702010b0901080a02060a020a061a010e01020f060c03090f1c320f0408011a090c04211403030405060a11 65
    0x425a038002e01c1c020008580704d000400c01140d020301c4580144c82c24991031410400700346050300b501c0d228481c95004031014080c2c14000660840d4005210004036034040c141807441503e00340002c0c1d42c00310541c1390308011411000a11440d9010900070501c10b00c085d8000b0019001c00000f04070200e01c092040e608a83d00007403240300181440070241c0304400148c0101d500104150781c7e2402a40d4011404161110849518640d00e40e4801c8400d02503070401e0002d44102407034119801d86513200100303520320990b8000049403125504021860307010001c007050725801c201d4200c40080d05903c15030207000046104d5035098560604208903248202c0700200c00b07500d00182801000d00b500103010070100c1610078440060140800e01880040040d0700801720040c0e101c0f6800c210803e41c0180c41855907840611050115101c0e000018188ec040081003085003c0e03d8503103050b8400024180c007100303010120500c001c1105c0002c0160151030b621606200c1c103010844120b2881c0a0300881c20318000d802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526928561 1250 526927311 526927319
    0xa09020d06020a110d0309020a050411181201020c070e0a05010e071107030c0b09120d021f06120b01031101030507050a0503070c051c08060609030c01111603060522020604 75
    0x140d0040010f04058100754030020f560b544002d0915a401c480b2201203a1075501c41421482c00c01d84100c0580806c64040102600342140e408942c06050040c01e201001400c8402482c0e4410708030341c00165108000b5913447c200e1298690b210b0286109006034030f100000841d002c040075008860507034080300390701c548030b54902e102100c06500529100d0700354017a1f803001002041800820740c0140600e082c2c03180da15100f050a008456481800164854104001c40c0740c0c1d00b40d0100d40034010501705020060001100700d031020040200e60301c0701d8583d40e2020441001c0001c103125050489000d0000e885072503010b840150b0907540115400702c00903104000d0f000d02580910041d503009052464400845c0c1880e030ba5a61904038083c808c81d00460b010042c2c00110703948840d14551004081c1c070124101a0484003107656a82541803c0d810b116590403002024107040014005402c08401ca02e1145903a90825000078076059404109071410b0002103480c4400501c024440280d001e080300e0301d01890 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526929811 1250 526928561 526928573
    0x9010e060717040312020f0706080610050f04090c12020703080612010e0106030503031f0e0403050a051201150e060307080a0213032108090d08011401030906090303090b0a09020d 78
    0x40104115000e00d40b00070103034000080807001d00003440c402e82510801c003000f000c5c042c1c60030340210a000c010ba030148906000103940100d200760012410348904c40402001c001c11785050040d2500144002004640000c0840064211902203e9551151148070340000c0c0d0220580c41003620150124200001040190815160700004464410000103250105048050955140703520594642c0e101105010402c95203a03440420014000b284041e0305150a11900081c000140003400703000000c120ba11006006408648822440c001d03803602640e12000340403440708040f09a400005d99030141002c0f90700704101220701810b0140c8030b5144c50380e9003540000281d400480c10f1100d00458100c000300148000180051900c40501000048400084001e14a640081100480d42e010313401091000e07030807400d624151908581d031071480000800042c0d001c0d048441005148902d0000d80c0814103505038001000e00c0e11902404140e40c9410042d00140e400c65940a54846039080c140000030764 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526931061 1250 526929811 526929817
    0x80303060f040f15060e0409021509280305010501270c091a120f0115050901031e1d03031009090f020901080f071505030402011808030406030c11010209010e06 70
    0x41d0003000070424950a0f81484169000600740700c0b1644007030a400c4c016142c00500b00d000500c0c09560400240d2130307070340000f0340629182008020841000541c00401c0c1c40d035801c01030b107010340c000d2030355501c9030101881c40c00b02605100a07141c40d4030740b07000850303070019080760f03c6c0c4d48903940b404d9115894902d1030b00344014040f80c46800b082c0008a00005515144400d140388094084a0110340300c0b00032090000c203c3c80020405440a00d181e001031250300c1401d0820700640917036240039078a43d030350540141c0081c40044d84009140c4106000621b10909980000140c0b650f0700d543c1c110725509022455507240002e9a14003c02000324106010085c800d50040712041e001d0044c1c14042486138010414012081e08143d400340c2081010780b2855008000d16002408400003080c10405400d400425500002e00300030b0410288020310004468800c1403800070780040d070103981d543c60b610a03015005018494400d00407a00c1e60801e103c00706418404c0e9202d100e07040c2c658100c1d034a403810170030003198 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526932311 1250 526931061 526931089
    0x207020a06050c010e1b1207050303030f04050304090216050d0c030203091e0405040c0e010b070206071212050f1b030618070c080c060a18020f010305151818030408030306 75
    0x90742e0307480c4418054004200c4003080032091121141c06d00645814400341c010600c0b8082e15070b80c030010342000fa50310000112076002e924000100d030703641c079140b0700341e821032003650b01003030b5800e0010801d490001034120410406921407812140160040c5101b03072100c0c5428000a800b40c1c0050081242c80d0401c142c3c3c6110f448103c2010380c030380000c040b00240803642d0a1780e05480480120a081c07145482110825015160601c0c1d014209a0680d000412500c250340005000c00b0820f02c0080f1024010394003c17021031804041488589000c080088062000b10780003520080c1030044140943e1031102140e0141e4800307010781c0d0780d109003072140c0c00c0140d030060485420011110300c42c4020501da040504400041b017405040242802c2120205541401441c890064a00c03000d100040c1d03540090400d02c0c440030308002c100d655030344082004460042c2011900000c04110100e603c1000c000030f98072611944404498900c07030b0403080b56503070180f4000c540007644100302180891502c00700582c1c000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526933561 1250 526932311 526932313
    0x60117071a03160504080318060c010504110a050105120a0203061207080708100c300e0709050a0c08040b060f150a030b0102011802062206120b03010207020a06050c 72
    0x2440d501c080046036810720140116000c4004400c0c0151501052250f015001040c40c0031400c083c1481c400d11b889201d87c2e640080e1000c4000139240580d2512026180641d140c84005c004a2416060110b1480c2c42c10707003841e10a14040300042011340c006e0050340c07042100c0c01102c502c0e0340d41d4030045900039400600388075405010941c0300c582c0e074103041003244054007015016010741c51038030b508213243c07691100410a9403802e142295009a81c4400505e4044e541d4002c400b070200f0a1403a20f450070b5621040741032003e41001e40b0103c0540700003540200b150f084590800103130b50390075615411940c3c0c0c1405940007607405404140403c40800d003294218000a14051500d181400050040b10141c0c0700c8015090f03001c1006c0404070707051311075481203c1c002e000910680c81240600e1468405060000b4481d04001c65880c1c020b01d0010607000e580b100d105049414113413a100007a0080395081443c40016040642400300350606000f03441003e070303000e070000f002181401c4054809070005070141c101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526934811 1250 526933561 526933573
    0x10302192105131e08031303090f0f0501080f042102030f0a0f230a1809090501090203062503020f0c0105012c091c0522170a05060117 59
    0x1c004461041e14051550f1408442c5038840500c2c00c070702290b40b84d03841c0c6498004a05400004204004100c0703a01504046455405140500e01a6090519a086904041100f450110380458101240c1081d650244c849000c03564421603c103d4a84044400512005141c0a002c0c94481d061a071001c81140328015a410245035042c1c011840d00421100e000040c4001c80340c00d200c907044900ea194410305040318440480d0300c0b070b081407050700c00c43c500f6904104001c0a00303a880d52140400002410b02d40c0f03002c1c80a5400c605249000c1c01002e1000d900c6030003a200070a208103012909201080c0c6558074052803c0c101c00c10540080d00f001d90a21003000f4100b00d014510802881014003800c02e0022002c2c61a5120100081103e1444d4010f40700c8146201889040000010904c544030003070b02d02801210700d561000c546034050100103118181c298420001014250020340d02a102c0602043c80529020070003146c1c0c88585000190007a000400184040f1161106510003011040c045801c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526936061 1250 526934811 526934867
    0x20f0718110f0307050405040b0d0308060108090a050f03031005030f1b01032c0607050a090510050903060106031407260601030b211228140d051501030219 68
    0x2c00c40d030044401500081300020300b0300141c500340c0300319030800005541119118181e6503000c0d021070030140110741484080e83c0003032400c2a00304000f500096002c41610520946546001d54075001a00c0100d07600100d000c02256a007000288518070300140b8000303088404804800e40d0fa0340e1412100c560425454140484052810030f03540c2c2500103840d14107084807980050a2401c01e24042d010318200304d0704000d00076201c2e84c0808030030156001120441c405000c082800d903028410480a00c0d05401080000246140c051f4800c5410346403003072a031151952103440403a1010202e100d03080c00c841c081903c1d03d4076a60b00e01c1201d544a0410704000031448007a01c000380c440c0018469034070f0700c510380085803c0440d800344a0490040748144507281040c1c2ca010306507000400c00303050503480d1555842d0300030b9001e01c20308143e003011140c10540b5517035154460340d0f180540000c8440c880e04601038995504254441c1c4212044010000d41d42082148400811030b000c42d2072082807044e00e002c030000c1721 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526937311 1250 526936061 526936087
    0x1e0905090103030c0c06022a060c1903020c010206040305070b090708160f0506090901030f150203010f1d100b07170d09021809070909021908060601020f071811 70
    0xc0c0618000c2c0c50702100113403180b4151400c0f45054205c6811500007160401c42030306008049001c241c5c3d1058082a42d030810700102c1d2003401154294500c0348074940600000c06990340001c0c2481d03009030f099440c220010340059076940c405860040015004101c2240030030122090a9003044003041644c2809583e290507a140209218002200034140c44003004406000b401000c02014140c0301a0300307007000715000034041c1c9014031002d000d0050f4142c1c640104130580e08800d81902d41c007601103450b0750b100c103809940c1818501400021a03000da5071200042c0900d01d0141c820013481401c12000c03418151440440d03089203c080f548038008d400107a211041c0e01c1c0240c07440803a0200c0004241120303004002802da00f60280c100140c030f032070342070003541e41c0080b52000603a4030b50140452104501e10110b100b11460014401c07002c8045227011807001d20200f4107038007400d0260300311071b44018075000c1c990f03e42415110310046040743c2a80401c204400390801d010784040406aa0b00303000c0710300303104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526938561 1250 526937311 526937329
    0x2120f010501080f0f120a051e03150103020306031e03070f060f060f0f090902061209010903080a0b030c0f01030915021c05091f0e0102040b0d0f0c1e0905 68
    0x11020a0351a90018440000100003980704d4030003000c010328060701c0754841141c88940a0000911905001500005881c002c908a600c100203440000b42d070408041c142400d80e8100343d800c20f8003820024a000d80d25846402600d0041200402500502002c50000410115900766a810034081440700c0700116107480301003100c49000b83d0012411941e024080c1d000c40c1c890f500324050780e84c3c0c020024407007070f684c420300c3c4001d030b650000000524591b9400091901d020381d500a003440350340b03142000075852064001e0102248a5107070300200d07454054082060300d8404040a41690000c04c2d8214145014002d00004400604000640e480103441d0014032050044428002c2d0350001050171400600300c01c1c003045513003e4001000a0308000725a0f540b6641040d402c1442941300311a001c0c084070081d4003042c0742196020003156110ba40d90f0b00d41d400b41d0001440d01480324945201d400c66818940140d46501026030707074001d2000032040216840f070516102c03c0040100542006c10940c0704c074510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526939811 1250 526938561 526938583
    0x20c0f04022a0c1302031b070f150b0402071101020c060f1e0712020601290a0e041407020c15090a03080a02151e1b03061017010e04050f070806130212 66
    0x1015a41c0c2c5000c11f0100b491080921207401160010802080800c01124061424031b50044201c1c42c01100d41d01a100035191034000b03603510a1000a072041000f00245801094100a03029507011920003010001c45010320040081400401c1001e0010940800b240c070855030a018611810201a40c4035190b6000b600d120410140c0d0000c401403003045146e071106040da480c64484000401c2c0b10a25400b002d0044100c000d0038030003c002080b490340d580d50811600d0383c42207111381e4030624004100a6075040102643c41c000c1d42070140c19074013807403810121000b5441c06480c450426195650300300103544800d00700170440c06a40d10a001803114408954000c1034503011920003211092106800850040e103e0408807204000c01400e41511401faa40d00c04011240440300d40c04005068401456644014032030807921400411509081c0c0b449601480c0680210740100000c12501c41c0d9030809400f80c46610751000c8006040040c11840c2080309620180814099100d0b2901c100d25007580889 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526941061 1250 526939811 526939849
    0x2040303090905091b1810050103110c060f061203030103200102010213051201060f121403030f01050f060d05091e0a08070605071e020c0f04022a0c 65
    0x5080003415804070048010340400502003045090025089580e054000c0b08400c44482c0c0b0f01055801e41e582001c0c5910076500001030000034501046c01c08801800c078000c05000c00d280502c501c41c04042c2c0002d0740c0c1d0408404000b07061b02e0301c6545d44840d10042c0180a540d11840350381004000007000e00103103001750702c600700207602d40403c5503e00c0d101800504103c0d04580c41031220030701c80c40c001d14244007190401c0d07980752140044000841d0151943d900b11008400c880d100c0050011168201058428090807130350a1600c000807440340ca07484203451104680540300c0050115180000b150080080010219440c0405944e017003000d40d00c04840c06171040e005000b001503408030011400030f86540e400080e08001c1503075503680706207028407400139003031b25950400590110700608a168014182020100c000a808100290f4a000c0844041c0c043c04c0004240c0c3ca040c01c0600a443c044030310242d090419230240344414503000000816418184600c2400c100e56403994503a5548503a500d0b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526942311 1250 526941061 526941067
    0x13120f030906080903030f1b040e061f05030c3601091a0f0d02070605010b0d0c0503070807050706111b060c09010f1b1a040303150510050c0312090102 66
    0x304001d4110803140c0d000c14284052031007040801e9001004a0f1343c07003045405840044d449501c2050100e010044c48128034402c005004200d000c110b103180f9100740c404980320300107800f80002641440d2550b51403c0c011070401d20200b1b000c00480005000c0110395542d81030345000404240c14100390400c130350286440c00041c0c0325080c550388400c001d4047c00c10f60041081410300d00c1d110300d40510420342d02035065040454040280580360301181c1216801910a11940d42c455013840c40f95071100a103031446614110300508890702a00030b40e482070007a5241e10090303940c1e4013400d68280c1c0c8207403c1290b10300d544030301d2251813508032005041000c0410684c48010880c0304040c9150580c007070480c0c907007250107000390b001e181e90100081115820b01e150101d408040c031070500721346614610f4010440c2500c04048070b00404034041e0365103d01c0c0a5941804220030b01c6a00c454001c005002e8542c10002d900c06c2c0444130343c00341004003000a5410105c0340781506800c041222040195081240381e5000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526943561 1250 526942311 526942313
    0x20f07030f1206140906010f080106180f082a091b1201140a0b0c0c0118080316110906090109020a020304170f0d090609030b071101140f07091a13120f 66
    0x20107245520200c01e007232901ca0710303c032580c01a100103c1481514100031000c001603c06200c443c0041001b00b809028101105840711038070703a26a40c1c09050112864080b0351000d072440e00240c1c044440c0340028242c0c503221348030040e9208041102c211105109941080841a284114581c0f513000b03216407003054821002c62400c004e1002c3d0030f5884290381100a01072b43d0822000462031150351442400c003190603140d1040c048505441641c010455400082118100301c0b490280300c4144900c118528181c00481004208640d101501ca10b034011880c2c80051056010f00d500a10404056004503800c0030f0b80e13041b2282e220b02403c102c0c500c0d41d42140c010181c0152081100f900c2140090609141050400400030000c0e0303443e00c0b02400b00070b1850041040d00c1c1c01200d81400c00c0361440024000e50004000388071080c401170714100800c2e200800060b15040c03080c00b890742965600b000d03c6004035203112810700c098016520201c03031171400c170a001440c20403190950040911614603c5442001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526944811 1250 526943561 526943569
    0xa0f2901020c041a10031b0c0606090e0a0b04110d0c15021911060d050a020715050603030909041b030308010f06080103120c110603010f05090109020f07030f120614 72
    0x203078410b250043d4148441c4504040300d4540c009140381e0180d40b50782c6103540003403085002d0070f81c40910071020b141d000340b6011015440010381684a0040e507090101c107990302d80c40030032201e4110207902e442e0810b0200e200003400e41108141c00078014980f80c0b4001030010300089005900341c0c012038140f4a4445c00300502d19203107003044c420340354600141207244003110741c103984c200c2e1030322000749070b0714041d18589503a03900c2c0d40030f0720542e80340035100704480c1c070300343c0700c0d02c402980702e54026144d01400241842e848846030183c1441401b0180103541800700036002d0040e2401701a02c00c85441c4800906c025241c03480d006403900942c0aa0380c1c21505524182c42c11f103444140e07401c02d0040019100c014008075909141c0c01214042ca0f29200b00c440308641042c4c602400510724040c0d0013840000000b070603650840302e042c261482120040c842c0c1c1d036106100380072031144009800b2024018808a804030303001d5170030300d6400714030f0341040e0025044080d03001007140c08581204240303400c000c500c1000e50070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526946061 1250 526944811 526944823
    0x1e03070e04060815100602071205011b110c04270204060503150423060f07030b0d1b0602030717030c04032406061803110102031b03120708040b0a0f290102 68
    0xc013400c24007178243c2401d400a4603038500d8040c41c0b0364031101c107030701601f0400250310548030284814044226002c1c5400001c20704100c8a0b45c00b041d0f0320071806007104a00e400d106001040c103032103845001c1c56002000e000f01c0300b01e581006030307401995540b0014032a2014011607500541c07031b03c08190145010f1510300d0a01c0b48111480010f145194425000080001403540d040101d814a070101e554071194101c0150041014079030b0455030801d442000c102c011101d400c00300e5000425503403803d480700740890f5640643c21004e05090540c05419415007501070017150000d000d000400c9c585900d079102c6400d101d030300d102c03920070460004040b400010440d10078503004d482c0358900241c55206560750b0401c0c243c40b5000c060914509007411000c1a070080048520042206042d03414507500740741d80d85e86a804c01c01c07000c03808004072400246454030075130300c00344155840100e8040c561030702c010100040111146241c1655070700d13a045030270b4294802039024046010b2070090305848865000a003005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526947311 1250 526946061 526946071
    0x20f07260f030c070f0f03081015142508031902070206030f060319030203130501020c130c03090609060c0f0305060a0302011103040b2d1e03070e04060815 68
    0x1041c4058016102500110307034024202921035a03d800b00da007022200071013044001800268140b0410041680000c40c03548944004090011002d9541c0342044032992090b10407030000700508050510203580301c02030170484a003610011940103020248a0354900000e400b42e42d880c501004001c100c5440039594849042101407e60906060740e012506030f01014101c40780c1c60804000040386500c0411210311441e01070041002c0e840e0395801c029403294414207440f0702804050602003110750001500314003805000d001e404031251034404c0c580091528880c030004041e180c44481000c5040c0d8000c11509900440340000c0c5100500070160940181c148106e080c103091204100140e0354044000046940a0800c0360645030013201003404d41c415a000789190350310100f9251000014020424409907150000038000f4001d41081c20b003038000c180150700124542e107d0000c0d400c0e1028003842c3c1110f80e80c1401c00d00b0508d2200001c058405a4008404d00d0b4020412052202d0700429007070741103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526948561 1250 526947311 526947383
    0x1611100c1d010903121b05100902040506040504080301060c1b06031b020c21150f0103031b05070b090102010e0a06020306041103060f061c0930081603020f07 69
    0x30504c0c1d03544031816072130b002c141c03481482198034000d6041c21840200da0102c036800000e40f4490b219484150000308107019090340154906400101c0c42d0800d44550b43c000c0d034100e0b000c541141e280c007200320313603518254208070b403420800c07182c00b0403e10000000c54041c200c02d440c0480d190300d002c0b030b00c4140d03010048100000c41d40001d822400700c0d12074005c8000b001c440502d180200020380e0300014501540001010301c130124800030440601060a4120b050f28070940d52048030003803882042000d2909000c0191150b0005501004150150780c000c016044040c00040366001080c41c440d802c10000314415159290000b042210520f842d2044c41c008500c0a403400c0c4c03c60401c5800300d600405e0038660a4011800000d40c64220342007030700100a10b211680c070501000c0220719000400b41241040c00f550340c820069003095184500c00074041c0c1d2441aa42c660056541f0701500480c81c110070405000d02d5402c02c111450041004000c1009901601c0000d15810010351000840e1021400a00031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526949811 1250 526948561 526948577
    0xf06210b0a051302040302090a150e01080606060d06080a0b04060b060a09120f140c030d0c1203110c070608060307080a0206031504060f03060c0807081611100c1d01 72
    0x40c9a546150341c1099074002e65803010300c41d00c110400002441170390006035200e030001301004004106504101c500c111396420f004c0c150b5903580c0b104034107501d0a01505007141c0010000a078642051030241500380310703500c400b003003040d41d9050003400c4c1070405405907503c40350041040140a2203001d40c2884400a030390722450f0040150005041c45c049024503200400070700100424800340c1801110b541c0d0300000d07030b1100036528988035075a800d00006d405000380107081e00000e03042d0180440d00ca00b650807400f5903a03140c40c11030040307009106070300342e51075803070018016024404010071203140034090a480b1500c00c1d087c0b440802d440c150aa034040456540a42e01050041e01c0328400d90360801760110724000c0f0480400300181c050070043c0c05c0450016440000017050140a4000c3c05d00102942c5070420503440302802100c0491040b0398035a60001003090460045214160001003044d14400340c414400c1c00351a060103680d80c0d0034500000400c034240c01c08903074241140e54106040d00742440b180f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526951061 1250 526949811 526949831
    0xc1008090c0402031e090a15060506030103060216170702090115020319020f010906021207080f01140409021c21021b060d09030201060620031803070f0621 68
    0x2540d41d9840000078000c40d00440400c2d10303000242d00440804268500302c00052905036003460b510310341043d041e580d081a00c05448100051442480160f8102901031440c0d80c2c03d40e2a141302a50040149001007408030030f1303910124580100424a541c1500545a605c3d02a4010811803180603013049a40114a0301010001c0b1380020403130714503040f918842c3c488103900080a03810030582c2c450008840d400c004e1a481040125030013021260001160400a80c480543c11070b1440012103002500b030700150010300c0f42c03040c412951400d00100800101c0c1c440c1081d4042001002460311a41d01070066400c40020004000098010140b000d14401d1049402041c020350f41c841107092a0050030405607542043d0701c03202d04480e030309515000700b404000c14034613000307008002600c180e40000310343c41d28491040c14000101420107000074015800c12001140c600031291000e00059032620910b100060042d0450354068003d19290311030803030f580034003d80c0e003a2070b0141442d0390070030740d10340a0b07600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526952311 1250 526951061 526951063
    0xb0406090b060712140d05010906060309030c03121d07050307050607080a08060f030a050705030f1212070314090a050c0111061519170c01050a050d05040204110c0c100809 75
    0x280901d4025a500586004c042030549a510460f0000000c0140020302c08280300140e410080c1201c10307000040006036942d580c11401c844181e64000e0000e50680e1140d00428810591031400a0b00414001580f107a0b000191038007004080c0c0c0c0003060740184404110b1458240181c40090109840d0180350050300c0c2d941d040740d48111001603083c014180007060503030312103250f070329140e62000c0d0480d424140142045a901c0266100340c501c40d1080c510303201e4031000e000c141c486205140240403070a24480e20082c00720020000d0282082654034104602d08100880350340e40a42003040140c450300c1d01074206681000000754040b814010354210805003210005038070b550020018030383c440100503020003c1e030803100b9880301d030b081814100c0d004034514400544035030046d010b0000300c48894440e40c0055646018158600c13002c01e030144045180000d40d80c200680c07040c401040007030706040075500d4005680295603048025801008010443c0c10b103504d400c0c50291103402c1001e07051074101d17802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526953561 1250 526952311 526952317
    0x1121b020f1501050a0b030c041208030f0c0a140c011b08071407080f0307121a1c030e0d0807051603021e0a0501030906021908040b10150311070203100b0406090b06 72
    0x26000c51b40300100040800c41d5a609503405440d03181600940114181440c0d1842c3c3c005079014801d00c20000701060f0322020f14000c85803c00e00584902d042110710300c0c80c50707102c0e0b0417511000031955207441c0e50050498042001503404949a191a40e450070b007503000400320190b404204405285c10030480b8086550041620346841c100c0342890780c2c96441e0441100e005d9840b16124511608003045440c0d0800d81103a0541c100308142d42c4803260f207264400b00010110540700160201702d140244401d9800c003284440d0019009440d4145009810380c0e50f40d142200550103140082c00884c024811868410b00d040f2190884048141200306608005800802c0920810b81890755070100d880030419540c05072404592400400030040028400190038403008079002c642010b200400100b107502481065000d035512030b03075120b140c4260707070506a00130301c0003101c0295618020320a9070010384c0d040041c6007905a10041c003040340d0b5101e2042c0030a0300c0c210b41103c3c020605100008a0a0b240c00d400d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526954811 1250 526953561 526953569
    0x1201091a0409020103150b0a030b010503130f0203160b1347040308091203040609060804080403120c050c040c020c0d1704030809010e0f060901121b020f1501050a 71
    0x700140c0aa207502c0141d00514010640c07a00650415400251440c40c2e60060415140b40c0d4034240441c55052004446501c401c031030a4640a5880d042d06d80818211752200d0b182c01d1019048515808100e560584918450341c85660b4140300090b00d0601c0380444404080204000e04102c07401c4403028030143c07804030a0b50705222a0000d42030515000f42d291245c440030000003a010a075496031a03042140300c0e030b0322600e5450b0003806800805440ca05002080f901280d06a9803100a51403d10800326043c0801500c2a82ca1075010302011003c0f41d590006440208415124484801074501e0440d061401d1401d19910072854014160708007500401c00c0c1a5850084510784e165a160380303460000303400562401255004045400720821800c0700041c401c80e1400d0700c41d00900c24031030041010b1001c04140043c1c00210501c105040c0354003888070803050100041000c41c0400650758050600c82c440c22116005902c0f000c000c00360b42d5818070606440c01101514400998141000700e0304082051007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526956061 1250 526954811 526954819
    0x1503050d1202040506040e01050a0e10060f12050109050907050301020406120e190f06181208190c02030706050c0306100c17030a0f14091228051201091a 67
    0xa801c1030041a4115400360500400613900c46031203a14030307018000f00340900d03070042c3c41e40e56001c142201d0600c00c1600c03548000d030080082e075042090454103c0d280c4001e1405006031016038080c48000b034010103002c1c20044e44000703111f00d08400c0061500300c0b81d80c007017406a44100024071000c1c0d8844980395100400c0c40c00840d0041074038110070701d06102108a100351000080c0c0b83c1c41005000320008401e40d000c2d02061090760b8000c030000002007540180101040501900d55100e10300459009600016040300250415641100f240982d01d48508110050b000024420300f08005481078a8000e4052041ca9041d442d060012429041c9080a01410f0006c3d40fa4910100918a6110030903822203042e2903480b400c1c0003c52a014011602c28448490b09161681340501c00e00c100562140c42c0242c010140c01901250b082d10542c8004038017a041c540c0340868480460814551200f04d2105598140ea590500c6520b030903008010303000b64016a08041401c00b14400303036440d01100352401c80d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526957311 1250 526956061 526956077
    0xf0b0907030b12070603020c0d0f08010515090a080303061e0a0e0c0c25080606010801291206010818070b0d0b210115052803021c0302011503050d 64
    0x10b00280c2414145606407100d807003811008252664140c01a20711000110102c0758001c000c0f0748107440c9007030b0300300c9000006801c000c01041030b4900000c1210080022a00071032600a050000c900e0303144154000e6a415803002045c000107007040301100030b540c1d1807103c1c1c29850754172100016004106612498844c3d041d424085100d0070f1048048449186001084450407030100c011400c041d0044640141c001012850000711820003140e041d11515050f0768900c040c0e800c01900c0544109400003154400b40c9445140304c86858034001480c04c180a020740305803c0c50712500050003518002e0418641c500724011f8210035210004404007030300c40110140d5250082140411f0003800404001035002c22001c01d2030a1140d400740110350440b60b03080c024449a003040e66401d40e080c03000d1041c0c0c3e400800c1405940310419002c5512800102e86810041385980c1c0c0350002501c801d082015141c49115400003201015024404c0c1040480c070b540c01711032401e1440c2c0700c9680f00e2480d03440b40000d105c0c0d49 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526958561 1250 526957311 526957331
    0x60105042706022a070e090d030e01061208070b06030c090c0f160f020901080606011d0a05030102071b081f0515090a020408011416050705010225060f0b090703 70
    0xe074060f04c0b04440d880c40042414180200d8a0307000c0301c41c464407480b0b140a9464089042d80d0f41c200d040c5d03c25051500200101c90310041700310f0050001180c0607409558580f0013040386101d00d4000b20a560041d80c049071a0519418190060040903104520940c001140e42040e500c9030600c10754801d1942800c03a03281d512001d9030b10300038032540001c3c41260b41560160340800140c1080d09842c14020345074100c03240e880340303034141c2d4550064a042c0d000c11102d001111a800008121508804c0047d00b00d8154994a5001c41c1c00e903001a44222150400070080e84400301c14112041300801089006001c0801c210142542007400f00e00c4465060342c90703c00207a900c0c007101031110001c0300040e0050000b49050701c002c1c40250043d01588400d035080088045804401c0d10700c06001310803c081f505071241d0081c80686d4607a000050440700f0b95020310803c40504040e00c0e8501c0c03244203203e5030300044030840c0361401c00c84004071490b05445103400250381c0340d6182c60400c50f5100c0c0b401d0400041041075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526959811 1250 526958561 526958573
    0xb0a120203040309030506060a051f11030c0c1005070b0a09020402070209090d1b21140d02040311030105190510120c0801050c04080a110402160f050601050427 70
    0x140502a509000100344002c02d50b001d80400100ca008505541481d1111000c200c06007800d0310480303511000142d5951041405400c54000d510b02d2420a00722886008c02c0c10307400d50700241c2c2001d80726040609844c0c0c1604207420043c1220346a8034042d450805260b440701c002d4070018210712000343d6600518411034403180d044443e070540080c4a40101d1900155840c3da40c0c80d0443c0c41ea0000702c10b00364182c014100c0341e54054070542d0004208691714000650307942050601410750f002c2000750f250202022801900500c1c041240d0f60000d80c0e5241542001e140b40703d01208083c0c0240e15000030440072200c00002401800100c400119080d105d0004010000c181908400b0303886503684102c3c0104052440e0443c11170b010b0380000c0c041c43d550a440703c0f03414000d03881504415003000000c0301c0000d5041d4148010550000c0006052584d282c0c4000c00c00c45949a0860b80c242041111806105040101034010402150f05001456840707000e0115000d8070324400d0801c503680381e440020414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526961061 1250 526959811 526959827
    0x5060d06050f01030c050414040809032104240c02040914010f050103020a06030902030d03020c15010803211b0c0106030209090313051503130f02041a01020c0d0308010b0a 75
    0x50840c00500c01400d0140301c800e4144003e200454144103c6080041d20b42803a0080c1100c4240651144420b0341d100d8071801125401251140e605000351403100b40036600c10602c0740e090340c651040703864480e8100000c0c02d90361407241010502c0e0046044000307400c142c2c000c070035200c100d034191800b080403030503890039005220901080001c2795081103800307121005203a128038100c81c001c80d1841c17021a607910060302200d90074034010307426410203440003240d14082c0d0014410100b40c502101d44000a07503200e08404082038028007200d40000072880701c032105035030181900701a020300e02c0141e81061030b9011800c19002c4044000c240003c00c000c0c5440d1002c1d4880c0e8000e41e000351000b0360302c0c6020700c20700d5140c0c2c2c803441e050450f0000c4500c3c04191401c140900ba846044100001445d6407100507441c0c2405080500484070f0303907401c9540000684641c080c3d04034400034204205281c56090002909169002c45100e002d1f4848103280070100c1c2e480340300541190303421803d05558404522045400702 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526962311 1250 526961061 526961063
    0x31506030b070309021c030203070b0c13060e01080906010b0901031a040903180b12130f06090b0603071e03080f0c070f03034e05040f0302120a080a05060d 68
    0x801c404020219805401142d102c510884e00203080368000c40214215208105018006078024008240040c110380300207a0080c026460141c100103514072010390140325900320ba0002080803510800e41d58000400b81c1d048080500640308e150b041140b03c4d0490b006083c00d00781055250798940640d01c11602050032a05400b1303000f03001c00314040c100680180c0e4000604000078102c5107000031504642410b0308c4200124544499080d100c08107903002515205100342c6014040c1400040024214070a0749895441605449420b252402c105400d00045902104204a42c020b4a400d074040e251420020742e41e01480040c0c66400c0380401640b2400b6207150303048a440b8801c80490380b14401c940e9642143c1c4255108464801001c48100703200c100c0e003482121035078101461050152000b500d004112148501001c10300c4400034050301500c6081d0760942c0c001e12400014000d041c0e05122070740c10600785400c06031502c040080000c2c09044020030740751640fa621b1000c500ca42d612018214426 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526963561 1250 526962311 526962323
    0xf1b041d1507200606100513050d062403050d0e01020a15090f08040312030e030d200d0501081504020d030c05030f18010e03120708070f02150d0b0307050a03150603 72
    0x140f01215402541c0310f001703442c2640315102012100707070350910a808841080b104422141201d925150501c0034650f2082d40172150a501c0750b21141300e581307045580701903495000007084a15032450503c28207001e186800c0404121100810134103e90f0000b4032146429440203c3e0650841c0c0a14550010000b100c13000302017025101114041c069803a01030020b99000300307015000f90354819401e608079003159040c0520358009201d040000b19080d0f0040f2011406400c210307803000340d180c000e03d00543c440c81480484540e0348005002c041ca040004541c259002c040a00315400c068000078420080079000804000c0c2c18841d2400300b12091081d9441c40c09a000455241c01d821019080070722020140c035030005d42d0f03480e86404145000200121040ba640d982e00b45491030310349034400603500c080360681c1c44019034080c0f400161100d441e20042c40e032409a0480e124048004514191410b0b860703018403d40c4150410300c02d540d01e801c1e901c0c04480d4403d46152280c0549051a405000c00c0d61000e048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526964811 1250 526963561 526963607
    0x702150d0c050a08060906090f09120f07060501140105092b11030d080c1b010204170a0b01060e031005040f0f0302060121120503090f1b041d1507 64
    0x4550300b00010300101e40d4651034481440e03480e0390034031807854021901660722207030000100352001880c4446a80010810003a00c800b10541650103105610030180c40030300120014544060009620a1501400d050390481120b1800100002d210f402043d00b91441024403180308180d49100d40c1300103000b00d440801c0c120744621203050003103e0384c40302040d0074004e0042400c004101c900c1409440d00c180d103a50621420103440d01d84074468403110040e0304a01e50741c00c02c400b0401410340c1e800880b0b044036050051003004907a2526844031101039100d1401d00810180462a035603010070aa4545121103a000581c2d41e00c600300891241c100702c0018050703060129aa47c281903000c200141038071070380740d095604000c4c10600390f00308413914040035003c4078021522004541c420401541c000c140c0354101c1d0304800381d0020440c100414041d02140305602000310040038140b60048482042c1c00c1502c441c1c814070100c00454450b40e84035410341100c00e8820000311614012001120452071401003440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526966061 1250 526964811 526964831
    0x31e090f11040c080406020a110a060c021912050304060b1e0907050a050729010e1617070f1107031a0901051b070501020409320c0702150d 61
    0x25000e0040009490302401c0e90300360340450a15002d00e01c0d41d000150f689610958a07925010029001418928100810020031010b0003108000d015503942c060750700020000d03610307078010345086810342c03241c25a250351280c0c00e004900031100340c3d1603d144034281550340c2e90340da10300000207094000716103a04c000c80c1e000c0d0b100c9004032031041c81142e510545800d40c1c03076160301d20281c40f00d005032071301d01c0001001001501300003044202ca042140503030800403500d00c1503c9800c1c40444c038098200c1c0318001103100c10041c0314810706101c555507105074101861001019400f44044840c020305070024054081011708065200e40c03900c0001f00c030303100103445a003504d9180c0081240d61030041c0c030140b0221030000c44c0e0a18018425a8061104160052403030b1103002800c0304941c0194405031000e56003444005604040b5000340c1c2070342e08409207135980c0e41e1400030030817603d031032a48060704e0300042c0b5104000034100210215041c60340c044442c0c2d085403101d01d6440405214008002804a08041c4540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526967311 1250 526966061 526966073
    0xf250f12030e2d06040909120e010f090905070903020616020102120c030901110a060204030b0628050d0204020708040824090c0f2404180203090706031e09 68
    0xc0001031003955010400b00c415410000c54010359a2400341402c40c3e83c8003a070b08005034100005403a440a4a00d41c2069a00c0c03408908464000d030090711291204001c440c403241d404803038500d614409080242c16100e14050003040000c242c00754400441d41e81003c60390241c05814040b00460740103010310390b035540c0c410504941e005004000c03070252241d0581400041c1781c0300213031342c400f40d1017800442c140425034004545000108070359100b58020500140c0c00300c6c4403400104055070044c55184001c5c10000e007444001c090b1200442e266070707030400002002d11515100c03501110401c603410b4082801500010f0000d10501900401048002400180418000c10b18001d5820720044d0100d11250207500c103410100212440502a0425a500070a52901ca4002d40c007210010b00884180854084070b06400c0c1d032043c0720b6512082c400314040042d215412440304000c02010025421030400000f600d50b500b00d10b005480c1455103450070100780c00f48044601c0c00c80380c0d00b1042402760000d1400c0c04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526968561 1250 526967311 526967339
    0x524092e030c120501080322030c031a070c0203071403030d020d0e0c011d01050307050d051311040c08010b03060d0503040905060f010302091e040b1215090f250f 71
    0x9002043d0380a0005440650b2071080d00c0c1200c803008051031030040b1600c4042d1350f0b030311226401c52041d11500804008070700428100c0c070145109500120011a41c0c2500c0140e10328010907900801c104e04204074010780f004681c0000b2561100002c3c07501000c02e8002a0070350050303110011484d0310225010b120f44059400032601c02c21200161007031004400011030742d16902c0030140d640000c18000180080d485140150307401209441e00608001880b0503a4064400641b540401a11075001c11000c4c0040b080c0180b8907064121030400c100000080040c21000301407186040c0d29101200184064079241100383c0c0d9103500009407983d950301d407603030480182000e42c1d04c2400351b100e160000085501a100703c80000e80001c0400d01800d0f01100801000c00385440400d410540760740b00d210403034171010203000f0b005108401800003079902c040041c95991008103000899400380092120fa448040b520300c1240ea09041e80403409141508030110041050340103010040004400092100712030300b0b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526969811 1250 526968561 526968581
    0x30905040c020a080a210c0c031413060507050f03041706010614040e07020a020306150f030106060903020907090816050108100501210f02030403090524092e03 70
    0x80112840e4041d049075240790700c0b1030043c2540410045d03413000c00d0040c08002194095074001c000c803035800801c104103651211406c1302c04aa14008000300305038000e62001440c580c081c0d103050034480000c0510182d107205101e10400c2c0980080c40c0c3d82800018440c01e890103000b00102d9030f80d5982c50300d0324640c0300d0425004031158041c0c0400070904c0da20030040340c2c40700c3d03941c511030506003401c10600c1021000081c1c010300a44c0b05038611640181c9040c460240300d00c00705075281701c043c0100c50910084144502d4182d110341d1400718107006164104241c5070070b583e016140d080c1c0f2580d1340c0c1c100383c48000c0290032204541c8941c0c490030ba030b030030f0318819500140c0360280e840c06041d031038007001d00c40c120307145010b51800300704120b00c103100d95242c00d100b04030710620028001c218880b8841380c6200702c0c0d0003500c081c0e000440b130340f00030300560900c9105000503620001c1e11411108414400030014003070540c03424402c040758040a09900741d1440c007142840e80d4240e0085100b4103176900030b0020400489 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526971061 1250 526969811 526969819
    0x20c010e0414040b060a0b0f25050a0308150a0f03110105040e040c2301021c0341041a1302040f0b04051303050301090e120d06140904030507140304050607030905 71
    0xc0494821f5158003991402c014130201c040c2005c00411800180910310040c4800c002c42c0d582082010070801c22403503060074006e032078203132581c200b0300c210702c82d10301c50091020b0050341500000c0120a4400c46d90300304603034011100040c45007c10004aa844c899030740150711111000d4180010b00c41c0307034455001100c0302002c2e03020358400c0210108140c520010140b83c050781020550740140583c4091442c031465851800003501e010361903110b00011855103038503125420264256420000301e441400e0034150510541d2201d01d040e50b0b800c051400345128150145400700041003864400589000c60154000c00030320a1020008100c00140082d03650544120704190105412000c0301d0004400c064040d92903d145a0038023043c0700180144c24a400790328418051300d02d107400003d2001d8042003001035004601c2030301d404400c0e00409401d8104511900c845d00920002a40042c21501c50680c0507060084080c8110000c42c114040d80d4003480c4c1001000549008040e48010440c040d00c008032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526972311 1250 526971061 526971079
    0xa03020a031821050906040608160309170c0a06060e0f0a0c1d0a09140108070915030311070305061e160e190b0d020c060f07020c010e0414040b06 64
    0x12142d007107100201101502061009028030460b03c03156091541209a0381041d5140000d5007000c140c440e0f0141d0f000000003a000700901c042d42c100078003c400180214682404049146c0c1c58034142085669815494006e00117008000340506102c0b180003a80c01540400207155554500f07803001c0e00c112a085482603254000540d81d8149100c0e404d1a60107965544c90100180c00304518555008a409a40613120f503030006200c1a81c0c0c0501d00030022038540915955241c20045480c00c2d01542040c04014189410001070500e0021400122901440d00080302c40130505090708254117508060814041d0b603040005051910711210984101420b10107180d6482c800340f404018401c09610001403806a030a0407645803071102d0500c0d01e106901c9414400c0e07601ca000c80925031200344c882242c02d4012a44202140050145582c80700901009092615102d00c2c0203440c0d4522584450501409010141c0da6849540c800c078103500118280042a040c0b608109217844002c9940d184034070300341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526973561 1250 526972311 526972331
    0x11a1e031f0c0201090c151b11100504030b13061401090b0109050301050609040305070c210b0603010515041a040f021b1920030a0c03030e0a05150d0209060a03020a03 73
    0x505c034680c00c05410949181700c05040007016a8030400840b040301c03c2158025500c00c5d90748000028100f8a84035494100c415a0448180252009259222001e00c0000c0c002040454400641298080c60009240d1409600d40c940a00142043d6245c122602d20000010801c05000e40c82000c80400980743c5880300e55440d0205400d03154201c5080d03130450821070100e00002e0203600a080e01c684100c41c4d4400154a500b803100b40d40541105400302d10186150072000d020040509542001c2c05030024840740c507210b685030050075034110340b03240519603d04403d580640d0b00ca13846028008018001e0007240f125a0095029403c041c0780c4000b44004d244000d00100f00000d140108004410500c500c2031034151212140700452a202c940d4070300b1b0500c0c00c807401ea9400e00050620503c61042d0455041c00c609000303100790114001c07240240005002403103142d41f1a1441c2c0250074a4104e12650740d03d40b440803034040e0094104180c0c11200202d6401d030815010b401403d070405040d81c041043c0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526974811 1250 526973561 526973563
    0xb070305010e0c2802010e1510150c020d030201060503010c02060a060611070b0d0f060308070507090608120c120a09030b10061b03090e090c0111011a1e031f0c02 71
    0x5403100c40e24081503010300e070041e2509248544d890320b000070700002031094001c480580c2000c650925443d040d56080f0100303c00600240d000070050700019039410022040024007601807403041501130301c83d868846400040603c02d4104001808001d40203005001c0803000c043c1d500d0b403043da5521809420000041001c9101e809141085400c400040c450585000560780c0345130701080c1c503a1100c40c2c031510540b034110842e00401004610812106a9401039410301c9402c00801e5040740242078206007081001c07401c002560010090b00d103a0317041e40e0340305002d1101d10b4420800c580c00c40d2108049000c0d00010b0704061080708480c001d441c2e655241e034607004001c2c1300240c0b602644010030300d05600881101d03000181542194402d003000721800d5180d00f420b0401c032030125400515030340526044001541e2220885402c80100c2c8002c0c05044404180d03500105003c10083c2c1c06010010b9103600e03191143c14a83e5600480076003522800d0304061002d2015100215020021074140340001d5a6984 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526976061 1250 526974811 526974817
    0xa110a17090a020d030c060f0c0834050c01020d24080a0503040b0f0c06180c01050301051c02060d0c05030f01170a06051305120304051e190f0b070305010e0c 69
    0x68002c00c0e200c0e200204c0d60b4207844c5442c45840c143e030010b07511002c0b018801c03a03070721640a0802e0151900416071401c0c031010512009190f08015130500250f900c100d03003800035072180d02155400d04202d5103c03c8060500c60082c080c80c14084010340c2818045004185204c01c4021003884010420204a0311034020683e1101041c000904550040000b00700801d92503003d446607405c4210f142d0f00e02030b00344844a261500c1560b0030900030542c0414001c800c10100210740c0080070a0030114210b40c0b5020008000b41c0000340749441ca9005030441800310f503980c00c01c440300d11601c07440420680717000f144000d2007038004840004501140d80000b0904401c14201480003112000040150340d00599510300030341070160501007291142369a41c00010303c240f011198007000741400948a1405040443c601512440007040c035000030b0705005001100460b4440103807161100c1100d640e00e0718944424000c010060282007030803110b050140544d45500017a0403140c0e491421708040d1245805401544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526977311 1250 526976061 526976063
    0x402010e0a0315090c09140a0c180909030c0f0f11010e0607031d06040b071b06050403060c14031302090c0c0a031421010602190c030602030a110a17090a 67
    0x440511100e083c841c2d001e4024030643c0f441041190074403a0303580200c4040d18400c0009611400600d410003103040024440c1036541c94003403074200c0401c48250300d003200320b084d10300a201003142c4401146042c5405078048041c00c44d17000c40c3c83d0150111070300701481c1c0b40c04000b23001c0340d04035202c1c11105120342c856a0440c200c0b89000b80014503000c926901078888040c2c06c0c030b6412147c81040e54503180c607600d11000d0b1004060400019503200020701d0408500121503c40060241050409000e456400410b460689034002000100c3d5002800245d4025050044051500700000104401170459082c2d840020b4401d440c07100198481410366130a50048110001c2c05a021105003c00310388a4a041078004510540303407490801158299001c000601158501c0e4601440c010403a069042041c0e408040040184082c83c100e6907560008031140c40c44060195500800071038400b0680d0b03807210150084500075a9581e09040f60081d0050304c060f484a180304400380d0015441147c0802ca802c5a1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526978417 1106 526977311 526977323
    0x4242a0204021c1b0206061201020c01090809100c0b22080c0c1e0a18020c010e070f0e060609060f070b0708042102101806140402010e0a03 61
    0x1860b0010070b1004401c107139103024001603501065107074000b0340890354484540900483ca45c00b9004911040032107528040c039036020042240001c0ca0040000c2c3c910702c24411101d01c00740c420001001c0047c0a9813503904c0000d1620b05641c1c1d100c60311860300400220000d601c1e80b070742e8905401100e243d4100d035202c46e401c0e001a140c07511214445a8800e05c2c0d010501a80c0004990401480d00c62481c841000d80300310b580840e801d1f01502d01c01086e9030001c11840e002000000d075a00c078139215038400d8200121020461913510070b40c1910984005c2c0038141350070500c1c400e1080f5a407042480703642007230342070180000186881c00c20038014a00d0395500d41031400c0500385840c03ea128143c550402c00780070501907036943e4020990425440c4200c1002581d04d900702440700c1403900031a0001e054524000c200c01715002d80074000c50040c3e00030303070752085015428001d000525225000160039 = true := by decide +kernel

theorem cover : BRFrame.Cov 526798561 526978417 := by
  have h0 := BRFrame.cov_init 526798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526798561 ≤ n) (h2 : n < 526978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
