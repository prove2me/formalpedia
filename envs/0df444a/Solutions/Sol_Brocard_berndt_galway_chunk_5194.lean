-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:27.418908+00:00
-- url     : https://prove2.me/submissions/253b99b5-15be-4fe6-a505-8052f7dc76e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933992805 ≤ n < 934172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933994055 1250 933992805 933992827
    0x14010f0b011202031509041104110310051201060b0c0303070906051e18060c010e10200a020102090402040f05010206130b0a090c0e09010c080108070506090d020d0203060106081b 78
    0x1a04401402d015240c010000525642030880c050030350010140420025141a16044480c0d4515001c2e90340300303600d4000e200300d510305401c0590f44244007600c82c0c07803242400c0c00e080040461040380d03500b0041d03407692070200d80c4a540e6405031410402a03402561641070006000e441e400342500110304020b0184100c0c01054000c1c03040c0004281011551951740d0a0004610003a5490100c0c550700003074006051000c04005620004120203000180c9400001101070792081d10f200600e0381403004950707404010035090610081607a454140001440c3c0081500860243c1c0c22960218110f000d111000b08040c0d6018460242c4c00341500c141092a41001e41d2a450f50005c0a41f15040e0650b40d89254010420300380e100c00040c180d0494040000d2034800101c83c042c001299034030000560781000000c00604c0024454196407008008504200001003400002c549001d02a40d0140702050040050380302404040d000c1e14142d41c1e28515458228004580110111050240b0038002c111903100c039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933995305 1250 933994055 933994067
    0x30833011b020a031407080c130c121a04230a15030510051f0602030f0928080606010c030206010519030c0e0717070206131e14010f0b01 60
    0x840242420420820030000410500850880094008840680c04000e100c0c0d0110414900b20708442201d055a0311400d00c2610341d1b2004800d40c0d0400040541941c890400da040850400914503002d081820402070101c2556402442200410007456403003001c1d0810b400b40030341c0c50520460141c0c40348600c402d1090003050080c04100f00079600c404a0625103924442da500650700b110032519007041481c1d9160003460b00341d4070030074000c8040e02400940007400d070a110480c0d240f40c01843c24030095601280301a44503c1c40168024400c4600401007030f06070f0118800841c444402c4800c0da4200300751a803804401620440c1403040c0004980000303903002951605441040d181d0306a11500e07008615030185076500014581e8000003800300300c44601402043c40b90096a68190005410404034480c180065a4010061300210002201201442090849188a502031802601d01d003641200c2d0300508a4007200d080794a0410103401e04024011000407508140c0100500e0300c10700006408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933996555 1250 933995305 933995401
    0x921040f060905092725240807030207140c0901050139050303090a0308011a0a080417210f0702070e0411041a1014041404180308 57
    0x2180809018110006030404017401c0100081007194140e40c581602d151015424202c0300300c0d050111600000c03118141401c0d13984a2100c038086440b882854581207403050f90003041c80c02895000c110752070001d00c4601e4104025000500a461000d10b2030f0108411082c042c1d01481c1000560b4905800352451011211100c5111010003030b0301060a4480520380c0b5404070f0080c000d03010100030402205402300b45820500d110350b4488150381c5c1c0380c0010396103407801c5414414800b4400e10004943c0c03405238510319000b50090b4403848602000407004149503200300700c1e211541740259041d8803c2645020119001581c0064100e824078020341c0080d03507690240b0886680b8a0711074003280030722081d00c0645c806d80c403001d0014401800045200d420f90301720540220301030080f208156100038452091280000e011258207440d282c5821015517030980710342e62042e4460f80e1541820a86503150a4040c2c40728800e40b200740c0c1c940b0341500c0749684400100305001c004a005c05602a40700ca12582c2918 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933997805 1250 933996555 933996571
    0x5060610050f0703090f12021816080c19020f12041505130909050c01260c0a030e1e0d0203120a051015081005010f0503040b0921040f06090509 63
    0x61030f2020b03420201d1340c85482d544070001b11650280301281c40a0115003142c0902c0c0252402103500c000d8042c0040100012508041d0300340b620620524034030321401c1c450340c02005a0441505001030046001007800070400100050b81c0721104411842009010805031106090703600d40c2001c0c5420020440345507032110501c2040710000740c001e03500c030140407900c0140c01c043d001080781c20320328940556109407110000d070128842402138107540c1703549070320009910b60f581141e0300c042c0c84410001d003280d0410400386003415100e224103001c030501044118119480c215102c600b0387c04840b4024140b4460415007011904100724511981c880c1209607908a182c40c5030001e01d946c0c400d0200058050380e41c1041078208444138841c86255030101000380034040003e22600c009a8507001580c00414428031240441c000b400018080740e0508111980007941000f51004100d000c0c0071110700d05500001c6ca040300c1c0c00418140042c000c0d9001c00c401400c01420030001c018100300024a0150300101030300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933999055 1250 933997805 933997807
    0xf03020a17030c0d080601092321030c060609010b041d0601021011120603012c0a060606110d02070e010302041505091320010c0816080d0905060610050f 67
    0x724240c0d400300222543d040c2114140e441e240d014810081c079405069910b030f0b0010307107031070400310b80705404156050364a006030040f07048070340800c0300344000754101141e4016251180c48100d8942d480500c02000f808450802030084c924001040091f540d2040c1c1141d40c91800610007030029842d0740520013282005502515003907910900101d03d420200175000380d00038148003c1c9486000c540015113802c0341c805c0f84040d003a40e01d580a15080350f05a266452210a0114420000c50049c3c0a0a040710325803500741d8001c2c2d07903240c80b244156020b96204200140001030941c0c184002030054699542c5284090000c3c2868181d0031980c030310040c0000f901c120f80d035620347d44042e9028040c6000500018005100034a408001e076140129441c20656500c401001b001034001d081d04403100d4070342c01c1612080c100303210984890101d50000a00c000b12650790003d4680450b0b5400050044a101c03400080780c10096454514184403020300194082c0070f17441c000040a50b040700c1502da040354200003032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934000305 1250 933999055 933999089
    0x3040f02010818070b030a0e0c220e031306260402150d0c030b12070b040b09030a15092a180209130b01030c02190f0804032102070f03020a 61
    0x4a011003c1c1080c0605543c0328440303000400d54001c3c006107116008550080242441d801e0480b900d4212400c020350b030243c2005c5080c00350b04400144c5984242c1c0311040014010006a6010300d142c0c0081da10440140e90309804006042c1d0007040e11200002100e010410300501d55031400c165080a40000d01c01d019801902100114580079120051981702d01845104410070f0090003c04000c001c4d035008030444811041c0050000603442c00b101d1030044202e14241c90001000040c0c5c003c0744080e03074540580705049002c148090b08130401c4504181c0300266010842c908030159403481c1c40040803105085174000058814840071100b11a11000181041520458100002e1041e540080e42c00008181405070030b28555024900c07079034003a00c4c10400f4a00000c0280e81d00e0000c10404c1c0040100450030344009480800d03850382c031921901000d410951659a04d1004e03204a0380c42e6049202c00c007501c0000305504000c1c58005250204c0798401190868020903980e0306a8000c03059002c01c40695 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934001555 1250 934000305 934000321
    0xc0307171c2403051905070f030501021215030606040b01050d140f0108010524010311040909020315090309040203041b060906020f0304150f020a0c08100e0303040f020108 75
    0xc55066485803050000c20700c03080c240c0c5400802c400500e14404508456102e1040c206002d6560103890b004001050441007040c004000c0150515040b10b142c0038a07400003509030084801e0a01942c401c100242e240c000074251082c01c204002e010540003500156190090344010540780c0d0002002c7d5008106104e09500503034851054185000c6140d103072120184100204808140c0540d800d42601c664590340c3d0340641b420303100c050790b24200f41442c1e0210465100c0c21452403504d5501d041c14081000c186180c0c502c45d03140c00070b40c0107807480da440c3c50000086240501090040000c17058040f00b881c2044200d80f82e45c0d0040c174440710302981d4008007041c140000d9140070392420003083c580c0d00300280c51b8100204040c41c50312905025100c0c084080d81c02900c00b0050350140c071481d100c42030314007480b50320031140040104004401d5000f4009a000402c7e2a2081040030b424840b00420482c0c3d02c3d50854811514008410070040d081070007400000340310b10f01c5641c002c03030302480c04007000d4581e944 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934002805 1250 934001555 934001557
    0x50402040e030a0906020606061801050a090e07080402040b030a030e151c0209130b010828060f0602150103260d0504061d030c072312060a0506060c030717 68
    0x2944070028440840c540011550103074079101a180e4036825190035481d0602402001c3c017808240020021941d844c103a01544100040d181500092034101e020980d104a02d14030908240c0b01400080c0d0801d04010560510380101001c03540142c004110040d482d8030001c141128100240b8802e04032120244030300c810f22030a03103903540b924102d564142030040d0071160080d801910762a0050091072807070680da0f4158402d012114078185c403041c1c159564075840401410328500c030305c0082d00c03082c6920082c10845126040c054a0701e80600380e500b43c00d102d00030f80f40c10410742103401082c00c03510040c000643c0101a860300c0c0c211440c0c01800c4d010107241407403168000c80f488000300b00d1030901048140710182d04a10b003415044400708409049032060729442e40b05080418509038400c2204201d64030b49140c58030030344000c40c58109804164940058080030f041c1070b45a40a500900070f02000d810a486265048901180c6807072502d20208105034a0b40074002e00900880c40703580c0c1104032112600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934004055 1250 934002805 934002821
    0xc1c02011401141809030a260405061b0f0403020d140d0914010c08091e031905010c0309050a0f0c0f03060f06150207140d080c060712020a09060305040204 68
    0x84492400c0c1d60311910b081d02c0c2803160280d0284075608134403045008900301d03a0000d00907030204029524015105d4026a15003d00b104040750421406521300380d203110b00982d05014030b105402520542c2403901c81034600300b480e4031110f14010320800018456042e00300c00c88003283e505958801030010f060800c00101d41100e610382840c0d0154074441d11060354040200c40503610044c03a403190710ba40ca0300044510912001000388002000c000100d100d00c0d2201d42f909006040c0007013405001100b5001c030b07081045031100d40281d0030142208108005c8280507250b0307400401c0ca01004a40059202e1035641c1c000b111001d000b69560f00300c00710a108007501c03460050912424150021f995071b1600f08020050344440b41d241c0381c40c01c140880e01c101c43d1188104505010381c02405d500742401e4141c900c074500790449d160b1200003000800700013801140900780d0802d00f01c000c0c2103a440e101ca07025241d00301c550b0b40411902d01c100210400036801c5400c603420344803189400102a9120310214004100745 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934005305 1250 934004055 934004081
    0x81902040e0106030c0504050612060406091802030606030c0906010c05100515311503060c050901020f0307031d0d0501060305010219090e01050d031701081b060c1c0201 74
    0x15001c40c9010012007014121012a5030411455114a00443c0c4500071400741590146c81000810402050041d9040d0030540003000041d03461b98440703004040b0b030035000a403400942d61407205d0095240502041e07600c1201503001e0f20790110001e000030841240100641d0500c00310883c400140101048040501c007640442007043c0d08081440700c501558212003548115000403003001229002c203da0400028031801d240c203410001812800940f0240c1580c641402c00c2107000800700b0400e0182019004254a5982d81c80c000760b800241082c1c1c40c090712601d1540100018000294040001c4004100c1c251002d114036411750000744441d0300000000d0020b6003404004000d00c10190300600641a1051111000000880c010783ea00c54182c890304111003620801000039040c80c52101840b244a0301d040a58112080c1c00080d01400a800c05221a40520044000a06401d01c000c00d8010300300c0d411801c1054080c40c003903684a45581764060840f801441240c124001d40001400d0746003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934006555 1250 934005305 934005307
    0x315060c1a0a6810111c0b0d1703060906030607020d030b01030605030d080f011413020a26010303090b0f09010309031b060b040c140301030b150405090105240a06081902 74
    0x24400941c1e84d640070404901100610382005540029080e0701224650400400c10200c00d00c2440c0d0b0a800900c0c0c09400c41c3e8020031020080350009100110002035500da090825440c2d0074403c0607c0880140100700c140683d002c4401c0c40301064001030704131003035400e80c500480c3d42000e8800480151003540d1185805d440340081000b0550b03003108441d4482d00400b01004c2c45603036101e40a400a03503245e0182d5401c00d2005100c580c0380012b07500140f043c00d4031030070150360429819106810040715000ca0002c01d0302c02c4c1e401801015840925800200942100d083c144610038810391400d100c0c00102606065a403e2984101f501601c1d022812248000d420600750005040c100040c01c1c2c10484148603034500101d0140407070044c0301d030480c0c00d00d4040c00b10781140c5c25951130240700e44000d00315101454940f03400349120340c0e86010b400d1040381094000b01302400e00a0103c070700000324007104200010030f190418290384403010200119041880c1007000c9803034400c4140c1e0340401e40040401d803140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934007805 1250 934006555 934006751
    0x209130509011d0d0504050613050a06090306150302010519020c06460f090510051210030b1b1b070807060315060c1a0a 53
    0x5010f60101e800c0c552402c0741900003920340c090068075488030319134460100d64184014050303810184060190380050070500c00840e80c45000240b02c80005510610005c3d0b110002842040a5401503201429108020380d40d000e041d6030000c0c02a000f0041c9105240810002c40303d88548200500035402c07a020700030540d00c50421a11100c282e11040040f00141968800615003c403080c43c0c002d20407030ba6280700c549d140300c07440088410504d100c900da42040480c03400807583c0d03650f090b03c02901c99403a40b1450399488800b01c0f00070740c001e0028110020411815020800300300b14000300c1c2e6000c01a2280290283d1358091004214050307c3d205a1041c1d98581841c121480d0009003c815609080104c41150341d8904044050300c0764801c011003010182c070301c200720050040300403512262040d00c00f043c81c0000141c044a0b21389003103482c03c0c00e0640301c2d01650018401c0703020303022254400101d240c0e03410401c943c03603c408841140c04607081119040f10100002d98201e41100032803214001c0c60b2401e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934009055 1250 934007805 934007821
    0x1a010b091005040b0a08060a0f09021c09031202031e040c03031b0f020f0117090616030204050f0d110d060c080c271201020c030712020d1202091305 65
    0x6001110500c0c0507003480341d81c1c00e2010340580d050b201100c0c0004999442c1200a1908980301c0c00040c040319081000014003090134110b0580d4200503110304800143c83d03280307110f0600c420082034507000104515120455010a60242d03034040c1d0364554810241e0740e600c0b603810302d1121001c1c000c44024050346080500c02000b1802009a007200c3c001d03500c40030044000c0b2012925041d010200a0416040301d42100c01400c014000d03929a4605041048409014440c0110303c24000c0b0382c0b0306240c0d0080c004000218400080c2c092802a0503d4114141800c11002c51003556446920034461602a10700b0401c10590500c1c0000740d50300039050480301100f40c90000007a02c040380385000840e06402c00503001b1100f84050b201100c0d0070a28024002d0025031b803100218400c081c0040d00b0603c1c242490504003424001007400324402c1c0010740c0e072540d180c1054032101190030030142c11500000d04402620f544175132801c800003014100143d07129801c1000824502c1c042c8010b01d901424002004851 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934010305 1250 934009055 934009057
    0x30b09040f1106131404020306010c12050412030c0605010611371a130f030c050c09101a030708070521010906090e0c100509060c0f070807090c0212071a010b 69
    0x181c1442d1440d20b0111703401001c000981c0801c80740716001640c40c9003c407010034404800c07901c1042d018145141340030345400040d240c5a241c0842a804500d8558124040026500c9182e0040c240c1c0d142c003c6000c6109111180c658107540108200c0c0e5442040b40241c160b1034100c10480c10b1509002d4403210a02482d042c001c40e2600d1410010243c00d0100060056000c0d070710b441c46141c3c0c42988202541c090787e50964090076041d4040d621845030103c80c1001c0c2d2241158140616101600c00340010726180c070b110450034105001404800092003440b034069040581103030072543c6414480d8a48014a0009140703002401c5100b011010314400054034a01980c050300907502415030074441aa2034100b50755950010070070b555007042e040351444600c01e11880207400d42100007080c10b45004031442c0c0003450034100d00c15071401e0f42c004800030400d034070040200e07030010480304e5000d01c60045104000794488110514030080d105000400e00f00304040384ca0003408001650180c842c00756140c40e060111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934011555 1250 934010305 934010309
    0x304030c050f010605060906161505061c26070606060f030b0d0f2402030c0405011e090b0912160609090204030b060f030712080307020607030b09040f110613 69
    0x1405140d041c640c42d054180603000030340d42c004d070100d4a480b0001c400d001c01d96001c2040904860f030292101381c00511205178080c1c03524800389021841d41880400c00c051221308030780e1008090b40d10902000080c031700c1c0b000c1d107002d141c1e80d81c40035425480b040d14150301485864002400c0d40d250040108001da0020003200c0458080d079030402003414110240308001011620150490300402d00d980001382c1943c0c100007810000c00c00c1c294000c995040e50344280d80041d62000102640407030300b0b100e0741d40e1020b00c1006201039017400c150ba40c404d03d0b4003d005400d1a0182241d1030300c002419580c6901c40c040e00324441003015040300c801c07507043d059001680380d02c2e02503100003450b440800035a4002078003d550640b6008101c000441d140d031030420140003a4007880b19014040e80c4000150103ca40ba900725145000d00003295603468250802818910010503d40901d46802c1210030300d03840398800300303a00c00d901000ca90071130a56401c203005403001c68055241d20240000e401d01014040c2c0c209041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934012805 1250 934011555 934011563
    0x30406140a02030d2703110c09160311090604060825050d15080d09061b1101030e0705030f0f16141309021915031b120b060304030c 58
    0x601003410a94040907100e0400341c1c1c00140d0040c48920030168842d8091401c2910140d03000210706454035910f0208818144164003046090346080c0b1044400c6c4035000c01400704455002061030160712507401000900b0408080650f5810303440404c0003c141210040d2400900103a00c0316511100209201c60031a003441800c000039042c20781c1441d4100c52004840c5054451908229520300d0b28001401c466450280080e840710002a10200a10000c0c036204c0d8103a85221185e410f00c0c40107460588010b010381d50004034010038030302040c11980d544e10036540910f00410888e40603403e0900e00309480e000b10f681030044c51017000b0540000101d00754010004801c1d1800852050701d11354102441e4480d407844116501e1509106103040c0740744400c50311600c440003c6151081d00403038500e007404007496540c401c03034540900014441000716500822140341c107124844070480c0207020001c00d070241e101480b4900f0074030460301c4c1298100034a4180301a08580e03c1349401d050060060120703100a403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934014055 1250 934012805 934012817
    0xd09060516030506031b01020309061908090c090a0b0402190e03010b030c0f100c06060b0703110a05120c010e0f0a1b060801120840060914040b030f030406 68
    0x528000d01a43c1d02c12040200503016082d01c80b0b018450000c0885070043c110b003c100300040e03041d5110009014029903c8806000d04401402e0181c100900601107000319885019400304d03580c1e4000045a11020b10000800c0b000305910205000e4015071590b8451140f401c6030085900e40d01ca11000c10340c0208500074060049d8923000e15480b64041d201e1607400000507042404181807500c0010181c4000d40380040d110741c00c1ea25400102c900300d03008024580000502c11060580c00388241140c81c801c6c00c003030002500d09564680c5c0d40e10219140c900e018101054800c5030007404e5100c40c4203200c40d0415904c00c00002200c06481d543c0005044405c030026840790300c0f001d40c0d900040000c0e10303146e40f03c002c1e060342800b00480354081c0510084600c8001006450889102100303507a42e11020420f1030254000028140d15444030811288a016030030007008000c0e441c0c0c440006821100202074603011910b100012a002e050000e12983d018891a440c80300841d10000061080300c255640750 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934015305 1250 934014055 934014091
    0x20f0711041503020a21020603040b040b0106210b01031d01060321050a3e070614070204020903010e03030f1008010c1d030a171206040204050a1a0d090605 68
    0x402d1114065010280d00110024024400c42d1215409040c003101e2140c070b040ca11202d241e000600a0b0b0044400b2900028041c051200304000c0072410350240125040c288000314650500c1031540001031040c441d42d9031903403c4500c0c0d990203a480320701c0c0042c001400000c180303200350046001e03107201e200403511507074440b8081e000b8040c01e00e0303109448040d40d51600d241c036401c107604440e1030401c40800c1c0c02c10642d4014000d10300280103c1c90320743c0d0500c14008400910075191040c205000c0b03034003a0042c41004280444240f40d54800c640140b60704039001030702c6034030042c08680142803043d40b0410900c40041401108071401c441d03144140d039454540006181c03140505401e0f00c03140e511443c082121007407900074010000000c0c21300c2c440d000c2c0458149203a29214000f00c118005180c01d030050700014803c074040d0070a96019488441138805524181c50b1002246400c04a0711810040300d031590040c16140300c1c0142100e0503076054a0342440b0201c0706040207401410160f900b885107124031880c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934016555 1250 934015305 934015331
    0x209030f01020901080f180109031e0201050121050f0d0903151a0f0315010e101a031b0409020c03090a12030806090c0904090605040203070b03040f15020f071104 71
    0xc840715483c0680d611443c5441d4982107014414018181041c0b101030326000114031803091141d403040d140a561100200c18407552922202851504101704590401005000c180d900050700e104d0b00032340080e0b0045811450402c2410f00c14000012080d9004614803014000e9005004409407401840060600f44040310f4540880f4202c9841030035800c450803034001e0714680019001d40d00400901914190b0000e0409000440003d802010710f540d05030060000001510500f50068820a5040e1505601400c00c58410740070007091064003007a6501103023640c4841d8003d48000381401d40045d0b451358041080c503512a00f100da8058082d41026a000454841e6544604852505500c030105a03031601e00900096107401803070300c100a0410020b191003904c40384140d01d03025006070800106424548109401d01c60780343c0c06040d00304030074000c3c480401d104114251020b54004c95544108a40503c100e01074011017030044400c401c04154501800303003541c0ca0b4240101d0480701080700240c00c61f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934017805 1250 934016555 934016557
    0x110c090f090c0904110d08040b0313031407051c03090209070905180115030c3506040b03030a180f03210815091509160e030a030e04090f1202010209030f0102 69
    0x244c05042d03a5140301c61600d25007410048400d585000d9091b00e8946603c4020400c007680c001c1d070f04021541042c5900000340355100380030803202c400b00c070000c03450804a0307121561354264080040da0b803200d00c1140644c01e02c0c040e9001c20b0756030f54081c04564992a050b04040c3c1640b10a1186c140180f01ca04a0314060100211140d81601ca01c0f01c1c401d020540301d003004038001e041d50188242408081c40c030201c40c3c89905421242403080c03401d107065281c0080d080003024600060020f50080e030415505070f100e0754010080c3d407070082e0300f032820313499a009041c40740e549030170305501031560b1018000000c424049031080c00c403001450700c800e001601c4548502180c504100711180b6403112802051403046141220501c2e803c110043c9910680c0031301d80000500c01c140580f607801c2d20f0442c080d01c036030040350858001440d070300040700070348282851502c01030487d4010303c00d02841541d0f01d0718050104600850301e050a6034101088400311441c1c5070001c3d00070b41c40329400c00c5c442e104503401d00c401000140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934019055 1250 934017805 934017811
    0x60603060904030509030f251401020a02120c0405070e040506010c0507180609020a0e01090b130b0a032903070e131704031509020a140d03110c090f090c09 68
    0x20342072041c00d941d55182100d05410420b8040da02d40118000c0b41c0741420700700801207454480f02805045c0240440000d910840c0962000740340030440480001c0580c0c0110f45480070703a0301561901a5060803c00c11810040c64000c0f07581c0c41480c12040c00131030740c1d10070003002007110241c90420081e2900d1006603440020100c000b0000d500038502444901d542003140010320b04003841c00700301d1070b8a8449600076600000c80c0440082c00da080b61801540c4d000d154003000340710215070300d4584103150000000188260161001e0a40001928482c4a1083d800101d048180444448008000c5a8603a50000c00c25040c1d6209100303240e00802d0032150346503454000d04071140f80138080404d5075544074408550050b070f9880000140800400304003036082000b201100c104000400a10500c108601801b07250000c034002c1320b0b0039100304c41c65129a8045894903406007410004690140709603803600d41d41d01446500504080f00f441610300260704054060300010742541ca0004001c000e101101d9011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934020305 1250 934019055 934019059
    0x91104240807186603020d0b0306040809012304030206070c0915050307060314040b04030e1c0615080c0f0f0414040b0c09240706020a1d0307081b0f03011103040b06060306 75
    0x10241c07035000b503019074010642a4400c940101d41148500000303030132b090f0100e8096a03400300c0007820303141a40c0e014200e04105400e80c4482c16008010a0100d0750a000e2404000c1c000d60700050300d00c080c0450010100300038401450240a24200c41c51522152040381c400c0c1e80c081d02c80e410380418171a0090091040602d18810200881c1e0f459440d212001c3c040a0010740512400780894195a1900c41254040002041c20988094420701c0c141d0115041c909400c3c148010740d000034003040070f0115011020340e500300e809900c036040440c00520009464582e45910038070700282c03080e46252801c1c0c0248205d00030605102259100144000ea43c0706000d201917000110b0b0994414010b80d4a0892160200c40d0b8005414180a9030b542c504a9000c4691800814117000340a0743e402441400140b14240540181003032519154420303540d02c641c00410000c900001107661101d8450516101050000030003c0c00380c000ba48001404660042c2c03420b985181503240000c0403420050f045902403040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934021555 1250 934020305 934020491
    0x70b070c020a320f130b0f0603010608040b0a06060c030f11031b07090b18070c02030a21180b09010c0503040618090b031009110424080718 61
    0x20304490b04006046c01d0344d946a10144955050200d515010040c1d40a003800307854510050a0034100a201144001c11500c951820321030144400c541c4803402d461001c1e03060526281c504040340c03080e1205540813880e00d21070b10001c0391494081114000500071400b403c0c040d1403040792680d40401c103407140f50b000c0903080769908400b4181454601d002c0c0358021000d19080f13842c50b91a500003828603611043c165801e010030000313081d100c41114a581c0d51044603040030340480c0420000d40d4603500341d03480b032800107131070124101c0c0e8164014510350009980c0441aa42d64684900014128510607140316030510f48042c400304403084035110312085a8801801460700d8206005900c015140180048540c5c9203e10144451901c0c1d03400b614880300400d60740b100c03005011744640003019090b50300c5031a441c0d004580400c140c00c421074070209640c0d00090041385498016045001d0940b214403a402e06000b500081e0f5035694018500c60300042e040d803242c030514100107104d4035514501c07802459003555 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934022805 1250 934021555 934021579
    0x10050411120f07140307230a05090f1602070308040305060702061b1912020711042706051005090a0b1f02030a0305100801060b07020312070b070c020a320f 68
    0x18404d031556040d001412619110345440340400c6005900da0603185001c0300e96001b040d203203062500d01c00984003e4960010603c3c0801400c1c154020117801482d00c1d146010044176205d100340f01100165410190703042e40c542e961325055668440c110380d4840180100707004180240503000c00c102c001e9041c0ad41581c00c2030958458203501828600107141400712040c0160503446040c00501425405000c9031050124120140400c1d190140721844c0c41c0c0b10004906e03000c0f802120003030b160198205500241554a106d10705c00170881540200ea0303c60b43c40c40030844904100d401c40385954000395800e4000590034070940100826140e80100075070001e1060608842c4240c1c0302c142e00c221203e6488200300d03650011a8210707002e54102c240c0c81400001c40006606040080000c040c90f128103c503c0c0c4101e0351201d0800c0312000d0004004c01c10540000c10070b40d0b98079415200600300b0310090504281800442c400700c00401840b90307102c0e0b200d48121442524043d05d9007408030342c010704242d403076036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934024055 1250 934022805 934022819
    0x180b0708180901080339010902011d180a0914030a0201231f050a12020a0512280519050d030903090b0721020d180605040902090310050411120f07 64
    0x5860f41b000281444006140c24001081c0040150780b40a41c81c400040d02d00310324000146000c028042d0f107805c00c00d0201641056440d007102c0d401c0504189441342541c1e403580f01d5410f01900b0460ba01034543c00c110942d1000503080030001300701c0801030750000c00900c0c01c41100d01c030a0624200290b01c48000c01e0002030001012413426421100407464007429194a0f1400901c000d0020b82003507800544c82201e10085007480300382d01000e004111603000030032101195082e80e034201c0c3c09013022a42d99207841144030030988100021665031040035903031446454030b1001c160540d800f10a0304c0340c3c0b203060105c402c024044d01c00d103680c5c3e9826984401819040c42042c41180d40200750131510000c2e00120100355103484c03c6e0051910000b6405420201c4182030000d042c581807200d01924034400c241c2c00c1008580190480d8100c540070040941c9542d00a0002418114a4a0004011030410302000700304220711004040340003040380c0000895120154813942c83c00d010004146661019400740111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934025305 1250 934024055 934024087
    0x14073f020c011b050708250f05042d020a030b180103060b010203120c0406020618031608070605090d120b0d230d0305190c020d180b07081809010803 65
    0x2802c0120f80710b000c4014540e80e22807810303100782d05ca00002d40009242e03100160220801c00d124141113001c1d602600c2c2058140c10680030540724040c070071a45c800303002c004110250a1034840010703241c6d00e0100039161041040c060351005040d000040d291021a80107450181800d1610024400001c520340c0c0c2150348840003030040d050807505505c014820724888202804409114050700e42c0c04644480c035150000c0d02d4964040c01d14117440c81a46040111f5150020545050000301500d120442650707050850b2984107444014216a0405d01007040c052030000302c03854030100701d0740ca10082c8881c100c900c1c000c40d00111095503011041c40411341c00301e007403100d20040303a1a41540000c0f403402c403680c2c912702e0b242c4d61400030700100752900d0810024040040c501d41c1e0394001810180040221201c0084d00c0c1c3e41040144800e000c0d005038500c20300508d44c80103a0140095030000e680e00c02c03580c1072282d603030b401400103510310149001c6501c1050908028140c100c030411001103081c010071111149071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934026555 1250 934025305 934025327
    0x2070b041502040b070c050907080f0f0c090a030602030f240d02041104060f08070c17070507031203020706050a27140105040309090c0212090114073f020c01 69
    0x41c4035024840401d040b40208020f091035403140070325001c01460541805070f8140018110b8040c007984008112000462410f8035030321110300341030001250b80e440c07007440c283d005601030103411401c4800040100b040300e138015809000001c600441594400c15400150000744d20401481450380c841c1003160308091452001c0e080c40100085031a6003001d900e503420303420a1b800352000410700d0b01600103060f0003040f100d4010314507103840400803a46444510301c00f5010030404134900c0e00012401c2c144081401800081d6912a003030004562403042d00a0280d0002030094451500e010007254400303940303104800c0001040d43c50583c60410380f28402c00b440055075015903000d008028900381030003080c071489200303c3c4291540483c1a080460340822141c8140800c002c0d9030104194110b2600e40078141e602103c000d00e00001d01c0d13911507225084a010725400280000d1103564070750341084404124108020341c508183c6500c1182c40c0d0320921001070302d04035a000d604004c0342c0c101750f54492152100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934027805 1250 934026555 934026593
    0x60e030a05120c250509010909200f03060a0203180a0f02150c0316151a090c0f19260105010e120a0b040201020d030b030c130605150c0105060402070b04 67
    0x404120b02145054080814110329010310b0010130901041c6003036411180900f0180000300003c030301b280c2d900c2c401280c5041c1541c14402810281c4107584d511404002003000000e410f50300c80307040915110000c0c0d002520031840b103031364100e4101c11022000075028501900301c0c1002e4580006902031051070071010f480603240180402841c03104a40c200020720903001000c0d4843e15460241c140700b05003400d50001c6d00c3c2c0043c02e1890300c0141901d03424094440e9203044502e800785c0e4665269200c5244a9500203000018010170752005803407801080c000c42000980301c0644002801c1d500c4841d80c080f0900002c07046400a0045c0503e51041d502d424203c50b001d82074400502c004540c03140381c0490b41100f00c0b20304850504100031540c0c14811aa01d1076071038101401004920b50000f9191100e00c40d030740c0d01400c02c0052032841c4110303c1d0841d00040c28080d02103450380720206d0054100c1d0b40244454403c643c03c0402150460406108035840207030415201200b036100c03640c540c1c5540d5180b0001ca0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934029055 1250 934027805 934027813
    0x51302030f0f01061a030141090a02070809040b060c0f07050a06050a120b03013806040f0909021c0507030b091b010315150e0a080f0607080a1e06060e030a05120c 71
    0x5168100b101c800d9007903c4016803400788c0d945500d281041800c0c035008003145001e40c0140440000940003a0a5a4a4000894010588001640118515008507084040144102240c480101801044150a84405444003a0003a445003819030b800e10400c614540000c218888100d4981400c0e071044824080050001c540d00703510514102140100040045651104151b52060200c0e41030441e268010309036201070429103000c17040c0103000104c1c0701d1031100da40c941c141c02c1d0440d03032005200300a0124415a48208001506085590b120036000c1100c203604000c0106060b40130000d840360711590f040004808840304540110003509006606801c241c0c1c809030041941e0206203441070201d1142d9075140c18a003078610400001400d1039000c00c2c02034021201d07104900034003141e100d45c00301481c140002c00d6116400c1d454000c180506641c030b024621030344041c03055512500b1010890300c46958480c001d10303a9008140e1a0300301e0b114014941c2d44102c1c042940000c012020307001091000c4191 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934030305 1250 934029055 934029119
    0xa0512070302060703050a030e0d080a020a05070602030106080718150c0321020324060a180b2a0d210b090901020a0809031309051302030f0f01061a0301 67
    0x42000e84d000488124046040403541c810030b941d040c4281011004260020440030104d004041d210b60700141904034103a400007075204415008008869032160302c00d00441d07a0303680d01c000c01405010107070f03801c9000912a50f10345607640228449003003038400c20040d40303801d00d00044003600c1014000c407085090000440520fa002003c0c191035004210b881400941e03240362111040c0c200060b070030700001c09120403004543c0203480d00030654030b0b041c205007400241c0300d500d030608502c11101030703000125280e0002220304441c40680ca01510004d0000d000c10445201094099100c0840c03140040004a00340e00c059a000c080d8a2940c1200218a03030014100c1c1c5588045410785600b1560314815a4000804001041d44925120f4ac80300700702000c0c604010b11400341066a084521481070a9510740008c0b60b408408680032800351075006044070f03000d070b00040c12280c43e242c006203000303169460030380c0006110300030806506a843d0340300312207455030703080c80311112010798020b10068462100d0055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934031555 1250 934030305 934030309
    0x5070201140706091103010e100c0302071b030308060406080a060c03180503070c08060f040f022d03015c0408010b0a1a1c1505090603010203060a0512070302 69
    0x802c542401001c000c0b51500c01d40c10a8240070010003030036402071380343c03100d13a1034292004904203a003005007140c00304181c0007065044001c4d01a64074043c140402a450344234010b081200b070202100e02c20380705ca25490391540704002c1103801e2803081c208a034001404401c0080c61541c400142140c0ba400c00050401c0440385146000d40c0011003160030344c0c4000741c4074040c00481420721000f000e00a0080c422480c20001c0300303c0d1190041c01c001d201c05070813407044045649006241e9a03154401500f82c16014803813491a45007103078401482e020354030700608001051000e5090682d060f00010101081c0201300444800c803242115400c500c400d4024a0910b070710001c1442c070001128175100054849092010050854080391034440c07040d5030143e420040111400b8a030008103420303003105a140c051f41083d510500310074428030702c0401d00e410112540b28880030491000d41e80c00b40c65154203030740e40c2c600341400c0788000e6441a6002c007084c102046680381075402010300005000580b203c4503500d0380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934032805 1250 934031555 934031557
    0x60e0402060a17010b04050316060f0c060e01020f18150a0c0510060306050f090109020f01121b0906030e0c06070b0405121602010e09190203062206030302011112070507020114 77
    0x3281405d000040401c12450304001034031040300c111034005e00803854808041c104400c40e14014091140082e002d60600201e5407210b074510301c03084001e540c4c0d040507401c00d80556102d001822098080c1080e410207909140d62644480e21f100311035036103080341251050f900150b50304000c480c184286138114000b200c02e40100c0780110721506000c60b040c2441030b044c00c40c201c402440c200007680f514655101580e6210303411b80c8014020300700501840d080d1550078028100106078070b1208064a203c09291175440500301d812500d00d5581048041c1c3c5900d02903807503080c03d945e050781c000000d200310004108908500c5070828400c204541011a00030601035454100120703054401c1c1021440d001596000180c40345551000c82d64144189006000c0c4480480110043c01100340c3c0400090015110440c04000804010f2200c0f1b100c4086ca10750040070b840381c0c1c00200c00650034441e24094425810040d42c50303d050354181c0740a2641e030720004407416080403806a0400c500300603000002e0034460 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934034055 1250 934032805 934032809
    0x509010909032f01181703070212090a09090c090e011404060c0203161a01050103090f03080a0b060f041d060a0b0708120910060b0a0207060810030501061706010504060e0402060a1701 80
    0x40d045800e041700c40c102600843c03040701024100420070070800800c1d42e0f010172075105a031002548542c440c500b40000c5140765440c0c0c1c0180a110380380911040a00409104079401c40351010010302030006d03200e00d02c5080e17440451440b104c1c2c48804010070000794091704048212505441201e0500c0e10f00125901c5040025500351392032091a951000b03140c0d00c3c20402030140100b1f00302804507091641d546410074180c518040d0400074040003240c90780c4081d0b000380241d540010b04aa0b11100c08900d4182c4541c8680f0845d0349202110741103201100103807503082e108007801420a800c3e0303443c1c000004e6165000d81800c95280784100300107400c510541c071a9501407040c950090900d101c600da6144c0071521590031041c1c070003d041c4007a451050780003c4070402d444c660300e444841a11800881e16480383e81d90030007000707942004408036042541e600c0913641007070780008030381283c1d1341c0f00103110480f0340f50700400070009080c00004025050040003444d034105581740c207140d00c20a11888105138142a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934035305 1250 934034055 934034081
    0x10b03030c1e25140303031311030f0706031d0d02070b07080d020301180b0a2d120506060108150109090c2d090923130503040303090509010909032f01 66
    0x10005012009402c144d4241441054000f0351460130000c0e440c400c03800c2c002d180101003503020300020103584c6090240d5128001d401084900b0580ca409016000d01849624104a0700c0c1e00780006c00c0780c880010720191078407103c1c1c02038000c0d14104001807019034050781d41904c442da0f00f00403c5640f40d500d880254001c00901d200c0102004400c41004141c8000aa041d0701c1101c1d5500280510f01009100800400c0400d1b61001880308035080c0100801a5a0122441040c8035071500c051142c007050262007400c00741d880c81c625079504513007160070008200140d800209508010300110310950f008800c0c0d0042405c00760070402002c280001d54a0b40d401d440740d0802d41411401e181e0503040036104000d0a01e0a80174824417030107914540320b002007080840e8080e1680c1000c0b03810003e507103030051400e50300142a00c0d40d8a46900340545040c009105803409480000000183c92401344140e84041303516554108151401c001181c03c02a590300d04012008804420020182000d00c20300d81e4403125 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934036555 1250 934035305 934035373
    0x9150918090312010e0702060a0b010c0501050a0203040c05030a0b0c0711091603050603012a0e0909061005011b2402040611010605100206130303090b0901090203010b03030c1e 77
    0x3c110400c1c0303a5810182d10200c2400240002d00112075004600d490307008616847c0003603800030960040342c0808140350003074015441c01c014070581d02007540081d4455801202c404807201d41e14424156140c0d803100f0301420f03c0c80388c070780071031043c056840c0249552030068280e8418401020001007100f08250b90719103030340b50160700400005406000b0036a105000310000c001d450800345420040c800c1d0103c0e004028401540703002020ba001d030b84804202c1e2800f40c000d15851a0038050142d441c0300c01e585a01d40c446c00b606002940e0762141200032800c1c0040940e00c10403415a50710803146011080d20542d000300c01c601e070804654038034405000107110a549811f0365a59211444e806c4558941119000710300721070100e1070701d0f500010341c02d81003140c00341d92400c84407460404030b008281100d00100958100700c14020040700542101c0041c9002314000c00a85004400b010303501e12911452072000d8200100b280020650b1109554145c040078054410320284c6080c0045188060399035461304103a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934037805 1250 934036555 934036567
    0x51b0c040e0a112b05071703041403122512030b09090708030307080c0c070b0c0c010306030b06060d02120403020a050d080709091d0a080a1202091509180903 69
    0x42546401c501003060700d04065201d02008003031081c2040219940c0c2c10b1104c07280b000c0420408006510041c07014420300d20f4810a8600c80c152a81e00030f00c1048511000540302c0c00c4103140101d000f9a00d05004c82c0b41524214481d0440480a141080c12a584004c04942507000c034410340f0a845441d00c03155400500900020300300480030b240a0081a00e552140106000507040042169081050f40c01e100d06140e0700e10b0a02c4c10284200041c02080d070080c84400168010890301500c0260711040c15111012088001142207804a2001410f40300b022808208a4140320340103040c1c10008a5000d03141042d0444980404c020640382280140d00240cbc202040c00000d102d100c01034410341c940343c0703058140160010040341050103102c002c40c2d9510401c64801c0202c010b0b245441ca440f8050f2400641030781401707003d0b50400402c00f000724801e0414600c028a6500c221000d07008000c1074075034000600c4a94100a030042c45039a508060b620b030180d500d013001c1c0c07003500303219200000003145d03280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934039055 1250 934037805 934037813
    0x3151030060f0b0f0318030d0c0e01020309011d040b090405070815040f06180b1008071203090924180b0607020108160212160203150403051b0c040e0a 66
    0x354050740b01030000c2d15008024000341411508503030810000111381510303500d07040ca40424141c0d6401030710055101c00140c54901680d2074100b540031b1151510f461440440120041e41c0702d100e505001e038002014242140751200b070201d0f2041d00c3c000e01030300000b05000d654022071403100d810f41e0306540d03a40c8071100c204190343c130400043d000c070340445007825114203080d9130b070052444030948010205ea0b1144c60351a00f001034449040c20194201e0140f40c41e508007040703004070080ca1409050700d280580c0201080c2f100d51500d0350003840c0d5040d601c42d0140d51403e03042d20001d100c41010500441803011040c4010720501110740301034500b0791800b01d08100000c44442c11582c1d1070107043e01681e014004080543e801c0a0400d030f0100065012180c044580c0108034140365211103e1b01e4141e0020a0b41e940041481130140000c610a9003140c2c40c2c0042c0301c18911559a0480d03000f40002c000b0003ea90392282c50a07800307a1081c2c0c011045840c0c4c01c402c1b00004080c7d40c08103c0030030710360b402211200140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934040305 1250 934039055 934039061
    0xe130b03250609030317040512030a0f0b0a0803040e06060706060e150409080a0309050a0219080606092208120127061815050306101a03151030 63
    0x7072180d400c16803032444c5140d401500d00d034208540d0056201d9000005802c5c07110500c10b01169400301605a83d680c54514016001860b450014004107403500308001c0d403900300012a442540c141c01c006504080c41c2003109914400024200c070b07048002403221000003901ca010304005002011100046450101120f0604459140b24588154245580c603000310398280c0403902034074410f00e0007160041040c101249000c0e00024025000514070009109410300d5025050036140c08105455a0303031102410040815425260761084080f002440d4482c800d07403003500c00449200344121401c08078034006100c0b00c01310076841a0480740c0c500320070680c2a40444810040e02c841c20030200321044c01c0003a594038002300000051121030343d07200300303412142001240000800f0010100c0d50a86029080401042d40e41d12034003a5041200d4000307210f01101c10706581c03240008000200c400300b42102001400003424401c4800d000d045000b40c1041907a500e2815158401c840c0f401d50600e24070f5240d6012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934041555 1250 934040305 934040309
    0x1309050f0c060403060b04020714011b0315050d0c081b01030c020307032a0b0103062a1e20060403020d0e0f1e060309010e0d0804030e130b0325 63
    0x329082030542184aa891030180c4003542d400c5140044d81c4071030940410000e10585401412401019143d1001003038150070a091440c20352503085a440790100c0160160740c040700d500000000c240d02d090080c0d0400910f1021b07514061550300d05078075610314040e0b003465441c0c95925120042c60403906001e50f00b41c0605001d40c2c0c0c151006620307203030300d0341c6008114068100906840b19101801c100d14105030710b130749005007600030005030055690f91500000802c00c43c110000b51404c1500c0070084d14000403004101c551158a0391180603040d0806448122610071000060004e036400c0704003100d02c60750a00c2d400c01000c0c0c00030031060526060181c500a400d6004800700421a5a00030050b19151a402e0700504190344040040110504003444a03448078142c941251000c010083d8020301500a2108222100103641d07000307411410840c1c030f00030100e5010340440d14403900c0f0115414001280c80407801030020004480340c41d44002410800308061811480721901c02400a00c0051440f80340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934042805 1250 934041555 934041583
    0x6151a04350115050901150e01030b100302030603120306090f0c0d02030403020c0312030915091903121a100e0301240f0806012909030109142406040c0e130905 70
    0x1e600d4940d18500c00c5400d41f031a03404018040b9401150350b4002e80105260030700082c602558500302c4a0010002e4204a030301078031a20a4800320b051245407041206e01641028000c101c003662101014040c0034800f4101c030400301400c00c0942e0400007944051030140d4031035406003e07042d041c403040600e08a4101c1c010b400c2164200280130341003200107101e0596100c03032258104151b581c034044a0400c071410600842006500028000b050b80c0240041300c0711740101401c0050500040000401401d98003a0036003003030303c00030b504410078091041c079016642c0080c0045214420102c01c074201c10760b0300da00d41410300f80e071840510060308510f4018002d0129040102581c2d072501c1102140340740000c100045401e000069940030000003c100c803104400980240203c0190b850540040341c41c01c020800c00c2c0c01222043c1c180c0d8446e0b141c1c0c0c0b40303641e51071030a000456140d50301000024555a6440e005016200c0c90010864688145030150064081030000c1d03501101e080c8682801c45c0c04a801c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934044055 1250 934042805 934042819
    0xf1a040f170606010e090a0b030c040f05010e1b03040803131a09010e0a0b0c0a050712050405280918061e05180a0b0a1806151a0435011505 61
    0xa1b07107480020b00d0b072101070709601290170070a100100b81082c80031044142c0042c103244442d11440d11a4000a040b02c1300e140d61402c640d41c03015003405840400c03000314100f188041001c20042840c0b00c01841d041107495521301e07201906551055842c44002c81e200c21b075412044100b1491000a2280034100c0c03d0b25400307055581403950301c4241c41c01000704504441100800c1e01480315110b413064440c00d5078044003e06c0c10483c01c4001501c1604544180c52207045010b03810055002c0441c1d64416200020316080605c90828007504042e1404417004030314064004d004e0004112039005403004c40178052403445002403904030940a6440060004d501d0959150155003e088001020480181c00800e0344040c0e8858005401c0134040a00c0c0281055121032014802d0140c4e070760141c0d80d080088071a140a05587e150744441804c842c8003482c0c0c040c1824002000500546621429040020481804c1d034a80c22800550061100b0b00040c035141c1d500c2e00020750124207c2c14141c00b406045030f0308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934045305 1250 934044055 934044077
    0xf120c19081816030c0626130503030a050f010b12130305190c0c0e0c0703030e1c05120a1518110412260910021203011e050a0f1a040f17060601 63
    0x107600d40650b03513010290b083d40c1f40f4001502c2d0b4818642550303422a48030081c2c03a941e09001440310042c1005484400c2c19070708010000034405227540c1100e9682085c0032480240355038429072080c541401c820254244081007098030103c80c02c4120002d40d0304442c0e180c2000d48216800c1410703404903140c00442d100b800710340230b012000c19001c09440a903541480c004ca19401c80b508800c0c100f01c0901611100c2074440c83c1522210b5400101900450440f888054195500c40c51030b581034560b0b91036000c4842120f6881844850a07901c0c1003860000c509801050b144040c01c1c004004d40d00075401501661700c0c3c508070341c00f00040c44185807850142c0e0800c801c0c00850410741c0074401c4c4200507c2c0c0e8400c0f42c4414840e0300060007270200c0d9030002000344145849607510500545041c0c03041c4041c1500b03014030304000c1030524140c4a00010786409200c9025a941040da40c41600117640c62400150181488006940108000110003500c2c012901c00355010b0303034071442450094043d0000741440701909038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934046555 1250 934045305 934045337
    0xc041b0905040b0312070807120c0312090309050d0501110d0518060405121602090a0c03140c040306020c0313030f02040b0429060c01020f120c19081816030c06 70
    0x740c40c00380c800517034071940d52500c44c030300006580301d00c1038010f140e01040c284140b07443d0b8118102503030b80d500036141c0a40c1d02201c05425402c403056108010301240e01c914041c4001c2c205581e03620841d5100318000200500c5008003c3d07455001404200d107031684600800940daa18000111084030a4000501880c140b9980309501c0d80b0082d80e006041d00c8022410442d110314440143c80e8164000e13101341c09d2418400d00e900302034100c14002c000403a0400d184d03c2507415004521520035071310703043c4076414203086948000180d4000e801040480c4002d02418842d942c1402d07103080214842c90f1800c000c01120b105000584480c04138091090345031a01032100200ea0a0310a0710070740080d50300c0240020400e00144c2c550043c22407601c2c443d840402d2001060312410000e010000384409042c503d0780c3c030030b200d0f00c82e203200314404140b80f00008480e01029501400146e41c009100c1580c941c5085070f03049070203160881c04201c20010b5607242004100703010003840e01c00050810b41c5030030340d403156031f8101c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934047805 1250 934046555 934046563
    0xf0501170d090b03150d0f0f021507030504050d0303151706010905060d02010f0212180f0402030c070b0615071b06080106020705060d061a0403031725020c041b0905040b03 75
    0x2002d00c034103120179442c2a03201d070740300841982c08030b50003200700341c0509180c1080300960a00d01d908a00512460301042204101c0e5816140c107540e043e941d0714505030812040c81646401c4040460038580c840d490300084a800c41c0c6400c4c058400c007200e14a02c0e10190310005d1078081c06a001c902c00501e000c00b07101c440c1d10745410703600d0016020309000400060541e000c03460700c1d0a00141c00d184000c0800d01042400c542294868142c1c0c040700d0706c0301060351340030402c0200d100c01d40b1000b040440c01c02c02c20f4002065070102b00c0e8000f078010300450070700030b03140140d05c070b10f5010603821101c87c1c001000d00c101070880140c00c07902a00b200e182042040d814030030040e61b569401d002c1c09219060210b00100c0e1160290000000350101c00c00d00e8940c421204400101d0382c01038041200403401c0c804100c005c80e450780702100e00c1175182850300c003100784410b00600c139000b10500313450045000e0042d000c4629140d41c09440b0240d002d9035000200341c0380101c001011405117810281c0310300d0404d400e8564aa81c002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934049055 1250 934047805 934047811
    0x607020904141635010f020903070f0e190b04050411011d0a052209051c02010c0813020d30051e2a07030c14030a06020d0f0501170d090b03 61
    0xb4205061107440d0b82005007441800c03034813942c0c407582003100c820701e601c02680260031101e8059080ba00f2042d210030615922445500501c80300c0120980012002c600001f00285c80074074a010000700310045c1c0300850180e80301100c09a131141041d1980d001c04d542d01013400c0043e50f172440c1c20303103003910f43d2100080c40c2104c1600c40c25114001403052503101e83c149005c41202e013161100d041007445198a013141d01d4030b80d8106003903d0688040c040a24180c010300804030766145030b5844081c61b035140456440640344008007a6040303a040b81120b0002030001c842142092103c03120701c000a1201224005030203c1803046a08211091103059181c06681c050080641010084591110400e401c03462692000510103e14803ca00c2002022100045140010303a4041c1c10f501c4008c4e9292650070a22030850300725160540d009032604000f20b01c999000e000c400c07403111000b00780d10603100c88039015078100780c102a1441840b40303000c0000500411904000b8441800e0042c032252038a026126603001c02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934050305 1250 934049055 934049099
    0x801080a0b0c0f0408011506031b0c030507031707030e010b030708030d0b0d0f0b090111030415110417030423031c0e060c100c021b01030b06070209041416 68
    0x1160f441c0d08811204103031406808500001c010700035040c0f04082440c4071390f128040100e0f00d00000080b41c132583d60005840e4031215115481e03070281c10f66003164264030030f003829810400e100251082808030030310890f00440c45a41c0c0862221500d283c41400c58050040c450b101e40d000882c03c000420001c81580c01c2c0344a01c40300020400038083c0420851050031000811145242d01d0320410400c400306118002d9407140002c200905074040c0b032400034402980d0207400440004c03400418090141c01501c2c0440e042052541042e80e1140e41000701c0c02c0103505030b14660008103090014920103440301880e25011000c68440704500c2010030740300c2107146000c04e0b940c900151100c010784d004044620800318040d1095589054941c2480d80754144010380091141c280340300950100d2002402c1025014000a494400e1b84035900540c01400e0689107d500000c00340110005661062541d80c0709500418215000c002c07014140c0742002140340071044001c2d01c032071081c442403404916544101e0b5503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934051555 1250 934050305 934050307
    0x10206070e030a170d0c090f030311030c0106031406011202010527030105100306050a0c0e060a090321080f0103020619090312050712170a05070c0219080d03021e0a05130807060801080a0b0c 83
    0x458602070a5104101c500d005640c01c001c000010008043c91d50302c00c44241400356032259032240c0381040300b40040000640040c00500010001c10810011485009180651542d100000001103030a44e40e0489482d046061092000c201384000350103040d40c00040c04200b0014540c100a0242c40300d8500b80300c0b940241c4000c1900c00d081401341804034069604105010000019005101c404907000c4820307100050000000c120324480120b81c05058940c02005241840b80c00482c1034690b0709050a5102000010600000410b08520188510158070303a40d60f544d50582c0d0411904910140401c07a08006504600c008500110010180c0003406010085440e8581c000111810410401d0196105202e81001c200d110219410801240c0e4400c090b41c40900e0021001e4049000d00e081c91413140f5034030b041900d03120707510b04000d02683c145404c0442c00c0103500801000b10070040d030000b0b285039108003818460b0a4010b0344071401000c01200070300c3d40307108a60756030580000190013101c400314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934052805 1250 934051555 934051577
    0x1137050324030708070b03010f090c0f032316172206090b09060709090b240f07060b040f0e03090409020105041502011a030606010206070e030a170d0c090f0303 70
    0x2d01403021200402c9030104855005803203c80641555200780b160341101008414001000101800f07011004007842d260102500d1038404290090510005000074110100d03110b411020b401d05050360054000042414628006030b401034035004403807030b141c0d441505e60000c2200844506001c0d8501c0b41590340b80c011141d806190100190aa00380e00a000b09a0b250400c00c0020380004e1241c422485a81c901c0c0d1011303520320307040e4200d440800c0350540101000b449604021004d90035140200c0040d204c0300e00e0a0881001d90701180c0100d14200c44440c0c41c0d03145807084d0b00d402e0082203072024800390100f00c0780c1aa075071029682e105840140f405183c031160114107680c018800c0e5002041c60000d01013030380c01150300c000d00800c1e54001a03040c01100314003e49060030002a814462601a001007100d500e80c2002594501400c00900b580741c8074443d4a01c4c00508a1040c1607280580c80110302e0f10380d00ca669002e01502c4582c00584200104d08004204103000d405109040301c1d00b50900303002c201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934054055 1250 934052805 934052809
    0x20d02060f0708091e093112030506040501180b0303070203030c0303040b1501081609080706090602011103130f0f0f210206090709020903030d0e07030c0915091137050324 75
    0x40c1040c584242007d480b00d22210521030030962140c82100e055504208942e01c0343e0400040f1502805000070841c0148000c0902075895070007040f09410040449007044180e50010313145034400340039503003503070004802d10007007100380c0c66005d03007103c2000000300700209400002001c01100070403248a80c440c11340c00d1070700280603034454070151040d0402d5071005a26120047c0540005100329001986004204030729100c9580689015842c01103002e1207205041c1c07101030300c090b215213082d40c10b441c3c40741c4124006038079440344901840c401c1001e01100c2e2004642900c1d40055040104259001842081403003400802d0100c1510b18a5a00588414800d00401e1650092010100d0b101c2d2910810441c200c40c0003901c43c00316407180c2c51101d189510340600e41c040e100303400d9002150b11881035042c80b06c10b81540001c41c18114210a0b94140048001d04001140e9150b440802c007000c2c40d440015800c0c00355a0011603031b00b103070521514600340080c582c0c0380001110241e2001c080c0c4101070b59426 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934055305 1250 934054055 934054111
    0x61b120a150305010509100b03032b020403050106031a0f041709060f09150f0f090103090812070f050403020d0b0604060b0408100b0f010507020d02060f0708091e09 72
    0x5075180c00001c201ca1512460410f000300b07025900703140b107440f03244540e2002d01c100d03010303c3c803007030030082c000d181000c4404801c02c0c520234102507401032030300c8a00440c0150b0250b030700c0504000e5000d40008076082c0e196090036100050710765040b66800c00d5035010031501c5260140220b40246c0d03c00301c00380c0c010b10f02d0019016a03024910486900100020700b6900482001d00500b4040d07900722403009404040402042c00351123109200b840400050000c15921031101c40900304402d010f0501103a08400c0da82c0e41a1135a02c100d41c40f4030080c4012023844001c0e540500002d0700301c20341d81400780c81c103405e5800140300300c141c455000744100c0c0b07030400103a40c0d40ca55802450003018511001512030b40c40d01070b01d80e200e150007405a4181880d0401400983c81e01c002c05043c0604183c56962031302c84280c0a00000c40b202e0102030703030421000c111214103005518000c1600034042ca101ea606d91003440300b0001c0d800d03502d0040004102c8551404122a5110a0aa50030102d000c80400b9a501444e10301010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934056555 1250 934055305 934055321
    0x60310182f031f051215010e07020d140f2209021312110607050d08090303160e0f1509120a0b060d030c1b090f1b0507080d0903050c061b120a 62
    0x8420780045480c1e100001d0b02a00111b1020a03d1616a80390803049a401004840c44401a80310300c4030103036103034060b441608801c0390b03888141d4501182401c1c40c071440d500152084906c610084000907282284099001c09001120001e46c5054420751440c115260b107809050b50051001600108009001865110b9118040c00075901d0b80c0903030500540701e403440f81c0c074030340072981c1d1000048156802000b00c074841c00b0031000c8156251a4103104903546200c00468540104e0b0781c02c03152a10f651080b101d0710a40105004566991200ca0300348650561044901c0c0d000354803015220000034040403140382c3c000010340f804d0000301081c2c2000c0310700480c0200003601d4494801c04d4800300d074611070036080545100c0c0c90140b05103085401c5000c11205040581103000000e64084080203104500403d120380c040e0184504020003414071404960711002d088020480004590b1020b010901041e64004030a4010900c4220280c0072200103105200495107250211000107a0000d9940d002c490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934057805 1250 934056555 934056559
    0x213090501030b07201e0c09040b070f020102120a0b210c09132a090e01020403030912080414061b06070219020f060310182f031f05 58
    0x104550b9241404920784206559070310004003003c1d0140c00d08801d02120740085002c443c020314407810301e060000c040d2900d00041085a02400407505429030310042480d0007580241070741c488508103280064a606050036003e030a40e4010300c0101204a9072003070880d400059450046510004400021031340b030701035244c0280425010645810b1071800203858000c00c801610b507404076807035032800803002c03456070310008210140d81c07050002c04142c10f02c0782400299500101c190402e0300c1d1610344041c0d81d640402041e00b80c1d80840d0410a00d60b0090b142001001800103090380310280b511139905600c150b010f4001d01c00c5030355809440136107030343d000c6403081c401c00300740d001c01402003089060b00d4075015035081d4014400c3c03a08240307042a1641408210940c01060400900307848414440300f80c10007032407a2038070341000e107001030703182d072030076403002003200300500c00183c0100701844071031021042c1100c0007a811000301c00b82030944c4c0446c1142c0c2c10103d41009500d68504140400c0f0481c907040d0485a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934059055 1250 934057805 934057811
    0x11704064106010509030307060f150801091b0f0e131203290117041a01030c0e154e0105130f0f030207050a0308030a1a010909021309 59
    0x44094012181e10000d6452018034010481d21880011106402a04079556260f08100704101c0000d440e680000d1104403102d20101c2d5058001e514091070f04480d60007522141d465000d064108828081081d07034140c403030340c40c0740480d03410a04142010a82c50091845800002c00851003900700441c108800c140d00504031440240b80c1d03000100a00064032000d071011401c0304074407610408070040b0b0b91100e103040c3e490380d0706464902201c220880b0302070000e4588410401c00c1049613214005014040e5002c0e04001c0303001440e1018142c1a03003001418080c400e110030281c209076646100014039200000815269240c07550540700c829071191031a12451606843c0c0c10303400d4008051050075038550000020072140d80c03514001820602c84c0080108011301c40c4460340c0000b40f0386100d00703001d036002c2d2044403801625540403a2005040341c00950b8081d902100f04022452a401b41c066004203001c0f410054211000010f02340307500601032020007030380200d442402d102c05201c03d41d0040200c2d410034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934060305 1250 934059055 934059131
    0x3080c09060f0d0f201303020d06050601020607020307020a0302060c15010e190e0d08100e360a02060307210905060c0307090506030601140a080a0b01170406 69
    0x1a42e420781c4a403440150440c101140c06508041c1d1344600042521103110405104400e1840100c11350700180b680009500401e2010000d0f031901c1451806061107800c000600d400c009001a24048006104404550007000a41d0050711609108400c03a6415075019440e64900389030a0b04085280f0602c0c0361a90000c0000900301e421240e80600130b00000c07004004000d200003200e4180d4000140038001342d40008000181e00c0d2051035690b038444013040f44c82485d0b07601c8159070710908009440718502004900d0b401c02121500c02c48110504028020400605401d05100760b11000c1d101c2020307110302c0010000403400b60244007009003d40001d0b00c5040801000b00f0494000d0410707483c160748601c14040013941454040040301d0003425142c440301e100c9417501042003403e900050544d070410203101c0d103454124185e0400340405103840e8880e1001850200403901c111142c507881c00d410858a2205100d1051150b110139801513049807011803514107201c003226180300a00c12071907078440c02e0700c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934061555 1250 934060305 934060327
    0x30f180d032114060d021903030905130b0f0127030b010f0b0903100b0607061a04050c160f0609170406120501050117090a0209271903080c0906 63
    0x1000c68440005a0b00600003905101050444072607014454900340b00b01e0210b955032a01d140007101d081c0c8010804480b00081c1e000d00c0d0024210b1350701c2140414522a8148040c1c41c1c1401c050741075214503401000704510007070000b040c6900100240d810b004407c000c0c158a10354000000300c042140c41e50724400c035580c904d0308800b041001d216100368135000c0c20010030044440e00843d140010010000c0040300030010345100201003a00106501c09402c02101c00013448a0084004041400c1d80064810005105100a40308020302001500707504101c0180181e82c4000080c1806403c241c0907407002c4800e03d8030b60001c003103055019118540a080398030007481d014004100b07848907540e6841d51294203001d1002902d000307006041c042201d00c04045010b46008200b00d90100c42c0f80c00701e90065200350042254003105450900c0320100d840409803000300040b4802d001040d0600040125001001c44038005e28034114000701040060408101000300400c156031840b00010000c0d175032411303003060b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934062805 1250 934061555 934061567
    0x10c05070807030201110d0207030b07092318010602060a0207060f0207050309130b030309041e09120e220b03150c0721021203060a0305070b031f08030f180d03 70
    0xf2080340080d468040b1448404001f0460800307082e202d4008107080c5045036501c01c00075200415100c00c10000007800101001d100d1b0780070507000803880c4090102d1412100303010b440e042020705071003260041001003103055400283c080d4424911007005032900c1c52031400030301074400801d801c5442800450324000703000c07000c03008244400f8202d5102035003080c045a50415203d4242d4200d90541003407104c9407190920350041810301f019064000d03424850f61140340100c581d418400d680c469482002101a00e40000401e5480f180c101e80e00b6101001035500f0010741c0e403403d440602100d0b110400060340f41c5041140000041d14101c03440c40c140fa0088d54003c542d003100700195103003011705000407290b8116100142c003800065000d401e20003001280400c10303903c00f030005c0780c01a80503000080458804e000c402c02600070259911390324200002c000c0c80c0141013001c403003500c030040c04003044403460020031106a0011001415110007100015404900c5180c0015402c00d682039041403c059100ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934064055 1250 934062805 934062809
    0xc21030705011a0d051002070231060f1a0d1e05041106070f030e190605030108010509010501180c0201180f0203012901031e0c1d0f01080601030902010c05070807 71
    0x83c01d0619100144080155038041d852028260750469946a124020b041d0000e00c082400941100b0320720080c081c281100360309084094807007200103919511443c2c00b074080c240050030a44801c21700c10303040c0001c059a10450110807060100000707030300c201c900070581000c0c45100012800390040700204000c4000f0f0501114111156103642d4502d80b080c0c507004080c7c441e0542c11440f403e51615080c0d0301580c050300411150340e48054005107201c0c0031a074907103079940500115612652039514250881d800c1d0b81d4081d10401c116410701c0b0043c0602e0b03d01004250068040b92000303d80c408603044140d0041101c4503078100d0000b03010b41010144507003030305035120052080d00200400c64615071244408040c03901c00c80300181c042c07480c810300b56200340c2001c1c00300f9400202c10001020381c4420102214403401600c00858186d20501c3e50400607495060542601501c101036582d880c40300081c00004010300d9241455900c410300015648a4405375202903400404c5840d8551100c180381d503904018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934065305 1250 934064055 934064081
    0x1306030506010602030d061508060609040617010f05090d02120a090e04060b0111010c0e0409030311031617010b03040602030901020d1118120606010c1b0e010f050103020c0c2103070501 81
    0x210f1000a43c00c0030003623503040c071588503540d00c50140d00d0740c90401010798442e0601c0341d48580c6510010031407034070110354010881e5400000003950540400d00d9403c1d510014418031080d00300003001d0410310b07008201803c00c40403400003c1d50711307a52035034240d588085a422003500c0c07a1440c0c0c02c02080041961014240c0c0b6002d80f90000c001c10103032201ca091b81c06407844000010512a5128101c1c181a0810040284a4100414030000040c1e03030b6242d42e0011900721600c9041e403c200041e090304480e03141040c1348440b8100400f0360504298140d80d110181c401090f40e507001001601420082d416661034009540091000312080d07400d070704180c0c000c104401981048401a00d459140c01c0100c0e21000084001400103603446100540e5041c9002d141503a50046181030303800702001d00e2001c0320150a00e081400d0895050130000e200d104116005941450b02c10000304400ba503002801d601d80c10b50480e03030380003817080c855102c122801100c03007007008034030021461800704a01900856140c1e040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934066555 1250 934065305 934065311
    0x2401053606280f0e060d0210090306140a0e0312040803250f030e0a03141806160b0a02070b1519030605010509060a050105030a0c05042102210c1306030506010602030d 73
    0xc0c0c2c0c1e402c213a070090580e80e441e44080200c0150300141009403c8007074051603800c0c00f110f440d641e07032a02c100fa1100c02d60b1184805003080100903841c0342e82d00c250120841040c00841c2040c00d40c24526001d284054005400108040002941144006190056042c460b0a0b13002e070b40c915070a0142840380f8003c42c043c0070030704002c01001c904100181d00e001c0c441d0580d0303441b03000218a16a480996116003600309a43c464000d044d105a1a51802041c107201400070704d01d810314560810030745810010b442540c40c903004200150110381000c0380150040c2d240ca50711100300d65000002062040c0a100e00d04002001007000418000b1540c00310b412200143d400c20301d907940300c4081100040341805030710b02041c0c003400402c1c142c0100d5444007403248481c1c00e1003458251a00800840c00000314000b04128024250709070031801e040621204401520800080f000908107941e500c030035131020601d001d0354524008840c2d00085030007030380046403c031003500c0c802d5848500003922540201085005141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934067805 1250 934066555 934066559
    0x31205070b0609090d08190c05070c0e010b090f030709150e010b0a1e0c23010f0b090106030f0b04150f0605041505030403022401053606280f 62
    0x90002003e40710f224520040c0c00d108110001c2610410320203003c1801000440c800340f9041d411a1103040c0880c030454407a252070300118942005101090b4001da0f001c0c452800042003804601825199109002c840ca0042401d501010924050076a4850b00e4058204500348030380c042d440381c07010309a40c101458900e407aa29461507160500c5107814041c00036000d00614007800c0f503490148101c128180c54117218080d000c0c1c90f284010700c4200c8016101c903040401a84d1264801d2103189101c3c0c1031580c1c140203148c090300018407284130520030304052545503280740d50000d409072f10241c0d00d680000c0080100c00d45c4912201003a01044c080d0862034085106d0205089004d00150740132145642d0f040400050144001c446540000d40104c0640c415070214041381140c1a030748a801842521101130036602d4107040109104c0c465a0841c80d0040c1c1200349142c0102040c00080704001e50700e0b0f00c001503199070012500c0ca40c540110a0250080e40d9106540c84485420034002c50702840e5000e411a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934069055 1250 934067805 934067809
    0x4030e03160e1024030504030c3206101404060e09030901090e04050304140f040e011e0c0e041a03030f07060c050405100804170c06060a0602030705071a04031205070b06 74
    0x90400902a2101c18130081c041c181403181e04020b500920a142020130f4511a40d9889003000c2c1d00c44903020914881414048d000e009001c0c0d204d400d62540000700030504141b444c0501006880c040d000d44200720440340c2487d5111a00840003e140c0900740d96010300c2d01c2062240c480d081000d07028002000280000783c183d5420280f13a004d2a007100c007540c6050302c0c10351800400b402448803150003004c144410101542c55110301542d8160050000c45c1c0381d81c03000c0c2c014500d411221072162080d40b41155801902d540664a00e0030340d9001e5400040b515003090b00c50340c0801805c3e0b0329a505200c00181d1020b98488034000c0d029107031047e00e050250816040b4103440501841c043c4680007010300c2c1c102d0396030500c6242c181307070414041d043e14850f44034a4101c10074194005140754080e54001d41c02c0c82903c1c14104902d50060565102450901013550380d07107600c03915140700b000e10b01c0c8080b0310200880d9001c030b07080b01c0c0110350000303450740311050000000d4169000460f0544440e80c1c0720001648038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934070305 1250 934069055 934069079
    0xe030a1106060906090c07020d061b090e0118020f090402040f0315051b090f030616120e21040f0e0a0f0e0d1b050607020601030c14010804030e03160e10 67
    0x113540051043c0039030f035070f031801d03c450310303040f14605070b9000e10701c03056000100d41c00d03120300703181040b10921007802c45504079006040310887c0e074007130140030349218010095092140601000c403001024090b0366030b1030701117015000d0700030182c40c95405440020005041207002d8205000c0741e118410003088903d00b100300e44120703101100d000c1d140d81d40d81a50340d03030000c910000415441e4001007106200001c8040401e1800300d04413065024084400420403426400c6000c60042c0301144c001131200c030f40c0c1842200e0300e4680e035001813a034400901c001300b82801a00c0c0282c5001c5c20790718803030031340381580c8883c81c54404c001955501d80316032415090400124141c014070040b00c100c9001001001c0501d003084407014603000352154901c40f40b07100c40e80040d40a009007030007441c0a030b0085c062941581450142840207038044c500c008101d9180394083d90b046a2182e6209805040040e03083c030305003020906140000d00d04041c240303c00000440c020000c20089409003204904502000b6200c0b0582c90749 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934071555 1250 934070305 934070311
    0x1140d0212011211060f071b140402030610080910150e06121218031c0314010e1306060e07020105100b1204020d02031203040b070e10120504060e030a11060609 70
    0x50100a4801e030780c0d42018170040004100f4501d40501c0c00d100c42c0c41d07045420350a02000f00d00150101ea04101c4040118511400f01d8001c4600314a1418034100003270003458040201d50034440d540000890601e001c0c014807001e050701c400184481d40300c0382d0807110300300154091080300c110f0902c041151828150307a100203141c160740052140e400e010025081c0717038010115121101d003202c0c1703640c00703075440c00e1202c0c2161080307450300000524103212016007030700c1c8008002c80301d8503a000010018005d000702400d40000c050081e03802e42c2c2d4170300d0038150040c01c45034000100307600a16060096860741540801e2241901401da107140b1502c0e01443c00c8a8820340c0d8101e40c01e040c442c00070501610304060b1300d0700c1d1503100900f10b900f81340d0300084018040d002124207507104c1c240324040000143e044449040c01e00030443c3c4211044500d101d010745074003007031601d40b40d00c583e0b15000501046200d50000c0c180d01d402c103080b240c407050082d40081a40d103101c0e0900c0940d0158002180c0c4608003881da840c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934072805 1250 934071555 934071563
    0xf04020a1202330a090e0703020705070b0d1b0f0210112b0c20150123030715020f0f0303060d0503120c0405030d02070806070302070201140d02120112 66
    0x507440f00034181d038001c440794244007119509075070b100311040b5001e00080c1a40041500c902224034074068000210043c02016071040c1401000032000091000c82c0001c2606c496064483d11680e500200200411946a07861803000c140d80481e041c568100c806142da07000141c0c03c843c80007001c0c40703510003070362400d00503140e91030307010701c45070300d12112543e00003003103000d01500d50620260030300201042e100c48013220404949108600210100c940c084840c24428840c014445170b265130303000110010051062a1f0b400c0d581402c14107102e8a044001c04250300c000f0304868886482d0200d072102507032181c4226015100d000c1c8600b41340040030034110120601140514150303958041400f441d08000074007110240401c01404149100800750f05000340b007031104241c0c0395420407043c11314001201c0102025548985801c000000002441030391190441ca4056224505032005030b60f1000f545182800c40c08002c2110b6034003030300035400713840056904100e00f012660713204041d59440542d004050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934074055 1250 934072805 934072819
    0x4030537030e0c040b12060c04080d050405090a09031211090f0306010e070f05130f05041404120302090609120102071b03050604030320031602060115050414180f04020a1202 76
    0x1680f107140c40d91050500070303c0541110b420110002200d401e0002c11a84500c41400225007031101d4141000140b003070381903901f0b110b80b42500b0070001590302c0600400a041190b03c03031042004051240000e040041c035281e8050010003600036825005800c2042030034050030307102e44224102c0c900080c0c40750481d01e42024400064076034860840705000124200402d0102c208102a21032030114400301c024001240106051410302c0704000945200b200c0394201185130708140004998240c101ca40e404c4003c5c1801603541c80b0081c04150303940640c24069601c0783c2e03c1c0140b406005410b4009012441c811071264500d0701081c2190a8032140307501004c0d200341c1c8204005400240170390300c039004000000d0300182c001c41d2040c8044009600807a920070f0041d442140320310740750741c040020783e0160600785903040b90481842c400030030301c0c09544034016038080011140c03215a22036042b2a85800c1681110451a10700303404c50010311030003610704900a1150382000103c170840c0d034210b1456035600070035003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934075305 1250 934074055 934074073
    0x103021009143015060103051501120e25080f07060c0c051c02180c0f0702241201050f090406020702010315060c05190f080304030537030e 61
    0x4841004081c58408244403c2e50070b201d04003909188140d41c444640d0001040f80e450480840c00b21072034064481030600d41000280800401100e5440c20043e03828030f01070701e005000d80d176050050040700560400c0c0c1d000d01482021013501c2400400c440000c4612030308455980c40c502640ea52940390004c8140c0e030001d002c01c0c40010300c01d01c469402c80b4010f000c2201c82c692540002541c543d468040c003090384604946050460801034030500e801002c584090801c2e142400d07250410f0300c25481141001c6d0800100042150b440708003118101001a0f4050b1151000c008007520682c05070084e15407080d41040000369030310f8400035070340041c1c2002d0106400d984a41e03031818065041520201d041c15140d12480c46138410b42481c02c0000c10440c2d03600302c1303c000719092031818102000300e035800c4e80c9921002c200110f02c3c400c0150280359841004503a581c5e50b1400c04452a0140015440b42c0c111200281d0800c94102c0301e40051002c1d1058040c04030390080803054007169941c02c0250b83d150495464 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934076555 1250 934075305 934075309
    0x6080606040528180606020d0c020109120f1b050a090903020a0209042f0112150b0304030207090e100506040c0c06150e0405010507140a0203030c0d060504020c06010302100914 77
    0x280c0c1904042a902d51104030ba243d5a1500400c04c4010464844503070b5041c1c108442581003202d2114007895090601c01d0b5800e42d00001c000c107090b07014480b1850042e00700e240812002108481a00b81c02041204101d004508129a00d035521310404e07105500040c00801c011401d8865600001e41c141c0090914050640c05c0c4000042e005000f03407040001d004014070102110101406107511102c0b4601c541c540880002d003656070300301d42c0300d00308600c0c001c03400c6030030740240f0007050a451541110684030365442c60100d00d0105d4603080354076914141000790245400c001080740300d0042c012001e02041d40c0710400c3c80100d40c180014480050f481c40449000300c1d0040e80040c601110701c0700800300c0d5644820079500c50840c01d0742d003254581c4d540d01c00c1040aa070f02c0030702041003441c06d2141070720b40f08030400025540d00004d17207810106000001e40510104565014800900c4050801c1d92220500019162036000034401680201e81101d0451240761003020001c0607600344e034030f502c05400c50101c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934077805 1250 934076555 934076599
    0x3110a2a170d2d0801031e051e01230906072a15060605040503010516120506010903020d060c03050109231e010806070e100c0308042109060806060405 66
    0x710142d540109202d450581030f0244090312001c046403100966540b4510300307200a0402c100030032042c040b000c1d10250018502040300201002e94041c948840441c4074070250041402c8000c400080036070307041000c115041c40990502c070f864110280c841030b541e80001603038120300708450304d00a1301c18030504840c20284c0b0040006007030301452034000307584507031071011044446a800c04408914041020001880c1c2401496881681c1c501400380d4020901e0000d400d01002d0510340d001603454800165003644500c260a005540040600302c0150842c100b601c020070700000c413072000904280000c1021360450090f2040e0a655600d1948020103c5000d43c0c200381000d40012610302011440d26026520880d02c0d90213090003101a09081c1040c80001d8160b0500003c00343c00b4103c0442c615107420742154100e03400c1905410610301030354442c03804180328018005a0343c2c8065003100384403049544001c0740300070390340f0741e48070251242c0340c020070440b41d406584202c0b40d02c0410b85140e42d00710a8000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934079055 1250 934077805 934077827
    0xe0f011a18090a110a021b06040308070305030a0e030d0507120c02120c150a020a120603020607021c050a0b070e0f1e01021e0c0907110a03110a2a170d 66
    0x1d0300160461200055202c160302c1726095400680c00700b00411604a001d0a640716486012141d203490249180ea50008034010102c0c06002d0204c04800180040b41940100303209000c04030640b03070f855000111100040005952100c0060050683c2c90718240d9544201044d40c101c5400900e9155000b03110041d1a80c081c118140a50243c1120310110b4032000c450140144114540540c03110540800280300071000500c0180050601104001507203c20044881554055440c182102c9258203810310780c58000070f000744148607110380d420505c69103442c1103010316003c7d0b40d66146818040204441c002d00006400c1d80006040f80c0b6582d80c1c1c40b0b042402035400c0041c01030315480d0200c81c1c0e5551704058000074050701c0e508400e81e415030526007100555840704842c00c2040b4211007900c0312550310b22196800509122800709810310048080055412107540300c5040c101c1401000c8015a9114008082400d840000c01000c40c80c408004002100c90001030300800e0082170703040302240d201c5101c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934080305 1250 934079055 934079071
    0x33070c060f18050601030b0702070e010317042112021b040905010e060c0d060608090d080c0d11190309032a020d0308060f03010204050321040e0f011a1809 68
    0x10b200d0003104a82004001c140e2940110050601507156040c03903000741070000c20040464102d40014000d070419180c3d19415a500f00c1d06950000758041c103180300600c41c6400c40159000c0744007140047c800c2c100c903007846131480380c4a51200010001c80036a5078020030407810400c06001301904044c0d041a0f840001218051f600125031803064440840c18001c1c152450640c44800140003e024066805048005c140701e18110103140303040340281e510b4090310141c0004000442d004100e08400c184113890041c01c407800c08004400340c02c070742502690b104100c102240b4640c00d041d08240c0d4041d21030721210b203401d502d030310302e089212081d01100b40c09548600351004620707a90110160f111021584141442a12105420305200042068201c44440203030f100e60300400050000b61008164071000d0840e4440350100703050815021031240c02103410900c2405080000c02ca954400b40c00c0c6141203440104102088412014224031075120398044101516500e810b0314403c0e0031b1a20b012a0300c5210703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934081555 1250 934080305 934080311
    0x71a07051b1e0a11090c0301061214070e0306010909021c030908010f050a180210030209030c0d0501020702010924080a0b030703050f07080102033633070c060f 70
    0x190020340c24041c2100c007940e441039100300000f034204400e0030104c80402204440440041c40c1c4000584200e120501a00c01007002c00314018000c0034141d0440c4003e00395121090070145050b4400a0000121186040c800d01c111000040d0014139486054a90f540261040726016404000707a0700301006071000300d040012080c1c0000c0c5111082c03251101359008030310041860700b801588035003a5500240981101c17540142c1080059842d0700c51703000741e6020340c1000358540c0d0600b00081c0c10706a00050403500106481c03403040c104001075006000e040d200340c07a8201890348030403aa6981101d8046044241c0b030401074015140d5008090a41e40202a40c4011892101080100f81402000d0340104e030141d0240e05489a10981400900060903106000b1421032a02d40741e41c00e44c80f240c2d07413030403040c2283c0e081e1221640141100e282c1c00c0c1e0020b82c002c54001c401c840c03400900a19420b40c007140401d80f481220020311520482041c025001e66458140d02c00982e181c2c038004000300c1d480c100382d13155 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934082805 1250 934081555 934081573
    0x92419081911120c0711030d080a27051615050906070804230111010903081b040519060f0e0d0605180109030903120203090a030311030f0c03071a07051b 67
    0x42001d02034803d0403034001590f205c005610300301d804800000c1c1c241e0303c47e801800f45034010640c0415110780c8040d84e050003154285100082c0c002004120324900d203051034000401c001e01c80d0006501240b000d00c0c080050280c0e07030324a0000d030703045010b080c804002103040110074010300d07103407000d005908c0c020001e46281c070395116003440c0b04c628000e100710b140144c0756128010795a008440c8910312031290000740034500303107035400800d0450b00515880085502751402c0c004404908156006418060b0407a030b4100a90340880e40c0d407486510034040000c00030f882030a105481303480035911040e005482c40e0050205170f91800e0280c20001c00e1001900cac81c0d0441d00c207a13a030f030034010b881055019845106c2d1180c11810107551040100c240c01c419540304012421481d02d4034901c0d801261382501c0e15034012100342c4200350441c030621400da0414500483c0181c4204000f20003881198414514540380d072054269840044008030b034400d010030020311101c2e00811601d01107506221281303040d0b40f8114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934084055 1250 934082805 934082827
    0x20304050a15080606030606091e040c0c051c120b01030f0c110c090f010303080717071110050c040605090d02030709050612150c092419081911 63
    0x1c101d40e44000340079246000380031400c54004108a0700110f058402501d54640b10010507401d100f05d41c0154090041b4800c2c2880c11518407402800c29174004005110083e01e483d40180a403005110a80311b50150886036003c5101440041e2032a843c030362650540f0750242c51401e0010143e03600c01505140e2240c007070141002031480785080807115602d4001031400f520107028500800c4010302c5000b9102603051180d42c0400c13285141c11654503281c82c075180c0c3e45000c01110340f1000015001e009113040014070a000b41c2141030702c1400c03d18142140e241040c40f0204100743e4800360b07003096601c4020132043c0701107032140000f80961840a03203035404000013640806d1a10210703074841210340ba07407401844114a01100300c5c40380b464081c0c0c01010000401c1004018105001c1d080005601c0c0004139000d03580c8a5405100a045804001003807104414030101d0b590352120761030381040311103030010822140c09640801e0203000b07441080064106200301401c001e02100c0c00c1252091414409400c0c00e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934085305 1250 934084055 934084069
    0x1909172109010608071415030c040b0d0c0f030c080f061804120305060324070e04022d070c1206091e0507090902062b020a1d15040303050a02030405 65
    0x6031070080000503010f24040c41a07043c26040e401058403100c02c0109010b07250b9641d0488120503801c111b41d9940c1c1e0300d4144000c207052140e5800540180b102082c420007207243e0f540605c1800656444403100c481d4020000c42c00c4450441824000c14032490106104a203914900e55011401420000120b9640100303885281400c0382e044941a920f010100344544d03150280c16008802500102003503d558528421003d80c600c0c48083e040004900040d400d5102d9802810700d1040a002155500e01c41114408010b0103101e1302d207980b5034a075001c1805000c607002110403840d000442c2c04a0305041c000c0d03000a543d02600d060b202c0b9038a48080d00081018011f2407500582000d0b010f0400450700d182c034504205070383e0307c0083d410f441d016000016807111800c8903c403a0700401881c526a1152150f090380d4115401502c0ba014400302d84002d2264019401da480058102921032a0044200803c5840340d010710351042c12000070302041001a0191002d041185640d0050313038141034641000c0394072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934086555 1250 934085305 934085311
    0x1202070501020903120a0504031e06060810150812030c0c010e0f1606081501030f0f0b011407030c03050703021c1715060313060204080a0b19091721 65
    0x401e035800902075800e40360030071081d641c000344800014206011150301410300c0c082e52002820034014141e0b103007080d805050041030419405401006101c0d16020b4065442d0076042d00f5120080c98100340c166495400c1480604030741c3c81c035004000410071001c0d040900e4001a111803079640050122402c0c0300b01c20701230807504102420061402d01c0032261440d28205003000141c494881002d01481403c0c0e0040d00c459120615001c0100703882c5045004070300518244003c40034135443c0003484000300700316800c0742010301000da031011100fa4041e50038403040c1c840c0c09001070100d000c0080c40000240104003500c0924001e0054508101070401110f040d01d02c400340f6680090a0320011014000c610301440b600520f00364111100c109080000c610648005484001440d80e0710780e1110410159030104c40260000f881542c0c8103141300d140c0355562600c00e403018a249540b00341c200f003010403144079100d5503c1d00301d0344100e80100000d41c0d480c015800710380c080c1880b200004003141f000b0741c1d4501c0280 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934087805 1250 934086555 934086563
    0x1905060f040b0c060412031404020d0f0605101a0c03040e0423030712020c0d030806041e06060f17060f0604090e0a050705010e060409020310170706020d030501050d12120207 76
    0x452807a041ca42030a4100c2c0c0400c00c40185441c10f00610840840210589d610560590350520541c006080201500d0b40c2d4040040503541030a04100c2d0404001d0340d124215441c1d110541034405035208405028024400307071601a503c240020081084080b010f01e0700240141301030603145180c6c0d40d000b20301d080e840300c1c42c070748607400000c2035402c2066007400d580705a01c10f440604601c4404400041d020a030f1844007600704170304480402c0060751507600c018041040e40c5440741240203044110f2015021510451002c00c004000c401d01250180701e04d603100c01c607500c1400c001591508100000302400610298200b6001c0c400418981407501c102c41c0c2144040008061540c06850401d1501c1d20070b8100e1070400000701e0304035025464100030340c2d003610030a500141e2280e5036201101c0c10301c0d202c2e41c80821041e40300107004000400c080b070004150350b0b10380d00303481550468031001d5040c1d80f400c0c811280c11240c151018000300c1d0704000129100c6440d45000902e18502e11020703410f982000100792 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934089055 1250 934087805 934087813
    0x12030902030a060209010801060509210c040c020a020916141e070b041416060c1a0103080a09080613060c141305191a0d0e030f0408010b1905060f040b0c 67
    0x51740c80d038000400d02c0c01043c091424038500f541d41808121031080651001d40c010079a1240440c0210040c0900840000081c208200c080e0150078001d503607030f00c45107080c0d00901811001c110305c030200014240841000703072240b6100c10140310013060385031720014040710150b4018540c480440d500300c4c003c000c120b0085075585043d04081c148920702d00d4101440c44120307440580140000744451040d50215a00d50401c1c00a030034550420701e0001820003580304682401310004420848414042c1c00308c1540341ea03548d400d030b54a42030340316543d20064800320700c22100c940e900070018440b60004032541406280010000707492205502d60b6400000c44014034125007001488a41402c2480310311143c0080712502d000d030b1400c0c00414504800e14208404410001550142120240c011442028410007142e98408078400700e080b51390058029980c965003071060340e00045c50048640d44054105e1860742e4407040c0b800b0100500e03640300352807001d4860340038803000503d200110054062400f81c0c0c0007130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934090305 1250 934089055 934089067
    0x60112030215040317090a0b0115030605100305070f030b030606270a1a0303070b010e04050f0d080a0e061519050d0c050f100e060d09081308010c020a02060712030902030a0602 77
    0x300031445c002081484150b200800803001f14501d40c4005044403003501030750050340071100d021405040c2135048075030040410740707428900c1549a80030500c50000d030340d034203484a60081c404a050f20b5603501070aa240d4006c001250152420f2140403620100104c4004501e200c40d102d200d13424102100c255101d241e03505444902e03071841500054559038201c003d03514011955944844212060180401d501f4842000030100b04040140c0c6010003982c42c100c0d80033000304000200a41012201d096015051040b2202c0d520790000d0701a0040c0c507905025909821020248100740410703040c002400c0001510024190b22010782030360404d03001e003044000441c00e000500024802140500c0c1c0620304500111302c449600010b0080785d56412201559544090303d0100007500c03003110090700d801d1b4000741c80020005c1c00b00e1014200c4503804001d02502e50212001d0381c03034510038400650440e0040004900088140e40c2501400e14141400101d1074901d8022a15048081c0012107400b5800914 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934091555 1250 934090305 934090337
    0x140915060307031a0604020903070b1e0c0c04050709261b031b0d0218040c150228080406050714011b0518090a200703020601120302150403 61
    0x5100d511100541c000c000d21480c50b922041c0c10000d20111a01c1d85100c50040b960f1343da180d4045030a0203000400f111b801d85d80316012140180c0c00450001640000402120300080000040d04c2d801c03061200940100c121110a0201421004000100b04103045d00089060411a8040e400028081012824009802440514210042032030611001c4100e000c034803070740e40004800d400d002d25110100d110120360400300742e40c842c0c0c045000350300c41c01288000c1080150416030070701c6140200e08602e100c9030f071440e01c10400e0304814490001038024020700122a6081d070f00c5007500100b20008181200c90320307150201c02d41c000340c1101001032070001b2510b040c0301d01c6901e124204010700e0000c01141152602001c02031140c03c01a0040c4080494108a440c030444506040000c0140c000d1201d8542621a600103008a420344c0d030050303166071344404d0b03010078140170344082d940d15400074440ca0f42004111281c41034140c804800310b10465104069034908001c015001305c0c0b080d2142041e070046401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934092805 1250 934091555 934091593
    0x12022206030e0f1b130609360c0b090a0f1409010815070c05032809120809121f0207031403090a1410060e010f050d0f0b0a1409 56
    0x40c3e00c0c007590125131540300c81d4110807150308112000311403035009826500d40c80e00252003d54464480c031450410f0280e4000082e9001d5040c1121081f40552000c0b00d8141403800c6503800b43c806070428001b440c091141320140030003010b01000003003d16101c00c0d507a880c0381184c5041a08545440c0e80c002d40c81c200207003080b02d2214003400b8803a015104403000c4d01010b08040740c00410703003020841c5191215040c0502401107480310741c4140000020460f00690f50180a0600c5046400103090843c0c0020b038007400d00d083c0714565a020041500e41924001004170400310141881414050041448030074840300304013000c0185c61110240e142c0409040c040c2c03440e00c40030906c500141c002c0080083d80040424981c2000391710606141c41303c400d03501d082d440d10103880108104685014030108003052008d00150480c0c91003880400c00e19103030000d0200d60101c0180c0100448000d0746601300060340d038098141d0041e007500c4009100c020100c4d004240e0482910312403440d0300030740c00540300044080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934094055 1250 934092805 934092823
    0x70507181d060f1003060903230a02121e1b07050d020f10030e0a082d0d02181e01030f0c12050618010b03101512022206030e 55
    0x7514400c0c1e03082607800c10b40b540c0d4002c02c03140b0007441500001e60741031183c01c2081c01031508440c2c10000e5840c54070f00503100d44524406220405051f03080351004c400c490080b241d0881e5541d01174860040c10740045403844c2c000c0100001090340c103c48480c1410209400741c0030500300c0031400f06004800e1600c2c1401d001041c0c0059019503600d010840140e114000f054130b4040080c0c4050100d0038041f90210014034034506000d401d400b80340045402e11810201074034076000074000c031b400400000b0300c4040b20351020100306c0e0400c840034001e107480d124017a80030741124554445c0d103d0360401480d0000d03200e2012170721610302486801c0102160b40d6494400c101108983c0c0710b081142100001c1d010700704241044050300425280d00000c1e0181d203d8a021b0448000b41d590300410f6561101d10120490708100e90543c0c108180101c0003500010074154a07a602003aa141c1110354450618140007030b62101800d1040c0081c0e1001c10040018030740091401000142d80004004092100f40d81c142885d40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934095305 1250 934094055 934094081
    0x5030601030f080d110412030e0901030f0305131a0a030506011809020f1c09050d0e15180d0b0105040b061e03180a0506150915090601020307050718 65
    0x80005000107452640d0454500307800060860300c50780a80301da08013400102030254200a0086800100c0030101c01c0002c0420f0f1180c1c80f422000b504210a20121030740c03d100180c9110742d498060000b0030f004030010120588040700d0020034944078044131401101c0c5002c15101d1690000788105034a603d8403c09800000074031f040a401d515542c10708501e14103030b0055236480c070390015001007002d85980c00c4416101d0401001c802038801c084280004110a410981c0c0b640108403540c40001d10a4000c1c15070320b44c0c0281350f01503800340d0a07400241d54020710b1001808c80355000e0000404e81e0307402d10764440d41d84140c000282560501050000b80e42c0035140041c01150103014003001071144088208051140350b01d82512035a4000c0c110501202002010790640580541c28041c0040070070210f105500303400c89074075203031010b40500500040803581c1108070082d90520302c50601e81505816080b80c0144122420110141c449030300b031000543c02003410385200300c404818503c0b2401000048011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934096555 1250 934095305 934095313
    0x30a080a0b031b030c04050a1d07030b0f270d0e0415090207050c09180601050f130504050f0f0601090605120a03030f020f0703050a03141605070204140c130503 70
    0x15190100380d84608800b0f03500c102c140c4810805009403020440d0250429006005002c035042c1504054020040c0d43c0c07201104410b00700d91310841e81800074a120440c1c0e4000d0403007009030750700301d4100020000548240d020b00b03140000c221790f843c0d6031031409000c41c03010b001503c1c0712016900c01902c42400090b07101d018904080c0a80f15009084120a007125080c101c0581e44400503d8058105200194025844440ca5092100c904800c072a88071055590408072240c0346d8962007000500500c1c0504a0741c4040806801036815140b504856082441142150203074400c152413103041203410103032010241c0c0414010030903070005004881c024042500c2e0308120380b081c08074164589800800241c140b640b10041e002001309954125104d1504454070183c0f2403502d40741c004c1039a40030324521800242030010100ced01000d14081d00e805400103910070790581d251190142c419400c98002a039000760b54031400000d000300d9040c000d104551050145a4540c440f010342401114036410503806544 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934097805 1250 934096555 934096571
    0x20601090c020d050f0c0609071811161703090d03060e04080a051e0d020a0f030b0a09110702060304061b02030406050909090109020d1b120809060705150108030a080a 73
    0x5000f207142c03205411549807540c0c0d03894851540d01d10718410b60112803280c0c898041008a01507020809105507034409080d183d4070302030100194103450f1121401c840c14141000700614034082050311010081c852101c0d0101480c0140c1031315000e4100b00c0305d80740107812800c03003501081d60610625014014107a4075211505264441d6407160060164010038030500141c2000e0000e027030805031040000804010755101c07241840500a500204009404075040540c164400d40c007900076006501009004401014906005180540b10050003403041e03c00820109003d621580c0080d4030880c010710001c0741d00d19200c0d540c041012000c900076011900240010720800c0d9100c01107a146510440314003945841d0f0003900e9004180352100298000145a1901c0404c440d02148001e0a40c408291901c07440d078440416500c1540100000c1c8145010014000ca51805030b000e800040d00505c200c981110040700f84084401080e04003141c0c603403001c03a050024980c441c44d040d0f4800f020b40c00900502c0c0f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934099055 1250 934097805 934097807
    0x209120a0312181707211707021b06030619140312180d0314132d0302040510031b0509060f0108060d060f0204090b0a050102030c060406020c0102120403050901020601090c 75
    0x10b42d601c070300e0340100308001400206110715240d904c4e41d9803441c0018807111706c0c01a1006844614038030301d6078102c01a100002450680007150222100d50240c6520f0b1a80307040034100022540024441c40e84514160701c0d05040c8142a04034102412061000030b144100c0725013054613110036011210810801000404220241e01604402d075110a886032130707145c0c019181c26608000003040307400070060086890a86140b145050350202d0f03501d564050302420214081c0d40c50041c1c0400b86034080380303001c0410001410540d00455122504625850105807255100c140d030340c101411031520290545000c0c0704900e0140403194004030212220020000d5080c00a4015030f0010400c03441000030145800c10320030340e5008000c1e803803850301045545a0325040c801c002040d182d2800c9029441e1800042010b500001c102d844d41c0c2d5541004000303a588554841029502040c10324825540901a0310324108105407082e00451013a10b5a0380c80340c500c4000207140003c164001182c03282400030014074070b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934100305 1250 934099055 934099073
    0x3040b042309040312091115070b0114010f1103070512040305010b0108061807031407020d09080604050619061503020405090a060b040614090901270b030c040209120a031218 76
    0x200b202a45c011600d41141d0601031520f084609170740750045507060b0342c42640c4d00300c040209486807207030700540c090340d89a50b460850500ba140a2601045c00c044d05030f96800d019140e069610440081100c0c03a181c1c042d0b540900b01000388140e4884400042018420002c0070301804031031003802e00e040003591404500103800010b14603200d00c2c05000b40404a4089442504601c414400c0e440300000d07142840ca20003556a0002d2246070002501c44a002c141100042030090260b50020020051600c5401110040303203041404c10902d02c0c2c2c4e83c0d07000903070540301c50b66440d64061f440d10f0068980d4a04018071400d020020701c030516092500b00140490f8406100342c9042e140d60380781003a55840185400c200d28420300e0043e03903101c40040300010712101d07c800302c40f10401090600c00300d20411028075009841e007400d50180e05800c0840b01e44420705159002d0605213000a10840c042171060100d01d040004a1005800051600020340d4641200f401541403400a000c1045007201551310b80e0084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 934101555 1250 934100305 934100327
    0x12020a2003073005030903070509060f10110a080301090c0f0c060510050402030a0c03151a0d14070804032a08090f28090c081803040b0423090403 64
    0x40d14041e0110003c03442929280040041c00300009280c01d00aa41041540e0350042a1038a2007032045040202d40340c24402c800501514010b824080903030701d03d000300130462400c00440001c000d407941204407441c00402c04200c0d40ca0040050740c0d56075041101c4401503403141804181400343c54041c2c1465a40d001c03003d20100c0c1c0d049840010561642c01c0908807218840e40719542c003500100a001c44802d8540c0009440c4002d5281007111310341403403812044e65141e1003400c03820300920000e2440c5000d03610042c001480811000580503070400c909404440090740c100340017441e860200030400d604240c400b40c0c2602001651004820221110300a00d480040c004090507000b0807022042c0c0c4038180c05100c081002001c800740310055546800d44006c154040d100c40491086000544030440d10032005810210390321a02107555016046c03811070300f204d01035080e41c841080b000404440000240000d4102e8a4032800420070310b41050400c1c400c590300da41d2041c007600c401c1c0400607070001c0311107074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 934102805 1250 934101555 934101569
    0x10209132906121503010204060914040b060403032a050a0b01061e26010b07060b0a060512040f021e120303010e011509080105010603020301091d190f12020a200307 72
    0x18031665900c02140306074400313003d0035406600114011a0050b086100e204c15200f40e0508d0b010320589100c2000195490880e200750060307010401400840c2c4540304007511410100701d40762581240d030606500c10540c0540580e039a80041c440c0c54201326800390014010003180c948680c42d050400389901c0c6009514269038180000207108109484135440b00c00710821000030320540940e0740da5074050569118060441d117140c41e10601507a1446e00b9181042079590580d0744609101440c4042e0005080240040d111081c0c09131901006a480f00341c0c0f2440185002900005000494140305010454404220894005000500610003500522811165149410702c4400f1000205075140034885d0400c42055081c24004149650140c0044d8101c402e20001009800c0b1041e00c140c812500c440342ca030440d5008094078554100c0b0111040000303a009005410f0305417000d40d2000b56014540071668056000070795180305011b030030500341010602005508480303000720030000b03440340e4417806051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 934104055 1250 934102805 934102837
    0xf020f0d08030a150302090403020d0906050c0c01050a050d0608010617061605070206070804091505011814060c010905100b01090b07062c0114220b09010209132906 72
    0x640020b01c1580700d400664007d042c0d001c44c1c0c00d090900948074529010200b01040c070098002840c0c900c500304903401051058064070005030384100447d41d942c020051481040401d00440caa80c80310b5205100c01001b9100000480900d0190310001c40012400742a000d50802020040c5507001e00001001405041c50004d40d180e10310700c0020200c0c05482400303407088001080c04030f0f1001041c2e01c801c1010307150f441c040c1485c2c0e6840d0300468034a01920980741c0c4207a0900740411030a0100100d00e41d03202e5004041c1400d000c40c003d1030300d00315418110251540d1b4894030342620154490312070480310303240a2a04035074403410035020310102e00c240400241100d54803044286d075a610040340070981120040540360106601c01c481d030180c9240040411400070080c085041c0340808007900d64031000191205d8424651a2100e5019107030082440c00155002c01070300c7d01950300c5011001148c05c8082c2c00040e4290400909031040c0910030001c000a601d00b082c40c11543c0d60034080e104403003c030507042c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 934105305 1250 934104055 934104071
    0x907110c06033c2d0601090b0d1d120a0c0201021c050306100e0109060c0807051e060a05070c02060c0c0603160219030e1c020d0f020f0d08030a 63
    0x11440d00184060300602a6000751644401000c060328400002d03c29403082c0d02da11040000e0315103002c55101c40a0039100c200804103078600b00860564000014189901c0d01a03841082494540c04074010040b00c0703940702102841c0c100424a11a1038540d100020044102001025100d038454410140b040c0002035085604580c401c006a8203458554106201604402640500340e038000b0b54a447c49504164080644580304001030180142c0581d5114000362516106541140384e000090350010380402840c40490780400031403c110302c41102d03400c1c40f05030613404542486c0000d010107032481e0a010a100301aa440100c025800e0740440c1c81036a1020701111491500a1843d81f6135000000801040710107202078030302600000854007a0740440001080c0b800e11070040f804014040760418450350001e00300740c40c9440b82541041500721200610f5000994510f414200032101c4010280c80e07a403c50804908024492505980180d40c0207440e030b642c1038803800018030900c00c0940d01d400d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 934106555 1250 934105305 934105321
    0xe0f040222080312134706091306060e0f1e04050a141618060e040210030231061b020d1b1a07021f0c1b080f010b0907110c0603 56
    0x102c076030740003900c20111100d420084002a00c1070074091001c40020584090b00c250407040e07400707c1c41040000d01c095900d0740c0d007102030080d017030200c1001c0e03800960310a0040b62448111b092140500341d13504940c01c05243c840581102030a00c00412080340c02e8003424007000402c001001d580c440c0d40200004000780115010b14640035006200045400448000160072400c8400c900c011108802c014000c050321138046500326401910f00941110a040c0c03800c400c03a200c0c1d4054401840484e0081c03400c00e486031000c4481c9241c0d0206a0922841701004000180c0c005d045864082e40c500300b47c107502f4105400003014600109006000c001071080c51b0791200007241d0320240070300341134060050141413086000c206074000c081c0807030040c006400c1c80c1c119803003020501c1d032403460030b9640c40d40d000311240d1314002800e0381c1c1c0e21110207500b015040418600300c140700e0141602c00403800014001d00d040704101d50703014090002c5050106007a0203d00b0b00701c010a40207038103c01a034002c1e07525261150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 934107805 1250 934106555 934106573
    0x6060604141c05160302040b0307050f04050403170106022b271802030f060904080a0e0301060312030c03110306062b05040c0305010b09060a060e0f04022208031213 72
    0x180003031841c014004131458503801442d8404c00c4d280242c0301006a24860f406050ba210151302409500224100c0d03a0b4146260640007640d0080c402c2c40d000100750314500c52444211402c0c1c1040700540c018510854034803107034801485020700856154141e400aa9a005e4890f0030301011041115000c000b441810140d030059130001015801c0d801122260ac0d844080000d400a03241c5408182040020030b0446c5841c64a89000c0d98001554520303100100006131425000e50100940654032040c0000204030900300444513489961004034a83c05042d0f40101110442125018200d9061080c80001c0c6c41e07040a55041d41c0701d040380920f4511800c001d040321100c6031000c1480b0241001c04100070010fa091008007240d00c40c0e0300038401e9684035802c002d05685d08441494010b00000b90804c140c901c100c42d403075007000024005550f80820716001c6001d0341d02442030440580e000104a102c50f6803e079480300001c188410246003070401602d900c1c0c1c54140c02910040390100021903580500c502c400b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 934109055 1250 934107805 934107859
    0x20105070516090204060e041b050d29010219080319060f12120219060b2404260a1113151d3c0103050a02030606060414 53
    0x8642c0759955600704003c1c0d805406010002010103400701601d041030b0044d020411181c4c10f88481608007020100c41540200001c0484162500b882c84a140c440c4241c4844c4880485542000b180c4c41d64000392500400e10401e0310f00340b02440d90303080031400c5202603c0c1c00a411001c015540c05852034500041c0516070050700c0a00340c502000907191a0000464199600c641500101d90035400c400b661500300d03481c200060455081c001030006440365003c10741011004203c55a038500400480c25099200040a60300000010f000e00008845000c4601c00c0681501a08d102d0b42c046000320380c54000a42005002e64140208444c442e61a810f203024103800c5072400300709000c210306101900d11980d220700c400301e0000c03811a0000240408015204000fa46c0b04c43c0358040f480f4540e02804413405005a28544000c950101c6041004200b40e0007140100018215884e103801003604101c07015000310b10444081100300f040d08061045003400c008100c41002c1500c07255091144000480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 934110305 1250 934109055 934109083
    0x105090409050f1c02061306270b0f090a020d080d0612060204031703160e01090504021c0e0c030a1202120a08090c310e0708070315060609030201050705 67
    0x1e1510600b2403d0001039440c01008400080c49041380d00020607038543c00180d6070410307150345c0407403680e000c20700f00d0300042c00141c2641d0454105040304000e909451500f2801241d0850555091116124000301060341060002020300041c904990001e40049490a0010040c00d40410013080d82c407001d40c0648018412965030300481c80780d178070b4030400a6010340801c4502d202c1c200340c08100c8550b080280c074829032080d004600318810110060311207424402c0801d0400440c004d000ca40780d21240042d00e2410510000b401414184d10b810b84141c42c0240e150582d142e210720b80b44890b44d58005081c03011180c200c4090740c0c0500580c5012802d0400940703044a003a00b000880441da6036100312480d215032078100030794081901d9035040141031203002c00d4402d00342007607071145545000001c8550714550103000c4001503e031504072009050100c40d900280300780e0812072081081c842009202100000481e0007000b03d40d0800f50090414040f9001c00f0341008008036800040241c10026146280c8031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 934111555 1250 934110305 934110313
    0x100905061012110f070510050403050324061b010b060f1b010603051504050f0607020319030e1014010e060307090c11010e1c021b0d05070308210c07050705010509040905 74
    0x5800544c5100345d20019045802d4403c010110b0828081441064003c543c9560350030700c1c54903a02d8000300580c1500d58468080210310b400c141090341ca40000b41206129040c0090015000c02d010900f1035a820070b90600400082007007030360703181c20b0804407044401200d0040021804402c5514014a4140c200601501c250901000e080b100f20011511403881101120b00010350104265250002500c036000564001c4c020800031043d5a01c2c080001892450300103450f01008291924000c1c075071080d503c0e020743d20b074000841d54159500b90380c0508154030081d1458108440400d5a0360030038441c105030380d40ea82c4144030342c05100b009200004100e000003809409461544d03192078045040c261000310700f00c1d0a034815224000300311045601c1580c080f051902c0300950903c06580c0068908440b1400f540380040700041100e4064100d03d00e0744c00b8015115200c500e07042d0b05003000a044000d800b00d0038420000040d00014402c001d880c001c1c60400d1300d0b4803107040440e02505000c1c20003806405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 934112805 1250 934111555 934111567
    0x80c0706120c0c0b060108070c020a0b071b06050f0d020d05041505070309020d06200408030910090b1c0605060706020d050709150f02031308010510090506101211 71
    0x41e0100e100c1540780c100e50300c1003103042940e090980b100148000020064a810070003c0d802d503000b0110941d200200d810a0310710b50800341c0c00a0880c4200d50400c051007003011030250f00344400c0d42c04001484007500da01d110b240b400d245028045000d003910445081d1000030317030714903000142c2d0150b40391034010b288240300a05051801e61090320301c80c0c00e569021481e00700010003c501c28014203201c0c60300502031400c111110703124040036045500c0342982c80c04441c2907618081290900400041c460781e800b441d15160140d080100c0c801640308190300700003030083c0030300008082c00100d90220003050b1264900d0040e40034480302500c50740e44003541c8542c010440c0700910080d07400900f85d042801d0400c1040b03030781d440300c01c0c0c3d0703c0301140c0640b900c1c0041451600035000d0180464a103a00c10301e004580c22b102002110024030a50b03504002040d175161000c3c06116811155031501410103580103108a180a5010130712007007040b0983d0302000f00442014034140701ca980041c840142900c0241d071350b91 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 934114055 1250 934112805 934112807
    0x90807030605090316060c020609012d0209091305010c081618030c0f09053105010e0703060b1311160204060909050c01090803090a060e030f0a0506180c0603060d080c0706 75
    0x400c80786c0a074050300403000007507151901071040c021a648a0300c02c6c40400203907022334681340c2030b00b40c0011003029401c00000440390703180c80001c0d202c0d95102d0141481e994a0380360990954080c5c08022041c0500c01c0140040b41e581c0a07100103200c81750b1701c0c218000700703206c40d691801880b80344d00142042010f1440030500307042240880301507495030981802582c5a02040c110900b803110030100d04529031203180c000307140d12000000603581c02000081500080c07000043c0c11f00324035030300807a00c003070b40c801c0041100d081c00010691405d111110802a10389803007051034051213203546988220580103d000210740e02c0741d000101030003201d641080102410310703045980e282d585504a01045040d000040c0c40b0318004221412044040c0281c0446c5141c948251024008035880592500070039804004c1780c0410007000129600031300007800a401c1001c04204940481200c0301e0304c40d044401050303455112074045070380101d4296280ca17240592820200c9460040005281c2240100d900000b602 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 934115305 1250 934114055 934114061
    0x2102010501080706050c0a0318030b01081506030f0604020418050303010e091c0203040603090602043201020d0c0209060109030b090604060b040c08070e0a091103041209080703060509031606 83
    0x602d111500300c0c0d0b00d16444d61016242405110150400350b40107184000010307110b0340340004030361074080030b0307020b80c83c0ca942c1d646002c0e520903001190250b000307620305800011103206250704228145c01500e108132450a2117501d400000700080d010340e844811817061074a4a40200d1003054101040c0e03a100d58490300c008440c4101582c0c1403c80c2d01c40c10000031041019601c01d1000102503070001d600d041c2c0303040e10035006020030b1001660b02550a1000007030303151103215042000c1040c0506214080000d080c001c002e650009803150455014214003200e59420209e01b41c200d03601140c0c02a0103a0741d94004860441190b04003c01d00fa00f850203200340c50000244c8140943d00c521808d21030b03400000d090104940d0400a1100000d59000120301503500a214800c101c09028050400854981c1c4441301503d074020342e8080060000801c00040c854403490201101546190a030b2006142c10512640d41e034103800041d081c01ea80c0d001103207000c402081190018007030152040e4028a590070102d0003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 934116555 1250 934115305 934115309
    0x7081e09251a03010b03041106070611070201030c030213050d02030c040e1b0108040b0a0f11031306110c030403120c0b0c091f1209020102211c11162102010501 70
    0x441e51200d4030410182400078190f074145c41c0480070850030b5581e0ba0716050b20442c4038001c8141c1049003000050003041d02da000741181415400800c80c0e6600713252000504988414407801e080605c148a418040d82d00d51213031504480c812141900001450300000b800c14110184030340e401f91502c0c00e20100b20402003858240400c0c1303610612075071003240c0c005442c0c4c6401150020301c001d00220000706030090070340c4104074842916100091640c600c10316114140c5c41520f40f1359031800601d81e41c408000700c1e4098000e2a0910010440c24046030112103a524080c40c0001071810b40c000032005580b07440f074640380302e0040d000f00e0010841c0c00c003081d110400e41d10581c00c0e54043c1d070b124031b03241c02c000400345003018642c11f0755a650301d4160f855510301002030142180c04c038114016038180c0c2e440050f0154002d8207a541c0003c0b5256600c4d101a4003400410350000780f0f0110324101110801501c10f00340950b0061400c24410315084c005c1854010560099520f00994480c042442450b585e90b055200b981 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 934117805 1250 934116555 934116569
    0x9060d0c110d0c0303050403120f06090e0109020a0506070201050c030423031603030503060a030c08060a1b02101a061c0507090819030e0a0305100507081e0925 70
    0x1491410309404070b445070504003050010851070341c18400041d1281d407010b1781c454080d10b001826040c100301002e06841007120031588075505c4503020301010500d80704183c28a02100000c110300e0f1100e60104403003d00a108961194030007023030040640e40550100c034065010042504d03520350312522001703a40280c0240f00c1d5604030b5118031011090400240365569061841d181416031032466804a031250f000410143e0803400d0340c1d0b000800100551500307009404400302901e442c0c54080450760031503189d4601d8500d10b5800340c0d2035440298000ca0026021242810017003407500300610288a42411030f0301294004400043c03d0700325004412044040d4500501c060000340c075002d908039196001401804050b41000c40301d050301c01150462228824800d080803031058200c107000030b080c0c204580c800d80e1650404001c9032100f85a030301c1866884401420115540e040c1050007003540e0380e030003840c02c000f0420381000c512001c00800402011007020900c0c03a0b05030284500c4110305e65040d1180700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 934119055 1250 934117805 934117817
    0x2090a06090e0a110706090201030e030a090e0f0106091502071a1e030702070506031504050403080a060b0f0d020c010f021c060f080307080a0905030304030c0e06040504031d010509060d0c 82
    0x2800c40ea20f5801003100740810140042d00384859900c600c0e005043c1800228149a51240081c03084407081c009040b0306506c0ea03ea80d13801d10300c0c1c003121402003e0010500e0740668206001400700c15006940c040c240c81a246030b08414041441040e842c000040e00718001881021100b00d00c000050002001c00c000f400d810420640800368420341540000e5840c0d40240e00300c40740c03c0c0458281100075507809402142d00304a61a00200803a048901c180c81c00e800040355a030800a881903030740610030042c001e0800c0c491500d030304001c000c03000303000707a28200141c0c91b00041c040fa000c210035000000d411880c10070455403404103002c07200c8020b150092242500d401d111000940b444c2100e4a0822181110095827030410036644581c80d40d031202c11101c06010484001040584041016102440c45520051070031130a00035035001c0941e0003044584201d09003c01c00000030790010507904907540c0360203000c3c000c010082c0140c03404d01070b00100d10782081740440c0c904541c095039000301da1006a10b40345d0b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 934120305 1250 934119055 934119061
    0x41130f0b0a05310e03030106080c040f0e0703090510061716090b03030705010509060601200a021912060603020a1238041a01080d120f02090a06090e 65
    0x404100c1110744545540900c4110710b20382418295084a14045442403642083c824078540341c2c42124040034403200e6940c03010006000c2c075500b102e81aa08424800b0400d410700c2d28085800c00c10f074086005100751061903101082d2000d0180d0802c1404a0b8440c042d2048560041502e00003424a40310b5032440d61200c07401004588800b00e83c4070140c0601c00700c1e0074039890806499401528084645c00c1c0c040c070007041034001081c028420580074402010203001c9a003458000102412006040d001410a00c0304040c00340180008411001302c0d03060381e2102d8001d55500055508290541c8400c00310401e01683d6010400d196201c4400e1364400c4074245683c0381ca4840c1103281021f0301d00d00400800e01d05600280292031003c03800c0c01c200c8110047c100ca009000300030780e0340e41e80c180c6048805d2006000340080c06041c0c80900c40c0074108040c0103040100403c0345c01040f410301c264890003000d65940d403001c0d000f47e60b41c040b900c1000c400382549841c070707580d00401030480e14203209000840c0e00701c0c404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 934121555 1250 934120305 934120309
    0x120542100b0f030105040c020313090c260609070302040515030105030609010e0d050c010b060403060902030f0120070609120c0303050109020a0c0303022b0204050a41130f0b 76
    0x5540c08100b100d80aa030840c2c0c00c0c0000d01000340320305124031040d84030500aa0440316405c01c5000d0203485482c40200b4014a16000580a00e0409540b0300850b020100f80368441071101000d85c0c4d1061b012030b1000b02a44401d0781c164020300c2176801031a0480b070b8500000300400203600080d03040702c6007039085a010395a4021901d0880f02c100c9115081c0ba004070000c02c03c00b40c4220042c1c04010b4824000090386110100013810b82d82c00b40d80101e42070350b15400010258170301404070000040e82c2c40c000348000c2d2034104c076802030945905c018554649010481d0000c5c059258002d4440c954040070032403a002c200c400180200c0004002180040d080c940041104901030003651000c1040b40c4a00598100c1035400350301a4206421001210002c0300f28203c50b800c9280d5a034100a52488006036541d051006104a895040d0040750313038011340925101e049807030300700e5a0503c040451102c42d45502e07411098642081c14040d0560b01c042011000c65403210a03500142c196061003008100c1c50141c401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 934122805 1250 934121555 934121557
    0xf030c150907030f03030f0501090f150b0f1605011a030d17010e071b1407061409091305100204050a050f09010603020309010609020403080310120542100b 68
    0x120700009401a00301080010102508525400d1103403e0120340c1c4c800c114519411a4001d90141403150340710641030180380c2d034520a41d828880e6140819210b07030304100c1c09840754401c80701400c2008000080128a00c1e20b48504810b0240d8098001e000d1800c00312031500c00c041180302030383d200340034070048501c0a5004004204541d49040444141a032801c4031184038904020303d80420b11446030440354a200d0f00f85800b0744082c1c03240c0c4111042200b000400e40c90003800fa0010800e0005c1c1848200c03e1024000603a10200822074210300317541e80314030b01440007141a940c000c01c98419003420904c1141c540e005002940d00a0350860501c2d83c1d2030701080441d130346020403147c0250380c003001404000d11940040d40d10584040001c2032a079641c0c0d045400b240d009034000e8440c148003109021481c880c022081000302101030074080600c165440741030303c0780c0c1c0070a01c4490502203a8040344d004034040c00380000401800ca55011800300300621340e0304c0180101c4a114044c030301c00c440824220000c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 934124055 1250 934122805 934122811
    0x1103010f0501030903030e0d080702071d2409010b070203060a140619151809150e1f090911010201051003020f1c0c08010e0d0507060b040e0f030c15 65
    0xc595000d00c189400015002005100802d0701050303152140c04d8480d0104000540c3c038405036550702c1c1414602201d009040c200a40c000340c00840201c3ca40c807017050b07000d40e0310a4104103400c02601c01c80300c1340000f15508803644040641c0120080000003142d240301c0f00076101c082d000358184c84942d134884041c201121409152041c002030010007145540c200750f0001c070304800c085610049900d881e04100f0481c04070100750000000c0c0780740f8004480a0710a8107141c02070454030b20501c08800607103804071442001d0b009807180480041d0008649400c8405502840110350003a080b040f92200c0c1c40c800a0414a00207540d009540307a40b0200b2544140300b0b1174800d002280c104142e6034156400c100720901d100da4260791080084000d16540404034010b940610700c1011401c00141c90b044041c0d00303540180845580540010921032442038100c0304459105a025400107200c004590009005100403035506500e0b20a901c04e030700b4011000801019202001c80032103200907003428410703540030411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 934125305 1250 934124055 934124069
    0x503030901050a031820120a03142113061a0901050d030e1c0302070e25020102071b180501050303250807031e0305250e03060c0d110301 60
    0x2003100c03c100520a0b03110340c400858200040103801c225031240d54900203800300c400320348035510290850718038011000314207001d03161010f00010540c94074003030020700b045507401d0069100003e030311032005100f000c0815103003c40c00c0b0354031050030a0f00d0300000800150500310361003880c00410001c8103507401610509032400031f148039031aa007410305020806610040c21018001c40901915081d07a0340c1400c440c0c400209a040581e0921a08000385802d01e82d0780300764540c9151505102c0d02c400f221180d00030300002d1000d01d08140d40c880804070300a00c58004081d14010130741c0c40344182152980045170464003540d869440c00422510108200d030390a01c00e140d851350007001201c4180c1c0144007080c602d850810401c034401703082600c03003201560000604400107a19400320820400140d58001010141403800f0015403504443c0300354100000d49400f80d44c1151100c081403101c0c860480004900d80c050280d9840c2e05007286012919002006544c0303000d030070041000d9506011105984c100c4a030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 934126555 1250 934125305 934125307
    0x101d1b09130c110a0602190c0f080304140313091508100903140705150a1803200307080c06130506010e07051209100b0603070f110f0f03070c050303090105 68
    0x540e0100600812482082005000302021002c10f010010b114145905001d000b0140c4c1d030f58140b5015020344031203c0b15600500c10840b0b0348101044400c03082c0111941d120740c0c0140c0d207480d1410400808440071404200b103100010744124041e40d001e140a00312440110b051202d175040300c000c00c03032070041c0d4041e143c820b90081c48420749160194022806d024003c0c1002d201e59100d04101414691129106441a50140700640c4001e003003084003980c008100a0200500003422024a440d80392503c0701408102c10240080c55038000c0f2651801d401c2c220b078044030350712039803481d0081c8140c00070001e0444030700420000421071480c40c01620115544440500003d038200a1000035000d805030204c4100300341881000325103e010a40a4014070740d210080c15038201608800041e656801c0340c01d40206d20504c2404070103a08010084580115410140e1f55189ca01171203034a00040071034103416904c01c8007aa009165004001490341034050001d00600545610501da0b60340314006c00640000c0f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 934127805 1250 934126555 934126579
    0x7062a021e0a0303110f0a0906110703020d060b040b0418020a1203020a260f070615030c260109061b02030304050d0806030a1205030a290603101d1b09 66
    0x132080d44a40100190f403d2032509140300c1d000a0b80c0950042e8401d800482d000040a1007201e8001101c0c81c0000160f00c01041c0e681e0139135000c030307906454026005141540710300308104540d0b00c0d0b42022940708009442080404040308400100d640007840580c024a107650012030908008102c085100740c050300180751060f0150341e00c20240581148808079034416120307040d590b40c40301008010101002495544074015400e11390100c030401d1180d14030f40000c000c0c042000961f501240341c11902040070840707821138100c188040f0500c107a00c410140394607149030f107800c202c4c00c1c0c1d20544503074907401c910000d04807039520b00380c3e600d00c0151009000b6030f000ca466210020700c40d100d8030368070210144c25603034013082a6448103440160141c0e0000458000b008002c03000071184140c00706400401c0d454422811118600305500010000c03050003030500000081c181100d00802c68001c1003020347d0582d004504240c25200d0910070788150405211040710304012920312415a45942070060088520700f07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 934129055 1250 934127805 934127807
    0x8090a1712070f0503030c18040917030c0405041107030e0306151512090f160b03040b0402040e0f01060816080c0904170d0902040b0303040605030c07062a021e0a03 72
    0x1070001c4004554018010001c100003c1c4c00340080d50049030318030011a01c0321103040080c008814540b0446010b9071620b03000001007002140003071083d52211030b00d1641d07521000f03106d18040c4240d80206411a00b0b05481d010b60790b4035a801040024060307581d0041c81c000031400c06448800c151030207500c0348003a9488500a2414045030701000b85584110b6103040064803e007201588100d40368541c94200e640f9820510100b8840341104103510520800c8890401101e4900c41c00041c00260480401000240454036550300c0a40325250b00411250582e6180b15102d01800c49401340724024000c030801c8498a1307100c40507081c181c4010340d000e0518001e410080c0011900010801d4900ea0a461304102088903603100410088450f8800400c0c0300d440c50051205407980b000c0014000d6004110810215a000301500d030401c4050640c50b40c3d0308070608140001d8400044400703440b14510202c203004050040e0070b03031030b881a55029203e05080c03001d80d6410920b004080e401d4182c02c601d110000013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 934130305 1250 934129055 934129057
    0x60708010522020409110c0138150c06070f0c02090105010f02120d060e010f0e18030c01020a08220309051201060f03030c170901050d090311060408090a1712 69
    0x61100d0020040c14207585e40a0f010a40e1814040c10341c052000044c0c4603c08078080c0102d42d0058a2540d21080105150500e10701000a8501d0003030701c0d03000140b00505507a81e05403919400a540e00755951508800c203220740c1c48903400e6030103001103005180d9103550140281040f2581d180c00501032006686402c0055502c4241030360039800f1801201038580b800184140900080300051030f000130081d00300305186420f600c06030004007040e01440c23020094818110649988a51f070100302d5115401103c030500d2560040500d4030031254000b0900c00c075142d0b07024507114032841c4003421141109480301700124050300340e084045c00060703480300d051080d405d206c0b50308001c942d155400040c14aa441c0c4001c070000501341c10480c0020f1001d1248810b005403201210000010380300c00914151110002806510614080502032610350316640107150054201848000d16030742507460919143c40d084140350301945440e881205c0500b03020440c550010800140004650014201965036452401072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 934131555 1250 934130305 934130359
    0x50d020706301127040609050c09010f0c200901050409030e040b060c070305010507030c110a0b06010c14060703110405090f09011107080c10140f090f0f0c030607080105 74
    0x43e41d2010000e414190403565803100c0744400100841d100750010900f008240c0340140e000c0720172541008144a50707a06807204451114109080c80440c1012009041d2100302c00140003500e030101e00240b003d00700c49500c08456040c50f00702d038030b541c0c80d070389075010001106c44441003c2d0010b0344120064159003880c0d031241c18100e01c020070450070034903203100302881c0410a800480c1e80303075180c106001c80a030301405900c80c10300d614100f140c00741503001a0303650744100b031040290011806801140983e400b56900490035908039012080700c0d01d0343c0404c1c3da80d40c0010754400002a1070151400c5180c1e117202c054034140c400c002c01d4508952a2210a2444640c02903ca60119503079410034126489a02e80100307000e601c6205101e4490000d10080d500300684000300c6003026041040100c20b0442000c0783e0796101c522001200c80944841850600d0040141601902c52042d00700d4908046000580801a028200c00b210b4141ea00c6010840d0268028170a10303800000c2c0060000c03096a146a4400c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 934132805 1250 934131555 934131581
    0x1903080f060a080a03120b0a0506192a0b07020102040614030604151211030312060d061b120e2e020906070305041e0509070f0309050d02070630 63
    0x120030358462940d0f40c2400d80700901240410f03500f404131a0344c80320901030515070340e80842d000f0850501e8075010460902c9082e03015501d02444100e032400050107681e907a8800c0c0080d03102d400c103000781d00c82260001c00c1412001c2e104000e12a00040c0c0f810301c140200d0b81500c0044da5a0603005051240d43c1003290000b52007503a21544601d02c60b149180164050300c01081c1c014541100e00b5600e08182808031055a0590f0003a0010410782c40d0300c1840c4060240c0102d0103661085100b0914200900242640301480840c030011800990005038415440d12002081f94401c12403500f448914981e140072a0740291012610100c010f103c150050703030340748401100c010b005464124100006000d9500000003203010880c0420306101d11088110500244401118285a40c0342407600254050b0402011001001480c03130314190b54a101e60490040030745e2000458013080b00d1305074041d40b540124040e5000051070b40c003081d01c0c021281e1112210310303002e03500003403028103450500c0340180c0394174442d1070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 934134055 1250 934132805 934132819
    0xb0a05071b03021903020105071103040f03031d040504060209010f050405031e161509050d17090a090603050f0105070c0b040807140319030e0703020108011203030b060c0d021903080f06 81
    0x1c204d6074050022501074030a50000403180b80c02d49014003020308410b01a24241e000340014481040f2600601003980d8040c1032000b9a0b000145240c0007610340664250f4010b4108810f010410030780d40c0180c0f001d0390b02620707428440741414038104c070540194404c0640c0740d40308851610782d45410000c060001d22100c1c00b6191101010040703900d0640c0b031035200d42000c00f81c0c951420142c5501030001e002500007110034050700a0340307031507042407064001300403000780d00c00140411003a0380d82c039035030002401681402d01035596a801d000ea129883d15202803015420040000e0344940326503d4049000c2c1e010140520035212270b185e0040a40000d14111500c5101f04000b240c2d006080000d04400582c2040c00740198158001c01029990f018900421991282c0c0302800144c0c1c2222a50341581d428840440781440f003410102c01a01031740f560240c0001c40001c5900c4007101c0420502e240c2c1c0c06603000c458400d180e0000310380030b13001c134218054001040e003c00b040c0358840c0703000d0594000714011320b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 934135305 1250 934134055 934134073
    0xd0902030304060e030c010503070f0f0e030a06091406070207140a0f0b031008420403111b10110f0d05070b060402030c040b0a0c0c0f030b0a05071b0302 67
    0x12074036651107a002100402e41000800e190b030310b02007040700c810b03141c20720300303d800c50070000006401262080711484c1482808103100d0368991103150052051764009044440c1c2c1390a9040c08002400103490a40d0703010b00c0300500410703140c1d0002c0c015004502c1d690042207600d1402e001503c200c1540b1140951100c00000006510351907506031102074007060f5081540c1e07080010b02c10203018400d500c103004030b030001d070000c0c103926264080725110003980940450b40b2140c107941446001000e050324520110031442484141a0720501e0410341d042841c0883d4002d10007904124841e11440b070000381c1c0202c4070502d07524031910541003894100e07111411a9028580300014074100100e92500c640002da0200d90300f070620100c0d0201c540c01400584045146003800d10f440601d921541c060411000c4c8000b0380c4510441c40341210501c0e280c0c120a903412803e0f00c0e900bd115803109944410707540c107040000400c0c5080403d2280754002d00140d00e4014440d00312511040d62403405800540660142041d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 934136555 1250 934135305 934135309
    0xa08060112151d060901140d020d050304080a03120b0f041d01060b191e03020c031201140a0b030f1b0d0e060a150602030a0305100302100c0314070506010b0d0902 71
    0x30b403405403503007125800d410544100400d480a0b0001c000e2841084c05400401040c82d43c56a6420b402c401942d04400341d01310790001c10301c1801c2d410700080c09480001000204400d0204954405c94800c0d5500c1403151030301008a07080e6035800510551200300445907900d03503c2e2a60044d007280c0d002c1c0c0c076400c140758102032040b402c452140c3e000901800c80058060101c0e56000e404410031151403c1401c00803004081e80b0f403a0f6024a0050010f040d800107046010307140420540f48000c6200040031060740e12124400801410110001e00800e02036802054080d41c0e401624845c00c21504914801e5075081c95101048074202004400211300704462071581a0a000356907170346c00b01000800c3d80b424009020000c0301c403001404064201c092206100071903001c030484880c4009454085096114540c401e0f150030b80310b03030000b54048a000081f940703240d001414414840e00070f441c1d0103080003414144641030b100c1c904004003280c12050040c0720300742c09040906507940d102040001d020b500340d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 934137805 1250 934136555 934136591
    0x3150303070b190c020307060510030f0809090f01060f0c1b0f0f090228032304150c020c042007470601021f0c080901020a08060112 58
    0x78240e4040ca0000104640e03001c008115240d80210040200921411a00025100c1c05411801003240e17071100f0100310152000c000c4200515040401403462000c3d1345802c1e000b0380e001801c0d0601400700c03040003889040311102114100c0d0000e454004a03105011811a8041090310089922003014008001d00501c0300c880d5101074002000c400341514100040801455003680c001004a40100043d001210407006080e0305903007681151190107a43c0c02c825005020101d000342010b419004440200215140c0c1046c0290f0203049000410f0b40c0c0450b240301076480590241000d41c2c0602e0f11388d14141850380c4101e00d60324424544181c0042c03607100d209426401383d04107072640c1212842010404c44194000c0c0d0b0613105502007507001018940d00407051b0300000071101040b00056001032000c2e4001e02c003032400300481ca10607a548802211a100081c0143d80c16400000c000c280007a00201d81403088030030b04106c0380c0340d00505e551954011610200e4013020701003c0c0707440c4e000780741c1542c401c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 934139055 1250 934137805 934137817
    0x51c12030b030c060702100c060f0c2c032a06040303030c020d0e130509011b0810060801050a0e090f1f0c0e0d02060306060708130e160e0603150303 65
    0x140c0c02056000a03801014980168070140303501c921001c110385001640c07004440c890008081c140507030303003506508003000202414581d5007566414182400d00495000e081e0364160401d500e000c00d210900d0359404200c200c919944650180e11070484480022500548019115108041049500056000300c0d0f07081d0003642c0124046526140ca0010054040c018000a004030780780020425101500084070001c0c07250a0760300e0165200086149040c080d040003c40e41c2d4440c2100d11840d0090b40e000b407031114201d412000d0324440c8000824084e2240c00c882e412204000d01041d01e040c1094001040c481028085203c036100320540314030b200740244100e007030780c10300000c2c0344090403d04070f4848240c0b0400b20f54070080000f0310180c074046544122500382a9601a0780080d22275642c100422018815034601030115030b0b01081c42991401c002d0a0607085c2c460a00c03480000d0303202c450322600e01041d41045100418042d908011080c203000001e10b5112100c0960a40302c11381c1d580110342581d0044d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 934140305 1250 934139055 934139057
    0x18091a19240215090a2301050f0604060b0f03060613120305074d060c06010510030b0102030a0815040203160e01182d0e040b060a03020a051c12 63
    0x122041c0e20345035010300c14060381203a840740c082c101c0e14010015545407014008000c04405d0582c0c00480c01c04800c01024801d001544001c00290900c00e41103040142c003200c0583c030070303420700c180070800ca207480007552106010109070905544810042201c550001804500094402800001d683d0080804205503d000e91a100d84e107490a09004d8041020401c10410315481855203007118458610a0100030180f000610500c400c4165030344810024008003941c03019000c01c0c2500b4440000c151300c0e0483d081243c101102d42d152480541c15501203040c55409a00107011880c0464010040580e102100c80001d041d082c44000005080381c0050301c0782c1c0e02500c1d92903e60300116800208159480d0002d0030309074030b070310001c8270500d10151160203443c14480c035403200c0ca081c80da60103440503881c0c48110810503240c0d440e066000800c4034100e0701a90010845008101e03e400e0a40401041e45d8010b03142071042c50610781400b0305580741c04084180c420300ca00c6501d01254000d21102000403036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 934141555 1250 934140305 934140359
    0x9120114150d0b010924060905030708241012080705061b0d1e0f05060a0b21073f1a0904020d05010c18091a19 49
    0x22074000707103414a607560034981c0182044002080400c076a03420711411101e25041c00b2544514009003000c81d80c01d0810b0301d58180c281c2c250081840340c1c210200c201960400e0b02190b491903070b80e800190b0ba034811710105417151008506129911510b4aa03815400510000c00d2000c0c00d90304e106a0b03041c201210400e494507a8040341c0e02e810000c060002c1904144805903080d0100c011540f1082c441c480c1c541c0c074965140d910781d4140562898040c508071501783c0c4040421450001c48107640140c80304a8840344654061100800c90003d0b00c800d8549007001c0000c0c40009000d00110036441c0030b0064500021b2108d045031f05135448140c420110101403046a500701c010050041c0300c46007014802482000c181400f5480b9a40c044444011180450844600039541c81d41d0010901c44010780318080c0c17580d402c01180c4002240c0001030b0001100020680070002d079901c4406504a034080d50710b646104507100020361040ca0206802c00d0700c2c030030300400e4201a03590b62010b8841400ca0403140200920 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 934142805 1250 934141555 934141561
    0xb0f1e130501020c100807020f060c07030e0108090a0602090d0b040c06030507170a091e050c0306010b0a1b060605061c0c0801120f171204110102031e09120114 70
    0x1031205050024042800103100b000440300009614052440e09003041100c2e04c0c0004055902c06c2040e000031010600c241d5a583c03e00007031003010796002c80f8050f40800c82a040b40840c55104400d0740e03201c0c0c1824005803000c0780702561a00080d501600d002644140c05a200b0000f05004440c03603801240b240c0c00c0185449c0c034220025080d9030004043d04207118000c0d80d030b40b11400801b9081b40d403008040ca00041da0011510b00042400b000011010f1549000c0540d14100f00d800581c0d942d04c0c0074200d00f1100541e13030300c071041c01403441940c2c00000019070168030401a0072940c010000d07454031a81012890380d440700d0100300160405c068104049800c4c8040b03840110b411311408804c110381e450481803a40c14107000c0022141c16120084c102c1e20020701ea4005d20240d109a11400c1104140c000d0f920b82c2d40701114050b9040c01c1d141620507406155246415600000460b4141c01c055210390404040c182e100030542d80050541c980c0086200c00640603a58080c4150340b41000705c1045000142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 934144055 1250 934142805 934142827
    0x9030203190201021804180209090304030b040302070e1302060f030a06090e01020904060f0302030c0d0321062c060d050c040e031c09020d0b091515100314010b0f1e 72
    0xd5008841b405035107401d4080310446a6004490403807034059501000c9511841d0000b071840c401d551003d0000c1e01d46009000030943e011401104645a5070000359140d120407542888445000c0070003903001c80104a0682c41c64882405154000703484080003941030ba8030880307401038441c41c480101160f580000d00341c1e0141b13443c2c4075001c00350602a464030782d0242103034042942c61003003940580c03050110350012002c05104613110320862404900c2000505035070926030010388401d000f9142d600e0310f5010606400d054110542c80441e002c02499002c585541050002064403100305540c540580c88821006882e54095001540c030103800541d07903400c030b42c050b14001e07003034a00070704600c5410004890007694440483c2215076030005451600c40e114446040d04e041a50088105010301d104200296403c201c800c429817110300351518600c040072094205c045076000700403172040380c03410070042c403514040ca005401c03000a56510306203801c005400920005218a518141c103030800903d0030050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 934145305 1250 934144055 934144087
    0x50d200306070521060a032d050102030a18260c1204060206070507030210020f0904140f100617040602070803010b0702010e060906070b10090204030f050c1906030903020319020102 79
    0x481350104585a41c2010f0000074514445444054a50403250310808100c01007200340105e0b8100c1c41d01203082da1241460b14038081e410442d20400c240d071500300d442c004101c01d60640304038282e02004100f444003045070f074030002504500394440320300b42c24003090195101c10032a01d9032020001c1d54032511549890b90091808000030640c0c01004800d01900000a40000d00b50301b480394059400340c0c40302c0c29802a0111400f4420903558043e040c442042d044260702008103000300e100400d078075019541c1404032071030740c0c815200344000a035034100300c0b03025034420950141d0002c0c480d0001619000c2c3c6510750625a07002038000851210002984108560b0480a1074440050030740e081e500703080744640050b00074040c8070350141805280600140c450044001d001e8007802ca18034045445507103074104011086118602140c06100740144402c15240c80c2c4552802d041d22060450307003150512000310017800c920f4208400b503110034800c505504101c0010391070a0b4000354001a00c94020000d0b001c0e403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 934146555 1250 934145305 934145347
    0xa2315030304080721060c321813050405150f0c16050f0115060306050301050f04030c031701120203101103070e011b0303050415020301050d2003060705 67
    0x200354020031003000081c00104014080710490004204121524a01c1040302600310700006c104900c1c0100e91140c5a0308071510310214050041c0300d803801e0b15488031850f40714246c0d0700b1980e0456010301010062107540340300f04200040207407007141e07100e0086c49402c2c00d407070013038400b11001e822071002c49000e08800410694040a07104585a00c1d041480c0400414407900310301210300117601c00f910082c842c0802c0b05040d4189048e008010010000d0302070040f40d0443d000390f000290812000051600d01405101e005801e44444200940c4540c0d80a990300070580d08100d00340500c0300901031a50142811081c02001b403c22001e6203002248105410002403103001210246003056110341c000c0d5120070b80707902800604104030300324240001a241d0003904a0781410101d07582e542041059810b400541c00f40d0b105440c401d00c29090011313503100303034002401095000114081035101040781c0c03a6114040b02c01216054108001520210741032403011a0441d022440001e0554650010f5400500e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 934147805 1250 934146555 934146559
    0x21f0504030f080c070b0601020a0218091e12090a0f03080301061103030403020d0e0a0f1e0501080103051506040e01020a020c030d0306080c0607030512040c0306050105060a05120a2315 81
    0x36040c600444c0204250141d894050000b8103500005a610390082000c0d0351203540040282414201c510280600c40c1d0040700d0004490107101944060006030030f08a03241900720001400c0482c903503154220450b0003402d4032540c482c014090002c2c0b500c440d040e0440c0130b180503e80183d520b41c1084006030501e800000160440c1d4410810080842d0380464040b064160341d00c0c10061140b404800111500c903541c10020a0704041000080c4040030402c5010504001c1504007407415590360041d94942c80921000c0c0c20780e000150811051089071000340d901c034100400005035018080300003030072608442c04010245c0e101d2040c0c5820380c5001c21000310000c03090701c3c1c144150303814090703501c0e141c10588103051700600c0042000c1c820540510242c600002c511001c424403403406051001001606100580d43d0b5450303c0d0021445041810407500c58810b9521260301e00485810070400b401001040c484000b84d54050400b00b6004034048107407069810901d4095070308045408408128001c081c280c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 934149055 1250 934147805 934147817
    0x915080105010f08041e151d190302070e0c1303050c090105040b060d0504051c0f080901020333042c1c0c0516030605010905090f0319021f0504030f 65
    0x3490401d14506c601419900c00c1c14070001362030f00148019019900c206031605003c4140e0f034045400000e00300001140c0100c5071004200009090302c403c083c000900141c03c0460140b218010003d045908451203940603232500302d03000051800226070390001c6600780c000d900385086034942016541c1c050042168100556150140001c150344190b410804030180c4550000d01849001e00c52a40c540184800394002c001c11140001c115502000201c0c000c0340d00c200100e40c200505109076440703120801c0701c8101e0052a0800050b138110072003c2c04080109140c543d4065403039074000c4588020144910780310211140c0700900b83c080c9151b42558196200c00d12100c41c2c0025009813190b40d0502e0b0500800c040000d09000e400c0041c507803003c0350b00030039424001041202c1c65110070b040b0380d0050420041500c4105400d9114912001f41d40010750041c003d00c0c0003100091a903609400c00c5004882003540b080d846485a00c003010401020160b07120704010505410074240c0c41201003620f041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 934150305 1250 934149055 934149061
    0x9070e131b0309170403080327070b0c0109171312050c040905030c03210603010b09010b25060905010e06190207060b030319110c090c03070915080105010f08 69
    0x2080e0791005070075040101510ba0f45814240150301076246142c6140f84802a41e45480703090001043c0d1054481000d041d00601c00b0b25142c0858003072804510090300040c14110f858419860074941000158400702d569407020030000030001f164000e00b0545d01402e136600e811401945007a0300e6459404030100da01715140d103000180f000b280340500c00b4000c44000540f203105040940c598064501c0002040c40005004c3e590858541114140c00368203010b829250358034403050500f0795400c00415600813045178018045025a03002405c1c4580b564040007083c8111115160b6030090120000e03602181c0d102402003d1001c00e00a50502800d0a00140703960b082540003600d001d001c404103189156030210703681040240c90341010080d00c00080c11a500c1d40031528414018946d045400c0d408910f1808a91803206808640203115100c01014140641d071801809101a440142200d0411400750390104056501000354641100240d031030640960401001500b0700442146480a00c4021020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 934151555 1250 934150305 934150331
    0x9070510030e0c060f07080c011505040e0d08070201020922051005011d0102192a061706030c0a1203080f130f03031d0c03010b060325090509070e13 65
    0x505405903c1642d0701641e5004031041c03c01030b4041d1410080c00703550000b815001e500415004400a24508000610500d540d88100800c5400665081a058100401800865002d400d021768003060078000503181a00c03032400a04201d030f04898046607003640d403803201e4660010380703c0d03650302148413680403214074181800a041000004c2c0102040c0f00109248499a4130038006940d009079641d90111401005141c41c4101c8030041c8038184541140c8001c0200416030040d5540807103a003038445001d55a4400d44188122100611594051003070302e2030241144c031942240b200a00031162044254140c0c1e25009084100103061220f4616015050200404131610f0181c03403030354050b030407410b13440d040d140560150000b00c500e4890300c01c6450107030844020100f4180e43d185000c9000300305451000d42002028042034501c0c1550f04201d10b0503220484103500400034107851402d2043c00c031950f41001540081d8100d401000068500307124240c1c904012900700320f0302e00d11031406e020030890400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 934152805 1250 934151555 934151563
    0x2100902011b06290102010c0806060414041104060e1f0f120e072309040b0f070c0519021203071511130e1b04030c12081209070510030e 60
    0x1100e60400502c81c0300b18401c008495000803a280e1140d06118840407824008103100118400c01c1409542006008810307580f141d00c085100d00c000611a41c101402d1800c8440360303005482d0110307001940d800140c120b1170301010150008003203960300d0740d0403031007560140040041503040b1000740ca180840003030340c2550085482d02c0309821a1030b00800c0041804210301c042c00e025201007480d4010380c2c401040950320505955400020f4407080c0c012440140207100d4010301c2150054089042140440d59620190500d1600140a40b80118092005450707140c1402c5039080f00e4078000c44034400b45011418001d1140724071102070b4000d1402e0450680310351204440e00340c078041700030f035403075900d070700e00c07406020a8504403209142c0c00920140c5810034401460000e4502207c03204d500603500d0401034072003040781c046c0c980c0180042c0702c50380b0381451454180e11aa1080343e0300f1405010003903180160500c81e5126803401001005010b03d00018030031100560550b400800d070604049816140d0300203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 934154055 1250 934152805 934152827
    0x7020a08071d04080426010623040902031213031104050123190b0c06090c060a0f0e060d05100e0c040e04020a0b1c3218030c0106060210090201 63
    0x510071004540e0ba03403401d0312072481541c00001d5a240084561280d4140381c4100d5800400d591740204070141d1038402c5691001c209c414070200b42c03c645102c06419003483d800c14040300740302804451a20145040c01c0f031041e001920a0901e044030003600700b00348406c0070b801525110041d901040f0f43c0d4144a80b28010f04045180325001d1000d0303030400d01c80c07030702c2d00000424496048001d82e50034a0715441002c4942e03014800e07100aa00c100000304100c0d40c008500b46006580003040e0a00c0c2603e4108140d881d5000a1114000c0c405581010340c460780b203410090169051020740000c0c18540203420552031540c9404c1541188403002c20881e00045440841e001c0c2c48400140d003040361390340d1002500e00718150700511800c00c070108540a280112040d503054080404030203022026414201200400304010b0000020f0160711107014520b03000c040c401d80000040d640f03d10720b00d50800c0c050340785034000040e110040e95128420024694103100c03490f9040c40c489401e0040c0358851b00003c046005c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 934155305 1250 934154055 934154099
    0x604060b090708042006040612150501020d20100606110d0518130903051314060706020c0c030106080c040f0614010e031009030c0c06210c09090e0307020a0807 70
    0x2091401300011000c6020612405c003c10784c1d030307070b591322004001c0a001c2c0e4524104003440c1810184203829644080f90b00960700103138000c00c0004400c00c4112101038404403008204034440e048088080014804060011544079010550900c1c107200140203c40c083d500542e2604040012032207190300c94110f50040000a2908500518034800940c0a4001e0740c184a0564503282007031081540140103060903a0103685000700130340e80ca00100420b00449800103500c00303403c04c0720000288066020f800441440d000311404c54000d070b80840c0c00c480e0250014145940300b51a21109441d087c01540140082410103006103450201c1c400400d180c541d00c0c641c14030044c410740c1d020a48040240407600c0100840034030043c0854140545001440c1906681d20184040302003100f501507a40c28921420700610a511301099410000c000c144000040081100c00600060041d103c1d009810001902c00003856451415204008050010b540410f01c1c6801c6140104442041c0c2a601d00e882509 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 934156555 1250 934155305 934155323
    0xb041208070203030f190b03031206032a06031305031b07080123060103150f030b281116030201020d05060d08030703020d27030806012313170604060b09070804 70
    0x12039484806401c264401c01c1d0127201c0802d400140c41d41c400c02c0d41d4000c3e2404c1c0e059130041d419070340b10300d900081c0400c2d01d0fa019507200465440300e42841c3c00210340c01100300c2d8204000e10030310b54a003401d690101210950080c6070100c1394042c004244130800052815100070481102e007819110390203022031a042c0352100780200000c03842c0c0d000b0380044007801041040030340c10548811a20b0f0029840d13000c16510f95101100048000b4264201140f251202c900c03070002c5d0030f0204071558064050840d0000150005001041140404180000055200360000760f10303400003000c040100e80000b0b000c180702d40d0b040c0421501040c08101200d4128555140150382d40f6040d000c0c0d0f9004d0034000349100b2030754900240d5228804401c290020095110340c1c0e4200d1541c0b2450011219022851090b101064090202c54800e0320000000e1019407036002d240d20500780c0c0c0310603011070030101d42141d08242c1c000b00100000c0018078491081c00e54412030307503a100b505020320010070000e0020002030200e22 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 934157805 1250 934156555 934156591
    0xc090f06060206010515131a0703030e01091e050f0f0304050405060a0302100f090f030b040327052e020d0807050703020309091e100f0807030809040c0c0b041208070203030f 76
    0x70400180700090b050801081321840d0040c20110234952143d0340c1500000e143c2102c40075003075418080e5111407500a01c540680b061001d07090030003801c2c2500c4c1194640300d10088000020700a000005000b841040a141c41d9441c0800344404d48000401030b51050b0526041480140d44c0c01c0800d24101c91145400c841904403100d0a90f2100400d03003050580d003108040002c10802020405032040b4413aa55010000031414800c03c2002000401d507020700180a80600150500049110f00202c0340541884040031103035600a009015240300340050f042140c920720410782100e40d00d50401c0903483d02034600744090301d0003500d03802551880d51160ba55100421582010003401601620901d03088032501d040404c009a8002018492040c00c503030400f900155074500400d816088980113010780345004001e0302000001c255400f0244107001c101c00004012401c030b1050305114a1084400203041204070030040c280c0040140228119481041003214810a0011751b079000740e5007019103003a0380 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 934159055 1250 934157805 934157827
    0x10e120f03130506090106150c03020a0b0a0204030b040b01060813031706150a0305060a0f0e220f11040f06031a09010e0d0504050a0e01030314030a090c090f06060206010515 76
    0x30000068210300c07070311301407044d9110194040b074101c84141072801082c8200c607106990803c404100500540c000407404408121421400c030742c4104100d40041c5015281e0f5190b60f4074000075603096031010360102c01400200c1e040701260343c120043d1130108202e010707283d40081902414400902e6a1602d8002003030403520b495862084100e000e10883e078655103180d0008000305011161140700311800e02c0009407035000e000c0c095094036801c6400401360ba841003422910120990300350006aa0008880c1c0040380c0585800901c2034400e00c0c480c040031928000300416200000c2404d003002d840c12008100142c406601c00000292800704038441e40c4c2c0d03105a442c01000b80c611015280c1c043d0214001003554400f000700283ca004681c0c0348001501c1b0104486d00b14800d000080c0810740d890020700c0315803011005154442100c500c0030645402580d078595620035035078011074080352503450000c1030a00a00920019042600c003c1c01c00303601d0000002c82840c1e4101100040e5000098210580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 934160305 1250 934159055 934159081
    0x40302040e0a0b0709080a030834080606180d111c0201080a0204030809060c07090c0c061d120c010b0d1103060f01060e15090a060e03010e120f03 64
    0x11500280100115181c40c46440d442c0d520584040328003814040006195a00a40e00384054411500080c003585c0c100f660265180b16002d002e00354010080122020307182c1e001c80000c040c12007214160269200b071510041c16020b005840d051280005104034013120744103101000140303004880310b154001840c2480400802030300e188a4000e41d6280c80326400001324150104100d100307980d089030b9a0f40d082c840904134000c502005103400401c1000d42c0c214034009001c0c041c8642e802040d41d50b220b03528880007048800c840c5000b004246c03e0804001031015a100c5c86001c1d03100280f0640b00340c85c1054a1030744800f86c1030120356a890021888009480b025445240d517518040c10b04420070b000c0e400c009840c10b81141c1c02500c240700b01d000042b0034260380c0d00414103d076001c1d11140804280307d0200048504c01d1100740160a809000300202031341c405660b980200402c4d12414440300100007071502307503a44e10a0460740380e800361901b05c3d411110700e0201c5c1c078035401d41c3c90265100d03150000c0070412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 934161555 1250 934160305 934160309
    0xb0c1c0c060614010207080604150c051303120f0309021503070908030c1e07030b04080a03020c030d151202010203031504021b0609010507030b0d0209090f010f02040f0e100b0702040204 81
    0x915031609001003100e101480c520562103e007602221601d903514014181c0d1088116030013010120499048070f03030290581c203c4d00c0d03200e485041031800e00d000d6045580c5508919030041e0b0b60f0441d0b481003000710680201140710380614a1809010511164020601c00c08036141824600200040000c2e849481200d8800c0500b105c2419030360703941b942040e51652030020258009016165550b03112990b07800250200807070380c0c458141d40642e07032a912030300516000240310340c0034960200440340d000c48040c0001c2410204800c80007a03402001d80100e00e4449040d0084038802004c503000e400540c2e00001640d030702ca8030501c400da01440304180070030080d01400d04100c070168003815200c001d052011070003501c1504030303600130022641c1d040b1049050f6294801520b411284550380d80d4090b0400c500306a0f8084441000c6903100d071b581d034500030300311410141c0c0808041d40c0400c0600850012841d40e500420800078844407900f4915111040d41003148030f8500303030a000060205c2152a00d40550300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 934162805 1250 934161555 934161563
    0x1501030f02040303031a120703030509010203070f0605091002041802210f070e0a15050a03090b010f0302011805150705010e1e0d0c15020703021908130b0c1c0c 70
    0xb4446039a45000340103013288007605c0c504400604c007403640505003d0f401070a0303d1207100050a400d4034585098800b41d100d06901130440c0800c0052034007107499003440ca10502c0c0b05440c000b5051602d048580d08008541d0f00444000d801000100220318042c55103183c0b0181003003005030b550100580c05000d200c2c1039040d0000e440c20040800500c611446010780c407c002e2611002e000109a10401c154030841e40240612544000860a1014451405018581400c0c2000607030102941c4a016668900341d12165581c02c0d0804148215640460342a8030603d8809401580900f02000603151600d03204030940304c0e074000300c4c50f5418440250061b11848030340d030003514116070030708403400b858241341d59805020780b080c1c00109141d01c0c0314000c28074400e0340203880100c0000c1602041c00c007135804044203a08602c10342102411803920701d5403010350684a00380d0f02e075803003500d03001301e4035156030980c0400011403040c010001c0e00400840c410340c00140310801c1140f10854650181d4101c440750300050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 934164055 1250 934162805 934162807
    0x7091803030f1a151903150b1306080a140a06090b0306010f0611031903050402011e02060601030f0603080d2a020a2306190605030a0f08160b070c17030f1501030f02 72
    0x180c03520b0301544640d540c006043d00850060b5124aa4440d0398400c64000c440484c030800000c101c5a40308212f440d410140300c0c02d022984000c00d143c0319521840c19140c100030590360300002c205900c00c61280c07000c03801065000c0c2845600d400d0018014080034403500c03090006008d03001003041c406008030752116051110400d00c818034040002d00800046400300c1c08592007120041c00407508083e41001c603e020b500500340c42d40c8510045000e05084035001040c50386400001c400114140040c2c40345502010000505169141f28101ca81c0030444480d80c0810510381e0000d9403030342c085000b07400f858011842c60342c40440420300460b003502c00f03800c1402c0c500801c0306011035060341015628510341210390034804d186d1103904240c0c41d01054880181030b80035550030740e80010803003009810f80320b0f0207400d402010305080d202c0d001c01100886291000603004842e03601007010284280380580c440545030b030b05603d424810040210347c050300b003081c1d050004c601130045038420741240c00d902e08450429 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 934165305 1250 934164055 934164097
    0x20c0603090609070909050616030e2e060602060f0402132a02030c0709090f0c0e04051207030c03050717040b040e0c032707091803030f1a15 62
    0x4075440b0602501d107000c20b0300401c2c800080701103160180e400d450750094050401034a51640340109410480411024151210f55085404800348842004138032010500b5260071000d1388541e2200100b003181c00c0c03400c1c1c600003040c072145a0005080e580041200c030851501d40f10750001620081c00122107070011402c11312041000d0340e1141019000d241c11880e86800f8000303002d0207070f8427401076100010b440da000020800009506420000785203004a440b0a07a48801e51600d514800e843d8005204005a200600041000c208180300181d100c07651103904010740e03560010714444252078003030104500429410203105070a0304c0c1c1040301c001151411340d00d03035651142d5402c503000b03032181a801c1d1540c040000c803070700e00701000c80703224043c802741081844072000d215800400d45811103011511402d58081400314076031044809444440e0700d003140c0c0580c03510f401000d45081000150040b41000c50f80070f504202103c0c03c01e81184126440f00c1c2800c0b041016014601a102c0d036a1142e411500c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 934166555 1250 934165305 934165321
    0x90103080705160510210e010b13060f05060304082106010f0201051302040905070f0311040f0b090103080306120a060209010906110703060b06040306020c070504060515040510020c0603 81
    0x60010750702c10001e4070303242000e03801c49203505006481225002102d1101c02d1846900c80c41216035a5000c0da51581e40c4825030b40d18140c02c4890385001c24010307a654404008040c580030404403103180c0300481c144070b200d0800350390b80c40c0200e052003010f018480c0131010504101703480042c2c0e074011811142000307204081d031515402d5803100380c4038903010654020b802c690061040c0076052049540360707031060a0700925801d02008100d01712003500c560045113000b043e030a104800b100000d5015a40103a8800c003901c04200c110f981c051510b0110925140c4040e6240c3c032040501411203401c120001d80713030307aa2400880c81c010130410900c1111b000d40d40c281020072130a540504114102aa142d004154a50a068038070140020703040d0b0156110074002c000081080c0c000c0750880e200a00f001e0b0400e03559a44480590b0060604058aa08410001e0004d03042030710032000180310031034150b8006401045c0f030b007180340705d2401100d0290001280c007119150080000740d40014000c2c0c0702580e40d02d80400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 934167805 1250 934166555 934166557
    0x203061006080c0708040311210d03050f010509041202190807051c02030f130e01180506010503060105040612020f160b0606072003160b1213030807080a0b09010308 72
    0x601404108401d0101e2031920142040e513a449a201c81c0f010f2505046459526a032981401d20a034801d001403010551000080042c03544000c015004041403110310384d0190036620000c1940000a081200422041d51450641e81c5c0058000d05c5000f03510860300022420b00d05c0202240f0500c00050300c2101c01c001080c0024500d2a0185041d62800a86401c0c040c82c03100c05148000016441400101915126100201a841e641c50080030207980d440e40302071003040c002d03030010546001040920302c0c0c20070715008060340321000f440e081d407035860035800180c414042da0141d00104a001c41c443c0b050b417038040d03040720344c1958501c0c2c03003d4807442c0420f01d40e99007032100442160902160030200308581800800e44000c1d6520030b00b0948a80369025400409038071184c21583d15204969030380401024042508010300320210704103646001e1a42032040058010b03001d450320f45c03070907103050004c01e5200a4030360300003240b0b2400b100e00307444070140c440c040c048803041c2561000040c0000410404000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 934169055 1250 934167805 934167809
    0x20f0d140d0929031f18020d0e070f0b0a2a020316060c0f064208060c03090703050d0c03030b010503090a141006080601050109050d170d0902030610 65
    0x2241403200004000711a184100301e800d5141c14100f024008200d0403980c03c0300340803013009030300e01e190860f82d502e10710404007182404a030324050758005411060400c142c007910003003202d001d006040e0940f400040307120f60342d494070800314480d00c04104040c040d8410403c0743c0043c07114426647c0c9a0b003075910601c00040c01100200d1103485445944803141e00b0784c0c40400c00322205511501030705180b03500c0b00341c24071400d104116000b565910010b617113500c0c1d0400e9500500e011030a801110507400c1c20a00c0d161204203440b119480e241c5404100b280030004990340e00030f401c014459200e03100e81c0d02207458000c0c1900000d013140290100320241300c1e4042c080c00400350103581c052000c3c0e4003100046d2107500c415503017800790707412007504203004c03502c403910080c50002c00c40200c3c3c071010b10f00000e80f070071a141900004016000344004111385d6034001190009410112111644166241c1e10000403a20750020000e00c0c0b800072646102091540e07000d16440b1750003906550f031515082e07030400110340180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 934170305 1250 934169055 934169069
    0xb09040506061810030f14031c150302090c09150a05031621110904140402040e03210615071407090204050f01030f060f0b07110d020f0d140d09 63
    0x1c842810f248002900e20034002c00290680e03411440c195191000e419034401e03011b443c0649103000301c0106290400080181c6103140e10f0485000071440ca400b0f0503035460740d180d204031400215040c000750752016030058010110302040c60341c070541500410182070300188404400940820718070b28654200780150300c680c800c50440c01700d14250b540165620100304074060f10407800c03030b00c0807402c96585500404a16190780031031424410400d000800707175540c03410404c48803440b00041c80114242070003804410b41c0d0341b002650400c80050040c01c4981d0900c03001c89000310310000450069250001c69440b40181c1192051b541e144900f040d050321342406034034000900c60042d00003503064062003a01d09440c0020b11180c140c030000030045025016a0016104032030780e8800015200c2081406c000090181c032404c01d40f213000d1401d10411421401148600800c41260010b00503074030300390204810f11044548080105880c14407040301e00b903c403110841442020000c541240c1c120505004031046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 934171555 1250 934170305 934170319
    0x1509040b040906050f0a0f180f030314090307050f011a090705070203100b10020a210302160507081006050a0306050a0209090a150b070510050402010c080f09041a0d080a030b0904050606 81
    0x112a8403c00c80d150304600705900301c10017108d60000f803a40c160024009001b4640450994440c102404098200f84e600030500c3d070000500600700f103000d00c95205240d81e40360080042c0302003400c40100b10800d1411140c072a02e200d40005001d41d00a106544180d50060122a03001d2003030701e8141d0041a003800c0c658401d00c21100240d5400d44001030f07020440d50b006a0780894551b1614000b8094120104c000040c035070280b180c15002c44600740402c0703056025400a00d607007450300c04002d04140707030340103080c41d11424450140455121112400100c81c0d0207c000120307035607981041741c020300403c41c0c032a038000d4605041c00030850250708418602080c8105000010303540320340d0024184161030f4002d0803a0000441100e20740d07616070240e0b0b481030040c1000ca00c050044d68a00302c0d10303400b0044041905501150800450030f10740300301030b8004205008516256207640c006101c8100d400c50003007000c04c1c001018000284a900801c01c50140640310070309504080c5041380e12074404031521801129 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 934172661 1106 934171555 934171571
    0x170a0e061f0501050f0703050f0d0f29031b0f10030e0c120a060504060b031b130c0f0f17010b13051509040b040906050f0a 54
    0xc0303031648511180101d03a890440c40ea058014034100035040c4001c0045422980442c0d011981600701140c6402e02e00240044600c00d0200002c03145003001c00b0b20700d4248060b0407405081c0c181c8402502403143d8002c0d40c84e00e03900051845e0354194480c82c0e050500c84021195200c031840e014210201c0d05030024080790103454031300b10740e1000940d01c0c0012541d40d0818442c0a00c04441240d212a0344c0f03032403002190340c8094081010b40401c0e81ca2012800f001010b0340b0000d00b40d10f001d42900c1c980d2680051001030407080742e02c01c5004010400200074081803d20510061a689841c0c120280c441e00c24102d41c48082c81340100281f150710042d00700e603440804c240300c2c001d00c1c071048030720341d200c00d142404c0e005402e803580304a0040e108101c011040d11a1403040d24001c4001350b90000b1140b030b4220000340a81044d0170080d01483c506020301002000b00c0c18600c0c8207116030b42c01400004 = true := by decide +kernel

theorem cover : BRFrame.Cov 933992805 934172661 := by
  have h0 := BRFrame.cov_init 933992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933992805 ≤ n) (h2 : n < 934172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
