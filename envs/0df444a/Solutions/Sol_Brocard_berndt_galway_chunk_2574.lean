-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:06:40.739535+00:00
-- url     : https://prove2.me/submissions/3d8bc4db-6b4c-4e73-bc22-c28afbc4b681

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462769784 ≤ n < 462949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462771034 1250 462769784 462769787
    0x804052a0406030f020406120c030201031a040203090a05190b06101b030c060609060b18031e030c16062718051b2703010e120c120a0c0201 61
    0x100c04260003a51000008500d191001408031400360340704544284101c811034081d45814483e00c0700400c1480080004c890f6240e0743c5414281c02070200034141540d4400110380001c0c8190400c0b200c50b409082190740c0c0c2030859000e41e5940101e5012185481101010a03842425200d85542141d0051100c00c0c00d4486008010a01d5022078182e0f003000b05440d070b0a0003142491404580f4580607880319405010a400c0400a944142d00200109030810382d0030001032510f07034121b038032070b1486140302002d140718500001c0c14800740c0384108034014941c070b840d0103240f10301000521648400c41d007211081c0030031013080c030030000c10f9100d10f1022425140c440e507807c0390b1001c440100c0007205c01a000e101c5480340802d000d071650b58001201601e50796000c014032a40b400100d000342d004580402030030010b02280e44035a8810703004151611311100740c0350320071980302500031400a029500030b03544400a42d0030210f036039030002c07105144d2600c02c030000b41411020f19011140003105036600c002c1c0d490b045400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462772284 1250 462771034 462771073
    0x100f1415030706110f060106080f0702070b0d020306011101060602030903010b0a0e011502011e0b0103140603030a0c02030106120506090d030606230903010606020c0a0e0f0a0908210105090106080405 87
    0x1d82e015400380c02071942c217151052011501800d001e84491951381400b60300000c0c2507000600700402d540c000c07030082c0050365102055034181c002814001da40c9940d4400122480c400826503d80c0c55803c0c290045062031700400549860b020543c020880e0782c9a841c00c101c4104a18840e51120b1410800140800013554114400c84c040500000c01c111404c45000c070b508200c0c01d141584100d642e811407810560307050043c0344442c20121054522401c01d500000c0d243e01c03c511608040c03203c10000340c011500e0a4010f440100082d00f801c0066188500b0550780782c283c1215658041d00a8601c0c511500d40240318101c00e4079543d030395540041d2601315846075550206e10f6440904841404a400603960900481e405456282c2c064400e4040300340034000b00080c0c0703030452080c89081808008a40908500c151fa1059400b038010841c42924140301003075114030801005205c3d01c0000003070b65540706050440c102c5400b502d0080c43c5a030396072011941d4800907580100150060801c9104010a080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462773534 1250 462772284 462772307
    0x1120b0a0312140d060e090318060d0608070b030106090506040f05010e0409051b040e07050f0f190905040c06080c2a0709050406050c0702060403080309100f1415030706 74
    0x82c0310f907100e011401d03400030359005060008642034460205005c0000706103003103600403890000841c280050150b503004841740100d01e00e40996400300d00313005283c000340c0200d0010070704001503d151070384980c511001c650090140381c010440d1084001440c0c18410212030868003903500100c9524281001101c1251100503015070007a1a40710040c017141050208820b19105100200341c0039002c4024403060350a13440403840c058000745400c00c0541c0710380401d4220380c1c0701120196080003080c00007810480c40720781e881c48010307101c15004c00d03a0001d9a0010307015501402e074400440b50303240c404840502d0110350751052404144140840c00c0401c0d000180b40340782d40400200032394040c0461a18110107603119018aa4440c400d00080c00090704c12943c0150410741080e01d04401038000c40c40b188602e00c0003c00140c800000034a2034482400103070980411040c0501401e01962650710103400c901d4082c022040e0800c3c0070840103518181c840d00c910202501800186140801c169102c56000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462774784 1250 462773534 462773537
    0x8010b0a0311030915070e0f010e210304090e0703020d020d060f0509010212011509060807030609091505090a3f020a0c08030306031b19090b01120b0a0312 68
    0x4003041021085002e01031840b035a80c62009020f40495000808080b20025000c0c03000e00c10003216049880e08c400000001350703002800c0000c510800f11f004602d00e99a600c0803104101c1d058007030300698040100003481107840a440c180311003501d80e00c44548481451000035801003010345500018280354079040c20351750007100c00040804991b804441916011516086aa540010001d400d45007142c0000d0240452005c511110a60140007a040b02040e00910040c4548000012003c500c280c00c000003802c00d20b032007804004c4c428a0003e40c0b400160155a900f03c0c1010006507002100084036501c181e004030640300c040c48003020012641e2a4242d4100380111078440300e0340559901180ca5403620300940c0284800350860a05464100c030359009145960420021b222250750b00041211940900c1000c09003448050350000b4240701d2a40f0404035410a1010001b0f081c1201c0d0b4400100848203880e000d070400024580c0c40e04a899452007154489200401800030402040800c041c0c070019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462776034 1250 462774784 462774791
    0xb03070309060f05010305010b0a090216030e1f210506010905130e03120105041107053c2505030715021906091a0705070f080d020c0105011a0a08010b0a03 68
    0x1072455442130700c2090f0004c3d50507030f454840c00c14443c100241002d000b8107200100714104002850080c1c06081c1c108805000c0000307601a44804e0b41d203034503030040c4440110742400c0300ba21700380344080d0181c038600303013041c1139041140b012400050150084034400c540596901e44035600f003404128011342c03010700c140c1d10303996504400024502d0420090425445800354107426603d07050810090b103460031440c00b40002c05100c0100001c50026040203002909044074030040025058103101070390358030b030364001e040d191041c03000210b00200c0c00114072031200d82c840541010f03c1800c1c00f01c0303a181d0300c1190381680c0111420001e50510055001040d50341c3c2c4107407084010081c5180d4030015250009a07007142da1140e640c000c024480c0c80381100052040009001c07454400001390060045917009400b041e940302d0311000700a1840200d5144a080003000c6440b00b00c9412070900811090055102100b1b416480b820801003d5059405a05e059501c0d02c42030380c2080c4195a03150420541c0780245a00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462777284 1250 462776034 462776051
    0x250f03020c031305040c0302070b0406050a021317010b0103050106020309040e01020909041406010609030c0513091202100b090c0a0f051c09030e0405040506010515090907030e160b0307030906 84
    0x90a000400f84000e140d0100d0750414280410003040340c3e894801c0e401030600c104800e000040c5280f810541c459040308001030300707644500b4001c010340300d05110005004034901e8081400c070089080d40c45444407040081088880300001036080f50000c0c000d56000d80c0c01841800b810385441d800c0700c2107401520001504091458001c581d80c103409076802c482903000203440d208401c00811440340180703228500f04902d01d1541c1c44183c902c9116014082c00340303540c84003015480919412101d007195110405980301714614030001c3d140d440c548802087d4904014040f080d515002c010940030b41940c00c0c0d80d44c900301e1070034015141c1000c05090002400010300c174040c10840700348030441002c100210301140c24021b0b864010030f0301d0035440c9090302c110300d410103010210780002400342c1907a0007622135042205410803880044d00800780841e602801e580c081110340d5034150000c9100c020b540d011100700241c00418002012000d005082c603e0704240000741f00c4034401c0d00041015401802d0002d800c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462778534 1250 462777284 462777307
    0xe04030804031128081e0c0f010b060406050d091a0a0b1509040207020d0c0b1305101d030a020901090606080c070f03180b0a021507020a02060405040f0e030403030c0308250f0302 78
    0x4013041018071115401007902d16107c00700f440f20a04040b0380000811000e4146000160a40500d0044004014020401c000000c05940c4818089504005800c042401464400d0120101115248002801c1000c00303252400d19242c04880d80f134040f9045402c2800900600c0000c1d00108000e0340c0c088041010380022a0f211961200500504c41d612035641e80c4901184003100600c0c0c0c00742d03004444e42c070107980318117034803103114030f56800b4000c600341c0d480e203804001901d40301500c180654003200c1e03400002500c180552022040702e080b03880300c0c08a640c2d00b6021005c82c0c084c0704400750214010081041c0000d00c280a001a081c40f19400700c8409034030f800300059036810246014015920030b03144902482095042c45070700c65031502c0208801003103039001c01c15a015910070746001d15121424400c1241c07071604a580c1c60703106001201d48880e0340e400d001302084000c420580c0030440600200c0c1c114587e59803d501900304544c0910360034004000100c1c0c0e01c00b00768911004240e800e100f8500c590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462779784 1250 462778534 462778567
    0x5101b11120114220b19060f0311030307082212030225050d06020c0309060a05030a05010f030b070c03020f010e2d071e0e0403080403112808 62
    0x6207410340c00014900c0344501440389651000e0710745090f40c10b412006144140c02c3e01070200e002680001e028000f03032600007070780d41c41860100c1d52a03c42c034100003000c80d06042c0711022104590246ca81c10801c41581010726032644158003010380940810460f00c0c180000c6801b046200045402d910002156030b284050b203000c0300384c48200c00580100c80442048125840c1000b50415404c4145e12100e24020004403d00e11244d401040250041558440c2910900c203940f8641800341010340d45907420031380103080d503104561400106d4030b0b0900105510310304107501d070300352984136010100d01e80340c0d0309068401c00740b030000450840c45150600103500c2000e010354000200303003100030700d415290302624111600809c008110440c50094429140a8001a032038040300e83c45628540101c100c0768040305204202d03004001058482c0301404201540072030724920640c0079a070703642e0810a0100809441e01c10f0aa00d0801444400c0718900000400e10150043d4910a90b00b081c038040e0100c0c040580c2c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462781034 1250 462779784 462779809
    0x807080f0d021804060602030a0f0c0b1e01060f0c0b09030d0614030c01020105040f1b0b04080601240c0303020d0b030f0304060816210e03120106020705101b11 70
    0xc0750b0041940311081c0554142207544460440b07060141c1c0f810b0040080d6240290000c0714100090310360b00312500380c0104640c1510030b41051200039546048048032091180d01303006880075160903400000ea0a04c50348440104101035a580f8001d00301580b65000091000740c803000c41703030000708222442500c05118032001000d058905010b40b8284c2c5040609151000740b00ca810359042208000014624110b0720754010740c00306411198201c01d40440a0701000b541155015040001d004039140c14000341090407100d4040c218003800c1e00218041950101c04029100411100503601000a00a4000d020342079508400092103641e4000020715029842e10b4010040d04005001d2017000d5000100e50342c4400a600b480684000602008040c07070401c142101d0410700450260b80440c1ca280c200c0b00010aa1000700c0b40c80316030010b05420303400c4e02032150402511410788001081d041603041804684096101c02c1203c2042010001444041020171a20001100b0702d54040f5900c03180071249 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462782284 1250 462781034 462781057
    0x10c0311031809010b18040c051e541804122f010207060207060b0a0905091f0e01020c0a060e0303013012170a0e0304030807080f 57
    0x2201242050006001060b08105d00080c070401050049060100c00c500d5417110640d0001649494580c1c102c0e150b000e001e9400c40000c0d401b41c1080310a81e1500302501848440300030464803400702c030401702c3c4460130261882046101090f000c11040c001902e02034a0042d95880c41c2c0b2a0640a00010f5011a094003200c0d07144103000042c0070034000d95148141ea1041d00d820090300e4203008042c10b088406038013030b0410b05540c01c0e04181c01401029015110356990116040d5202c01e0149072081c050f12520140c80d000d19804c1d83d0008043d03c0d14010103000340d902d0000360805941544400300601001240c07540030584403108000540e8092004000150341203025010400c01407405c5c50540c0c0a02d00310044562040c00140105801e280010b0007804000c1035100a03000c1c10711b40c03128160241a400340016500c184200d030300d640c000542000100030300307400404c40e03512503210604803842d05140e18026482403205000048a40c4010005c3c503000c0d141c1e05080c00c185501790402540101030150f03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462783534 1250 462782284 462782317
    0xf070303050604020c071e0513020a0e0d03350c040f06050903070923090d11010e07060e0a0b031003060606030b03060c16051b090106020604050c010c031103 69
    0x42850380c1403280c00d03040341003114298502000b414207142c0d21111401803200081c10241d0308152181c80c05c1d040782c010600645910074003100c0d0a0804000d41143c0485008100f40f00c0810710540382c000f801146440d071685550b080000d008072100b856800039620b00000c6032a03000701ca45103540d1001c1d202c1c03107440f442240d0743d501c5003403a4007880085203d5103d0000c1c4007007440444280d5078003080840654645c00d40001e40c0903150b40107610a0f2088a01003201d01c918202441000000401e04030520141615655502c9442c1e0b040d0340c2c01c0ba4000d0340f001c48240c0050205101c29841586507800c007002c010040380040341c881e2154031140e0700c159903090141c0811841001004840e01079840200b4090030204520880b0b1404207480b03030b80c000c101e5030a10800060780d101c40118004450400c1c0d030480200e030b80070182c4018003201c078203003e88000d2160031104000039a81d480013640d54880d80c0d010000e800302c03814440040d01c2d0811068400c40511042c1004c0ca141d402042000d011955408000e12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462784784 1250 462783534 462783547
    0xd050c0414010504030f120c0816020901050f130e01090209180c04050403050901210204030b040c0e01050604060503100e040506160e030705010c0f050d0908010f0504120e0301110f 79
    0x90420250301c101a041c4081031004001217030b01190041400c0350000c000c1807d00c441e01b40200c2d04614010001440002e01184100040102d0003043c652644250b521005c4c9980f103004014000c0b142d003410759404044140003441e455203580000031403445c15000403a40310076960000318504002c0300d00c02840f00d062480b50040c0907041041c42003140c800c2c0c60802490400b80c500a080d8401c00340101d05002480d11550351a0303500c070b00006c484105500c411512340c0d49a1400055280303040d203040c0c80d0035202d21004600b02125081090403104001c082614207032401a0644a9410040810160241ea400000b406100114410384140d2052004d0301182c6026905921400d00e95020b83e03007084145484010f81e920005034030000d0300c4003403c101042514902d80340d49030208405004146005482285082c5900000c440c0d0954031110028040791800d543c00d5411510212400340c4940400c1c44800200c07405001c0002001002038008603107017441141032902540b022004428521000820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462786034 1250 462784784 462784799
    0x306050c0c190b01050108063606060c0601031707120c060f06050f011202071407030201110d021905010e070b1306020a020a060f021c050a031815050c0d050c04 70
    0x810141403942c01201c01c403015440d400c3c2c192405016a81c10b01644802090300e503510030200c0e040c400195014601004550500030100040c0711542d0034125800ca40428014a032400a441600b1584d00061036140c2c656190400680701203040c021000004000300004241c0342440002440240e031106140c0381501c3c82c3c4202119044120a2040c0b49090b03814465a944c40c0c20388c40b0848001d01e00b01007407064002c0f08030003c0c4100c0b80020011402c0d0847e0210030480455004120383c000d0b01c481c403011074118811521134400000c0c10005810030300d558000651307a1689203041902031000000c40071404911245045015042505a400c0108201d1540d94041c50f2010141c000362018041c10010b40d0b0200d03a01c4503650150405000b09010800034445c1308200c48800c80c0d4500ca0000040840c000000c1c10b990b02c2006d561002a0170721605101c5030b00c0c3c00e4416010b01c0d90100e001c041003050180094020080a02084c0109004101609000509001e4180110001c0000c1595613142c40710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462787284 1250 462786034 462786043
    0x40f170f0a08061309110603090f101a0303250f0f0c0e0901090302103803010c1b03120e0304260c090a0f092a1e120204060306050c0c 59
    0x4940c8085080400817000150101080c40c00d540040d520749443e6110840494145464400100440d10685046030500101e5401003c0703109032512200001000d15010701d5100c1c440c014500c0c034a00c82500356039030114420000015280e0041414010002203030b551458070750120300048d55500c0d5001e000340881000800050b40008034100204204691960060340705e400b0a5480700c401540c0c0d03205d10140700c948006044802e204002141c226030324030715420f000c040c41c58020700d000c0d41c40c0c1801220f845020b00030000740f00400546803401000103036401c030703680c00c0300680501074940c035034220355124103042004c4c2021340340c19042d040314106e02c580f00f903100121020081d036959203e402d00000a44440694076046480035101003440c0701d002c1a4140900340b503403402031020300003042014200940000c02c040d401e400d0b0080f03581103991201c01401581507a00246030349881e00a0030001c503200400c18011981c40071f08003041441d038944861007101c500326003030b04036a0000500307040354160500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462788534 1250 462787284 462787309
    0x1809061008010b0f01030f09050a0302060106020d08150f03101506110d27080d0c02010e03010b0f062511091303050702060a12110406031103040f170f0a0806 69
    0x20003c00056000c400000c0c1001d00c0e403020513040c50b035101c3c0710880603a030380e401c0541c10a80184c1106c403581070514009603180024801d60005000d009102140240301d29900e03030062908142c5e408055036488108513880810810303150381482900714440c542d403d2800384110700004500070200081c44c00304c01403c0301c0c0354413603509100d030005414030b0303040f0386c00568691003015003094886541c1d1079440b50300c844001d903406c02d000320b100705107036420398a9011048400346032003070781d440361140030000905007690700f160a500c0d800904003542d2449401c2440c05070a80c081c508403203041e07074104c0045914004885842c140c412000c10308040c0c942d810100001354100b9102c50040d00c0604039030b10020300e54081d00e02c00034810798002646040061003110825030b0325403000c50410041403031801300c250640c000e105200c0807130f042c801c0040340340c0c15041c250707441642c01500740c10b8103812981e6148035403c40c0c00003505644d1024040e1403d01d0001070007038900c12115440794183c030f08001081203201800314 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462789784 1250 462788534 462788549
    0x6080c15030c040b0702130f02040918030206070f0c06230c0309060115140a09080c060c1e070f0f091505030307060b06160c050f0d05030304030c0218090610 69
    0x100103018580b0100d07800c482c100c0c0e0aa10100c0d803140c28038400540240800741c140040d840c2003a100810f03011055000340203ca02c00401003180d094050910070f0410381500f40680540c1003240000d840501138070340e10b004402c1c03c0c54004440c40050352418100c0d2000401c011000c001422034102c42010580d01c65001014441028118580861525070b2814140184140c1d04c54616012100c2801404c845002801c0c45060f030341c03501e00034600100078924074800c5081904c105c8085c2c0c4154204841180d000164510150240d090031100500c1c041100d02d040190070300c0b50a90014400054115003405001d8607801e0f4920b0500d440600000d6404110510310010000702c810031899070000b040720240359022101084190a04000941c2c41c09113040f55005080900a80010000b003011100c095440441c4c40d00c2d0386082d0413047c003048401181000b812640100046000b09004840c0c00c003044d403005120040b528001d0b000e800b034601090301d240c60940c1c0000c050003200441d0480e04d90190022 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462791034 1250 462789784 462789787
    0xd0608010b01110706111606210501060504090b0619020303100812070210170109090b0c090a120501021e040e130201090b0a1b030e180f040305030c0d06080c15 70
    0x7000c6004e44400355441a40c09100f003410404034440f9050200d41d14101c0040703200ca488a03603c103c0a00784c0c1e090054000d400b46900b0791502c03c0e11602e8841c490581d8a81c0e6585410103080544400003007103c105a203030300c5001800a104d1211041030844a509026806907880e420540d42034aa00c15440e01f200d0341e10307000740702c1e01c4502c2488802a82c02c001e40490303210410b0201d88109031445680c41c03c0c0d10300442074500010400d083e031030b00b00c00d880c42d125040c0717a070341581c0d058055903441c024500016031102421804029054109138004041750203140018980a60240c100c03a174001d6004c0c048d07810580100303081185201544000d039210b0a01280314021091030f5000030000303a454010a190600040744136110310340b28070a920404c0840d140c140c3c0c0c51007031600703000e081403503030400c000e00ca440b400400381411241000106d0190720204c030100e13400e4550b95400d880c1600000c1030341c0398040050003200710007000d0380565002840310304007911031007801009000b2168000c941040c1400c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462792284 1250 462791034 462791057
    0x1e0d080a02032202062110081207020f011422290a090b1c0507140406080c0f03040b0103030915020a060e030c030d0c0e0a051c170d0608010b01 63
    0x4502c84001c00a0303805090000520446100050301800b451001e0346d600e00e001c44010009440070229540a04907030300c00300c080d4581e03850140d547c030000c8884d1200c0b0543d060000038018200701034855044101414204011060032600352802c0c1c00520350b02945d034190035080c039504d00300014500081c14011000d1450441844109828445e81817065000c2c084001440040c007403055807020b000e032440d58851035507602d00210b040742c13260040e9400002203140c24041810680545046d141a40c3c00c10140d60500d4a07011040c0d80c071500080c510401600c040001c1c1010860010056101d5886508220115415030a00a10010300394110f490f01c0200d0400b4407134460740010f0307401481c0d6400000802c01048080c9c800c2d055003e101601032403840f0114114000c800f40350030020954045542c2e0740301c4942d03130350200b00a9481c5031140c15004551151000d85ea61041c07506880c0e464066034540c1c03084515001e50303101c0c46e0710a2101c500c081d40d071400c3c03d00c1100300070302400e0356000092805510000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462793534 1250 462792284 462792301
    0xf030a170702060711010b12031201060c03020a0b090313170601060e0d0206030402310b090415020a031d160b0301150c03030f020403140f1c050c1e0d080a0203 70
    0x9800b038005000c5c41229160329000d50001d400030019070201800c2c4041c811440166107540390811007040159100400001c203030350784590040d40701c5036015801813180312410345801c60a400003a011845900041000b001000b029038520002041030b1540c2902440c24944040d04185040c2c10400800c0455070080c800c0395600101c1c1618a601201c0c40c0e40e4a80741c0d4030000c0c224414030b0040c1484280382aa0780306000800d03548454028070034100611441001c0000c000100508860050215082070411000c201031680a01011815408c0c0021496042980034140309001c00c1c45008991101c401d858013800007141700401442c0000e551420b5505158081c661071084071028000c0104605850702803603c00e03045001d900c848000b0465585499042103424944802000b2200d4414081c034045d00d220002212224880500b03101d403080c190181c821600b561098500428605c01c8000f980c0c1105840780c6030682d80074141c07005141000340c00c030020b05510001040d40100c60f106104226003103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462794784 1250 462793534 462793543
    0x906010501051c0e070e180d1d0d14071e050d020904080f0c0d0915090e060f0a0b0309010c1814040603080c1506030c010c0813080f030a170702 63
    0x990001540140001c000f8190000380300c4e81100d00d003d84504513000500b10103880c0928007601c511f40e040e84502d100300c1070140c3d464010342030803030000781d42c8402d13150784003c01401c80020603002882082601c54036144c030340d11008513084003c95904010700c00c1040c1f094800c801e040391602c0c2e806080140c4e2400300006c201b900040c3c00a1b00030307203041000030104404641100c05a107230003400c3c0c0b6280c14140ca0803980c0c0d410380784064404104160008104200344034801070724001c0030754840740c0b400d090802144020501404140d0000d40b500a510384955071001444040d000d080342c0c0030b89a18050400c0c500307545c0540d25a4040c04215100c2c11744500044c8101002d946807825408406446200420000c201681c030190000380701080480c58008003064000b95620040405441d58541008046d11200d2011403907010401c41c401c0c0c81c00007260704005c2c000c466804204d0032440ca60751407030f41d410302d01d600c03074003001e55080020203041c0e141c2c0200c0c881c800300420090100480c81d00000c00b9564 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462796034 1250 462794784 462794797
    0x3020a061a09040507050a0b0906090d0c0504021209010612150b150a05120f10050f0d050d02070612150e04060b0303041203030b060901050f0c0a050a0308060108090601050105 77
    0x550301c40c24061003000100d00501e50401d03018040031803510b441c0c2401034403040c4502a0503c204121640014410380440c183e41000800411043c07400500c24200030608a28000454505416680c0003485030354030310241918001689494406260020079031703007182e059410030701034440c40081040c00304000c16071541450030b140034005000508400061903012280f1000b155403040090707810a40c0c2c0c1c0c40b6010700000c40412041c0c200c03540700c4141a04071028116044e003904a00f00030f00300300d03515107000e200c90300040207000040c5c0c01c14a40c030b6990502d611210003101581c8150010400e15600804030311541041010400541038201c4c02240004114850040f02e01c0310140820203100305a8032030000d01e04000c0883c0d9450355924218001a001c2c0e0b441030300484e00d882c28a40850601c41c0c210b45221005079540c40c82c2480c0c1c00315203426030300a44500c4d5054480c1c44c2c00341000560030170900d5a01d0f030003911140014941900014076000c030040881119410840040020b40d0b040016a0b80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462797284 1250 462796034 462796043
    0x1e021b0d141615060819080a030b0a030c0e01050306180a060902031905010b010212040b03010b0a1713060f2306060d06090606030b010f0e0616020909160501020a03020a 74
    0x7a140a50192444019001c0b000900504107140c48080c42d40d43d10741c040c0c8100c620840603104084000c444208140980c3d20000e00452001c00404d40000d229600243d100d1200800b0141d25a13240c0d10f03041540c861a4000e8144600294014002c51800f04921a03004003080011000343e040280d800340c803040200c0b4020722868481c0303055021507030148000951840c6c1c170718400e055071145003462800381c886016164058002e00e1740d0144108107060445043d201c505072058916480d00d182c40b0600d07400019a83e007000b020403a00b031b036540c1c03400c404640108144003404060010a0a03c81c084680703c018400f070307403071900034840314800c001152100c0c6c503105403284000540c0c0e18008100103114001110f943c0700d1602402003114030441c1c0c819420f85001d0742c0e00304414511a001943c084841500c60b40128103151542c15403840c100c8000c0c04401240000c2100c01c3d42c2c5980800c484903010340719140039821001a0308003038807100c045030380208024401403941083c01e4a0294540d900c0c0d040160 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462798534 1250 462797284 462797287
    0xf140c190509130b0111070f0b0a02010612050a0507060e0906120c120609070503070f12031e031d19080705030909012c0115030b041e021b0d14 63
    0x3000a801002611207a4601810032207504214540010040c04800b4219011607065070303048035001c1d80043c098040d070b050309103001007260410b100b545682d000752402d042199220381010034440e0310a070603410b01c280300d0001000c004130b103031802c2401c11040da00000c040080d00c000c002503a5441300e400980110301030b15580910706401c6003a6080914a054140d0031204070310011046d04400517685104800f1401520944c64031f4100b09500c0300035510500a087d44c494009104c0b400ca0b0824158030180f081c10000704c40c507a5503101b5106089081604400321b55500070043d6a550040d05004a145001c40902100449203407030820100e92250090080314000ca400c0040040400c2207880d400c1004000700950761f541c082080080c6a65a01c1000020707079004240481f230040790841e416a610805074459140c111842200140221259154000d45401d1800000c4003800c82d12030708006410307130140c1e031850030441c4071400e10300c0010340502a0b4000d0a00710202c903403000020300365010072401c15 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462799784 1250 462798534 462798577
    0x51b03040606090e07050a1202090417040e250903030504090b060d1b0f020109050a0201120906151707081e0304180209090603010b240f030a0f140c 65
    0x1000900700d0f6003000510924000907400c0340c1e0f01c000340740000c66a080322071440241e03e81c4091015400c00d208025080407459000c100098044250424150300364082c040c127080d40d070080030110703090680d1410b0b0420007408030040c00c031045e1982d1b105480307aa400c0500106241d1b41e40240203110701c1c41540e1100b030741c0e0010300d1919512801220645000307264244120f04200c0550b00c0314525000c3c16802040c02c05902240c00d03070041c0100d01c009034010f0044c2c60344079250f800561301d550a02200035446550349030707500001030161140380084442c0d6900c0c40001d5041c042d640b0f05415440c0b42c1c44c0c41607840302c0c4040000e558000303030101c2110b03042c0039441d8800300f02590f11383c5140615000507000380351050001540402a174050480c0100441e918201c0381c940000341401c99150103140c0d0f420140319402ca910340300c00a03e002c1840301d09041c90038034040e50540442d070b0b60340060b6009003104c0d4580c5c0d080d80c0305600301d0240b04880008419040c5c003d092490305030311709204403a40072000c140c505001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462801034 1250 462799784 462799793
    0xf0c17030c0904020408010501091d15220b070905042901030912210612060b01020c0a0e09120c030a0c11090a05091e120d0b0d03080907050301051b0304 67
    0xb500d8450001a005545030358451001c140a00310900518251502d00f6808811804c50700c04110720100c0c8510180004150010381c51660150040c0300c2104442c503801c44040c002c034901a410380460007000c2c0b942150421100c0100b078415142c0c4030f244a542042010510030343c0100c081c1041802c06044101e042c02c038100180c0203494140300c041e000c04048004040d000360080580a140c41c8011400d644032204d01c00f5003412503009018216054080303100da040050120352109602690500484003018443c000044824811344c00400d02c41841e10f060010f030740c0f0204400d61021400c201a641004980d410f655a28041d291064042001c102c1641045c01010603e1440000740940a00c1440c605086058040c080c140e80030740f07662044000058280c500c0c10644207144008402801c180100c5000481194120032051000c131030380d4940450300d9a60b8403211005003803080c0c885043c80d02d41250b40e11705007200f41e40468041e0341080c0401c1450703200149140d9242c03403054040d03a125102d900b030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462802284 1250 462801034 462801037
    0x9051003081207090501020d090b031305010507050c010f0b010f05071502040b07050c010c03121a0d0623190c02010f060303120b01050403080415111c0f0c17030c 71
    0x14106030700004120300c5444181c2003851040c150380e1656a41261360b4401203170707500303080303004c0000240c605a01448641010310003990448111102d010f58141c0e0764a07641c0c00c40d0303001c2e511031000c6080001c3d503000b182c8d428001d400c1c95019040003041205641d40c000b0304003903c0c0c1400941000030004980d010410f02d140d0031104020742d5282152550b4a03184182e126a000e0a801d864074402d20815440700d41c81051050343e85585a55102080042d200c07200000d00810a0800014401c1800790a1a51242000e40307504031300030300c4081401d1900d08001a091100521303035003200503001d800c00403c280741c403c01d0350007812940c9000071003840040c2c04a004080512540500b6414218000300381a031005251403090701e0008100602c020003001500c6a20403480010011034003131000b002200d910485460342d446490401511a0003140d0059040c82c014003c83c445404500c2c4603e10126032106541a203025a41094444e1440c0b41d01ca225401c4031492040405041c00400588200c07100710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462803534 1250 462802284 462802289
    0x9053003010602060402011b050c060a0903080712090803120403050304110919050c0a080103260f2107020a0f02010318060207050c061e0706140405010b01080a0b030304090510 77
    0x49540d4495858032002504c5013400c1c0c40a0f40020419a201007180c85540280504154410000c0c08118608000e00210360050040e010074440c20400c0000412038000c000c200d11486481c3c0f074581070550310805003804486802082541e4011300c0b10f07907032030070000700c0042d00a034045c28565103d40c0ea515150025000810300960004189410300529600504a00c2511030a80405010a544501301e1403d00d024000c41c040004100f000100b02041c00c0e6144d40101c0c0b1141c0616002480c504518920140d120300c01c0d4440340c07000000c08881c210250030b0b04075144241440598954201880002d50304d4040d003101403d10003080801d0710031a8025030000101a101e003040d4011a003442c10160700a400607201a00c00c4d024a0350b9160f49441c0050440d402c01c00c0c4080300c0184070a25030050700c4980c00ca0601116070070b50300c1441c0d821504006440382d12841c8218004210b041c140760004106160182c86803a002d070900240e0a9107035004010345040d6040040c0c001281d40c0c441d003111325600c815a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462804784 1250 462803534 462803623
    0x50301181a130f1103010e06070c17210a1a0612090708010e0a03110a0b04080714010f091a0f060f01030b0414060a0e060a23100809100905 61
    0xc69842c4104804c10314250504642200200400101030b281d031500c950017203e0440000b00781048000c005511504808038805078040d1460600c045e88503148030003606141c019064162400c01c1000f1400140a150350041400e08030200180c2180c000c00c0d6140070f4a03c44004100c141800100c8503001040800000c1420078024400780a07034804598983d0702c0c01005500089488404140c1d15100180c1aa00302c0d071b2000203c583c580d100d441c1c2c0d180c0c540164004480144690b0645e0151142c03d0048000d490180c9900107012003052070085c981d4007d00100c00000c0d40e0800070071501840752080c43c6e030700c1141a2406580280c440e40124010540024025402031601e8046040111100034141c8160019590101866102c40b0760941a0900310340e420ba100c9102d2509001da04521446003604120039490b10008840040c00210030100e50509a000103000a04000000b84100003c01541140820401c81c20101c0e4542e07a44583c141d511030b5400d2a03c01c0c400c0d8110900602d0006000b0449 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462806034 1250 462804784 462804803
    0x109050d050d0b130c120506300601060206010617090a030302090f0316050909030304151d0d0c0309050a03050705060f07020a0810050a1a19080d02030301050301181a13 74
    0x90404c00302c01000b1041d2100300180d030309000d0620300300092081c58001e039801480c00c1e500346000e0b00c1a50043e841001c518289000171100c8144680701088035501802c1950041e081940c10301e0703c001e0012140c005a501546031781004d120072001c0c04500b04075011740600c9c0251343c4d4950000841c09403d42e2106d100e8251048810007180e060702802078005481c1c04854411050701e813405c000c0c0e600d00080d03070040c140f071840100800041e5465440101c003080c2490003076001000b02c0390041d05013a4980c8509000c02c11203107042d401c150741300981d2005480125083c681e042d045071101c0ea80c5003080e0003058020000001d42079807030201402500c3d0b0403980204000701441d00d4140181e11841034400000c181070902010400c0d0348220f0091680c10884960040411940385082000000c45402602c1c52030060700400701e0741400500c0764070380c5400c0d075800455403545840d09041c00c4035199943d5122035416800204002000402214001c0c0c2404640750607a4440c504002c0346447d10b1440103010118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462807284 1250 462806034 462806059
    0x20102010e030c1605060a02100216020402070809010f0f02030a140915040e010503010606080415270c08060c0a270e24031c020f060a0b0907020109050d050d0b 70
    0x140000c05440404e0310640700701ca003960b00ca081c40114005c428844000d41c021800490304117059030b010702a00f00d50b001d911000c88032140c000c2012603203c0d07c0240d4002200140510071540c005640b0f040f44c3e4414600283c50581c6903000130744900030079144400304038095141c641d41e40020130996800c44802002102225065201c0416940c420300c81c0558002c501c50000a407807406114003021505282c9403404650340d03c0c1e680700172010030f142c0d00016481c0c1c2c407000e0800320304d04021911091002604201001c1a450911410103500c5a011034003543c00f80d0b04010350007180606841242c0641d0400f400610340407102d0007007210b1003500d402d24940d01040005903485200280d1030103000c0c800b968055a041007034200280003c01c01e011509503000c00c002c200c0c4091390b03aa0801c2186814419102d846110031422420300706d00b44c43c211445521901b0031005442d09000072a0480707900d0000708400140c503680c2c60348410448030b0600c148040403414030005405034008050811005014560004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462808534 1250 462807284 462807307
    0xc09060a09090c0804020307060f09050621040c1403030f090f0a030b0c07121e050903010f02040b0403020a1d06010f170907180b010207030b07050c0a050709270b04020102010e03 78
    0x6048401764072a110f1502c000031010300902160ad05011141c3e40e00e5041c41c101400c2c05466840300700883c21503c100200070080040880714180218402c1800d2074840f8900710282c0e03902c01e0031581c070511a4004010b070148074180031003210400c2c80f055505040e00100c260014a4460741c550010f00140c215104110705c404150004065840c0701e00c1c48107055400300d907800c454800b070001c3c04151385510740f00000640d500400261036081c000074008100100c40c508004244e820550201e11240300100c0c060045162940641001d0000c050141103c881200f00d1140d400c800904a00d0520030194195110140300b100001a0b0f40360382550f00040c0d01341444030380e645a10b02e11400f23854104001800c40c90540034040c4d00c004800507402440d40c3c07411500c0d201808500a0310074428400104111b00c6c02c0740b028018201003e004c0c5000c2c00b585403401035103400381c2e401510426012a1031500c000c55013001412044103a6800c2203c40710310f5076403480141c2c018151046001002d101c080703078421821 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462809784 1250 462808534 462808547
    0x409050309180f15030c19170c090106021609050a022b0606110a0b10080a0b0108060630010e01054305070305071209030b0f0c09060a09090c 62
    0x1502d02001d24402c99031141200700700003404c80006036258120152903030342c0389400d090200883c02800e182d0543c90380c0e1510031800c50020000d80c030519400048070350301c091600c041d5040c01000b403400034098181005d24410400b110758000c1c50b82d803075a100081080074102d681580c6042044102c1c17030744211408044c1c0e40201c080303c104440218104000401d08601c604682040d03c05040d0013400320801941d0f4145205000414000c07114014403400550740404000a4070240c1c003e5004100d01d504040324907003050b034004c0c0b0841c0240c920a0025410003468000104c0440711202ea50014080f0b0b04003840c09400c030342511000a60800e42031042200d111001c0b42020700f0344500f00d200800142c0c2440f040c40c210100004100300483c0034141a80d0700501c01401000d00c6460600d28010b500c0d035505a03030641c40000c143c0007880d000014010400f036400c4981e0006445050b402d51468030f002408034901c110750515001342008201585080d00500ca584094046034000b480b092140040c01040c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462811034 1250 462809784 462809791
    0x11505040503011406041505030303270601090203180d1b03050904050a0209040c030e030a0807050d0908030a0e0f10020904090218070e060a020c0f0109090f050a0b0102011109040905030918 83
    0x31b10300d042c1d00900c00d0540701043c8000c969000d0051420365075400800d6404c0c9c020512120075000703041201104c02801400704501801901d000143c581c200414403075920408040045826407240654a590f82e800090b2100a01a034101c40090418285821a060f01902071081c0d04603042006101e010750305c0781c014040711402541c08004a080d0f2100c101c0075290490303210803c642080101000d03461113000c1c01c40e0f020200342040c0740b5200300d22110360100c4c2d5180e00e01b079620607004014414541d03024042c4c0807140307840705e000f82540c45070083d43c20384450400d403c020819900081c4c8407070302d0f115500491100c27500102088050b6000c420070f55107124080300c000e4009000d1500c02c86480c50060103460489001e40d004081c15507003141030050a04c20b88001c3d0b41030051141d00007400c4820f0380901f0102d1060580c0105140c03c0c144160002e48401402c624150790600520021000d04c0d03074140d8198060403140480c0c0f011003418a14150b1142c0006150002020000300c00201000c000c641d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462812284 1250 462811034 462811039
    0x602120d0b0402072f0a17070803120f0106050a02100506030705030d0905240304030309110607050a050c0402180405130816151515180f08150f011505040503011406 72
    0x10144185541488040d4500000541c0030459240c1405108520f49020111f40017410031118016180c044083c91030b0014040c9020011540c1d04001100c05600032160040c51141869800e00802171406516519504001c0081b0b5a0780c41c0096400e40d01008050018440613094440d03008500000802a10302c5020f4a8060360003c1c1c480d00701c00c00c04800d04d0003501300c40d8031124203684490380c0480107044031990540d01056406042d030b00c0356444000401c0c4003480b643c000c00f001300061030401c0c10601d05240c20340c1b09030700c140003484800320f020003080b903404011a0001066500c41c26991280c011060014184600129411080103038420070318050307138014a000402c074505083c0705801d969079900340c5043d10740460340402ca0a40c0b41d0040c101d03041030904003106007001c21f9001451001c4242c2c841a034890f4820710070445080184084290814184407078065482e0064414070b2085040c071480b20024821034152280c42c0c451404c4d6409480020300034401116a29454091080141c45151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462813534 1250 462812284 462812333
    0x80706021203010b070f050c04020325020a260c06011d09010e1906091203060501120902030604020d02030a08040b0a0905030d210e010f0906060f0602120d0b040207 72
    0x120400c0c0c410082e0703812100001149807a00d030050342c520054007034030001158184100318690f0801e54a0f400694401c0c5804a8040441c6900040514031400340003100360640d009038882201042100303214040a402b103000c81d6040c80042c414481c4a40304981042043e4014040040f48184100082000300340b010f01d034160b0562240004507080301e1032262441c0d031030f91251007540410000000c0144c0755500503000022403001e107444c0c510041c4806a030312000256112024060b42d03802210400c080c01e00000b003002000c0c141c1e03020036550070000e44040e1044d41e01004402c21583d04110f8003404983c80303042c03d0740321595074092441d20b0304079102000104400c0701002c44c8500f80003c41040b041c001d0b03664400504801c3c42c038102008000c408603001030341c4800705842034072406d00611850801c01711700001d541210341044001c0321040c1c3c1142203680340e540c40411065600241038036455406208866550314010f0005004055020b1290741103130012038240140b0101600d0488409118104c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462814784 1250 462813534 462813553
    0xd02040e07030204050c0a02070303030b0a050d0b0105010909090f0b06040b03032803050f0604051506040b1312031e0c0b04110a0b030c0d0f241502010506010f0516020a08070602 78
    0xb212140503c081c7c0704016842080c080020a100750014144a48090000d90b803203500e90000c908000c1d900401600e08009a600403c05544e1044004008080380d810070451904a40e454080010995001402c8081400d000c41e010f980c07036510580903400300030100c0b0b82d500103902c68940026200329410380c01c41c01044410100600034000c1c1441080091907989031552010304100007800040d01c42400000b40d02895101034070383c40001d0015140c2041a9a203802d0110800022803049400100030100031001000020390800386c4102250390f00343c170140c1c151240c00411200480704450142c05100c0f00010700c000d10036032808091041d9801e4078040800c9445000c010f040384016940b043c80c01c4020800c501d1030b0300316544101070b9030b0b541940201e40c400c01111060071002646480941b60481c070041003000c52141d010b13801040201740000c0c400391802d880060298002181c840040c0000020307100306031070841c64403c90144d80141a01c100c01c0d100c41c18581d0b03503000b40c0101c0d009481900c011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462816034 1250 462814784 462814801
    0x70b0c031605160608160c150c0203220621110a0806011806020d0c030504030c0609170a02030a0b060609040603121d03101508060c2808150d02040e0703020405 70
    0x18415504203030184110381b04448225180b4503030340c00c2654141a007084440b0211031500405c0f103c880300351f0040d520ba0715410411000d09450080c40340001c15508410418035410103959007038000108107038807015004040140107001010a4046042c1000554001d02508141014050700086e62044031190740c2d054040e5010b005402040b0240e4090380c10559101e1240310201c01c054401d01c0c01e43e090641c0c9a0f0f5140c062581900303e1004144014414000a4984000e030400702003030000a0143c0e0016401180d1503145082e4003a10049010b000682a515540c044402150020300100046a80c900b010360641c03075040091400038049101101c004401c01038410b006503002005005500d120111800c000c000c501c1e034410503007000420014070b500f010700c415480b4400f80f0345001d83e960122032000600b0791a024412001d0458078041e1014991701000c1c180d030102a02c2c1c4c04240c05417916002508580035000c000350b000f0f041a450440c66100451003800704d92007aa814020390704d03000351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462817284 1250 462816034 462816047
    0x614040203060c0d0207050601120b0705040f0e06040603120e0a080c0303030f04020d020a061106072a02010e0607032607020d1d090a050f06030d02070b0c0316051606 73
    0x50281d85603200c1d40106003407400701d0009110555030030304014901b50003a601c85082070400d88c4410803494031807043c0300500030b1034160654001c03030514160b03241c1400c120b56030701e600707610f401911981c071042000140c05e070300c403a40311202464021001d29401e0010303001c024000709880004500454540700006614400000c50111101005024604654504030340c8040c013000148242c3e0311120080c0b91a0140e15074114080180600ba902c1900c80c00000300c41e1840c108020b407850b0f04101c021582085080c04902140140fa6511505409640321030300040324110061600541c0c04080040c02d40201504081400310302e003224180d20182e840c2a03a5010b5524108450700030250300500c140c000128420180001405070841d80e40e5280d20724070011510940c0112398510020795103c05124268009800180d031018044009101090810b48000e40728078191081c1d1418600106628540b000148141d40c1c8294481d100101050ac55051451703903050550701c50311086120001c04036030303103200c1c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462818534 1250 462817284 462817291
    0x120e27160216270608060a0c0e0a03020d05070b0408010b0112060503031c06081b0405090a1e1a250c0b0c0f0702190f0503060103020d031b060e03070614 67
    0x4100307240c450720b859a03d4401007414221100306004903d0a40261902e82c031481c005010224010106072400355042001c8400c0e00d542c02003030001d03c0780702108a55a814040c41030b6a4142c429020646091425500e440b00d5034000c07115800e004178001c9842e507070541c46000400d03401d0b60381d80c1100b0301001084044404038025a81c158104000540c1c12100498504582d80c00341800001c055555100c0241022079410b100010030f02c01d410f0304d02c060724140c006c164104c0310040c050310142c804c030f68440511b0100001c000d9081c3d5a804014004c0c400602042c02d010100308210740140d1500ca54001e001749520428502a41c9002a1442d01ca6109102c46907096a1244a2919545502e611070f81c90381c12141c1c0703440c0442800c110202c0161581d51841500d42aa103444070030041c02c01140e245500d1454120740d000c0d03440320004002603590f00034680300700350b0541442e0031481800440007001c00c00000000d0075113420200004640e403c000020038003a801074000b041403070705400c508685001c1c00c1c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462819784 1250 462818534 462818563
    0x30106240513090c021212100b030f0a0b0102031608070c0b0324040605030109030e0319050a06051e010b030405060f04050d0e0f0a0e010f0b07120e271602 68
    0xd034024441202a41d10044040e04217004a400c80001020070840320350105410641928800092100030000f48200d28064103412030490300b5468086062442d4082c010708820b03565444c1d40825032117074000c0c021996410003040f0ba0f07050380b0f0308a0625131510361254004958403150948009600100042528014009641c480c052000006101c2485042841c1c0f400c0d800b42d9a180c000034a6542442060b050318403a855100940c0300d00c504160038003103090141c00c0c00c2560109050002440030494a068651007900050207864a6005107030800c0c011041100420300070b03001241d28115000518819031091084490980e10940c0c07031180d4a03001d84c2c008000340c2c080005420b01d00c1c046c1c0c01d03141c5109009000c52040300c680ea400503504a0140d03020301000c0140344018044c03135104000d0030000d400020805c1e031030f00755243c0d180c008580f20700815004101031039019100c01e95886078000907140d180001c20f84100c076150548455640180c900c8036045140f00700f45078116001154242d0304003901c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 462821034 1250 462819784 462819817
    0x210f090a03050904270317060607080d0b1002060a1b1b050c0303160b060603060d02120715090816061d040902060d0c02120c030301060f030b0301062405 67
    0x490750181e4007908500d482c0340d44951942c10242c82e141c600346180c8848407010350303582c03074098081c100901800e59034944151005240300c10810760b51a45004c907aa960307030203584696542160b205000081c41c0e1500525440001007840501761640028050f000b00070251040104d00c05800000340340240c0200007401190303404011502400b03181a01c131003528054019101c03005151070010b800d40d80300c2c000d6100e4444214040005110758203082d10741c845401e40d10140341d4200280010300c06520700e0700c001c2c4681480410b0007542c1342c0c14403200005024400030185808141d25019008210a01440c1401d01c5496242c010040500c00d810b02280c040c0c2d250343e0744046800861302c05040001840035006501d0300200801a15183d00600140168035000503010811700c138028203150b00c038071000d215034409000040c0754200c00720803241121014141058544424041580071b0322402030565815441e08030005260320700000704154212041410015455400e0b0060710680181182a21203008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 462822284 1250 462821034 462821053
    0x118050f0f030321100807080705040c021623010c0f1101090b12070807090b04061206030f05011b031112040f0506010b04140402040b030a050714210f09 67
    0x70410149401004003400352403030014640e210542c100003041503410070480c2c13241040444001000c220000d0720790b49000d8001503180c07c0c03030319640b40440c1c0170340341c0310781d035200c421502c8680208011242e0001c6007141840413a070310b01002d01c110401d402c41c42c410045c000c60802d155803103001c4c1c507105142e00040300500350300c1544610500313852024415040c48001070003c150001080c014003103103c07140c04900c0072441c24210040c81004050720741030603c040100140300b9102018240d400f65200303403511950112450b462a4040c000740da2000e0101c91046610b20103020044d0040e055001e00344024040e41d214040c4103e0440e610001c041107803000910080c200d0f005003851041d001402a0f20340d111041302a03c90380d060150aa100c0742d07a080c000101000160390800030201e0624044400f181020314080030f0320780511000300520002981d440000b400c1c24002c402c6c1201c04d0800c4c2c4c10064070340c1e662122034010704404020070007134582620001a07180d8405081700b0302c01c0c512200079002c00c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 462823534 1250 462822284 462822289
    0xf07030b0310062309010b120408040510020d1701301b0e010b030412031e0e011a0a1202010c050c030109030e0f120705010e0a0302060304030c020118050f 68
    0x44000c400079818042ca205881a065080c00f80d5405804500ca01064004580c10a0b0a064030a600c00c07501900300540100002d18408064840da40c2000f030703440d0500d5a807841c0802b01c91080d5088140c0c082c0703011a0660541d5800100d01c0500d01c400c0e02e402645d080000b800c424202000d2084060070359000000303a200c0d5591054408a41c03400c1009984080707200d0703a414201031414060b07080c60705a4240d040066602084699004040c1c01e00001e286060035100e84009043e10811300c8103158884a0703910745603054080754249a20145001c1080d0445061600d020340004003030300074403440b4854210594580070003a10f040300c40e00d0f4081580c4092680c010b43e105102002d00750b68500400503d4620f0f900d00303006401c1a941308c5e0751050700b907030400f50070002c45100401d405405003c1c41700d822424200002581e0060394801d00700080000c00e4400080c1c00c44085070002500b00301c002c014001015000741524001d103100343c079410300031070000740304a200740e0700303841155404441499040ba960 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 462824784 1250 462823534 462823541
    0x11b050c12040b0306180403020d0e0316080709060f0b041e0902040e040b09030a0903110d170307020601120f020409080c01290a081c0908060a0618050f0703 69
    0x4260352099840300c1289900030440d5801c19404010301c00320020400c8091315041d8002803045072202d615011034103044c1c81c02943d0711103210303603003090005050301148940e80411401d64050302140d80c4000b5942c45100c010f8480f82284160368603d4104000442d00c07004590362034081e100d0000f50302d4103042c90400745c0410086900c0712100018030f07018004c1500a10b030300017000605490b08218070941040e00e003131108014000d01041c86900284281200941d1049100c03003242c0c0c1001507a001070b0f4400d40011680d0001d407400800000b151140c980242d20701e42e01440c40f80a00b5001c1c1d075850381c0d8610f22100c0500b0780078402400c40c90400c81040051515a00170340c0c0f0030f03001e443c0985c10b000c4d44160301e42c03c541580c100780c0e5551040404401c0c2c0240a140d6030040b80e00d0603103118540720720b4510041d070b03107540140b004448484001d4000401e1803040c0755040040501c002101d51314102001b03014001c000030702030120095105d40c03a06814440c140143ca00443c241006407427199110710044008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 462826034 1250 462824784 462824797
    0xd020a112e0f080a020a0c140102040803270111151b040602030c060a0623040e032b0203010e0c0a210c0810080604020d030c0605010b0c0f011b05 64
    0x10380d44480d100c903180c50940404610881c00c03626031011424050300060408480280704006560040042440c0c0e242e203d80da00302e51b00c0e80075046011000150f1001c82c00b80c0259004440d003448045900c800902c038004112014402003041000c2c0042524011900c85c4c4a0150099440c1e1040c0251140c10500040240c0d024880307210000c1c2460107500075031625809a480800140d2004c95a400704200c00e0280d25040644071208200881c946802c4511881880c3c0c0c0001254804608000d1540c4450300103210341544103050329518a04c41d80d8038a142e1000c038424060001403038400c4404901b2920031a81a00c8680400c00c005507a0b81e900301c6010f0380700e100a8020003504d074110440c45c0d01d90590326403254000e9040800d0000f02e41c01c1c010401a0000d06958030141c0400c8104102d14010411917003150701a110b844207500303141025500c011403084010001d5262000000b80b0100c8072001c2c2c158180c1e04801c0d204401110114603003a19503000747c903400458082e95a80406000b80000c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 462827284 1250 462826034 462826069
    0x61306150b0304120c0812160e0a0b0f120412120b0d0b06010e0a060f021b0a060e190f0501030506030a020a36020a03061a03061c02040504060e0d020a11 67
    0x200e514555a014226002543e003204901c84039000d20111041d1350603844088d003ca85015028a515a000a0b2a60f0030610901461381c800180c80b500c60a07030a400c41d020104101000c030240c0c1880c2c0b901c500d525051100690000320003540140d205c01080c0141c080100008059101d4504140c5503003a4518014201a05104c0f940d0110703078482e1900e181381e070f0040c0b4080d146d00c001d01d0040c450203828100c40804120f21102403081440c1d09a403007000c6803058036454130703141d000e0a841d207001c514282e9200c10203048800180d20001003203078134080395000b61075003a82c05110644466090641e90032103404000d40c4485841011300803400080d170044d801109085c18440542c1d05030400250280750400100030b0207400089401c83e0035054060440205401080b03c080f4030408038661000740006403186104224402e038001452291050141085800400070401c070b0a01e854901c008141500d080f41d00e03070142541007009640081010510b01d07402244c2c842104100404004001711031925080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 462828534 1250 462827284 462827297
    0x11704080d0f05150312070201051207020703020a0e041109040f0b0c160f0c080609030301090207030507080408062505090909010912050a0206010b0313060b010c05061306150b030412 80
    0x2c04180c1c0b805403a004410380561103d207401940d091604200c00b1548201d00000100001030040c0d82c054101e6a2036400000540d2858460348012410525a0761001c1d40c41408400c000c14400304a0520900031840350203034a901880040074400024000c40307010b041f0300740c6684114046658400e5581c1d104003019642e501d07003409606104410b07040c00e074003502c00c041308821100c1048112800c500241000390000e103418509580c115039288414028090003d40116880c070806018005031105280d1240714141c5546e12003006541d1f400d0101c03880f4801c442548c1c41d400c501644010b2a120b000d1190366054030742402c1c82d00307120807104040c04d0420159a0381c0460404221900350429a2080f2a07403001c1e9201d003400c01c000e182400607000441c0c1132008009110074100c1c0c403001a85801c2e070043e800728042c408800141c171303101e0030303c1400740072030007000300300681c0c4100c9aa090000500c5414200141c505042040e0541e44880c015035404260810108001c11010320071302488009138500103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 462829784 1250 462828534 462828551
    0x6010207031502120604090209180c09070f020d0f0518120a0c1509140907051c02030a060902190c05070807060f080a050f06131d0a050705011704080d 66
    0x20407041070220080025a43c0071808180002e80408000e80105048600784000c00080d0002280402c014000390032103482d200ca05a003414007407160103110715004100400c10319040707001400c0340400d000040010300030381070800d40d1107001750b000886411441d84c4080c01c0101c40e4a600c10411541d00380c0d10361000d548541301400030380030030079400c459214400791100306281243c59080e14020b480200140300e2071240c28090400c0340c58a6580249007141c02c00d1017038940d510140d43c41c1c03064541d58408a28102220100e40030340ea00118016206140e04000099440f450b440c00c07400b809164688941c1c60141c03030f030b049502c11520381e80d100c0c1c02071083c0c404069490040e40d01d8600c80364480c0c0e0200748191040c5150070f820412141e808080b20906002a241540c21980780e0742005044034425a0303071503a0141c001c480c42e030088181d0044207182902c031403031110f005941c1740341e038400032201c510030303501c020820b54410b0a2920281721144440c05c0284c54550b251401c07904110902d185103503a41135030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 462831034 1250 462829784 462829793
    0x80f1006120f1505090705040e220516051c03091502070b130623070f0c08010e030c0111160602070203010f090f0605151518100809250501080601020703 67
    0x10824844601c0c081e20f00410300d007100340100384000400c14400e1050034402009032560703990030b0313603031101c0049a0245000240910b40d129003c2803130018003184a219516096403183c0f0592805483c0308072035600142c60b070902d0a860788007003800c00400089540350100240c0300014600c00d4028001c0c015503400e0798403040c501016800c5280c030a40e460b410003104200341500a05140321900880080305002801760303040f40030354880c144006200410340082c0e1420300005000f01070107840014001e0050b50818141c8650b00d030400c9503025034a5290032036010004d800ba00880e04c0c80e45190880e0041c9441b9500c2d14002500540c03c03d070b8055480d18416164203005100d40c0301d480e8402c105042403180c4904014044602c02080d150441c1c41c0b580d40c2400560700c0c451a02884c1300c0404041e5903820442e0300d1031000a41c401c0ca815049814600714510164220b010148030740900740c21920915203821030301c204079a0306540f071100080300800c14446035100e40c03140d44d032001c0180111031a00786c0e41e665 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 462832284 1250 462831034 462831041
    0x509090f0609100b01030b010e0d0f0b01260601080607050708130605180111030313020a0315021207090b0307030228120b06040b0904050601020709090b07080f1006120f 74
    0xc820440b80c00c250f5603201c0c8055144540c07008503500386002c214188500001070106000300b065540f181c840904a0070400c40c4054580300b842e9400044e860895a5444850420281c000d1040c2d010748007640d04607402d1040020454100d40403e00108582d07103c0318020b03125948040025203611004104002441c11501020380c0141460b544e440d580740c030302c0303001404107094a8a505041050703030f1400c2c1d1042000081601d800408080c10100180214400075907220a250310081510186080782c40015000d5406450f2000c1d41c480c55210301e0b919100e04880801d01d1740500c512880040c00422031030b910030790140101c0d0f01c0c600540056543d40c43c0007a251040d80c00070703410003d50041140341c2c0c0e0305461300503920041c0003526440d041508040f00c15542e401060b05141c01160380303c001992586c42000800c00401c00210704001030b072040d00f007000740c4540403181301380802c1495012480c081000403845100d042000750f00e090280c1031100484030a0000140c003100e4603103503070007020b0008440c413 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 462833534 1250 462832284 462832291
    0xe3601060609030b0106020a0b06150732030a08013f050d2d050403080a080603071202030a02040905012d060605030103170d060b030f0f01080f070509090f06 69
    0x11229038002e441c5292080310070005030018400c40d085021184001080540202d4000c80103c6028072146800e880b8510140124007001e8100c500d0100181802c0800c00b554a01400c11981218a000980380d64281d680c424101c65600182d450b60040101302e0403080260451181d916402c0c181180e4550b4503d0b005a1b80c8520a40400c0620241010450104141288544c40d8140944800381903814480c030402c04a88045545504403a110f41d41da102c5c1d070031100a1a8403121023900c60030802d000a1201c074040380c24501a1080c2280420090000101000d6003a0700400800001c207081c1c2c2030201408081c00110354642d2034a240401c440e40265481e82c010310045002103040c003e41d00c0240036108542d2045003031100420040c004208406040803408003191001b030350315014203810200501c141d5210798000e510100a01c10313203d201d041c242d4050f40c2c0d10064001140d80358480c0c0e036211810203140f80c0c0c09502c502d6041055051000b82c07598003419041c192020420030038010350a090045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 462834784 1250 462833534 462833537
    0x510021b01051c24082509241a0304151409240907030f0512040b0403060b030d0905040e010209040906091709010903030302090310060306020903070e36010606 70
    0x121816400458080078140c081004d02c4a1440c500d481c06040c2c61321807480c410141441c8004913007401031940300b411190001d04000c0010096035848404542c1044862001003122031a080c000040b02da04000da6a40c2160f0450542032550300c1d45ea8803070140039607140b8084900c82c0c645003031180d109160009207118100d410090141c001c0000c8200114220103c80041640100c6090101075840026803005481e84280d07a400d0f081200e0901a14064030741c7d4007c10042c1001501250403110900504222440341d08123201d00e250160425884400d120200000111550b004005901e05900302d5440d02c280c0c01d00051400c40c000b400300c3c0c155008003009988d081c1d2501c0c4044c04105c1c140108503201c10314100b4a5040800c8800021300250541c80060100f40d0003143c0f0300034550b130910015000e010001030402100b6524a48940a034102c1028103110b07002d214000110000c8400030684915501c90150004041000b010018210303000c1d030810b140c2c05440c00603620088c0920681018000d01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 462836034 1250 462834784 462834791
    0x9060b0d06231005121005070c02010f08060904061d06180c01091401050304141e0c0d0f1506030206070c090b060703020a03030e031c020c01060510021b01051c 70
    0x300350101800581e42151404069594010004641c00c3c0b1450001034075001c440c000d0b542c1c0282c40d2440e283c007149004154000b442c1809001000340c2204800e02028404c2c0c86100910200c00002e4610107030446071070350001982d000090000306154001301c0000d0b4440e04051041d41305140c3c162030503c0449200c2c0d081c014404a511481d1810003040210000034603000741c80f282024005031040101410007814020084081401c1002d929040c58203580d507031040b29860404240c908203801c91400001c0700f540900520411a800c1410b48808448e400043e0203c2100d46a0344a1120b03c01c001e48819126541d840044016529407000f4415680500d401c03040d0541400c9800c81140d100f10300c1d040c0b250b5000c01010b00001c2d00403520348052a01802d0000754066910482d50861080d0388014030010400d948060100141e640a007a02204650003040000e440313205000300341d50100c4242e03016030701c041c4c0041541005c090703901e0311640040c0741043c00e2000d5505801141d1880c201e42c0d401082d05c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 462837284 1250 462836034 462836051
    0x2030a0807081e0405011d0a060e0c010c3c030e010207320301060f18060513020c0c0910080c03032b020717030103020f190510020c100c02090c0301081009060b0d06 72
    0x40d18041c3c2986100e8181c041c2040304bc03810000380c440c10f81940000d041d004212a038903041030300103020f01d41101c180b0072040340320010f81360400c0c00081c1074a011004144000320541440d4400610f04060b41c0100c02c90050b8800000a1780d010018103400d0262010300301c0340c0e0030303000362000c1c0a808020720560050000c82c60804001d960613458000c072900c01d40786401010400c50b81c0340d021041130b18134003040c0141e45100d1100700c0e90608100b41002e41d04140c41c0024400000035082e04002100c1c0c90303000f074070403900b040e4080544920500c080789551a00c040024910010301c1e820042d048407807840300500d000803c0d07a1780d1703498a100101035580c18201000400c20341c00d0206400030180d00462340030084210700b1034900c0da803255600620b40200051035140803040e00030000e504031090010840702000c564090300034002d62500d41d0480c000c00080021a10720118601564103031201e0364064001c1000a4510800404c9a06000c0e41d401c0d450303406000f1640c44001001c0c10f098059400800c81c9071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 462838534 1250 462837284 462837293
    0x106080d0c03020d140a0e0f03010903080907170606010e0a030f080706060501110d05030a02040509011e0b07030804020411040504020a0f0206010503031c0b040209060a02030a0807081e0405011d0a 86
    0x844a0f540000780101400001017003032000e022a0b0300c640039820501036440540700410380c4042c00300c502540640c40c104041d028140c0000304144940200c1088842300d0303843d03945c4440030070325030f0100045641c800c00100700c0641c01489505002c02001d07000417001c0f40d4076210849620040300e426180e1207400100030701408254042c0f400600400c0c2001020510b0240032190b6407071520740b82d00100000800450b41c400856011180140030050100d13116503101d04000c445811181080d2907a00440310000401a802e001034541081e01501e8105003562190248030207003440000140094004000210b15583c0b54030160042980303035070b102400042140006032500b0360680100c0c1c4030754001d200881c10302d040c2e9801a480d4007800311001c03540d21552400b060180c001c44801c04da0103100801e1182802c1d500102074151240c0e5a6920301182d200e80c0d1066400402c03d079905900c05640006414001c00c5100d64540c000340700d84000030b5541d0703109883e01440c1303401c92280790664105110036002c0c070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 462839784 1250 462838534 462838543
    0x20903070311040b10050a0818160513090201091415071101020705060309030403080f0705030c0607020111191d21060108151f031e02010809010c020d110106080d0c0302 74
    0x110303415541d06450005000b00a00781d4018038940c0b00400a8200004800c008036040d0780840b84040001c17512030310102b43c4201140c54503402100d00844881519644030140347c05036480c40354040e1181c0884500b040d10500041004001d005d81206c0d0080320444408503110041040a000f030b10041380441d08400024207160305503100d540702d40f409006011850001000321400c903a8480300c030300d95032840c00c500ba203064000d0140140c22030202052600610001203013980c49059203a0080010755400040d48420b03001c0d2400310701c021000010300d02e89486c080c5428503000301030041004c000301c0340600066040d200b0201c006403162240490002d900c40d00700491405080d880300540013400b4850908464030400900c44240100d881510083d43c0c07500d400c90307801a541002ca03400d2010304156803048114002c100403800120454001000d00d00180f01303155420006501806804030024822030f205408100760f032110f95a80c8500140c00141000109119038842d22144110340003403d029041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 462841034 1250 462839784 462839801
    0xc03091e0503060f090606041a09070503011d07050d05060402090406141002061e060d0b04060204170109150f020d090f02090c0a0c081c1404200105120a02090307031104 74
    0x13003000881404030b071000104803241d1060041d100060307810b5414101002d45a040c5042d0b07908914100f0a0000c0182d102c002075060b610780c602e82d51412044400080c4d40c0c440100c03441030020f0400c2c0403410780144203400154110200900140c144031540c0005070484030154440c0b00e003a0350805141c0c03c0780c28100c031400c1c91055240060403851601000400940e0307030617051504a00540ca000980954580400700c0103990005410b12540c68030340380c003a00070750041c014207458144510f100602d075103050007040c01c000e60200c2c50403210740c00c0445420140840f4406504082d400b070169016881c0c3c50b10407400407030700030301a0030b030703482c030203005019103c40081c00f8250390081c20000e078910103804c40c1e10000407613030110031030355101e46920000c160b11440854841c28a803e101c6c01d00c3ca00d54400074418040c40c050925416409944480170106d086900705180c0030a00038810701c110415034810083d071043c8258005894002c06000180c10310b80fa5070021501c0c121400e041100e035003803510030710b0700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 462842284 1250 462841034 462841051
    0x110619030e0a030819061e0e1312031a1008040c0504020301120305030601052701090f180509030c0a03020a060b09040c0e040201030f111c15060c03091e050306 70
    0x2615203098800a0003584020305c038559550601a001d080c260543d44a50001c000145103c0001042c1c5d0700608842e4407148640c50440700885e01040035045142c201524136039001d80c000c00044110308040c0c0180c80003800041c0000801280700c0b0340c41e01c421070b500e80011001d40c1e41030030ba071070030340750090b5008165009980114414001409018034050034000c0040d05070030480e481755543d0700100c40c184a21036214290740074698a2000001c56140c1920788810243c072007c000d26261020184252142c2c4511307205801d40d0302d051250380455a212075040880e03d0241c0b42b6101c010102c2a1034510380c15000c41c01640507a00030414070425100360081188202e4540c40c8a00741034503100754460807401007a44205075040030a045a01a40c445100440da544003030184401c0741d0440300c0d083e048845d05c403130030f0881c401a4000c4100140f10f940c01f418100c415940c4500c0c10483c046448502d416003c606000c90701c01c022804050301a140702d0980800100384030303500e050106140c103116001e07144a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 462843534 1250 462842284 462842293
    0xb030c0d02011b1b24020d05070501020409060f15030e0c040c180b03180114010501260c0a110105061507020a0e0108011508031806130906030f060e060702030a0c110619030e 76
    0x5a9030100747c08481c500380303180807511082c150134014024820360f03024040b1549070180000b45003503100038000460300440a00815450508819402d8039048a070000d4142c000503039014003858a0307030008402040c02d2421140701503110760644070745c1c1c2554211000000e07003c020401e14024a070aa00d160160302c40080c8000081d060800b11305c02e20601407181400100c081101405148c0a0309002680d50742d98180041e040c501201c01e0154401c0004e44d001800c0b4080c042d144440501030640034100180644404121819001e116904000800c076404603d90500140102c103400100e0f020348001c40c00012010000e5542c03d000750b04903840380c2d0315a00144480c09400414071002c00c401070050b217005a80d80b07015544030820070100e410443c00107207011804428490685090860a4071a9408120940e000140b00317941c0e00080741c3c2c0c40010307407040011212052168140502440c401c0380c0302c0c150b001040000a0040d0007000b84a5258410220b1080145a242c003810003562240405030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 462844784 1250 462843534 462843599
    0x5120c071b080d08280501050306240d050a121d0915011d03030703080402131407050c0a0605090604050607080702030a05090d0f150b030c0d02011b1b 66
    0xd8558014070460f400f8400c00364002440c500e03084e88502160f100780c50700002d4030301c0305032000b10042c103080c0500c901030b22414000134061410000380d4410700d0380652801304600d89080800c80c001898090480c1d8600070700030040d0020700c00e2710391040c1e205640d0701e414000002c0034151001d072055040a0610400460301807040c1c2c00301118540303401c3c0f0428600100524403070104e04856000c030007100d0347c06101c009852000e055011034498080e600c03c40b02002c00118100f05a80cd4a412a2000070b4802102c0041140f0a002d000102101454402a900c446100351a45402c868040710301e0743c07003600814100020404140940d607844001420703d0100c90908050003503803405014041c80a0020004200d40300b50341d10340314104403d601c0500c0c1e511080040c07421484006503c0401c4000e10b040c80c00d113a40e1841d011890380505c41c8083d20301c1052601d55001101e1a04509d40c0d10b84110b9145101400461407188180110f0f401021068410728079101c40c044010042000a030503002c80301200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 462846034 1250 462844784 462844799
    0xa0e190c050306010c111201020909090d050919090609050103050c0a030c1a0408190515011401081503060109240503071a0c0a0501060603230105040c05120c071b 71
    0xb581c0e00410286400f85074401c0c079260005001000d40501a4440c012903008060b42d00c1c150000c00d032015050700c1c1480c1c2074a904012079501d0510100480c0403d0052000606604040000c03da0b82002960100c222541d01e15041717040b24442c3c2c02204c81951a40700600610200b008079612002d03003a911103540c60b28540b00c07000f60828502881d0400d907070309030700c1000f03c18400c41590042e09026059031592284034100d0300508d02140d00880d0140144800940400c0c402ca42c100e04859680c0701e10940414440011200200002c09107400061f40b5800ca10b0107403070030407426010701f0055500240c0700103803043e0f0207540705505131216400c20220005020307584011910408035800d80028054480300081415140d00680103808828030030140210300b80b10054001004544070394404020b1061041060100060650b410941c580c0b1560010400d03820194011524100c0c1443c005091002400e05808104800d4481c0d902c1d1440c007142500900440c50885a014900d1080480000d45800034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 462847284 1250 462846034 462846037
    0x20f0f0f040e181c0309150b0f010801140103020307032301031709010c0605090a1208060a0b040e18120414040c0804020d080304030c02090109091205040f091503020a0e190c05 77
    0x10003118080c0f0900719030780d100d4029040700805552240302c003191350f11040007840003080e048248c2c0748101c0d1002e469005c41d501848020341603591190002c21144803c20042d00a5840a000304042640d01c10b000c00c4000030b2071884101450010f5000e40c055491030400d01ca914407900f07114944440b0400c000d00a03070380c012041038410381c0e00480100d0641d41303195445041170a290400f405161a828207901015440546184201c004450041e1207548803401083c05000d5030051420750b2f011040400e10310318030302d20000f24445c2c2040807a9444041500d080d091604140d0048404240d19002c040151410b80100100d28180386400411413800ea000280d041c412800003901000c000400300b001d16200b921030141054014145902d01e51f03440c840c80c4010140c2c003a058415111440c0c03042c00d218890803c840440309466400c80c0d80d5800c1c00c00e02d0000f42140301d41c02074075418019001005844054918004126940c411245032401d0b098000110790030100c1004030515058040543ca90002d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 462848534 1250 462847284 462847303
    0x70206090f0c13060302030106291e0903071503200a090e040f1e29010b0d0b03011508070b03070503150d05010f1b080f0a020f0f0f040e18 61
    0x243d1402d84552500020402444607810194140d4200007010a100c00c80501c42114030011468690b50b440d980031500e0640d005022944070303101c004030b61000803d407000d400744c61542d600a084c1e031030b204c1c0c0c0d0f49040787e80d12111034800d0011948620490510a202c5284420851001a1403034609642003400520400403806460403030300e10315020406100c0d5606480d1061070b840505400c1101c0c4900381c00629002c6620121440321074110384425298401e903400d44d40011b0b0040403031184c2d00781841c00c4401e4100c490030000e83c41c1d8aa102641c942e81c2401140703180503408402825880c02c101c2c0050030401d980d0411194001d0410a01088940c40400c581c1e1286851500ca0710910083e4001880c1441824019103e5030803c40410604503003503006012030309440c1e600030800e0213040000e458489040340d0301d0389040308a50004a0f508203a40042c000b003c411100949004500742542c0d40a80210303000031500f660100e0144100707440c0004d02ca40105598082d410144600c2c0062540d548118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 462849784 1250 462848534 462848539
    0x23030c0901111009030c02090a0218010e0f0405010b0706110a1b0312020d140108070b030412030b03160815191e0e0a060501090b01021011040b0a0206070206090f0c 72
    0x150302e400c40c005040c00458035405010a003448040d419040081801c649030b142a403240d490b260105540070071038400c07200b0445c8003038988099104040010b407010280403003d260040381380c03541c084181d6202d110305030180145c3c1002030b440d03d021f810040101d4000c02103c0905407420801420426001958030602c00240e00d0070800c61070061408031a030300c840d01c2e000c0c940740f030010504203641401034005804046810000041503a0780c0c0900039540e83c0c06210b86080f031041000444c010848951415800003084e09000c9030511804001c83e107041804003040d0b495046a00c41071041e40c0d0140318410529513000d00b06041420880c01d002c0301703411850010040d440d910030f04e10b505941088204031600540c80d4042042d004808191526030000c918203c40580c80c03d00003140545842c800d01614170410ba004041051106481034010300381c4070342d41581480c0034400041c0c10034280c80200101d0000c0c0d0b0140501d401c1c00e010192404002400b0700c411034001004032a07800200254807404407508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 462851034 1250 462849784 462849797
    0x602061302191413020f07060203090715080f0123010f090803030702010902042007080d0b0306040303020901030e070e070f0c020d0b06011b020906100e1023030c0901 73
    0x40c400901c04034045042c00c050701d400144001100140c0442c0b003c4201c000b0f40351824444031040c00c2c80220312030460040e0007928140120004940e0581c051a03000e15000111440d590b01d882c0030741c2c13803c0c10800c0900001050384041010a41c4115082401400c0000071074103a002d80080c00300400401e140d0690401c4008414000424400c646000040c1a0002a00d42d2402c1c000c4001f80030300704000003a80158101501c00010364001c104c034145160000e0021410700401c0d50b5001d1440e44041c6103441d01c1a00d5a203d01200c1d42d05021a83c0078900c25200180c0d600d00660014080da800c46a1002c041d801c814000c00012030035012641c0e015200b4940018000ca1210060710b4501810101079040402e0000c0703402000a0182c00c07900441c026240c2241203001c042800c49000300c17081d070094000c2e000e80049201400c0501c50080180c0842c240a0720307030386074000425102d400410310301d4000b559048a170b1040c1d04108804028484d40002610300d103150040e10030305a48a030400d9035040128 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 462852284 1250 462851034 462851071
    0x102090a062f0607110c030709020f1e0423030c100216090903111f020d091b030b01051504050f010507050304030b0f06010323450601060206 62
    0x1105584440b80b440c031900300714034218030181c80c41d6290000c940300004114214a14148040e0010f42c298801c40300030000d000c01803c01c0c0404002c0d401c1100120303c150810302601081001c8001d15208a4482c071800688491410707040e0f941030017401d10b80b0b89400d189020090441d407000304103c50707c1041960184000c18584070120701d8803000ca10722400c2e42c20344120102e500e02075600001001d41c0a9524901d20f0421001c106032580c51801c020441a20041d40750344112015130094240c0c4080c10000040b07140040d1202d1a403005041185064245185130500820a0490001d40546000d5a640083d40c240159540240c815402060b00c40c40b0025220382040c1c2c819011a406254408242c907110707035803480d10196900c030940e44980f0302400c4c3c80014001e54828481c1c10703507082c82030301e801074041c05840d8010a015009811969278090560b00380046060030808100c024541211101507440c0c100d491038200300c00b0030026052a0803c03c010880c1070340c0098411340148490445034001007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 462853534 1250 462852284 462852317
    0x7021f1704140106091a030601063203070e04050c031302060c010207020607050601060314041203150302060c07030302011a210c0d0c030b07020a12120b090c1b0102090a06 75
    0x1028090034040f58201280825105c0f89138104e0030f640c0500d10303124050001da0004050b2070750000d01030741c400901c0412400383e144941c60200710b0b040c180c1480a01c00c60a00614a02e41940125898000300f80030550641c0e40f41050711030982c0c02048200003d04606002030f5400c0019041800a44224070100f98032003422000e6045585155004010b5550b902d6a0324220361103060900c110b0340404d141c01c0000d20150340e40c0d0b800318400c641c050b03910b0f1416100002c06400416290803e40d0003c0c50503540400103071035000c000c03c2d400c55004001d0081926626009007950f005010000706072a0074a0b5840581c0c46105078180c0740c07002c612103240160410140907150425160031941c0c003175240440c0405200480b42c640d0b003501d0041060049503901c1040036a03840081c14402441d000e40d010056411500c10010050584400803020079048140d41c0002c24114054998100030480040e03000050406505031000040b8140000d50030410034800144094045100b0401440f640c03460548140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 462854784 1250 462853534 462853553
    0xd03060b0313031e2307050309121f021b12120601180902070b0906040f23060f0a0c090b03010b0f0c1c03110412110301060806010b07021f1704 63
    0x1411007911001040500c0c00b008260f03010501145c10100501c08440c00201c1c0060101c1c0c070074980200045140c4010807042c05484882d6684920140c0292070521a050259042c40000440c0510b80036868643c1c00302c01b041240340555001c0700980c8048003040d50302c070848003556241302110030079000f0b40d600c140040e030b00030700e009010900d440d0582c50701141d4141e4a6024007005c502504507140d2a9440d4050180d8a002c2079a0280c9400d59101090300000c10b1480804010185a44500d0b502411440f070b603881e0030000c0e5440c0c2d00325003d180c104030240c949441000480c080b80e207801101c161500320700c1489440180184202c200c40050135a4100c13441c03d003200c4031800310004507004090803501c901c50031200402c4800010b030030b001c10000c007500d540042c0c0d0103542c161054041c2400141d81e4408441d0783c0165a02c0d095500c4800c0040c17951003d00417035000b0a9186100d0380d0f121494810400300080d069825030300c42207040250040e49034090381841e00a82e59069000030b9450700c1c00e082c03400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 462856034 1250 462854784 462854807
    0xc0210090e040803092e060b0306061207021212091203160503070c0f0f03090f050a060c0213090308040309080601030b0f0901151503050a1b12060f06050703020d03060b031303 77
    0x3c658001c3c80c00d40400c92284206c81074080740c00c004100c6280c4440001180344010b845103a48200d05002c0050541402800a40c00c601e040c011076018180f207200e8550b25411402c914070000544108100001d0070a1141b0401802c0c07004003240b079460030428051200141d07298010821001000281145002e0100543d0300c82e000843c9004c1d46482d803800c010380a400c0e60045000442c0350a0004074a03d00801074415600000d10380341d92103090100c100c030403070040385003a07030f00190200403070018502510600e03a1b103d0095031500c0740351600d420003504040c001d5101841590185004202045507200641d4100c07a040078041c000380c458a0001c2d000d0007940716000071000d0b88002c002105c0248800c002c0100c6020b03101488281e58248480045403807030201d1008401c0e1719440003035440d1047d480e101d0b5600b0411000a07101d9104c070652000842c0ea900420042500080d9603014160100f00074102002c19250500c1664140005451640009080901c0751f04c0b94882803401c0500810100c0b41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 462857284 1250 462856034 462856063
    0x80f070302100c1407091b090803160606031703060a170325051c0e0301060302060a0f09170307031b0507030206090109030b0f010f0509090d080a06150c0210090e04080309 75
    0x203220b844441200040044000210045e00d030420107e41c50f5008440300d504490444010350308000e000403412001800718181228540e50351a00400000c0d190f581d0300c00030700305041e0030035140d1034035100f44402c0180a070032607010001413040040c00c0e8080002160921161403224045030380f243d00d150f000c660100c0d88010300e980074410b42070390071030107940c0e100c110580075903111f50b40f00d492642814201d800b1ba000194104800700000e1959074010700e6000d0301c00845181550000f9998007095030280d10258006070140c10018003003040c16400308508038a8400386552107140081da9540d660f82e2521884001c0c040e250103d84050240c2c0100585001160088501c01031071500000b0004415424002c01e00ea242c0d42180c003140500305041c809200d41003039002080102d1601c04261400100144520900c41c5c440038003040c40303513030195115800c4010b51145041c40a581c81001400c1440381456020400c000d0410843c210b0b503112550307005070700100071030368a80321007850600706103014000d103d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 462858534 1250 462857284 462857293
    0x6020a09120303050403090501111005070905030d020a03030c17041502160b0402130204030503040e0903160f11090c0915040f0608090d0504050604030809220204080f070302100c14 79
    0x207043c0c26402a034401c5100c1d5031460155074490006581e0440c0708000a0b22923800b80710b60180c000c5c010f80c0401c0c0c210f0410f0031321122035640d8100007890018411600d00068012101070020142c060044604121490500c0d550f0b59581000c03005800c400180003a00002140c441d0181042e02903040750207800750480340d100006886d0518031514103054038200d004650b024500480c0240610940c0d0549502101451402e49050f40c03400d90014042c02c406160b01042203071140c092640e41c800b01c5000c1c4115885801d1540ba800c10410340f600424486000301500401c0014502412080303501c0d00c0000c892440d40451544081d031000e000b01c6e00000c000e0b000c101004504039030090f40092050722004125140341c12500c5040300d441c0142e118598005005200c140001003110014004051010340070010140115000004240d54100c0c564000c0d540007500303000384107041c0050030b0b2000e041c0300100015031035a80072039404104480b100041140d00c030000400c000c00301c0c40c2ca60705051030030100c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 462859784 1250 462858534 462858569
    0x5160308131b0609081501361406040b1003180c060e09090c030a0b060105190503011d13080705030c15061206060102060c0f3001120803010306020a09 66
    0x2004446801d01904002c00d0070a180014885d200040d13082d242c0c0e0800c0d8a04c0300a0740303864103550b044058804008078000352a0308001402c0b90501014104c60103464003c5590b8200b039114502c1a5005040383d80a0341c1880e6001c000340d25200443e0110842c2460002600f0030000703201410b481c0d40078030050940c0506040014965031110300960324100496810015841c0d0b620015580d02e104034001307404d5000205020003103005101030300c1e8003902c18104180703400000d1006400444030f01d10707032802064001c40103010003031180203070444500d0b01007070410740d0b4206041d03000f000246607080200007110001c2e038002003240504c2a21452610401210483d02c01c00d5014003c0d0301c5c00301e50090007002a501500744404000402c14002d40041e00a03060b2a181c5c0600002c003a4459107690500300420018140d94510880032091b590945d20410b503410800d00420006c6654180c1c085840038900d0f004a10100d4440c904503811664401f5006943d440001c04c2a960f4880300e42c400c9222002c0c58215 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 462861034 1250 462859784 462859823
    0xf011401081b281412060904061d0f0f1506040b040908030705031509070e0d0809120705040f0204060f031a06042d120f170a02030c0d0516030813 64
    0x150901d407400d6407100010000c4039100d004245c020f0017401001c9480d044003140107401c011001c540c1043c0503010100e1001d07100300884e940b040303036448521003651146864600180c0140520403580f40071501814042c03c00d40340020900d40c01803c1503204079902c0001d114150f650b03a10008041c0d5001e0302c0c00f5240c0c5011400981140c104551607040484006c3c1d0200d00ca10741040360600ca440750f6190949101c040e20b0074400b030308003544011110180c0030800301a80d55039140b01000c041e2080d10060412038108400c4c0000e8500d09080d40c164180180002e11113075400c0aa5040307440c0c8249000505e0101e00c014010003801c400443d281c20500000d4042101031008402c02c200020a83c130801080c403400c00540c804145034818000c0c82d5000840f40e000081c5c944002e808080d00403100922102c08500a40c0d609500c68032400c00984d000003298920244113228040009200703090043c10581c00c020070881e46080c00000408010701440007940d44403988494010300c0e40c1140400714800c815009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 462862284 1250 462861034 462861097
    0x70e1e0a030c08100603080a120902031207060b04090302120a02030706050703020307320706020f031302010206011d06091806010f06121104120305160602030f011401081b 75
    0x40c2503c502403000d441c036116000b8020792045030b0780140900d2801c0035844040f5074107241148c0c0e1011064481e0741a00140e0380070400c1c45500041301200550300c81c85894858215041064094002d60401071404007107500440d40e0180d01540e501810760b02c66803014200c0c00c61141c0c01005041500e40004d1003c4076a01d03a002e540308841e151038640c41000c074900c0719600da1850f06501c2c4115450189411000c42d1341001500005104403405401e24110b2664241e00b50400c03510344ca08a8000300524003550380c10404c0340d004002600000300c4074269030907919610320004080ca40030380c0606000c15104030a83c2c0c00305803104000341c2903d25658440e03040c050320704814803032040050104145000e49015500c0f44500d45041e801c0c8803885c0c00e2a203628003c1c181c0c0c40c201c2c00d0307080c40303814030060000b40c8016800b404803610840006a8a1810f040010080721043e00500e2542882c3d5641e800c00e170340c001c0001034004200c180301045103580c410004d8010312415460600d4014a0561003507031145814 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 462863534 1250 462862284 462862289
    0x102100f05012d151205090a1a0f0105040c2d090f0e01210503070b0907060305060303030a0b0a050303130905011e030602091c05030a03060e070e1e0a030c 68
    0x280003440c1d241481c0340e50080070000c225090300580c43c201041a40315131000000c90003002d0400050442c98401d060084038401c0720050050742101003480204408983d40c50796407003a9004115840c1405039006a000c41c050084074015541d510150743d00300e015081c0440c0c0c034159081200c2d000703100b960b25800e070b0a00d50700e10710780481d540c01c0001c01c17010034400907a020740d03000035043d8503141c2c80d18051802d1065802e483d010108890040783c004101c003480100081c90107042c9100f0305041c041180c40c90b11265034840c1080500d048144440755a0102c104c0b604038404d03000c0821860101000140d510b11103034070683d858400007039aa400407509041d24000c072042c8a01c208160f03170340e60412540d200e540d034100a0b981280040c050001904960240c184104050070200d4026641c19041da0540000718042d075540d1310100b42e1000d5240d060040c0f10107020800c42d0340e072f254100344d5805003403001c1c121100c5200342c501300d1810342c4042181c115803115402c02410342542a54a040690b00c1031400e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 462864784 1250 462863534 462863549
    0x204060b0c062514040902030108030a09080303040c1202041d0a11030a0503040e0a020f04060c050c03070513021c112523010e0a1b0603050105030a02010309020102100f0501 76
    0x14000591200f10409080307603c020381c03002080103c580384004503030100c070b80c1c542c88520398410300001c114078200b0300c0654060090040110341d58070585001514180c0c042e130203d1a598402c000b040001103801a944040b5445d60500441c00b03600340c400500035212001c00c4103d0b4031002c0f9820f03c1c100100184101c0818081d00411800ae0b00c4201030688400c81030a0140150f403042008000c200c0b040152982c2c062001c000060400b03003219000100c0d075001da403050f000644202103050901800748121000c10301e0840c001d00c1d4039850306000c100c1342e05104030500c598070f40c0850304918502c1100c00c1082008140c040030415040d001c1080d6420307410603c20b4010484542c2d80303ca0040c0c03440740a1002d01c9400100750420501c05c2a040320001c4030011141d0300b1075489410460b0042010030200e07070021b1180028402d8031220a0442461213501e922900170107085c8001004603450101c2e00040554080ca0041003420150006030702e40001405181c0070310786025800403049145a00c054143c0710365 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 462866034 1250 462864784 462864793
    0x306180a150807030b0c07030512040f02090903090d020103021605191112280f150c03020a17270a0309050d03050909071e170603070f0605070309030204060b0c 70
    0x40c0c814407a0740f8000c9010040c00c80f20184089008100c15102030591144285809032800c0c0d2081495442074405407411114119894802c00452502d84241a400003522004600344801400050720300e15800c403000e814140c1c00a03401000c009106003203080250010112500914080da54a03a22518048252841841c00e101121903140c141e0600c584518150000d2040c0c1c4000110030846100f41200c4111000d445031820001804908024034024064010443c02096011b0294181d81d0341c081030f081098410010415015003100070071075550b140c0d0b0f0701110990354034545209885c81e0340d40f07203081d958440000b810701d0f00c00001f0415500c0344280c2d04d00000680d20400d1125101d00d148008010071000e000b81404c504010b4030480e80304280340b92500304d02c0802020503038005800c1d4091000900c070020440c8081404846460b00043c2c2a4010301c641850948003903000071017402a10100000041e4101c01e05100c1c0c1d0700c0340d010f10380080003007081c1540d80d40301c85450343c0300c1414900d95008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 462867284 1250 462866034 462866039
    0xd150f2c010b0307141909140f01061b110616060b0d0f0b040203120a020d020c090c0712030e1e01050604050c0306040c0c0803010f030b0f010602120306180a15 70
    0x103060041c000c040d24050000d02000e418039181c49020301001d800c00f0f4100c80c10741040b882014150402c4130003010300c698001407e62040c00000e104500040030310301c1e080b070004c0c010000c141d07100420440401000c2032030351003050350b0b180c03620002d96880c0c1c407103038064400314114420000c0b08070420401c1b4446c074001c120111003002400360380b0400c40c602801c681150011030b808a5001584240c0c881c0c8024191032541580d075003550316a400c40b4071000016405004850081c039010030100d025030380201c0716200c85240c0160072000e6403203000b4004024450014803000164020382141403031031861403d45044040328882514602680702000c0059030070080454001e003080d1145030b01820b10110440d1943e501c00060201616012000e442040b5104426101242c2c6540146000c0c0020f1403406aa441c075504040021140c007600e1802e880750600010000c55400081c0303061b4200d0b203c0b80d820b07200ea0311000001e000001c043c80f6000300031069130422528485a910126650740908584580c0a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 462868534 1250 462867284 462867371
    0x9060f041803020610060906020a030c020f040c0806030c060301150e12031c05071d01230409020d0506100c020904030915021006090b0901090504060902061305011704020d150f 77
    0x14882d43c800b60300044490300109203c0d83c00f00e440ccc68001341c0240e05102c0c0110100c1c0071100380f45449400100c1c054240b00c1c05d480c042c4032445005c08111040b50540d410044215948a404181d280a00c01c0c5d03c620003a02c1d032184441220780980c01420380e5151440c140000c1c034140b010709003070301c000f9107000001030f03019010f080c0d20030b103409403032403042c080b2003901d07006445591100030071300c400c2d180000c020141100d82400401c0502100380002d44c0700d012004001c0c0c160340c80034040d2485803440003e09892184c3c0031341c2e01011640c048803044026103a505081d10000126000aa000e500380c11289251540019101d0301c42014008200603440d44d42800204a91820900340c0d84840e256004001c00c002c69000b10b5005806100001040c003810313070014110707a20000b903040705c00c10480800c008640e0004001034908090032507030100ca10701940060741c68040c01e003004104004200500d1140429907121701000311400004015006401c560841c5440844204502c9800c41c405007200702d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 462869784 1250 462868534 462868547
    0x50309010c03180209190c02010b1806150f1207020313050f060a080a0209060408060a060605161e020a080106050f03070e0f0405160603020405120c09060f04180302061006 75
    0x140450b150103c45400d4036420040603290103881000f814094040380402d9200303d101e068098000e40d0000500d0000316014440c2d425104420401c010844004100040c0c0b40c1c16810301110300613420280da00c50124489a0310b0b8016000d400c1c070b100e24001d040044290700000101402c0350810702a4003076030799800402001188042440e034001c00c01703202c2c002c606070180f21400c2c0c03c01c1c10300c0b402600b00003100001c103002e500240d0000e0142d41c4200c0a1240c03813045ca04c940409003005103402440c2001c950709002c20b00c207118800a01c2001500c42c640c20000d840040a40c846d9401001d103210160b886261601074007550055030310912100f444c0d44a44d150000c1d10004883c0c4c07070750781d10030150f5506541c0300c546400100305031558001c1314010f22110302d840083d0300141400e501d0058a860400f400d02007454602910700065901036044450f03545e80c0d030340c61580c1c4045c0803112480c03400c1d0b110021501030080038002c44410803101500303004058011030414810030840010301900d59691500b00e420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 462871034 1250 462869784 462869801
    0x31b160309090b0f0f0d031b29060604170c2206170709090c090903021018020901140a0807080a1202070e16210b0f04020703021e0a0b0403050309010c03 67
    0xc11860500c803030041c140068070b0751b00306e8000d040c4680c55682c1c29040e1b642c1414010011906a01d1040d498a0800c0d4090740f07401e002502e2028000389840d0a001085843c810350095030342c1e0020360b10300340b0700c100410001d10001540c040d180640c201c43d01300a59034034000b40d0351110703240703400d14074003003201a0b129188000c0c0031840e00007082084e00d440d01c4100100040d003401d50b43c4020040700840e44280031302900301064807a03070089c4401409202d40f64121819142450481200840c104003d80e94451666054901c01c0e008650700070707540c800050004405d54030440090142c882c002030744c1040490034059070390040d4100c95800c1c500e50401c076241c044d1405814099402d800102d480b610950b09540042d001c01e00f00251480c00c20b45503090303850311440e400e0095a8441c0458180c0e800c107008144460501034a040d42411031555000c1d4560450042d015205142d101c00c03a00350728000c00c100c0f18020340101503007405003001d0400034020361086078889261b600340031580150603c2849900700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462872284 1250 462871034 462871039
    0x1a1b0708010e16030b0a020c19030206070806180a1805060a0c1b24050103053a0e0d080703021615120203180d050c010f11031b160309090b0f 62
    0x480d02c3c1103170f81d441e50a85000e016981016424083c80b20318103001c2220f003050b0101d00c17001d041e03250b00501e8000d240c00c0c0010217003810040104140051741e2078019102283d80041164021169107400d4014010b0020540b81400020164500024040081000c0e03024004251044c03194201b0f1103019a11803009012070902d02407200d00b14404215402000c0e011507620340c7c8555142d01c181c0c3c40078005e950003038109468613086500343e480188100510720b009400c049607210151100052000340e1082e40c04402d0307080c00b025850f80d0407242d41c0c41c13113604d00130780c0c2c8461b42688031422414006d5460394545490303e40f0030020040810480c1008031045078910f070540e02d2150a0b8004444c040c00382d0405005404140500ca41c2c0320050b00d8103111220405045590392500d400955030700d98292035807000c54101c41403a094010102e4901601181d511000e00c10640d03881f00c2030001c00803024400c0c200310452021b03610040ca0205035000250f1012224049020b0008411a0040021041100c0c070002d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 462873534 1250 462872284 462872323
    0x1170708010203070e09100f1404050f16110f06011d0106050702030c011d0d03050a021207120e01120f0630020405060f040509030d150602071a1b0708010e 68
    0x8800d803800502c0287c0c0207003607000c210502940d03503a02070382070300d0942c201c041c013902540c1090303c2e64145441078a40c014800ca50403641801c0402c142e04444501c02c0680d070400c00400810f440882042040d507000c0c607008000c503505503030b40360940d0070020120242c803080109101d000048052040c000d403900717079400601902e0700014460055640304141c10246019460020811050381c6d107a29030344101c103029898050b0748018085000f03003400d4854451011910061100b0341c08510b141140340304240443c00d0101600c0c1c0030f44016919100c2071203030b8024050070f140d244a040345003600726000315200750840142000003000c1b4200314011480f030300008807101901107009407805812440c2c2000b805416001c8034000c00c0c001c94140c0320121410745265000003801980b41416200744980001c04400d2004500e080100c02500c1d01e07203070b1084000d0710380c52034840c100071034826085a1800290000e40c2d140702c2c011001440d10b80001e882812100c2d4a0030280244003240410020858030303031800301d00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 462874784 1250 462873534 462873557
    0x917030307230a02060108160311040207060212010f06090504020c1b0103060807080105010f0e0c030106080705040e040f0b0903341707110103020a052d030117070801020307 76
    0x440e01070801400c090040c0d0901d805284110091030b0043c004aa60f50340504015810a0307002442c101900b10200905140c804041000c645231a4000d4544441102d016940700582d05000002c1d0084200c07000703052554000000b058842c0c2030459007292001d4841e450069034680401040307000f41c1c10100365a030082c0c9a82005d80d5010951207810039814100054600d40760a200c502d44030740740d041004075030f560324010710258000341340d441c0080c01142107003030b1607142100c0c0d40130041c003040c8240824001c100b80802c00c2c4e82d00440540e405040d48c510080c41170320b0142001d01c80209211811f0701da99584501155a0180100440b52200c501b802d0050345160140085040c86100f040030501c000400c202050001d40708403490058542c201040e00d840b0301c0c16007172200b1040200101c1d107052601c104800148a0f401c01c050794414480c40c80300c15114500200c8065402140e510410700c0d40f20000008607105080c1803031440001c86500803180350075210001c8038201e1105807a020049510140030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 462876034 1250 462874784 462874787
    0x40302040e162d0803070318091a0f03010c140705070b0a090513141506130608220209040803040c1710050604050f0109020a030204081b010917030307 66
    0x40340c100314104882c0c42202c0d01d803500011040079000300480418011504042c28200d0941d1071408003020500b03180c580c50541d81650f40c3c031403804001c1c20700950ba20b0407100b0100800c0d641009249030041070000c14600c20015110009601d8184c0c410803241c1045519414140b03d2004404000d440e6a95807038041d05140c502030b00180c1e022110341c403618802252152600014000c000550380740d0210060518082120342081e40d4260714000307240c502040000c00c6555100c40d0400440500c03500d0707032901d041c04140c0750f20030f90506031415030fa19000050324a03030151038584102c40620f8820090750140382c03d4000ca0b003070600080d50284940002c500892285002190814814112074440035070356008802085034030070422015401042c0d01e0501c00c0c186000e80d5600c08002c680030002403425403030b6440300c1c00060251a003165130204900709a81e0003503040f1070250004400b1107002d10225044079030352000c0f8000e50342c0014485000016003e0304a0107039002847e43c0d0b0042c504640c0d4a000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 462877284 1250 462876034 462876041
    0x7030314120103060b19030b060a06050703090506030c072013060308121f080d08011401021b13060e061201060303080412020a1401050f0c0f04030204050603030904150905090c0604030204 82
    0x120a91111483c803c0b05a402c6c0d152080324011340c40b4034140400c501e03000017000280c00312540802d0030301408000d05c50000703910080520555004582140e201d480f08102a0198002c440b4010019014a215000561271569820184440031980c0720884401481818192240d51200901c105428401c2d550800b00700c810b22070f4047d0004a880200d8501c0d9424078403026495807108881d40c0000f2101804540d000610381d026022400002070540700c0381000230b40d6111551018602404443c491141658804880700c00d00d0748065014814280c8903120890407050907154980305411b590f04c0c2e40c0210038103004400c11250581ca0300c08043c0d4850b2101d0b8200c0900d6000078046021300c640440008a180c1500da10111140000040c03c2c6001012a804070901801c1001c0d850000d001040c840d250351011981920381c1034401003541d459a0022900e94002c03000d80300c2e0f03c00c1c280b40384005034200300e104100880e00c165800f8045912646c031010344915110748426000a0304020a101504017500b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 462878534 1250 462877284 462877301
    0x18061f230c061006091211041d0111090a0b07060e030f0a170405060402010804060209090420030a11040c0e030105181b0a09091a040b010503150105032503050f0703031412010306 78
    0x14041c07c0c9044001021600520040c559100503003100b60303681c44007442015520803408000f54580010300000441c46035079072203460b0074442c0000b520b10410103190402211500c81c003088036100e41d085500018507400078000500051002c4682041607048403140c240940e800c2001b07480c803a1110307001104e140700010410f480142d002c000840c0c45072200603085201e103028a41800d000e1140d80406484160b90040d018480d510885461012400e8451440c95400c81250002101c0b800742601395049040340c40ea403a4194a4502008100324019280740c0c050701003481550450044a0100d0820300616225107401c42100700003807110300c1545e4840002c1d640180401d0306c504040e800c3c2510201400c82c0d0845480c1d07501c0004000508003000080c005400340082880e0319818540440c2e9207126101750302e00e0101808010507002c80c000490300c0013842d08941036415411900520598075030705840218001241c4403000c18085000c0c1040d03c09446003d98445140e0f465525418068803102c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 462879784 1250 462878534 462878543
    0x2a0e0607080a0e190f03140d0e0f240304050610140621040f02030d090302010219020103060b040602031e031302040f0f06030c0518061f230c0610060912 67
    0x401c1c501300e424036410540107050390700844030714504514001540401c0d42d031a007517495000d00070710340d901c681104e9480c824803001e480c01c40c1081e81500005c0c0402c50300c000340c111120359040c1716005100d00c030401144283d01400c00c0b59226111003c445020481500c03600c9412549808000b299103480001810981d1b8111591160400c0c9610001180001641c081303031480103050907201141824804d03598065600d0919005507880c50300040d40710061003c2860b1425010980c1c5001c5a009501c000c006d0701b0742142e42500c0d1a11441e02942e04e500031003482c1c0005808010300342d255450041202c0c40343e820a88101c8200f0000c0c1d0920000e0001002c088480300d80300c1c040400c50300c00501c9000c00544c003881c40c030a84a0300d4002400100340c82031040310700031001507040040c81e86401c0d0410f00c404200012840711622144006c43c0c508a407480081c00780c52445108492286252016004144400d002c1d9191621078100315031907101da0303101e40c1002c103820483c02c00400d80215070b11201c25028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 462881034 1250 462879784 462879799
    0x8040219080d0809030f0d0c030c05131412030a0c0b0105040c1b0302100c090302150f04030b070504050d060608010b0108010f090f1b0c05100228032a0e0607080a0e 72
    0x1411b003041019006940c0140101d07540b8020352040641c1401106500130180c1089480c0182e20080c49101000d1401039a0411074945024605621010344c483d031a0310404045d217031590403200001341440900c54044d20100e207510b002140e58034142c403609030704016584407000c50001610303e1859206600c6d07801c4d415805201e81d19401204c01d40555080140d072951121600c0d419271040002e94652400064107402003070007420345440d60103044405407604106401601e655150085070144540d0700f150360003804100b00c01d0200300c1d994102c02c05550b40c0900a01581c0c140600440300c41000748502110851045d0042000c0d6082e54026044030320480c8000c203180b105445081100303100d011700354000078124440c880601505001020459020140c158600a003100600d6500740d00d000c0da505140040903520f003405800303944149801000307a2520702487d04181c68240051943c080c40b0000f01d60010610059031270b0140480c0d8485030310140207410503064071411160080b02d5029039400540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 462882284 1250 462881034 462881047
    0x30a0b0402131d0709050f06040207020a0801020d0f0f0b15030a060f290f0702061303020d050d09050d05071202060403211409010f080415090308040219080d080903 72
    0x40501079000c4031078802c040c100100c05068000d44c07406029922142243d0b1600d814080143c684402c40c0f6003001003120050307101c030028000288070300c980c1c0d40060123039803002505d60b140b40100d800549001040e81c50401150b00105d0b90321080d925800046507206002c005030030b800c0351086001d550050404040060403540300d0311282c40d4a540d40e00b1911801d810809112012400042a421010f2032040e08608081e03400a11345443e01034000300034446c6c0804100000000065400c42000b1900201031500d802c6050030b0450710380741450202070000320307001e8011078241049019580c002d9403010041003e1490003843c2c0341b10001e8184126804a01040004049021710030785010344000710101c10b104440490014081c0700ca0251a43c102c00d00610120302660b81111043e80c3d0351920b400d04100c42e03a03070340c500744a8185040c41990401844c100201060560020000d80700d280709a540900c10240d10f541100b5807101440384030801e602c914080700040d4031810119400100310b40450b800d101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 462883534 1250 462882284 462882319
    0x5060f0a1808010c02061611030301171614010e0a123215010807030f12230a0806040501030b0403110a0c060c1b06050316020309040c020d090e06030a0b0402 69
    0x1001d00300381c0d84c0140e11000510000c441c4403281e404d64250141001c0c443d2680e0326910075200d0105100342034103182c292240400303014090000c0d041c6080240b04080045071a50404100032030307440c005a0002d44a01801e24442c20001d041d0400d4800550142144500d1030341d5909038041310440010340703024002d150f0818800d07a440c48040c0741c2d00c840b01400d0452550191100c0c0e00314143e1104410382e00008080020030f40c400d103864502a007180c103030719024aa071001a203005480d1020881350704010380282092407100000382000034078507038404155484610802007911000e0101400d001c20600204001902584d5069401d04012041d580c403400c068641d01240c6040d60312490105003016011400c201150f46005901011008050107241c20624001e00600000300440d4408080c13050340a14a402003041d64450200240144295840d4400084d12201d45440341d201140815a000c0b8041066400880c820744000c1c000b441c0c003201c1c1703031580304640101600c280c0c0c02030114101a0a1030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 462884784 1250 462883534 462883541
    0x90e0a06020f07020306130b040201081e160f03020309120304031b050703060c110a03081302090a0606080606040303020c060a0504090504050a030e030c0a030f06110409051005060f0a180801 83
    0x1e4042c401c1c0e2034441c01c2070700606040c0140107218032054140d0540007030015941e0084250883e07020700c0c003c44590b507000c2c0302c01d0b0801440c444510b28064a001080f01d20755403200d050340d900c1c04585d943c040d0009506019800c0c0c0c0000c2d101a4216000385450500745840d0502a40c0c3c00350092170480c061200c0702c0640c0007032500f011800c2d591600141c0c400c0c01409503d010707907840c07461a881c242c85400ca030308044a40303c1da42c800c07004042202d00004101000c18a010311907005030018603c045504180c0c0e84400100904d02c1110040b845800018034549480c60683d002c4a0f05034001c1c08213486044104001d80d4403280509041c80320a01c4040b942802501c0740da441a442070f0001c1002d080307682400b070401d007011070000b4881e500c065404186a107621440500310303540640c2c1c03001585028079003030000d44444001c1c0c4608031408640021080b29941005000d81204200640c140751260f003070000c1c86c881c000c0500780d440340030080384d40c0c0f1604ca03848624154403034840c40700c8000c0e2900c0e8110b094 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 462886034 1250 462884784 462884797
    0x1a090c09060f0406020d0c02180603010f0f0e0706020a030c06050604111204022d040e1002030403090e010617060112090510270b130303140f010825090e0a0602 70
    0x8040e000f10301402059010407501c1c4105145082480c0080a039074001000a4002524610044940400b08102e900c2c250004d10021a10041c14051070b2090002c11008010004a800d40c61081307010005803140081400a1030582550300c1c80441503098549401411001c0c000541041d903416100040c189003001800071490030400c0c603181ca04290040005544590a078141c214a07441c0c1460b50701d041d0035081c0b0a200710141c8001c2251350940300d041d42420968080107103654000010031003010703813000b85d0200780d030703d12540d414a0743d0702e8030b80c12100003007c0004500c40344c0c03803c408281158091b800d4403403400981c0320082070940c01390303503240e04104541c2d080361801501c0b000ea19032540c04108002407003400740c03c0c190030910320b107440340040c1001c0a041d180040715062012828507100c0d42001c1d80c0d114025074281260b04000d0715a104118092103415200d00030240341c40a03001c1509600c0c1038031800121103500d641d0401600d00010002c0c0410008540b15031810000020f500b40080c104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 462887284 1250 462886034 462886057
    0x804141f050a06050f1507021201020c060901050f010909080d06030309060f03020c070608041a090a110f0306070e041d07170a12030f0212150a091a090c0906 69
    0x115000d030030300c0580c1920006006108910b040041c00d000a8581c0e00ca4a0a10081210b150310b07044078034071500c5a144540803020390408100705041110701e10540003800e41300403000885090741d80700001c5500304e520070340e940703240f1041c1e00c401004000b04d41c1d000001c465000355003035482c0070f90400c41d6800b00d95003540b0450110b2100401000190f401072504188c000c01400c2c103514010b0322001c415110b15040c041c2d94180203c080c04602480b43c95a03500784d03e005241c01c4540181080c40300650307202a09117040fa1004a040201d4a80d41080b0040c031600d0400503000301403035183c001e02916200300006810381c03c41e90b22500d4460304144a020280ba0641c954090064142402c480100d042940d007034030342d6964045103100001518648410b03241d045586800640f000d0407200c0390029200c2c10b02e95102d001940400d0000100307843c1d000310b01c4403c0440b07032000c0d419070794a82c100c20f41d00a204000e60038503140c5c0a00307285040c04550240d002c482c0c50307190741c50042c0d240e00081d41c50f00b0100d40d140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 462888534 1250 462887284 462887323
    0x1050405040e010e01050115090314120f0310060509030a0605190c030603150c02030412051509061e090c04110904060e0106030609050112080717160209150d03080414 73
    0x825070710084c0b0846e4050518041c4422104c084e460004d4174600c082e200040801846010245504205110181d507882c558515a50764140c0d08030b80c11101d4005640c040c44030f181c3c5d070000042150103003080f03d25610020300a0100d5603403c1d1030f5003004280080040c0c00e00100b00a424041035114800c6c28a10703500c0780c44c001100d5040d4105290711644450155000510704400d800d041a000020303101201e01d05074403020030b0101c504d007240c10000050040c40301d00c241801408180c020110309140f040c2c1100211018a141e14030152000307200603070704444642c0041407080d201d07051a41140c5000c00390f19241c1c51034400e400c00404c0480b05030303600c03e82e21120400d00502c00668540504401000c0f2041c0c14000d80d41010056042c84841c1c940c001c01030440045c43c1410040780b070700303143d01e0b81302c40310350f429240c402c50840d4640010403200106d00c185403800018504410b40d1920b59041600a040341d11041001d9030180c03840580544184c0c1c008007240480030002408104188400e1210328049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 462889784 1250 462888534 462888551
    0x11010c09060810091e060b03042612072a030503070e0d020d06093806011707020303071b08030703050c1201030305090f0f1807050906180109150c0204020901050405040e01 75
    0x40703480c2034014180f40314040080c080440d0311080c003245030b40b4078108a034807002d400c0302c80400e2b207200721011100660f00b048100042580c102d036103440c801c10140212403140d0342d07070015100c18005003400100803410134070101d0644c034841c1501c40b0b84804042c110614113610364001404106840200322955034a8001e1001000301d09220300b40031002d1401240f104281c60380d04c82c14552481c0c16090b8489084d90b00040300390303110b0100c603410036451a02070455410308510094030b07035108032280404507170420001c0c8180b42c0d001c0b602540064101807030509648a101044000c1c00c0301a103000f003000c20500c940000004019000c90003076201ea110075070380d81c0345c0c00140403440441d94901403203411889080031f40354440d120b008070310314036130f18908055603a503502c20b940c24080d0794040c1d0b42003900450b848510305120580a40c0c0a00e00762035446806923503003a01c4441481c402c55840004005407014001402c05070081c1064010504000381801e86960105040b00e26212140c0500d03134680200303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 462891034 1250 462889784 462889841
    0x15120509011d071517010b0702010c020418020312040e13020a170a1a01030305030601111c11060c09060d09060f1802040c0f0f080a1508060711010c0906081009 70
    0x22003107a1585044c4034100304c5c030310300c0350749180e540c144203039074084e40c001650782c0845e0f20804d516551154000c100304209044022481ea03240ca411200301c3c040e11504a40e9840c1028900c01d8800320349070b6070480070032641c4001c226070782c8030030500003241c000142e144085042c0c140e01d90b1100145034918020450441c1504001400c0c800c1c010141e1440c070720079001440840c2e800300031203902c10800c0c203040c6094031840305800e14102240000c0411603503505203864406030301503480c0c84a180908111402501c07404450040c500c2460013241d484201001140e18a003950b4009490346030240e000004c01d090645289400e4501101544107181c08000200c8218136040c40ac0010901e490b252118032080e840b1f2010340307a0110f0200303c034140079910700007074540b410b01c2d0014240b00388107038607006000c0d42c0d483c412962510305035407040208622460a10342e0410511504841502070354604481e1450704201f503505c0207014166415018644101007600e201601581d100485100096240c81140026 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 462892284 1250 462891034 462891059
    0x1c080c0616090302010e0415050a0815060402190f050c060a231005010c060603020303072102010b100c050114103206030c070611040f15120509011d07 66
    0x407000c0910020032030078005030b42e01280381640d03940f00341e80003d6007002101515410b10082e500050b800195020045a64103000c078501c980e0100340740344451940c5903c0100300a038003c4a1044203400b50f16841903180c3e0b84510340c40105060b141c00c00c85e00d400c40a0071040d003000403c8031019807036515420104806440ca0ba40b0b140d1540701091800c08a090902c00c91103207180c03600c00c1c68104442d0100c1c8030213200680d0301c04401194000d00301c0b59140350034501594100c410500c8003007802d9010380d502406500602980009980003031245498801e1100300b0b03200040a6002600d00d51f5803400124141d03607006e4091030041040c3c03035840d5002c0c4c0c60301c000e40c107841c00740e06400200c801c5217201e4081c5460104040d5004010221000703034581e40c80d0309207810240030300e40b00581500d040213188610140110020070542c1d51000c00c5450b0582c81e8602c1210551042c0001000209000c007810143c89072230b8001d41e00100c0c1e03240086400759030301ea01121246041c0d403441440344c0242e8410031042d0340540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 462893534 1250 462892284 462892321
    0x2151e030703140112050d030e150103060902190b0904050a140f100602030906161707080304020310020306130c090b0a08160e1815060f03070f021b1c080c06 69
    0x1031751a500c4c448165030301600c5407024403030b08090507107640c1c5468107040c040c010300844140c20b5038646e0556a4030b092281c090000d81e403080c1e0143d610003407204449100c143c41d4100359800c0750b06061030000c11a0030f206c01000010001244299148540d5084818020303680b4058128861a20480d0a10306140c4c079054000340d20000a41d8410060408a0b4807150217681c40425068401e40541d2151b0900c401600d1045c00c0d1060358820008810080108032405940100c2c0290102c0b48580c82d500f440d4001c910080c0d4590358420010300d441402081d864001080349010f5107002942c50344d0b075140d20380964005d5851000861202000c02c1010742c402800c145002d5590b250160080341c04401041d030b042a11402d1491580d03491000a28400c2c8644840e4176046002e020a550303241d0032004007000d500b0a0310b40e580018203122405950300c6c40040c21111800000701010f404114040400040740c41c0800c0c0020700c0061369080001113402c1402a001140d070110160110b4903002d445241e2000188 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 462894784 1250 462893534 462893549
    0x302030f0603010e070e1801020a05070317060a090207152c06070e061b0703060905010e06070e1c0203011103040203061b1b2a0f0a0302151e0307031401 67
    0x41d640c4d03940d820009441011500c0d201940b50303803916a5407100001c0c88048040c00c0643d800040c50000d5079510070000c1030410700030b03070700d1814144415640c0307885114292000ea0348900c110b90f041c06440b169600400001e4030485e2014129101d000402041c0d400341141c054114804100c41d00b50082c4440704450801a444c01412080ca8561000341051170400c252600550010440c0304441040981c4006001115011034902595a15265016041041c8100c2d019400d1000e60b111415001840034042d0b84551213104d03458032204140459400b4404440003001038500d9108003585081c032030f005d003030141003130800d6480c0b5060052501c0c00e80050030b25047d441d031400c11210380c120310350140c03995074100035815880c2111655455240c0001551600f50240c1d945d0b401c144006000403041011020541e10003032101480e50030403041d82c3c43c2d8440650007107440442a041d541400740205440300c94508070704103919003407501c8030701a0411504680420f40d00d401c8108849103204c403507801840c2c04c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 462896034 1250 462894784 462894791
    0x406081e1f0203090a0515011719031d04020310260604020f010e0306071211071106030c1204050c090604050919111206060913021c1e030302030f060301 67
    0x1418000d9141219080c040ca10440d800300c0451380340703d801e10040c1c2c0265040401c80d0360a40d0340a5110203020b4003842402809c00c511080304007a00030120313500702c4540c81c0c5440c10440c015140c609071044001c1600e005841484690b05030290b5540b480658084e50100e60000c100a049c240c00c2100c003001d06000081e011124441c0581c0003c000550f41da02130b030306030f03105111070451030b0043c0c4043c0750b44000c941e41402400300b0009178551100b10300881104001060045182c00740c0c60b48403a100e0204090000a208400c0e600d075030070f2800003107402c00c0ca41c0c0c2c0120324108640507504241e1000343d8040321140c1001f840710704549081c5541c00d800800890b0100454103041082941d62484a1f06203106c440b00f5042c0300091200c4400c8407000c40c2d03030180c41c00401010800d02d40d511070790115903803445485610080f800c070074512002c010700319502800101c1c90390501c255202020b6403022085a184c3d82c1d404a0f40a211080140c10100c6446920003607264203010b0b07007901e600c080c010840c5000e40e24 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 462897284 1250 462896034 462896053
    0xa091e03150b040f0203010e100f050f21030a051c02030c1606060801050a020d060f03120503090a15021809101a0c0105090a020310021c020a0c020406081e 68
    0x11041c034500c656400818000030800c0303510700814007401c405108000381030b10101c000a011036034050002c4c800c0401c510b65000140d12054805501c2d2803a00949030022264a02c00840b07060400c0c030101c512041ca440b0301100c3c22000e085900c0c5a100c0c280c9603000840201e034402440e01c856407841e0001030209400d50542c0740c1054034282900454a000048080b080000300c10320245078012000b800b2000003d02640c500381084401a604c00410710101519000d000211860000e8041041c0e030343c81a003940b84c804028400303c0c1c072134001034140e071a10b003d1000c8110006000b554006010880b041780036840e85075018440c0c01383c01e4500261401b4040450400c41c40105480014007983c0c14504202501200c00c400030f10a8090800b000c1041d40c40e2105201070488002002c042c000d03c2201210369004c02000c0c040140d001d990f8070101c17851905010b1101448198000d800c0c03c90307081c0340003a555410b94002806031542a8030605c1ca0ba003080c0c84400080c1d91490001080300710711300040c080d00c0d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 462898534 1250 462897284 462897293
    0x908030c060c09040b04090605060310020309120306011803050706030e06090a030f17010b030906060d0b070f210b0405070201110d1109100201050f0703051512120a091e03 75
    0x100140b00040d502c50029060210f0381c3c403a480a04107200280040003c40201e180000040500790341051082c03041648088a4050f03d00840b48980c1e41070b0064044400c24920300140c0e0f82020300b105040c01354000300034580040c59821000154005e800805200b03140c070700003408413889002c0c600c1c540c0d04803034208807251000003060703a5016890324144441c0c1e00140c104413a0005490486041d0350403103c00041c0001c5a10301840c0111100825120561521002c014024248100c010009032889001600b400e0090550170204203003810490b58500601b007400166184035041520348036922495400141024415994000020700003004401da0380510301d00380740104490040519140c01e89007180a200005641d04280701600d001c0c14001c641001030302070b2608842680c080d24202000403c2540329001e2140500030345201483c1055502d028410308140c07124241d07000e441180c44108103d4641c00092107107624503500d10395442c1c1007600c00410020062541c10784a40c40010510105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462899784 1250 462898534 462898543
    0x60c0e0306060108090f070b0d0b0103050708221a0f100b04170a0c17010b010e06040302041a19060206011e060807090e040c090510060912020a05100207060908030c 72
    0x84400d0130308210079921852914a00024403d20b02d4490003112000240d61a101c006407485580186040c00510381000044084400407624400056580e070003290f200c161a50300240070322800400103e50402d0354548000d200200e03400942c82010380310030055107034501006183c10140030b0580020752031410941d480603000d5801520f1042080039508001c55004204581c601c690024071412059555008808122480000349000b03500b0130080b4040b6610941032810841001426907040c5400c58007400020500b91840a4140301650042d0b1100d0703540841c0411104807800d0300303101d51820700d030700241043c07410303840351480c5034102c0f10083e1038164020b9401d00340c03102854031103080d981d4075400301d500f040c10f54059600203083c54107000a0000000d0414180c6482c0482400280c64558944400100a201d06000551000420f21000400403c5c448116000400c80034586885000049078a9040040400547e00800042004540080024000303203d0880598102210420303440c1d2107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462901034 1250 462899784 462899791
    0x6070807050c07030f060203070207090905030a050903100e01050613091e02030307061a0f061305061308010e0601091103011d060a03060c030f0f0917031819060c0e0306 74
    0x5002001c1500902c081c410821140215089035901c0310f10302d2207041000007036200303894440042c0a40309000c5802c2c0c100e40154041e46034407a000714a049841c00e0b0448070340d00101c050b50b0749400341300c0000906201d680660044000941c000041c80e0410604204000c00c000808004181c10211041c0110b0184035202010544024085070440d44d9480003a0031407056280051000d464520f0350404000d800150203a00b0740151207403070070400641e04124031401400e00e10024070303040a0081c050341c28828081c05580d040000700e41400b40d00c425280b400e40d00f10610b64940c9610140c01003080d84401e000b0122032407080d084071442c42d41061050351030a000d20405040003144000881c0b4240c540204039001540c0080042140b410302000080141900300015a00c05080131010850035595100c0c0100e000d900c42140b06441e08002c0c1c803410190001001080c0c402e0341d40385e5140f5040410b000310309541070722001c440000f5215113070010889a20901c40000c002e60404150080c0d2000510243c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462902284 1250 462901034 462901037
    0xb01080f060a0312171e04060f020d02071b05010507050316110405040f030e0916080603030904090302070f0902030c0a05031003020a0f061709030403140c04090c0302100206070807 79
    0x31035652100440c582c01403030f0748000e108540002d07100807400d5004101074001c0e4011005150340d91280300d03501d02811103080305802e030364002102142c0024819405401c0d030f030311507481c0542400220304a043c104d03040303480207840c05c1021070203241170040c1e21b5010b030000d020700b400c20908045182e11029034a0003650b9000d0f50b150a924030704014414110309020507104000c0c0103100c40d14061518294202d40d01c0300850105580d80c8058850f440c5c0b8103643d911410321031004180d00d503130104040340c00300c1c070140000f905404100314040c2c00741c0780c0d8081c070041c00d40030b60020040d07039241800e0b181e00d541842d4001002184140248051288a00d085400300406454541c3e100d46814a08c0c1e4200841a0303c000d40c0320901250029190f081108204100c1c1c03040e440e40501c0e40c050040c0085010380031038424000e03030410041031001401443c50140003907001c00c00c65402880e8840403504480036044241c80d0324080340720070000c510b00685005440d640c60b1000c1d1065003864032010b0523680c0094103480 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462903534 1250 462902284 462902311
    0x30309070e22060623090622021207022802090c0c0708100b010503040b0615070b07050723070303080c0c1f0510030b0415021218010605040b0108 64
    0x1800d0706900b50101809102a80601c0c40d121014a05030004107003d11038806000080c084940b17400c400001d070345804160103400c98002c0d5490a0410445440b80243c4824058800c100740b0000b001c0d900c080d10321420b141034146441e0a200c1c1e0040c0c9040e5a114048443c40d2882c1c030142c0070000d08402d1698000e0f41603680b00780b240c46200f014001802030100c05882d52151400004406100103101c1036100ca0f0f4002c100241158003004545a210458001d8944642400482c0303042c01c04080108002c1400c891040c00c10038144c0d034101120209803003d40c00507201150683c00e0141021070320111541045020300016104001c240d11070145e84005414010100000741d890392310042201d0b0440700071010381d03a00d00024419403d804000303801e02c01300207240500103066034003080c3c180425a80c1003000302c0030603616035607a440100442c20140c000160240003514195502102c1240950b01f00c00f804c40c0c1c03562800500c14212581544914410f42c240300341a00142d130030280d00d60f00003496a1002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462904784 1250 462903534 462903541
    0x41d06190b180a17010c260f0901020909040c060206100e061005040b0c010204030b1303050d05130f21050301060e01050732010608070b0a080414070612060503030309070e 75
    0xf4091050b9980030720740f48070801c0c40f940300d180410f6200d026220784680310460503040c00303181c00301c62151010070304000c12203040104120424804403e44d0008101c8005454211200c002c90000d02090300d0440d600354555000303118054061000603800194404018040c3e45084900d03040714401610460113003801e11901d041a5204004481c090120141010b40d290b1301c82c16010700035442071200b03856542e803650104894064a40000c03014580503a03130141040c00101c45000200005800c2494a16101a4007000610818150000580142d14400e500101442c00c0f81449160407510380c10000204018000c0d40d80100691064010078078240303403940203501c6c140307044042003203817001c068142130025105c080d980400440050300c000003d0101ca603407200c2080da101001d0203040071405040c4001500544951091039201d40036598210703000000000050070419a5000100041c0180101a00409640c014040200015001503140d031400d501401d448110300e0064045080401020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462906034 1250 462904784 462904789
    0x70b090f03031303030b2422081c0e18061003050403200a0605100303180803040905060414070201020c2a0409032001090c050904030e060a0302041d06190b18 69
    0x111440181d035400c5644801c00345503040b000b20740204810001c45030007000c000000b40c0d49410311800701c3d40248001c000304a58180e00240000c5204018020402d070480c100010760385255214cd0014111907903181e05080032420b004030303a882d00002a00b40341c241018000040d030301103c62800002d1081181014090040c4403d0030b0496a00c1c016080f241421300b80007545c4d200091240480b03101c2d417540984a0304c82c141c83c0500300c0c2d451007202d21680041c481000320301d80700c0e0003065020302c00810000d03940b900084000d02e0100140ea0b040c1c0180c0d400b007003440c01020108950f48100030041d25265405000210742031071044629070f10343c007454542c02e6a004150245800190100420701280341e07110320f858030f5a0081034407000c03d0303501c0b40e0401c0c80000c003800e10800300340c0115059520744640e003003c1002d01003140d1001001104240d0300300400074481e40d4020304584904a003d13240f404605292041192400c0005140c000c0c00819050400c103280710801241c0b52501080d10840449078403000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462907284 1250 462906034 462906049
    0x50c0c01050a020f01020c1501291305030f06240f190e0c070614070503070309020a0801110924031501180803070b091f0b1302070b090f03031303030b 66
    0x168910b9800401c42c610a1000824030110940030400007040d0703a030342d80d0b0f102c40c18ae40044900c0c1501d8400035222141c0d0130001001409000c1e480c4002c44006652103011900c4c156040307008400c25008581888049060103000b0400009154000454200700e03500080c00d07400c040045503c22020744002904004a9503403900051900d0118a45107241c5070020f2207090388105401c880c2c80e1302d02032841c03c8990061441c24003a00e12956054199520250306070001e2880c10020b81c0c4c8011140070001d4024024090b01190400b01540d69898140700d00c184140c1190800070807105c0d140e400c81c1441d40001d84800e5950001420940c950740c2e03000c440058a000d00081640503214640413000b007020300c0000018003496115a244504a0b50344608103034070380c01741603104850000d169000003e100c8550f0460069000012300c110103e503404c0c0d21650403030f48108002c407540a07081d0304200b030302c00062155220151500004d5444c626040d400005100d14042005090642d21403092205485502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462908534 1250 462907284 462907303
    0x30c0f0c060f1c1104030515040b040f030c1203061403010b01050717090d03080711010c0816020709020c011b020c0a030209090123090d050906071e1209090507050c0c01050a02 77
    0x4200c130f0a006902c0107000e038400c0c00166444d1003000c1d410800036414025043c0b007a42c00c4042941a81c459544600d220802c042044d010084a044650f02003107100c021740321000043e4800098035842c14580301c40b1601e2545178144a6494481705c4021079030800c04039214558000c003040600c00700c00e400d0346047c1c041c0301c15541d04402c48503105420140c0046040740591155103d4103102c84040c1c0c800d03801c1c0e8481d070030302800191091010400d00c1c41c2412441c6602c84550058410990321074441314101d0301701d4455851070b40c0d1038078550722010340441c14602003100f0310301c040c01203c0070240100d48598281d100082c09400660001a413007142940f064000039400480c41c0640c0504080d52000e400065031801020700852840e00710027801001103c140d214003401650400e407032503d4141c084603135082000740f4000d002c010b030340010700305032a001000d1107a43c6461034403e04200032642264001080c040a0110801600c4015400056401c1040c9000d103071065565081103070480c00d00b100c92 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462909784 1250 462908534 462908587
    0x715140a03090201091a0315060304020f060306013c02030324120d0315080a0209160c1b0927150209180105091302090f091e030c0f0c060f 61
    0x807003a030a0b1b40201c000960090703076600791070341d00c0350003110800c0250320082d64001e41c48a80d1100741411402c1080107198010305c141030810340001038512295880128480040130b2000e11521007030108a101317402c010b81d4803035100450651901c07404044154840c2a00705001c05103007903040d6151396406d04205014401c01c41540c951400c13440016019000700c002003051000d040801040c0c0c0e0b4000502c00f010160000c0030804941c540401c881034801d03000c546103003048024110307a07021a01c01d080070700c10715200c45401c0e5241c52070004583c0407038501d4646445c0744044d45400c0700e2028010b0079000c0009402139440e0804d9036204035000c00a01c20510b5590300203004412100d192086404454121201502e5130303807441e03503000140070100c0ca5044009621889020115442d504c1340050158001d2440301100e80d54030034421480c0192018503010305070740c2d2000818800300c0c5018040030460030080c0c0c00034241c0c00280c0300001c159001e50f50b022080084c1c081200201c5985250f4071b00001000f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462911034 1250 462909784 462909809
    0x606090e04050319020c10180e130507121509020603040b180601060203180303120c070c09110d0e0c280306020705010902150f0a0c02060d05090715140a0309020109 72
    0x894001035101c0060300303809841500c0459410301f00c02d005040602c40901e080ca0090300e0541002c80c03201c00b4100c0580070420803915040e1001c0000c8003041414080c0403580311001440d15149046500000204800b6902070708019440340146c0b5110141da41045e4080b10603541c40d035404001d080c59120369010042d1a124000000461a4000c80104140c00800f04050107904001082c5617492007002c2c82d07110743c098080b001030380541111024018a61281720312417692075680041005440b00c24070001c0070101d00044510340c00005202e801c00101103e0040e0030203400300000140b88818803080300b91840e1900c2c4031805038812005c4d40c40d0140d50f10000c215250603585c00c00c14000d207904603089002e080720920703020f49015410241d843e5a9010280d052603e105160201c40d5844840c1c0100e8000a080c0600c042820f02030081e50710502c20b2100070419603244c03500e886071211000c82003c00f800a9606002c3c0c0d80d617000030880d01c01100c24100864070b8121032004803100d9410b41d002d400480b04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462912284 1250 462911034 462911077
    0xf0807260a0f0c0810290102030d06140f09090604020103020a0215010b04060f1b020f04020f16060b040b03031b1507030501050109060e010507060902040f09030801090f0606090e040503 81
    0x144000d00300342c60668003121100010200c2c0e04040300c074210000311520707501c6010202d46e48511944400c82c0141841500e0a25411441a10590700c0135000410f240100401c09215400c08092003194540c0c01c8500c1007050030481c540c40c0d10b5070070151001e070401d900003440f424564020402c0346040c031b00f0a4444451507035035940c243c107281c0160150500060610001c49a09842015400c540c0081b81d100071020709031136400c000385d681c030007007955030460b40901030029800114006052001c0e600700e055020440c5070714000c400c586120441601c038624204000007103445c00004d83e105c8001c1140e009060031700d082c090320300e403046070750704070100220400402c581541e0523089681259000e0300d6803007042c2c0d01e84006880c0b00d1045601140040c0c01481100007151054104c0f1402c6800500001125007204c1400c40c02e903103401405030042124034004002241c000d200302c80303424490200030040603041c010003d240d01098401c102500450002060601c00248100c5908141040038590501c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462913534 1250 462912284 462912293
    0x8071413081b0904020306180712060b01080703020322060b041b0f020c010804031805130b0108012306031902030f0613050705090d0309090908040f0807260a0f 70
    0x2d40c802c4806078084010440300d00340e040010f403080c000e81d801030252107681c0c1d504606444489501651800c83c1c8070350880090016003d444034041d42d4000c81000c1803094208001510420300601240201841003042180006010041c4041100d0300602d20040c1c5005040c440c015008907e6440d81c0030345007884201c040b100c0340001802c136041c507895140e603000018005a8550561a84040c003103420388000400091240c1e85941542c4403620340c03007883d26111004991503051a41c5000340803542d4504140c0e8960304a20303100e0040003032101d050503203468050410141000a024a030103040f01101050b1042210303031640c6090a05000210344a01d4440d4940d80720448c250391442c0604000c0c420007002c4d620501440b0311a100646869280002c4031080c8400d00790418820f40400403455008a818203060140c45c035610b005044c041c0d00d45081002007100742d04d41f030f84104202d6100e41c1080096039403103c98021640d030014046280000b14084103410031407550b00041000503000038480030030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462914784 1250 462913534 462913543
    0x18151501020a05250608010501020a0807050a0f0503030108190512090114030f070e060703080412090305060907080706020a0302060106030f111603030b0103020403050606060f1c0504020f04020a0807141308 90
    0x514078504c85181030390b456106449200302800740d1070060700584170f0300c00480c00705402482198490310854080491079121100421648070041320250000401000031200420401103011408603440d114006d0b19a261990341c42000c0c0c9038140c400c004510110168000d0a8251950300e191540716664a801c4a420381e02c10402c0390041c0100343c00651042e09406c0060644500640c1a26424481c6d21661500c14054000c0c85c04c490422010382e8001c80001c600f0700c401c42c058105500104210303401c20340c00c281840c1068012204641c00a081c12002c04d40c0010700e0b0381120124107000030313140400c402c0c2e4406000a1109100e600304009252200c04800f0407a034440b280c02540c04105c444d0008004506904c606d1001900030380c0a41c0202d1a07078606174005001c4032454180d89490710504502908122003809060700c440d9603200100070543c1031854145040402c04c440851805800000241142c5000303001c9004010b017040042e81000801821140c400c80d0f1451000700a0341e42d8030040d56207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462916034 1250 462914784 462914833
    0x6050a0f05090c0909190f0207060509010e03070305030411040605041d0d03020c100e0c100c030807050403080d0207020d0b0c072f060c071d18151501020a05 69
    0x141d490b440015a203940f01d03000d0712082a0010041c458a440340e2031024100c011451046150556416030501c0200d194401400d0b9684103110100355450711207062821036083c0081d040094004004202c0001c1d40041201e5005501c420108107085160012400030651908941d81042c03074006182002d82220f860121034480b600300300c07020206441021030503030140100c20419984440003840d0204110f0f0040c00c5058455012030700200c51040c009401c9984c03034aa0034000c0b4402d02d0340d000074564010b0196500690324108185003038610f5841410a00c95080056040c0f980802c04100f1075964075003001015401440700c201e0742c01c003c0c070000050350000d4422200d071403a50780d24000007054401000d00d032061030400800d4a0101000740f02d05030348500580d82150203003c00c0460585001d80d10005091445003003d183c40c0303445072200801102096209141e503000981d4400d00791202c024443d8001d6441c4e85042d0400c1d10000141c0c54652541e0005041c1c3c0504c9180d0940f0940d0384400004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462917284 1250 462916034 462916039
    0x60c07110a030609140f070512010b090c191121090306040606080c010903080d020901141602040c030e1209010926070611061b0f07030804020f010e010504051306050a0f05 75
    0x170401076110b00540c0d44691a640302100e07008540c080000b49000c85603070800600c0c0a00208001650320b0009030141070498013260b00000c045003080307000503c1300c080914070300c1a007014a0f0000c2d80e50151341d0341e1001209040042e1250456120f0032500302c0702600c5071801c02070104c0c0d510381005d1a1407c050501406642c005104206006a0340e6209290303100860703401c0003001c1e14000110382443d02a600c03140b20b81c3c6c140401880000400c4d80100e000b41001e089207c00301c00088120f104001c141d44206040b5400c03d400d0681200364000f01103044c02d807280560708901d950360400700060b501480252b011400102510031140041c40d0b01004100810f0130042c02d0321541511100c0039586204800b80380c00696101a0014080c4e0b03502440d52451000c0c026042814140031015000b000d900803031084000031018002c2c40114105038402c0302c29904e003400c00f0120308000d000004c3c010300542c03146030b10032241f40d501c0500030800c81e8080c00150030b01501c0401070a840c1c4529050400b0544903690 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462918534 1250 462917284 462917303
    0x4060504261e1c080a020a03020405130504120804020f040b01110f06061009060219030924080c04050625060626011104060c0309080105010609080f03030702060c07110a030609 77
    0x8051070031450121008003640c0300c00c544c94640c4070f00c0300001e400072404001403550810002c0341540c1e5007909080000510b60000c6518949894030f401901c1d282821981844415014880165203515144203c8001900d0004084900b940121200c80c0040421046030290020f010140f40f1f0108076644915403e903401c9030040d888040440302c07000070748a40401a001505000341140260300f1046c80c5500914104003159200ca0640302d94803294504c80e901d04d501c40305e44a4499402c0341c02581d00640031060035051504c0c180214808e8480d080c42d00e0b6449500740c00e21402142c1004450104a410034410090075441e00101c030a83c1821078201d440907036885000f00c0b21000d0500444103580c4030200141c4c2058034005054030850340d07120048040c0000c4407800b00302c41000344600d80c000c00c0f031030b90344429481c507000030301e805c01141c40caa01080b90020001c1210050300040c249403c0910000c405690785910700f014030340551924800e80d88012a828004140b004030f81201c04002e00440100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462919784 1250 462918534 462918553
    0xc041508071403030702090c090405070e040b0117060d14030d060503250b03040201020109050d020c04150b0f070f05010c0203030f13030806091504021908090304060504261e 76
    0x1120b04801d0549a40c59403041188100501300048030540102a0108050801021a00280546000310381c501c2c00039860607009089807625004004400e0001c0c2420044007200301e00d2008510350040013540a44004150503042141080700000070045403800e4944602640440781d01a00c0d01c0e00c2000c1c400c3c400d0000f500c0442030004d481508540b2484800080285844407441350750704001c00c1a810340d5a100040c0005c200305015401c1450181c0c3c0c06448201f07000f004010031500c3c8581f8131002040701d4070301800395801d410101c0e0000c0303041d4550310741c40341c007507140940400e45040c1c8010f20f25400c0c8406405d805800102550140307002c14103054050707840081c440b0005404071406400600800c0124246040504c003080d080051403001150b51564500890107a0780044200c0040407040c69a682000c0d80c000c51481d0407400c2c48000c0e5141c1458100300030035500450144030380d0340700303010300101d0201c0c0031f03a000303d04201004c03080c1c407069011400030911442c1040300d401b101d1b020b0b0351090f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462921034 1250 462919784 462919799
    0x8070c080c0a02360c1b07050a0f180b030109140102040303080f0609040f020f1203040305010609020c031b15010303030221070c060f06030f0b010602010f1503020609030c04150807 79
    0x2849a9286a940d2004528042c2180800360380002d405803048540401003001e845088100b91b0a003011751034002c0444619100a00400406a500001005406200900014040207003d0180b0102d4900203d429000000002d006007645c480044c2603c0414103408422913064005d841207034003a40712010641d90700083c0e01d41c2c22a044580e65444010680000c000462000c0d4030b230005400070300805201a103440204010190702141d1581036400840c00300704100007409001c002e04050b00056040c05010000296280910490460301041801c3c81008500f4100425400e4500c01070040d051541c2d41e08001d0300030b50000c500e107122105c0d1400c21300382800111407818043c01540d030340d42010800300c1c0c1710000100f203980307000601c0a45800e40000440d501d01c2c03400803018060101d520343c9514001c5c0c040d08680042c40d100c0d00a07030a14014220349102504d511046940556105aa80e10914002070800380074540b21030b44240750030100380c03d517001c05440c2005e0b10101c00413070360459100d00da03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462922284 1250 462921034 462921079
    0xd110904141002070209010302090a0e070f0e101203050c030d0212091006180908070606060e10020a020d080307110d02010b0a050607080702041812020c270708070c080c0a02 76
    0x4c010307400040e404010001820003400b201d510450310320b000035404003043d5019050030016885403400d4224040c040c842e100b19181120b03008921800049006031414940050b1100300c101e02a05120380407a980c00a28401e10403900c6c60761141c1c204641d9139615001c000141078060310100c038148240c1c4107101c0105940e10424094490f03e01302e0160790003004403600301410b400d134801c81d11140140300c0d560010703030940101c03c094841c0d41c4428007112088010f1101010810740d5010440d8400c0e19250090b0f11158412007440ba00030200594035914544103070741040035052200d803e03101c0e02040c1c0c00c1301275065100921840d0101e4084803442e699030300b0010341e40550b140107040b21000300014401490560311121840ea00c00e848445a110703940c95900120b00907604800140e0030100c0d0082481ca040d040480700c8980c0001403250b080100d800042c5800b80062000d0b0910922001040c01a401100e1040c1c0d0700740d00c04034003503503056085c4203e521100e80e100102d000c0d018624001005000c00030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462923534 1250 462922284 462922297
    0x608191401181112010317040f0e1017060f10080601050d021909020408060105091302040506150f0c0106060915030213030605040b060906090601020c0d110904141002 73
    0x10219803107900b0b129482d0400708612505102c9903580341c02d05240b82c18000050156400103444014140d0f16509011071f50003c142c0c0f0544120720100014006030415102045c10382d241c0d0742e40741c6103954480004403280c1c0b4160b000783e0903071401365a0320409440300083c058411000c0d040d542a0b60340300d00307482c0d440441d00380c06541c030b09030401d0700144024105910303240100c0b40003c1c442410854000c1e402005142c581e0060840301d500014203001e4140100f003c1e42c010603050318075090030b20b00406821102c1c0e4074418024401c90700c030740204031503594405c04c00c5a405c03070381c80040e6902d402c1c01d6020308056000c0400c0740c0055090101c0003035124000c0728604201d0304c0c034a100c01a1040700007001c0f0020b602a15012040011803803002c80131810702d202d414407945c45100c41c40c40c0c500349142044002c0500510591007110750400300300c0e241c1d83c00f00b403048040c101602d1070060202c04e490014111b08940300d10b60740200c090760401c0184031202407010305c0c02d900700f030a6407020344110038410103a10880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462924784 1250 462923534 462923561
    0x712050c0c090910020a0903030e03120a030902030705130b0f15040b07060219110105100506041412030c01051f0b0304081602030a06020c07061e050c0a0507060819 72
    0x500ca092414540300301680440c1d0003007070303421400130700003144101d1300301000d030000040e900c0409008040e0010505040340c40103c00400901008541070362542c49030301c101d401015103502000085407000c0110f1009488000c0c2185841c00740c00304c0d150001d00700200003500c55080740d1500b600906200c500c0040c1c00140d000c1030392506080c1125a074a5a00111003110030300d6080105c5052030810051450103100c2940e50b1042846003480e2040c03d4030405001c0107149a1389034420045650382038202c508440b2000d0000071030709000e10014010006161007140d41d80070008045a52080650045109184041c0c00f1120110104180102040c00b4020120006020030104e00483d4861024200400700040700420500055010905100003000100c1d0301070340204000b144a00b052100c6030140c0018036005100f459000ca450103030f51840340058040c0036002170b2141c1401d00610504a16a4200e8200e80d440c50b40c5250081000004580d10f0320740301746510021498603a140500130240c4c00703c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462926034 1250 462924784 462924793
    0x12090203030703032315040e010b030c121908091206010b120406061508040b1609030611070b090f01050c0c0309010e1212030f06010e010203041a04030213020712050c 73
    0x2243e409800900c1c25443c15010950111044901c0700e64a040e00c1c0d01ca90128600032154201c1c4006002c00ea40c2544030b20049030741890021991354400080302c200c041021500381d44441110841c45040640b10449082c01c103603444903d00501c080d680c0100040c00095648094102c0c15401d001c1e2500d10a0144400440040214868102c082010b032038005000c1d0300e0016505560b14900c0801a1600d440070780800c003420b081106100150000d103501c07101d40754400003400030b2084c00400c5d4101502004051a544030342c00071800740c8400a4440703141e400840e0401d45d04010441c15130b9050503c2d2140c0c0290300740000102690440c50a6602000b0350a0095042c8041d20006480c150034a00d071080d0050039165001105660070010429054440f01095580b420303c2084856003072802041241400f0500705002100e0760700200300d50407580c610306400d00910b00000100340324070440c2c5c400396020000c2c21018840810590007404c980b8810400c58070456510034090b01d441c0601020301541c1d810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462927284 1250 462926034 462926047
    0x120a0503070c1b14011e210e0a08180a051c032307030305090319140c010f060e100f0b0702010201020d090b0f070206040b06060a0c020d03030b011209020303 69
    0x10070341a9440d5200f600e5520710003c002030050030303108072940841c0036240c43c20f5000c1007a5030800807400901090011200000d9030501d4090584803402954203414219400b6255846201d540180d403244401e600351b948804003410158100e41100d800010301441c0340b030004641e4075199500b04111078000d0810801c03103a0307154800c80001801c980640a01002115a120740c080c0d0711045415198501c0059440780700d13a0a005081b038000920540003032340100150f0b072152040a4004040f61018600310f08150700c45e42d2407107580d00840c03032070006a40c245281290480910740059007601c00100e08101030340d85203802e40040c00510301c511100d121040300144050b1494030002c181a50040c000546004c002650000403240c1c1c400c4207036072428501d004d1182d079000c5401581d410140500c010249410300340c032000c90001010341040d2140d8000502034080741d000e88100c01811750010060071280c0700c581006006031904001c3c190005103600c4804942a03494400c0004a51300030307004605001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462928534 1250 462927284 462927287
    0x108010c080a0f020d0501030b10050103050411091812030414010903120f021b0105010302040c020d0509040b0a0521010606020f03120a0612060218060415320c120a050307 75
    0x3c114101d401c5640e001c020341c0e42480010b010f040c0c0210700c201d4411800e4a04a900b00d540300f010b54120381e04160404083c040071030103151302c00407222000c850b00d40030341d100c190040e40503405845003405103000e0056140103240840010310b06c12401075459440e00741140e10304500300e501c0750384010301081190400420807001039000388054844480c006123040b0b030240b00340a84084101c003076281691242d0042c0118145402200c855200d18001411800240c4c000038015004101550340240d0303840c07201c0c404c1e943e200c8e001040200707005042d1038081113150402da440540c0c0707d404044150b00f0003070002610303440061207420300300a40001d14240408402c14070740342c80d00600148485911203801144800342e0007079402030244650f000594550000a8032540800703c04902441000d0078030080080050810503516a000189401c100c80708803022190350055008000c10340442403060f440c42d08002a100030219107020000326119291140d480c801e0610420b112400000c20a0000c102c0c0326 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462929784 1250 462928534 462928541
    0x51005040305090d210e01141602040f0c0f050c15100807060906090531240e1303020c060c072313061511010b0306011502060108010c080a 61
    0xe00c40c0ca005460100d41c0b400007007244c004d618090742d1070710348001c102d0025469200901040f190314246021200045400603000a86550980c3d0007071800003a800102d090750300c3e0400f007643e8002d1040204d18040403a010080440b02302c80700c0442d002440c1c800802d405001582c00100004000384000e0004400300741c1d809501600003250002404000300c0c08520910800000d002c03690384110740e043c41d10000404002e265401035000705c209036221031280d03e0034141104088148040e0554100100c8042002054102041c01140700180c1c640c400310031401c62000210703a8601012059502c651090907000c00d803100c00200960700081010b1030034181140030780324100c0e0110540f41556130324250b0b004000c00300703008148071000e1410080d01c80e240112100446c90041c42041021506290700d07115908211b21141041c41080250351072000c00035005030f10200c80c007809032441940e403200c206540d0300103510b5440141c0038030400403583c404148540c08090801e41d82303021054a07201201c5005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462931034 1250 462929784 462929791
    0x3090213241509140a171f0c1112030109110c030f04050909010b300a0f021011060105101115060a09020702010c02060d0612060c1b051005 61
    0x916a00060003510705041c407001002080c481400024410a4400061031410603803c900c4d03890300e6032a03030481940c031844d0360f80c000d0751002d4000345108040080a14600205d0000040301034114007856000807246410101c000182619120702c0c502801070129100c0c1000800c4643c105010f100410010f0f01c1034200c1c03072441071006482881e081d40d01d5481c0741145d000e1450041910b1300080c0400041c107003500700c0c81c2c0c44501c1a00811040c4450780010710b18084143c00303840264844e03140c00500310151524000d140180794125203a10480c0d00e80070900e400702100583c800e00d40383d4203405d010750040300254040d503401400f91510303078200410000100480e003c00410040c0b002808107050b0010002c10059041c142d100501c2483c00700c1c00c00c180d080c010f4202402417801400300c1c3c80140d800a001c020a2039049400d42c0d02c03103849480e4130700100300c1c0d68080d0001c81d1500c4044000e211080d403019200c11410358803078600e241d144c0402986940304040081a41d40080040000d0944550000d42c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462932284 1250 462931034 462931061
    0x3180d0204090f0f1e210306050a03031110020301080d1b0602030906040b36010b0306010e04060b1009030201030b0a0510050c010f06060203031803070b04111003090213 74
    0x4140006883d881c64401c0c240f00c08548080000060105000c0709207914402c0c0d03480e240760b10640f08102d540d001740c07200f00da1030701c5900004801281c1140900982004001d450040e04401a4940c0c90400400c0011088042c2040d40181101c00401404034000c681c16190700742c00900701070051140c100e40d0303a0041c0d0340317024904011940990004080b80029800b4074502c400038007480c20315080034146284003070801c0c00301000e07041010001c2000003903608526510207240c851014444414180034107140c0c0380b0180d042c0901000460101811010b450085004880070405c5412400901240e902031001400100307107403c504000645c403035040707042d4030309002d041d10365170554400c080380190520303800f4000440e2021803000760140d400d109a01d4940910300090054a1412501039107030b00c40079028424140c000203161000c00000c00c112034031390b5404414a00540b52504104030b2a100100f180c07403283e000702480da00ca880c424020303500c0082c0c006004105280328550500300070319554a003401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462933534 1250 462932284 462932291
    0x3050d0204031505010e06041406040b0f090106032f031311040e031806040e0f09030c0d1d010c05060109021605060a0905210d0c0302091002070e0903180d0204 70
    0x200043c800d00c2007900c0d4515189001c9059410500c607002c40c1030f0700902e001d000340d24101071288011010160107030014429240042e140b10408085035024005904107900303c0000e20000a8059140e8030520701c1c20700010b00b101c180614043c1c43d000403000d00c1054021100188041102000040b4284220030700c294030102d81030036101c0c00308050f41d0b1200a10360a9800104040d10706646030310007441805001c86565203482d040100103010a600600081900d42d914400103503c0501002100d420a4401c0115150003101d074500070f2418070b03112000228070751105104052540659141100703e5400781c0a041207078209850b020007900003000300440f00c0c18815036a0080b034818013655015034680c40001c10b18020310b0402d117180088012518446100c0078a00100102c140415241301208440e00850141d14004003100680608400360ba0b002d18040411180150001145002c440122241403220307514029000e40303d018404003500c080840748013219407407030540c00e484441d610041000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462934784 1250 462933534 462933539
    0x30c0318031b0501020606181302010507020306090703020a1a180307211a070c030c11040507050c060a0509030a0c02060f041d010f031205070212060a150e100303050d0204 75
    0x10211065807609224030b08044000500107941e041c01440e40c082d501351608600307080003180340554043c0c02041015082c551406481c00c6a100300219a031850b001400c0f40e415041001c440c90b01c60550f44822481500c59820010781c00d08101c000494581c1c41442c11800c01c030b0703141c201c1003150380d82c0c100d00ca525001b00f00f404036401c0d02c1601440480e00c042c009915003081c0c18500601c01100709643c0d265522044410014041d5012050130130540d07151400f56854076171850f110f07000070f81c0800010341c050304007030800081543c40380181c418012008100c4015488000105003124001d84104c500c5400c1041100303880e03409a0a04141c075440517001d03e2030f0a2141101c00610b40090304200020740d1010310722100080c400f0410340c09400c083d0041b80c100c41c55030b40c40c214040c6000f086074092120100d0420700f55540c80009880c0d0740c0380071080d0351003480c003004490000d041491038007084444440d00072070642e00b80d6058500c16018503407803003546801c58600362020782004002c80c842a8007044003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462936034 1250 462934784 462934793
    0xb0f120c0a06031d070305060c16083004201801080a020111070503150a2a120603050316051002160b0a021c0b0f0303270904030c031803 60
    0x81030000c2030b09907400569070006015640405220381003c80a0340d0100c44144040b030400710351250440190320482e590340754110207200290740301c40c2e40500f07403a0307010440c2030103881e0100f00c120002814103507044e041b00207440c021107080415180905500303a091085001503040c00030303004542100902040361040d0b455007112890b40f00744c00542ca540c020344654811960407903068400d00c070030300f03026060160070b0001203583c0d01d0081f000305014210b400c2c0450890285e030b60000b0746184400707903000031010400312960610403d6044031400030718450401981c05500b4441c81e402e480d800405185072200300e0400c401e03824411542655180516003084030310715214401080c1140501b010583c1d805014240307600302040092601403d0b83c010804154003c0d4410300071308078014101000174902544034081442c24200c41241781d0140700010302003240070031021040051886130348070168818459070522100b25410385004004c03d100b00b560f031000a015801540142c0301640b03a91225655a0b1076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462937284 1250 462936034 462936049
    0x9020d06061703030c0d0c050c03120601080a020406050405060703050c0f0c090703020414010c080405190305010e0d0c060b04090b04060509060105010906020c090c1201031b06030b0f120c 82
    0x444400341e5580c420008040c2210b10040d1800c1010701031811490000c0b0a007419100e489460151603503150782c0508114001c0c4140c6030b0340500d43c4105c82c2c640d501c1511081d10b1007005d031542404150044005164681e040c021a416588143ea8050a1a1810007400000e410851b41142840020b00040054910811002e041540c1d903400811100035110280140383e030b000340c001010980104400d01240714003d0629000d80e00c00c3c82c00b440000514188081c40d8051a00718590003400c2e94400444240c1004011003038038001c40082011000d4859616610f5045441410200340c000740c0410114146ea40000860f034405800402c620001c0d69441c2c004180444049403002d5841091000c02030040006601411003800d0400d132041c01c011011b035840303004213011842091102d001031001d0308071070117035058a6150410b0a00a584928259500c80940c9049196004042100041c6648039000328215044042c0411521201c050b0510100a200ba10900031a10524100758899105c004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462938534 1250 462937284 462937309
    0x403081b062a030423120d02130e040c05130207051014162c0a0f03150b06040504050702150c0a030c05190806030708010207050c1017010303030f0902 66
    0x41c40300ea42c160b450703145110b031500c80120280000c0001d008110000d80c52100a4402003422041c000c80407120001c0c1034981030300c030071040020002c042010040c000070358010f8540740841e80c803001c00254440640c11490769003102e02520040002904002900b0000c4043d03102d001c0b42d4030003614000d4242c0364280b629842c207121071020340d07070781d80c11581140200c81030642103000340035591202450301e1002040e0721440403120b0107440d100780b40d150321140894031071801e950000d40004860b6986050201700c3d010b00b07110a0b15480e034154142c4603046114401c40d1300c9128001e03c0a401d2030f082106003c01008010101d27020351041386c5184040304011242284102120801c603a902c032690070008003a101c00c1c0070a00103000007444a10f00e09840742c02542c000c11503524040c0700c203607030311000645080c10700d41c07012a8551001a4840c00d211001c03c070a445588151803ca2600711030702811101c0c1e5552001daa0403200400005100203482070704900004600b1140c0880c480420b80c00240e206c180a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462939784 1250 462938534 462938551
    0x2001090905040b0a1d06061e0d1b061704030f0c02030105130203010b1813021c080a1403250201020d0e070806011508150117010b090909030c030403081b06 68
    0x510402064401e00e01030504001c202030f8404002e04170414031a40d5405024202a02c2030000d08c008500c40008072080e280302a100518000c0001920b09140340d000d05c8111624070150721100010420a018824201c400c00c000c0f20808165039464508841443c0308400c80010800001462405a5024015907000d00c40d419034841110500b48101421900711000482c021074100b04910744295000c10920b0713019403551908600c624040c80047c3e844140040325070300e40803409014034107100850b800f42491b0090742d10340e280680e49003840b500c5107000485540081c00d00a2907002090481c800c9051024401030001600745101e40141600382c5600d0142c42080780e000260400401d42c08012803401091068028040c5c0d803c5060002d1840b0f4009015404007880244a00d04a91095410105e070860030030103540f041d40c40b042045800d5000d038107a01c1c880e05800c0c0105a00c550040211440321032000001c41c41c00b40356660f60355694014a0003080d00c04422a40c903035142400340020391152140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462941034 1250 462939784 462939803
    0xd0e04140118061413091a010303020303072c1201061a0c0c2b0f15060303080946080c061f06050c030706090308070e0d200109090504 59
    0x10001c42c60100d649903400700080013445000c18100e40c03520480686420101840422003200b54208808407107004030745030000c144d602d17000005040d8080080c41c0907141c02d50300c00076911001543c0510048150310301e0040711000c0f242913030345881c03e54040d021840001001146490340c0d04441000c800e00344030240100b520004480f82444403d0000a1907a03004407071581031704903d501c0ca8541c01410300665403040c3e542c0c180d144140a040c20100031034917844640d00620765040081080035160314032003103000c2088600443c10b41c3c403000c00c840312070aa0008420001e11049481a6040034ac9081c504140c1030000340c03807143d28000c1e0000f00020500920715a641c540303030404c080d03182c440000c224941d01400e28020b00d000028650496049808600e001d60b19640034040550840c0b00700c081c01896145000d003404100760300901c0d0244502d082c0e4461114803407842c1c003481000700025400801d46806126905282c20705191030100c140303070624000701d2041c0c0722a0380800320781090703400b6030b0700024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462942284 1250 462941034 462941069
    0xd0803010906081209010e0604090606090f06030902090601031a06031311031b100e120a03021c0801091d0d020f0c010c020d030c02151315080601020d0e041401 70
    0x80318015a4010481c4600a081352940694a5410740c01052111810400000044c1c140c50b5120400d66016001c0c2c000304001d43c640c0d40d0000ba00300300032481606000ca440c1000010782d070303010384228640660060801c0400d036452000440040400c2074050f0f201c10240f151040c001d03158a0042c0d40702350002081c01c5c0e02884141000c9002003600d60307845100703511505404203214040e090302d8169078401d696005c002c0e44c000c441903c038540c12600ca29004544070900d020b850000007040c08003240213070240ca100075000c2e02111035100c03040e0b00480100e82941d00404c1984919800039440c3d81a1202091649010385001414000d0080300d00e070060348401e000b400b04540512200d0403002007420001c035071040c103502040c00508071407000703010b22280030154425501c03192a8980d19800c1d441580365a01280d03482d030444d5800f240103019405401d44207450301c4900407403007180520f00503002004640800e02d8100c44600103c070003641c0041e262000740c900015502201801b80c401602e40b0754017084e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462943534 1250 462942284 462942299
    0xc0b1506041a0903071406190905040f02190f1d0d230601140a030b100f08010e070902040f0b18090f071106011811040f0305161a0a03020c0c0d080301 66
    0x902c1504000610981c00301030300b0055649000301e030241c40c00f045071014514448e140944038200706607c8580c0190500c4800c191241041d40200700051410300030b0303040d9401c5200c04a800241c2e0034032001c00b0424104680c1c000362445d0150460209009002014076500c0e60360394000c480b04011110b02040b031240280d54980302c2070000c00d01402082d100301c04080041c5e800188030002e548000b421710030190740480c02002030f0341c88046c050001c101e40d880d2075507951050a80241606902294075000d000800300e0311071000d000f02e40c100c0d0100c0020f14241c6041031a11182644407420344800302c011044c87e0281901c84080c880d100d6054102c5156681c503111002a00300a4400c0b00b0503201d070425401440200103403000065a611000b03000103d000c40100c04c04d01c41d110b1038115029404e030040e000000c001000882c00c143c0d100c2e03210025030b4244e44000d40308107803035800c904880000c0280003010406229a01070000c3c51a910704441301c01072808041180c28224203403d54040c00300200600002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462944784 1250 462943534 462943543
    0x1404030218040b0108030702060a2d050a0e03060103020d03080c0d0e0a03120c1709030408010f0b0406060203040f0510051209010b0108091908030406110a050c0d0c0b1506041a0903 79
    0x1003405170041d610313114107075001909920850511006010040c02061a811208801e01903103248142110348214480344002d001508809001000074059000154403030030041505c83c1260390103819000d9404550340c2c01e40f44540001d1408102e05018441841c01550a02910709507070003000c00380c0880c0038141802000c0801401b1402c1e1050300b402c03182040c0d1a800f00600040112048014610751110b281e458198801c6500c094220347c00c226107a02d004080380e009e040410b5044904004544c0d8079903050b6107074000c5204180a418810608101c142862584030b094103005190940c0341020f1510394004c5100142d0f07160240303a555147c00c000b6940c010b00442d800984042c014402d0030402030401404402e924801400285d0110200301006882e400c04120364a01da4003058503444105030080240d0821002c000c41d520031100da01510900880306400d1045d085100072a10381d9403012200c480340f060041c1c2c51b0300140b00b00310001f4000e00d5100310500311403400d40179603a02d00d2050105841d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462946034 1250 462944784 462944789
    0x1b0c030f0705060f0705180307121505070e03100c050910030f140c09010e0f1f090b070803060d14010501060504051306060207150e0d0b072d1404030218040b01 70
    0x7803040201800184c0b44c011b02503401114899401c0c0c0504c030310031404030b800c05800354040010400c0c1c1451080400c0780c40b510010443d504894108559940e500c0221407400c0d0110f540c5825401c0030358041500701d03a0f600100100c02c0031781080c61610007008003040e003440b00200900c00180c3c0e510341102c00b004050069003200150104480107034182202e80807401e1142503400f6040c02217500071070b0b445131150a11803401c0c1d0f1008140101d148000c3c5800110203010007103c4000900440020811940100c146d40e1040e0b04811000d00316514041031102026000c5002d4071800b6000c3d01c005501d50007401031034003800541d5a00703038075140703803c0a009905599a40141002e81000790130704c41690f000031817501301c51101000d00500f4018a80507640780904040098009040803245c030280003c4094503400740d92182d13603035a04403c803036007a105141501c3c14480400c40a1142d42c003800c0344a00c0c085000350b00070f400600d06d8036989a002071070100c683c100750803e010303c8404000c180020070109500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462947284 1250 462946034 462946051
    0x6080606040c050a030e010932150a181506082a041503050d030c0807030b0a1e08060a0504030912080f0f1b0610050114031b0c030f070506 61
    0x11042c6200a04075000340d511800c10556a1440d46802d0407007500141c00264100300c0c04c0c0010480740a24541e0031070400707505d620310341140c00b148000b030708002641c0301c0d00c96900d900c648190301c4100d03125001c1e02d02c0c44100e500310b000c0031100b103012071100d1021103c004030203903000948614080380e65013070880f91070716414689200c1e003504a402650280500e0502412540010300040d0f0f10190100282c8230340001e00a07102c1c014901041c55010383c40f01244840907281c0080994810714100c060324520f018091700851001010030060000452140d01d001103040031800e200e4131140c0340d0340f03420342c1101c0f0f034040280c0382ea0a001c1031541000351000a0240403e41d107100c00c0b00307030b141d0205521a1840c449035a001c00140031103246a0300c03094031030030209031110a074034515a0180e6551500d0588182000314118440081c1c5580034600141c0400c5054003003604560300c9080034089031081c0b090880c00c04a00f0042d181e00e40005000500e81c08443c000401d0720746109040c0680303000d2000340040c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462948534 1250 462947284 462947291
    0x31b0e1503030712020a0c0e040201080f090a02010804060f1a120f0706050306040219020109150b010e010302090a030215040e0717010b1b16081203011406130302130608060604 77
    0x350544012040743d200c540c014404021500c5074450480c503003424140003800740b43c020400030401d13514050f4914040c0d03000744c0c4d5203403060300c502c04400d01e07040050700e51120700d602203040d01e00194094040700d82e0082c0502c0c4000b642494840840013520445d80d0b4407030082ca55000140034034500034281d02d000315603000091034107410005049943e91214007544003400404030000e01180c0d5550100da80080304000200300200c1c0c00d00c8045d020340b11880c01151004040b8019070185215882045c4129405946041105401c040150020342c050380f10150490418200400540c440c05640b4151101c00d810b0b15030f40343d00d003448520f60390f240034059130104241080b005603100c0c071050200b41522907902c4101d55401201450012000b01c8001c800200d0042440707a507011900c48031444104c0b140d00003a560300195070307505c2070207510007401541141142021181d079981842c0026104a01c42e140300c0d03c90301d60300c98000984810350740b6016403102e61144010b101c40c0400b8003c0c80c1c0c120304140c4050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462949640 1106 462948534 462948571
    0x109061a03060708180d08092a0d0206090901150807020106030308040221010f02131406040905040510020706150501030e062d0c070605090316080a09031b0e 69
    0x134546000c3c191403014920381490807921141c41d03207800a540b91004270104100b01d5003007030303090382c0100040c4043c5009840c1d80741080c1c0a807840f0400e81651000a1800800328400240840d0440e410100e040000036040f0f9140c540159040711391408002480c03500500c428110f40300b0640e59820890305001e5120182e00400341c032000e070a104495161a031348405a060ba00301c46042d04660200003c124045480c0d1045400c94400c03025903d8404180e0081030507038020020a0350b034107a4903803d60040c28200d4800d80c000700002e0909200901b87c01e14142e485143c010700f003e90003015114084800f41c111314100d028000350a00035240307810900240961900410412584c1c1761602c0c0100c2c0c41d5100001c02e81d51520300c5941c03103211600b03244c0c2d92810b060700180001410310a00304408000031b4400b4183c924943c44204150001c1440c12051256400001e0800c540d12074041d11030 = true := by decide +kernel

theorem cover : BRFrame.Cov 462769784 462949640 := by
  have h0 := BRFrame.cov_init 462769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462769784 ≤ n) (h2 : n < 462949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
