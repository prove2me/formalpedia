-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:38.846369+00:00
-- url     : https://prove2.me/submissions/ec601f74-9d38-45ac-b1a5-fe1bb5b3b006

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721582733 ≤ n < 721762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721583983 1250 721582733 721582759
    0x1c0f110f060a05060a17120f070605010611210304020d141207030f0c0c050f01050408011a01030c0906140d091a2d040204111201120b0133030b 63
    0x406008100c513154000d06800a00142c0b1880d002c40c079010310324420340500a040040008111694000c001c9140d01110038013948000c0b0f001486101c0c024030707581d10340e80014458215110b0801624800e02110040700d5a02919520102421203511a60403a4045002c40040c40e02482d42080d2200f11003da10030420400036038000c6100620074540291030701100100c21181c00c0340d06440401d4000c1c0f035401035000c104500d00b000c1c880b44101140504000d800e080c3c4031030609003164480240f0000c030000420007200c495806110706942da902c10f103841b05869017000405006080d4405900e000d810700000e000c40d60341d400364001c43c2055485007028400280840d070070060b2400c107503414140b50780030715074044040d01080b0351200d13049540d0700755020503501c5408000090040111010111000f080030f840d90001840103d0702800000031400c441c81010b062448282c07005800c81c0c4025213409900c5040ca14045031080ca0a40140300d070403000000700c3d81c00701c000d010066000d40d00945600d0000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721585233 1250 721583983 721584001
    0x13110c0a0c030b0a0e0307030e060409021315030b2119050a030e04180602070602040e010f06030e1204030b040507031203320c03100b040603020304051c0f110f06 71
    0x204040b203000c0d030795500c00c0740c4490344007208842c0c401c0b2000100d82c1c001c001e2000045d00914034110071403070041003203080940d10014a0180e902060340042c1e4824580307810300580800c2408030304200903d245c200060780b51840882c003144840c0c030a2004c10f04106200304003520342044000b0f42a00d2240035001100030501e003c60b41c0d440303151001c40200d05084240101e0303082a21815607c103401c1a00c800803d09261101c50096214010a440e0341c0d408100100b060f0300703042c46d401d00a00c0001c401c0c005407803a002006048601802c03001c0340710341012600b112414041c0059030b050b00d8005180740c110361101d00c1d010749807100f66071004182e2050001c884020030f800d5031100c04c84e08074110802410300d068644242c0103440a04400000f03d500c0e0300400c04001118000c2c6034010b2001e1541c01849856110000b181d410560005000076000010042001018004803414001144100043c1f1310b140c40c0180c071429a01401e04c0402c111270500082e181000c10101031907842a82c11744815090080c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721586483 1250 721585233 721585253
    0x304030605070f0c0308012306220b1206150d0c020d1413140a080109050303060a06300b06030a050405160608072615040e07030213110c0a 61
    0x2081c0c08110584a094103590081d1340c01c02d00c0c5030b03142d0707103c40c1c50b42e08050340c002c1401d4035064003404410300030034072084548030100101100c00b450240701c10b040c41c3c0c04031080403c4e2025003098030202e82c00d01031449100524143c0c0d503040041161400c240c0800e0481c0c0381245d00526510800903400c040700c0300c5a2030703008152004500286e50340c02550002c1c0e80c3c00d1620500c81ca01700d104000045030410081916800c0e4411401c0400030801414030baa60718003542940c00c107030030603113a58100200b4003025141c0051900d0050040d402c18403094428104100c0ca48941407014542d802c01890b1201040b00d8a640000004140100710a03203a04102900d48001d0008540031100b40c894078469205296a4070800e1046500d00c0d60740c1115690b0342c2d4400c403800004c440140c0103c2c00b0300e034440030f40c5503844e43c402441000a210203081da00329603403c10083d100300608000c17043d004844e0a201680301d02c07024486001c00800c2c0030603608540702030f8503e1440b4048000c14039004001c2c004040006c4d0b005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721587733 1250 721586483 721586491
    0x203010c08010e1302010e0f24040e011401020a0213020d1a0f0402090907030c091502010f05060a080709050402120d02030a02060a14151518010210020406090e180304030605 76
    0x45030000c070703903524412a03440c4c0e1080e042c042e02203600c3c0a026045403400f01c1c1d4004202ca00681006041c040029124041c2043d0055400901c3c002142c14025a05851441c90040c88110120002c00c80d000d800030b51070754020303031020f030256001120101200e26141c04491120320101c0c401c00c41c07011801c3c0400301e01c10002c84a01d103e0554494100c80320318060083e108000c03001803048055840e000030070740003800a100701c2d505111003c100000c515440010172040d2000d5900081440748010102d0300032180c3c020300a80c824440030401703210f44000040c80d038050b1200b0010005207a00d075400050082c9907052911860740c852202d100740340d03e5010002c1d04c000202a002c440c40c907200d40a07038a040da104440d04840e000c07001c20001d8044111011107589080010f410740c03050306000740d0307a19400d80c801056100101c9040040c608903513410040c0c1d8203410030388a8110300b05800c0c000000d040c03014521401200d060000c0100d204c04007160205808002c010040320754032941d0b032826a010b04801c0b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721588983 1250 721587733 721587749
    0x1605150c0901020f0a0803060d0312093816020c150a02150f0415091b18091a0702070906030302010b0117130311071e0305070602031e160203010c0801 66
    0xc41ca13104001040300140342e2041003a0304550782c03203090240d100b40018003601040b500220381c40d210102c0b0301c503100d00d96005801e803540e040c8100c08002c00300c00c0b001071038035000a00004000c10b01d1241480c4683c001000c180c02186102203c5400c074030f4040c4602800c0d500c00f52000442d00005c0c1440c00520405800d602580c2612440204240c489101180e00d00342c0e40680000040000709080c1000b601c1103a68400060200c6481e00d8920300360800c2108000740d00740e0300c003042c410200011000702c810005120140590000c59070751740c400782c000540c0c076100b03511400d0100c2e00e414028452100a445c29803c01c03c10141e807410002c1c0603118082d11180890801054a84400f000d004814460b20024000030b8442c1000e54040b1a00c2d65049009880307400781080100319000c6c5c0d2921201048030400c0783c030080c10700f9401e00b68100021544a4030a550041004400e68040310001480030604219107580f50300b04042d500c58001d500400082d07055190010001d2050b8000704140e05031060f40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721590233 1250 721588983 721588993
    0x506030a0606080105030a030903060b060d0e0f06060409050c0f24030a0c050703020c0f04110c10050a1b0e130f050403020708061b030a110406020f0d0c081605150c090102 75
    0x45c0d041c980c88a2640c60060000b4510010034030120703a6a402c40103551030046c1c40d1520344012045484120340807001d8280154202e0040540070310301c1001a281c00c41e4040310b041202002c2651201da540b41114003041c001d0010803020521a59011a00360054805400c0d5066a41080070503002a030320813105488d40a252031200c0c81624401d500f600d41c0c842d4590024522805244100310fa03540842a00c19400b50f11007405c5984680000090420310100b40028094840d40000940035200000c0c4012031107843c11401c2003041040d01c20000c2c081c141070030448202180500807035800c40d0341d070031071400301d03400e01d00f840e001c00009902481c42240240e0944018503212070001e900c0700c2c020340701201e12001a440f0850807044090066401627030b58440054074001411036402c2d036411903071218000d40c2001c0c10442c0e20708028810880712168030704d0401445591a1f6643d61a4000c400c011201c1420416076402041000c003c210340c0180d40300001c0c16946020b131035410895000d0003172140103000e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721591483 1250 721590233 721590239
    0x30604030c120c1a060301060b0a0306060306090e0d0f020c03010219080601210f0f05070e13050f0f060d0c080618160504090503120106090e090a02010f08100506030a06060801 77
    0x201e0034802d0308240d4441c0700f0b10050f08402c9004d03842c440c0050040da0380345d542c0d01000100150004010400d00e01c0366100031070014a4098003600f250030981c0700a01007400d002c0c0240c8081004580722064a102c1c0c01d00000000201d10120b02e00181b01c6400740d0598400515100c48411900b80340800042a5481d202950b4600004407041603405003000840e5510f1444284403080e160400e0a502c5605840041c100102c941350a00740c1d4000e80b2047d0205030415101c2c882414003840100d050b007028030043c003042c03c0040c80324510800040c40351045c150007001240c140d688206d14400303211f8101d0078081e612507c51070843c0d100d11095500801514100c641c1040e0100d01051001e9030034030b5920000c9103d4500411311025142508040382e060104024030b40e8203001101289018000c103aa6007070300780e81811071014101e44080c01d441d086038411143c900040c6c0c1d020b01000600903c9140c492000d072140e000c000803944254101d154044004010098030001c150320503000c440c82d03542c0d0003a040c1d80e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721592733 1250 721591483 721591487
    0x9101b052802010806040c02030f271804080f040504050a060e06240a020a080408010e07060302030f04140717100b0f0a0e07021204062102041d1005030604030c12 71
    0x35a1035402070100301864002451752800e54071800368081e541c0150380c0791240b4031641c49030030f40c00440c403203448a662044070301d01011842d000320500320b01641d80c2070151802e400d0442d00040000c20052405000250182c000200360046c1e50061401500c00c0c083c41c24264014009000b990162290400c82e080005607686403602c050414050628002c1490f01d107032001d005003503441440740009501c03403401c80078000350900000380000c001c80c100024070030610780321031030a1010b10360200e400c040c014400d0060648038400d00c2d0b90800d42c003800d1083c84c074102e540b42030706100d0607500c0512030091417130305080021004248540c451898100030494030300d2a104101d00030780840380a80d0404101c0600380000e0421660345a0050403d00441e14010501c210880e543d6000340c011100040403001215680d071500b804c540c42d0030100b400b0950609042440021030300b0329a00000b0090030600000c240c03940200840603000c0c050150036910070340780a0401801600c3d004608446440e0480703140f5500d14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721593983 1250 721592733 721592803
    0x6020f13030f02040b1f03020904090b1e100f170f010213030b01090c05090603040809100e090f010b180f0901031b0801050912071b090c0f0503060609101b05 69
    0x41850321b202d00d0700401841045000b500502282a0026070750b07003401c404a400d00e061a03203e490303000c0c50052a10710b03200c0c039880c0c0110007030011115107031107660078400c034100244010280c84800106051548a0703a041d585400728001d48032949510024a01e807040240070b07040406daa0048115441301c1c1da071685120704942441101c0c00004030180062402480d20b000210340003805a0900ca0900d07140c1d42c0084c1d000224000c13485d01013400c0d0764950301c6070b040542c00315603c0030b101c1150030703210340c50300d0700d090194440c810340c6140d004100000b2a1441d92113241484d659003000d80004003968403458401c0f100c01e060346030301002c01000300c0001500401400750620504041c4082c1c2003440521035070500c150426401212241c1c00c2d050911a035900302005e0100503c800d40022805000c0800003908810086e50f40004000c002c00404c4015100c0a048921018054904d03000072007555a0840b064101009044140c0608844000138440002201240054a860f0180c130104a8480540c0c00c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721595233 1250 721593983 721594009
    0x61412040b071413030b06010305071403101e0302010212040f1a16030e040b1009120809060708070209060d0b04060510080d0302040314070b03010306020f13030f02040b 74
    0x444598000500090080480a0340260090901d000703106800c034060541c0d50804028440d96410301c42007003003400002c5000d5078000c00c0030f08003002281040c0600030701c5400300308003d800c0e402d40040414210780880c0707201c000500d041c48217840d0203501184115011001d034032013a0300500c210601801d01c20006001c49003201c1038180d407080640d2602c012850384803440d841c009103042d81809076440724140760a03032008161080e582c0502070b20040c4204022103040c02c98082c0074000311000c612701550400402030503030311000151803504006180030b075800d100e01c6038000e4021101007009400c00c0240340280129a01c2241c1e0b449681d55200107104103003072a00b0001e00110b00e80030208021403901d40c4415080144800d80040c803544840305246468040800c141c0025800202001840300d41e601800060101130050511540b91102456040c0018000a000664001101c0c0780c0300201d4030855100e542c048002d105d04a40e04e08107007602c400c08560980c055800e0624110b454a4402c0c130740c81030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721596483 1250 721595233 721595257
    0x1401080f060a09030c06020a032309030901030e0c0d150f1a10020c0405010f210512130e0a0915090c060f02190c0f082b051b03040614 59
    0xa03541d2110b0168014116152054041c040d02c91280307404181e190006200035403050314007091080124204e18540701c4101079001001c030404080c00410075000c0200e031a12a024030b40807a000d880b10800b0303800c0c0540c0c120060b0b40926050521420002405400c0f802140c88003410042105100203220079214410105c0706511001956031443e1b18050b1007006404040384115140c50740c0240100342264000e07003180c40341080f00482084461224411540142029105070003003207840d54400c1d030390324075400c004000104081100007030002ca100d0884000c0400c811030000508014415034014451800e0035140074001c4944039040010380d010702c2800a9001150b80302251815074103c4e104c1d11010304840450007581d44074609030b056100c240745a2400f07001202125460001e001a80c507150703510203185900f0405d000ba0640f4402c1c103807400031440c0340045407070150711000212054070401d50300300c40b148200c0e05003500101001015209440007030700d404101d41c040c0798426020b40941c00c1580c3c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721597733 1250 721596483 721596493
    0x40201080705070b101724060d06090f031e0e090c130305030c1507051e04081e010b0f030703140102131410080408070b281401080f 58
    0x194400ca8000c1d51002081c0351003410880c182d40d6880d842581540c6070750b01004440018420029444a1100914480802807424205180b00c0c6d11210110078802c1d5002d4010000158460710765940c0c0d54030b560b5104a003080b004031b1070314140050018400381540007485506800303044802c41d00c50300c014090f01d901c4119404501c101003140036280100149800b034814004182502040d03030f0440e0203117110300e01850322141c524030740b00e291000350b2481c2c14a10800c9002e2011040d005021510b03d0788504d081e0130401c80c0d03992080a414415035100d56100d10075a480e42d0a00c1d0034641c1c00c0242641c042000f40003a00c405030400c082292440b030142d9040e0011041000007501c40081c1e0240c1100700700001d81001104881c2e080c070328040d6840313034140041d446508000d6181040c15903010250f50300f08003070a824247c548400354040d8030402444000084042101d00c000d040058000010050112000008100d15140909a001c94085d06100c0f60380000c9850070011030700300c0e8040f0b4564001c5c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721598983 1250 721597733 721597741
    0x2090604050408041e090e01050c0304060f18061b23070c0e0f0106020705030304030c03140c0604141507030c20030304060503181c18050a0608010315020c06 69
    0x901d0054403c80380442c00b04400104441040d00d050180320702e03c44100010b92411100c1d9090b110102c8039001c050b454071040108202459041c0ca8015400c840f0008145003801b0805008090b00706565030640700b5441031508001458000d01c1030440000101e90740c0c4400341c41d007502c2d8950b02c803c601200d1065010000442c450a101401c04580200091910b895549000c0b1102900903100c010400d07401800500c011601048480d0042400340c008502d084d01e140c858140134944c1e0b0200800702800752450b0004124208401c1541da00018801d039659640c0e1524007072200130944d003080c040c200e1405403141d40c4404000b51400550180c545201c0380c02035a442c441c0c407107540035852044a030000420003058404102600107040b1940b02d50b55a8181028202000c440e0340a01404a52102c8504400e0a04c070410883d40310f441d905060f00314000010404080458540081e0382040c903c0c240021400ea10012040c122402510510355041d82c201500090340304006c3c00f60043c0c0c1c000d001007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721600233 1250 721598983 721598989
    0x10e0a03080613060b0f070b090706020a08030a0e100b040c0305270a0b0403020d08090a051b0321070605130521070b0f07020709060609090c11150f1003020906 70
    0x1030006403582c3d010014501341c417801d01080303d03002402d040140d4200891030804214280e8016504002c15100030400c139850003000070f54640051100402e0701e140800445c641c40380c10b070050031030a10080d040e6091290385080d01030081c00784166441c800e9040840851840e4007a201d41030042d500400c60041c0e800101d10800c5a0400b01c0c10003030306501c541044031000c28076007484203004038440e5014003205180c180b4003d04082d005001446107030080150400000d82c0001d00c1c25044c0321407032820603d0801000000d00705451440156619205615010355004c1424000c141c241e108801c01c1006442d030030407001340b04800040c001c02c603034004010000f003130034600e9811000303842e4280c21510349251591031590143c4190303540d280082248003407168441d018030032140580f000040400c0942c1c9002001032010659110345584590b0711034040390700d644216111400894044120344005010008404400300c00702c0324000025041c0c004190b1304100048880202c940090260665869040030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721601483 1250 721600233 721600249
    0x3021014130c050307090e160e0601181715090a15020304110a0308090103061a0901030b030f0102030f0117010b090c0a0309140a170702090f0a0f060f0503010e0a030806 74
    0x1520003a0000d03000003511341c0d0030004c0101a050003000850b00103081206145026541200000a000181014811070600c41c01c4503522800c2440e01500090030316441000c0e050540e00644002c0c0714040c280c44010750300150084008080c5040d068040e03845115494685545e448014224400390400b210441541e402841d000350060745a41c1031441040c0014082100507030084071061804a5152120f68062160708014201e41446c10354402205140800c244103142d042c03070500d99200c80e41005501e00300a44403c5c00c2006000319524101a846a0041748091044030380340c1e00e01034440c00391180c06000e02846070101070700c1c10045032503446054901c0d4115000000070142d032500801c000c68080706520510143c80000350542501c54189a844501c14148108904130100041c00c01170302d600409590022640214000944803648084003901518021441060a00b400842e42c1041001d0300f0301211002c8000700501ca011010380c03600c55080d540042e010911250008500e8106120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721602733 1250 721601483 721601521
    0x11042711070b0411100e03010b010921050a0203060a0605150a09140f1306050312090901120311010c080105010e100207090b04020c0604050102072a0504020f0c01050f0403021014 78
    0x1d2005200c590750004170300180004089000083c450649202c0d6a09083c440e1412010080c64511207082c20719005000000101200c1d050078100c40c9174101c24040c1c24040442d009500501752001070034000145400b6040d2401424810101685500c01c10041c960444800b1705958039410f100c5840c0040c0d80c281d42c0280309411350411040300003030000b03581b40c0c5074415510a142c800003607814244802e15203800180a00c0d420350400411203030311280d550084080c111000c148242288900a14084618003241401c080c5103600b043ca040080a40216120741070300d60a03038962849240c1c00080080c103940300e03605d241c00b6822024042c843c2040540000094520240c405480c0502e00035149181c00c00443c4c0681c2c0595010401604114100e011100c00d1460802000040d0091801003281c1410a10801d407081d075000440e4418540d0820a90b0003031061803008008034a042800004c0d60041143c045006001c0c08403031003d07508040c8100d003070708660b60f03003210328650707c1c1881344003100740d889 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721603983 1250 721602733 721602743
    0x6040606111b01090503061e0702030f070209070c0804030609030806181524130b040513051b0c06072d1107030503030c0a0e0a0302010e06090411042711070b04 70
    0x38004219920204047c07401950100c070041001e0102030440501120040c01213002c540040140070b92a0350f0080030749043c56011108607a181c0c540789e0f41a070748a16450402050b6280119000081c000240c1c481c00c185030080e251800141e9a1404005000208400c5030f8411091500407460704c071007503051808039600c05043c0c0007172081d041c000d158095007200d00403440c0c0c1d800090086503007070900500d000200b400c200200d04090503c00010341500c0032000d90042165034400040600725440010b219180c940803120f03a59039462024591260390031074030000460b00e4081804644002220190620400010620900d415041040700d400c42501e03484480c03403041000102c0450401e200a600480504140e10b50700c0c2e142020180101060320b690728420060b1100820240c2d0300b08103007151000e030442d6220307650903502c8005001081c0070080700c0d07501d100104021840c0c1d0180c902014142c4400503207007440e0f10844d0783c11000d4800d0890380780b85201040c401c0500140514980c1c80e0854815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721605233 1250 721603983 721603997
    0xa0203040515091605030a08070312020421052b0e010e0307080601030b07050703080c03091c0504090f02090f09131218080c0f01050c0106050d0b06040606111b01 71
    0x30480c45002c400b910320101c0c0750041950750348110182c8510360002c29003540078000c80782060300c2e4000d0500546001409000021072404c0c1000036030390449020b003240488a1012411030409114400d140d0502140d40d40705585444011080041500a1420001013030340c0128a0840e822210a00c50340300950611224030210710455400b440800090084140200728562450421b00441ca0029020030b01b070000400c0800c02180c1c1c0032500e983e0105d0904501c9a403501c680c01c81c2c03480d00d2145600502011030200c007440103260b005d0300800c11915601002c3c440c4410502c280002c03031007503c4106501160070b81e22020b20341000d500c15a48240100124020714400c0c3d21014060407003051480000b80c40c40d0144440c00d0b943c0a0b5090250080c007000704400c1c1256008180107000c0c0f1810581403000100d0b9010101000750410800b4010150003e0084141854600c440700300980e4068416030074000302003000f61254040319825101d110041842c4101140405c1c0342c4c01078003100034100608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721606483 1250 721605233 721605253
    0xc0c0204020f0c06070807020303040b0714030915100e040f023607110d0e040e100f1103060a030303050606160f03020c030c061215030105012d030b0a02030405 70
    0x4920140c182038284031402e40c1d560000e102c90b1810712100410107002d01c04031b2002d10030290742c000103590340f190b4088500708007612207020035603561200c00301064182c980001007140b44180451007030701d18250041040407544500c41601e6414203e8010001d03030300014800240480e032181074081015002801110045203240034000709080400a1940c001e2180021101e1054006041d154408100e2400d55036680700d01101648070000c00c03004008002c080318000e440c0d581c99078803800c4030207421011903040a00700390042c0c020700341100a00010902d00100d5201c412034040c22684600c030010000015a811a81d080c1c00505014103019040b80d4240540168190300500d81142a40648001d100070302c0a071a00038540100701c09440e0007900f141180b840c5686a22303003a01d040a40c0c078241d0b442036a4607840144561081200e44503890f40c20701000044007440d00854100290044506248681c40802c0e22800ca4020b0700c0300820100780000040d04801d200e502a40c1c0140c032450a03a110303500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721607733 1250 721606483 721606489
    0xc0a080a02041e030b0601050306060306060c12130f080a0506070c06090215031515032d100810020f09040c030e0105100504060f0305060a0903200102040905090606030d030c0c02 78
    0x411040100f01c040440005000b40300400b40400da000e40309181c031600c0c41c0f9000c2e01240d10f41c040a06441c3c0070307075404212005000340070f01040300c00401c43c9010701c1d2074940300300d4103861a804c00d01c12074460855000001c6100034002c2200c0d00c20580002c0180f005807108070302240e000254020546086039210800401a501d18800e17520600480c042c5903200d052680404801180142c211403060824868034a03081d0300003000c1d2640f1517080c1c00e01000340a0044002c20400f03000420380c0a00700700c5a401c105c0280481c200c43e009444680f4200c516111100102c1d4007203208014051f02c00c00d00c18010100e0034905a080140c054016280200e00f012044010342d0135910150344001004091500c01d0103141081d03c10701d4000d210820320160030034650b8440644403c030161415030002d0300d64031420185401003560307a20b00f200c08020f408059482003c424001d400c42e004c0d94800908000c0401c2105600050890082d40c0040c003038100070000309000e40043c0a854625000e1000b0a00d00801580d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721608983 1250 721607733 721607759
    0x110a0c05070e0709050108130b040201030b0411030115110604110d0609141c0201090807140c10080f0f0613090510090302030405030715050f091f05070b06090c0a080a0204 75
    0x1070040d8584d051010300300000548800d00040c41c0c0d400d84000002c001c0c01044040e1f0b0803030740045d02820005145200b680100380a8641d0012182d51100000000964881d0702040d1503440200d80e50394280004018807113039100d2409030741c0540040c00c0301c100304049152802c00c00300074074843c030800905c0c180c40d540c943c88a2000c6480c00110380c3c0011102004120702c0b201d01031140304a5100030003040c4080d07540c4101c00d015441d005800b0b100c14916070401460200311b540346c0d640d0000c0602e400036201c040c008000100032100303e0b00f88140070001c61485141e00e0a0316015840084c860404040d40e200c034400100342501c030907a080c0c407401ca130341d030b000c00124441c0c8400c5600a901440d41c8900740410315192100d80c0d8016451500d4018400c901c1c1171344035043c3c4480030303041c1c501280d480d003003000016145152191b40721120441d0750034658682c0d07000300080042c02c0c490210941d0664440c4204402c0340d85c12508000311140801c15100c1c2c0503c1101e049a010110f0700c401070030701c2c0e1540c5c040c517080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721610233 1250 721608983 721608991
    0x406180209090a0c171902040b120303010f0b12130c09180b010b03061f020703051b030d02010605010203250b1303140f090427060b0f0103110a0c05070e 67
    0x1580203502d0703407030074050280055000380880207500e18619118440c1d07946c1d202881040440180c0d0301c0ca001000719038854105501084005218031030f1b2205022445172240e1081c80f9010380d21413182c0b40011200040425500402620442130343c5a98400400001c902c9180208480e15a80c3c65004038104055200c3c04040d00e402003040e0421141d1894030440019060b080320115490901c104402641c0340c040d45200e039120411500880b1314151800ea25007180d940005001d07000300c0140103180b902001d440001c00c1c2003103085401d44052103609070300301e42d0380b03008030350040c1c104100c6009404446482c00140000101e001d200d61003550721a00c003610f1045d10810545040340c5108000c2c19803100e03072100129410810640741550001020940384541042c5500035900c500c040c017000e05044000e0046890301000001460b03c4c1031515900406042c00f180384260f00d0905c03a01c4141d4402d1046002d40841c0e090080d207440f4116006980202c50508112068416840702280180190f03442c5805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721611483 1250 721610233 721610251
    0x50a06020d09050f011d07030b011509030501020a051c0219030b0a05040906020d0c080c090d231c180308030a060b1201061b260405030106030b090c04060308030406180209 75
    0x3c050860031b06a044c0b0103c8111415400240c0c00d1003c115400441811600380c40350f8112102d580360425280032015500c003078819440840c01307010042d00a0010502d0745001030381d45114030b64800d460000c90240b41c0203640482450300030844524000c1e40b21005000d002003080031040d03940c10028043e509609800c0324040d40210344ca02c1c103a0080d0003441a0350070b503410300c00081d00d0b0848510f2494001c1d42d005034411420b5440c0801030080c081c0c803001c805840960002c14241100388410340d81c4444078410300c0030b0140800040e2040d489000882990800200f49181403851911180e041c0d400140040c41040d07aa01800110078920f64011b22000400110601d81907160590141190718120140c400d9290740751003020020b018256044160418070b111200c2080038101a04024091900244d0b00b5600c5c000e404000d2100b0034941a200b442c50f8003c4981584070a02400156040c034030000700111410320100703000404542084001c1003400140c0601c14040303400040c20080141c4016030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721612733 1250 721611483 721611491
    0xd0b0f030d12060801090f0b07170f0f010806100303110f030a0c1103061302060309250801110c0304151229120c04110405040f0b010206070c050a06020d09050f01 71
    0x20203060b0900421004090b0310b0020811041c0580b21154a040800c00040845c0c1803e070000f90200d020700040d828000c100c580442d0b03a45484800200402002c0d925613461354840f00000a681d040010701c00d1145640c0c4070f241d40524a155410b54112000301030148642c0600c0720f54551a0742d0810190429440c250346503602e1080380c0c106000401d00b50785000c1c1c080d420100c01c00115040308044080c480354107030760301c0307590340e503001159400d10054511914001e02240500350015880303c1d0284152030310000208810510005a20254442c4010820351030300140010448042078000340c0c1c641e401d081c14584803004031405442c3c1100e4945101c5008801c07542e010710310012010b0100010041e080e10240b000440c0380070a01e9a0701070000d0918400d92b02e4961039981b44c081d803420381d0002c010241083c05103d142805038800b5014039400c09006101d42c50010740e54610881040062a80201c09424401c0094440401075404600845032440e15030f220000012020080e02c84403c0762400002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721613983 1250 721612733 721612757
    0x6140c120a090b03040209190207020904060b18041e0c0b041e050f01080f0a020412080c06090304030b04120e12010c0f11030409020309120c0d080106050307050d0b0f030d 75
    0x1a1440341030781c00000c0c07040004d108010040c4c90702c004061f048110b030203140311086a13480020000c0c2c0302c0c9000c000d4002e00350070144002c0001c0390f0070070b44000784111035221805400087d20a00300c8000c440107002e030040020240c02110700d80d0302c00b200c418042c40441c1031aa44034001e840300381d802039000c00d640f8120154560f0b440108443d85502400c0c049901c9001c403459200000c041c0b520107811301405680708400308a004500e503046074001d003d051940e80140607141020001d5800482c1140224011580001c0c0c03001c0d004011541500d9100320320414039151502c988901015040900086c0002d01100d481c1c1d44d550002407940c070042640002c00d10460700d0b0401025040420700d80001d02c0700c00050181340660200075541510300f80d01c00181c407030380c0d6242403903e0305824402c010a82d2800045624003100040789543c01c0e51041e446403400350341e035000c0442c1d5a100c21108000020300070301c0203400205041d0000301801c2d070b00910052000002600107070030100d034407004c0d01c0801c44d683c9140b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721615233 1250 721613983 721613987
    0x10204170d09060905010806210a08070b0105010c021e041103090a0c09020408070506030423060a380307090f0b04061e15050403200f0901050a06140c120a 68
    0x40b0010703110b140703000742c0b08501c2c010028129000140807103205540b0401d418540c0f16080941b03401c2c0c0c0d1000422114074121504200d52180d02484050782d0071511800017040f207501400002d40bc455000c0d200303152111040303421003207843e080881c241c0d116445030300700010035160101079401002000042c0c0581c01c214502800c2c0e048141e0710608459006010030030984c00081017903800c03910b09403500c036a80c3ea80d40c907100c60005030040d9280101029101403498407031000403504d00ca82b111040c10482c041050344121a0b000394404141c08089000980d070180c01039502c49100c1c1c405015084803442070301c900821065036280700c0e01030980355407500311100c9031034640941b000904400d0000480003107001110701c5041501e01525070041010214080701078840d004550045802400203000007000000c440d4100c052049201c0c8102c0e802058020507142c256a180e040302c0d00280b0a00c10180b03000f100707440d039480c401c1c0d03080c079140307010301040240c90014040c00c00c0002c0400c41603070f6210300700480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721616483 1250 721615233 721615247
    0x60f06120515061b030d0f0b0306070212070210170a050901230408160503040303050315091512100f0b0316080706050f07021309060506030c0d080c010204170d 70
    0x40e140140342c002c1480030351034075400700300d0360344000b00e003103d078182000703407081c40d14603ca001d010140391454150300355000d240c1c1d23500610294600b02c0591b000b54842c3d8001326a030f00f104850802110104000d28801440c04240350080b055007030409202004590403850000c54085440e603120035110310410078031907428820542c1d107981090161400b0780c0000e61003100d442c00100014401d03100015107000308105060008419640402102e9480d5140d180081c03141d002510780000311405403121580341c1c5000d0321110b21602410804117211411502002606041036001070f03114020031202c05904c0c20280100142044481c2c00860100d40e132400380361420700b40d01c00103d0001c07000c010600c65000b0110342c0c041203800c075243c0217848000280c1d41a06521509070004c1d44440b000c52440601c0c0402e802503100d042c0200802c00003a501d080505881d064100d0340c5551003c505941c010009a10602402051a80c0e40006040c40d8076078031469905000083c4400907a4051591460b6081e07101074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721617733 1250 721616483 721616491
    0xd03080a11071e031b050a0b010f05060a0e1909050f07030504020d11061c0510050f060d15030f0507080609071202012303070507020a09151701060f061205 68
    0x40c9240c05000e4a60883c4480300740d007102c024421007840e040c140751003820311801c070014418200c11401e00398a001c542d200c04401003240d803481030030000100149000c48107000c031072001c0c00f800d140041700041115100300c202c40c01a800901540048004542028550060a1000d03800165800c028070b80d4007030180000d003560209800c003c00c000040c0c031011050159207a10010100300d10a003c00003c6490142c0420001c5205550398900c0c8140c1176900b16038040c440510001040e2030322142440443c4499100d12034114800b004081c03e4890281d221b640240b1008861344c01c80390300c9a0b0b840031820f4114109641c2a1302289081c0980310062003995041020640204503152600c5c018900c41c1c1311540019040c40502c501d00e2000c0300c1e02d2000c0c07541c1584000c3c1c40c43d0342e91904400242481c1c0040c40240d02450642d6804950504030f4403908401c4030301c80000026861038484142e80240c441c540c3d2170f07102d54032003c0000d0110310215000c0c001d850a40c4542030101600c422707a00803030350020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721618983 1250 721617733 721617761
    0x14100207031d06090910240f0e01050f0a021204030506071b11060306040e0a140d050c1207031202032802070201080c0903010b21061f05040c030603020d03080a 70
    0x940c0b00c801d103076207400440d84071040a65140005940e16070b030701c00050850340d00a540c0352056132200142100355024000034080503031614168140b034180102d540300f51114499000c501c04121000100c19104050301c0303c81620310413541482140003810b0f2454006a00894040d40454140045946c204803003090b040700840c041002a907058907141c00c101c04844400313005000c0000494480c1c2c9a503000100c40100c240d00301d80080d4213034030f001580c07880d6420000c0c2d8140111600504540d202d4421518842c1c541c10040281c40c0070b500d2a500703240e001880440610591a41c0804010440d001540c4520075070f00c8107420850760020003603501a82ca200c0d8001c039910400107580180e030030482864004450500300c1e03071500740080c0428010301d90001056030141a2028582500568800d2108203600000590301d55032100e0800b0b2401c15016164007a1702141001c090249040c250312414400070302e0310700840c0182c0e0b0703038001c1030552013080400d60001350701100300880b00c503c500460400701441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721620233 1250 721618983 721619027
    0x302120a0c0e070f030903031103041b08030a020a110d0203120408010b01050910080a0e03040305060604110301050a030b07031104060c1a150f030f01021c060f0b03131410020703 78
    0x1a0f0000d0145100f00c86100034541e031050f1140905100b580f00014100e5034058080d44d84c20641400040c000d42010700e02c03811080080b0115550300d0200c2034401100241d0002c00c82200d042e92103080003813000e03410603001540c84e1a00405a501008514103101c0003400c4550f883c0e04006501c4c1c01c2d100902c1ea2a814042c040104003031588030f4003d9548004103e246c41000c0361a80b20307490014180480c0100028440807501006102011070003d009070b008540c2001440148950054070380024410264481c218140805c0070900c803004541d8081c640c0d2500048105107141480d1b150340140d00420300040302d4410041c10441c1c205200311415007449622955464082000e10201c015140c072140201108140404551402c118181e40702102c0320003991224500d0304800d103962444010861546d04060f00084c00300341c2504000241c0f40c621b80002c3c615600e0080304800c6090200d01240c008500b0314002c0c80405003030007280c40c1c0b2541c1c2c1801503034420113070400400d4011320000d00692100c00e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721621483 1250 721620233 721620241
    0x19050916090b01030e010e030a090e0c030f0405010b03030301060915080411010309060e060a0902090109050c160f05071e17030d09170d0906050a0e1b0a0302120a0c0e 73
    0x440c403003030084501071500070072000304040c012030190070b05041540c4030790b0a0440071410380c1c81c040007a1481a84039940e800000c1c3d035841800ba01d905c029a1410301c81641040441e00384500c0000041d84103010781d00200d031106141002ca840c1d036000364000d0300003601c1e02c081800710707070070b81c4042e01e070058003505d8803000f0b505280e158410465182440740e03040c55643c540e0790042218580080c0101c10605082d42c105190003040d40015100303200c400c0707200e90301700c10010a0040691155500a101005005003020800e5040c2c0758212245a02641d1181e003525007440010750400c00000038005046007014026040162a45140c2c5c290f04000045d00e0035078105101e0b41c0c000001d944005e42030190200d00d49a1f2414076420320340c400c52980780d1010380002c0c19101c5222a4000180340d61080104002c2c0f0740e00d040c007034011201100c203041f8058018003e100f55494070410b210092300002000c442c5d80342c3d034a0340000c640c0d00d1010940300c11034028034102c2090100c00c505840c01001800a09401450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721622733 1250 721621483 721621513
    0x3070806030303041a090a150501051c1a0a060306020714160e041209032001230306040e070815090c04090b360c09070207050612090f06190509 63
    0x4c00c0500c00c03038170602c1c20ba00007a9032500c104911020150090080ca0000325003030f084801a1109000e80c90003421800c5092000d21840b55517002d620f034101800d000c070311a101040c0842075101030900004140c9640307011010409610040090a20580094100101400b030480c1080e00c9990f2000d07c2c103102c40340804c00c50258045240e0f00540c0000301c0d0b40d00580c0307101c00380d900a4581e0806449030716103041c09440e00c0f407041e4401d108040b090300d5410300c1c03200c0a882c2a24165081e010132548070014404a01181055002060404180425500c01c941c0300c40d071342454101142c0c110141d0f8803046051050200301071201c0c0c0b001032001d4030700f4000c00d0519242d03954048400392196011207035042c40d4210001500805035150030f1b07103030320a11125602090466613074400340d6095210b4888800410f02c01c034000a9188201c800180920b802c00d00100444031800100404100c568041d82c000304040e06014004540300300c402c403004001d05000403c856013100e03001464400720394000b00322125245 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721623983 1250 721622733 721622753
    0xd02120f01210812010f0317040b0f1605101a0613061107150f031a030705220c200318040203060f1908010b09011a03061507080307080603030304 64
    0x715401450390407030050751030f0401c00f038481c0311042e90780440000300220f42400c3d80c40411044034040d101445224548401d40c0c4d8640c404c1e4810318010070300400c9003254000c64030000e090f41170500c4008900c0b80c0780d141c5410b41446440c0300d011070503554030016070b0003000c0140340800c81e40c1020b42e0a1030030118589840950030f0414015242884055010741e8161002000f0060180086100e60040d45404410240c17100c0d19a46a0b500400c4c140f44480c15140700400c580307018034100a00070110709240000388411801c11620720151451122081480038045005800d040c510703507a80c4d151402d40241c10440e0805410488841507001005184242e4065001c0200142d804440043c1c0d02c2d203800e400140c100324a8495035802040007e954684951512000d0003281e120130000e03c000100c0d9020081e500e0b00900a0300d0401881828408e0304144400c080c551203000640a8100001104d4486c0782640040310f00b199810000410005195404808107401c80c800350011807c5007000e9803010386003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721625233 1250 721623983 721624019
    0xf0c080c0a0501050a150b090f1f081504020304032a3206010f0501390606050a0317031806040503040f0504021602040c09090c0201050108060112021305090c060d02120f01 75
    0x180503228227510460b507a039040031602041300340403c0b940403035201019140c400c0c204c40c440142a889641d180c3d00c0c0c2494000c803842281e0540d5403041c04034282007804204c2240900400050b144420460005840540d012021034620200c045c08401b4a0040b240d01c000341c0307480b5110340c0d00b11000401c49409096001c1c02a14000d003490780c1c0483e2103108444803a041c4200c08101600099138982d6542e42c0c00e41c92103803c0d4003c0d1402d104a81e1035a007408610042440010b054107200b68645040815000c09590094070800c5405a113424199100d40380500c20344050321140c00005080041416120780d5000824046d601582004030140030303101c0900c0081c10103401541c9404d00e100c0c0300d80c030900c40740e0b003c3c11143c1420007503151441301c02802000e00740101146403041e24000324800c60100c18040000344d0080041c42c010240d514504040c00c17001e00b040c00144140803400485542d004081c166801d880b40006885491082c3c61404c84030018261046042072103006100c0501059404050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721626483 1250 721625233 721625239
    0x601091b030c03020706020412030305060405090a030c1407080d032405040b040f05010b1e0c1f181202191e11040f0506090a0b010f0c080c0a0501050a150b09 69
    0x400b2454241c190080e11440d90000c240910008001c00c1c1804601d44d0344100e5030082e9810004c5507611002d110441381c1c151034090307540d4084c2c20700303000203449080f805e07400510407140100c01202c1804001d1134200d0702e0f000703254642c005a1040340160f51500c80e08a0464032a922a071808860a81d0b110a2800ca0300800340036544803000c1400715260341d013103a03804490440041029694455000724245c00907d0380800d09140c802140041e03174004019509101403200141400c070034130a00200c413075040c04002402054650100d209600300582c3c58007000f41c001c030b414030100e40315000c0082c20040844040302ca0b07024220008e401050340c1d401204182e040c1c4070182d0101d1603060601542202d4011a290703403080c1010301c040c0c1c1302d4150303800881c022002940d81d5506a160b2000304011ba0340340e061035a00180303e0780c0c81a11007911480c0550780f03007409802c419240c07004001966040648244007560144c0d1a90705000d6102e14902c920012038540540030001282000020780092141003800c0344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721627733 1250 721626483 721626491
    0x18060f051215070807030b0607050c060c19060c270308030702010e0319030c050a0509041503021c020114070c0b030c040b04120c0e0603060402101103040303030506030601091b03 78
    0x1c8400d00030080408014102c0d201145503151070722006000c4c0ba030480e9107a0000303080050b2003000b0b042030001d546085a019015041c0300160b07800344807a540041c2c81b010310901c82c0e034110b828148900384069003201e0044401088a02c3c050340040c01507812082c1d0070303809104400c04680102c4808411105486d442a20f170f035504d40316600300302e0151420010b040ca041c0030008501900083c001c3d8601c0e000d00b80b5860601c2880240d810036140c0d8017900070f6071004140308111540061510f90302806091151581da8080c0507103940201c2c0321552405a25490042c100b80c10005546c2c01c18020340758903804003002d07850140b05503541501702c0000d110310740381c45d000032020030303042c0c3c0c800320580f0003074800329443e543c4030f44d0b403207000104d08000070380c040c0d40400020f01c0119041814070502d51040c540a0010505178503035909021805000d0303600101080329403000c101c15842c081c0000c00081d800383d076000c146d60800c903040604010069104211b442d15051000300214403034403c030b85903000a030500103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721628983 1250 721627733 721627759
    0xf051f080f04110a0b040801060e06030a030c031e03050604050906061c170c06150a0506040509100302060c0a02011e0e19050d0819022b05040801020d020418060f05 72
    0x3400c4040d1007140b584e02000c1c19201241400011010300704564004000780409940da403031041c8810b8003614410b405800030721410004c00e000b1112850514400e240045c0201074034442e80c00d0101d82d418000c000661980e007445000d00e450300a40d500121444081c141605002c40000c00440c0440e881620002c01031101c40d00b0300c078580c1c5a84140c1c40c2054489039480d80200e0106898443c201c40103020311110182c900303510305114110f44180d68000d404d1524003410941041018100145402c41c005e403152400300c010f860f124050110f00026400800c0340821510002d060b01e4505011120310f03d0040c2d92641d2103683c01a03c01c0c8a1120a4991040041500d0516001c11416800a81e0040b001c12082001c0000c1180240200c0c094600c0a14007401400c41c102d0305d07142050b04019012155840750b001500d0b18910206075402c95040c00ba1810303940e07040060980c0c210762003000d50f07070307130702050801503080c040c09030743d884151442040203d1402c003004003044a043d40605806680044d02d03070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721630233 1250 721628983 721628993
    0xe060609011208070206030a090201080906040308013003050406170c070b06120f031e03040302060a15180501080d050f0a05031806090604030e15040b0a090b040f051f080f04 76
    0x4c96000d600508219a6840c00714100c0d0040c02c5864401ca00242d1690000341102c10302103012401141d03da6601022a440c0540300007a00350f56207500c0b20311000288442d071481d010b01d4001607180b0300c6600e03042c0c1c4071172030590003030001c1c031440707171121516030200b010071586c4015503040f61700c1a46c1c4100444032548901c80401c10780c6625580654180c840c0b20000385848500001402014198104100609170454040c02c0c00d4003090344d00501503401480401c0d43d4a50f240c0001e0711600c2192400d911041c0e40380c00040040a050002050350741d0384000501a001c811712006901c8803903400c0c210b242c40b44016a0088030701c02c0300013140400070f010000c24100324070701c030035000a08581000c82d5850b0620294258132243c044d0760403004181c100490b40d0b40c0c5d0602c4503503c1404510628214141071511520440700d5211105041c200b21031200c0c0400c21081020240c406020708000a5200504000074003002c0243c816034001210315468440d0741450b40803807500d034080b240d070000003501c2d111898a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721631483 1250 721630233 721630237
    0xa020a0302130e010e0c09010f030515132c100b0102070314010f0b0f0307030303090f0506090706080c0708090d1103010c052802153103030e060609011208 68
    0xb090040707540c50385002860424a88031541611192050902c5075156504408243d00c965140c041c085040e00111410b43d034040e1388a036602482040014647d03005580c0050001010350f996a40101e42e903820103040844101d029101c44061003040340c400003034400c3c01950710882d00000c110407544035900700c031460b442070211200550744101c001c0c04000520403d01d01a000391002c1452a0785441c181410034a8011900b91503108081c01806405045440c02c40103400084d5040daa0003803403040c1c2000003042009000d20441c3c1c0c01d0094800242014002445900060700707042c140002400020041035204c41250810841148c0007040002e2920380810302a0b071341002d00350f00d9442c08a101d004160040000e280d06145036981d554036084041161000000d8035445800503400302d200000310103138500300d080d0446120341507002281044815052070401450359102880d601460010030590107001c2c000300b2840403030103400c0c40c1c901130b008200400d405103c0c04a10010509011046c0454501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721632733 1250 721631483 721631497
    0xa020d260105100e0d1a0a0b011b05030f030c0909100302031c18090f0606030614060a0c0606090b150a140d1103010305060105090108120a080a0b04090b060114040e0a020a0302 77
    0x861a00f2807103401c04c08802d0b0b0b026200181500c00d504c00042c1c0398491231180031040401619110b007688065440088002c0c0701a8048900e840104900149623403600040d52040007103035000d45d51060100244100000040c111400040b01c4910174001070380d0100e00d44815048a8003110320f0365050700c104403481e141b070303000c1039034204441200411584655004044500070040f800d100146e5641030440807a49a8418212528400b400c0b00245240807001014034a690b8a855002c010450b01c4400840e4203580c03001c0301031542c913404501030341016141000011041480356080403040500036007030342c84030320302e0421071400028401d4884074158005d1508030341e500950f45e00c960f124074007203607914401c0c0685071280d9240400010b50311030019411104480f0f410910b42460714180042d201c40c0005000c01d41c0c1107441d0346203d034090b190f520983d040a801a0440c80550421000141c04420025146010301000300030500590081108494110300310140060307862650750412802401148 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721633983 1250 721632733 721632739
    0x5030906250302011416090b07080708040803030106080a02090d0605040206042d1a0f0702180c19230723030414010302070209070e12030a020d260105100e 68
    0x4031120700745070f4154000b0768410b42c0e500150005807034001007240303404640b101006c0000c0c1110f0042c0003c5a080b00500301452184070141c0c01c0000550b04c5000c660003c1e0840011a0300210040200c60f511695681d00504100c0b800c61030a96440c0208070714000120000d02000c1c2c0324008035046481e501c1c110f50042a030b0205606c40b201240d903041c01854040c401d03000c0c00c0c000e040c1e40810228542d00400e8101d814020b041842c00301d80000d815880d410910040e640b10860710035032070504140705007840c400d01a1000f040d544088a101c0b0b162405400c00075901040000d210f03d01c1204e0144898811000182d10740d20307200e0049181c0310f40d1000c8070141c10207200060104507d0525070020242c0280c030400c2c03201e4103851000000440072030240c994040c1d40a02d81e00081401107025056140c03030710b030001e00b00c0c0c050440902003807032440d400b80c0030703401c01a8031000d14214043c1e40181d843e498210803904800ca400d107420301514200c101801820b01c1100c684050401d07690061024010442000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721635233 1250 721633983 721634047
    0x70c1b08060a0c0e03031306300204030b131113090f0f0203060705031b090102011d0d03061409071b1a04030305180616020f01091b08030705030906 65
    0x307240e6080601603031a640401300795050164001490007100360b81c13580c000c0b42d0030074489074a40482100c2010707000000c00310000c000840070304000c0e00c40f800310710065501d98026036180d146282490040100412405215810004083c0010f0b0a8504005049400ca441320010304800d07140100804803200003e1101d2200030385003040200c42c40c4041c412600032002e903006c1c0d035100d041c03d644520044849e15241890720200000c2c081060024080002c41840005200300c3e01c40030b54030500c1410115400c041d401030301c41581c1c96516002d200003402906040b1441c1e2400e800101c0d01316080505030000340a42e0007500f40c11185040180c160007600318064104581e54030b81b502c4c903505425a8290f00282c10b11000030790006100c40040325264000b4001c120940d100c1989110541e0b85984240450103281e00e44040300c0e400b406a010000d02a410204c40072050100d00d003042d0310a5407010910360001e0040d100031580100695882c01c1054901035a503514130102c4950402029110402d104d07a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721636483 1250 721635233 721635241
    0xc12051b0c0906011404050904030507020306090f01061512020a050702150309100204031a0a0f060603050901150f03060213030b09010f0e060108070603110405040507020a061103070c1b0806 83
    0x2000075816580c1d201500c0c00d1800c0d0315090300444d000071100d01100780b07900c0e08000800450a110840da6413140c00780c0352541c103090300c80d170010307003000d6003a1103200a43c1e00c525051405041c00b88285001450b030b44007522202102804090b10a401c030320100311f1010ba000c506480040e0150048a1485500422002c68009403181da56001d0f0002c0d0b40040e201d100e8008141c03807800140c400c0790141d98016404861502d004070140314002c0c4014884060b554135104a00301d880c14901840001e4103168401254910b004106207086603c2c10b40720809142560b40108902002508100c040d2500001e02590303400880707144505c0d04a00307510080c90348c80380c0d400308024030340706511603445d200710a801841880085811595601802e0164501e50b8000050400c0014044d601003440d4140d5240c20307a003050381e5240090225802244c50b0b901517001807a401701081000d1056070070702c0707100f00d40e21425428007281c0101909100c1c08000c114220f040b00042e85155048110740c000c0540504450140c90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721637733 1250 721636483 721636537
    0x4050a0b04080613020d0809030c03060a060618060813030509130504031803030801050d0204090609110a08060c090409140d0525050d03200d1d0d0c1205 67
    0x1100d07100c1c0046a0103201d02040342192044c02240e81c268008048055144c07070764640d84600e502214141d07515220b802603800311600c2c00d011082c811030050400148891820b10050038a014460255404017003225090001a03080b24602c0c1d0400e03094034040c610492245419141449608240799111101e021011855016034119600c0f03503100355100300e028018010100d0701680c280c0801004141500018041800c09000e2203a134130380020701c003191120180d00c524041f10000d08045c0c4404403c60604000f5040003500d100080c02191b004104502c0c1c0b1152508090090044091155840300840420b000c010054048144112019244210628036002c0c0c61640011880300110b020207080000200031003410348030382c1d80c2000103003602e03400d40c110490051401a070300c4465880040d8540200c8044000034020303c0814040000f10300804011600c44201d030072203041c040d0390040700c001400c40da0140d08181920f074400000000440124000d455a001d8590b01d0790203110001501e00c01c1d42c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721638983 1250 721637733 721637737
    0x20f01020304051b04140c0f070b04051011270409081306030b0109121506081009030e0f031e1c0306031406060d080c1507030507140a02071a04050a0b 66
    0x3000350b040c4494001220300178002955024540e4035603241a2000007460744051000800b00c00e000d00c40401e02d4900565202c2442481c00e88054525502009041c6c001e500c951142e09410700010b04030764108001150074a9242140c1c080c0140e42a851a02d41a071540701c5030407034850290700101039611b401c0180b444005210891144600007410800181e00c154000c002d000190f0310300001080840302c80d6295a14980c15400200c070842d65180340c009000b20782031203140f450058075030000c14001403a06009024207000c07030219100c2c1d160001c00a12954000846610159050701072040d05445800c0c084c1c2000b070b4070b000d2503150340803882420f00b0207680365102d842600c1c8100c0c440c82840c030184005aa850710211039180d085401c045421010401440c007130842e82c440c0f02e048405c48a1500028544040e040e5100e402180d155402d01004607000320f40e05190640404210f0b04111a0784802541c88041e1700c20300001000342001440e1038015181113401428025001516480d81d48117281001c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721640233 1250 721638983 721639003
    0xf04050f10091e0203100905010b1206041401060804050a02040c050c060c03010620030708070308061c02060910031b0206040308070e0607060b040f091506080102031015020f0102030405 81
    0x12420801c0c011944049910a9040d050f00112030341c00f02145a41d0410000d502c098241c0040507141c0d000000e1100c020b0041c18042d09141c80700300e4440f03248103050652446d0140241d4862410f1000381c01c0054100002541107400c5031400f202540c9036803c00c00c0c00d01c5d12100c0040c0d04103081650381080e02d40c00500030b041903022030b8221840780c0c0e02d0700f501100501007030180c00e001480400000040c0804c1c04003e001098520061301d02c0c028160351a00d0780e503800110110080703412841004101c0c5456004414003000c0310049042d4103007650300203000c80c480d400e03200e4400c1521000340b058949c4294480d0741e003070104000c0c105071002102c001039511071048404600190303d0740000b4121900c500031082d28110701801044c20102240c1e15003002d041c800d0b0146401580d296010740420f180c0d4002d4039a40f034010000c0c003800c820050b0414040e500c2d150082a00b031381c01001881241400700c0003103800c40d88034280035034140000c100200d0030f005d16184642c08a6001009001c1400400325103400d0b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 721641483 1250 721640233 721640251
    0x60a0b030c060c0c06070c0f1412160303120f060306020702030c010c15092103090203010515010c02040905030f070302010b0a1a03270d0201050103020f01030501080a110f04050f 78
    0x48828004200815449000300500f500c0e004800d0803180740c18940098840746114450000c40c441d21002502382c134002c268080c00d20440109001c090500300040d58009801d001d8000e0803407a221800c006103440c0c0307075100040402071000d109000c01030941e440000304031500c860600500d592400c0860183d00820301c00da10034018000703100031941c051700c0029005070b07022041904003980701c1500c3c0002c0141e0082600c1c6094503085454061100f01040401140903803000180b1001c03c1c0141403c4541c000d00078400c2103207140300c070314071aa00805071140c015412030303001c50b140c5698501141180520381c04040c200502049840030141c06402200b400b0704161007518459aa0b00e4901310f90151808040344240c0003000481d1501f0400b9903112402c0805c0c03d402c58017502d8403800c003403401030525400d00050755a03038018421032600310b4503810303222801d00e002d00244d414000714940301d144d4684010700641e0007180741a442d80b241c42400400780b00c014000c10a42c40d0485100c0c40c0000c0444903010307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 721642733 1250 721641483 721641493
    0x15122a030a14070210020a0306050a0803130806092107060203040f110a03020d12021e1501050307150f1419120504120f05190f020607030612060207060e060a0b03 71
    0x82164008a0301445030f440f80d4000e043d2009881c00c000000c2d40510000d904041d1564804107054803212509402021140000c42d0350b41c06901d0b0302a0b0324225500101702c0c6401c480c05000310a07000040100036185d203540f080d20002d102041c036402c1c0780325440d401803005001200304414000d60f00c1c82450400e015940711a0307491a80d03000c002c0d0b100c0761800000d40c04001c503a94a004030300140110300489143d801103030b03d8070744861500b22070404c51203078003200c1c1e50040c44520a20701c000c100f81d60040000764000e0014a041000303120020b400303904510204100c10000c4101c81c0d102c0c0c5907680c26081e461240d0303640d80c40001000000b1072003510428010911354081c0b0110605e42d80305481c4507582117190581e5a03010000122054007654203980304001061220300c65003c002da007009405000c83d141c4c40115040c204019081640040c949811b1500c2c24604100b4036441043c5c0d1300300b0590141c8016550705c404c1c035100c0c008050120242149100f000200030801d10310390301c072280540c8201d0441e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 721643983 1250 721642733 721642751
    0x405100309050613060f051f050d0840051008060a0506091203160512040b0d020d06080a06050a060b09030c0d0317040b0601090515122a030a 62
    0x5820345680d080c000b071107944008001840c414588640c002c0301480f4500100702d804090f8401c80a0307070f405a60721019180541030b41205c0c684054048002400162840b80040a00d0340b40c010517400b138504003540315903444d5407003468520851500b00400807542d41c007201004091428134141d05c3c8c00e000c0d043c0101d01c11405095260b0084800f50302c00c03400140010783d96803e01e400e21010b60064410301e5004208040c00342200c9505001600003424810350280740750442d03084c45480e140428000e150210340401090004079030280c2220551000d002c009a07a441140c81100e000f40a039078000c03c0c5c0f07801070150040400040390007550041e40680f60034411591a081484024420206959415807001040380d015041c10114111401d000341013920000040030407049410f5400c40307046442e15101001c0005540e04580200d020346000c0d60b24900300e0f00d501c02540f09074490602c0c101100c00307514000480b14009503034404200c80a04450306d0f1120003640101149400917520180140c1c01e00b9000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 721645233 1250 721643983 721643987
    0x6010902091c081c0b15120a02070515040f0c09020a020a0b04050c0d0c09050f04021305150a230607020619030b030712060c09030b150105120705040510 67
    0x207180035000081480040c0052100380000807a80b0b08400c40c3c00d50b000b80001544e0400003140c050707840120003000b048024442013081510072101c030000c100180e05016030f41e6403aa030740c191325a100728070500050b0f4031113a0382440d91a02001c203000400c0d1006c0301040100f00204c07031030900706080c07003801038012207030315050014142c0c040c0008160059010b12000300125030100034094106002d0f100380d408140004022482e500580002611181c48241040004800300d204956003d10000007140c298206940041d00b15400090b20304c91194540d800724400e203107030510340301c0e074014024111206961f54003040045426000201100724000002c400c0741e81c1404011181c84503402030040749031031100000c000c1c0810394032442408056480e01c503803a254504100301405403108101080741074880d07140c40780580381d50b00a42c104019071480c08000188040190a41000038804104190540301d401200d540c001d20b50407d1181c0c0c03907001407120442d0058010400e4a0341070703e290b00008440d840c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 721646483 1250 721645233 721645237
    0x6020703030b03061806060d110604090c110705060409052e170304080a06150f0b1e0c1b040e03040f030b1303050405010c06110d2c03030a0e2a0306010902 68
    0x111a4441c6c1242c0c3c0043d0f800d1929216914a01e40704132a003003140400c08000c2105500180c00003417030b1560b61114550216005445206240310708030003011500d01384030204010b40540d00c1030110303d80d2140b01080c40304144030b400896020004070030f0040c44006e8100c096140f40b0360701c51040b00702d038008040b100d010000f200700c1d4103030f07031400d801425140324590b160002007104c40c40000304005500e0700800d0b05405141004010b1803000301032615043c0300c0303d80c4000b0b10074041e60100303490b00421440a4580022031b24216514a02c0f8020114036107450115025006907015040b07d40400500031403d6802011114252030003041d60070110703070f40c01038030100e412444040a00486c0040c002002030750311482e40041e02500c40ca202003480401c4800400c480c0c3c0140021000d210b072200c605450380d8414140d0000500450301c00c40e0b02c0303030341090505501e910000d000b440d00c4a880c1c4003200103d140c1040742e1502104818ad660f01282885484104590900d070001803080c0115000020781d0042402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 721647733 1250 721646483 721646521
    0x10f0909030c140c090405010c0f05070f02040e0717060906011e1e0e070e030d0212071b0b1204060b0f0f060d200d0f0c050306190306020703030b0306 66
    0x31281c1d0440c034151510541d640b00c43c000c000c0c1c9031003104502d1130617444005545000781d10038000030841d801c020002400100290200d034042003030902c07850020404007100c8800b03807038059400240841740e4110a034288049608020f10030200e10840c85011500040d00600c962110800c0d00c040b40d8840c030003045c0585110206243d0340540f01e0051200050f4001500b540c542c2d8521003030111561040d0506180f0b41c100d9140010900f01403144100d0b04081c090400300400300c3c4040d01100c41004c030a40414040c10101502488250700300c009901d168441c4403001d80001c0316016101c0000e40500d10f10030340c003101c00720342160414060300b625082c02c10740050400c00082404510f03007822014002c0b5508203001f00d0040c20b031200480f00121300ea8071000c100705242d040300c243d036820b06401100161603035140811b4011385080e05c000e407000d41c0711041d80e030022400c8420748008484412213800211454001424507840010400101074042d400318030700c10b00603070a89043d07948208100c400440428 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 721648983 1250 721647733 721647737
    0x3020315010f0b0c031e0403060c020607080a110c0312010501121a04050903120403030b0f0306091509030d050709091d1b010c0c1202010201060b03010b1e041508010f090903 76
    0x42c0c81030140890250150004005280403241001340503104510280031504800854000000707090041c071103a4013039446802810300080c1304605040d5001005503200502d001c04265a030f1042c41e002c021210b0446100303c03c01c1c42240e0b02e41e03501501c060740030402072003120701040b01018020181c1c0d1813802a1000c03060907009550001c0c038818184000751030001c01076192030204020082031502104a41c9026900035030303000441107684402d02801d00034404886219910003010041e030203d0006030210b00d03180b040f00305460303903d0b00b030403091070350244c21583c190050030700b000c0100d041d50003020035040b2042e6400030312090000e40c022501d400d0760000c0c200748a400c04031071100f24150825074140030407010305d00704440e0000307911781840c204003d40040151100070602c80c0b0641d0b038240038010142c00100f40a034070795450b10301c80501e00e1140d80d01030303462524002e540501050300380050b5401014103c039070402ea444030100041600d0f509028603c0c2034a0040c0700480d40c3d9180703102e0a00040da0607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 721650233 1250 721648983 721649009
    0x15040608101d27010518150a2703021c17070305040c080114010509070e011e050d06090902100f090b070606090e0a0c051005041e0902130302031501 65
    0x1031100d58407400401090001820001c6401d100c01070950f101840103403080400001d89400c010980c40684803540725405469400041c0380d15500c0010702880b50402000c0da40000c00380400301c820210610700c109444061030400c40c03450141034010502e05c4c400040300301624000390280c0d42c1500d604001c034009884941080c07000501480c020750100b07400c40d00400c0800c4030385540750515800d644901c0b101c0c0c4a00c9243e00c00412890034140310316500000182411840fa1018034002461001c60954100c40c030461628034030741d110302440445100000130321003400310315200e4001c2405001a40e800302d0107005416081d0000303512828001007103811943d660504149400c0f08200903800288050342c0c001c0c0d8507500001c0003100ca11800e04000c1d58840542000c0240c1e00781181074002a901c00c1d07004141c11a40005416448412281928400003150381d2082003805e44408070100c13a041400c58510028000c00400301c00c0d12100110b038030880485118112440a01400341401c0c82044001e00c2e00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 721651483 1250 721650233 721650269
    0x1c1515050306030a02060a091d0c0901140c100605030c0909060106050c010f0c1809150308030717010f15230a02030c03040308030109060506070b070809010b1504060810 74
    0x2040c4015600254020211902c1c0340180d0002061b80e4041101c43c804141d184000708881c2004202c01000c40d03d840c22180b813545014401da0103103110360451a410001004106001c041c4084165450010a4400c0f1140c903400c22912000414841c0942c0780f0900c20307640c003045030b4600010f11390f200c0d020b4100501001c0e483c1004c192082d8010901d400015500c505e022801c92445118400c580349156803400f8401804020f071084601c00b9400481c841c90a1005541c0403208098100741100d42c08812266a9030300c0100c1224510107075408203140107490800080d64810030840e400c00d80d41c0401c9202e05044c0c84210035075090512000340c01d910780b001c07070b501c007100d001c080c02410300f0824a0064030b1524802c0c21000e41190701a80003121001400b00050001c80b01510900000d050f05a8010380341c9051601c1d81c11852400400400070002401c002544400c030a412940c0343d1070000c0c0404005121492682d40640c026000766000103da0b030b4001462203100c2c1ea8182d0854080024000b25007038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 721652733 1250 721651483 721651487
    0x5160b091006080a1a130501090503040906080a050c0105070f05030304030e030c0315041203020c0d0206010305010623330705010e0d05040608070302040b0705101a012a081c1515 78
    0x300051804403041c00200440001c00d070203005e42149d4510510166503a2030070001d10070f0846489400482d2540e1012120200042c800102e01c0c034180004d080c42030711003595240039001d03032030f011304002c240d03020100a1004050f04501c10030355a00c0102c0566900343c2c040011706503105885519440c071141903002040102d0852241510025403500d0098504020307203001a2030030807401080c2005034002001001404400e200d100043c1c24515000e41a40c40251355009120303100c900d0180c800c071144c03551040d85540109500d840c1c2d0500344d103640544522030b00402c0d403d42046a090b0703150750a16a12031044480801c51107203055040e15124201800d00c3d900f214152001071400d8145942040081401000e082c051b1400622910041c0313402c801103111031042d10361030402c2c40494042c0c180e0780c03482d60303800454004400c2c55020115103c81540c0004508007200b416002e000c0403070004100988001030f5409006594807404240500d103448850300307600c16943d100e000000b4080415080c3d0580c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 721653983 1250 721652733 721652783
    0x20903101a03010207050706080c0f120601120c030c120c08010b030a0b090f01030201120c020c100e0a24091802180a08071a0309030a05160b091006080a 67
    0x81045085000c041e0780c00c002c0703422030740804000d891a5001720030401140d6446003011b58000030410889003803020500119165014082c16040101001c400082d201d07442200600d40441c070310001480110001c140280080004ca000100024410003960141d0ba08901501e034009100d540ca07450240ccca0690000c42d030b80c2000d00120b082d5921070080401513510308801d03c0c02903071404984002c2d0751546c4005000640c01d580440d040508254600042907000b01d05424801000d0303450055007444000101c40000c0401d20715580201280401704901440c4285640c00d400001c0700c0c00c800d1008020306a901e844144240300e0403e00d82181403609000030f030003511500307031601c00c1031081c000700d0380009074045c0140d0003400866204007402c000e8130441c202248646a446c00c0000e20314203080319a15242e10a10120303800303000300000d00c0c200340e0b00b4502115030103a41082d800611400c0c40342030540c03503222001d1428510303814058041a406804542c01040c20f6120500c40480c0d04040d00854501c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 721655233 1250 721653983 721654001
    0x303250f0c090204052805090621011b0503011811071202060f150604120816050106180605010c12030f14040b070e0105180a03080403050c03060a02090310 68
    0x450300008000354004600c40050079044030302688940c280713014016504840894800e02c600350003445c0100300f01c0b17020654103590041c0e50191480c1d85410102c2d480b041402c07842d903007480410f20045510a01907201c20400e0075000740e110300c80b076540241121640402e0041d0f2900240d102a1200f107401c02e503204858000c007440b14141030090780e0702c441402d168150340b0100940c102208002900c2c0803074498a50000b1817161155206c01c1c0d000102d9a01d001d21f00900d0002d00400c45028280008030054407100c1684442052598905181590181146125034400300305000c0c2c920300102c02502600c4113035101a5680962200340d6222810400c178402078200c00e15a4480d038001d0908428000c2841a280f001076000d2141003900d0511a800c400914020400207000186c1c01184c0e0b10008552a200e034081c03603041c1c4081103400213040f003071090303000902e442c5000400001f003103408503a080c0044021000d5820581c7d460074514103a1141c03501c2180d040d04410000c0803840f500307a000c1544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 721656483 1250 721655233 721655243
    0xe070f02070e01081e0613060b0402091504060f02070b031303090302210f03030f2a0418050a0c050901050a0909050f090f0c060703030902010e0406150e030325 70
    0x75660394030034604410800e800008071900a090540c540850204c1d401d44510004ca00030b042c0c5152404009000480f10700307004000740d444407044600b940d21501a0b036a030440081046001070301d03443c04100c82d45d20910966010602e607004c603405190001ca481801c580d00000701a2441c0c0d548030b00702980380c8076010103c0500641d45c2c00480503841e12901500d000706907800520703c040040c202c6524040c17041c031030769001e94002c00400541d1003034010016044000c080c1c040c0c0c500d03031480d05020220405080e40b050120800310700054075900c04482500031804d180410001c03500c07000c0000c0c0c19210444854030105400f0001c080c1194880c1c401410401c0162401c505040d44600444080e90030640d120343c02c21800c0e006008100105104031a08188050000e007603070750400c008034085014154016003410380e602c100d8400d59003e0400e248400030028010080551a15000b64080f580d4800340c6000a403100d2126074203050001c01c0b107504002200d800d5841c0c1043d0000e900f1411901c031000c4230 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 721657733 1250 721656483 721656493
    0x4030804020d0201180e06040f0227061605011b0309110915030a110108010b070b06100306030218091605030624030d02150c070b0601030903030e03070606150302040e070f02 76
    0x80c0303900556544002414aa40c0811b229051600411003602e05034200c1c41c1c607151042140f511000c040c118100c106145411070112054180030004c0e0f0307070340112069014608004a900c01c2041410340c003101c0ca060101c141d1020080340044101e00703c84103004c004195540c02c00b080d030450725041800d9035000d503502c05000c00c002ca020005c81d00304a030b000c0d811950284c0d80d0703116082641c8c000510383d01404a08100303900702581a12070108944002c2d000320300814858098514003480307504980080c640142c80c020225022120000001c1400c80d410140b5014440c69511512080040c010803101e00400501d180e454208900250b070440000b004100c0d0030030000b2140548003809205c40c0f11004c2e4001c1c01841e00c50380191040354000610300102d00c40704000d0800050141c8107155003104082c070f0001002c440900d0158000c200f680d001000502c030101d03800c0c0c208803064000c10140e414514160f10310804c0e0900036000d90242d4060008100030100002e20705500c40c1c40182d16403000392044036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 721658983 1250 721657733 721657757
    0xf05060d060f0e19051209030601030f052109030105090d050906091906050318190b061912200102031b030906030703061e0807060f030f02040801091a04030804020d0201 74
    0x14507100704840304c0049070030310503020000e102091000b0000526010078035441e1036100d000181d2640014000140b0701803200c440c802c280b14040007000030f00400d40240c1034502c1c107041c00301d102541001240714425800c0c0070019580142c0440e07100e0014010752142c60600c8940402c11000d504070f9461503800c14182c02070b800c22156021450350081c0319603296240c4d80c0c107001341511000b092940302900c40f6481540304e8196031104e00284131074580c116002041e03d4485000003a5901c0d0452401d5000081510020440702c0d41605004880742c807031608004800180c20130000181c0c43c2c509818050303002440b441c90100103030000c2581592803102501d280c480e5901c00601180c105036850030000e81d55150a0208040601403441030700e003207800650405143c1500903507201264060302d0100008002c15101c4207001c1d4000600b0b0204941055484603140d00314580209038080d019107003100c100c3d40d40702452900b0002381d400780d0780503031b80d208190341d0315003d01403141d05040c7d080307040110f000c40754 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 721660233 1250 721658983 721659011
    0x302190e122a0f150318010504151a15190305010b070b04051203070513080c0d110316123e0d0f1208010503030c101104080a0303020304060f05060d060f 67
    0x580051404c80700c0291242807550307514400300d001c2220504144c1c03501c418400443c2c0c0c95145021001110303e070201e102c44010200e0300c00031a036144040e4102c05403c0403c41150403000141042d80081448256021881c0b0411400d80d9401c2c4941d0f01e4100003003026002048880c4c0300c150b40503004200310745000048502e41c01322030b40125070410000300c0215007528049400b441c00001826203000605000c0414800664466803000c1e00420528411005c88940e031001e2082d0007082204082030780c0c0f82030f034810b54000030910002040710583c1043d0700398417602603e980300080ca21189101a2000324600e05e02d615240111541c965002c080f030032801c40007a4044c078010316064440c000041da014401003000e040d640c8113800907442030300103000c200c01920000800304211100e944010584940c0041d0f42080340c49107170008905401009c511206050f00742d0000c40c011031284804221005018400e88100c51060364403580c0100140d0564010400b00c1d00440c4042103111360000758401001340b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 721661483 1250 721660233 721660249
    0x1020c0a0818041e050601020106150513060923030304050405010b0909010e0c2b02040b0a09080d0527040c02071a091f0302190e122a0f 60
    0x108036100301e0000b50030310010008039141d0300b8007882510180004000708240c4d1482500e9011616440d56071070f0001034040e0b200350803100086c520160880c10a82c4c0031307040103041d82c0c4440c5008504d900c10f074400043ca184154035103000c0724211aa41803520509001c108608000c0381307103580c0d06210501010900355540d00c40c0380e001341103444007643e82d0b0380307290b0512012210503070089210842031002c01c4a03000d881411a440c0300300040214411404500c0144d00c16014001a80186403000c900880c03032500030001860f6444040e12806e11040d41c0349842991030b2540341564000038400d1000c10274003940500702c01d0980c000b03c48006541c2803510007007002ca070401421900180d0143d00d0400c00c0360b103182045807a045440c0e000d07600d00080400468040d022182010780c03203201443c5115622407207a41618502c1e51a91030b1098440c940c09070003000b0541d00001e0900c614581c205040584030006800603804072205062405584c912200c20881100c0601d800d400c6510450785a0081d541d03940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 721662733 1250 721661483 721661503
    0xa0c03022104080114041110110f0303060a14010c080c0a02030a03030b010e040501120b07200604020a08011401060509060d3905030105040b0f091321080c0c01020c 72
    0x4040d64940f03107400401400d44c0c80c2c0d4482c074041024500240000b0807842c8215400c203100c240c84128414410400450303c0c0c01207810108400d00070450000780a403800b0004500422040b210041e41c16207984070740010110040c0614003180514550000003101c03000035220030070000703040da801d1800c0c40d00401e0602803098012030003e5601c2140410075a0070081c50000c0940c01d4a04120a40c1000c0c07081c414200c0c4081d0180c070880c4400c0014a030b041c81450700b10015440c0c4815101511407021390203075140f405960403489081c4441000c1000030781403041904102c2041d43d9004107902c0c000c1c0503034942d4805010f590f04500108100d41c13065241d030140c51403030b561840741c0ca0040d03491054070015003501c0c0301c0720100c059100104400165801002d41f810b40b517086400180780001980010b0056400350b60464010092500300004400708001000e5132078001c880029624a1040292441101100182010502c46030100d03442d4a0440c020f0700041d982e48000501d01054441498680380c1050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 721663983 1250 721662733 721662793
    0x609080304140d0f0e12070b07081e0702131113080f2e1512050a060e0f0a140a08040b0a1d01090603090218070f090e06060a0c0302 58
    0x552110100c2e00800003240403110902c1c21002440c401100217000c5c14603c1210b911030540750f1902e440e1010f003805550000c0c86155850b40c0c3d500881e03e0805025040481d00c1d48040c0c074052113109421211208450b50300341d0050441c81da50000c1c40b02c03040108028101d03151403c2d004d2000c09550088105800041c1c0800002015807901c1081120304d40107298a29040c0b4010400220b031848007075034090340394a01944408034440e4402100c00310865040c0c2e0084143d200600c00e401c061040114011460078003038101405480b2011010603034aa80780c21019001c4c0c0c2c0302c0500034011400c0e80ea941080482108241c0b0454034058a5109150b00a500101003c590000f0110b90064000d80d901030103108690800300a0b0b03540400190604906124000038140c540c0038070000c65032010302c500074600c5240c100d142c00d030034808402030504141d43e4080001c03900030180496452614001d0b948038803401072030b4626068440d0340494200c0400c04d002c07025031040e204c2040845205a0180314481c00070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 721665233 1250 721663983 721664003
    0x4030209130c03141b031207140307050d050702130911060c0a08130509011a09090603030c01060603020d0f0504050a080a17010305160b130510211a0a06020312040609080304 76
    0xc03007020711030140c030f00c12176842a40300980381d102403a566020b481d41e0325080482c105c0d0314440c03038105505611440c800200746010300d09070b920340d0316003001c05031145500030345010fa034800740c90210404a0744ca0500107001420804402003142c649480203291340c80c0141c003a1003502115030340b80103007134000c4118600c000c04490000d1000c1d05003e140300f40148481080b012546410f005801c1480c89840010782c001c0108a0014045803410011200100030070b0000300200c170b07138800340240290000240c0e402c1e880d0800005060301d80c20340c0a118050b40d0030201a041108055440341266031001d648502442261142221b4103621410340c0d83c000c60080024055044900422001c0f014494000112040c8144080c011503d0030000700301c00e40304155922401c00c148417a00b0f43d080e010507550748a1004040703a0180c9103134101c0e00101c1100e40c0c17140040c031401c1402c1e020086801114041c000050b403040c000c0140c01d10f00000f4440c0c206000c0c40000503250841c1d1610441c0d81d0048805660607101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 721666483 1250 721665233 721665253
    0xf0a08030a2a0e090412081503030315030105090d05040e07140a0302090315040f020d02041d010f06050306040b0703050a02040b0a0309140105072c120f1204030209130c0314 76
    0x49200c1c0c02d40b0f218103d40703001c5075150681da54960a842d000451041000d0000000c04201e0303aa06403210500b40103007200d0702c0345040c0d00c3c51080ca100e1000c1c800e000307509100101e108841c001610320001451500d070b090a05042030400c40c22248014400c1e01009043c403140300d45d111103a002000d04500558001d42d68050b032000b4145096003008002c18211400c60400000c40d0901d00404c5040e68102c03004505100075000060180010000c2e00f087c000d0170040e8813001107815403001d03101c2c842d00c142c14000342d0b50300d0b805c2545429040b40c0c050a848a004000f54160348664859a8002401a070040c201501c1e900800d000c0d0300691101008643d03119064400c0c0041e4003540107450b01400000d10441c40c2450000b002e13803080703c64420081441c200c600060320345c2c60301d40d00c406008c050000d44020f018401d41c241d40e51031103540e1561600030b0512603292103894604840950743c0150403960f480d292010010200c0821005c180c40794650b00c4404000994140384003408d02c080c40300181210302d031b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 721667733 1250 721666483 721666487
    0x7080d0f0c05031509100504390e03070e130303110f040e16050409020901091502031c02040608190902210706050301030515071106070215090f0a08030a2a 68
    0x10200e00744a20905c00411403107034498030101c015120151000b213200c1703024000031001c160b04d08a07a0f00740c01c682d000e400300c000c2400c0542c90900d40026035400742034103070032814151526254016031075602c1603000000e40c01c0f00d1101c04614071502ca49000104540302d1900e81c210740d040b144ad21a4020380c0082c0410403180009086c940011120143c110118501c810180ca24401c0e48105c19089801096032070003a80294401001404010a07003448000400c0b002526a40024814901880616072a07540c1d008288243d5003a41c0c0c00d503c1c0c0310031b2901d41c000c43c00111006001304101c00384d01d804400340184c8580d06580e003108060705840400440780340020b4104090f503045141017003814401040851400580081d210001c5180c0da925515501021070f143c41c408210300460b84aa901405480c940c0021104110071680c3e08907000c60302c909104580312160168442c155500040505020480d26801917403c43e0100500107034044500141c410040c034000541d9168803499013000010315 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 721668983 1250 721667733 721667761
    0x120907061d010909110706020316020105100f05222a030b03120c0a020a03030e030127140f0d1116030317060103091a0a140c07080d0f0c0503 62
    0x5811180c0724a8004400c00201042e040307110f040703e6142c456080c440546541c0b421140c1031900904155500d24145521034401500030004100540c80d20300000e440d18200c1e00140c0a598a00050810213841d10082060032000f4000d83c6030f108450004203000018644039072804a100503a504c003a200c0a141c1d03201d03180c03910310700b00d209041c18082144410b95010034102c1000418546494413442092803072031401000c843d00a400c25031010001c0289a0000e800d152130010850081c0550418040c1541d101142e41140003030300c0050f80007003000108940882c042d0112103c040fa0100709400c6000c5140c07030003140315100460072005031090110024030414203201070408440650318076540e030080c241d50038404004034202484001c00ea05078400c1c3c0141c03017865002886003210119101642ca202902500c080c6522843c1030140d03860002c91241143c4a401711581c81c03030906a164640d8100c50b40200340b41c41c00103a0f6105d4840181d5410701c80d1262010b0150f5500e0b0310f83c13404d998401451 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 721670233 1250 721668983 721669007
    0x50c0601032d140c040618110c030a022a0108070c030215070905150901050901050d02040902040f1511100902010c051203180a080a1d13230f0f060612090706 69
    0x4034184a420704c24544005031f0000803564003000080c1184000c0f843d00c00ea401170f03210a17442404001220f5407019400100c07000c4c1c0b2602121000c11418a85450700c200030b04c1c0d00400342c082041140042c0358940079103102c06c0724502900641e40c01d20001c0741c0c3c03103406110844562000c0f4500c858144600d082044010068510001801e440e0400752170010b4054020101d00da410400c001500001c6c0500e6501078034011300103450207646603500c40540a4907456140503120403003600c0715001054030720608010450183c4c540182c450740c04601d141001600507168141d0600c0301440055000540802c001c802121808a10588034202941c40103d0b13400000e420149550102c546200442c07200d0049800461403403e201c0000340c03428102014061003d0055030b400200c000100181043e1a0084410306440d07905c3c0c26a60f039001040c04151020a40b50150071904020005903405401d100d016001100288414201744030300f12a12040301040351013250a8000da4402c004550300181e400b044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 721671483 1250 721670233 721670239
    0x30b010305060d080f0403060f0621020a090f060e0f04020f010906080601080403030b03061f06030213033507050610050603040b0606040909030203041401050c0601032d140c 76
    0x680d0410b00000f0310410411840030300080c81c001074080b5004040d00c2110000c42c1e202c4020b11160071a418203034001c0c021071103464203a00640d000b540241c031200d995030307000b00d60080088910900340700d40a0001c202c41050007034615031360800441ca104080302481d100c1d1004492480d13039450b00303105101481014a00fa1810311480751010700c20390f60440002c81d0301c8002860804035035511400c00302c020305032045405816006110a000d1008407614114087c0a80009035442e5a9071350700049007244102041e840e40c0a24845c000c0c00011415444200b45804805120601ca0b1115000050180022102d40308400b000180d140030420184416a0301024010860b5025881c22001caa07191100410082410a0000000f040c41c2c1c0c1c3c0f08103403000351843c14010030044050307203000b9540c0d6105004401060f152040a03481c65889041141c10566103000a03141607480d582d01c010300900b0010f18100f05400608071403a903415004005201117004480e40c4c1091280000194200305c0c6040744180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 721672733 1250 721671483 721671491
    0xa0213090f15120314070b090307030809030c033c03090105090a1208090703050f030c0f01050105010c02010c1e0c14151605070e0124020c0a030308070c02090a0c030b0103 75
    0x8003440c1da80c0c904403c29058102005082d440091201952181d0140249190300305001c1c84460000007000e0040c003846a1228022912040c01040c0e40e070045d800700f8610340d8400c00550b41c2d0040ca110302c5840003911007c0c291055a584080070012000c18400007030306620100c10400c50140034028a030b00804113101402099541d13459090b40309102010510070300450b080480c1e41c402c1c04000b01d100854002040c0c1e5200710f10440d80d80d8603640001d018482a00c6003041e5030702101e406102e0a0704030f0b01c058403410409102a80150b807a10b02810094400c100404d42d60040440f4415000000c18401c400c01d02c15a81090703c00b81180403101400b901662051704600141e4101340c040342c0d80e5101d030007007032905004503142480c60580190030040100d04030000000da210319100050710440c02d6031070a000718440c1f25104a07543c045c0c607204e01c0d074818007101c030402c00b10780a400e1040d0040d40750700e8622205c1c5541d40124144d040d080e1442c1d000b8940c0e078034241064030341c12300c02d9800118003403070140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 721673983 1250 721672733 721672739
    0xa0c0e01030b0606210c0a0905040b13051f0603060911160204020c120f0723070618080d0225030c09020306030c030609070305060610050a080a0213090f15 68
    0x40602c1c0300404083c081c010008090100340303501424107071103145003802e0411524060140c1c1d0740c07681000d41d041c80032070650b00003c200e5103401d0082c06000100645125a80400e40009c0d20103401c2c0a004041c084001004040340755551300d1203080036210a48001c5480c500d011040c0040707800400490340010000c0c088102035036a041c00e803d1166404580258441441d0100503013410140200f00e4090f03507001403442d091100d080c0c06000380318062040c450a5110005d5003080703410003188200120740180700240320660050100103126006002c0580d0304a803200891b40c542711042030301a0141e44194100c86030b46000e600782041a03000b00b111080c50303e117555181b00714042240200724040381c010001601e192402c1010060000c0c0003030481d03040742488250140c0f59801408299039501401d00001c1960421980501c1003516076682d0031302e01540810125440c0001170b1200e005147c0800010b861540240502d0340500400c081c00140985240711500c100c401c0d41c00d1001041e000c000c020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 721675233 1250 721673983 721673993
    0x9030c020333010e131704060c021003060e0f130b0702010509010c0e0105040b030c0f1303050d0309020112150f091a030a052805070906030b0619060f09090e0a0c0e0103 74
    0x20a41080b01100c03030045c660b1603482d2070b000f904611071520a02085c04200080c03059441403409641d10300a5030340d40005691780d0000c4064940781d00034494002e0700000410b0382c880d00d0404855018070803280c2580034074010360705c07504190700660700340b00181c1d107501c140810004207200300402c0403503070b003000b039035000e42e10002030300f1402a441684c05e003480c04800101d80740604011039045e1016000003d50b00d24070226050709a0000340416500d5224480c001c4000c24045c2c801c3c2e01c12590141c40c1d0501542c00412854007601d08034007101203034600884001481c01080700c1c0d010260070001030200d03401c20072a144204a208c82c42c0d665102e40d000382b03803407008200c0c0800e00807a03900d8107a11045d1144001c20310641201040500280719110340500020744280c0c42e4030840940348a940c1c4c807505910f404003000078260128071018070064440d80104001ca000e40d5841c00c03001142d09001c3c40d03e41c0e0f070300192012502c0c0c40c00c0d02681030b00289002020840040d000e44007400911800461030b505507221 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 721676483 1250 721675233 721675259
    0x507031104140f01061103160309170313030b0c0d050a0506190b0a080c190504030308060619360807060c080d020906070501050a0f0b060f0d09030c02033301 69
    0xc41c41407050130208450411024411690309402200c00340071461054640202010b180c1d0bc210b0071280b100525120481c0004012076072200006001070310100d00359200c0ca0700da40d001902011460004010030300d070919650103118031425050200140d03900d080000e1000103207080f10703071b0003040e1601d9406010f8a007408040c1c0360f07c0d518610b42040d00e80d940c00104051031003081c7c4401e04980480d0302003130310749a0040042042d24400e03503892545440e1181030103c0c600170750642c03c001c2031402124890951180001d8162600040002464040a501c4100174243e40303000713004124080c08428440343c101085600c0081c030031850030b400e5080c51a1160040ca0103041c1c4102c1203184c00040d0400d446d5908003d580d6181c0c0c00100070401414200e291200401c0340c500d072048a03508006c4004541e207845d105840414100c126980d25002045640c00300030950410100e040c4048070030b142c1c0141c3c800f00000308940049000c441e074421905084441c0f04420307031070050300741c0f5140c41c0184180350030054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 721677733 1250 721676483 721676489
    0x418140c0f030f04031407120306060305130b071202130306050601210902010507020a08010524010c02011209080720030102031b1b06100611070305060f090a0507031104140f01 77
    0x80c034841036403101d1030b0071511b0008070740303c4c000003030004a13414007444850135810750781021a440801c00240d42d940140e00790f80c021214040005605080c4c000402c00c105031095203c40302e8545131688180c1d40c45200300704c3e004498070a206101c0b45e84184100140b502c1115000002401c0650040c0300507000007045400000c00064182e450308051021079000d03034141d90f0642d60041030986030945620b20302d03009010445a01d421903200c4500079551501151100095203410b07510f42d070291040e50015030316486401949050300c0d0351102d450b004110244060000b191198202c05d400701700020103036041d401c503218414803d91040043c84080d03a205030b00a202d0703004440d41c082c0c030350491800300250400b020340e42020601900c01000003031160000260192003280d01d80c06020311480500301c0c1d6803d06800014429440740c000310701c401c403d4080c429840307003c08044450003280c503074071342d81064450743c0304841d00840d004902d5403e15160241e14000068a6406460361070300310320b400020311040c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 721678983 1250 721677733 721677751
    0x80c0f0a0b0c0118060b180105010203030c09010c050a14060106171308070c0f061b050601090e07120b0a1109242502040617071a0418140c0f03 63
    0x940b0303034042000390451074400b4019184400503c102e81031144c0901441c4c0010b51098118041400b00c540760300305050b060340d038103a00039421683d030014015040d500c447c00e0541406904a00000080e0041100540c442d102e0099003041d4002403030007618024040e08000180403580700c401e034950b004a4001544000c000324001064030460614003a58442d0030f83c042d103944400040400e10740b6000e1024421101151746014108480150003010009d503808003d0250b0059401000a489550000c0b4608029002138510169a420702d0024000110320200c1d6510389400c00c00500312000c1c4603505804426020080c9420840c00c001381d1282001d86022445480519003000c0049031030042e1005180100d202029907030101c0c600685904c00010704912407401d080c40072450501c240c61108091010340020f146071810400e00c030340408a601c0031074080e10405d11000800c1142500c8907071019600c50070000b01030702070113041d20301c1044c01440710101c11070030003418855054030303001c031f0394028101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 721680233 1250 721678983 721678987
    0x2109110a240f0201060e1e0124121409060906130b13020102190b0a0506010f0e0d1b09050a0c050a0207030803060415150e0a0b07170c01050c13061e0507051e07080c0f0a0b 75
    0x82d02d2b980000c100b07018400807111349040400c101d60702d00150b894003844801080702c40d503a13201910002019031660000384a02100e4002c40c40040450f4403101c4403510500588411340d8056103140d03004042c118059845421440c1030004034140703486034a412450a1074003004041c4070000180410070f0800d0694014464558644280440c001345c0c03003206285c8803c06141107031b542280c0d6020781401e44007000d845150003800f28920b030046045903060394182d000381c00b4491a45d2500200c0e604010803e5030050f4076640d517070144142c5016020b000c0c0c2074140d900c0b2214100e101d401055200061101e41c080c0701442018002c503019007058643c526400001400b0340305502d2403207000c5018035040e1540542c01d00701800718070f00800c0050040d120360a50185017903a5074040c00c696050f80d01c2000d41c22000464080f202e098400d60003050440e002d90215100650b0462512403c2889181c004070315410407402400174ac01c06019495034840d0031240681030010510024100e009540314510702d076140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 721681483 1250 721680233 721680257
    0x8160801031506030822050d120f022416230c070b03040f170f0a03051302031b030d02010b102109110a240f0201060e1e0124 55
    0xd0383c0120001d1940701c40e0054a49445030340d0001424a46100140805100c0c0c0f404502410000c00e0296503582180c00e80103030514600066031040040d42c004000c50085480d542278000d0003a040b607030f000c0008901200140340c10400350f20010300240c96002009251880c0740c030b41000074048500c1c604080001666207500701a54940f038032050f5440400392490100402041c02004101e180a15004141001900c0c0c250544000d8911500c49030300301014041c00b503a0317543c0344030f075000540c4120500c102e0800c003076440d00040e00d81441458040700b6114215140000c0703040a11801545242c140000e20640c43c3c100000360140d400007001c2802c025141d1010030003a0102480c42e104001d07000c0d420030010301d03a400e00b0801a03402d1040d05001d0301d000000020b5045c0701c001022270745504640c1c4c8186001c1c0c1407104564140d0300c1c0010104540d03d4210210b04240c0c1002c1c2c090003101c003125000c02250b00a000c0d0a12190140d00541d400b0428110080824002e1000c0402c000b03124a0b06070040d0030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 721682733 1250 721681483 721681523
    0x6101e0c0606140f010f1202130902070b1b09030a0b07170f1608070507060b061b030d060503150109090c0906060509090c18041509020f0a0816080103 66
    0x600d200c003404580c00c0041c00a10f484081c0348103400749000b500c448030118141c0c401920049115802440000c1200502d88100d82007a170191501c004100c805250543d5550101410b13a000300a082d43c3d450564428080700110f60040041ca40243d80c10580c02c240807080002e0300c840b000300018291819100c0000c4503039100d8040c42c141c004400031503228a00703051501c1c5035422011641074032150b0541c100300022500800e00c840c0709005a5640d54030708883c070341d1200c003e001908402500514140200e125414104202c2016225210011130b180c07103400c0506c034103035465580068080e800c1a030688101d4111800b40324151081c83d0710205030035482c0e26080740600d11030350080e1798036803801c2030206826922000070507081c4408c44204c0b016460b5548603040d1840b503442c3d44050700c01e000d2a4250103003880e07000305031002005190f001c2e80990740d00341c1d00180d0380182d42c603500c4210001902403034507401070a21608101103d594440155140d28060a024030601015000074610106042c03030038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 721683983 1250 721682733 721682747
    0x7031409040c08181c0c020102010917090411031003081c09241509090503040504110705120906070605060d0c1e05010221030601021002120103020906101e 68
    0x34030040c0c03042211001d003a0004100c800c0c2542d028414444402000151420004018140540c40d2001c1da41102200c007043d00d030080440c500324155500d6030041008102864441002c1502d0140303003d6858489e1000c22040310441c02511086007014000d005180107102c41c00011760340d00c2800c0d103544041300404414000e052081048516040029107003c00002403125100b03010300c1100c4080c03540c44190803109852804074038a0702c566824004001d600c525410810301c0c2c5001d207041c0c030b20340b58982c2c0105064400c030b0f03001c861554030002801e600b040010021810f40802d822001d0f82003500358400510035200e5038801400703450316440841c80300d581c0e28540000030b9034032011940f50b030b555804081c000074012501500c00c0c450044000601c80d4000300d030b01e1449400b02060072552110007400f0010942000d00924118420b041d0034019203400781c0f000341003103035403500d41160940c5144100302601600030b002500a1340d01c603401d441c0458028031035407407291b070800e000e445100100b0000c4800d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 721685233 1250 721683983 721683997
    0xf180721080d180605060306060906130905030310031a01060e0d06020d05070c12020106050609130e030c0309151614010e030703090510020f060c0a0c02100e01030b011103070314 78
    0x8a458081d0f0015a1882c007003101c00c02600c0380340c00f071103182da4078010035417038480860310140c0060031000000c0340c502c0c1c00315034a034505036580c60000b110b0444c0d854040c9940c10458003040341c2024001e00b4414007400e8409287c1c0e07125400c06d0310030036606100c0c00810150a00711424082e03200c45240904001d019015201411110801004185010030700200311000d032101c00d0304c10380003001004000f2803041c01058203491028100514200344801071040c41580c0c241421029030b038038450303040b0b071078400c1c40248a40180b00d0b00864030f4483c4413041003072441007a14030103048d40003084021a840b00e241424240980c00200780300d152102c100c107403405001c8840c45607400303000002c0c540c420540c00102c4002620010749000f8440c190b0030b40d040c0c0c0d48032020a00003105074851000501500d000c6801007451000074541b103d030408160b0f02140e1141001240326004c00c908000030007040d41d05d4801e851002000746040c04820b0004c403146620791080760b10160400100070820200f80c44002e007160a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 721686483 1250 721685233 721685257
    0x4032310020705010b0a0806150108040501021e071203063b07031e0e190c0b0d0c0305060405040c05240c0f1207020102030a0c03020f01050f18072108 66
    0xb4822007850001d0080c0900c0158a12440f515500451100c00004409210700005403006c10341c51156401581c0140008108480c02e6408005d844060605007008907107904121030346645031001340c600300d0540d90b00ca4880208052030080b00b0030040394807002201c41192003074403500c1452458800081c0442c2060490751000b81303c0d505105802e681070f4443c7c035103255407006810224003400c40d040e080c1c0300d000004600302c0e40004045c15032114590441d44038a0700c25400286030390baa60308202183d07000389000b51241ca0780c642d81c4000164041c06030b564010012a010486440c1c030b40d44800c450301d10f500902d8082d07448484203056a130401035404203042da01d90702075034949000541e1a07a441042d2060b132203050041440c000c4d070080100d030580d410f2990580182d4184084500c00316220302000038254214400c03808150089403080c800d650040204a01210182c80c1451284a9543e034421613200e031940724400c10448034201e07540e490510540b007800364141c4000307414603100074050181c800359 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 721687733 1250 721686483 721686487
    0xc050a06050f160c12260108100b091335130506120a0504020406180c0207050316090c020a15090506071b02090a18030c0c08030403231002 61
    0xb82c1420315003000d01c500101070b680a080245028202d51000c24110300910708071442168603c094000c0c15122113950f00c0400c0440001c4844104201c4010300383c7c04003003170340c020b002858100d150f14090480c44c0c0030180d5012071217003040d4840751140003414001500c1c11003140848034518400300d5650341500400401c006100c03800000280c919448a900d0417510304034150000313800d007000c0c82501c10120701100308000be5950201010080c02d4000e000300e81c0031b42d407120f010170103c880350072aa82d008a5404005803005000340c0291600340c9035008203211754044100d445801000c5003411003610581d040100e20154035036400e92034100c4140b80140002a088121604186a68461341100d0700500855000b611900744c16650780800c0c40702d0401c0c2e060400000c10141c10704004a540040354808001980c0780303c60f1911b04810a8560224000b64160640702d06101720a40210090000c090243d80303098a10795841d5003188203902d101e11024200c0240074100c042c20b1010304a441580c0c00159 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 721688983 1250 721687733 721687741
    0x31d0d210207051810060311031302030111041212050405060a110c0a1203080703020301060c290a020c06060415050d03020a0206040906090f0c0203180a03080d06030506130c05010c050a0605 83
    0x1801c13458003100c42c40c03458000c80c0000580300d03102e03010f0042c00c3c3c0e035585013031482c5d500e4400e171070342c0c4007160f40000340d805640b2a8601104507450701c00500040c0071810a118036528245001d02c0013039044c9155804219061009110903640c0008440c00c0c0101400c3c42e600c00707444800103a04040350320108582c840e808502c005200d40ca04401a845c582c070940c1c41d03a0301c503a604401035080b03000078050600040e80b490315040c001040005580c203e003000107190f01c0e03801c5204114a03010b40c1c3c2110220086500441c55504205040242d550032401c100e030140710020440c910981201941e03ca01b074420204581038100b40760003031044081380d6802a2500b90b8440d19010054060000c43c40785c4c85c44c503442c0150043c0564010f104407452128640d015614040e500d8103c60b5081d1701d4080c9150340018040300000c0000c0160009101d1640045e01c041a211720f9414005e091080051035200c2c644111101c290010b01e5400c450340c00e8030805d0810302100718080c02d1007490002c0104000b000e0a140c40140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 721690233 1250 721688983 721689019
    0xa02010e0d020f040228090e0103030f1205010f08070509040209060d030923150306030d0f03060503031801020d051905032206051006020a110409021804031d0d21020705 74
    0x41b4408031458600c0580c20600071004849008280c8615103620704c1590042c00002c0c8552504003880c40185816140004000310b03880840f2001c1e032142c5121005140c040081d00014800000181300840310000c1e1880c0c1500800c1c003400005000341d00c190b1445580608141c060444440030703007070318411041c00d00884000701141023988070715648144641e68401c046e046111080f00c0c031138407000c0d02419001003582d07001d0702c2c4240030404100605468031000311b035648041014000f40e20100754000c40320030031200007904062841d0600d90410008004050000e4909100042982c4041c42c015079641d84598800740200000891240040d00420240040c8000b070b80180d8010b90741030300e45100040d6030b0b0301c0c2070b66558400d503802480808950b0b00c2ca0b04918041d4060910f03140041d1503280c0340c9100c0780c03040130a02c00440f0704801040c02d60104000a1609921385200300ea000c2d61801c4500764103440c2d00341c030202e40c1c150702c1d848000c01c14001d400c528800c0c0b00001c000c0401404a0b1841901e000503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 721691483 1250 721690233 721690267
    0x6310e0906060409122d080406150f0e0703020909010312090806070215090a0212150c0f040b03060d1e0201030b0303163f110a02010e0d020f0402 64
    0x81000644180d201141e2180342c603100d4002c400c0d900c10070020546004060176101b02c0441040c0c0c00d40c18902004040003a0000d03244142001681d0f42c917002030307150511f007413000c44942d070031031004608510700c00303019002420008809464031000144019034400b80102c010b032103064a07068101c3c4a49000104100c1c400e8039804010b030707490b00e41212180d00c80c40c88590791541162810700507480032400c1060519030a4a042e00560001c054500803a003035001728209090501003040da540c00312044852900000380c0003034000e02e070350b20000c0c036010500311260b506005034000d940d200308002000c50346564a11001034400d03680007440074115410700254880031765801030140c1c0843e080c007041c0409842d01104595044802000400c40a0a240ca52200c506080401c81a100911072443c8401e0f076000380c044001e00b8005514032900141c4180000d1268403081c508216952005040a00603a0450440b6000f41001d44044407880c0c800c0c0001032070100b0030b80c800d0f0340103440082c2d8400090301ea040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 721692733 1250 721691483 721691491
    0x30603023a0f0210050304120503011d0c070f060501060314060a0312022503030f022e0b0607050c1504030b0103030e130e0a021002030906310e 63
    0x280604100c4014200c01040c840040c69003500c407032006000405101c0141c0101e040c580200707242c0407081c0c00755000c03900150300c42c2010720102c0d40c00b004210400ca0040d80b100d0200c4150f00e0864215450107000d0340b074495540729040c07200000040001c4800c800c040c1a140741603045078488858001714103003d401440207004010001c6d0420405403809801442c074940039000140500c1e154500d907850b02b02c00300c80c0c09480c0b40c04500905080381844007103c004020744003042c400010300b240c82c504d0042c05007810a0404d90942d000001c503081800c0c00c1440c42c03100003180a03440500c80c04102e84001c014464481d500f40e100101044180620100069503543c003c005d90f201d803561010702403c0111801188001048038040d82c0040c80020301c60000ca010902001e0a141218181500302d101501d18aa81030ac0f12580078004450070344c0303400301c16100c1e01403d034005546020032480c0032403000c1c03091908031021098200c41e002840c030116000a20b810000390031810380d4544540c0e140d604030380191 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 721693983 1250 721692733 721692739
    0x15030a0b01171209040e071a0301090b0117070f12060e105315070302190507020d060c020607020106060e090402010e04060e0a090c090605030307020d060605060a03060302 75
    0x41d81c03030b03589004001002c0340040c0f4181582c034101103407142040003405c2920829038030303030040f61000500c00b040c030240c0d00f0002c5a030340301c4251a5814140f6000444881c045410b04102c1e0540907491841514001107810220601d00406e2661003044107a900e0107c2d56504080e1a14002000401a40801c0518002d042407070030074100700ea17150110046020542d20f001c10340d64a604120381d41d0f904448a1004a00704807102808284036041081d01e070380c8079101007043c01c1e00700c01588402404401040e07a400710f02c80c1421414007a1040840450740790f0034012209006000502d0415942c500200c24039650303002a0622425100c03620003502c4003001ea422030059800c000c4042140c6003c0c40e00104000d402810008265440f500119800901c120403141c0082da07600c40412404400704c1128400e0011480100e800c817200d00d000c40400030b10f548460242480c02d1000e019a5070b010088600c0b10b601255941e468074201d06145000340380c554040ea40c0003100090799141c2c1ca41507002242121300031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 721695233 1250 721693983 721694009
    0x307110f04110d090b01170d1d1305040320030921010207110901090203010803090103020702122d0a020d0b0403182705060d120c0507030818180c0315030a0b01 70
    0x494102d071301011f0700741441000750824182015018400c2c6000110020400c9003209195085004218501480500070056684800030842415001038110b5001d002c80200b44241a403208c2a007178172400703000b108a100b0001d424008845c980d0382c8440b07000d41c00030080219981c00322071130800300160031a10f142d80100c05840000a1810551090340d04a0300c044019528086d00742004400a5100c06c20403a440f150f9000c01005002c02044080080004105050111521031390300c4110001c03280d50031030195000c14a0000140c40303c0c801d8050b0303140d22501c4c503111030302c0c0c51400703440050b001c0040030605d50031000002244d040c0100840e1440c4a00000184180249c542d40015500129403894108a0000c09000000c41d14203900010011916000c60030b0b2a2582c3c0700d07401c181507a88250342820b000300721448a66008848025400300403503890054130b141225512151000a008019401012001503802140000c015a0300c440003015074501801c1ca15008511761000e000729080c0e8404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 721696483 1250 721695233 721695239
    0xc20040e0d030e0d0203030f04031b0b1b040506160f081801030506010914010e19091509061a1e0313060f060f1701020d0216050d020307110f04110d090b01 68
    0x404d00741c0c40d2401550286185594180102031f2201c40035100b1000c00594202d0010811480401c0382c10f040e1144800071120300b000e40a16010b602c203c0c1550f5108a000c0004000d956142c3c007c5817007488541e02e858001c0e0301c1c0380c01c105040da0566400038000410000b035000c03100c01c0d0b04041ca04810342c00d0301c080080703440ba4001100c003590b0750701584030710200741c580d803008540c014008441c5140c4000c1070328180c44405890000180000d5014807101515900c1340b0303601c034000c401d44201500705107008014807403915460303c1e15038105440c8484070600000c0e11108101c207401e0a00c01c42c00080c0c2e602036036810040b0f001220030301d02e8a000e03100b151402e10700c0a80003400c0c0c011601296142c040d41101c1c04e0601c0003814010355103500021441d9130030402910860075a0002e41400c2014111071903003c4185d0614038107100b004203003a4215013040100400103000604000110141a12610600c1004402060003807103080c003a41001c01c000b049201c142541500a40800780c8034407001c0e40070340d90b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 721697733 1250 721696483 721696511
    0x5040e0f0411010518120a05060a050403050405010503100902040e06120c0a170f06070509011e09060e0301090f0c0515040806040b040f08041d090309010c20040e0d03 73
    0x415a0000d1400802520b500c0c0319600c103001070040080b030300a0a9001210b5100001c04110007184241c3c03480e0000340304001404000d00089510072880042800145041e41d4010420b1203a405080d062140c08800308442038600981c140142106881c11980c450304d17201710502c491001c036002403083c000381e030021860315008540c4d03810084016005069045c00c114a000600c1c00c0d00c4041c0d5401d02ca521541d402c080c608101d414000c1c0e03880c1c0c80b01c40e502d11309071000400050804408080102408007074030079040e0301c404a0421a142881c0c6500005c038800c0003c1d000d480d03c407201801442481444100380070348241b2000071100125495150f41c20306800c200b459001c2d13032003815a25003103000002c0214805400381d99026100e4124940d6400d065502c107460798201f40c0100d2840d00058044840d0b90203515800b540000c4060000c42c28074040000003028144aa08010080f00d440107001c6c40303120004500740701c00d80c00240180540b0102060042e9030b002c41640c200000780c10105130b042801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 721698983 1250 721697733 721697761
    0x10060611060c031504020310091104121205040b0315030d0e0a0308090406051e040c1d010f0908031b06010b03040b0112030509100c060b190618080a0305040e 69
    0xc0c69010142030385540e00e501481c1c60b604014143e44a9594001c4403500d10355444c4000d51041c400b0407184075000342000c15100c212011503020b0001c4007810003050040030715810780c0001c001ea104000329455007001004580710300841e0301820400038044103029140c02941403403c14080141d0444202100c0381004a03544541410031b0354201c104102d042c0b020405203c0180038441c00a4804100b013540c45000c40c0849071000700740b0b01180c18000084c85145840d008000e41c61086107490044545a0395000b025461000401414840038030035500c2c0c403500590304180244103401c280c80d00c43d46c004c141040c500c03004001c800683d0207000d00108594040000b503030b0180c1c1c1c2082e500d140f50703030a00300700ca40c1c81a41c42c1c600f130b02801000c1c0700808055031341031190700340850582e90320005050186007400a640402d0b40c0c00f403180300043e5449050a000740c1c0e801c81111014504024040c207442044001c07100f194015035181c0c02200c9481060640102c0244104c4035441c41040300390351132250802c080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 721700233 1250 721698983 721699007
    0x3021e241005090402030c100203031e01061403100509010f24050919030c03150b0301060302030d0e281a07030c0212010f05091e060c04030201110a060c02100606 71
    0x1c006a007810301960a01c10000340e072003403000d01140d480d401c034500015031a209800c00b410040c0d00c000200701c81098000111a0400c010701c0c00c0007580c0d410b100015020f00504582000111804000144621040030040740240780c06810b851440d40c440d03a490b0450011402001d90b000c2c100b41c1076107006151240d416034682031a656090078041d8140400407010800405030a84415181001c001f00e80625200401503200d50b0400c0e1500c000c0607402800e80e8013035040c9500c40d9160003401c102680300401e510342d12a8007450040301c0080c0c0440002c41c0b00080c1c1508655030040780618880f0741c0b0280e003074007060390301c0540312681103200003103030100d203221301000240090794001c0c0d010b0040c2850001e00704044108000807452070344605031801291411030300b040c907a0f0700500032040f051480c000843ca201801d600a02032a2902d03045007905807245100080c10001c5410b24000032160074043e5542c22544070300144201d5141c200001d5842602d401f100000328900000061240c1c044c0d2816004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 721701483 1250 721700233 721700251
    0x620070f050616080c0615061e030c0723011404030909021c02220b0a0c1e050d0f08182d010903030f0c0c05060c030403021e24 56
    0x2050810082c4036064000d2158805284071881507000001c60b424007030b114400c1c441004140506c0d00e01101c0d401403007500c8405005410811440d90603140f100e5035100031000c4403098541c0c941311420191410310810b00c01400001c20004800c41000d01410b00703840c240b10400003800055460720711035024043c1542c0080203e4981c020402c02904c00f900501980b1a00014110002d0741d00300317003202640c0c00281c201e01c0c000d004428103d0042580800280a0400c0303003a06410b02c92045005003000942560190924000c0280300e4054000e48600d950040d07404810f48110070b1003414064001140c242810b804070318102e0002d010b8544500c8007920500328800203044102035200300348529000320001c20210012080540450f0b607090041903c0503100703950000354104202d5040301220425041e40c400c03ca1041600380105d00f00080854020107031803111540d980312880c060745010140c02c0500203030740303038143c2ca00306148010608400c0700481040200c03034803100070f6641ca010842101c5442e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 721702733 1250 721701483 721701509
    0x1504030606050f212b08070305190e0f011113090b0d08070302120307110c09040201090608130b0f01060e09040804090e0c1509010f0509010f030f0f06062007 69
    0x12025602c0540d80099060500703075075050288003a6480c40d01105d403500c040081c07082d0300b100a030301c2d44010043d9101145e03180c20890750808480d4681c2100011000c2c220701134075040c8242101d101031090003061201c0c50000c10054240d0f40860440c0e030060048034400800311440010184600d000f070100e40000144102d542c0ca03000d80d24400203401400007982103200c1c3d1114800d0590000005601841c072075142d032400c00020020f064607240b9106203185c003034201e4006000042c0d82103c0d988040d50f02500b4549010b689041010401085a04c006089001c1c8030050100042c240650326058841c1681d40840000200040c0b140a0f04142c070000c0c0b41e400100710811081e00c40d90301148110818030140e41c03c841c0c02000241c40d88900d91280400480e001819280c1e660304809900c050080038104941801d1103680060a409214105c00b03003459250380f9003504d1035403103901060b5200105d44d01081029142c0100030100d140185081e0b40d10303101904044018800041e01804590584142007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 721703983 1250 721702733 721702759
    0x30506070809100e0f0706170f180d050d05060d0f110a0306140a0b03060f0a0507030902121506011d10020102160605250509010c111504030606050f 65
    0x5550801c02080d000443c041d400d0300d00190a690b0243c5020800c002c0000c00f1030017100c0e840c06042882681c01641402031040d4000990aa401c8106038000e01f291002e0300076036a2407000c03540700350422003800d50600403036040e811110340200180c038018118010401403551480288158203000c1200649414000c1030164005800032200d04140031015150402c800c1c0e580e580c1030b06903201c080640790800b40c03101c10461411514071500184030803c40c000d08050400b040c0d03110f14804d014020041711038860001591680c000d811820b10103a01400c540404020350321034544494074034a01d04051000100490a15803148038001c0d200b0b0760301d80c41c0c0202c9650303040821103903c600018140c2907540a000d42019044c19510381d110041c0114804031f0070749801c1310302d00c0d0754040218440720402007990089002c00d07030003401d41f0440d0070203082502205c00142042e030464820f1b41a8550b22240303a0301409004403807603001c2c00c00c680c400c00082c00019110001c0256078880c4401842d08500041e1101c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 721705233 1250 721703983 721703987
    0x7031806081501051e1213080a050306010c1a18061009050402030a060513050d050322020f150a11030901170a02120406050117010b100f261f03050607 66
    0x929480504089103042100142c400150070f100001905c1e04201003150a064400d10042c075502c00629100f20300007440580d202d09580c081c43c1d0b000c4041060207c00155580d004a101c0548560840480786500100a80701080c00f08216102c4e02c090720079990b00e1040d448009005806015540c9000144600b86031010009182c01041640c3c140300b60000784011408910615004240003660250242214101a031409500440382f42c10000704008001481c09407072849000001018036400c1e2038003003400000c0d840c40440c00701d181d0110b401d00c0011201d0040c08014410104c3c1621107006544489944a8490040034019404920000540f030780f960341300c0580ca54040039003c0e00606207031315403145034202c020132601111900e03503400050101812090111291511002c003e202000040d0301160b5642c0204407809c007444040c400800303030580940032441108009801c51072588000040412050a040e10700fa840c0045040c0411a202c0c03c00c130201c81900e420000406550710389082c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 721706483 1250 721705233 721705261
    0x1b070b0a030e010e100f0b060a02150106090f14030a0b070e040c02070e010902090607060c0c0209061903060b060906070b010311030a05060f060607050607090302010305011e140a08120703180608 85
    0xda50343c1c1382e444c041f0741140d54850000c3c1000318469030060071194055502c03009825030680003070081c400440002c202028000d000e40058618558036000788150040110f49404000100103041c140808204880564450413105617100210780603c10862031000a0340c40c1e400900640361104810b40040c4440034a0360001c244a0a01038040d0f071502001d900d52030200ca01c034400180c0020701c03000e400341c10f6142c1051360540022049540700340303080c0c0d600128918001c1c244002000b003030b102d4000c5002a5500ca05446d400c3c24040c0245907070f06030a00c1c001040d08801d000890700b020403d00705000600b000940000240d13400002050a85c9401c0800c0000e2800108082d50002082110100003401440110301400b00c546440d9400f600b10700c00501500d005130460001c060240c81c0800381181e55410500840304401401c2d2030741e069000c041916002180c100030014411582c0c2100107420a01c003d04070f0070b0107960b038121309107202c200c02c19641900b446600000f0780b40c0d40c042500d40400c045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 721707733 1250 721706483 721706501
    0x1003090302060f1503030a02060a2007060c0201060506040314010f020a090608040c05040f02030f15181306060b030403020f0d0f050a120e0705130b01020d051b070b0a030e010e10 78
    0x80d0002d584c0e000c0100092966020389004401608041d060142951460080149104180303410418400313a582c40c50306140612107001d0041d9803508005649503000f03602c4900500400341a42c1e5030b494403424401201025030b55240101e62a1404a41030a01d1901c00e4a50300344c2c0c00c2c1e581800c1c0750f1030030004036405240500180d5503081644d50010f41c035529482500e818511b00f0301d0158882c6810243e0f0b4005c410300138099022003425605c000482e584200c1d032a40d1405d20081102e803551240283d2041429188400a00041c900000814414a59406144a0f510075401c490f10070405050b42912000c20300c55043c04929041c0c050064180148040e0101c00014605840300c810401f140308151031181c0c0d8800c42a8002c4c400c1441507041280e030681404894a609000c554646030000750354034468203207101000000301c0e0404010ac0c80c205c40803c1301c0d22400071503041d40e4803416915419484074012201091034003d02c441e203d44113004d40d1210b8540e032009000030309145100c81c806824402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 721708983 1250 721707733 721707751
    0x9151009050402130303081521010912110709060f090e0a05011b0f03020c0c04050c04030f0303050105010e1c080903010902120a42020409020a030b1003090302060f 72
    0x3400c04112030301c0d5403028107a00985481d80003078061940c18080c0c042c4034090580584407810400141c101c5d22034014641106001012010240c260b5160f21401001542002410340841414050905074040441039821684405507500c840c0d460f100d2801700c48091091148070503104000304403416050b44019180340c802801e03111a5011341c0c4d101400c440b800300d1084d940d039420018148007186c2c412040d2200c0003050504514100ca880141f0741e4070044440424450340d210000500303c0c081607419034004540c0040950700b000503030725001d0080d081c2405518001340d44030250303c01c9440c00804511012188110b0706800b030718103440d040050703846181019015900c850341d00c40140c54680034105224103901c013810f4290103038548482c482c2014190701c031540c59000011040010b4080c26910301d0744040079152035451001590310080c0c02a548908031280c404107000ca50280c06070060030081070111840c40342488219025011102400d20107030060780240000740d21444484840c981010040f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 721710233 1250 721708983 721708997
    0x60825081b130b0409060504061b022802090a1a0a030201050313031b1109070809060121062c01050108030f0304050c2119020907080a0b0307170c091510 67
    0x1403c042000d41d121311600b1108580e4544c100f2052110301c0c490030400c00030304583d00c40880d10b6544001c0d6501f600304104003c10195030310045480c103108204201c400d81c00741483d0210319040a046009203400c854110b0000070f0102d15180619017003e444041e00da050310788a007140c84418600001c2803426104a0601c244002c08007401c2e00c80b007403940d0b07001d44180f112020044400c4140a4001030113451b40c010f00400800307020800d1408503103181074800070705007c6035045540d01482913002d00c05501500c075504e49805001d000510112a074041001e01d0400800c001c0204400c03030803503400340305442c2540c009000c1c0400084800000315085170058040ba034035101601c0005044008001e104842808070b8042c060359000140400003e20085030346030083e1007050340200340010001044801002032800001d40031f6200c6920044001c00054102c860203905c034a030080840c891001890a9441050b010440c1850030903c154858084d43c6409128048035806011091046080040030f01c108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 721711483 1250 721710233 721710251
    0x10603050118030e040b0d0212030d050a05041e0302030d020706060e0702060106140301150e0310110901090b0906043008031603141603060825081b13 66
    0x400d008003801074081d07400b19000c41c41607240141c1103445103aa0075004900b020b001c1c80c4555039800000428130f07015078100921540d51280241540728400046c600b0510348014480041c1c80b560210f840b55206141600016080e001c10403030f403519604008006038402c22586044801c0c80d005072101511070940400c030b00d80c03684480000303100c08a13501c1d030041e800b1034010001e00d03074800c00709000f04400107c62851941440042d0705030920040f40502071003844803c0410a0b1810802c041301120340c4c402c1040005100b1005458030344c00101302038001800403101085c0c91002408a800700300005003803501c0c180c54811210205242d0201034204013415010018070345030641510481207108514040c0d591401d12444000300c4c03160039400040500c1c0599201d03400d80100081d6400180307000c500402146480c1088000d041c030703600844081c2c010f4005c180000b100d8450303010700030007131203484021180d00c0300415a40c2e19068000e000a45000420103c03003400e02884080d04002040004074400350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 721712733 1250 721711483 721711493
    0xb03070b04031a011205070923040c06030b061614010e070801020a14040b030f041b08010f05060405160f020c1e1002010c170903070f080c0105130305071103010603 72
    0x4142e00544100c0c0d40d80044003c030000c4016442c2c09040529a6550421015110701d40d0707480300b502400e2900c0381d90b640c02841c04200c0c541c401d07007264103031001c440140c0b51078a418031403140039104000120782042c4840616117000c60903584c0000034045806a4040369848240f5010000050ba0406541c0c0b031030068407000381070084130003a140d010005a911281100010040c921005290005690501082c000c1c04000400c583e0801002000403407980c81ea0b0509590303100b810001074180e204031074800128504190401100340c0c4028204000e00d0340c80c00c05000540d0740488200e00099965424010414040c08004002e02e2181c41140e8042c035884003c901208844600d020b000c607403240d085425890f0100f59407030800c90724070092100105040014019086403c00422040211070000d80000403c2041c1d51b01c82d40c01c4110019403501e50b04128003e9403001d41e0b034814a50030b000000308804061510324141070752640d0343e10310301481910b038230035000100700c0503a80c555211540000428 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 721713983 1250 721712733 721712737
    0x3020f090301051e0105060406120c0e0604140a05030c090610050409060e04060c020d080604090311060408070c06170a02030403110f0f1015060305040305041d01140d11040b03070b 79
    0x12258943c2003510070f00e40710b11380c45444168080d41c8291710400c003d110003580903001d283c420412540114111003000070540d010200107401030b03002400880e0004200720030a0420198800941d8140c01c10f079190310501d511080c405600079040090f86002c509a4202001c840291030b00d2403030402e00302511590103c05585003580300401500f02c0c00140b005015003445a030b22020701a00003070620904a94003c0c100c0b0f01e00800940c400c0d50307a08280001e16005e0589140320721044010b88059141520f000e074011f8208000c1500c140c2d401b0440812880c2c050032000c500b4401c11926201503079038650501010790301c010300450030440b030f90f003000d00c0700b40080090443c0000c1d04400791029400d40040d1510304070a40e00d10400607401e0001521040d040e801c0060140d8045d8540400c6d559a182015a114441c0b6840240801c960552520744c1a140040c918143c0e001015201319082e45c402c02c00200b9080c0340340c082d1280001c0d00c3e04401500d0282c0c07000100e541c01038243d40d8442c1c1d0303400e182d0b41c450f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 721715233 1250 721713983 721713991
    0x90302011b030e0325060e1515030c01180314070f05180a09240b032a0904030306120510060905060618130e15070206040b011e03060f02090307050402040b0a03020f09030105 76
    0x123680070301c9050916820309000c855208044c0c82d1b2003c8189080c4c030009640302140d41c8410305102d107a01900240c0301100d07098001554001aa5030715003017100012a507141e0f440e21a181d1081906000401c1074a426680c2c0303100498a144421119241c51490000901c200381c011143c5c0200500f60400a030100c4c0010003004050150004043d888401810300340a60481023a51070301d42c40d0190881d51490102e443d50a42c8250358a9010307a44914041d0020038050300919000b80d65174a40d50204140007440041c0d00b04030360000d114141d1340380c410100b501da00303a40c04c6901000501034483d41300300d2000907180181004060442d000410002442259012400890160080300c160840c3d4aa11540542c02500078070041406203426103800e8540380042c0500d01e1b21711a00c04d0048030441c1c0d01c03185100650380100081040040400b5000020340c452042e450081c054414002441e18262007076804495801028a181c41c010250860080d031020402404c583d40c14400c001c440d4400344100d41c85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 721716483 1250 721715233 721715261
    0x1b0316050a020a080105090d0503040602040503070f031202012d3305030a050d0f0e1302030a140403050f090a031e0c0806130204050613090302011b030e032506 70
    0x303100007a005101a28080c1d030041d80041c3c0c101020700c92084000541c0a51050580c507010f071f102d4403075160440281c0300e103505c072035894400e075540450460541030403d02104d2207000020346982e81010142d0aa401120707217652403144c09005201d80d42040c2d145c100c1c1c00ea035042d0000450124549041701220000d44265101c1c594084003201d0955111a110002d460101d00404c0600c180b035503240d031396900f60303541e00c1c04002078104904050703401000d003020004401007948046842c80b200e85402500f0443cad10380e80b40c508004c081c0d1000c1ea2201040390041d0342640d615807500c040b110859a0700c0c0d0100b191160040c48105000000c00e0441c40150804810f03481045c180f1041c0f03007800548580a0780140045405c18414488082c801c1d0002d09416a07042d580401c0703541d513580018002485840b107003102c2e0350078100c6043c100350381980621080d20302d02c0e010b01e688410315603085003203640c070661912107580b00f04109840280c4104040c2590310070714891590110460742e6081c00d5031440118418 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 721717733 1250 721716483 721716493
    0x1807050d060e0f0303100501080906270f2b0c020108090c04020d1b02070b270907020a050f0d050d0b0609030a0c0608011202180604240e07030e031b031605 68
    0x10100c061b42260100030142480c1488013030a00360ba6281d154400544500b19100045114082c05841380c180b0104091100058a40078141224080c0c0c4902200610000365040c0640c51900a00b0560801140644965800c154240240c1c015517910100ad003841c00b00d44510100c1c0c10751a62a400200128032441401150b00d080c401c1c6076200036039035140c0c008151341180b0002d200b40c03c888030542c0c50707500b9840d0b80d0f41440c071010700074082408089035403950000412010480b456400050201c4d01c9445501143c41c42001c20190a85030f0303d041d03880d00000b0354100a4000c40f010365801101142c0d000610051074140359000207868030518000466403519044401c003c0c494000c0641ca00404084008000c001d15940c006440590b428215108000c01e1401082031511a40d10203e01c441224951114000220307485880c0c03d103c601c1040043d840b114000b800f03c80c4280908100002d0110041d818901303211040c40702045114000c48591200340907020814240b4159001d4250150000c5c01d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 721718983 1250 721717733 721717741
    0x5120a02032e091a04060b10031b0305091509060718210c03020a0b0c0105011403071a070f0c08010f140106051c02040801141807050d060e0f0303 64
    0x9810b2151006024001d5a0280c1c00107004244200040d404042c02500001e0304806628160644403110800000c031010b441d41000308003c030b96030141400042c21100854020207116046054034010218594840509001004a18040c0e0040da811901180031743d60700729841c007030508950b001120640d2460f070010b418400b521790803074074141c1d030561806140380d0000e05200c5002c1c01c0d0008039404070300c00c1710b0041c0244140820440018003940d4014440783d030300d56a44181c240b1581101a019407154a014000503501c60b40f03240850245001071701400e040c61074401020540c10040f02103005214040000314005020015004021032140120030000d80c20140d80900b1032b000c1c00f22081c022032038426202d51600342c0c5161a07045995516100381e5582d41d01c1a20145180c48009441c601400490040760441d0190065881c00d14500c03043c0e54941d8420f030b000d8252800003442e61249420005041c026802c7c110100c0b196240581000702e04203242c081c9841c07030404203800e0813030303140c00101c20300c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721720233 1250 721718983 721718989
    0x3040e150a1a0703050f0c1e0106050d170f070605071701290307030f0f05041703010311060928060e061c0903030e030703020120040b160c05120a02 65
    0x620290400b6007804442c01c0c1041600c8807948280e40e00070781404404141800c031009000d04860b42004d9080a0701c4141040002c1c14a94569030744400304c45508204010035907090a03420750140541240d030a4230b032a004000003042d03035880f9007801a061042000741001189680c000c190086c03006980e072030310b00d00282118180222068001d4000401800000880c3c500c07542040e208076000e100c51301e03589448011054005029a02d10000c0180c20170303032402c510328460307801907200340d00500c0780008802c200b29110303d15210074040107090b58034a0810101c0350425001814160708090484e0107100c003c010f170043e00c404071840000305404a9a02840215840741c0c50444422042d2040c5042845400c10030154030b01048540c0a03480da510705a905041c40b81e0042400313003c00c0c00969694030780d107040c024060183c208000b028003103041e4030058105146001c031005c55140e04503003030600d50042c3c22400c452107150b03010386a005103188041026505c0000300002e02080c00c000313000e44c4440b4418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721721483 1250 721720233 721720249
    0xc3007031e05090904110f030a14070b0405030d050d021b0303060f06030c160203071706071d0108070302090d141b120d110f010c091706150d0503040e15 67
    0x2400800400f4030019289888004a05802a9111480d001603c0c480c0780415000d0503110031180d0315200e28046c80c010f020b0000c07200281c0c0364590040c0d90001303403100d20a00036071040d48101034043d031259120041c610f1042024005101403030b240503241060b1111144c0c0600e45541410005400c0042840040c3c074207400c4940413034600703440090030342ca02503404040328000e40300c801c00d40d844020480021594207002c4000a4111240d007404560300d010a01c1d9901c3d041101c2e80310104862208407000d074040322030303044030300701050f0344031426595412811800794024140603500100c503c040100000e118456105400c2d407041b00030314408a030300543d0200c1242c03041800b4012000a498107031400c2c4041480b00c0c030003406080620883d0204514185031842c1c41c48843c069520740820315000541c06079a0700e0445903802400e840b002030882140303889000507260710307042910349640340b4103900744840d08c50304541c0a0400e40c0d0a159654065200000d4215411010b81100000d6140c1610300005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721722733 1250 721721483 721721537
    0x6060815010b040504020f270907020303010f031e021e010e0609030a0303020306010215011d250f05070b010806060a17060a0207141b04050106050c300703 68
    0x608014154034050442c1c0e010b1245001c0e0030301854000413500b0600c0c20120407941030f50103034548903c044164403441c00c4001e00c80e0b03500c180700d03c10440200310300320710020642c0c1c141c1d9000c0761070800981c13550b40c8000c20500d405595070003a0902040c00d0015a807909010361550300110411000c1ca8028800109002c000001c843d1041c04203010400c42b80c6c82c00560020794503414180141cbe0783d1070700b1005078900140c030144148401060000411f20740000c982c2e54141c00c7c1c61041c3c103603194490b100000c80c0d01c1d5001c1c0d80300c440034080c60880744a0302d1090000d078409150b1070500c2031900e24161121207481c0e10982100030141d202005200350303400d0403030311000200b0340c00d903e1824004400045a40f0f8500292141c1d0900c4d0b000701e214000c0c402c00300104100c100c2c0c0c03241140c00007100c0300481d2000b038000e000752a11a602d0940006405401241155a8501c1c00303005401d5000700c2440c220602d0030301640140c0c0400b6030003111a181c47c2c20f4030050400e1800781e01c4240c2d0b000c1002e212104401c88050f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721723983 1250 721722733 721722763
    0x30c050301270501060b07080a39170a02070807050f01090902031015031d01060617040501020d02031f0501020d080105040b040b0402030106030b1f0804030c030e030307060608 77
    0xc0d103041c440125921078000c420b01c07800341d00700c10328101e418018090103ca0300f1940451784000303600340402010400504214890b0744418060110151408024400d101180203046491103021100804407035012068184110b40980c4001d404030749010203a04400402070150340080c41c00e11000d00304111500041804031101400c0142020000305506c401e13103c0c100d16030380c000c00481e0341103900d91640801741118a903011072543c0c28a8000300600140040050301c0500e186820700c481c030040c000c50055500d82d88a2034000700000c1400a4503c0c00140191403555007030000c0c007c040401c0c0002c50040d1004401000c0c0e88d007508281041c1041d5640c0241c2c190350102204009480c1c106940c5411984e00301d40c0003917842d8a100102e0081d03c0d445420a600510010000c00da01d0f0301a8455200302c3c005071103050320801c131141860003800c0c0382044074000c1002a0300290001f0310070104114154482c1c070306124800c0d1036001003451504040412200103464400920421004005540c0c184400c1c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721725233 1250 721723983 721723991
    0x160606090f0f050c0a050a110a1509110108102106060602060118090309180e0a120e030f030304020906030f060405060105100215010504020d091b03060e0f100b0a0b13030c050301 78
    0x654046d2092203003180c80001c1c020100b442c2c004c03c0e0010700055904a4002801036410b190b42c44d0035000501c850513088550341692100100294840c1218074400c40e4602075080e001d81c2090011a01181e29501030701c4885400141240010514080e400050010350018841035041101496802200b110744407560781c50079061030042039010307610f00103ea0a416201c40c45031550b40c0380e00c001d0b00c40b02d0001c101510070982c0d29020462245000e003002e0000340d0300c0d1588075010710200354a948086d017100425038010f02c0031a001d0302e000d070700003900404010100c0303002550768000c0e42c1c100b0108480603a5076800400040103241021003282d82080000d00c0501000842c1414400c0041d0040c05094040c0f0360101d070910003403015074401925103400c41f8031001443c0341d55040500b40a020700048640c107007480382410001800140101100c200b01001d40440c03201c29504100804001c204d450780028000c1001407024803140081c45000c0040b0550b484076400d504008400c40b0701d42e845a4001d82c98 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721726483 1250 721725233 721725247
    0x810061211121828031b050607020f150109020a050c06040c08100207050a0f0c1809140f0709021e0d09030e0108060f04110c120706060f0308160606090f0f050c 70
    0x130039500e29001c210203079454998948a8141121003000c0c00030b24008903900f0400200078800000b50407481440541d0031101041c4401065a0312a02c82030541081003036000300520000d051034010b485080360a140550411001d15507032468500165015600c4041d210b100703203c42c100c180620484000240d00951070640e582e65100d80e94505114060211900306c0c1d504010400484400300091202d0a8204d160030000e20b00300008051804040310b10000341071208482d8400821030080d11141c96028044051070300175403c000c1d521403e0801c00d02d01e2145001c1c80c05460b08005003680c0c00c00310701e00040009040c64040d01c00c1c011030b000103040c45500c10811425035140325814000c140262808904603042d42d407403d442e401200700c0c100b818000c40440c5103003250f05801230824140200c078240010355550740e189075441601e00000d03001000400aa03d02c1d10300a2170310044580c0700d00c100050701c950b50300d130481c01c90301c0340c0040d0070300c40f40c40c1d071000d0351002e0032030007815001030702c0c0410701e40742101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721727733 1250 721726483 721726513
    0xc0a030b0f27150603010e030912030403051b1e060a050d021b0d140310121a0408040807050604120b04021c03051908100612111218 58
    0x120060403100c4030062076000420845146910355681c0b40002d8284000b200345003034607034446414000080c1c41945060000b002d51030140200c416222070303500030310319250725442402484c9480042c1c0d14500d201c00c2200100140f4200011028619100304400b41c011110042006207400141d44001c468049101202c15543c1d030801c8602142c540c1c10810360b590643c0c1c00940213401101c54420403994040240742c0171850100da444030808207551680b01d101840070541003079010541d295414008401e0303040c044603d014150740a01c900074101811105002c41000002d80c030308503002c0382c1210002c20100446042085030401074081112140d08144c2800d03c0c14504660741034016041c000800c1c003290035520303200c3d01142c0c0200740c0004082d006119040c00f61841e0b20041041c01f107a04c1000e02c00540760b1180d8004ca000b0208480c0c240501d07031600104071188100c46002c20f859980d01c1005001c2e141900000300040a800c2004500301e143c1040c1c106500300c00c5403d1150103401018003031000507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721728983 1250 721727733 721727753
    0x2d151203090902030711060c1209030406023309011e02040e06090a0902060f09100f0807080a0e0d110d0e061b01020f0f180321091306170c0a03 63
    0x95840350300140c590707417401000c484010303000d0303403a501e14042c0c802444508a080f0000b42004006e584004805456609125640b4031492040c20f0058120142c0e00100c5104209441270350104522100c2e8072590108a16400120540c0c040c4101d0790343c4ca1200103e44088a540800b0801004003141444c7c64000c0020f04143c000300b03003c1c42141c00c1c0c000149140215130100f10178580180602d0b4840036201c0b428126a0300c14058188944890403120046611680210b001e2030402c4d41c03000d441d6100d2440a0350301c0c0401900480f10580c65104488001c081080030881a082d1a0b0b50007412a0025000da8100b070032015104c0b08004c41a1402403098035102c0c1140d90100b80310441205100c0300c2c0764424024010400d01c4c0b0b00700103001031800b603a0b160442c0608901c0d24400140881500c40904146c0d4500000c00c0b13410507441000310381325041c0c070010f018103580300d0f02800392801c2007a401c1010084400b650001020307201a03109544070300d08100008602d1440c181d070030240d400d04540b1411901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721730233 1250 721728983 721728989
    0x30d0216060516050703080318010203060a060e03210703200c0d05030d0c0c060509010905062212021c0302090609100302160605071d10032d15120309 66
    0x110000050411110f07220302c50391800544c100e000d8504a64483c903201482e40c4c800d40d0a10003611500e00c4060380e90106208076801000000c0048001034030382a4281c0340180c000074a1541400350102c4001c901d00b4081045003900581003c2d236a440540c0e181c0644413052014041c4140a1280c2c47e001803240300080d6170701d6603c02181c4e10200c0f2121458001e18602c104055a43c2907400c011141d101d41c2d0b00f050b00418043c1c4a200140846e5072039446136422200d078120081c007079070f001c1000304962444048002400c00c2ca4000b446100104a0b10f0301625068009030700c41c0180d0010390703116420403540c1404a0729400515080d860440d40c8070000e4000d00400e20041c1c4204020f122012100703009504a6070307808000488101a1255400c00500900080f00c00308041100c034250b00c551186c00c0200c030300d000080242101e2a0014106040700241000c08003600c0009168000b080c2d02e842d1300407280030364880400041403034140207540003181021507101030400f507420400c1e500040c5e00a030051050b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721731483 1250 721730233 721730237
    0x60518090a1103070b040e041709010c02120a170a03050f090a080307051207020c010f021f020322050a060b010f120b0604120b100501261504020d0b030d021606 70
    0xb0305018000080c1002020f03400211841e030300040016405805400003880360b4005e0040441350f40d0051007151a0740314403201d06000132010341440d00145010260f41c0030034500c404c100c03030114905070340d4001102940c400075586100e01040581c582940f41c014203a0000c44804480128101403541e143d4417800c80100a10000c0c021000840c82e600c20800d5a003043e0859014490030f04010b880a1340719507155030341900043d590382c030740c00846000044e204070b804413144006042c141850907860094101900007210182d00103480440700010f40b07900600103005d40041c2c00855124540182101d00881d107180c14402800480e10000740c002680021424801101180c4084988005192885a1f400c481c07024460788128900b80b149542030f4511450310b01d01400b56440c1c54000560300485400c00301d10068400d8044940380003040e2a089822490070000026240c0b03180000405070303001550300300700c140e545e40c403142d0142c0f804109c078500451a0307001400c4001c1c841419800045518090141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721732733 1250 721731483 721731503
    0x80d1b0501140403110610150e030a060c052106060a1805060313050c03060603031606110318010f0b030d030c090902030c0a08010b1206011b0203010906060518090a 72
    0x188102900314100188401c2c400d01024507203440c0141800340c10f05209507140c401c1d0300005034240003a042050690f140310307405090425a8541c121007000c441e031344040e00b502417809200c000500e54064070034a490740380c45168803001c1a904820124801c000303444e250710316042c1072201586401e401c61b82103100303d180822010801c0d000644101803a9404550490800001c20482d26061446038100c14411415190040008410941d646c1819505941c7c150020451803c6031178540442c000401e11400300401c0078090080c009029400441e11480c000324015140c81210f9800e200e0f03000209019041004003900010201c2d640741c3c90071b0b40355000d242d9034500c43c034401c5001c0d110341c000800e25690f065507603140c50500d004031a00002000d00c00314602c400007064407180d500554000050f0b54140000c240e40d80e00046601381c2002003000591f088000741640507032401e001d00b42545008010106845107000c003440307001ca0480d10070807640901c1c0d1092183c4103102190b02a4500d4004803c66 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721733983 1250 721732733 721732787
    0x2120d140f0c0f01020d0e06060901270c050a03050606070c09020a050c12070605090304030f0314040305010e0d02160f0b0702031501172b0f020f010903020106050a080d 74
    0x201c03452040e41c050301d1072481128044014920305400030406090a1802070181080300c0c0e9800343e07500000d50300d20703511000700c4006000a9041d4420922410b6070961008200e4060030a030a085980030b03044c0c1e400180300000c050b49515094010703607400c843c003510001d01c2e0a00e107403610080e03007d1500825500d140c0014900c0340980c403801c240e4035034900306c006075484401074114208290380200c008403180307411308000030390001d008001d81f41125041500c10340d010b0065541152040c0600080881d1a107044c400800071a82c00d1080004140030078004110641901001a00d00307000440f821a810244140c240404500d00280800315451010b620361600d0729803000034140702694105000d0241a4800010446585800c2da4083e00780c4a017590301c0000702d808040d0356002d29112072160b070140e520000c03d0085c890a007855881207184107880c01c60196400503825100400c0064006030745490b0107215500e081d0140e040205404001040c4815010b07138042e000b0b91809061110b000e0305a6110303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721735233 1250 721733983 721734007
    0x3050c0c0d030902040605030313031106040501081602071a0c100213180f0e0610051f0e36100806190b100306081b0307050f0604080106090902120d14 66
    0x706e003d00302c000d080d2501c40d00603010005d0f4425162105a858241794406800e81c4c3c10030404a40584406a442e840b49580d8145889030340f80e8940d1406c0300f10310420400041ca484184140903180084250031b580d90f58000380c84a161006c010130702e05085104001d98030b00030031049401d0049030482c68201d4440c42c1081c0388000141800d4880440da0390820b1060341d58000040f44452142018254139480740f9200d1b01804050100c82031546c2c6006480b65014204d18040c2c02821403a840092125100b42c140c190034410400c040c082140e40450005554044038401c0d820840c0d102003542241c00b1100d2412001654405020317164078070040c02a440041e80200c4c50300641501400540903d4202e0781001c8002c0040085205041d503d009210a00b184a0701c1203401450054005000340241410320742008400001c00b0702540d0301110422000480c0003007802980000c000c001400550103800d030050100040707405a1400141d000a114201c1c44c64001c10716503002009580000e0b100e402c54000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721736483 1250 721735233 721735241
    0x1605130212071701080c0f0607080702100302040f0605070c09110705010c080105040513020306042a080114090703080f1c02130f050604080c041116050703020103050c0c0d03090204 79
    0x24a01018030100d0400c540c5a41008032540602c605801614990781d172448919260b0342102089035100c450003034404207901c0c09201810000f03000340b01161800c0e11590006119580c02050742d80460b4011a0030865580136401d032000401160405038039102041c0d949500b007500902071212181c1c1c2c1d641e010100c015182050340c3c80d190307000008002034a441c4001501d50003007449210700c610304107400039511202040400c3da80b9940a00182070783e4a03650b448e171200303148080c10680c1412000e402d0039880b2001032095001044ca1000004003111100f10920807040018509403a41d417000342c0400c009024101250b00c0c07013400d0829692103c0a2111402400d00d000040d28003460004c20650216048220081c048940100e0b108040b640e5981c20700c20a401540f144d2031450b0003480307000302e150600b81c00c0580c8201c86800c403145020b101c094212010900250f040c0c03100e40c0071102c00d104658040c4202a0400210086030b410481002c8015613501090b01c0c25100709512810504115211900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721737733 1250 721736483 721736497
    0x90d0f0c0509040303060e180316022701080706020f1005091504050609010b2403060d06060323070e0412020a0c080109150504030e12100507030b030d0216051302 71
    0x2c090b03002d05003810010007500c030900903860001562004990250303002d0316081c000c030070020040d40c242010030400c807410340003684059802040c6048950a40a281c1010700c3d41c20f0300001510700c2c1541404801072030100c85401c50f45c259400805141c1407944001080403201401c600302190302c3d40e40d2044c050400d510b07043e101d442c225015017408200030700444c0e4144600002402004004106420000d18511102c03c41c9104c0e04a00800c00802d02d0345030085500200c00340040d00b500b0340596812046410560042c0c840303101725803140140c8a84008110312001c01300000b00714250a003080b0103010000504020600d1403008042404e9500a011200000b40c20410807040766075036210440c06000c1900c1c0c2100d50700082002c0003020040c500c14030b80140d40541c1c8138416038108005020b040114004028128442c0d6052602074114a01406101d07030b03c5550f000c1503110b0010141850508458503440070b5400c502e5003c5000c070354141d149021600122500c0c81d1001d0107241d15002441400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721738983 1250 721737733 721737739
    0x2010e10030209040c05030619271e0501030308070e060414010309120908070801020c060f0903040b0a09060905091b1c0911031e030a0e01090806040606051203090d0f0c05 75
    0x8019440c1740d4100d0099881158281d48941500c54159503142c11140c9500411055046031440c6544a071a1030f5000c03c075004c0603840006411101000845214440c00c041801c01a114001841015441864a07400110354201101e00510203400180d0302e01a5010701c0c100411150404102d982c4280c025480181d08141d0b200c21140800000030000310560141401d2031040480000341e0580520889400703030031242c06056075444da5503440300c503030201034080384481c4024803010400f00740a0004141ea90340645803e011245000c6020b00211701580c007481c03296100c04d041009204a00021007108460000b003140e0300c0c000031020721031445506004d07076907043c41c0c103020008000d00001d000b0302408084003240d440c0c550030f42c0e5603008144c100d079845101d034005110405c0650300804d107501d180c3d04141000c07110113032281035162401404650035280951203a404011901300306a950803100000000b45282a1300300300841d100c95401c201c000c201030b81c0e144a80301400040c00503940502801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721740233 1250 721738983 721738991
    0x191b140f010e0307051c05190302091009050f0103051b0408100f05010f0e06010504090e100e06151c05060924071e180803040602010b0a0302010e1003020904 69
    0x56508559211100c041022556181c501c00700400300c400426103032019400002007019070b5000000f0740046a580d2684018882c0901040300040c11032840308000102e590f40045c0c42d615180200a50b4034401940708081c0002c600c401e00040e214003142245011080c00c02044640f50b05101421190038041d010304156030101e8003180c040d0b408030f098500b030760b40b0040c2880041d030040040c00403610203200c3d20400301600c5e00200a030f46178400d01d903503003c241414194249a1384001e4242a10400d903c021034580041e400100070350410320900c04140c4030a4014040da10308015203044034100800c5841c13181035844000501c0315032503038446c00f900340e002095a030ba070f003000c180465881b0041840781500040901c0d5580c11038500365041c0707204603015079a40c0d011031001411210409600034203001000034030342d00000410100300c0c102000303210010082d80c0c1d55181900c02400c4808221440d072092140450400250b80e103c82030300c00702101103810071004001404250001c0c86020b00141c2c1050030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721741483 1250 721740233 721740263
    0x605180705181906031116121815230d1509060312090b031303050d0b0405010605031014090a2d02040f060201180b070e0a150311191b 59
    0x610f0694504440c0c440c2c505201c808500741522200d130290009940500c40e43c05400400304c1d9a030401419922110700740001c0500e40003c04441d01d6115811141e01903a4008030b01403504e6012a10400c80003004550001d0040c92200305d811078440e1880300c1c10a01d48451103420b100c0340303020140b0000e240c1240c0802140d03a0340d1804247e1a070340030358070902045908000049900e902800c492050311038840042c400c590039a000d8886400c40004401c24030b50f01c01d82032840fa1075034800e841c0a04a40c0e100e00d0744920348401001c45842c1c1c160440d80701c10560383c102c90340b00c2e100c51211540055080e9404112000906010001030080041c41c26243d01c1c540ea900c1d51309651640240103907042521000c500944a0009074242e42e0301400f4000c5604144030200d001c9404d10401c0ca81221a51526140301881c440003d00010710301e80001944441e00034415145541520a40c10500382640e48642080002c0c1da50b0003004030400303030700f400b030000100002c405c80c10b003c0400c1d1495540400903603a100d103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721742733 1250 721741483 721741519
    0xe062107060905061e0703090e040f02040b030309010e060d020f0f0405190303020c040e01060b040627030c030b040c2403050603071a0c010e0609030d060518070518 72
    0x1640c1c0300307800204a12080c0410241041d0741110702408903a49050700b2403203104154085603008440c00c2c0c04000d2400e0303022804501c0d25000c81c0c0503030302424a02110181c503004200884144043ca6840795100b004490340c1641c2000f854800000700300c0e2055110000c4144000c042d02c1010824140b000780060410080c1c18200041e209880080c1d410400700c10700b203444540040e04901020f030160b40041e0141101e4030b403c3d008408a81150000030960655440081143e500584c00481c08500d52210300ca006400b60750b1000c07100c0300341c00026114180755440300401e454940c00040c00c40c480140000d010321808011001c01021100c20003010040c18130105070744a0390202c40c80b0000b0f420800801c2041c0350002c9c00c5004d8503070781c41d41d1036419407490004101951041440b22015501d6030780750141c000f01030004600c901d031030030003a603951103410400d003040b120a074014501c6603c8842d084104801145c1c200c0e948102c960801c566609400880100341d4aa80c100c81e50b40b024a1503030502c4091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721743983 1250 721742733 721742743
    0x50f0d0510080609070b030f09070b0d0f1b0e1003061203050c0f0c03030901120e03130305062404020a020a0b0c04060207080c330f0318160e0621 64
    0x48072a030070f5480b661920103040e03444055900c40c0440004061010401c00c1c0980c25800d9000250390003221b604c2c542e141c0000d45550014a03862a440ba6107050940a06860740100c14007801c40c2452040400d06c8031401606846e03040f1441c1c0c2c05070748181901101d6901030b40c0040090016103101e100c00f80103905d8001c01660203c0940300042c09125504200414001071009100d00010069820810854011a900e041c55848500d049072616100000108288010100c12101d00c5084100f83d086040c040e04e04030001c0d00c50745600204061040840c00c5102a00c0043e55040310050b0f41c40d044284221328003e50b641c0082c02400070203091110250001c0014003c0310415000d03181e220303955000171034907400480c0c003160b04101c1d0003a18240c83c60142c0200320346041c0e20410705150b41c0b00c00d024810325411620b00c40060600c008184130300890340c030b10643c440f04004c600030035a46050703041c2182d45000a03c9840c982d407880c2030101d250340c2e42d841d000c103040b0b901d1b48503014034072060024115610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721745233 1250 721743983 721743989
    0x10c06020f0a140a08013b06040c0203070b01030204020f0d050a0b030601060201110418140c07020906092203021903051b0601150810050d030c03080105060c0a03050f0d0510 76
    0x4544480301401e600c5100f5000e40c0c000d45807030b4855010aa181c1509a5812122030b41800c200e901851034504240f49a281104038024207402c0f503202d42e01c4d00c030702804100c4046081d0903081d03501c01c0c080c00c0f00185d0f55115075410f60f42c3c150703400360716004207200c02c44003405030010511a00d130805c01008102d506c1070744a1014144110704443c5241da950f1000c1c0e0884107502d4021844003400c1000380711300100ea2680d10040365800400149040d0031410b501c0b00c1a10a07603030240c400d40c000800c0740a615041801c0c0f80c000d10201c0b0890024100781180003a030084680c15140021104085a010b050007031040555404d0f9440580b180f1007028a0000d0030399200c40700034011080304680307a104040c00002c2c0141a11303c40010f084001c95440c505490862004126014081030414041450307120304440c865610301c01c0c1c41c2c04030030385198500074040f0740058110364002d02040c8402001c1d51030002b8203600300c64042c00d049540b4141d445001907148078110410b210035040c00148828503524030389403421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721746483 1250 721745233 721745237
    0x51906090b010e0618101a0d0c0203040f0617160c060606090812090d082d0a08090c010e1327050708010b01021c17070e0a12021e010c06020f0a 63
    0x4001c50700b00e00100c3c0003401b0b450090428500d0b040501012106c410744402011910000c5814201501910005d0303629680d11400180c0020030100309840e031501400000c0c2241741828003c901c10781c165030700a10b10082200c85508070643c64040e1007401280843d01c1640c01070000e0246907162f24003d00006009e10841d20030f031140c00d10904004007500c0035070360a0b01000740100010000f90b181d01c40c80c0d4000042003d00081c0e03443c00c200120a800c589141040d00c643c02d0f640e207603c003002c005448154000c0c8a20f030607401c00201081e450b82d0040c6409602c1c1030032200e01044446400360503004284c84002800e40c88070f074181c074010005414030309810440c442e50850b140306440d6102e507030a0f2002110400c1c0542e014956810840d1020060710410a8540c91b04034400a03104180d0382a20300b05a6404011401201138041982007100c1c0482c081c0004d52032540d07090071103902007101441c980001e03c42ca11602c11500300745a202e00c40352110180c0004042d52a0107200b41d40410381c2c2d1101e140100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721747733 1250 721746483 721746499
    0x10501020c0405160c0503120702010f0b090610080c0f0301090b0f0109030f062d27050604140c0d051b0103050f060d05010b040218030613051906090b010e06 69
    0x490300c1c09003e8107106191303000f110030300400e2984081d2013150020008860500090000d085403804038503445200d0700186e80046200c50480c860001140c1110072058090341d0b901c000c0180d1030f12200341350521460396117440945907403840100080d0740142051414040d1000000040d001c130300d608800c160120489525100c1003040c40190745007541440000c10712610140780c03401003613030741c0c0c095110381e50f02200a1024404c1e580d90166869900881c1d0490300b03968444111fa100401856405500802c881400c44801c0b15141c0740c1c0e44200041c4001c1072004000581061403005000003015160b0140c41600004168501283c5803003100c10005021041d040080b021580f0074003c2c10301401c00c1044818482d1500401e01c500042240800c0d21103640302c464011280d15144000c0050807402c2249450f00740400040604000d07010300028161000b030078100011440101c3c5d5030603100c51860444c0414151450010003a02c403604001c0d154a0080f80001004040b01d101c05201b500c080340c07510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721748983 1250 721747733 721747753
    0x30224060a0602011b050c160306090b0f01270603121d0108060d02100201140c04030b06030102281707120c0923130213030312200a030f0c020601050102 67
    0xa08940c0c0b16241c1c181703002e440056007054140100000c0903001c55650503200103035645070320340040f03400c03903403007204d50907036851002c8244520240c0a580201c018400320040307500d4410b000c41d070540c00e492801d03081d07c0b03100f58154405019038000002940e0042190790103002c41400035269032521103825241ca0104800141c280d8403986140744a100300410940c6015116001e224004201001c10000d40d940c5040b40c1c20a104074090141c070540754071001582c0d840c01d501c1c2103d0503440241c62640a40c4c0180405840d50440012001040d1a048005142c40c405120210b96903040044440305480c81c2405204126030301c03e40030825909030721001c1c0b03c5036010420448000159128511a100092200e040207a60600901e1a0740000501030700d64210045140303412a80300c441032803aa2407100108104144d0819488202c1c0300e40702404101303e902400c1e1903103403c00d041c00d02c4000701400094400605000c1d902041c1604011641000001041c01e0082c1d0b5580082c0207050261050385840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721750233 1250 721748983 721748987
    0x54b0d020a05070308072609100804080d05061c08091810181512060501051807081e040606170102070c090207050c090a05040c0906080d0c030224060a06 67
    0x755603001d610900910a440c03464440010b160092902100c117840d049009003134000e9403400c07218100c034503083c607103507500e49203000c10950000070001c2c40107010401e010440460b810100743c503044032100c0b201041070380d21000000c2c200c45130382031000c1301c800c00d08080109000000025180c0350350300b600c10181c01c1c04c2050141040c0c450172a0716004c0c00c0f841d080305000c014100c3c150404903000d0f80f100031800101c00a22002d0440d80341c2c0100982107040c00081c0103208290180702d00406041d102c4030b07800200c0201d00494848014280e00621101c48003041c61903928052014010544109554450500d4075066001c0d004c02e104000484102101c41c40071400d042c03003107641e0b150340f0406003002ca07450440384001079008080142d6050040041404c0319403200d5000d10300c5801c04440c001064585860243c50444580d04071130201d601e060801d00c007980000801002c02c1480e402c20708800c96081c41c1c100e1038101e00100f0300c03220104840130305007005081c1c80c0950040500700c3d01e00044075154081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721751483 1250 721750233 721750243
    0x301060905251b060e0c040e0a030813060f0e120a02150910020307020f010f0605062512020a020102191a18030a08010311010804054b0d02 61
    0xc41220501d20700c034152016981c0c5464080b0110050501050000404151880c40300c2c200005442564031a88404014202170000441c03007042120100980424804100c2d602c00c03004800805000144010581c0c1c01c6903581440c40d2168408014000c140c04524108007401d44245020b80500c038010410510004400903128003522950081c4041415400b0f5540c41e840c001e0082e461304e029000e9018001030843c00214071540240e0000c180c1d04c10b00e504441c0c00c40e1000c800054015141443c00d100c16926041200c0740c006600d040312159a0002d42000f0300a000f101d0004c1c0902580065490007507004a19111024000d800761517454a0308c601c4038040c1c2042510003807c401035480380903400e241d0300c00f40d15004a04004444041820000d80134515400781c40c03000c01140040004004212440025200c146020b02c0e00c800c0328105603941c0c0c1d5940001254091002c050001010552112800c486101d610f6040503540c4059800a040341500340084105103240105103071701d61200d000081d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721752733 1250 721751483 721751491
    0x111b06062d04020304080a17061021090303150605031003030804140d1d061912090b13111c0206030601170f070207080706090b07020411030a0b0301060905 68
    0x101211944044080c1604207019446200e00d00c603074070600e1140c1980740c920145110f1481500c0403641c9071020030000d0a100b140a00381c405480b00001048030399104d542c00e0b441010b00c3d034240382029a002165481003d41811240503a0301d16001580080c1607264000c1c1e88900c10182a20140c2c64807004119030b0b91008a0340349404444181c03003000060b00c2a50995440783c00341403040740d85280d4510b414180000b41c0030000c000383d10805020010513000101c04400201100d050745400200b10140420040510b561401c0c0280d900c0b6039409900c0302d0b0440d03035080ea40080c1e441c01d80e14040c187c1b440904082d0a0a80e5441d031009019196402c00c00f946100003648030706450f10b0104c0c0c0b0750812802d41d0005018a04008174000c1c1800085035000c051400341489480c1e6040030702d0300f078400901c2d0100c5540324525a6000b103908100706070304a12400240c0d0000300356a55140001e00101d0007924108001490410b0000200000c481c1950b000045288080380280401641c50042d0700948509917 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721753983 1250 721752733 721752739
    0x60507021f05090d060204050307230f13060305011506260a020702060a02030a020d0201020405010906050309160e01080d020a03050d0f0b031207030801080a0803010303050c10111b0606 81
    0x7000900640456004441c101c8015241091421401c00003040c08909902021541581c0100301840a03240901070f1384003522182880140303a1592500b500703400c80b0310184060080d0003850600d10941c41d1069180c02546118500340038180d90383c23402600a0014844855800030100804030b80f00b031040c1040e10194203101d044102d01848101ca807104000080c00003081280d08001300c10042c0c448001601d20503800790065038840d01401c00207400e100c80e0f900c40f981103900c100710500c00baa070000072000c2982c1441c9441902c030f554002c562450306141d5041410400c020311000180840101501c1d4140c0b00d8404c29201082c0b01ca85090740c0c2c41c1100500107001c0b41061000b01c55450583c2e10203594001105800b084541105012a081c1004c1000050380154001008020f0682100f10340c2c2c010035205009001e041c1d91529070451030300040c0001010040001048450703100100840829840200c0c020490881003102c0c25016a10400c0400e105420200c2c00484000001c18181d11451000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721755233 1250 721753983 721753999
    0x1e0303021510210218010e0609010302090720010e0106031412030708070e10022107020f0f030307140625020a0204020a0203040b130f0509091020130e0106050702 71
    0x380440f40103407403855500c0c0d5010781066110002d80c0c3c8408801031800313a100c220f5149941080d0082d551030100600690003640303410010401a02c0e520703a400e512040c1d40c64071150040d480308001d20b40e81a001c41225007982803824002d0015019845441107071710810f03541e0282c5840018081d1a407001d251071402c0b00c8024800541818004c6000b958000c207980f030030840e007140c00380010301d01d8440a494030f0010303805022100301c188000081ca00034195081d10440c10001c55500240090980000907805021030791080861518104203030f0301c041d0740c428400304040b000740e180a96074010444040c5c800100d40d003248540e4650078151700a604040d80c1c06001d81c11095000d0001940c071150342101144010800003500380d500e01c0c0502903034941448456401894030302030600c08011a00124480d14401051190302d01d400621290701081d418808185100c1c280d1100c0c4060112802003038158000040c2407a01000500000054401803a00c604180e625203808503041d025080000750440702c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721756483 1250 721755233 721755239
    0x90501020604080304020f22150609080703060f0209060d0203160318020f03100c0c061401060503130501060308070b061212040302090a0b0301060f171b1002071e0303021510 76
    0x7c092200001400017074440e8941c0008686042031a000592584030420b45d20b090440e03440382e0015600c0001d0140d40340c1403081c6800c0400107521a495840b00070003050f42e8800c280c0c003040c2a0780503181010002401503480c4d070090326150002c0d40c0200c40e85c60702c001340c0401c681d14a6002c2e1040030002184012902d601c16441d43c240031520300b14481555061140580c800c01c0122140603403201e0710069902c8080118180c84c2800a650114400c0c0d0620021080144411031340201960380c45030014600c00b0700c501d56401c02900620840d0005040072000007030101c2401a482e413800d0003404140c411403107540c0d550a91503210303094a4000c202e01e901c00c0004002610b4012041500b0154096000901140c2c103c0001c0c2144c01940c45020010401e11017001030203207011411000c071030f0345006400044180c4800200105516511921801888528554142c400c1000341d01a20b0003070304032680c500d049070000c13100b4030350303840300301c0040c030030100c03107103149018011480d00404d00154401c0700c03142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721757733 1250 721756483 721756489
    0xf05061b0711041509090c0b07210908010903032a0516060b09041b0b09030619020c15060307051e0d1e0b041101050903120f07020a0305070609050102060408030402 72
    0xc42c0c402c02d2503000d07468100f1401c1c203900b1009540700421403d01c001548080314907210550a01075440110003030720910103000030421100010f0030400c0c41245440120f1880d0809894809030340d0030400180d031910540504254047e4010a6440480d440c801c0d18030381062010700181203918910400504180004a15442c00070007407042144145800301e03141d01920f0200380401002c840075261200500c8061010300302840c0440080d00e4270759060742c9440c503600082a80c03050041d10001c0c1c01c001e5590043c40c24911503050750600d9504006580281d00c010081d0070742840e0903038809210340a00e40d8001507a25154500c2c0f8246130001414000f110340c0c0f03004100d68000106001e440c010f04110219807104000001044614481d4100e28030500b03207410140c0d04240d40b5440d0030305004080060700e44a96000805a000e10010301c500c582c0c55807411040a918040e0a4009420200464011040250200d41031007650f1095480c80e0045607079000483c0e0710341c0d0a07100545a0003042001c180941 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721758983 1250 721757733 721757753
    0x9060e22021e13060f02160501230c010f06150806040203040204060f06110705040501081c020c1005090937090f1401051513270f05061b07 61
    0xc900c203003010b1203101449504902036100c004100f8401c0c40401c014050700303411440742440328440e0b100400301c1c0307040d45007000420f034103502805061003a003204030b060a565402013401c440d2221401f903500da041c8a42424040d20721114030301c68044c00c107240031412040c58462082c00041d80e0381d070b52426854000900000b580b01500998100740c940302d001c141d0504801c0c521000b000143d441d2629001003540113828564640c0120748075a040c2001081001000241c0c01d80500510b0a40080b0f100041d03801da103481030861405402c60f2200e010410441c2c0c00c0b9020340551603080e03e42c04e410b59111a0380f110211809000c201c1940c1c0025140e8210040c0716580c04101160b5500000d9040c4040e03c803001d440300b028804882c1d8400d810107040e15060207000d00358000710524500e6803048500c00c00641e071180c00b4100400c84694030708580025040100100e0131900e815100b440010030a810310541c0f001c500701c2c094134503208100205001030407811040c24203110045d00703d810034016a980b5002a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721760233 1250 721758983 721758997
    0x1050a0525020901080615040204030804060e0d0b0702030c010e01050f070c0c0e1005030c0301060803190c0c0308040e07050406051905070c0f21050705010c03020304080304030309060e2202 83
    0x402074000e840c0060f00c40140c030f113000e0503452008101d5450070310030300c211150b4000c0e50940618018801000003902c00800e031410381e096400c00d04c1c4d80010075000314500c0c191808019041a100b5014000c9007a00880200a034059240091029146094526003640c80942d0f1f03410700260201d00194113244038403a40e4000900c19005024441d54843c1c544c08903d2054403041d4004000396010040b070324040003ea00158019002800001d1038450a20384034025240e6095440e00082c90300d02c2401e20618100c60344030751192001107490348030b0401003a90f8000340545803042a140010954484c011030030380c0c0881e1030981d40c0900e014405280050009805007840040c45024020300c0009040c10342d40c08080e09010540701c0c102c5251840403440452400c0300c0192901c040c64030130010900c04103001e000e46a00782402070514145140480c61882154030500903800041404010558400d88007022103240d951000c10074200c107001c02042c607400300c48000c01258040c40c0070713805020740e07005400300d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721761483 1250 721760233 721760287
    0x81c11030a0b0f36101d060307030825050a020906011e0c0c170c01090603020a09050d030e030f030a2025090204030c030c090902030d0309060207060212060f01050a05 73
    0xf514006203041c101e00b040507211034094440c0c01c05c0c1445a00d00040c1034400110310081c20401d03a06200d4040383d200c0380140006401c007180014958001500d101081ca0302c0000d403c108801061207082082e141c52080c0c404030321070300e9110301041c440e41c0309001c0c5aa500b03100050340b40800c41d1a40059811588805040711050cc04040000c1c03100071060b901035170b80d41200e015008460807080014a0000309401c001300389441030085050040d448070602040c1d83e01503030554020449410300b516642c5148011075898403c48003900c15413000480642001d094585420761104044071400030201041c150581003580803003104d04911104804010403002110030000403107840d243e0b0542030360302c90b8006a40703400390140e040080010590310803004100303204003000101400d5000075201e0700b200324444101500d41ca076400030b00c032a40d41110b09440d0f1041c802c40d541d903400000c4509a00044400c10300c22a107560006540394002d50450b008001503a86483c600402512400071210b180035500c44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721762589 1106 721761483 721761559
    0x90203090a0204020904020409022d0a0e0f280608010806012108220513151502160305030405030f070b07081c11030a0b0f 54
    0x181e950b044401695411100300080c02034080c13138005007010361000038000c0f001e04200c204400d12800d00c400d0360400ea002c07034046007054051101c601012070380f8030307024058502d0001c9a104201c0401851210495110007441110183c9021100c600a03090903050001d00e40200341603004002c1d1030014941c3c0c3d030401e83da806c102c0b80502500104111500707a004200111801650b050500030143c1c241090700400c800c0b1b0380040d030352151a0065001129400c0c03160290b0007048120702a403e95440c1c96071030072504403138600007542044118022514070100350900c1d881d04100440c008c10045450300d041108150900400d4076400c6070035481200100043d004580544820981110115869020035107034211f40e0380302007840090192900c502216403181000166014101130b03074003001003d84100501070404c6100100342c1c2d1001c00764500d40010003031404a64007100ca00341003c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 721582733 721762589 := by
  have h0 := BRFrame.cov_init 721582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721582733 ≤ n) (h2 : n < 721762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
