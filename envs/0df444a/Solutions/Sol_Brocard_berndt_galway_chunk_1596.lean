-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1596
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:46:31.849727+00:00
-- url     : https://prove2.me/submissions/19244a9b-639d-4b9b-b8d6-119f097732ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 286870503 ≤ n < 287050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 286871753 1250 286870503 286870511
    0xf12050c010b0307180b0604081603110603040f080d0902060d1b050c060109051b1809100602030405130902090106020313090204061b060e03040e06090a0204060f05280201020a03 78
    0xb8018507407501024824400044043c10b41c203405141c5581001c002d0b0040500400e04003542c1d100310500d041c01500b10203240104040c028418800c14401a501e1082c0a40300750b480c5092940d031700d07124561403800c00741c070402d4041019402c0070440d0304040304060f002401d040e1901c144241201c02400c45a41c0024900c2010721902c0140f4000ea0030b56400700e08440151030203a10f4140b03500d014003401020340380c40f4400c0302d4181107108201070103084040071903901251203500c0c1600303001403140301a0814105100441c0e0804c00c4680c004100e03010303910152030710810480c80c81c001c880075046040000b5400340b4809e00105806a0010207400388000310134074280140d682d40c8640040788a40d000741d03c00250780c1d04250f84125265403255421600c200400209000c10005041c215006504030450840825007480000d1600019458002082da84118903092421a01a090b00d0700c09403903c1c03c0c0000031690007504a03000f600d02020040260580408418445c0c00030f000394130201380100030a1070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 286873003 1250 286871753 286871771
    0x506010801050114060304030e010c0b01180b1507150e0607020d08130b0103030f171503010e2806020409060b250203120d0e01020f040317030402010801030f0f12050c01 74
    0x11131850280414040d115034074548483e2001c44404100c100c41905110b00c0c00328043c002490048080e00806060000d201511071071030078035003070b2021400300b14420829008224940c2200c1d40880d01c1d6507034049404c3c00d00d038074501490303809014410f046141901841d010401c0113500801c400140010a80d2800c1e819a2070b900d070301c4008885500098410100000180000390213080f01020004150070500341050120400d8807100b80d04a03509403c8014030880c0225038107007409401d080d485034a001d080c010842408403103080c4243c0e40905135003441e05c080702e000c0c001c0d658111005041c0c00304c010b2111030340300d519112b0941d10861014040e0092084152380d03c8244401d40702002e54000c000c0c0411100c0c10f800d41d0116001042441e2507141d481d81100310001c0c1c2480105141c8209903842926103240d41401140e42042c0c100c0c021030607900f0420440141e9200c082181940c0c0d00c0201501c0849407410f01c000301581030b08000b00080d00e101d00b060441d076000760280112003031240c000d01101e14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 286874253 1250 286873003 286873019
    0x3030f080c0309191a01090c020706020708030915040306150320090c0a0e091f0609060816050405031b101d040c0201140f0901110301080c0906061605060108010501 72
    0x4021205042c50b60804412624090943e4011303041c0240640740450f03483d032180c0000a00c414081c0d000d20041e03503507844441c00e55174052041e0030041c00720780081c00810340b608518179101d2103914900380c41280507007010002030300800e06840107150050001c000c40000c6817050f444102c501c0c0016240404003801c000107400c1990748042c4052000380400e0020b40318140841c4050700020800b10074004088030440c215116049a41e104900310060804c0c400c58040402c0111001a08441c0030080302210500c16950000c2000e80c0041070340000350382c0c010f1006011180d42c080c41d0000341d4180220454602c00c01d49086641d88580000c40c0c9400541c1802442903450601c442042408030140011810b8a031400e40d109400c04500f600010034590555201180d020310101c90400d022100f40041c0044031209120f014070005502d8080c2e0f217594100b07111b9035500c040d8103c00903c0380500030009012611840141c4688402c0c5c040e40b00241182490f020b030300c84c6024010307610a91b01e440000070780c0c1b507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 286875503 1250 286874253 286874257
    0x309040f0207110d06020913050402040e010501081e0307060f0203090d0201061a0306030a0c17010c17040b100e01061d090105012307050316110a030507180905030403030f080c 77
    0x103540000d45952109251042c0600c84201320000d560786a130a011090aa4032007080e0070000a059410000d818a840d10400003240c00804141e0456031424005104c0b000b0009004e82190045412410780440c0c0f001d07141e85144a5442c004207c0c03410000000940070782c640165000319140d005442641209000803803c0311150b201d8162207844a0100700128440c80009582006000e01500c20a03040c648604915482c00d074040a40883d032140c4d010901c5100b0b1182c115100a14984003103d9040754040006a0300060b0000e0240010b00d4003007980820b107810004000d018075600744c000ca40e03560b40d010f0840e60800710a4000c0741d40c070f5950680245880c401890613610161204c2070100540800f14501e524071460014501c00104800000719108001420040c41822071801303107000300789443c8217148222105680035000c40c2c9818030000713001194400a85407001c01d1000b4900707043c0314030b1000e0a80f03030401414a00000501006250b440913003490a1001521f0740e000c984c071410355580c414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 286876753 1250 286875503 286875517
    0x90f060c030106120b04090b0f010e010e01060f0309061a010f1419020a050313090b09150f0301060b03012312031e0409022101051806151b0309040f02 66
    0x805020401449044d000703580a501c07500030301c0c90008003c6481804601100d00d10042079074030354014020052002c500c011803a01611135129058500d5142404004001d2410b001d01020f00c14400c00c2001d10078032a03488069819007081041c0021150903012107540381400f030340346002520a4940f141414081e0f802e400c181035944200c685880b1004030251400c070f841010364821405182c550300e01154080004c1c0200c89072120200003600c0c07802650908030340300302099500070a078040c1007005105100c0c6c003001070500242d03005242c1226803000280101040e80052000c0d00c8088000304244201703030310448005c102c1140034050111100d0801942c42c003136010200e41e0794410002441e03041c00f4a18100100054004086d04094940c2c1d408400d03a040174418001100201c0954000d07400000e0719980103141c1914520480c1c81903848102ca40e0200800319405110107070036690034082000100c614418142131401c0806450361049a12030388000001407056052814001d1003d0041c0b080b6281c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 286878003 1250 286876753 286876771
    0xb0a110705150702070e090c2b1103070f08060f0604050c030412030b0a060c0c05090c0f28021c08010b030403030b01030902040e0307030813050a151b0305090f06 71
    0x1100e20080040d0000302c200410304001c40c01650000036043c01c0d1003507030900078842440030b00114003401c03003031141601031038a030140c0d8800e40c40300506046140840361404560400380348042c04d600e10303020900e809100e62088400402c00307480000d4040b801304020b0702070310b50490301d003103d030310b5000420042e50b10030380710041002c10401c08200016600c40c1ca08500044a060104180700780d10009900c880c1c007070307115001080000c0c41800401001c03c94002c080e1204445e54541420a280441698051768502410846000400f030281d242c00d080e1146180c035072070103206514032a00c40b0080d250149079a4400030030041c28002100705000e41c0c0c200341030b101141c0c6200d007903549a490403400f600700d44815074145940d8100300d00160b11740340281207001c440600115581d10052600402410008140c890700d29034207907500c1c00180002c03a880b5a55074221002d101c0641c001204040201070b03450010b460303460341e440720910854041e040148281c840100750740c0441c944140868480b00d0071038144031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 286879253 1250 286878003 286878013
    0x12010b0a08010605031f030804030b1605030610020f2401060201060b030a051510091401090f0306020903070e13031b020f0907180305010203060f01020a030504030816050a0b0a110705 80
    0x141130f105102a50340301c41407441360081d80c510186803181410194100781d61703e6900041c01c0c02401000c038007140d040101000391003c2070380f00d46002071590002402c01d03441503001c160344610252003040820551315540060302c000640c0e001000480032003031310a50340910350307a10000540f5030040c03081400315040d14032070780e21f5561141f0000c001403100501212004030140d06c1c1030140d4448041d0b014040f180342c2c840480040c2070880400f04c50407003010315410032114103030500060032204481c40c104c0f81e10140240e11064000d002030308241c0701d60052004141c03900100802c012841140010301806512032060010044012010424110802940021a40c0c3ea00780d03d50800c86225984210580b800d8420112010031150780d030900380d030003903c90f0707074002c4284045031801001d10049541c1c00d000604403c000e41c0d0f8041e1440c001e61002821380013012a184001c002da95011003402903010007a00e02a107034500e0101038070130303058400c81070307040c81c00c0744110040d00c0f9001107804164200000741 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 286880503 1250 286879253 286879259
    0x50a1202060d060e090a03090512030412240b01030c170f090106230906030f06070509030c1f02060a05060a09020706020c070636090b120607030212010b0a0801 70
    0x2115401000b00b4861a0307560000080c003a140031880b5402a9640c5003c0d00040700301c2c0c00c0080517460141c00240c800c2c1d40c2034604a0a100c1c00204403005c40e8000019281c0e089424140201c40c405c0481541491001d0040310101d80c0d186540803d00c400001d0320308010f03d0500d4a001c0313507000d070110700003100900c0800c0428810f40348402c0080d13110001c00004188940c541805000d1086407030141c0c40842e06030b0300c001c1204c1c5051055658001019001408003541007080f00340c3d00c9001034092001c1c010001f40132002910144000e00d540c00c0040c100641603011081c2c0b1124200f40d000141005008003404204802194001c5600511000300741c007200d9810209036000940c0f00b203c0450b082a401c01c00400100340c2408824014a074944481002e02c41d0004110f07180090000754500e41c0f807003100c40c41040d010010009058680030140041c50f0383c016000b203103a01007010141c10203445004200070031030754160010480081d040801c004144d90b60001c2100c28014540030b0700200f01518018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 286881753 1250 286880503 286880509
    0x3030f021f0e010b041802030106050d0503030613090506010b0c010e01090804150e0d0b0f09010b06040909080d0e0717070503060622092f010e0118080111040f050a1202 74
    0x7404480c0070b51000040148080e1300060032115450188440e1303622010b241020f500e003e00c100300003000306960540c908900c035661244c80c3e00c0018105849401e9491000800c81241e510000002d58080b0840d103803961a0005060036401211104400d9801d008034070003102c0041c050b01c0740195000750668181b070309140001e042200c40d00074440c10011141407070440e560b9184041102c050192030755010314184450703e09000b1200030403021850381000305c400d4180d15024215011510f4036000003070040001d2070040307411702c50701004180b82801d21600d402c0041000c101d0404940c201c541625422441080c929240e524038400d42c0e034140c0000000803520b0070700c007480c0131003440c0801c0000815a1410488011a0440c071000e6451441c140c040c014440485551036070704180050082041c660307040002051950103112542c1040844003154400800d040340010140440783c00034007183c2015416200260002e02c2445070804c1070510004050038816810801e071000c41d008200800311070740038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 286883003 1250 286881753 286881761
    0x9090203120f0c06010b0a02010608060103032f1c0801120201080a11041205070312090e07111c081f0f0618050a08060402040b03070b042607060903030f021f 69
    0x70035032448104203103c411041840303c10b028003406003009840e29040480242128095080303190680d005000510100f50050f81001c1c0410508a000920301902c0d040c9120021009245249910503103280b24080001c107035001c0000380d82d550b00c4c2061b45e0b1ba214050b06070f6104004029000ca9804404980342110725041a0790111412002a14080d52101c0800000e40581d4098442e0f401840c4180204001c91382500c01c034800c0c91502000b010300b0841e003450342c00030142c00032080c0840602e0407103c0880a0012404e41c01b1420300c55040350240c00d0f03000d40342d06800c954142c019031a46102460f120041c00030001520401d815412005041040a0b03032100d94003010007021181c11080010283e8901c1000c0010346031420103000c03142410f1052200f901c406c0c89002c6e02c26040420240810365008095504580e0024801d01c600e16800b210070701c022074002c40030b008034081e2880100f5550782050490303086070321075540c4540082c24484101e0300d03000086811401c00700d48115124402d451504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 286884253 1250 286883003 286883017
    0xa050c071b0503070b030a0b090114060703020111030a0c1e0207030308190c030e01050a110a0f030f0e0a12050a02060727080708070b0f0403061e0f090c0909020312 72
    0x440c03500e41a0b2207600003460070f20036510071520325100108200350708266004403510f42005407010201541001c0c01c10340a010543e81140c014023002c501c183c1814400d40000d030524110344049952402c1c544036040c0640384132980c00c004264130f100c0fa6502d0000d0800e0700c803c1019164040d140050455904480c2c0c610058925004918041a801c040c175101e44180c2b2814419a100003a000044954403803c0d104c00078210b2528901d001a0042a0300e43d0100b111464100b80c501074182d0070b06410150010301259a40d00a003070b14180f00ea0340d0071240055031072901d600440e03202ca041b02000c0d50403505885506140700058201201003003c550142d8000081c00c10007075094910301d0110440500f40c044c0360340c0046d50710390101008000e0306105110220282a00e000300070b161410034100f4210a10491000401140d03461214840301040700052000302040c1a0303041c0038910b0301c94840000341590800c15510392404d00d80019020155102c0c0c0000c143d13015001e402c40d03840890011419421245c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 286885503 1250 286884253 286884293
    0x3060f030708010e01140105030f0d031503050f0609060c041d06040905010e01150f0308040e0601020c03060403020a020a0e070806040c0e1c120302040501080c07031209030503040b0a050c07 83
    0x80c80104034000e007030160b0003081c2458030000820010032180c0c51b104805c1a80914040d42000c409168140300128441d00c3c5840103081c0880c032286220035602c0c0e1306906174000b1f0102c0c0146000704807064004520180500802000c0b10041d844404510030f16124a100303400c940480001340c12800701c005640300382d2001004000041c0c104042e15000d00317413003038021100c615940d5422a00c003c003603026070200c0501400e04000495034119030707502d285445140510028000700c9800112507a20800c04684407020103419504641010b00c0e0107961005100f00482c840c0c1c804900c04508403070701200a0703100742099641c101c0da94a501007408020408100c07820100701030440314a409480e5143e06403180d02030500850240740c011306100b0780304600c4000071010140100410800c0e0383c1c0c440c0c0e0781c9401c100c07400c06c01e0b030f17460040d03203070540308554203c407031904550801d01d62805164100010b18415806414000c80c070b0380d1050590412038400b212031040020090101e0400300d0500203100190040a0f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 286886753 1250 286885503 286885513
    0x8060a0308040902091002010c020a200a080717031306031a06211003030e130204081009050c03011b03110702090a050601020f0706020607050f120405030405030106050105070803060f03 81
    0x26100c64001d54400d0704101c0751107400085100244c2000c0d5040b0b8000b00b02840200400075206e03000035161060a00081c0074100000f01c0ea004155486c0c9005c0039030900102040d1045e50345400d42511004244102c4064034030002a0f00c0040c02c001c022940c41216a0149440103400c00d9000e600a104421468105030440340c48241d640e00d40100a00920182c0c4111591180011145024440006156070301c000c0384510b080000035042594441ca074041103600d08100d0002c46503860013070040b548000c001e48240d03c00303441034801c1544012070190140090f20260403403201810300342c84640016003008100101e9162070355103e42e0117600c0034403c5010207032600c0c000381c00040a03030f003041d203401001c1a541c0f0103101c21583c041200c19103c40c2030340d0113080315525105001c1e48a00004005500380400007410340c21084c0d055080b00e1034410300789171107400342c149410f005a481e0094024a40258030700600800c80390701940680300e10790360040700d051a65442d0410f0082130100704e0b2a1039007512a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 286888003 1250 286886753 286886759
    0x1060602070605070b0c0346140c030613060909020901051e01050a020c040e0d270e070c0615081006080309100201020c0604110f01050c031204230f010c0e010f08060a 73
    0x58140c20350700d141d00f40e29803081c002c2d28807101c4c0000c0582c02051070f508e00b0b10341260780704081068a41c00303071b010b20481c00da00c2d2240d0b62000803c081652000358000c0c0c00e860004045608a5280d02c070b075a8240c0241e901c1c050981e00c9105024020510942c4080f0407280440c80285942c402d000410030b02803680305552141189202140c10380b01605490041500701c1e1500200e0b1641c88400305d1a0000c0702101c0240380d40900001c0f001c40320b004c0c05180089040b20000400d00350007081000c010942c4842c0070400b015000c800d001d0a48914050b904080c02003000d010030500307c901a0a0546d000f040285213054140300070010b204442400c55800d6540900c02c0001c004001d201030342c8600d000e00c0c3d10400200300041000348541400e0f10444c107008082c07061441c11040001950401451707207440c5825510f45081540308035012040d40d40c5c10801003103500b051a0008204a882c18221800a100800b02c44400b510b41d0a03003000f0183c005084143d602c2d07807642c41803640070b4000601400c40c0d10b030151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 286889253 1250 286888003 286888051
    0x3030714030d0e0c090903120106050901090e070206090f060106140702040603080408300306060d0906020a050d0f0501051f031404110f01020c1c2301060602070605070b0c03 76
    0x201c4503801400301e4000340304a90560900f190b4407a403084440d00958230308001840709400c4142c040c0282d82c20000007095202d05a4003c1d840c401c06852420b5040e8003602c3c0001000b0350701d54086031070f00c0e094000c0a110728101100051000d050fa05986c0721080d4504009003044101d0b04400c0307090b6482504c5400010120700440002c1c009014500054141e0b815800d2402d181084c1c2034038000802402c2d40d682009440c0144141d07500004100e4140e0fa480d104030300540042c0a406402034500d44c80050684090381c1c01a00601403040108401c4c13280503c0c50000384220342092103000d4220b2072402c040b842180885404410034085400e0000700c800e2200d68030320038104d045508840000c0342522180c0203207001603c60407179001c2440103200780000e07100030032591001000c4409400300705500c100c04002030341840039980d0b1490311107280c0010038010007078040c01e82c510801b40940510340c1c02084461054048862482d00203242c0c20007a00d50310559030341c0341d00007012441610760038009065580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 286890503 1250 286889253 286889261
    0xb041802091c050d110d0305041103120d0f051308071e030504030b180706030f1e02040e09070605070318150201060303020610060207050906030a0b0c0408060a0b03030714030d 77
    0x480a0151142e0029240080c6428450b40074402804007050008000b40d900180c500131400c2c2034900400c50307031a540f4041010507000c83d0b006600d401080100400045200301922011202500c28480622801003036000c488007070f01c1ca41078980080d00d4841c0483c0b112802081c50034481e41100c0c80307510840401859251446008034005480010b00b00305100401c2c400c0e5400000402c08410030a4035146001d40e04c030395501c121001c0c0b640702c80300403828007143d5200c00c060600013100c9015041c401000e03c4025441030003510f0106030b141002c1494036030005580d0081e00e00e203403100d600c1c203c020b8400791840b100c0d0350900e07699088034100100c0c010204800200091009400118145007589006410188000c08003682400b03d610200b0140b5400141c040c120f8070b05031880c07492038442101207800c00d070f4400c0006d08035007044014010a45003141c0144101e40d01c00041d1604c50b201e141145080c1d811000b45a50f0550060000c500460f00c0750180c143c0700075901e41201c2c0b0307101e450000d50042d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 286891753 1250 286890503 286890529
    0x4120903080a120b090601023406020a051002070f031b15050a0e060c0720060c070305120f220e1303110309091602030f040324060b04180209 62
    0x5a00f560341da041e0704209008540b09000b04440f40540f40c50504c0000355140000c4180c0a008060100f07449c0c1c9418001041d0208401d6209910240c0c94035a10083e58810008004540920907440d101c0c0f240e071018070a031044035621048183e84001c940d00c080790744440c20311503e0301c3c0b0b50110b071442c030014140322543c103102a2055800300c3c451800703d80007806c803244103280400d40c0d042079082050f104203040071503003101c2c0c1c0981e442a80c0d00411480011461141d100541c00840020340092010400202d160489202e8001c494121480d05101032a601582c4085ca21300001030240030a841c0c40003072420b0303480e00d000c000220000d982e02ea0302d5114400c241c0e0074810803030080e80700c0c0e0306050b44140744504002501c0000c601d03012060021034038003e1b0081581021800b6103861131507852003482142c0009001c00f0940d81c07155124100203039258a20306401c040c4400944d0400a0001d940c00340108444420910701e043c11b01c1c0400c9680358014000842a0a40d030820202c1040e0340e6a4601030a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 286893003 1250 286891753 286891757
    0x9031207080709050d0309090b0a1401030e071208030105130b0102030d020d0e12040f090603050607030e12070309380d06050a0f0528150c0206070b060108010f05010804120903080a 79
    0x40710f450301d488032301218030078080e65006811344082802200842e440318000c00c8000c0c81d0000e1b51103c41c514003820480c658018403c2c1d0300f40d12030f8200c04c2c000f402c80914184c8a040741c05500c00c3e07055039141030444603071440c0103000d03800510007001c413045550b0107840141d980d014081104007141002c203080003000b410000342420049402e00410022113421400345c43d01400c00c021850454840a42c1c4040007030842c0b0800d40c44003560f0b4401d00f4140110071200302d504d8102e0f03450b04a28507014003801e03024000e2502c64180306140d2640d08500d4800851100001203080c0107640718071420b84243d50012148444103074540900045d140c860541010041260b4042c4a60a50030601042030604460f2030344c00c000c1518001d102181c50391a400342c8100c0f00b11004444992079412001d541d00701c00c8400c081d40c0604042151410301c014402e9892040c2400d03a600d01d11a0f032030b0121000e00401e01d0180c00d0015502800003400a10004c00300088880c0904010880503601e6482c01c0a941c808098240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 286894253 1250 286893003 286893017
    0x91b03090a06060902040e010b0f091e0906091302100201020c031c200f070302120a030c0206090706140f2a0c0904021509120709060501020609031207080709050d03 72
    0x105008207032040c00060130000c032040d03180500c0c00d24030f01b441a0060181c1c450000c4001003801c10f1000d8203084580c070b403c001e44004440c4103440141c400c0b159034a080c3c903004d42074040c0001c01074030f00451135620030304030082d107074200a40c00d40a01c561040b98a240101750f40d800c010215440c0c40400152042880014004825074006c410590580385a034660558400500307141c0d40f02803a603c01940c0894000c002010349032445420100c0c58084660f18282d050b01001901ba400070340e045d00710102d168650740880b0b81a441d030300c02d09941e4100a1080c03900055088980d032013141175900c0201800f02a20301c000342010034201400b00d00d055001d0b002201a02c80032544a4481424454000c041f0742c2210385068520b042d401254094240032020746d41c0e03a5001a10000325519541d10389c400e2080794007110003c580714511800100142d00855000d88a6200001e091244c00002c03241130b107040d54200320b02911741180540352414050412001e0010701c040200f8503403280000c0c034171054000d80c2c5d030039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 286895503 1250 286894253 286894273
    0x140d0e1b0109090e0319030204181b09080d051b030301080f06090102040305150601030f0f0b0f0607020f010c0f0b0703062102010e1318051005090318091b0309 70
    0x509240c0341907001c00550f40c02c042404100c40004819500480704024001003a540102c208038003e1289821000060050350003501c0401200c1e8025107080c1210354802c00c0050b60700c00d082e29000544c0c40360300380d240c1c4100d240c141d03c944a107000d4012807008909061005525140b05403c4d9082604000c0c8039900610140c20038070010421607030405c10540003140b4050454132881c0c2c9500050f90440b00315070640000c50204c0e4402e1b0302c0a104081c0d0801c0401075a20701c20000009400120700740c6202c1d502d000c82008103460a04100c0d071405500502d0f01c160050180010b40c0c0c440304140050310050b0108041c030b00030075405102c4501c210501e60700000c40c2810000d510001d80d15100c10040c80003041480b03400180d8006000c0701c408003040301e0340200f00c020060307984040c01084211111080c2c00120031802c129001611a8501880180c1880f0503556240d11a60364060380c4601100340c40801e06500e440d0038610035564100d042102c055402c00110080e103801030b0f10950f0803030b00c0d95025441c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 286896753 1250 286895503 286895507
    0x41a060a1809060e0604290703151206060e150609040b06160308060108100602060f100914090601050906180405030909010e0f010605030106050d051005030d0906120507140d0e1b01 79
    0x4440d2041e10150390241210814503203001c0d0030b07c0108000141a65086510400441004010004c00d01e1800390102d0b0841498100060301c0144155032101200c040424503034000624850202d28000c2c00d003d00701218202040083d103a00008107410810800403c0f4149510101c54100280262a08072850800388001404100010803010b00b100c2800710078010141d000c2000d581100310101305850b262101d03808140502e030a9400008118980403c030081001210070161044100170156500d030ba0747c42081c440302c0c540880d142e0741c2c0720381d001039125102c4c3c03048132249400a0103401200d042c1500e40c004662081340030380020030038019480c02c101915000b040802d01500d0a45061419949000005080ca000d0814400d001130348800c0003401c070070b01c800c4260340200002411580342c00c9420358060b10180450042a001030803038500c46510442d98010700d400394200c0d548410061900e07011040158120b01c0201401030b40b01d07207691110500c10482e224032180315803a00c00500885c0800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 286898003 1250 286896753 286896773
    0x3030307200303041104020307020c12070e061020030906030a09120c050d201006080601060306050f01030506040b0301050f07020c0901050f22050708041a060a1809060e0604 76
    0x1091660358410800c1000140940d5048000701710150340241e1a42ca4000003a03041c44200815a90414024050042d0790800001c40f5070480742c01c03840c41501c940f11881440755100804100b0800311b01d206c0b07801c00112a408143e6410841c898082d00d0910b9a484001207071640256150840c40b0303141c02c1a502031010400b650224801c6a04201c00109403581d103035601d88400e40500014483d250900105403402d200000304c4011100041d07641e20140f1109680c000c00c600d000345001c522428001040890191142c041030790001042d45a803109600011030141030000c01c2160042c2d118080045261004d00a0500804c0c45001042d45850410710092424464600017807264803148010045a1650100305603a00d40a8810382025908003041c3c44082c090b036507a030141d007482e210070070403000d80c80807901c3d028620800041c2c0d04048001d0011000d0340003034800c154405030400040002c5510a60741500300100c802c0301151107401606c500c01165000258010940c2049003000200311300b0441c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 286899253 1250 286898003 286898057
    0x102030118060b18210303040506040b06060720010c02030a12023007060902090f100603090803150a05121006120803070f0203070b070c060e0118031d03030307 70
    0x40680c01c0410200c103618480c16452401e500810034240d4400e8818200d8000d00840c1780741e0001c0740e85e241014544240e45d8101104d00fa546544242c01007810391900d003044640c21504414110000508040c10b1144284043c40c124103120440c1c0281006842c00d010505c0c0b030500807611081c142240c000064100681d82c62944104040100c0350010b141032031103e0165014080c06032a01c42c00a40380c20002040c00304070203580300e02417504000e1100b011283d418400c03110603e02400c0c8659411040d029260b4114008011804c14070001e100c420301f4030300c6c810001c04c004002c9405a43c2c0c44001c92207014103400c44c2007854010b025549001d0305213018910040241061160380c10001d42c40304100b0b030001a01c49020031034502846400c041c820000e8511250b0010030003510303801e100300040c12001901c43c088036038a080c07822400d02144103200d52084d070029940a020040307460342d42140c0d2240c1d0300d02c0a0b11500745081041006071010806180310f09480d84a0035820a40c8600740400d0400e400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286900503 1250 286899253 286899269
    0x807080105240304080409060b190318060905070504060807050108091902060304080403150203070e190b090303070803010b0310090608070603020f120f060a0501030b0a030b18010203011806 83
    0x60b4555101110401c0360b250041d0420a9200e441e0392802d260548161b80c000000141068408192050140c0051031303803000034030080005000660040e0b080e100800001240124603000000c08901c6941080884034861000ea98036603441c1c03030009040301c0d002e401400040d485030300240700550308225443d0308000400c1c0103100035005000b5a10358000c500100034055030012010408100c1028150b40140d03911100403d913946071901004000d4000725030b654000303980100420580d0074841c00c04480c031803448400407402070404080b0701c400e901c8401450f40601c0300308000c40100e038500020b103006e00850b140c1c4681d00c0c141913403400541c1038039401100049140207020440f1100c00500d000c00c03201582009a200e43e0821101c02c51406100030912203c03032108204040a1801a410f500c605c2c0102d0300c0001c465101e4004400701d90300303ca4000c1d002080d000c1c050011810041c0e80c1c44d800070710302884860030b0210301510f40c00d81e0001c2e071044412008907004401058040d001f11005840c084e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286901753 1250 286900503 286900519
    0x50108070518070f12020f0a09051903030e030c0d0f0210080c0415030225150902060f0903010603020a030b09010c0516170f0a0503010312080702100b041b0807080105 73
    0x41203041d01000302c0945010240502d44c02c0d001681400f07920300c0c04603100c200c0c0707046465160001280c0f60542c0701e0000e40e40020b10748100800c0f40d161034075030303581c074081000d40f00301040c1d043da03900381d17041d000001c4615071500c60200840304580c0d60182404001d0710845542020407507510510051441015404050041607020440d05410b0a41038804a0341000414058084201d40990003441800c00380420301031081504203000c44c840b02d191070881d104034902462400c03174651200c101c3c1e03290000250300c2502000030400d031075000d1000c0c086500f0010000526103a580c4d00081011403142d20450303540900c40c04000481c00284503a1842107000e01f4603a1508141100107a0360030440300700202040304842c2600140220341f02a620010350401d801551046003000151447d002480226032845c51b0505030785c0001d10a0780e2890040d003a0390020a19102c9100d0325402520102341100e0300203590b40e0054000200c42c00055540010f07036142c454450900080c020901a016003142d4050010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286903003 1250 286901753 286901779
    0x5010c0305030a05060a12060c1107151809050403020a150204060801030209133c1e0609050109080703110c030606060c01020405150909011a030103120c150501080705 73
    0x41402c40794843c3c0c000c1c20000780d82c0e542900264602e002030700800c03060795941c2980b034200126988100d407078001649400344170454460000d43e5400c554010340303a2440c1500282210a40202c4594042031101310410780d0403600c44001c0004c84070212800da0050b030001c11110240062550700e01111548030f02c0962901c1e0800001070460f10041c40000d00860400d00010151130000c1e800441042d4895801e907003075500a070b4421800c003107442d012141c03580f07007a45420f244500304400038001039000e4904003544000d0503510010f07089045003a1342050b103035111000040c03420320515a10503c80e542840d21202c803070800030141403100881341000e61040c0d002d1a40e0765000602207502000885509a80703161200b40b50340a8040c0d035003d075810240481103820020005c90182482c03031005c1c0c440e071005a07030f200e54014034900b4603107170100c0000003080184080b65086e2588114841582442c0f0f40720509a070f9040d07401000026030002c41950b800052220f0741c130038090803004040c125000306490403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286904253 1250 286903003 286903007
    0x120b0f070804020f0f0102162706140907052206030b2d0604080105101a0f1806040b0a090e0a0b01080a05130c080313120f020d03020705040f060f05010c03 68
    0xf00c104002c62117031a0081000c40305a10070032104d54801f1040c0101c000060f501c14941418240496204070400204064404602c540c0d00c2228126444105200c000e000603030284202e40902404410400004001d83c0108082c10011010480a010003014500e4a0201c0080c112542c5081d400d2040d08000c0c2040d0a10808401c0e1505e175040c210940c1c0d52604c5004009002441580d115851039400c1c007041007801d0b460402203508034cd00010104031b40b50030112a210203440380c2242d0300c3d9816410311a405004440f02201d4480b180301825441c6001d44500c030003a0580c00074225840003403010b100500018122400d6a87c010204040a000f21035508002820482000b007680103181d80d40c2000924841c406851011099081100f6210884c0c03201140c0e616640401d20305480001c50420001d0710041074004c603848aa041860006448a035500b0015504424801501141705880300450b41d03503150b10901e121100d801000081711403034140c0703011000e681030b4046418401d4000800300429 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286905503 1250 286904253 286904269
    0xa06050103020c1b01120606050c06221502071505160302090a0303030f0605090c1207170a0507020c0a0807061103160b1b0d0f140103120e030304120b0f07080402 71
    0x84510001380c542d40154001251617204050407000054240000040d250f50014000d02492510600380c4480f6030b41c040e82031044080e040c10384010b04110740340392000b084035514000551aa494000740c581401c544a4030800010b5010092144e59100284148d07820000c94124940030b03d800d056080c0a18400081c540d11014440034050627140d6090a43c909a268001c00140c4001410510a401d100c0500c050740c0c1c000c1111003003899100700115107800e02855003800345507044100d4202030340e14181c1601c0600700c0500f140045d0311a000b101e07040ca540340b41e003110103450340c41c00030702480345042c100a155440c1c8030000310060b00b040051440f030b80c070040112400160003241700006610341c0900030310f004007507494402035007070042a440201c495940181d01080da0009051003007050345156164044400c0c0320040886810b061402000f42c01009803102c00c0000800707480c1002d64954001e4070b01c030050301c41100c000b09400c0811032340b1119660465080841860200354910b030640c08500c0394 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286906753 1250 286905503 286905523
    0x20307201207210302010e012d0209030a141011091504053703030c0204051513050703060b07060e07061d1c1b0503010515010806040506150708030a06050103020c 71
    0x843d8800c3c4500309150003500580d4980b00900003c010108aa100100c0490440c040d40040c3c0c1c496600500402e00440c002e491a516009002e4003074252507655000540b600c143d00305c3e0650094844c0401141c4040c8100c02c00c4d400200d90031a6110486020000c0c8020030140251041c0001d2005018a0b210300302258015036241c04510440d41c00c403c04485089940198158500ea2140c004403c165010003503601c1a4420340f820701c415191042c84024200701c0319070440c5c1104c1c41301407403101d5401c180c01c40d0f40c11801c0c9040000e8150f03208d134840040d41d440a041501c40d9500c4440500c10311504000c1003000f860b10b450101c42407800024001090070b03428036140c3c41100c140740b00032102406024010fa00d190b00008521310019091484c1c10102194851395210b940380c44001207140e190740d881c00703a49040503507a540c1a9030320340302040000c05000e00440d8200501a1310000e01070b03004401018590301803c01c8540300c4c80d000800c0c2080d0340190b000581010f0040c05403241140000846901e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286908003 1250 286906753 286906799
    0x1a0f0a030c030b0c12100302010f1b03030902210c030c0a0524040906120201030e01020f07080304141504140d0504060302091315051c020f0907020307201207 69
    0x1144e202d1542004090040200007548805944180304070201d101c250181128806c0c0c8802404145004080c0c680803880da50460108451450220000384240e0242c002c1910003485400300545601108500080c1180e21640681c8414400025403400304205203696004844000c1013a081102184082e0f480d001c0aa80c24180096602c480b46207100984000d014800390410000359507a140000140c1908010b0340032a18014648010300c0043c02187c2c44950011016403030400d81c0d070342e400000c0d4402441911841c02c600c03802e00e46c000050259214032980a02c041506061034200784440145401c3e0f0021a40d11009450b00140c3e003100039038007107070040e040060319000c29001054403a01e4401c2c08099181c40c143c0c9078010070134241a00c00590b87d061721540146070404064420401103084003942c4255074201020591070070b8035115900c003180744180c074205400380d51420540c2d01203407410120307004081c0c80c13500303942001010046400d10400c004c10b41c0510300075055030903200c529a500d103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286909253 1250 286908003 286908023
    0x7020909010204210b070807080606130803030a090c080f0604230a050717010b0604030605070210110d0c03050720070e0103050f060714030a0c0309061a0f0a030c03 72
    0x111048003035050303e004105040100a041c0000c2c08200009850000308a4030151510007160a0718800e84000d40b0820350354890046c40d40768482007040d03903000701c1c60f2055070b0070320381d00d02007074041061021b140a5042c1c230710080f80071a0203240006051445802852059210450340846120005055500142c11000a03064540441900c0c4a0300a009480c0c000c684070b200400c00c10020009865070441d45803940120301c1c1091141c503d40bd27612801040c1c0d0788840140000d202040e131583c04170b41c022600f0300441e440c0050b0341d9401c81c1680c0d40300b807800548003004a6403001c66900b5004802406070b2901c0c0400441c901690041c0c1862004c203180300c0442e80c10b82032142050010070008028041420152403650303900e03e04a48d80d802c0c1e10098180705c1c09510041901c85000b2022600c0002454076040d007141d4803142d00000034a4803850503010940c0300d0b1034020116083e0b1203031010401000403140d854080c4601132007a641ca10ba8401070141030340210410104944d04400d205484d40304580784 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286910503 1250 286909253 286909261
    0x30f06030602070f030f111f151215050f04150605060f04150c02030307150b060d150608012714090604030f03090317040303110a091409070203070209 66
    0x50020909504014015071000a200081c4181074903d0446140f0076030340c80742d8440542404a940c07249480080403182d201c0c091800c2501c3d8920b50006000c9101a40002c0c481c0010046a1002c1e001c1e13840540140240a035080501003081c2d440c03003980c4d4580e60240482e0a0175400300880f528004c3c030107861880f180c500f007289403160350844002824020311007504c07009040780944159026201e420380c040711074803209051900540040400c01d400038041d5040c54920345540c002c0c0d21110011486c115911940a031480ea00d850207480b1b404400040081c40f201130110110052045812803024810208010402c2d0600008020b00c0c0c3c2e40c1000c640b245c0d4401d031725100406800b00301d40030300501c6040e40403c218002c002510714807460080d41d50300300b1b03d5480b000640c100d45c9440f17005030015400b40c100c40401c0030100b124582181c80b078500041c4280103d0085441900b140b03e84030b0019817145005c003c0700b0300c0044512000703041101d0b16060b0f8207052402950320f01c05c0344002800707518418002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286911753 1250 286910503 286910531
    0x204081011121f2111010c0c090608010b0d032001060b041706090c130b0f0901090905060a050402011d120a050d0207050316150507050d0201051e100605090301021c020306010207080307080a03 84
    0x307c8602c55000c6082c610f810b0312200d4060140055004d40d4a0b2513282191000407440d0002e42031906980545950300035403d00760902103000340081d54510b1541d29100c0c005002c030801c10007400144680080713000d01c031403030050842c1012005003542005620030f9a030562140d0384c1e80b0420b00380700b080707010000c1c06904a102242e40c15805590710340d4051810000003a40e00701c990444200780e8481c6099441039610450071808440080d1001307070002c1d00900d039841640d6401d000c491610b005c018042d1a00180b009402c0b0325240300500b00304d505400c40c0041c6d0f00c045404016a001800d021006840b440c0d480400f24440b0000c9845074200d8040d80030807441809000c0e0f8120740039290000c042d941d401000803000303400307408180c40e0b007445c040584c188400005580d0010500038807680c42d0030560145003e0048a25030821194254195400c001e802c2800f0003000c881d80c0d1031001d03084003603181e00c0c0c80000a03080c500d4a603c2003089400c104180e0f4000f402c03c000f2100c48403c0c2d810002407090000040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286913003 1250 286911753 286911767
    0x9070f0f200a05010c0504030305070b10051c02041b1d041d06040b01090e03070609031101020c06040c0f0305150406090602070302150a0204081011121f211101 70
    0x1c10000c50100071405a00e01c0300105501d007085005000a005600401c0021207013441140302c05000185e0601403140020391042c031094004032204c03040360328281c803480020300c81190715004603001d00721052410210f051500031000c8443c80601c4196400060302e00251030b411582c0001200070343c000050318880c0c0d031503501007ea0001010518004480341e00c807032954a2030283e9040e2052010300000240c2900c0c180102e0940c2141170000d0750808201d07a98400c041d00c00600102c0c01e000701e0018911007041c3c00d102904445000c00d008200b14105414407240c040e000c0d421291702e4810a26082c8081078001070750301152180c4c140c2c850266038842c18140000c018100008003d01d000080c0c2106060f4000350031424840001700c4081252109007078541280b00354800c004082c0c000148002c1c40300615403240501100c83d0384001d02c1d246003804035044802080300c6c1090080c1c0005000e6000f03000c2850f5510180845c10301d9502d011200c03040c02c50b8900c280420040c00f02c6c52004116180d41d1044030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286914253 1250 286913003 286913027
    0x9012d050f04200309030d050a1107151d01020406120b0303070b1e0c040e060a05010f05070201050d09030f140a090e13060e0303090114041a1f06021b09070f0f 70
    0xf10f05600c03410f095110076107a9120001c00d000c043c0c101400b03e4030b00c503940e03c608901507000310003a40c50404070b9a10f00d18145031407004e000c055a80e40d0700024004112514850f45c4c2c040210006aa9500340940034081c150001d43c41904507140801041c41c54400004071030059810040352030b0385030f9451401c82c2400c054404800d10b2a01c0c0030041c0400807260502034402d6a124542e0881d4075a608030500405007241c0c4606070008024050070305000c3e01613801402018018034110307117040c160809178001c0d24201c6404900051540250820f51170340091030464406840765124501303035580e04006c1450165004819040304040b01068424054a840c419190b50050042c01601b80440007281c50350411110803800c0d500307241c0d2158041c00911342d039034400c9502069004200220101c00c1c64070000050504a0005130700101d544103020004c1c4110040101c0c1d0300600040d4051020744c00d40c0c135403014010340074282d284c2c1448001c541281612001c0c0b02c00e071504051040400e202140c40c81034001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286915503 1250 286914253 286914311
    0x270319060603060b0906091605040812040608070804080405130e0a050f070b0408060a1d07031506050a0605160305041e03140f062409012d050f04 64
    0x1114800030000150012811a8011030041280070120001e002a40c0011120154032448050001d801c0c041a512209410991894218101500c5000c118070701080000b00038280040420100710250707108a0307169110102d49406405402c0503500c20903280194028144283c50f917020070011300702c44d5800745804a065804440c2c1801880c01c160b52680c84184840780340d8003c05502003510241213049904a60782070000b020241e43d01e600210040c1801102d800c4120a1000407440f2004101300d68405140a20440d5100070b00a03a040c1302207400c3e50748054010f1181603c1044116002401da814000c0c0d02d891081e001d00303051601300d590f48903d401101c41c030007003044820200443d118105003940d2103003c0c024030700c0c0d040c0c51005a403031401c022803445551100c80001c0303c6110308880340c0c203039a4006280d41d100321100b80c0020381c0503200360481d000480b4210070007410b400d100308840c120108898141401903060a000c20b000814046200e4012500d81e00703400c1d4480946801848001452 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286916753 1250 286915503 286915543
    0x2060906070803100b030907051c0b180c010c121220070201030f020301030c05120106092d09030e12030d0c0c0b010602060906010603050c0d0e071a2703 67
    0x14600907065800a8607400f0f0f500315884d60209031010a002141e010313050040c010803015251100f0004400c041405801c200e00c012740801001641031401c090091803448070203c180200c8150444c9058681c0c2c0c1c4880c10410803802400c041202d60000714000745140c070700304032884120700800011340300024280f107410051281c40c1c000b01e5524406840094400d0380e00340041ca4030701000c44140c0c0005c0c003025180d480310040c10442e031b20b03207402c1424030a040800086017003603a48924004864501c1d250040c07094921081c40302002030880008112062243c2c101705255180d10003c0c88841003c4010b07011300c105065210f18840104141c1d103038105188070621050080c1c00c40200b00c105554821108807003000c2c004070f406800483e60074440c190120061280c3c2c3c1c0b03481c600320060400030302955800700080040005c860507601031125000441c2004181c000e181070150190404018112002c07580b090208000a5080c4150305898042001038070440480102c0080c0c02d0522407c48492901c0c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286918003 1250 286916753 286916767
    0x3080325050a0f05040b03010504091703070309021002010c080a051b041526040f020f04050f010312090f0302060a02030408070906081005090307020909011e020d06060504050604030b0402060906 85
    0x711100611012019540c1c68000d00f400c1c1805450502650290141c000001d00061169003010303801213210030300518060b5040d4611840035540e03a8020f95940000030340314203000041d41030200d80d140590803584020080407038452402004600b019200c040d0140d11080814400001a10056540c400b494805aa10340c0d507407150461610481e010100460000458072500a0b008011004028444c07010001e155542d60f0350481d01c81d11107081260701403500403000d805500c41c0e02c6001c1c81440840044c407600c1d419400c180d141c0842c0c00b19600c1c10020032000a00c070581c00e0568000403240d040d120140c8881601b01c040e030170f42c059a04001d070385204260002a01812507040300381202c40d81010303228007242c010400300990fa0126500c0100da48208120b60050400c11181e40e40012074200000340105c010074241101340412a400c2400307a00429090104460380c410710009000c2410824501440c080200303044e80604d104c05010701d1a150009019074a82c9401c4480080c4001c140c181e072080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286919253 1250 286918003 286918007
    0x6050709052106071b060b0a0e040f1103030910051c290f1005092b05060f01050a03080304170d020c0f070b180111010c05030610020307080403080325 66
    0x1240c901c00ba1180b0601000c108513602400c60846001008000c1c502d203003040b629400302404400e0003107034001c50a8840050b101c0715101e160381c0a207200d42c0b5095805510380c07d0400081d051404503c2c4650010000c0c90311540e0780d03000e45400c941803410515121055035102825100741304401d010554248124001ca000c00c1c40b80d0080e01801d1f026a04aa0b84500c1c824484039035550f005058112041c040180c0e6900d015401512071268001c0014041c240d000ca940c5c074003901c07000e250041b448070f8501d642d020060705020203607005a4410242041d5858100002c0c5c07240350601c0043c1c080300c000004a0240064405150b10300040d06003025a600c031002c4120b0001d500512000043d40210580030f40040700205140c0b00300c03410004060304100f881c0e000004103800c0c0c42141c50512100498101151400780249078100720300c0d488864803440c0150a2145210541d04690215002005103000003030fa14000d81701529003040702291644e41d14840c641c0d0714403203022600144c4450440c0002015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286920503 1250 286919253 286919299
    0xf0f0d0b18070b0f0306060904020c07080318040e1518070620011a12030c01090f020f010c0302060703020703090e0f010f08030711041a0d080307090b030903070605070905 75
    0x12081400c50702c01c5591000441c0403402115a520140c190030000300b031030762a101d4050b207096040107100600e440410002d0074546005c41d8007003d01c603007001c0b44100318403070b561080341c03100350301501d09101ca030201c01c034400c1c3c65120304400c0038031506d4410f000c20042040400607404481450080798519903c4070409840400340c8420300450120a0001d210560410300030f8600c48003c40b41e003401d0303071100301081080602d0501520314040c0310903c007100c0c21410900602c210f040c01590302034200d01e01801800017812041c403519051001050540b0006075002984941c402c049290050f125070040c80c007140d401000b907105030751250b243e03420b0280440418500328100e602410840b841d0ba59902106522405002005483c0b00203c100d480d009c0e08158101a2034100c030303201062541000c078030000709a40f020f5002621140404400c2104482e001194403028002a1401c00d0039403500c60951035882c82407810007440140c4603c08a2071007801030030081c000c0c08000b01754801c3c450789003071408902 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286921753 1250 286920503 286920541
    0x20912010f0506010f021c0203210402040b0108090304120519060b03070801110708030a020f0403210305041110170c28090303110c130605010f0801050f0f0d0b 70
    0x6185850b010425541c004c4a030740c0420ba0681d0003518900c0c0903004c84031402c3c40345241031415404108041c0e00303034144450700c0890a407021000c40700c89003004c0c0140011501e810f2091410300a03881e0501030f194000009079011151203010a2002055a00d011400c04554000c4d04d0402c800b40440b403c100300050700200510841601103501e0036565401e0389017a501b080c183e0b03003100c00003049240c010910040003981d01004e5040094680183e031022070203958820761090703407262420989242090b544940345541c0e04540d10f4217003c542081d4960b038041c03d58500d1428880c4910301c014240302d6008042044418115603074440c9146404810190668061549000301344a07020303480e0780c0d0210080107a50301c01c82c3c6a4070810414110781d0180c440034500b408103561481002c00400842d84d0300e0041c0c11320642002d1010641c50724260015011542a8400e00b00344419440107100302c2d2680b0108075001001202c09011420691020440c80d225000010f81030074101c10070086610b140c2d6441c10380c0c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286923003 1250 286921753 286921781
    0x90b0304060c111203010612090f0f1b0b0301061d10081b0f07020d02240417010c120f020f030103050c01090509041a1b0703030c141303021302091201 66
    0x780603d910110b62a201c0d00014100700301c8040c4014400c46228803900d01458520450000b8103660b1034030b50040d031003140201110440d061041d2402004802060b0720610381240364000d4109040ca04828030a000501404c01004087c111a4980081110120061803400b0305800031582d4009001082e20f1000c6030403da901080844aa810200140894042c1d40303490000c5070030602903500704103060207280e07000c3c2c0e40892061900411102c140b4000c2c500e0305081243c003503446103040c5180064540c040006034469150412f82c0026540058801545652183d0005002001c60038030000900030540103001d8440084004010488002596075589a0076203503288440e0350703582080400801124000c0c070b40704484040640b407180c06515103030400f002160007000580e900e440400c0c0e81d0404501640000d848442194000f50026103007a280e14030300c002c0314a09402d4440c511042002844003d003c0d10805100016401f0607038107403501c000000b002c100c07205020f000d007079019001074542005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286924253 1250 286923003 286923017
    0xc040606020a0b0c0c01110a02030904180f022101060303030b030f0d14030405120304121d0102031b03040b040b04141e040902010309150c0915050910090b0304060c 72
    0x61038900000e03981e054164424a0942c80d540d60800440c40e54003d8480000d6547d00d4201041c800c580010182582000c0c5900464030344501e581044180d0b141ca8016465000c0030a031001c010a10303401150750841d40584506460380e02502c1501d06500c94072020074825480c2000c04402c0690540000050420072803c442c56410400c80232070b1102c00000b00c150202e9600750b16080c101940101465100d0300560070f840d43c0700442c00f21403d440d84121000c4400344524001c050070349070400500c4003c2460038408114540311540081c4d503074402d0005012108214405808404104000b1140a0a1a610503c1c0c0303c1d03985154403100c68005001d0300480c1d0889101c0c200741070401b40020708502011041c02d528016481e81400001c01c00900241d041613101c580010201c0d4294182c880c00700c2182c030700000c0f0a030341c50f900103000503003036042000e00700c01500c0000d606a521030300f51610070204458018070320004007002d41d0150281c0d8000d9003482c4000c0100001c0c020316a00c1040c203640c00307480b200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286925503 1250 286924253 286924259
    0xc090603050c040b031b0405040f0e0d08162a0609030f0309020a170c0a03140f0f030306010e03071508060a061e05031003021203090411030708010506070f140c0406 72
    0x3841c140a24060308031413100600005540d0000455211103088100414500e8a40c0700c5000c2030580c3c06000c03903440304949812500480c150104940ca542d1012850b202106080c02c0810301401c590a45400040003c0c941b004000740c030f42e050307400500c03045214005142240c280b4054014081e134003c150080b464481800b4041030082c00f4410300642d000b0101103407142010500340c0310340001c1c009201c041c071841c2c242841c80e480340d070722a40241d40a540001c115180c3c01192510700302c2980d001c00038079000400c0b40c01c2c00b00d50000903250030000900303100c105608602d002c2441c0c640580c2c001d03804020700034100c034011504015030501400e0195200100350391600f07030a403a20180d20000704c460000c15080750000710b00c00e40c05181c000880904e0690365a60b07940005214065000b000e1001350000a00844d19107000d2040c0800c42c0c20881c1c0b840d0440c901000003420030007052060500401d0b000a0700b00c208091028518241079104011000705514000107665416100c40d0403409186804004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286926753 1250 286925503 286925521
    0x9033405090f04060f0f0f09050c031204090905010e0a08040816080303041211030a210902090a0509120301030f14060c041e050a080d17040b0402041e0c09060305 71
    0x11481003100840011240c0c491341e13280f80c000c0160101210501e42d0f20300d1040b4a092140c02a03e114900f00c403000700c1c8a821508109040080560a50b4441e41c002481152000c000d001030740c0071168002030001d5150000d05040f400b40400c01040c18680c054444410200800040508162020f4000b142c0c0f045161000d190112011805414607e6000388009000039a040202003810080c503d404a0070700c0081841030703c0c54100d400d031003011035803842c1c2184202d4240c02c6402080e2044420a1210ba4074907008556184009481d22050325280e2000440d503007030811440085885052229039290b03581e003001c00807162400b00c1110024528000723000000300009280c4c1c014100c17030304810310b4540343c03d44190204000b444140700300040090002000d644a60081c0c0c02030400d40b014013005020b103e0000e1050702800d5200350100750210a010102c0c00000c18140d00aa0607200082c401781c124255510b15040c4844200c0e260341000d8102003801d42c4103d00400311405520207002c0340c1c98002403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286928003 1250 286926753 286926769
    0xc01110313060c1727030304021c0309030206070f060f0b010e101b0605160c1e061d070603110405100f0513141c020306060609033405 59
    0x14104004200000c880890920b5108041c880c0c003a0034000c903107404440142801d44c804848801d008902d00729440003d0800c00f000710018a9003a01840c650b00d0a540054007002c0b6904a081421321400811810540100342420285800038a615210b41d034500e4000800a01400c0c21a0030303a0a04030b080014028a02420b0100c02c0140c48000d01c624003201404900c00412158800700000080060b01204d0304204c0c2150031409003801041c0d502d08000d240b1001048100d9050420000418a02c04502180000094001d005210345040810b03424480040c020b800c007420401001d014907840b81080000d0020102c840e19241070082c1c01300328602c0384503409544261504501070040c903003240f43c451400581180800c3c01c20718100122403000d110110301c55000080401d5108041410300c2c506455030742829484802d54241000080d80071a8a030030b000b401150081300d000c42c04030010b950502c9480c142c1c4085c484411705903030110000000400d4401030215081c84800004180fa05009030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286929253 1250 286928003 286928011
    0x106030c141e060a050f0c0a110a03080a2d02010912050c10181202070305101b111009030206010e0109020702011d03160611251806030503040b0c011103 67
    0x92150315074201d0920403d40d100f408004c04000c1c0420200c0000c4000c18094010707862644028080c4852529101200c068503441c4d071441071100360400c00018440800322a116403141c1b0341090aa0640084120411240410808950028440c2e40081075055000c040281c0c000c000e6408090280c40e0240c2d41441610303030100d555000031031340e0030000000d40c00581070190001c1200c7c090041540791254107548150b8568016000144200248030080240314a00f52042104100c100f0703000c0c080c0d45190754000c0d0084c0a21007044d8905a07030030ba0070b00941001c90903140e4148480e846505d0001d480d4076090240b4940400b010b400030407183e210340700347ca0140d94181c41e11082507443c10740c0701d4014540c0f00745081e818419101600148481c001001c0e004101c1c5444400482180662807030808070103070990072604641e104c0e202d41200410b05024202e6650003102c841460103c0d4a0384080d182e190001782041c070001500045485c1d10000500041401d030008203c2c030140b003900396030300c1c1c40f06076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286930503 1250 286929253 286929289
    0xd0501140c0f0711030703020913052a01110c060a120e01020408060403050f0c03041214010b090c07060e06090a0203151306020c0102120103031116080d051b0106030c14 74
    0xf00803840082c0408040100114004044406682d0b8039030009484010440e1405d54000404901ca03003009001c0103030410403c07507583c010b00340951161001402440e007900e51410860095840300220200303200c2d4001c16040941016590400c1e00009070051141507801c0509614003025500011410310a0b00c003590107160242c1055280e1b030320201d42a42103030a410300790f01e00400c01c40350100c2d810401000204200d00200c01d21011b242003006034085040d403000c1c55641400c0d008071340f43d80c43c94080c42d403114200000c0e94494420741810ba00a1000081424662003280f05000d0b135640b0001e210f000382882101200c0c0e03040c90401180090b28420348031581104085130b491400140705802030888400d00301c00045c2480e280d404401c4182a013a030007a4042400e0740402d640c030840901c240f0b00c40f24002c00c4070088030b42c0340c0851551341c0c4122071410701c100300b800f00700007402502505080e10300d41180b000901c036007500c07420060030403581403107400030307400a08404824a081c4003880d058020400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286931753 1250 286930503 286930507
    0x30303010b28080f1f2d090501080607020d08010501080601031e090201110c15091c0b060a1508160504050a0e060a0f05060d0207050c0d0501140c0f 65
    0x2000031500c0d40e070441c10303882649100420405550842d20310030003a080000782c0d074454007814841030314120b00794043c00800c40103807591080110700d0003490304e0310704440100d450720307004d00350300b03000c103032114030740c0f00080007201d8860303000142c0040e0035041141a1038146c07003a2409074807282c0f01a40d442d8056003204010030010801004158000c0e186154009010f040201c6c1b00c2c007c0821540068404141054961313030349001800c259648441e072609070126030b2004040a000d1400002c80c98900250401d4844800140311100e0391102003040140c0024010010f02d511045e00e00400c042030101c40c2d440c0503a035011030000d02c03125003100c00550300005440317522050b2540d041c2008501380b0540c60708203104041000060b162111684440101044003400704ac80c2080c100300010344440ba03001402403500c03c0c00a00a0359501030031a1046950040b0050303840d24580b80441c24501d2241820b603020b00c1509450042c00010f4000300000602800d501e04c0700c0d521001c0c0040140915000d0f500d0314001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286933003 1250 286931753 286931759
    0x6051b03071704050c0a06030f0b01050a09030809040e0a0506070201140f0609042402040906050a0b0f3603010f09030801091a060705010606020f070303080604180b0c09010f08040203030301 83
    0x2c8060910b410600a000b5030301c1180c11030011403a0b034683da40c0802c1c0002d941c0c501000d84d0480d00d11070900d41c61000d1030b00d5072802e100d100e8001c0c845203a500000c1d01c11600001d80391981d6071f031f0703038003015080000000381c0d00400141e042660711140112661700265003060780214112000e19202c80c4605003005060744951201c100b4030144040c0104115054920400802c05407060109240d03404002058050b0f51142401034202c2640c5913a4400350080050030400d001031045c1005451700c1c2a0400c0e800c94441e00a881008015164141400a0348200500703001c0f444001e0f0301344007043c0c441074000303200e8148070f400c0c0e40040b21420800500004c3d110001408001030303d401c411000e02010100e215501c3e44403001446550083d9001c4580c1c0e0b543d8030342000a42e070180042001c00345400b0250003d5882d60314060005200180514480d540d82c044030540c0c03062800c2803840094121064580d90b18007a446e128a41d40b20101e00e40c081180c1c1005c5401091003802a00c0c800e9902070301031030950746 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286934253 1250 286933003 286933037
    0x106030e0604060f090b040b151e19030c080604060b1f080703020c190501060e0f31030918022502030f15010e070309020105090112060504020706051b0307 68
    0x55050940b138946030301c0b1010480805d0f8081025070149010b02070400450820070295248004403080160242a0b07c4a0076100401440b50020302c00303000759019107020070b202182e18600f600329040100080058036011030415800141103104520411040010500c1030041043d5030552414844c0d0186010003000625440780600d00d400c1000c50901500b40101401403e0510806543d5105e40700a220b8104091007000d01542c00140780d4640840968101040030ba007001030014403c0030b414104141a2103981c1c1002461203903055000c1011340c40381c245290040c00c0300c04e540703d841c0f00c0f60010104e90141814078400c540641002c28640d80c0500c40b4505264001c51403114142d9040c000ca811803901300714240084c810843c440c0f0280203440d814000c011010b1000a40712808251a040e41500180d0f00042107038840c034005d0078048215412694840302a0109410403070b00280086810340400c400307900128000d201140d07440030421000c0106200138001100c0500001c0c1d100718440700c441d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286935503 1250 286934253 286934261
    0x6090a0e0c01140c07060206041104050f131b09020717090a0e041e050d0225051306080717210f18030102161202060708010603020c0304090e070e0106030e060406 71
    0x140c102e600c2d01e0614160340c0c4c0c20360401026034050405604000204030800200c1d071f42e98948100112410446410030b4a94a0030003040100020341008440c2c005c8000d00c5030014242d00c100b00305807600c0943c40d0716600888086c1d04560030031109030700c40b440010701e010114000d8442004001e000010480e2508041001070b00f03020700281c501c18281c80c00c452204400020042d0301902841c003c1c4401c1128040c002e20f801c03041e6250390300c1d020841c40b036031401d0300308842c034001114021a01c419580306410076100040055a1140d9114422648001240440c03030303040580c2c02040340f00b91000d50445002010740041604200c0c409038604100171215028a10301520044100c1c9203a810310000c4000800e08a80c000c41c0d13111403040c10241041e080007403d1a00c0450a081391020b88928249010301426050042c06a1014540c01241d01c04002004009541c000c200040c0c0900c4030760807681103152524000d02070125081e0304500080707051170190080d5041080c41c0d50080059594a440d03101c010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286936753 1250 286935503 286935527
    0x31b01050d140f071103160303021b0d021006060519030c021002040e0105040513030e040506010212041d010602071404020304020a0905040b0601020f010b0108240607060506090a0e0c01 81
    0x99070760710031032078031640c692444601c115080600e520703d604114001415090801100d424158020011000e407103030b0300503d00c0780c0203505040250b12014021044030108074500c0c42803619105008500c00b01b194005103400721200302c90340401c03444d501d405085401d841008082c141c0150140d503250503640c8694000201c40f4603904c1070358201c2c08080d0340e90050340d00503400001c1d6142010011f1110b031900740304641d00100d01c01c03800304080001341d0300945401c03100110703180b00700d98031400158983d000380030450140d030301d01c1c40e090b55464841e08209545107100000d0525092000000f060081c000104034007a200c0f803a0074040e0502400c1e04100196000038402ca812015503440041c80003480d0092a000b544242501d01891410100081c60000003005e044026070406a06084c1640c0004c1e1b10354004451309008000e01c2c004000c4440c040703540005080d0009800204030040c060b180d1300040c050502140c20401580350320040e4026101c3c003400c17191054100c0c80094111790300070000c1e9527030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286938003 1250 286936753 286936777
    0xc0e040605150c0f06010605071106040e0403081f0801050a0b030a0305030406090503040509010801021e030c0921030a050c070515040e15030102040906030515010e130317040c06020606031b0105 85
    0x100c504c500d43c81d50a191080e8444c80100f800820080c0400c450401d801000982c161051802c19140201c0540140b00c0500064240812100862405404416004603d0091250301c1c3c640540e500c400b07a001f060125642c03003040d407510b00d1803240c40c600410154160b07609541e4044c159112502d451004048801089038148800c000025150301c4016840380201500800180c441888003c0c44000c1040780b5015030540c00c0400810130b1b0344451b4415904500390550700e0145005107018180c441140380000d100d4207100c0818810380e0103500c04000c1c1445907950081c0c032812960741080c801c0c0100305600c20400c1031170522050044940450906900c28021002c04642c101ca10303000c00e007280d1140d008140300c540c0300e40061080c42030030400350002d02180400710143d503240040c0044600c0018003910a4803039410f410f10f040c144a01c2c0892400c0901070b0100c141803c3c1031506000750345540c491107025004c0d1000281c01ca01d408034401e1200c0302c400d420589415804401100c00790b02c20184d03802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286939253 1250 286938003 286938013
    0x61106041a0a0605040504110916140a021204090e0d030902060a030c030914010509070e19020a05040b13050a12050601140a03082d0c03160206090d03030c0e040605150c 74
    0x101da5507240030740e1f4040c41c000d03603440c1c07020100301d4140940d50800800b03031509910484001104540e014240c0503809510030b01217500c1ea44001e0ac200c0c1850321700d12110300e00600101c1d01044040141c0d20103103000342c41301d040301e079000300120042d402d0702c429010180d445141402003c1c24940039811081b0301d200203180c0000c01c05103d684d142e068a91400c0d001800c2d0b03540d40c1c2045035840c0200305d510090a001210700156141600210309801d00ca0b0700201e05c815008a540d0b407680b40100c05417405003810703281240d15035201032034901c4401e400b4440c0600c00c43c00304800248140c20b5108015000d501302c000b60045a0801242c028900c80b00020030b42c1144a80740000003181811000d016580d48520511001400040e46210a000b0b04454110207102c1003240c2a08008008210340000e21401c0384055850303841c0c000a4490300a49412641010441103c9020168554031200248065403104562203000d5014001150b08602410380c108081c424545a00803200014108125011045079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286940503 1250 286939253 286939259
    0xf040606150824030a02060a170712060b0906090405060312120a0c050301060c12230904050109150608090a05250503010504080301090b0f1504061106041a0a06 70
    0x8080c50034440180e40001e141c2c2800d00a00400002c280e25403182c11490a680d0b28001e9000241c4911040c000284102000a120000315000b00030100510807010440e51340c03850320100103480c9400807415010307103030324000c4041000c095080941d5001c1c00301a1107a410300c0c0b00d00d0240306c010300c00a03002607494800c01940c0016402d00400920130070b40700c00c03408043c41c00d014184e00259151900340e8014044144014020180e100350b1401b0210340046480d0440480514141c0e0b904201d07170000307082009410000d40640031644000c0c0b0214030203132030070407603030703a80760031a5048555101242040e040c035081d04003c0b0901c510760f4103400807138031010f8800e25100c0c0d6440a207054001482035210702d0601041011080f80c841d1010b009042c194024040c503e0281d40c0d41d66544014061404078903940c2c0302111954075078850f03003c8584009842e0545e45405800080d072140c20620441d40064103011a0552400e00495818001c6a00c583d13032203280300b40e140550b58485001004010303810f684107400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286941753 1250 286940503 286940519
    0x11030121020d02030712050114061c06060518070809010c050f070c0509040516060c03050702011b020a081b01030204030c0905040f0b19140405070302210616030b0907080f040606 78
    0x1030300040502c070909412046e8a4a08a402d40d0f50410340058410301c52400c024540d01e0304078400c00000122036010311720901c940f503c40000e241a4000680014500400c1c840c0e0032041d10f1220f0142c0038941b13035a1b42c3e6580704c0d41c0c01426a401200010300241c0188000142d0b000700d803003e00040b41c8100c106501060315000842d017442002ca400b0f58150f4840c440e0420819a0002c01d2000b611103850659000e01742514007410341c0c800c8240080c1002000000c1200081c40001154070300ca0380140303241e03072041c0c0d030342400c6075184486890207082d604c000307400030100e6001c0e1003110304482e4050108000189408100d400401004009860500c82d80b840320000a10784681944201c070411200b0030919040340a80307044031702e118085401450750344103100c00f1030700020341d280c11685d04a40ca02602c140300441c5241911101c14454440c0c402c00d410f11082c81c038007550b00031003101950b604121411041e010003100325016108407021800c4240803c00b803a0f143c906181e8807902400700400c0c259510810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286943003 1250 286941753 286941763
    0xc030209061507051633021e07030303200f0f040312080402030c0f010801030b06061306030e0c0a050f12010b061809060d0308070c0201140703120e060c12041b0806040611030121020d0203 82
    0x484055812041c42030042540510502210805491450480207042880c1d4500c0384119100b044c5001d50103fa0045001041003c4601450f40f0800c581003e012815000d840b182050b50b040707106c0e015900c0d192100e0308015a65885d800c0d0140e50b501032907481d644902034030a030042d0065400c41400c2001840c1d2402003907189004007003596001414505c0d5144503404d0103003070301d81c9511071141c1c8c0d0710400031941d03540300e894440881150300d149241a01402c076401010391042c500e81000c0c0105009040c2e49a044c41c403d55480146c42009036655004100108100c5801d4000e003c210b184001c1000b040c4110710f184590751045c18890542c10b4044088140c9070000c0307c00300d000070300c5a000d507100d145050142e405290004002000c2c0c906000e5032030301c054092202c2158140e0900400a02400591000e00400440b2079801c40704a94580031040d031554400c032801d444141c2003d8040000b886200203c90481c1ca0018109141c0304082040785200d682012090349d000045842100c00350f542407007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286944253 1250 286943003 286943053
    0x12060405030c01050109181101090512010b0306060f011b1103070b0a180f091a100e01020610210819030b0f0306040c03020906150705163302 62
    0x8544400c102e200390350942c2d4050700652101401c1c0090040080060006841c0c0e80d544500355440f030071015001242c5901e86503004560115010340b800606560644c40211807900c15429520304c3d940c0c1e501400701444c4540011070010748024a40784620748040e245e03000181c0310f000c186244902c0c1c071000030700e42030840d08a40c2409900144504103d6000000c081088030f55a44040402d0b00e0a004002184098412404007a49400f4200a4100c80e400011000400140078244d140c0903160002d0840252003000703400342c030903040860484100d10715403a0131118481c00c50320a89404c1d40139a03c240720300c408112a600803e00c14050500f4440c0c2e2407920407500350342c0004524240c001082020140340050900a400c03c20038480400c110003002070a407601920031008940b039000100c0c120403601030144001d0a004149d060400001042940c1ca02d03200301500301c2c9541d1114642040110030740303400420782600442e14100b2100716409061900094019903e01d0400c802140d23501000c3d0701 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286945503 1250 286944253 286944263
    0x308070206071a090c270115090803040308030402041d10181202150a110909070c0c081515090a09020f120a060c05030112060905010902100c050606090c0d0506120604 73
    0x1210700100d5040c4411401c44116481030206e5025007481d1906104c2c5006015100403062000e50f005441c900440d002e0004210440860796590f44d81d05018029400c103850891003142004078110b1401407260302010390b01c0c200030280001c2103006041c0d1000304081401c090025000f8640c88000c40e101c0d016803801090309402600440710700520400c035007500105803c03401c52030110422090400e82c004e80304030740d9060350f403080b02d40c0b1210340558810350780c0500148000c1070481c1c0070814080c082070b0b10700707001c481101480309600c507039001d00b4011040c0d14005801c4545003000502d407810a03081405040e001501007589444800d0110321144030f8a1a507110036405000e084081021920400144240b83c1c9446411541840d040902e4046026000b41140f42c8131070b080f40c01c2c004207520030383c580f55008041c4c1c440d41241070005419281a004180c8550244030006141c81c1840c8241c01d220344030000200d07141440b41e1180c40001c10000d0155900302c50b02403e84d0316504010002e69024600036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286946753 1250 286945503 286945513
    0x70222020315041e1a030a0525050f0f130609140a06080607080702030d181412030a020c0723032505010f02011e1b0206010308070206071a09 62
    0x31100d000303842c1071141c000c18010f07840c1c0040c60120006604500100c00e888107808180284025070718541c401040d0302c4198903000d0f04144404000000030034405c4140c9000e54410f03481c4000300701120341c074150311400d6000904460741036800e10b8808000411524010b049084a040b401491002c80368250007491200303a030341440c024810030154071280c0c42511050140512070900005503101d0b24041c010b00c09100040000c2131401d8020700943d840b240315038500b000300d41d050b02d01030150b12252005c00c3da15201c8072481c050750300c0360200d404240d09880183e1545103807540c2c0c5001d002075100292504607070044540100d041525800f1040c406201070352001103000208040508041d014104020349481c01025000030720035100c0044105c400c2420981d00a0b0048801030b405058156541c0c000c0140e4034050b80b00400c1254080c400344105040c1d40d086120500d041031f80d5420003030002070700800301404100e00500d8407c1c01401039911074010042c0111038410f08248600e020784480fa102d03001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286948003 1250 286946753 286946761
    0x1401110a031d0a120f03110d030c141e0c0a1406040201030b1f140c0604030c21050913060b0318190b0a0504051609020309100207020112020702220203 66
    0x221001c59000c800040f114001080e00d841c41d00410f1900e880802032002d1540f0b0100410305003d55400300c4405001c0c4140d500c560382c403410040051007000c00c281c002c0354442c56a45005a0b141082e201240005134050100c10100c0108510540000000c24558800c0c0c3c101100054035980740000c010741d858004103e41d06252002405603019682d231240101c040c0882a4075684903e02004500e0006051070752813091101840c9400d4070070240e0356020b52140105201c100355100401c0b45100c3e005801624520b075419001502ca0359403903648000044080c01006a44d04d00389039000c0c4002003000000801d10b0b6260003100d00e54108440141083c9460b091501080e00180f01e0030300c2c0e001c8010700e803100c1c00c10559650554114041c1040c68001e684a00040802004018210030303c03a0b174199008142c0da5a00c201406580110b80041c05405200310662480e070240c025142d18681c16104c000c00d040ea0400100c000f034000b04001d991180b80500301c0c00c191400c000341c0755080041040c000da50703443c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286949253 1250 286948003 286948037
    0x40f030308220206040b0310030803010621021e1605060106080a0e07030201090611010906180201020c0319081e0d060e070f09051908010c0810061403011401110a03 72
    0x6481c00a03400c09000c01c541440c016030b1031801315016190586d605c1a181e4450381c0b0003600c054000d801c0104621320020002c944150848080a034080d030111010b12030000301e800903401c0e0701402c0000e5070800c5000c070a610b03010000d60f02603e05c40c4503044110414045030b494aa2078100300b039010102141d10841808066056401201c40c2c100400000b00b40c2039103503500081503540b0300e00c0b4072001c01c04c200d01d14101441d002e42246280542000301401440c145101d02c0d44a505010001c0b400742c8902c50130040941001304040303103103c034074280d00c40708901103032141d400580c401c03042c000700c01d080716414ac4100b0f100c040c007800d104040c41e50700241d180c2c00cac1070035032041e0311000c1e00c040240329011801c0480b06511290309010f079a81078554002c100055801e001c0f191003180c128034900d5003458801c3c1941030740200d1907441548031000340b5109640c0c402050750051491b000d0804410340410040c030014081001c16500448185400354031104542c810600780801c0e400f00701c00240034036a000b60081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286950503 1250 286949253 286949281
    0x10f0f1d010c170414072c0f0a0905210714060f01061b2306100806070315030506240a120b04080405120a0c0e0705180303040f030308 59
    0x4401040204020282d08a010f420495400002c000d02c1101800107020052542500032510354214100d814040d00e803500b03420b0a5054076076110454010b04041c0e6801c03200e20740786501845558400044030303240c10407424003030a541e03402500c20f8824184800d00003031010000c040700040c0c400e01a500d0345440e01e4a016410140010850b0581c040d005110561800010540c116071040c140568071406281c00410050200e8801401e40310000b00c410040c01840c090210440070b85600fa00c3c60356a070039103100b007105018012050740d548860700003801d65001381e124020b6250448003880a56980382e40f035602c1c0180403500038143c480c01001d81c4c190404400074000c40c608007228401521420070310480c40c0c9407012107025242c083c880010805100351032007228051700014280e440802e038090101580c034006484211001c50f00c081d000070708030b030820b0811070085a807683c90903d0091709185802c1e0085001c0c1e0391a074140010800050080300111400d00194402d40b0340c0c40103440c213055110894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286951753 1250 286950503 286950551
    0x507080a030c170402011d03120c0304080118080d020c102931021303030c03020d05070b010302091915030203061f06110f0703030314071707030c02010f0f 68
    0xb50f140750305100040c0e80001704204c03c071514900c0d502003c0075100c0001e103041541500a00c140100040750900d2600c080000c006423082e0030000d1140503030f4400600c2d4009080c1c1000b9001c0d482c144100d61503402144c0082070380381c1c000e20071911520000b005a030202d65040341c895141003114003019054034400c803103400740700e40200c402107410004868011a1001c07004c41c03269910b4040d0a221300084020342c1a61b640b82e81000136806c0c840d45924015000c505541410ba005d88034400000c1c02c0d480c407420486842942c81002c00c01f01d64a10b500b0b1000c45500544811040904640040e070300050720302c181703034188a40303429405245145005240c24084c0c003030300e4410180f1021621303040803c01003004408590b0103203801003602d410dc0c000c55051200d010026112802890800024180c1c5a0408010711a9008a0342c2281d2925207054a11441c0d25640840c0b2281e18000074414034000d91114100030001c2c000810b14183d001c80d0481100c01d17900d01604d24a41c0e41c00f4100070044005049005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286953003 1250 286951753 286951787
    0xf130306051303050d020708070c0602030430230105071d010311030c0a200615010302090a060305070201091403030907050303030702030904050c040306020c011a0402040f090c0507080a030c 83
    0x141c20103a40300107044d84680480c0074120368000a00c0c1c5d00b0442084115180c2c1c80d088000769074200d4503101d00079101e80c024840c0c03d034140b180c42000a19034010540d0b900040001c640012240d50166945e4105050580190b030140c0c1000203c4140e491004c4c0030b11481110342d550342c40b109803800c4501919002c01940d000d8101132500d1201240011400c08030b91300141268000c40d124003101d0411601010000c00090380d08400c400d6a85049800003200e900451103045000c0060441600460480c004c0401c03107584025000e1041005600a40c4103540101d03940c800490380e408251508651801c0140c640e180a60000003007040c4444240000c40213070200b18055840c604013410002c0d0350f80200c00940c0e22030f030759a001052900c082c0c5001c6400469010304190f480d0300030314180da030081000007031401a16400910000c2039107802d00c2240c0c01c1d280c214131200d0340241007d580000420baa014403406000c1d0401c012008145100050048403015070780c0881c1403512458010700c101c1c000d03110001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286954253 1250 286953003 286953031
    0xc02062217030a1704080c070602101b0509040c090b070c030b060102011503110f040c020604020315070c060b04180b04060f020708091309080409150503071d0901020f13030605 77
    0x20903800201e0081d241040d03010902030340c469086c003885502c28241c48030b105200c2d000000441c2c40e00031846c05071b50448240d08000400f0801c203c02014220044510002103040080c01c1c52854503620825000159180c000ea942d619000c0f0380200b944000e0090f10b5807407600404008002404100c1d9070300082c00c0c402401110040c511301d070784c80d03c413030300008040e25050890300c4403c1d16030b540540c60a174801007090020309204403000e52038135000e071416802802400d01d03a0310020080c5440500a100c40d90f6002011551925080700601c1c1c40817007268401c0c0c071810141031841e594461408594025040030289040c50318002c81140c192a18400d44030f801801076501290b0010103640d030004050b40c499103125180180d110003410f402070010061100400c01181942040d400392080960030440f1b4010192210101070750b802e43d51140100d164120f000254082c1360210030700e90031206030000036040c0f40c41c1284042030358201d0811960001200c00c001c02c20f20401340111600b01d030060368100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286955503 1250 286954253 286954267
    0x804031d151b0d1e030b040609090b0604110316030b090403261312030f2d0e060a1d0f1506010509090103080307090b0d020406020f060106020c010c0206221703 70
    0x150000840489116565012136120150507020b81c1060001410007041005000d80340c4000500610500d80c0a0700d4035201c05000600701c0c101841000d00c4800c0046044d811603950f80850341800c0d1602140341c0c01c05840350400420794032004817a50246100e42c48142c2480a064210500c070038070b6030f00070150b1a050350180005d4a40541e980c401c81504452410704500840d28150090034242200e003400501d080341040e4034080301441c0e150032441a00b114801d2000c4142050103495020014540d29000307900800c08807841c40d40061240d0380307050390074809100b209980600300500c042c01510540c0006d200110100354014001d540800300f401d0450400e602c260120344012030501000381030344000808079071034074001c0c03403560020450900099a10541c0c191580c010390410b01c41d5070b0140c0f040c03401c81c00b4030142c0490240d06890296005088480e0316800444010340800400d07038003d082040300b00017156600c06103a204000701e100d10200f017860036000d20010040042c01400c50b8206100d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286956753 1250 286955503 286955507
    0x30c060f071209080418060503012904020c0f0604050c04150e07121d0f0106050d0f08030712061e0509090d120204050a0608070e060a0804031d151b0d 66
    0x100a40d500e11800007410305140c941075002d40b2aa80014101c600d1b0307002c4200c62070009802001c00d0702c1c8190001d011901c5500401c1050341c140703c03811038007440c81201a650904180d4040d21040340702c24210390300c02e91040041070404400b5281520140c1206200490707505260103407120340b03a1007221007030080c0d103004403500b200403000d02040c040200c0701c1c11581ca004090340101201090a00b030415205004200c0e4079595007590303c42d81030315400c000e8002205e10702140306850032500314560000b00d5070156907501d07150703000814440c28410510750a80d000b1106100f1400544040c1da0540b15242840c806004410820b0703000358801d2459008001c898400496084401c1d10582002404148090ba03000083d00803074000c1ea80000342e8020000d0703110703807001130039000b840b242e101c0c681e044285a0a0200074031580303410380c1c040344e0f0b040301040020744a686210705805020303000311010007055000851654561000710a84140402d448440e100b241c3c0440503444096001440f03a10300b45100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286958003 1250 286956753 286956767
    0x106200a030509100e060409140f040c060f0215010b1c05041509031b0c150504080a02010e0111010c020309040c0203071205090a09050f250c150e0f030c060f07 70
    0x406004d400d02d5910301c148130740140c00f819180c01000f007281d51225151188680209048900c1401c803a0003980810105109040c1080c01140c125203842451401c101007686c08410706c469101c114460707010f44146d40f240d5440102c0c0038186074690903030f6804a12000680d078140c820400700140303141c80140400030308422002d040da0141d843c004510104181001d0350750039045814001d40350303070700d02582c1c4c100440141c100098a02c0b80000c00722070780c1c25a804891701e0045001d10040c5910000485026600030100d0400d00031051511140b040400001682551a022010070259001084484582c80d1501580c0842034640c0f00a40c101691500d66024603000c02c898441800400903100203140c0f50417500f0409000b1403039050010b424003400101351b406045950307442c00b05010b000c00d40b8079266105844840e5595684119452200340c0303904011041d0b501000b10f405980349800041d0540900207c10f812680c18080d40d202d0741d5001002d810250018482100150030f03104024000f40c000c91 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286959253 1250 286958003 286958017
    0x7050a0b091f03020702030f061803072f060c100c11060f0402010203120426071101140d11040f0e07020601031104060e1906080c010f03090206070206030106200a0305 73
    0x34050030b1030448010160024070410801035010b00840c00d00c3d2103132040009106004200c50524654404807800d43d05407a40524840100011035400c029541c0300c480d82008a00341920a01e400341c0386c625003000443da41e0260306102041d0300b0101c44c1c41390312485441501d0b0080c210b030400108481c41c0070113617901c1c0e52000340b401d05540b4140f0045020342e44204152003140200704a001ea080c2082d00b0301345159500e0380401465403e210f106565900a0401600c4d050f0f0f82c0209040c03004001080103481c0246016964800843c05002a000380000340c011082c00441c1d0a9409541b1420244c81c2c500d0a02036070002d11902e481c202c240080140d00050050469406c450032001100800000901904007a40600198801c00050003314010100d498001c09801501040f00c940d1f504842074456815545041c003181010a040c08000e02980101c3e41c079500c0242818035004e03041d400039485420a030480c0d40090901e1200280030850600300c0d40d0000303008001003401c0c49031580c0003040d070310800c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286960503 1250 286959253 286959289
    0x80c0a03062007140613020616021f050d0506060a0e150d09060b1815130f05010e2409010b160c06020c0103180b27030a0207050a0b09 59
    0x501e40b8803800910407058240741000c6582c1d640c911240c02c08040c1800442c090841d14003075600800d60244110742e0a4108070740c0501403030304024120310807510303000c80108280d80102c0a41a0401d4051000c020020b4021194680790345030b0341d45005003c01c5440040000c1d0289904010074600260814001c441c8803008888a102e00d9510202e4144240200d8440500a6090050701d41c100401e60700302400c0c40e00240d17001e840358501001440c1d1100c40640341c500040a803d40d004180c0d00b03000207407034150f50120302c0c0030400400c0ca4419000300e860036800030703242c0c880340c209000e0b031284890a581d800300106200009d8840714000041d510a806104150a000002071b000507001421042d0112135900700240c9210039641d02806912081000c0e11580004c3c034040c80281344030303020f000a901c5590020840c82007a0348590a043c2c800700f807640b01c0302c000e1403640c0a10300c10a800304010039a00b01c0a42c050888503140c4002e00c00703065025000380e00141070a0145e2500b9459042003c681d0035011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286961753 1250 286960503 286960511
    0xd0206030411130c03050a27030806010201021b0706080906041106090f06030f01320603070302190c1a010e0a0b0109082d030f030406050907050612040c080c0a0306 72
    0xb000005181034014282050198100a500b040d00358066020038403174080780000744807440e210851070f1400b54802803600c160404040c0c10b0404240303e41100ba6100006000051070042c450070502401d0600c1090700c0c02950154006000360f90380207070340540021903030000f02180e051039540d0752143c0050441050161f400810344804e01d5a601480540000c03024000a5883c141070385404004c21090007903661480e20a904a00c40c800a48110000f6924034110141100d1042080040991015000c1c00416800b80f0582c48141100c6098001844941d200e00c061391a09181048044003200351140c21503000c0e800404c103500c0102d1030640c4c0301404a00000f4840d403560010b03640c0b0051608225183d2041c0e81a800302c010b00f5000078014201002042280e071010b42020b60b03a24803624205c001881c0b002d0000c5030000313011b60441070300304020f503090b07862403034980005c10466001011491350701071001c400c3c84188074484010300c0103818400040e11040c007510002c00d200c0c1e0030600c002440c1540e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286963003 1250 286961753 286961783
    0xc1505030705030f130f0b0603010b01090b0a03050a0902041b0f0302030103031e0c17040612050606070209040f0f2004090b060d06110a05130801020909010e07020124080c0d02060304 80
    0x51714400703500d0301d980581d00740e000c111281805010303c50226085d0b4025860001d09204c04c3d0701036414070049550511402d8030340141401d0480c05018003034400f681e416203078400c0c080140e6440c090422804900a07010648021071403008098159410610083c0340c070410050000c00c2d840407001d035850301050702c041010081c000b0211803500c2c2c007520141007c151014030341c0162501c0030003001210070319a00d81e8031112901c80c5200450710203650b125400303841044200c005052542005a000740100c1c0b108094030041d49440d480a5954802100d00b4003000c6012494020a01300c1191165000c0d102001440025a500003601c0400f50541d8452440380c4107000812400d5007101c0e02d9840d11007512a2145144a0003400a8104048161648030401c0000c104c180c0140700342e5281072002040141c007640380c044003d0540c10080c22010844d52a01050800010b003030400340c61074100307400c2180300390303140a100e0350800c1068918940300710140280c0c04050390381c8c0029680c00a800071404c45803052 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286964253 1250 286963003 286963021
    0x9031009020f3715020f0304090510120305210412080c040503070b04090c080705070f2f1507020325080d0201020d11030702030d0c090902070c1505030705030f 70
    0x200c03c019942c5000085070388910f108140c003c540480d009040d40342c0f0401030ba000c0590312500c401c01b501d1241d50040c40104001101b030340107181c1141400c140035030515100c2c03402c10010580c0660640106800280307018031500f02207009500d42529080c130350101e0034551364488003020502582c2040103610004142c00300e640100b2a401400000d04858856a40d0b15541c5001d8100340b28810300d00d8507001032003207000e01446101d807040035540c1c3c034a49030441d5990790351840502c5030000e0b1540e030403c15090f442460b000340c04800070340f200100b096004050804100b0020072070124549403c00621070800107880025000000412030305000a004030408140209842d80764851460b6100354202a19425019801005111210b45e020321641d6040321a40c5918401030302c040d401640b04020b0415a03c082c0d6014418003e404d00c0d210308082d81d0744440e00144d0b004004180c800e903215800c10404103034480400304074011b840c1401403c0d45024000074103207000060030003030008190000242d45903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286965503 1250 286964253 286964299
    0x303041b17070810051b0a0903080a05031512030703031d03030103140c0d02010f0309061103092a0d080a030209060706050108011515050c1009060209031009020f 71
    0x1c0c81d440a0050240c0d20030702964a50751440b421030103006002030744400403050b0045030300c078040405d0321024401540d00c014070594007000c1c5001c1040446000032001480003801440051601d0ba5440c0d16814a0381000040141b54030010f48615522104103c41c10000303c2a0341401b40c140c10002145a240082c00340000f02503080f00080380070000011007041b072a801c01c1601035003400304492204039443e081c41040205514003034040340c807000448143c548250841000b842c4906004907042251905080403500252604d4034650407a60b00b44400496080b8480070145100581510aa801c40c001c100c3d003d10f108005000f4080c0002c000c0e42140c06a0112a00f03800c0c043e040795950102400d21500501007801040d0941d400c150f0301344150f403260704544090b03400c0c1e00891005020a10804e540070340c00005050300502540d581c64003041c1042c031860103d1801180003582d40d5100c0004c05040900d450000c4040f40d1404984801588480891171071034102581c02101c0b203e603c07044070640d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286966753 1250 286965503 286965509
    0x1807210606030f080703091a09040e031210080f0c24120103060906060501050a0f120b03161707080307060f180f02010906020c06070209100312030605210303041b 71
    0x9180f848070741041640c00c02090321a000b0342d91644800c0e21000d010030030700700ea40340d5495401820700680805107445e52040300c00c3c5d120001100e10307203080700100b4416120f04594404400038440d00400c000d00b014020f416051a0090145c03020b001c2e0305e00041d01c4d401c1480c0c42040c41c0110359031224910b480750f0084440d400c1640000110969681c0741c864080c020b190011500c83d4140301d0000317001e502030016a8031250564841081613a84024200c407a400305201c0e001d41a8ac8400300c001a41e1024070111003072031402046c54480da4242010f00c082246155924151540078480402407821701000762552298017403008a00301002200b04c101410406024605a0700d80d01112130401c900c0525000b4800e100f82c8520710610381d990000e90300d525030102c3ca181c00440822006c0c00500c0c0c0704c01100d5100b030f4100c02500c0e00f242c481c1c880060391001c25a030400800d030348100901c000d20340180c0d031807081165080c280c400100c0c0396145503203c0c00042c00c020130016805103248105c0412100100107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286968003 1250 286966753 286966763
    0xa03030c08131a0c0c010305190902060d020703030509160b070b071707031508010501050a170102041505070c050d1a07090302030f0706090905040206040e0a14040b180721060603 78
    0x2060f100080d80c06100e40c0501d940304014416448812000e500030700600707100701c0408800003400140140808090329800710300701d80c8200c041201441c1e512103407000c0c101e400d000360b60004403803510306c00003440c06118000c44081210540c17010408889070230100c03004268068a001d1064507124019205500c6400c03010300c8804074401004003090f810f900c803280440f0b2041001c0e004660b5040480d00b05c0b942800303441e07042084400c00384403405003c400c1c40c246c0410304c80010301d000c0d0760f0801c000c2500b64500c686230003d00300007115401d101d109150714025210841c0d001400703d4441d5654603001c0403480d13142d0310000d5400300041e0741c14061803102008507000380642e10000c0000380c0702d41d1118140d00866000c56184900032031150168441c4611075680600030902d89410b016000001030b20082181c1c555646480282049024440203540258482c2980c1007150030b0000721144501400c00c00c1001702c0d80070703d00400106403d4000802040080010110702040c1070420300040c02940c0c2000d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286969253 1250 286968003 286968029
    0x2010b040606050c1c050d020903070e151503070507020103050402030a15020406110705030c090c0d02040b090109140d030f23090108061903020105090406030515090105060a03030c0813 81
    0x42c2540c2200043c400c00c1d02102c00d5031a03e90056407013281c182254100000050010b010050540c28564024080040700a044441c060380d20001d014812070111a840c0d1095441b440704070759400c101c8044689405011409400d5181c1800700804902541001904241d2500007180954070240102c100c50b0b6040a003055460300281311101c080c1d88a44510700010300d0301001000c5c41c082c040f42c0340c0c1c2030303076401005094560700032001c018800c9005412480c480d00d003086208025080c520040c4010321020304e0940d110086400003520004095010b00c1d000760310a0301c6400580d8a0008011800b035141c20090001500c0701e9045569400b136010700440780351100000719400503403070054201007400760703203040c1640e58480074444084500c0102842c0f0b4002204107000560184000e8055041d0240000880c2aa01e072100e61a06c11100d9034501403901060038400701c000207007c1c05d40d1114060718104d802c10310f103940c0142a030012000190044501003004c2a2601c00242c490303000b8040112184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286970503 1250 286969253 286969259
    0xc0d0b03010c0315150806061b07080c01020c090408030a0c03020918041709010c080a021f050402010909051003110f03010c080114010201050c0306010c0c03080a1224060f02010b0406 80
    0xc1c0c000c16034040100104ca0901e440092035080105411649002da0350305c0c82c0c099265907081c0041500700c5001c0c2d0600c070610b0418240c0b52003081040d00c00030400e9000805035200484000b80c140106511001d00900d01c1504200120303c2c1d10007107a40040b02d15000040300710740d2003005c030024014441d002c1d40c4400200d202900e802504c44040d802030b401107041c00f402c451003400c4c51940e0700c16030641d21301003031503400f0000c04540c505000e0507400045006890011300c09440c0d008580f105810501c00b81c0b55200300b400b080d56800b46074480a030448107420001424500c0c0304052180c203500c030007402c261007440100b45e40e0311049180115000c000d4024403000110800103001810240100b40070b0000a07030202d4000c0d841401200d024503030501c3c426180d40c1fa4003004480c0120b0010050703d030608417440c00000203c4180080007001c4080c1e845110003020a00f003c82901c0781ea400c1c0580f413400c130f03840010817205000ca5000c21503a80b4140b1807806200000b00f42d001d4203040030090382c013030300d40a000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286971753 1250 286970503 286970507
    0x1b150b0f060304030f0c1b121506050f04020903030f0c0f060a020a081b0c0f010c0f090e0106051c020324060a0206060613030501060b1b030708030c0d0b03010c 70
    0x4212a540122040810a402242400380e0790004580c0900028401448040403600444a02148a0180302c40740520500a030510040c290760382e01a204480300e040a50f014498030035600602311107102d90500c0240d00d040002a1860f00c2100c0d864842c1d540025003451668040044030502c41c1030f007607075544500d120140991035a04a000d201d95074003550340002c00c2202c00e48200d4030040c4ca0f0340c0718101c0d180c59204541022403045a40b000b400c076030400c071350484101e0420401c0d0003046100008281c42e00e5180c030060010b040411650f0502c0320400303061001c011942d028030b0545842e458415204d101612501030002c0c03100d0310802515200209008000705001c030b20080d040309085581c0740003000201404860300c074401d059401604003002045042c5424401400c03a141e000030ba1100321601c0e501c1d07103821039010b6403181010311b2000072100002d07200d080b80c007100038426401a60078807000b03032690151840000c0042540090005140c0181c400c2c1c0e034030101c003441000d4020020411000c2c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286973003 1250 286971753 286971761
    0x5071b02091e0a09030e03071a0315060c07060315060206180a020604090c0906050f03181f05010f0603020c03040b0307050d020c0a061109010e06071104090c0603051e0103031b15 78
    0x130640020b035484413140003a08001640004840401c844030040201d01560100141c1012300182c502c0103c02c001c104c900d94400026000c141d00c46e0014000c2c01e490860301030200d48881c0050310f8840e40780901003200380d4000c18129484034020042c10411765001070120309240b0360303c80096002001080120341d0b038106a101001d91807450300e0b125081a1600c2c1e01340d40c0e0380113044016503025002c0000620040013182000010314160088038100c030309480c100b442030b80f034494420901e542d44100410501940015420080c82d0504003140703403000c81507020740c407407141d4000d940c410200040414446031182084410004154108540758882d82080c40d4850b0f05103003050b00c0441c10310003606023640c82c0c441190305410050b155100e4024405003406078a0304024800c1d1032010040c1d0b401c00150315507005a0000d28403070043e04491600744100070701202c40280c0210440403800c160300c90440700d80c419080c15283c05080001000501c05c40002046101450050283c242810310000540042d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286974253 1250 286973003 286973021
    0x70c0308041e0911041437050402070218040309031211010c0212090d1403030709150f020a02060304050102070c0e1503030304050703020114250605071b02091e0a 71
    0x1d9181c0c0c0310b0761000c1c2d10040e00c0031104000d441c0e40007004200140710030503034802c031b0506000c3d140f03500c010000240b29005101101e018490000303950b0300120ba02100a03400400b82004607401c5007449100d0300800d504101c50400d10f4040c00a01d400300302414010070780c50700115402582030084c0704050310014038004200400302055801c241410704d4507800441c0d5410041c2d150446e25003800700040c20000e080d2050103007901c1480c2d451040c8107041e203052006611480c115106c00300c5035482c0c07401e01d82c40d0504140412040007071603441810941c1e0b0224100c8a00740c0c04071041b94032510343d41000740c02403041c3c0400600560300104001490300390451260b21440352505108030903641d181c18152a444211802801034000780010310044d80600c6030400302041c43d804c0d036410480c2c040251801850204c001900708500c2c2c0c900c13a010014213014166100441d481c2100c52a12908645440741c05801002803041e100303030300000c5645d44a8216100c0d8a0a078241046082c1407402904000f4141c0c62 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286975503 1250 286974253 286974299
    0x220507021f0f0501050f0114130b0c030a02070b0f070f150e01050103050f01020c030d0e12030f0a1503030e010f021c270501140a03021303030806190b0f070c030804 72
    0x140000856180c9503a81b400c1910060f1902110341c2c129a10416503035120500c14002801c1204000c980301044201406a06003c640215034070702c1c004034080c0c030301714980c1d00c440082901084181040000c80c070540320503c3e4000620004558540b410041b15940c000030140802c5c81c10f41c0b210850201504000c0c1202e0252040e65105100c40c18a01c1c00d0344107608800a00e944200003242e2645c40b01e40c85001c48120307003415a441d041d03180c0e41e01c002c0ca501c00d80310007003d00190014000810310030300c60000032400c54010800798601d0340c0d802070100a00c402c4000d0611443d5241011128002d1210801d1054500072440c05803003440409042600e2440c19a10a01144034054170b050409a80070026190141c440300c420a29441500d1030680c0040c21117420183c003805824400e51035255960302651007500c80f648076140680900003c5007410080e00080b000c010001c005441020b01202d80c5440c0f402a0181d442005080c01445600c0503840100070600000300026501c40784040404007400710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286976753 1250 286975503 286975511
    0xa0303050c1e01050a0b0f032107050a15060f0e0406020d0902040c030608100501050a150203120f15030a2a05060f190305010807050603150d110f220507021f0f 70
    0x44c4144a10382c101d41c8096234250380b110900401008508840904a1507007400c0140343c030340244c0c2c5950412070241e00886030b0702100d0208143c100520701900c80038001616820801c68980a4002158100900003410726540010a90343c0c00445801030311350560003910501c851452642e004006282e244034411141c040d440210003c0782d20390150720b04941c801001020320500b03000b4048000300074020110300b584000c029080e4090500e1404130310550110b40401481c1c9410403450808441489a19109410940e001700000b10300f640c0240c0d00c1094141d048083d0a025054030803912810f40107198000c8001c01c41a000c00c80650007041242c41ca81b006800c2034101031010b4081e00c0081c0607074500350f04012014841c07801c02c0409158046003131039030301030340e01c4030b4502140044006080a8840e18028090401d50307040c81c85500760b6481003540d50302e072240443c00341040140040c1040034455525072000c80c2225108000031412035403280d003030f21f00d020703440144030000701481550f102402c0d0034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286978003 1250 286976753 286976771
    0x6060f0a0b030c03070513060801060f020303041a100f090b0f0a0803090603040f0209040b01030c1a0f070503120f010305060105011b144204020a0303050c1e01050a 72
    0xe00500e000ca40c4405a10350450301c40c9840488079810041031241003140902ca0325100c805000d0501000706103e403a40d030080c0d414104000e140c08085c0da90141035500402c10700c00001e001e90300c180d0390549140c02d20034440d00e61080350750306811154030041c00d80161980118401c00d055104401d8103908854014140ca80c0005210030070100c4e2003045450b81050150f00040d050a000559219200f40c41c008c00c540b040d54001103c01c80e0540b001d483c2e8842e060010b208200c49640650301408c102c3c01341d41880c0b03240349561451440351000a510003240801da4004001341001502c01140000001c1c01640c40c016050003c041c0092005075900d2003001d000203041c0d4084c4601c00d518980c0c40f62164060f042e40d440b0040c44000200c4006d144d440341a200482102c164801e050b03044180e14550b8031441c410413004402201131170610113003d100481400010381d0748a0710700c7d0449170706003003480c1c40e0811b0449050a2101c980650780100790304840440d40c20740c040d4441d074481c070342100c0d0401090b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286979253 1250 286978003 286978009
    0x603030801051f1e03110703050307032714010f0e100605010906050906160b0a0c0305090c060417010f021303020915011d210102090102061510030c0507060e06060f 72
    0x70380c010300c1d031010501c2d80c00381d240c090300c4d02d4001c01c0004082d41404076151005a90242075941b240c0343c20ba0000f5400b1040c441c14030390500400c180d040924056034424010302580490000c0044c5004002500031040984031000a410140368002118000c012100b0401170b416111800d565440b000e1602e0803001040c1503010741000340581c0d01990381c3e5400c001850091000c194480540a500f045170702d012200000c4150140c0f0f1700c00d1404000120f242c800d403200c01f8007980c1c0050a0a01207400c040003041040c1c882c03034103540031213040b19010108001201205d0340105000c0030350000903400018840c0055402d00c0000044a2003680c05201d55525018134100c03041041100a00041702208408000f6030f60640070b0380d001400802003c030781d000139202002848111800003510740d4010500c8401980c050254a0b07003c11032208003da03080c00c04002404582c40f00300100309140e59116141000d61254040c0c888959003ca03003000f00c45041040300d9624032045418a00c07459080b445401541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286980503 1250 286979253 286979299
    0x70f021e07051503090705040f0e0105100f171c0504170d090e060a05040b010201111b010b011e0c06110304030c0501050c0c0a0b070c080d06230319050c0301060303080105 75
    0x4030344070015006c43c81c1000c04002c00303010016403e01c162500c95840c1011124203200f12030007200d103102440742662030612095011200c4d680b0441403030107a00200109494080b4503948180450520440955500b00b42995a80596004203100c282e12101c0c0d007000c800001203c0da9070041d1030b12084042540d441e403240d16482c04072419500071880610130840c50901c4d8008040310401400003141202040000e54519046078007102c18076000c1d043e8107181c0c50000e00c50b40c442200d080c0b03405900c0900782882c40c802050043d0442c82000351140000043c000954441d031403a4055503030590362810035080050035080b14030001c2d1a103510b0000419084d01c0c02404840b605c00c81140074118181c2caa403240270215500800b08014421108564000140440c0007000c1001c0103001c00141c0034200242d802c141c000101020049102c80c0702c10f4a00307a034000440710490314100e0b02c5400e809080b442c0030382c10036509110701d941660804801004050f044041d01d07040c0e4500703440f5903920491005c0c00e0f100c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286981753 1250 286980503 286980511
    0x20606090115080c04170601050a050a0308030c090d0807050303070315060e061e03340903060548030c1e0c0706050712090806070f021e07051503 64
    0x407401c440000b0040301d008150f0903911095500e85541850742d43c0c6208180303040e00e00044810307a00300c0b2005021915100448501501d0180e4445000a0442d0394800d4030b480050030354403010300040b030801c4a681e5080240000d00307500c40c2038103859050ba46400340d41ea0b0402c1d68020046030810118013500c01e24031800d401224104d5541d882c1c490440401d001141e40314090034407017048000006240801900011402804280105103c00e04d01c0c0c8000d201c18010034058003404001c17a44036010042c2e11482000a030b0f504110002403903107402480c40c00329203801d00d11500c0c403100c90fa48854019182078800d40100e0114034101e002039090394400840e03100c200d03040c0c0003060301448041014400f000582c0782d41c00081308560b2608000e17034075151400246910020014000140400411083c00c101c0e461003a494104840098141308603144c981e00024401c0b420001002c80d103943d524820014010110446000c036800702101c1c820b2107855210600500d40600040f07010660380310500d004403072007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286983003 1250 286981753 286981769
    0x82106011202090117161404152d052502090403050a180e07090501020604111c02120a031b0809010e0f041505040f150506030a0e0a030c030206060901 66
    0x82410780d1001030000d401c4003040343e0401039a14614a481485100410b000c0c3c5808248500840d030b020300d0060041d812005000c3d8440350500c070410403c3e00d00841c82c8103150043c18003103d41402d500341c0541c007071b44203078003003414000310064440055001001040c1604000050900700d4103040d5050354a42d11550000303402c1408d40000402203403041c40684004003580ca41030080080d0f003048000352031900c3d00107068203941c00c0c00740002c45400500320b000034072081c0090f1405203080e40320140302c10303002c807405405100d00030411702600c001c101070852950742c001d0809480001e030f080c41d075984040c006011401305100844c010b40c0e800c0143c10304813010303178010780e106d00e40940c032001100d00078600c100658104814201e5041c0700d0b6203074010b29030440b90103050300c564141780030100030694150902440d01e1a00e000c2c0c80d003141003085507404065070416145565261038684c0200c00030704400301d03040074601804003c2420541d101c0c4070340903d107019074201e4041d51120782c10088521420710030054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286984253 1250 286983003 286983017
    0x10309050a080d020f030405030d1b0c06091b080102040f05030106030c090b0604050916080615040605030c0705030703050a092103030f1401061709011505011b06060308210601 77
    0x20002d90100010696944030b10405824183d001c0041c0d8082e40086e1000c4aa85c8c00104040c1d915641d5481203031a81440e01e4000c0e5424448914003034484030040320068200c1d0740f20640e6406005a407208503605c021041c901d18426503a40503007500139002030107940c4100320206030002d40751905010301000d03079400100c1c0d001c5151504115078000e0007100110340e0400713001c0c0000100c95072003c4503188102d01e080044a90aa203021001b1b04018001381668421450651020006003406081d901660058184a6038a0f00c030020301414501404c1070081c003510000514a0030107030b00034054032400c0610b03190080000c0d26800d809039201c84032004401600c9080c6903400c003092194011000d408459070b000115290055003c681600090b0020404943c5080c1e020170984012840700c2d612202d20f40007080168821a221400040c05201d441e041103116070f1034043d030396103220700d4034845a803000c2c00308070503984c1345041d1758075410010b5554032001805164400141c0c1443c480b43c410401659038903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286985503 1250 286984253 286984273
    0xf01060503120d06120c140904030e190806010303031b0c080a050a052208120f19020f0d0f0801060f020c04150902030103060504110303180904032601050f01030905 72
    0x2e00a802456104a6590702c4060014900d1032001101d250f040c040c0c1c07400e01000342003911411015242c2c2c540309005032002820000801d6120380c0d20000700600b2900814900020b000550503403070540c0100100e40100d10001041680641c0034802c2580070401d91100010b04020035200c51503948406818007800b009070a070428070400c010882200542080d604101c0f103a040f88481036613034612648283c150102c14000728108100200c1c0142540440d24030b03110204417000d0560040803034405401441c003501e4500c26000380007446501001400700c43e041e24289800030803130402c10b00450701140d441c1001050f400d1141c2aa030701003448070b40092101c24104000e010042c01c0c0f51104540c110410100815054068002140218002c0f0404112400d00c3d0521a0700000e851920f507200354000c0002100720070b0f0210798082e80300021112554581d54a00b03040da611031468481604048107240700080f4458081403041c1a1001903c02410400c0f01c10015421a8100ac00180144c1d00c104900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286986753 1250 286985503 286985533
    0x80301051302040e04030e0a05040c05072303030a05010e010b0306030a15020c010603110f040b210a020409060525120929040b060607080a080901060e090a02030f01060503 75
    0x525a892240e0740189010b6444107604080030042d0340071000035514210000b22440e0455402d00509000c0358100100341100001500a1240c45002040c101c40006195501c407852080010090b140105680c1c2e2881d003405500d000300400d00814018120060022501280100c207503031141d4006001426810000d88a40344108510344520a2140d000c114248001400703004000044d4440c50601420304a0a01004410b500c0d50030340078000e40c42c0020103c0140d94a10002c5442000c0d4042e80b0302158003e8001810800b0701c007001b940007818140c90740e042041c5540082d01c502440084110b403071200c3c0380c044840c0d00c000145803000403503265050f200b4450903441400c6143c440c1c07040c110100e00c40d004d00c00b50201d404404192484400c0104400e0141107491603900c544110fa0740c5151400750317501c0450300e0092a002e40304101c0c0c14800102040d030300350f0100010b00a00b000d0185c4a10b08030140f1551901c00c05800ca010380111003c614400c00140111010713504024040c1c2001704c0080c5203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286988003 1250 286986753 286986769
    0x60e091306060f06050a030609091101050a020304210204050a140106110f1e06011706012c090f01140906041106280906081306050c07081c0b030a08030105 68
    0x9441d115940ca900007450809074510760010403194840039280ea105c110302404030b0300e95a00480c040c2d828020703910001560003840c0c641228003400c12503104e0180690881c618090b50300000034038500e86404054410620303c241101c103108903403d000517600c2140d0b00d0169403001c180700081d100124010301c0030a010f0306a84401d180800b080713031300c03c60141c0704603490145400720030b03000300d50400c103030341c104440500442d4050061141001499000404003541e00d0a0500c2100b0050403a2100c4071f01012900d01484817103c4800c110440a041104030319031a104101a4107046618100b4041d040460034002d02e07100d980c400b03010f0a410390700da40300e0484402c02c0401082d0301c100d0404c04004505451400d44c0b45103111180c03018000c0c00000c0e8003500e45080b42e0008030038495600c00300407140008441c0b01d03850070b502c00310100e0680c0316001d00740a00d000701d04000708482400303c1d00780300182510b007641852004000062280061180906407910300601f8090480082000148603d007000c0e42c6c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286989253 1250 286988003 286988041
    0x30a140903010906050c0702030d0504030f230d090e07110c0609040b0901030f050c09090d1416080d111312020a12030c030207090203010b040513090f0813060e09 71
    0x100108181d030091307075480221402201d0002ca464801f0410b401542000c00a2900380b61850501c946418159210120902494400102084003119040d2811450700b12042160802da4044586070424800080c0c0910740300e0040756610380b2240c0000e0f02ca2413080c0800f580048042d409402c1203020390703003405900d60000d109581c000392111160070f0940c81e961100e0340214080c0003030700b4580c1a94a00310b81010310720317501c55209000081c14014818408101c1c603d200050782000c007425120225009a14010001e4800e085480089800107104603080146210702415004010b03405075265601c003a4011242c507480d00510099043c070000c001000c56507000c600081111a59130340e074540b240c0d85032001c1c0408500081030216040304145e0108543c1001d0205a9810b50556040172551000c41c026032290301c0c814510b2207032004031070010307074402855150070501045412904d42071814659000314102c1403d07010b44070001402c240b180d151039440c070000601e0500d203074803042e0301d5410011141c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286990503 1250 286989253 286989259
    0x1506070b10030c0f080c010f090509040c08030301060f090f080705090a0b030307081908010e06010c0f05060109060f0803040b0301090905010e0d021b12120f1903021b030a1409 77
    0x154040049103405003280c00a0440b2811351107200d04040300340b82800301d2080307002d0504c001301d500307900c0c89a00550302005550080c1e400f40d0503561913041008003800698400107150100000120b012544110140e45c20101c07a02c9803030b09190b4a9610709402c100034442c0c48201d410100e41840a45070183d40750342c01c540354003c003096031741c01200040d085a00405088419440000320710030f03032240c0348218008110703080c107042c0b03030341c1d1b2400d000507080c29001040035040094421868080180308d50680003025049011580300f9a11080e058005103514040c2c01c01d0384104d00400129241c0c00011a019502c21801060841e46042084000740a407510308480c0341d52659603c14803224104480102d48059500a000e040c0754161400706002140340e18602904008a0080030020300151140e98032651140d440d954107020700300030810b0702412004400302c04500094481d000e9058014121210401c0c14641082c0c401544a07030b030300c1c46040310140c0071070456160107051310500006082903000103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286991753 1250 286990503 286990531
    0x10110a081c020d050103031d030607030c050c01180b1b0f0901050d050a1a040c090302060f090a18060608060f01300603060c11120309012a02061506070b 67
    0x22075a007400e07a0821503920809aaa542c01042070542c0a80140b101d41d140c1c8c05582030148420003c179403194401020b036014140c9a42185003802e214600710303600304280320020071454045640300311b0b00c80600d21040d01d01c50000000b19502040a05850070002051462103140c2000d071200d03550b1a40011030200d042c08018020342a171001e480c0141840740d502d1000016035504411700203144055a48120f5009524110390040c01d82e03084480f2000f96901158480d49800c1d050385c401c1c0d04d910410201c140c005010400002c2c82070765070303c402020202c0780241440b529440740011906004111032160b48114080c02c00d0030303254001c0c414101c000b016000c8001c0303040741d055007003480303905011031255180b5038460307081003400700e03520030900103080e01e01d0140d20f041c00b0b400b0120b64404910001101c905000008603040d90425071004000003c064001003c035091003044143c00d146155601e0091f010300c400260b9181404c0207400088038000f860541400c000b615002d49540713004260301004055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286993003 1250 286991753 286991797
    0x6130510150c0b091e01150e060604050a0e09011a0d0209060a03050303010b040311030c0105071e02090a05160807140a1704050f0f010203010303080f070c060f0b10110a08 75
    0x18110201d00c124080e000500e00c5100c50b18450300c1070465003001c17102c581d140c80c1c803020804100c1c410040488a00304040181501c910001031072038030070761f48100d6000c264a000022901d21302903030a0f201d803911310002c201071402c040784c440d56220f0000c9070560141c6510015801441c1021580d5000b040103000b04800e60703140d648035841c6910a030428004210042000c1042101c640320701c941c00c550a401070115012021f0002e0081c0c000d8034401094a140c4489030840300c8003004031001c940c6e8008000380d84900f0564003035002010152044150b00c4040c07892224914003403d00a070289115a03284180648070403101c0c00b99400807041c0c581007048245174103022030a101c903540d0142e4010390103480000f2050700181c2c42e101002c446402c01d64018001000480d4100c1c551940c080c16001005c900e80d9222401260a11400c150042000d07142460900a0036129880070000040c103039640002080d00c08010349981040e141c109005070f01802c59a0001254cc00203420361b9480c04401c04001c0328 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286994253 1250 286993003 286993013
    0x109090807150f0e0c0a06090f09110c1f0b0301050f040201030e010905160620120702150d0b09070908060402060918070323070507030e03070f0e06130510150c 70
    0x3e840c0d1200d1011740d011242000551030300a6140004004038100905105d180c1110342003040100e200305061240d40e00e030b907020903012071402ca80351101017005644900d142465852003000c082c1e02c0641c850703031402d00146080d0070148a0107018201c1e0019150090380c1310360046000d41400c40c1101003554988000c900055000c0105504085490364000d000609020004241008003e234500040c10101c001d031f00144808100c401035015844280356032000980041040209000d4012040030400215080ea41d501607104210600040f101602c4503140c014003100c00510500032006075400c800d000c02e00600c2c1c450000c0c40070450180189188401c0c1c6504044012421502d202c0840e03205c406604c4a005035421101e41083c44030910000d504254600410328050010000c0a001c900c0f14044140d50302001002c0c0103100101c85491843d0f228544d0310f54800e030a40742e4a015520411540b1420392440c0036051080240e9402d0084142c030300030108283c1d01035040503005001c1d140c0ca523180860 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286995503 1250 286994253 286994261
    0x9060303050304020306090d0c0f0606170606010906030516081012030203030906090d080a0e0f030c0c01090506040b090d08040e0711060f0c0a030f060909060b090109090807150f 78
    0x14066207540b5207034030707090051504040000701500840d4000f400380d038102c01d40054580402c141c100c0e0b14a00c0311a850310700b80300241029040341610303501c0c031040000907050000c2d07018403482c0c0a03a5284071840e92014103905480c41502c0040040410300311071131145101c0c003045130f401080e010f65440f8040d92161160301002c0e0700e0350140d006030800402c02040b00000c200c4142c1100e0002c008020420b0340a50007086003e019140a1625468245031400e2800800c6450180c02c0d64800b5641c0e02c00a01e4465a1350726002d004283c00b191000c480000c803890184203071001c81c3c2050814a1800540c1020132062419490f0202d03601d610038407012911034080c1091911540d0141c54403000340d040c034100c0920b803602c020104d9124082400030001244030080654035000300760305000c120030f950080c104c1c0240c1200e40100714441c1c0340034088428410180c04c425211013096524800a03603c2e580302c1000da60700f020003e17019120400c1201c0c00103506192000100c442010005803034a200701d120001d503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286996753 1250 286995503 286995509
    0x1b080d110f0d05010623040501031a0916031a0312070c0312030906271e050604050a12020601210602221a130e06010207080a06050912270a0906 63
    0x342da55500140300c001d0300480b400140546000c1c030210f0384020303101c0460040c4200d001d03036810903031903018001c00c00d01468014099014020b1810405280c4030b0400300522a408042c20300290070b05200d2040c0d061022203104a80c00c010f405050050a90001c011196024903021503402c0412540000801e403407110031f60300d100c07540d40c1c08580030070142009029030b121451040e2910307100d89451943d548512025070b2425070320002d00840700c1e203048540e040c0c0c08400e034000307040c03401484100010014049400c010b414494124840403d200301c82c2203948060902400148101118030000d48420030048000c186100da00003502c1e1840708042070b071540c0c0304200238030281031000070140041151110084a41810300d9442030a0002c0301c1d030407a291003094403940928400d120003048042c0d00c24011040944412230072180d080d411407426400401301218002c2c01409094250000351101108a8269160300b1428583e81c070381e115043d500d031104e015400da500ca00c510200140c031540780d028034001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286998003 1250 286996753 286996777
    0x901020c09040f1a0714090306040209040819110d0806030a0308151201091202010b0f0402070507031205070507051c0b0603160b07230d050c0a06090c03031b080d110f 73
    0x4281011400901b841d0509800030080700300c18000381880351400102d4279405a011601d83c03059803a6824280b0717191044034281c00d520305022280ca11405e4001c4c6c00e010015102000301c13680c0103d104012148980107840c081c0c0c0c10741010919202180c40341c080150418020005480d904843e030700091540c1c1d8401c0c641c1d00269440764400c1f4284a0080c0c626003440303d0301d000a10500e03a035a400607072030340320740b0b65101c0c8140c4c2d021448405100040000402440d407200001200b140440c202414036000f43c00125520700c070b418400b041c80c0c202039150403210259014171114504d416a140000e02100a01158042c403071801601a511551201c040080000b181c9980e5200040e085c13082b201000c06540320aa00083c2c007801b03011802c0013421854448283c0b07040f139158143c145080741000401c40b0080d041c141000c121070140042c5020f0725080724401d460f4011201c20260b0601039040c40b030400542400d03414803540039103012903008001c9603902100072a150258520b2240c0b0356801007692191 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286999253 1250 286998003 286998053
    0x302060d0f05190c020610050d14010612021003021606020901170a0e0c010203070c051c171b06040201082701020c03040608070203040807030303110705010e0f120901020c09040f 78
    0x1072800090702c501300000300d151019141c50324040d0380c040c3c900c103000d00c40d5034000c0749282504410702214070080c10704050114000d01417250385454080c2c480c03005076401d034803518080d0200701c10b450103442226052030050b25507100c811003d807114070081d000840028140000034a90b0b01d408a000703809203100d03030700e0000f00280ea661291403091811089440c000e0655004105100c041003c0715071140c1101c00c1103840849250f007034004c08080036000000282103510003500b071a0300d00b200c4000390010610288289800d54040c94505940300c205880180c04120704a000c00c55208032a0741150030913038010300801d0703011907580b00b10b0300b240d000122401ba6900041030a014165114900c0380d0072041500c01581010300300890151101403e100040c14143d503508030305035150404c000c3d00d000580050080268911549845807030701120056920b0a0180083c2c2d010008060300655180c4141a8010304a0049190a00c601c49a02400540e060358403030040c1c000103041600c0d40d141b8500d014038014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287000503 1250 286999253 286999291
    0x10203040f050c1c02040203092104050405070c08031302061e0301030210020d021f06050d050313052205090109060501061106010f03032708010f09021306060203040302060d0f05 78
    0xd4142440035401a106101e10708038130604090441c130070355829804031001aa02c1d100d08103030605c0d181c40904140d060069418000340c20007516400762044503030903142449165606001212284000c60780204081018400318281410140c45034034140e201510721032408802e400040c5c011404108142d40c0c80d24008014011030034045a0030381c10351400e00041170140c0d80464040e448009102c4000791b9841c0d0004500340c1d20100c3d410410081002500303031600350310300e41440c0f500c941c41718140703a0721f000040400007403906010002c070f03c411010300d00809841c0c20300507294010300b1000c0e00c1094299200d0b481800402d03810300c0bd0f940280720907111106038200701982d0509000c0c05034480194410039440c104007003600400c118411821120841c0608201400f1004e001e0225420003e219880c0c810244440c85031a40705895860080322800305140da2010b5001c2903d00c503000f8400140c10900041005003031880c0a010a01c1074103074081640010749943c06c00307c540c1120301320b0001d0902813100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287001753 1250 287000503 287000513
    0x1502011103240f1f092402010b09190b06040f0b131e031205210118020f0a050a14160209060f10050a14030c04090c0c03080103170c010203040f 63
    0xd400d8030b207415200250060440c8000072160312a1040c02c600000c0350350600070310107109581c003101410040d102c140d2a01c81c0011040d1010201946c40e602540c6440d14030071480c074003103d6940c0700e917a02071140900c940011203070101030a82002c081d80c0140c81480046801d00f01c0fa445400500a0210307026107408007917141d1945044141c9c8441070001005407031030700c100103030005402540d40200d00001c41a1211000311a64070910b4050b900310b08420000c5000b510401e540302c0e0486528018005400c42020900012031044110101c00307a141000b0548900d8000d9020f8140c0c21158284a0920395080d441c582c040e81c401c075010703940c0c0b0000d005483c0840c90420300c140c0d003000c810754480742c120a1900220300840161241d42052102c086603940b0403d114000c20301d620081e95003416203908016030840c031150880d004d40c102050500803e6058144a02007a160607505580d4884003a440d40e100c800d5803440d160721020700c41404000b00b1a20640c240000c50140344540d41c0320454010034141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287003003 1250 287001753 287001811
    0x903071715010b040308130305060405010b010305070e031c030b030d03141b1c0e03130314011518110304030203090906041a01110a06050f0a0c0906091502011103 71
    0x210040241c6003001401044214400d503425242d128800b035070380c0c1e1800c1643c0700401406a1000303040f4400c80042004210040d0002d0819a0080c2c9060029271649481600c84070210000c0c25019070101d85803400000b81c4400c181c180203a17901300010319401c4200400e003040c69181c43d031008203403200051001048a140040c1d030201300659400000404134110381620310650390342c00c1003c09e031440b152280081d241e01441481d0082011655103180c6c4c0c2035109004a2103110a8803016020703455403042500c180109602e81d0841a01000c00794140320710f120258954032941d002d00340da913005030001000364000541c043c5009800558980b2825000c00c0121100100300c41d0085050100308480340034041c0d12045608000d0800b86003403000e00d014140b81161004001c0c185034284414003202c2600910414003a8184203010f21984456800559504036a4031412000543c4203c040108203c04184c40312965114800400c2842030f03071130010300c5a001a82c00141052070070041000745006011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287004253 1250 287003003 287003023
    0x12040f060806180910060f0306050f04020108040b131a011707080c041e05100608090106050306011406120109020306040605120d0302091801030807030e03010902090403031109030717 80
    0x81d050203240b8040000c034020380002404100070304443d40115200c1c0ca001d120311208404d04c41400c001956641982940c00f0b4190f1100351842c2c0d00d004040b4010000c0b403e81c061189030103843d103004c0d5071038a9a907000c2d00e810050101403424a5900c01d003001440a9480c15050006910302e103800d94184104509000e800b0340e0b009017140c2c82582c041000b00c001144030000740e03a08440005148210307610040000e1342c0c1702a0420114605030400201d5009680f945040d00e83c1951030944a99510080c00c4c01c0b03480a0151a51590166004200708050000c1075030f410000501030038100b0007600d40e02081c8179002c0e04018500b0b43c000c01000301e00d080070301c505030042100300c44142190610502c1191111a20b24404e000c01d0380000e5400e0807903c40d011030f00e00d042c0080703134540003560352814503070a6500014421030005484410f07039191450140103881d0700b01e0f0001c1951846443c0d42e03170150010b0400d800b880c101c0010510000c200b07503906000f0b420042c40d04040705808102040810380c14400d01e21 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287005503 1250 287004253 287004257
    0x604170307060b0d030c08090f040f15050904200d12030605091308040b0904021306030606140306030d08100807030309032a03060c0504030c03080d0f020a2f12040f06 73
    0xb2007000013107544030413031110450700030000d1688d4800e564089040100e00354039098001c3c5c03c291407081e40d00e42d00c0e07001c092292184040c1c032000a07100c40401804071004e540203004030000c8000d41115803034807200500c10007402409000e000300c0d40d54a100100f1440101c0c1804269070303200410441c140758054582c0450382032580c16200c90b584c0d49400990044d401084103c041c04100d41c0966226681250307400e0140b80324130b148a96540000602900d81c3d80a181c00044001c003850b4281c40c10030050320300440004000d016849041082100c00310340c01449e03c585500c021000050b4094203004841c09036000e1f6a44404550647c200274a20218607662407207004002480381c606400280d00c2081500e41c042e034003086000004400321458065500701808500c0750b5a030000400c411400141740a15000b80184910382810a02000301e0142580071000f0610454003a07180005c24070103061002c000210a5821a80701103c580c6064407070700248901c4040000d05002c2e14440c0310035400188002c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287006753 1250 287005503 287005519
    0xa050601020706030c051614120c0c04020a0e0f040902040614031b0901271d010f0b03100902040e07090519060506040501030f0b09101406030f0609060604170307060b 73
    0x79200041861050350341c500907e603003240a10080001861090507501d526034202c40c403091502c11318404551003446920564841d071413112540382040c0c003c0d21220f24a40d140c100c01c405940c1c0900c4800b000200c0d559900a542e211003d0060384e80b0300c12079002d0304011202038420002d800600d8035180c42424840030109a940359103540355218101c16040d0341c241c1d034524402100d8152070107100c500c0d1000c4105603d04100403002d039171403c0904503040c090b94400a02a001d400c4541000726100c00c0c04c015015004400203116481050f0000c911b858030180000036084800003525080a0b66034200c034502c0d075100c030305004490003451300d0354000d00204c0000f040702c2803500c1e00140c107900c650320945060541710050300c003407a03401d42d1244281070300107041f1310b40e54502512180b41860190240816001c1140c015000314202344c42607902c25008920000b100d5240c280800070300303100007030950750702403010800400d01d40e100e00d070100e19450a0340011078940d82580b8000c0d05413003c01000b5405440ca03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287008003 1250 287006753 287006771
    0x306011808100903050d140609010e070206070f0c0c0f031103070e150a170c0112060602030d090816060f0b0108060108040219170312010603060b0a1103040e0a05060102070603 77
    0x80400c907030b11400034036540015200502d150550b0fa601134602014503080c40c00105030f07403404591034454413411084410b076405a88a8a20000c501001c0d0340080050740481c000034079450050f03240c242090458185802d100c9615034420000e07045541050141c42203020041003003040b4901da2640c5d00c20110060b010792418604072004d080401000c4039480f20307016451140d00e840b04455007004c1c008030f0404181c0341281070016951044c4aa01e11400601c452039202e1104100344519425100c2580c0034500d0261001001405050801c800ba5080c2e0b07810449000340a000f0340910000c58800c1c1c1c8046208a05110304008482c14194640d050020072020010b80740e9000305150780c0a41d04a403101c0007107014088440f0014a5900096041c0c1071140500b901800300002a0101a50f00c03000359a1680c2c891200310301b03650940c07185050703110701440b0349248540240070b0760310401c0c2007004a0b82407650b03d2003130900741d080507120401003d13601d01c1404000d59040c072030100500b109003418411070075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287009253 1250 287008003 287008019
    0x50a060906020a031d04060905040b06060306150f0f120403030e06010e011806030203030c0f0105130c0302090403050f0703030603020f090601080c070525060906080702060406050903190503060118 86
    0x14070f81e80014100302c40d00d01040070f40c42c4a0030f1070502866016101300026600c6100c44801000240c905854500c07408000440d6403074040100e9100e8000540045803002004100e1181c94000306105c0090803000d00c1707401d400c18800030160940005a2140c0034203820107003005001c840d9000100708154000748014007140c1e12124207a4119850032a61ba42c05001d80d2800d500244040d41000394180000901425a003500041c85c82c031210407a03000300807540303a080d150612109083c42c01011681035420420151400c241e0740c0c3c0d4814081d0038614a05281403038111004e034080d40c0c0803408655101c400f0700943c00e100c004850b140c002910311200a04000c0c00281020304000c003400440c100000d60b000812106100e00701d513240303500ca144802c2030480907000c00c070304109018040000380c0310000007404510034017456000d026030750040d00240c2c40b103461710700c007902e0000c040b190244000c00040340d0400c0041302c030b00d402822696820f510b9041039000100304003807118900b11118150501031040c85 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287010503 1250 287009253 287009263
    0x2040f0c0f1e0806030316200f030606060702120a03092309042019090c140910030e0604050f0105131a0703110d0209040b01140307080405070f0609050a06090602 71
    0x158440c00e14030300c0303a940c48001901d1441000c4a0030124a6585504001c20004103012483d11016100c6010307122043d00a00c003449c1d80150426a05901c0b15000c030703119003445c00003098403a00140035080444110303880e25261035040041100003d41c060004c00c00c003401260300000c0820f5040c0401c0500d8903000c0018030741702c0090406882e480742616000031004c60302c8031900c44990b0161020050700301601e50365031661014810174402e6400c00b204450110712583c04294020102d03080c641c04d0410460038403109140c182c410105240d80c40d602034140d0402001040d1003548280001c18070184400c13a05401e50b80c020302098058040101e0304400680300c41d0300c125082994406401043d500d82d1b00c2100909411503440c24000000542166030f6170182d002400c003060300359001c1c0620001e08004640354a582c030140b60100304240041852907120b402d000782c1290141d02241c28458503501d0030110356640e80e0024000c211030303034410401350411755000801040c0c14200354006500d8041c02942b50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287011753 1250 287010503 287010557
    0x1101051320040204081e010f0e190503090603191401060f0c051615020601050906060d0207061d0a0303050912030c0f07170405010e040905030f1602040f0c0f 69
    0x72540c0440c014494076203905071001080604111415181c0207005c012110309440440859542031402c0381003016a140100030b209500c2600410200145003c00c00044c45440310031605400100001d07080d950b91040518000c03241d001c12100d10001011135401106e40041d400401d4009440040102603000000e86104148600f85110341590f14501a0308121034031200071006550030304081144190848110595850703034007120141c4c0d807107204204004404803074007907001c40d0400c0b02001006c625006000b00b41d01c20000031035076090316003911540a5401000c9811036008516030028503600d409003a81122980700544400d40030340d1301039440c61000074011070700300d9800180e02c500c00180342e044640345034100e001d200080d010b000d1001c1046d8041e2285c240001c0d10103110401034134061048501159124000b50300d0070407650f00054140c2c0107000c003800d042d140040034002688035401a00800c41040f040000e8005805601911074811081c17980100590005c40c1001e045002c0424090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287013003 1250 287011753 287011793
    0x80904020c010e0105040f03261302010c0204050103060221040b181f290a030308070306051e01020105010b070b06210a050f010506010219081b030a11010513 69
    0x244048941c0500c0c003414200b44200c030558170708002c10041c44800c46211720554860b985102e900c1c54510105985908035800940c0d54910180c0490101503600301748010123481030400480004a41d000281110f000b42c0c0281c4220350000f80f02d0a0300c950040d0b40300164902c1804903012030030301e03484141d550b0318010301c80400074001510b10011744000300081e00203852040701e445541d441000c0410040d204c03001d45030720b40b0350b02288405020764401108035240603014000202091443e10201c0d1045800b43c201014190b030386030b0105854848228030104034102c0c41c46840d00750144000242103a105a1001c100030109014840c0041c0504001c50f030000c80407102c04c0300c10400798101d0802c035500f09604828511400989008102d000316260751200b6884001b048113035940c100581e11900140d03001c1c929512001c1070070001511941c003502c440e480103010600c2c1342130251030a0b032565004410503000320302c1c0070090048441d0b09000e1294071100141c507034482c00225941c0c81d075100c0307a10628491 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287014253 1250 287013003 287013007
    0xf0a170708160f020d0303021201050a05010f030507120609060e0f07050301230603150a061107090e030f130e0a111204021504150206010b070c0e0703090804030b2208090402 76
    0x109100c04110aa9602d94009180c0b0500303d410341ba006d0020341c0290301019911034040c00005a900c0c140d0303c0341040710010b85484005900c3c0c06000c41c002c04000702841c00340315850000000740040d61090b40050001c40a0005070b0703500b0300c90701800e110300041c903000507030301903404104055500505490440d80c030b106960501c0d07800281d01d04407035290342c841103070840740c04420000410a01240d0407251541030b18154102500d45100310b500000400c81d40e0f000d0b500440040200900c194040503c528442e400d03203050a03084e505038a613982c019941c400c0c004660381400d00581502c1101203070803601001c0300300040440d000245542e806035940c00901c0c050b204001a055481d140d8501140081402080daa00c0f612100c084000d04104108440140700d00800030541d0244407044171322054100317010180c60703883c0031038020034a4001049002010b0301e960980c00000c0640001c0c001840c4075804035001490200c0c2040810031450580c006082503051100780807900794000c5641c4e40c281590096 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287015503 1250 287014253 287014297
    0x1406070305070f0506071d03010b060f0703090509010306020a081612111e0301170615040506010513090204061209150b060c10050618010609050913050f0a170708 71
    0x540da000481c1000313420340c02088200f2000c154061107481040342e591001c7d5a0510902d81818200c4125070442d54006c00308210b80400030026802801c1c0262003441d0000d02280ca502c0840c0242c0002c0e4800c0310b80c5c03030700410300650300c5410104080e4004c07000b0340d003641141014080240000e44030f03004030404035600d00044902c01882c000300c440000c1200548001405c911742100d006500034400d604441c4103010450500800c0070030701c075004104091b445505000e01004100c000d12026001d6414400200060200c00900004000041904010060722146011005060729000800b6142c40d9440c0c4544031002603030010710014501d1f81c0100004541e0811000308070741d481090740f002410301c280d40080d04d8864043d04042d10902c1e00341c0d1304440380384400300c60200c640b00038040c1e04040765507420240a94100f0840c1c581e44544001851110700c036141c7c84103410880030b40031104494011000c5003040c40441d6480c0041070f001801c45a1504000f9100e9000340d001c4e00c032001c90143c1c2020400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287016753 1250 287015503 287015513
    0x90703150f0e0f0f03120a111b0309010311040803030f09010e161401090b070f0302010f020301230108010b0412080702270f0f0402091801050718140607030507 70
    0x511100c4015100070482d800100401e00e9940d4459400e0850f944280c00f13031001282000300603103981e040c03400ca9091036130b05c9039001c0c0c0002d011601142120030806203da40030990b68070404281d1109107801440e50340000d0000181030365402007402c50304102c10081003200c85800012203900c43c0c0284104d8040e0b49440704104d01501d085641c5081c00c2c403030115003401072414410008222007805200c0110589100015201e42001744a100744140f400e10541000c1042e481c02d00050510900c00020038046040c54002203810a80025400d00341ca00c0d200c4c10b0480c1400260200004242030480c4a9072402040c1c042c2c512403070040d1304881100d02d01220801078084d042d01c00740303a802414404a80690031081e44000c0038100101d1800e12240c020420b40307411088030078001e01640041c0501551907809100000d540030f401014889050f0b549a000d0804c00c2c402c0d240903503036940d59913000741c0e115914000000e041d0741003070f001c0036a036a4004409942d80800c03103c030b0980c94100365440e04414109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287018003 1250 287016753 287016761
    0x4030b15030a0c090c0815030c1201020f1201090506040e06011a070c08010c180503030a0503070e04151e0e01031202070e250507110906040e070909140609070315 71
    0x102403c001e00d402180b4052160401010304030300e995504229980c1e444540c00d41041400010f0b050340000006182d07608102c0b140c9210102d03641c001614004075858403031160b44c00070720200c0d141d607040c000503c252a076a020303054211104039014048130b044031800940b10740d03042c8603881c0b4002103a8640000b500400c01942c5203260003082c10007140ba500c241550280c0210b034980710010700f40c0c81100302c0c000c2d5800c04040607544003500450400d6510300d010b4820f43d0010f0080c4050210015200c0741c159164002c4c0405442c149071027480b40c61400201c6032100381e070100c2c8071040e1803003041709200580380340d6140c40c1107a800c10300c40342c901090004240e04001c07035900100700710b5030001c081261040300d035000066040780c0e004001e038110016904c02c40b09402690402003611701040e0f201146454064401d94004030000e1000400c1c141c81d07a103441c58802c49902402c40f40ba101d00c091b030180a540141030082203c61000f81104d8034083c01400d032580c04c00c1c0402405009208817100c8000b1003680 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287019253 1250 287018003 287018023
    0x3060f0610090509130201090608160f03091b090c1403060418020613030308070327110a0e060411070c0603090503120903070b0a1514040b0303040b070b07030204030b1503 75
    0x210380c0c445c00c14507003400610303111200580c041255040c001a07503520582415200310040e00740a2903101e164001103980001021403001010745038840200800c408504012400003148400c0c0030b194a4115503400340c0d0f2080f4000000e101070310044440c03524195048aa10507000c07030340001d60b00303035540c0c0c0c44007840344145010390800301c00314045c203410020030015010b89020303407142d000941d079410003141a43c02e49002c001070903104900703141c001d031018a20416283d102e40c54407040c030641b0740e0110ba01c0f0b03043c40d031150f609180383c0e805101050503d48940c8100d80e200800741d0b486c00752591a10340c0c208031039215040c20140d69483c01030a0000070700a484210704406010400307401d00c070000b180d070ba800a00302500d0606074040451130200c014030443c8942141c1400c643c10f4180f9084401c03403840030700b00a05800c29183c9108080641e003e00041024000d0301c80341544411507404c052422000040004d014188100002c0c00491400491141d002120311040040c00818801080c2892101c1c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287020503 1250 287019253 287019259
    0xf09070605030603150903031008013b0d03020d06054002040e06040c0201050702061302041d01020406120204081e10060b0307020c010318120207080a0305070303050603060f06100905 80
    0x145c24400504808002036000c1c000403c08901c1c0c19444403929401c0314140402e0702180200151820910f083c00b201e01048180445807c990007100401c115040610000d038010010381c1c0060b951703050b003c151040034041c1100b43c500250944058a4180c0a01c0303401d2407041c00f851728200d80705100c1c4500d0390170300e455179600d1505541f038a540391036410f01c1c3c91059820a02c83c42c10b1641d2903100a00c14031034584285010303401018940c071030341000d044901400606a03045911404113070f5541a200007042ea5800d420000140e03600d18154000381051214a80c0d0f40c42d031801040200420500001c64038080301014400e801d0048102050914100348031411125240c20b1080020f110b14031400a94070502c295000c1e105550400001102110300340581003c00c864050b02810115114250f107608420040c011904011340790b007442e619045888504400065001410344200741c1d050003107c3d004135041e0010207482c00c203244001405400104424084c140d800e401101c854410744000700101409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287021753 1250 287020503 287020543
    0xb0403030c03080c070b0402120307060e0606010e0108010308090f06070f150b060a05180a031403130f060c061a0a03060b031e030708030403020a08210f09070605030603 74
    0x914001d00700c004099410707804144104000342e071180c1e800381102c040030b902419155181e40c0303035401c000168000038407082d11488244040c400292030b0b841014144106080117000500d001e000050070302404282e41410030841d0401080003c2104045d1262079000f201d202d4140b81030540400c00074052000017400402d001504581405400c08841c1102c010415081c0b002e02c4038070082c4280c82c810244102e00080080080d484c1c54078400804201408005180e002d0103552030301d440b21500d0b03220043c01e4140e00001078151901c04001c2e03a4500601c043c41140303900e10715008000c4d000e0b0741d4100c000390050f51034194040a00c07000310180b280502000f0501c03201c00751281044801461034058840c040e12074007058540002d0200410300015800078010762505e282c035682d220032904058030072800d43c4940c1e64480000b40070400035087c808000c02c21b03080880300508141c55005070241c0500030321078541051103181040031540c2d40c190f801c182041a543e49501c00803038500303201007905c0e02404140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287023003 1250 287021753 287021759
    0x5060a05060f1f02010f0621020406080105040507090c2606010c0b1503070803030c0301030206210f04110405040c121104090609020306071b060905030702030105070305071403040b071103040b04 85
    0x2c0305502a00e6000f15030003041080c5055000c00203c0e01d060040480c0120700758103250030079000f4100d40562610140010581035a2944941e084d00c0007902d003103441d5004a0428400b20103c0d12840407614214903105016608080c10440d807201c1044c40400c551a5560000d01140d024800c1001004e9012155900a1401c60030402d580c3e100090154464040d546002a810200001f960b009650100360a480c59103107a01b00031481d841022091450215001866030055041c1b4034140305d040d0b010092503c92070b01d45400900c000e140007405114525003420310004c0760105c2d00010688603a00c581c9500c0104508100342808042d509566100d414040303401c0c01c0119540054a083d4030a034100c0341e054840303080c19910f5205e5006080c2079100c820034450003155031340d00305080e524012420703613240c144036801290a440040390302ca804a6124000d022440380c1c855044141004c0b141d90b42421402e195440000e0128003030514410403c080303042c040180c0c0180100c500415500259695a650b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287024253 1250 287023003 287023039
    0xb06010c02030f0c01090b120f060109080d02060711031c02090f040603150c090612020a030f050f060907090501021218030604060c1704120c05160909060605030a05060a05060f 77
    0x507135299614002503200740c00244c90750510003920180050054190244d95940a000054000003000107040101101d800104001c0902c01110481d03415030140c070f168505543e01410f0410078100803002c40c2e00410907180c000d008400e0305814007031401f50242e079881d070b040000346c2a01c40d1100c207540d01515108001040050446100120003242c1c02c1c1848000300ba90801c0d14854080d205031004038000c1000c092001805070f000b4a92281ca50500280c44682d442800d01114002c407407441001c400c040601c096850402126548800c240c82e028100d03505241c0000c0d00d0b200103142505400101107904100c03420303003103240590440d010b4111401490175052120240c401401020003054100c1c60f40719a5000781034660f4402c0760407400d0642c508084103000c42c0c640003401d1040c0e401e40101320304290031340501505500140303400701e000b251105d2581032000449842d540310600c41d52003030000b00d0000340e011482c103a001005900c00141070f510720020801480400740724681c8060700039102040e1003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287025503 1250 287024253 287024263
    0x11104090e060402150f0d0204140414090a030c05070302120a150504030504030201081b0a03060512031602060c010e0105101e050604090e070f0306021c0501120b06010c02030f 77
    0xa045110034821a00750300c0c552501c580054a000c1e400c03510901030a607090000000508041360003003200362620115400d03007400c81e00b0a400c015865a0b60304000d10700b9190601400d151020303040e0441406052a0115551b14032803818006d09005040d48012706018044c850781d8011500a0442408038400c1c00800d621501c0010040355241c2010010310104c1d03410317200d19880b13260b050b2201c6241505540041d80d9150005244c001c0c21810410326000c801c140e1805000126040d0714041040c0d03041c40d007001301c0c001c7c040071007035550b500c140301c034030742170880119649540b503015503805594cd01c20300b07000d0b80900312900350304e0215801c0500384280d80350f1440c00a0116040c01482c03407859240c0c03d000b00e81c5140c9510546a00100c180b10500070040250f00c4400301050000444021310355406c86001c075081e41e5402512013075400b04900500d0310321102c0305030303082e1000d5408101640c184514151403013010000508901e07205000604075034006d1010446050b0003d0403507070b002c021042c80a035aa = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287026753 1250 287025503 287025509
    0xf0203091306180915050a20031b1204060e03070b010b18010f080c0c0c0901090e0c030d090909082b0b0d0f0204050411120c09130209150111011104 65
    0x3c10112407100403990041c4140e01c2619440404e03a6695902e08207640060240600009601c90b955100344a040c401c0e201c0c020803500b44080d050340c0700d01c3c0c0144201e010b031445d035885043c000001c014446c1e5030901c64281c0c66200e07034448000980c2d8014a10090700c0d50107280300040014445000118030313042140c01a00b280c00206004c5c040c507201400044a41d100601d000101080c036040200340044c0010000e464802a01004c9907000040c49000800d8803e003030b440315000f00c0d59180c0461403502e00b48200c159481c415001404a140b143d0360050110b40c03035100743c0043c1541c0b166000c082143d42c80840e2181d00803034141107403c07600f010380090320410f04001050701618002c004006800e110b0b00009400e9000b451841406038680c09120150a000340100c03045c0407040050a2203a9860b01d04c10499095a0000c00b0841c80c25824040d001101030b200f5281100b44008110040ea41d50f42e080340e004c545011000941030480380181c87c80921424000429401c0902e040742081e00c850184c011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287028003 1250 287026753 287026769
    0xf120f0b010605130f060813020402090d080c100b150703020c04020a05090406060206010b040308070f0501050f0a0e070e160926060105041a010804030c020d0f0312050c09010f0203091306 82
    0xa5445c6000c5200d0b40541c8500c5001c00d045400045022189041c0c406096002500242ca4582c4040006150a0440034219414580440e00f010100c1040008520340a5008410400f00b180f450004407810a0a00c1034245640c002402e141050300c01c0c840d1280441020f04199102c7e501018003815642105141500551404500060492000512034129940c69101d0707032402d0f04607160700c00d030b03903024002c141d0302540c010081100003a424031035148606005003d04500c0c0c240711981c0c0042c0c42d5026070082d03c030352021005000301402c284549400004000e800c10109010300c2c3c0c2030384d000c1d8659001c0c0c401070321050304000c225030714410701c001105500000e4507100da880d402084100c8480300c42c4000001031440025859502510381c064100b80241020a228030301c640c0052101c101140040715810b84030b0759114101904950981601c0d20020030622403460500c030298541c0c060b00c40481e0410440c0c03030080e2006402441190010b0308050400c074004c1c0c1c41901403038054012031159103a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287029253 1250 287028003 287028037
    0xa1d0702071520210a0c020a030b090f030403120f1803031110060b04060809030714100b01020f0c010813060204090b101704120912030e0907090f120f0b010605 70
    0xc0e1100010842e0401c202c10300c41480c43c1180540c642071060b17001805d801003885150100080903075038044010004502ca6860300c6140e192240c0c00500345400c10300c61070290340c4280024000259100c0c80090f04c0e0015140c010b41ca140340090840706004511080e056440f00c01e040070003410350001e4111a0014685c0031035606400071099201110224826114280d0b414801400340701d1240d40081c2e040000841101d007800c45a840d00ba07002018114000e040c2d0344510001540c800720340c000c03440020024000b43c05041071401c203072a100c0c0d81c102c6865040040c1980001d400c4800d0700c503070012290304050115200c03911102c00900400240c620039100d00c0310041d040301c0c103500c40c035040f25031003104415401a54540c4e0766410b648080d004051820722440b000c0110350b560700da6102c1e0200c980a66104617000e000001400303290180901080c0c2002b4013800107120240c03403007071003900b10b405011280f007159001d4205a803208110030300040000b0740c40c100019040c4c0e806005091201d1350f04550003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287030503 1250 287029253 287029307
    0x31513090b100b071b2417010b070615090207060608010e0c130b030c100c0b060103052809020306010e04110103141801090206030a0207110a1d07020715 67
    0x3003025003103841828410a030401c400e02c00101401d541080e00c5c560441c41c000c14688a01800c2c2810b1300010903959105038690840c160240e00400465021100301a8843c00d94140444403a540c4030340f901c06000a503c0d500c0701c1e811884100400e02c01001c40301021500e45032107281000180030a44543d449540c00c0c032180300001000440c02900f1141d00802545070030791b00f444460060005944100d506000315100d07440261280f055501c04003034155200f4030924220314002c8913541c1c01409030303030426103440104940d0200f0072290403000c600c14164403d000f960104036078050450188000d4150203440b0000901e40005070781d0f140558811020380a58a000c10011000c541030700d8070300c0709110701180c00325456030444203440002c50558400030941e80126000b1410a070b20980c0c100210981c00244d450034001e1606104510f000100d4540c10843d10308540c0e001101c80f0100303660700e4002e9080c0814062402041000004c042c0207042804541142c44040c081d858000404800e11191030700348 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287031753 1250 287030503 287030521
    0xe043b0c0406210c0305150901150807170307140607020601150c1101110d120f020f0921070305010506011e1e090b120a0615050f031513090b 62
    0x10100b03461040020071501403203c0c034101c01003080400141d41c078611058011000c01c5007403007034143da08010319400040341010303107985007164280c6180d0556012020000c0c400000c011030b902742218541d010318013468881000c1d2506601c00c03020010002d42c0c650000c0b01c0c4c101004141d20b481002a902669a141e03030303a6103640340e0b103c0544818030010309036000301030004d89a9100401c0d81c060600d0b096184408008020703140072090076025011600000510f413003107032240503106101140300e80540c00c0110003007a00240e4041c0581c410700c550074001c100c5100b40b400003250000c042ca0403084500c02540ca08055000b0503040d80c0e03060005440c0205000a2081c2400182c662480f9035610080315a10300035544a440410501d0000c1110350000060100f4112002d010300300407140c4d02c01e500b418580b0b4030303004545641d4403044440b41044803d81105411100780c54401c50403800f81682c179520120006601d030b800e04507255100440007219850035495038440c0100b0343c41404412443d8840d9110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287033003 1250 287031753 287031761
    0x3020f0a03080418060506070501090506060d03080f07020109120302040e060a030b04060504170a031d060c12060315040303020304020414061003020903100c0c05100c0e043b0c04 78
    0xc050b0500c10100000c0014401400c90101041241030000031001e8440c000030300a81d20801c1e0641c0c0d980c3d1183d1036141800002c7c00a25000380c4d0441d80c0c007180410590f0054101c0e5001004249506050400602c03224001c1d00b01c080b549600480e1a030030f80392920000f4000350845d00500020304400400580f01e402c00c0b0702031005881c2c00108040c03040c1d45517035071403018150080048400078007200911383c0c01004c1e000980b01144050301d000c2052a0400b48691003110010f9811109034015814131407100c10640c01c0302d47e03000400c1d00c440107555481c03000c2450803107600705502e0b03a10788480400045c194564059402548215014401905c03a9001a440303d0019180180e0100c4191034002400f4040d5005200940001d41602c00742c000021050301219402d201110115042242480070440c2c1031025075414020803c0400100c403601c0c40c01441a1000d00344140202c1d40c640c0101c0b803050000c0c401104144082d12001c070f1442e12069051a215140104581144106284401e241c541805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287034253 1250 287033003 287033009
    0x501020c060d2f04030201030b060f07031409060a03020a0e041406101e030509280305030601110706110c03012007021503040605040c06021b1306050301090c03020f0a 73
    0x2019040c8000361920000500543ca0822541c11140891844001d410342040c00d4261903056201d844925500024095415000b140c1e442501c04000082e50072020340203860001e0b0301454800301030b5040200c40300540c410400e44e582d0000000c03c001080d04d5140c0c000304031910f00350340c0e5047d80c5c1c0204810320040d5007a951181172016100301c001101410042003101d004141403a01d01031031000104040c0c0e5102015800000003600c41d0108184401d040001d101800d41c1600040c400d81e00071343ca031186100726441c00500300480000810704c1a031007541c000903401060000d0f1901346680700c601400c03000606181590b203005492101030360741f50600c5003641261440018424140e5400c41400701c681c0450790490303021501140c1e0b20502c013094405580300d248220030002d10390806080c02c7c82a401c5079071002e000c40d07104400048070040c1c0d074007201e06010b0055402100b081000c641c00c2d0f02506654214581640c03912000009005003581c6130011030f402a100704c400f224424040c80098010b0780 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287035503 1250 287034253 287034259
    0x14030a03090311130e010212011d011203050c03030f0f0c0f03010909021909020901091406120a0f090516080705011d0109090612060f0615110a080c160501020c 70
    0x56040010030070f28001900314810003031096000b22020f41440741250b40c10740c000c900ba6036012410040149a1049150242400c2c070181501208608520114400140250806060000f0111003058020002d80d8140030030314044da0b48a242440e840c0c241d087c0122078504954074102c02041500c07007034500300c1c1d2520300c07260001c03441c603805d280c001009441c00e80c50880e040301310858000302070b0b54815400380141004001c003594500756000014129102504450441d0250b0140555603a880e00f04550180000ad01201a284d442c40860001081d000100c03218003820f202c80d10041000209511400310070700b41d10f03820400d0301d40d041199140d8450040301e0214000319000c1031500d2010602c1c0c41450b04c1454070009294440070f1400554601d5880b813a009410421030008200030b42c056248407144d0b5201c10850035180a102e41201c99203a01c0708000e0002100002e140003105101d651400303500708103415500c524690f00d89030323944451a03d0a07c4028040408a040d40c4041400c800e004001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287036753 1250 287035503 287035517
    0x2030903070209100504140a0c0e0f0d03031508010917120f0a091502180f0f01030f02043f0b0c0a02100e0d02280609260414030a03 58
    0xd50030f00600e0040a000c0701001d190242c0c1c0050b403135032940a90403003410920303040e480390308001d01d100042c0d8001103402e1013801840d14441f5095206d1024010140b48100d940d044002c08504050307004105245150282c201e00480100740514150441208140f0865001500700c181c003659141501580107151641c0b003004012501c031013956034080d6000449404005000a00c680c1e85040c0d071443c1e0804654850340101d41c1d004040f44c214414041d00d40c040d51450038120f02c0720002161401095001418581d80340082e0410f0150b81d0305076000340c124903000301040406a521440a0b4803007000b000900440e03103101a0030740c0c01c0d001d00c0c4040c56500074100f00850b250643c42440c1238010310418001c40c0304401054000b100a406000c0b080703107500e0054070070144881e00090414001e080d400715400a80301d0b00150002d840300c2407a00b40c50704924005000307501840e001c3c0350312040100c00c4540481c00740e150040d40b1840d01c0200304030b0382c1060107407420710132410505844522900d0040c020500c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287038003 1250 287036753 287036767
    0x90b0f0609181f030506071b12030203070e03060c03040b090708030f0a030b03010c0801030309090b1c0503040b0a0810050108040b040f03020f07090e06091f0c0302090a080c040f02030903 82
    0x600000c5500141c0001c0c4070084845a80c40d03e00c22094680d2099035a90300c80414000c030780e1303003011907000d2040344c0c9201150840b10039229014a00e03038040c003072010035900200241a09101c2d0503c40610040141075810a0409030700031300c65908161000c1c3c80742e4100c100420508440082c00030111141c0d100a1030404081048035401600610141b02c07c1c56107402c2c85841d507070360070b00c950011000152909000b0754103508000342844155000f031003110f07280c420740c00701541e2500c501c01c0118842441c280017040c52454820f055024690141c0c08100010075500c81c07582c0c0040f41c0314400d441c002000c4072169901c4004482042c015580a41240da101010601007200078104460840c00380c01140c000000c0c400c00c0615020556000b50102d82d17441d09c50380c50111f41444290740240044006016090030400080300303035010195400d8040b40e03510a800b090a00030b8041d01d494000040c15107410a0365002040d84a00c9020742c05441640303445546040d0345114801e6030b01072049280150b00b0482 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287039253 1250 287038003 287038039
    0x1050108061f1206020d052401051314040204170319020c010e0f030f060a0f060504110906030a1451010909020304031701060e01121a0a090b0f0609 65
    0xf80e400c41c01d640c1da82d020009101080d045018281c0614810020112038400309a04203010660002580b41046010032064906003114010351040d2116104610350234050003000400030721581d40f184100c0401c1150744845480040040c042d104031002d8010091540c1c550200d8481d94405040d5010508201d002c00f42402c244a10000c0c10002508030340059a8400c019450114122040700006486a40080300041d150140e6001031406039010300c140000c01e002e194107402100605030140f44048009040800144c00c41040700da500090750800d402e28543d000c003281400d401c1c0d50101480303403c0c002c0320007424290f40c0f500c80f0542064685e21403d01440d08202c0001040d0701410800aa00003040199051000b98001ca1082d00d605003044980070780c103941c0b20016440042800300c01c2d800040c2c266004030384001441001100003a5100038040846c10a4030301411aa4124141d42c2001c2540c0311241c0c030002460800f02d4400e00c1e4800301c03078100801071045080b8079030130184025020000725 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287040503 1250 287039253 287039279
    0x611070e0f070e0904150b090906070804030c0b0c070b0705031005010e01090b0301171c140a0c1505070201050108031303020405091207150c030504050316020a0f0801050108061f 78
    0xd0345261801002c620f4400040d0400310036071702502d0158500c3c803030a20102940c8110f145002c1e05440402c0c840c41c0440d071407900d6140003003a04003400010000107081610501c00d030405e007030307102061025508001c0c041e042e041d00b181c0700c205c031013040b400c0c0030814080c001c078241d0b8800c41e20000f0404140382400700444d640134850340d185052040820307002c01c481d840900a9800f80c402000940485080c0010a600d4031800214203413503803580100e29611250b02c84d01030380385410503840055840306841000c07220141040000303061a800c140f5841d09000f440d8000724013500d555402840741d03989401c040c584070b00c0340d00150495143c0c540400c01c018101171308807650001c001c1c0241c5a0416610070464140da000180407101d4044500043e01d10750b54038414401c0b80c0c1400c1c9401c000c140707095034480d59a0f10403200d020140940596600045503140c01495016214441c031a5002c9540c2d0f200c4140a0034080c0034040c00b5028100c00100c074000c0403064480a007a003a00303074000141c90700520801c0700d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287041753 1250 287040503 287040511
    0xf0c0f12051c0b030d030219030e16080c0a080f030a080a0605091603050f07081311060a020f0601080606060a1202042111040618020a0513030c0611070e0f 68
    0x40002800a1490b0440354681d8161800424101082d04150002054149011000c1e04814140b0508c25102030120341d4501c110b0644013410001842e0039604004da26103d0244e00308030f0084c20550010401132404110b8000300c1105895003c2c0d92920b070740c4016100c00d45903200044650040c40903824840c46161050707001042c02c0d50001e400e0b5244c0d00800c5403500200c41c2441c802c1e00b5509482c0e070032641442455402401860303844444e0500250082007140054010041c600340130701c00c071081c05100803003900054001040a90b413056070300e034087d444071041041808180107540c00010444400306040d40f0443c001041507241003e100b87c10f4404500c1d00d01e1120381650300b032001082000c116000c3e40d0300807603652039a903c0341d400b034540f0060f00f15907411400c3c001c5080c00020810300800b00b44081d0003030701b80c54000d6226030b00d40d01d00b101c05003e5401011a40700c2842400424041010104402e0700c0b155581c41c4401048841c020765190000d205108a103c06140040c019280d0a0301c0c1b6a04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287043003 1250 287041753 287041757
    0x10302070c030b01030807120201020406020703020607050c090a150f030525031a0f150a0501080603150a02120612030301030215070506180706020f15040219090504030f0c0f12 77
    0x516201c1c1c60341034400f50b0980088a15880c00100c0341c0501c81d80516034400070780340d80300952a20b0304018009440780042c0c48000d0081101156600c00c00c44d06100505100304007800181243c9041d0018001500d20400f9260f000654614041206080c84024205594009009141c0c1d8041150113002c501410024062000c2c0d4054000c4001003454004086041d21219094881c0c1801401540c5a020240104200d0100710090f00115200c0a2030f002c100d41c400d08000c10700d9038070f00c0b0200c0d0401c0400b1900009200c214000c01185030700544c06066144100c020f40c100e01d541d620306001203490000c2c217202c00e0303a005000400040c6080007808043c40001d000803818941c1503954103240c40000e40303100d83c4044560501515600c000c12143e001411148001e02207a1000e0707015607141c1d044080c80c4c0c00c0b0307420020f00080c150748500704000042d2080550084000341d6846076000100401c0c1c03000c500041c888aa1942020b2080803510f00550304041001e0070078881e039a035100340b803c40030fa581e41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287044253 1250 287043003 287043023
    0x10b0303041701090b07050c160815040311160f05040207031d0307032306060901050d0303020c070b041701140f180c062b0522111c030e1e01030207 65
    0x82c5c003080a45d004440948615488203080340c10a42004c03648154115015000c004c104a0000c00041d0455204213100c00c3c400103499905046410301904a200c0e417451240800ca05849c2e80c500340d8040445501d2409002420703100c17070400c400d82c400c00c42c0c0a0005002010602140c820492401c0c8044400034229503041340c5e07079500c651a00c0c400d84551310407a04011185403103154140007084e4040c8044944042541c1082c00040741c0a103c032a0140c1015070200741c40075440400c09c05600680240041940c503195110324007112840e545695040950900c08440b0f031508031904601e000e15041d911203035a0366283e040103003864420460b802d01d10700c6000d12020303144d243e0f032004000100203800004480c104050102d96041606907103002101d25190410807180d40e540302a1140150480d41c01102003840d0030300b851100c03801c42600b80d02c4101441d41c4030704030481a120a00062094403000744c0200f4403420841c80503c044d00c0200d04080200c084052988281e0045c9429440344d00200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287045503 1250 287044253 287044271
    0xa0c050601060509090a050615090d020909071a040305191a0405060105040c08060d0210052b0c0201090b0103110a081f14090c01080402010311030f07030e010b0303041701 75
    0x80c03800c03200ba8010000300d280060080d0550612520316580010314050031b1003a4102180840d01002401c0c01201c024000441d0040c015551415110100d40d0010424036941c1001c400389a280c100501ca103402d0300e00401e81402c1c218002c401903904903034011001e004405200008510910401c2d4003c607400e1411f0300110740744031113f005840c05180280c0041580c0d40c1040e0a0004840c00c500c46002070100300c030104030065a5400c04e0200d00c0c4d0f810345a549044c2d41540080d12030f40a011880c404030b05c004c0b04a0048400c080d4144003080001070000d1000701584e00090342218003080c006048000d5100050002c15035000803030038910f00280038040308a40d9a070102e03050484043d0440c400d002100c3c03180d2001c0d84030340240c82071901c0603c00c40d2880d003840300b07a0310340e2500840007040c184240c00001800f5603010768000c02a0301120b03121107590307107020109840c280380c0481c0c4420200e40350900d42a044241486441c0030703140b0180085140506040003016440304c030030003000c16592140d280c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287046753 1250 287045503 287045513
    0x6070602040b070f020a060201061a0a022b020d0c15110d0f021e04050a03030e031606030c0f03060803040611010b0607050313090507080403082a120c030f0c0a0c 71
    0x3d01ca9503015136070854100c60036104101d10b10515502400842e8140802400307501204621416102e03810500d159895081d01416810220340344662040c180030310745031840030809101d4181c0318100e03035402c0d500342044190054070500781e05000034000c03041c1c0304005010750032541c0c411b074007595011f1221403c110380740039100161550091800000c6802044a10f240a8185076020b486402c4a86660038141003101140304200340d444080c0400420264a41d5207840c144101e0303d1258000c01ca04144036110721024000c0d01222010200181d5045805030507203109218040c1a615150b0145203010b00d020b00c1158200c0c42203200500c59561800034509998846d030042c00302c284a44051910b908400090b50544e1b086940821101750421040141640d4030142c00c66015506080920403502c9841d0f903091460002103581e90802058024400b1409200c0040c0012004a100d010241d07502d410309009240004c0c0d6801c4d05000865010520b1003928001130071216815203001005030280ba229 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287048003 1250 287046753 287046757
    0x36010c140f1b030a1a0408090a0311090a050709060f020313090509100903050d05073e03090d03050702060f0307080610110703030e060d020c061008060106050906070602040b 76
    0x201c1a0160700001844441440320303201c26051400842c0030308240407560311070500701140040b841c400840000c0c0010100010f65094505114001c1e058068480d240d10b03007480c050104220052103160303840e0029001900500515104440c42c0e82d80c2c002c114078140041d40c0c0b10b0141c0e2800415404140400e401c40f442c085160710050605171008189424800e60440c14651080348592030582000940008a50020220b0b00004000716000031103a480300400c50342101d03074010075482c0042040f019156a0f1880b180030450394948003138910708402030407d0580c0d902c190250035410010350601400468001d0002c0c081280c00604001d25104107040f0071b42c0c6980c0308945520100e600841807054a060000900304031000d40d003010484160404c03066907494845100060401c000f03660784001da43c80f5141510303210240102c0c1503480b104807560503a2900001c454554404848410004003c04001281c45c1240c5140d2a02441c01c28803d0500003194045003040d07990980030000045c41c5c0d0078000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287049253 1250 287048003 287048023
    0xf03010216111504030b07052505160b0711060f09030f0607021006031110030e03040b0409050907050d0303020c07030b010311011106060102070501050d0e0303070536010c14 76
    0x4520742484954004210f07001084828080040006020038000102c514104c1a0081c80300d0400300e440d803050f00c10301d00020345503070302411101a120b4900c0d020007000084500c0000403088070000718035100d8408503454000c260018248416054582c101820584010034415011b4041c05151080d81c402003494006a0620804141d100740204142c0c1c6c0d03070600070740a803024501c60030700049146840b04452500004001c610840c242c2519a10080c040d0303002000010b641d905481d10b4603901c0380d002405030028070a40c0b59190402c40040d410306000f01c0c140b41602c500809021581c0d40d9514120009d41100b090048039210f80c0c000070000c40c02104580e07008600c20740c900800d40c9140c00004010004a411110a42e80714100340041d03031382c000c41e104040d5002071030240d44610f14480c84038080d2400850300022404000207210041350b00030020a2030038011513040040c0364190f02078504140c5100280d80d0000c2c21140349035403940c0302c0c2c0c10803444c842c001c0031180c418010004040381080d04100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287050359 1106 287049253 287049263
    0x60b090f1807030203010e0f060903070309031e1e120908061306020f0c01150602030702030601050402031810021308010501080c060304030522030b0121020f03010216 73
    0x42e0320010750f0000c0082c001c803600640d6031502c0c0c403d0581074140701d024120000d0100c0c1e500004980d20740b03506907210710300035146842d4006690310110507442c1c0802c1d04001000810314840c094040c0111940c171485403800c6a207040d050b4070510360b4256090094000c02008410000306811f41c0c00030029020696100241c640007009124881c001c00380301c400803d00710685201507010f15641612540244110380e19070000b40c0e540c2c00340c2c9400961690000e0018400750410742c0165810200100e4014541d0356440b50060a004c0b407074081c0c00180b603001c1090405507003d84074110003040408002c12495041c564600d0722070840a0760740b800345000002140030584540200d824030180343c20307030b12012454183c81070346400d00c0344400d40300c551742d500000c0341d18002d420702d50b2625280c828050050000c1031b424845408a41060300c0c0e4955800d101c40350346181101242c0d01309610a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 286870503 287050359 := by
  have h0 := BRFrame.cov_init 286870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 286870503 ≤ n) (h2 : n < 287050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
