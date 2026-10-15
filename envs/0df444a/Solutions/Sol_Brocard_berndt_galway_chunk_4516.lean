-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:52:26.975813+00:00
-- url     : https://prove2.me/submissions/3fc664c1-bce3-4de5-86f4-47e14449abc6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812050359 ≤ n < 812230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812051609 1250 812050359 812050381
    0x5040b0a0b150703050414061c0f0b060423060c0727060303050c0f030f09040b150c010c080a09050d14040e16030c0e0108130206070605090a120306050105030a05 71
    0x1c90305103800701d00d0229400c3d040c181d10030043c0081d0345654880c590000703804010031000c0d010b513481191032030b40c2070715583c0551491a041500702004c2c01b0804213044d8910000034180b81c000d41c01c0f499004183c40f81e0b80e0481e01c825500c004540074103551040c17500e01001c480c1030301c800650041d02d0b0100300007105149a0079195400c83c0c080030141900b0095643c8034a0f00a18592003094050818800c2180704214190048102d8100807001d801e00c0d40b0b41030b40e41080c84041c110600e0a203911110106450488041000007481d05c0100a000010070902004000c0e0190501502d9100540d142442000c001800060000460502420700d05003041c400044d03513207144104d40103e002041d101f0103104886401c00b412515001d0180c9080c011344821000448040460700c0007240040c2c4104003203102d24200404c20300400d800a403141d8a000038549844007540d41c02c1c0c44030902607101d2203842040c0009072110400003040c3d450b040c4941483d2400080c03290101600c09040c440d6681d001c40c80402103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812052859 1250 812051609 812051629
    0x7203c0d0e13050106050f25050313060207060c030f0203090d06020409240302010e1512010f0e0f0f06010302070830130206090d1b0e09070f2102061c06060305040b0a0b 74
    0x1075231390790100c504c0305454050340b40e0704400c4d42401c244400f11008242c0c64000701703180041d0b4000769070300000c014464408844020051100109500003040996200d0b11a100400d19640c090765015944501e000b61003000c580300c4105c990361694030542581c107500c7c4c81c0412141113a80903c0c00c15a1042e010001031091002c0781c1d1440d00400002800c43c1800c2c0300e624406040755017a9000c80b03901d40c0d80703c0c0c01c944201012204410560440c1002a9050f1345d040c02e81030700039074189401030800722281e5400c2c400341e000701c400a4440868200c1d13054100c444080d40307010000d03c504071400d1030070601c2034410840c0c00c3c110021322641012030380030741646940c0b865a40003504090308598895402c11008101c075480e019500b1004810310004000d00c800040c01411949101006044039107032075420700500800c207400a4040001c810b02e040580e884501528401114100703190340101842e904104448241d441041414100010007020130040080e05030311041e10703400496000280300c009408400303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812054109 1250 812052859 812052907
    0x2040b130606080c09061b07080a140c01020c031b04020f0d091a07020a0809130c021f05040c0303080a0902040507203c0d0e13050106050f 61
    0x4000381050520892504564119455901da00c1482d03103c42e0700e140780c1c91140000b51900400d0070813111684020030401010007805503015103150750f841d4510b441c1041c0d448401528112200103401c004024140300e1200914402d0000382b8001782000d02190b15010003c0101a0b442c906400e210545c0d04d45804454100b107800710820341d15100380e11494000e0004540c04d8400700481f500d045000d044021206014075030751303002070540044a0f07490b4a81e5912003c03d960b0840c0c0c242010f00c21748151800342840c04e03099500500319420041d84040720741ca03511001e03008458202000e210101d08800c44604c1a01e4240c5403c04d4503944501401001c0e0901e907000035040fa19007030411101075401000344400035a032220750076040c00170f084415651504000071010304101c1d003029555001c401d40c40b081085008003d10301d040000107049505149a04070b400307000c554280c01c1e00e00b0a1038002e6034030b040807140020410440d414103c00034418000e0010307040c0b015034000b03030500c44817a400a8440c2010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812055359 1250 812054109 812054119
    0x6010b0f13180c030504020604050409031404120308070c110103020f160605011707080606211f111216020a200f01050309030f093f0a0213050402040b 66
    0x640d40715109011510340303610000b20306280a101040701e41c4680502d5000e144c008103002d042509000030007009104143c011010f0044040d5800ca202050ba00600000d01c03070b0003094620f00d601800d0180403603000070226000c2100b008508030000d2450143c0e032000030420f20b80180c0728692a89031340030700d114030300c0e800c0d0580021a00c600704001e125001107069075107000e40003941d101d2000b0031aa0300d40140c0100201500000006845401d00c2d44c0403040305000d80a882e0380168460740c0c41c9041c03d01c25021510300c01e8a0400355410840c82e0b003d1541046c00310380c002803400691046840c80414007928030301041d01400428800ea5108105611080e03800c503011035006101c0ba44110716050840720302d94020381c5003d01c0442c680d8054003d603031040d0391550207545440c180703103075016490740580c641030b911070090410451013003012070000501c2c4103520340c0160a00304d200503060013144654881106948280003c1005031148207086500070782e404800300b050b48403403002502400003810110703000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812056609 1250 812055359 812055397
    0x2030a05010c02101e020a0c080a0e0108070503131401020d060e01050a080a03020304270c030c09050301051302090405121603120504081602010e10030b090f060306010b0f 75
    0x40300040d807000d40d84079907030b408039110340b240000401d0a54522400740303a5075450320045002e820b100c58006081085041c035100c240d00c0d005035202d4080d0340001456900051000c03106000344c2d6006081d550f007080860400328111315020030701e800f80c4c1c1c240c2a401401d4080311400480246000d40503a244020b0b402004c0c41016101c0c5e1070400408001d10134103119000c0341d0300004160f4804200151140e4055001d9440c040c181181c0904809035207a01c5120625a00f4220359007480602c900011006240d8002c64445104000203011100e15004903209901d8001444070343c4ca00818524640c0d40d06072902d20301a81c42d81007840c1407540f490107104c1c0d46840007403482c188443d003020255040380b003511a0394990b00d41500040845208840017800e88204005c490708950822005403201c034414505030414a812a021070b20b00e00c45141805d0100b501c0d42140c4e1a180740c03410b04e030341d40004921902c48171841c180c1c00181d0f90b5030044c1310340110148000369881910109001300c61580100300340d035002e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812057859 1250 812056609 812056613
    0x20c0a020307090b09060a030b0708040c05091302130b090a0e07030605070903030206092a0415030308060a12230a0b190c030b0d2a03050a0b01060f082202030a 70
    0x51320080412921070521350000030002d00c2e14039002020b4a420117441c50030340da244207042c2e844202c050010b845e003030420800011707160f440020943c41901000a070380b101401d170b40705000754500c040700b052591606101712508261104003005500038240f20b0045840c180780010700f400c0c20004e81001e40100d040400300700010740c020f030625007164802c0c1d08036003065503209819a02c41d01e02c004c5048001c0940024015003210340c801c01001741200800c0040c180710030301e00e8a102d0348403030b40c0100e01040c1c0c0e400804c42e19191118036200204401510f0b80c642e1001603031800c4420040300421100c1070000c4c00107904801c1d04001e031411f4180c0c440278440382d41c100340003140e11540311040784804203401c105009000c4c5101e401030402165000e08014900c0301640d4902080f064101d8080e46805001d48a01c04401805503c8500842c0950080e0a004900c0d05048284030f405030005001d001070948091800340e4005e40b415441440840c41b020010000c5660701c0c0d0880301c40c0c4010350f042c8100700e01402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812059109 1250 812057859 812057861
    0x110304091d0706020d0c0602040b030a09020f04200705030717090a050a030807060504111507021f0c0f02060f1b1b1011010b06040803030f06010c08040504020c0a02030709 75
    0x15450340e910740d02030560441000c80d0350310203d01580005070800b410040200780104e4441501520410b0058100ba07114094417400c0c1c1c10864041c0030041c0c984c4424030640c00c01c503007140500c60301942d00303102c0781020054040320f81c0c000d81614800c4080004042c0c061200c1807040e1490070380d0159969015070034900303041c2c0654100015461090328a84400102860a40031074800c0301d03440100e0600f082c9103078480000400d001003094900604080200e0802e50701c0b008440201048000354a44902c00d50040c01b0750030784501c840e00854419500c074103204a400907400300d0003d0384076401c00e120700d41c40c4c0b000c5902801020030f41c030224000454903028108041500564592040d421141c0d01800d00740551800c0b80300160454004100040090b0020300c14112070700c0c0e03104940004150b0b000044003103451a4015405200c00f9000442482600d01c0d00042d03a9800080c01d10306001408c0c5540c68805061140303102d06c274440c40e80040c41441050050100c034444540040513a04400d5490380d2030704c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812060359 1250 812059109 812059121
    0x3010e060703060b070f02040203130b0106020a0302100b010203040b0a02010603080a1e020703021509121204030c0e06010f0507050a020a09062c130201020709020c0705010f1d06030711030409 84
    0x440420f08101c0042003800000701a18900340e00130b10030840000084d02800001c6d40013400141e402c0300402101004511100e822038000c004903401000320341c0c0d032420001c3c101031844030740c035125506040210825a90000540c0c0030f0340c2c00400700c036507a086260003c0c0e00402166100401442010601009842e00022115032030230210030000b80c602d030310880807601c0c0d411303500000394050135150300ca54122621101502d19040003524007080440c400030703628603009001c03000c0c6842800010b03050081142e0060010300404142604032410304000c000642050b8080d102e0100300100800e25101b03000e0704000c82d03034034180c000c2c02d01c01d40c098484240401038031550141c019a18404032440c0008880044420104a10100c1001464450a1541740880b02081090341103100e40302c40851000c409200400e01c9210f25401814413074034080000d0001c284a8160406124034100c40041c05520b41d10500b24522007207451a5499482c02d40c02d50311407414007881402880f0102d008601140c880d8458 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812061609 1250 812060359 812060371
    0x8030a030e01051b0306061303051b010c05060c0d110c07140616111810140d05031b0106170f0705220f110304060c0f0504060f0507020f03010e06 64
    0x20302055034001078407403d8840a40c2c00101118200d850003040d007000102030754001400030034440c50040000f94007500240142c00c20354030fa410078103110200f0b038801c20055030381c103100f801c007803280b03148607100c441d1640c2d001828103c550b0700000e5050b65602c51340c5d00c5103085a001c001082d07211946080c07010307503600381e60294111200750a5844809441d08005980030b40301c0e0004094400d050560703e4075402c50102c50010b802c5100d0314a014250326080d03da0350b2140c0b6044115000851520101c13083e26081d00408500a175000c0144401150340802114001c40d0700742480281242226000c500401070f0303074001402148a8801d840710000e011801c1e908060010040354040d9442c2d0702000000c0010720984000c42088002030300a131082500040b5070080740c1d200008040c1032065000035207900845086a015959506000426401c0041c4015403080c504d011820070f4240302018003241203407041c1a00b403210104160b0704541c0d03401000128004050024044100030b880102c1d5144c03425526 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812062859 1250 812061609 812061611
    0xb040b060a090e030d0b0a0503010501031a1b220806070903031103030601020a1e0b0406060801051609141504080c1c020a06030515090408041e140120010608030a03 72
    0xc00551521580039905072aa00070014515060200401780001d0940082c200d800000e2400c0004844c2c0d0284207142c000c0d40203920310395904140102070200400b00805c1c0800449c03640108000e6400c84000751100402d0307032584034240356464035a4200520081c2d000c0c09503441400200311410307030300c001d80c102102c0c4245c803940c1909803d00c01c032549a000880b60240164810410740f03001c40c090800300c541c004002d18580ca00c19001303440e0300596035011602aa01e40e500d80c002002150024450079a100392031194a01507000c22200c01009450113224012240042e040480320542c0d80c10500b000f502d4407443c06030fa89586d9030424903190b42c080c504103446400103040400304840c80c40b0310031000c9540148940300950030030005078010300e40030300000603400c01070904901e2a164146640e00640c020a0b40701c0e105c0d49812003084546a641da50055a02c050326001c00c40020158210740281200b4242404683e00c1d4840301d01c1114851001c20100790700b007510001d0314440c044005c110b08481d1b513070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812064109 1250 812062859 812062879
    0x161a0103120f03050c0f0307140403060b09150906150903060a05040606060c15180f2604180b1c0b10060c12031d01020c03040e0108160306090f0b040b06 67
    0x8043c0c0803a64105c4280c2142802013046a60646990005591003e25420007110035001c0c0794815000360415001110b205503142044c9031140b4103840c0050340306012100903610b0102050110b1b4010b90f000e452640110b444800d0801d40d003606e03500b41c880815000d01201e9a0345051200603024080a86054881c83d260040c0800c0a501c15032580041641000b649085007220001000040800810f0301640311030701104000040c40704150f4035001c900421a035a02d064038140c500d14500d00c81810103405040801080002c074201c58100a404492000009006060503000c40c4410030819050414515000e0310349041081d60b050082c0508288508909019240c9509454482180c000501100c907981e1040040a1080e0130041607284240c030340b814034129129042d400d9030000c407225441600f001c03a040c0321007502903c03294010403054004259450304a1400701d5182e100d400044c0c500d5445445d0041401154069001c0351030b0b011519426a01c2c05c0d0410140c00c420903a00180f01d400f1800e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812065359 1250 812064109 812064137
    0xd090609020a0f0b0f1e0706150e191a09090d021c0e12120d020a0e190509220b041203050f0121050f0303040c0b030705161a010312 58
    0x5020701c0980312520043c4e498400d480c1c2d040b05c41034115003402e28044002d0b07810034112180c0c0c0c3c8080d10225100d900c010a0a01440140302170800c203030b82121484050030820065008130340f2800f940318044a800025441001c00c4204040f11012170700680c0206038002405005880001d502e00c0b102082d900341ca503002c0101024528603548060524001106442214a02c1c90301c000484071070800203003140c1c0c200209413810300b030940118407600c120507408100d04014030307084107035807090800403504010484500902506030620900449001b40c1291001808c661125400110f91984072810f4104200b681d10f860b02110300221800c8655107100300c80c0304602c6000f809114010400150030f81002e0b03003801040220400c4482a900501482030121000b0500c01d0180c000d4010a070343c065642c0b45410300300b40368407910a50045120410030020000c115600c20291007034a81c0465804511065038100603030340001040485070200d030924000030800c003202100d010041079644070140d40d40a09 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812066609 1250 812065359 812065379
    0x1b0221040e040b07031d010b19050a0603021c0f0903031a092e0e012d060302030a09120c1502090303090d0c0f0f0303080f06010e150d090609020a 64
    0x900c1041c40404a40020400040e01d44021070b6100b80c140c03600051510881003205000035044885c05466591441400300c1406c006030110b80c895088080e8030007032460320010442c1c1525903c41c10b02010350100b01e1581816800410000005181d2000d03c110241015203600a211400c0114042842c00c007087e0301c200c00d44001821040340c000c00003040c039621000c1c905000103110904500d50000c3d400e460f81c0d01010000610058145201c515003150704000745801d0344040041800d01494242180b406a40c400441c61026601d10f40303005600e03500c1740000c00e0f014180610004019100203045c6400c410b5001102000f402c0c050003071250002d4602860300120701c510034205400d40c200300040c2d5418140035411002c1d151107002e00341401541d071010303904c550320150001c40010061100400074581e0120b2003e030405002070741140c0310f04008001800440f43c042c840d9010300d0031407880211183c0094261038103030103800c1090220003950300d4100020504800c0c22031003003030764050200d500340380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812067859 1250 812066609 812066617
    0x30a06050f0f01030218040c050d0c080f15070e0102120c0c0406050a140415050d030206011a03060f0d03030e011a12280f060f02071115040611011b0221 67
    0x14004400440e00c44003124020030f001003040c2c0d00046230301e0700054a0303200c9011414800d402071401103003140c00d080345c00303083c0b2041c414a280c3c01d030700c810707080b60041e0101c211158212200c1c0c00c08030309201c01a40140e040a10754200558113100100d00707801484008034403580702c1a0215420418661608200250031950740207041004a0380328400d13020b824281c0c01007246207a2118040c0400740c1d5031f8006000900000802c800503000840108040c40c2c2f010501ca20103424071451a08600e40381c0e01240b0603a181a0007580308440c10003905013898040e41c4042d1500c01c2c3d0030000e010449814418921101d21124814041c41c2d61000c1c1d07004000d00826a02103c50590603404101c000c08170301d200c3c540e545240b0648425200246403000903c66101d035000756203c508003d40c4580c8203040040040300344442c10b03030261180f00304c858950903501b41103c0554038035003031800c10360041c503421500606115017141c201010490700e41c80b401d50006036550036041c0d00305c454072000d90040309405023406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812069109 1250 812067859 812067863
    0xc050f0a05120f0c0a050c090a02070206071e060603030306062c01081009061203030e150705130515040806010b160620120144010605030a06050f0f0103 67
    0x10901202d000c400d07002000320090050519082c64141c1c00e02d6424a10707011030884095001c200000b0050410142c4540e100700100421810a211034021501d644541c3c0c80c0109249160420a1050040f80455101c503681200c4200100307612854064020300d01e034014031300070440ca8800070752800c24039210a40e84003202041c41c0400000f4100640c0d001c440940710080309615860042010089480740304000c1007490100d070001c140e0b40c180503003121000f418082d8190010100700422048100002d9004010742c034085681318451600409045c100d40c002903400401c0c00100200c1070841400750007552042000e560441c0da0320384140303503588a818a00070400e0f45554206020030010b900c42c10b1030b1804007100102011441a03000e43e603601880090241001e10001030005003880c9500010404010b440d200030b591441c0b20700c0d6800300c0c9515000d8100300095440c040b091000303400100081a0160803201d10300004d290400c064070b8220398a2010460400014a070701c007600b01d07014100c90b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812070359 1250 812069109 812069113
    0x170c120c060423090a2a0203090d03030e0d091401080f19062711030915100b040e07030e0c0f010302070512040f05041b050f130b0a0c050f0a05 63
    0xa20b400d400720900400345000514281a1030b041c0c110b01d4031001304180c8200000240000d1511840c414400b9100e0746043e00740803140942c3d4555151900042110802c040849a030070b1a0381d0280b070101d000e04054034041c6018007609000100311034008c0040410703610a0000d0300c0b6802c60f20001115060000c84003804019444004207038200720194a110340400c3d18600409c12036111601d0040264001da8504c108414004c215031030b0404601c191b62041612030801803550500c089095542c0c0050b0301c50180c524500b0b0081441500e9400e000c80c001c00d0911f62007902c4d00c1d07803440a249211002c5036120082030418007003480640000c22541c4003450700602c2000c0707a18000e40110008d41021000720303014400c1075101600d4413480809440245801045a00d14a05100902080c1c1c0d8000b040c52303502207000403e070800301b900702003603440104440001c9615032101e03c0040302014140d901c51100b0510004005209170340c0000180c40c240e000784101c680c0400890152540c070311a018001d4015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812071609 1250 812070359 812070367
    0x1804020a060c030c0602161e11130617210306060304030c0303151e0902130317130e04060c0c030e09101d1b0703050d02070c170c120c06 60
    0x35024030b0b1a5104507000340b400080c9010265500d104070307803201880c0300602a00c403900808200004840740b82d41040c5254080815403107075039140c040c00f000b40c001e03071081c51031448680d1006003d5101e940100a004440c0b0440404901542d8a4048054102d0a1b003026a41c844001c1c004982c200d038003489000c0d220520b5a40caa4500b266014078129003282050381b11881141c80070a4010f0960142100c0c00142403510405032011841142903800881c045005109504500895140c10f0041300d420401407011050f03132440715031003840742135445001c0b08000d11000c50b280803414440d9201c1c0f44590b20800c00039000000c1510a0750b070000340240018520003250441c0e00300640d0b4140c004804541102246854441c8a100461910b90103040d49004208010b903005400103034146448844101c2440c00e616618000d0041c4034003820140b14580020f070794410801c3c1c040c0c86c40300601e2110700d1031490051040c0902d40303901152070060301c01e0451100440c581c0c01d011503408810754009040c02d1030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812072859 1250 812071609 812071619
    0x1e02031225050c030f090619030e010e0a0f0b180d030203011e12030c020a0b0d020309210a0c1a04030e13180215040b0a080117070303090605130f0909021804020a 71
    0x103960200d00e455070402420321101d1031081c0201050280c3c5c621271344000c1542164910511300f10b4030560341c0704c0f00c6903000342c0c660000b082d440b444a80300e050f0030980d01078036680c1c3c030700b07a0780c003000c901c04003468a520500c0100607003164554059810703036084410107804031807000f417608007804030b901540b20040a18005000024080c20016400d50b202410f0701e1412a6180018060354100c280c1041000d5000820016401b4043c080700980ca40c400f040d00000c000300c00220071860094091000078031080100c454144084031040740b0740081c80340c42c0003900e4900340c5401030001e44541000c9000c3c1c0c0b40c40e4030040f120708150088180c894410701e001080c038807842d0200400b110700d040c1e1650070800200008107007a00303407000400c5007404030b84a0400c55450010069840680c100d114000c83c1c2043d081800041d074000100c00450b9020315105448062a2001d804c0907040e80d40020182000e6007800107040c02e031a00603000e414000c85241c0f504220105440085050444000750311489245003404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812074109 1250 812072859 812072887
    0x3150a05150301050901090312020703091203090503160303020d02011103070e12011d070807051003020d0b0d0302011a060c0a0308041a011e0503030a1e02031225050c03 74
    0x80e0095006502403000d00201001c00d00311401030b5505179841e5114008901815002201200300051146c011444c0440c05d8400a00511882c00781c1c03103402c20003003004030a0601c5200d140005d000004c0643d516111840e070b20b4280980c19103c22005401140320590a00e4010b02c11000818510203580f0304d199070b11542100c0c801d01403003402d680130f911402842c400040903c5044145a42c0d04c001c001e0340c13800b54408500c1c110940d8401203465000180038007054403106810103180300a03050258642c0ca55400f0030000e006d003225410307040f1024090004c1455815040f000d109107140b100c400724541d0300e40500540c1c0c4102c624205080d481a581d84000a100c1d202c00395109000c0c8400d05a0682c1030300900000840a038020340208045100045540e81d07039202400c000d00084000f1441c0c806400c034090440115946608140440d01201d800945d00034400c039034160001d1101100c0b03d00e00302e5032804606000ba0022540741441c4a910a0a02e0080c801c5480c02044007008608102c244160b580d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812075359 1250 812074109 812074111
    0x20601060509150c0601060215100303080c0d1e180b0f18030d060602010f06060e120106050d05011401050609090a0b190303020102091e0a06110102280e03150a05 71
    0x103034010085440d158070f600c40b03180103081c18000a40140003294074010b4000d2409030030382c40602700e0a0044d01405040e00c030101c008030072250b160800e504150388514490b0103500030301c04529071890800c010341d1605480308680b501c65026114003002208039510034800701444540e001130800c00c0d00008105a044282d69070340e8045045141d540b0145039031010f0030708541104020f0b4042b00d1311458140041c6030280140c070340c1e0a03500c8108008180c030b041c8001b0082103912415a0003450090404001840700390007400c00340801800850300885945460350080c051003100e000400d0058001255070310784001242c5200d20020014249070b119214400020098580d03581d03481900e030490404070480e8644504011402500016100c10150090102010800c001c0e100ca030000b07109410020368a440c0740b14241d40e0a45001c4e565511400c0c6030b940244a410b09001015106004c0a0b130324410700030480307406036810340e0b90307410481c0030500f8160784040381c4401001c464a001c00280e81550030364411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812076609 1250 812075359 812075377
    0xf040b0d0f1401090e01180303020d060b03150411070515130b071706030127050c1f0909090b010905060d350705151003060203070804031b030206010605 67
    0x14506114809070790440700501d540c00c4074111000300420034000c080c42200e08000c1d000b8001e100d071030584044160041c000e680024145680800c0400d000b40d142d501c0400035042c0d440b1241d40c0da05203403507804521341101310a18400c03410141d05e541300c1004041601e14182e4003030010f0075405541007107440c811000520042d0131a84c1c41c046007000c22a600c42490040c0c003151101107803a0103490b95440c0c0f060b801022140241c0c10015403140c0e02ca4014480786100d006059100c3d15142e035440c050341008034401030298801080b401282d42c02c01030300c070854280703402034980c1051b890382c81d81400c0594001d824040c040144107401044240d4190b00040d40c0800002d0000b135440c075280d030700c18258481c0d90301d074503010498072035030b01905034012100401c64140c00f00215007070010941d10680d5502503820041c04100e001c2c000300d20001000f4035408080d55201c43c0a40d200d01c0d0121004000726005c4505600041100004a900c14020f058003190f16170154003403c40c1d41c0c204981a81c240e4003601007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812077859 1250 812076609 812076611
    0x3080904090812070c060c020f0c100210050a02090418241e050a050117032713050405010b011409041a040c0e090c0f0313030e0a090c090b0f040b0d 65
    0x10380305280d40000030f4610a54040e00c44004185080c00c241c421111512070182c1950300c00340351075001150004400d00003a80c1111100b10460002008a08024000b103141c56001d0504051280840d06500903204101c81950b04000c26000c5801c8140d0074494014081c0022100a000c09030b5690f94a4074140003e020703c0300420203082c13101891850620031610340c11034603641d1040c090240058011070707005040380c010b00e40620703407090f062686038400d039680308038110702604d18080007600f4100380c0120b03050020500e806041040d4030b02800713010b044030121055403070150390306802d601801d17200c40a1a044500c040c00c280c840000d210080c8079545c44c80459082c490350446441e540ca010b9404815a0391740c403140591a10303000e10000403800b0f05030b244280c40a1001044d05000d01c4280d0f94030a00d070528416118465007015582c003030b6403011464202400e40004220044a5046807040e07030040e41e02c034940745548280c014841d0103016180100c1c1c000c1000200304a281100c0940341b42014584 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812079109 1250 812077859 812077867
    0x702160915331e051605120a020709091a090c0913060b040b0f2707031d01091e060b09011716030b06091e0c04090b0604030809040908 59
    0x3a00100d030348100986190008650ba20310075420315030088a041161060500d6074000203044041d41c1200c00d0500e02804000c000b141c904084014501012090340d00b150540311040c50544121382554070908100002d0b1140070390000e4205824030403103c08a4009000240700d0340403444413540e14002820304202c621805000c0301c1d05903101c1e03207158024039000c0072008049901d4605482a1064504a240b08604d07041300d6035403640b00c240e8540a0300030308940c2460049000500c20500c0380d484040d03240b9018141040003100b0ba0954030a0008841603041200690017245003182641c0d81038600800805900c00d8100020101c0b401e2a1805482003d000c0b0b08089050b01180004500341e00c089407a42c01d00a2081c85100c09100e4102e007080400421300d10182191146200504080c0c40f6034050075003100050400c01100080041d52103045100d0019820642501035980d085405082c800a1400e41c2550091600000322401c0305d521280b0315081c03481c903800b00001002004000c0d9503050f0104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812080359 1250 812079109 812079119
    0xa17070504061d121b0108060603010b0c071d06090903090a0306020c0f010912030506120a0b07030b030a0609050c030312130201110f0709050c030712110904060b040e0702160915 78
    0xd10340a0b0000b070600000c104518260600722040602c07440317084e052007060b0b4144420358a07040300701e0741550788290350580ea072001c113a1020701d44001e5902c41c3c0040f040b0350f1495042000b0040f51580588030840e6248140d807a01454986c5900ca00c1d04040e5100c41156010400502c1e1500540303103047c0e4280c19150b00060f400111030039100e404408846040351070709200c09a580502c03829400210664140c2c04240360300c07405595079a01a000600103026040005408501c2a0041c90344280d01409881440400380f800310040d002c2075100300c0d4540200001349032541000030a807540b685a503562100786803500062a03888140b1310600f0b90402c0444a060f5815890800004207550643c1c0300a00202d46462010411210702030001c80e0141010001d000803ea0320420384850418003100006522160300900c580e603100f050b18a94001d81010701c00180c28988038060011038121201c8014035640c0c240e0300301c0c0c0703c03050104002d8441203101e905005590355540203001420f110038054035481e85070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812081609 1250 812080359 812080369
    0x90c080d0c05150603120705070f240305151212041e06030911010e1906020708010b040903170924090d020f0c01050724020a17070504061d 61
    0x21200100400c0340241e4003420480d040245001c050000e844101e02424000000380e25580070f40c522210140010610300c0a020742440808010880075482203281c55451606a122107601203440594440803146004550300a01620344120002843da4044401d0391041140c0d25401e44040d1110b4480c1c1612000c1e0191084028405030086000210b4004144144006141d07001d8100b402014201100c5000044900e400340d1404c24003406c0826065110700c0110b500e4400c01c4100882202c0603c5001030f01c0c0c0d402007580c609445030034000344403103d0203d0500058075a040c4c001400a41210780e90104900050f0301c980e00200000c0c140d59032203684d1215150000e141072001c4801504c1c0109001d10341c20100102c480111aa0024101064000031040c0c1c5031011500e08506100002410300100031808004a0047c250741100c0c0e034031540c3ea000044000d401c40000e22021842005a8402d00d500381103800348140c00c81d41e04c051902e402c109046908a49001d01201c071007504c1030113100641c9e10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812082859 1250 812081609 812081623
    0xf0c0801151205270a02090a0e0a0f060c030f15050906130c091805100b1303080408240c09040b1f0e011404140d05070b0307080402040501050a0e0a090c08 68
    0x440005601d010005034041c0c40c0120007a54104d01a0b8011080000183c07502242c040e4803841440002598084214196080c5401c0500003480384103100400c00810015512140d86000b0a580c00c102d002c4030702c1016004c540c0100c032480591014441c0400144c54809095075001d04082c0011008070340b8002c001d015a285c84901402040110b0003e1107140ca00e82c81103290707048100380174040d50805180040d0b01840c14010114444070020348170b2220785a07a0720010040d0342c00034005582d80e54403c84541c40311502611030102100705403181445505103d00c10b4000c0c40c0d0f0303021441c5003001c100c04010007406125034440e000092162016160700740072001c171980b1055921440034850010000400d06a2040040c05581500780000d224510b020501030104050a41c0d000440345100d0600a10b003458030f038014070b80e00c4000800c00c00c001c0d9000d00540c1c069442a10b0a0041d80d8950341040500b40c06400340c0082d640407000002c5072240c07290042d07030300640908841038040c0d032140482410000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812084109 1250 812082859 812082871
    0x812040503190f05030426040e091c3c030e0c0604080d0503041406070f1b0b06240a0309050601090b06040b0d110714010f0c0801151205 60
    0x40b0b2000071403101c6441000019019103000301241da4032820141c81400041d001402412045210303c001c40e04c02c0244250920000548903241e5543c0c151a411000d030441d002c5070320b800f62061260805664021030f20001246455842c5900102c554072034400d103440c500e02c4407000d044810000c42c40800701c0308a0303138007000365808074004000b61921441c10038a014035034001d05040004002c842c2002c00d2003400b2003c6454000d50b039440740e0030180d0f4601d1204640300c1c81c80c00b43e00c0500c0710710740d00f041500d40440120384849103a006100480e44d0381d41204840641034842460014009190900c4440721240000803104e0000b200c9080140194201640c0131002c41d0f1340b050640240101040f4560041041200c02c0c407032910020082001806544291580560041165a88804150401c4982c0c0c502441c3e035684606247c140010031954540c40c60755594070303010142510707241c14003d04450400341e440f100016440c0505200b505604045000204140d00b841408083c200b4080c80340104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812085359 1250 812084109 812084113
    0x2b12090f030f05011503050303130303090501061e06020706090501050a020f070f17010516030b0321040e0f0702060114040609061e050603190902040b0306040501140105010507051908120405 83
    0xd45503240a84c21504400e03200174200b20000c0c0100300190000003107903440440391814110103001443c0076006400703092030040c00381d4248100450788131150607140000d12a000c0b02c40001982c0e8000a03a101c6e08140035000009a0100c8e060005500030402803e00341e18500c1110f032440c50440400d0b061060a0700421000d55090b5401c0000e60780f030010354104190440002c10041c100800000c0c1c02076031a8402006250710b610344081590f4080c8030380c010136028560907041250748088000d4043d40140603805501a4001c04280c003c0440c02d1810b21500464008040b5a400c1c01d00a04424201d4a0000d40c019169003003c55541d07154084e02c00244840051080324810b02258101c462407681c11082c060704041c010042d81a440c2d00b00700410320b07902e20b0b000030101240c3c00820003504540c0c2400381c141c4580c509100c2080015401541c07050b40c2c100c00d25551b662110011603240c804c1113005000c543c000b01c3ca144c00c203501034540982d442d1040940394541044401320020958088405540a0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812086609 1250 812085359 812085383
    0xd0f06091103010606090b070b06010908070905061005040311010c0c091d01060b0f070b1e010e060a090b24250c0506070206030109021b030d0b2b12090f03 68
    0x500b401d014860103402d1500b0301d078011790b0030310314540517501841c1e03c0600380d0044c5202194599025508400240c20144140e60105d605e41751600c003e03020641c0c1080c050340c1030001980c4280d03c164140da01b9aa44209158942504800110b40f8148100700588007801d80751000901c20480e03119103416070b84c031030307949600c5500709001140c00c4904030344c0040a610700420059a940c0030040803101c40e2640b064140086880c0c03514042e0444070001881d0084804038800850350880d6111030030b214044c204d41c40a281500c94804400762440c8040c0d032a041951440e070f0741180886d4060011641c40c080f60b01c0e9040c0b4600052032049418007111034000a00388031070a0051103080311403400500401c1d50302a02c1d1082c1503002c40e219100521551a00035404500c0504020b160202c000900c4a110200ea0711545a503000100800700d5040c4244211008045102c00d040a103000c800e0465a11030480401c2209440d1000900781c003440860410410072404141e9880e1205c21902550282e05410340d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812087859 1250 812086609 812086643
    0xb151e010212031023030619050a0b06040b0a17070f11150408070819050903010617150615040902040e0c0711040c03020d05010803030406051b090d0f0609 68
    0x10603400c90100402c1c03510800801602d0b2140c1d00401c8105c4080d40198145031449440c05d00304440000340165060107400c1c14403084104040c450040244007940420203610b035040458211603c3d1004150010781c00c2c001001103010080180a40e5072941c00c24940d000e5500c11581c00383c80d401c079840008076010004a41403964000c85c85c407d4890340800400800400c0d001250021000510081c0201000200002006a0002650703141440303080c82440258440401130901d800840345180a90f01e4214000340900501c50543c4665000e2000f40a6814020f406200391210040c0f02c9504403022002d1080011907500c0180001d15041c000184c03518140302072560103e0015103881f02104003403190302c0105044803602010307050101c400103500c04002009401138000c00c141d01102a180000001c0c209001100440c4114454141007125603a1460320781c0c100e0480071903805080d4400c1c007108146050454205507904e00940185903001c400b0b550b45400e0f02c0800c0b0b02110b611380403881018be = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812089109 1250 812087859 812087863
    0xa030e010c080c1c0206011a0307170a1d01020703320318071418220302070302043204110409060b1816140708040e0103030f09030f0b151e0102 63
    0x42c3d2400c130742c4003400055241505126030001d0f041803554440c040000480c500074010694070030645201c003410b21191030b0440e52070b4010030700403e8828641c0c2010110602911040c802c82700026807644541c150309809140708846100300d50140105e2542900604011418080145108004100d00020f500040c02c42103801c01d1965070005281581c10f90107a049540c6200004429030005525443c00d696650a60f000b00b090795410b210305100782c403408409255001c034020040d40c0c0280c906001c44050184000b00080c0c01e16202c1800040407144440c1c00c0c050404902e800900a00c000b030707410ba0500b80014200da404070811515541d807107051010500f400340031010a50408602107101e40b034421440f40703041ca03081d0131000030440740d22034499034414030006549259410603042500c907521038501c0d01d9008030a00054001c2014070152103c2c1500c07880300341068907444045074071a8481652240c4005201130304000d40d022030015401140e40b501304551044802000400080130840400a8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812090359 1250 812089109 812089153
    0x90a020409080a0909050103020a12020307170f0f030c031605102c0a02010807120908040b0a02070b04050f060a0338010c05030304110d080a0206060a0b0a020a030e010c080c 76
    0x71740c5490070200104003680e1074060035021202c0340030f02e00980f95034501c0081d0404c0e45036042040380411130444c01c00c0c0100d001405a0b510003040e421552a1a80154150f6407070051801c00381403503004004c86e5001030b665120158465204500301c0d8400b980d01e11030001654030115215105885403000e5107114581ca103025011440241c000c0c1c1408500345e000200b1445c0f004000e01c1c03c0c4110742e440130b01c0714160ba51019000c103410986e45511180c466100d00b0840e03000400080051081c0207006c1820307a5079008070340455200410324451443c405081c4602c94024180100900d9940c000ca40d071a900b940704005201d829002e09005442000301030080d0f5981e20388000c0d8100000012040d001460000481340c0040c2c02182c02d510820210700098007840c6000402400308202181c1e0706155600051aa80501b0046030f1403116640c4405001401d40203400c04080103a001d5050400400e02410000c2c3e0104010f15100000084a4480d1411b55104c241c5134a0310303070712841b026a11501108552 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812091609 1250 812090359 812090369
    0x605070c0e1027020d02030a0638041701140c0f03190902030a030903030201050117030d0b13290f060a081906031407050a0617090a020409080a09 64
    0x1d035a182445064041c071020640541d0441c512107480240d00a01d0301ca11004000b8100307a8190355030114105c03140007a4005407907100e1064280003000c01c00f003c1020f5414030f40c01c1101c4820040820926501c018035160403000140f1320301c200000b00e40d481100004c8060000e038174001103106821140f10105211000b0403910300c3d540c09210408000e20780c1d1003101e400511001030001600a10000d01c8000d040500009601d0321884010504040d0000550002c40b40207400070002c5a0b03071400c12030400d0100760b0500b40c82d03030001c00103032040a40e1680010b0708142c02400702c0200c90483c400ca0f00449000200c1940481c07220742c1031114100d14003c1c540c600f40400d8584440d104282408100503018881d46001886004400a00300350f0f144860b000d400590040c0c00c1c0241a41da051215146a01900f408414018074038081494100a0011002c50b030f025034940e20b150b4020341e01b02904070400f9180c11400d0042c3c8101c0409a0f03580d000b440401c500858000d981d8a9244d44090841021640f01d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812092859 1250 812091609 812091629
    0x40e2a0a0219051002030103150e0a1101080709080d020318190b0711040f0516171f080109050304050a060e011209020d0c081f061401050c0a0c0605070c 67
    0x1048a4181d808103040c5000d500425000c451019a4581039080100111a050380e02d032001c030000060214100c4144072503c00c0150800025a25000c919100d59529901030300036401e41e201117072154810345e0100e512045d5171420702003a135180c0c1d031b050703050001580e81240103074401b0172640800d94050a010400101c01c071a1a04d41c8402041c007158125024401c14410420201d07607802404603011019802500c024800c02203007206001d0040200400e99180c45000740444201c6d03003423800380f101040c55810610325208241d89100c014100e0b50080740c01d0311603954140200003486e034000d0241180c0c940c411406561070314202010300c0b5088049510050800c4450004d9045507600055409045c200c420008941e00c140380c00400d80a01c03083c3c200600340807030300344c00040742400420381d5416030011103d00380218020307040b104e0995002c5e010301004050000684c0a00e580100c000744a01c00c000c070284c86c0c0691858030f034288402140d174002000f00f100003030080200032501c2d60030006000c580c88 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812094109 1250 812092859 812092867
    0x803090a05011b030305220606170a03080109020d0204030203100f0507020327060c0d0c0b1003050c090a1b0801060207090e0c150c01060308180904050a08030c040e2a 73
    0x1091411040ca042c0c1c01a0605d691580840c2c100c04100c1c0b40e080c810445101d0310003100046241000090920748903034410343d0f44006415844500c003042c0c058032541c042e524a4200d0b428505920300a60210f0090009a6801c100010040e1820700000a00e038030b0440c40040e040c2c1a00c80c242c429140014042421504100400d17000d07080f0b034009400400112035510b80f000e11002c800b0580c580f0520324090f6a80c490080540085507200e07042d42c2016104940041550710741c42400141c4003114007004100781c10405020429041154001d075003c1301070078002c1800303188411184007130b40c1d084803100001010f8800511100360100403140090000f41003c00c1705030340c070301c2d084d03900c442d000850140301d0090049000781203140581500c000c4a003c1000300940e0366207250442c00382d4442c0c00401100c0305801060745445c505a66924822a005030103880450f030641d5880165074801024400203c400b400082850303a02c2c00b0045100d00c45482210307200c4034003003900701031140201c42243d9003610200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812095359 1250 812094109 812094137
    0x1104020f07031d0a080a050f19170d051009061a030406090507081e013c15062006070905011419030203071d060909041b0803090a0501 59
    0x4111104a501894550704000e1031010000f150711144601a81c03180c0004400b04444030080380315000709110360101c80e80d84c1e60340781d0304c15280d4134150400741c41007403490840e001084c001c2081a83d403a0503d02c0403440d0a84110020742207442c159441c64400550034001d00c2546074900c2540080c1002c01d1282e41c5002d02461200c3c443d01c0300401c0182460707142d03001311080103020021007000d8205401544d6600c0b2038003490b034000c0380d1440015001c80d2309100b0f4501310034107100115035003011040d9006058002120100040c0b11901c1052603000780e4074070650212b001d8080b1501e0190403640d55580c80401c0318050b04480700803203900c0c0360791600000e007031051103900040158100d030400e0a14181039440920f44205034060146c84010281e40a039540c258598954000c501c1403505840d4100540e120400ca101302e14200b55a040c0c1000d0200490100c40c42e082c8925584148950310707a9134141c03840c1c074011795507861960041d5003544c1f000c6401c011a161039101d100c007524084ca041105e40b01c600e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812096609 1250 812095359 812095387
    0x140c07030b01080c060f0d020909070509100509090a0216060c0e0a090209030601060e0d0b040b1e07141612200a0221070305070f0806072d050d110304110402 69
    0x100410b602000e800140d010a07c8055010303103860003802400404d0360b00e801c60307004c0c109074024800765100c0ca1902300c082c14106d0084c81138038040c81002c1e144d007000e650350500030707402940070459440c448000344000100181c0c1034000c4d010400c130306a0305e602c1c038054888148055015190006554580140314894441d200040c02c54110cc1091901004400d542d030085542e0307181c440c50151007080201c04203c01d02c214000c00c54044c80c40740b101c60001c03060845440315445808d481580004900c810a0f6003103541980141c200c500302108000300d2038020395101004541c1c641040c00214206400b507164650a04086505802c3c00c2c0c0007400d02c00109900050f115075030485009203c110800100c00c40c410100500000f03190b102c4201e03103d0313940365030030031007441840e04c503415007841031300c00044180748682c103c080c601510545221402e81011010301b00418424a88001c01400313010000f100056030103101ca440e5100303100140c0d00c0c1441e0806000941245c003050780600d0040000700134040360 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812097859 1250 812096609 812096617
    0x901030503093006060f030c031c1806030506040e011b0c0c0b0a11010c05070b010e0405280212160302060d0b040504120e01030608070510140c07030b01080c06 70
    0xc01c540785448915042c00c0580f004048000310040511400309000c01c0a1000030a14017450341202c070044c031280d10001300740e03640848041f06601600304000e00103188220020030003940c0e50b81d04203d0324400010300503209034281603004c507001039169018072030f00303007064400d03006019003000080c007915010303c0f041000001c41c15030140400c4101450081440600c41290340500340b000c5000e40d80303400c05d05d402001085404000c2c81154a007110040c0810f015100700e54107030b5408103154209a181000c0f102c039070500104180d68034000d40f0240708544c1c1204c040c4030315400b44200841d41c040b04034011310000302d50996201d20345901a03c40b903900a0042c4000030200c950489040e07640d40489858040a0185d400750983c0060418050004100114044054210f11540c846d040a22281c0c01142074446c0c03880b52000300d801c91802840369080006020440103060309000c0b10040d9035443d013510390f500801059146800c2a0b101b4410050142c51403401805e012005007801003690000842c1031117 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812099109 1250 812097859 812097877
    0xc060703080a1a0603071b050f06040b070c05060c1b06100807060309081b030c0613150b0d0303050a021b07051206010e0a0902150d060807080d02031c090507060c0b060901030503 78
    0x2458407078030070107195031f41d0324102480d81c028103650f00100c081c03e0071540d9007015102246c12100e24030004003064422420480c00641100040c88903880b180c445031556800b0380101064208580002d0320762442c1007000d14000c00041070241d01c0d062400409a003451815001901010306105090f00480c14804c00c3c0d5034080d901c1090907015040c5180300303603d144a0010800c81c60701030b0368100600c40c00000014082240200300c000d103035100320141e6200321040c01d11403c0d80000442c600c07002080c8a540459403120f11f503840140f401d84044810622050307405a081000c0d401460148074a0809c0e0002c2d03034482d4080d8008100c0d95041000d00700185800070450205240da07002c42d0307025036444143ca11840c500c4110540c1d82c500c0d5000d4410003030561030040704032512401d0000100c1c50f00000d003042419042e580a1418040080110800d2140c1c5200310b2010175116007114010032020300903d0020046600d0b505181900c519016072040f2000704800d00c01c2d90110700420100d44044110f40d82d0b44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812100359 1250 812099109 812099117
    0x1e12030e100b0d0f03030213091b0e1c0f0203010b010305010302031209040f06080303160518060d0f0c110705090415050403170c0c0c0d020f120c060703080a1a060307 73
    0x80b80c1100403502c00c1c4026400034048035003c4a0070403d0503015401010980d07288900309403010b40340c41d006800c1e62048104030544040311950341150a01c641c250308070348607005011200c2012284020702c00404000415148500441042011480c0c07d11440403025001c0c00c05002e550315640000c0d407112007002c49402a2100003415051560740c0341d02c00020001044400c200040d1039251450b0740e60802c55a040c421542c940d001d440032030082083e9403000040c0040301c80130401407402c0c00341681042a1044c0000c0d1900400d03c0c00040d1800b65103a107a0150340c2c0c8420450840c8442841c3c0200c651101d030280103900180b02c081a0706031110100d40d0b40088001c02c4076280c51404032507590100d04041c0825904074144103039000340000419680c2003a40c2141c2c29400c041080004005030004000c0d03000070546903040c01030034202c0c40d0082c8118488140c1c0d070060b5401340845e12075406998120001a0b036182080442055032060142d13070b5035414813044500c00103001007070031385c440034002c44240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 812101609 1250 812100359 812100371
    0x1416182304120203270907110d0c020303041d0f130f0209070e041406150f090f01120207030e090a05090c191a0a020d0503070203040902070804031e12030e10 69
    0x503802041120001c084141036402a2071410740d50064000d101402a0306c110841c2c404034070701a2140300100c40d42c200030b2014290000142c8000c0ea144281c410080703030580002d1000040040300344031101118802505c101040b880c1c4082840441c00c001484c00400948499052010494201040750450741c190b0702e40d805c1da1507485090b100e03441d0340004c1540c0541815443d03420300e1004259140608000da9140c1c1070325402e48a45451405401078030307503030302e1070500134914245000100781a040c50103040003038580c550004070906a922002c0c040d4049001ca104450141c245462819800020000b0401c024100300038819242d0381007940f040c0c031507620103075490076804425560030014403064030f01401807210b09140304030301c4d00004003510150184800c00b49240b4001c4040302d06c07078019540550b21309418400350000a403c100b009488450040c400400040c240c070070a22403062143c8800d82000381d0030303c0c02c190300241c40d40b43e038030405052002c010030194000594040c050b940c0700c404944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 812102859 1250 812101609 812101643
    0xc03090b1c090c140d03020613020a030b09061006030504030e010e040209030d0c120215040b0a060b160b09070b042709081308191416182304 62
    0x1141c0c81000840c80c1061400c1104020000f140ba110302c1104c0b08543e8404c91810f0b000d080104003414030ba40500940c00080004000e2045070f28641d518a00c0203041c255078944030303110302076142c2c1c084940e2107a03a0f000c0b40c140484081903400000c000c0400385418801450145e6004125521001105040c0282815140890b9039a5010f4a04041000e0211507400e40001c1c030080c400c041d582c600759000d000714450146032a20101c1e9441c85080d13401100d179800d4450350740f0142241c1004001001031030782c0e4240031410b0940740004002044090510090151180c10200d41030480900041800d83c00880e00300100c41300c0405a4003202d104102c4c03603104802a0980c0c4e1160100107040e07541042c0741c1a00311007040360a201512000031040c08081043d9203600007680d50343c10500400e41100051004800019840142d0386446511202551040d072113102940f8071740d00194000e4010080c240c0140300700410b03203101302c082c07030f481c445071280d852070750f264802d283c01402800c091304401200700d035141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 812104109 1250 812102859 812102887
    0x309050f0a091e230103021009081b011106010f0506090303090303030a05010f060306060c06050402120607050a0219020a030f030212071b1512050601090f090204060306060c03090b 79
    0x1400001c00c1801a0400d6040d0354040b14507803070f00020304a20300030024104c104440c81e290b400011000066003580d00795001c0280d42d0311612905c1e0304203c130003c008901e1720b2040c03100a00340000281c806129465050016050303507541650007009521410041009500080303525040300d02c1540d00c02e98404000010a0440c07154100d541c0c1c1610000051000314180d035840311341200c9542c040822902c0c0c848800301c0c1500c0851240200240c01c148010001c518a80e1229170400d100802d00300480000410050401104590100103d100440c1c0340c000705805111500840e040c5041031400040300794006185c00d10b03d8000a407003810b408180208042c02009042c5103a21050700345500c1360014501240740817040790380c0180c90300400d0742c0021440a0903000900c1c2200701d440b40c40320b41940c455044010803000f09828100884242c0000f106c000500d000b81c007406000d800965581d040c8800601690115807242c42000402d020040c0481d92021403001034800f203c0c2e411b581e5040d807143c552 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 812105359 1250 812104109 812104129
    0xc080705030601050421061b0c021e090a24030302250506070c03051605011d06090d06060f051c0305030604020702040f02031e090a0303020c19030f02190309050f 71
    0x618a16640b640c1074118034158414099000d00c42c940030b0141401103110900c8c0400450081d0700400c000300340d0305005140c030f40a220010116120040a900014000501000401e640e100610355464502c1850008000030600c80203030080d8948441c58555a402951081e2004070250002f05010ba4210601d003445200d00c02043d000b00440d4880005040c100c0481c0014801107030383d4400e400140702501d4114030004100d5205841c2c2c450325120b00f108010040d02d2804040341d112104001008459a480c0840720403a802240d0008440d41001944d002800d45908170500c02e600c52528405000b80c42c1900c08c0600790301d4078001d0388076100d00d40481c002e8090b020b0001d502a003007100c00c0b081d2a081d0b5014600c500d071100e400c05192114800c2d80c01d103020068a1588260300454804000720303000c2d400034003a03d80c101c401c81d6407610040c000c2219004040800b20001034074180c011000f01d904224440c0c0d41500b00021030003e001d01e0703902400705103041c85171038020288404802011755558141e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 812106609 1250 812105359 812105369
    0x1b0503090109080301091e20070609240e0c010e0d0303150b25080901050c0703050613060b0a0302013609050712020a02030405040c0509030604060c020f070509060d02281401030c0807050306010504 86
    0x1080c000cc184041949696041c00c2a410300b14580b1010080d445c0000a001d4103091040e111b440d4208961020302c0380e0f00100343c00a13428561101c40c024128405065500001e142c00900c1d2034952520741510580e08080008000c903a0318075080c80b4010507101000c480c495442428501d6035402c460055509244c00e075030001e0040e009400800070040c2d014055441d4940c45022704000d090001001c02c000401680030190000b900c0c040002c03801004c14510a4010248c0403250702c81d1962112401c1c280703d0207400210329162200140003280d500290000041260003a064bc14802010402035490045201e002e01c21034882d01c403601c6543c010740440c0c1425a000c0c096541500d41828602c025102d01440c0340014443c15042c1c41c2c20f00343c040385060a4540003000006161582c07000c00c0201354030741e0000d9174455105100300d00d01036601300076601500c179440c810700001440c02c000e5585034000c2d46420f41c141801c201d005545190700042059200020b402d1940d101c1d290030300101c541e40a0340d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 812107859 1250 812106609 812106623
    0x305070315230604020d0204050a03060207120f08151215071b0503030c0a05090a1d0112320703050105090706031b0503090109080301091e20070609 65
    0x1012080c4420075007181c800501464081c0038444448000340c0450011545202911114001260311031516400400300c016000b040036082c152a40e00144603003c2c1c540c400c81b809503002945d14200448069a0344800e41c00c0d0800c0407850794400009071004c00014840950f17900040480c400300da03268103119a1031300b60b140c101c5207001c3c0380b000a04080003040d155440403440022820050181061100200d254020051410b42e160740303200c0c8403150045000c2c8810f0001c103200d03000300e0b505c0f1078440e80018980c0c01c0760100514005145c4c04d079a03502c183c000ca0000d14141d11504080307040e24003915403420b2105225440250203c00350404441050449d1595008a40c400070901405400c090302801c50700091f030703c03416521842507080392260819040c2403102c04150301e0b007aa0042000d5540084600000304d80a1415603800780283e000b43c00190b0b41540e00d40500541d62180b117400d11301c89003450801c10055802c421460b12901790b0285021005900160039001c20a50b60032540b05c090388080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 812109109 1250 812107859 812107873
    0x1101050412030509090105060f120a060308070b0411030a031d040f23180a0201140f03070302031501020f28060c02010605011e17070302071205040f06140417070305 72
    0x1d0300030302c0c3d6400740c10100c3c0700d040340317000124107803401c2c1040798280d00c0101103071440c0c11030361602660703001c000601d5854240c0d0fa902000001c145c80c032006000084c0f25581c01009842c15240c01007425803040c80707441c0290700940300000003a0304035189006840341401c4150620001c00c00103400303001100800b0a18600b03040c0140030316440d000189524000c1404800341650340c10000381c103241b079446640790581e40000045400340d4050b007040c1c0d42c010850302100d071400c070002d8000101640309441c0080060760000c204211a40810110240c02a007403014124104405007500d642d41900712414020b00c5142e8203000c030221400c41d50304491a03000d00c0a02c040600d501c0068000e207030170312425000c14500d4541c101d0410301c40404056204440d2540074038400341030007204004c0c130000c201000303250342000184080366000100586c46800780d900c059031181001040c56146095131b000704107002110f00324012011002c004e4800365554452660203000081402c20320b03240180e8000761041c01201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 812110359 1250 812109109 812109113
    0xb030d020c0102070503150a02030612030a0905010306150215130609120807050c0d050a05120906040215040b03010b0a1713111c0f330609181101050412 67
    0x41529078081c24240c00741d07003403143d82d2001e045c3c030384151a02d02c605030141c2e040060b4844100341c1c065a006000136100c81402080030301030524641c845556800440c0425500f08420341e0305009041c060090080800300a1903c007030003960314002042007444c0c80c0c50110000d460382e41d20780411018140c0041d02446501a0390502c1001000e45c41400b030b0010f1a1000040c45150003002210f403c668100000c00c0c3d09280b50004071a10b4014001c480c0801200300302014820503445030241c040d03404032025000ba410035104000c1200700801d80c2450340c240c01e120410022110b4001d0742e04607802041d010f0f540300d140400441c0c00d4410100c115003116010024080280325204160084174880c04080d45502c902c1c100300a0844060382107600380006a10080d400200e4048080400d1072290284c902840b2094000c003110350703110b048482000c441c000b03802500e14014010b940c020100b0680401005107000384071183ca48042902822a404200305040180d22580483d802800c002c0c0d00d03515040914 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 812111609 1250 812110359 812110363
    0x5090c03150f0105090115051c0912030f0b01050703030e19030f091d0604021e03011719030c031107090f020405030c0114180f0405010e0f010e0601080105130b030d02 73
    0xa4a200300c0c048040380001c221800e0000b0241c1c140c611810110380312035079040c01241c15034868018032508038840003090b0000140b41c060ac0c1007051080341d8800798031601043c0281264140040c9412030313424011441c6003a60440d0803241c403182c00d86000b003286030b40c0c144800e14000c00c00200d014001d0100241606140c0e014035480034041c400d40d51136141940d03a14016000740d03c14a41442034280c0140800e050b480c03d039008246400040c4224117500c00e00915011158009030f00032004402850100c410415090001d04107143c548206c4072132042c0d040d20001c024048008008090001c160521380c0d070180200300c103c004010300b64081c00b01c0c82502c0142030285d001031003258002c2c400c0d03000040980d809610302d03400d1450b255144505081401e20f00c5c5c90312504040d046600302080a4201e6801c2d101d50080d90301800c542031102500d03092007240103010580592014504204039018480d06030781c003e441c41e044038000c03103600c090304501c0070303098000382070a183c515814455511041070076900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 812112859 1250 812111609 812111611
    0x1201061e03050f0f030a081306090312150806010303030b030f2a221d0109060209090c2104140d020a021e0306160e15030a0609020403020f0405090c0315 67
    0xca6010f840401120300740e0942c0d074040c9000305003116003080c0314004a041c401e0b0030141d80320b80e0440d04403000401c55120b4508884005000790b000410176150301c26207000a00800b04904541c1a05840da2498040d00359214101030200608141d110b40c14424280e408204072594845400151a2040780030110902c1c0840140007007075903030b10121b040000d50b2805a2250a100c182c2c481560305403150510620000d00c2e00c40a00c2940080c820f12a49082e0000d11401c1c14181c841e020040e035503042d450030003040b024003c01002c4a00c504104280740d00c0c50082a0014000d0601400d00250319545000070300d100300200004960710032144414100b03a80041c80c8203846000380c504042d0814050406100c212800ba000354047c0d005d42c011900c911420620108000c0b11071070901d1032001c07103a0028905800c90f68113035100300e2010040c0601c0700d24501c16100105112a02180390034a141d01007072101d047e402d904c40c801e50f030340d20025411180500c4084401d120060075180d503d0a1020300d403142d072030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 812114109 1250 812112859 812112863
    0xa1703090429010818100b0a05030a021507170f1b0106150809010207170703020d03050f040201051303080d0903031b0e06130f0b070b060415051201061e03 68
    0x204100381000300b1010101200b400101c084001264a042d080c0195916080940440c0d0000e200300685002040c09220f80e41210b6107141003c29910082d80c10000102c038250000e6200c1c0c4c2020b00c030080181c0c3d2b503084001c264040300100a4450076141880e019400c4207a03c01429140d000810a10035142040286400107200102e00c1800600b51801e5080310007902400008003440081c0c3c507040d90048805661044803d4000f500d810b1490361032141d00c0003480000c0e9140103020a01508060701072007088088111490200480e02c3d2107160080400c00140010b030600000007500c44800700081503020145820001c1160346145400c00350004141807402a000249425088a6094030204d2400b00361829030ba1014181401e020400409a0040041e9a16580240c0e400190032019002c01d00041c150020920380300c0c421801c00c1c55546000621040c412403410f200c14040088645080082d41c41c203075900c0c6400c1d5480c0a10900400580e00410101e100c0c0700c41825000c44a1540d460940b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 812115359 1250 812114109 812114111
    0x70e0406152606010c02040209030109060e07170309210a11041503050a06150e04051c0e0102060109020f1e1801090605070b100314010603170703021b0a17030904 71
    0x1d5203406200351010b0641c400070380071003003040411200d43c490f51070174440a00081c00145409aa940043d00b121311280045a071207440300c001854184003406504010030000140b503c90b03018548140b41c41e031080d55545403180c1200700144450341d18180901002449680403910f2084003800d080e00503181009000d441a030402440700b11201c1118001e4040f20b5000000b41003860255483c0d6014000a8038418040c10403444001a5518070408103801a40144090800e2040b004244d000c1c56a5203540718050154101c905203040e40d00103806411103402c02c100684658214020881038030588604801a100b1860005c502c0000c0000901180c8038a81048481c40c0c0e40300015905e0320030600c100c0b00800c1c410700c0307442c0100d041d05009a034010359001c141e801c0c164907980ca0907241ca803120100b451507036450720103008110070345e4000311945a120940905111540d54000d41c3d45458078862001205c0e41c3c1e0074038405444004001001d0049042441e03144083c507000d9540d60340041246074419 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 812116609 1250 812115359 812115377
    0x4030c1a1e180304050f04020c0604060b040b0402040e040b0601090b2808060a060e041d15010602120417030f0a1101060e011a1c020d150509010509040b070e040615 72
    0x650b500a484107040b01d2204091418640341c5003c00500c80c82004440703421076000c0102c9040c0e03880500849120718071603100091030004800501c404c40c0c62044034140198030402c42032009021080300b1551055100e03100e41065900c000040702c511032280e20001103004045041c00341c440601c0700c54010346905500800d007403e207042c01204d00800950781550888000d15040c80074600c01c0010203d8010050004241c0c44600c030210088a19050740e4004560080311204000c480001038a5004010b039100a000c4c1219012141c1128403940c42858200c0740307107084030154620144150340c4504907010185032104800c00025000580070320a042d4a9460306101240034800b021501d0b040e0742c01d11100380c0d1611400145010070798071004042c00382401c0308c030741a910340042c0d00082036420303445800401c0a01705217684800d100015040707580304030070040042c0040d8840c00d004960090b0004101181d40d01c84030829915401c2c04840d070b940260800e4404101d032a0b90400d5104040003030303a03400001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 812117859 1250 812116609 812116621
    0xf120c060313111f0507030302070b011815080c01050d0f0c020604050f010614060f0706050106050903070501020304030b06060307091d1801020a0e0f180a06030308060904080304030c1a1e 82
    0x405a0001d500c00940c1c0c01c01c1c0301300684501c014000d8544607080051400e0705588481c48031140983c82502000c0e203618451031001118001c0030002c044e042010350740d003820440607036144d03003d81645504100e00411802c00301940741d0401c41c40302500100030082c40100300b034001d4894404032000d0341c013840380c281500c0030760034140304000072144040d91042c280f200c900c0030410300c3d90048480000701c400034002e00010540030f21a046c000d01746501c80c26900c8002c8400e1504004d0550300450645d041884200042a07058040b180e106504403401a541c1e9159481070302c0c001c0c0700c2c1d0042c60401c10910304000f9030382c0703000a80600945c2121034800c000e40319880f8032400c0c1e12487c5103940000300b2440f610001801c20504038241200024201e12148a05132004400250b0440e110819240ca9207010400d00da0007045241d0800c2054902481d076180c00e0f110940c2520002d8001006c00c5020203c40090109005c0d021441c0055030440755403504040c207407408221a040801e888152680c808214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 812119109 1250 812117859 812117869
    0x9050a1115030c0d05090607020705090415050a05180c0109090908160503030907092307020319021c02010204030b010308130504020307170610091406070804080307030206150f120c06031311 83
    0x11040230181c1c01402003509110601244400140007141d0101a00802c40200400d03400b030b03184070f5007060340c0000b4149012100f1f4814080e00300c90047d4250010003400382180d0f0b01002607801e403484a50046022280340ca41401144900c0588070118420342400e00c1c20024044001c40c00b4844503c1101d03481d641702d108102c01c80b10244440c0c0440c2130310b183d00c4400092100101c40c1c2c020b4290046d030781002600605010220002d81c2c540d40140c02060a50b404e42800000510100805100860909003143d40b40c07030b10500c06000c05050380320046620204101c50704d50300030107000085d0041d5101d0400d031102410160b2003d418003102e0010400044840c01c007850340780000c2c0ca46a46500d0b84038900031280344040134070803905420080800801c00803620301c1000748000c00d030f64401180e980c0f1090500909189018140524108070300703196100c240e4465066518142e400c9a159190b00241510345281c12030380008070382c1064011007001001d20b411a2010f40060091880d50f00802003c41008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 812120359 1250 812119109 812119111
    0x3051024050d0302010b1203070317090a230a08040e0604090512160c032303090117070e210d0c02090a0b0310060b0a1209050a1115030c0d050906 64
    0xe0280c021030030030801d0703180c000c1280d000c0c03900900000420441e007102151003900000007036000d50744001402c43c10164400031044200028815410761410600c00c1e00b6140c003852a805040500101443c403101440340c2d445602150040d41226500c000514040000f40c2103807241d10708010951000a00c5810315005107c16594840064450b40b00c1b8401c0a000d50780002c1c24003200c00c0501d00303400000800f80361155007d107000340098090141c0e006441004213203889414082c81c0c000b03001d44c151a0360003e100d00c10510740651f02c40402e60300c6d1401211403075141d284480d03121814404000d000c0c100142c0c040b4030001a90145d82000c0a8000300b5141c8500a0b04001d4012140d0350024807211600e601810400e4030080944607020031000c0e071041590615041050b100c03000107400b5a1351600080001710008240c01c050012060684601c0d80350303040104058841c610403200c00748199a8400643c0e0f18203030400019803281040004900e076a00200da142030341a00e800046021100001509 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 812121609 1250 812120359 812120411
    0x90312010e040210230c16080c0307060f0806061c0f0b090106020a030503010b07110618040b090c07060506010302040f03030206150a030506010b0711040c021c08190b0f0a030510 78
    0x4817600214402c01c180c07540d01c81d10400001d405110300c0c0031514111641018000d0040d00002c00e0720341e062504050801c030312a40030006100b40c40301e8001c0703000c4d080b0301800d9200300120b580b2900c602d0011084c2c45148100d4070300500c0240382030305400720040350364041c0c03111030415a80900f5a0fa21007405076902d4000c000c000c0d010450038001002241001c4000b45500d41c840e2908005001d4142c6c0498a190003090220b0383e00c4508102d00415407c0030300c1101200b44003111600100d003800070500d6428811f05001520043d10303540041d02c964040c4d01114002e0410202c1b5104240e42da0078000d4840c04240e501d026402042c0c60368048501c0d01c003606c081620741210191095920303101d054000c5510104044400c00c00040b2411050398035842600250140794024000c8038458510184640000c0090203040c0039002c020311860007600c0404601903403982d03500145203104040040d1080321b260403040e91190070581d012081203000301d41000c01c200c0b2000188107204e404422421403440303403580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 812122859 1250 812121609 812121647
    0x30605181011040311030c030303010b04090e031c020903161706010509100e090c060f04050f01020a0309060c0521090306150607391509080d08090312010e040210 71
    0x52000c01c4403245045852017004040314840c5004101090564009900144070110003140400140c655401580c0f00c09072140003540c504203101442c414001040f01c42c0c424415030106070f01101d91410010101113425a0340c010081c42c3da00c180081000c0003070001c80c110342c040c0000020f82400c00321a1a4043c924500f8403803015400c08100c2c40c2c103680d000f8914155441040c1d2840c101e900c41a0003803c2c2d400d91070003101c2c0d51354101018030000d208003480d801d04551011207004042a40300d582d500070340e02c152a01148005050030202d103040c409001c402c150302d4800706424860300b20130f00100512501641035405941d1400c2d90f8903400303d5601c0c411600800d040100e080000e1448074015992a0b4283e400a0128480683c0d0718201082d0740e8012840b20241e84148013010100b5a41c08030f0003560301e41a4001030401e195980c850a01a601c0d03c02d0295180200c0c000500a0013621a00c03101124038044030340e5160105446240140c6082c2d0285004035809240688030b0444189484c001d00300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 812124109 1250 812122859 812122867
    0x2120f300a050f031003060b061c0246170a1805030706060303081821090d05010b0a1a19050f040e04150c02060a0504060204030605181011 61
    0xc140c5859500c01c510304010072004105622041c019074004d94055152520030784609400d5103441c004866a06c18114428041405040700d0310841c00e14922440da0880700140e1112450004418180c8c419100c0c920794075003107400c00025000e0b2001d0720507030703038845810320407501d920074030640e0919460200c220350319511000150510030b0a40050300605a00102c0104246230f90700c880c0e0a607001520f04461094403400100240350340304203880c3e0482640c1c0d141464031a4640c80301075030b48481412100c5295116240407020760a814207940801c900602102c10003c1035251290080070b40c220891b02c0f68a40b4503011032003c140444a1780c5039141d40519505d00f95402c600001c012030001805030030040100712140d040f61102015000400f401c14008586040520707003080c008200d129180002c910741703407000d0903080c1c3c00900550001c0c0c05550025840d200c50410703001a20480d000544020700740000e00841e00001034142c402004604252854041085214020384805403248140404c040c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 812125359 1250 812124109 812124193
    0x9060406121101020a0c030302010e0607110c0f0411130305060a0203130b060a0906080705010206220b070c050d170708460c120b010818010902120f 65
    0x200c4a580b42c008140100c800c400394070754800a11042540003180141d44800d084518003034108502c64014400d414281035500800d00090340c0c408401651030300c03c9a008400c188682c0303896101040e44102c5a14165860000d40b84550003a41180710807507a921842000603590b00c1144241c0740110300300601c8640f50000c035240c070740b03184401074103030f40c1d0103d2140360000c1c110b001845144001d00b103140250061907e00310000e82403d100400300c05440e400f822488400e414280da12114140d80003007414a035843d08682207540469401d0006d01d00c2c81020342e03107481c09800c40003078900c1d4520340000d85407a03620500c084818100507540d00c0c04440d01e050440184207074140350111402006c141e80110190034030740b003a00e07040b000d00708000b40e0707070f0b0710ba81c054212030f402441001c65159016007400002003007000207001c294000e10080c0c4203002003001b4a5500001c0d0810941550001c04003030b00fa540141443d6140c2d460b0384240c0b1568400c514084524240e030340540e00e40b030b04c20303100340c140303804090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 812126609 1250 812125359 812125373
    0x209060d020423070201110405150f0f1201050a0b070209010b0c010b130605090606040f140f031f0b1903020603090703020d0f030311030c090415230906040612 70
    0x80d50100d07030094840080b098620400940b080c00343d038249140001c00e09103550068216142c048804d51554810481440b01e81c4800c4101100c0c01d50b514502a0348104a00c20815540140135061803a000700285119000d2020380005040e204112402d600c03150703642113440038034841c0f018025004200e040040200c12040740184c104040348400200d1003098050008541030280040090b05907030b2240c05001c81d007800e2907102c1d8010810b680291078107045c440c4101c108584c61080d043c081e43c003010702c070312662a98500300042500c05400c4031140080f410304100294a005a80304003549400204000d030b00d40160340c0309009098800b0703005075604580038081107038801401003601e880340010000041e250360901c916410b002d048082d02203920f51400809980c1103445111540c5070510500590030304d01021a030720386108690015069624442940d05925240d0002030348141584c1181840b15444c1c000e082c082d0001c44c4e41400341c0d5a680100320071507101d400b17200802008584007000180c21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 812127859 1250 812126609 812126629
    0x91501031a10050a0b030a05071b0f020d0c03080d0f02040b041e030b131506050f0f1210020d0f050408041e03050703060b131103070f0e0d0f0309060c020906 69
    0x200a05010556114400b0444685442d8008101c441c2c0c004100312002e00c26200d402e1304270116240459240ca1001c20203203400420f0f00c000303400c60600c20000d0003103580f564200829554400c0b00300303411998030b0921814580041640d01e0320725040141590300d9004503c2100d0650301500161401c1c1130a111044021451001d003540d600e0b4001800030002c58003108905208070451b14600c2005c16640c503009110600d80c9114030812810140103101d00da94000e20006884001d4602d40d4030080580000b030704204001951104c40d00441040ca0166141038004240c290038041c0c06102610b0348410100459800312806080c01d80144007e1026018007510000d03c00c104100a0318515100d80300c842c10030031142c4c41101e0b01c41c1e1310f2959480604104500d622082c440400801104011b40d1500e202c030300c8010304600030815003d8448141ca23001c1da110416142010708600c280b891700c2c2c0b409a00c00800301364140c1c040f500040c1c0016056100309806001a5401340c002d036116140c3ca401d00c20070a034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 812129109 1250 812127859 812127871
    0x50a020c03121c091b0302101806120914012f09010305101701050417030702060714041e1d01140f010309020301020307080f070e1e1801030803091501031a 68
    0x24640811801040b42c1045426940d948900b580d1002461b620400c0071003110f0490342d800740000f500d0195800c40080d285002216480c2c00d012403040c0942000394003c00c059180200700808041c0c40c005892015440141e00502d00c1c00351030070035076985034140c0310942e04035608401e2680c2000b0458465101e60011030300030301d4405050b42c0443e15410301c60100d46016101002c1a0340d15000c0000348013155001300b4880302502c01c3c061450802980080d00c940e002080350082c081d0b0009210000c0b01c02d101102c00070050305881d641d0800d82590b50000c0f45186110312202501c41d0040c46546011501c2c3c44d5040310101203454083c500710405000c18515030030f20781810f05030388031300680143c0c80a0001318413070410350362080054a0114000e440558000e0144810020303089140203e54a6101c8a80c2494515140c604600308041e00003c4003594681c5490b41007044900000040213072950146010f541640142c0ba0500640b0b08100b50040c0244000740c100104a5503040000794680442c5d1781082c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 812130359 1250 812129109 812129111
    0xa06051e0a0e19030206070f050906090f0f03070306060311010206101a0d24060e012001110412411c05090108060a03082b0c050a020c03121c 62
    0x350200d00c20f2412404400416000b41c1c00070000c001c0082d510031354280103000c07031303091580c10728200d40042081030242c00d400c68058284032104030181e03541c11401d0102410300404507070390301c0d88a1410001030990751008880b402c1d009201d03c0350030340c00840c1e003610070031203600c116000c02c0c41d0510613130034418a59080814a081002503401a034601c0c041d4040d2444500d011110984010340b44054610069000c03c00b0000d0301050f075001c1d40e07442221845100c404007031100c8500da40250031401821441c1c08420031010008002803151199605010841e00990540c5c04442c03034041c1a00140e1504030701d08010f00f40d042180010009110b0344181c07104100c41c200c0344001c100712140c000400203101d064000c21408174984040f5a4032400f42684144180c0b03030703803580604d0756640706820700401e60292030000d440c90310108500060107a125901c0004c180510151000b0381c070180081c0e00600aa400600401c41f84040c01c1c00d00284442019886102c0c4600c4c084800ca4800c4118041500c0500c0c0340d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 812131609 1250 812130359 812130373
    0x8031801020a030b03160b0d110c0601120312050601050313140a32030414011205070c0c150c03030e12031608010f0f060311090d050a06051e0a0e 64
    0x908800d00c05820601c60940f00051200340501c00c042c58406031a420400c0b40000841c140010010b000586203ca41c0c14400400d45064003603002c1c00c68090460307004c079184164800001c84080304409200c00c80c0c001c0c4c590004a040c1d0650280a4880031906d1902290003000400c0c00035000b6000718459a0088000b02c42d90398041c0329081c10400c035124260b601640103030034401c1d14880642035003030118074240f204420303815240c4599124080c1d442155000b010408402003070b41d0143c0d02d50384221411a40c10020f03460803100c040d00301c400c10403040c0c50240c100341e000311701d01140c2001491154401c1e04c07080c40e402c205560440c082c1c940142e100c4c1003405000c1e00466032440000103140500d4500011100d0454429402407440005900044040c3c0180d0f0040245450348400402519600d00c0c0c003140c03803400b0400740b03406403003140205600028030a0110040c000301143c012210352107098140119200c0c08841441e0502d0900304120f21205000410011071030396101d07903c0b204115060f1303245 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 812132859 1250 812131609 812131651
    0x403050a230a03030506040b010504050d0809030102040e0906010306060f0302030c0906031c051b0c09010603020a030b130e0106050f011704060f09140105010834150f03050a06120803 80
    0x60030720b1403204a0100381c0f258244031161038140138112210340d00b0300c0c6c00c90a007032074180011401070b10f281010b40080d0b0009502c0840342c400f0740465002e01650454652581000800c1c659245400d10060700c1440ca0050701203800c60111b05040101c84c0c006005005c003120f81820010f0f17011003d800c0940c5032080751100c8440050b100c031401d40307000e60bd8aa468480640c2c006001c064000c01210360700603001640000c406da5a015440d90540b00c0360302c2c0040c0c84d0840010140c00038030780500902e07800301455001c1070b5103003250340083c81041d014074004d104042d81e4030207025903040742d50103241c046400390740c0350340c1d14543d101c0030321b507019000f030202044008040840c0d008443d140310007507402c43c815407410340d00e18000340621401082200300074184603692020901c25075000560240d40d4286d004001d001901714a0482e03070240801c5080000d40180701d11024140c1d070f2055a004000c03d0405002a544114600c90501124000340484040311541d40c3e07032070380540c4000c0610010307041200ba2402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 812134109 1250 812132859 812132863
    0x120604090210020304051f1704050307051c030c020c010929131d0c0d020d1409030307030b1e2b060203060a0b070f1b030203100f0e030403050a23 64
    0x10070000b00e40c010b15603c0c0d041c1000d21070315003c0c0850001c000c10403034a07201c3c03810f6841001070100b1141c000300c0400301d840d03a01d0701d14254483c002c1c0c044c1c02c0b0307c104c1e100048054441e48aa1142868a450400000c03041810998943c41da00109a0208148000c10800201071600300521680c40969803414000d01f014404202d0f002846010074174405440103007c105020341500140c1c01c0c0c42c81d0085505e00c0d16045c041124450003540005058021640061001064101e01d1031003903800182440c5141207101030355203400031240000002e0400060b1400343c1407d80311010070340702272103400040010f00c0c01403042c212036805020180c82654400d0b0384000700841c14410030984141d10241e502d0504c40c04001164180740c00c20341c80e11908001940000740c1802594442d0b66100c0c4140721070050140340240369001c03035403010b0f40602801c1c866140b101041c5e8400c1544500700368040101001d440741880d924003403404000d0107581311032040408201001d80c042064003681010240c1034402d032808134 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 812135359 1250 812134109 812134129
    0x1305010501081b0604270f020d051603090c1e0b03090a0203060a1e0506010207050607050a02041805030406050f070212100506040b0a051e0d031806141206040902 71
    0x25107580c202100d180b078800c844100f0981c07964400c0340d4050809040803460040074010f080804001851407a070407102021a80012480201401c8115101c2c0c800b00944006070a080700d5400940540007070708907003103009100d181f2540c0d401c4410088109e00300548444040d4426000c800343d614520300005d0b84004140007903206159003030182c14103040501c141864440050080607040303081c60740750507084540346230044030b50760264008a034544880d001030b0b01b08512070300603a030807060000d544014048000340e00c1070703a0b80c402e4400b00414004011154044421490300034541d80042108000703440c8190003801e111841020000d00c0c0000c01d40c0012555103d1030a15030342c0d41c2000d00b0003081c00b40e03a072040303940c0004180c90500800782c00380c000407504a0907025a81c8994607010580840800c40a0b56520f02c41002c0c04440346036201c1e080c060300886290340007050386030041c078000c24000d200c1d42ea41e003001040e8801160400c00c103a640c6070b1901d54014045078010745e071101e2071800f594940f1891 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 812136609 1250 812135359 812135369
    0x20c0a0c030c090c0801140f0a05030d0302090f030c060703050729040618030e1201060b12190b0105190e10030f0b06090a0e070c0f03051c0e12031305010501 69
    0x2002062900c0f0410098a14045854042c8401d820040003003949408030468102c40441c1c070b0700003002510000500364011a04090781500c10040b03c048078940642c010003240c1c1c4126020740b01c152480c410199550040c51220303802c1300007031000d003001038050005841e51500c10400545240003800703412803100301000800021403052400c0c001444011b12a01803181e64001440b1100d40468070050480305c403192103107001d03c1c040e4000c9050000203600080c0a80315800101d40e031034a10a0064418074401d179141010b10304680c0c4e07000840003580c4500340c0d10000c1a102c660600c50954003001c6c00b0741103035034000284500c1c03004003081981d402c14801a0501c1c2520000750003419821315001312039060000341d0051004208403880c9031340d448141c200719205607064013500c0e0b4400c00200d0716030080c007000401048400013041c0030190000d01629603907036144240f4104c03480c14201d48090340c2d040030750784800742c1144203004081000314004640c840320417000c05243c1c5403107907102d40c210f0f5400d03802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 812137859 1250 812136609 812136623
    0xd050f010b010306060804020907050c0c190618271d0703030e10021002131512050c0f070210180e0105090f091005091203040f150501120303020c0a0c03 67
    0x1032501c0543e094801c040150400e803600518903d050740c080b9010071000703028203080c03210200303241012090820901c00003c2c0c01405078a070034214400c00e2088a00c65016004c040f840c2240040859222814281c080351540300c000070070f81010900000d03010396000380080c0400d0b140d03859000340a2072410103605d401c03110002080072501d1424000e0804810329007040c400d46d01d480b85444c003103500148820410f00d0074500107039500b03102203140300a0300c1264810103012030a0300402d00a1038100c031451345039040c200d00038005a940c180d0343c03441c1407044801d4208a1001804010054140303403921030320031280c80c203124101d5040c00c1e0383d060807107180742d0040b22568550300040c0700c0c60a0a941007904441d00401d0802d5074284020b00544540704150580020360307503000003800c014001c115042c0c05451003900280c0c3ca083c41c0c00c0c1a850b5000b10441138a001680f80072021131043c20780303c0c40b0304032410007141c42c5004046030350890180d441854001624400d021110001c5166448540010b6104020b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 812139109 1250 812137859 812137871
    0x7030503090f0c03030f21070203210103020612060406050603010f0603060b0a09170a060c0e040506031c12020d06141002010507091403030c061821040909020d050f01 73
    0x1448500e0315000780000c00060308003c00000540c0c030000280c0f6500014050380903203c141c080c0030441c4d0710790980d01101004021109110320b030340d000702c01401840300006982000c01c6000100510906081c40029001345040101c0b0f000184a00c0c032154000c4001400441d445540e1030000d12190020303000b40499920b145802c1100310b4040c440c000003415690051420410b00102c0a000e4800a104903031810314220a9050300000500003414503a912040c208002c10f0804002890307101c0c042d52140c0624640b90101b0f1140c6800242c0f840407142c141403120602001c188102e40416020b8bc069410540138402c403543c1c0300c42800f070300010b00419101c413007904820b0010030064445512421055915060600041a6000400c5801c0d0343c04200104421402280420b00d54400c07003c90f00400d0103002e00744440d1440e003009060b000b5400b003049030303500074907a400c156041c4252920220841c1e0200000c10251440c1e4008101103400108000c103e0310340c640715036042c82680710032106140d40d100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 812140359 1250 812139109 812139121
    0x70e04061e0c090f0b0f03090a12080a050601170408090a0929010c05030d05040f0204230907180e030c060709230d030c080c010e0309040516050423040207030503 71
    0x203400300040c01d009000d44101841c1c503801d0700701741c45504481030340418008002a035096040000e13802e02584543c13492500102003a00901c1d060043c1c40045d1814140000b1544c4d562242030401d01100d42c40600a8071600c0700e41d43d000c420307130084004c0b680041e0b4491000074403103e01d00c140d80c4a00c202d003000440007600c1d0f0318200050994455a0380c103100d0003180050108400006860f40416040c40c005096103403800c14010b1118030b500004e600c9800c000a514001e046156030031040350300c0d1103d00c42c0c6a26411300b901d40707034140c03401245141031810302e9607d004106074000400820f00401942d140050070061030f070030b107401110f070240480d132802d00801542400c01803414800e83c4081c502c41d540101c100028000130b0000c2c201504014140004a06210701700080321000600e0000030008126620f100c9c980740e402c55220b5074415864440011019082001c6c0403600c0005643d2341c918150038500d00d042c076412005809a584425129550002d484a20050440750300a444250300da15140c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 812141609 1250 812140359 812140367
    0x1f0803120f09010203010b07030c331d0c0919060b0c0705031c0f03140910050a1b0807140d090210140f0724090b0106020d02070e04061e0c 61
    0x142c00340005a2040004004800ca900c0c1610705003689450180128195410226004111807400012041c2d20301c410b4100c1516100d81d400e240c0302c0c800014448500110391245c02e0014030740040d0032542003070290800915142201c503034081010901540e1111000c0548001c49174190000b095207070002801c0e0b81803410401031040107040440061031040f049141140705110085200005d1085041007064654083d801006440581030040c456520344240c1840d540c11041c107405440d5483c000100c1d9821180e4084c4103240c2c0ba10035244e0080060100007203816a83c004e100e0010400e040301065402820380005001241c1a0400030404020030b004108c40410008501d0b01400282516221031400820a9940105070f180046842c2c0049050101c1c1e030605082c10754203004031040a01ca0201290b9118850740741c0604440c1721160f1701c68200781d035111031441e1190301603441103204000c08081c2d90b500c40d500c280719410204440640656000e80d0f82d1601d0081840d06480b05540d608050340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 812142859 1250 812141609 812141611
    0x9170304030201061e03020303120a0222051014040e1f061806050a140a050904091b0803030708010513020904180506070318060b010224010f140105031f0803120f 71
    0xa1580860340c1c0e031b86540e000075900c0c811500302c00e8450000c54001000d0114a0303055600841c0c106061820190000d101d520300d4201d80d0040d90b200720000d10418031454821201d0440010160002514050a24600d48000d02004001c040917844564010107107289211184006000c6511511481c0003200e01402c41040c8640081e020803400740100c030140f0340e01105071a21801c00310a995a100300340c3d1003c070751501c81c48000c0758015082980c64400c00c01d40310380b130401102c42e01101510700350b101c180c000e03140d20040d111440001c414400600c010314085860307034641202640010328217000c20006c1801c3d00d41180c1000900e1746103403019014440203024050f0b10000c0d503d000c100c1e41e407140d118020008901030010f860381c7c0c3c1e034640b20780081e4020400d05030105180c008031008214613144402c00208240920351004288220000e11400c00705410300401905848030343c15a2b4410070304110f24240301c2a29070161003011000500d91100b80001c124803061100c3c28039039858540d4500c002004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 812144109 1250 812142859 812142899
    0x20a2103030605180f181b0301060b041802030601090302210606060313082212031d090106080405120307020127081902010e0105010b0a12050403120917030403020106 73
    0x2038074030f224200d4500651340c552000340f0000c122103a845606440020512011050500b445005807104541c030102000a41e5018224003c0c0f10454940c820104513004905c500e813203141d014400c6000d6000990003450340564185084844a0790320340000702d0b4107944403400300070a4152009501c06040512403580c0c0a4419203695240d4144502c000102030f5480f1006041c0e00d9002c164140006d14a800800380b0107000c4d01000c0e00d5645601098042c0c40e510fa80440c08182215410012502694656028054000c00c0301c40241c4c80c2c200161100100180304075182d029483c001440049a04d0165009030601c1d0f0001039500c0701000c03400026412a51094044c160720350106c0009107150301210801c0030558080f0448400600f01a0301502103071941e002c040d401c210011a2507036111b005401400001c0e40c80340c000c1450035400c14200d030b8060f04d0103000107000c900c0b10b4a44c16002d80081d075155110703132034565080c4030380d48055a858109950480050351124010400e00d00741010340802c0b00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 812145359 1250 812144109 812144119
    0x31204061b0b130302010b041b08070801060203030712020702040f050a06050405090706110f01053c04140a1a09061b0a0305100b0304140d090b040b07020a2103030605 73
    0x10680d459020b816400289564100285111803400f0140300390007569001901510502c0650480c04423480b01c45a90454100016818800500c00d40e22178440c150417500e10350051451511800e80845900641041103d00c4a0b001c000003001a1603d200d15403000c540001c0014090600764580405e445841d8440d51041e8141424402c00013004562501100c52504107811001ca01c12003031420a0028820001c05510b4a001c001e4140004030315581000c889c0700081c0c1075030000065002c65a8080182d48a6006415000a000403400e040c9110803040030012141403c0c81e0355600b035101078002c4900040c1c2104c82c81440401c050821000d40c200c003c8080500482d100d400401210380030301c50000742059161400f1510032641080f00d031000e06030180390b080d92841c0c21300301207041c46421030502e0640cbc401c1a41c1c07500428400d034800400d035180300f04003502d060b00d0310055440b607820210083e42d00c243e01250002d4851410b1040801c140000542c1440c0c0c00007605002d070440da601d91086001d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 812146609 1250 812145359 812145407
    0x180319020d030c090b070f0b010b09030606011b02240c0c13090b0c09040605120a0b100503070e15040207030906030f0b0105160c0305120403050724080a090203120406 73
    0x54001091344152007a404050391590002e041030f1400040d6040040c11030204000042440c160310300c01044124400d4048070800d4807000b00465031624000400d0904101f980c078002c005180040c1421085201c10112408002402a100001f94044400510380354403d20380613855003030200d1545103140c0c810710100030341f0490b5290340da40140018214501014005042025070740c9503031094001d403802508a0703030103800000e24a03503070340e554010607541c0000020001c5c43c600e1004c0003140030b1f02e101070003412040385404003503142c4034006028009580786034030343d403202d68445101902a25000366141c20f041031800d04058100d901242c0360031400c504240421505076046130444a03030030f92410300240c6180f49404e007111401915000101b06025507068850340400c10005003084d64020030540d8286540c9010500c1c900001100948280d082c0341c0c1c0c00c01da0b8030b000d0f080e55540400b60344404500c00d100c5038000380c1840041505c12000410225080c41031540c000d0f0591000c0110f21181005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 812147859 1250 812146609 812146631
    0xe06100609171c18030614060f030d0c02040b1009030201090b040b07030e01020309030d211a1002150109050708070804020307090b1c12022a09180319020d03 69
    0x1103440d070030044020f02c02c055504485a500c01c900d24610703281c0c0546184102500c82c903080d00500001c40154034840008404200103150040d04101c81c1e4000800400031002d80c0c1b1000d8502803855201070780d1060b41c880141000d071701d4820512081d400e081da5070b941002d0861001500b92002c40c0c100c81a808001e02c0140441c0320483d080769400c54041c04c003048441d04880040f459441040303909905400781108044401740c000305015004200b10300c0500c420320b11085000122550201e005822000b000c01454040c01d106254004204452040d1204400665600881000c080e401a2119030b6503004101742c07698031017481500706046250040030343c20140c000039641e0760389001f0f058070070399200d0781018141d031400076000c9040080c008004030034006050980610350440050f0f4054041e4000c02490910150525103450042d01d00a03451586107001f4480211001000004107001074200b107640c10308108045d0682e0f54042d90300220f48030240d02c0082c00c105046080b01c05050030940c220344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 812149109 1250 812147859 812147863
    0xb030906100e04020d020607080c101a03120912030c0a0b06010807120e1903020313140a1e0315020904060501051309330305060f06130506040e0610060917 68
    0x3d0001e80441d580e0b180700b400d0b4000100e036481031540040502d13200243c07040c1000740105402e1081c0d0f940d86810040d624200f0701c02040c418114020395810741158001d00182c0a621000e011801e0010f094170302c5043c0408001d038031390b0303000031103c1400d580690024000c02003c2032005900003400e282884160030102c0b4080e02d484050910240e01c0c90704c988001d080100c082260350609051b24201c1c480302c0d4032506019441b41d01c046807102300d01508010105405e00c1100180300c84500c00390011366001d00e810810610303407480c0304a03032141d402d107803070f000001c02e4a85244414980e4102c40060761800480d0402c0100d4001c0c0e0701c1030f81844000d000d507030900d10808a408048810065000c03e048032107070011400e04034400c0280440810000308052500f40d15400c00080c2e920490449070141c49a112840d2020b0088845542c0540d0111000080b8909600280d41003d0054000328100c10540042410510100c5081144a02010042045d0345e072044000c8002e088150440303404004243c6065 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 812150359 1250 812149109 812149111
    0x3041103190201120e1c020610050f011103070f060e060f0403080612120d061a130b0a2309030c12060114010903050d03020405121c0311040905010b030906100e 70
    0x40d041c080c000740c41840034080c4d80c000140200c03094080c2c0359848510880842200541c10001c00148941400200f06011028117041580e10060800406040c10001100c850104807444881c5010601c440000242141d8411841034407411000c00e08a8001c0309040c50b128004103009400064501804040f035004546c8580204003a110703102d1000c40d17101010300d48011240c070900b0f400b00000d0404294005988680f0039183c89030b10082480403421100300783da0003040a403030180c0c08802c0e001c0001c9100400106144801030604e01c92805011340c2441081c420550020316200000459211a00c1d00740b001d0032030790004403507609541080d02c134095690031050103240b00c42c3e03c40c540d0644c03190780102c6018008581c86000c50703010500740d5100030040d4010703101d4a80614134550140500300000300c0c0e0903004038402c10b42d55440304145c0c10101e0180001324100c481240c410000800e8440050180314040d20814044030ba0381c0c100021468075001c4028140f031041c0b000302c1c001f4802c08ac0206852 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 812151609 1250 812150359 812150363
    0x31b1a0a0c1104020903150a140c0a030510050402030411091317070314031014092a0d0212010810090c03140316060903121a060c0114010b0304110319 66
    0x101110072080000c14001e02c40c0000856152080f0064034054907c0c840a0902c106000c2005000e0b9100c683c0000d0001d031030659184802c240140400c06103140b00c0d0f48060f90080030b414865054543c1e070b4003c0340482c1c0c0184c909440d07050101161802d581440b0a1301c42c0c000170b15250140546086454041035108420740d00c00881c0340008910040c0341c440c904000040200030800e03980e030b0030024040b00c10b0014038441c00e450b10507440c401141914054403400c0c4a00044c50f0080310345415090030001c02030020141045500c81484441680e05691002e4120942e002c20301d001154144a0303d10b14042ca1013070081c0c0c81c10700740070070900000c924161041c102d84d40622001006507280080604601500c914600c8003442c17088100280031080c0c00042c0414040d0320350076400c060059844083e0b030b0b00b02c0307254505000c50900046890070040001c142c6440721800000302da07035808c00105035600081c0e10141c0d80c0103000c4244410b11000c0740e01041c005804400510103881c10398500580d4014080380 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 812152859 1250 812151609 812151623
    0xb0a0606050a30062301030504031709070e0a1d07121401060902030a1e0c05190207030215090316030203070b03070c05011e11090312030709031b1a0a0c 67
    0x10450311500000c42d5042d1141242da8240002d0b0b46950a09458601c0d0894515034112040f00c0340140354088d2081d103019036096541c0b0b001000c81d8110044850070040e00c0135601c2d103d9040005400d50403d0710040c02680d08170404980840ca0843c078400390225490010303c581c020500c10441080d0707a00140c454030354400f403402810b501d290500c600400c02d17540185074881c000420002c0d003008540c0003140300040c6000031203840078481c042c8406c0315503480124010820400c03103566009401030040080240d04d10480d40380c40d4590340400c400003420840401540d40226a1242d503190910203881d400e4510702118248030301c2c5400103503503581c0b10702c50381e03000f110300001040e8554400c0520b000c0e280c0e00b00c0300902880700c190f80300144411039090701c2c2c06042e103000b5102e10000c81c1542290201e204c014020100d60440c403901c4101c6500288c00c1d0000c1c411380c0c50000000525005070840c41e82c0164200d44461841c00c0344014003c8407620040e84498010010b0741001c507000b80724440407a4100c56 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 812154109 1250 812152859 812152907
    0x70b031f0f03030c230102070b090d0e1c1506030b070206040f06050703020c150a0515090109050703090212010b0102070f030816020114121e0c04030807031206030b0a0606050a 77
    0x205060b003411205c540d40400c0c2d9454050425009054004100041c8180b40460980da40c0110241d150400c0010110005000089140c81c1d440d10340d40060800398400d136243c44045465a5052000031a00c05004919840304401c01c280f0001c0c1524903801116400949202d00d481d5440c20303e20b44030300500500069550000c510043d04c29815101b200820004440303200c040c00c01007d1101204581d41001c0c2818500002e0b0002c605000512084c0d0020301444040d07420701c0800070151200500302c000705556184408050f0351080d211180000091000060000d8900002401c00c07483e81c00c2519456000c5004000080c030030340071661050601c900341c020102c8144012203d00184256041640801044100c401104200628000c5105124500c04100c4020002210034002c88030311200c0b803003e21081000c47c90a00003009100c4c070038a403810005c00c000320f0400896038280c0080c0c54241e0008108907281d00c8911814026081d1800c02c281418500300300101003c4801e040c400350703e10040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 812155359 1250 812154109 812154113
    0x30f0216140c1f1115090a06050121020d1106210108060601090501081005030d2706080106050a111203091917220806061306031a0c0c070b031f0f03030c 67
    0x20200c9480f000031711400d909079060028010355540d1040300c080d10384034603080000070918803c424803c0180c5054526503a03600403a02003080c540e9a0200c203171400100306100010340d076207000003000c449110346503600e4258050600242c40c041d058011840d01e601c05001c1c4200b581e08030a150381280d0003440c1030050740c2d4951200c1d1f90701091590013a901441100c03c03200016070000c0c040c0c0c0e11403540b6001120502e40080c80d141c00c1c603c441c8070703110110784001c0040c04441d1042c4018101c0e01150708101c20220380e81c1103000e1410804c1c00d5180c0d020103001c010711031224000d02010410a00d4007030300a0042600b0b03200c4c0b960944068080e10b000440c0022a2200400d42d902211240046e0040320070700b280c0d4800445895080482d1900d01c21030704180c0506800400e8031464050742c2d00300c480c2200075100e11182100c44100a0701c96031007044180070b101c0300204c0420408020701000e80c0d9454403420619003007a046082200000c40100e21404184660081c0c1561581202d40625040081040398 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 812156609 1250 812155359 812155363
    0x506042102090a0507030b0a181119050304020a062d02012306010e061206100504240306090212040f0212151b04120201030f0216140c1f11 61
    0xd044000e40049420b410802d24843c2c2e988500e04c03e1050352024029070380309408000c0d6054441c001c460301200f04141d40c900d2844640d01102128000c0d401062500c050300f400d44030300113180516a8002100001008118100502d070340e00242403030308015003c00801c0d8018414a0000e5000b1075000b83d404807640300344c074800d4000380c0e5040b050031510000b902000100b9100300b14104c80c400d0204aa00c107100055007000d4040300c000400c0c3d01c6000006031034400402c4250191042450100901400041100ca01606005003222004400840030000d0003001401b82d44c0298003a5500c0791052024941040d01015041d501ca41d202c191400c10045e544001140f04460341c1001c012441840041007404002c034003080c0c010713405440380000d5026002e0007000c15210f940162040c0c9000300340d003100154041d0b005601e01e1555880f016046c04020b00c02181240b07400c0c0d005880c10040c0120f8240d40582c00d201400e00250280c0d00310108014214203004c4004201000d40208002300000480174441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 812157859 1250 812156609 812156669
    0xa03050403021e0a12020303070f081314030a03050907080a0303050c040f0e071101051303050901121802040b09040b0f0414010f0506130504022d040207030c031404050604 75
    0x200000c03110703c210764180039a6450107000c1c00c8035102000040c0c0d0404a0000054034460461a550f0741d0700301d062484100d54101c8054207411003000740c0090540012024483c00c288101403c00445d20384020080003000d851014152045541140b0000d220400d00499119002078040c00e0208080d03c58910100252043ea40311040204400102241c0c010701c4c1e0306401d0044595643e81540c0d0074003000501d0072110305888840004483d44010340c002805080504102041410b003002528011700c01d40382910780f140440d96031801c03010302120840c58184103d100000d401c0c0d074038041a190503035039150b01e244c01030b10f090015180000000c0402c000640d68086609007080280300840d24024480c02901d401d480b410310462110259003070101c00c5203d5180710741d800600000c2d134842201940c00240041c182e840c4ca0401e1071000c0c0c060306480c0e41c001010b14030710a6481117403440250074000c2074115040f040c0c080740081048200403550316a01681c054513588149c00d586e40c4642c9080f8602891 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 812159109 1250 812157859 812157883
    0x1d0310020a09080a051501090e0a03200a060615020a0b070c050a05010204090b0a050d020102070b0a0e0a0b1b1605010e042c07050a030f080903010e070801020d0606080108030a0305040302 82
    0x813600918a00700100801d0004901001050070342040c0d8840602d0419500402c3c08405a940040030003c08284900c07003540a803030808007442004100c0407141d41c10041402c5040d60503a80307400c020004007186461502080c1c0c032074400303050450010b94482600a40103001d000c10058610014018004103200d800c1e451030303100008541e501e42c1c80c030362000030301280e0703072050b01c1600105030010765800c00880038242d0f40e905902502c10b540c01c00da1806038035000502d00f0000c22041e0a104076a43c1c0741c01101d4009400c01c01086034464004e80c03e28101d01c001c3d03080b00700081e080002d03940d6928480c042c0307940c26110b013401c1c444e6003a00418007040040076070140c2ca4014081ca05d8078180140c0c9039082c8440740841d002d058441c0305485400b401015852480010703d2807012280103004951404003800d0400700040020440e901c0300c000d86450058150000c0e038041c2d40c0011800000f10344c9205440060503a410300c0c420562404840e41e4903401000ca43d8400c2c0b60302c503030000d4100342c42842624a414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 812160359 1250 812159109 812159113
    0x3060f070e060301030b0907150507121103070503300c390c0a080318040204050d05030d0e0d0e0d170406030c0207050d0b16090506030411011d0310020a0908 69
    0x241c0e40303081840b20305205139241c050380d02a00c0004130b1400007008503882421003d0f161548bc1000329030314803c1e20303002251510100311100340000e4130110144001d0000c6030180c0025a2554034075140c3d604200c42c0002c58610685440700c8172080714180c0035010754495550201142c4521010f220032420401d2540045a0510340c00c0154032121040154200b9229984003200c0c00e1019000c1400540c0074039028140443c2e00a01c03c200f00b0074003218034606034074030150025040c1703651180400e10810146004542075000481c09505071038540c45a404c004184030002c283c0ea0b02904005080d0f00035030f110141c007031980a41c0e008180036654007241a03c900c0c4070074440d0303030f2030355408010001c0030080181001801440340003d102d1800342d100030340c0a0341105030360b00c2d0b0303403a5050007441580c10012101c09200d40e107a00019607584500103544070f5805248010003841c0500001080c2a04c0d03516611101c02444c01c2c658055200028803222800448000580c1c070f440312081620910700c941d002c200c0074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 812161609 1250 812160359 812160361
    0x210052203150e070b18030105010807050118031205090316030302100e0715051e180901060f02100b0d05060a090b0f042607060e07150c0203060f070e0603 68
    0x544440000142141e00039448803850384510446039043e20140011200c160b4881c0c0030502c1224402c00003840151648041841038490a03008282511402d9008041c02e411010040005513004440081082c0010b00407542d814210341d9111076045510901508010000c030b80f400e000e840421a640106c022903211601d040c0e50382c90001d5440513070794600c0790f1660828500c5c05000740c0014002e03003036a90200b80340c0c41c508158a0101c48a0b0020400c04e041c0949150616000c0e80f4090010007150640205031404010704005001720000d041c0c0c0a14200180309009160156010a4080600011041c042048081c00e07000800d956543d49001e040c0703001e000140030888085a00c80c900080c4145043c1d1281d681c2c8080030040d80000300c8004d04184690040501c0215a52118901e6490040726150a08040e500c40000f2105075140521070382d440200e05001e14140703060441c18440c030904d4075200b0104240e0209880b503501500620300d994404011a90490141c043d4a1a2100c040d2640d91a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 812162859 1250 812161609 812161657
    0x10b0f070f0c03140607020d0512011502070315090302010b0a0501051b0106150215090a0206031815040f2604050909030405090c040311010e0a181b0507060b1903021005 74
    0x46170310503190000907108032000c95047d640186c083e00c2001c004e46600c50300b580c0c60480c1502410b541135421901f1030103080c00110001e040004000c03010010003000198071801c0389400303400c4803441e1700e10601c2065800010045680d0140c11204100c076000064800c81d155041e0003070142140e500910011126404010041035002900111003462034180c04001c3d11200e12040d00c81d00e0415010350060380400000b0502108081c42c40d4902125004480d00082c00c0704030020104015142200e85581115002041c049032004101480c03c0720404200744070123000300010a40300700d11a00340503140c4140014011802801540c0040c20094640b82c0c0914014407205a00c0c1e00a000403507402c001c564000925500c41e0b42948000724001c0c060300140f030b0070242e2041f800ca46680380301104a450311070300703058401c1d069040c18420f0341d00e81703079162141c15601d02082590302c0070444900440b5803500c40b8280b411040c201c03004503a010f8a0030301d901410f0030740c116003a10407010705414140b511855140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 812164109 1250 812162859 812162863
    0x9060902030d0e13020309060115170408091e130b0f04060902040f080a1505220c1a03041e17190e031c200f0d08010b0f070f0c0314 58
    0xd00c00c0e1040383c01c21413005055072248101d0005a6410a00ea44000018811040d0305401e5081c211a11305204146080040d41c1c0800e900044038200e0f482000030a00c039210703003070540055111614502491624070180320204600142c038034400c045a50b1a0140e81889440d505d250754050040503000340010381c5c41b8036407000a58800d105c1d40c40d1000002400040205010a540700c030702c2c0c0e0240d00b003081c042c00c1d2804078000e08009851400f00c651900380802070518140982c101140c800c1500c5c170036080c5401d0b0010890064080003250802040003084005107504104c40e9024004c03039925041c40850b810260703c80c00700345142007010400090140f1107074007031603c1000f14082d55030714485181d01000915860341034643c1c04040f446148034884041902601d003010186414a404241104c0c148a40c00c1c40c7c400d003000c0c07600b40c41d04103110000100358411542400341c000840610326203030b552020b6010500c81c0134800741000191000f000300b0402c40c080060004c40d00648552248206c0390b081c0b0b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 812165359 1250 812164109 812164127
    0x601170c0310080d05070602070623040302010f09031b0c050a080307050c040207200f10081f03050d0e030102191d120a02060f0c0d081e100909060902030d 68
    0x78101c85166000401c410b000984c0c074140030b050790354141003504a664080180d00040d42c121415078460b4a04044002040c41e06500c10180704820b091038101b504001c0e084131207606d200da00c1142007000180c08240c01c03007200052000950340d040040b07061400e2285020310160000e0350711400c0d84400090000000000d0b003e01f9025000b030341d107180120000c11003240300b5010000c00d201c0710b151030a0101d8400040e00014054040d180440628003070340054624041e0b00d1801c80814800028002c50010b0303100513015840c0d030300100c055407034103581b1001d0f500c3d0852441081040303118601100f16031005e40540d8103101c0940c402c00b003480b18105010303249010460035000d201804025004491030304041005030b4114038800b40032034411030340038480c19901c081461228108100f090090280c010002d01d200d02000f0f90710000282082800c400071903d446100782d010040c2d03503007403002c1c11143c0013145044601c5840c002a001a89180c00005040d425102079030500400ea803c50701a0f400000e64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 812166609 1250 812165359 812165371
    0x11d190806010603050106020304060e0d142505151903061a040303021c051806090904050d1205040b0a1d01060f150c0c05210a0f0314090d03080601170c03 68
    0x5c0c040d0f60713250901280d40e4040ca20500e0006034206039030055a05001800d10070035400f0710380310385410740c15506641c5401400d01d400c440949042081c0880c540c010403403c0003a100484d50800c98414141c42c54040303001e07103802160804080c130748040031903009510400050404d004207200c4500f0000c205440c6402920043c2c015001e054003c00a8203e2031480c221242c00c961111420462034614001601900705103c07500070800f00944952583d84640c06881a44030b03900801200402d5a0001d014154039441d80e41c07a542820144400101c0c1c09480c00d50010881e0800203800e603c010202d40007164010320000c06502e82880410884008001e100c16101c0c40c030602a41c0c0f14040e14201c590301f0017810003800584010109000030328120240c0c0c5503041d03088040d4000119140ea501d800c220855200700c41e88502c1003480000c264009441d051461924043c0d5030400014001027100c903210f8034401410001c081c00081c04076070060b030039810541a86102803005181c03a01560000d42d10035180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 812167859 1250 812166609 812166611
    0xd0908030402090a150b22090e0f06040f1209091a0f1005180111030a0810124b0c1514030705070206071a09030306011d190806010603 59
    0x50702d0036004d4054051480c52007507540200c0c03480c0021004035900702803110303070704110542d001e040d0a2001903081c20203017001440000b04032640c0a01c45150042c15041a800c3e50000d41c2088042466805c2d2000700540201c60140340c0040c0c41d1044400d46841c5d00040c41940c5044020245001b606551f64501d0400b591500040e601c0c01003041000740c05009400001081004941040d101032895071058074418100a0a140c0404003180e0a44c2c104d5010080050210f204010070702034070755100310080844850720490448117440d0a184940042c00048892480c406a1110860211080c0620810102204403050b00305c1c211100300380040c40d41a60301e01d060080c08107030381740341e09009008000e49880e98004403c0700d4840c49081e4200600d00c4041c4030b0144001d078003580719007008000192240e010100240386601c010f1004203005428000990700078001c005d003590704502c84101d00036641d000c002c9415903481c001441c407100d540d11b20201d402103070000a01c0c0000050414161041c86d20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 812169109 1250 812167859 812167861
    0x6030607020318060c0114040807060501090b06040504331a03070206011208090d0614180d050f1902010516020c030d0825050903150903030414030d090803040209 71
    0x2080360799029284444004803c0d119101200f49400e6000300321582d841400403070200c003142d180c0c03450044112400d981c100c0b000540c87c030811110380b1505000d007070351850800c595403850000c0b80c014012401828011036603034207a20317000a00003055620810801c10040070040c000111942400c40c0f6108540f801010445410a0749081c0c00070b5034810340165008091076841d180b040922844818410398802c407042140c03c410392940509814020f00824011031a041c000880043d446001031403842c00c1c1600703c03800344c1c88400c0400d45600400040c900b2540b10701188143c140396106ea0103245070b24800c841000804681c06402003440b5045511803080d00e18025203099840c1c01e109103015615030403a548000e002c6000e05822900f054155001d070040d1076018003c0080701c02d41d468221b002c60804504030003540340410450200682514a00340d0a060454001d6075a001c0548000c4c400c0240c0c52040b1a202010030550704d00386003030355050000d401d0b031382419142d59005031420703401120a44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 812170359 1250 812169109 812169121
    0x10e010b0a082a010c1e0c2c220507030203010c05040e0406050a0216050a023303040807050304030303050a06090e0607030f0f111b0c15090102010b060a08060306 71
    0x201c1c0003001c11440c00700c20004440300c3d05011040d40500000c0c1c40c10300003080f1217407002c50403510788440d08401c000c1210207402802d040480c80c0e02c500b03600441013a030396000150a20070580c80030303002401902d5088022501c1b403000703000c40b640481c031442c11100380d40c454440034080d000442104a9009400030450f44100810454030f501c40c50081c1c03181c403864580850001091540041da011030071800041c04d10042003695007103424054000d48a40c0d200804e4601540b03810124800c00c0005d50701c0a4280e15003a8902e482c00801034100005005800f20000e02400002412620460f601405880d0755585901e0003400070141a03c84503d40c5240941c003003a09c1c031291180341d2001000c5801000c0c0c2d540c401004501074000302c2481c511241d03c0c0c00d04c25090654030301402d00306203804540340b521480b400912010311000c1014252050f44100c1c4118071036110b420281c04046200511035688103080300042c3c0c0075280c1d145407950454400507041c036900e584032100e0b50040004409039461501d0305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 812171609 1250 812170359 812170363
    0x3010e03300721090b011701050a0b030d0c02030f0703080406090f03020a03020d03030e010f020a0e10211506050702041508030a110106030b130c0f210311010e010b0a08 74
    0xc82d403600114070800c4041411030341050703c000f4214421240031882c55401c4d51030a0002c3c50a0380800618801401c030540558402e0007115030182181800700001d207001c1e00002c0e0740720300682140c814080c8a01411302951070600c00c0d049140b000c2000c846c0030682c1c0e032410380e803035a006200707080016940b510702040300303440c8200310011640c004241d084041e04540800c16046180c010460615654060114940f1000c0c040e0b0003001c6c51a500050b1600c55000014000f500c510342510310446090000b6080302d0707004680c0b038440502e42018072080f845110300e09001807030641011081d11144810001e90543e0241c0103099030780c820345041c0404000301c40c101000a4080c05101c034142c005018107140a8419400317008190711020001c203c0b990743e81c46400c207c1c0c0d4150744000075589420440e0040c4200341040c413000380469031840f8811850085268420f40e8454050341901b200a0f44c10300515201d038241001000860008014454440007954024600c3c2c622003401040000f034006a60140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 812172859 1250 812171609 812171611
    0x3230901050d020a051315170412030b12070f210c050405090c1f0314070203030402010513030212060a0f0c0206060f0316060905030111070f020f03010e0330 69
    0x41e1945410a0201212507010350892003c00041003810301c52602c1c2e4010b046455402449800002c10380440b5440c0c00900307942c072001070050a489007800380400611908c03c0e004100e50300d460001804030040000a5103100744c200747c651503101e000c0c00440e40148012181313080756440078201c0004c42d21215040000a2035400242501c1d094090070441d605094019680c170407040341c07e441c003c81117100003611240690b09445101171446101e4102650940724000701986108070340000f03032400da840259207100c0100020f04116000c102098501e11300150000074540c014412801c150840c0402a030703441d400c03541a640c007400d203160319810b4180d038810b03403070501a180e0140c0441e41e108000c1c40300801c5003c0c02c3e1031300351003030f91495001c3d4142c40f04075102034079aa03039a07440c51902c0c0c00201401c1d20074040c40b0002d01c6030200a144000390522803000940e96041c0d5202809442c0c10700020300502500b06616039500000810038a44c103482d0015034501202c404507041848400303450b10040d075030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 812174109 1250 812172859 812172877
    0x90a05090c0702090c0c122a0a03030c14030a021809010501170c0c0303100602010e011e05093408071a0d150306140f04031b0807050a0323 61
    0x404002c0000035040c582600380d4400e0000404520b00741c00f0b40080c6142100c501c02e14204948042104204004a00f290803140c40d02c0d01381060034540c006c00b21a4844106050090a06955101d03221001d40601000410000290f09040d16881d090f40701801030742c0480004044101d400b00d01039010f01d400e41d42c46042e110181d42d0000003a0741c884103451302c01406030845c945054180464004034404000035032195201c682003c0e50070313140603406402e6a90034103a4a007a84d060110040703140d8080c0c0000c640044401c0c0001c0381e00e84039a81e006050038401c2d440070a0741c0c03011a00002d24040c0e030034540309600361a0a11950030981c0d66100719103442560103680046802c11025100d4003968802500403030b443c034100041d00c03203e4031000a041e03c015501c00c0b140c0680b1290904503440d01091580d0717014a0010040e5050f1905913002031004900500c1c02500da01103491000501c1400016a00d070281c1c00f1046400680c1207050150402d4814900400c0c21100d82e04203c6030340d5555130540b14030760 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 812175359 1250 812174109 812174131
    0x20f0322082a0f010c020618030a2f070f09020304020307030b041a0103120906020f0a14010f050a2f090f120a0b19020901050904180c0308090a0509 65
    0x10050805000c684100a61400740142c10a4450018481030010710303455641d1100016840800060190074080010641c500544000c2610804c905011080301c20a80c050310701040d141010841809040c0765008100002036440b1840c2e540d803000c002003800c15191003416080c2003a55400c038040070384c0300885000b074054111420400026a0210210703800501c038011181c0c2e503c060545031501c0007400d0740251020000c81e418900200e40040103100607004920103412858a91030341255904205000189501140041003140440070340c0150060b1403c004140104e0500c450744101501d0740c03410000070a0441104940c011711030f86420f091603c1040f88503810b040d0b51900b00310b142003d0400c8103411218846400c0180c41d424005901e005100d101c01500c603040140143c0c1021010401c0d01010510401440086070303007003415902c1d03200c8219030100d01c9064400d00e02c038a2400e20304004148505804001c002c0011150240c90004001e40d04503001c075540d0403c110303000d1800c0e64500286 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 812176609 1250 812175359 812175367
    0x19051f05040b010519090312050403053f09120309030601090e01090f060e101e02030a110c0d080a0903080a090c031407060e03070e0c0c0c04020f032208 67
    0x50400b50803030000620141000ca0810384185101113aa2015040010005801540610405c1b68408580c407045c4050316040e800d140c00d44da119030b500c992021074415251040644507006c540c01540103030705100028042920b00c1211040503071640c00c10315054cc4240c03d4985841c5010000000356500c10100400500150346000e074804002c1c076140194103495500c520b014408030300425805034149124043c001420b070f640d01021402c010501e840306440509024031400720040e885088180b230300301402c00507507d45502d1000780c0149203a00f1403801600c0089411a0014000318214181c070301640c5a15a01d5640d218054041b03e4201c040200800d18160109020044950000c20020301c2000c14012480c1c50b5198030385120b008003008507095100c50030611000e68440708058492005500400e00d103800c08419280070000101403403040320340130035810384903007040048071900070000d0030456503810401c004101542c4111814030052490440d048030380c1642d507120000c1c1c190041e50131810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 812177859 1250 812176609 812176619
    0xc030115030b03030301030803010e0f06061903060e010807030b010b0c0d0c0203030d112104080d051b0a0206010e06010804050a030e0310020d1b140a0f1719051f 71
    0x49510000c0301004242e0b0320001051141c4080009502a40c00385600540780c1d8501003c000c2404c60040400d50f40d404c65205101d03072030b120842a108880c002c07803c1c124006650f210100d000300003a6200e1905c01c0e070700000002d21880c0118a0100760380c010b01504801d13030303241c5000415520440b00c06140541c403403044501650b12441c1c400b000700b480102646c0c54020101c00c982d0550b100318403154181c8000003608190b12504422000c8041520100e5500610349030700c5506007402810740c2142810340b00e0002030000058007407102d0750714040c2020070380c031684c01050082d900d441c02d010b101051203a4001169a0b036006408441c480c607031040c0100801c4040f950308688041e81400b90750740602c502240d00d906122103002800849007210340c0016840881240300d2a00744000c0081c00c148881c4401c108a00308109044542070940ca0420407c80800003404888480b10009081c4000a820080c0b086403015501155009481030714188aa91140c0740049408070078078840b090301008038a02081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 812179109 1250 812177859 812177879
    0x20306010315030c120c090e060a061d0109020f070c1d13020913061d0a0b06012607020c040e03030f1617151c0302060109110313230a0309080102030c0301 68
    0x11700d00c135030555010107076141c012100b640c050801c4900c2c19040b507010410160707000e00c0340c6802000150102e405070000c50a43c042c1c0014107010700e0a17a079400040c03407401100c0d1402101c40040c4c0c402d071064030a680d900c000d040121103103820320104c40d014501042071b42402d4080c0c172607030b660020002c42c003c0c0c490000100080700045811141261243d01d562005851005141088084c4001a103c07000326490041010000186494140b0680042d100050290350b81c8010828043d0741800c4440d403112601a486d00c0850f42d400365126062000e90925020044061030084480c46182416a111004005a0044001c06540c0041d10541c1c2521050420704191038000402010b0415404290b80200760003081500e400d060442e020b00c035240406504007c010700500d00391034100084500e0212602c034521005c0c21030300899080d000c001003404129130601841500c03448040780c40d460003181c0152104e100344015808165041c00014072900d043c0200d9110711a00e2014a141d80c0c00c00000075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812180359 1250 812179109 812179139
    0x32007060815030a021c23070b0c011118041a030d120e060106050a0215040c0509040206092d1c02010c08070c060306090606031506031d0a06020306010315030c 70
    0x26410303c1341e075040c84056110139498508444011350309608240e450708081c0d894601e82c00b450502001c002441000828020070750106407046070769250b9aaa1460749118054180000202d1385403000180315004200b5200036104041e005480a100d80146070100c092070034096079074035800da003140d003502c80542d1240007007100c1b00f000710301c0001c0c005201c05842894000c0036001701d80451000609150324640401924101340e003d41141c880d585030079994041385011900c070b80d501a04407072012800b15074488055409880001d000c131001600c000d012000d2150b1900442160307018000c004031001e08000c1441d43d1540d101c050711004a0490340c1c01100c80e0a0341c1282514034000a1203484000b0318054002001841c20b0b82d00812160b0030284088100c401c00d5102c03e0a0514080c11194084003025008040719241d06000900140c1030b40400981d2119403403480c03c5005061500040140950246014130800ea8040041c208035040390080c9003090f0201404001998204000ca803981c0d001c80703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812181609 1250 812180359 812180401
    0xe040b0406052a0a03060e0c04050907030209030f0c0922020f0a0e040f0b01351f050a0b151207021504060518160902030604060b070320070608 63
    0x70f10903440c0d000300c029030f484070090402d600030710740007030000d10310340c1d15000b0356010382054800a0030500b0103151409103440f82e4410203024118000000703400d24000e0b070580300305202c064251400b0f111104449511061400c10b503d102d083d01c0404600310500058820f61007452800000c2003c0015408002070041080c000d940d200c0c210f05408100032207410241e1303004a01c50000a06c444601d45040451194140c0088000c0e50790218080b402c00112851144003081d6559814401880c2c072a1040c14000541da00c0c00b08000158404e107401c011680c1315070b109404203e420051483d0041c05c000e58401844012a9501c1c070030302a504030400c200d102e10350028858012521000c4a0000c801092a400c0310b0503034103030f0f50715410003050341025243d015945512401605150300340030075005481d1600e02a40c503c02d41d0100024425454550100004c0c1101c0d0722130716214165490001c0070070324078030380401011144c030710855030902c0d00144034011395280e0b8840c0c840994404500c0d485101c111070070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812182859 1250 812181609 812181631
    0x90c041509060b03010905070f080a050402150c07180b06040e130f0f03080714190c0c030503191403040204020d0209040f0f0e0304241818060e040b040605 68
    0x400a07688445214a8004284090f22107403250301d03052502080300c0b0024a0390341440784042012451650002880c2e500545034007001440d52a64004280303401143c14000300401030000e1400000280041d0001c200c1c0c0c02c03011020240f410b410042c2094a044800741d681241e0148001c0c0310320402c0d030030615440b0440e80040343e0645003d403540340c0b00c8404118165a03814102c656682450384c8500441c0c1e1062050600d580d00c11484d030b00f0790740b4511441644000c800602125098054854503203521400d4000414186035a104c0c01c00c140c40741e0201b0a4200c2041444a08445590041142c00250140b1241c254290781e80c603000d00010350b10080c003007280185d080010060503a100e1107a0390f481da804013000110350060140c0d40307045403d51044840103500074401040590074036a83c500440801c807000c2c81461500c81d5068425000c98821880415064007001c10760010024013044101c1c090b090501015564003071903641240c05071000303410340c14031400080200d0101e07008035420110303442c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812184109 1250 812182859 812182901
    0x170c100509031e03030403260411041a0a030b070c0f120e0d03090e070c08130602010606030e1b03030f030f100609061e050d020705060a05100501080412030b040908070203070e090c04 80
    0x3086145008880407038508644410ae42200c0c1030038861041c20345a03070892400042d4880c00040d003400400e00c0000d0001b4170090018265506c01d03958803000c982e03c000959a1a01e09242508c0380c03400c048002800a46800038a00c010310300050000f0884e505078039041072141c20a00030307a481000051092092000c0024a0400510ba03440200102014060803509050414000901b13460b0198814000c1604010f01d4003c6a0380102d0000300303e1541007030b4100d80c6140320300440d081d8001d105107510360fa0004070030041860f9000c018580300300c400b85582d507a02c903110101074640c44940e018400000c4e10080000c800c0d901e200301001003003082400d0440c00e110b00c940c600c01c280d03407055600320f80ca904a2018001c0c07144a40c01032a03000300b562006c5204071410400028841100204003500c001d03050002e8101b007500923444040041c00150060241003420300305444241d0090804034040d1158000010300030064411143c09040e03c0c0026000d104003003800c00000e8000804456450040a9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812185359 1250 812184109 812184167
    0x80304170316030f0b0609130603081207020d0203070309060c0c03050d021e030414130b0d0c05090601090f06050c0f03031017030304020901170c100509031e03030403 73
    0x80051482002042c1c203107140b0429101c0001d00f03642001d0610051182490f4500d07081c6c0d030b1000260741140ca03060712900212840c06554101500c19a8005041c0e200005202507030140c542c042148203c3e0241c00b04e075043c1650300c1e4126a0ba108002c0c0181c0000c0b00940b0600c01c0611506404013100e0041143c50019516a20707400d0819031001c0900015a203c40e8600d11601e6622031100072840307900380a14103041ca401607208401ca85144c40074802e4a2640f540030850089038064251042d0180103d41c240300940f0700054603103114011544107441590000e0400d61250aa40080c2d80c4102070481a0901d0030394190b40c01d800540d0070782800c0c06149044480c1c004c08201543c070031440315080300700e60f51520000300d03820070a4400000c1903400c10006c100240c1c4500a550341110385a03501c2e10030701c9844091207420403400205881c5c1c05402c000a0043c0300da0301101601a00008900f9207440b4050714104c105090014040740b54035420a000140210b8000c1b202040c401ca64001d0700d41d0014244 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812186609 1250 812185359 812185403
    0x7112403070306080f0304060e01020a170a033c020f070605010f08120301052b030c03121e0b040b031519111603020102041508010e0c16080304 63
    0x111265250840100c00c11000c1d9505010350801031100001a00340103600f610342d02d071240b02d68001d0000780860b0750344600745648200701046038160486c00c4800c140d1400e040d140040c0d40056000d100003414210341e50000421041170b54500f01d42100a5070359640b1016100c1d200402080080140315401e200000071800f00000918a4510818002510f9030500032403103c90000b5130000940c650103501d1030402c0051a1701145d045d0303641102d10500d581d41401d040840d00c4510040c0d0762404540550350740406400500210f0503903c2529526008442284048100c0d4110525142c180b080345080d00701c02015580b005500080240000c1100e40719800401e240c620383c0b0500320040200a02003280c000a580803205003121215020b005c1050040b0510525000d80799451486c46005446581094001d5048074001c108000180e40c1000c1c00743d0340508081c0e02403140c8002100c04900280c3d10f55110821034220003d030601000400c00320340c0342e0200c2c5410082048600e2101c001100d610030002e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812187859 1250 812186609 812186659
    0x409020711030f01020304080403170d0f1d16210f030903050606030109020108010e09100f0204030606052b08090a03080705010b120601050411090a0303030b03070b09060711 76
    0x100c022141c080709600505141c040700030f8000029034414801c3c84005100d004c12102200d070031800042030303950303586003410706403207400b40804010740f42c06421400f141170394100006600744440360680012002d1143c0d502d559020700381d2500101c000340300744110140c80e0000320403840c0f5103840c140040855034030640b801006503c00d501040c400c410801c03c12804022107548628103500030320510419500113400e240707040c021034002050690025034240300801071030300790fa08400b00078401d58010000203402036100e80029660281440004109d90a10010340041c0e400001d07920302c5800005031220100d44105403003120411b404011201d00d036501c040e8414042d50140c0c0c18565a0700c160f103060750031120300d02c6490b2f00482e010780c40c6c41c958a0000c0380c0700741141d00648010030408a41c4401c2c4249224242006601041140010003072662552000700609801d4048502981c0c8030003000350503016400c0c1c50741e0301007010000e0200140c81030404a00c03524003d0012201ca0041165402a07004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812189109 1250 812187859 812187863
    0x6022808040906052e052101031113150b0313050607090914060120100518070807120303020d0b03191209081b0a08100f050a02030105031c0504090207 66
    0xc0c0710b007418807061030810004841c03d148600101d181902003058245c0c4070380c20b071510308180400803a8290700d507070f1205140a020800342808a003a5078403031402d1440c19018285060045e00c0b150210b5141c2c3c0268030400d0300040c00503030321030a07079490b00320010043c0d4002402c2160040c1c1030b0800c0d0000940400400e800380507a80c039010381803424000b2041c112458117074030380c4002d51440b003070120b166046412540140c101031540d1240300c8a59102c3c500d4010382c00c10701301086242c0000c0003140842c410303119081c840d100041e6520941d6030110300740d85003010f02807440081c80030018400003038020b0b80207005000c030901001c580c2c9020f0600090502c60514081200600a07080c58010402c00a070b81c0d000d01480c904042c00c0f00c03824001003550358028034001d40d01c400210650400540c0d501c0c1c800d50003d000d2201141c920800c0152420040c0182080c030102075030911011036250079250003503905840018000f041c1200034582c0b094050002c1546181c1405020000807581355254001080358078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812190359 1250 812189109 812189111
    0xf1c050f0f01051b031605091203090909060103033c0c260d1a0a080a150915021e0307030e071d04081810031a0109060228080409 57
    0x144a1040035403d55600a00711406803441d000a00e600000600c2640e802515002c0c990280c4595200283c1c0e0920072100804c5d03001c09004014928041c00100416490340240c4107207005440d1004600d60312503003800b00030003207064608c071340c03850410180c00500c40780b9032406082c0740100f404400f090500000d0074500001102040c00c0e00501840b51400742d034100000038403086031001801c1949042c0541399284101c240c0301c2c068542e1000020041310702e05440104003681165840c404c2c55511140b412088584180c860110400b03001184034814031950006407543d0100d204208072802035010101d200b00a0341e9138809082042108400b85118003201d840010f4400540800e0901e0415a07512280c109104c00700034140a1882c0307044140c0099001200c15114101e001040c24114964044240c000303851008110503607030305810820102040820307070004000b000c401114005514003a15025038002d03c400380c0c1006000400c2000726204205404408005a86d000c0483e44594000000c02e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812191609 1250 812190359 812190373
    0x6130209061314221518050f090a0209010e0403020a05010c020d120506031921031d010509060609060f0d14151501050702040f050901090506060f0f1c050f 68
    0x6005214030703040d00301d00480d4030280b42030b142a1442010303514008850007942d1644685c603807104040715840c004e4500b01d6a085a580590840c5d000109000c5684807851204030300410900714010624000854014103907220581c24001410000b25014104408510440c003955001c11405e10504515902c554041c0596080d4014000c10802c100c07209112840e05d40014404a1740d0001448401891440d45280303034035031141000d020a001c0030400c05000100c566450b41a0b1341c0c140c0c014503020000c5030494002c056042c44080c200c0f042100d281c00e043e401000442d600e8507040b14499404840280b003060900e100e00301150740400f68800440300c00010350003400b468030040c807001240b000021015401454a41c0c2d03001240b02c9683d590f40e05110303000034014199211034100707883c0ca02c2041000c3c000c60806c140446e00801d4518400d840718000c081c040b500514210810740d80140740103080440c181e060b10108a44048002c0811221982880318100002c0b0140482e030300f0404040042c00341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812192859 1250 812191609 812191619
    0x3060e06060306070906200f07080705131802010e0a0803070f061803080a0504260a11010c09180902041104210807081606020c07031e0b061302090613 66
    0x25001010303004c078081c4100040c0501c841030780000d0030380030035068001c501c1412409103000d03420f00d0795034062a007942c081d070355021549103400505081280c00550300b072040640b803804540120340d003c070000d42440c9032200c26a000b541c8210b03203c00880030000e18030381781980e41e01d600d05c1c95036004550031201005540f0300d06040c402a07104000c1413843c4110102401800399400500c1e0b00e1008007002d00c0c895403600414140080c03910245581c07609001042e03103414581104c00040d820402d01000000c1002c010114200c0301801b035010b4103030707090701d968508904005d04544002003002c00503650a64032804000583c0e1540907030141c50702d05034001075641342449294085500700d051b80c042d44120325080040021062000c0302d10403134128106a842e401441290002804e003883c0103064140080707070b500010800490100700301c030701c00c0580058130452056840c01c00700f43ca010250011841000040140c10020070003910f000813404010b01d0403650100081c00c94100a588000c0702c6000d010a01c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812194109 1250 812192859 812192863
    0xa060509010b031b0c0109050106030309080f01141b0708070605010315020301080d0c1e151a030a020d0213060e010302040c1d01031107060501081b0a06020a0b1003060e060603 77
    0x3002d029011095850752505004900d4049900c410782160386400041040d00e200084d4010300c40698000020301c401542d904004040c0c540d24041c0c503c407401810b4004214120511541d000000d0701c03491850f4a50700d000169001c5241200d04195800040001000051545009001d0a440740900080703550540c1480010b00c1520146028091f104100512141c4000254281081214a0200c00001e82440e1030651800d00143c0030700403504901c00d190400042040c00806400e5455042000d4207400b0103454015a0841e0120342503006100303001c0c05824500ea80c1308003030b070020b8584211031203034030141011a181c130383c030100da0041410010720451910303018001004507540b4102041c40015800080007480c8074451b28141aa1a21000e00341d4000d00160340c0002d0700800300304034560751070004a850f9881070301c00d0115a1850120035110723141c00d610030f1050b10015401040e5420503070b90b40c0d00d10320001a065806040e00450300000149850107601081038241c00a05034a060440c240744c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812195359 1250 812194109 812194111
    0xb070318080307061d030a030f0b030a023d02010906051308160606090e0307060c08130314070804080a02040c051806160614041a150607060e060a060509 67
    0x40c00300800404214400780042a40c04054003c000001c0118400c02000f8154405d00440301c031070300000c60b44c10281078055100102d40c600c01306040c00319009844c02c25454200d0a000290301040c0500c617040c0c0c45a184000e058485480b500e12144600c0d450752100085801d4095440140e4513602c0407820014180542c0344c1241000c1d403035020035981680c4242ca00d00846615a0300c544030507403120180715942e00120014040c2d20001c00c10a61584011516948106015600d803420524400e103a90300c030f05402840703940d0148130388010254568044800c00b407502c250b406070300001d202140114121400600080c4807120061107214440d01c140000c8e0361581c41184280001402443e1046040b0308807402d050390122500d50341d52160f81c80c81540485464000f40c0054541101c507105a6003598100340120300451510001c491042e1400072a007100716154078810f079401102a03042c0c10160081c01307070b40e8130600021810020148105251200880d089800151500404c01c114241100c00d0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812196609 1250 812195359 812195387
    0xf0426012d0c08150d06050a0f150302010c021207080607081603060f060c020102071a0307090b0702011d061b100f1a0d03180b03060f0402030403020c15040902040b0703 74
    0x1440b51002d02e400283c41c40c1c8000f440314143e08628201401280e80d5001c4540504d940010704204505200708004014074041981c01c24085c0741031a4654038802541c044821203a050303581c036140c00000c3d42403003103540720411104014400e050b03002c60b0b1210b06200c2c0134402c00341591811010700c0d04103c2011600380c81029401031601d0070703000340081d4116000c0b10b001c0c3c5205c2d043c101401c951503c0100d00d81022a84192107038004103050740c1031542c200c00194007030303c11643c0b8200c1c0380381caa03821010940b1034080000d0110390b40c10800c1d40380c0c641c41c03405800c0e8490001e002c541058014940c010380441c0069a03240107030010b20401c0d42801d20761048414405642108100f4040d061101c04414030440c10703000d2055680310f01a100301803060011809082c4282113140c0041d071340e4440780700c0941040d6400c07403040c02190f00034038182c20b2600c00d580c41290140d0080819520060920015040c18003290892001c104404100c0c60184e0009000501910340410307554112418000d0442000d2116 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812197859 1250 812196609 812196611
    0x60b01030b0d0c06140f04030501060509010807140904060b06030412020f12040e060f060a080603060f04050a020409020f040905070314070e070509040204030c0303080f0c0f0426012d 80
    0xca5804140c5800524060300e5140c1800802490100c910317404d10301808010312030003240050301004021040d04020101e5805490610323069888011403605ca20640c051040290703100405510707585010030360315411501552000402c2c0d5040400300e16194412241540c1ca1f103200d0460400c4640c0c100900c3c0e411010180c050174884a204107074102d0b030b1040e4404e0030000e6221801061041d500c0807920111110300a010710741e6840500f1010302803400490700c0501c2409044009036000c000b611361035100302e51010141440d540780e035080000a080c0c15905036004a4000c080300d1035034403144281c461060103440141300a41c554a00002c5000d03200c0c00b6102c5a070064241080300404190034141c000b440340c1803058590350894080b40090185500c040c020140032440003043c180c100485500414020110003001c1d95019044009071003401c80e05410608208070410020300c0079460112621680c0050207116200c1d807240600390345e0840c0403140b1000054002c03800c2040e034846107128039011464 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812199109 1250 812197859 812197879
    0x13020301061d0307080a051c02030712030f060302060c07030b0c070827031b03010510030c050d080705100c1115070503040f0b090f0c041a01030b120703060b01030b 72
    0x78010862211820401e09029441007607030202d9905010703003009003003104100e40016800e07041095490022103100c2c140150207480e40d00c25a84040101d50362150445100e803c80014807400700c00900b0301500040c4807568460000c0700603a10314009210b62044200102040c904504020003034820240c100e204054041207180c0019801109a441d850307000701c60751040b110540c40102182e2004204150f140c01001d500036186c5415502607460f090080d0000c200c55510041125260f03042d40c00090918141da034400c00203481c01190f0071201900c155a200d003070100075500d031840c00e034900d00700b0b00606864190184400c0e0740903018000e04040340d0010140c5101b01050110a03120141c900b4042183c00400a8148524011084402a400180d040080c58410744a68840d1400b440d410716034040c02445004c00d15140c010803104900e001140700c1c0304c2e152080150014654460740c03d401510303900e0300010f0320394103124503402980910404200714000c10001001c46030740070042c07440f40403200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812200359 1250 812199109 812199119
    0xe0105041a03100e070306030c1e1e0323010c05030c16022d1201060b2d1804060905010e061003060f0605040305010e010e190317011413020301 63
    0x18002000c452100c00403642d803a101c070421080c05800e07a401c0700711006444401c2c0b003410750f410340c0308074105d9010b500f502c064030361209000300d108980510070415805234103d0a1003151003d105803145905032007070101d4225680d0f9644021004503481c1c0c4c60403100d403035403000503011017070055804203100c0d49081c40c6545401681d003161801840b03075199098a10701c14000442d2111a074100101e0107498903442c5442c0c0b0100c54a003090484c001171405900d160030703071911410050154000f683c10740c410043c10a41410f402050aa849441c2c0c2c01451072000200b03111054020001c01c0e0110440c550100c010400d2010701c030581f030b1036500540f030780c034a8a001040940d100c8145a40c01c9102101d8900000c240180102c02802c0690440000c6003a4078100041454000d0000d20482c4d01c00c0e0002e020818001910781e00722080b400740d88403250072458034588007541c8004485d1090303100e810640f40c500f01944400d207a040c1c00342c011482c0710544240340713501c1d1301d8151103801580020080a6207198105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812201609 1250 812200359 812200379
    0x5070e1003090618151a150304020a081b040b03070b0c101b08070828020702040b06040f0b070501020f040603050411040603081b03071e0308091606080a0f05160e010504 74
    0x84c03c810804507594600100c1c207502c104101646e400c4000d010f2182c81c501445144200d60013614100e116202351040042c3c0d15401040c0018080040d451301c5400422030002c1c4000741440045042d40f500035a10042984207050000e806194204401403030701802c10481d48045802034000801513020460014070760135444103405601c07450524080180c0d8440c8000850056981e408807035600b042504c20701c41e44a1030ba405029140d0003150705010103c0c9010500009100b54042e000e0b517140b500500303010036115800240045441035000600e000301d076103030030010381d0040d400c00000a900c0340184018403155440860650504460030440d45195a031203000c1846046c0b10740c0400441c200c0c02c10174031b0900b4410f55035120f40040203100c0441d02d1034941c00c20903c5004007200840e80005c003007802c402000074140c280700a10f00c0c180700d480e4144581034036130344001003941c82220b0316203244180440e0a402100c1c0108880c040c01c92a040f0f02c802c0160513851904201b0b410894184000c00071088a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812202859 1250 812201609 812201633
    0x515060a0918230118080f0f070c03050615060a021b0301061a07030314070c0204090804120f0201230304020f0a0b1305130e03030a05070e1003090618 66
    0x71000000c0e003904181280301c065074070181c018118094101820102c1d2241d5182810410344840c000c108016640d8031040c065003024001030304250080c49600ca00318400c1c0020240424840006401d004c099515010b811405400c11505c82d0003100612011280c0b6000100b0b0107030044400a04100c0e04842c000d503660b00a06e41c1c101010b4040300c3c02c4901d61829803090000d45400d4480c28000241c0e003e0300f01ca03962100004400003460021140240071403030380c0381ca000e05510b42d103c041d000401d400b080060103c2d004240d4118104100c0016001143c03501c03410034600c14203c008100c83c90f4000903102201c404240c403501e007a4007228400050624003100d512a9040f00c6e544100d110b0100811010001e50308001d004600008088000c1c10b84408024102e0348103e0702d1744086100800950243d076510340342d540542e8002d1002c60b4012500c1e8008030303130007011468600d40c1041078400003041105050051300120f65140103040510006010359204c50101c3d40d118110b060040c2c0c2d900e044210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812204109 1250 812202859 812202869
    0x8011b08060f01180b0a18090b06030c090103140708060108060a2d0305120c01060f030308060105070203010e0105330307061d040501090c1b0c090f0e0d05070515060a 73
    0xa50101d05001c011325290310140000d0745c200364482100c401e020301a00b04026000c166100500400100501c0c01d004004080030080c3c04141962207800b00c401240d000748120360b06241d01c0b800c2043c0e031800703280d403c0707071041e0601d0343c6040450411780005000b00c50080c0002d406025454000c0c000c24040429601900c0c840c603591a0303880c0d802e01000c0c881e070030240e000280540166006184062420005440b03640d010030020050142d5480c10850307072006070b10000300441c8030000052035641c00b5074043c000301c60010700081158580401101d007110000c44140c505030380100b00c4104200c070142081746460f4100b481006600d00700320006a0f90340c045200b4401000342040c0741c00881000d4444058079001d02500034449944c560b60101c010300126000c034000242c1c40140d10200b03406400c030081400740c011424000b45810107520b08054001d0209401e0025210f001e0b03800c8036141000144810b02440d940e8075164072091074428203100c01641c143d014040ea140c00d000700d9546403446882128 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812205359 1250 812204109 812204117
    0x1b0e0420031801090c080604030215070e121507081012050304031b170703200109061407151a090415050711190b01150e0d03170108011b08060f01 64
    0x802ca210b460151112600042c01185681e04c0000c0c044d100040c1980510700c00e4003964038000c0310f410807090a6104482d09800565440180741503407c3c50404056141c08442c01d03100f50b42903004004070b550006541040000e902402007000c4480360980d400d0140080d403030706e005c40309202d450f100c0c0d82e0300441c0070140c20010105900501c1241c80d10120700101455422000354071031a0860750303140c001911054071ba21903550302e01c0342c3c44454502020007002050310b400180a041103030840c0d00070b00c0d203000707007040c441d00f0805903010502070088040c910700340100100741c240c0110100960715041001481c06030003110240000542412020204000482c00c0010faa07038490000300c510410400b481160741c0a2078801d03400d81c1410a4145220501805240b2841e07640c0e00c50442c0d40315000c1d80c61400142c221241441686021504112070901a1a240140e03041d50105180041000c1e448000759a5440320a07101030040c59400c1034130400c49040c0700352a40342c1000810a81d848446100d4100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812206609 1250 812205359 812205391
    0x908030c0310050d08031902090102061b041a07050705030a030c080d140a020306120c01091a090909070f0806060f040b0d0803130201080108060606040314011b0e042003 74
    0x803030b0507a80c0c071004101c020400382203011142407a15869100f645c90024160301c04003166424440360003100d0703460806900070480355440560448812a070a00749011480c000c100005405a501c00104a90b202c00070305c0790b6a80805180581c50112190700c154040d03081155401d0200750440b18540c004c0d0381005816550b0b070400b4101500034000c000040b00589020014405e0030340c1160f002e0340c4641d100f135940d43c00800c040c00071107544804258210340041c1211000384081c400716442c031009880c090300a2802c00081030000707841c2500442e00010f09521800c0300700108480030307003014010310408015009605014010170140c410302c1c6841401140c0b90300000c80607072500080c091003a03400913000c540300d0070158007007100141060416400624640e002180441001c10507602903403004040a180510319500c051406c80c44820500e0340e5569452200d00880c2c08a5610010041c80c2c2e950054001c000d60401c0200ca0b1310003000c641d0890703031600d80303101c1c1403440f4100ca03000b82440c0321940703607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812207859 1250 812206609 812206621
    0x702131505091003080a050f12040f060e0f030405060903100c0e0a150c020f0111100605180906160c0b0108070f2301121d030406030c02061302010e0d060218030607030908030c03 78
    0x8c1c03440b58035041034200e0042d0041009001ca101c89042100e48105414000c088046900503034805d461000110a500100810852468040000c04441101606030f031900020030141c00210785503001d0070004104011b18501c440d10307019104802401c628161441d40035404a40100130104a5038020700a1070701c002d031100c1503801069040d448400301022200d41d08503141010000c1d004a2054a01420444034010088450352200c07910a041e100d00401d0240d07a4028a8460f89002007294010f00001010b200d01040c650021540a40712581c001d0203490b180c0020345e01c2c05040da900c00c61042c00240190420441c000c2d00c035882c0680240303001703041c110175003c2071030043c01e03a0104641200c415800e0000390200100c040c1040f5046510204075070350381d0f10401d030388481040b241d69444915500700c240056010b0740b1a9100007101600c0369032220055910402240e00901007102100351800781d0102c546010404181d115000389824480001c00d65118200c0e07001c0039252001d4900b0110000f55 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812209109 1250 812207859 812207887
    0x80601120203070f090b040b1204020f03060a0e0c0f1f021207140606061c0905010204050409031106061903030e030c1008390702131505091003080a05 66
    0x4510314901000c641e03078181850081c0c211614000b0300b0001c0382c8003140008200100c0750030340d4100c0790495065031828051114a03540d96400600490b4402074660ba2131a503500c2c1008494030882c41a08001880c803c4800145c1c40c120800f050a44103984160b6020318644840c101183d01d0000c01140c40b0f03413900c444070164102540e116200c900d4050200301401884100ce1541d9452101081030f6042c90f15030b4801d20043d4400c0b41c541128504100300d6041d00c180301540170030040790007400010300740380c1c0301c9001070140d49001c0c0080d00055007034400240c00c103100f03000e10783e00070208a5448510300540307008614003142a11011f400c0c0b03c0300c0440c158007502d00380014240030000602d4540c480160160140c01da10094072a500217000b015018625000d090820b83c414608199490700d001207010f0222503107078440042280c001f040c0c1910304061040900078046c0080c411444102528104014064444e030020078040d000d200c014070400100d2843d00461300680541c1c03030010307a01d200e6485011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812210359 1250 812209109 812209127
    0x21801050313051b04110a0504050d030302070c12021908101a060412120302091e0607060f0c1103030408190203041701020d05010803180f010c1401020304030f0c05060601080601 78
    0x40c00368001e02001c2c64844100b550a06007040301100e04116102465071b40c0c0d0801d000765086400030a000b0041841a0301e0a0500c10650611030301c0c000d03180050a80d40d01c01c08410660001701c041080d60040001c45c54480c440202c51840004a06401480c09250307680e01c2c0142d1558051182d903a0303c5210425405400c2c00784481c1c00a0442d55445507582807803004191020010f8903680c000703040300005503102c0c0c001c0b03503d4680010300c03105010a42c0d0180c1d00d0340c0e100c0811619400700f420440a4009040c030700500000b0140030000145030310480d0000352001e0501c3c0d0118445800030030410000403600000d5610f0841000f0404807100700d01c500c02e0749075200e00e030465403900070841180014280c0540080c45080e007001003c3c000c60340d94021443d42e038003407044030072000d5250007900d010b5401d10b01d0449108480c1450411110007064459144440c1c0c12480408907135000010001411f400c0700c1c401d0315448561410b034503100061340b503e41e1905405002d41c0d04100b0000d01040103a889000f0300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812211609 1250 812210359 812210363
    0x180f100c1b0302060c06070305010e15102c100e0d060e070e090a02040b120a15020d090305030f15090403030b1807030506090a0c02101107050105040c18021801050313 73
    0x10941d03505c081da440c42e507101d600b2103c8000090404001068200ca000c082c1402107980c45c070781d00d01c40200c100400c02d0340390103101c12608024901031050f0140c100130062074814a204035505002480701c505200122050b054040103114405138080900c0d22034540d1141ca940d04501c00064010040003402e041c804a03070301c00381d54800a60180b152019000c68030454440c400c5604118205880c03040c03000903110302d400200140c00c0707a541c00c00495041c07a5031001c0c04101000041ca44142030100208a60508900b82c0c0040c070044100320034102c41ca190380c1d412500d40403441042c3c2d21044000381c600748009000030109521030a0032170181d11680d84904250040000c0c60304107185c07080004000340b0048494a1107130079081c002c50200c08035880f9500d20340c0c45690142c40080c2542c0a0741003d400c5481c1810000b100c01c000303480126100b0300c600c6000c0c1d0300c154400c211080c03030201054480d401245d11124018410805a45421201c240ca0f40c0e40c00030a082c095143c0d0b84090030700f030340340c0340300311300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812212859 1250 812211609 812211619
    0x13140307050303180d08060d03031d07090915050615130506074d030c0a031110020325060f1d0d0905030a030806060708180f100c1b0302 60
    0x2072000000b00100703800c9141041e0000c55829140305d40c1c1c201c1d80f1b00c8065954a810071321000d0700c4070100303100350007032584040c05410510400c03140e4a03103503141c0308140d405404119641d500d030f01e040010080c5a0a08007680c01c01c180722074102100012a04030020511200d5035000048080d141e080400a0400a1400800650700c071345141c10002e41c49001800151285034031b03910038031088000c4090000f070564200201e200c00d1210070702c1d10800c001c00c1c0300c3d032683d041c031481e0192440c580ea440315050142d031040d41c000c0302d8100d00d2001e1140c020240c802100540d0001d00590b1244003031f500c083c0c0ad2100c03802541701281e002070b0510000518000d40240d60306414484d215040800c000f0402201c03000490803079400c0b0000383c0d02120145410f020312070b8150443d140000c00700340318280554200c400107205a24150366642c4212966110600100c100054034403440b07035519144000c4180b004080e84c0f00d4240c8101c28000074051003002400812906460051509245d07011441a01441e40688 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812214109 1250 812212859 812212861
    0xf0103200304170d1422260d0209010e01020f0a15020708070302071a0903030306040938010b12070c0321060f050301140c07032604150513140307050303 67
    0x20340003021740402d503100c407040c2c81d020011445051800204031011084154a0340c0c820700165101c04200c44144800c0d049a800c2c5682440c281c1e207000c0080141ca040c3c28801a07842ca41440050078001c200710101b4155041407603a854800d0000c648598110b5015001b08001d031801100f001c002d0050b84406400c1180100c0c1550800d81c0001e62a400c0d00c1501e40324020005154440086034404c840d0b146400d60401e20109111341803d070420040c140c8907004040d5007040d45403017070b400d9007080c0c40c008a58000503001c00c001aa00601c43c10b000d480621a8649440c10741c40443c005041b014080c6410000340411070410f041c45942500409844641016901240c0c001282c024001ea406106c104420300c4200294030714052041342c141d41800000c852417592403808007681a04045170075800e102c0c40364680344e20b00101d40c000821003034007002440843e040c03c4c100a0407852848481007211841c1c034040c045603000d00e6640e04640b6901640980c010300221107003505601584400400900c4040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812215359 1250 812214109 812214127
    0x403030504060e0303070f0c050703080705030a0801120b130c1e0e061806130603020d080a2606060d06081009150603020a050d0809090403020102090f010320030417 72
    0x140040d070056015040602041d07401c3c8840c1910b82c84246d07901c40c013003000d0300320701c8110383d0040c1850804140600203039180160780345c0381e01a2030360060900f01c40c079420005c0e1445855800c00341c40340c090b0002090b9038480c41c02c25551448100f01c007030201010241440007c1c01041304940e0004054600e0f0a034841920585846000100d1040c0c0646030305c01c0142e00000f001d41c02c2a0310000107010210164000b9611400244440d4203506204030700c0c61034850a020000d6260040b11420552040664640c1c40d00218002014126181c0c03102a0094400040c00803000003000c20603080801102d006a440a0040401004010a9003c1111030042d800b400c42e406046032b0190400a004954460075110404480004c4542d54040250300400b005814481802d11005298819104407002898003d82d140000d0046204880840050b90001501c00131307400e02282c4460b03282400e0034184611000c03420143d0b10b070500c00b080304e00c61140100c0050309000b01749450401c40700015001c29607950b006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812216609 1250 812215359 812215361
    0x21010c0206090c060f03070f020a0f03020307030e0d11040b0402090306090106080d080106080109090c03020d0b0402010e1e0d0c150c02100f0219210504150f0c1103011103040303 78
    0x31200c0012600420fa143e40c001e00301942101d41d28569101082e01d0360b5141e44064a0700d0380c2c4000854118410081d20000040c84444030303d420314020f030010f6840e40150f180040407038002c0c60361a4020500d01808100059400c20240a10300e01141c0200341c500300003020800034000c000c01e141e0b151082000340700b58418190300c820181c036400021f903a80c90f004a107003075880410030301c11800010029401001510100d0f80001c520324421500c0200c0180d0325000030b01055480fa0040d901c4402d4034051004544e000b0f50320914058003601c4004490a181d400040c1014490700064015806155281d040000c2294801c0c0600012000300b544980c524100030a10b8140c0780007280079011030309022813882c0c0552914000c0404d40c1e802407014440d0f01690750355500c4038031000c07506e500811544540c0c4c21101e010610a4007015501c0d01c0c2c40c2c5140c580e1070034024415a42030414401c5503000c00a00640c41b00901c800550442c1021402043c8880800d0051501315408140300c640030003804101541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812217859 1250 812216609 812216611
    0x405041b0311030c060a0c030c050a080403231b06340302191e021801090c020115050306131a0123030f06161101020409021312030e21010c0206 63
    0x41582104c0b02000342d00c040c050b540c070a014101010a44001903000040d1090404005040c4500142d87c0541c0c210740e0366004541080c0c10458150302d841500c24011205c5101c00721010424000910810b5010b6441e13044007101e525015014840009030100440c030040e107200c810310724854852518041030a6030403182410428114014001c01180d148034000200d0038004c0720350040c0001141d500d841c40c103a0740803446e42c44202c0e040001d2881c5011010320300ca0b5200d000300784450740030a522144650081c01c6450386d800e4882c541b04048018403494600040d42c40e8400c0c001d1800840e2900b4506128040c0541390004041452110002098191031a40780c1c0c81b07038007914804038140002c0340c0b003015118042c24100350540d600c2800081c0086030203000c00c5682042c41e041c074031400c3e202d00d003000b400da80c0140c0212201d0f07078001414004250b0500082402884802e065014180256400501522580300c1c554412048100b0100802d03800007009220441c128000300301c954102c5a001e0340701e4038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812219109 1250 812217859 812217893
    0x24021f0b03071706010b1c0603030908070b1c0b0d061b09080a0308040308070908150117030406020d0302281116030b040204020a20062401020c0405041b03 68
    0x1840500084003c14105160082c040b060084e2419a00303141e524032460b003050507001c41e961801c0c00a1031200c141ca02c00c03040618001d035100d1280710706100d03120b413405503079030700803007a0340c0e001c205040039440340700704009000d62506008203180c41c074140014428144410050703c039609e01489454550001165200b5005107601e501e00e4456540c41501c4e21090404006404505814001400280b141e100590300600784d0801d100020f8888039150328007070400c40c0d154200704000b0010301040005100180950865100440c6094203010009444107244c0e407481040c03680102d080c00b20750045c2c2013600403805e403003040c4842d480b0301c03018000e08550380c0700c190000318012002d0003185456100e9030203082e01d41000030403802c0d40700da9003880700960280003d4000c011142403034242c19100800031002203880c1000030300304c03410300b000c940308120007150840c03d4030300c481007800c000d9980220310f503910b0103000c031000500b43e9218140004111800c0d040c4c00c040704107041000c410406005d410443d091 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812220359 1250 812219109 812219113
    0x16021f0507090609060c060b0111010e1e0105221a0c0a09060302090d030818120d3606060b04060f020f28060615030207050c090124021f0b03 62
    0x5558000130f8407010024003812000034000040ba0b0080b0784e01c2e4000043e0301340d0600d4542d48040421402c1030848c1c00a00410256070040584904584591002c0c03494084d03c4070020000303030516001201ca00108200f600c41c00500804841052004000306090700e8080451143d0a5141141e02d018065001c60b49801c0828004107020508034801e10a40e003c0c1203001d00f00c650000d0301d64a064480384001005807445030a405501c480d0b007a418403000342d40c4150b8590190703c450f41030303628006941800c9001d4507413030f000440505150949620501c85000160812032078460b45090540c05000d6603040000194000030300091700310342c420041e40141c5019800d4890100b03000c400c540e2a03003c095103004148900649815400d40d4001d601e12045218560019010380d58803405001c500d02c4120750750100744e02080c402c0510205000320b03142e51008a8030002c0642c10650803240c9502a40d110855011202818180703a034000c01004006070880000003100c5500c038500080548078030810a1300034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812221609 1250 812220359 812220377
    0x906021206091b0913020708120f010e160806030f071401020d081605212401080f0c131d01090e06040314030a060b030907050405160816021f0507 64
    0x3d04104842c1c83c00c121016000c06140214820412010700215030010386019400c100d100c0c005105100140b444603100d001840803460065100382c0c2072039050340315080041203842040b5030008800456107100c6454206a01c00303445a40221740b4000700010b20a401e849038510102d00d90360440034644140e18240c1c2150000007030303004201c407110000e440e50301015180000c1c181c1c100f400356014040001e441e451a401c28031080200484e207020a1b980000341c018070524004842c0541c042224002c1402e003400b55442c14807040001883d500180004410303600450b200103c181300e240d0500051038000c1c82840790303d06401c158101c6440070700c602280c1501c1d10031705007000e03440464024810344c0c00d51603110001c2c41c41c10044d00c85034030080c070035411183d0361100803821050b0304014500401102c40241203032070a0205000c21510f014281d01901c48040446281142d0710001950303010925203801e840054820b01c06902d40010341030a8002c5041c4065030401c000215486a44548110b5981d0002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812222859 1250 812221609 812221621
    0x90a0b04050916291c1506020607080411062a21070507120501090308060108010f0306090c03021206220215030603070f12061d030a0f0201090602120609 67
    0x510079500f20030b120798041031941005450160310200c2d00d0006494281d601c01050b45021655a03881004900c6816130b00c1c008200c094480c610881418480301d8018003076040c01c0c0031002c1d580c0c5e0001041c00040042d404001410070003281ca8450003071001511198482081d01982c0c608003c60368003800b00f418400360445100c3c2d00000c4d135401c0740d05016003a10242502c042c0c604a00f94017146023595580f141c1c81c4000744c00c02400148440b903a00070b4000160f001620725004004283c05803055042003900001400b00412030710103401280c0d80840c000402c09141d20b0445114040d546c0003075808000e003a0000000a00414070a2058006070052400d44826225080701c560310914082c3d00401060914640c4980e040003c68010700028104e4907401e50b45c090340004d42d4096001840718060800e6003004014950084a8045c18000e444a40703040c030b5001025500d010301c2c0041401c01456911210700d9500070b5019411998000070b065540d4101c4100d100b07031159003651000c0c000e020a02c00106 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812224109 1250 812222859 812222863
    0x512040302010e06181c1a040b070311040b09010201061508010e0f041a071e02160b091521010902130819060509070512010b03010e030a0905010f0e090a0b040509 71
    0x324084031070b10000c0c01d405000c0906c403810035005845050b06a00c0001c960100745541c40c0300782070000c14104501903190901e442d010245003c0c0080c0300b498140004181180b00c140180e50580d020280e1303007516681e0480c0101c0c05011503034000d0b52014030400085081036071181115044e980202070049150310385241c08072144000301c0d00981490600205803030f41801003403025400410b680303040100407440d036140400640800f12500c0c0540d00c5005c2002c1c950500c008c0f8a0024548800f603d4140210b4038081003154940076144000786000003242c87c0b03c51090200101ca00c00c4c060703070f100d28540c9c564002000947c0080249038046407e06070014111f900000c00b100d514181841d020003001d070581e9028040c01003e0100b04160081c108041450303200c04c140380e80711081600000c9940054101030608642c618200410213420401c00401800d8010380301c03030101c6a007881e00b280580c004001c1296141c0c1038600907640440a5802e20181041ca0303044003003580001c5038100581c1e00e07240001743d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812225359 1250 812224109 812224117
    0x20a1e0f17011d03040e182406010c080904020a0302130303230f120a18060f05130c180f020d0e1006050312210f01060f050703090509090a0512040302010e06 69
    0x200342a441044140134078408049807d80105840c20380b1f91440244200050418011500705035078034030b280301a550814100b048803034000c0c1b800e0a068901104c1c544602140748994000c45005540004400140300d10030740c101c074000c41588001030407064503464014203101c8030310b0854007009905107100b0011030b8a02e045035207007902e0243c01440c1640706881500000002050100801d03074680380107044444200c901040c091152000242000d440034102c400c4400160040604000708600c01b00010640e6244000341c508181c0703912000c0b00c400c0b544001401c48490008100c07400494840c0322101260410711004407400c09607888980403280410803100180300d101c2c4e160340220f90280308100000000c00d60392981402d4103c0000e01400c118174007040c213481000403001c0040040203c10b901282041007070803245801454100d40e80c800414080e014054103109208141c041080c070316040042d0400da03941720040c1c5150313072081c40c03d641700c0d50000d100aa02144010009101c0d52506408031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812226609 1250 812225359 812225411
    0x2060c09101206090f021e042607080a0605040b070e01120b010516050c011b0206030714090a0902180d0503040e1f0b03160c020a1e0f1701 61
    0x981c031040340700e82003120000ba02c0710318501d08655416000c142400e8900800c20090071a64000d42d8800002e14444170243c503114521000507000e00c014010407a1801152260181c400b85051520340c07a110b903541820900c0d84020141d2060266404c100b040580100d031089000d0242142e107540c4594003610800811010070740042e0300c210f400302440440d98041d500a03481072600303030309060f40965440d91148621300e05640315071010b150044c03150391102c8071000450700e0125103864120b1075808224680006803003102803108040310781915441c1e02d419240c495a00a1601e40071682c0c540781580298000070149081c0021101301850604003007422410341648036009501c0e00d8984580d803a0b04090140030800001c0038451000303c012404e00818020300446080c16690f410281620503074900107803101c9040c400c21001c4c2c1c80260390f44080764800c41d0910748145440180300400103502e81c2c1a504031503410380307580401140c00b88256030b1024442c4130080c0200400b990b103c0c420701c0211200150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812227859 1250 812226609 812226619
    0x50d02033004120512070f060902010e0d060501090506240a020f07061e03060308120628081509060118060e01060e1806060717070b01060c0302060c09 66
    0x12a080c00c003074814440d241d821039940c101ca1601e281516201e2142e0207540300c00b00700d02902c20020203000d414408019004000d800f0705241815a65441e2407441021501812842e0380301d050740709690040314004034069000346144000e071042d103401d00c01004280210300c0a9481d181c00110b0318100702003040c0098030300741448030195201c50582002c41d8840c2d52410118002c0d17006c0d01c0c3c1003001c03c00000c0d010300220b441c2c2d1b2410700315802042003c1c00c03000c02140205801c09008001107041c501c03c4031443d0b55550003601c242e82c0c0303c00216040e208090f005960031134923612000407070000c002c5d5403016203619009a0700920405041c0e241310600680d10a01240c02c04401046376080c4140d0741c404050360310b2004594640d40340840c05195400341d0000001c136654480135a00c0385400b0000d203500f204482200d99072030030100003080440c000c1d0341004200145a0712401045036000701030320140c6a104006541a40e1909c90050000084880480151150b50302040300301c48040103441c041130000d08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812229109 1250 812227859 812227873
    0x130914160e03031803150f16050708040b1614010209120609030a1d03070621090525090504030203042315220603150e0108060a052518050d0203 63
    0x41c012000b140550251350b8544038030a125020030a403030044034464031080880000780c0c41e200705102e010428814a0404001d803c214400c002110881a02d040c2c804402c000c0343c449660020098030119218409405202c07503c03111200040d05400505411005840681101510f01c8100769142d45c05c0d141c01d41c01c2c1e003060010705c2110b44182e0303c00001c0001d100040d843c41d01e000000c00d0411136150000d10004003d06000b500750920603144c0d0f600d90000e99020400d07400e460701d403680c507011a0000310701840151b44000c940d02c1150b225040c0a4140000100300d071b400c0520300a5917a03803040c07203003d070342c02410100c030b0140b40da03c070380300004191001c0e0a0355a204161205c100080d4001701c040000c0104408840192210396501c1070080c0074603440010745c2d805607548009a4198540c890803058100b20014414044041013194010744030302808201c2d900c406000c1c2502d0880c40b030a214102c12100c2c045002e16910078a01d940b001d140c0c0800030011138407030b41800440c00302c0800203074044e44400c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812230215 1106 812229109 812229127
    0x12030e28060e0103020702040f090302151303230a0309140313170a05100b130621030513030302030d0c02010212010308130914160e0303 60
    0x3540030a0548840c46030300c400311640a4403003040920700e410b4580340d020340c045c2c8240d117900800a112555007444001c00030050680182d0051180c00c0710001d4654a03451502c0c002d4104048114009043c0c3d141942c1a030a040d18203110f4119000b00120500300c3c1c44041d082401c0280e8012440221606000c5030030b100131061560203030030811244040c030b08105110411280b080e401c0d0900174100d070b8500c81c10219540c20140c400e0149a00710000d54405d0751000c3c5041d80100c80c03040241041d180d0b000200c84039070280d91007041e081c4600300070081c9180d190104641c03092416614250388543c030481b07400200d5008401590001c242140030036498010000d64500c144000c5041c4810110105400d05042c40080c080000c0002ca9000107502049103502401c2c1070765050285c41c20040c01c0c48181e00007103034034102c4080c60180b103850351032140e0465144041d008000f03500b000688 = true := by decide +kernel

theorem cover : BRFrame.Cov 812050359 812230215 := by
  have h0 := BRFrame.cov_init 812050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812050359 ≤ n) (h2 : n < 812230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
