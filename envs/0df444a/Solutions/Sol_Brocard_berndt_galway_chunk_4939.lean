-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4939
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:30.264979+00:00
-- url     : https://prove2.me/submissions/143dae22-c9b5-4ba6-aec0-a42bc384ae7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 888129496 ≤ n < 888309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 888130746 1250 888129496 888129503
    0x1b0f1403040923070f11100608100b0a15030f0606030b15040e011412010e10060f0b220b0f0a0f020d091e090e0c03010b09040302070618150c 62
    0x380001040611000c903d0708000f040c0148401d0ba43da255002d0844511407045903000500c0b5030496010a111803c000d00c1c500366244000000c1c629081050343c50070045003c400c1d405c59414074100903050303610441480122206048445405403403c0015001f409020a0440480c2e00d0040002482d0342c054011042c401c1046920507001c02084460320080e005900030240c1c200181d10040c4a0f810616111000e4075000034480ca108a9550103c9800d44910608003042c030707003005030310459600309401030390080c02000703401c02c5c01c2c10f0030040004614002c010940c010210a460000643da601e01c00c8803000d0700c4600c0b05a561005150f4035003400717074441e0f80c6020018041c0c4500410b402d06c08a16a4460800ca03500e20030494644070f1000c0c1000a00c03030642c01d0b01c00300700e000020740314900d10070a43c0e420b24000c09440b20741c072401d0415085175100381046000340e1601d810807000950206106003503580310704000c444403500300300030841c044203908900444c801d040b401c8111590001d42182050b0320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 888131996 1250 888130746 888130751
    0x90907110c090a0e0d0512270d0f1101110d0b1c1208072109060b062d03070c0803280f0506041b1b0605341b0f14030409 53
    0x605c000403107040c0300341c0d407000076840040b2001c214070104c23001c4202d00507612414a10008200756501e24109003128010320041890502d061081903000607819a0001554008102041ca0340382e81041d03d2040351b0300800700303681c0c807000894180d94101c620000c500c640815180d0000880c90700e11841101c06403480085034603140001c0b003151051040003110701d41d90798035201ca980c8051100f0094601c80030f0440301d1030b445500e0004d094544502406040d0080b0340c0071844801c803110300040020280c42c0d41024440c04000b0803c01580041c0040d0a0541c4800419502d0340d4660300500400021021200c40c14910341521803280e541d5088411100c40c0d02d04108800d407500c1041108548004203205110309000d61214089801216885456910044a9146410241d688008548003260704244403c0100c00b141c400c0c1c240c114102c80d0a501844500300c1c101c1100801816004414203211f6005c00c00000e200c08219030003440142d020340c408151184140701d00c03c45c41d141d0b0400e0040c60740c80752 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 888133246 1250 888131996 888132013
    0x41508030408011b140a0306080111040f1703030f0405030705060f041a040309060f030f061706070e0112050a0b03060a05160207050a03142b08060105090907110c090a0e 74
    0x60925490000f040710343c0c0c5a421184080000000d240c6d00006e402505060b0780348800560b0701e500b801078014010400c52456542c40c184450b44040041c0f031313040010106585c04031000c0d0820000116a000201581c0d120250780d5645402c0d4590f04c41e80c0c000801038080d060501c1f09a4554012950246101e0580e950401901c041c1003140c00d00e007181c001e000210300c510100015070188141c4140910249000318000040c5130780c031015540075601c4074103c0c00303041e01c85c0f00040e0000d100b05030700050285008804581110002441225102c080003240c6d40e88601145801070356500104e00414040d080c1c40480c03030b1444564009040c2125030f000030701c0d0911810346000d44041a00e4050b0381b001410312200e10f0079034550741074524590701c10280703030700c03611020403103030b511100114000c05401420940d107030071a454004c0190002410007414001d05208142642c1e540d5084598086901e26100c514100c514020600d8111042a59504526100c0a1102c0000e184d002103001082d840215890b01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 888134496 1250 888133246 888133271
    0x3070f030e09090d0e011d09040c06140a1409040906050f24090c03041106030405031e0a170415020c030c01110a0203160c03080a0e030f03090a1404150803040801 71
    0xc030701c2c0d13034250300000700302c400301a100d036014501d546139461109118405407800c01010986600b420f8905031501d0440c0c020401619500c03800302c1d01c14211401031541002c83e1680003504e40d0421300080c41c07081c80c000c20842140e440c0c0d548500c0019802040070302860074000766849902009403444a4200c40f0b040c980c04140f2482d00481200c4000584200440c0e618055825441c0d0000790040310325060141500c02d1542d590f902030350140b4080c1005d940c0c0d500c0b0400c0300d0300b080d8400e0021001c1301c1c481030000c805480d0b000421054540088070441c051540ea62410081604080000848161002c61284e0300620000003a10901c01c0c8900204405000f100002c0a14014100c88900582c030800444e80c0d1490f0000c14500038610502450620640340d56030154180c00c1440c881d80090402c0392054500e15080111811000e000c0d80035610b007424010110300e008000d40074403401030800380d5805809803120760054641c0d036003e1100f031b0304403900d4071803003522070344a403040d5030301c039801c01c0b611800d078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 888135746 1250 888134496 888134503
    0x160b1f06020106060c08070c050607050f010c0305160c030e03010c09060e09040c05060f0408031206010224160507020a0902120a0b0906010e0f0a030c0612092303070f030e0909 77
    0x280c40540e02c80005c2650780b40d842c5c0440b54001101154100590b030000116501c600c409000d01174421b101410154007400a80fa0845640001c4d0800700360424040c05541120260280d08901852174803000541907410295890300107210056010761804000019081d0b104818500362145c5d030f41e807040f07261070309000c0014034041550003400d26010301a0401c52441c5c41d40c02030408400100e4080d04159171512031078210f4200025079440d55102c0820091107690600a440105030003081242107448100f00d14076640c40d00038154401030ba020904506801d000e18241e55050b83e006081e42451511124124080d40050b0084080f5032120000f1900c003858a0040c40e02e8200094119280d65446100454005459004482d0007142c20072194145490713005130b9a01541c000c110000b4017500d000d0005010302550003400340c0c0b0502d021119000107015005000180c1100d0306029008143d000c180d60851081d1000100721b210301ca51050200b540284006c104107808503400d0110b60f4502240544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 888136996 1250 888135746 888135749
    0x8090f0a0b1903020408190218010f1a0a02100c09050a031505280c0509040207060c0915021902030304051306080601090603020f0d080c2e14010b160b1f06020106 71
    0x201c81d00711805202c40421190751211035240010820110700b40709d030901201da12000e0304000c01c0c80e410720704240082c1e529201c4110349007560441c4a0300c1d01a0000b030094440c00c04003080180140c5a4071880c90301440b441084bc080d10300100300a000c65540d01c0d100785420342d2000020074943c00d12002a025035004000c0803030450708807000c0b1320408444900d1400402d00d5070034a8041c40350078018400240c94034409481194800d01c40040e081c42480400343c441d00640d40040068a06010341c18a003aa0124100000320100300c0c4141c40114144006400e41c000c1e81c03c650307044a980943c2141c04440e40c0c0003c001c6a80010548600c2d0b41c0f502880c02c02ea41d13013070002940220801020144606081006025181c050780e45a41002c0403090386034100710038001d20350700744000881211403400410040c80c0515a00d8442046050100b4487d000c2003041485000145400440c010608014100551340f50355800405c0e60034514007044003010412035803080e00550452158046442c0b40140304030380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 888138246 1250 888136996 888137009
    0x1d060301051303050a02100e0f1506060f0304020604090207030804060b10080106210c03020903070e221416082a0f01020c03070923011208090f0a0b19030204 69
    0x185902c10070f40301a200ca41c40181c0350030452040310440b1984001506c02c01703040c40d902c0405004c80e49003104043d440c3c071348611510142030032402d0030b20425a42c1c07181141c921140e51150147c990b0b950b40002910340c040c1d680450140e07800011407070f04040c1d02c07040c00c91007144544410001078090703074248044071412a0906010680082c01030000c180160104910b440c1000c0c2c0e801030150f59140e0340d200b0398071720124a10201e600482c80202a1801303000e020081c14121403008104e03d032159455a40c0207803d818406070000c00d200d0001030150010020221508082c110307010340b88883c1d500041c500c017500c0f0707a0016000ea0a0121102c1e94100015000c2401f1107103100d03207914044081080241801700000d0540c4212108501103407400c0c86180024500da00c0002041d0014211050b4518100c8001c0b002c5180c41030014003046002c840d41414458012a185458084640c00300302d480c0e050f403031000e510248501d80099200030b840000c0208604c540502740c191581400d040c0d080c0e02a901514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 888139496 1250 888138246 888138271
    0x50702030c040902041803021011090a09152706050105071a07090e010e070201200d02090612040c140a0614160b09030c12041d0901020904061d06030105 67
    0x10005854140c0003100d800b0f000400000700040c0840d8580c03071b00c0d4009401140507801c2402042c100b04200d02c03881808510411015140114050004e4113080b5103006804045940704003021074104003c4840c80501000100c1180d94180b203c4010090020307400c0d0101881c0c184000403a85510800c1a5484a47d02c940d0342240700e4902034201849410081c803a60401218010004046160405050003000303071000046003401c00440007030a40c0d451b05000c2071301c02e14808201c00c071110300c01d04966101960440041c6c841811100090845c4921404001d80386030b08014007043c4882e001001040b1240b045c404025800d01600340a003201c00b82c400c00740880c1c00c3c0f0448040b41c48400c00240040511808804203101c000e95808e203084a00340c0d0071042a9002060050b140b940811091904070303c5115034506242c03428201500e8900c0000c4004130003201100030841400e42501070b1640c803c00100103200a603120480e401c0c0c4684256406252101c941e0041042824103214085c0500c1000700c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 888140746 1250 888139496 888139513
    0x11060a090b181c120605190b0306040209040204030506071211090103110d020705060906060103140c0a030915090b150105071e061506080a0b010806150403171905070203 74
    0x1103035404451801c2180807801804416050ba8968900e03070009501e00792070700c1c02d40002449070035003107481d06d070050f03070065000919084e0344803040c81c0c4400c00c90f280d0001d0160b696072a100400c020f03008141003186c20500200e4048208400417601d40c4c40761201d80d0314112429a400b15860980c0c4200ca100d14400504110340b800301c1d4445d8200924a01e074082d04c07603203000c09001c20392049034041103083e41d850704040284041c02c4400d01c0200e0b044402480c4c24052240c51195411541e10040e1031904031540c000348c5620b00038041e4100803565070b0000d004050070240701410101414128604031115807120000803640c00107804008541441030f50349a0274400d0a5441c100e4141240c03a0241415110765203410000c1c4281c00f846c580c6019101081c0341c4070b4a400d00c040e01c005009044a41c2c0c690502c840114580d80c4102c0c0f0b030b58031070340450300090300c400074003c0c2154600c51508082c0064442c03000000d5100184d030b00500d407480080304a01035802c6041012070700d0b03001e840b00003075064009004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 888141996 1250 888140746 888140761
    0x50103110a0506160f020a0f0501090602011103060904051e030a0f0306080a02011809110d0b060a020a08090a03050f030c0708070e0408071a040b0412140d020a02070b0a11060a090b 79
    0x105204c10600c103480c5d1100c0941d6a4001a240200031f601000708a000c5000c20b02565078800c0303550b0b0040005000a01041c041ea445440041c00018540c50107044224001004d0205c1000700c0c0741d142c0095980c00040c009421b01e000c0e1650300c2222102d002c110704000d6091078501c24450541219050f501074036801059500455102c0d0401584103801c050304000400c010b5441e01c82c80108004410045990740020b60b44203081c9c0b2174507000076216042c180841c10a040c0c01259120b00c10342d000d800256111402c0c0300045030700d40c0e40e0700701500ca03118040c43c05a4101c8004010424280c0c40e500711150710383c0d1485e6041d0303110858094000b916007004013250004054038013814540c1d104080c1c101c84446c809891141d400c00c119001d444c40030300a811301c01401712107407201620070906e18205440c455900e9083c00144143d04030141a2603000030320321074580c4203005641c050301c0d1034010b00380d642c00310603001069100e101c0802d1410703004803808184120844c6c03003080540c5a000041c1000e90799440c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 888143246 1250 888141996 888142027
    0x70b030a0507031d0106080d0c05060402040905030c0d0e211b0102030910031a090c04050d290912040501090306020d0f0203010f09051008060c0705011806050103110a0506 75
    0xb810705051549030071008070300d03001880062048400c02c03000010317a540b4152501e450201c681e591002403141425503440410302c003244c102d62060301031b9808900800c0901e40680b840c49242c0c06a2407a0050305c0103408103035842640100d4510301161310a0b09810880310381c9540b4131800101c0311070b940c000a541d0341400481c1c25072210640050041c0d905110303c0c0004030309880c0001c18603078000b9031340d0b0043c0c2030a1074034008443c00d01e000c1940c0601c010b14184d01e04107007070300c2a4065144a1070218020208025a50295240f8002506007040c032444004009040e0900c0980e075064803409041c40000c580300c4c41e0340c02d54080b1038050f510402158610f07281c0000a501201801100c10384403c0501080c01d49400150b0007010a0314401c10b1841c5401600812904041c5c840c1c072064545620070406082c0008945803c5040112620743c3d0361040e1034070500400d860360007080804207402d844000d011030356000604884c0104ca19800029003802040742411042c0030391684600c0c01c0c00000340c40310b07642 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 888144496 1250 888143246 888143251
    0x903021e030a0b07080a1413060b040905031207050a0e060f27010201060b0f0307030e03160308070e030d0828092a060c1509080310090e070b030a05 65
    0xd589080d400060080424107040c5201001d90b14000f102c01484011680001c0881e8010b403048010403805444090440380000f02410300345101841030401800d00c55030398400e042000c00140104034a85082c07a08a0f1a80c0100d003800059003018000924218010b82c2128030f017030101d031f690003600d4500c9010070206403c80c2c460b0b0707442c41c001031018030b0140b20300c0800681c107187d50120080303411000100080c02d44910f50048440208280110094034119509803a080000c0e4100403079424500280c8901c0c5001d2400340c198080703505c80036603040c150006000b6018451942e03e1b0030940c4149014965104c8449a0306030000700300d10700242545142151004203051142480c1c41c208070031142150a50300940c1c0c0544402c80d2900b0ba140007585d003071946464410034940b20481180c6448001340c01030b890601c1c05000031440700042e1840648590050041c1c1e0b40c401c04050302c81c00c100c0442405100d40d8016080342d01c3c6000e041c005c0021000034110200c4001501d50340c82c594840c1c40000c00ba0001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 888145746 1250 888144496 888144529
    0x70b03010f052106070c3e1903030815220506130908042c01171c030e0105010f181d06010b03150a030201050d09020f0604080f0715090302 61
    0x100c40300d591500f1030501825000700d0b5076a0b9001c1540b840b03401d180d05229034444006c2e9110041810402a1010f10410380c8040a5001c5e840303503c41c464400854080120303550b0000c0d6484015101004040e0400c1c82603000b41200e101c81a20052440d041c05642d20310207880c07103054054440e24550b80040ea0f00015032012026000c0c0b081070020b80040000d03102d54041c2200c1c400c80200d000c1c8800d08101d001d0318181c24140e40014141400c0c0f1005020000040c000c48032490740709611a00d104404100c80b4800b082000c041001803880820024000d01c1c521181511650070180005030624000a40000340c6058801c170400203a0188241c1000303120f00400c0003840c014081c8524690001402154000c00341c030380503a90f8915058010160b002c0100407a075209101d01c0d9414000760b41d0000c02d40f4502c034150030740026a2031a41c000503018580e02001a0360041c0002400302d4003e101042d00309082400380304650030540c40d8061418182c0e54400100f00007080c6074410030146c64485040745c0784610 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 888146996 1250 888145746 888145789
    0x4091a06040b040806090a03081801060b0a08190e0c06070501060906060302070b0f0705070803090c0907030f0c0c1509081c0501210507180213090e070b03010f05 71
    0x128081811030700140d20150320031001280c20004c0140c00e21995500810040251600d03815641e0060041600540b10b803046895611031142b9402c025480030004c0c0a4511201c5d4803001d410300000c129000444092511500201116400055074000c0041c001c0000c005040303031580c0340051000c0c64112030b40a83c1c5664898500003a0201d85102d0f180c0640100c0da40542e40e40c3d520704140c03682d030102070f210101c1300c40c00781c0c2041220381d0f00c102904c50b401c0d4052409a900e07114651845d1900c0302c1d0b5081b5130b0b84444540107001c1041c5c2c0560040884284015090220040c441000c1e1800014a0780c06082c1310003e41c88010310003129440100d01510846455003007554000700900c140e60350507100032603580d40308014010700550000c1c0300d0400c43d4000c419200c8009541d0340c25155141c41c480d01c08800710b1700700281d0026074503406403108400700d846844200b42d42c9002800182c0302102680740580035814010800161100c1107a050707139000161940d40502e402c041c03100ca40c084410070000c036003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 888148246 1250 888146996 888147041
    0x161e08070302091503270d05030a0b040c080901050903340c03060207051005040827060f1801020a0302150a0b0d0b060a081917090d05031b010605060409 67
    0x5803074404113403800854010407502e07071030009800640341d000414006010340c80c1c8100554400c01c001040d100c20708003403502d0703510307038942c1c9076060041d04031441d2030f55016041115107004a80d000c2e5800e0b00c036a01410081c84542c440da10415164420715400c807118500da09030840d1040b0384400d1045d510310324a2030b080d03801e00f010b89038110b0b845503075081103810640004a44080c00340810a0100c48072841d0402c0145007026500c0040358461200d00b500e00d64075020640031040303034004c405425100054040c65540307070408182d02e003903071003900201d0b036602c10302c111b440b65540f00041000c55154903400414041c1080000c1541d07500c001422801d40c180c680781d000d1402c1d2109040e003030400b4402d103040c1c4810b0500b41c003001102c044e181c200c40031307650140e4482007061a000f07500c5814580c0090420248440703810000243c3d1048488240d003110f010310109081100c004020400000060009540d26480310b1416003a2207003440f036181e01c032009200070f205c00d03061607000d0803502c48501030388800503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 888149496 1250 888148246 888148249
    0xa03110324060d1e0c0203180d05010b040e0c01180e060d110d11130c140a0203071b030212122b060603020a0207050f0d060b01050c010f05161e0807030209 68
    0x1918120391307038034112880a20321540e007100c602808044803000e001a50900042a0f0402d40c044c000f03401c400e101340c8001403410705110081d880303081d0800d030190050041c08034824200341d4850000c5030190000d120089142c815580002111040d540d07250341358286a2242c100300801c1ca11203040640c3d4130200c1199940caa9a55040700c25600c0b8030401c0b6600c000090f030020010420a6012159045401c118910001d1a4400b1440158541d00202c9544a520010080380340d805144e400400c2070140141031100e420010f040403040b0380c4201c8e00b000d4800c0501c0c5c0d040351280305200e0001502c0900b07002b0107600d03958032071a03640c11400311250351910403913550380358094850541c06040465400250000a00e90601440300a440c0548000083c038505001044e01003600c0c10001d004541c1d1a203030a05c3c0780e0320610442d400043c2542c000d1102d0b060503a000c800405040d41c20200d40c00c01c0c0d002203982e550081400a444030781c402d1903800c42d1084000140c1e0a490024a802c003015820001c088e152b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 888150746 1250 888149496 888149501
    0xd0305030415150e073b180f100b0d05070e19080f0304030203070509041a040515011401020312041707030201050a0b061903090f0b0403050a03110324060d 68
    0x2450305030340009400a1801d404440078603809005c400800070051084840c140c2200542c48140e034400100110748400108641d9000440124890303100c141c070300b0088542072410b03100d18010f000d01104a141c544a03280e002340c9020151280b0320842c0828007040e403425100e07a2050390702c5045410700f8101c01126000143c09203c0764038049a010204c400144409a030400c100c50b00740004000640c6441d007590002541c07041c2510919101b12040d900003010051121800c0b41d80000a4554000c1410f1506d80151a64a140b941900040c2d80c00300001c2e20b44050940e0050606043c1c0141d40340c402c0c1100c2000c000c2034024008e03540c2c845001c0383c0c404034810090090038106c0c003a07400000e0b282460074104095809072340c8110701c02c800070300194094608400004000146e942030010303029006150a16001001050140804000308100700525800000030013104015590401805e800c01c2890b548502054461901071074180381c6100782038080da180d00d140c00340d006284a04204890800005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 888151996 1250 888150746 888150761
    0x612020412060203040309060f0e040509030c0f07150831081801090e040302071502010f0908030406140c1603051213051207120503131a01050f030a020d0305030415 72
    0x32002c3d4000100824503921245034009450285800132100000003002880701c540503480612503946c0b100407402481c0104226415140060700752004286018102e58554003540700d00320343d810303842119165580c491b444981c414450100310714810041052a0940c1d00016208e030402c1c1654044800003003040c000c050306091f1030b510404604030603460001450304003603500001c010b9080c00280300010b43c002c140c6130181e4001034100c8501d0022500304a016104c4100d02e1881146409190424401800c00652003140078841c24800d00c06641b194038890300003101d1052009005008500c88001c8140d0482140e60207494558200003032440c02e04480542680e0600311400e801c4880b1040020174005080046984814107007403041d40d03113628460b030b1004140e05040080001c00210f00902c0035034280500b5406c06180e00224090000407108000d00380503840c071484160700c8074a05481c000078800300480d8042d0003414048010740c0c003640c01e900090402c8501610050301d15920940a201d28403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 888153246 1250 888151996 888152003
    0x18080f0702030106090f0b0103020304021521011203030506060a0914011701080a1a0f1302130218040b03030f0403020405060a030f060b04050f13021302040b041404110c070612020412 80
    0x60216024264001f10b803441001d1505140c01402080056610078900c00350001e8001c000d1580c0d40d00040300100c4040f40e040c010100e031030029001054185000080001c618482d80341040162103840400519000c0d1883d5040000c014220034001c032400e00e00d0307200788208181447c080c08284034500c03074280c5000340c0210802e5401540d407074091082801c80298804500404490181016903452818100c0204000c18541d040c80d009070464548042841803145104070441d1188690010006060500d118403449241080400d084a2801000b102c04404a943d440d500d4240355909000140c0320060409034407088040d0008045805100c0855546109240007e41101180300300411520080d0405500900310340c100314507001d500311105c0345c407501140d1210000304e40101c1c0300082c0c802d42d081101e54031030108000030722801c0c6011031205044100c0e8180324012000e14203481c02d0148a400c503000d640f01d26800c1080e1800b50602c20050b69400da805481d154640b141d12103901403140007203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 888154496 1250 888153246 888153251
    0x13140723040b1201090618020c03070209090105071e21090804120c0b03060f010c0f081317060f010b0c010902030d0504091508060c0c16060c140118080f070203010609 73
    0x194002500f100c028054110072008000c0582820500c0c400001e0545513041d030650300140d041107141c4100151400e00707600030003330516481c0c40c808144c0038010507942c50000c282d503c0c00c0104541e05151050780c000d0001d6480002e899920040700d040944d500d000001800c0d600c180690100b89000c000304054010000310803190556450700b10f01017481540806101c3c43e05000340b184a43d40e81182c03000b03a04003480e244c2c98491482c28005442c074103001008001d0200040c08072080041004258201e60162241143d8407580420f0551203000c201c0705203094941c010018083d911000024028003602038000140040032907003c0303464100b00444038404554049010011841203003d03004201039200c0d649140203160a10342a51280e0180c4141c011340c0c00450303c426000c100b04480c0a16441d0139485615403980d560024040005448060b52401c4118030f007c0354480050041012904140c110b8846000751510b4640d02e0b6008441c80000300300d400c21241000d640d0901800c40079100c1407400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 888155746 1250 888154496 888154507
    0x121802150c060c09010f081905091b04050f0406090f050706030605041a030d03110903070f09050708040b040807140609060603011b05070206071a010603090213140723040b 75
    0x10902d4100e000700160a00101004103000d00d9902132486084000d940c2003488280d11400c4c04642d10045071410350400f03600c1c000c00c000d0103d100180001e40c0c503102e221080348581010090000b1750304111034030110700c9074040200700002d8081d8071003401d950041069550845043c0d4031141484002d90141d00000d444000900c207a282501c1062000c20035200c034003041c1e00c0c1180c046070302c1d40e6104681c0c00516030348800c0310348003010200c00ca0b0703d4100010141e030545134451520450b141401c2c020345071101e182600044a16006040082c052a004900c94515a5540c2e1301c0a9460388036150480e07a084003100035901400d0b0800c481c500508445c2c002d0100b920303200c0b040c503003103c0e003106500c9074904801c0d00c045545034228003100c21003038054445982c2c4011604294a4041c1c2e074109890901c8415000000d0780c0340e259110710280b034422550080c00044902214060310001c4074041503090421010811140c000e24011812035240d8140055118001e507101d036003a04190311524400da0001071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 888156996 1250 888155746 888155767
    0x1902040b1303050717060406050c0408160e01090b0d141e0c120d0e010302090418050d03050907051e011818050c12071d0d0f06050f0712180215 63
    0x11344800392200c0d04440d61101000044540c0d1181c020b840a0a403641e03590100381c101055104507005005104116015141d0300b820b00000d0700740d280b2501d6100450744001090050071805210b03000c040091040401444135241c42c02c0324110350300003030a40e1240c12810070681566290030200d00d061103000c0e140d200804400e020b05132034840b001c001e458101c40c21664400703030400c1c002c0d12415000c2c6001a21800c2103404280202140c00c440d000b5048018070000406c03c0c000340303030203a038202c4d030380d081c0401e0b10b44000495481200780505a80145540040146100c104203003076540c56051420503048211840b4031880f0070b20702d4002502040c00c42c00b21912403481d50098a0f013110480e1366081c5031019174114001c60210140c100e0041107092185950441c1c450078015045490080003a08402003d16002481e04222041103540c00d04050010700c16105513004240310300d140d5100d0214119000f500c43c401070842410032316901100c03401042c09a25034031480c040241503455542d80d60000180d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 888158246 1250 888156996 888157003
    0x30b010303031a01050417030409240f030201022e050108010c030e0303090a02120709020a0309060f0c090302210a110f0d170a1101151403070e1902040b130305 70
    0x10f4049028040320b071240141d90342c0c0305046400f1240c0044414004122450000c1e040d03203e141d201c50b0942d4140350700c41c1d510b100582c0d82a2911072030301d0240d01480c0e540c1c000101da0310700940f00c003a001d6003006101128880e1040c06045144545050352580c406c0b80444040881e030080e0000340c0d45079540c01a0301d081681500c40e00040c07807204e030700441c110b00e00781c25103a5640c131024600074080d0b4a450000c00385540101b0450000e007003801700540d21240c03540e200400030007030b81100f500c1c1e450034000017000308440e504c281d00030a6040e40d1455034490440e003c0c030140986440701001c2d1851841501c0e01c4680003400704010701d5200d00d412103403000c60300080000300f0485450040c45102400d80074000210008207180f128042101c030aa2a4000500b0541c2c040c032014110b8507803942003240070440074020801000556081d8072940010302086010700d42d560000f8040c0170311488a9002141c24071000480c6189a9400010701500c4c20b500c2c0d8041003425000082000d9061105c3c0000740700b000f0342071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 888159496 1250 888158246 888158261
    0x140d1e060b041e0f02071e0b1b1902030c0a0b040b06040501050306011701140705070b1006140702040605040908041701050c070b0601021e1b030a02030703082101030b01030303 77
    0x100d40600016260700c0124034030701c0586a4000f94184d940e40320301000181601681c401903040504002150354040e0412003c07103841c001115825102c1000880d01c5010f400b0103010810030660190a04140f0011500300100121142e0b0940c802400300b00c4410344c2c00c0140e1100300d446000301900c40e042070700e0020100c9401038003c030701c183e051a006006a44000440604590f4103c10301e0380d0f80748010345645e004100c800142d00504020b0010001801c0c4c0000003001c60350310a45190b4040d90b1401d0020f0b241940c28021000040d0340e00003200000032a80025101140c0018000210541d40302d002034100c0b0804a001c42d8144002301d4100040340000d1280801594584000d01552414203201e40e4079108804005108600000204410307910130090100410000b0400d100b82c0380e6928951952030b0646c030121401d41c80104c840302c10301d040202d400d03509154042c0081028a003550355120868000c03d51031140180d03200f96800c60704581c450418025401001d2880165045040080541341c48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 888160746 1250 888159496 888159499
    0x503030a0e07090b092a0304030f1b12180e0a050412020c010e01031d10050a0b0a080c060a1803080a0801080102030f010506130b12010602070e01080304140d1e060b 72
    0x4104c0401c0c03880d2150500194400345100b44440510102c42d2000c04440c0c444030a415102030200c2004201a0404003414903030300207488000030003408500000d10711030070402c02000440303081500413900d4020a9206501c0b102601c05000ac036031202505440c0c003104840b021031094540341804180300d074642c00780c00d04030000d10140000c45074243c0041c01d850902c0c02031904059441040c2c1c10041c0e2090780300800c04074400140c800500704035602401509003561a20142460840b03003040500d0f0446a403001c645052001d028100340480400445d90000381c602424800d140400d08280c00c03a0350414005544140111901e03545103450007070a8020581001c1035503841007080c4401c64800841c1e40b411618200c510907138480c142e444d1120807045503408108181700100305100305011503034081d03040c2c0b02c1c160300725801990340c0c000c1a0305a510a10401d00b45d60010001400460300201500302c81d4030000e024242c11a00700c1e6078680303851401d0101c542c501c1c07581c2d486140401040e4041d50149540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 888161996 1250 888160746 888160751
    0x40f0c090f030b06090604090206160c05060a17040f0515090d030c0804060b12030f0409050a06050918011d0d02010c05181e04050408040e0703140f0709030503030a0e0709 75
    0x10b5903924800600d0141c4014419200072000444545d581d412009865038068110b5455450055440c0e51400c2d00c4030044a20803840d40c800720b80c0d410320800307030351280500785e40b0b00d88032070300005070112003100140054074021801c88055000c02c0d0100200c80714124040180451441c0c48900700d400c2c9011982124201818a2101c0ca4142da101e440603403c15040b200005801a0b89000a20580c4411000024600002c646204a80c6040d00038008488500000f03020560303e894440f41100d400e401a9035000c620a004036043c40b040a405540802c1ca0000004140c0364140c1244082400390741c00c9603460307100342000b103443c2c0d40c20f0180115441c1d43d420454202002c800d00ba00c0c585006140d2036000c0c4941d800e494581082d66a80064500b001410030404c41c141420500c2c0e89a02c180581103609406a001c507a40f0b620a109449803001d48109407440c0f91100b001c0c810008101420300700c00c01401e51001300c0861000e0005500810520400094000070500c41300d0400641e030b030110b4078091 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 888163246 1250 888161996 888161999
    0x8070b090601030b072f0d020f0a08031306150b0a120911150d0204080a0302150c0403110303070203120316080421021609060e0a0504020a0e15040f0c090f 68
    0x1d113514000c030f03000000e909101e07040070f0f80550b804194180751100004084810340d00c10440b01c2d001b0070301e06050b502d1942071360b84507021100c407203640c0da0250340e004010702c2081002a030781c4603035552040b69280c81910007184200c3d0314070301c1c0313004d0311116004003403010300000d82d414041da00701084c0c40008a4880090045020584410030303458880c034401713401007005802440d0240310640c112200c4131901202151569250b200e00742e82d410514108801612a000c004420700a140240505c11390355605070303030700d007a003540d071284001c5858440460f003510082c445a40103a8040c030000500c0142a0703005501c0c2d1800103454220f1400102c1c007441440700705010f03c000310788216210741200e82c6100024445c0a001c0908924102960010001c580010740f008200e25885400940843d200c2800d507410701c0c1c0b01d04105034100c500a640003544103940a40c1040034414a81e8020340c006004980503003240d00d03150101d800d482003050900f000940e00e00e8030058841c2c0040d1207070041c05900c0001203109 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 888164496 1250 888163246 888163253
    0xa12030503010609081b1504030b0405030406030c0216060509040608190c0512030d020c07050a0603020309010c031109010c030e04061706010608060a09050c090607050c1e0a030611130308070b09060103 88
    0x20b086c050308413030181c05c404407242c1070000200c0444004503484074150001d440c06051650300c03600140900800030b800d0035034600d4414030002c1c508551103000c80b07082c90181e24040007656175601c40d055658100c0e4a40d07100040548051295040013882d2200ba058804220302e4454080c0c4415040700384140800010b8240d46580001501d0104501540040c1d40b80201e03c1180d142285507407015601900e20080410b44940c190080d60042360108000d106c0880540c805800750303090030000100790031090111965640c032400f01d02808038041d0401005009202010030103031070b481d41101d050000000403031080c0200401c151401040e02c0d24000e04941044000070b4183d040d20f04c203103038481d034071040880c1c0d6041e83c0c0d00c21076010000c01042d241d500d03441c500d491902c8020580e1018070030300c2e00380076040b140c41d00b030841c1b25070800e4010a000780c02800e542e154002880320305940a107103c014424000e4001c81000c8100265018130f0780d042e100c2c011490102e0548800030502d05240d0080001007001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 888165746 1250 888164496 888164533
    0x20f040311040603060203090a06060501090612020a1707020708070b0f091e0d1a06010c0b1909060908041a090607080c0a022d040603200a1203050301060908 69
    0x40c0d07a40074003251405815200094041c1c601030b000170b0030300b034400024070440c840e0020724a03501c2441180e09011250b641c000540300c4600600c05c540100307100018100020707500b0740c001e004126050034160b0500c1c00005007801c2d07266040344d4038400350f8481d0b0350505c04094100f00c10001812008201460075070402e44550403801140000f82c020000994042d040c0741b0038001d007110085002d05a010311003c00d04000807030220709600c1c05592807801005c20703043d51044101000e0700743c01c2044013076661148420961141a6244040708099441203450006141c500507461600c1c01020060b854500304588090303c150000100d00c50148100f005044030348805e0252010203411216081d16603030a14030007800e0080000000b540050452002c45400c103080105c1002907101041c48040300a9000511003252244d02000d4091046c1041ca20039003015003140154644000d00403641c019a070700a4141d032080c0c3d0b0032003200400d90100060110a5001030b104004003540c1e4010580070410b4200900b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 888166996 1250 888165746 888165749
    0x519092d0b0a11190b012103050a0e09040503030106020d051603080a06180e120705250b1803100605010806010e010905060408010608010c4b050c0f01020f04 69
    0x180040003042041c10030f0300070108400a2a500390039280030314404c03089503014600320f0b4422162003c03040d0000c070344d45211750340c030001100102407103050000381c60f20181c0305500080900b000f00402e84003030902c2500c4090712503004500c180b000310380365414680c01074141703400f0003107010030020180950080c030421840c0c0c45035a41d42508100d445600d400043d58040c05068106d0420b000008401d04000500c0e580100500c007915070a07610104d104c070b400301c40d46201e950070181c11a4841e144002440c0884403251244038940c0d031000b0000c0d80e81c1c07180920b268019441c418120301454000c4022070074140f014546c0c8209110381006120306207c00a0b1029001620a81c10401304c1500c0f071550340d024580b410050500100015143d030340ea4100107010702194083d15031203509010117a030324280942c1c0d0507500a040301c140c3c00641140f210b004007a003240810910081014440c94124112003003415044d00841076441513500d5265480703884c9031030f489a030030b225241e1042000c0d0304800e0207441500c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 888168246 1250 888166996 888167009
    0x42f130e19150c090b1909080321060f03060408070302012003071209020a081b041a12010f0501090914070f060c02030c0a0801022104020310020a0519092d 68
    0x3d40303800f07504000c84825100b0b81103042140e20005200101c1c640c0d200045080381d9003035488070b01c0306e82c4528484c0d8890082e0350710215415002c003241100f011000b800703641e0020001d040303500c07691102c030b00083c83d0503419502501c428500207000300c1030660a0160036103901900c01e190300807050281c00790b4180e105c01040b01d0104400c0308902c0d034100110784c01400c141078000b0416554291202c2c8525114280d0a2484048800311012014242070a000e081558901c1e00e1011611031810002d2150000e0092040c920035543c1d100e8001150240c1e11a5074041c080762040065000c146250600700300d03203051000243c0383d010a0007000608020b550348006d60301c052421007088040381c40403038a0800a4924070368020303072041020801c95015400f6011160402804280c0000c4818005e42c1c04082a6006501504151400c12000f801600140700c1c186061034402d160040e0a05030b0701c2c0740e5805c0c420b10310001f40d83c0b4604001841c02c46e00c049648040081980355840325074500301180c20914070a06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 888169496 1250 888168246 888168251
    0x51e060f0618070807170606180a090e030a17090606041104090f020a18030b070807170405060f0c091c05240604060e042f130e1915 58
    0x40d6454603188030b0704006640d8400c0c0c10001e41440e49024081c560201c1d0340200144c0311002c900c2a600d52010128011300c0041c0c40c1614006149103240d001d140c5504045802000349240028010717400e05c50360300502d0348000075640f01d4400d82c800800505440070082a0b1a280c2c6080c0b00d00c3d0b520218015401040440f0000b032480710b9081020910700480e401005003034502000368503081080d030010042c0c0da50a941341c800e14005692180c2200b000d50201411101140f070006401c40c0c028840b9541041080c00d0600c3c40c0189181c081c45580c5084030101e0305a0031901c05c1c0881550181d2003240c00024080381541450603c501248540040d002c4803c1110308041c0e11303205200080c8682c1e0760000d803e0b1900164031450100003801c0600641d07049024524010000503104a076a86690140364445000380258010990129000301d014031040d01e404501650503481c0c0d0313948145102f041004d92400300f444280740c0c005505220355451000089030039102180c000801c0450700c10300d0b404512800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 888170746 1250 888169496 888169501
    0x23090403120b03100e062a030403050327100b010305090d0521010320010314060103090c090e070f050d11011b0f0305031602010b1c03030e0a0f051e060f 67
    0x3d180070400072013084081d00d4512405441500450000e10070000115051400d80c003190015080d6035882c10a803403950030910210b40082c0c841d000446d0844074a00d030300a16a000594440e40c2c0c00101c080191580c0c1c010b010b003c90306600c078090421510400d00b410046454030090181c0c9466100c0c0260741041800904651900d45007142c100c1281221741000c810703507031286801c210441401500d010f813620440ca2110b1030b03601c00e004400a040350003104014640320f600065020f403200c100201d0b60068243e03400b140a007010700c542201c11000d403000385441490210610940c910a0300000d008254041031500815a2082c601803820828644190201440f002031519115078001c000c1aa50800910000745903122000c2d501448001e440314010025031803043e422902111402c54202081c5203001190710b0880d800e0094150203400c01103180c101d828032590800800580c00c039a403c01c1c580e18001440310030040a50601d04900380707202c02c0014203164a5490744014032105403462442c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 888171996 1250 888170746 888170749
    0x3040603020f0442050904110c01091101090b07260c060c09150a1e050c030d09030e0102030a090b03180a2102121b0c030723090403120b 60
    0x442d801060300d80ca80444c460295070b480b2494000c01c3c90a40340704072003005890000c000f001141503410001e9100ca5207080c91403400c1c0409415620031407121680c040c0700130100b008080c0101081144a00001c42d040705c00c10001511030500f0f0b420038500c0000030b010b44000180311001e1141950400c0311002e500c2030a130390303a41e030340c5106100003014180103090901201c411403102a203110b04e42240c3d8a68114209807081075140200303040040001c241d42e8030031044000d68030429aa00950f440c044d0320b40b00381102420328581c4050080b01200340e0351402c240515a01c2050388504000910280d0f2901149540040600000340100e074208000000032420b9025015044c192150301c40080c0c481529650900403840035521000c80300603101076089900c031901c0400c40d8507440015103a82030902320042c0e18035074030280d40034094036144900321035101c1540d41040444020010403000302c41c008502a1109000b000804455001d03800c0c1005200008c3c0c4c000900e40e032000c06030311000907001002d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 888173246 1250 888171996 888172027
    0x2030706020f07050d0e03070b210c0c0a03080108070902030c04060822080a03061a22090510030c0e0f0109020d060b040f030b0f0402010f0513050a09050f0a0e0304060302 75
    0x3e1009100740300e0303800099400398105491720303045a003c03400e89001304d50b81e8081c0034141c440c0f014600c2d02c01c603800304a0000b010030094a00c0d0040651200c0c1d500345200c0b548002c1c0351401000707064010130820b10042050010400000002d004c00380001c5d42141803079415400c0d14007a502651040c42071000010701d0307003503214000c1460907441400b1014104242d08000d02c0343c2e480082030034002400d00380040756003614000700703420741c1000315900c918003285011528611911030520404100164500041203031560142901030302c140405c1405152640c50250002c0e11030b54800986100010100998404611b02d91411506102e401595404400b070154001300081c4c1c010b07a40d900f001140110f03005038201181001e5901c00c03504900326481e83c1c44444001c190450700280041d012a80c00c24103980310300080d240294410400ca2a00b0780c5440004d08440119000000301d0b42c2c0c0d480400001c04224060180c010440395002c111034280403200c66224807990140780217160b00010f05070051203806 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 888174496 1250 888173246 888173257
    0x4200702100210020331120f18030606081006030f1101032408121c02070503041802030415050906180c040e0d180b0301030b06181501020f070602030706020f 69
    0x10110b54900c0d0096891340e04980980c0502d820303500310b5604040d4074140b0b4819140254007c1e1504400c0401c042e4200c0d001e4900b20700c001c08210144010a0000e5880191240554401e00005ca0340300d017000341171850410b4030549a841942011002c10202c0d0304031881000ca1508181101030f100a0744005070050081500e83d2400312035030303d2455030700314112900721042e2000c1c0c1090303030501c95500c07841c40c40b1400381c000301c840501c00c12034020b00b00d1b0b1100d0b0b005103581441a020761b428950b503002d00c840902000da03011079402d0340010401c801c100c800508180c110382650002c0140e4100076070381030798540d0024440b00e00d400c40151040f02e801d40070015580001401001407004151000089403a400718088080104150070980390300c03803a59401a80590302ca42255034116861501c400e101d00001820a5801c481402c0010720317506407091394a842010025001c4900701a288002864120310100c0d800154004080034050107501004031174850390451000b58580300000d4241030540b14a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 888175746 1250 888174496 888174523
    0x1a06040207020d050a0b0c0c07050d0c080709060603052503050a0f09032001020c0d12090f03110606040e0a030809070510020703050c0d02060703050a091a0702042007021002 76
    0xa0183c800c110f000910140b5842c0f1400d0700b08981d445c2d480307002c812030181c18040001030300400814400760404014540c0c4a40c002e0f008040b885907640c075407604005454202401e21925500f040c425182c041c011141c2055048403a21341a07502c0d0742d8100054035102d4401420036071200c0100c0d030901c1c6076412450035400c1c0b803042040041e4003403a0207011000004104000e05c0c0b006000091044018826188040d152001903c68001511000c89041c41c90f174041048485d9140d00c003030301080064520500c01c0c0e03c0ba44800040342d089541c0d0714508000100000c6c07040d0700f040e4006007210404140d0001082c0d01d4202805140c0f078011311a4205066a00b000c0d410461161002d4030a503170008010b4100c1e4081d205480101402c1001d00c441d00b084808081d4120001b0426003002910500041c00c040e0300303600d48401501e840305e400418907a0001d496450611010a5480030340ca8513101c0e4200d410303c1028107a21030300b1b000348440624000c6070f0700030b0321540c02201100c807000e0003848444481001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 888176996 1250 888175746 888175759
    0x40f0f020d060501110109020a030b19050c0c100924200a26061e0907051902060f1506040924060c0201080c0a022a0306070c1a0604020702 61
    0x403614014004206034490f450020329a035400702c5210300e040c4915400c2d41e40191010341044c0c10f43e2660030b8005005000880c1c0007a40e2411403000c1e804034850540284500850705544038130680701107140210085c100b01c06246010142c00014104141c6c0403031900100c64101101c00215034550003c240d10105220203501200004052140f044000d15a105990301c07030001440e289403940c820540103400e101540040384011074002c3c942500144001c1c0d08105000349100c4c1900c0100d000d802090f54540c001c0303000804c0303006c80140901c1030310551449500c0141043d182003100200464805800110440424030303c480060702c40d0403c9034040d103104003007400740005020050f48030b207110410608d079140308040c0c041641c81c8541e4004030034607016520844151500b1002d0902e03030b8025450b090235071042c01c40c400f0080d858004d030745240c09130202c41c4468514401c13061506201e0002c144c00e04006001d025840000c084409540141080031100d020550b10007021800074841c0d2400a94840f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 888178246 1250 888176996 888177007
    0x91003021e15030408040e0a0b0d0c090e0c010e040c020a0b0415060506040b27181012050316020102030403061a240702150409020a080f01140f040f0f02 67
    0x710029030344555040103070b981d1220900318040121541c04140d800602d0324204101c1001030b00a13a540d580d4210502c0480040c4036040307000040d401049500d01212a41102441004084900d220700c645c00d0050b00090014840b038900000c03d400c0e40c0212040c480e0ba51040400a424804c220b00e841842d4800e0725000c031810a410040081072003d80714000395410910080380034140310040c3c5007220505c0c001700303062191035030000c260211050080030f500386007103010100395030710a0051401ca48600c0941500d50510f2408a0b800c0b43c400e070820600540c0412074107000600c0007084403101841c0718240d40b024400d038030041f0f0441c89142e00140c4036034100042c00040e802001c10550312850200c5900090744000d180355a1000a0300c150302c02100350070300009002d81002100b0603400b0304601d0000340b800d40c5950024040fa00803013990b100243d0200c04000103242f4074200c003800b4041e00014000d580040c4d4001800266040c88481e0240d6201c030f40003203511200d50045500c04408003429521030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 888179496 1250 888178246 888178279
    0x504020f0909121b011d010c020304031e110307121e0f03050f0c031902010b090f130204090501020a1e08091e01090210030b03070524070515010e0103141b09100302 72
    0x140c0c00101b001d0040d443c0000920300d50340004100c404a950080306a8101b4516429480541510080c161525040301c259040969018405230f400f42400480c5122414040d0900580d912501074070441150755608402e8049220702518120250745441c009690b601c1507882103c160203101042081c40c803000c03d0311072940b184043e00c04800d05955008202c80c004900c204000b14009803541c41c00c918940d4041041c0e40c00015a410704680058004039142c984d50f41c40c05d0890f4010390810000402e4030b450010003222849480703014025914004810b8106104465240d556003980341003815404ea0030501d000344e007900031154a0741c004058405216900f24085d015004d0600c0a40c8240104640441c00d89014001074001b051215103280c40302a101c94464126480034078151001e00ca807091000c0e00150800020f40030b0407041003080d45a500d54900b03030f40030101d820300a603010303040100018010401c90214240c0c401c400c0300d00410b07030b84070f6004010746850b03942c01c040d4001c0c034032007450600c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888180746 1250 888179496 888179531
    0x6270332031c14041101091206050f01150509100e100207090609090816170309030a14250c05040903050c06010807180209220504020f0909121b01 64
    0x150301c0070403401c148002c56124080b04940510114002c2c0200c1e49003c14003007543c10982040860060501c0010181c0b10701640481141c050411121b9079194010400b0503503c0440a074010440c03c805501d19201003200a801030240704141c40c0940724100004d48224401c4103188825003015122941d0701484441c000c0d00e8035081e024a03001c0c0d90034417070000f91100c224481d01c0c4070075801011007410107894010b919003c25010b40250f80e8034500601d401118004180250701603078a6800a694580302110040e00380600d0071707000d20a0903814000110586029500d07410122a85a04035245408618100c0181d6070550003540d0020300d8100e400041580042c014950303210300c1701c11120280e984070f905030798401c02070168586850303808120324420805600504060340008001200e00759048102618400f0180081d2101070740340c00c117010941c14940800c414012040c1c074946010315000d43e00943da5603220080c2d1404100020701401122541c420303100a2159001c001e101e12203102d60302007003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888181996 1250 888180746 888180757
    0x140a05070f0c061d0319020d05010204092901051c0c0207090e01022106010c15020d020a0e3307030c120207060809030406080610020c03160627033203 66
    0x135144200c41d05042c2c03400090a184105112104514040700e60b400e2001084406500700d40541d02480040f0300f260460180b0a4200990300710001c10001d01d002003551b6036840071400381030001c10007400f2507007140e1007080c400a0b4690325003c03610f8408040100e02e40410350b401100124031b4040d80c00c9044606400070702c6044400b08003100c9801034000d10b131034004401e4400c2ca010441200e81030700024242c0d00c070044400482d0100505200072040d91006a80c0b1046000000544c0d00054800714038004603007011001e001008080000702905612079480410b220380088014040741039401c15200d0040c0920950f40020030000700d100801d800b96403948a80242d101046107100041c002c0c40000040d54121003003680c95110b692190000d01820704d032044074100c210f0091035108a0030352820029003140d44003803a100000c841c50070b000100482000d400381002008114018150410518900e6043ea604021070200480000c030100203103120b03030801360389218030b280c04d030002a8030701202900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888183246 1250 888181996 888182027
    0xc0c0b0a05010f0504020405100305070221041a09130506040b0a08010f0b0306040b0604110708031f060306030506220516081204031a18010f0905010c140a05070f0c06 73
    0x3e8003503100d41c104002e0303000328020a908020706003140c61045200e03130005a0006403074016948041480b8a4008020607861160900b5984c006010800c1640400b070303240020300603601250502460000050689000c0491030300442d841d0b001140841c4c2c0c2d0365214051003070303004010b00b24035542d0301c442d40e001e8106181030700e0945d40350a24000c141d00f00070076464400c03940012004555030304c0d4010003008114840348000f0710501804500c00044580c401035010748003c800d8034020a01d40d200e407c0c003a2600d83c004008140c00c1210400008000044868000203030b040d003601156195001100300c450743c03501c041c0040c4070f4a03c03040d44092480d030702c00c0305841c90308060b910611802d03a803589841c0b1907480002e019030790341c640d070018807040c48400ca500304404400740c44080400e01d48590a462a10200c1c1c810140d4039210030003008005d2142220504690406034082c14100620500d0b5015900300c4009101000a11b0020401c5010000c1d03207881d4000e240301055034440340010a2000c0c0c035510b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888184496 1250 888183246 888183269
    0xa090e0607020c1c0602070b0703020d051b2b180b070c0b01050607020103090c470a02030403020402030106090501121a010e0a2315040602030306040c0c0b0a0501 71
    0x20710304600c04200d00b003e5200c050f000707a42c0a01c00e9200301030510b904c181c090380c0550382800b54100085807040c015006541a03600940c5070604100601c08681001e4510b1a14640c061070940d114112901030b0b5800c0d4900041803815109100b101e00042c4492101c4880981e16246000004c4600b0b0510301150900800c102629039880036410790303400c581408081c0040d00e006004001c05d02c0d0140090200074818500403880070708590b284a103001560b00940444214042c114964a290f581c20340400d28070b401241014285441404100140d8aa0a00039504002854002c0a8000c2084400455014104550b40d603940c000c010928246c60107154006500341c441c420b90303071100d40a14100104542103150078009001c00644125036a1318000d900805240300024007160000000400540c1c03411007908542c02e040200114681d00781c560503d4000c080c0401d0110303990004c15281d20480903100020078002291055510307040c00c030001080745040400f0410b69054540003076049882c440301c003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888185746 1250 888184496 888184501
    0x26280c090b150a27090f0504020906010e120703110906030f0c040c1115010e0f01120f060e030307030b040e0a0f0b060604050303160203191509050c0a090e06 69
    0xe40c8150740060031a6580b00101d902050b1014800d00000e100002d0f660800001c0081da605032022203482c151000d05942c90100001c012200041c086c000f20214085402c01203494540c2c001208142c015011a0421007a4580d8109135142c40d210038404a500ca011a48150b944c2c2c905078404600c02d2050368080c4400d440070400301d090020b012042c406140010708240c0050100740402003564003202030401c06c0000c0c62403009101885200c3c1186a0888041c0b559810040103440c050001340031514080908001040115075190800c0301566220f036500203289818140031010b0f11240203441c001d4040001440334075030305603218100c103031002e507024480e483c1c600c5405900ca00c2000310192102800075042d4000130703c0342075401c1d840040180042d040c561190007081c65900010314040c2c6d0034002c40d00c03120561174200310714508050b808203407940002d2941d481814072160020701456a98032203402c0000c2002c28000d091100c00b0103404100c401e9030f80c44080002c1c180254000c080741c0902e402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888186996 1250 888185746 888185759
    0x30906050412060507090b0408010509011a060a0804050c0a080a1a0702250f0b031f03080417010905061303031401051014090d0308160926280c 63
    0xc0d902111076040e9102c40080c201e84609000d440003e160b0010040e011201041c942c003980041d001410700c85000240a10744800010b08440c0f9146295003034804c002c00c0c1c0354030ba17035440b0211503054141d4036140401303485500e001c1e0b1070840c40b640300f01e500052034000450940c4001500541c414019454402c2e175414000d0350300c2c1c10001c103580c95401608040020a44061482c00300c0307850484408542c1c004541c0c6814101c0c560615800401056030300006001e0104c8a000d2209018a907241d001140c2c4e52035a81c40e80b61910582c49220200b145610840c0301c407440a500c4100c91070303001020f40344940f4118035103c0c00c1d403400e075108401081c0343c0780080d07503a8103843d5a658165200a0000b4511082c0240d06a4800400706103411100070200f04e04c81007600c07286c0003070440a01c039459a034001c2c105088244502041881c0300d0382000408070040290102da002e4080c0c0461001d92a031018030000313480242441842c003e4040004800e60810801c201011150170f0214003030301c0440c060544420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888188246 1250 888186996 888187007
    0x60f220813150f0815040e0309090115140406080f460213060e030f1504110f0108010e060607020303030108030711120604240e01060f0f05061911120304030906 70
    0x841c001801c5c11403401031010360400f07922085980403d00b0440342843c01c0e03000042e03a0208247c0091040d070380c08803540201190007007002028100d00d1b90303840c0e00701401c0140043c2202d8004207816004465840072400e01d5200803007103421120358085019800441315604541e10403885c84450181d0884104400c0c1032003284240c450024540c4a2912180d01c3d00034100c42c40c5802c80d40326541400f80c801007200b036217070401034400400082841020585002e0606061500c0e140b03080034000c1384042040304a60b0790200c88070b815600c5c1c0580c00e03100c6442c0c91011a000e8015800c0094041c88000700100c5c40d0000003026200c194415001000303000c010209015400e65409511040c42d4001700126002582400c0029440b2070241c0d005400368a461381400706a440e200b00c001c542d65901c4201f13106518400c0003034405460f034400e4030300c1c2d041c2c9081c0214210784200202c10000c41100302c0c1504680740f20306401010001c64000302d50a80e41d8181c01804103a0055408401040360004001055800340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888189496 1250 888188246 888188251
    0x9050303040504240312020616120504080f0a03140a09050d030504020d0605040f02030105071e03021e04030c090b09160309110a090c02060f220813150f08 68
    0x25025600302803405040c0005043d40442d2a07564100741c928908140408281010003075009065030300141c00b08200190611001400c440310050303201c084211007603040842c1d60f00c01600000700080c541d03200e01705682d00340a000602c1482c83c0c0c0000e400101e2a40c0341e0084603605000d010a1a4107890f0700552a04484001c031000b002500200e0307045a0150081e40b0a9030302500150082c1940099903840200f15101200e00700c0e10080701c0d80f200002d500342445110b50001650401514107540200b1462a02100310b00706800c140d000121001c0b01d803c90b0701c03c1c0100f198503030b11407500c841e202e140401c14061207008d5840f489140c03070307545203103072030b08000c0305004020351a0143c4c90060b40800460250502d40d00c2901e00450380e419807103e9840740e1500c00d004240c80100007590151420000f8240700e00940701e0240030100c0401e0100c0c09441c2881d109404049000780344101d56a0701c0c6c021054081c10b41014440c00c02081d00140309405040446206142656071003d41c41c40102d0642c1c410200b07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888190746 1250 888189496 888189499
    0x80f0a0b060105160b01030b04141b0d030c06020f0910030510170309031e010f113c0d0b030d080109020c0709020c0706030b221e090c150905 62
    0x146000705035654002d80c0181510746400206880c40f07a01d40d140c140c89090300307034021a0181190420041408200d00e01150400c031203102802c41c0f140c1c85254404510210a2854414228200340e40c1c01c01d4001d0014034200ea42c80001076450760f6210b0880c0d40c1070380085005502610010b904111502c0c881e10409100c4d40000706020b2500d42072465062031503d22120074900c520007004070845a680030405075019501100c15040494401c3c05a1825100c070030300010142820811113002004960f410344a45102e01022022201c580b0713880d03003540c02e0b0710030300396541c2780110300d2001403495180c4004c2c003050b0b02e044418040710551405050391511305070410340020340b650700103222922141d0001c01034a07858401b102d96070b0380c40e03c40680490340030111202503907010f031303404000032501409850007401c0111185032001c92002c5807407819a0b00210301d01c1c40c0c00d5032101f904d0042c00c0b0001c0e04080001c0404410045894a440e0290b0030100b00d011b80d4103c1c2c0c80300c801004151744104146030682d0b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888191996 1250 888190746 888190763
    0x60918040507142b0c080f0109021507030c08030606162111030307030b0a1a040302040c030207030c1509210e0301050106020a03030e01061e0e01050d0c0e09120f04080f0a 75
    0x1a0440011a00e1302c80e02c00845008807100c2000a00700780800140c0400c1500c03000005030b43c5134071f204201020f004440c0d5042d89403001d000001c040f0b40c00988418100c1c0d0440c440f15078a503110340006501e4030481d00325801c090001c1281c4401e0041c07041500c610010b0090700217806030072801064848003107100010400d41d00800000d10341c1d51094000c9601110060040c0003520303203a8184021450000550165540e03004c1802c10540ca003d020307456031a150b03402c04624048294400402d682041ca0014044a4400c80c1048000305c01c0e9100c551010f401880d010340d407402d80901c0d03001e0440074000c4080003031800305c22000f81e86411300ca414122507403900280103603a00c65a00b43c01611100300c079504a55a0380320002111004e02c0e9048075983c5000c6808401c8604144903038080045c1070304070038060368070340c01800000340d080f40d050415608601040a0295550302c1003c3c40c2c0704c40a400c8042907580402e900401c591400e0140c41075400500a9440348641701100c99078035042100003801442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888193246 1250 888191996 888192049
    0x10612020d021f05130509040b07110c1f020114010602031e0c0d210903050301030212011b0513050607171b071818050c06091804050714 60
    0x5415400d90071964030203042c0d071600c04905440340c07002d010b5400e020804200c001403606000e07959041d8400245c401141c20040c01d080607100e084011100400310001c0c42210304c1c0040700c1030740420440300030041c020003041c200f01155214071003286d40c04c41e01401641c20f24840a0820012524041c10388015178019414400410340f02c40c89039403101c50f4640f00000810010155810900005802c0651a1030b02003070171038903003002c0d035403110015944101c151a003900da03400a58428102ca0440340c04841c04003081d0746200c801e038014041c80c08010140100c00307985164650708440607100c0c2c11101c0c102d49a01d2a950020300800d841858001001c18001c0e60320040c041403540c0c0a840c051524903d92954840c000300b07054a00203041e0442003c0b0190050044681c002c0e5004401e48000100783c514401c0780700381c4d200382c2c1d00c0c0c0a40d0030040c0300e801c0214945a554440c0c1d54103107000900003000715032a08050524545800d03050181304044200f00c6242141e50403c490700304104e020740085030790004d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888194496 1250 888193246 888193249
    0x5030a091b1d0910180c084215030726030a02031c110a080a0b010c0312091a10081b010f080c21090d0503060303120912071a071b0f02040e030301080601140301061202 73
    0x2054010040d0b45580649c4000e1082c81d10200506000741100c100c010802480c40c0b100c1e40c01412003400645800d5104000c0070002d40c0c2e0120607282040001b54201c0d9000f01c044100102030540061302c01ca60100c003180f5001807e0744074142900500aa9000700203001c2e20344011100d50541c01405030202d051441e8200d074842050b4040001a401210307103c03800001030390b800c111600c0a80d45405911640300d000e100315441448075440403100c18007440c6030a041c4100181001808108400511044200003031484030320200311094a032800400002e0f00d00110400c540b6128203a8519140384101045c2285444c024400c8034040c9070010b00550509080944400469400400185039806200815205401c02070040e01c0440d1040140c1208801e0144041c00000b400134008401c1000030b0030170715035081035032501ca10007075040300000684107601e0000c0b0300a030045400c07038106848004000a4103060208185d41620003c040000e901071541c03040600340c0c0c00c540560364039180b0310400140103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888195746 1250 888194496 888194623
    0x10f05160807080d02040e0708130c0e0a0f0e070e010e01240e03010c0302030403030b0306040c1a04031a041e0c050105030a091b1d0910180c08 63
    0x802c2d2043c40c02524242c604209041030740c0240c1d01c130000415440d0240301c40d0719048200654860200c0d540d03018031014980364210003101a110324401e0803280c1000c40d81d90b21040d04692a03030341900400340070040c0b040c18019512842032055901d0200480d001003840a00d2409441c1207900e603400c08600c02e1054860345541071044081003041c4003805106006a46080c0224044c2d840715032001038983c030b05800d016082d240d0010156103c2e401179020040001c28911060341600c000b03240100d0084e48020980341705100c2c03a0805441d030400e0b08030038140ca8030072000c441c0c4918813828003006103481d00e940d200e08a4110030f200401101c44000180000c2d4443d0740a540d01c60303030f000303004500c0d036820b0384812425000c0c40a07410f0004007041004c2c0702c1003c060004985005080d200c0c0e1202d481e022000d991600700980050381c0c40d03612819420503220618224000d403503089044485001d96500c4130329500e0f03a210003840c0c000400c2d0447c40a051184181030060800c1f000b0510208403001e41c0c1c10706c1f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888196996 1250 888195746 888195757
    0xc060115020322170c130c21050103110306040809010e010509040f090302010c020c091b0702060a0e0307060c020310050c04080709020702041a150702180c0702010f051608 75
    0x461205000850000020f01907801c140e65485036110003407420600302c4e84002855030b00e920802c0c0c0c8468011512619001c140f0b8200d802d0f0300c03031b00003807102d00c0d000112041c048840d003202094a912429401c401d21503403015040384d00c071f10382503600307842640140f540f03a8a0403907019029000c280007080042d4025a400c082c20281450481c1c94404450001303802c07208401d40d40800590350b01c8030b02c02056024402c1250102c41d500090a00d0081c6400182034000700505100e0500310103800d00120741c1c80807003902c030460340c01014161101e0340c05030000c001c103d020550520070f1255490000c1c0f56806400c000d071826801801070301c00a04843e40c1d00380035000c050480300401c4000c21001403100001c2c8408009801621400341e0b540380d5500421054075090f12007600072040056401019540c0c40c208085a24288420503441da0f03145d00001d0707000d0495010820341440200c08005c0c40e8184880202610f80c800d03200c1c0300515409400440d0300d4000c170b404a94412141440100214150340080d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888198246 1250 888196996 888197039
    0x1b18090c140d0b040b041a0d050f012a0e0a03033b0a0e0114091306050403030e0d03111e0c030f0307140f07060b0d061104090e01020c0601 61
    0x103500d10440a074040250b4090751109089503590310340407206180500550f9a60390b003c0300d09010540080d000011021f444451880c440c92904064804202042c0312000344807402500800c8016060070034400900c010700e0780240480030340c05060541c80d0080d484101c0015018203034084060455500350398280349103180403000820b00700c2018030781104880c00d0b800013811011070b00d810b4000d641440710a9a00d0340100c507408541000600c001c045414606c03c5d110411120980140c4410700100700744002c1240150015080108000c141034041d044020b0031808903048614928044d14200d048461004030080125010040980c7c45080364540340c0074101104c400d1850000014041c40c0b840e400400c05106e0f084003c0100b102d0305420401c10690130384502c07100740ca8102c2e0410ba816a510034400020300440c0d54410500c400d80700c14040184003a40a0400c011004240128072010381051040d000f4041c142440020f140f5018001d80d0b0883d900840100750503400c001c0001800b00006a02c0c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888199496 1250 888198246 888198257
    0x503150d03030e070e01080d0c0314130e0903120a2007050606030105010f03080409050c0d0f0b0301150302090609062407030f0c08090906041b02011b18090c 69
    0x248000d6480c0c0c2440c000e09442600c002424545046802c0e0509485500c0459800c11400042010040100b10001100810318147d0740c1546e06140c00c0d2824501c401902c04007800200c1d00003544044a201c40303080d54078420f10302c0510740e50300303240d556284030b44a0b444000110080c0801c4140007a070300009810f151300c1c80d002c02d41a10020302d10074240c0100d50242c0711507200d2418050182402c0c41f9071400b40007090f4041c02c5c44c90564a8242c20707440795100741e001540d44c8000258060140201b80c2d4080c41200e9001d00c2038840781842507014040c4007068078030a51800e0350009a40c04600c10641c00c996018100d03c40030394401c0b04008a501c40100101c1d0040c070110404100c1181109441c1650b00b201008151034101c9810020301800b0000321290903c0a035280450100f090304d000d458888200b200c0001d1541d903140b0204020705021030b42100c0b0f0b44181c0301621030644d010340110b82d00c064090400991040c1d40801151002c60072a0680180c45400c2000d01501405803c0000c9101160901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888200746 1250 888199496 888199531
    0x60d06051008010f090c0f0317091302040b07031724120f0d020712150c0233060a0509130602130e1e06210114040b010e09010c020a030503 61
    0xc490030b41303508007414840c465590849100300480104840041c2003101d8018001d5421a91007003074040c0a116048110b003000b00b0741c180ca41c0e80302440e1189500b022402552150341c0c410302c1d4680ca400011045002c01d503500070200105a5010303029101d103807106002080003464400c81d501102d80404000d8114400340c0300c449050004126100100003840b00424440841c00d10090611109400444810601520410100380803904074640c0714030b00f00d40003d8181e80c20105925004071140e140f035000d07180b00354080110080994440c000c00d521444004141e0701e20341009101d003428006d85134041d00020207da03032405100c9482c46d4030385c4078400041ca000300640f038801c650b021a500401c00c0d043c1341d01c20004200d02c10700d062921090b00c001c4c003850390704003100025034401c108401da480c91200d00c801b86130303140000d400440003800e00c41070460503400c2508110703110000c240218000c1030182c2c0d0120342c501a05200b902100b033125400b909059800d035504480319403024211041c688003a028 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888201996 1250 888200746 888200759
    0x309061b0b0906010303021b1f1214150105040b070803060123190503070816091a070212060103110f0409140610090b01080c07032d03050609060d060510 67
    0x410750240c8650300040650f90316503d4001d103400c0342c112008020051414000102c1d0b250740303a0015074031349811440231110208030012294080d0701d8181542d50340c00c02081003040351205080c40d0080f0202c600720040c9201c01c40c0156802c0c4030368801d05540000410034a00803940c1d1201070f42d004001490314030200300c5c080c0c444001e021051070103083c0c0030354001500241080c000c9210544c101c0c160515a04501d005500900001d0005000382c10740e001070610340c1e080c54401e040307000c00382003104c40041d00000421100c0c1410382002e40203c1c0a40302c480c0b039a808100d4006500b0381260303030000426036541805402d1101c0c1058034140c080c0c009855604441c0013502042c0c000c2c4c001c20304a0028640c03440e280100c2d0050f1081548081202440c1c1050010581da0080280d544440d0000c2c0702c0c1d0740d540c540d1a085403042c1c107030890020440d401442c101c04101c0081d0060115544640d014012500c0e600104210003e0a60700d459012103c5a242400205160041680940d6010322602c03183d540300d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888203246 1250 888201996 888202013
    0xe0c0307031e050307061e0501050d0201140903030d050105120601030c0902090102100c0206060a050a143007030b0702061003020d140709020904050c030601020a08280c030806010c0309061b 83
    0x600300c070280d8031516140c0110040e01e2884031590b0b03681c00702380803551518001c075500004606000e41000703420702c40031001200f510125104110060101c075075032a8600b18010040c4028040e1620890303c001390301352140ea000507100c0c140c030381000c0540c1843d40346c01d001000a43c0075100150560107003140d075484802e5644100884400c01e80c000c2c01007890320b0410092407202c550411881a07030003800c28801e42032500c01c0000d613003074142d500d089880c20426a441542c150708c0740c012461014111f040c0840140440c004003101e03c06e10f4003203180d84400f001a0b031940000c88142003c1d1812040400c05803030000103807c1c50310300821200100b0000181c00e0384c108034550300502c0001d900042c9020550406126040c1e00018403e5a942181010310000b9115544908050f243c40004180c149047e04130070301c0980181c0c4029040c0108248110740a02029003000054007ca1203d100258080d40610440700d409c560644d10001d86d00e050580c152642010418080c000c044420001400075842d46d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888204496 1250 888203246 888203257
    0xd0c03110a08031501021c03090602070206070c1d0f1303032315030f03090108040203151f051c0605101205010213060906080a09240b040e0c0307031e0503 68
    0x2d045080d0f0b645410790403c0c025080e1110250304540c0041b22008444010010030710401c03450345408071b180801428188060301507890065071005000400300c04005030315030842b0031036106104490350046075003508421040300b05d446030310a1110000148402152289034880c151181c180080e007102003048520800000c10000c241040c828028048021411803000c0060b400880042210081641d0104c0d207d015504c001c03030602481a01003800c550301030001002c60008194540020314040629400b400d1149201e205640c00b4503e002c20360b4200748640c03e20301d000c0d8011035502000150b880a004050040c41c1c2403040c074105402154040f54980d204046900840015071200c40f40310b200c500240782c6030710860030320425810802046422060950f4020034440c2e001445054506010704111184103085252125110700040b03011500d603c0701641700403d950400080a141e0a040d41d290301c90840c4550560120b4030400018074500c01101c4142c1d4100640412207070785595452958109 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888205746 1250 888204496 888204503
    0x390703020102160803190908060a02070317071b061b020705031506010c080c0c040f1407020c01170a11070f0302101808090a0302060d0902010914030d0c03110a 70
    0x111104200355a8108954140c5490b10f60140e0030700d519200d02140d503403140c00b8450b4107222084d44900e900a01440c02d501c0140082020f0301d41780d1500703a40a00096000c0d81c0100e01160800b0b0507410305400b80344001d84118269101d0202d030001d000030304402e03103821000481d070103521600070454225151551204c441c9054000300100b509090030503040402c5410a03031080ca04a000300241a070307010140220498005400355a80c044540e00b00e0b09142c0781c580d00d9500a82042030b014500140c6500801c031058003006841c00b00c0d222807400720713203e103402c01c0314500007a0361300640000503008451035504140f80000000c4c0c20b0000360010900c6810019065551030690701c515000d1540601564082002d0030004215940c440ba00080d0141d8100300042c0201c4004500c511050700c403014900c010b103030020461919581d4441c40c2001a010420040380021103c060000300c4500c1010b14a403c40b0008002d04034034031224000301d80c000042c031010b804000c0d100c1e000c41d40e5a2410b1004000a500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888206996 1250 888205746 888205753
    0x105100f1d0112211724010503090f070b030402010f0207080309060c03090406030f0b090d20010b13060f09090f060e07030818010f050a0c0618020316030b0f0c39 71
    0x13075445c50100c00c0a00911407005c4e1140c6541066460101003000841c00000b42412912621495030042c9401d070041d481817154810300c2d0006ca250200100958882c0b031013640d03152501c88005a0403a11540144070f081304540c0b0502800d2558079000010704000051b120490b828030b82c2c10800513065446651042e201c08002e00f10400600400444882c0c7c04900080100342c5441035000c02841c0e2050700131102c96004003084040001882034220f5490490300400118a40c4031003090fa80c01000144a07003c20101000d0001450201300d005240c101a00003c000c00c072200c40e41c036858040c180b1400b050340d071400b4226000c00000c1c11803010b040403080c6450340356508015400050031235030380c400c441c40500a0910a0005080e031041d0f000d81c6c55070740528041851a00081424903034000700364002d52500440c0208a00a030004503000e0860307000e6035031181ca50326910000380001f0303819201c4015000342080b40180740441c1541040348400e8104071601c100c41010b0304612a90024034180e0750310381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888208246 1250 888206996 888207017
    0xa170c100e0d0605042907050d0b041509060f0e061002030418051b0405090a1d15040b0a02040602071202030703170d050a0509070e0603030c0105100f1d011221 70
    0x209800d540001d004c0c50f0f4070a15085406d42a0924421000070011001c00100182c049505040e5030000000350300007510a00c0885184408450306407081d000d2101068900000040e0242a000c001411a4140c02003600a504c070305043c4140c481855206100303600c004c101c0000c1c505c100000c1c004840f203c807074000406040039210401429101e485103041c60400388000d2110b603403401d400e25000b6542c41c00005842e10490201401c00881c3c4800d080c2c00d006401038002c44801308146a4451445880c0c1c0102c0d40c1e540100303000490003039005000069000c41d00070b00841610718803038000c040c0010110361417983e0f030303a82d9280c00000303e84424000c42004a056003000605029442d0450340c0110184414580601210355910700380c403a001c504501400810b440d61000e008039400100d40400078030103441c142e810f41004200c1ca114500c05000040700020702d4054000001e11515210b00f9074034600d9107020080032400c0d000c90340a5914403002d412808200412000c03040d504010b948900d54001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888209496 1250 888208246 888208253
    0xc0314072306040603020702150315011220030c040812041517060418050a03030608070e01030c06110316060507031d0a02060a170403020c0a170c100e0d060504 70
    0x40910a9024a00710300c01d0380000c8190303512001c3e101503c2c22480c0042c1c60350114000a25225104142071070388210000a120711041d24100c0d034422440c0a803a207486c8503009400c8002243d5007190000103400d0301c0328262110600c0b1030000c1d60003241c0c48a00e00d042a4441103600d0070210123070001c0041505c006020400f90300c604100d41460b56103418180201e01006114049001c03004140500c5659140d5040905921120105514540280844021000c1343c58090300600c0c40d4081d0148a102d00c503000141741040240d460b050301c0e40941c0c00d102c028a0140191085600c1324028551760005115456501440d49039200d9039901130b18000c5500d00b0188401b804807500314941a504440243c801586594006010103045038181d42980ea1040780071800c0f512102c2ca00080c003081141d9006000516600161a103030b02c08040310000c50855076070811450114000c00c940e01c1c640c11a0011110a140100b8070f03540c560214202a0581c669480c001205120701045c200d824907914418041031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888210746 1250 888209496 888209519
    0x7080a0201120e0a03030b0114030f090c1e06090d0b0f0a0f0c0207031502120a0606021c080f0c0d060f0e0c12040611251416120c031407 60
    0x544540d0b202c1040050420058143c485816110150a058680400c0749042e440307034548044d4100902245620790034800a061005941515401c40d5441460359100151604d50303150030008000080076000c000101040c84100e401c00701c01c4e40e40c00060001d4400104203050340c2580302d80102c28001e5a00d160087c00e8904039442c0a80180c0540e20344040f5000c4c0c580c00141d0b84c0140c1ea0800b10084442c2401d17580704000c4c0c41f4415005840aa07254144280171541e500140c0a40f205a02502c42c08000010150741d280050080c26000071110000308040022002d0256007000c2c20104032840d00c0c0b07030009600152b50644d4040e524140b840b09042140c490f802009a4001c01c0031844c1500c1e102c0d0711814003140c00e0011300040c144640c0ea9414102e408074090464441c00c0c0d810030071100e030410b8a10342d000000c207901c2c800d95488000c1075818403560f4020540340901500301c0c41060140e807e1426820341c0480e4240d040b14010685400403004c202c1081203040404c048100602c12903080200c80c070403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888211996 1250 888210746 888210767
    0x50f0a0507020133090606020f01060e040201450e09060405150a02090a030602040513090b012705010f0f0603090b01060c050123061e0307050105030c0c07080a0201 72
    0x11a407406034802c92444001e0518040c0c080480c180e44204c0c60110010440c1c911503901126205251040008120fa0080380118404282c28000c1240036516804011600700c21a4000d000941c0200e4910504000b20101d001c800fa94011150040f00e0040d00034150240c0c00c0e007002484601a601000b4201b0502e405076884a403140c00b400e51800c2542e940d540d00c0c400d03002211382c2441801d000802c4131015905030703120171100811035408a0350302d0400c407000350300c18001d25004905945150718560301c10b000b49803155600070403c0312280e10b40b80d010b40341664641c00c5d80d000c5090302c01c0900b00c0040e09010301c030701074840007407036404541c5420301c001c0800c80c031079001406041c204200840841e201d01c0d4a9411682203003414882802d00d4601540181039200708103005e001900d10400d2412041b520040c4102c000351603801002e1640e010b550555540d05024542c140c0c0075100a009a5110f200030b50f410895242d40c0c070b4103140244003003d04010f0076400c041d92a0303112015813030942d80e10800610 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888213246 1250 888211996 888212011
    0x20c011103100f030b13050f0a060c0e030c012106090f0b09090a05210d0e1b0d080711011e08060f06181504080f2a03060103030c0203010f050f0a05 65
    0x12071a45e40e40c0342c18560010054842841103400d6102800b10030b00c00400380155000035160004020b00d0108c0003000881c00c0003001621080c00070003a400c00061002c00240140c46900d11018a8021a00880c48486000089985030440050100064003030303694040b40801c0c01056000c0000140a1b0f0184010001500c5920051840e00858408280c04400b20002030000d0040c0001c12080407a61084604954400340b0b0102100190500411500a9050841a400c480002940030858900254138000c5c100000c2004140005035000c00c0c400c02c0301d501070601e05841030b110303e0002686852001c0003c04600c1000410000340f5002225000b041c804885880c10980c000700f000048100c910007644c0500004205902d00f0f40c100000e480003094010222814419842c0d1000d89818050140306160140d510a0705d0490140b00255030103140f005e00141003a0b86561411241c0c4503409406a81655a03070007800701405127805074900c00e01c0600c5d03040101d42001d6040d042210303002818803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888214496 1250 888213246 888213269
    0xd03090e060114120a06030b0421050c1b12030a0f080a050c030c030601020f24060a1d1905070815030c0108070c0203190c05090f070906050a03020c01110310 69
    0x1080507807026019613000055034405080d6503034403100081d00401607038001411014156040204101080d00c040d280c10004108444000c1080741c410340300341c013500c6a84281c54000c50100c1c4040742e00703450704600030301d0001d1564009980b2074030054110f60007a180c0c4400615401c1c840301045800010064104680c10410021071400d040100f20320700001e02100c00c0c0120000c0800d01c2030784200001000c801c115011381c0c0215907903141042103145801c285000544010780000e0240c608055201d04413503800d010000552160104070240303081c000c140c03000c1452403415465070340d42e05104141c400d0501d901c3c1e050302401c1c14441d009100c400407003094400c2d07014400300c22490b644000e44a0700a400d504018820030f40a200003810914410324081c070302d10115a9100503c00c43c3c0700788404907002a110b00c034260300c8a80310000b03001c1d0125003002c0411a007900400120b031085009180c000401d01d401814207030300b1f03480e030741c00c2d14110f444001034400003105000c416860002c14400609440051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888215746 1250 888214496 888214517
    0x20f060108030f120a0f0e16090203040203070e04023c040209130518010203040507050f01050a14070309080f1f0e070513090209010603091101030b0616050106050d03090e0601 77
    0x222940f92007409041c007480c02c184400314030b000e599a000107200486403601440003403091501030340e5400e0b0700280c8404907003043d040020446030302c2c402c603801242c02902030400c0301d05055003d5002080030b042240c200c00400c00b00104003003505001e00910400d040398400303d1010003814101407904455003403060380704104034401d80e50380040c00200310100c07820102d5182d071907010414483d0a01304442030103500001c2003008011001c00ca4009a86c021200c000c0000c568000444680c0501c19071017010480002c03138200c0104009020f0701c40b4030b10900d48800034644841c4032508140000181b910141d0000341d858030081009082c0c55100d8080c00b004109011403040451303500c000c148240790180c0c200c21250000c8844503040700800c0c40e0042c02042d103550b5074203001030040c06101b4050340c50302c400e008003005e00e62290003035440d5808001c042500f0004c204003a042c040c0f0564800316103940d641c4500042d180c540340864032460b400390300c5404990740707802c1070081140d4005080b070341000f115009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888216996 1250 888215746 888215767
    0x19030203150604060f110c18060306010b0403050304090203090a06091101080c030702030427060605070606080a030806060a1215030309170307030f020109170711010309030516020103090c0303020f06010803 90
    0xf07010017118554039250ba035a00b4400c09080c28111503400c10340e08806040b46103030542442003c0c15018881c26012100141c1ea1400901124000c5e400020440d1b04104401c1290a200e40c003c0c541095440f41501d04582150351400221040c1da10100c810094140c0320141640c2c00040c1d02d540080903605092541c500003a0094580c41039005072841541c00d210203800007000c108006a800c5c00d00441005040e8031040060000c3c1c02815049940300e0400b180070520700c01c08a6011401c1c0e134503856500640c2c46507010400c55402000c10b04081207042c0c405004089014094002c004410100303030a54a815420010300e06540c0d07402160700111540140881d500c4004111440b00f07806203001e1700c0c04038604804901402d01160040c00480c0c0c40d400004040404034014401c10f441100d110038840e084078019401e903955018080c2c0070580c18448906411907040c60154020710500d000a41800c0b60350780e94220300615041580164441c0b88500800c1c5000c02266001d410b0400003142807448059 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888218246 1250 888216996 888217007
    0x40510150c0f21090302061e0c010f0e0f3705030d05010f06030e060406050603070e0c070506010e040c09020706020408190308070c02010c171903020315060406 70
    0x10503199000c191002144540703109048286503640e000e0007010a503031a908101d60404403c01e5504004200b8488a0b24064020440c0004603503025101e80d061040d0142c2244090001049481329002d04101c0010b0400003845007940c094140003000610500b889403c61403c1071140d41500e07154003a400d122505a076003160344803d071141d81003e2000707400320140f00c880c2000c0350b40001c041c1e10000c50041c0c0e0091803078010380e043e1041d1200ca451015626903046043d1550508200c003160810303004900400c595030811580850003400303d07800700307640d6078a86464003012102e64004520106402080041c20b012050061048050b40240d43c18180c0302c51040d8203041c0302d81c0300c0d050f6001903000e0800a213501547c008002040542e09901105400541142001242180000e80385400121054011000d225000340c040c0e480c1305001d0205da8441140050000b0304402c900b01c180102002d4003044e54400e41546210358015850b0704140c5843c81c844120100001d1050340300b0321084c41071540c081e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888219496 1250 888218246 888218249
    0x41205090a03080f0f0a022506050a0f020c1008150301020a050d0531120203180103110c0d05070b01080d05030705180a080d090b0a020a03110c0913050606040510 71
    0x7960b564940001c00030074164411640451180517000ca8421242c54000c501410308032071414081060f008454a90b00c2050150302400f40442c0040c4002641c6c82d00c40c0640c3c0c20003540c54012a940c4ca111507001400005900000b00002400c500404c40d6490021000000595054000b54140031a40390044c0c41802000c0d0601c50385507903040011280f504007640710141d2401c6440c3d4040f40400e194000740600c42d8540c041da19500681200d0300d580d4800801c6030b078200100b82503054900c42800046000c1d00b4941d141e45040c0c2d00c00d00c9031024910040c0a208010000350300e03004e40e20a9189030071121140141d0100000707400501c00036280307035001004ca907400503192a09950719130714000b90300300030b0912540003508141b4500000c210340ca0001070100039000305894901155903070300031840d514131850540c500140c100c01000703000170f03004040f1740311601c00c18010b4965140b61040410544a011240d103502c81c0c80c1440d400060000c00d006450b00b2a100351030030300241c6052119450f0a4903107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888220746 1250 888219496 888219503
    0x9020405010324230907030911090403090b0a05130b0309120f04030f02060d060b092b0206031018020405120a02210109051b032e110d090605041205090a03 68
    0x4501014110840c905900c40c55020000c0001d0a98101b03050010700030b0460380700c21260380389a00c1403090307240303401140c8611132039255031100041802d00c0c3c200342aa03003003450140c040c0b2000380812003052001c4804400030b410384240858403454580f050528000502d80d201540c42c00400103c03070048040c2c81100d00360390b04518207441c48c031018030116200e0b02c01c0c444001c102d94609440070500c00c0b0070348024500300d0350813600f558000c49001c40c41250501c20011001c148403c1f150b1000043c10100040e580c0902401c08540d45107a0391464480600c41125000810a5001400317100914061214115461020700201781c000f0056001c11400e40d00301000140600466003c1c0b4011682500580032980d800010358049410b4455646002950a04110f00c28064400c0c11686d8200d4010800f8500240710200741c1e9141c205440000144000c03481310000d080c040044071032111090040d119180c1c0300300b81c0080ca51a080c149070040e000030140c80340400108101d420301c155034101041080c0e0340c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888221996 1250 888220746 888220769
    0x604030b150f090a050403180608060f0609031f0614031e011b1e050c060a0c03110c100b06090312030a02040306090c150e0d2a09020405010324 63
    0x2415000882c503003030000700d481c3d03c84041c030700300850400c064000f540594400c0d211040e811512075010750444d501c40c00b0301000074042d00001401ca29190090035480700c0702400480c9450300304000309041c0040960a91203c41da0f000c0c030301500c000944201d00040640c41035009000741c0c4c800000f1b44400e90000c58900c240d40480240e4040c12083d4001d80020112000300255031002c1c040192801c4203101c940e07007080340003084424610340110100c8ae03944640302c0207840b4a56440303903040c00400007820b5540400d686d0b002000150f02c0400014045080b1704401800c60075140c0e1058802e4564030720619011710014800d8013169140001e030003040ba169020007945950300c1410800084c082c50780040c0500d4200b0080b0b8007441209043c1006550440d0301100d84028401c1040d65075840c040715031b540000c21040c2d0381010a4001075102080d40044558012004084d030315681c900800e9005481d81643c005030401c541e42c0c0601c903030004201c6000707107001040319642c0201c3c000c0e82181300f2080000b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888223246 1250 888221996 888222031
    0x90307050d03150314120c0106031b14090406020412061d01060b1c0f180c0e070c060203070c020d0804210b010e0c0c0d02030310060c052a0306150f0604030b 69
    0x210500c04001b0001700300304001c0d110941074101034007900a6100c1a581c0d1400c50400c40e801034006e40c1c880042e103540406074004406600d05010f00080014025143c40e80d091201080303d1041c46800720302180940004a0941a45560b101c1c1c07140b440a80000d00303070301d4058100301c50b13225081a03400342200d11114021100c0303454000400b80802a44e00c0f440503181426480144550303070f14202105004204000c50a030322002203480b82c500c1031f281030003c62200c0f17140c400059504d070003c0d540f0510324548150303281c400f40d0104e01c0100d51150111034500011a00380113040c0b0340700c801142c5042c0e85426906070451a01d611100c1032041c01003010702c0e00302c10300040e0f030440d0740401c42e8080301c2124120b60794005400402034880c2c2040c1c540b140c207a62440c900180691203542d64aa071030360442d001d03002806100001c18050040c502441e1300c0a84801c10341100c580d070070310002d88140060306150340f9101c0c9007801c0120b2400030001c00ca124020922044c8041442c08904940c08280c8042030420320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888224496 1250 888223246 888223283
    0x3100f06080703050313170705041d0a0b0129120a091b03120c1509151406090a05041518020603010305010b12010605060d020f070506090307050d031503 67
    0x201101d4000401500c00c0103000420048000000c0c07109030865411244403585807070388000701d03a0300c0300d02c0b08000303078800c807811b008a140c42c0c0d00c6402c1c81c2205100d1410602034140d80681024403003a004e5900740580001004140c40e4001c0c00071018140400e45e0301102e007030314240402c2d406040b280340004001c0300009440321600b9403100c400b9a0700810034601440003103112100c1e0781d04be03020031510070b00720100c010030003802030920030301866106990a0603440000c0d03038400185417074902030710403c400d6680520f404050780b190700c208001515100c03002d490a0300520082c1040600030400c40c1c1e1400d0300f040301142c02c460030316203410075242d0003160382000300a80c50042503044d5400707903010200200000410405600c8401025410f680f00d0414080e804041c80c01c0350500c0c429603412203800c0000ea2000c0a0075030040c800c0e0903c85846601303012171612550700e4000c003200e01c0000d42d4400229842800002c100c40b500d02c0c0701c646014081c05034400500300240009201c0281f031025110f036850580d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888225746 1250 888224496 888224501
    0x71109090d120906181b0612020d1d010c090509010e1815130b060f09180708070f050102060a05160311190f0e060c03180d050a06021b0303040203100f 66
    0x50f0404c0007801300c0c00080c0907505502c3e01004c1c04540c014250b410750302000214140400440ea425125074901490a82408c0040d522800130180303e0741c0c0d101800802510000c0d5410300b400030600c00007510f210f000d0300141c980c1006401076403103403401100405c0f50211750b046944c0e0100c081d6075045294200c1c181c01c5481d080c643e4010000e0f000c068020010510001040b100f60076008405031651500c4950030300605030300480d886a0000720000000d2100744030200d600e0300c140780380412a08000e544849560070075041d41c0000c420310910340c00c200140c0d03a04101c0b242d0003011181040240f410404a01c42e44102e03990f0b00c1c04207140c0c03240307a2040b0301480030013554070700c03154072185201a0f00c039518002c10b01c18202100c50003140d03000c44105a07605040b0155007100310004003c601d40041c021361003915060360f040c03095010280040580024070140302240c01c003446404050f0b01c070350702d500081c0c2c00480d2030411032105038401c0c42004056079001600024a94038210000345150540f1580f501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888226996 1250 888225746 888225761
    0x5090904150932120c15070518040b090f070207051306240c03030c050412120318030206010e1b0c011a04020f270d03080108152701150803071109090d12 67
    0x2076586c03c80030008080d0b0000020008401d0810201108540601c2004120341000d200c60340c010080c0310014640a80078094903402c115940100d8264503a140c0000300e03a10031514881c1540b07a100c0500700301c8842c5240710092039407001010590b100c50380348801080680000d0000c2d08064498444001140c09101101c000d03280804002c202c01d81c40d82407071101c4400c0081520300003441c10401500c4241030541e0104403603816400b40c00d959281c90310b802c01242d40588254520b403601c2078641d6000044c0c0c8000c00340d220031000042900f40700c54045062030985075a00c1030246004101701c0c0c02425100741101c107014101d500100412072421700340ca0b040012050700c02d0700140036085880034950441c40c024103d9558004881d1081200b1014070a8807600381c6286541a583c000e56150440c038466543c00450b2046000250a0008100d09443d810382c60307200b508281c100040040612140e803100070b062010580b17210075642040450300b40d4409043c1c0c00c4408110000c2c00f0400f890516402210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888228246 1250 888226996 888227023
    0x30f1707050703022a060d0b0409050601030c24120b030d020a05070f0b030403050304110307060e0f12060a021b010f2403020105090904150932120c 65
    0x66440c40d08100240195002203001d50240c4140c404029200800040302c94190b45410400c0383e03844205014020542c00043c407902506480d5134403840541c07141d00c01e00021b14081c1d0b00400c01075240d03040400103001590084100f54059102021880b690000c00442c0c1c440586841d41488603200402030041648901440d45405609449140d03198001081d444040c0910b00342c03042c0319912040007101c141c280c4605d40c0041020700000f800f10340540c001d1503001e0f009001040d4034840c2480001c1c01c007909504038102085204407509064208440150506a01038a040b402582020340c025610b00004201c0e040302500055915644903507500488640e480b031a00900c1074040c080c000300c0c05000e40200e200501440081c1000c141f1022685445c1201e0701a120703140b4003000700003030040e00b440040081e248001109103004003013001d031080120580c0180300c040740244110481c00716551050b0000f010580c03d05000b03a02102002ca2a40305c00c56100788082c2c0d5a002c2c6020590400c0d1012868a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888229496 1250 888228246 888228287
    0x3021b060f0606031e250804050c0d0528111903060c0c050f010203070824090a140a050105010e0a08120703170a0605030c060a02030711041d1507020105060d030f 71
    0xc00c006d020342c15950501c0d021041d1446846500d001161301c4801160701400c1340c3e000f40c0480006050501a01c06854000d6080c2e0301420b01d280350504180c41d0340d0700c09818003035154404c481880b021501103140810b08980644891070b881004002d40e515501019101541e60103844150f28022650080c101d5070180035542240813030401e90f13000b50400c42e9020085841078001540b08547d419883e42c1d0840d40015045505001c2404e0040940c001010703809401c3c2d40c0e07203440c8062207444815521908910101003100e40c100740006040074983c0c0c083e00c3c09141008410300010f2004922410003240c0513a2a03502e0751440e040c121860b0b000542800701080c1218203210301c00c0c140b500030b40c0c151403050301203500d10840d04003848442e101d64402d400051704140125000182c02025882d040e940007800491801008091482454494034082e13149034000c030464034803250074000c981d9101005000800075440c0800116100914404001f404c000f241010000094020019030400940c8880c0380c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888230746 1250 888229496 888229501
    0x18080d0b040b120114151011030f04030809210c06030a090209130b013606050306090718061d2208030f090d020c0f040f050703021b060f0606031e 64
    0x1124001c040000a88240258010001c3d084a602410400c6c07950005002840c4500514804481d01030034901320100c0d5010802000c0001c112140190001c3c5029602c4240e1340c45500d010010f100006034416880120440c1c84400d24400104000100039400d44001d0399a51b40d0b8070251009002d6400020340c00f0004105110024400703440302c08000e44201ea0384149130344c0703400784407420402d07203512140c0440c14802c80380c40003644c10038580221290400c011901c00d071204002410400201d5803104175600464080041040c44d81100c401041910002c01c80c0c83d0030642c1000e001404c4a8041b154104e81d603012425503000c5071f8140030010f0704440d4250b9500524030f080c5070303980c0c0242d44403109811214041004244081004094002e164000340a04030b215002d025195603040d151030b038041e5569503002c0e14030400d0b0041d5403160156640060303032004441c4641a81c00c942111000d0360380d105008100e40b90540c40c0c803840d0452030495a2507101e03a115080c0300b0034980e1600140e214001d46105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888231996 1250 888230746 888230779
    0xf0305011b0201021c0903020a06050a02191b03180f030b01030209071d33040306060b180d0807050f010c0306081501171e0703050118080d0b040b 64
    0x1004001e424449818100081c40090407403d078081d905010341580c10400e04100c01154946c004880f46200780162030100700191103078412510100c40b02e101081d000100c003080e441840c40504410b506c14181480031004100b824500d40c005d103140203052207a4060449140604151380400800b000c01200303149580782c0c540701201c4142840201d005040e0303031004c24802030041020076841904240e052030603130707085405c000354440c182e2900e04c0b4a044071501044862000340da416280b95040c80904c2da190b2942c50980c0841e00103a000401c60030302840843c01040e5852110101c2141c11a5107480c1c0805070304180c3c8282c400c0c2d0310010168070410440550341d480640148850121944003080036940d604105a11071150302c8a8225240d40d80c001800018500f05055103d5250a000c490300d040b0b000702800b60a0300c0710b0f07602c0308499004041c100300300442406900300480c0e02054500c0d03440d00030380e1442180d000300d000c1014940c1d124818929140c59aa12140c200c20307004040c10303104505500b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888233246 1250 888231996 888232001
    0xc17040602091c1209050105070b06090c0904020a020705090906040b070f030f06030b06010e04060b2a010e21041202010e120607030605030c0301110f031b04061e180902070c0f030501 80
    0x25413580070460310f8200084542c00b0745c040d2121607070004145c41c00c6d5520b660801c021064010320040b018907041c02180e41c2912144080c02e1408002d80080581600303141c00c101c3c0303055004042c2500c603402a0b0030080003504000c0d259400c03c106003030015103c01c0000058000d4078500d50089a210700c0c280000081c1f1070324946c814010307882a03c1d891851081202840b003600c440c0c3c010416120401c100410b58600b00d1541d0b4003202e070310101c041c4400380c1c0020b803460a46a412030283c405070b10085003101c1c404070000464003a0843c607000d90b03140610f00785810061011499001c0d041c002e4001c0c1030310315501d508040d070810388000e106542c040c0c82c20f9500030380181620b005881c000e00c513490381c2d104103090510900801c0380351296291700b850015401220b2a83c00140714080505480b04032100c030140c17690282019188544680a074004000c0307c0d0903490060000b400108030401e049840790a12042d40c2d94140e41c18002c3c0581c0e07944090429805124803540b1000d480712400d24000144801035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888234496 1250 888233246 888233273
    0x9070302030118060e131e080c0d09051e010201141618050a050603060a0801050103080d0b1c12020102090604090b04200f0a0e060a0c03030c17040602091c 68
    0x22603900c40700810f800c00c0c1030455001e405003101c501c210710045441e10f1044031160f044540705074900e41c100c0c010f00a9030b4480f120241d000300c4500d43c0c045041200706c10144032030300918101345000b0845514241c0050b0712001110b035003405400803000440c41030392003900a02014050610f0000f2682080144500307111060b1640c00c0c00504440e0401d003258000340003038402c03180010000fa1040c0e003080104000c0350f10280205e171380b1a1500e14000703000341007030182e5802503004591181d10f90306501242425203900324201481070600034400c01580315558034103d003941e045001d61400021b4100300781e0080c460460010340c450404600018400001d80000300030700b005448c203000412102c00b030000c0408140c00950382c840c009200750b405a01011014061107040c524000f0708009804020488503401f004000000518524880c010301d500f40c014241e0348061b51030b00e00d0051307003c03032440300c4c0c40362010380010281500083e040c08195100c40184c071010b0000b030700703012508181c0e01d40020a0547c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888235746 1250 888234496 888234509
    0xd0f0b0105270c160606032d17090316180605030319031503111008060f21070f030b0c044401060f050d031b030e090703020301 56
    0x310303003400c20000d82e600c4061030724408010080d19100c2400c20080080c1402c41d20a81840090181e1148907207400c0c0080c020840001c007a820350810142c0300c108800500c4520b5072047c1c10340c000d010b031601e11085468001d000c111068411414180092103903a06e2940d00d48120510300e200c044ac00c41e0000100d50b1040400d0141c10440b0441f0400d07034003107110361945a0000c0c8001406007456000e02c5000101520f00000d13103928402101001d0407454000b520054401002108241409885450004224100b001c150324001001412007408041c400c1e000da030740c800030022030a8231341141258110b0604161204c9548a0625485002e4544020b40d000d4200b000401d003816125800c4030195a0440072a03001039600c41f802480c40c001c03030001c00c0600c03050142030100d54400c104648080300020340012540500d401021910b40359560411380c4240d6501c3c40d10000203401410780e98a8140c2e2101e41800d500041c14159051340d185801c0035000701d0340f18200800c2e5541a070066058801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888236996 1250 888235746 888235763
    0x26010e0604021c080706060f050102010c1106010611120304080306130902010c06021b01111c0b0d120903060c050316050702091504020904020d270c050d08090d0f 71
    0x2a140912a80c810341600c020b900412008803c10006003030481101040c0d014840c21440d0000d999184d10448181c4d5011183c51607050b203081c0001e680c20300403100c0c00d0702d50b450305564409060360099110b400612610051104040c0440400c5006120320300008c648020300301c0d102d1506003030512281d0b0048170070b2440b4100038082d00380101c00d00d220380100c1c80c0c1c06a6400b8001034440e52400000d5000030030f14040b111401c0d503807002444c0c003405034240b0920b1000c4802c3e02c9003c078440300541c0b40a0b107120114803a003040007148042c0c44000101c00115089a040c240c13540b288642501c1d58005508060303c0c06080500043c47e00ea00700d0029401540807464581240d0079a003c21a0140101e8a0083d80510014041203008158600100d4a440000e100618110020740050200d0f4001d410109400c0d450b86214051008403100a01110f200081c0c5011400c0081e540c204000300d03140211031003040d1040084081c8041d1030143da00c00c460240c001114400e150900c03090b4100702c1c2c14122640700303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888238246 1250 888236996 888237011
    0xd1401050d080405040510170a171e07020402040e07080f060d03050702092205011506030501060c0303270614010b160b04050a08190216030b0609040c2601 68
    0x1031007208098050b81000010f030800d403d020401000e00005440751101e0090760381d000c41c0d91440110302d402c1e4074040200408080300d00c5c1c0782c110000741c0b21541c003425081040c8506149010902c00208071204110000c980c1c85582d84000b500034003650f08224450245d15003044400c84e000192207000740307100054030f0f0143d0344040402102d000c00c002c0c0240000c905001c07820040c00c1003030500e5005800d40780c4020400c101408124240080030b0001d5410369194640d50384c1d00c0031580d0a100c0644007a00d0107206a40c10010090626200758a0081c00c0603924000066101400d0500285601070007040310158140d03814818090031280100956008021000080d46490078080b40e045e402c0071b00c0540b400101580344c0080700100100155180d005501b80c03580007400810050100d81c44507448040780c180d000070001d1a00b01e88040c400c0422843c48403e0001c1500b400c4050b034448001c5410308515951841c01640d880f40a90045050000c800c9030401c0c2c0c1000300015a5001909038020886030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888239496 1250 888238246 888238249
    0x10c0203031b0703030e15070204050603100203190b151c18110405091b190305061e0c0f0712022b0f170c030714040801060f240e13020d140105 63
    0x640f00311f40d460596030801c00601c00141069001668801070040075580007800c0c0800e0102030340d01c211110001d1000421031060900b0350391144940801c416180c80520019900d00300b501440f81c801d0b02d4581075140d083d80506000c0070380140e047c142500000402c00115403400110783e030401c5c0340d214412424180040c807117090000e100034032014090741510881c90000144465201e0004211080610f204030100101d20100f001d2401a41b801303410301c00d00c0e1218500c06011100c050720960392a102001104c11400e01041030b1280107800000c040d90145031030710281e1400c1054074811240c00320140d125061401c2c1040031107905c4201c0d4540000d55280540100e40400640800c440100360900114220703680c0c81d000b46030700c90070034185150300707024007441c00110f50010b51128a01d40e454003801c1c0040c00704029020000d01c900c01c103030580800340380303841907015410103a40c40c200104a114005159a02c501c0c003031451038010700456030f80704d608584030064468240b20400e00d0b048440001107a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888240746 1250 888239496 888239509
    0xa0b0c10090f0525240f0e090c0c060f010e060f040b1c120c0206040e0c130e10140d02010c0c0b0f09040509070503060a020d060323010b011b02010c0203031b0703030e 73
    0x8410020303000a02c0521117001c151007010045a0b010100207a101c14541a07031200c900c0c650140c02c030f02c4551612242c0248a003032078042c0040c81e02400c585c08100400458600b0b5520941020084450300840030010002c00c00504480840303a902030209080e01120b110840b03100c0b019103025003004d0443e07102c500720075200031142c0000250800c1c010042040100c804c000304076001400b48411030b2070040501c4402c21a280c95402110002141909011101c00e801619600134994225218480c00c400400a44d014000c5a0b001c0d0610004170280300c204142c80d900c02018280344400d00c4d4403401c6c404e032803600c0b9412400405014524210115014100c0000d24204840d00200140041c2d03880203181da000e904451140c00c01c45031580d0780480010507210100480d250600b041443e0300da00001321500f5030712920415414000c45400c030200c1e004407070070b084016a40a003440d0005061610100b0714600c2180046501411000c900c0861584040755807400c685c06555041c1d1108440c1003004403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888241996 1250 888240746 888240779
    0xb06190e042405010320271905060c0705040f090203010e120406052d0a03150320120304080706020d0311031504090c060801050a0b0c10090f0525 64
    0x2411001d48004110f25071080c1c020000c020040c0131a85203c05803c00c20390403e4116a9060705003c000d040303844101b03101100c03440e00d0340404440c950b5400d42441d038100d85200d26405114003841002600c04140c1404100d50300017400042d20801c144210080080000e19486008030710a508002580420724000030798031150600035100d05141030b1a0000c240e03551383c004042140e8001c041c60810721015085000100b0242c24050000c1d0341c0c84014800904542c03110241140c00c290000c0d050001c1520054a11600a030404c0b0402d0b100c04400c00050f20100b07012020346040c400000e02060840000c40e0184c2100c0158084540440a04000b0750a0702c00109030317284011018000641c0700555885003c0c1482000f80001403c0d80a40d03c070900003c030350750031140110304803000400650401d05d00349801003800c030492a05003c500610341e030b00c2e41c011404d02440a61542043c0051000804a0260644d4440c3c00c0b0340c4007100210f03030f84a140c02e5980c01c0b4000107102d43d200146800a2100062 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888243246 1250 888241996 888242051
    0x83901060e130311060f0a0c18051507080c030c010b03150f180d021c0c0f020f010e060703030f11041413020c010e013c0b06190e04 58
    0x907076859180184641c0b40d00c120580070810300c0307100d801468106000543c0141240e000c1400c80740740ca4282e18080da01c40b0642c02c400c02480d85c01e0303191600c11aa18000176120704652401301a500c08c81084180c0c002c038503010300078100001d5117500c090b02c000b0040c82c500040000030310802812400f01074071800300c5503040e682e0303685400005500c0c0c0950001c2580c000009510060503013800720300380d80741c0003c0b82000005648040c900c444500c03550b200842e02e01d155460f1140009810b603a07542c0fa001d11511009006011040210320039070700414856a410b440a080541c4442d10307400d00170003034440142c041c5d4046242c000306004000d051400c803420f4825200784010051030100c18044007800c10701d00b03a02615070a0028905545007800781c041c2d044501800031502d40d4003940b41c4004141a121041da40f11300204181c2084e030646c5420740c015003a403107400330702c902325000860305521460b0024114490540058800140c000c21045e585000c1920100407444c260286200501030260124 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888244496 1250 888243246 888243269
    0x509010509071211120403030203100b0a0207033203130e0609010302090601031d070302010e042f04091407110d05030a3218070e0103030c08390106 65
    0xb005100c4082c1c0110640d40000400c2030305d054030410002d0700041c0103940c00c40020b44c001044c025200c030450040e50103070442c0503039145005c0024030301965441c02848010704640c4d0580000344400b0303c2d900d003060180b03030345031481280351041c10019443e13900c1740d80000403d5800c200c1c04140c070b8640d442e003203100c1c8801a10380350199003190200038564034000e0060f8101601c85040c00980c1b0035041c5180850410711008040903429031002404040c8840101d9004034642480c0f04109020402e40e90044030980f013040d20785c1aa0140c04e09c290303118076006482060b050a070030418212118800300d20810032079880032110500402181d450b181c0340030480e4009041400806c180c0c10b400c1c0c1c090000b4400340c04d0809040b080e5162016209000b4111a42c909030440003080680f01050840c2c8440045c00c1014000303c80c105010728080110601014041200e150071b040b0800000c03100306c403446100704054044021070b22100d07080d0415141c040391040409004a1000000d05000e4401a0364a06404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888245746 1250 888244496 888244517
    0x180213060207080c04020f073810060806030703120806040506060a0f2114011d0906040b10230102010f020c060612030f0a0507120f1b050c03010213050901050907 71
    0x20170000e9041500d111544141c10000c81000402e582d0b65109440a80500c0e01e04081840c480441c0c001e03500c1024400d0449188100840da035680c441c84005e490040c00d199046450b4000802d252071010f400040800403100710b0044004e410890180c81a54111820301266480c00300303000803402120400c10104800c0201e00e400140103421081a035103044288408844408102c907041e00c072004084c190b20003007600144071340003080340604c2d01074a00d800403500604183e000c00c1d0784e41c81e00034800b0b48080c405101060014801c58a100b0051604080c00303a1000744403c903d03030310300303900d00c00d1940076611300565000101d41d14002d0360444009031010300f07141d036140003c1c00030b045c00b11840b400c00750004028241040e0f0111001d40365500040d51030360f454001515000d8108008244150144007210394203d4040781d200310441d03a030301000140c00e064106285411480c046148807415850350000c02da078482c4840d094122011038000700d801d041b0503641c903414804203c10680e480000607045400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888246996 1250 888245746 888245749
    0x60702010206180c030712050105010506040b0415050f0c010c09060207080c060d020d050907090b04050f07050a020c0907020c031510150905030a0f0506060a0b180109180213060207080c 81
    0x20301503c500f0b5110a4424808001000074204075541d040000f5500c0c501800c80140042482a1800740c40280e40a0b450642800841c8030b260180388100c3e00003581d00c151500b0200c0c42041990b14036040104040d448180100308680604880381403e8001500e170b0000141c564070025002d0200e429010181181424400078002190301481c1e030003001ea40c00700f0099000009030311886204000e00d03c00707040c0b52401c107101c4800f03076000080110720a0b41042e041c001088100404c0c0390b04a4020300704543e8440803054181d00788030411020f01e0384024070000300148150041858001e641084080d1030228540648074402030700d06545a40c80e203143c024040c00309a03c92031b25541c5103242c07810010100303980c3e200020302e0014403180450300300a80c0352005080080c108800c1d50419002c480780c0301950306003c032481c5039004007141c2c400782510381d040b018041c1c1d001c0c002c00b03009800e410010300300c1e951007940d118001e03500503100400811104100080c4580c80424030074182c3e5580c00c003814030082c1440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888248246 1250 888246996 888247021
    0x30f15030607081311090103050609070b0903030405040b010c020307080102040515041401050a1205150a0602010c08040b181905070501020f030a140405040c0906020c0105090904060c21020304020f060702010206 92
    0x80d000c90f101c0040381c0001500f560f1b100740c000c1c020761096006006518003440450f040c0151030b480740300c0310b503001d111201240c0e80c0401a41c0c01c0c1c8005582c0007c0399118040121190741040234081d4050150100200784c030041034000b0010380e00c040d1a1800e00704855400e5524074441d0344100752481100550102c0a58451001044294ac1a04e001d41548800505080417a4410b9404a1113501c1c4280d06543c103086c40c81c4610001c00450008000f0009210f10181c44500c1c020401040d08028000180b0a807500d146400036480903001110b0065064491071180f51000d40f0003680c0c0d5201d1040001120b610005a00c2605402c01014504000c58800c043d200d50800c19120f16542200380000300320380d1036601c01c0c0903013203040d41d48009040380340ca41d000e4103002c1907980140c100f02080140c00002d07143c41503650b030840e07482440021030350700c82c40e001c69030b18a02c0010028a00301c000c1c8020001032598029500480c022130b41200c1d00c40240741000710368030030b6440081c05600058002858000c016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888249496 1250 888248246 888248281
    0xf05130b0705150702160b03010608060906130e1f020703140a1b1104050c031014030304120c08160509040f1704080f0c0402090a030224030f1503060708 67
    0x6900311465155604000d00084000300d813210016801806d80c10260540c003184507000381000498a4595410080c00408502d401000030340a03820a00119501da105e04268020f1031310454070822050184a40742a214207181001640400360f080342d001d500700140c400c580809505440d0444da01d5240c512020080e0841001442030049c03080e08050203c50304164801598450803015a04070704c4202000202c450140240302190014000c020304981d110b8889825105500900d10850f40c240c00040e20f584038980042c00c052200310003410401c940c42d40310006441071081681c01003680d2205040000726280b107000d90024110012401140b401d4240040207130140f00d4107070245081642e02071040c2d00540c803001e03242d80b20411820520b1001c6c801580003101c01c44041d4603001c2e4803c0018000407080c040070744036110400b60340d90341504c46003460400055130b904036038aa2411124102911104a40b0f007900c0b800300796204000c0d80380115005108810540707654030b49889800d038070034000b2121b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888250746 1250 888249496 888249503
    0xb18010801050621070e0402031611070608070c050703150204060f0503071704050102120403261005090702190f061a0a1427070314070819091e030f05130b07 69
    0x44101c068190707c49000462180070200d507065558003075504003c0c01c08544100e440c1054111807410f01c00f5590101e22103400503001d103444207242005080c070505200e01940002d141e140001c4c07441d0b0408400703070054030494520341c4601e08901d0607884143c941e0300c070441e1900c000a42900d03608402008030750107560000d008100040c00c003124a00380c2881e230300080d1029004a050715010603601000555001c40c981090100300101d410045d06042c0c041c41680212071082144c1400100014401c020607000301d1080c200701c58951001d4207140d045a0303540d002c151102d60900c440c2c04221024081412024800641040c0c1464681403c3d50200c0e81040d42642c1e00070000c44511003103000f0180420445e60310f80c1d00010013414a040c0c00303030444041e124050b10182800b82000300064004800d0340e40480c01115165401c58840c0410000b444091001840e51440c615603011212001e05d000c02854440d403601c0c615138404502c25203150258841c81c0c01605003680d401d00c40911404040c2402612 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888251996 1250 888250746 888250757
    0x62a04030b040c270c09080f070e06030c0102060109020f071707200d150b2e0305131506030f05100e0f0c1e041113090221040c0b1801080105062107 65
    0x7120340d801f50815180001042590340200760900a0328016010075401140840007042c202d007a2100107500c030300c41482400e1210758042880f054000383c0d6001ca4180c10340c041c0520076415000c512a0049030400281507410b0f1021030401090041c4103102c1a00e4110000c2c0341c1c521104c95542e5902c2c5810094491252480e00d90000409507200c1c824140c0d8024841130f140701e4500c22031512140d0040e030b03044014080508000034001110080c0707803040c99298204440d4015440c1000c1004043c0205600080425030ba180c168410b2190200b0344403041019030400784910802c041c50140c3e1403a02501100d238541047c200c503079107850051a5107800b422081808000300c40c800c0d000030122102192218501d04002900c17004c0c0094008042c0003030256603030210b0a101d100d480350200c01c00030054941c1013850700d6010406204890001d5001400c560724940e03980c08140000001c41240d9010090204a00308000704843c40c1c40400e942d80140602d90030001017004810380c20040d00040d141006111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888253246 1250 888251996 888251999
    0xb0606030406061a090102010b0d0c0b0f0f0d0506030d020a0b010b2206030603020108010b043f03020c01020f190809060d0e0604021011062a04030b040c270c09 70
    0x4042084d442038240e810308050311208550006800c1da044098503a21954070f040204001581640a08042d181c20a4240c0d44405403000d65128500c10386411050445c0080b6000d03c07040038503007041c1d1050500b034064441700c50045000b0b0341e582540210090072030050b03100520080308034402826602005441b2480890556140d07106a0400d0703800c18400030351202c10030310079035802c4041c144c014030030b08000b189021700e404411100381103016035418440c1095000030b803851283e0f1035090012015010200900d400525010f550307482802589070150042011032805854040784140c03407203024540d0a002d100440c0e44281156000040c0305034003680500c400c246e6001c184c46000102c200b440002e1000d4140384c0104184c1c43c4261031407070104681e0481c0d5010000b000704040f07800010605401003d1441d0254007005050f8154880002000204000003444505d1032814000c6009a86a81c00140c59001c03100e2001e556480210905000b0700300e9158422080c0d1188201d442586410080e0300d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888254496 1250 888253246 888253259
    0xc080c090c0a0903021206070908070e16030908120406050901090305090f15030109140f0c090909120c03031614040303080903041a0a030e03040503070e040c08151e040b060603040606 80
    0x1580b001b005500ea603006108011007913400000000c050b2000c10000c180f01c5181041d2416000300c01080002c034502c4038003011004078080e420640c0b0103503000010a40782d6480541d20f800c0d07841c0865058030180c0c1840c0120305030140611507280d42c0303074141d43d0f50361804010301c05100b50002403803200d94000c034004081c5445e084010001e14007a02c0c0302000401c910740441e2541c1c0954102902c8000b0b44102c4601344102d00e14414100c1e504444141c030700341c0440e520021900d00300184601e03a09112140050751600c42140400114812100d40d848800102e0700d80100310340d91040411740c4100024104401d0002ca4020707802254000100c1c1c2c02c0320b02d010344600c0380200c41c843c2d0440c2804d010070042034014101c0d4150040d8000a11404020743c2402e18000c002940c4c4c01c0039100e420f246d000c1140202d0f0600900380a2070300a407242001300d40f040070000755602e08082c81291245641c6044030440b10a8032803541046005a4220b1250780c5103458000400a01740d0001d8021181d40d40d6508001070135 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888255746 1250 888254496 888254509
    0x62115090313060203030a0c090e01170106080f0a1406010e01120507120606140d02100e0f030d27151101140f07020d0305100902030408070516030c080c090c0a090302 73
    0x143c1440d9001d15203e061400643c419901080010024403e081c581030010300341000d03e550440f40d542d0403110000c0b0b1048401070052400f508141068080c0b11b0460710000400100e100c031440c441c0c0a82107a03101d090a1191722400d0a00030700821030b0244004014050151411402d02401074003540c04069a5049212100441c2e05003207400d29201d010400c800d0040b926442ca5101c000da480c01b2a0346940da0016010640d004010310502c0400c0741e051081340c9601c000400c42d11009011900343c600e010f000503101000c000f5003411450790700c2c0030400c0400f401010034006c0301c0009200c0700956071480c0c41a14221401601540c1540d41c1d2002400b400300d503030301582d0141018500b407400f141400003009003006090041c1409042c20a0148000503841e12a2807085801554005840e038950740341c1800c441c07154220241c43c91060401442041205c038050600326441b8940f5410b0240e9a08030042d26001400034660780286070000148604035824001e01e0203520342d1030000e403180d481b540001c55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888256996 1250 888255746 888255749
    0x212030a0c021603061505030a030210051003020a090203100f060909020306011715030615240c0601061715010e010e1906051e03042d06060806062115090313 69
    0x3007080c1ca51b46030080c0305600e60349140c040e203c00c0e005400d4412041d180655079821100940c03003150f50b120005880c2c0d60100001a026546c001c02e49243c1540c0c0b040c10b05c01030b41040e01c040381d100c4820000091341d0200301c0c3c0000103c2d029a2911200686019081d1000b5040140300d0350510519010403c041019084c2483c4030b100140d8012032565202c02c2894541040102102c41c0718200c5581d8401d15950300405048000c640c01461f640944503104903d068001c001b5008482d00c43c080000c0b840710b030004203140d2100c020841c50603007070303644a400007419000700041501150543c4a01a45548038810185030214007405c50441229042c2c0704000392900d650115000a001040f10007444640040e5940c00d0910281d0f201e08509154640108480401019280300c1644845100040032103034600c0c1c443c00d4200008200042d81e48009a40f200b2041b100f451040140890402c000b4000a0184011034030003c01000c0d1380460501c00301e1004809880e0030b40030310007071241980c81e0402505400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888258246 1250 888256996 888257003
    0x30a061d1b040515180f210106120b180706140a020703140321010b090105071b0f1e0b0306010e0d060e010c140301080303040803041a07020304150212030a0c021603 72
    0x280d44001c0d030910300402c000c440724411b00c01d800002007809150f8460411002ca40b0902d1031507259200582c201c98010f1038103070b014164a409440005040c0040c9076a030a01c5610b040c4170200b81244420003141d2940c02c05e000d8003000c1901c4d00e00301d4418a12001c0941070001c0e05004031002070391a80c1b10240f0005200ca160080390b40001808003400421130b40c0402d8070b0383d070918030254039410000c01800d240110803030207040000120b0711380c1c28085412030344040d00e40190098003c00d41c4a0718220003d8481e40101d031441001a8422922010910300f0141211811540c0a0640e00c07284011102140004c3d13500d90301441d8000d6245c0845c46910455040702c0301c074400064102071640c0d01a0a003003c611540c0045a024801049040004002c40350b0080e48102e200b5a0ba40c0e03146448460602091030001200101008011002d90004001c00c01e88071034844460402c0782c0488203d0b074840a4110003c5500b8090011031101102d54200c00e0110b580360041c0e84c4003440d02100c8810705074880d070058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888259496 1250 888258246 888258289
    0x2190c02300c010201050907030b04050a14030409180b01030201030e120f220b04050103020304170313150e0a11031e0d0f080c03130507120602030a061d1b0405 70
    0x280c1d80c409081060040c100800e0000748000c0c50b020480903110b80c410300c4048c1c030b5040e0560000e000c00600b0301a8059041c3c0c0001d800c0c50b404440ca00260b6a5005130040300c00d0140b030008114040c02481c921303d42c095500184c6544540e0841d07004501803d04000038003100c0c03140c0f4031410007440c0824090302d401c40300741c00d100c0d071904000302080c0c45054403444501c3d408844454148010401714040303505179035082c02c01680d2a02d503072501c080b00500c00a41c5040b188000703c20301c4000b8500011224007940100d180c500390610000500044070300000c04544154083d08900c0300184650b0712404820350010b050b81c9804603081c41024011003010543e01181d009122500c00c62034226084021821041c588a0082d1074840144007c034400980f42010b10941035503508200402001000e020f01003482c0d0f140c4420f192460a071029400545d80721400506040d004502001ca518060101000064405071980c9038031034411070400c10600034060a000c1004081400e444040c1074030b03d94400130401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888260746 1250 888259496 888259579
    0x732030f1207050a0f050313081206010206010b19030e0f01090b09100219232a1b0108070c0b0f090f0705010503010501030c0912210302190c02 63
    0x5407030007070000b0101d0b0240001030009020311540607402c0009000103041443d40c0f600c0b6406101e601410700d4a008156103c0051042200186282d44500405007a000c8600030303603c8403200840d60207500d20708080741d5a4203007401c0740c1a100ba041190495000010303980c020500c00c0c00749094944408060ba904040c0005010721210b04002580344200d96400c21401c028424610150601c6100423690401070250500c120100003c4040010310002c020081d595142c6592400008000306603101c1201119841510b950100444c0c4a1005000d099840030310102040054620300c802604040403c81c3c040710010000700d40e83e404a010f41d458400301c581c94600048110320b480360800211615800100c0204001d076000001da80c10b65600342004200d0a00b0300b8002c80307060035079034040001899100c40c4c5805000185240d0996104c201c010342c606007002d91010b506a1080b00c014110030020304505041c014800e04d45034100a100601c4500c0945c41c500d08200c6c40704c0c0754110000a514852003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888261996 1250 888260746 888260767
    0x60d091a0c041202180405100b030c060301120804120c03020f0414070807210b040b01051813090602030f070906090315090302012406140732030f 64
    0x2200d010155800d00495114a403650300000349001d60b209400c18030800c0510710b811036440f25051520110b900e00035080030303e86802c0041d910307007160903d50300c49807501240c50224140482c0041c40040041e10403442d42c0d10304880051001c0701000280e95071507081c080413408a840440e06941240101201034000c0d041d801041010301c0301a82c0144103038500741e00c03404400e46400042d42c5c042d4182c14106559640c446054500305601c000c0381c1414040a1505174051680b98000460507000707890420109840d0300040d200c51190a26002c452220049018903625012060880c0b00c0d84940000c940c01b500c541d20319090343c0040e1036000d082da2504042108403540503074050002d003260719282c10758500d152100c1c1035810400e80704040058860080c50305141c000d40005050315507a0007504081612000558140340450088200044085544880c4200300c18280c8d000786400600c810b030038a181d2064042841d410b10fa410102449014544a5040003407010700f000394041200140c1e01d030b10304113 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888263246 1250 888261996 888262013
    0x403030f08010f030b0403030b271603060806010b070f08040b03060420041e080d050304050d031a120a0b130209180a030f0309020316170d051c0b060d09 67
    0x20031840380c6108807082040420101040213800a4142c00d0014070540c80c0000705012b0002249101550303c130103a040c0414404a50032284200c91482541a922210309803c500b501c0d01403280e445250300c050b00611614034840010300c816846003110380c00002c019550f400090704260b01240b00030b1408010400181842d02611340b504500b03c0f00300e4000380f0f00c00d6100d445070046018411030158942c1081070001d80210000c8050000c0c1000c4680340803841200074180e0307200301e401700c4d5503000b00780118101034028025031540c030354000c0c59010710040c03107001e004074051042045000f5100f0588030801003259444028050300c442c041c120544805401880b01400c03028146130340d4264011040c2400380000320f4503c00319641841c001c5079107000c01e0801c40c00b81c20070000c081c1d81401802980e1000a145c00345038812154001c90004c034003c003c90301240c5a406841c5080042030081003007440c08400c07041e00d40054400031400080491805001c40c2c900d822000c00c42c00e03d40e40c1c50f40040706220380034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888264496 1250 888263246 888263249
    0x210f0b01080c0a0e0106030c090e0901020a140309071404022101050102070e090c040e07030525050f030d0f11060a0e0609160b09010507021e090105031212090f030403030f0801 77
    0x42c3e494031102071404110905840052042904050b0359132540c1d03406a206040c10f0f00200800700c1c08040354145208c242d4000d601c50311082c000f14031460282280010400290385c4141c942c1c8018084051400b24901c8148030300070400c5502c10750810004c08080548000b00b0300c0030100c04101250b42d1f0425002a00c0c01d503064006400c500300713100030489080b00000f005403441c5000d88012480400805040f883c160190300010703c640a0880c050801d101c029150035000f4100c4e00f002640140c0d1f0b0014802d0180f06c215080e501500400c46e8411040e0189107990b0401045d840c14000080041100b2820902c0c01e1b176003010196200c0c0542c0b011b0540070880580c201e541c01002e8800e030504804034041892051154040da004007048031045030303018801740c0e40c2da40d4002d45180b8012940c01c800c034141d0480c40e82d460303203d50303000c400104031402d0018034100c510b410110700c0340c0381583d000300000c100d01300146602d41a1103045060b4007452018000341009500ca5210880c0c01c92540700084c1921405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888265746 1250 888264496 888264499
    0x30f09062c0f06070501092003030d0902010905040c082706160207030602070b0603060a0e0a1e02150307090801150623041d0c030709210f0b01080c 65
    0x907211440c0a644440d003000c1c1c440c8025000c0307125609410010581419460780700302c1d071095010913000c05206042d080300c900300e4414176801c5085030160600309502240155080d405500c1400118540380f040e9010b901e00d24014100011410b540d400010706448101940e20300155012091008000c0c41c400700280c2100100f91900c03071440420003d9664150007080003117181e06c1d844400320076900034840382c000396400ca9402d40da0381b090703400c1003c030f041d4081d15010f0091180c00c2c0020388a98480c8904140900e202c0060601c0c4e02894465040420103510204082c003c0801a0001a0781d080542ca5811052031031041c2c03a850040b40250080080390701a010b1a4144684d410701c40030b0700b880742c0b001d484003410301d5200c0c0f018400d03c9a0701c0c1c000b1119001000100001d010614000071800f0a00382c0071041c0190344240d581c440c4090640c0810380f4014041088a1014041c02041c844a01406001c103025580380045d680c4901000801080e01505c01c5901c031030041c08610824060007a51600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888266996 1250 888265746 888265757
    0x20406120b090f0723190e041e022212051605090408030411040518010605060f03011712070303020721210e0f010b09101d0a0e0307030f0906 62
    0xc0c41216812214402814042004005d800c0402d400c241910003103c032000c2503130401e84031140b8491680c00400b0800400380801e1b106140302881e403600d4043e0140c00c4400c102651200078200d0185030180d045804060b50703800188013900340700b00400d4070790801007500300345514020000703041207801e050543d0344046061600120034402500c60825594002d50f012160594a681e40d0400c00800004c1c081004d0384141050b00b40302d024165114440f002180040080100990743c10800c14644101c0a08000402090004000b941c8941e40aa4864501355040d02c508c04041720340206030303030b01c00807040f008a41c0c0440c041c0107204614103d01c1a4000d01101c0c40c84011034a030300503000f03014845107500c0b01d40700901c41c0c001411089c4c001e109000a00d0046418642e00384100c203002c0c00c0c1e01c402090040c1000d0000400f5455100740031b8084901d19506031002505c9500c1040801c0704c0207240e09007003610380c2100d00607a1400c000410925010b90b03510250000080c00003400980c075a07101004124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888268246 1250 888266996 888267001
    0x14221703160308041110020703050f07050a0306180b01271e090c05030a0f0618020a060c0501060b07060c0801144213080706080105091306020406120b09 67
    0x8803003640c5201c0c0d0142000003003503440b40303440700548041c0580030340c11007414108500104d030002007a4041d20700c01c0c01659030b20100354020580d9103403a0312540f548500030305070030000310f800b60707200419008010107030b0000d45159850303a60b504a021b134010361800c0780c941a80d1b81c610003645403140308482d1380201442070302d5614462507690f0710381d07040401c06103682d5a0341d00e0030021010782032801800040c040e40c140d0815400c0040c00d00058480640b4098207104018144503840140c0008180d402440141d0351030500404451290322040101e500c0d6590744004500d41005201078076817680700340d0011960f40b1251318000c29103030341a80140881c02c1002c0c841c940b144c6c0c8861814081e07604d99200344d8103400621142401007001084011a0100900081003034055044000e11100c1000d201d407007101640c44100d15942d401510940000540600c0144414a440980260400202003c01c1054951030310b0b001e080303074025400380300459545881481040041d0151003004402220545a40e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888269496 1250 888268246 888268267
    0x60305060d030503181f0501090b031e0f0318010e030a240b0d0803061009081203150a1806061b060209130e1e06070e0114221703 57
    0x1003075440001c040c4040800050311a02074002c13120801c061901c129441c141c0504030022601c20203016400e0400e0400001103034826190050702ca00c000041c00400008040c00c040181003800ca41038007003d0300034070818412005080014000300e0009405020401c010100098460b175013128001c0e0298114802c024003080109107008003070100e0124a040b035030244000034004188d110740e010760229a00410b0710500a5102c09036100d40e405482c0d500170501c16000581d0600454415119180c0c020908520703010201e202035a00415641a915641a90580012510903482c1c2240b220b150458644003607075100c6004450003040c95040040c4410004002e0503002c0082e002c000c3d20842d0006804030041d1550250414030082e005000c101120405410a49074545c44207075001039a40c4086407642d510001c60494080c8400d5100d0b0206103412000541d11800c2a42424400f0107003800b9500c420844410503a000c0b2441e440941d20b46410485605510010100c1a403500c0d1310a00003140c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888270746 1250 888269496 888269509
    0x160906060e091503010b0319060509070e070e2b1707081b070e0108030d0b01050c0307061e0237020d03020f040f06030e0c01110c0105030402031c0503010f06030506 72
    0x10082c01e80d95004000401c101003400740c11a40c146c2c1d9014415900c221042c241d8001001124030300c595024005500d5030113a00350760390240d0041e80d07000c4045001207010140120342500540c40090180210038072410302c10000c090110b12001080c3c609880010304101902906814a032142c0b605141000010b031910f51450044825030b07905000392200d94a18484104580402030440e40100440c40da15080c02d151640c00400c0007240b09408d00c2c1c000110b82d800f50b0141c0d00c1c2003040340700440c100001341d12210041e00ca04802c2d80380030b001c1c0c0040d42410716400d0000300380c0d8002105958420700c101481c4582d24403030301c00400e41031121422070460070070390200703081140c3c03001031a0158541100700400403d0b8401e40d8001c50480d0b04405002601c242c05400c06903072500e5500070341e00c0c500c1442d001540d00702c0500350074041b0b41c2c02200424041e03600580c0074542060003d001c5807448882c800b0034190506038061b106001ca9804801003001c00400303102c90b40682450310f002d101d030f07051480c00b1812 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888271996 1250 888270746 888270751
    0x80105090a061a030610030c05030c01080604090201030603140a0c050a1a0a140a030b010e120d11010b06041403120c0304050108040609061401090b0904020303070201030c020f160906060e09 83
    0x40302d0703110035410030308020301c04040c071195000506980403070500010305015400b862008440455100e100011203160101d584181e13800b046c0c66552050350b44004000040400c104124140750f038440e40880860802c00812204c6002c10b40281705000f00d07070811118070541c42d40058480c1200c840d0034040b42ca1505985524040c10011007516011401000e940c0c0100c10b1001e8510b40300081480400b40d641074115042e20002030f05c4482c41c2d130741002c091014410365a4000b07107556208500f07128200d881040f45c0703491005148000200c4049680010b0369a9000313a021441d12125240906061b24051103442e001050004100d440c154005400540b00e014a2050303a040c0b084190015040c0003054100024050f4010f504106c07580710703101c904071100300a0054082d40b0346425118100c50503c0d580c140e005640047c01581400c070300b940114098004203a5040860060200400c0c0b080e0080000d002c050060001c030101d5941400b00300d0741112480e03441201000400c1801e60700e242c0310f202c0c0c1143c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888273246 1250 888271996 888272003
    0x1115060d020423040b0114010e030c0909030d0603230f1506010c06021218030702130513020a060807120903211d0a02030c030607050d2f03060109080105090a 69
    0x3c0e80c03894a56030101c40004100251032001404002c02080002102d0007a043e110046607401c80c000816004603100d2003200c10961305130744054020012841d0501159038814031900440703142100a01504007aa0741e81c0c0c0c0200c81303000b801110074801c0c681c07800e0000d491000310002401030f0320010604641c0ca4902c100c0c2d00c1144e41d015404154107912428500800c6500058195995402c040b130420100c0c6045030025800701c48444a038180e514040101c40c0700d50f0700100b1040e64484090000001044003034442d102014100030004d005031104a0800010203090710380002034a01520042c11032000c00200742c402030310786041c8100103908006415070b20240440102c10715442086010010012600d04940c2d000f4030101c501c401000000d41240c031148254242c81054404c0c105141d40d8078410750324480070600610000e4603100300c560101c0310190302d88100c8000241d10b00201010319200d1240e01a8011000040000c2035811290318070007840c0c0f2030020440d40c5812484240c503191a8078004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888274496 1250 888273246 888273251
    0x70507060209040615020616020d0903140102130810151d070c0203070f170f0c0910120c062606040b0d060e0606010f180b0904090b04031115060d0204 66
    0x1400c040d12250701c5074002d042c43c00309102c000705121700013030341e5014200c41040b41e03c10140d4040500501c041500f8070090310984564030a5404c581e510310185241102a0040d90b500703004c0704040c81040b491440041c800c00020748944000751788400103413544207460b080b852100010420200300745640008007404041c0084e9400d46508004481c4d11443d00e0000c0c1d13043c8079020003c54849000c081040c122490b030084404068141c0d110302d51201207020400049410440108545040446056900000307402d686451180c83e4420340007103c00190301a00c1c4a07105110501c0050780050381041032180850503101c07180400d9450b03240d42100100301e41e024a40399200c0d000c841d12821004810a64020810b00405801d840e0b01503440c07500302c6003503001810b00c1001c94841402500030001c0c0f441c0d071441b40d000c1541000903c008560001116a412580e81c6154902040d036038007103180130341d100e680d2350428030004000c2140741209000c3e003443c4141c407030740c00e000781562450340c42c80001d80e055070302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888275746 1250 888274496 888274507
    0x30405060a35180a1e1b0603061502010905060103151805150705040806041112010f0b0a050109050d140a12030c0206071d13150605070501050a050705070602 69
    0x4140c0e4124070034004041200e6040400c011440c0c0b690030b69108540002035a5403070740100070440c0d540c81d00d012001d0668a010074110921507604460282c03403c1c011070440c80c03040220516011070f85100e5211000007a6a1107003444011066080d00c0c150720420b2000380460f51942d220f040e02c4000611004000003180e110155190806410a4466001264513501c0340c1c2001c0c03c00e00e458003440811103014106220016039540d00440c1690243e400c1540144225500c0d5569410010005003640794494001464024191024052284032440c0b41c00003059402c0d4040510076020502c0e08018180030250506002c0d6441e10510800c0850704000c03014511248042d906042c011155000380011406443c0c2d4000560184c0109c8070450b41d81d42200c415555440b0201d07103900010762101340b500916020505585040401a400544e1904000070401c4260a0426800e290b66000700d011031004600704003805000c2c8105684030410403c01d016034544000000d0162060301402024150302050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888276996 1250 888275746 888275777
    0xf0603010e01020c010e0706030e0a03050c010212010603090203060c0f0f03150a0305070f09140c07150507020c01090b1612111203400f0812100602030405060a 70
    0x98900481d09100842d90b528076100880e0180a00001581ca030b441031400000c1d0725803192240c00b8401504801030060442c540d43c045429078003541c1c0c1c610f06c039074007400841410058040b21030300900e6507441c00a64030699105160404200414510030075900340000407142d20f5001c04c48040c50540e15050782e40c6d5551404614200f00d01085030b540100c1c5512002c4100280050403c1c1070754141d400d007040d1180d54107403c00c191150303001071560561100010032005401900a001e0383e52240403030500740b41c1b03011011012900212a5200107901ca080c1203125541c0012401014140c50b410161800b40000300320204081e081100418411101c0c4a42ca40d191094482d105048422401c0d1140c540c50000c0c0442da07900242d4110280500c2042d0158400c4031691848a08000803000c3c080740c40c50041900c1b240c5141c004040c1c130200d002d10806000100303460000c002021185911034041c0c14045034013245800b40c0c0e0440400d45d4001c0000b4005561040c1c10340710340034504d1410501d40b803c4201c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888278246 1250 888276996 888277001
    0x13052d010c17030414072111210730030807050708040e041a07080106051803010e0105041b0e010b070c120302010b040c03230606120708040309050d05060f060301 71
    0x8140381010000700a0108010300c0e00c40c20113121700780c08110360440303440d0b00c1c400680721580048a01c00600d01180040041c0302c18595100a44004020608800f0384030b407441031048603084005800c3d04040c006000405245400103449444440c110300c0101c820307585481608070450380503050041c001c00103115035100f0700131180c07a243c1c80968991a90b035036070304a80012009480803101245822100d0120551440c001480381201d50b4075000a0391801b4000d481c9544135820101181181052400c0d0580f001d005d0302d40320300b0545000040500d0f090230441d0f90220b402c01800070546c0030450800441c00303070840443c10744055a40e03950350750841b071901c1d811b6190b15900c940c45025004071004103268041d0710036100d40c02c0503203003031100011620382141200d80068a2150410720407035084242c5800507000c0c0ea010f000588070a00d040030001c244803010008461002c002901d007820081019071111103035005220603500e440b46511180d850984401c0300425844003086044001840c0b03070307000d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888279496 1250 888278246 888278273
    0x102a08030615070c0e0106090611101d0102040803090406050402070b0a1e050c070b010b0301050102032508030c0706060909080702120c10052710080a1113052d010c 72
    0x410140310190b6881008072980e00074400d403004288c541400040c05402524a242c005100c04094008140400e0892004010851840000c040100b00c00f0443c401d0920040014141d020000c60702c41e5039803001c01c03084d0380c402c0e04120301507401030180ca400510352034803440d003143c07a45a0100d160568409020001e060065800588904100910045e182400000d1a179280242041c2a00d41c2c8c86100f8030040d03220a20549005a2040150b4012200038184806c510031041080c001c40030502d840721440c5800507140c1503403100c00083d440c01040f500d84540c00080c045200d061082d1040342c0c551860600913200064040c40b0500400413024000380180000003030002c00c41c0345100c106c0e440040090b08a03110109000859904c80b21040701b403000000e107640001815260411250401100c190402401564042e602c0d10070f501d48146010001e0842614501805180709103000204035000c141504e08c00c0c9414900340580e40800c4651030100c25500e800c0c245601282405c0c940200e40c029103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 888280746 1250 888279496 888279503
    0xd11030a0c020c01020705010f1808060a051e061003090812010b0c07092703091211040501090504020a0e06030c040203040f0c32010509102a0803061507 67
    0x304050030341941d11404101240750308455409040d14010380c2c0d1090980500d0380031400da0004500c1c52407207031480c107402c172061030940d04505584110051401750305891a0f80d1184c1c0741d400700050892100814800e0000b454403130b04440c10100049000050300c0203a1108140c0c941e035240c1c040c08041c1040725807103952310481c1d520315039465200400c0e80c0c01400300d201d554002d00600140b041054000c1c644d58412500c84031840402c035512000510611003002c909200c0994000148007107066440710425018a11164a001030b100c1048211407058001c003800f01d00e1310040c080561075100d604029201003101c0d00d00c3e00c2d1900e600107442e10b00b0307103001142e1041c0000100402c2202c1d9059094440d0720900c0180205510b070514626031f01428601408521580700740300140080c400a9071003214810305001e0314095089000c40da65610300c43c000c3d00407449400011483e912410415122111101c803000a51041a070320720207540700140c00c50b44074003050700c915403030000c242d0101d03025a0b91 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 888281996 1250 888280746 888280781
    0x2a07050607020c0915091518010e0406051012170d1104050a08060906040f0f020904050f100209150903030d1407110a0804090c020c2106090a05060103080d 68
    0x40800000f0b503210f003005050750180000c803021410b040c000041440a10400910009155507800154a440070080c054a6403006107a1480031103d40702100b0301c0d020300501c0b5811545403509003031034400d4a00180c604621240301e41420040d070384825641c80d8119a01440000302e030400c2c4120340c03050b40180310505161900c2d0045260010707861200038011503000b551611740259076100071395120881181e03d1845900100c0005000581443d00700035002c3c85102d01c6003612540d0340214500380390071a0200d441e0b80c40903016030854501000108500e042c2d240041d484c0c0008070700815100e00303030b80c42c480102850129460889540500c2a40d916003141320782003081c902c1c201f0701c0809001c01502e5100114608908140c07009401084d5590302d00c0d04a8459440d0520b4495208001c10804040000318043c030701301101d0a9445090100e2501444200d10b50b0540c0104059030410350050080b0f0440e0380140a8500090804140141104d070805211515406160300e00000340c1001030240b0708111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 888283246 1250 888281996 888282001
    0x6020a02030a031b0203040e04052a0f03010911040c03140411010f050702060730030f14010e04030822080d230f07031107060b0f0102062a070506 64
    0x15800005852a0302040c1d50902410500920581604d03039013100c4400184c104000500c0b20341b0040c0461b9810501ca801120180808034000c400c5007800d884008015428890000081d032a0241e8901d042800c110000c202c03018196844204580080c9000780c001c4c0c4e00c070900190b074280254803003541840d000c41080c0f550f24041c50a0200c07100e108100c3e6011521171400495641e10807415141c00b03d0340a8412458141c0c0340e1203880e43e1390700c01c91380b1900036a1300c2c0c1110b00c1c10105c10b500c800d80080140d1800300d0507204903107254080d10b82111040c106040350300300410440300d01586244c2c0094040c10224a02e4448080044400c241c400c03550317078420380f8043c039201009020002031a40ba801ea81c010030414100c001c0da208210442c001641404005c800440c4100040011140e00212316050000e01d11402000d46420b81e084084260b4885076104c0d141c50050610094075250075000344040c141925259000c80301d91422044140150714280e825040c030020701400300c0d5441c40e0002d04480892 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 888284496 1250 888283246 888283267
    0x3050601080708121e0d0b1e0913110f0420040e01090606050a030c091701020301030b0a020708220e0a0509010c0f0507030c020406090608031207082206090602 70
    0x7410315102d00300c680e02c50502200707460030f501000d0b076100814182c0002688034111500044d20f410513400381e115280d1f0340440b88459079481030b5043c960162400c110203000003000800155a20003000b211a000e41002100e0004443d007440c2e042415084039040105c541401c0810b0003130281e01d0b045220380307104400074100300c08481c01400846903083c0755003045a032102c000905a902030f10640020940c1405609009400b941003280c82e5009440c0241a207136607114101901240c9030319444045c3d41c00401441404502682c1c01e43c0302031589400d502e4039200c3d030b6600600d441010441420202040256091010313681100f0005240641c04140c00d820100400801407009958042e455868000b422007020301a010000c0d40c00301e01d0303c445090070100c0d2000c0d03440c450001c2003213030b016a5905002c03420720402d2003280041c001070b800640d21881d4003101010305000207000c03a4180b014000030820000481e81010f6042d0600c40c0116a2011462405401030210020000c01460000c20b102468 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 888285746 1250 888284496 888284503
    0x22140a0519051e25020a0c050114040b0a030b0619030b090708010e04030e03030a0905041505100f1b0f0b1f0302130b0a0e06010e0a1404020f0403050102070609020114270a0305060108 80
    0x186d5004060340b01c0a10358500064034103501000b03212590200500081000388018406410b00045608004c64078051540c005075440e40900c2e0a4040f42c04c50f40d03082120141c1c144034103404141d09583c1210b083c1070110f800b501415051040d0301543d103408000800b00351141c0d0101800c2940031b0304481e00d40406030005804040b0b0303400b0b01b0303005600e4001400013031030a001000040b00d6000d40100e44090814104440500705042c20b1004d002189414944c01c0c22411a000045801507100740b585221602e4540810003000d445080b00d8940840b1104a8281d0351002d04101c0c4c0e412141d40e590b4010f0402400d001d071480350400c607804041000b0001e903060007001064401d1800740c1c0c1d0803158002000400c40c1c940242d0140200304011000f07401002c1c10305a00030181c1d06140d21045081c65541d0303441c1d60a9a015400c201c445c82d03140d00b03464085507044500740ca040e20a01c00c00b00c0c14141c010401c4034602e2001030001252441c50841170f04240c58648064001d141c001c07041d5542c075130b121071210b9074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 888286996 1250 888285746 888285763
    0x2b090801060b181206241c06020307210219020708070902031902030f0403020c01030c2304051306210b04030c0809060d091b030222140a0519051e2502 66
    0x40d1b020304104244103d240ca44401030740a401020200300c040030780d0301c1341002500000c24540501005000e011614207a500b001d900700030761140096910325404810300d000c0c0302804d0b103100555000c03001c00c0c480400041644820344045480050f26030360b625800040c0b00c800242c4c4580e0840c40003090045d60310203080001d101d680281c007110014002d200044003180e1005007100002642003507156101d1a81d541004035510000c5131250a068940c80041d90035410200540c113910713640e13241080034408034246005035030601004100701c07443d0703900d03604d20751000200000d00300321044c0b100307008107c0c0c010242c0d201900d001c1d114076100c003081441e0200900c8098801d44d0002469202c00041401c500307248402e0740d6010780414070100c03074040c0b11001704481048400241f91500941c02c00001c3d091400c0c1d20954808401140604010034842d20164200c0c0502c41001e05240c1041140c00001481c65171003481c0807402c8000c0c0d650f1a03040c150300d0b003a008a4001404030081c00a0b80507034002041c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 888288246 1250 888286996 888287041
    0xc021914072903061215010611030703050a050309101802091003170a26060907140a12090204020409150b07020907112b090801060b181206 61
    0x280300c562941036090048400b0a5102c020b0800c40910084a0310300c0c0e80915004640a408413000d01c00307a400b910308000c00d4040152002da42c410042000a902c05000c00706c8070f19a4024510700740c90b68800500e18840c04040000340400007000c140810010090b82107210903070003040144203003010248042c64a005c1c0242c1c03043c084040402c01f42c4400c0c16502048a0740603031203880c03000f03003403865001c1d580240f0b600100307008401882051070b230003400020500c000c039100c1d5850ba031310b8010300708840301c0d01c090400c0c0c08200607000001075800c0901d00b15240b25105003403421908810034000c001a00803240300940190000c20005481c8002d174000d00380355286074920056460b00c0c2d030510b903501c0c0075a050195114148002040c59540216000640a0404425181c002c402c0109107020743c400315241e0556510040c00700d80605074000101400742541a0007400014640746441211713004490001d40b8002d041080d400c0c20b966a51044080700385013109a41031850302c124030801001d071081180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 888289496 1250 888288246 888288253
    0xa020909070906091517120f0d05160c03030b150403111f090918050a0b0f090a020d1118070521010303120e030c010207060b13090804090c021914 64
    0x200e040e141c03034005c40c03010146001140038a00d1038100d681032036030f83c0704034281107500650104071040c840b071a006103005049294140c2d40c0c0d03030052070040c4c219a4014000b45c104811884030700003441d0300c00c0012403080d416242c045121540d41c4001003c00408200d0040d0340c400c0001c00204011340801c007404241c00c00c0728250941c2c10b0048481100d610f20f1540701001441d0020b0501c0a00002d5220105944d051103020b44100780aa80f501d24280e0310007030a07a4200940300801c5420070074a026160b0258801000d8041006c032503004ca4414803400a00602c1c1007805060000c01e5100c1c6001229206c0a545900c43c140c10170030000f4003207a0046440f18566606409080340c10b0300d40b811400d040303d81c10b5694030f40f440c0e54008610b0061040fa8120981030008000c1c501200d6001d0028011050103054000303000d0851004000c0c10980e082d0f607a02000e410105220049040c042c180c43c00c94034000300c0810300410b6101d00b02d09191001c0e141900d807070b803c244500144054002d907880000d140f4000c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 888290746 1250 888289496 888289499
    0xf0b07121e0215070905030706081302060a0203180109050625021c17030c090907090f0b0909060d0f0201110c0d0b07080703060e0705070c0e0718061b0210020a020909070906 76
    0x46a084095001b4140c05600444e000c00c240d501c2920791991000c0d1000d50f4107600d0ba02c0b42e0004182d548040300342401680082000da030840034407011009080801d080070b82c102460040841e800b03020741d01d2074404280c003c8040b4451140d180d0340701200c80380c1c0280841c40601c4880040883c500d202d000030b9070740e100c04400c550000c0118404590017080e41d45045410a1520b808101a0400041140c020000d4400f00080c160449811110280100c90006501c4001d074005004a69000900c4148a15094020940411007190341d40d0070961702807a04a000f02c0c40111104d2600c0e00d401d00c1250405443d0710001c0a106042070124003520305a40c5412140c0c64681040302622064050000000c0105021461140c05140240707220b0348900d04011a0f03a55403400000c0125045540002050f4400c00064503684440b6002014140a04042d010011880d401e090305039134840000b80200d41e08404016004c0c0204030325041300354001c00030030f141c1c9000b046007034035130280384541d22200781011030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 888291996 1250 888290746 888290761
    0x20d0209090f15071b03050903010e030301060f02150105040c09120b15040b0f1306031b03050705120c1504080a21030b010804060f020c1204050a0f0b07121e0215 71
    0x490040701c03580e0340d50348610745034a405d001079111100d0032002e01208200c4444903440078095100c01480170806140c80798904200a881120103081000c11900480c0181031403c000f2402e40d415a80c0650f00020740c04804041552082034641180d50701000c3c0451517000c0102050b1964462151204020409501d010511080e5146a8002c55210081100c54881401e140091403103440e0381180108007942e030b98581030341e02e4844040103103030000441028810b10408200b41c0004210031b0b168842501030003801540c0720700c1610080f40c031500a240c108203042c0881000d5601138003c00c0d054801d0984c40c1e10f08585103076075614043d43d040c00e080d0041e4042500a128004440f04180c40d500c0351981c80c0e9032400002c000c05c00034009000c0d4248049004070704100b21b03d504a03070700e01c00c07043d5603541858100113100c5d203950300013030480480c010140148814001038504c00c0e54030405480700b207215040159100c074100e004400300441c05a250001941d4009280004100081000d00c0c694a4200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 888293246 1250 888291996 888292033
    0x30605151e0f030609060114120402211f020403081c050109020309190602070516030b0c13140d05160f210318080d1e020a0c12020d0209090f 62
    0x1420340c0b811036018800100f0030308001040c603510800515141002101164075001d85400104c1e1070008040010b08003c218180900002c40c02040305d592105040741c0c00c0301007030f92442c0100e00c00c0c420300c50b00d00c0c81d9405482241c041c5c03000307103600074001e68a408200303100c0c00005c070141884c54006c1d07040500000e020342d003610840c2e0081c0c0b96034018022413403800881100e901c80b03201341150070550070040369010030f40c10701c84042c008600a582c035000b5032070743c281140e00301006000c121505000308000c4046e1004420008100e401c0d101c40d02c45540d46883c001403286400401c054810701800030f07110044031501060a055801042c600ba59031500c84400d5074aa03980c8984004100c84000a00c10200e4052442210102c0a01d4000482183c40b071503283c0c00c00125580041c0841c0c0312804001415908012a00011900d4401440e0000c0d0584405503450709901c0355101e059010030348941903445481540419940213040c10350607040107001c0d540c0d5545d075003a404c989030242400a809410b40072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 888294496 1250 888293246 888293257
    0x50601030902060d090807120e010f0f0903021c060c200f0a240608010507030c0c02030d030507030f060b040602120703084002010906171501030605151e 67
    0xa4642424115140e5000000b0141e821741070300d50074020711120340011044801008504442e88c0c40368101500f03007001600c18a018002d038800c0c020484514000c2540c004200710032660111030003800910306000b03400d106030030900040d080e1814180c14414164000c20b040e241000a800722003040c0103480642c94030b61994a903030004507001041d11801241d00055020b1305100014041e81c10a4091040c0101311283daa0186c5004e075140d404000c0500d40612a11050700140c0c1480c0b024030040e0f900090f11341d6403040409092590720000305407911300c41d90080007142e1645004111260b1501e5101b2410303045441640018810468194140c800d8101503500056140d21120511f444d410202c0d07070400d10f500600c0c03035400040d00301610951a2950000b100d62000c0d59480c40071002d5000050007444960400c03c18001d0918042c10104000803015a0040b500c00500e64581380900048001d44a1940440d91100510081003201030642d00104180200c0c080b900e14800c0300e00240c040c81d4082c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 888295746 1250 888294496 888294499
    0x10207060e0609030f0604030225060c0b150406060c0c090c0801061d09011412010e030a0c051e0607080646080d080f040b16050c01140a050601030902 66
    0x10500716045814080050032441400800703071902d00c4071400d2001d1501c10221000d50040c0c4c03002c1100055030301e420044c030700e0083c000d16400810030b080c200058105500044010201908200041c0550210650f14800088028000e00c02103603143c07401800c1c0241c000050741c80800304540045e4021892013050000742e056243d241c2d06078a01081a01d5101c42441d040703282e9001610301070802d5840381f940b42d0180c0254103281000301084802d101841e2924000c0300035580c9081020007030501e0000503200c095a080ca49841c00c2c02c07682c034201d4140b1105001e0180716448080c3d00b100c100c50041051342c0b25028503500e2605540e1690100140480080c08021080122a0390518a103a00d600c001d01600b00c00980e0081d814454000c080001718a0b5200c601c882e001a01c0c0c1440d00c9074070000d00d0b500f1440c0d03d00141d54504107a218143c41c4080030300324814504928011a1500c2e00401c103a0314201480f000800007142c0c8104405200c1d401250884a618504400168030398040e00c2651741c010740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 888296996 1250 888295746 888295757
    0x904020906060a0201020712030c0219020906040f0b0301110a12110307030203040503090a18231503150a09020406050d12051b0a111c0f0204051e09060603060601020706 74
    0x314030702405010750000409000715502040341002280101d0034403610402c042d5800120805003450013405c00707010144406560241070030307040159551881c9150040e41c211000240107400c80c080800030a90400c545806508045150442105800c00b0f0b08218103561624803100d0300600101d41250340141ca0800c0440c0180701244c3c801d4441c0d405154030901c950122441c29501600154001d95150310441045441645042c03903a03031a801190185141106106a071240d02c1d2560211800020203005110030850b0711031025540801c0038400301c000e40c0b100310706d2034240209800041c0c80051000c0c3d004174104100040c103401c11980034442a42c01c564010410190100100c0301c0e41d00222604070440408001c0742b082e030a00b03200d030b00d90181c460040008a91140014407000190300e5200d80060825403c84030046081c2c000c010700b83c0ca6046900042135903a80c10002c5250700d034130020045c21980c02c82003100d0309100140c154000d800843c110b6511350340e410012642c91569002d00d500140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888298246 1250 888296996 888297001
    0x8060a150c0827032a1302070c0612110a0e190b0d0f05010b031902090415080a0c0504151e0b0a02030301061d06030606090406031b09050609040209 65
    0x1446401c8001d00203210b1102c0c180703440000d0a00403e543d2a02210001c408401c0942c242c86243c00c101c45072085181d44600f001d080c820940c14100905d040403014090041409007030f05000017941115031041c0e02100d00740c407440c0c4500005141540b1049000c140900d058110080f00880c18195a02d040c4c1d00e03a5a005d10a8921051100082d0f002ea40387e07138402400103001c17401340e0040001d0710b181e50308400009048001d000d400c80c10b4440680c04180d590701d0400c28005500e6510b46207002c2154902f10259403144a5404940180002c4000500320710300082c000c104414041404400c40d409100c40f204501d85400c100021501208605480c2a840e07640400141d078401c0700700e1401075030000c1c0d2101b80d40c1d43c0704200d814541c440c80820006130000001404182c0c0c0240200351440b1104024445110306a40418281d01c00603012510800000c42c03229030359600c41e0818400b442c6d0145450141c840384008603000d20205001d414400c9050000040c65828011801d0740b00e507400801040300ba4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 888299496 1250 888298246 888298289
    0x2010c0c021e1f0201140612070324020a050702030c030c090a0b010201020c0f010204030212030c0607031a0d05100f020304050c09040f08040608012412020a05270108060a 75
    0x10692611150f800000e6002c0d00000003441c040046a80744040c0c00100d52155182d842c0222a0401000c55105030f0480881500d034403000100c0506803a030001815185001034202d036039405040c6c40c0780e59400d80c0002030780000e86a002e1302030201c1e64401c1d401ca600c04000c3c4c01c101900c6400401c0403070f410641d00c50008514152641114803040810700005181044081005040090110760043c2c00c0c0c0d00000c0c10021800c0980c0c0d41c1112444000146007440000c90306661100c0000d80682d08060b141d8000307000c11108000801030320703c0c00420b00c4010801c1c0e0720300030340c035141c9000007002070900c0c0068003103064800e4000c40c0d2103203070320801a01c603030480d01e400c0041650028109aa0100c1e861100c40005100580101701401440e207420301c50f07603d0030064092003038040035030b0014062401c020746a401d811200f00c08200180e40390150f11445200d00c11103103070040b0007107010000034010b040c3c1c0c140a010040d20764080000e0780e400145540b41402c0c440300c10751f10b01c900e034041c00c201140031a20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 888300746 1250 888299496 888299539
    0x17011e0f0f02041d130503160201140307080a0605191719060e0c0d0203031e0f040f08061e01090903090b0d0e010c02010b030d2105070f02010c0c02 65
    0x140c85480c90020700707003404034650001c0f41c0140d00048601d00c2c0021442100071014840c4550280400c4c2d161280c402036550303904d450b400b65000740c0c05c28661b04043d5404680c05a130619844400300c208540d20b81ca40031800500c086005d882d140001d81c5041008076442c10800c141030b244180c142030000419107041c07400d00001c5080c40041d0124010710748a1101500500f158110180c044d0002103420b01c80202c0303c5090070200c032080b80c400d000190507440182c80200075100c4201c12500c0d40c0c0b500f80381c07000340d442042c0310b46180f0100d42c820003d004100004070b500043e06440c6980100c0b501a56280c035040703050f01200807039a80b54680b030740c01001800b07103a42004010354401e1800300c90440e40d0303802a1140d50012103600c0c11444c0c403588483d8110b5000d20481c2041c41080c4000e102640380c2d10042034460041c400694100081c101040074048501c40000030708841c0c038001040103140401c002010b00764008040e1006500f010411554103200d0070000500c03680080c207190305c3c0e40412150200707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 888301996 1250 888300746 888300761
    0x90f030c010e27010305070312020c0a050f040b1203040801051305070b16060f020301051311040501051e07030e09010608090330070f03060e010807050d0c090e0717011e 74
    0x95002520480c0b0348661143c221150003036100c2d0004010f91811450b200c1003a4060050640c110b41c4450f10005840d91403c0d681c000b00c0b071050750000c50391801c48010801501c03403001004d401c248544500300410384000020000c43c2c1d41c540003041036482d0204402e0307544056200180c2130b50321030328003441440203160042101007514420214030440c0c544d107030410358100f4102c01c10141d034088010066400c011604100e02014840c0400a843e011181080e050155009944c100840810900e840e44014004000280c042107500c607207030521490010180c22807913007c58010324806000007402402008202d0240c400b09001e5401e00039550540104010b910719000f80c00c2d03940d1000c080300d154030b2168140c0108620340d00c03014094181800903050b80d0491740038489291300540104005040411445d041c2e903422203803c111000301c1d08011441d907505400c90a081e0b031078a42c00d61003041e0002100c00440c0d81155100070022908007003542282c070b450108408449820020078a440101d500202 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 888303246 1250 888301996 888302029
    0x927010e0d0e18040305180301020705100506180a050411090f160516140c06040308030103060c030e0304080a0b07030c020604020d0309091401030615060f1220090f030c010e 76
    0x20070f00c8103000f030800d005a0700740c0303007580440d000140b1402078005000544400c00800c0d0000d61404005036125680c070302003844580c03103260390350300420415030711310106101030b40e028001d43c6d1140c200140203400402065030104c6041d0a075040b0f10100e401c0107112940b080364544802000d5035140303803000d440e05d404101ca00302040310800141da034a00c0740e4136030322041c0d50041410f40c01c10221202851318140c9007800c0280b244409101c1000010302600459040d258482d00100d600e4910740429405040509880c05083c000418085070030742d00004d139010401c2c09a6081549520b4003001581150440070483e80180c00c001e001401508000c0080d9402a02c00d1402110f82d035981d9620b001115840e91450213000100c2004005005660088501d403203d04070200e070300545070240192680c2c0446d01c2400030b0042c912542400d0561542c04000d07400c174000c01300f000c02c2101010307409141d0301c4045550700c18020450484070604000807600900c1030188c4441410082030000c0140b180740c84082003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 888304496 1250 888303246 888303259
    0x30503180c0907050a2d181205060a060509371b02100c0522030f0b0609090a020a090209241c05071209030e0927010e0d0e 54
    0x5403140c2e1510700e2a24400e0701681d5606484650f403003030041c860f101211601d240031401d9100075005000505c003840f801400740c20b01d4241c040706401110708500c0590f02c401d03103121001d00440c080c0000810010700c50300d40c4802c100401d90b20b400c104820440305880c220f58240e10700507487c038076913034144030034001d04000514008803004803288901503079904c80315072080c8a03400d883d40c110240c04110301110b1051108042c441c800045500902c3d074001d41b1080d50700101e101d01c0070460031085001e003201031900324400c0140100c550510001c80c810a0310080c0c01500910002440c079000415496840c1c0e40c0102641d51540c80c0081c050060340140d03c4180d4000a1031312616268400318600e030350a203020680094032216014803c0d088464080700c0548081d003032100300015654016503090806810600005050145003000c448010308000c0854101e13950009114040300900b000001101d54260310715800c2d48404030807030a94070034086400300e0b5803080f4200c0080c240120340e406101080640745 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 888305746 1250 888304496 888304513
    0x40807030204470607080a14190206011403010c020a0b18010f0e060c180d1a1503070602030f04030807060e0a0303050708151c0309050604031b05030a03050318 70
    0x220543c184031400d074401280c100440c1c05074020195020606800300c1140c1d0f540c180601602c81d00d9044c0702d14580c040c1040354143c1544107855400341540c808500d100f00d070301c1041c400402c2c040e6aa440a00603e40c09404041f00440140f40c14040e0b041c00021a0b80604120070460707a90100e160380203400c3d01c1040b28141401c103030740c4109200e03000c180302c2000d070f001c070700140071204940c00c049000d0705c002c140b0311003044040601e00606024a58007071080d41c641040002d503080c000c44075510700400c14400c0701c9003c01e11444400c1003c2108000380b085094440003660b46a00381d0b524894007100741010403044c001080410301070342c040d244450041c0f40118004110303115845c20b00c60f0500b4205d012a590750240050755a0143c00241d100340b81c3c4440d10510f0400000081441c1d0b0a4244242c04d05110480c0d0805c141c0305412030002007001070455512151285040500202214040c4080c9004680000307002c1c540000d001c9551030701601c40900e141c03100700900807901d0003e10324282034420500d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 888306996 1250 888305746 888305801
    0x90a0b0601052b050c16081608030a0b010e240c120f03071713061e05010f1703190c050a120507120903051c021603030903030206070203040807030204 66
    0x2c0f40812074111400300e120705110941030100720750001e020b11414410a106800315644000b10010f0701c0d03904904495200e500020009003000000e1200410000001c02440301100440c0c01c044440d013402d0720b42e83c403d102c412007404800240641c112a00700c0c0100d029640160301032000300300803075802341981c8680e05403081041850340124440030200c2030000420186c550703c01018031440c00c03220325a40b03d0b814110951420a90800780150004d943c61030a4040d41e0409091181d00b000b101409001e81d40c0e56050b0212060107a10500c1c4401f551100c0347d8070103c0010089503042a43e142c40c03681c541f000305004031103100172050101ea10348520968030000c10000b11820031000e010356100d5694643c00d141c420388000c2c90200c08001c2c0300304850700740000781020400c88130700c200c010301c1942005100c6008a240c0194617651514001c04580003109144d1301c005002c056034000c0d000c442d0b1545689008a0b6207110382d10031034140343c0004101303000501d8150022070080c4201021181c41d07502001c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 888308246 1250 888306996 888307027
    0x5040902131802133003020d02160806041106070b010816120c090b030705180f0f011d0a020d0f0c0e01050f030c03040203030403050d0905040b09090a0b060105 70
    0x300c075a0300000404080104101c0248440b9880400700703015410001003c005841a0501d406100c28079000b101019502c9481400c0c01000361011001c204642c812504000c0c2d10317440c0b00d010307040060003021005a900380b15001c1203821241c0a0005103104c0d5119113500040b20203012a9551080e41000701c0d02c082407803058818044d004c00e0001c1d00f280c004010748511111960303845a5820342c1102601c40c0401c0452085030103c1e603001001040c0e030303414000024109402030708040e41c41950700b00e4200314000c00c0388480d40314100c1ca00540ea4a0740340c0041c07212040000348100b02502415100c0d51314880c441514154018000c0701d400340c103101813042401e09581104244200403961200c060380103c0d0300090a007840003007800c00515182c400359a07001c19210050a1101f00400000424115207080040798000c40c0c02100307980324191004130051040341241b0a041c412170510703256441d80d1620303107070b40341c001d0001d4401441b84e0241c039a01c1150703160000b000a414010280000d0071511000e2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 888309352 1106 888308246 888308257
    0xd020c152b0c05071709030607030b01031d0307030f2c030709020703080108060c03071e111608010f05040816110a0b18040908160305040902 62
    0x2030740740010710145610411281c2d1a00d00c4448190794407030003078040103101e00d880b0400402c400c050007515005445045070b05412071008581e80d14000c0d408085a1441810085103008400f10300b45d2054200c84404021500001855802c160340061908070742002410324060350b400001d03186518110241c0350295a0310511101386407a50204201001480050070a541e100e0040c50002d0004000b845540d80c6031062102007291201500180c3c0d00c5116155541199444945084090150b001710084d0074000d03080901e01c0700d2402803164201c4509035010200384980340544003401c461006280021300c500e4030040c400020801ea040341e41a0341070b0410340b00d00383c0250500c01705610341006410791001610400054107200c813400391651000b1018840f0000000e0007c0c04107940612000900c0e40804101c0d04840151280c500b0202500a1030043c0c24951902d0302c1204aa001 = true := by decide +kernel

theorem cover : BRFrame.Cov 888129496 888309352 := by
  have h0 := BRFrame.cov_init 888129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 888129496 ≤ n) (h2 : n < 888309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
