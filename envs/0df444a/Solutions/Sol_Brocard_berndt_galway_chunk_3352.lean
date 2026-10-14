-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:24:56.28395+00:00
-- url     : https://prove2.me/submissions/40b731bf-35b2-4f3a-9e32-07499da316ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 602697841 ≤ n < 602877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 602699091 1250 602697841 602697853
    0x5241006030209060d0c03090b070c0510091b08061b091809010b06070f0501180b150d170a0206090712061503080318060604020a140304020a09050a060f0806010503 72
    0x40140203900810840038080c004e1490007a07484440801e0744c91024001e00083d0b0b41741104001d10201c2400d058200e01d1903d01000c1040c1243c40303455981026480d2030403600e82d80c0411500308410000c10064120b0f6a0030a0f1540560746c5010541b1644119480c80107542c940020204210303250007100c08840b00184503154540620004003401d8100810814180d076a903104603050742e55840191281512403004064034075264139086007500c2c800c20102e05445044c100440c001110725018907884800840c94140e4160000d0000c2c1c6a603078030300c0c40070740728150303240c1c081c0b011842d103100500c1d0140407138085803201c0d1035107080d45542c0c2001d40705005007403580d6412040000c0058010b42183d00807100001a82500d82c2c0383c401844e8410b40ba64160300700350030b1110b0010b010a0010550100e4104da0443c02e2013151040030f4101440302d4028001d0240000024045583c1c000205024040c048c0c0e0400003842c0c0030040710002c00860083e00e07500006e620001484000011300241607031030207409030032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 602700341 1250 602699091 602699099
    0x2c060402010503043207060e0603040b040212030424081f0b0d11191d0306070302070201020102120a0b0f04020705030406050304051903050a0e06090f01050a0c050109052410 76
    0x1c08481c5030103032403181640303001001d0982d0179054602c2c0c2038164898058002c1038905076003e40001c265000e1240135000600070400030504240d951a8008d40588080342c084201c500e070541188116003004500e86500c90820400c22440b100782c0e1500412a180c4100780e03104e11348510840c1d28030f140c4100c410382092109116458803280a054540007015000c02d41008210311b80955411580290046100103650701001c25031000c503101ca11401088880800b0350b000303022a46825009284400381a00000e1810459200f5070444a00703401c0802c41d000700e800d06051900c054100074403c0da10070f08602d6601021490244201d0314010390110043d440d15251903429a85604000c0007036030b25015151403d9505080300065641c40d52181e5101951041018800317010001050003803405118184012310700f039140d03c1a0b914070041300b402c2c03203900e41a148804890302119a140101554244140042005400141215521040748000203810390009550040b140c003200c50041c04041918200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 602701591 1250 602700341 602700353
    0x20f041802041808040905090105070f0504151209050604050708010c0921150608071d0f040602040b04030804090f0506030a080708070614070f05030702070b0c0109062c06040201050304 81
    0x1a0f111400744001460015484050203a002548961502901ca40030000d10b940d0a01c9501e0780302229051820342c681000b94010120302542c09400c00032620482c40d061694050103c40c0b00159a440e001d00600381180b51a0b070700c511013610119014810f180d408135011006018600504a2a60b20303103002624100318241940401004981d240d03844030600400724118048242c20741e08401d2000c2500d62805171141e250020a1340720021a8400302034038a003d0900d100200d400c4100c814040e08980c440d801d11000900c1150722405c56114001000000c00160380007801c2200c044040401c0078841d85841002524822240d0b107916070000d1464200084080020b0b00c0c3c0d07140180c0d240e5080c00c0c901e070349200499414400e45841420810200030b803007940040d00b0603024040d49003070381c15400c3c4107101958400303240c069402c0701c000204a44904000940c0b24029141c0c00c104188060140003400008540480401110101040300c0c0d40c00c86803000030b6810301542d8180e480b580745907030381c1d2504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 602702841 1250 602701591 602701601
    0x204050406090f0305130515030c0c070f0f05090c0408060621060106030902120f030306010509040b0406031a09030703090501050c1005070905032a01051b1603020f04180204 76
    0x4550303540d9103500c01c0c4085803c04280c2030580c0d100362a050350341c0d03041940c2c1c0700c240816544018810304500c001c480c00302038031505890308600000030341511550521211402c0442941001d0b140065a40c00099061490000c1c4401c40d001074811468503290ba401d981402c2c0f050380907180c4a0350242020034110701700944000b00d00000900700354030404042c0403131400e0100aa0040c1c0002e510340c401c90303055280200514030030000100c000c005070b6441e270010684a000040101d81403280100b107122003511a07411031400c048000740200f040d103442c0d00c4c010081c214042100300341c04104000142190b6400400c41d0607068040e1a001d40c00c51030400115501d902c03040c210712441c000c0103803c4540340c01c9405424041c2c416511401c00f55420481410b01d01048200300c4c4440c4003c112140c02041c5010b0361000c9128001c0c07906581d14042150b2020440c1c1c040040c0c844e83e44101591044000102c000fa101540d20844a40e407030000c54008020a80d407101e40c408900000303441d400700042c80d06030b000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 602704091 1250 602702841 602702843
    0xf12051b01022b030515010c0b070e060c06010620030304020d02040f090606051003020901090b0304052a100827010b0301020d09140f0a030302070809150702150a0c02040504 76
    0x480710002c080d54041c0c0300c43c50442070110100c5010b40a0400500c0e05801615030209002e52105901580700300004c2c07036810002c601510031100c0354042a4402e10405a580c1117003030141c18a5038400e003800b0804e5407010240b0a80c80000d4110030070307044020004803c040c05182490080d0b0440d100d5800300300007010b8015040340c0c0280c1e03911444007182405c1c00f45c0c0190501030b0380c00240240c0f80009100303108031072803920b004140c070400401c03115a0704002403805954580303a851b07840740e41c0c40c548945060035410000000d42d5a910041c00312007041e40e150b00410703000b40c40c0400b0380e04500c141601c034a5003d6aa01d1803960754070081c0c02002c0030b00d50715041c0f00c100c2400042840040e00b00404d007240c0c00058042c4440d034880035020140300031956041d8072014101c0c0108400b40408104507103403040c6207c01000c240e00004c0c0c08042c84801416999040310042c00d460b00909000103e40d400d45c403c00e0104d0003104010381e9860000302c0d520a40b4003400c0151240c443d50506c6500308001800300401c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 602705341 1250 602704091 602704093
    0x6030c0216080a060b06040506040303050c0f0a140709090803070507021914011403010e01030b0a0b03070b091008070816020f011121010302030a1220070f12051b0102 73
    0x4454100901c5400c0c0d007000b0200c0101601d020702050034410261841ea5100d40c5c01003404000410a54507444115400c49805243c1151500d529402580c103050030020b01005034403803810010306100324410a401c010942c04c040b2000d8036038a440401c00e803840c07528017501c20034003440002c911074000c2d0001c00c81244001e05c9640114051b000c80a030b001400e8101c00c0d1030008041d00030020303580001011080703070745000629080d5072500c6041c601028050000500114100b004100240995000706868403c000d081e41c514907103a000070300158001011182c0f08050031504610801e010f00190350289109541d45205070f034491100e00c001c450010600d000714494442154610301080c0b0800c51718412110400d035075842c0030341c540301c403032520a80c2c000d0319035220000400069400080d01c940035a400740804100d54001141a900c5980c035988880315040b1941041107040c0d0080740340c10a4955054000c41d9041d140e83c0751030303085010360302e009009502c00206100c1c070919032041408400f41c144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 602706591 1250 602705341 602705353
    0x10905010f020f06090106060207050a290f0c0c04140402011707023915071e0212010905100e070920040801091716020f010201020c0a0305070b0609040c06030c02 71
    0x89915844c0080071129014544d558440502c110303941401020002c180031141c81e401681013101c06103000740c0010f440c008104c05010085d90880ba85800d449040119181480c2c0319004000f060340c5030760850030410322680c6411040e454214010201d40d02494041e50b819014140a00420a02da00040c0075001984a02030581b000040c0e0303014403002440308110041e03c155641a004040840c12101e124403c28440d103211001d42120f10950b041950440e0b403a482c0d040760002409000d41603003501a4100460020038081c000c015003210030000d220b24101c48050600002120440394040c0803c1d0003900500390401c034445503500121390548040e42e000110341d20201c403a80480c0e020307500c0b08203607035114040c0605001c00b000070703046201564000b292a14400d03110b68401c000c038200c0c000f445902418800c0c4c81603403003541507503000b429201c1151740b0000c090401524682202d01c2c1200c02040c2c010001e0242d083c501801030203240d1024a840e0740c43e0400394107034041d220384484081144101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 602707841 1250 602706591 602706613
    0x3030a0f29041512020a06030203161b0b0a0c3b0a210c09110304060f0b060a0c021e210f1603031b051c020c06030c030709060806010905010f02 63
    0xc3c12180c004165a10b000e105401140c418001c50507416800581454070600c2000040c0700044082000384c1902d00d080c0039102d20185c0820b40b0710412110282407901c5072010008403a000da40503507481c49191300c8448030000300010104040e0315007220390103400340d00404e5001000001c8014044440000c2484202c6501d884203803840e04003031281c084900c003c070f54035042804218600400949011081400103012241507242c051001a2005116070b5072403a0010030f4042c4c0390300003040312900500c095620105144020003060b445e0b42c050b440b070701d40201803036101400c0e000f5402c400301003e0303c1d05e00c0c90740c100c140029401c00281c1040c603150041e90000e81c2e80c6181404690b004011182402c0740450550a004100c0708410b00d40071030701c42c0050020343c040b440000e080062600d007122680c074008094001241030000800200740c000c880482030000445000000e13511910341c50f510710a80c240d42c0d220032990030206840c00ca020a009003414810f5502c50140e2002c0c1b00c04500448013000c1036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 602709091 1250 602707841 602707871
    0x11d0d0e120a0305090112060608070f030207050d02160506070b0c091302040605030f09010510031211010911040e03030f13080702030303240d02011e110a030203030a0f2904 76
    0x9038501200004c0f80022080d20940e08078606189450014400308149130070104080c010307000103090302701031140c2d00d425078030316500c2601219000c03940481500d05e00a00c046010b07643e24502c20340781c1d0541000110103d12424030301e0a0f00d944641100748000f26440c0e940c070004541d84030000e103e400004076248100000810300051000b8141e50399040e81d00e1a01d540c0350559403901400020969040009208903076000b441260b09480d0081c901240d110310760713241a100c600018107071429550800754844240111702e8045007402d54103542c203106201d5010181c035180d10003103d600c81d07022144c5001c0340c0c0580f00304024406562050485030728004064001a00d5900111140310759040403007200c54821200c0a40e11180307145c00e5031010310b03442d000d60010305034407a4280401400c900000034001d02c58403176010081800c51003410780e400f032030070b6040023902d030760080f80c0500080d410201c0c4003024105c43e2003813080c100103180781440302c8002c03c030800043c420b070712260650054a891040d440800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 602710341 1250 602709091 602709103
    0x30c0901030b190f140612060303040f03110909060702070b0d0b0603040b06030f011b18270b03030a0c0b1e0a020406110318011809060b0309011d0d0e12 67
    0x1449003d14500342c40e0241c0c0e0210204160410109070070b200030421104d031550b006440380c5080100741c280d410340e204408240b0f1401258020203040804880000a2054880007900c0c20002903419510507543e40c2c0c03030a2750724030007520b11500590001d081001078506410140484104101c40410035280301e030b001039a107810603502518000d810100f489554602084202d030151070f1140280207048011800303102014a00348a03409100300118070548440e0305031211000791100c0f08181e0721000403a0f05200654660001c100d920a2400c00d8098032443c000094410802c815540c00e0302e0728005d80d459980142d03003e081c054156113000f219407003145070300c4181032140c4d08a100040e01e480c94030100070030151a402d03000344940c10801600c440e2540c00750b11110105006e080542800e114040c440004400e0b55100800c0545411008aa114004d80003903004080480080c0401c0400001d061100b8521100702c0c134490b8040b10a085106002d5030006100b0000141000c8030640e100d001141400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 602711591 1250 602710341 602710369
    0x127081204061b14031206031009020609190f080105160206060d1202010212091606180314030408060901090b07020c030604060c0e042a1e1b02030a0f0201090911030c0901030b 77
    0x140000c10409088c1000306000b080da6400c010702144886801185042c8104601d0500803010a008980000040f0070704400501070240413150703d66443c1d000e24000c20080d1501c490000d0f090111003140e610001d0b10f24000c19009089110911581e079072603040808849004003555001e2000c0c41040c50b403000078502c03600041000e88840341411501402c00c403440e81018080c020313500c403811001503c07040040c1c1a2548821207040108240c0040c82c0385002d503521015081c89184100082c0b0035064220115552140f01390007540c0e182c8407030980c3c40d8900045000d805a1009000502141580d000385900031094240528581c3d514004981581c01140068602460030144c0032a071643d512003200301c2401c6c0c0d147c109210880f2180365a22a25214a180304002030421b0f406111000a1070a1034807aa00a0840780040803524210712149442c00090707000c03400b1020001581c00013806019000802c61044610316a07400d83c030084550040d8070300c24105079488805401644503600c4041c040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 602712841 1250 602711591 602711617
    0x6061203080709080304121704030f060e0c0a030b07030f0b030d0c050d030c05041403120415020730050c04092d030806040b0127081204061b1403 64
    0x10314100c02d000c1c103506030582c40082d46500c108401c0040403907440c4609405540300f03c0000c0b0b001801400b068150045400181c0345100340c0000348200010340c1e00113242040f05909488645201e0300410894803064400648191902000a010360b031090b40200f008440346000000c02d0005d6102103890480207039181004510346461007401c0c4030b803c00c080580b00c41d131840c050004110341c1c00001d110703000314030031201002041070300c4800560b414045041030040b07020900303440720380d5030402189125a902801000d80242c280204451144400d1002e0500c0c6a50703c21382c03c1c0c003085a546010f189484415103007801140c1c0f0304041a526409442007043c01200d0020141e41544100c280305001f400205456a00c0000c54000080d00310241c01c0d841041202c000030000c0d800700058805444191504122010342c40f1610341c004150304020054401c0c040445200140300c5072000220710407401964041804508002c01003000003102c0c40c8098441c114100c0f498904041003440d40c2c0000e5116501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 602714091 1250 602712841 602712857
    0xf0c080c070e0910051b071b0506030415050703110405061b0a03030e0f06011a090409021305091b0f040905390102031c0c0c0b0c0a03050f0c03070302030406061203 72
    0x44c2c050184030380080e0082c0c17000e800c080000c0c220906521a4100c010b200c03a04440710fa4607411800035440000300313005007403542d50345003a1500100c90f850244a4a20b80ca1801010a5000d48280320745c40c0510745c802c5c1d07814a040d09000801c5a21b402c41d01d50640c00340c8440001c0052100c2c180842020030748240c80204001409088450401031384c40d05404680d4024401044200c031554051100404a6102c141d03440c069800498090071745114044d4108151549001510304194802e0b407084078a40c2c1a65845040310003000e080f01d01d12903031a54042c0c90f8140a412a2411740e1008080920800c1103500540040703002625542001c46075120f4107011070304440500c1445c40311142d081d1b000348051450302480449800000034403d03c0704038405d03a40c10300f201030140505208811701c0c6e0040041c4015191407100202e15500503c0c0308000a81010049205148100000e5001e00f800c200003034203654881d52304a00a400c024406d031103e0b919034a0006101ea48c0048041899000340d6902c49 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 602715341 1250 602714091 602714113
    0x10020904061a0f21070c0b070201020f0f090301021606060e0105010e091302010513180c0c03090e070c080309100b010e15090315010b0703020c010f0c080c070e09 71
    0x108032800750340b04415501e00d03240810500034000044a038500d03080b41d00341d91600381c540f20904a06036600310360700000da1070005200e180d0750040c081c602490b04ca401d40c280c89070388080f0200c1c280d008005205510304401e100300c40d540c42141c8c0140c0f04d0900054001800d06212410742072014401403025107050744d032441e0520940c00a0001140984420b09140c62850429408650764000c0182500307490030b41c1d1900e49045a00c280111851680118080143c207078540c40f10f20304880711014428a05803a065060143c10300685000e59402c0d0103407640d52105140010303080940318010b04440801099000110004500d500594020400d550007040700d560309010b4401102e0380400030505000e9020383c290789594400f56400c01c142c805294454582c2410000b00c0e14100100c0000280c2c104180c1c004100695144084c0c00000c0c02503088a81801d0600e0040d500510b5203c00d203400034107260202e4020903000710080140030103107012289800d580340b00300031521105030380012081e00606c00d00300c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 602716591 1250 602715341 602715349
    0x70606060e031e0a021e10260105090609040c090c090e13020303040618030807030e090a050606031501030b0d030305040203100c080109230a0b2803020108092a040c11060a110903100209 81
    0x4950020000c2002c0c88e9411f103c001031459200408041c414044840000c08001035100d4a100030b000c8600d00380210400c42c0c00203012111640070782c000c5046001c000603000c09990080e800400c0d0050007840c03400741040021500d06041c65907603041380c0c500100010001d190304004044a60181d51240e202c6c2d0b0084081000d808030183c0340440850420060040507a2203004a031380101701e6040009045108500580242c0003400e4141d40c415100c0140310189900b58100034403c0340308070701f500c1c0c810683e0000101100e082d0100e40c1c0c00201c1e99001070003140c03d00c0c4e002c0c52801c16511003c050064850560400e0b14504031000400203072583d070712440034100400f6001c0130f0141c1103040840d80308041c0201e00002c84520001c3d041028031400700c0d1140c0d0b000c0c4003880c44807001066549030301015500e00101c00803140a1b4500a03460001819032452141306002c4070422203002500d050303240d840421010303002d0461180085101007107880c1260b41c04004401075503074a03e0000d83c0f9142030b11700300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 602717841 1250 602716591 602716637
    0x2d0702032836080106060e060a0f1b05031306030606140d020f092d1c32010b0301150605070303090503070606060e031e0a021e10 57
    0x1111290140c0010412200d030000c00c4812007500542c0320103021100000d101024094800703000d0070303000342c8100c0460361002c10b422102c19114280c1340c00c9007100760402842090b105020840f0300041140010384101441039001601401802c178a100100d4059203c0324110707802400e540d07060851600040000e5034050107888014102070a000e00c0c408224220140e00b4807034000454080e550014400307426040c1031050703c0000e00c4c080c10000303c24442c00c2c0039078004035001040020030f583c1d480c448612498402400321282d1082c4180b0420ba2006541e9407680c85140c000031100a0041035190a58040c900346885032500c0705130021072844250014503017125509841320a103402520024001c3c1d80e00303c1d080f00e0082c1e90500d40040e5070f29460420500f54010b00c0c0d0003c01c1a0705225000a04640c040f04002c400201107085e602010070400f503191096001d400ba102e030a810480702c680243c60400099a04d921036522016940460710700010810030903d48454041580b0070348860442c0030404907 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 602719091 1250 602717841 602717887
    0xf32040c0215180714040621050106050603012411063c070c0503040b03010b0405010e121c090812040f15123b010e01090b2d070203 58
    0x2c00c0c0f200440c41d10104e44658490090f10b03901200301310032024a481d180d002078001e202c1150812000c101004442440d80b03070400041d00c96608042c2d01207103914040003124105c903180d0095040102107920240003908944040200b48403807007181c0300c40d64104cc003900340309031500c0f00800c0380103440529442a107056690060410407400420124080000c0200b41c0c10100c94140003181c000309150247c9507106a030050800030307102200000340c403610718010303000b594000d0301c0b03810a5082c1c4506204481500c2904400c040c2e100c002d001f120740410901131010818146041070741030391129400c51502c415100390707005c010000a0708000040ca51a00030b00500041c5d4040c2d0102c0c1d5010310b004000d1082102007840a42c1c0c3d522032207030790340ca00900c12542c241d428142c032000c0810a40c035045007540b059a2031b071525400d01d1450000142d06103c1e90010a0b485036640039252a02d10710811021101d4040904c2c0c922000724003140c52101c50166803040c0c24550045581b448110b00141b211200000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602720341 1250 602719091 602719111
    0xf0d061806050a0f0e030a080c04080708070e0610021b042d0506120d08061807080601110d02071a040b07060203040203100e0d12150602160f32040c0215 67
    0x40100d805d80040103c0743c00141e2854222510b44480303030807142611456000440d20300c40c0140000c0d843c100030909104581428440c6980d540d26039040c0004540c2465007000140c11140586a13a01e1280d03080f10082100a000000d64864002c0f400407100681d468ad00c2400c6e544801003020b4203103502070240c1c020400e4031611501c3c440c0c031280035a20b8540d01000d5080c4103600740001c10365180e55006100408088400d038110b400c020f9005822070000399007550005001d50385d000328040303000030f6074030707681c54140c0c020310a66107083e0b481c540907007060080c2c186c40300301004002885980e1b800036080c2603000c0c1d800143d90b13042c240f041510308005100c01c428002c1c00d012554112100108203d015400c060805d42c0d100482c07115440b0051403d0360021460020004010500590008070310fa80d005951007000942903c0d08111038495215101da40c1204109488220300018044400540081822050000342d40c0e000000740aa80401b0444001640500600c0300c41040815000c0d0300924100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602721591 1250 602720341 602720351
    0x140c0a0b07030c051002072006030c0f030c280e041503020904031211070203060c0309030403030f1b08030a0b09060102060c09031c0512150f0d061806050a0f 69
    0xa20809030314041c10401a06100c40703d010601400018840e0a1008003059170440d039416103407400c00312188a814444134480300c0c01c181d0302214200b0204407409900c2480b492420107900e4803200c00c0742da0000b007480c00c0c80c42d8144440a0140e1041040d01c0046460b84508149942507010051280391081d164510480c10612000050700d0b14050070000d880d0123980c2c0ca62070356140c0c02c2c00c1d1641c0c10b1009000314850303c0c0282e0740c81404000c40282c401603101718180d070042c0d21085640c40240c041961012003070f410400041000034003c03200c920003284181000a01245802d12114039a500c8030810707262200000204008039080d40304a05881c802161041e05a0074103100003583c80500511410f8041400030f210385465a00300090150014010107000c05112017440091103600f2100c62807a100304206d0118410a03a1b413154100440800b62010f6100281da0003042207540a03c1429a901c954840205604512001c10421950700404d0702060710f003800b0800404031000610100605481c4c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602722841 1250 602721591 602721599
    0x16080a0b0a061d0907031a0103020c07050613080303090709060816090203150618010e09090c0904080906070c140a060c02060c010b0358020c0d140c0a 66
    0x40441074040e1062481c00c0082900103003000c40355040c4950b10294031900c0d0380f041000140d40343e007110b000c0a8203000c1003840c0c401c07040e0054050380210b0240b42c1240d000b030383c1d041c000c0b42032070800b03810300e4038070220701001c403640d42d034800e0741140e1003650b5559146c1c00206084c0003100b1a1300441c0e00900d028401400d081481485501c080b038081e0081e00b4039203400001140403121503c408002400c801000a40d0700c070ba00c8083c00b00c4001ca5400c449012070b20b0040c01c0c80c40c601d840950984604000720141112811004c10002d003c0c40041045600c04000d000c0c100c0183c4542016090360303482030b100d0f00034441c1400c2490510454059405100d840004418001241c4c0701b40c0389070040754141d42154440080710b6181c4d001d07050601d07406030140b042005010840d5091451101c0669010914410310f1100b55a19407040a0003041c202c0e00306a00c01c500f44072141c4034252020450307200d03c180c2e01c1620b00103001034014404140300b50354440c0b0089040d0701d46c001c2031141d001580d4040391b004005030301e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602724091 1250 602722841 602722849
    0x30803130206040503010c080406050105270c070606260304080a062f07060509030f0a0e032d07050306070c140c06030a0212130507120f0501020316080a0b 68
    0x8250350581042040004115252042a603020b08002402880013100881004050080489040da440c5040100003d0541480c032010f4443c141d440c01101a03c2c0c8190410f0b201320040070f0190b0410010411401012551038460705c005059403101d030304017248620b5800b0710610b00c40c0008160300e170410041000075440c0054100100380e482280801d5520f02d80c080c106400280c01491411740103a40c2120100040e01d2009004840c4103400400040c0c8801031b809950780100c0d4005881006e08200c540d003102e004000300ea50342d0308000c0c11180f42e0552940010b01030310f20041010141e24801420300c500000512200780a4103045e80140340500c0c04020060004400401c00303466240d00408040c2c071004180002c404005000d000c60b03a582c14080c1c0c144000b136200f1081c0455030940b1101103000d069a106043d110140c001004050741401d08105e40886204440111000c81002040600003030080c0042c1d841034000042d45501100b01d0b220103005810001c250340304140ca00480781c4801c3c0c7c1e0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602725341 1250 602724091 602724097
    0x11070902040305010c0e1c030908010c09030302151501030509011b2c21070e040c0312021f0513230d0807020d030510180905190f170f070b1b03010308 66
    0x7e0741002c0102d42c900701d4201940e1966890308203500359401d00250000c0c2c1c9412062450480b0303c031fa4200c480c0040c084a59030300d45001134805600b0f00c41070480e100e003158404c0d04519017009605c1c000041ca10042d01001e0000d0184280300030100b109042407010400e00030032407900c0802001007a2000014803400688005040a42c0d2410140804003808414108100a4010340201c1205003458240760402441c0c440203440101d030815801c0c2a894155840494418486184c028000221650820100c4040d0400810107105070038004161800702c0c0c003803080480510030503d07100ea0003009003540c0c0ca0402498001850600410b3360078000e00701d031300103101e2800300054540014151181340c001d480b20940ca600a05010310850442d014080300d42e8840c140300303842041121680114cc4003000420344072100b0103010981d00ca040000840d81d9001c554540c2c5546d0b01540c0d103400494a40722409400c00c21007502c07241300c040100640641e104883e40980b1540b821140d0856145546100e110b03c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602726591 1250 602725341 602725369
    0x4110414120309030f0c210a02130e01061409010608070203190905060408010519050912070804210c0834030804090b04050a090c05060a11070902040305010c0e 70
    0x9503480040c041c0101841510440040101a42d4000c0301009005a4440c042003045108000100b030b41e41d603c03003c04503110304c920200c4001c1c0402a0035a020024144110302200c2e60141d121022081350240a101e00340160005a80e080d81d82408071043c0084060705800803014070427044c091018098002054900100400c07802d45c0010301407490071224100f00703034411038004001107008115140306400c0039210700201004030005100503140e0106840302980d01d0001c43e08840b104244030b20080300100340c11b44c001c211a9213402c0c0e03500044807000400410304009a01414050383c10403a014070200c008110040041a20500004102c8149003021560010100c40c121403107003680c07894083c01005582141e07026468aa03504501d201800c2c214040a00c00d1349880006001084280301d020b00c40c03038010402c80c110300d0a04051080603408916040207004c01240e103100c07100802c101c0c80d8040c00c288000903844928502d002d0b400d40301c1100c05081880070844241075a0f813101c00010b8182 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602727841 1250 602726591 602726599
    0x90f011a010c0b0a110a0e01080f0c0412030318060b0a0b0a0e06070f060504060209040e07120b0903040906030606030b01090e1b060c0604060c0f09080c0907050d020706050604110414 80
    0x10340c1311440b40000514410461440740d2034017080c00e443d1141c00a044824255080c1c8442560303903074201c0703581ea003c28201c0d0f401d225070030b00b80012301a4146910451810b030388a8100010444600c5400a045030b5080c40e0440c0c00710340340c6505251a0415919202c010942103d200381040301c05503018150340944103240340a42c0d03002c503154060002480200004541001042045003020705100c40a5030000ba00540902d0a05096402060000408600301d80300440b18400c2d8896940c0c1c0d003081400050002840ca1105010114501e403003442064001c0d40304000004440b0725510b41204113010580c0f004032100c4c50408484400d45003c52031442481c03c00900051a00020b0000342080c01014100c01c481d12540003080100803079644401c1c60100151990f44002c00588001c45440c07103d030140506903002003890a000741481d0306403982000060402c02d040100c00c20080307049800a010507101030f900c5106008240c1094810035058002d080c00b81450f00341014112061203051152440c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602729091 1250 602727841 602727863
    0x20a0b0a0801140112020a0c061811120f0d020a060f0209030a11061e1b031c0b0d080a031a01020c03030a140d050c1e0403020d12090b03090f011a010c 66
    0x3d1603124440c00c04c84c0010f861411034440203103407401004201d100204540f6a8980076180f45210300130051032101c640d01c140035075079004000d001d01001000ba44030b2449207105094010b401c202c0c00348080c01c1004190f6000384104840d42c00e1040035624101d58001c02c2501c10000017105480102e00384a1450b0400b84908230301c1603440c00300305948a25501c100780a00044c00b010b40c00345005008012404407a4500c00848038600c40440d102e214242120b51800502e500060700f03423465422804440c100141589046580e54490071400e0f07003c00103900000e43e0f0b0b001140342d001c40f0050300502008082c80140b0304101000046030343c034465410b0381d82c240000d20b0100c800d505d6a1030100c0d0f440600f0030314240014140542c02c00e0403a0007406c403442150f0301c00d666403090140f0300c00568048907001046112090080d0310384061041c201d814420401240643c04501c0220200003140541000742c01000d4011102c0601400c4a0041490001030050041c82610a1fa4400c070142c1026030050741e0102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602730341 1250 602729091 602729129
    0xc060e090414120c161a1903020415090602010510151209060906022511060d090b0f0603190c1e1203080a0e030a020a03030f09050118020a0b0a0801 65
    0x8600761107600c200f034401c0000119900d0441002c00d41000301016410140a9291141c0001014a8400500640341282809a240d10801740b4010400202c0d107401d0042c0341c00d82b030340440c11800c031240c0040008030f4840030042204a03824031440394003c1180452504040c208610785c07100400c0000420100480d9480043e0110360a40c465030f03040e4be212a0800200d40c40d4a401c2c00031790490200f5040d49286050607042040300056141c1555501000c04c2c0101e4191004005407904804015030060b9541c030701010016000f6005940918003d082118032072409d00101450115440c074080b000f000008240800100b00100e02c006490b420f1040058080c40170400e110488126030040307131801140000041850f82200595004d0180403a00703001c8004030102070380c1daa2090301d4001006034050f040e108042482984a4402402600000b01d410300072034035000c0c01c0d54401c0d0386482c0d542501e042e8410849c81d080c000d01e002841004026810041400c00241c5000390510800154901c1c0b184510f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602731591 1250 602730341 602730343
    0xf06020a02150a0f0c02030705100f1404140606040902010e0d020f0a0308030702101406150d0606020106080c091608091612030906021b04180507080a0c060e090414 72
    0x460b9400100c02080034540100103502600c001818045000c1c980484480480d01c0401201d02c070a070030900070807404d01d8400d0440018102d00300030304541642c034002e6020000030440510700a41c020650f0302217850000304882d040c00b030060001d52050745000043c5c80140d800c0003001e950850110384217040304149001007110a2058800c40307034498120b0501104122103207020b075010342c00b9035081702c0c0303049103518010084900441200c040003d0000008089291200642c072a28480d61030f00380c281550350844506841464000380c016035124141404030900411410100210494640e111401d00010002024000f05c00307680800c071100300020a00c1e60104800491003001d00e8440b025940d807003655005101500c40100c000503481800029203510009048102510054140c80c00d13002000401008180907005812a41c1c48402c078200880c20600c250001000010003804020005103442c814881c0c040d00017000340400c4410300c03001070716280c03096980294804c0e8107588802c4c14490036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602732841 1250 602731591 602731603
    0x10e09040204020c060c0406232703070f080c1f0c0816120e0d050601120203070302150703090801060f0603111219290d2105070b0a05040f06020a02 65
    0x10074500c00d1170103001381050b90000420490301c007542d5109800c408400b080541b070042403210603400c5402c3c415040102110845003a039000c003000d074000c821a82c3c40101c2e0a00310264004805c401d4098410056404213000846031500c0440d10401a03078520f054000c812101c02001c0e03402c001d00700032118208100d0104484901000346800c02580245180c101c0c05075070782219060001d02135920000301c900b000341e441c0d10362650000161602c1d80c2024040300d040c1122010aa031700d84070781000040903891b0340034088021081c445030720390f07120914240905492100d83c862445c0360704d085004c0003c4c004590001e01a41e6848ca40401c017403580b0505182140039140403035180740c00c88818024038920400201c15804840d86081c00220000d01e804000c0550080526031114801704850265240c07104003080038500c115401c2040d1024104080d00d800d100b45072000c049540080c50350140214030808030b9000707103001c10610541c076203513480780c110301055100200340c1c03a004241801450f00034465 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602734091 1250 602732841 602732857
    0x3021807050f1305010f020a12081f08010509190510020a09051008011502030c0a0f050a05101a10020a110a050d05010b0a061445040507030b010e0904020402 69
    0x101988403044103c0140070589188280d6010483d8100310070703112400443c3c102c501e80d4000b606500c407402c604809079064000207150300b0601484005d122000005000d141e0060030104000050303626040b0710103854080840d54004070301c180505084000365001416014206040402603101c041d407500035510700c0d000f42c0003961300259007007400701c006a121104904035a004a00c142c40d0070020390042e40c8900c2a02000d84541e0000f0f00d060340810108002950b20500c581c3c201c602c8000191241401c19405401002d5515201c4055070910f401c180301000400c0700c126100030031104600e001950307498000034000c0103490b0001214007a50f5030045002c00400c005002d0203803442d5985040c1e4001c1c00841409845120500d0380410084e00c6407030301048540107034059038505159260056410a42e043c84050000000200d0800c5118102c9000007000444100700640c01c11041c03c000c103403500240380307004040c980307921403c00daa403082420123420801d0324010300c95151400410041d101d5400b03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602735341 1250 602734091 602734117
    0xf120106361a1503190513030e130603051c08010f091812020106050a080a240902180601030e160b07030216060e030d02030c0303041e0b070807020c0a0302180705 71
    0x56000343c103180303590040d84a0403003c0c20300c0d50081d03400d60304178003250402d8456501d01c010320503102000074020341181a075920024010030204010150100c1650034a42040310550040758118a03010b034401500b54a11045085c4900c866040c90303110541d80500d4850340c4c2015480f0511b01c0642c80509003106800c17070300410400404030019102030b0103010b031071158a02642003440300041c7c1d10000704a068540d0b074024049500075954000403048a4244c400c0d010880b0707910481180182d50713170005500710f9a50201c0f20709143c98480005800c0310b540c1c10307042086030880b50382101c40200201c01e280584d09034181d0f142e114031003410200d18216610601444040340c041c0003142540d04000f01880e41381044044481d00300c00894100d841f402a1026000c3c1030b8002c2c0041000038a180c3c0350041030341c02d01c884201000c3e1907600c98540602d4241c4140300071a04010a111034164140044110b421080c1e60740700c006d502e5640031a1114043c80c500031409440d100200d002c80b4070074003c46000c80c42c452 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602736591 1250 602735341 602735359
    0x305090d030509030d020c1807050f12010314010504030c080c100e01020301081c1b020f1c0605070e1f0311070602040e010e060913020f120106361a 65
    0x7140141c0194003003101e0a101e40320701d0f200d004103d4400540c1d40090b0002501003040408110000080e101c80502086c050003002d018240454400402401344118540c60806007075140d803c102d0641c11101340c0070b64035030741044104008250403410280015500c206540c0e600d002c2c0c641c03568205101e2503204491a81000c040c007908480540156060701e8006080d190b0402448800415071013042a5000119034008024065907030305075130002c0a00c2c0041c1c1010302244040c0002014200e031035a81c2440541001350803014020395101e400d910500d04d081440301800c0e0080060b0306508031803c0f5035001c4403103062003405e4034400e4001542c625002d020494540c92986001d0029401c0740c003400640c1006807000084020844140500076500a01a00b03495152030780c1000900c400d90b202070380c00801040b40000d03a6183c0140101541e541400005022414103003c1000400000c0300c0207010452115070310042da100d1700e40b080d02034010040000300a80510107013040d40c02c0310050b0380e601090003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602737841 1250 602736591 602736593
    0xd24020d0914190c15030f18030809160506031008070b030f250c03020f0601090e0f340803030703051f060e0d030504030c121e02011b0305090d 63
    0xc42207406120000030252843c5103007030381c00c103180303000f100c000030340762074003404040120561000041070042c1c5603240c0807500f068001b0307802c015281020a9401001d80b0210382c04149580070319080e0300a40424050407203121500305140d20310510b400307410b110b80400404609600702003c0402d00174180c2c18140c030941a5030317804010f5140c06c200d0b00c02c18200032a9001422980c10000000141c100130808a9081c5840c44000c55034886840c2c41142940f18412480c2414842008428002e1820301c001103241c07881c601c411410a0900d103880e6110fa0f01c0302007801c1c21728203202c1ca008002441c0301341d180c040503c1038003100240a502e50104000b400000284180d031030740368110501c256244074204035031a0003900c0c21051802640b0980c030011345001c104514901c2e0851511170802c3c000d1619130b052031340301d0320b0300c0707254103050b5109400c00058204030b03e08225a204141c0041562910024006491500003030504405154900e0060a40800c42803c0600900c16140f1042d0041d1181c0d000e8805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602739091 1250 602737841 602737853
    0xf0302161a160509151b060c04080f160920030108030a0f0c0c030204020d140a060905130c090506210a0b01080a08120c1e07030e0d24020d09 62
    0x740ca15142c2d841d0310011907902240202c0071104140005060700290111039448401260060580e1801c4100203005222902200300300e01800760b0914600c03503942c1d034a0304010300e00d840c0c4496842d00b001c2d080900d0b40c60458050300750900c102c0e4a44a0702203400708000e00103003041034052001c11020750000c4004144039000001500e40c28035103450705810b0b543c0300e850668140c41000b000400c8203480d60414001824250003900b0b00210b980c00105030600c0e10042c034002114101c0304850b0456403050b0030040d03518203000b170a0f00072004681c0490551034070380b070b8402500d240f0300411b20401c0d1281e0104240e40c80b01040700c6c0300a89401c07100c0a04a045101407605c60036000e405030f80c0840c500d8000f280004010503051825540030300300038030b0401a03040481e006503000b4045c24a10030240041b00490107158007200000c42004200ea035210380758038000c0c20a046e1000798a02034020080c100000500b1000070602c082102030141c1b040e107041c51030207030291150349031201015042c2104503081291b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602740341 1250 602739091 602739143
    0x503031317030115110708010e060907090b010813030e040204120606050105030622140106020610080a0210180302120c0f031b091509010311030d030c0f030216 70
    0x8452a00c18250410303100840c0c981e4003003070290720140011510f2008509018020800c0c009000c902507031842a0b980d46103901316003c100744841141c0040d01001a0900c080c0080c0c0e003c4d10b24038004004070a25280002d000400060500c913901110001d60000e045c05640c49042541c07000704290758494650840c0341000e1039442c0b088918504044001c2060b40c00f0300180c910070300c030240800919446816014a00d05081c149440107540d44003000701455003055451806011150024906800c0c01d0340342c1e601c1c030b401030750040d100d40d00801b1340c58005a840e0503510001d4038071032038001c0102d01c0101c1c1d1040380f0403041c0d0001754498004207885258080200311030804903021200d10102030018001d241d20398a0602c4885001c0c04140d000c15032038a0910025070300018051062040c0c02122004a4030125007130b0410741d1508201016445c0328a0f0030800c1d04004106480d05002380a469a005000041c10301c41e1071050503004660015804201202c1505481d017182000000b0550703405801c513071341 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602741591 1250 602740341 602740343
    0xc1c05011503150903050313060609180506070f050901030e100504060606270302061b01050c0304060617060a020f0c1e160b071113020a0315060c1a1305030313 70
    0x10224000c0040c0302c00e40f80c412041580d03050b40703c1a1950b545d840074164016026135003120180c0d030b940c0d4007203070f00c0d81144201d0150103911103494401c0c00301070800e03614002e801410441000700920a0720b81d155440300030f55581080a08011601c1c087e01d142403820003015560342103c00f40b030710007004140526608100115825500d4000c117142441784070f242480208584108034820301c801c00c1005007040b200400e03102454000b500c2e600c20001c4525821f440007601c00c44030100c2c2c08403e03c401c2c007401d441203030004d001150198a2000440b80c40c5d9485000c0200310500207540424000340c80032641d4212810103400005507103070401203082581300d00b1541080d48526106540d002603000c2e00022590040c1c07a00380c0c08080c10700843c3d643e03021001c00e601e984150010409424445059100d0002d0a840031080d01c002c68202140445000100c0c9940e20510030418070700f1084002c6503503181007410721102c040c48120966242c051341403a6503180000144148400002c0016803105181b007880e4035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602742841 1250 602741591 602741603
    0x70b090706080a06060219030513030b0f0606090d020d03030e070b030f0a0b330c0c01030b030606010c0605091c0801090501050d0308011211120304051801080c1c05011503 75
    0x2e5155502c502007214604d00607a000b503030009480c50780c0b4549800c1ea42e0040c41c46880c1441c0b808800e50740c0450385d400a42d1044070079040841c18000c071301c03040c0749800340d008070291186800c22100000081030807400810180c003070307000c4041010a03d4400e070440c20880500070201c1d503c982e41c4907201c0e07533a030b40201c501441456601000c1009241c550044100c1460018200298013681c5004005c2c04510300071035106a10045400a1a021012002c1c010040440000d4441d6060150014098034040c1da41c480c030130341041d810400700c0d0b81c01001141d0450f401020006150b9a4a00130034034001c0b04131450828103c2115614990b81d038082c0036241070780c501030410b00c410390f43c0c1c106018803d19900700050100380c0400c010320503c20712100701e06a450044034402c09030083e0030041680051132042450760b5410006092180d818010400611840780d203818003040e614000395180c503000f8190400d80700e04800000c0b0a018480c3d095001c91a0f0340240007003044249810345203046112b00e10040b228 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602744091 1250 602742841 602742857
    0x28020a05040e03040b0f12130201030c020a0312020f0403050f0a030f090509070f020c0d1101030b1509122b1e1e0207031a040b0c160602030606070b090706 68
    0x1541030600807540a04040701c01941000d00b0a00a92019001b000386e0f860300d800309104000800340d4400c0c1d81da0050340c0050040000001c5400014191003c01914030113640c0709030f07100c0780002c2e402442400d2b040b6098400607100c0920120381d40301441141c0c0701502c0d511170341060a08480d401b0030105d010304e2090704c4a4505215000080e26400420b01c2000d0b8001080000589040d003e00c1c2c201c44409114130640301030940e085e000038001003040c40d0986071015034030400350003960503202c4c007007440b0b8003102d0802141c0d241d81d81112840c07141070075403130040c42c400791f03120305503613081014080d80000032410691949190415a010100e0700080380c0000e841014500200581a40002240540b541d14030402c040c100c000c000e50040e54255110031807041c010700001040d0840c002e00e00d01c0d88030030b01004642c00e0031b05010042e01030203404410700035030400c059884e40300d01071298484a41d2000001d80c0741c0e03841e0380000e5040e0141050141255050b042044500301011481e02d040d100c4e96104d002c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602745341 1250 602744091 602744099
    0xf050117060f0411090703050103150e0a060209031203040b0405012003060405060a090c2f1c050f0f34031202040f0608071704020d0308040528020a 65
    0x4010000c04480c1800c60304014007240000326446611607205018404081c510981d1801180180c0c000301c0f00080042d42e03450050080050200d0f4184102c401147d090081d40c0381d0000042c2c494040001c01000c25500151041c2903440030b00188080d101442e5100e5145c1c541802c001c01c01c10070480b8121415440c006001c0c42074240c0003080011400c8801c0c2075411170343c600707090000815003e8210346c1e00a08407000002d0110090285900e0b12540340e40e440c444441e0383d01c000e10f42003403102d10134202e41c00c1e111600035404400921500d000c10340c0803000501c1d00504601b07440034891701065078a1684005001020b84001100518001d0014904d00030054145144c1032010002400000030580104101d0400710788142003149280c00c450200500c0e2581d98008001a01610707800200400d03c0f807400c00407070729080140000a50b50042c4450300d80d14165001400c2030100ca41c0c01414400b00901280078003004125050700d40080783c6192100b0b0561030004050f003100200200d100c0c0c00800d0000c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602746591 1250 602745341 602745359
    0x1608090109081c09021f0e0909030703081b0d0605010206180316170426031312050c0409050102040f05062a10053301090501120209030a060f0501 64
    0x1c2140d4000d010541000d4603403e0b03c460020440303010803881c83c0c85582d02005a5150018030303e5a844840750050b03413002210340900444040410315100e078202030200200e20074080f0444218a40c075241401250b40c44001d2110650010f008258120801040380d4406151940c001021340c2c4098088421907a501c078454900341c0a4224141502e0308140491f041c0c07461684010001d44c3e20840302c2c140ca50f03070325803008049900998050700c05075080c04060942040d00c81c5d480140032010502851800c00e40784011842451584030300c07070301031400a0201007031000a102484103100020130a0284034100e04029001c0d4005002c1c90080e003442d00b100151602e8041c08482c603030140701c5280c20710781035252071460b8a4140c031005000c02d8010511f08054004051141314852420200c4441111a4a1200b0302468214046641c02d5050a040b031400340d0b0b820a611a0480b0f0091900c409003620409200d0041d00613100d0260b014410424154108180340e000504160b448000802680c0e1341c1e6045030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602747841 1250 602746591 602746601
    0x118110702010e0108100b0d020904060803070305160212010e0606030d020109020f04020a0302070c080f0c0402070f0212160b040302150a0c060f0213170105090c01050a210516080901 80
    0xb40850300c0007a19298650041d40c82030350000f108451409034a550300b00644144e0f00c0108845102c0b580003c064401e490315115030806172030104010340c1031640d2035402070302d6031140380301c401000ca101c0d41c04241155580b280e05913810503818000d004014030000f00503919101501e043c4c0c0b00b80501e27290b80a0b40c503c144114420382c2d0b0020009004d9003c0f000a0000a500c8a581c42d01016001c00c440004664800c41240041898900070b0000c000c40d1880c1c0741c188421008030340c0c41a401040140c02040c0084002d560f0103804641c00b121420020158510f40b059010101582c0800c03620001503031400403020f001100e009840c0e00c1102d0040300800398040c0701d203042d001c0202c2d072003401c1a000303c0e01941c800012100d02000061404641c40c00042c1d10013041c5e480101200c41090b882d8200010a0013115046010702006011031402c00c800a0031078041e10701d5031000c00c4003440d50142030540720011400d0b450a400d004029904101000304504021036043c00003003000701011402c1c0e100144030b6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602749091 1250 602747841 602747843
    0x30714060c07150908070503040f21030e010c050d0c03020f06100b0315040207150e070608010501030e01230609010e0903040b0a05130902030a110f070f05120301181107 74
    0x805140400542c0c9001c6a900440001203501c0c0c0c0c0c80700000700141131174004104080c05000115117652034000000c80c1110160494840340b50320f8222510304100d18069883c0195241c2050150f250061004843d0340f80f60281c042c2243c46034580d0000c1a5400405070002d045c000d81c00e4a04a0f03501112440d42c41c0d105031441400350018007009c0201105403800340d50810851300040d01c210990030000703030aa821200007654400005805070841c851648500c1c42c2054a80d03028140c580d207420006061003c0c1441070a05242c0c80c0c0c100d135101004290700049000b11021941034030024a5541c2030f0780b4102c100c81d180c1c05000e0b0307140003181040704c1018462140040200540c5410b00f050440c3d4280e4005010b05410711909018282559050600c2e500280855440060302d9180103401d134001e4841d04112501c407013404002111100c200c3c401184e03805078100e030480160188628000d40f60583c603959480b40104044008648180340300382c8800450820001401040400ba602d00c90b98030070008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602750341 1250 602749091 602749111
    0x180203040210030b180705040501030605011707030c0905040f0b2b1b1502060406062903060a08150402100306051f090f0f03050708061e060319030203071406 69
    0x180382800544290011341031480d01600001400c1040d0008507502c2909170348031001302c0c2c000b08040c085540d0600c210301c0200800d1078124aa03e108220711001100e010f0505401c143c1c80d5241460759900030700e5100001c14000d44100810340544001e10014540a0521449121000c0c0302c030400c0415404046184808012204030340015030340c2d144424880c1e00e001c007541981c440c7d00080e5841a040d5800d03200e80958000c1c1582d0328048c90700900320745a50b080681d074000444080d414103000055104200103000f054075580383c45100014002c0d03855a40100014841c0480480c106041140902d002e80d10944042c010047c10f81010f03415141140a000e40204030b080c5950052125241d0a0000d05050704000d86090b8039050807942c200b5013500289280000c0800400402a00300244001414a403000d8010303400d004440489410700da02c04201017400c0710010422503981440050b51120552018241ca81c11500e006034480d00720500560700f07a507105c0d00c5440183d0010800900c030701c003108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602751591 1250 602750341 602750359
    0x6040c09081c030b060403060b090108030408030a0c0c0801091a15130507180b040501090b030c0a050c010b030d0e100305060616061d0604120e01020319271802030402 73
    0xc05400300c0d0b03200207061001010746621402c002501c0d1a00204050344c003c120100740501c015092002c0844181d010190b20345c0100401c000c5402d01105440c0140003502d0200b0740c10390035051040254585400980040d40ba0027081020045800c3380f0240a140070800c00c040359480042d82407482c0507440b07005401c1651800d801e0990125640170a40c8a440ca06181240b014428000e15940072180c10003114004c000405100380e43c2c2040b2000300400900311901d02d186000c3c24450082d0103841586030a0240201e14004480001e42080006460140880c1c40603442102c0092905020b25a4240034000660071202c80070310a00907144211005001946401c8145c030364504104940d600a9588039941c9603545040c080103404651000480001407125080500f072142440386000e00010034425544400c61941e600881078900ca115840604922005a510262498201180c20825020360a680c0c6c081104003d80d105080d070b408005600007038921102c9072400c0344000c0d00d01035481819a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602752841 1250 602751591 602751613
    0x10020706091410030c11060403080712060f0b09120102270d0f030e060408100b0108060307080703170d020304060c1206030f02040213080d03020a0806090f0a050c0415020606040c0908 80
    0x85d07040035080e459a49040c05402e188440030504101c01582e0880000d05c2c168207010400381d00000d00041c07480c200d0303406c1050515040c2c00c5205c1d92200d106403c9036520200d280022a56540f54000f0a900094000c3d5900e24024041c00410090309041d07405104140040303480c00d04200c80028407495011a059108144e2a182504d0305009900e94551019040001140e840000c0c0b01201c00c0401c101000300d00021001c0015060340c1d070040509019a02c0b0000030403090038005045000c582d00001000102040a00900c1c03151194100e076621550000003072104202c03491380076450610807950303100d80094804580c401550028030014180340d000c03000e98009450b2560081c60324004800350003a0007a43e60030142d080103c1054000c01181d8040303801d065890301700740520340c420011200342d4054a800311001001c500302030010300300e00b5592800514003c3c0450304036409001070081c3e00c960309400c0c1100960f2000c2c216803140c013a03420003030a48003641c0140e1040082d00c20401c080c15800c009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602754091 1250 602752841 602752847
    0x30d09060f020406050d060b0c0303130804030b0403120e01020301080a240c0908010b0301110711032b02070510051213020405040c061e020316020f10020706091410 72
    0x10554040e600295a1100112111003a100038402044203840b02903e80a00001c40412200140d11800049201f0042e11740d00242c08400c5951111041401d18024042400d04080c5801150801400c1d1110242400181508102d844100b01c0c0b40f92014000000b0301c26105003070740403c0c0324540c015030180c1c940f40002800040003990805090586d121030404403402d80d400c0e07840214110011400c2c15501780090402801076584080c0143c0007401f6410305000c0e08001d612455034050260718400c0c2d503a20981c0d60038000d455403903039060000c5800032009603420b000e9091080d42c11001d482000800200c508001500c2401400d26845031401e1040042c00203245440c0100074055804002d0610f03c010b035250f2003224015405032600700801c82c1050400ba1006510308400030704400d08070051200103600000f01d4200400c80c1401012032400b51010502c0c82d400e1104d40d69001c2c003070f00c0e01d00714000d41c0003c1c02d500b10384d010b9039981d403442c2d911820108240b4141c0b46c0903070040e420240100c106c40c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602755341 1250 602754091 602754101
    0xc1c061a0a020102071703100f0302060319020903072606010308030106200304030303090213090b010510050c01180c0609030c0605181e0307060311070b0a0e0709090b0708040302030d 80
    0xd0140005440c1200303d071b0350f0011096200d10342610f61103011040c40b082004000da01720141c0a603014001c034650460300000c4c002d010080c45500708002550010040990980641c0d60020b00075003100d900e1a20707203060402001081001d68a2030b04c0404a031944030b807000801c1412250400c02c6285164201101119400703038001d1100000b40041008010b03601c07082000700700440c0213a8001542c0c00701441003050140c070380544600038900300a60500403514040c0641d045600c103d80b12451100d20460680349030180c0130ba107103125481c14105280070b02c001500c06007105c0c419200b69190303640310f4005594440c400e02020b42240552f060900840f400b810003010f00c150141c01903d5006000b0001070068001c402110f5004d00d09101a0584d9007000c1010340b000d000c19080901c11001c601907a482c083c01038403005040120890007250504100b0703030040c10b074607900d0000e4844072500c421a940140000c0d800803a09800e10038001401c051060b0345060055031701d075010754a4140b40034a039601a00f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602756591 1250 602755341 602755357
    0x302061801090f03030504050a0e01080606040e0f0304180b030d1202091c05010e060f220c0e0405150c03190510051207050307171507030908030c1c061a 67
    0x5000342c8007080c0c0d20749482d0b40301c0055119540c1c16a032581090140408007001d0b90082e40300280180c014003a0710804680c2590210094500150400e5246009481c0c41d40510b10701781c1a00002034042210b40025841000d611a170040900c1424401002d0655503610716508400040300c0742c03e0f04007942c10b6a0020103807214000c047e00d62040f805070240c030b180215403400710740580d0b680500e03c0e0924000e02803076a00c205a0340c150400c038580007604150f008a1070150f040a007803c003030b44204005030182c2c1c580207801d0a042e20368051801d4907003240c2e2002034902e2564080b42400001d0502416601100e2040e03040c4c030b185140c0c9440c0c504075103010305000380090b031075445c00d10f8002c01e00d52079960b04510341981a4004014145c0b400081c1401c200340c640040c1802a849800101c407901c0000f07042030031440340c58644072250b82d14034088000b450701c880001e00845000080c000d500041030040c0000103040c440480220303510301c4001c01103030301c284175640510a491024050b2808540c0142441e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602757841 1250 602756591 602756597
    0x15161103070605010e19150513020c03032e0f0e0403020f1c090602060f1503100606020a02010e010806030a0602090103240e0f240d0f03080a150302061801 68
    0x840c40c640e440c5420b0f640260482c1c1e8070369000c0d40820017045000b5050034940c0140d604100099483c0c429024102e09003400385a006140b9400c01041e80c00e4070f070f41103509845142040d00d849081c0b0b01885d50700584c007040c01c110255000881c41c821a04600b41b050212058205556003091400c994044264070003007098065000300e00300300480c2034052004a0501c80d400c540040c10244d4680c0c068003a4045400c10300c110341c040343c10040341c284031410340743e0804d40b038500d8801d10015420000e4a0182c0c80e140100056042600020304650000b40c12000c8034800d8881c0400504104011200c4c02c60407214242c0c107901c015064801300d20305a00400702c00c0c4043c540801d0b65980681d000e2560001014071041215000708104140300d0140301e4103030010440014110b4508180c2d01d480700c0f8101c403200c803034115100e031400015203658910550309401d80c811030ac900c002c6014107014050340700442e40840302030f003007040426400c8410070310348098a038001e110301c1c00e004100c42c21004400d205040c4a040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602759091 1250 602757841 602757847
    0x303241a0403083606070b0604150f0e0c09011e0e040905061608040b01030b091507080612210702040204170708010f0614130603080f040815161103 65
    0x118040d00010000da20320300c0840c00c00809030120218402140b024510400101d40000c4c019039940c49044070481d94202c3c040c20070a803581c03800103001f40580c9004200c03012a0820000e001c0c0300c00410042202e681b132200e03501c00e60390402120001e02c01c401c00c482c00180400c22041d0302d84441c201898040d102c9190282001e9541c43c007182c12100d0005040d100d41e48100c041004851007003440c545032040341c0c6010341150600c6e50300e09162a8041c003008140d03240310400203404d07600c02c10110181100400d00311009007403124001e0040039060340c846004074460035600c181d6103800590541000350000140081c001e03a000f60315455001150100e900540811000450102c01002e442d03082d40610007070304031a890480103a08481858081c6a09107050400c1080645003075400c00241d490142c0d449078044189000403801003540d40c200500b00000481c0e07602d5042c160030f000d031041d1900c0c10110b8452510072100945560404c60344200d400c10001980c180c00d600c10381c07401d08540000412241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602760341 1250 602759091 602759093
    0x10e0618100507170708070f1a0f0601031401150e150403030e18040804090b010c121e030603080d090825110d05060a020c07030609050a0303241a0403 66
    0x10101041080020b8008200d01007848418440c0129604a820596107040e20580c2c5400f042d001c1c2150290140203003002110501c00b00403a074a0403d02d0300c400804540c40c04501071001110207641d81d900203407501300000044151080ea05059400000020210390f0111340b040b1020b0510740100e64228001c24005110071803100c001c0e1010310f11a07102c01600840c481c0130302000b04051144850356501410500020030301110481e01500c1c031200000c182c0b40c80050050300c10041c2001f000b40a450501a4103007a190700102c00140204036200010340381410140440983e011404007510343d420401c1780c0c07092555140e00924801d480f4a1503141440304545841c460280d4030010055500d003100144420040e081144522451084810048150050b16040d40d50100107041c00c882e19030005114012101c00c00218000b035a0000c41030110000c0c510b0050303120501414100c000c01e090902181e100c20400340c40c00d15480f4203136000c0c2a443c0c6402d4004854481080e10a0707100d01007004040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602761591 1250 602760341 602760349
    0xa020c040f0b0319050c030303040f1b030b1003030305060105390d05130506251412090f040b15030a06091a01120b0616050708070303121a010e0618 65
    0x10069058035013105440c0582000d500f842032200419210750802c10403c400900c21100d080802a04003455040c0d201c1030880b001007540031500050240c0d1805810488942105070014003074070700c280e50511480e15054015102409400c2c01c4031102c9001c0407006005c020040b0a20003807884c107011004d00c40f04402e500c2401c00c03106001310302c0044d40005a0701c02940032040b4000007410280c0307080c1c1c0351191142103055181c102860140c01c100320542c09605020111103d21806c540c0300b000d44e00c0f40d50201c1c540380101d0348074102c80c0340150f01c011668481d91170b03c0c1c1304110705004060040d440d07003c22480c101c1e0303450f80300428000751320340c1d1040701281494540c8280729001810700d90022010900b0070000d000c400c1041c0340c50040714144001075040d41c44240c103883e0181142408503010030701d54901581015410341042409224001001081c944d000002c0320201c03000d44410481240003000d1954103002d00c200440c041101b40000300c400e424000700500b01d00c0755000f50100040042000a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602762841 1250 602761591 602761603
    0x5030d0617100b1c1110120e1c0f1e020a260906030a1512051501140411121609080a081803150106020309120303150609012604060b04020a020c040f0b03 67
    0x1d407580c0718803c0000007131f1003981030340c00c44040201400481c1401408049a44807400c0041001d502c0d59030130004c0c0a8400c01c910320714080c14280d281c640c0e41d28006e5030dc1325000c405503440215102506c80ba00400300d8440c0b0b17612201d12141e880c00b0103000c00d11119a00160600c202590344080800300c49100074000c01c0540500000c1000755041410f1091410505001040c5040320341c100412058103401603512a0b40001d0390042150340c034851a00341c00c0d00410f02ca007038801608908210f003031640302c254403a5505d09900c880c0260750311060742c0c2d0350b01c0341c0d040030060814400f009a50f102200410201494075401401c980c0102c402d400b000c4a006c1d800e038013403005a400460580f10500d05100002c1c42c0c0c51401004600f503241140d088042410b8120803203006000000780d05000703900c070340e1007028404e0040441e1105903065480c1501242c1045400b40e0340d1524164800d403c601e824002c0f2046040f250f03005180890201081200920300c4c5450100303507560b40c1000a02586040c001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602764091 1250 602762841 602762869
    0x40909030c0804120209060306060f0f060c06010315050916030807020604080a06050a2304120215010b0901090b040b030f0c190e04050604111605030d0617100b1c11 72
    0x11350101c0d00c4040c0706001c48508003500c80c51080e0890410442c55844051603444041012a0b10840d0b10152101080441c8545000f51446c1d000d000d00200601a110841c08600100c003041081542e0358038100701d4440e0b81c050181c081460300c1070000c0010400407000340c0101c0e800104068070706981c6052091411001320b000321211522030080128071282031081013444002c46400b41031019101d030301800c004900503c000c01c00b075062941c511416200b0095201104800c9000580e1544c41d80c1a0064540007000c209001810102010481c84000c0e019038003211101c02d05036045880d101860840d2001c0103008828500d000c0c05100b0b0300340401c40740c581c84402562200c41c041120041480f0035103400615083c002c40c00c01c0110480140c3c5030049030603022032204011320f15406441c00508601c01c60003030680e102c0c1002000300d422092549a002d040302840e080b1070140c40d0801d402d41c250b43c6a080c2d031301c3c1c0c07010a2030b01404107560182407401c1d0080c4100020808040501d002402210000b03c0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602765341 1250 602764091 602764109
    0x406090608010e070609051c0609020d0c03110604060816020f1b01030b09070e060c0709110d0f06060203031803040801091109010f050f010521010303050d1a0303040909030c0804 78
    0x40300110f10207050000602800781442e00702c54050400b40070030380100c03070714104d040c400300620300e00c009000480d400000959402031449a1171850780c00e101191b110740c5d000c280c480300f49420700c40000c2d103090011034007202d04540300d19003565160300141410509200c00790041d809100005419030340180009031550b050040b131082460306520005044508503002e00c2e0080c01c41d441884580c1350044034868031110704581c141c0d0381d40d6034210b129040c0f15a0307030b0010f071400e0b0404101d58000d105c0b100c0079044000c441c6400b00724189a800007e000d482d514410303040960810404200d49400c2a607001042e090500201c030f00d000e5442d80c41c2401c4030541d1800703468519003d0481141490307d5101d0b60b0041c03503200140c080150900c000503c14170582c102d0241446400565100ca129040ca06118903a440d000c0007103066a480c100039107164442890403c1d442c3c54546d040a0000d41210454100d1601500a41c00c240c00d108800d002000340070016028064942c0c408400144048002d0001d481044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602766591 1250 602765341 602765351
    0x2030f070306020d0e0f1002220603091103010b0a0e0901271a0103081206041b2703050c090a06080303071701090603020f0f04110c0c030c01080105030318040609060801 74
    0x540702d130045696121415002e03800010161542c1500061201c102801c2c000700140da41d610405014240e88000e824440f12013210240000c07900d4141c0d00051285014403091044101144201403c0781d00a1000d503600052004080c00002d550341040b9070f00c07403118800040c2c4220341c5900d0250314030201c2c140d2402c030340345408564100171200c0c18505010000400390116541141c1d12b1090901400c80030100d20254607001450030b98450700702d125070b408001c0b50000c00070100c2c00000c00d00c0401d0a40300c1350510b0143c03442d0301c0c07480162038454100d9402c80080d20200120400304014994007a0028040c55114040816440005d2004500441c3e450712199518201507e41c103244440c168059405a0300c0e200e010409a103c1e400c00005400302120b00c2200d02251900041c01080c1c0b8007180d00e01004080351032000b01030000360141008070102c080381c071142c40c48401110300300000d008082e0150028000f0741c440c01d003182c441e6404901700401c00304242c1d0301c500858003105c00c03a40c0060403580d150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602767841 1250 602766591 602766607
    0xa1202031c090e040305090607030f090b0c2d120a080a0c0f0c060f05070507060506031b010f020a170711150a0c150e0c03070b210402030f07030602 65
    0x410600306440900d0074105884440080d01410b103003514440e241a0007078400020341014440d03012a0000000109626201d1410b41801860450960381c000045900000d001c50704e66100425145440800c0c3c0040c1030401d00243c01c070366040134480c06155814100030200c186424280040c0c03905003032120340c0036102e1002203030051641c0742c050070260260303141c0031140090641c000d581598000b6281413a2946900e6480c2c500d0080c005100c828a00703078648414000c0d0031380d0003070040010368020b940501075512010700709a183d071240c0707140114400000060520a50060780c40c00d01d8013009005841d041c1d4815120010500180396030f40321500c400140b40810416600e04801d4811000d60b0603401c9070401801da44190711850031a807040c0090302d4058001c0081c0410180107070443c40304240440e03415041141e80d903042c0090414803d00a1500115142410350140e40840203144244c3c980c0d500c49092020020310040c1c41640c1501601d150807a0041041001100640c403800005a5030104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602769091 1250 602767841 602767843
    0x106080a0317070207030f02010c0506090f0c09161107171e01140612071206020a0801051819092405070c03050d0b21150c030f0a0b0402090a120203 65
    0x100c80ba0000240381000c0910403c0344d4001180000c0d03a920503502441c110f09400181d800d400140c0004101c0d10481e02048410ba601003814070542c09160201d40d924030050041064104088550072090041c40400012491042c400c8090441501d405d86514a456041e0445030105911ba442c4017940520244d0148110250f444545050804005c2000540070300d0440c01e450b170040e00d0148600740445141d0904441404a4801458640c440041c1c2000c185440c00c0650440002d000c046207516000042e2820030562a161003024200a04500e60b201080c45c080400701406890070716a0700c040b003400003400c00360b0590014941c400c1400d600544080408240c2d48001d010204028904143d000001d41000a5070302c14041040c010070089241004103001d13000140400711130308600001d080c40c602d0045038905089841c0000c14086a07108824a00c01d84803e4543c40b806040c190005100c8940c240d11150310128000d0016217031044030000201e0740b96064002e01c1107101507294600841c070b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602770341 1250 602769091 602769107
    0x10504064803021308030319090b040201111e0a2919091a060a0807380301030b1005010c0807030509010c0c0f081e03070b1806010303050423030c0d0f050106080a03 72
    0x8003100b024440c9c0c00c85c6a0703601c15004000742000341400003c120314412054107024034507059203c02c260360030050344100443e6549041c00001d42c0c010544100e0a8403495070490125102c00300600c1c480219191100c440c0c040f40007508544107075550358902a000991207824030f140241e0300540788541414040208000000c0c41da008010390340c0001c5081096200086070401422441c0c0c440031061084100105410420707083d202c201c0c003a00100100801420404250080342c201c1d92810300c7c1074903800192a004c500030302c040c00b80307502846207000092240d0001d11440d4010f140140da17421660341c80c4201422140c0040280d81a160000d01201400b040700808034941840041c1d491a00c00e415a512071048100c00351004000c40c000a00b40c042c080245c01c1602c81d22000c8822560b980e003402082c58005008542c00301d0092001d100704485001d6501ca00c442004003e4418980702c00b08001d4400140074003250051850300320301c00440c000b88103803401000000050301140b400e91800902e400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602771591 1250 602770341 602770381
    0x6021c0603230d0302130e0109090c060e1305070e09011514070f060b0604031b05011b02030d0806030f01150602010c0801140405040809030105040648030213080303 72
    0x508011140e8414002c0051080c0114806090040e510b820b45503401c1103e0806c0e401003448490404000104005150301200080c2c1c002c0082ca82581d071206011900040c518105941c010a90202c420076045187c0c4400d07044400c038146070001c200e260003c1205c0c2c01e426070014580b1030058000074281d942114601481020000e61149085207a42d14600246003114001d06400d41c3d400801016459150454016582101120010f10406070320b5007846503040c000c0e070f40003442a95100840b002100c0d030808002e50b00a015000007132175440c0c102c521181c000c05072507042c03250140e807403040c8078207104803c4075100e010828003c03542080b602a0031b503010b00060b042000718910041110264607583c05000d004110707000b00c0c094885003001015405042d01c4554903518280a200401a0720f521000741c524582c0a04c94154201607100c007201c400c102840c1440181000d241c41140c034129210000c1c0105a0a0060130310442e0300340302841580503080701304554000424803d080c108019804c00407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602772841 1250 602771591 602771633
    0xa0c060e0d081b030c0a031118040f060501020616140c0304150918020d1103011701061a0a1b080c06150d0305040902070c09020a020d08130209060d06021c0603 70
    0x145800c80202107040c400141750850060020a0104078103101c0e412548411103009581615070442c03600100b4042c161400f03c1e44500d00e41220b03142040c1701c1d40120f1048900503000340405a40d0906c0c000301818a6100340030802c2508004001c24440308806084881e5600300215121404d00715102c240d94960100c0409000049030200b03c0d083ea03621035110303480b0902034090f840d05c3c0c2242203040605024040140281c2c40070001041c501703054000030b014092030034028080706e030b900d815072075010700243d030520065001000000c5519006a2029441d05100445004011410344600d0000d80125a0705907031900460103029480d8289900b103960180112403403c1e1541c49950040c02c140700354400c100e41941c000c0b0381c0c8824440f80912820040c1841c2c0c01c107654034401c1d00c0000b034649054154030700124907110003041100b5490700d0708032462980a46041c081d51249420070441c0c240402c003c4400c20b8007048415041844461201000f9064070070219403141580b0b000000daa40544043c000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602774091 1250 602772841 602772871
    0x61b0616110a0209040201121b0e0112110301150207182c0a060b030a0f061b031109060f07052a030d08060415030f080301050f150a050a0c060e0d08 65
    0x25135100156640c11581c242403000c00300c040045d404014200c51040751003090f4140200380041c4d500300d20341d414445801d03603500d03240c008529900b50481380400460541041c0620041c0100d034504500c0440780e0071580101c5201c143d4800c420300020241d110911000c6440c2e02c550f00c14848505601c0010840700040d00301014901a001e0b581d40740c4003900900b10761788901400699072411b1011035941d80d00728a100785040c4035410640040d2204280051102d607650130542030043c402c3c400d0b070200301b030262525440c1050383e00401c04103030000b0035640c00c0001c0400000c00083c0041204181602070300d416445034460410b000a1a10703001081140242c02c52281c42d402903501070130705507000d0422100011040e0817503420803c80081900014800d0391200412403c0c403080402450403150202c418a8080440c8800c3c012a500b00060aaa10314003e10404207503d00071409410030b031140c0c0c6030650302d88003030ba1905026610b190541140f06e420000c001d12000b54840c0c41681e220144e07103881c000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602775341 1250 602774091 602774093
    0xf041e150509091003122325020307050d050f060f070219140321130f17090a0e040201080901020301150c1403030c0a030b01170105061b0616110a 64
    0x400c5105080c0910302ca0f010301c10006104840f01c01400340031356040b01103900b491812400c0038000102d44106005000020101c42104403907880445d20b2078032850010a806020400980c1c51400e003d0702e0032685805124000305d09611101001034800340254020f01c60704101104441c10071102908051118003004200092207400246810703002c45030503d1481443c686040400d02008910b44194150000050580200060350306070214403000c0c0d1113000c05900d6a401d9851001000030b001410280c21303c03441004221061322126034440c1d901191480c00c1003003400030341d1500098108100c02070900d020b000030365038041d440342c3e80a04440021461941080601d24006c802601c854040208504010040012840e88000a4101b1b5822691203050140482e4820b801900546001a01c6d102c403141c3c280d842681e60440c00c542002c40c4030001d900f80028041240d100ca42c0c690300c2014030345070002c5002e404000b15403080c0383c1000782903001868840020a04d1b03a030410070948591061203180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602776591 1250 602775341 602775347
    0x604110f0705010902040e07080f06090715030b030703060e060a0501050603010902160c06110f0a0305040603020d0b03071401030f051509100e04291005040b060f041e15 74
    0xd4584200c014503581c48001d01c0c034101c1c1c050b04902d00001d41050504448500c40c00c000900d15050707640c1ca405403110408000141ca40c1c44908486070031013540460740070480300ca50020803213000c40080c5400300d00e280c41c64010903c2c1c11040d51080314010781c0c036410002d80c0001800440e800c11005002031046514040020381e0500040c0980808264001000b0301180c0007261640802a40700101f11003855540c900545150396010a079001402060000600008045880c0810b10f9042d15101e003031900348001140250001c4022408103540c411008138540d804000100090940f011260895800c0100041c1598140c1f091561035600b40018042c0500c0c2240c461980d80780161001d814030b56801c800c0404141d490f5028110000180b024070017401210040c05448d0040ca00c0b0280c05485011110403444908036881410120144000d01043c6807581040300c210b90002c0520b801c24022401d1140e107035210f0381c0f04404040111015410b41c040c02207800000b06402c182c1c0030120011030f4805 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602777841 1250 602776591 602776597
    0x31f080d030b09101701200c01050108030a0c0b131b06021c05030a0c051204080a02060c160f081c0b040c0e03060a0b030a060903081f05010e150f21060411 68
    0x742c13031784a00c0c100c070f0b07072208500960010360360303032200802030b280c1d0380c40480c01c0a52a48505000c400650034100041641e0100004841c1d64802d04d98600701d07411682e45501c0b0710301134050527080e10440344110600c003188003a40d0b10885400c8078003240f503d8900e081c02c06482c00404500e103002040c8141c05a080b13558009054988c04a030003000400e445d0b045410440b054031a00c50108000d003020001d201c24804140d02400200209400300c030103076241e507000c034210350054000c1c0700701550a1120300da0000c0e825449801c1040d1080894a04011003200312034001608421065002a91818400410b14040c0038808000445003042c01c1c511008401003500c50100501c400c2c02e854403102c072985540c40c108156050141c000c102001132641d14540200651000d9650025601031000d009030004841110a03003101d1058540c41c070705440d100180304000c0350004079450090810b001006e0305100b01001080b40500c01410000d10700b1001c04181102c032805000c4c68000e505e00b90380e039102e5051900c21 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602779091 1250 602777841 602777849
    0xf080105011d0301020c070f030b07080402060921010c26010e07200304060c0b0901060602060a0c09050901080606011d030a0807330605030f0a0602031f080d030b0910 73
    0x2c002c15036210100f8068810070030554045e208442000498480100001007503d1103408000141c2c0c44908040700d915000303450181d4001c03010801c40d045c902e806035401d030100a141192017041c0b00d580b060342e82100d810403001d1011070407500c1158035451912046140700c00b8898235600785541004800c0d280710f5801006075051110408160001c4d11480d0740300c2c00141200c0c41240e40d9180ca03280010a00c0003d40c104449242c402804075038041d80600424094030304550080200d036644001d40d4000c0c10480820700c0600804040108150b01c400c8403444c040c040c604000d013014148100010200544400c02e40c0c4024a900b03840c010329039000c140c4c0d4110a400241141e10f6400754180005c0c0c0b007480c4044c5800400464a030310354407070482c00101200c1d00d01a0b2040028a946205158442c01c0c2c11010104a810144000001443c2640599003001c103840181c4c1d6414036100c0d90400d2919950480c501642c0a071842d00a65035060203030070007078041035038980018104003800340b1074803a40380a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602780341 1250 602779091 602779127
    0xc14030f0f0a02150706110405040c0f0804060b0607170309060f091f1d06100b0a02060a05150603180714130504031407140d030603080d1a040e0303070f08010501 71
    0x1194001c510b0200d400e8817501a00b0240030030a104169441000710323445480341c5070059050000303000c481c1e130040180d013032400155111a80782d0b503616034441006045103060541d118105000e214040740d180c12541c1751103000c58004554a00301029018a0014000c008404400d2085d040141e00d50000c07400e10b0f00101d1450a200c5100c4129103210041d0408040c10a41c041c0010301d0749a00740320010f540d50240070321205110441c2d44561111009205011008001d80c1c01040841c0c010a2240c0c0440c1d4000d03040d2007c40e100841ea0400101c16a1080e111901880d2100030700c2000721030107001c6e0100505c031048100744441c42d120301140d136001c86420900803461f03036680000e06041c000c100c2001e01031413101c0c640b50794100c2442c04004865400352018543c0c4500003030710011a0080c0700d540305036500924141e041a9031292180d020303001804403110801b46200030215251624058a01c03141e1040000d9030b01c82c98501e00050011000941c400300b0070200000420850340c12204005803034100c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602781591 1250 602780341 602780359
    0xf0227030312060126060f062a150c0d14010f03031116060c060f0e07120507120812060405071b020411030f01150c030512070c0c14030f0f0a02 63
    0x3c006a8120341c81c144000c001c2404c000c01d20303030404024000345120b802c00301e440303000031084981804001e0007148070f09482c506003008031850440c000c41c004202c0385180c0c0204d910325002030320701507000681503d058a03034071800706610800d000d05020314001c004481a0590701c0350326018042c030b4030038428400a800d02c040c004002e042c5100c248269821520200b040340489179131854001c240001c01d010a9806502c1d20914020401031401a02442651800181441428076075000c281010750300b000c8409200702c060024618444c1301c40c40c40702c603003d00c10140e101c4c1046011075005100051426203e645480100b0a502c0e0b0232107040ca11346220311020f80700030381c2c20f4400300300144000758048041d00c00c084104501c52540b01410f40c1030b03581016944048500850003a41c102c4100b000050101c1d03424001010072103864034606038442c50300e1402c402c007040651140910f40c0803d03000b0b4100c940107000c2038004d504040046401c601d901c1030040c1162380035003041c5500c42e4030b032510081c4500303100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602782841 1250 602781591 602781601
    0x1305010f11030d18140c0111060402100f020a0c0801090c06030506100809010e0609010b010f090311060a140d15140d060203060109030b13020109120305031501120f0227030312 77
    0x80d443d809016078007032100302c0c5503170302c0a0360705070b03107100882a4900140e0440880d111408000c28110300980d409808050002c015810681d04203507580000011803107508410404601903200300f0000341550000000c000c81c0d54184121411001d401030400d242c01d207400d000440c2c0b5203e400c0350a00c41180f82c8008191a124091400341060001800e8244514800c2c4030140d50194031200b4940400d88400301e1801c010803050741d0511300c6200180c0001090401c5504c07504100008012850701440c1c04070004401010620154000c81e201d1814103603200e8100c0680c04041032040042c0141407680100c50a0040000b280c29440310401071580c1c0e008404100241d02a4074248080c583c00340c0d0302c1540e40b07082d06100079044154041680040d01c0d200c000901007010750b0505494903016034a8602e559203540c5010b40ea1280c00154a041100794184032490204c644203000c030b04030b9180c0c001769035900e803404203000c0310804d62213440c00210100c100340c5041e81e00104460304058a100f004800f43c0e54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602784091 1250 602782841 602782871
    0x210050c0303070e22061404090302071a09100c060f020c030d090c0801050708090d08010e04110a05091e0c041d1009050a05162a080f1305010f11030d 66
    0x241e060821182d0307914501c00c0c170030a10039421110581b41c1104214821510345810030042d12203055000c0c0158202850511070035400c10100c0b280303001400c0380c440c601400701c8081018040c4200d00c3c43d0008804003000001c2000314014038150200b007410030360420340c020380000d880c2d20440c41811a1160358808100801010041190040c1003401c02080f0700d142844004d0b01342c1e841107980414038021034440c0c0030054001c49805058400840e000042c6a8583e40d8101030416540900d5a0001101d18005229039426140c03d1041c01140800c50f051400040307034000400c0003400c41c4d1111002840706215001d0a0450585820748850600c0c4031f64071404540080c5000c0b0b034111006150800042101c9401a0340141c2c1c091002d281c425414603030b061404a0b16422010103060203a0305003681400d00400f60100c032481c190040100030320340700350201c03c2242980010140d0000e0400520104140c1d07801074140c941224180c142142c0b0a0303180c0d071616460703100d000340c10340220703640e11803042d42c00c26 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602785341 1250 602784091 602784109
    0x100f0201090510060305210f030606130b0d0e0c090610140c0123040b0126030c060906060307030c09021303020d032304030203061902071a040210050c0303070e 70
    0x40c02c0416600b010040c0c4403010040d000c540800d0b140d0384500440124018840d001c0007400014401c029810501c0c0c2e2018010280c0c80035080c40c1d4041e405000101046840d41c0c3e20300c004003401c05a1517030351903c0d11890340549200603603155140c1c11010861113182c88248000c0e5202d2012541d200404052090503a21264010400b148028000c694124618030541c080e1451020300340002d02060602c0f5811002e0070b1f41158001c1014000380010480c1409035084600d031a076130404c03030030140342c1175051851858200c895070790003d612080a05c010880c0c1480225000201907000d030440509680790481c4031802d6205401d14103038006801c00c02e60001041e06000f030342e03000b01950b4409446080c000e08a6103050410307408201001307011381d07200300304130100c0b01140c0d4007074003601d61a610820040050006941b0915101c2c0e0200000000100401021000d03207034107031004903203800d0a00500400e080a10158824080d04000c1c9001121002043d00c0c0d0140c128549640c03800954008142801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602786591 1250 602785341 602785343
    0x121605041824090b010b0d11090d02011202040b070809090105012a02011403010602150106030c0f030504230303041e0c170f01050907080f01020a0c200d0605060f0906100f020109 78
    0x31442c4c2e0300210751400e0407001406044075101d010720100c000c6800390700342441030380f2001d6444090b0641c4100154000e00c4001c1251045100060405544140c04802940407250442e0204000100e1109a00e05901c2c2c05024007000e2a04400005003205180700440c1c0d09140011800d410880c0e5800710380c8542c4051011541114010791a03503075032040a995070550300200000c000c4208004240a0312a124440031556103a0ba50440740040e4101078005010250050395501c045034000210f103054aa00032500c20002002195030340343c6070410740041c00b51740f100c400305030701e0f000c0010001c41c00300314580041c1c0e5840805074641c0303100b40a07013a1414500b0134117110b081d404d01042200c50200070a803c42240c0c2200155000300c4003c0601500300c3c40b1b01a40ac402103980d00580d0320200c2d1501c0660248004400d0284e09695502c40000f02c0c0511400c004840664540080020b141020402550821000d841c60116410100002003a45000c0e0b54060308010780410108261407003500500c0a1b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602787841 1250 602786591 602786603
    0x206070507080405212419020d0207050d0f1b2d061a06041d071110050709090b0d150b1e0a0b03041e0212160504182409 53
    0x481841d08a45501d80d4540c2c401017514010b6115103400d40d102011211200c02030910300d00001c3c0d0b2a8010800090070440b605124241e007400a8074200c40303503200400c5a18040c0e0000c010403240450010a440341c1290031100304601c602c0b15400450401440004565120001c1503201c20302c03d85a00701503114440710b020a80343e0b4a207550a03c8101d6100a07640c40707c8040000401060f030042c001c02d881648980d0801141c1d107010078184198410005070881250301c2c0c140e0100c840170008910388441c804120f02d0b15643d40090002d81c0743c0207643c02c0c008151846c02842035641c0e000000d09050091000642181004030040d80c01d1601039010044010b402008108450001c1484032001c40c0c0d10400c26004a0756503a001c640c071701c869415241f15640c40107011140b2980e000768804404200d00080741c02c00c0021507056601c450a101140409007403c5810000f54034080c2008165181760684941c100140006003000c0350412000440c0744400740c6116002c1040c0c407800038010308400c2d4000c1c10f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602789091 1250 602787841 602787859
    0xc1a13090b22061401030b01020c0609010c08032401030c050901080402011818141003060e0a12020303060a090b0d02091009020f034317070c03031109010206070507080405 75
    0x81c0103020f80c407007415554a05a694aa03900103401901100c150f8466103015074003a071818121860013030010004820180342c0040340401d1669510000c1d0000c0da23003200e548001d02d160710010959103000c0c868030030b42441e090011064129000d04284100c0752114100203840000409690150101d24a01d030400350146011559605c0301c0b520000f01000b078000814286241600c7c011440500d050003180e40b00a445581c6246580e403100424241c1c0d044842c5002d03044003c0c0220f81c0d1040c0000e15040709030050340d502d00d8020100480c4d00450781003100c90b549000a0400c5a8079142c11020200d07034180c8450405440301d24000c0d01407030050f031188490b40c3c0001409101d0341607850141d4056402c40b200850394403000c8002c0103015a00d80c072a2071034180300c00080c1b0700312008030179a0916550340c0d00340b04040241000d5040302014044580401051040140208041e0716204100c2c2c00343c03464000a0401080c000000d489460140650f0204039011400005200300030301200c0041c02c0041000303d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602790341 1250 602789091 602789149
    0x30e03030c0408013b070305010513021f08150d0f060c080f090c010507030302120f09070e01080c0405072607080603150403050c0c0301090c1a13090b 66
    0x4141d602a0041c85903d508200c81d5140000028501c04600c00c5520480c401d0200c1c1d800c40326501d02c13209407805d4014800d140c000030100e0000c1c4202400394124120032000c803c3c0d140140802d0042c01c0110030811851540b01c003060990100c1e40d0b50f003104040e1101d00d20480c100d0005480142d200401400244d0f02030800d10400103e50b1000c90030340290380b52602d0039031307031107001e1540300400f00d40b4a04c1d6900700381c80d510740541c441c030010314040d4482c2c03c0041c1015070034007a4a0700c0003800c4424100c1803851760140101000c0070001080200380403100198698140b881158640c0900c00005000ea501c2d400840c072400e0007110088020b90080c615498042200b03000001c00071002e50300200410b600f200820380d0b03410b0100f01440c043c0000038000b6103d4956a5044130f40b40e02c24044a00140203058011085036428021020414007446090108909019140440d5140049400c00c140020000c0c001600d0000124400f114940c40c80020f15185010100e4503d0a4031011010401d0068907002c3c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602791591 1250 602790341 602790361
    0x212031005120102070308180a0201030b0a0e1e1b091504080a080310150f0c02190603020306090a02120103080304050313060201020d1a1c060b0303210603070303080a020a030e0303 79
    0xc0074172402542ea1a18903100c1c628488603d090003943d401031134102000c1040954042d400824000202030300144ca115503036292400300c4481551246d64400c0903d0401c003d402900003956080460184c80500c520014285110701c0e20030041344a00a0282c114620954201c01d0107840c018072820040d40c24400192514154580c400c42d0114801c8a2503030000c40c0802040222507a009516110041a40f00500094513401040741d0200c2e40f00c413005040146d0f1812038411400140225140941c680c00c2507010081407020041100b1291441403000c1420b2001090b0010b0440ba0440e543c10354a44480c20001e046100300034031a000c45941c268002a010b60541c014488211801010440300368012144044c1450f2060000c0d442007400440b8040e40405403240101c5030700c198400a52028208003080c11900810030603643d2240d40e1046886094404c9005940400c00f10094070446040d50360141c800c90025000050659000c84d11030107081c000d42c1310000e40c01052048a40341d1a000c0403030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602792841 1250 602791591 602791597
    0x403090303091a04060809010608030c0a0501050a020702150c0a060204170f0106030c1e09091214040503070e070c06090c0603060b030609070f1407030c12050a0212031005120102 78
    0x440c009402008009501c00c0f42a241894003080f14190038070706440c060003190f10701e102504190541d507850400144658081000300904005140500314080450420038215000107050f900e0300e1340104082001070756001c4800700c01450031128540c646049070b1034245040398a843c0100b410344001004036080034818103101d01c801840d012a49800c124420746400e07907107148802000da0b0803442042c840c030305a22800c02814411031081d0541141c0e60800c1c90282c07140000c0983d400035001c00350840444c0c0c045551250803000d503205901c2c1901c4c0c803010070b90740c055034840c1c40714184456002c201014421030342c0c21041c0b85c00100134400c0b0011810303e004282c00328407515007c03e2400380c0004032000144280c0b48103450041c00c0e050076640e90401601d00b8040c0541c144c0400000704c02104000c4d070241d01605030740d4000d41e1103203891001071800310498809550100700344a03061001c500080d0b40003600050381c0c20140c2c0c0303598607a19917051600807019a42c1107154042d4144100420080c01503010b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602794091 1250 602792841 602792843
    0x13060809070e0108031c090515280509071a0f03041e20100c080a03090510091509020f040f06050a090504050c0f011e090b030403021b190509060a080604030903 70
    0x207400171b6421401e80104a500c1c8030740092254100c07050340d050f45030442071b20507800244c0e0000302240c01202c105210300e61a0143d9000c0c0b800340d581d01400409442004550041d01c503000407004544045540701c540d90085040c1c1c50200b00b80040014108407000d0b0300701821109000c1200c82e581c1c101d141201e510300c40800d1002d40c3e002c0f4203110303001c1e52608815000d4103041e90380306d00560310440d0f02d07440700d00e030b020100d17541c103160311001c1d903030b0000d2410041c00c0c404005c2c011300010402001d250112100da825010401003600307143d05c100150740c904c5580d1145d960129130020303400708a8a84400501900e038000c90740440c0a20000070740c00000d401641c070482c40b4409a48548204504120300306800200d000e0025010720042004566410011021806030341040002d041e61000c45009a910884085005030040b1060174100348003a91001d44206044078804080306c103c0f0340044100c04a071140f2403184818201090080e04d40c0306c121406404040191081480c1504004d011a2850300c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602795341 1250 602794091 602794117
    0xf0c06220f03060c0e0619112b021606050a0c02210a1103030403030207031e0615030203060a140a09030309060504080910030b010503040201030c11060712060b13060809070e010803 79
    0x109100c4141b40000459440380b007148822614409001c9044a42494940b8207241d00e10464061141c0c43d55110b507540d003049100000b81d9049041000020b040c01204689090200311404040c030001c1d41000c03e8800700c450501d480c3d01080c4282c00010352441400758400503000400d0701c0c9040c0ca11010032490030950062003818a02003a24090541d00c0c0301e244000b074010307001888144001b81c004e44003821050084a106404000039407506400c81d0349920a0030a80303070181c0000c1007142000d100066001e503586004201c5045000c01c0c000005e43c0041081c64417903603c14200080500944c40035015503001001000186803d2400c80190390007a6140d0380304040216400400034400d0040d0218140180c0d203a50460722598015005000d50584d00341c240304040e044240038403400c20165129800d03544e1440a45c100c84174040044502507041504056001c00812207a036030011081c5080b5000c510b060b443e5035880242c52400d24402d6000004000000d600015006200001928008100c1c103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602796591 1250 602795341 602795357
    0x2a0906030605010e0a0e04241d0327010512010e041a070215190507030b0109050301090206070f081e07030215060f04050c0f07030206090f0c06220f03060c 68
    0x10b0040d42c0441c2c100710100c0c2d000c00d0862060000400d0304d02510f41040c400c1d82003941001c111000c2d042c6c184600701e0030784c2010ba41d888207840c0340c100041f41985191920005140740c060040300300404440495008103816004040c5080700d40d200c0c00031103031a4501c00d11000215611000c281c0c2c0754180c207a03402e0b1044080d0f26900c50303c001c035445009002c6c4c04150018180c0d90310a900080381244000d00309040010520841507444019000f50b40c4641085e0390001442c0048200260a007a0141c00c503038000da14041c42c107001a201c01044a140c0d0307400100802007151146080001e03403040c2d8112041240145204144907511407010706081c0d8429001c0e680303824100340305d41100700801c80d400c581c0070605004801c07190406500c010340240041c1180b61038008012440700480c4e0001d00100c0050340900104010000103203e030352035800b82c000250040d55200000a2201e008130f6200002c80c1100e21412911500303e40e849200520400d4940310b0442e6980c203000e80202011a100e0010404034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602797841 1250 602796591 602796599
    0x1b1608030a020d0c061e36020913020d0308010815190906060e180f030705120d15030b0117010c022509020c011b05090a092a09060306 59
    0x4000da9800407980d03030040c9488841481d084900c0000100c054039003036600c2c0098003042c1c2039124219403043c1c0e0440d000c51040b0f59102420b40c0603080380e180120190124441c06400810311003400039441e011076440c6802d413200d1404042020400400035881094a900c100070160008503960403102c2240954520480400c04c03800d441c2c00071500164940c445998107121090241d00180e13959000d9003000a14640758101c46421305e50540f00c40d42d01d064942146900840c0800c03405009840c140040c50034100b1541d00c2c10b0746c0d52204241924090742c04600c9a0040040f0303800031904482007120302031041e80c4d03820000c49c010340070b010380141038a003050644250714050144000307010090740201051035082d641d861280a0054810711721000c15040002c5004090001d44144072190740000742d8504182c0c10700004104000c550700621400f402000300995405030ba001c200e0304800ea001c62001d40c801c0850f100c0c0da1115250a0031003d0031200202900e910035414010784100d502c08010f07a40d1a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602799091 1250 602797841 602797843
    0xd050a02130501030f02280605031906030512030603030d0c0c021f0c02240315040b0102070f0b1b030307080601020c0f060d0209030705031002121b0702090702031b1608 74
    0x2404045c04032003000003540e006051542100200d0680c0700440001d51991086102000305107900080000d840070080c4560f0000b5001c00301c0740c82d0a800004c01c1030901e11b540302516564824244461818088000b81c03081c1c070240115100004238070410011b290b01c5880245c40340d40101700a80c05441f40041c500d08641c0082503151614080d40c4490054400d41d500700248a04405031510000100548146da5200c0c11409140103802c02c1102c48036641b0644203100442d0007100d4224110350120404002c00050344100ca030540d240c07284080d40e60b0000c010703003a483c8004000030120f0b900c0000204200c1d194048140e60140b0f030264244c0c1c5192003420200140c0340044038410354444000c0103416924107e6038021321004c10050140d4000300d6881d00000e01b040340035040c4c00103058000480700a0b5030a02c1c4260380d07101c090190807111401c0c500d440021640140780c8002d00074808240440c58007030003042a251381d0110700b485208480300b80d00200e5150040100b0005503009200408101820 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602800341 1250 602799091 602799101
    0x605060c0d030501140d0b0a020d091a0f25051201060c05010b031f02090307080304030c0609050316030b1b030c0903060f0403390b060915010f0e0402090d050a0213 72
    0x60006c0c4091b0001140e5100c803c2e55100203800044c40c95400c00c0f00d41920100c50050091250040d00c01c51074001c0e00615031510032400428508001151000f00a0341e4040c0c101c0e00c00401010380d048040741640414140c0380d900c070300900c450740101e00030000031f041c81e44140c00b5a8a581b0400007800542180014950380f0000c4c00580860300c601800e44600c400c0b030310f501030040404020120350500c2c0d5125103036400d56000350001d403058001c4050a00565400206403001040305030700034441d40d00c05890040080d0003901005008250700d0010401158047c0c4810000c0049080519a00c2c01c04080314022507105203946030007406400c0c0040c590b840b0500040b8400da805031562048550840c64400602c480100c882c0a811220041070310203204840b900401075100b1800036440d414180c3c200804038100628035410540c4290810710566441171010003100c40e60706200389100c203800001406800740008803500141004551800c2c4500045c01141c0c984c02510510721100f400281d00d002c1d28 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602801591 1250 602800341 602800379
    0x41a0601020304171207060b1801061b0302100c0201020a23070602030618130611130b0a0e060f0409060f030b0601051b01090b06100c0c050f040605060c0d030501 71
    0x604140820401416031300d540c81400d0440206403801d01541d0f62034480241c024071819215250f403850545d1590804495103d8503034081044501e1031340c5041d000515610b60340c1d1542c1c002121030822201014001c1085090742621580144a034484101c0001c0c001c0d044080c0400000d42103500915141c100c0a4500100f07600b0413202500d440200d880307017800382d8405801c154020078401d28114071a00d11207400380c043d41d0712084540a480d0305c1d082000686c0d0a0407814444c146c42045185d07000e490b89040300c000c40d40100e034456102d034203028068034490310015000350400e20008001d01c1c0d00111200600581d00003440400030140c07200000840c0008a000003081008881c0100e501580100040c1030304207020011009840050041e02d42510110305049500803e00c41c00c1c014685003a40304070b41246090f28103040c0003003d03034480d005810241e10486000d00050031400380ba98945400081c0540006001180e0314003c00045550318003100c0801c100092509002050325003c444002c8115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602802841 1250 602801591 602801593
    0x42d06170109090f020d0311010b0906010f03051b0a0302030a05090106060f14091e0f010206100608090a080c03041e060518010c0b010b180307030f08130b0d0203041a060102 76
    0x1030b0700b804801001403c0c0f8000584001090854140059492040500000e40301ea5544021015040616404e4a401500080c480c410300410048079907406103100b04104d0307062901140503140c500c42d001070840c0302850030400c80381c0013420012040e0560011400340849490030010350b070701c03021403d00300c070280d014080c0011914170b18644200c4c41071411201d4055152401303480c0c04138442c001052400c2d82c00c102e800511b40b07010400010728004240c80e51000c02800600b070a4a0025004448425940074036024028845d01143c48803408120400d54540d101511980d21210501d44c2603030785c3c015109048102ca081606048941c0b06405058110394070340d1100d03410520501c4204104003551080b49041004203000302c1c02040606140d10300030400d0320780a603660300c9007101600c581e03440c20070751b140280d04c4440e040000076031284800d5207140c0c0081c51591194101c00d40e0b441400c600342d0041c40c0349017000c0740d00b5164011550055002c1c034806c103c1c0c2000c081e800e01e40e0401c203079821035003a405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602804091 1250 602802841 602802887
    0x20d0f150c080609094c050604050106120f021b0a050d020f070306380114040e1302011107030b070807021f05090102040503121815070f0305042d06 65
    0x241c07003603030541030300340c0b004410408100441b0030104080001c002da0041b00c48000f280309140a452880b800740c0007030040e00c00380050743c10320034081e111034041001c0807500d55580c28217011000a680c1501d9080c281c4c540000307070604d0040b109a9403041405029a001d0043c007800084440c00000ca044184c15010094511130f45541c40c1c4000420782c9968920705a1031000e450390342002c511140c1b280008035035101c0d070070152080c00014030202c02c68841107203001d806c11003400700c407a105001c1a44030880340b00081960f00e091004035411601110243c04034440da94000c010045900d030f81e1403042d41150b0b00e030b0699650720801240d65610780d556a07800c01141004950403460f10390440d591022302c4200161602e0760310000303c0d140c41d00310700100702c28440214150885822419403641c42c51811a043c2070001ca080e080f41e0524845c1034801030008503000848810940240240c400030444070084a0f0465800009e842c2041e0040d41031003c00c00b1078a001040310f900602c03e00291031001294094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602805341 1250 602804091 602804113
    0x907030b0a15050d030206100b27041e05071d2d0612151503010b091302040303050702010e06040f1e08010c1d0901050904020d0f150c08060909 63
    0x1001c100044440c00b404101c00403e450300e540c44020030442c441e9000b000e0503e048410250f6409858100340f45410081003001741c8100c41500307e030609990700c4010b458205110000600411150482c11140e00546c000d400f2044042d40c0410710500c0a5100d0101e0200350200c03540786803008000c2c2580c020f00e907030400e1070b9600120b800740388004a06860746204a00580000e401c2d6005521110919180e0400300010a040043c07509035074a02130341d60343c92f0805403850724440c41c0030502403c0f0101d080850000015507641544461891103c081150f5845d12400c0c014410350012100780e0104a214002d4a41d0f030900c4002c54040701d0180d18a0440d003400c2c2a8144801c401c1a03c124003503844110780452086000e105981a0480036241c02e20848642d030f4072011400c0703466650714840c07400c5100400580d10345000f502e40c819411100c24a400d5280c1c035007800711f0060036101801c10b034600404044c16000981c0400b011034000e031602d026950b152810000340d54012109041144c2110702e14030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602806591 1250 602805341 602805361
    0x8010209131e050a09031b020109061b02060409051f0f05060702010519180602010501140d03050d0e0709110414090405100908040302120c0a03111305010e010e0907030b 74
    0xd20768103041d4012407104800c0d2880501928004e4504041d0b0780d03900c1e5018400c0581044510801e4413001052109a010540010b030060140c1d00c00c010600800c0c00e41c0d881c0c280038240c61104c24a600400c01ca07102c2d80c9030507001005060865520310300c4036140002c8034480104541d040102d50300104031440075420b040a0200541083d40124180321050114004005004c4807641e80c000c2c0a070f540e40780840b400c2c0c1359210402d03802d0f4000410759141100601854400200084a100c416a141900c9901516007101e40d48100c03030500e0700c1c0350314040060205907004140071003198180c420034010f441d0f108910075250f2081b0710440c0095101101402940e04200c2c0c4560307030050207501510b0085150801c801300303544007420115403d00000605000314581070407107841101c04000103003030003007840d404140084030b01d0101a01070610282c04000c10355801c400720040c1111340109201ca07582d0b038440d180103803c003030180445c0c441609001910865002036900100c4e50000016042c540385c3e80902 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602807841 1250 602806591 602806601
    0xd050d0509010302040b0313210f0c020f031006080601061d0f06040302090c0304020103150323031c0e070923041e050d020601060809031c0209030105070c0501060801020913 76
    0x102c0c10700d5024880040d905488001071032065401c1c1c8402c038002c4d030003490803e400300d400c0c020070018010000c1c801001c669200101802c1d0050504050f191000301e400040d4141005100030f65040c030030000220300c00b0328a40c1249003220106c4003101c600b030362030742020b03503200711000310602c3e2075004e20189412500c0c1c43e10b040a24490081e0407285040d840341c01040b0148001c5480c40200000002031004550f030510404420208204013107000307074115a26a02c44181c0c80c0075811844040140c00c101c811014001c8070301a0a52070a000c001083c4044500090403e400005286000300c4000013142c50960007149000c254800d200c1010501c160320a00c0c8442000d801643c40e4040d5010221a61b1001101490403a0054004040c0d41c25038280003072411005800420410100c0d80038070099100c00002d444d01511030340300c0c04484800d51051040240034481c1c20984c158200002e00940c150856002403080e40210002e01072581c41c0c01c580c0f403d0740300305258550007000b59030940d2000d0340c981c0d101d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602809091 1250 602807841 602807857
    0x10e06070b0a0f0e030703090918060e100f060f0b030103082b02040308040509130804141201240902090f061b0d0e030d030506030d03270803150d050d05 67
    0x800242070f0b0742d000000c0d0440d1922501010316910005030b4605250300700039084028030342c42c10140040c60031460000c1c2025030741c506c000d04558840d0906449070205120110340142d811a041181c03030089040070020305810700c00c0705021002c200e000305204214100700c1e4182d0740c209013118588503c24004074a01c9109806140401c2464090314180c02e459000910045000d185103903211400c28041210480b005801a101c07074820000110025220702d041d607088540501c4071000c8208040007090b1204c442c10817840541d40384c0454030855041c0100b4804c0380540c00d87c5d02d00b0000389c60f415170208920410001c80d510080c1140e6101c3c80d860814000e1511003108214483d00490034030100b46861001c401c9000030602d2403034500100d007401c210b84800145503142c14481400d009000c03030780315506881004101515900078800000c12410380325054403840580035090340312801c2c41007540c1c106a610b98a0028440c805138035a15250040042c0150004050281c400c40c44c00c0644840d445411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602810341 1250 602809091 602809111
    0xf0203040c060809070b030103060615020a1a07030b060d06031a071e0302120a0c02100204030b011701020408070308071a010312031a0301092303070f1502040506030711010b010e06070b 81
    0x2201051201b2084007039030003180305000203e4100d041c210b4440189060034040821540040c266101040426026241d0120b4032612400c00d5150940118090b1480010854228000280c1c005000d01d007940304108490040c07902200b0020b100140020011013038402c04001004903074194040030585480050445041c28014a0000480103400602008660100d21150780d007040120141c1c040c0f028442806440c1400c510f06801c1d81da0710140f400040c040e011784c40c407003c0910305070454254101c8024004070790488200c5a9a0315102e0250781c824042200c600d03074a020070503101c5480c20034084c103981d4800c18500c441c101640e0124001c00c0c841080c1c207000040c002608460f6102840784c803c0c154012008850807200348402d00206034002c4030340114a03402007040c0c90114648022140040d940400592800500c0101c8200680103d401081d4400d600005000220360403401c4200b200c819000244400c900708001503d501e03106030072142d0400002c0190f60001008080c0041d0701c1642c0d15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602811591 1250 602810341 602810353
    0x18020f0f0f0d060312120507050f03040501180516080a020112020706091e0302061b0307110a0203121207020f060601110708031b100209010f0e0301090219090f0203040c060809 77
    0x2500025a00c644e8415954041c45042040182d54481100921902d4034401801103013032a180041051160000c14190311002101003410040d0030341240d00382b240400f20403503c1e01c0190410580350a421480c0110281d05500001905200031031020801901616004110020f01030028007a6201d80070848890360780d103519100003030016106d25064420386040c005031098901d0081d01d840c00c050b0441c00c090603210f5908042a00b014116a88450246842a04080c0713071580a031030b016038403030300960500031458104e901c2503441003e8440c03642a0340c201e403415141c0c010103a03101d0705010300009464002d0000200c19501482044000e82500000c803822290350f03414550031074010b611104035090008c040800c8045003040003203103082c480d040451400d400c2100203007002d40541a00800e1020110040c503071594290700c0741c41d5240d0007500d1800b8009140180509007401c9000340d20308240340c004044550701c6d0754803e40b441603501ca4160617074941005d82c1520018001007021485110b40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602812841 1250 602811591 602811607
    0x91104090305040503011116030e012c1c030c020402030c04030c0311031e0d0f1202030a0608070603020a051b120f0d1407120b0a08070305060118020f0f0f 68
    0x1a1045038a003a00030342d03826440ea41040c0070142503450345601c03410f00d05020b006c2d4100880502106803242545030603ea054100c0d0080140e4a1810803044060a070380c0e140d02800302181205880c0400c2c10040300c560385180301c1000c40403030b41d00002c9005000035408082c00300041c00e01c0c0e40110b800c0000701d10710b6420241c0d03a0f524201c80c84115042161b001a03270401c0e10800341001c00120002d4032000681040000d4403864050365824209034031800c00007004a03c488240c050b22242603000c8249205551741e01c1c3c6030850b940600211302c96241c403407142c010002031040c461710a07101d9101441e65031320f01d01062140c45201141c15001000300502640e0219202100724000400c5c2c0400314244550715020304840110031280d244c60900078a101c000104500c442d0312401082070320781d0f8600000746091005002c50055a07054110185510170700c3d40c044140a4009001740c100c513988181d414022425404440590146c0d2030014880035040c0140400c1c08801d5020f403404050810740c0c00d04006038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602814091 1250 602812841 602812849
    0x2c0d02211b0c19030b06040c1d18040b100906060504120c081e2806021b160305010b0a0308040302010f021002070605090606012a0f060606030c0f02120703030911 71
    0x30310114055040b04003c410010803036805501580407108440800c5005400d2001400c0381488074403221104016140c50b002c29a0707002041100c1c860002044043c0780b90500d05810341141c19501c407000c0e8190f4000005203003030075005076401d0b1040c035030780c40b4106440e148101c4111002000c040b104000303401e401059510042003e90485c3e0300c6404040800350743c40c1400c03030600a640d040c2da00340864039a2031041254041e01e105000c150700c45070050f44e03030214007402e407a500c00844542d2441e0203040d20260035450101128001d13a4000c43c000c00802d02510704004d40601188401450054140001c001640c01582455503060399801503c3c1c0e88244503408000300d80c0050703001c65511740d8800030300c0800360081081e41c2d81b00400382407000e400083d0300004845480c3c8440384a4014401048010800a960f4042050280e01c2101032080b241c60319030240142050803440c0000176030584070307481301510001b4a0b03100c8508443c40b00340741c082c6640b02100038041c451400c0c1c5034801601103004098039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602815341 1250 602814091 602814109
    0x60408010216020a150806011103190e0a120b0622060b0a0f020307020d1104020c01020c01020d0b091003120e10020604020901272c0d02211b0c 63
    0x301496002c0d82d016030510401c080e000b0b054000003480c0091428200e202500200c2a0346c1144090910b1a244404030101740c1c9103100c2c0c41600d0080001120b014800960040c20783c485d5a042150140030441e2501641b0389500b14501d00078119184040100700709040500d00c0550450f004000807084c079005007545002d4502584c80f1100103200050444c6802d13500140288072210184041d515116043e00090b5040c1401803014201c440e44545115442e40c65504860900300a40025512961195803040c001d400600014a1603402d05100300828540b00750003503c511041c0245203402400c64640e045e080580003412400e02000d840200b0306940ca0120500d182d04003a130043c1907034035041c41071051440703040c2c0c4404003005c12484001030440b580c10040c1c1c0d0001144500084410600c00040e030072130f81d401100000303125018201d00d480e41c1d020440403081489030b0200c5625810103055401c401181c480c025180c88010721482407203844007403003145d140040400b01d0303100402d510005003041c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602816591 1250 602815341 602815357
    0x504031704050d08070906050d0e0c040c09090c093c090e07080d0c0f110405090a0c12080d1e050a0c091409041b1a121303090b090604080102 62
    0x9801000028001030380703d07021036400402d6280c01d003840361030035030023418034003031040480050780d21801e110440350401c118031113062200030024840c0758491080600680c01e01c8c056001140c0c2008412148070303014084120449448602c991000507c0350300801d040c805200d5203500c0c09225a1843c103001c6480410b0302c0241c41d00020004410b00c507902201d140c100310303900c02c1c2c110b500103010412032a070f003118001c2102a0044015040d00361507142108000c04c000c0c0c20f0b2580b00e0f01e402c041c002c810307400082d084580341c4290081c606960312447c010504c100c10120061984004109500342a10a508504800001c10078210190501126a00152001203804d203410580c1d80d036540f040c040d841446031008168005180ca046500e080114240c12002480074010300048401007405a42607403080004002c4004460700700440d0440b500700c55070003000c1010781a04404049144024045000c4420591580302c1484451800c02c081c8031a400a080a6a1141091000082d07070f01083c00104140307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602817841 1250 602816591 602816593
    0x315090a1221050705041205071701091a150609010516030f0e0a12081309020c060f0105090f0105090717090a1403191209060207030815040207030210050403170405 72
    0x4038100701c0d40000e02d144080101031880b81800c041c040100c1d0000111429a04074000010601680e401c1c51031400c0055448081d220402e00c400328005103040d40510481441140c074081030440c0100c7c13110030003c007038403220410b403403000203c1110700e4540002c21040c04103061441c00c0c101900c099200444086c1c3e8142c1c089003004620030449a8400503a0030b0307092040b0303558081c0303909010f40c6020f507001003040200944000175880341c0d0b410843c1d6060b40100f00b00c84055643c0ea0f03545000c50f4079000c0656411102e001c40c40d002040a15111091500c22411991812080d0b8031707010402826200190070300d410322102a441c03452013885072203d10302c00d801007030040c0448070a030324240c00d540d4002e07120401103400030700010308105807160001240c81d1451408428003001000c3c4840104003505004082e603200182500801d500034008a200398480c03041c00c501c407100b00003032109901c10041e0040c01600404169210000594840b03500a8081d203000c0011696400208400c403130140c40a80b12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602819091 1250 602817841 602817857
    0x112061b110d02011107060504030e09131e11011206170c1f02100b0f04020d0c090801152303030f0408010509070f0e042103020d0e010b0315090a12 65
    0x706081000b48040030010351008000e00300825010340418000e00c3d000034110350320b07400401c00307061203800c040c4031510005244000a003003802e800302141002e130f038088a819072008102e0f560b0741e800700d0b4003072149500100d900505040c6d5000441304200c446400700700e6544e03584408508071b6010300300c412640309090020038101c109401041401030384170000220048220603003014590740850041d6100da4070100100b001000c01c0c001034854008035084035003081c400b01c0c94040d907043d44e811600d600b00031a207540000c26201c0c10040d00703071824500b400301c0701c5480d040c0400818448513007804c2164803182c0c90032003030580c00b0000b0307055621041d21421141804a03080c06080f000b8891640c004d601900203064991500310030400030180e80c0f084051001810000606000c6041d417450911440071144064801840c40c0180c000d400001000c0c40f1246000040722007502d0510a030040018000d00070400085c0400c482e03d4403a0008100001c04c4c081e419030200010504d54015000905948642c58 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 602820341 1250 602819091 602819117
    0x3080405062d120c03011a030702150c03070806010206070f0e0f06040905063c0613030b010f05090408040b0915070804030611090f1e0306100510050a080112061b 71
    0x1c03d421019000f4580403c0400040190658203840441c545c010344010940340d030303100c01c03003030f810a1420b000180001c2100e104112040340d603580114031440e45031315200308540f5800d00481e07580030210f03030748008182041024004580113403c5c5c10600c0c840141440c3c1210f000d0300120b50960000c1e4040b41440ea191802d005a61a102e00c201d06036030841018020706414202c0030103840f410444a8400d07094045580303040c01d4883c1c104030b40c0c11046001c0c0038050581d40303240000c01201d09115600e00c0300c501c0700d00031a1520700044181d0061381c00011490a25003802c0304480c1c6032388030708802e650140a120000e81000420005003090b1409a1001620f49141d81005000d81c4c82d5108441644c0000308182145991600c0c0300c8035134100c040d00c2c00f00e014903002c208003c4a04400002c47e40c188101c6c01000308400500000c402035450903a103016070140702a00503a032a0081064a40105907500011300c5030a980800500015028187c0410b03410041c0008246441060800f20009440601042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 602821591 1250 602820341 602820367
    0x708060a17030309061f1802041e081212040b090c030d110c010e01050a03050703060810060515041d1b0c0c0f0901060c02010c02031c0203070b0604050103080405062d 73
    0x1e03500c500301c803289806402d801a2441c446d10214021103003d500c249201312140301c2a0340c185c0700608143c038810a404141101d409020200b280319140881c410103030b440782030b080414251010710034443c0051019841e01d84d21041c0c0310700c00411107040d501c1001e62403206683c1c01c0190b01220360603522400f5540744a400c4042c1001003480700d403070602c6844180502a40d0b80001106d402100c18980042c550300e071200e08801504c565440500c50340b090a0741c010650185501203022a8000c50746103a5010700c03800301b0040c5025520601c3d0a17000101c880c503890143c0402d08a40c00b8041d60f10b800c0101c29044000a0b254020034200c11050b84400fa49003514144801c4114481c0c0d01129045010341c074240d0010040c0609880007030401c12550381c000c04644040185a041a10750b0325404004850750030001d54980202000340c51030007010000c55142c1c1454412241660f400c088020b1415040c14140300c0c141d0302030800380e0240b444500c01c0c00307001105050011420300130702c44665070300e101e0b504880c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 602822841 1250 602821591 602821603
    0x4080307090f1208090a0b0a0527030304031502070203070906031103160501110106050a0605071704050306550e0d0c0201092d0902120708060a17030309 67
    0x40c02d6200e2082d10501a20003000c1d400441150311410040e951700c941c2001c1580c0c11801c0c0c0c490204410301043c0380b4005600300001d00540c0708240c1e000c52100000d007450452580841101c0c81d09904104000d001050043c0401c807060f8840080152401501d5400310740f8100c1d180c1e00c0408056a2030b00d0905c10058030b406c2040c641e0304110020088150204c0643ea520a00c0744a1a0306100c1c401850348101e0100390459402840028940d51b402591b41d0000350290f400610110b50781d00030245a80501c80a0006440c256140a4010100756a40501260030390100200d41820020aa40706541c1c00700410b950a2840c0b2414190000c0981500070b203000403582104101ea20364100400040030003400a850300750b0300c0302403600d80da4141c42400141d41010954000610180c018198044040904081c042c0700001c1220f00c0e020043d941c3d84901c089004416074031803070380d510f0004640311a02c10784540e90410001441a400300e03960721081c0c05003440d15240d070344003500080204800a00300b4418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 602824091 1250 602822841 602822849
    0x90201141305011d0a06030c020709060f0501020609120d020703050c190519020f09040611040602010606092312011512050f010e06011820090406060e0a12050a0602030408030709 78
    0x2401c600f44d65910001010404140240c6082550b0351507400c008500c00c011040040c041c900341007210315142d520232040e240380f5001c8c0300d02600c01e05000c0340348017900180311010b404000c403c0700d0902c40c1204404d40a9031001034142c041040603c01806100402d002c0c82c0c00d07445540c0945043c2040505e02141001c0d10041a0030804421214403009601c84000c0440480d208940408007a912031070800018144041c00c2c001640740818080b40d4107030154031801c140d8442e600c840c00041c0d40c0d2018440348c00b2040500c013540114601030844281482c171002030b032100074400045803182d0007503d816050481d5902006040c8a046826014041c0034010185c0d9040800020b1080c03c005807406a9603500c10300c00c5c40020880c7c10114695580c040d0b0150420072803450600455110b040b51a900340d40081909501c40e514007400028264002c03500b5404000010b488441d5091400c048420750361f0503210242c038240188440080010b400e4402144540d00c45c040d21a12424501c90090081c815900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 602825341 1250 602824091 602824127
    0xe060411040b030703030c15020c0d11120901030f0902060f090a0e010506032d07120c2a0302070e0c0322031b020f0d12020d2109020114130501 63
    0x72041c0f0303103000c40d101055030f401d400d240c00140b4861a003c580701d07035404c0482084910204a1300e03080200403031150035005043d0366892a80702800380c03194507410001c100102c408020084400154001c0d040001c41103000c4100181e100c0e0075801080207948a031307404102035100090302d0324080c90319204140c094000c85100580da50b05046c0407891074803003d00140c441241040700102400308614106000807050300004146042001024042c0b540d41d980c2000030904100303110852501c40c024a014030200b16000d501e22035031413420710300c0640c2c0010b020f80440c000c9071804610310442d40c810314054020200c2d010750303034a1f004418400103c6800300c901c800a441400740b81c0865488000019a036800c0100110034428510000300c810000d541802d4100341d05035036560500c00c6101c201d40ca880c2040e02592040e02e02c0c035004480403400c181c08000c0b50303150107405096180345980b1050105106040c0203a0010301805a0841904400c0c114915892007260038420395030f11038a60035070f50902c2c0c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 602826591 1250 602825341 602825351
    0x50d0606090b040303140d0228050306010207061107080609030702030c010207030b150d060c0c020a05040903390c090c03020708070b0a020412060504140a0c1a0702040e06041104 78
    0xc22002070521640c81302404002410391407220440f001400ca808200c01d81d03c00b15030ba18154000c190001d00383d0700c40752448030715210401c3d02c818003880c02c8031b04c0340c2e2050b40600b801d6070030080c0554407900c0c7d80e030305291180300d180408154080100600c90184460b1001191104084e104041c60070100c0a14541150004041000018084050b4940001002c0f10140c0c26101031404180d06110500020f0001c901301000b14921903000740e110080c140c02540e0507090f06880300e00380400c0c2c030040d40c80200060041401c100022107820342100000d0188000d0910500e11100f21044a01417540706031550742013200100110386807441044040070a81c20f0560418120707032580201405480d0000d0302054440d0005000351b00f080c0e048602800468840c000001c105050141c02800d0880d800c5412a4407031100c403101a40005d002d003c0258032207440c00d400c506100081c0041d682180841a004c50140322150059680e4001c2c10180003403140141103e19160a21001c46c4152901650160b4904 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 602827841 1250 602826591 602826599
    0x110307080703171c021909081906020708130602030c011413030318021e090901020405030c01050d06051527060d0e121803070e0705041202060d050106050d060609 71
    0x5119620211800041181e4a800d40b200754620301044c44080603d00c1440000e000b80920004544c1480299043ea24001c4035a2112003542c0d0f01c0141c04d42405246248040e07180018000f6002400c6492251740f210b030400c6400034010a040d00720350802800b6820114503d000d03807a0900c541c000d8040c4229071105142804901062000c1e8801c00103410141c403004440c03000c0c1603205480486640c0030f40403c407070000024451940c11140416188681c1404011800780507050080c0d0b03003036650040281c603800305060019592980519850380c1380c1501c81c08002410b0380c2d806145041d0b481c100411640e1021614918803100c0e8030032841800c8508520840000c0791140300a590744120041000509084c00c0c00156241c030446007000c08002c0400280b00e500c034070011080311074084c416000c03940c207103440348010380c6c00c0c1c40c4c200d581200159040c40100042095940c4240380180080d08540c035000b40e00d0b1a80c0181c4800340c0011010900000b44851106031521030710700208040d02e00315203c1824 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 602829091 1250 602827841 602827853
    0xf22170d140a0513090509070501110606011b05060f06100315050613090e0a030e22050c0f0a0207050f030d1202030c0424080109061809081303110307080703 69
    0x1880c8a85807029011a100306802c1c010070448103940074040984002640d5100c4107000740404075404040e6024141002550394007445407100010381c071a016240c5980e40a004580300c500311100c80089402444140012403c140204c034044c8001e1940300d030aa28000d02884034410b60740090384105440d2098903840301e04815894410b503101103480560702c1d2582c55128080d020260840c2c1c00c528682408418110400108024042d00c69114024034001d130f40c040050510703107009002e4403100b0780ca41742030964002d5840741e60300111510800c0e0904c0e085030141119500900f50907005640009000d0149203816046d020414108400502d90703010b032818020440c200300305440b850070b5000f00c046a910142c41c400c4c1c80241941100c4c280c001071092502d031108284424a070000310750148000320382102e5038003442d015100e11f5205014000e42d40c1d40e41400800f07480300d0503510086d0034440c005407034000c554200010741c010100400404c1c00802054208640d550040560343d004150410010b80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 602830341 1250 602829091 602829107
    0xf1401050d0906020c070f03060c0302030c18011809241412011b0f080106021b06030703060b030a020702120a020f010809030412210c05060c0f22170d 66
    0x5076000452040418500640030f4020010240b08038011558046503444602680c44100c0f80500801d02c07040160800543c200d110960360641e03641000c12003c040324110b055001908e42042c58201090290390f01400c00185050b04a0708606231030b101d0600c41c00140c080044001c2d0390351314a40c26020b00e0480a00401195940240d0080c1c86112401c0c3c0c180300c0c20741c030500500071101c000e82c80c40d2080c12002050904030702e40341000304a107c5d0003c50814800507003045807803030040c1080d4455006900704901c80d04001c00c83e100f01500c1c0d80001c180b040541c40170314000c2440d21405038440120344100300e81041c00b0700c80000d050b0b005080e001c0c0540d868000c604004502805c01d407409496101e250360540c81290006204a482c1c03403400d004014138903d44801301800c0203916a10408800021529030f80201c0000d40258000700214215140880c0188954000401d940e4945002d03a20b0210b04c0e1840c1c804e200302c0c2c21409020130018261030f080801007842420700600090903250002400e151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 602831591 1250 602830341 602830357
    0xe0d050913020c03030106020a0209011d060105030a0f06030615090b06030a1d010e0c0406050303030403081501023915070803040f020d060c1404080c09130b0c040f140105 75
    0x440508010307001c00154115003024202109483e900d6860b08000b9554400480b4100d00a40041000090921415030403c00c100c071280300b0401203444030303001180c00ba0405031040c20005d81d06c82c1162155542c9215240003107108100c003051181c03a2010424980c1d8050380a240b00900300310b02e42d042075a8076012250b0040c08000001403010902071500b16907500d030b00c01c3c0100f66103440900c00e41c0e441c000800700c1d24921704503414016140c445061684078001134070010081500840400d18040c50026170b00c0525a040c4103c0b00e4810310a4160050b40301c804091038201300074004c12408194036a18601d80c114070582d52600d00410080b0348001c2441004006416040c001c0301103010820369654070403110b40c0003001d1103600c09181c1040c20040c080072055801040110210100e00c01c2803400360360032201c109010300740c8280b203281480038003240200b1510030071108038044030009204003446030081c1100b0440ea6121030929081038541d131615000580e446a0f0312038010701c140c0c0e0001c121000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 602832841 1250 602831591 602831599
    0x1050d0c050d03091a04081c0c05100f05060111030904420503032106040207061a03010e010b0d030804080c0105010f0f0b04121211030406020f0613020f10020304180509010e0d0509 79
    0x230140750502100c0c1100300341401803040c01000c00c4040f040469801101c084034580390704102c5520f41400540b030b8542070544400142d002841a03006514081d80422011f02c1d1244041150700c01250072170001c8400f460444006480142c008c4024070011011a00070f8003043c2c00441c90021100070265404803500b8911218202002c00264151a540c0542c2d100b20b82c01041070080205c441c40181c513214030029068003079803802410b404044014054054000c001400c00c00005000340c0b4101e5080d40d00600171b07102c80604100180b4007038424030071140280681c1e1890351446007411a042030070700ba2580700040030701044c0414404022941c07000c0600380d5014105520100c141402a03031b21104c6080c0744001400003203000116142c010503c40881055101510126a2036000120200c1e08280000c4e42041b4044c81c0340780541008150050314412074011039003050303652411751a849095542d00f200046d211003d105000d502401685008049500940f41c00b1031401001070450041100302813103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 602834091 1250 602832841 602832883
    0x1107051c0b07140417060604140604090215030406060f0b07051b0102011d07092018030a050a051b030d121a03060a021803070b0301050d0c050d03091a0408 68
    0xc001d00400f00c80a100c1407040d4099180e6680c3d00c00045003c01441c01c03032140c2d0040200044071450300380720b01c4183c0208910031a00c40d40304d04040c0001060044012600301000b0745001e0b08580600e0003640c41640325800c04241d50b4100540d00240a40c80c1e404000b034004244030040000f0404118120400708045501095042c03a01c0100d000d4041c081d101d01d65040c0011403281004004281002031300c1840c00c05010b00c00a0814000c804024050503000e589000c0c07100201107000d02c66034241c200c50040c12140214042e460340307030904000e000304850f00e80c03002020b18003150009040c050b04580407000703000807204003440904a400d054601a07852a560140c244400054140002015201604071130f424a00341c03080c00000c2d84601c55001c4076003941d10485009250000e100e00c10f50312101c50080c02c5174a03201c28482d182034074840450305400b01200104030b5880e00c038451009107021b40c2e911003000d860540340031310000c002007440001404c100418840e801c00000d60f0411210071000b4120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 602835341 1250 602834091 602834101
    0x1202060910090c120b0702010e03070203071208130b030f0c0901120c140a05090307050a030f201201090b07030e0d0e06070b1311090f04030503090a080301061107051c0b 74
    0x20044010b800400c44c10f921000f0300014428100101c0384165002c0d0020003060100ca07113500d9490042110003507060740440340a100760880c6c00c8800400354881c0110030b013806540030200150a0b410382213044441c2011041080c0803041c03502081d0424220345203203141c4002040000e062a802e00056412980c0f20080d9050700380c49000310080284600c4070890315a0980d2000070415846001c40d54424441e450b00030070140f82070700c02101140c0e07200420102129566a5444080c0c0507000369000080d02c01500310180d466590380c1c48030910201000007203121035450802c031342180c080c0a03403082601d44400c900d0710103400a00110a140302e420800d214070030030000105584201d000003030008041c0c000b031002c020501c0700002040c91251111402441c2604188161000308840c000128103411011501290141c401550812000c03400c2e84c2d03000c0501c3e00c40342d240d940280c2c8820f0008403180409822480c2c00d000d200082c0400300d0300c01c048492816500384108448080c00f0301038441e0480411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 602836591 1250 602835341 602835353
    0x9040c0305060709080640080f03061003153303060602060901020a02070e061c05060118050105060306060901270306050106050307081504230103120206091009 70
    0x4603405002c032002860044002010104103101d4103503144214400314000c0480f04800b208800c01b91f00300c1442c0300c0c10594101029074110401c01d00400c2c094a1080b000c50180401421200107810038642d60f810320b941800804080411a441010710340800001c40100c081c1d188011035011402107201c05640c0e030b804107d01c0e64000008040084600460515203816400c10411546142c007500c0807a510544900d00741e00c124107020b030044c2c002c0d1005000e0031880b0420650016400b6115010002c584070240624412100d001d4a075030b8405401002050500395034141c1c0544d01010900541d45488041201d03400050b1041b442548003040b007010603446441c0101034040030340783c04035900040030041c010040c01e600040c1c80c0d40d4100400030030914003840c210f0340180d000390303502c080965407070710900d41003401010035030360164030350401c4418540d00c100444800d1101c04913003045035140d4506500070b412b6203020a0709540040741005504c44001c10801d412551b0b0b280040380490300ba24041c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 602837841 1250 602836591 602836613
    0x622021312050d11030a09030b100902030f0609070e0a230a0e0f060103050f040f0606080d27030c1e031a160e150d14041223090904 58
    0x1c0009070081145040c0312001519210f865159150001c6588a651041d5201d104554645001c034640100400008401e5100142e00440c007415418480f0345504c918030a907441698120010400030060012600d01141c0203504030849040c8050124242c0e40482c40c1318090740f05e00240c1451a0800d03030350484140201c2d814801c0002d02820a0075260405c041c840c0000f40d60316101e110000c000110654080c0c030803a070090303841c2d2074904000c1c0d45964420070b80750b5000d64110b411507224a03001071034600801c02104401600c2d152604070303584811441813017541510700c00e000005a14001c00114281c1286103003603070603c0c0c480c0c21500100c3c0a050a507410242d100600f00c61036603d04102d0401d0698409004955441c82d20824402d40c3c00c00321421050080055801410303a0035662418913058001c0911000000c0086800d120071012010580000c99082e503801e05c42044070405982c0c0003104111903402c0a5203001529403c1d07030241800d0082c2904a4007130420b04002c9030602c0a0032070382d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 602839091 1250 602837841 602837849
    0xa18020306030c120f07060309150903020c1003060611030703050f03180318040510060819091403030f1015030c0302130611010612080f07021809031206220213 70
    0x5541d40d201302414140f95121009250380c4c409008100c8046200c510074010740c0102c0b90007410352600110781908040040c64840b5040b01584580c80361070030b9a4580c4403240004400f10349000807000d01e461000703040c040a444102e40d080e0010894400001d80181c140c9000d500340c0206151a03640c3c01525030408103a03c03201042c80d01c0301088030811004104c4586200b542b05032018401c81c0c59400885000c60341c01e0203031102160b54040090309030361800544d0400c40d01d1903070021641c4445500c945004840200d07683c2d00d41d810000802c281c040130341035140d4000612003845d0700790f1880d140900c134441350707c1c6030850201505d81800103c07151103601680c0d1003040b0510b410b500280d90b50000741c44181d009501c451154203040d80040d0180c009462260b03000e801490181c0707400c028580e0003410307504c80b02040768414141c0e031031416950340d00700c0258805e03050a030046540d0007031800303520150600142014850310012034200801d0022103510440c0080d000c0c000350b102c860008d101d003048941d0740c01c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 602840341 1250 602839091 602839099
    0x141c0503161e060b1005090108012d0f05030d050a08150a0314010b01090f0605030105040905010e07080a031b080904110c01090c0302040f050c04230913110a18020306030c 75
    0xa4400705000d9650302041118400b11060319a013401c8540c140c9a07406603071107150104c9c0e00f8500421154a030503c00c20300e990b2080020707040c8054021940c000c9010380d13422081c552002100d00744040d04080082d8014003206081480c2821481000100280f10081c00c080c0b510b050030701132981507100c01c100b920117076a00c920745070061001c0f10a554000c1c03880e82c00d082c0c0052110720000500c500180c050b0300641c0d0301c65030341340e140d68200414040a0301007010f08440c2990b0b02c4240c041180400e0201a0180c81355002230702e202d0089040c0140040c2c842e030640f500000c8042c0507840003581c01401c40f451010305480c085a44051043c1003081070240d0f4031040229420051342c1b000704041e407108001a41d20841d4100001b6200c8480e41c3c088401c1201c0b002c810580400040c0100c90401200701070005c018034100740222054008200080c0c2c0950700c4074407008428110400b00120801c3c0580106c20544000d40c5440c5011240d07030f0029082c00300354162590000100d4034640b030501003a410500090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 602841591 1250 602840341 602840393
    0xc03080f07020405070201050f0a150b160c0f030b09160306181217100e0106121104060504051305160302070501091a07020d0302040807060503061801141c050316 71
    0xc060b010300009c80d0304400907401080041c9404416104002c03c0c42d01c2c1e4400c84052900f00007818842d81c1c4a20b90030030b503840380c0144440c0001c107000c4001007d0080c82d0400c188080c03652420038440300002e440d00c49a500b11911a0783c0b682a0011240c040b02e1300300901003512800e5013480b1030f108882d14406805034074108140050707150481d0031403911951034600c0034843d5694180c28000d0f51102e0082e030344403d210f0b100412a00307104a00d10b2030418268103002425031210b480044155106602c2140892801704040141e4940000c02e5065034480f864180100d180c44d20b1003018590381e01002d001070541c0441ca200c00d0040075400b0303106151380082c0c002015120042000e4801c10f048a60308014030900542c046090b100340291400c8422040c010b040c2d0741d0811000fa119034000a11a81d0030003030300780c3d028046080e64040140240900591410521242c5090101d010b000d00003c03101c0e034640c409803c0014038000100e44841c001e85017002903078a00c3d880d001d404591a02070003002c1e48114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 602842841 1250 602841591 602841601
    0x3010603031d04062607150915020102340c031505011e05012a110306151f031b020105010806160c030e0303130306050a0f0204030c03080f07020405 65
    0x1c460352114040e80c2200c40c12500042c4100000e03609607004403c0002c0c2001c0840c55030104800b01c08425030a85c00c00d80e9851522146014680e040c06000800050540101009602246d000344245903081d44000d614240101c0e490590100120031440380c0c120750304c00074a01c0385a1540b110880907500005d9000e607156241800c00c511210b00c4c099001281c0b07031800000e00140c002d01d40e0841c2c0d00e2901c6004180078174100041d00d458114a80d4207210b540404449080040403541c003811481c402c110030304115001005152428400030070003510940525441d040c1a940c210700303a0640c18038410010031080003c1d20032030140240d0144080510402842141c5603501900094140c0340d0800c1120b14695690401c43c80d1313402074070f400e000800d0300002e4103004640f00e2808034120702c10140c2124501100d40304403c241c8903155105075159603031a41406400e10503805054518010300c401507007494290780360380040d490184801030110700002105110f0254500c280c801650700103008000300d1801c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 602844091 1250 602842841 602842847
    0x10b0a030809090132131803020f01020406050904020705010204080109240b010806010c030e06040b0d0f02030928020a09050a0f0e030301140105040305060a140903091005070609020301060303 84
    0x441c10070b491041e84180000705002140802a01d64086041183d04850074180041e01c055480f1103400354002c50081c59134039402040f4010401141040941100c0513141c5080007410030394001101d2044c0d900410081080582c0881a6140c4150498005030707030784682d20b061402807241e540308078150350900d1519010300008000c03042a40c204a1020340c030742d620042c402000c492040c465180460308044c0402c0c01e95129804440e01c4512a0030071104066201001441c0f5400a510041c00090000740c641c900900d14091210100741841007542981441003415484600201c001006150040d2081182100012840c0d050a4024240291240d11502404041c0c87c0c21100c01c031001342460580303041455144203400c4403900d0103000d10b007140d0902c40c0410300303442c5000d500390400a0511002c40850340c18004c590082c640c490f8002504410403482c080a03500080c004c941c5900305000144144e294035068151400082c50402d6580c5884d180c2140107001405002e9050342c0f90080c04020590 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 602845341 1250 602844091 602844097
    0x5250e220b1008040b0103030c050a050f0f150c03060904170307050405010f0f0c15090506090d0219120327050601030b01270f0902030312011a2802010b0a0308 70
    0x20a5a11922803002290706880c0b03c04180d4000707000b12500300c01000424490400920309521810075141126002d44500c0e10f00044110070301e51035040486c0100c00d0410070041c0207032001e035181c8040610b1500c002c001703045000040c80280211402c0b8001400c000a01f100c542c1000a4280d1154490608100c000d280d80c2050103001c0c0840c24002c0e03006080d5019030180f0102c01030f40d58800d010120b07a275403108450345018150290380783c1c50380d0380040007403010305c0420301c0381000c180289096200b42200914120f851f2000341d10905111020001060300d083d43c500b1600b10380d05001c2a90814924404201000c28401d0030014a00e900850104034022420604a90180c041e041d0f269880300f50310015035400c8242e095581604e03000b074130f80300c00c101d030032150340310326440710008143c0c0e020b80200341180e016500e4090304100782401030000305480c00340b00c895440c001104d1401d08440110240c0c1703221082d071440301400d102e8080030840744d10075085180759140c060000c980e0a1b40d00c1c0740194190b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 602846591 1250 602845341 602845361
    0x10804060b03150c0712050f09010e0f060703170601030e0d08100b04060c0312050c07060902030a02220c0c081b160603021e0c070608040305070c030c0905250e22 71
    0x20958401140980c40b42c415120523200e001c0003580703089540340c010344400d101d540c0e040c0c0c0c00175004024600325541d240042c20340d02d4001c0d22250040d040d200030284185070001c0ca140d05251904800031055040080c5d4000d01400d10b04059041e42c84c3c006440d0224a40ca600550304e10f000001c0118940758001441040c0303c0c0300e070722151a6006500c845c0401c2e200200c035013140d0110700303000e02404186640c1003118010300250998460b203159130082620703900088a204506061780030f00a0380d1140d90301c90f0b603a081a035887c1c001d041d208181d803508428071442c9280f5a4450f426040e00c981c0440c01c1c400703100c0b560046502d090190f540c4480c080c000e500040e110f0591170100075000c3c0d10404030030088480b40581d10001d854010305181c0c0998048801a005500300502030105d0800100322040c4c12020354000c50030004528034055404050300e00040484084103102e6000b003e4100801084c5c1642042c5401e09421400d0487d0104451800440a100b03c2112440f0f40022000603a0300100d011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 602847841 1250 602846591 602846603
    0xf090111010605360403020102090a081501090209180414070602031918030f0b041112060712020d05041109102304062409080c010804060b03150c07 65
    0x2428000306280c0c2225520b105903504043d55031100c111307a840000e012001c035950b4001c407180030f4552100030b20540804a9048004d81c9d4002142d1302c052401e104c109004012001c010413010700d00882162071040706100d00078003990042407071980c40d9a041c840421104141028000518250a1281034a41c3c94100d0b650b21703029403000490107034400301c21503040d1410825a1001c0201126084480c0e54911880a01081c0d210b04003000059480101c1c850031802032070303501a01d040c02e0414020424442071080d10580c1e80c106003c4541d036001c5120b070b9018819041811150100d10a002d0181c4500c81d4901e448624007410001001107180d0b098101001c15144808207036544441c4040054403030140c0c804d0310b041c0e13001c96180c0c3c1061205110000501802c0801d02981e24a803070f032960702c3c1d0150704d1303103501e42d02c0c040e0740c40560b500401c0500140a0000200405400a000a01601c0025101500305c07502c1e05071152094a0801400311684040960007046190402e400c2c101500228011544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 602849091 1250 602847841 602847857
    0x11d2a040221010b04032109080a051c0822111c050613020303030a050421120b041107021504030c03050d0e030604030f0c0c09020406110106050420030c0f0f0901 71
    0xc0540d021748081d40c0d0301c002c80007521040b9118500300b480452082e81c1c10407a9600c0049a494801d010b4550100d210314001c10a8600c00762070f5a072004c5c81580c6020802202004100c9031048803400c0c2001503803003464040000721a8100b07004e82c0c10625425075000244813080e1084a0b4150700d00305143d074050404e945040e100ca00d412030030460032081c040c0d80b40d4800c2c00460030041d066403009810920501660310080d05245802d400d1441200116001c250402e40d808a41900c038021f0310030840049404000908940501601034080d16002a01681c08480c03104000e074070754012200955004584195046e40d681f0f4220f603662a4850b100300098140fa02040301c0703040004407503018070750513203070750343c101e0f00c11101203520601c041c90130780380100000400220b0f4805840141f014203116901c1036034002c0d0901409007590300702d5000d80d004903d000318810416602401f405071030401030040940d0790712980c02c1e856045c0512168201c00040020b003804420f00d291001b071140c1c504c00c2c0c8131424 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 602850341 1250 602849091 602849099
    0x20408101a09040b1302100305062103192c030706031e02030a14010f0503070e1506280302070215190302030703020c06010f050102011d2a04022101 65
    0x9590101c80c81074000881c003000c50000344191001c0c640c88000d0201e42000000d4580004400d50302c03c01d9503202081c0ea40d002c0c8051404d10b030002910b00410400039202900d12a02621b58038803809282000b1344400d20307030550380c1070700c64414854006041f04010303007524030540e50b0080c03c0702d640a05511078842c0010000707605019004040794100b10032240a20b0b0324000c000040650720052036036141a60721a6480300418900000234041c01c0c01019082000c0d0510003454900500ca40040481c000d24038100080c81c02c80005004d0744160580300c20343c4035110501c01c0709420741c3c3c0310441031040ca07440b4203141d81d241d0315501800d541402251b40062008034a9401249449072500741440210540c80328580203000c0c2d0029608101c140c640185000750ba40551820440281c1084081d900300803c00c104940c0d090048580c240403001c4084030b82e0b121030007040d564200e100c1e42c00c1c071002ca40e0310150340e0a0500404090740004d01900a5586803a100034105044040101c80e0148003d048000300f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 602851591 1250 602850341 602850371
    0xb0f280305100522060207060b060c0d11030702030613030903020603040803060f040207031719060e16090518090325050f071805060409020337030c060c0e0402040810 73
    0x600d80350001300c9440c28200c0070340c07a00e0707019610260040d103905444150700300841d15104020500e000f41c15024041c001003281e00107041a2040650380443d074000c0c003283d405a500441e4003500900030001c40000f0200e285816a090f40e80340e03002039800f100100410003441350440007580b04080031030310420946000400c0000301d000c0c000000d40081c1c0d01007840c6884895419110340c204d84900b08940d0b2100300d0b0018203003502d5071500001c80308011003013030005000004500c4100c01031a82170105a80b81400d011601810020104a15000d0828003003040b0920030f104132007400002c1c0e1030001010940480d100c0c08001e1000c011200c5105540070a0f40a00f40494444141d8a040401c03803241909654400094074010b000c0550069a910380701c00141d030204402e580ca407101e0b803403483c1041218071041c0803003071401d052540440b03000c0c4040400030b54020b550f1302c00701d980080001002c42d440c80c8101c40200a248096422603c00107010441301c500064014240e0b120720300a0200400e844070780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 602852841 1250 602851591 602851621
    0xc08010e03041d1503011109030123061513171606021c0909060806010e10050112050901292b06020a170403030203060906040b0f2803051005 62
    0x300001c5414002c404100d83c01031450704080c07400105020881c440c4006421505403114840c070a4200203400c5c0031500303080c014a04140741640c1003010b540803110b106920150020001403042103407915900c900000c00302a920710b041e414110f00e4501d6110246500c11620200840e0080d104102402543c0d906416a407025280e96501800035000c001110840e05441c0310381070000e0040a08012400c10b0b883d11640b0014140d1100516003540740c03071003c0c01c541101901000c1d803040e00b000c0c14132003640c10103000b8000008803035000038a43e9840780035600610603084241c40d030711101c841d259030402d8844402074078000c00315070888150715410303072a0386411318a02c0d40500355048804920045807156001d85100301007414508224030000181000d034907000c950480c0403940c08801e0080c81e080c610074059000c030041c0c80c00c02c9002218000101000f10f45049a407040f2034005039041840b906440b0301551240515110070303a0744d105e203032040c0c540511143e914401464074000a8000c9000052 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 602854091 1250 602852841 602852849
    0x303040b12131407140f0d02011b0503190e0a031e1707050a030201151415041809050c2d0619110c010201051e090c09130501202d070c08010e0304 64
    0x1f1280b2041d029801910101440d403403604c0440c002c5050000422401d00043c41e2020701c0181d07034864413095401c007074605a006001c180c050740718000c0a20008a07490145206035401000710b4440781290710300f0000100b0b0b1310302214901580400c1c03100c100700000030803d024510a4001748041d40302040480202026407003682100e00802d981000581000949609101d5090b48142d02c0d1588500740a902084a000c0321039116581c0c0080c54180001840402e002c00070484407018814079402d0241c0450b100c4c0c00d2250201c2843c5a8000350f00c1c1e0301e183c11507039044442500d81c04150003000300038066010030445205280103440d40714040303600c1889001d00c2031021001e002e80c1078816584e190a00b80f0001c1c0418043c0c810ba00c5100d41c40c0d500c3c000780920902400020501c4128185051801c0d40c3c6102402003d44d20f1601720001409050020303901151035a0509441074040502c40d03e154424800841106500008840091148206002003a030794520f00a00000b0400b9100d07940d20702c12807003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 602855341 1250 602854091 602854099
    0x30c12030b0f0d17032a04061d0103060906060e010809121b07050307151101051b1c0204091b0806010f0c030e2d0303040b12131407140f 60
    0x548003143e15007032962203000d0340540b80e001c2c2c680a15020345202503005481203031a0458150030403007071403100c902ca4000c440311401c1842c1481d1031b0400143c08c1e585038612101c1006144208018140d00c203900100040424000500c4010340e0b40708040c0c070b041100c20700d05000a023000005000c2c5000002c0c251011803000061a2900080c1c0c50400c15410401043d83c1880c090303500001056501004480090301070041070f00140d4010301406440280700c1508044141d0412040100e001140001640b650b200424960341e04c0844010148007c0c201c07800211100744007045c0030500c1052a4040c81c03200a00d440e0201c0f4860000105490250003191894002038858211000140c07240d00c00d9241c407442801c03c8240ca6888000003010511120200742c850030f200710b03030b20702e401c460b04011012605055000c1c40c680b03818042034004a114441a01400340040800314404141c920211141e0300c2e08103800c2c00c1141d80800310340707450780c20a2058043e21408030010164070301d045a641160310500070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 602856591 1250 602855341 602855359
    0x3060102190515060a080f07090e0a0507030b13050715090803070b0a0906021c090309050a080a1b08060118050a0605010507142406040c0507050607030203130c03030c12030b 76
    0xc0c1c2d10f07421000c2c010819500005100000900300c0400c0110b08060382d10b581c054403070345040491203c00c95600f120302135480c1e40070b41d08100200340c020803a64282d030b0308601d0902403559040030b9141c2c00c001c20135008005100711a00040c10116030380030101948810760b6001419541c1e036032901c0e41c0b40501880948003200c40004945000b1042d03000c0010355106090150401140c5e200a10310140c4140d200e4051036215503080d4101580180c19001510003111041c200505003140070380c0d5041c031003c1c000c0015180800d001d130b1400c03240e040d4100a0148000b2240ba568491f900e444001aa61800080b130310309001c003048425884c0c0c00b0f1041600d40695900d81490300300d80710f00b1140c590504086590b8080d0079423604060328070300c00b0181d41558204a090b058141501880b04039082ca803003513801c01000b40000800224007160094106c0c0182c43c0150303d0340c0b80c0c5130000b00d8601003000000c0c255004c03418000100341e0006810b011003800780c6003195401071070403801c0c0d003950030680c20260321880b24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 602857841 1250 602856591 602856613
    0x50d1e030504020a09090506060901050a121e0b07020a05011103060f040c2106031502180904060b1f11060c0406030e1e0a02030714030709090302190602030601021905 73
    0x40e41c0850380c000c0c0000c1c010201d1598500c806005c075000c00000f0745480d00304004000490030b001008500400c41554448074203031412a43c3c0080f010301c1c3d280100202c401000c000c0c9403004c00304000c40b142c0d400c000304070403a060103c0c01075a07503a000300d0100c40550030180e0b031000040440080d07a11824014001400760728289082100501d0711a04010602003000c50400190340c001c001c24039511001d0100040030f906504107583c09110803540400c045004011004080703403072501600c05000c06a420707840640f607501d07185018158811510b0780001264052420110002146005100c215180c681c1007012200302d854070b581c42180c039a040c405080004200d80d901c664403081d0a00003110503580c003e0f0101001d58201c440c1080161282e0f4006501202549818445000100540810b26800301d4010000c2510b0380740d00c5c07080040060b559030000007850300038030058041d6481c0030000c0c1040005803400100139001950183c0c0184140c005c180c00101080040b4078000d070f081030003450740c1200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 602859091 1250 602857841 602857847
    0x100903020d12020d05011710060f0506160f03021b0f0d020909150907050108010819150e031612050a0507080f0f040803091305010b030f181603050d1e 66
    0x1901910b1860590130080b41425181900c03890340030700304503414a02d103a0504401a49800c0500d5487c0c0025458001c0070040410700d00740302d104462007035601e80c1c2c0320300d07100f40d06030151500c03001d01900341400b507602c003410183e000c5036680e101c100740003c8420100c40340c001d12521402c0d051030382c1d40102d030000c070032405803400e005032035407100c4154104d446107480300c640501c1041e0165030100039a03106440501403503030403800950142080000509910303100c40304050b440f186c02c041c05040e80400c0d100204000d03600d508010405690390003100e0b41d43c0c40c0c00d44c40300c000b4407581f401503480004004003054080d02c41c00450320401801c0e5540350134000181c4070404103034005048130081c80320800c0341310200180c40e4054001806140302450711011840c0c14000c010b40000620840030340f1700001400300c141d641065a8000f031514441e01c2c41680c07070105850148a800d003c0e8907661155980202d00c03400324000c6c001c240c81c03041058501034002c940e02a1500d02d10341c001e07140045c1d00700040302c6d44184 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 602860341 1250 602859091 602859107
    0xa140102160809030105010e0603071701180308060405010807051e030a0f0c0617100603020d0b060c07050111060c0403170702100504080f0703030914042c100903020d 73
    0x540400140740c6000441c24801804a011080310700a9010406101074a001c1c45064010448001601560701e0442c0001c0d85818142c000c400d200d01050303005081c03d000951025143c82c00c6016190a00819800e000e031075842c0c00c880c1d040c459070034000085032106010a2080032075030050002003618400460a03904402004107098061044a2220002c9540c039154540c00350b002d0703842c010180b0700b4100b008080c80d00015100d03050004003018001c604002c501001c044035071070700e001601c40710011209000740c201c004002c0d60014020442e11341d04000031842c41d00300d6a09072100303140e44030190201505d60780c048680888051b400d00c01040491350340b01a03010904100e20300c142c13802c102540001d07112165501e0101c0007c0c004501400014402c1061804080c203070030041210900d1940d008140403c980039800c240084841464a170b9140c40e00300c91803a0322181401c2c0030140320310104880241040c40800f045110340543c007194400c051003492074982e090b901900e034261308400305459101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 602861591 1250 602860341 602860373
    0x60606070f050604030e0a09060501050d0e0c0919150e0c090d0512031506091e01230706060605040f031e080a020c010206160207090c020f030c0703020414090a 70
    0x1480181d0340c8009841845420b20440c8a5100d22511038110018000e484e0407a811000e1910714060042c09160313004400c2e94031100c1c507a180480c2c035a001440b05400e04041070b14081c1c1002961080c015107501c00112081c41840d01c2c0740030000c04801c826505c1161003503115034000803182d4004140010030420040180400161a800680880b40d0302c01d89060300f00d105000515802000b840350340e06540c0d051b5043c0940440e80c1c00c0c100008000000c40d0ba040b00102840140d1252800965a034003e0305122014200004090b00080d0060708110540e404400c046510900d001d1010602c1070041e0300744d44c2070b034503820f0b607000000c0d08507900c2041880d16500d98200b5619161116800110707158003c7c0904112070740540003108100002a162010103059800750501c0041048012a40040c124084403c42e400110701c0030441c01d020b078180711201e400301e407013030000140c2020040e41c0002e940341100d00c2a1810001d40c201c1392210200d00d00107491402d1036802c41740306880414030740c0f0042d0040f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 602862841 1250 602861591 602861603
    0x1b030702150405100f0203030a050a060803162a170102090a033c03180302060a090614070816030909020307120f0e060402100306090c08151206060607 66
    0x20000d400050407250300320654980784000140038440760401100d00e00c550800e44c10502d00f503444440c030181d22400020150074031076660f080024071881c620b8101d40d0003009040d064a60303030511288e642044208686050710801c18031303440b8040b2050280291440540781b00307400c011b0a4105141c401c1c92824a5820400a42d0280020200c1d5a1940e0140c001940301d0302c8100034120a1407030003580e00850040d0700c0307924442c408009034140031504114884942c1450712060b4041081c00e440340c040d80d682c20181d0081c1d0046004440700760400443c4060394403035100c9400701450191070000a1003041001002da4405000e009030030400305007648480340c420b0505200c1180c89009400480c0c004980c9400090350707488801002c90b0b804e100325200b41d41c500c40d06202804580c4c4800c0c0c3e0312100944006d010310301c54445105020b200381e20410140103032110500022160502c0103113108800d4824100d000050000400c5615283c002c0310746446968002d40655030b40d40c3d0800c100b54011600503121 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 602864091 1250 602862841 602862847
    0xb12010c02010614102003032d0606031b0c031602180702030403080a02010e1506150705070302010c02060705010f090c0801052802040911040e18190f02090411040e070b1b03 76
    0x12040144059803049181c18032602e14a007041a0600c8542c501401d81c91020b04d122083c0070484d20382f003003200c0d440306205000d03414600b00601400032901c00d200300c03e4564000070800e44160702d5210181070380f0074002c46468405003021981150f0000c8107565100c0940e01c20402000000c0344034024180c91001c40c0000107203121540d50503410004400d002744212401502040700c90310f4044254500e24a40508181c146481681c0310740e603444440c08064103101e0560600001c6541300c030100c1d42032590001c000e00c09144901060005018140d070202c81440d41d010001c21090f0341445460711413a44c03034480c01e91b200400c03d11034108002c14001a07a40039020800410005481e0103200e01e842090348069941d030345800c40c0320030394086c050b180c20b00c507820302003200030481000a204c021340500856406450300003441d1485016540200c0250841c125004000600c2201071040d80030500a0344e081c0b11803429032800c1902c0d80100d0040c00c0d032a90b800c0c019880d14903a11070003110100074003811a45 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 602865341 1250 602864091 602864147
    0x9150a06080f210405010203040b0c1612051c050304060e0f070b03150a1a0d140a0203040b07050301150e040603060509031b0102030103110409060b12010c0201061410 73
    0x401c051450b82d8854541c2d00084440300701c40c00140301e88921029507000642000d043c040000d407070703201d203104180440ca40031540c910183d40c02e2004125002e01400399030000707685c07400c01d00304103001c100003941e050142100086546281c0c51031385003000440d80c0c910b840c540c0c903591400024154240301c00b25500c5656510f410b01c040401820002d0000d44113070300c0c1caa02d80418074125604150758107034040c4076911000c11600410300e505101d01400300010302c0c0c403004c001e180e002c003c140004501d800c3c0c0384010f041c8121010b00d5401140124010103001d03030941d541c9201620103100a1003100c441c0c203240480801818131440084640f403100800115015130751f5140c281c2a6442a070324000f00c1d81000900a820040c103106200c900800d0710000d50a561440d08c4190440005600b001d015a8840002c03c04100c0264000c0b0b000d458014041800141e08603800341c020000d0140030400b640c40d0400101e0360603400502521031441c0180a50800b44000c01d04035440350f6101d42c01c620311a03c1080f844 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 602866591 1250 602865341 602865343
    0x1406030907090f060e090c180c0906040b072009010504020d18030306210b130f02040f0614040902090612070e010303050a03050115021e0a050703060e1509150a0608 72
    0x2490003180c42101150450174080d14811803840a000d13080c265000c4003100d00709484458000c06800d182452101180da641c02d54140b042c42005c0b0300f5984a4400180828000481c03805090301a000b22a4000018505400c2e0b4080c110022200c0341d1005501e40100200d20307007900204054150040d01060301211541000e4000b10102002c41c007203520343c4401d0140c81c1c5160444230000c029000b40da00070402640b00c8c0c104500000e0304005809426031071341000d000c1c8891805605660151080011400e400c0c2800000d14045c001d6000132555440441d841d441c0500440b031401d500101b0020391341d2100170400c035111461000f404101e00401e4000540504800c81283c000c5010384c55042d9030740c44405c402400c84071b058201d680002c006029403400325600046429070304051030545161841c0e146031003440e0244d0020024610310607500003000b0800d59401c540c28495800003140c3c141060f00300050b440210440304520aa480414840307548010310101c10b802080d020000500035454490302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 602867841 1250 602866591 602866601
    0x150b0a020717030a02010b3705090a0b090603010b090a050a1119020d09030f02010e22060302030c010c170304111302030403090e070c230a0311060601020601140603090709 75
    0x50b80b0682c102040d013a030141d0f0280039000141c0001c51b40840300e80a02240c2c0031f0213084149100b21207090840500c0300304d0950621203030240c40018040c200e64a41551a60301521541d0b100901400c1c10b900845d10900f0140074540c130002005040484c65a5800207540c0100f034007d0040a41a0f2150054890300002030000c250700110b0000311f069041c0441800391500100402040404c480340d0301c10030102d210380b0a0202415824a001c40490b0240400a0010209081c0c00141994000d00c4043c12000302d9100ca800c482c42a015511500100e10040d5650f070484400030303203502d070b640a5022400f900741e4011039100d817107031010030101034100300410a0024580c0c070035034110b83d0010511003495007000000000307191403501d070011854111002401d0803070754400184040c45d400e80310741c00160085421003206d4954005c8903c0c2d04242c5c100206070421000a0030340b00d01400d00070503165440803d20701d0585400a0102e038554038010280007141d40010641c0c1c0c02801200303404a030041583c068 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 602869091 1250 602867841 602867879
    0x120b0a03080a0305070518100e3312060d29040b13170c0f0a0503030f070311073306140303070f1e0b1303030f150b0a0207 54
    0x3168a82c102d6101c080c04840015004034207120050000f5030f01c03020444100d010b00c201c1545c400720101c054000035a8210700019030180d0003da6180c0d01040c030054100406c050b600180d140507206003141d03a0420580c422075504850180b84040000d1007070510040c1c00b40b004d0312524407110b503200030340202a1a50304285100040407034180502c000d11001c0103140b90850701561801410404030703500d00c9035511247c4002c8111507000f00d0400340300181030024070221040c40050b50320780525071418a89075030045580081c4540081c2c00300790030318802c5c89820b0480006c14060340c0b07000381941b107174118002e030015458100c1d000318040300304040b072445075041e0344072402d04003007111810450712840401851407528003e0740284500004152000f060360000c50300040e4696618240c99040c104560b017444c0040c0c4500386101c10300c0722901190034940442c600a50b8104066020088400300751480c60300a4a4603c201d22001e000c0c82e20001c0040106080710f0048408481c0d841c0984024890301d220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 602870341 1250 602869091 602869103
    0x80c03040603050106031e1a090a05010e18070e060a0b0a120c0201140a0209030703140307050c01080702030a120e0f0c090a0504150c02010902090f061203040501020706120b0a03 78
    0xd81005150b82501545014048505090144035110403030003503100000d120305035585464a0070100b41403608441803821700c46c080c00301c407035524014540b800136103000e108110900140d40006212406803816036081089910702600310f06240c079000981202010300341d0b60b03002c1c00414000901201c0314005102c044000e440c1d4805001a0314140400c5a100103021000e59061101011a0261842490364040c415003001a1296501404030b4a03000242d00000e108171301c1e5410f406010341d400006404003503c00c2c000c48010408402c01180c4034a0305491a0707002d60b01c18440741204900411070140319003004000011031640d9025003138501405000020250340048002007807908100311150351002e01030300140902e08051741c9202764040e240807458040b6079a507075007400140c402c3d007003c81915001045d403031080c200000510280303001900c0e4544188408846207282c2c04d800300c241d07012100c050f000390011515040341501d0028010790603000c4540ea40721f1032052a44c03000c41100245001311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 602871591 1250 602870341 602870347
    0x4050a02090c031b0708070204060f0f0f050a140432090d0801050114041505120a110a030b0f0a0905040506010816060c11130c0e0f0d030305060607080c03 68
    0x801072210000000d0001c201d0640104204000d440324400e60b04450741c0e850401c2d654600c41420400c007103000e4500001c1d805418007100207143e40c412138404054480c114140700b0b100750755050000e0141d42c41d03c1501d4000820740d1007003060704507078080c002c0301c22000360005c40c0789010011403030410480703d4204001c00d4050b20b540d04d50090320403512544007a01400406603200c498501620305081489854100441c43c0b050040a03a004420340e00204008810340680a03188403028280e0f410072015500b4101c0d8041c0080c8a0050602404446034010004c07145008078118048000d00300810351147c00204020841016031203540f0140024088a81d000400d810240340c8141400010391003c0c54a81c40030384101ca262261310514400c41d0807509111049030381c54904400c589000ea49041c3d8030140d980031104200280f5003140303803401659602c81002c0d5460704100805503a000c182c0303a0b044609101b002c0002400396000540100e401844c00741800d2a558134110700343e1201450000b03e41000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 602872841 1250 602871591 602871593
    0x12010e011e050a05220f0b01030b0409020a05040b27041a0c0d09060b0d030e090903070308190603021306030b100302010527060c07180203040c0909110904050a 70
    0xc504100380450101400c1c916480c020005403000004e0092502c40c40e80c1d01c0d0600c0b142190340c4920300e0440c4a107034007440200211490b0380020912140c54501083c01c1c001e80e19002d240921500b00f00035402030000c00210708100a000080490b608482e07000700e81c1a008141494415040380142a59402072031010315007440c140900d1200d81c10150000000581030059980901040d0f424510050100149035050380c00c04a01500d07420740c1c034580001184840c2c10a055000003684450f46080c4d40c82415900d605005c6560f034401c0c1072025000071484004114180c134403d214145021100c00040350a9441c0d03000100c030344400300340200c00b00da65000200100b003002c004c030301e03440340303e03010b401180c2491600082c00c10711800700d200d505050400601d07080159440410006014040d10701d41d10740d0034601125660729003502403c15000e51820710b070926401c640c0200c83c0708591286007541ca003468170307180c0303009001c40540c119400d00d01c0300d1400300d10340c8514440307d1240340a0380c01071404c3c00c12 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 602874091 1250 602872841 602872859
    0x3130e0a0605040b06030408030601030b04060e1f29040e0c0304060c03050c160606031401020705160305030708130e0a050117010c0e010e0a03020603040602030108060c0703080f0c12010e01 83
    0x326a1100703000f28106600f1072120360701c4806071ba51140d0030883e003030f40c0d130b58803000100c0090684000c8168418038201000c06c4040a00040c1441011172130215160786550340480c0b100c81c07001e0300c1661a030b107900c050384e661280206400400b1040400020600702038450302050401c0d601100d041324114004810003043c850b490203502d040002d5801c0c20081414100600e50091049008080d00b602108908a081080c1980001e0046070000300c0310440c0400091814080d40c0516400d0f15030f489500c600602c2014420209404c807540400214540f14160b615020190450440c0b03010b140c45000f40084c50000d07681400e48541d003a014009901d40c1803020f46100e402e10204101026858801440c00e425001240c0c0140c80d2406d08100302c41281c00c00015100700f146410094100101009007c00c00c074007500070354181c6001009490259942d01103500702c0b0700a01601070001442003010420310210b400c44a6044001d0000551400d0002110382501f044203a010700c40180340741c801003100802d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 602875341 1250 602874091 602874101
    0xc0515070f05090901061d040f1d01140a0c02031b100e03130902130503030d050423031218010912032007021528090509010815070203130e0a 62
    0x46400d006041c0a03e42c0c1c003180300b901c07050184009000100c12001d03c42c1c09060169201c104005006002100c000603a0101414103844580565514107c407040040010700a00062030001003c01d41c046e59420060809440c030b4040d00019400100009134072541c0580420a03c40315500050a044000c011800c085403d104c00005a035041030000045005d0070400c11011140c4000c00561240000742001c0f500352000da110541c14031000030320140e03905454225910680c003820001d501200c83d05030301c40800d040824030640315001008070141202140d1019034000000115026042d841d00380c209084458420040d0307081681e40800341d520360780c54040c01c4100200c1c0003003980c0450084842c0c4030b1a00a0300c2000340724900288a100b441e0985405480750552001e46c801d10207040c00304510484c0c244c4500f82e8000504250010400e420110780b07490403038549400801070310900d003d60220083c0090034a00441c081044a104045058020304000c1d00c11440c0502c0d60303042a261102c2212 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 602876591 1250 602875341 602875367
    0xf080913050105130e011514090106030501080a08030406110d1d0309030c0d0204020906070c090606030c0912030c0525080d020604080a0513030803010e0717011202010c051507 77
    0x5800c20005000301c1e01c51069114020400000206172440700494481c0900f000c1001e1032a004142c08001500e075102110140c040c240c207a445800b66602c54130f0071016a002401840e840354012900c1e80002102c0b4001540d12034007921300001c0c410807412403d8025481101c1e00024561607522503100c0c071903409806820784c481400154502000d4102182e2104101c102039403103040000a0207043d03448030740440e01d403840c00030041652104c8074a8540d0700030030f01e4040c22503e10714000700842d01c98002d10804803282e20940712008441e107030002c0049100e8600d541182007000307054144c0e000a4003000404c859440c500312032940842825140c10b0003080c0c562140441d0307400002409602034020400582042e00511116520f14003074200362014491241c1a000c4844000d9000051268540180d4141e0348900102c2c1c48984400104039100070138003000e42d82038045076004112100c1455118000c4900c1030414000c140c0036510b581d0f04012161301b050000700600320070082c04640c03218600c80c0c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 602877697 1106 602876591 602876629
    0x1312062a1215060c0b0109050103170d0e010c090503120423030f0d020a060b0f10270e01031b030503090402030c160501090201200303040b040f0f0809 66
    0x304c411003001d8070341060140c0041110b00c000d000c6c45d030481c3e402c0042c02d2050714904009101d2980100c1c1c03109074203655400a040024000e00030300c80c500d603850311070040c0c8078901020701d0b09000c40d80c1030584007047e04100910510521040700108840c10485550048810300046403400010901c11078051291801d2512207650000b03c481003184204014011001d42805001410400019950b07010540c110800b500f503110300c1450002080c4031600340d444d04088181e104408403950802ea11080c0301d00014000c0c0119a1000c1c90b0400680d08011510b1307107503444058890242c50100d62140381c0020104031120780d0607040e241004824001c4043d14005490514001c00b18888100d01051445a190001001e080241c0c00010500d002551941c1e50b1603039000c0e101c0038000d0003151001309100455000c1401c0f00f203280c00c8076101e22107480ea510488400c11452080510701c3e00c1903 = true := by decide +kernel

theorem cover : BRFrame.Cov 602697841 602877697 := by
  have h0 := BRFrame.cov_init 602697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 602697841 ≤ n) (h2 : n < 602877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
