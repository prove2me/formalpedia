-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:36:43.363658+00:00
-- url     : https://prove2.me/submissions/4b01c512-6348-4622-930a-ad72217aad10

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71402879 ≤ n < 71582736 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71404129 1250 71402879 71402897
    0x1020109020904030c080f040906052b06051305010516020c0a0315020901110a050c030d0302070206070204020702120601030506060901090c0806010f03110c0c0f04060303091809120203070507060906 87
    0x4240100341102109101b503c82a2414601e1100384080d0303001030380680c402d26140c04080c4200d1410100e50381d0700542600195103440310719030040b00c010000841c09014079580b032020130594500441e0001160781c00500030b10190810030b82c14410721000494100c0180103d8848049514080c4103903400ca0703400200c41300c400402603034030070001d6000c002080c0c18042c1540110b19075107424450344500d14041c0d405460340c60b040505240c00d02c1c148001c01420544100a807100598450b815507508a40580d00140c0b204114408540020940550703070b240f500c9160000000c0000024503584038010a4408030001c0c0d907074050300b00035188603840280c0803401d05400030300356502c65540e403200c114481c41d000c01c054100d181100101c0d4441580712003150850b0114260504110585983d0804156000c00c0341c2403544d103000b0207044c201c1c041e5112000c0080c050320007001050b000801401e4014030072171f08600c0100c1c000781d542d070300803503048a00b0700441000280043c01815418110b0712035850784406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71405379 1250 71404129 71404133
    0x4080f0706210b090103051005060111100f090204020403080307020d0503060607020405040318090b01030605060a09050d14100903180f0513060b041413090302072102040e010f0b01020109020904 85
    0x40b200380103804814542c0d90b00034a0350243d907201350b000c0c025802a009803000c040305815031810355000810f81414440ea1004800c580b400c0000c818014034510000010b9030000711b071040b0050440750101a51050001c9404014007262100843c0503241580840740103d041070000c1d5090b000c00c6409581c0881c0512401c00941030a400003035216210b07103031280400b41e0f42c1806010301c64aa03044100103a5680403d8042c5507018451080500022203416080003451039000306220801d0240703600030030001041d43c0070025000884081c451001c82500d110304403140702c1c0d000034158081d01360001000344010901055520521400b40c0b410b202490a8032070520003030021981c8107408032205603950b94000106000d185001c0c1014004030164044080785840402075220b01c1041030b007640d40d01d041c50500011790005003403011181c41c0d00c951000c00d01145000384000c1c2c96008007940050504030381c8004800103520208541c0d0802c2e02c10060250103c004908071501d5050080d0800211030200b80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71406629 1250 71405379 71405417
    0x801140f01030f08031504050412030605060304080a030c11010207030816080f0402040c0212180f03030c0303071202121018060602030313020301061e05030d1b0210050c01020a0504080f0706 83
    0x21b4440b80030707200b40b0325035403919001c201100d8040740c00f504c002061449145806600d07004510040008844481c21400c0c00e4548541d07034071030607000f001416507c080041d0030320b01031240c0c440c1c201c10200085490307460900303001d44031920468030070300004202c81031510b4440c0a83d0f0304d140155030700d8500088550b02d80e824407001b0700702050240254460020500b000c140300100909540b554503241c41c8038003a00e0414884002012480d130380c8260018489885046000002d030b0785c1c491710600d42010f0030f01081812000a00c60b103c07400be0001200300420000c207144c03120400407501380c0840d90580c002051610402c450080c0596001a04100b010564070919040d2607069580020000200da9aa403048001c40c1500c0da002c1c0f10040825080820452605000404403944603052201030340a507500151210001c111009210758842c080000c110703031046c8240d502d001e400d18000c55440010601c09041034003c1d10030b083c52482080c071841c81c5000c1c04145401111095182ca40602a494030455 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71407879 1250 71406629 71406631
    0x3050c07060b03070f08070801050c0304030531060503060a05030309030c0103051b030f011d10031202150c0c070504060602030319090b010312020607030c091203030b0a0801140f01030f0803 83
    0x564036214130f14010170310b14601406240101b8004000740700c0d040ca070000303d5080d990006d0840005583c18001c10004c26040701c211280209002d031111464892500d414402c41104810313032000340f44101012540a800c032000714082c0c40d08a981c4000c1590311410941d0ba4825500c0550f00340e0000041c450f41e55020750001c81c0c2000000c11101c42000b220811902660012070b440901404c50800400426150740345200495140b00720b565528907110980e800c91002c0c910000f40090703030340b01245d1045d905c02d010102c84e482c0020034008090503c9288035040d0740203400e15508a024500700028175240c5807094100302c0d040b41d0090740c1035a541505820a0000c803485000311162541710100c0003412a0307480380d01071445020304c1448200034100081c64124024a29000d041ca00600e6450ba2a04407030490204c3d0641c2c2c0d4550700c400341034a4114060110071900c01d0700f2001015010440f1601034020500300b00300c102c0301c1900c9a4030b100032041002c0e42807101070141003001840601280104c0011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71409129 1250 71407879 71407901
    0x30d0b0409051204031b050d170c070602071502060f0a050612030a080103060513020f090a060e04050c0907180b0a1b0c17030a200111070b0a050703050c0706 69
    0x110a507290320744605089070342100d0001d104001030706104001170b138403076065030194042c60140064248030200304450007104000d80704010002c01c15012840007403c695000d01801c0581c2d05040d030302c0c2c81c0a550ac01c2240110440c0d441c604054600e42031000601170b00c10340c1120804504ad440300707103120000300b50150003035400803502d007005202e081040004058031025580c8480c0190324605180d022284042d0402c42041107405110000da0385046840910000451b0071a9642d20340240000041200d40d0103045509002c40412003408000701310950480025501505e0b580d4039100e0490b0075000d4941d0111074211021424003c1c400e07070074080c01c0505043d042035451003d14010038108070542d400e089400701300c1d08409012544800807803580701a100e500660800825090280c61010070541d035510f1750540d00060a1080c209402c10701c03010b0f9800a800341d50300740500f0049a00c0004481010440303042101140070b0a11a10a05100d07a8640031361a0130194a03075181d03400b502c0340d0000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71410379 1250 71409129 71409131
    0x605040e24060d240615020604061109150714060603060c030907031a04060605010905011202031f080604030305060d030f0c06060905010801020403050606060a09051002070b1204060b0909030d0b04 86
    0x30352800206020f03003440c02d8407820450b130603626a24818030803c1d107402d0b800442241c0159504601c0a9400055258201c0e5102c0004942004112038072002801030b00203041c0c0c05141d90383c2d041c0b03100020704004d103080740c0520000c0081c0c81240f074103169103003420795003290140c0c00364001400e44042000503541040c078841c00d48100580e01e844841d840418444140a0505484144403c06c00e4500c11000103100a0070b1810480b403a000c000781c8102c2560404105264001000600c200001c161008490009800c6d0705150303920790b5000c5a5038101128120007003840c000104055207403c907030040740513515a0f90344044000c00303041107500b41c80442c030403920316454480100d00c100480c0101406404100001070300c443ca9428a1841d04501a20384ca01030702c0f04100000301103a00c402c0c00d030b09844003569000b910080002040b40740c00c045a10090000e000441c064540b44030b0049080e005074010103040c40049440d90400105100645078140e00383d00800402d1240b21290700500a10100100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71411629 1250 71410379 71410399
    0x1311032404060303090602060601021507050906070c031a0903040e010512010b040518070f080d0f110d0315050306251709010204150906090909020d080d0605040e2406 73
    0x1c0750a980e09504200c010030141007050060701d80c10000103178400380074030007090304004403c5841241c401c0901103904000000803010001e844241c219034201e584030045c008841d43d039042c000341c448010300f89640c089181d40c000c0b43d01c4000c008142d50a468041441d070f29640d1a10781044615502c0d0807009116548a20311010195207a2107458820003092102c41541c0000c85285d60038071107241c1111a02d40300502d414400c00000203802c2024040c02c1c01c00c0400c46a42010aa43c00c10141440320980d11900b890f1b1010290b040d0440c2414102d900842c0441c543c46004154480c4400ca419420600d0b2401640754407a0341d40c6601302c609950ba0900c4220411170085606642c00200c0e90142d01d40e4000030308005891031800100c1606000d440c00302c480c541414001007013603481e88a01d001d000d0f100c104170402c0d556803040345542141d1180d4450782e44c6100071603070000360540703210f16840769140042c2c40b191500007184640c8081c41040c43c1070b100f46005a0030041c000d1010302000e4101107056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71412879 1250 71411629 71411701
    0x16020f24070309140705030d021501030b04020a0b0a02010c0e06091003050c130e0610031112150d060b0a060e01120504050102091903060c020a020108040b060112020a030902131103 79
    0x140e040c030070310300d11301d0090301c04241040140f52500c00e03030620050855105c240c8042c24040d6010005041d02c0e0321002000c01078070395000203148890140c0007504003260014100b1a0250158022044050151941e420b00c50840c0c08001841c01400249904100c01c084412019031103544529488100403c1c42030030440c214900108e400300031b4200320014221503080c400c0620f443c2c100c010212081c1d04e01072100902c1c034070303840134907001c1c0f82caa100c0e507003101102080344d0704074200006400000191000741d04240c3c0e41002c0d000380c980140c0060080b0380002c40403541c9882480643d0040c04180c4540356075030070090100c0002d0170001c2c010380382554240030345611590b59180c100c1c030400d01d84d1708103a0800d0841c240a81103858605516042d90302c003551290041c1d03040f5108a03400f03904800b403644daa60700c0340b0041e1800f0b50070001d03400031a88000b8400301c0c03154150344249030540c020380c2c6144804441c1c1c000c400403100000110000441c081c800101c8106080e604950f01d004e0701c80451681c01c980c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71414129 1250 71412879 71412893
    0x103211e18140901090506030c120109021005070303050708010501052b0906020301240f0503090a0b010b0409110412120504090e0601090c02060f07030b030c060316020f24070309 78
    0x7070340118190301e01d581e25407149890804605400f40c0a0b140c010409800c10f1000243e444103015003050148100080715401844298810200160040c11040c40c0d803a070141c00401c076510004085020a207090081b544482c483c40c40f160680d003041c1c492a203000c00d07880000d61541f00b01240c41c0503142408485843d0380c1d1140c0a050040c038424180540c90b9418030613034510901080c0141c281d1948214202d40d640e40d031000c0c0d2074407a140d46040c090307501d403610324000d410201c0c1c030300c40500142d41b000000500110004001c00880d02150340800010205143d503240ca44141c0c824a8400b9022035040c1c0040750035240301c0b0134030408a0400c00d00c2e00341d566041c0d0040c0c3d098800d904507030b0b801050041000040074040c040021805101901c0146018020f00c502c02502800b0752007055602d015131019520100311010b50344900402c6c294481c50086860102e85040240c05070041c016019000f8100400080007000406040042e20020855078024000340000070159401c2549825500b40802c1c0c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71415379 1250 71414129 71414177
    0x180e030c0607031b05040302010302091309140601060c05070b130e011d06060906120901061a091507050a030e060d0204030311070e060f01030e010905010608060103211e 74
    0x100340c040d004601d0700070800390480c0c601200c20355042d80e481c03011000c50380d406030842e400d0301d90900b40140c88042183c049088411401041240f251a2111000074087e12809003a00300d50f810049600310b80e02c1318001c075954518035000400d02d030702c804814000341102c640900205c603101c0018030b05840c0e8856800700b0130a000e9200d004d0304546000b13034001d920043c0c0b618640c01102502c026180100171000305007148109828908070300e4510002c162540ba0a4210340700415481e01d204409100061110b070056001e0a0414840c020801d403c2102240602c01d8503a800c0d0002e0107040c0b000801e031802c0c4c0754043c40700070841c1c0c08101044041d203c0c1c0c0701c07440a131001d10301030f644080c0460740705080c0f94542000394016080700d038940410003406984403803050146c10300a00c0c010074151a100d41e25800740a0f2000010019402d0800c0032500130400a00941200c3c01500b0302c8074580085042d1061161541c002d0a000445801d200d004040d480400c11518940c50700c0c0c642c0421013203c3e001026201 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71416629 1250 71415379 71415397
    0x30405040e0c03011407030c050316030c0306030602180a0806010806060d0c120303061404050603190501020403020904062703050d05060d050109060501060306090e030703030b061606061a070c180e03 87
    0x545c00f040c0007040b6030601c580e884981d400e00700140f039030074005402c403240c0041554040400d03403904482d0810900ca40c00400046a101030107546400d056500240511703546000c00b8003802c440c0304000380304080090414100d5440501515140d10390500348031102d40d1030013050316241c000c1c0b070b400030b003c441a40303250303904174003e5400040d1981807501000d242c40890044911490920b803d2280340e550101e214995551050750a41e1000114640b2901901450b0b0029500c091090200302c00c0c0310742500507414401040c000300c0740d503107503a01d0b00c0910780c9400d080250002d802400214240d00e41c65000541082008016030760704010343d50340301c0c01d5560071102110b4103600c4400402c18144c160150780090441040148050240c94080c25542e0241000107070405848410b4611783c1d44420044580b02148501c240308001c0c2c050a00c0701c080e20710b5110315010910340c840000c85504280d400c1e0350340c05900040019005250409201084441c1120242001c1d5140c0082c625070500300300170491a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71417879 1250 71416629 71416661
    0x3080307030902041406090f15090901060602070e0c09060a0e061c06060e150a03090c15020c060c03030720030a0c0c060906080c0705100603050307020f03010b0102030405040e0c0301 80
    0x50b1951043c0070a96281503404500c070061102880040d5480245c2a5400005100d000c031869503580b1001300e03000030a0482d2074001036003005100b06280190401d005030381c456022968143d030703a001a07030700018040b125408503400c00c0c030409005192000040600009503e4680038080050700021400e41c0b0040611160341c4514111004212207406000300404107801c200d122010720002017404a00c2716090303c1140000040c80c8e002d424000d5100c2c09580c0c0e00500c0074480325440b980c1203131001d070131440000d015108040c1e0308841454080110380c02011140b000c1c5d403c5449800303091741d001c81250210000001c0d40d606180080030200041c220b5428142d407801007a03451340c2415401d86001c1d810180400c546003105000c5181c1049505800c0300804414540c0c90195041260405658085000425040903800018000000041c00e442c90089513034420540808007051300301e907600daa5141c0581c00500c000c220301c1c50158007001034003842c0b405444407210700b000000d00f140e00c03504032032200b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71419129 1250 71417879 71417891
    0x2010e040609020909060a1a2203050f06090109030504030b07210213090e0601030f0c03020a0308041401021b011d060f0316021605100302120f07020c03010515090603070308030703 79
    0x151520000851b0080d0044c0d9244165504201c1d075545920b0621104829100e40000e0156000c0f042c8418500c200c143c0c16551030100b51070303190698981303500100c0d0071442d00c02c40011940a000600c14600f020f913040d21840e01e820b1540c0e41c3c50700e401780005c0800d814442c84486c80602003440c20a42034640421400050b65141c1002186080507400d0300041c42d05403800e840700102c2c082c005040c5054a0300191301e003621b1046c03131801140800f220b800081d0040c02450340042008118009402620080e107240da01240007a401242c0e24030300d03000800c0c07000500b060100c1c2194003551740c80d5001c511343c4041c11000308200000c10907552000d4694000040d00208205600c14803204040e0b80000f46e00c082c22801e9051070700c0d0307603000c0f20a00600d4825083d15a024150a001b58101c0d1207001d41584600c00914000c10404e00500c4102c5010000d40202c6550038070b40c0c5410b1152a2060b6181d12000060a4032241400040c0e823000b040d02d03425214540d004030200305800051403082c01c05035030216074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71420379 1250 71419129 71419147
    0xf120905100f0501030809060702030f12040603050108030703020703030e120a0b01050901060503100311120604031817100c02010b0a08010504020f04020304030e10090911030420060a050702010e04060902 89
    0x1141d4140c0e031402e6090f0301d0640103000040002c01200e01203281140c1003900c54aa03400040d05084030390944c05400e205000030412081d4090014008640e034a460400c80c2e80c0c0e844a86645a201d1a030000b801a00104000e00010380a00c05000b0452009004103415848141d030551500341c4d1008250340500050004100c1d034a40001840d0152640d4a0b007941141000701138244104824017000b8021400c030751003a01c4544840b40c0d600c00c50340c5607000702c401304d00f82401d01821101da000f080503c1c45002c54070104619481802c803190b041d500c80001e000b403a00080351b41c0b00a20001d04448115501c650802800e59940200d480c00790005000014090410344104800707d0b079141d001c40e019030300500c104070209401c44611481c550055442000140d40b4800c2101c1c003503041e41003001001e01d4019016004010300c006540300341c0c440e009080c0c284400e4070040e0501807140c10b03504c0d80420100043c1c0034183c8240d000c1c02140380706060044258010703000240581d0f1850704007040a550100b12165 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71421629 1250 71420379 71420381
    0x11508061009061d04110901140a17031806090301020316110109020109030b1b03070c05010e07080a021003020715020c100e0309010318060e0d1205060607030f12090510 74
    0x400b500c0b1000c000d0b4518107601a002052403551100000b000d603c001014420900807650405a000344100010342e12466420004041e0a4207a8003d145001010407111175290b02d14031403480e080c00440c109040b051628aa0009006940d034202c0e40138002c442194400b4000384d40115805400300e01180241c82e0024090a070781d8410b0140c580c1082c4423080941d8100c410348081e640c000703210800c1e50361030407142d244210340820340c1c00909200200704860b031076200354203883c0326102d4002444a0101d90080641e100641d006203203503900184d407100d0051802e0644685500c1d406d05001d403c0290304c0d203541c0d4000341c2480600504980000d40d216140c4001d0040481d1150084c02c104103480315248032607508d0003003400c1c080c181995120007141e07000005806046081c1d01c81c00900203c0d12014107151986104040d41d400716030701802c1007040003a54012940b0030780000d00300038140006628215240316a18615805000d15540d43d0840b10889000d0240c045004500034003078007a480420030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71422879 1250 71421629 71421661
    0xd06030b0708061906050d0506030c0a030501061d01050307050d0f06020a0905011b1a07231206030f10020708161410060506030a0b040204180501030203060601030c05031801150806 79
    0x100d1000713442c1c00c280300c0d151b00b04050301c0c0400c0c4202c0c00000c50750396031400300b8508210b40c10b941d60301414500b800000c000c4150800c3e82a130710883c041c100d910350143c45942d201c1400303002d001c0d40750b0014102400182442403211003c240203407440103000403162501c0c400c80c0d00040d003040c00265240c1c2e05001c1940c114090280603690b80c0030740140f152517a251012040c0308400d4000f041100d840100f40c4440c07084811900042c02500c821f403181c00422008182d42c0e0050003a590182d550381d0004800389400b1a40c04a100c0504001d04030701074048296200950203c40c00319400b14040c04038980700102c14170035804107441a0384003a0020a200d000038a0008901c820303e0703000c1d040000a10080c0c5a141c107a940040c8081c0c0d0101e04800c58800242c00390023035801c041d9840c985d0a1003003240042903003019040ba4000c1c2e042e502903841304c90046043d0303071003004448042402000800c50712109003101e4603420b540040001150f88014448800013502d81d40f22800a910640071321a16504001e010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71424129 1250 71422879 71422909
    0xb010806060f18060613091e02040806160504030b01090207050f0f190c1505070303200313150f09050106080105011a0703020c06030412030c0212030604020d06030b070806 75
    0x2400282d800000900b80c648030384180014a8020004a07003151510002d403410350810900c202e06054880c003011005244010040d10451280d0fa94622070344c01e14801c82d002e480071000504900e0703075004900311407010261803403405c02c00100030010110345d000301401e01a209580d00541c0c1d45a0500304207140294050240800f40c11904542c030902c04002a10040d030281e0743d840d48000c503d14140206501038a0b03000c50100042807100c220300c4c50f0f0040007482d04d24441d0310108103220101400b000110690011940d81280130000700b6021926102d04034501ca101d2129031440c041c038400460255011a008459995212040c80c800c0103802c0c0034000203402c110000b042550f25003020568054400d1205940b40140081d0000500d4030a00078201c071144007501480e941e0500349410745001aa010265001a1510300f440c258184085a82d1240c0341c0310b01c603c1800c540745d441c2004020345c00f11009e850341c266075407000400112041c0310680b00380c513183c540810501e003100a20850400303407007003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71425379 1250 71424129 71424139
    0x30c0b07330b0102010e03130806070c1e050109060603080d06140303070b0711010507020705011d091f030f0b0a060501110a1b1d0702010c110c04090303090f0b01080606 74
    0x9001e900c08400e0690041402618408103140308a040140c1c018001038040c0c0d1014040080d000d041c040c110850781c011500780c00c0884010b40e0b00c3d01800c850710b42c6543c100610040400c0e40f40c220306003980e881783c1441c6002c1c00000032100040c1c0c4e111004c41d00d65a008550901c1c0205882c080421544600002030132002c038500b00c1c2101d0080065224411404004e00a800843c00324040314401d40c03007800e8540e9024001c200b1400d00100195072039800e442024001a812170790030030048200840011400e001a2040700d40e034480e107803a42e410445920b012038420f005590000007066160b800e0003403031070041e52407000a04107000140151801600f240303060040200c84030504580010702c0c40b0600744c1000c0210140c0042c484001c41d4981240e2280c50100030601724664420b401040d418040c0d82250000c1095028841c400d45d030452100e07444c110300c4e07080300c404103066041941004c01f030148030345400a1100071030303902c40e11078401c2c3d5003040d5551444ca400501c04035004001c22a0400c0c01112 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71426629 1250 71425379 71425433
    0xd1406040c0801030204050a110403110907090302030a0b040201050d29010509030706080408090a08011a0306010506040509100b040611300a02210919030b07110304030c0b07 76
    0x2030082d09480707061000900803541c601c0010082c450a9110b080500c0c08008915980d50307590070010a4003000105c128815488900422061070040e2185c00c21668040c01804801e140307601c0b45102618000c000340d051090812203816010028400d034504d128412070094588280e07280e100300280300040120381401401c10082c1415980082c1c050100d5049140c40b0040b0b039298079002e0840d0280350807540e08800c008802295115040d0011821803007501c0c400c0350032402c401c1c00c042d80c419085c890607401c801c1c1000184141e0400d107059a80c042c00d0035924000c966650309042843c0c0d40280d0103100040da80810031031241000707026540c180746214408204100344e40100404501055005207061240002c103681040c4c000e1002113172641c030404050149100f59200c4010651080305501d01c07414000000c5244c030814100000162500101d0442541e92a50001d81d424194034104040902c0709020000010303040c4451a00a41804410030b5101c056919082644070003e0324203401001141e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71427879 1250 71426629 71426651
    0x60c030e0301050702030f0f0f0f04050f030604030f030f0b150a17090c040b0d150203010801060602030c06041b0e090706080a020711090c040905010909050d0206070f0c1103030d140604 81
    0x40c0c030100747c910005030781c3c0c03007502c40d0030102c50380700b04521001301e1a40410600128103000c1d000e00200c130703001d84098089000e01004c060701c560040324020003003100c418a04005030300c81c0c1e20102e20180c004400203600032841c1c000070185040c99500d840e00d14000141c80d00c14a90054800d085000b601ca04420541481100c1c261940c5000c20040c0c001d90369103500c584540d131065100b00d040c81c0c004008000c000e01c1c107968000607500c2402010025800c003500011041c1c0b0000413201c1d80c401c03032009070100b5103a0707540d5860340c004d03d15503403019901140b0020a80c80d01d10403515009015080c024051980361000c00b901400d0000e00301800c030351041c44804042501510100031540c02125031407200c0c0c0d038031454041180540e030000c40b2a14507044c00482d00340c0c0780b9801100c0c1d4074040c000b00ea41142040504903500c2500300c48800c00640344003c1d680309280100c080501c8280328441404030005620042031450b004550700302042500e84034000100104489443d821190a440c10302814280c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71429129 1250 71427879 71427883
    0x302041a040e0d17060402040b0c0106031407050102060103080904090c090903120506010e041e09030207030606050405070507060e01060b030c0901090f260f030c0d03050601030b091302010c050304060c030e0301050702 95
    0x150070314144c00807880004403141e1701c0750704a074007a00c441180079844249030387c4258000e10082c08221000c1440c01262140c007840003503a1005c54005a005000e070303a003140d80705803554001c003501580060321024908001035140c010600500405032002540d9080ca04000380305001d02c0e00d401d01a68500001e01c512664814214034002006840126804c822494691030b140c442e0b00c41100745d03614010250f01016800700340501160300030b440c20710110392a40e003000200c540a454441c0030804c100001400503032550480c031081d0001c9000007400035601c050312082c5a00844842e0440c131400100c5e200c05603040080072001e8205541c082004030704042808102d070000b004a10900c03102e090041d242030341d0801500d10001c3c10781c03040d20303103070f0f01c200018556840507443c051010a041c5400100154804d00ca41c0000c80750040110754240c0754500c00c0035030515004c8044e410004a03c03081d10100d002000148024582079480744404842800c00410306001e0007202c038400e9042806001c0710b1580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71430379 1250 71429129 71429147
    0x3180f061e020c0907020a02011202090303071704050a0b07140601031101030207140d030e0f0a03020d1b0b04050606151918170106050405010605160305030606040302041a040e0d 78
    0x8480420841041c80700d2081e0b2800c190058a154402200300400511917404202e04004c14401c5c3c9882d006201300b0302d80c2d070060b801101059505a0301c184600701c0440d00d0800c908070548202c5840500d00350302e40c0e0205110b0036481d080048203540010f0340c4420007034a07000e84e072200c020090190140c0d5045950751041c013102100d0701410180c010440c01c0600c206e403410400c0c2a0056411585403440e6103201502500c06440c100c4070b14000c13140e042494400200c1c0c0342e03900551540c0070340890060460152941e0401d00d60505015030180346940015200c2420240900d0050005141f64a410820000f60003201c10034001c210304103000c2c03140c4240300c1c2d1b809100713031002030300300f1207030030650718141d04082803a90340f151010854030181310000c0342c0c0c194080000c0d50b02c1501c091103981e0300d510080e030f00c901c80d00c9207082440520704410300200c1e00c10310103942c01031001010b19140c50740d00e40000d81961030003000b00145103d2000c0c1c2a1092409200303401989411380c000d00a4181c1c00400506089a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71431629 1250 71430379 71430407
    0x260318060d020c031602040606020a030e04020703030e0102070c0509010906031709010e090f01030308100506031603020405031e24070836070b030108030d0b0a0803030403180f06 78
    0x1001c036809020304000d8065440e0f00b164041129210312880102d85012107265000703a025515209011441d548082040f520298040d11800000164501480001e40c810302c800d504050380e40c05140c000420a00003000540d00070150a0060b81c105801c001d403000040e030001004502d018010400560641c0695911880030803109032208120350068a41020905100da070001c140c0b420468105202400c06050700e020b651103a80700d55443c0c0e0382400341c85042c014180d0021050000a43d0011002c80300e03040011240740142c00c0982e03850200f8a40b1042100001150305605011a803865041002012460324404006412b14501e40d40031016a4081c0c02c903400c00c001400090450182070681801000801301c0080d18003805035480f05160a2101e201141070040c40e000040884c0140240c030f06851501c0c0185140010031071040d0010600649580d41203418910b00180c2020184041c5100754003030784078441c22102c0e0b00c161184158440d0031404103801075280c00c0c400345500c811441c0d2595 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71432879 1250 71431629 71431639
    0xa090807060e0d050708010903210c050708090a030213060602010f0b010906050f0f120105100f0909090512040815010b0403030804080a0e031209120312130212030301260318 76
    0x1107030034071300c2c02c282280d0081d071815802c10b011041010f501100420000c031081d00307c4070720301c0000c0307041030f05a4458400724000554240080c6012030801c0008083d40040100804101c82d9294041210581c0200c0d411402c0c9544d02e0b010040160207001d5a00078941180080025444100c000b9201d0760840c0034100070014003055a280704840b0300c04403021404087c11090300c41c100c9034100d0412100074000c5a0040e07914008115626004503041007960800fa00c44000860800c00400c00414a00c08250380920541285031420002c82000384050803584000e00081401c5010041d0407042c1070740401c2620390200001c002080e44440316a4006600580d1a581e030a180b05080390002c3c002d4144561600079039290385280760300c20b00100307405502501c0002850211242d003076102d0081501e016844c15504000410340c1e41d20300f000a84040c4010318140c00d070b5542090152440d0002d0700980e46012800800c0d030b4640c0c0140413100e1803034030307001d0045207042001d4009c0ca060210f2051528014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71434129 1250 71432879 71432899
    0x60a02031008060901090201090506030f04060b010309150504050105070804050604170409021206042405090a0e0d0c0506010f080c041d0d02010614030606010c1b030f03050a090807060e 81
    0x700c01c4030700c40c40018a1034200301c400908022410500800d5880012400308210800c0014203060105c00e036407083c800b00070511442d580d1920703030a001c1c06030b0609040c10150342d4013030b540000e050000c8030340207640a903000050070700c2d00707182444c01c40c0c0c000f40c1400240a00b8804210014034001190fa9000f984182810b10080d580c0401c80740e41d01950b00b000100300d001103142c0341c58107018260309110f00c400b11014084100044030701c0103995481100080500007001e4148540d081c03c0307280941044446000091006444145d2030030036501d40c560b2030014803140070360070920004003d424007618014080110061922121941e03c03242555024050b07520b07500400c04c120b52581070244010840f41c2665500381c200c0788028003c10150003810245c1514000003000d41c100000e11a10610041c1c651f04521646604e5114801c00303203080314505911351190110008142c4031600c0c04040c46611096100c2901081c06041e46500340c01440460f481084c0c20088250710504c0e046031103909031055202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71435379 1250 71434129 71434141
    0x70c02010c0c0b070506010905221a09030304060b03030a080a0504140706111009031b08160b0403080604090201021b0303130f0f0905060102060406050903160302030a030606030509060a0203 83
    0x78000008050403403a45a44000b61069411000780504c1d489603064803216a210052103045801c26161040203100c541490801b50b001c0360207a281890041e82c0d07001682c60710f0350003c0e0070f80c40c0440705650980c10200c144820803140d8050288113903011005542800280c860042190380014040d0100e00d46a20100d0240140000c09d84003c01159080d2400c240d11140041d2030501c48520080b00745c480c0c00c80c0352504941d2441003d01f402d503d551450070f295002ea483c61240d0a0140c01a604100100009030307410030440208a07115109440028252415080180030968003d081c140a1400c003030540740140c0c0c0c0840c208000c0460029a0050400c0c2e1202113495405100c82010200c0781442010418180140400044417106160551019114a01c507015540709441c41405680a040403500203203e0360440f690010803034007120308024120b02c48a90b4030b0f1460405501580000078080f1045a0500440c40034013802d0605200a0500c0740300c10b55180340040013080c0155021010400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71436629 1250 71435379 71435387
    0x30601030e0f010507230301060503180d09030b070806030a080d09020a08070807060c1110050c19021f1409030c1503090106090b1c06060504140906070215070c0201 72
    0x16201c1d40c01021607004110140202d030080c0f0090b02c6542c0030401902e00440e45c40305d01c04540c881855444015810359207003c01c00d80d40b9410140083c0f418406101c64800d0350b800400158921039203640e5454000c074554202000076460141c00081000710710707000c2100c16200001c41c0b01c0c1140d032104015030340c1c40456548000406007640300944c0881c0ba503d00044210b800034038101503d00034020742e505181e03a45d80035580040144c42c010480c1d0750b0366100020301d05d00341e1004020b550303031030409526014240c41a40c4c142020801c000405512564032201903041c20b0140c410b26010784580b040400d20349150140035100501d404e142c290000041c0c000300f46d00d081c403d0348510720300038060111400400d80c0b252030680080396212465031070054000b500d04464084e000800c8402b0303140c103080c1c0c1c400d00780614075410300c80020703141140c84040c0007907142c071184541060110302e8088000e0300d04140400d01e05144010303000e0400c65000c8220350113142038010b0103980244007801c10801038840340c40169 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71437879 1250 71436629 71436641
    0xf010f09090f0504060f0915050613020d0f050615180f03070314010c081e06010201090b01060c02131a0108040c0902070b0403032a030c020f03030106030b031c080a0203060103 77
    0x701129051109201d58141203030003a50040d40310314014001d80c510308480d0300403039556400260004030b0004c074510f10200154011900404041c101ea150303001080b0b8800160391080704500034040d658a602c80c9041403611850b50020002c40e000600417400c101c942001d8000c0044050103007410364028815941e0f610740040382004064141c5180711f943c0d090407281ea440c00c02d22504294202020048524480d04101f4031404501c0340e900c145943c6611a03c000040051040b815076581e41ca240c00030074500d01d25036008080325a04d6100080240c4181310401201d84405e82085041108a000c6d409402440014107030702031900c4062a0b80e607043c5819000b5466000c4a141840052603a05000711744456520450017034805024946102d454494401205100704107200c41441040114901c40c0e00070350040c00d0240f0440c4d110359410351201d42907a200781d0250b004a41d45103401d181a08091142c40d6071018503a00c3d40c1440b80c2104000b8004070b10040c04902141e40c000300161b10340e07000754008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71439129 1250 71437879 71437889
    0x100b0102011d0706020d0507120c030e03010f05090d02030301030803010504051009060e011a13090e01330e01060519110313180614270a020a030c0e0f010f09 69
    0xc00b000c4182c4800e03444666500906005001d603e4208681500030805c50310304644c01641c03460210320300401282d0003d0111000c03401c003d800009010305940074000c0c03201c40d1494140000312030414103035091510741d81c1d001d00710554105000400c0400c083ea01a68111001510b003c0f407140d480081681c8000119004840881c3c60410089405004e0010240c1a01c09e000c44a032245590010203041b02d010f010300b07000c001e0040000900484503c2e801a07025000c031800086503140111040c071200380260042014051180550083c2000e0800800300041c03c0c1c400b01c680140d414010010140d101d41003140c1c0c9108600300e02403803c1d0344107000f001494183c4000b500d803078810301404181e8904040c0f160f0083c042c5410303000d000d070715454031030305041350101d1511030700c01d126041c1800511503c0311a290000d040c1042c00c46415408105801d1140100040040c0c0e602e60f10300c0040c085801c01c042090030405000d10349000c940716801030101580090038091001315604d0021503001ea841d400c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71440379 1250 71439129 71439161
    0x302091b0307080105040501050a030209060d030e0312120606070b010303180e010621020a09030308090c06040e0a18020120070911070506150d2607030503040605070c0302100b010201 80
    0x704110310783c1c0055441d06803502100c040c002a40e030344e405c010300c2150f94000030394405c00d8200811094609007401c86105c900c01c3c208210044014800203003030411440c010521950300085600100c4680c1544035403201d0222015410401c0701d403035141d104241408018184010400613079200186088402c000717220621400d561503854210040c01c146031005038000c2c0c44c074104000b6078420b00d98000e850710030411b43e5032118845d1940d1421203d003003016103203042600410501c80c0940d01e40c0c00040c00a040642e0b9032101606144c4c0313042c1c04035040a042c0006424800c034030000182e074480201044403c404022a503844110b02c1118201469503204016039841e11180080c1401200054024603000d03105442840c5d139480c20003550380e01c14911103644201d074002100300184d1101c8002c86141c030f420140031030751503500b081408681d012501c15004200003108100802c1080c1c0076150340a00396203880d07148116265006583c48c0180c0e05140000c0da1181c7c1c1c1c4d4680340c3d200f5845500c51300c0100c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71441629 1250 71440379 71440381
    0x2010209060a03061410230c0d03060e090109050a02060c010e0601081f02030108120f040f1d1302010c0305030601020f030f040f0509150607030306051305060a150206010302091b03 79
    0x2c0600240850321418801102100d41d00155140050000380702058a48601031001d140c107600c1c034021102d042850301e59040a212115154000300041d01d0a8001610700150f200d081484a5030b0752000104010b4071030381842d0314040041c1001c9102000203905407052610f43c6003807141a8054180e141001d410b506c9450000940d080d00019000d0311000b035900b15410750242c40d141c003400e074802401520856405020306c0c00601400341e0080100003201c0d00d000341425210303001403090a4041c0d01c00002a10108900421801040062500401c0d0704ea0903908c0d402460340013a01c0200c0499020342417110100024150303034000c0c0142c0c01c20044d1348041c1c2e681d510030034030100400c0e0881c2c050408a05811100400c09040400a00d8007421441c0d01c1c007449804103c0030009254009038040703040640701d071800180d40e103892100410400000101080510385102804001d0301580c8c0402501d41005c00c031310003c10f802180c0941504d4059408014580d00d0409205400142c1c030412446420008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71442879 1250 71441629 71441647
    0xe0301051509060406050a0e06060f0a0503100e06010219060e030a030f0608071d07170103030e1201060b1606090807050a0302070503060c0d0e0c03071e09140402010507030201020906 80
    0x2581c901e0307214220303407020250301d503074044c8401c0717030681e003d10340e0024070000e0b0030b01460f00740702c112640c0850300030f10142c40c015100740007140070340001402070089680401441740e1004081c0c4150050501c24240e07021926088000079aa84980401850100044c616580901c80c0d5500070400448080c1b00301c070344c0c0c0c10318030300c000b0010300c070110100005501d040c0010528a00100d804001c81c0d000039601c4410a483d20341091000c640a0000410301401540070b20004031100d15541c003c50003a2100b9815024403014800200d103ca8074160499142c544113001c007809642c113840d0848416003901100c001a840c01074004e20088502400000021a88100300800020100d003124482c0e8203072044c4075a1113080c1076480c138095030500c0000e0018081c2d2100144c0961140c0e0140d0001c40072581c440107a03002003030034003980b50011119500c0d4149a0310895000c0d0808100070005c41104110301d0902884480214202030002410840d000409070107052013501540c045800003400c03c0d41d100440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71444129 1250 71442879 71442901
    0x14040302071211061305030d170907030c051005070605040b04050616050301090e0a0204060b0903121204020d050c090106120e03070c0302010311040306060b0403120e0a060f050d020c01060f050a031e030e030105 92
    0x80c0b942706010103818000307030544802280740c0b422030b03a0010001c45002c0c102000c0240c00350b040a00302040160600080001c550795014850107540120804c008a0905007801810b00c1c400038010602c00784030310320703012020750b1000441e411201c1c0c1e4180068001c2d00c51032182d0034800381010203503000d0700f8200085003d02404c0002c1c0b070000d200700c0c215413100380300c0710343d440080c011110b03c110703c0600400050050300b84074107441c49203840317803080d90740036070207000001c210003006c4c0c014000266142000300080540d074410090866100c1c2d00450074015259610316890301280002410191117030702a00c4100302410941c2c0142da444a01480b56035150220b545d00e540140c0310560340358010001c04200e01d07010762010004e850000e0302503103a080c01d02205440c111340d6804500100041008001c14081c0e261001c0c00f02c0c60990341c00424007618041030003c800a45800c5940701f50500d4004100103052100009441c40d119020614403401a050076281c511491461640550800041040307003c0d03c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71445379 1250 71444129 71444147
    0x40308150d24200901051b0616030b040608100e031b030c06010b04051c050c030a05070306110406020a0b0702010b06070b0912090604030f0206070614040302071211061305030d 77
    0x12129040140b0701c00311001949500050040840491041140c000c04e9413081c0010300c007454408040c05c007040c4c0012902458000112400d010903030000815150342e42c0d2501921200b850220f4062000d507007450081c98441684a01c200340030381d0350300d4520b81d50340d000340266014101d1725581062544200c1c6d0b505a1240e01402e0000f000d40100030011490a11820540d01560005041c20100114100b0810000000c1d4001500d0f00c4c803440220b02d119036020000f160303016100307001a03e00c0301e186241c06800e07903040c51784405840009010501c803403540040c3c164003464000381182000e48840c40141c1c010020441e0711504803034000380450921881c444458000d10b800e00480740010030240000d120350003000c603c035034020010041000850000c105245103035000602c840d240c007421381d81d000c086489008000068101040403c818550144500002441c041c03040141d248229035511307401910801800e4496074001c19001c07011022200600054100074085a400203000b036005050558 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71446629 1250 71445379 71445443
    0x4050f0a170303040317070c0204090609020405010b090307050603010503030a0f0c080304030917010b0f01050a09050607060504030207060201180f111008061014191b0b0a0b030303040308150d 84
    0x41c1e41c0054031b02183e60300c0440c4120503030760354003003c40003903800c00002e020390010607150310b9102e201c41d4025076100d2082d50300070990580c0d40c5a03103155100601d070604607281d1219116450a00041109407804030403900ea001840c40c198039942940c01007511800582c0c1005000070f500881000105600040000169040c4c0c001403103001c814074440d01d090f10440000180c0007003110307000e08499406000a081003800318144642020307107520200701540c00030041079402e00c4d294400e0205154040c4040f8015094070b1000780880ca0111920200da884100801403013454004051014440101c41c0e030450000014802c50182c0800c240c000c1079020160f52403403250750308800e001d200c1070145411002100345407081600380941d410940b40907405441c02030b01480146404842060440d4140c085554032419200c0d000c1d080c020034541c02c54649000260003544100144000b283e00842c220ba445640c140c81504c11904400100c0c50880c49540c000b010444000020304014004110180740a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71447879 1250 71446629 71446637
    0x1c06020306041d15090f030705010f06120b011208091008071e1e03020c0307060903020d11030711030309030a0606030b0702120a0c08120a05181204050f0a1703030403 73
    0x84480f145110340c031644110101050340070310601c08000ca500441d0960222125041c2c40d00a0000b2460a045900c095011140f5035910310031500c1025440c894000a0465035003000c083c030141399038405402d10180103500c2c0d5011000e40003810041c1000403940f1001000d032142d5100441080003800688080c1c544802080401403481c819401040c0d0020502906aa441c80d0140c440341c09860601280f1107100105a002c100c054080001003000f401000d101c1d40700000c2c046060f04009040510501c038000c10030907140c01404031040000280c40e20140c022800c15865442c04000900c0e41c414034405941500a91001506000c52a40040100da0003035007120083e0b61189400c90308c51074542211a001001440340d001e00074803e01c6440e40140c42103801c2403803c1c07204401e07104401800c450181d00c3e40d84071810010102d035100c1c60b2030308078440306005084001c001c0d580b03d85a80524001c860023140340d5810001c0c50b0307592220303500041072810900c00c03400400b039860b907440790310450b803e41c042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71449129 1250 71447879 71447891
    0x90b09010b040b01050703081503030f190806060405041a0909160803090d030c03020c0409111306030803010605130306020301030f17030919051c0e040b01030209100804021c0602030604 81
    0x7a003001d0144420b0440142d682924003884d41e9010344440c80040c160f28201c226445207600d180c0c904100400000d60140d14003500d0780010318034000b04c505228003860411043e10244895521000180c0e4207a0383c040b1000700c0c00768001c0891003030009200400c1c65000c0716040502003405404900410b00044843d0468000b0b600d68250b55502d128800150341c0180d606003044000c2442000c0c4420b045110340b0540340d1455440c80080c0541e00851000d8511060f4400d00030028985032821000003400d150051209510303540318441c1e07500051198105204001070080e0303844003964851f2010303680c441000c54603540c413070070840d03122040843c0c121101d18487d003001e00c001c5824415a407080410f6002000d06c101c100d4244444c403001008101c5d407620492020081c100c03449041513480303140f55076554103048030000400c07007500e0514500d24103241c41006a0b402d40d1725010002e842c40c01c0d15090946807920303a8408540030321300d18112a0f9900c03000722400c030104122500214000c0c7c004450038858 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71450379 1250 71449129 71449151
    0xd08090a050316030b131202010506090112030206040303020a020102070507031b0b0705070303030b0103020c01020a02010e060a060b16050c0d030f0e151621020601150f050a03020f040504090b0901 86
    0x14407075481c00341071002d080f201c80800004080b010425400f01140c0c00c090f4446205640b0301c515410503a4480007d40d4413681003200034106035a505005050301180c030321b0011901d4138045c0d00c66a028102504046e00000c0c8560620b000750102d42110340d0000031154207585e6801d140490100c1c5e0721142907400741070031001412401d1070302030ba02e1480c4c214024000140c80c540d01940204000b410b00c6040c550240084480c074902840a00050820b54002041c01030541d000d060501c03000a10311902c1c9172a00d201444243c0c0440240d8611103906074401c000c02110f42040d91130a2621060030b81d000319040d034030000b055840107881103609107e0b203e520341d88601c041042030aa00c6075040d43c5906005204080d0f00f071150b00e0032607098034021f8030180080041506441c2c4040c0f9603540034809640039100400110045419200c83c5108030302c0c1080c0701407110030005040744034403008102015000b00c0c50124200c901811100207250040040003800b00350f14041c1c107504411524030f0104d510380784520813 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71451629 1250 71450379 71450383
    0x6060607030207270212061003020a120506150403080408060106020304060c0201031e020f07170909011509180e010c03060605042303240a090c050d08090d08090a0503 73
    0x8011603150b0040c1c80c88030b0034001465100007410151100d1241152800b02a0805a10041c00c10600c001c1202c01e061500341d044c807065a403000851003c06104101040c00a81e01c50114901100c08a00c0401c1d13984a170030002e24408901c2e84626040200010b00104000c0420000c00848106809a51141ea65010266101c1c001c0b4800e407004510024129001503101f580986413411595010b0354420042480200c1242c000041c2c1016035403000444200303009030240511a0407a0780c0040030701d404044400314416007410720980440d48500c18010503024044c031020000341074860100c003556803030320407080702902659100c07400c01c0d460106809003451180c0144010740340d954075050314003450304031100d21f4001d06c1e03803d07401840c4000340d020041d584d00f0b2001111a800481c401d983d0020300341d454103104240942181e01c07183c500510000043c403140403d900301e42d0100c95151200405043c85000b40c0314820400c0c0d0301201240d800000c001d000000b41541d641c05a40718007800e0341303400a0607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71452879 1250 71451629 71451637
    0x7060f020607140a0203131401030f0b03030a0e030a060e070302090c030f0c0a05040314070303030b12060402040902010903020409140d030b03060a02070212030406111b0d1b05060403030809060606 86
    0x4000030f030100480c20b42c4020350318014403100315144102c0386804155011540391901c190048840c916009011124940c2e01d4010340c510743d646160104460000d1400003a0360b8807808040d0303c184200703030006501c1035a06103e140380b4170307800c0b2405120760b00c4600c0d001c50303c1d080c40740001c9120300900320104211590742001d5900c034603014045090691524560007103190080c1d0182d1040100400c00840010448a081003184050b00d0041085600314a00581519a40d0701c8160007440c3c044a0590550700000d0071603002074040c0c0300000c4c855140d0004a0380300985800203034009090850002c200141680c00181e490102000d440c4880d441c01c00c203c2c1a10221850700e030340350384920041a00e911495004041d8141700030305110f5082845c0c80010300310341069100300c010841204003141c05000c140203c201e001418644c850310601e40e40002124201145000f4041e580038194001500c855030120078003504000b42016201d96880c5401031241c0d0046404c4d0b40e05000d143d0118601c1e0074500240c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71454129 1250 71452879 71452891
    0x504020607020123040305010506090705130902090d140a1202060601020c01180f060801080c0406060507080306241315020a02060d1103130b070804030e1c050d0207060f0206 76
    0xc9807800d54280c004483c001940c0c0381d802c00640000c484a1a281c110313a0091004502c90000403a491505400304a44031000601e03c0042c07207001c01400c46000b214203004019144020350058460603650f010915410f4070500040090544070072003d201c0700009880f035800c030320403083c04102940020701241c0b50034080d56024003581c440c0c40c2000316507001d0041d906c0e40b400c5420308070791017a9517200a03001d4040300da44078001085404006018440c42442083e40c1c18a05503030074050304e8034005000f40281b1407504c0140040720048041201c0ba034582d130a01082d166110815070780b10411500309000d5030700c0034a01d040820341c161030000c2e00c0b4403007646810007018150054200b0510a8090058507031100f00c159050036598014087d8268101020314040c12400514920000c42da02d0301050346d8001038407003011710400008000000340c1c4a2106038800c18262000d0000084050802001d070000e00401002c0b402190515000d10742d00180f4102141c440d41e40b080d031501c2c820b40341a078036510141e6003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71455379 1250 71454129 71454139
    0x601170c0706140a050907080a03120915050103060203101202060d020a020f06090c040e06060a06050c030f1809010b040311010c2d050106080712021507020a030501020418050402 78
    0x80c00c091a02028215860080801040100f2219592810b201003150607007038156480040c05074000040125202070f2816030000c200108030341d00c0c0580540149040f41c500c0070f45031944607041000c141c0715120408a560020720507541c4a1900d10041e40040b11030f0410008901c10004518145165140f07449402405161900c00400c40c5040a9444200c2e04003c0d4407810060901050040080c2441542c024000c1c1071212520001c00c410f840c040400b14880381d0218007071011503543c00c2c3c0702e07004075800c50804690f940e900480c20b904502400c0f2441c0300c1107034003240502807201104504e1324400d1045481c0403082e038852004143c1c502072030002610800e10302128141950060154950032405401c50b269260403c0e007015404140c04203000310024400300700b21082120034043c481c044c1c1240c0020344070407801d0200e840f410310100031010f03200e90b11890420584d046081c045418558000c0c0610f001c0c161070b400c090340030313604c9846142c1441c51025030742c0c0d5000c451071042034011540181 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71456629 1250 71455379 71455381
    0x403120504111e0913020a0512010e0c010c0210080403030f1802040c140d090501060f140f0103051302010c08131508060109030305160215031003020f0f03030a11011503030302040806060117 83
    0xf807121750012040c220b80104001c0c40201d0181d50f44194048a0700c40c0d40300124401c441140c20506003410800b025040c002402d0203a00103958510351414880755074070b0031040035a034070b0404501078542d502c00100c8440c540815405143c0a9042000905d8002d41c0c05011140b8000c03c02c40c0c503122003507881c5190443c04c1c00310714029880d40d044501c4180c05800040b900c7d90706c448812459406590004603544200b614514050807c01981a5081000d003030402c00c501e0804081e844403154210000d040055090b180020008018140c1c4e0b20003000858550700b40f034440e14043e02d802140e01c01900841c810344006252903200e44030f90300c10b0301c1c3d041d6661800d00c05170b07050840340f11690400c12a032245400001060f0140601c01462140303c0d02c4080c65041c1d440c50042c040351410341c0130200c3c001e105201580c0079584001007141d40d195524584004007103219660240108054040740140c00303521b2900005050340b580290050310240426210315448500065604404000001522241d428 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71457879 1250 71456629 71456641
    0x180706050307020705090112060f050402090601050c162601180312020c060a0203061c050d08100e0106020601140f0a0e070302070213020c01050106080c0405090403120504111e09 78
    0x1101450b0000d442d030040b40d0600b61114000f07035480d00e09070054400045c0c515001030520805008603207910740c0e01c0008100d81e0600d81c004c9042000001c3c11107050020000781c800821800b08980845503c2d40c80040d40b040d074a68184401410058221070741002c002141039040c41030601c12012103500000f0324081c43d8840b5a01038a51200c5c002e003a440859003840101309002090210714425240102c0c0180c3d285044002c02c04148400c04109131041042c1281400140c00094000b03a0070b5964242125180d9030b0a0b0701c4031040042d900300d80c0d401407086000081c80b03600018910b041e201d04078138140001070000244000301c0d011a6509070702a40910341080a03404940352943c101c0c076240740152a04034541c000c164030340341c081c894410340c0b540001c100201c2e007000c2c1300711400b402c3c0342c0c6042a40c5013801402c0c02124010b902a0a00c030b40d000710b0220703081500450002805040305c5000707104525140c10700d291290003a21803507014030300c813080303090610810204101c01c044d0020302c4006035440740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71459129 1250 71457879 71457887
    0x5010e0f1c08060103091b03120207050a0909020a0302130c031a060313050106080a030e030c01020a021e03030d0c03090303110306030d030f0b0303040f0915050a0905040303092108180706 82
    0x6803003e81415a10441e400214000078484030701602c0380300365040603510390314120f51803034030390000d28046406c4803005100c141c3da0300241d60110303180d030800815142e45500003d43d4280ca50b41c002544504d800c1c460100c84c600540000c5000501034400b006075001c190359181492001c105915030002080000481c4c00309030421840301240540000611144c40f50036031803404840d07100540104504061a40721031604000c00302c1c4444013071020300981c4105a0100d00d040324075198196100d00001a02d11290700c08109854001c91100000d1020002c2d00802400802080400780d00107420441c180c0c3e000e100c580e085070f000e0035029000b001502d0000b6801c030021b00c02c14840c02802a02d840c0d1848040d0307405c04c0600f01400c07600b1841c1d1251440c00c07201e00210742c2400e1407501140705030302d42006a0f83c1c82e0900041203400f40303600440c40756100d15046004004042000f000701011f0311a40040e0303512001d41498901c91900c540303009488241403120b010303507090711807601c0740d000510034084188030f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71460379 1250 71459129 71459131
    0xf120203040b01121b290f070206070f050a24060828080307110f0601060c06020703180f06030e16140109080304080d090605090117061201020705010e0f1c08 69
    0x1038a60035074001c581c005c0c0e0780c0000140754049002c0540c050143d1a1042d91582c41c051290261060355140100644030a8058015200064801c24002c1920018881c1030300d0503080d459800400d03988000e038503250890042503202001681d407140080000c00220305032003071030305442c9594001d02600d07003624401d05a145410001038000ca50152500e80051040b80c09140510041e46403481190810300d016842d01920201c0d03841e10794010320040000682048640c20095004074015076038038590f080544a03502c41c80d0070501c40f02c1c83c1420029480c0a040542c405603170f07080d94140301071402581c80f00d03903039401d50183c000c4004070714904004104000c400a0b81c015410b0520060455a80805d50b040d6001a8030680040d0070404000b01469400078490f0050411401d105080180800000b02007450042214504400103404182c0a82e109103811541222000096546071602c3c9042c2c0d000c0e080d0b607901e0312600c0c8078810803201c4038400070135840101e4034140540c030400d42c0740c03000469036a44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 71461629 1250 71460379 71460383
    0x1080604050a0605042a08010605090603071b03020106050f100918062601051602030304150608010c0207030c1d0c090609060304050604020a0614090105031909030f120203040b0112 79
    0x16030f81000042d0754886028140c1d070b4512001c48060084c180821100500d40c150000104002c040c0c2e00601c031040d000010b41c0c1c0580c0003038a03026140d95039250103490580115000034425145c14901c00308156054000c5400d840003a104000c0c40400503040c4003d4005075081d04001c00c003840c10610803440903501c1c0034a41800b00c10701040c0e940e541c141d0043d203020807011003004030942000a0101750000d0083c45d0b0002c4030303040521064079500100940f03a0002800c0204044108071315611580000c1e0401006130903030394001c0040e103040980181d47e4410610040b902030341d44000004059002e00d40b40800180800c4203a2410ba558500c00c4006034000040a60f02640910400700716450380d001035441244a1401000d682c1031600402c141148690300100401c40c100c1e06030010132407040e0503030361a954282400340c1c41391242d11002d4001c1c00b882d1602d002c1e0611b44100e800906030710082c4a6000000d0381c480c40600030708200d01c40107a1104641c050003a41c08900100050074501001c013800354 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 71462879 1250 71461629 71461631
    0x3060902040f1e052e050f07060e0f030a11060901020f0a081308180102010e0a020303090409020607050307060615021212040602090a0803030114030f12070218091006080c01080604050a 81
    0x544820024001110b40d042140f1018070140d2403860301200c13840c94280010450814a003090000c590847d464844c0c2c4100415064a408a24141038000c100261548585c2030903651509412000182320006401d001c0980340700700c2012a122a8040c82228082e140f049840ea00e0080c4542d01543c0181014080042e0741c1c41e015000000b084a103805400340d00c00368588914141c1d00c0ca0002400d5500940801c0e1503600030f80c46110043e0b46c00001c03601c6c03018007950003042c024040c0c000600700b0b0007140c6018002d40000518a13080000030b0380314000360383e0315600008a804400904a03581c0f04c00b0441012000020851500003003604009258031500c81c000c0503250150680100703200c01080e40c0200050382c0084014800c148140c080400b41c050700760018216040d8051034260f441c5958250300e03404100001e42e200554807402d114840ca9854003e102880e41400c5081940d43c030030318100410000e162203c045020b240209900000c402c059503902d149880310800c01c0000c1001410340740d016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 71464129 1250 71462879 71462939
    0x307050d0207110112021201140f06030a0c020f030a021b06091002010618090209160e2106010b0f030f06060412050303040213020f070305070218010b030703060902040f 74
    0x200c199070006101c034502c1040c14200c42a5500300141c244803503c0824440c07580107000840c1d0f84003000211a0442d10303101a0520f140b450746022550312250120740a4122800000b0401582403d40001400044a5003141c1c4200d8461024a8030b86c016594000010380052190700c030f11080c2c28102054885c8010718040c50311300c0f02000107100850318498000580d4484c030041007902d03510000410b2048002100340300c0c0f000b055000030941c0800030034401c101c01e140d040c01080c582c410319040c0c2101e02c0203020314402200da0b20f085064918601c10f5664540705000021442ca04c50301d05441e10b000d80070714040e003180c0703c005120754901d0009180d1038100c007080c0000262070444401c00002e035405000134641e2810640180102d000750500ca04203402d0042100004d40700c0c0d1340040711403494240c0b4001d13860301028030020b480392141030605d41e401400341c0004154901401d00841c001c00894800b000300701e0752205c03540140d0103188074004c00c54038410746c100855121402c06d6081c6202c505d12000d05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 71465379 1250 71464129 71464147
    0xa060221071a0702060f060603070507030513050a1701051b0414030f0d0314060d05060f04060b0612010501030f0b010e1212031003120e0d060e01090506040b15090603070b030705 78
    0xba25411110740e0010f0b0b00a4080c40024005440002e402c41e4094400c1c510314a003054014040344220907004040100c005a001c40d4450bd00341d510010b05001050390322901d42c4c1d5a1064954520b400b5006015460b000102d82c40700c0d024100044c90418180c2c0b00b505140c035005542d200303002c02240890305030180c10000c4a801c64103000e406460041e0340c4001601c0b480601e111514010b0081509001d40000c24140c804107038001508c40c0e22040e502d07010074099a491400e08007800c0d00c1e0a00303a40240780841c4046080420260180c181c5000380d800300512551a030700141a6400600341602082c00505d0040c01424410602000c130003a200450700f044814565004955100300c41515511030b030840140304209409545400b4500b0b6494a0100203189400088141404c0c1170014055580c8000c20322000d5002c4d003100f520b03260004142c0e4003919042c10605041c4404803426244800144000302c09071801c000035600856014000f0403010381441c400510b2980090001d01c1401004e03c407400c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 71466629 1250 71465379 71465423
    0xa05060a02031905031b040308071716030504050f040510031e021c0309150f08040303060e100306050a18060507171510030507020a02040b1314060a06022107 69
    0x19511001c4d0349050762450100d00480c10400d00c0003500c14404010801000810f0080080d24001908440d01e000320716500c1591944504c02d4080d00000c0b40c7c000b00d0300000340364001d400341044800564403d002c000340b200410040f43c000b10307444401c82040319070a2021808640411441c4110215050b01c001c0f01c940000b20760140701c1d0032130002810741c640c05004140d8404265001011510003000003910a040d001d00310f0541d0a00740420480c440700020145446074110b0401402840703240c050341c1c00e251001040d0714503640416208507040801107540090706200b030483c6807282000c1d207034030b0310300780c0e600c80c030188c40040c0c01001000101401070798400741c0700b400c1c0c41c081d440946045420141c1c0000348029138075141c54602c00c0c90319207803c10140c99008603590f41d40c40d50403a40012190002ca00281018031600031990801b440c050f0f68a0304124400040d03030080000300d881003415607890800b02d942c2d8824003403c0c0903200002c01e41c1c29013828220090052039110b400e003c43c5030032410803484 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 71467879 1250 71466629 71466667
    0xf0302101508010f0b0a090b0609100f03110f040506301e07080408091210020a03060e0601020304050904080c01020f030a0f06060f0f020f06040f150203060a05060a0203 74
    0x107031111804020050102c092007000030b04d05411a051000103205030002c0e9000b01203100f1510801d03203407881000d19560340c1d0200c54075000b0043c21005a60405040100f82280c408002008a450b000c8116100802c400c2a1602c8000704100c0131f25060070401404401c0d00503600c2c0020703080c410140100100f503e289005d0b22106494200c20705480e20710701d15111112140c402c40c050451707c0080c01112503008a181b83d00641042c1050303038954100780071900000c0403508440e07450081416001e14001d0301c0c0c00804541c007056505000540c2c840e9000ca280d880292103040c003692003004200400c0c1440305159a00900172100d903810049e2030380d105800c1e030744448000e44416800008203c84610359200d040c50034444000104012814524054006401d40c0d1030081407081c0f049014003943d100b000500442210b0301c1c203659503400c2510301b100c003000305204100d8889072000d01050241d0308034030981c0d204d104000c1003424080d26101c20702100c0c0d84556480c4003140800c1040090070012510301c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 71469129 1250 71467879 71467901
    0xb04080a03080f060904020105180a080607180e130203030c010204030b060103060905070c020108090a1b03030305071103041a0706050f0a0f02070b06040507020106030c0603050f010e07020a0f030210 87
    0x94400c2010a2500505040000f002900c1d00d010b103005210b25903c80c854403942c89030342802d1459440b900802c0d1240e5820b05196003541c03140c543c41000c1400d050100d07913940201d1181d1a070100c031000030b45004a408180d4042d0400c03020303070302d0300040f0030f00e443d200d62281d02800503040e03a00d810006424030313099034050f400a841100c50300c8140041c40d64544642d4000300120305081220703003003400e0000d0125600b450013038108490000403170681c034000d000489841e6480102d84404010303101101d404c0f110188015000300346094006081c5c9405181d004004820740300180d850300b420170410030b0001498800600f030071541400042c00084952041602403400302181e000503143c429060401d4400c04034400403130500600034500011210320a06030003680c201c03404280c5030380d26141240146515440a1700882d4280c000184c072582552105001c0c03580c44070b070101d9503a20386050002e10078003603d41da001640042000070103e86a02450b200749486881503c548003200c80910042e98018980 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 71470379 1250 71469129 71469133
    0x20a0305060a06050108010603090b1513020c070e0c04030f0f0602040315020705013b0f120a020106080606010503070c03030b0909010f0b180f0403030609020a0302070506060901180c02070b0408 85
    0x1303110741d60700030020701c1c01070006182c10b000c54042980d841010a601030072441c0c440b0100e007403c0307401d0340e603400385950a41681482191504000101695620324500c108001d00c800c000114030312400f408219401d4981003049000016900d58070740c504040a41d00c20380d040760742484040000740000c0c0044510000403040940ca49449081060868810000045c0400f61005205c001303014941c0301148030f04034001050b10050341c1c0003000d80c01e1070740c0740c940301405000d00a4441d54424420f4003500642181d58020001192101243c40e5500d03800c3d15103038045a401d20004150758421a00078080510078600883d00a4020b4045114000251001203030750351106c240c81146089072003241e010a808071003078007440254000c1c1060280016140c9490041d1900005003854005d8006e90010f10790444115030740c0303032a500c5c014000d40050004540301c3c0079580208000d0b00d041c164542c185c80101d101021000840c1020700c00800d01003213a40198050924005100d5400c0005400203002d0940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 71471629 1250 71470379 71470391
    0x70602040f0810141f080312041e0302030403020d08070210020c0112140408070c0806040809040c02010c0e091f090903021501060f12024b0313020a0305060a 69
    0x1001c0350074420844070f107000b118071380315440302042111084580c00074014017604000e00101c0d55045020411604941d495205c0001d00d01341c450704410015214601451804544c5400094020010a0003040c044c0050303006105c20320151411440d0041441e11507410a0300d0000b0300d43c08640245c610149540250704110024280c2d542c1002e103107c2c442a10342410858070707000c01d12580001d071002e04068528240840c9100c10060341024100180c01000704442c00c918061074000516070000d81841d0090b0b0030020208030342d9005000b5a0101f08260700c401c01704540c070000340060b254000b886494150000ca0f040882c1c21030800309800a0304402c080800e2010880c10081e03c2d02c00551000e140358641080100310485c3e00601c1802a00e8003854140103200301400c0090190155107c1d895044211010030f200c8035403041c0b038190102e201034565881034910000d220710a4445114801420b01080000034804008544640034a9100901d503204180d204c0d140d0034a011000c4030300401c42c9950310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 71472879 1250 71471629 71471639
    0xc03050103200d080306041409030307030b06041202010309060b040c080435030c1b0313050303130b090307030f081215010c1407030210030605131103011a070602040f 73
    0x5442e030080c1c1d101c0784040c410848810110380000604030014020030000b1012800c41ea0321600b008201500400384807a103414a01c482c3c40c0c40b68810b480280c042403500114846034203003541542d0454480a202a0111805800550240a1009041701e02e00ea41c1c180011065030b69100d600080300c20342e80c0f00080c1e46001e250040f1140b0001116510a070f800700108103407950b6501d0803091925201c03807800d0303c9440e50441034560b405507005260204132490099000500000003501d284410782219032032440d0342d5010306841e40310b850075000154104540370f01c42526840700410540707201500300d81d034071a0380340c80f420310380c4002403011220103200085140c440f0703d908074883c0d004051103112494080000d00040c080b214240c02c0100360003081203072107000c00410b2042e4001960040d000025940811000030300400b041c3c05041d106003d0000c2c03903400309809102d480500d0941e002c0c04d910710703401c220800d04000c400c03c094400700c000800018000070b980340041d00040aa003420001c10078108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71474129 1250 71472879 71472893
    0xc02030d05010807081c05091c0303050f0c0a050c07091130070804020103090209040506090f010504051504022101020d0c0f020d030509070b1308250b0f0d0c03050103 73
    0x107900c04006540051018400e80102203002c00c881038541d0b0026040032a42c401c00e88072401070b4008140c0c000207520240000d0800340000b46400ca00c2b82e94100201e940e2064140c140303460035540c0e45089a018468155560301500c001d04a4000301022290416902d0410701d0035502302c041c00014102020881c1d8180440105506806c0403681800200000f060300308210390807402000c02040042c940003080079a4000e60010030155005402001c541c60507091442c0c1e1410140c48000081c4500340d89a5100c1c81d042c4035090240c2d61000150500000341c50b80381089600207401681c0c89203000321341c0c4180f0b01e5009180743c0d2004181d4000760f00e69004a210310222160b80a0290500846000c0f0b40313140d66002c02c02c201c0541d42800c1c0060075884203a10989010720540003100c0100f000103030041c0e042d201d100440c0860704044100c1ea4600c0450054442086840905803900c41c2606c109000f840242d1000c0c041000700000103130304152030b0145440550340b4100100d40800c0e95200148148805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 71475379 1250 71474129 71474131
    0x150a20120313022e0e0a08060406050702070807030228050306130209010b040501080a0c0e100201151203050304080309010b060a0c03020622020609040f0504051e0706050301180f0c02030d05 83
    0x8080b6100c0215013104d104a80c06800c20a180104134402c103030b180d0700c1d50310941d680c006081c491003101c0c2c880c5080d1410300c0041c001503c801025100315403000905441c001480426a0340c0a850b5040b68030030313440b68843d5010000071001700b403c000400449c15850401071039200e201c051941c04400c0513076005104c03c102040c7c00c0084903000c00c000078003c60b41c0124407260845c0c0380c00000680f880f801c450403a101d14580415680c45418488064401981500861601c0750500e1003c1005c550758841084c0c40850450010003141003070000a0100c0c01704400b85611180910000c42d840c0f103074100241e09541b00d42107540105181d800e1a405150341084066403240708103c2c0c856025140b10030720840c4081031800244a01400140d0300c001e03484540259200b20b0400d04140940d00f03040c546261610040b1860000c03548038038044c1e5081d034100092810854511380c4030342c0e01c3c5034204003400d07000798207403e1100855500d500d03030003030754207240d1040320400c95490707020319210f1079001580c4098400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 71476629 1250 71475379 71475409
    0x507030c0b120711210705070f030201021e070f030f0b06010e01090b070f06020d0c022b030b060c07090501181e0c09030605010303020606150a2012031302 68
    0x802880300c40550301d210745403280c2201c11030502d412600240900c0c5890003d42240c0d00742c1140039038013284038100300b02021b405007921035070550b41d802d030b16660a0000c214851001078010381c841940d85034003072941a4200d085084420544010344d44404002540a600390702c112126124426118148062029031513008502481c01088080203900024a48030140c003981109290000741001000307402200d0104042c1d000100359201c501707480154000305100d031440d01c050f000390a62480402d0390030480c41c080c6071f820381c8490382003074000004400070306a0148103504114208640c1c039041504114410040540050108a9604142c181040c907041e80b120850307014100340c031711034903004000c7c0d5048120040c2000043e004502072030484031484180d10181940386014000b000f4590301061044c403d0a0070348444880c501d02c5582d042d50b07441141c074201e000a00143c004440000d4a440d0140700008840c00c8070030401200058012039441070f910040c14032049880c101c11802c2c150700c030120b000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 71477879 1250 71476629 71476649
    0xf0f1101020615100908011506180e0a0c0c020402031005010e1c08090103060b040602011415130b030c180103110d0803010b0d02040306050a020a14030108070603020304050a02030a0507030c 83
    0x205083c040c5060030074908103030611610b102d1203070700500e41c800d608901c001d01c2c0140c000c0c0901d240d0410012800031081c0598400100034000750900500b10884000480d00c030ba247c0e04040350342d400303004401000428400002c1105801d40c4c00c2c05030b91a800a58015151001001032813854203002501e0080c1148145000da03034000c16403440702200e480709240032600310103403503521502c6500413002024190041e01c8854404140414480c0e0305511409400200f031a0340e13407154807041104002820b0f402c032480d40c400c12065500f40c41c10786a070082030300802c01504450001b216000007484e0904c4e00400b040b200c03540b21004005104500750100000743c001e65515040030b00c41d80b41d0143c5440705029182074100c000898003141030b12541114011a04a0303010083c905122840c0d00281d4400900040080c409010561075040350808030781c103c0d11800014032100340b0b00361080d0040d42000b0f000752114006c1c82d00c140c000d40c030144624103185208901a1644505500e0710400c44030b6943c108468403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 71479129 1250 71477879 71477881
    0x11010c08090c0103050402041d0703030206070509101215140f04050c030402090c070f1a070f09140f0405040602190306050102070513090507080105070f0206090703021c0f0f11010206 80
    0x9540d001c5081c064440080c60301140b19546c900114001d0807009007004190030b001e2600000b0508042200e50580c3c1c40fa078296581502e44160031035090140d9140603900280d215100e41c2483d006840d4103003080c4400d000800c20292122804000600d20b500100c0c0e0750030091401051444c0c8150340c0c03140c8403422541001a401c2040d170244103800010002402200600082001d0381002d9013503400342e50384114a01e22000003031403c0c01c401c3c4d41286442483e4034800c008103403494080c4200000c841c56503aa8149154a4120210304454505080035003040c03101020503241e84460140d684168000c120240c1c1c0e03501002c15507111010326418001c2011710f011004d100d6aa4040384001c01c07180200c1325071224019000038807000744041c80c030050062140c07841c00104040e064100c00d1141081e526131070500203450b141681c6458044a45100340e80090f9000d000600c0c100c54002d448880c0d4011225524900e40d03640d03da020b00b880c034240d40c140515101c4c1406c101041a5403100d40b0820f03c041e10007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 71480379 1250 71479129 71479141
    0x9060501080f01031403040b16060501050108040314090103020f070606060806120a0210050c01090c030b0601170a05180307050c0406050a06120f020d060f0504050901020c032209090311010c08 84
    0x4410060000034441c031a03000c820712117898100103035806085100c002a84e0380800b5410080854125002202e5a60501000140740e40c007031601c25100303c0d0144c644401341518007040c101d031648040d880070305040d400e1000c00750b5a081103015129444c4602c3d0001000c07401e01c00702600000005001c60311540e10703e0068052144c01240c90308440340c0c16103894003034200d1000181d405004113119000d1030740c6022452014041c2200f0b0302412a0300030302086049490340704c011114250084940e81d08586070802007a44401c071541703d19030280030b00c5a001e45402030001950b0459204210030340b103e07401a20201f195140c18031072040100021070301c0136411450210050f0150f08001c408508880c0e44010703000032840a40c040b070f00c01500d000e10403c0310a072200b00c145402c8660f40904e500551804000822120b41407003158203141100005504081900310f100013450291107500002410701040040c00300c500380200000f440c429160f48803c2d0756401d000c982181d8020300200e040180316414051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 71481629 1250 71480379 71480401
    0x60b090108030d0b040f0908070309060201151a0409050c0c1207030e01180902030123030a020312070501090c09050a0b0f0a05120c030a12020706090e010b1b160906050108 75
    0x1c0c414805020101d100c131039010000700148540100c40d0181420200600104004400144400341c400e4590102e929280c1000301d08880c8101d0701c2011103442905c0a004c0c00000d1b0400d00d100d9842802454034080e290882c800c1551020769011340703801c90100d800b0740c0075503003400403041038900c44500c0c82c1052516207000f01452403150b060341c18014440e030841407045007402540058005890b0541d6256914001c100c41406c40354841c407110310451a40405619010441040300d82d001001800d488140c241050f00c680d00c540300c11a00c1c1d41d42c13403840800103203001807450010400000005094a800113542098550b174500e114810341c042c0450000568074003011005980302900c0240c4d00c80f155040244c9000041a000d645c54810b00c0d80712030400c803103062800d100c0c22355603083d00c10a641d10030017529100241d00419410f2a109001403240f151004041c03d907080ea210600c00c00702964694071030410f03000c628a400050030300d403014440c0d086a4001c0ba0000d010a107400000c44c6002d0071420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 71482879 1250 71481629 71481637
    0x6020d080708092a1507020904140a0c03050a031e0807031e050108070617040302070e041505040c0f0b0a08011703090303040b0408010606140a0804020a0b0408010207060b09010803 79
    0x4002e00c0703102c03070101d0320044080220042da80360489000000c80d5907103090044070849559070510a502c5101106041c1c403000c01681c2c42140c0c00740c4180c0783c680341c558079000d0f280a00d004802091007192820b40100d5500700c9248002c40c000e5024011100036401e008003503050358403441082d481702006a00c0c481e503200c00066405800e510300041c200001003480340c1c02c10810420300d1030310350030480003051405001c10010100c88080e183d41c65418142c052180e006d05003101c2c00b0300941c0140390104142451988459403143c45a100e0701d10403024000d0000407184140d6040c1c0352a0840c079000d200322194000518064020b10305914202400010014007680d014007035886d140c0d00302440400d22000400c1910450140101030343e0f00c5a464003d034091a800c41c1c41141d24540c240080091264002c1d00f080c81034501003070020f464148461000d071014070740680201e070000300c010000540060b281c2d003e40080c150340400540d9916076030602c00180c607600a005803080c0c407803900401008000000310f03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 71484129 1250 71482879 71482891
    0x9020d0f030e0604170f01060e010b03070309080703030f0c03052205030d02030708041b030818120607020c0f030607020c0907030b03060106031d010b090606070204020c010f0902090106020d08 84
    0x3910400805160444640e0269181160489008240410381841030342c19040e51421120443d0003495400808038241c032114481d00411500c000018000c6111f0703940150b900c05050300740419145220f07038a0b04025407203060141e00103039541c80d1200c540403240c002c1d034904024500d0140070178203102c040706034003250384122003400340e4641c10038000304002801038030800c036003101003103440b803401070b102070a41d07a811101203e85400700c007418043c0e400550122010b40b034000500c076051405a902c06008020309803007050303000560508011090a04015092080340c450f409033040f00800c0090007040c0d018041d04ca44241c01090800c0301c0b069001030201840c400440c0c4000030ba44070180190000d05603070709655014011070b80003140300751300344d000041c2d10995100a40d900000c192011822100c08121181c0c0c441d41e0400440c41a10b0410b020f0b04003580004c1c4018506110078031082d003101c060381320b6211443d866552030811b45c60300c4070300b01e07004041d640040c050890800038000e101e05001044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 71485379 1250 71484129 71484143
    0x610090f23030109050c030d2c0409020907090512030301051c0c030c06020d2d0f020102041806031b08120a0e060c011a040902030a020d02010201111206040f09020d 72
    0x9a8500c00341c0307604044586100c00b90081242d00400e041c01c070345515481140601921800791150b110520400005c80f031501d58200341504500d580303448101c0302041241032640320303488098a40c0503a03100344c0700501400d0142c646011382864541032001d80e8a049010600700d420070300c010403003a221034807002c0d4045511602e010318004e035171800c0d00078101283c0000c1c003000040c071808100960000791004254800d034070340300354081c40a200112090520602d03440c440580b210070b800306600909050a070000b945c0005800d00361a04504c080605000740c5100e640c648500c000c00622802c40740840040020000c07001116040104c0c0303540c3c902c9469002139015500042c080c82c0c2c3d92003001100350000004000301e035128844000c95020b00b8209030508600d1400a15016192420344642e4500aa0141c080c0c102d55806800708020f111140c0e000ba030555481d101611601c005440003091149401c4800880c107040010a0008030340080032160b150034540b42802c00583e1300d500c40741038000c0e80b0001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 71486629 1250 71485379 71485409
    0x5100c02060702150409050114040e1504050319031b0302030907120812130b0106090f030314040807080307050609060f010b07030c02060307090302030105060a0b07030f05040b040b030610090f 84
    0x804078004c0340402807400c3c41810089404200019140c0080e07040318245205000110980e2081100b1195083c582d255207a00a100e44203400c0150203840303070300c5070144081e60f0801d000904603091007880c40503c1d500003951f9800e002c00c0c1840c518021010f010b03482c6011403c40c5040e1030866600c06003801200e0411302d09100741303070421036908115070600f00501255090f505041071601c40e0100c0c500d004403650700c00c40300081405d510865403501100c81000c003c0f25601e00d10744090300c00da4064641a00d01c10030400002c580031904209000c000d10b0717400020344e6140c0c6903041c1f00b800c200c00505000c14681024007807080065010902506440001c620b80340c3d190441d244c1a9a0a07401020094001d80040b081010b0b1903003142e05001100c2c002d40003800705a0b240d008020010381d41c0e0203180310344141840910046032003280d070455110030f203091491405449181d10803058010b607101c0000301c5800070410259041100340074400001c0e900700581e440d4201015440d03091143d000301d40c034802040b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 71487879 1250 71486629 71486633
    0x50f071d0301020d091109160c020f0904050f0610180b030c0904060506030d03050c0a05070201111c030c0806030a0209060301021309020307030c180603090f06140a050105100c020607 80
    0x49608018a03000030001c6584501540c5070302d014200e00314090b1072210840030004c80d1800c020170303051710486403d070404011008024080e502114003c0b401d80c0c210300300c0003a0200030340304c00c0b210b2070185000344002e02d0b844204075400f51500c64010a000122a500c05c3e08000e0b00201160000c01110081004a20425407402192600e810440560f60180e1031005000a2256a1780b00c01d0103400c05500355501c5007a0f5a03020b8043d1041600c407140d0700d00d810805c109026109401415203184140351004a0134095142d01d0315021008030018090b803111100d4010301a05840380940518407403c21800501d4003500003900c070000e8100107401402040000f41d207541d000e60460701811400522644501e80340d002e4a8002c0d0412540c40f00402e01d07241d13000c40e003a030040b1203a00000c00c111700401002400c1c940c2c12005000c1c40d200c1124104000110341001854502650307048200004451441e494041c041e0420390708181d00440c01250520313554001d09901c000443c1242d50140c500303a070750382c2c118 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 71489129 1250 71487879 71487917
    0x4030f11040207120e120304051509040b1002030c06060d05060a0f020f0a020c0f010203091f0207030f1505061507110a08070f060e0603011818080406031509050f07 72
    0x200d0b41c01030818221210490900d50013060980013083e0554243c003444a050400a589200d42d009c1c85078840c030130043c43c81d16030601000070031b03010f50040d0011696226a80118100030b0ac1110190f015030400319105140700020454950b20040c100c0f5110900c2313813103031107154440c000500b004a255480d01d880c00b080359210380450b00b503150210001075440c03a40303800c0251941920b01c00341f0f2203a01c0070080e6114940c800070035500902001000c4032600c01c0010241201000740704820019401450800008100341702464a4440c4c040c10007024021640c614000480b00001c1c03200d4403503106880c070381c000110409c0a64110603400320b001c150078040c940018902100c00d40c000d00003481114004600000780800240c110b41c4982c0750b1681402c4040100080c5000c2409240d001c22411110780564180c250400c80205c4404034080e020292540c4072003480303030701c15040440402d48a01600c59200900000c02c4002c1505802c2003100f81021100ea1004003006001601041600b4004021082d15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 71490379 1250 71489129 71489137
    0x4140a020915011101020a0912030210111801020d1b0c080a030504061409060d09150510080c01020c03033a14070c05060f0c250b060604030f110402 65
    0x200419010700e4080c0c0200c403802c800c0c0001c01c1c0010381455012014070f00500030b4800022040d2100d021490030314101c503503101c08600040e011480780c1410740403092087d1082c0500c0360900040c407a0341e084002c0000ca0030801e10404c0c02e0440d4003804480c120700703a2060b0540c91410007003441c045055030a060083c02d09240343c00c0510b07503001d02c3d0b01c0c1200b015002030003841102c0c8103850701d481c0300c884100502042d0080407592600b010b4100414400c000301980b0801d0303100d126074610f2544213001840b84080f9801111b80580c003200030791050040520810070360364160024401460050105800b00b601c90040c039184020f03e844445000c8133450708540034080c200401c010700034040800032181c50291410303091241840140c1400324001a10880c2c1c00d00e21030750020b004059170380700d0368003046110714024503140c0021002d000380a98040c80b000700103010600a48035504201a908150000702400f9042e54811207080208100080703a03400c4490a0307581042c41104a0080240820040d2007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 71491629 1250 71490379 71490383
    0x140703050102030f0a1512060c05040803030907090608190602030c09030d0905041407080f090106170a12030e0d030908070c0e0910061a0f09030a0822050904140a 71
    0x10020041048800940301820b201740d50b038500900c2407001030000f91103401c0450207180ca11000900c08503000c00c1541e00700110f07420b0140740c0285441d554081c3c00d0308541094803001c4082d00010400c00a03404e49001d000060820b04c0081c001c0e00b041d41c1300d4803400b054418001006150044006a03446a80d20700384c48240d140681a00c81076484604018205a02c038003a90b44254a4803560404005058036058400e1300d544d2104075035520b61210200f6400d00c0104198529901c1c1c01020030740504003040c5076001c4503500700030040f0061b02c0c50500d240a0240300c44c10101484d00014114004000440002036002030500090718000d41c20311651622540102030310701e80d01800c0c0010306400c50442d1310b2003030704040705680411400d01429816640544180c082e00040c441440b44101500740c020300c485045074824519290f8400d01085c2840c94441c1c0603104400d011840c2205140c0b40c1410501078241c9802554456040100040c1501d00181011303010898042101003404802c005001000c2d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 71492879 1250 71491629 71491631
    0x1005150f0a030b0414011b050313060605060d2a05090907021011090306070f050405040c12060f0501120207031b060e0a050c011205090a0206072f011e0206041407030501 74
    0x21609003006403106865450321710280d841c0504400703c251804070314000c0c035035450f9291451500d4140d02d940c03124640480580b0500d1f40c400c00001c0a56400c401020304c822001404100c0e04602c2010143c000c088600380d040c40003410f41c0e00c241840c0d100080703a00060045031103101300d80325680c0883c07812074455000d414052400102c2d0141c0c13070101016002070102103085030751507a80d8540498405241b9610100820414402401540b620b0740102c1c1003001c1a01d07050325080c003100c41110940e002940140b18149401c1d00a00c46964001c62240250080b100e007503141150550b40101440e0120706607400c0f8111244114041203040d070800082c003103a5070115100c200640c14419280d10404007128041180c1d000407800001c942d0007800d00c2200c0300c0018102e60074083d0240141c42c1c1c0910001c448600301840c44200b4021110212400507400c242c0d0280070708800400034206e05a500c01c15902c1c4101032007203940132a80000d01c0e0364020b40c04400180082d4215034207914080071500001e04c19 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 71494129 1250 71492879 71492881
    0x6080705100203070b0a1d060a0c02060c04030804061805060d0e070f0b0306040e03210105100309080a0e150f03060f0d020d03140d0614031005150f0a030b 68
    0x4450001054400d440084480704041074031a04142e07640d21991800400c1d4289000016030b00c9242e607407000300e0f40b0396a9030081f40c481d205206014104181210080d5a290ba944080c18100d50b041002c550b01c80c200480840c5001e0440e240d081150042c5c1c8250300030001c0c18046151021a00203109008107030103402e15071a03a2042284002400c5d501c0c8940c0440d1061040005402078020000c10864118890051554a900b0140310183c8412a081b9610784001c110700409004940028000201c1209544130103504040c00c00080741da13400711005c1010b0600022402003501c24003118250314517030800c0034600ca000000b04a00544180d0307850406000032560fa04040c101700015403040d2001c60b000000c000c014000c200d004051404d020350810f003890038440012b400b4185075103d03805c102141e1340c14180707100342400c00e440e02600400d1034600e1011501c86682400c028250450b60203c4041c0300030324188900c160202e07000d440303080c0b00d4524114801059114907034200061a049901000f003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 71495379 1250 71494129 71494139
    0x1818090105040b09010b0a0308070c1d01092004050409050a021f0306050d050721050607050910170c070204090c080f10020903070308030603030c0105010314010b03010501080c2206 79
    0x2007400322020b0381c032103035440001000c00c14103224040c070b9800c004000d0f9001d60f040da104c42e1000d030041d000440c2c81e031100410100f80000d03c2d0300701c94921034124070403940c5981010040307802c2e19140583c0c4240c01404490340803846080740113550941e00141e1340014102c0c014105146088480d18000c0d4000407103010b44400e181100e10348028641d407503102400160ba032202401000007040b007018103582c000001c14000050030408081500c45c041c4410b000701e480036100d40d810200103507580d001062001550890606003210028050810327802d0185102c0071600040380c0d4550000c009520240c2c0000b5120110750b0349e91311229200341c000f101017542c1a214688241e90f043c41c40248200e03031050f0004c43c922214107000f194601301015000d410003a1955840381601d070005020f459040c0800d12043c02c110000b445114021400f4071035890351008010189421107560168083c000e03410400107224860000503921580c40040d02e8103180d200881004100400010300210300d103a0600f980012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 71496629 1250 71495379 71495381
    0x3110603130609051e0f031b0a0501111201141e1c12080903031e060a0b180f0303090a0302091005090c0d0f020306010f0309030509040606050c160b18180901 69
    0xc2c000912204644400c0c45c0700400c9540f01c0004c21201d4056004106c20b1000c0810940310311844800301d0101d5206014695907503081d245080c3c880040d40c10b0204007250105140c0140c0760040104c1000c8520f00c512182c040785c2c0c01400d0000c50390741420564103090803500d50b0345a0f50381c040b0502580c0e4450070024a041d04003007400c28a4030740050412404650a00310100c110b80c0900c80c56440c1c40b8088134404060288100001c2000b9440a0006400103107a0305040c000d2503240621107070070043c064808100400e00301c5c03500d9101d000794010b2003000c0140e107408042400341c0b501114112140d076a040000640401c5a8100075049000c1909101200c1c410102601c00000d4010b07007031140c1002010003070101d001c00c50351140000c24400140c01442e01960120659500a18000d0702e03000c42c0b4408101950840d074402000600b001580310340c50b100510036030700180c0c109420101e030180391505400c04c9008503204551107900c0340b00d05d5510396803500440000c00e90740c1c07a00264589000c00d4228 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 71497879 1250 71496629 71496643
    0x91f030804090e010b06190207051f020106061e0e04090f0308010303030f0513030f0201150807050312030c04031e061a040b010c020a1806050a030602070311070311060313060905 78
    0x32144505010348010043c1042c0030b654240314025007450b003801991725690031210f03031190030392003075001d05c0001044036220b0084842e01003100f9502118522040140242100c116602c13003000c02031035055403400e01e0980c000340d0200e110706113004001d88084c0300000d0000c0c1140070000b40741d100c08103203803001c1640014805040300d0190310f0400030708000c00c40100070303507004581c40b03035185480090520000f0b01440c0c0000b1a1a0540300001c0d520750704450709071721036901d80c21072900ca51083c90100490f1404010f1064642400b104150550501c0304280209000c0d500009210300d0100301c5404031120288001c00030242c02460500140503220700c01d0b0116011201d04501541c10a442004194051040710f04c0f00390340600513034842c51a210800180200307007180f107040c071a01c41400142c81d9a6004450000d18050b03040141d9611035413030064003600030072030542e8258100150400c0454900100002c00020a848031652070355001e140e51030800840c00c0040c9000d20700340d80303035089c00780000e002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 71499129 1250 71497879 71497889
    0xf1505150403050604060203040f0b250c050c04090f0b010623070308011401020f011d0d021603060b120102030a090209010602070b0712020f0601030605040b0109110702091f030804 79
    0x908403000103040485041c1c03103580009000360313100c0f0000c580080c0141d402540c1c81030107102c01a50364507941d501c820301203d0aa07403c205403503d801941805aa20215071019880c031400d1250b10303285035940b000e8966504880715071145666014600c1801602010f40741540d50141d10b80c89a50785421010782482c04404103072a0081041c0b28501c2c0e00b00c1601c007190015501500c5041c51a80303001005600f503801e0a034042d0450055024941c1071343e0b800d000e1100b8040746001101c86d60790b08030048a00d040310720704003041198032941440002c0c0c030700404030f10183c0c0e0300500b000c289900d0000218041d41d01c800c0c1c0c20b40f015071000003008030000250303210300c00c1c46100301c0d41598240d0b61188202da490400340104107406000308001e00014955030030703c40e00304115005076500c603848910100d05150090748240c40040d121307030401040150600125002d065040010880101c403c000b1405074050104028080d5242d0400b090390210404181000b981c118120a01c00540307900d8005001d810521039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 71500379 1250 71499129 71499139
    0xa09050c100207060207170303061909020a08010e06010305011d0406020f0a111608070e040c050d14060a050f040326180106090501050904080d020c030d09030e090405030f0d0f1505 79
    0xc0440d08540501200c08961f203041d0040d8203544954003001810890200d00840310314104100241803545400900320480c15070301c550020398540500c080c2480002820705040510308001030051352089580c1000113050742031042c40070f41d124a4100001d104030304003a82000c3c004107110034110342c81001c0184007024801507805202c0650180e903402001d030701030f64406410890083c018101d00002c0c0c0daa01034014445503200c25a40d130040b40d20600c4190058584207824030880142c00c0d4100040c81d00000c9030002000a0300c0c00c03000f03160703541c0c5024000034100029000e0f03c2c0751400a50810117004882034182143ea418040c00d1b4a4040541c48020060380d424000009043c0041b449a203048a0300a802003240756160781e10358503154880369402d05003e6090041d03d48a510800c0076021401c0540800181e0041a08001c0e0a0030101d560030b520840f080e10030040040d04c04020307503c51030407121510361207910f5441b03100050654000d240101504e801d13804803031010700c45000d900300d44090755 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 71501629 1250 71500379 71500393
    0xc030509031e0f0a031e21060501110604031d03031207050318030c120a0215040606030b060603151e1503040314040f050d0f02042a03020a080a09050c1002070602 71
    0xc1e0035034030f50b030007450003901052403010074440903011001c01baa0314080ca807a110060012415021460340c400888018289079a9141800b807560040c800041400440c00145600d203007581d4001e050300c20140c0c0c5115031034104000310820341ca04000792403111000b52001540c905c0d09110050160300100c401e1240040c5442000c980898040300301c41c00c100d400409402c1d084201d02c0d036017502c1d80c003043c511021403103141c064a5103603024069443c002c0f0b1240e24041000383c0f440c1050450107001070155803250703000300b05100d246256251052404130090b03402036005183c0d80000340106450000c0c144d00049000000c5142031b180701c0c01948540d220391201c0d44501c0c989201240180110700500c80a0b06601d2814801d5103001000403445d1441500440484001036000c6801d0f18001c55001004140c07040e04a5030002107c0b511000c921024582181400d4011000500f10b10300504070111180e41c3d030308032409000c0180511082e04101502d00400f200c407042000f0365558a030320554006000d542 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 71502879 1250 71501629 71501653
    0xc0c05010912140702030c060f0c0d020a2010120b15091804050703030c080405100512090c01120902060d020307080a11310312030c02010f0b030a030c030509031e 71
    0x8420380b04d21980150003480f4007490b000500815502c0203d000c807547c1000c0c011885002c800b046207003040781c041d030302a0010801500c0c10209028403a286a6400d4640c90131940803a10341c10100b01d04000b043c60143e03822000404140c00420b6220209500545a99040030144800d40002c1200c0d00046d5018244026860311441e03108409440c000d060b07802840040010921800f03003206010b0092035030920701072b502c40014121324201d081040200b040803a41403601d0142c80e00c001e500c455140c020380802040342000824000f91207028800c810750303d02c0c2a10554031802d05542005491030707004c541d44c0c00c2c03074540680b8a00045508110082c03c0816000d00b4a80000c06d80316440001d40f43c2480d4a1803180500440142102511104020b840c40000c042408001c0f100038041c0c0030303180015101e8207200b009003075591407415180f00740e041c5003a02045460000b40b855000e0b40501c0c241101640c1481c1c121503078400d40d01c1076030f8141b042038246950160a012628100014042161648080c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 71504129 1250 71502879 71502917
    0x70b06010e011701120212070e010308030a060906030308010905090c01140a0c052409070308030a09030224091b0f0d0c0b03010801230609220b090102120903070f060c0c05010912 78
    0x49c0900522041c0c8200101b00180c150000b641d00090203603004035445807101c00000440300303654029000108903038010044090244512a0050500b401509003240040c0001e001d0b40d1003200928808000050040c18291107040f440e43c90903400700c01c0d541006842c0420340780301c0441c058449052007814001c00c000400000390003040f00d0b03026804a00b1a40c50351a48802814090000e07406d5005203004d889110000e14810034501c5400c0a02c08440d08000b08124a05194561008001c41d0141790030700b026951242c060b40b025500315541e241c0c2c81e6907850010f10100441c3d0182c1409171001c00045248a419040140b401c51607c00c22120000100800032900d0801c3e50825001086800495115885807036106100590f68000c0b481c411220394130541016800c85490318141d40c00310340c1d6030a54a010301426040507412004604200d01d50715038000c0f61880080041c000d035684c1901540c010b000b030840034162504040200403205c00307803c08100050381c0b008000c0010f8500843c0040c0307180c80d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 71505379 1250 71504129 71504143
    0x10206010e0c03040c050d050f0706020c010c02090a0605060a0906030b01050901050702040504021507030210060b1c020306040b12010f0f060b0702040203040609050f0a0b060105070b06010e011701120212 89
    0x359981d036400c1e44400c1d0040055520241040c0c0d2180c08a11010072543c503039a40c800c141c24400c00050000d0100e808003035041c80708075000300b011900a0445940c43d680d200840c49502c41c1c040303800c1e032403944038299810000c00c0c040e404290016804a51518140d4000340c2100445120b07031400c2c000b440d83d100045980d031040d0301e4400c2c0071400030720410001d8203003a404a0307405840035110320324480e0810350303004c0b0300d800c003136800c50040e8007080d200100c9071224012100100a400d103a03e060042e8141130484803c40d00c6841c26190303a0200000d0000d81d12500a01c041d918050b11003600f0b16071040c10755018100d2807500c5180c031414064080d45040203403003180c04841c0c12015107802c0c07a049030700304070103580094015510b82d6102e215860200b81c082c020002174001400c014a20b04c4468030b04283c16000003008241809000d0004202241204070740c507602410910346290f0784401a40143c45055900d0f000043d10b80d950000842c1d04009484100041e50003205c12540210f016942250340e040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 71506629 1250 71505379 71505389
    0xf060c03110d020d060803030127020403080a1209080304140114070e2403010b1207030504050303040618120203040f090b0a0501030b060c01020c0d031d0d08060112020d021801020601 80
    0x1500b00040c032482401c0c1d602429a691480001040040c0d5a020b0036103542c0080c1c2007440880344003070307141142c4819017040001c030b500713a56000d42c10203146482e1510b05007d007a002e40c0501c0060300c01c1c009091941d80c0b000b0b01d2a503002244903240d0905013000140d228100c200c0711121340c0313000e048406094445e0754191080103280d5920300c0039000e00050040e282c100440c0088441c410424810402c01b030f01c4013540c0a4030341071103000c0c2c44400b08034030381c048008081c000c08207052a14047c0004181d022040f02c0d0300540000b0081043d41407070120084075014650007824823903071100d04482e99503000c0000d00c2103800c1d0107032000b007030703503c0e00c40480846010f400001d500c0780000c01c0c1007100e0750103500208a1808010701d02030420528440141c00ea90000100e0800e81d080340c100000070a416128185181c00d48100903040d00c100c00380d82c0b50f80c4084a80c002018020300c48001212030788296140e104546020b4420754440c51143c440300d000e904480d8074102e405070a1030000310786501c0020154100e80c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 71507879 1250 71506629 71506661
    0x4081b010219030315080106031202011401060c170403020d0b0103030801050f09010311040204080a0308060a0e09060f0a0209060408010608060f0c04060e180903120a020405100e0d020d0f060c03 85
    0x4046943c042d801403002103040034210344001000900c5220a05c80d00d4010350040d54286100101c81a0084c2154a0001c1c000b005400400050203460342c4484081403466001a02c00076807941d06a81c0031450065034030007948828041c280c00200120412014101c80c46900c515419980301c0e010441c9038040752446039080000000102b020a01c1d4030f02c6001100c002910062901d510740c001c05041c40d003944000e8000c00da40d00144100d506060803105c3c000c110402d4045554101410181d4072008003500001484110b60003103503440920303a040729568000104885c0c0d03115501c07080c1601a00c0c8a01c80e41d415401400001110458000d461501c1440803842d107034905030070010280d60462030344d5082900b000201d4004112510850007150003031000000440c3c8520460800d2000080003c2c071085805005101c00c100940315a080520b41002034248810640b088402080c0c0300400d02e04080e50141d02d51140c403050002c4408150b00403030068405100b1031811403c103805075085404650340304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 71509129 1250 71507879 71507923
    0x60105030a080d0b0603070c0b0601090f0308070614090f01110f0306190801020409051602121911030a090602060708010303021b030a1b060207050910050603130804081b0102 76
    0x29542d180200002c0c0d042c1c050000711580d910b00401c005800c106c52110220b00ba490b002c5040c00011140d681d4410000d01c1c00c45413103800d1000d02e049800d40c80c8130043c100340c804150300c0c08005503500401e910780f06140c1c142c4d0003441c1c00001d881e0f0380c006501c064651075103050240303030706a52000200c4d41860024101186151511000e0210500ca0650541e801040c0701d071001c2108032080c00144010310380d143c000320301410945004540400040e44070300035540724001009855000303605490151541084080781c15110305c406840c01c142a175603aa015000000f5604d1071260008030040c2a50740c981e007161025961200c040c1c80c2c4060a00000e000b40c3c2c05092034940074840200c0c40070006801030b0585200f0000c0daaa9102c03041190007000459288000080c072004c1e0f0304100700d100500c400c6840c402c0e03e01700030b8400000c44205004080c000e00340000000ca4221041541080780c0d0303800b05078260380c4c1380d44070790307803921044007080702c684101741500340609075840001c10ba080f0800032001c041c50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 71510379 1250 71509129 71509133
    0xa0b010b032502010b0108070f09180906090506070306050a0e0a020f09060a0806010206090307170307031d030702190501120b04061d01080609010606081501020316140708060105030a 80
    0x1141c0009082d100b00500c5484000200744401c56204600620b540001c244000d0210024180400040900d01042180e40b1002e9030f40d83e01c61046000c446008603440c600740301070102417000e468908000703402d0354244484442003050010700107208240d155400c00105480d6010003802c80301e5803060505080d503a00c003080303850b48075900800301c6c417041040c10303460485208003203140e81c3c210032140030205135442c04000380303540c06100b820343c05000d200180d840d280c1d83d0b81e00c0d00024116a082c0c607003a0071020000500c0b0601a6000c03007044860219004046104200c072103541c2c0d0301100f0128011508002d50441c030044e5260300b0026648141c58001c281e240007a1070000800040d4000342d8400e4581400184041c002e40800c8044607000c06001c60b6036040c808000d1070000003420314a000d0317141c10b000b00113244e03018142c2030304030780e00300b00b8030f1000d50b81840101c6c5107009045030026201d400c619007008001030084041030402d04ca07002d64a5007a80d40c04459212002407180c84e4054020184000c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 71511629 1250 71510379 71510399
    0xe0402130e161509080d02070303031d16080f01090b0106030203100302060a020708010e0c09180a0503030a1a03010903210912030b09150a150516050d0f020a0b01 71
    0x8024203039001100d0302148603102122600d0701d40e6204074103c1140840c6042070079446030305880a407240400401282541010003544c90000d448003604050740c1d8684c031010540012126503440085800300c1d9154840801d0300701200140344201101845025036002500c00f060185c0315810b41c10040700a200e0b0b103410320a43c041c1d03000030700010b100c40c2502004030040e981c0d540030f400444032550080804c5801c00710030508643c20301c18040201d174046004241640e554400c2c06038040040103c0c2c1201c500c03440d05035403900450107801002c5000100800402e504283c0c048a00400d03600c10158080350803100340b50032103a10700c4c8080e000401001c0c03040e641c001007407191202d17180107400014180105440f241421562052400002a26403e501d6020718049001c2c64100c20910551a020380031080019021441d034418582120340b0305103640c1c1c2107801003041daa0901e0420f40400080c005502d00b2079100c0d8800308551010415820003401c80510004442c256254404040c064590034101c0c03100d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 71512879 1250 71511629 71511641
    0x403080a0506030a120f0e010e030607050a120203010303020a03090b0c070905070903020607060b090606030c07030305040c0e100810020c0717010e0d08010503070608060f01030506040e120c070e040213 88
    0xe4040c89001d0740e450014421985c1c8940800300ca0b40e41e441011410300c401055281420503e904005090380c2c030310540e982c0401c40030b03005007990a02070754a020103036042c0c6d0760320b10070715045d01e0084c800310000082c0358000c643d0140841c86661101d84880d00c520700603c1500483c81c619045500401302400503c09a80c0074540109090a03d102e03816030740c0d80003e00702e07488041e007102d6035500c940211a060030540007043c0c1020f000c03a4070b603044d46410800c1010034003039148040c0c105500c5002203020710070b00f9861600980940032801e051441d00401034030041005205126262003019885080c04100b03200b62081c40840d2400b034002186083d0421180400382c06c0c40608039541c3e46859460241d04202228a80c1143c0c0c680381d0880d8580340401d400c0c147c1c40d600c45414003a0f100c080240701c2e603440800001d1b1041c2400c000941d030f12200c02007402802200c0300181540714110210103820428800b43c03130b2400d1004101e481490310391888030044002650020b410bc071910942d07850b41d000c150489 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 71514129 1250 71512879 71512891
    0x702120c040603060209040c23031b0a0806030609060114090c040b03010f031109010e0703020309160602031b1b01050703030b04090602041d061e010207090c020105011502060403080a05 81
    0x2105000300450000341221040d6200b1541c507580014440041c0c1001d011f020000082030400001049405a40015102a031a080280a40c0010000f0410114200761840e48138515401d00c0d2101c2d090400034000c11016120544130744540c00010b408400d001410318140c40d50304c00032003500c09a400c140014000f025120b080754020034071000c168070100d240a1170090070f14980040701d240c9141002090321844040e0b060107500000c0060201d480050802078015010340f5006a0f02d9603590201800d004401290ba181148c005100041056000000e00820441c6400410385021415141340e07843d400c001e82e003c0211003030001ca00141d8052700103401105d0107410301082030344d100750001c0c0403540002800c5072104d0f40840c0030300c8509100044410828802211003e180c10b04030001200038120342c4002e680102c102000b040103900c20b00c0160300614a0031803c1c0040500c0340c401901a0800740108178840c085034540075009440041c045001e9600741d140c0120644550003a40003802008100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 71515379 1250 71514129 71514133
    0x1050a020309100e01080109020f030601140702041a0a0e0108070303030504050a05060c0a110d090b0c0709141f0b07120c0f060920030c04090507030b010b04151103070212 75
    0xc55020b0b41c80303c1c41c01655011059407044079240c09800050007100d81a041210010320622803001091600c100f1a90441d0007401e000010102c207950000d031510600388020340190070010008100707620310581c1000d078403040768144141600c0c2c02e0070720b424074800d11a010b8030394441201000400c0c0a03500560700640a0300940d0807040146c0c0340c82c0d1400d9010384103008071400000390381c22910340c0600c0c04d80c5041283c0026204068095000512090840c01514100600002d41d1191400204000c0e0010144440248000851035002910000c000c891044503641c518a8102a00000e6200321065548102040b42002181d84480c7c448540c2c0e00a0001886803d1300700201150f0071050f2410114424040468644414500100642c201105c21b1100600030b80351000655400314034003150480545002600014030f06045203000465803024121000c2c40c0c00102d031500c2c0c910000d1003a030300380c4482200300303668142c4101c038025016100029030760002d105000040c50440a262204186441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 71516629 1250 71515379 71515387
    0x702040f0e0313180204081e071805041a01030507030f0c0b0712020c0411040902030c1b0d090b030402130b01020705090705041a0f0403080f04210203060f01050f01050a0203 76
    0x2900c2481c42e84883ca00354085100d040c810010710300000b00c48585038450840c290706243c41c101e80d2a54400384c007802e036924011101000104c0c0001045018028402d00c00201d01070824030340310760020402602c003a6010011540c0001c038001202e804a4101c075403100c01840c010745141c6545115101c0182e0450f40d0340b501c0b500000d00c50001e08043d180c12401401040e40c040c00340c49020780303065207180d25140110305003104401c0740f408083c140d40403902c40d041c0240e500e9403510305c417140900c51950200064900002501749060000032503015240041d1a4403a08542396420000140002c039402035101c1035401421203000d0340354214100d105018012034210503210000a011008220b8004000a901280401c10803814144521a802c119a42c903481c11142d810200220b11460001410700000002d41d00300c4250f4001c1190008c2500d0855000412884074007444003040030320059100c1c0c8504404514548114816141201e00040120f18010020401522103070072240d075070003e5000500c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 71517879 1250 71516629 71516651
    0x418020702130f0513080301060e040f060e010e010906080303060618040609020d0605060403050a020f01090b03040b01150509010207090c050403080705070312020307030c03030504080403290702030a050702040f 92
    0x8107211161401020b00892030207280002c40b001c07100018244540c05501a145a001c10f00c0d58080340c0c150b0701c640c5060290040000c2c0480e0241c4580d841e01070700c00b442d03c1d0000030400700d020798440c10307500030f41d03681c030f00076643c4994203010b45166000380043c5400070000f19120b407624000415150303541d0f4902c410a00c01c01c3c00040c088450540c82103a070241c00080f0b0741050b541074800c41010b020b0440c0c02ea420541191262992010340f030000900441c600ca540c100315038040c000c904024058042210394900c0d00303140c0815419001c1c030401826a0004149070401030061047c6c40e201c04044c0d0003042282d00c0e002980002d01019001c85041c844d082102102080350000107000b820b001c0e2000f040d403145145410907521065103030803800c42d0014030651000940c000081e00c0400c0d0540740204543c1c6450410751864030941c1c5c0014600612028030303415a411900b204425201d0314440d1081139910201e080e6120b1140c8803200c0300180c010030114006181035484400c002c3caa900380040e21200c06 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 71519129 1250 71517879 71517889
    0x70e130e01050a09031119060203060312031806251409030a0f17040605031807090e06061f171b07030504091503020d110d050616170403050418020702 66
    0x9030360030400c840d200c041001c141070f00880803d1b14440314000500c10500888a01c505c14500c4c6003004110700d8000000c10350956080109542109807012181e40d02d042890702c0b074100d00348040307200795140203200000c1c084030b40401000ea1034840c41d04090005071140001203890a000c0c1542800c5c1c400b00b80030119190f2420801103210910583c25500c000055080c4003811095480b1000c110801c208400d2000c580c0c091f003079070342051210021a1140240ca4082070a102a42e00500b040c245007510407034070101d00040c0640154000d4640020f800d4640e4844c2c010820130a400601043e4403010481c191210089a01c1e07000b881c4146e0150a111246404080ca610040041d8005800842c05004078113292140380056030304003c54840151555021840c80780c511000608031000d0ba030000da245481e6007050088032980102590510300d084040c401c000e040f600382c014000342100d0b12101da100003164400380140d030941c42d40c0d401c0505d4810a52109010104813600c8a50244010780c0141c82d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 71520379 1250 71519129 71519131
    0xd06210209040f050619060e10060c1a070503041e030519030b0d1a0718090e0a0b1006030e0f03040e180d0206010509091c050d0e1507031103070e130e0105 68
    0x1410b40301b80314403801c081d81000b5124980c00020b541d84016041c0305055441c85406011a10a803e0158244056040c501c913103015078000b407058034201c0020014030691140080d40b1a030f10400e40080c40c20342082842084003280840180820b404111740040c9a94900c800031203c1c03a0340c980130680701e0502d0081091603c0544007220000c26121a120840900810007a407051081c23805a4004200400000b0034143c1403250580280d614a06508250428040042055008403004415003450103041c840400d0301e1141100103031415440b13100200c0c003c1a40c540e1002c5410045041500703080480c4407141024114800243d282c900611035030005105201480900e60003030b0005615000c02d018580ba40200440d2040e00406012680307041d0740300095035403640034642103849950004170307a00107081e55199040755202d420403c801d5540c0b184529440b0350000e40c0c00707020b000c0704c001810b40d1501040e00e0300d10201d07841031301300d09580c107141d8100c0d00c040780c0550300030941480e0755102d242140c034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 71521629 1250 71520379 71520391
    0x60e04020f01020d05090d11120c040b1c080307020102091002030915040302010c0b100801020705010e010f1103010b03060f040203010905070f050a0e04050c0705030307050d06210209040f0506 84
    0x40010401055260401d0800c42016003030014060788141420700414070b2052501c0d030f900c2080c40440c110305010003042424107405014080d01103c0d501d169106a940c02c681c0040c600c00ca0600180d200c1c20f041401c05d0304c00748079500039250b03100d01c1e45035190b021640006000e40110365091291090a0356500c00c0050000c009401440d40d8003004014050010400c81403803400d55000c210800040c0d0380302c6840c0c2c003c01d42103429001c403511240d40d01039090401e90300c0800d081d070001c2501801d21034103503c01e00011082c240200306c0e20003008910300903600b51074a01011040c040c00100111005c6400a41e80308100400071403282103c080040c00300e810030703040007110316540d5041020700c5400040300e1210340d9903400d1a0b420500d4000005059200c403941c0c1c00d00650b1510b0120f101a14070106a41070503900030252a12480c1502008001313070045146c2d1080181080c0c0000b80114104100050002c0d00784015084176000b50280590a04050030071a0600c0034003d000c40410300600c41680581 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 71522879 1250 71521629 71521649
    0x602090306011e05061801120e100c020c0a03031704031209060203150405040b0a18060606051e040806040609111005031605040f35161e06050c01020403050106 70
    0x6110032410103e41c00b01908072a000d40d00421010300030725071390445025840300900e001000705902001942c0039007001c08004060344915000110152a541c101e1130707411031316900303c5260070020010812030a4541c40701038081880b460300080380560a196840e1b0041c06810100d443c000b0008044048030b02100c0b0035141c80e9408002d0081c170044080725203107000d904880c20700a41c2055111400c08940103046031031510780d541c0c00150035002080b0000d1070079400900070454141e40381d501511580c0520280b2070407021800701d1020b0040c610f0151019218100001c04040c0d460342c2d943e0b4000c0101c564141d40d60301030003082942c20743c1d400d540b03241038800e5544e900b82c1364106800b50000b1f8840e0300c405541406414403040c80f40380c1105151301704840d4114900010060380ea20801d0103200e0140aa502c540f43c08443c0000520780040e142416541045000715400d56603080070301c40c030f03a10001449112104084c1005010311880207080302032492400145482e540b580c456003120b105600c101041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 71524129 1250 71522879 71522909
    0x60903020a0605030411060903190b0609010b0c0a0303020a030b04020a0c0b0a0207050307060b1c03020a02090a0204082a030703111f12050406060e0f04050f01110403020607060209030601 82
    0x60a102080300010202070503c107084d401e182d0744d41c42c1c200a040c03841502a00c4003241c0b015a80d0303000c102140301502c0700e40d183d0300070103203505052044a01c1252014010108040005038826400e4211555914401e024000054481d9400c901a601030000c450400d03403150b101c0441c0399070b0b910081c4511001c41e00d8561350031043c1c5c0303400d0000f001c2c010071031038100d8410f0265401158000c003c695401c3d0f449030000503110f10700c10004281c1110380e2002c8628440348200340040580000d5180c0d8600e008a5180c0c61641c0c406518009a115600aa5000b0740042054040f62100362110640c80c0d103460011400322000300c0046446c000e4070b43e00644080d04112202a654189540303a0080d40000c0c1c0600c1c0041801c0406c05411101e558000202042d40c9000040074010700c0e600130300260103900c8204001e800d0920100090102c15103042c0d40350300a003a8540a110350502c14482108020920310342030502d940c00b040150f801102003511380c0f42d020840801e03566002e000b541c0c0031780a040c0904240c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 71525379 1250 71524129 71524133
    0x2150301060c110301020c07031103010f060e040b01050405060d0201030507021005151c020d0f0303060b040b0301080d1e0f11060c0310060f021b0d021e040f060b0406081f060903 78
    0x1529505083c030340e0190b481001807003000b000104819082d65000104607a000711a100440d00400a54220310043c5203003c80101d101118003002601913030243c0500c0c640790b620b403800c003c111041603544036804442c2c40f00507030055019800607603020f1158019075142c0c10480000d0002c5d6001245c4050f0801041a407920781850150701074a01e071140520355014104190380880c446900c0303031901130501d4a034080765408162007600594007070724a43c40d42036155692031400d015207800c20301807440103018001254403090321030512080131201038a44d04032403600041c815281800d40132100720070801900004030210750f04200080c0550310441c03000d95603213025056402d0707000090300f0a0040000c86641003400560011701070f9002040d0010941910784244002540b2008240000f5080074440000e540400418601028004821b503410300c03141460482d810b08549041c0641d0409100901003801550b200f0b005031540304000380140789000c05003e104900f00180d40c0e12840c00541d002d5010b2003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 71526629 1250 71525379 71525393
    0xb010207060e060414030f0a0605010e01050910061d06031005010206070c030e0126040506040605060312031b0403050f030a090e270319030204030605090a0213050402150301060c 78
    0x814003881d050307a540c405400002e20610951080e48480d81c041517a094017680c00b40701c10141c0381c00b01c00484240800e00d01e4007001820b0244280450150403038000038190501d00000da200d00c80e510b5a04040d50305002069511a284c40c0f80c0d90001e080d40d1705a910b0720380754040203500270021007030b4131111035141c40002072620348000c2481c01040300f10034940b000070b50042d40c00521600b003400d214031409101c2c0b86031240078039490b241c40f0b2009814002c2c0020301101288860046016a506000b00d03035804083c555140008000b8280c40ca000f0400500403c2c41804910004071031580c4c001c4c070345581c2e91144da140018000b1020301070b030000211042d42c1608400184d0003041094074403112454a8441c0740010005000701d1208261910a41801e021080c01164030404401d01900604803000d41d0081c025000790204440031403504003c9008044000b030090200d590042c03000c0b4018004000040c00b42c040900200d80107481c0b040a00d0350a610b01c0c001e14064980755852440c0d034141824040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 71527879 1250 71526629 71526643
    0xf020405041e180209010911070803180c01090501140304020a03060e030307121803050a020f0f0d020705040203090a0318030206030c0c2406060a02030c03030408090108090d12050408070b0a0b0102 86
    0x205400c0c040f190f04800580b1a440b030141102c148079400200404513100c0940c0728440c80d00000c0102c1300020070440c10100e00c4490380300582a240484048030390500064501801901409011401144a8109040c1c003880115440b910203020600101c0d07807a55208103586c094003850140c0d030404030170414910340c0310700c2c0c08081c1402d13800240300c805512509a0300004000720007804000c000a070080a1500030040482140e00007405c1342c0c4488440e920080d107407084095800c00600403007a0004182c40c00d802983e0041e40b48402410380f40c5070316a01030b6140310032340c2c0340110490300c881400005603640740099071240740c1050344c5650703a005803084541802020349118465405200c0c1803c0a202c0180d00260700c1881620b40b696034030750060007a841e6004040e20b400d0544000000c20080254000c0503116060084c2c80792412038035074000c400d881352007000b400c4002a02c1c105460360085d6094000c190098000e080c118a001c20645400032803103811a5044069520b030784909010b940c1c100400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 71529129 1250 71527879 71527901
    0xd020307022b020126180c0301020c100e120a030218030a0b040305090105040305060c0706140c0306040902040608060703051b0c0618011103070807020d030905030d0f020405041e 78
    0x42d0204120000140c881072100c0c0103070400503401da13040c01ca0b4015030031088400d00c40d800544540e250001d86108500703c00c0360805d541c1d00403c419800325003414000e44101c08140c00207401c41d840c00c150000020140c41315045614460700b0300c1445c44045100003001c690300c2030341d00076940c0c21780d070700c011007400e00600d4496019a110a4054000c00c1490249035007140d418a4411350b950391020040740c050141d81c1015120340501c00c18000703800e40020040680600c107c0051001605504156151480c101c8142140c090304000003042032800380d0014526030b100130310022b0006e03112420301d0320301281181c00e030300402c1d500d1041c8958071020134400000c2181881945140c00c2080d80414ac031200058054034041c0c250354800c003543c003c203421814010550303503d09501d9142100004105c00390a0300c0e00030160058420b901e020611038024030103041d802800552500340c0400310b0320300070440007150300c24903a07080c00f01181641c0d50740508503102c0095201c50365134903440301c4d00e03d00300e500d15841 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 71530379 1250 71529129 71529169
    0x212010b090106050a0c1106040b0d1e0216030804060213180e010204050307050904050705060c060f090c09010b0a120e0f0f0604032a0f120206060904052104080d02030702 75
    0x2110360782584681b009401c5540003d81c40441040e40003c00d1660189400040d03a010010030742264420082c2d202452111903445140941d001c800c201c10100d210300301942080b514600300b0000070a028002c10764100c5c2c41007a006141c4060b4649101440c0000c1d0440c554400d040d0b10f628069840500850401c1c003500d0008525140c80c1400207541c5541c00e100e090301075001c40e00094107201e0300b0f1000030010203000e00307441d40d04c1c01629140c54607400d048400121503011440818940307000091404241140604900750990800a03d0125a040961034000700034210461002c12041340c0100e1189aa000e0010140c3c50030308030b1000d05003805a506005150310010800011981c8103c0100c03a115100e076410b526401e281c41100120042560064589814070b0240b4041003030351489a20b842d90558241c44150b200c400400181d04015034001d08039074000c0c1e405840c3c5c8801103c0303031302030703086086082c600d0203076145080b90511080c8100b040140c0c101140103015420414164400f03400d007540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 71531629 1250 71530379 71530387
    0x60c19121806050d0908040902040902030415050903030705250803010518060906010e060d02070b0a11090102100209040905070801060306051308041a120412030f11030f130212010b09010605 83
    0x280007000b60040c02d090501035910317182c0c1c3d441405650340072074002d080000400e556a94441d400d15000e03501c1510f044405030003030720300740301c020409203c5e150107014200051851a150300d00d040758980c0105542450301248421440042e807504240c2120f8207103c0c4071540d4480d80740400704003104c0710702c0481c03c0d180324040e801c000807503544c4154590301c113009080038032801c00030304003095003400f07038031102e56145200203401024443d04461180c0b08059400090040d40000c495000c4a4000d4000e151301680c441445061502c030780341c01900c00134201500001e40001e10342c5402c1d10b004499480800c40b40d40d1440d0a10910002d8005d00d07600003e4550794464403442c90b96441054030881c070030480c1c1d146225449480258800c800c40790090650818400e003420a03050581120502d615100301003403900c181078140c03081601680c030354032448030351140c115902c178418001a483c0c010300105880505040c80d1b00140d842c80c4440c10440f28090001643d0016801408200001a00a8424454244 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 71532879 1250 71531629 71531639
    0x207030801030807142a10020604020f04150603020304050c03150703020c011404140c15070213200301080106140901030602130305070b090a1211060c191218 69
    0x40c40ca40c1120380c04a1056950005410a0640c8403034281d590303102c80c0503540d002d00403c0085541e044440084001c86408007074800704111050b1440e01d28a800741c1c20410000d0054a0710b0340d013038010544c0142010400c120320040000240c03407640c11030004254040300340400d101e010030501d030100070150000d03d01800c0500c042e00b40c20000504560405400103601c1da00c1c07400079040034001c4c420341a20301d012428685040000101940a07040c01d91045410003002841c02c04403807150b40380410301301894400d0f41d40901040080044403041c20580b1b0301d09038007a0b00384000762608070204900190380c40b941886105404d440c0075902c082030041c3c03550500c1400380d54001c0020304480d84450010396a51070b01d10340381c1c10740381c0c07903030001c1d2850040d02c2c0e002900c410808001c150480088480d2451380d07885a1100d0700c0d44804103006084070640c1140904181003100c01401340c1c00c90241102c8071225140d150350300b01c040842088918103841000306228903000700011140d0014038500b010014200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 71534129 1250 71532879 71532887
    0x60b030c04090605030303060d020d080706090c0302010f030506091329040c0902030f070509180106031a09090a02010c0302031b03090a0510020c011b0215031b0f07081c2a03020703 79
    0x1040000c4d1040c10460f0000f00cc00100008441029900203800d109074404ca0070048c0c1030405620060340858185949030107000e1007803150901c0b58400604040032074480c0d61041080551420003155501040004841c9401c403200c0310b2100486030110b0154545444d192030201c180c02a03025000ca40d0042c0b0030700812030440b40300359500050b01d1500d0b81d10340c400000000d036030031a5801d00c0d001c055013810003c2103040e8103402100310104006040078410283c00c0a00090b500100d071a14541d8004d000c400d0015840b8000c0300745640e0080c41140c0c1030030014451500d140e0200406a040d690000070310074054140f6801c4074006060444003c00c0c880802d0802035101e544c0c00300d07498100100c00c50032580241031140c0100901d038010f807104900030120000c071000c41c0c0c02034034440701c8504040701c5d0302e40b0085410111021a0340328280d04d424203080350388424040d040203d0341c04850200c144050008142d5108402c2c07000b600784078100c1a168001001e29080c45401e06090405004000380004241c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 71535379 1250 71534129 71534149
    0x61203080c0702040f0f14060d0f060f0e071502010c050708030f070201022a010b0303070203030a03050601020307020409061a010302131802070c06090f05180a0906060b030c0409060503030306 84
    0x16500c1c040d0b501c041c54030000b40102424603000440038644050004d40c10010780c0000d9100c11241c20401d15038496104204007002400c00c000d0443e03e6041d04800083c615403c51545421404000700d981c4180d80b803820308002154001122500910100c4164280c2c240071b0720034203000b2400d04510740506501c5202080c84001d00b400e69100c107803030200300d915200358100c440050010006e021445c66068a05d0429610f00395125625801c001000e101c61a02008840c1c10340e0b4002c004618254000005402800c00200707200d042d0f010070301c4450096200ca018188019102d03440000b52a03040369588070004500c40c90850400d881032000750100351041d14031606540007030b00c12140354001140713100060b10a41100034540903444100241a50704008210141c1c3c0700616030841c03140c0c40300140300414105420200a41d8200ca0214003050f4090f400101d036540a508040313091500c80340703901c0c0a0351040e02c00c2521034000040030420b1803001d02c14000641012005145141019070018107020b43c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 71536629 1250 71535379 71535391
    0x507020d03020708100902040f11460810030201050a110a0602040b03010807080a0201023c0607110c0306011401110a08070b060409050d081305030f03060406120308 72
    0x22200003464103050007001240c0041c803160045411602031007554001030001400c00300d008604100c17003106000941d0150601c814001481c2d282451040345801082d920b606242c021055044881e504190807a40359080034901e0012008039403070350282d8000c4c2004402007640204002040303007440180c0c1e12100b20b0310803243c0c1d841c042c140490400b15107800c1100b4040000d2a032440024001851500c1030051812a0301d20707008c2d41c11059a60744243c0e00d500c0c804200a0041c1c0005d8800440d80341154440c1c2d541c080a0038603000164086104620040b0303c640b4407004035884201007041c215440212560f078804c40c80003605c001c0100001203940c88106004100c100c0e080c111840340c842e48680f492141108860f4111340c8100b00a0074681500e900c00c88055800c01844c400051740c5082c10b0196001ea1075205c0c0c010b025206405000725039500000d00304601a960030480741c000310300100701400000005061035903503400c0c01000c2004880d8030340d0020701d440c1c08024030740003c690000c2e40558004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 71537879 1250 71536629 71536639
    0x304032d0c1a190f020f030907050102010606090f1203050d1a090106020d02300d050109050105041404020f120a0308010806010f0b040e060a090501060c0b09070f060e1915090e07050702 81
    0x802034071041c006401b03400c2d468581c192011040044420740020b600007111420f070020000aa1201801c4848c100c2602480c1611182c075041004903c0e444201d012507113001c3d01d0300c181007610242140081d107812400c401e0f201c861403103c4130041d190107000c8600404d503500043c4407414015201944402c1c810810000081039800290b5004651721662079042d0048440c0560321480f00d01f405c0000c041c2070103a11030240c40d0030b00104a44c2045e100c1c1042d164015251001c00c0d90b1207500b04000390a60790072290300017134038038044040f0140410032a00854401d0320b84401640c1820006860900141d2000c0c6107039030904810440c00324160304079000d44022a1500009035148000714144009513440350702418076180c000100160702c03511712000d41c2c1c03090b0031116540e160b400c111070740c6000900078900c00394500001001820f0040058010800014104d03174a006400d40480101c0f4042d1f52100320a015000e8100c540558802018400380420030074405d240d04164100038864003a01500a0060f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 71539129 1250 71537879 71537891
    0x2031b010e04051f17120a0c0b060a1a0a03051303082e09020a030e07060f03020a030f050405070305060708221b09021c0b03030304032d0c1a19 63
    0x44c0c2080e120f1000003104c0554030840703e560ba602204c07110018135042d403202c0d0180303160b071400d805500e0b0200d40c04c1c0c0d5025900c44501d214540c80301c10f0896000f40140368000c0500d44006000414003980301c820600d01041c0e00e0310350618040190a0701c40007000790303691404a09000e00042c6c2c01011154118000c00160402c0100040c10034455640e4440c51880038910704034000303030640868008280c40805a40c00b07204804980d1071641d5503030302d1030280e180818241003101e80100d01c254041c151031542c501c0d010480543d0246640100d81d0b09840603034103500800d01c24824010201300c829000a000d191204051900e40703203643d03c1a140c0b00710030809100e0120740d00284400300343c014002840741d0300b840f0420703943e8034110402544600d05445d001c0403015021505154544221001d50320090085d52441c0d88558003101c903a840f64001040b0071038a0340640e11078104181c1310095100c078039213440c0da180e0807500b1301c80d48600302e04408181c84242007081000c1140c64000500108001c21404500d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71540379 1250 71539129 71539141
    0x80d0e19140a14030301051f0807030b0a030602070c080d170105041a130e0c0631030f0303050601090515070605090f010e0610080c09010303300902031b010e0405 71
    0x81a8a1100241a60f200200e0400c82c019002c0000e5040b1202101d95140040e1640c11401c00e030380042207203c0c08540140c000036081402604486090f030001400c910910341c4070b51302e0700201e03080140192076400204500b0f104411082041c42404c201a042c4640104a24061515080414000c4a010300d444002c44143d50003c0549501c1c043c4c0c000317081e80c20404410144200a00915040c00d0f0288036000310022642050421143e02e10f88005071003148081d8a0a42941400b4038200c55a42c0801810008040760702e0451a40280340b09035400f00d414200300c00010300508803a084580b06000080001c241100540308442e5000ea21410102d179503541c0d07921481c18079401048408055083c004407080c03a10780804c5180c0300d02c40e10341140111503201c12045030360301642681e01d500b01c45010014000309014411342c00c040203060810321203d0410b0030101c4640d917501711f1082c00444c2c4981858045260910103080c00c0765502600d4000b030712904000070b040110710803606010b03a42c6e43d00400c503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71541629 1250 71540379 71540383
    0x150901020106030602040b07030801050f06090d0c03020409080409050109110307121401060507021e03150c07080a0f0f020604080307050d020909011203181d18010603080d0e1914 78
    0x3000f160000b004544a07a607450110090394418541200000c20f01800420f040c43d286598100440c00600014101900c150910403140608c2c0707001d98490801c2c550000061340ca6004c1c0c0341c4111b106480d4507498518044440003542c0781078020105032070606006640b01032141e41500d9010700d0a1900c0150b10301c89001e060014038113850200b40b10301c3c45200218003141c00100a040b024802d40c3c692008a03080161100101842c41c3c0c1c050749500108080380300d039110681c0f11a008000d4191071351602c0d800d607640628641c03201d00540d01048103a00a5081c480d08004000901c0709e407030000d401c1d80e24096441e5406484000c00c4501444800f040411940500e40d0656a8064000d0204481d9584511000c641205200001c4000610041a20300303c440f441042e81c00319400307540b480010b160020702c040011680100b10f804450307044403038901c902c402405850700079802130703d1852b50344580101c140140e0b46c2d20441800c055112004c0e00d101c8021841b210380034079400c800d0f00162901d001d03035854 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71542879 1250 71541629 71541641
    0xd050c090d050610060908150408130927030f080702070302032508030703120906020c0a0c0501030f02120a0905250e0708091c02070506070602040e060102010203061509010201 77
    0x5400059007032415040040001d08039004404c02484042e000d560b444e01154640c4490289541356000422031f00d0300c1c1d41c00491f1158005200b012281d0500ca0400421000025103501501ca010780303540344c1c2544003001940c03040f5071a024481c1000d13590b8540e1030180c0130166071401d103c00c11203890002540e00e442408594099580101916040904c22841c0c0d0701d10038203800c14211030140d10701e00003000c0e4000011079200c2c80d4907842d6513101c0c181c0403030345030b0080c040d040c001c0d180e4540800410030051700c18807400c40c40034070030020301311350a080400040c11035280d02103608a203441003001004070b01f040d0b50b03055846400c00b580854404803c1c6046070074840d00300a40c0c42d01282c0310803000c050081c41c181e442c09031000c0444800c002c0e511014102d480b02000e60b42141117421106050b0903100003610000b032000c61300d00485a000380e0f1080442d03c02da00c51074064414aa020600b801001c00d102e8419030030034001d100950071400c1443c0080d1030f40001c82ca04451811001500c242180d000790403030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71544129 1250 71542879 71542897
    0x220f0b040212030a0203120903070203152805090f03041d0a020f040b0a030e0307030801030602130807080307020415060801170115060c02030c01030c050405040c0c060e0a030206070e03030d050c 85
    0x3e0380d00d80b80c0c039180281d681e4012050241451441d080007465458000041e0740c1c0894008008202c01128000311602c0d001015090019180720240440c04642c644a8400311101001030002520300d00030307c60a04241c8812001c0b00150002c202c100080050b544d11510b4100c00a030444829407280c02d4041c1c0240300b5035804d400300b03003404a40010380c1c490800152500d43d607d07840600c185803009180c5030f2284101003005000c500300c480140046117141d0301804200388010141e107a0301d074070b0325015840c0100951100310268400500d040440c2010b001e18112889240200f40c61641824806010344c5014004c14030310601046191120180c00d400c1080e00c2d04c2601c0e100e8038010f0f1258002841206100000c0e8040d00c2045400d0315a94424418855603011136a105400c21342440c0400010384175020021041002c80007070003000c0b40d00b5100386403895a00c43d0040c003082e6010b183c00ba0030301030002c0800e030900c4a101d44803645a00d01000712640308407a0500003e9580e03c80e81009514020040e80c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71545379 1250 71544129 71544133
    0xf200c031201080c0112020a02060c07022106190e070e09071e030b0f09060103061104030c0906092f070f050d08090c1002070909020109050612220f0b040212 69
    0xd5100c3d02203064007000700d0a90b5603040200014444c41d05901c0382c25104001070307100e5030024500b00d49100c064000325100418403107401016683c0a510f400b031180400c81d0a401100038000c0d0307803d60210b62041c0b00410072080c02041d5208890580b90034251003101500b280c00800186481d074184002006451050401c07a560507007607004803401c407802d0004461071005280840c1c80d14a110741454407804154000300810f80c215603501c405404102c0c110201a04140004400110007030b1078503000e0060f4000c006451803414207800d0070784940d030009142c28081d0302c05150b00c45c00016003520500c2da2008906603035600d2403401c4001c4440540010307120307010f00c07103545004136407100c10540100310300011070b000120124100b007002d040b00401c50300503034041041000b0303041c456009143d00e1401410300c2d400c0360b5542c03004148503a001034549508a12114104241d4114444070300d0064014849500b00b041947d590301e80340c00c0706400002e4154071112000130704565030295004444021401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71546629 1250 71545379 71545381
    0x31a0c070f0602181f180b0a05090307050609060301120f0204020307030b010906031505091905010602150c180616080a0917060906070807030e03040b070302010f200c0312 75
    0x5040009420140311318150280821304030f0214a03020741d0f400200b21001a203003904410703200e010b4401c58450307800340c1d0300c010f4220000522001407202420880c2c007151070300c9030380c0d2086408160800050790405071045405000e41c140544541080d281520418100e0207080710980c01c1018904480f00c1c0003d51050000003000011036041e040340024810a0f280c00720b0960701d4100030f03001d4a011890880401c41c0c080741c100020710b026601150800021210344006000c1d040d071441c00c2d940242c0103840940d1213004106100040480120303400112614064100440c01300b045074041407448015220300000f280c1002140c0150358041d40b0359610400c1169520741100000e00451040d101d450b080a0210100d08903241001c145d880c4034484850241465039a0340d2030030b454100014006e2010182d840301240c00b00c3c5010801003001d032046890040d2220083d04d0000c3c01e545625410f68281420454140081c0c0c1c1c4400032030400404030300c1c40c10b450f01c9403030500740d01c0c0d405001c1c40d003c0e242580c1c0c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71547879 1250 71546629 71546633
    0x6030203160612060302030c040b0a0806011401080106020304060c0303020a050c0706030506040f06150c212d090501050307120609020403050d020a05070306050c04051905100207031a0c070f 83
    0x4102c9030340b900c0f142c80000161007084121155440060741640250300b044210740380690200c0d43c0c0c202d0040024008680321002c0c249401c00980009801504076a905411507820450490041900344000c618180c10301c18000c00c4641a11001400d05802244c0901c09500403000d482441c800d50044885050f076076030300240030b4a02919198021450720003640740d045958010342c800d903282401c982000d01c42c012000c450704d000140b07040e00c20a0000b0111403103541c41040061024129581c2c4140c45940c0940780c0c1100b0900c10f0030701c80b0b013000b110140d403808d0f504880c403142210400d00700580c5030b0359603079419104100c140d8060b00140b4038100f00031071000c0c0294094410b50340504211112560b009000340c0e40d0320211312011708198401d4404200007401c41d008194806010066241080d50722808a070820310742105100401d80d01840c28006401c000541240343c0825100810500c2d14544802d40c0181d031001ca030840080f26100020f00d6407918000f15036005a2101001440c00264 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71549129 1250 71547879 71547913
    0x70e040303060e10090b06040b1c0207050a0b070f1e140d0e15070c0309180603080c030712020616031a0d0f05010c0810060503040203150114010206160203030609070306030203 77
    0xa170140d00d91903450880c001c80103040038020b131400e44545420013850035841d11406005545504c54075046290208103020010b1410b00c2034444051040a4120340d6050080703000e8102c00020000d10700f00115114101c0c1800c070f0318260f40e00d121081c0c0c241410b0f101040281c1c501c5901c80e070441c100c00c65081c000c24100740c00000484002c4420300002c803103000e403190740c02114416020720020f070010340052010700181c012044002d2441e0510031000078415900c0e038400080d500010380100c0190004520201404224103540c000316085101601451034842c005001c240c8110045004150340c0d038004d4070342052074507d20110300900501c42c29030040b9500e44080304208180040b101e0b54200b20882103282d00a941c0c40e8000c1d1000a1412030a9081c01e0080302d81e9080201305a915101e06c106008560628000742800303020003045024903003c00000280ca07061001d045203402064404581c0c140c181d000c019a604140700f100d071b8030a035845116045000d0001c60300003035454094010400b01445034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71550379 1250 71549129 71549161
    0x80d020306040f061d18070b0c070e01090b100e0303030a0b1908030403120302040506090402030c070b04060501090606050c030702010f020a080406030f050711060a0b040f140a0b06030702070e040303060e 89
    0x40c0b003845d20030b0756965017064442e507040002c800c0007503112400500510541d0380c003a00701d0a8104013220112607455440c038070003540c01c0c3d00c41282580ea9202e1500c50b81000e600d5088030101600306181f8007203807407000c00d40da44002041c5104007030f6111484040341d03413100c00070589a00340b098000c2c0314507240d5040310b4480e4058132089448283da00b100e40e0080d80603000352000c56100802170750a00410341e040c0000317980003c09611075144100994000244c0003406240654012500024a0b40c100010b11007141c40e99000030043c4001801210100031001084420f0b0603428609482d54000582c2c00780e10300381209500800840f4081400b040f001c0d415480481e101c020031205000544459009079205d030132004001441d50030100c0094410010b54000450104000c1d00004070800d040041804644074403022000050740c82c1d050011300c1c0c03c2c034010140150070880d01c040c82c508015501035a626050b02c5100c40000d00c0d01c00123401d240c000d0703004030010301c0d440080350401d1410060f50842c400b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71551629 1250 71550379 71550419
    0x305060a0c0e12030d150504021909050301110d090303022b0507080402031b1c0f020301060e01050603160311070506041202030a051204050a06090b070e060304080d020306040f06 78
    0x60384030602c001500c0d1505a011001c52040091807400d1102644000a40644100304081c10440417000a46403103510003000090180e01082102010031703003000300035865a40c80f15121340e0504107101c08000c560b03011201e560340e4905002640108624064004e80162600414410b0b01d02d5541c901e5680c3e5400d070101e414008210030030a41c2d0300c25409896a072410307180a5059805626201d0241500402886144800501042c14452494801118a030300c40b10111203c04944a4110850500b406400050131080d5458810fa41c141804110f0602000f400c40c2291901d804442111394003917031001d0920342074440d0855907403e00c1e09016665000039202120303910748070400020054408001e45074188080c0d681c9610700020b441c440f50b0a4040500300b5070700350041401007400100548a01c8800714411105180c0d030340380c00d110151141c180403100c640501d10800c10000020190400c0750369145a13140010b85949403000031800810a64142000e020f1902f1000700d03418411f0405018000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71552879 1250 71551629 71551637
    0x41401080c03070605121b1605060c0c0a1e02060310060f0e0109050d030210020307020d020d0309020f091905070809010b010201020408060112051006060513090e070614040305060a0c 80
    0x49841c1d09042d5603149600c526800a4000e00c003540d040503820f626a90400c89248802d06204d0408400c5c2d00c0c070f5400b01034046504944030643c1c90030810203000381e60740308406990140c148070394944459120340c840c15000701200c0c000020308d850713101060360122260380c024210548034985000341c0010709041e8015007010511200c1d5203940d41c1d215100d482980070040c0d44401003d03141c202170011140c09401c0c120158084c4480e290121260307807025502c0b03a502540101901c40503098060b041c6412a00b6640425080444c0403000d41c44400040242400544079400c0507600c00000c00c0b545c48001c00e12040803030800003401401039106298038041c0e841100204603000c595001039080744200d218610141e00000010801855000d09442002d0b005405072244840840744d50021107400b504842c000c1000030984584444103404640050040d48004014001d114851035603034216501ca040d04006d0124440002400c41c2004d8038002c561090441c0d241c1d081448a210107020bc01d8640e80000e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71554129 1250 71552879 71552893
    0x30d0509011a030303040f2022050108030408031c1e05040210090f0323060f0f010e0103030e090403030204170303011703041a070614011202030609010c02070b0d060504140108 77
    0x1034a000300c1102e0203142d0094115401c2442d60752075180682c50010521070081d00e000f28040380303031075104d2541c110450700307449d114203250360300800d80413a04107030010495584184400e0104480002c111404076514101d005120185101c00e0005400c03074040007000349080c884048101c40d6241c0040e0300842c42280e51402086101c00200c80c480c11034820300800803540c9034200042041d01c1c442001e00c083d00d1086140c2109260049482c040d4180e640c4503052074000c01b0080c5100001c0e0109024102e480c0c40b03481e055245480003803600c582c5e80030880c07151034418081001c150003a03046800900300c41610745070700281c001e136242c2c43c4d402c24811802600d12021840901c480044103c81c141c0d0310140c0c88880e910751740c0210030301c83c1c0c1000030100c0d40340e0781d01c40320380c011400c24160550003041300c880007030a0f40c031607803040c181020701c00b07451844103a04084c2d4130201c040d000b143e204180c601ca610a0b0391140750800010780600f00036400b103070b005481d202030f0003d541c04107001c49040e80e130710104a80003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71555379 1250 71554129 71554181
    0x120f060b040506010c030309050c180108070503010c0503070e0f0a0b0a02070b040501140f25050c0a03020f10020a06050109020a1d09060409050c1201020912010603050706080405030d050901 83
    0x190b5600f101c0190024540d2070503100000e0103035102c0c1e64054001c004480c48906040d011510103d0340c007542c040c0301c022203401005a002c1c104a80c401510041e4004d03c031443c46051702400380e0002500d0f20701445500e0001c075002c2d031601208410350b0035005000b190503030369808001415a0000c1059001401841008954248401d0441d03088030010f0b50303002d40e0034080131035014450b003040b41d49490007441001102004034400909a41c00306400641c1801b03580d00780707031091600140d4554180624400e1004002698868000c41810031007a5079100715803040503401c81c1006c0e0004002802946480300106e411003907503000d07050000141d115400300020f010f9051305c46040252030350303502c03441d04400160141004c0d0495141c544c441c00072904071140c11000200114401c88141d15961350100d80903d0354a440c0c4081c135614803030000208100c5080d602d43d1600c070165400391a0a020310360001c50100704080040303500c842e010503000c0180b8140010054041d005042078503c00812803042908 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71556629 1250 71555379 71555381
    0xa0803090f07080a080f040314010606091d07050a0309020d05060114240d021b0604060b040e061b09030f030d0f05060d02011107120b0613021e0c07120f060b04 70
    0x803e81d0091402000142090fa6440071158041450214400c0041c0400800940010f0130200c41c40041e6001203a01030620b2402800641c89a0010f88680046841e09142581554a1541040d41c0f8a080f07566426400b40a030302420054400a400003900c0c0402000c2c0b04010800d42d05850080401c03c0144507100c081220701144150200030310445041c4001419640000415060340645400360401914040d0f80c00d440819942d01105500324204000030001584298818130308100c408000c010707440b1000c039079035110013005154203200002c0e44102c40001841a0b038500c4000030102c039581046040800c0e100d81280c40d00d094400d08000c0300345d09400f030a00510340b0603200500b04400001a50700115510840c000400d001c81c092007801096809004105800c0381d4040ca0f010310490030300c0814450800e00e44842c48850901c140201051548006012007d10000c120892b44800703801000350300301505588580354002001c6c0c2c17010200130a65000c0010240034003000c005868403001400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71557879 1250 71556629 71556643
    0x5090a110301120c2303010e120708070206070804180f0606080f07140301060504031e0b01060809070504050708040501053402030d0903111b0603011403010e0a0803090f 74
    0x503804401840180030110560881041c29070003000c80340b1909a641008000c0b4140400303410880134142440401315040900648a02409500c01800003040590340034040d0300a464004240400024910b015503880c9401e855845400c80c4070030b55110303518149940011340e20003c81406a007852242c125880e01c5126440031507502e5110f451083d500d2403107801d191400100078900340200000002c581c102440042c5000c1d000e00e44941d0b59070340c2036080c002c040000201401e101c012011410b03a0004040e205498110741050401404640310400440e080104903000b0980045c640000c115244d644424528011030041d002000f441d00c070b0b0340da0421814480c062071034804020f0308000900c0240e003031244008030340c85e1041e6820020540e00403415100d44004c02e0780080c001103011281e100703040c85041100320751036910050480c801000700340759000501c0749071a0540701002010040d2429003144010f03031240011b8540042103494600869001a104000c0c984030b8481c0454078241c00284071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71559129 1250 71557879 71557901
    0x40e1c050f0909040201030f0606020d0909020415030b0604030f060501051f140901050d091203110301060c061a030d0908071d060f0d0b0103060903020c0a0302011b02040b06040f05090a 81
    0x240c0d1900800b41c003803244820026100300d042540c0c0740c00c07220580c00c4a11551000e0300840d4040d00110030310b800010301420301500144001ca104210401003074140042c0080016110700300403e03036150060006005005aa00c05001c0304401d04402040000d584d101c07034180c8004952a181c000180c5494952300d484244403800401e10b61900c40076410814400b80c41c032410140f404600c5c042002d01c0542c203807a5050402c90381c10001c038107130f42002078040c0104003458207852001400d40d031500d040240080030540016201e10b6585942c1d1807480001c054840e805040a0300315003007500d80600061085041d80718094040c0604074000c10404104070842074007201c80d0045107440d8a9440400180340c28013051b095115503940030280008450550840c02940613450006604a060401070304107036502e84810300c1138410782018001030b03811440d082c0300007a07198103e0303400071858808074004006103000640e0110010a0010b081c01510704258142c074400c1d00e59406c00d480301a280d0f820b03620152a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71560379 1250 71559129 71559157
    0x11b03060b07111c0609060506180c07150c020a02010e031b0613090903050c010606020706080a020c0c040f06050a050301050f01030f0302070513050108010b0316091a040e1c05 77
    0x51800320354500b9402101d0f0f00000d06000080d00000da6584401d40000412986a40c0f41c0760782005220b041e104150344003100ba524680c03071562000d181c02040710010716482a014022450030203110b8185459141401d0400c4104518121010065032751002444201e000585807401d4030240d05021881d03600d9154461800290024a00204240c0d034000940240c44010882c50001e41d42d000340c01100e1501e40203455003036a40ba441200c40f070943d00190004015036210450800400780d00c02d5000360b01c01a228030044e1141c500311032290401d080c80590551050500b800b86241c0100d591151003240c0301181c00c1c0b41180d030b496050500f1780380308480c009010144100104082880c3c4408100014031900c180da131610f0b11791000426850309044543d03551659030006001228003481000c07805c11084009014403603d080c02c403a4200117501034200c050740c072040d1111740341100700c0e00441d00000c0200700340b0652266400346540c1e84a42c0c54603c0001320915070401003180154100c2c1d04c0b00c2040c2c0360b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71561629 1250 71560379 71560387
    0xc0a0303320106030b040207020303040b04180903050f0c03070b0103050607030f060806060609061207050403061a0f10030e0601080a050d1e03150e0906150f0105090f03070302060c011b03060b 84
    0x4004c0d002070412034039854000707808201d0400140e80034001000504461104c00d40c40b86d042000c0813160052802c2d52001c1c039407800c560000880d800c842a60040025078605603562098800100c0c01c2d070044010041c0111000b000120412034041075203886001c0a5a0402c1501c001d400e4490503101188aa140650820000304605007032800080580e624060031403490300609560740c240303101c01100c40100146001c10240304000c124019041c41c0c10789665150580015900054504480c0781101c40c41004030030010fa03105030007500030419502004060740c0d030a40e0369070920354442003c0d00c0212214015003445408090050120078130a101c2e94049480c4018007000a40c01070000100014143d04000c0d80014002d0744010040d100d43c1c1c00d980030700180c0c20701050b8181e40d00300708108240f00305071001c801c0e009641e0020950741a40300440300240c40c070216401003418200150000f07900b000b80025400340070041500081880c004454480c42d4035a0a40030460888003940541c40403500200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71562879 1250 71561629 71561639
    0x907031502090f37050f040902100c0c0f0305010e06070201050c03040303050c0906071a0708060f090c04030206070c031e02100f031b0201060e0105061305150c0a03033201 75
    0x80103281e40b2060b500301c03182c51101608408041c041142c64101e08008100284501d0401c1d0340c414004100c15642440040010749c0001d180380c000d0600b01d000c101d02c104490301800f160365186002040085800314459403281072440c060205049104014444c1c840800c0b5040e02c1480b40504c00d01c5522405821602d6a030f40450103030802034140c1c0c5600300d0a0281012940c3da0b24014410380e071080001c41207600401039200842800200b4210600c0100c200700801c40d11000707884480310300100c551000d15624610180402e0007a078001941044000c0380c503408006a48a19006403801188003004005510b6903a01541c903034800000c0d00442c940340c1302ca41c40c60143c1c00c40764205c0c05500700440c0780d0180940591411040c010343c80b0042c1e44131141006400310641304180540001e031401d6180000035a40080c2c844560b200e828011070030f080c4c4a47c0e41441c0403095504139404c94064440c00b80d184c2c14010061700f00b40c0c0c2d031300480c1690030100c200031280c180045e41603002c00d10700052240c2c0ca05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71564129 1250 71562879 71562889
    0x6030c0b040b040e0403030f1a27010b0a091a030906010b030106020c040504030c0f060c0f090803040605030702030f0c060403030b0d05060420090109050f0c0c0303012603030907031502090f 83
    0xb1740101c0505458400c080c07920803850140912880d00802c0305a000c03100141044219a0000d00011810007550454404d40e04034480c0e0038156846102c900352b8600494a048800c40100d60144034401048485440b05901d130400941c01254060101c039210798035500807040f1071100303100c0da40250740010f107510300e04e080503004241d000740a41040c0b200f80d0000c1e298113100410043c01213aa1a640d0301c012416030f03400008180c201032662078280851428501e1140e6030348128092031050040100000fa040d6208000715400c800a456030766031150504808141d544100751011000b00e030501444400b00d05090068055a5410200078000c5484940f50320101581c0c8548060f0038040d800558042c0391140303070180c2d0007054134200000701442d10802d101c6040e03d002c4c09040c031080007001201801240003050382c1c11754035114481c115050032421451124104840d500c00d140c0008010410824004501d8500b10390048003501c100c0e4040309800804c910038108482c1d805450110a08114141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71565379 1250 71564129 71564131
    0x409060f12110d230601080706090509180d050904050109091a1005031f0513020d14011b02210f07111c050f07050114090402090409020405070306030c0b040b040e 71
    0x40c1948010203030913280e032a070328400640042542218081d24003002c01c41009030038010300300c03400980103036410844014525051880340c14402c400038008162104851740c40035200c1d41415041f221000c0710000b000e001c54014591f09446145001c2c00012100e003a03004121041d640142c0024501490000d5211058406040f000c0c200180620110340c41d01d0410440c1207036411040001001030020300c0c50f00969400401c01200d5481090600e40162240c044007400c050340513583c0b0644a406142c4680140740d103130107500c40d00020008510503550003089500c0c506005a11110011800c01c0c0e042c580782c801c00030303950000c0e40100301030400703d0440070590f28000b800401c0d100202ca8000c919404030460560309a40e25040300000c410303404030800c00d083c0209400c0c24990780441c1090f41c2c040c618010301c002580900d40001e25800c850b81c4550060340160782c000c00030000c9052424006008014034002242d410460410100d010000e440c05c0d0341c2150000d0321003a14003820000884580f882c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71566629 1250 71565379 71565413
    0x605090a051903021c06270209040302014511010309050a020d05070f0602011b030b0f030601060801050114090a0303050a140d051605070c0605030601020f0709020409060f12 76
    0x1264404030041e41d9200305c00040ca0448015600b00003913508080c0200c031005130304100c01a0340140e0319409120302d0350000303d8484d01200c07042d00c01e90b00e508069001d44024245440807100d000309040241d600c81039009a42d010810400c00b402c500704d401c43c04070510241c1c0241c05041e01e800100d41315031003904060700c0b080c0b2034410740341c195905030f01003032081d204100c0440d502c1c1c000d040144426040310560f44000c0c05144000d01c0b500e10a040007100300408001a181016200d007000441a22010300300c1030581c40c081d0896105680d201c1c402002e449080c000c140c001190f4030b106559044100081d582500c5001740400c4030146159010356859101020307110500c650234130400031881c4410041d03c4101c080c1100851645444031103084119142005c4100740803080c414000071510003007089058403c1403d0980e41c07600c50b000185d2500c014801c0d6042280314440d0007245920742c0e0340103031080714103103001848031580350085d0084002c0c2500480701c015410003481804542ca030041a5108030b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71567879 1250 71566629 71566669
    0x40b01151404180b0108100312050c03031515040f0e0709030f060207050105010e010308030a0f0b060c011a0102010c0503070c0f02180414012f0405120a0c0605090a05 73
    0x44008041101c1d80e0040d41c80210008542c1950f09a010224002c40141600c00d1038041106e103029480703098800498000507120303a0606041800704c90003603046031049a0304508581d12450030034038520301d44075481001c0f8000c00c010000009081440b800351000c0c2c501c0085000750f5a82080002c41d1003600c02805074040200500c80080030a103400780078090b079800b8503409a41c03078066003000380c2922011303070003541207901c0d00c0010008a200041a02c2d000b082c84a80890850022001c4401400e01003d0940d40310764005090b04c1803000c15031116140b60a404480c130004c1b424600164201c03011440c0c403030041401040021081c501c03c2c2c2c9007200c0184200070090b00e0f410301ea000f0401c61050501d104230044850014041841302c105040e2041d030313030680d00901500d055155000062100e4004101c213040110200c1d2000d0100c00701034a02400006c0c18030740b4240300c03007622180d461540c0181581c080030381032404640c85200d1003c07202103020140812024503d00390074080c10049581d144c0a0f01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71569129 1250 71567879 71567897
    0x50c0c09060a0b13140f010f080a0b04020d060501030e03071a040f050321090f0d030c051902010615030b01080106051c14060102010f0207050706030b0307120503070c0608040b0115 79
    0xb812801400c0e0070b52044c02c8900b2010309090349210b5507000480700510070444c04028070f0241c0c0e80901c80c9012141e03507241c0070300340d500d8041714880035200d54120554010300100d01668190f007154050002c49109a0303040c05061601c80b0207580300d1252000c0600002000c003032911000691040198010344100d601d04c00d4a0780d107440c0c0a0a54010049000b40f188185001310001c559605038150000e080d10060000e08284100460741da01400610100307042c0c03118412804640114140e52020035451042030070314150107002402010603020f00c070118014207083c010802d00c80d01c2107a00c000d5043e1200c01484c3d003070010507681c0f6005650b46a100e469584102c00c0940104e0050710074842c0140000c00003400c000d0006800e440030910b440800600c1404110081000000c1e034004455003070400044403040c00000c00d0900c00d01d41c001c1a9a07000b12003061081040000050203624002c0d00e01070400741c0c840e03804440303142e01a03d000e0440c0c84203000501200c0031709401e002150015040071044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71570379 1250 71569129 71569139
    0xb09090c04031406040b010806060d110f061b010510030c05130e0307030806010e03030708030604020c030f040308070209010906050619110d02070306051501200a0602160210050c0c09060a 82
    0x7000007440c050f42100d400440c144820000340075000c6014244031805481607190540c0443c00f6172102c0c5101801a140d801c1035440d940e1103d00c101450060044c0829684001d2100026800c0101202e140003941c80e181c00901c1480b44c4190300002c0d65880041a81000c0c900360411140c000d140c140400819920b081c80100f15008000030000c4c0e500c20b49a0010b03c2c40c102c5c1c0050011806046250701075001002080005808001102d501c404225401a150325008203018614002d0089038444000002404814092120041c1180e94400c9961503801c0c1c1e00e951343c000a60300188902034000c0d000348050903081920440f040ea07808918030b00407a4100010240034a0b2040c2c020108000d40c01441091052066500403071b980600340001c0e0b507088581010000b484603854114403410b0301703220b40b0022401b1000344000340f03119420070700a648500b0300021010b0102c000c46c500701d2150412004034000240200f060712030074a26400074010140e503650621803440001000e15900041c1c90700c000c50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71571629 1250 71570379 71570393
    0x1b040f020414012709090f08070309080c0d0c14041b0302090312070209160908030316120903120213030f05030a0908070b040501120f0905031806040b09090c0403 71
    0xc182c80507400840c0d00c50030703001400f900c95641801e00f20b002c030755000741d00007241505807004440c0ca8410005058100d42010504c407410003a0042ca1804000fa01c001450340c007180c0701c01600d4003102a21114034658007080000d00d1085d000a20340d00d400c440c200b242c0c2c1b000910806000c680078201180384049164002c581e140c444e070072280800e43c04505a072907403c082020310a41401840c10074601200f40d000649540310091002004d0300c1042a41800144109040c40051136404102c030b4603070814502c0601889440d00c15000010070303104031059205141d000f8202029015254500b121702d0310340e5140e01039031000c0c107103071440300c508040000040e000da0340086547d07009101860300c40c011090700504203445948036580c180d0000c4c100f8000c550b451421541101c0d0242020307141504226160400352441c061564000c80c81e01303029000f4800040010412011310015000741381c4440710130000c41cfc3c0254000ca03140460184140891400c180c0462500540c41a034401e050542d03d640d460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71572879 1250 71571629 71571637
    0x1090213050114060403020f0607021504030506071106100611030c060103050105071701061409010309061a01020610060207090902120a1115160f06110d020c06060103020c1b040f02 79
    0xc51515600d9004004040000c085085070680440c0c2c0d1300d00e05403550b00080d01c603101d521301c103e11070040011610110768440ca0900c0c00f041281c5240e54495a89003070040c0c1310242105c108020400d08401c012a100010803401c0c400c00c401c0180303403201400e0100441d1400343c8171208045510040100710065a03040100303e000394820000400c003490300780c0f0b0040050002148125a92a040006024158000844c04507160100c101c40e03840d01c154a0040b00500480d00000c0c0c0110300e000b40d14468000c07006100450100280c0841d02152503c041100003087c140c420b039001600305280a0000280341e80214401c036000a10344501c80c4e20b4091407505004c00d410084429042d0000107004505056071020f09004e00026107504020240c40711001c80040c0101c0180740c01030449460302084000e503c0040c2c1802e00318800354481c640c080030b00009602101003403a03240701d8200051000c0d8481d00854103607802d030b4406800401110309000d040b40c22401011684a600d404c04468445600d1001d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71574129 1250 71572879 71572909
    0x30f0c0d110903010e0c0603070309080d110909090f07060c0812070203070c0b030f040201030504051023011224180c0e09012903070506070f050f1c0e03010902 70
    0x150b070301c600c100100f40c21150a0700c0701c400303960040c881000072680c400c0c040e60340c012110300700822104014603003c25240300317000c0740c001e21074034101c05107000310703803940203041e01c01310a407550003642e202c2002095581e0704036044030342c01c1d90007a802409414070030180f412800e840740c0030007400c01d03010050040030b443c1d046804078010b9101080c0030043c0711031040c081c0010010380da1f400e440c50418450303807402c02c8002000a8145525071000c80c003046410441c50808407ca01307410080c2c203000c10070054071140207031400c960007001c0e0000403c0360380399a9a4200c0050780408001000003c01103150030840507002000312550751a000c4441c4400c00c80603540d5400d1152140b910074505040d200060782c43e0140c0219181d0303150102c1d001c0164034003a182c0e05200175070090282c0101800002034a4803a65820064210307001188843c1040001c80d02a900f00d4441c0c400c0d60141500300d9401650b4950030401408081c0b11422020301079030280d05542c040030006000481e951200d50085032151043c01a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71575379 1250 71574129 71574161
    0x206180303090618090c0a0203030c0c031303060606090801050606070605041b06020a0b07031a1203040503011a040608120a1d030a030f08060613090209041d01021309020c03030f0c0d 80
    0x6000b545040700c40036a02404240600d8203211000c7c400a60300e010040007084104e90005004040e000c080060320521280440011402600c07450000c0162245108240100340940004075060b030040c020030380f24200181000e824821683c45040c051324014109551402440d5003401d01c0c0d403000d400c6240648801e400030718010346245422040d810005283d1001c051800c0c51070414074171522240351050104884043e5403001d450b1451b82184540c1c0d000582c1986000c0210038020f01608448600180450b01003180e20341d41ca10781c580300c42002c19034111442003003003181c007a580a17034000858205483c140342d41d885041030100e80740c081558070075400300c3d0901c0075078000d0b07561014096520500580309070342000c20004201d190038030540544440c441c3c0108201d2800c1e26031341c1c40042d0b07180701d404800300d241140011301d900030740c801c110540c0090b684180100300305000e03008540300d400218005515507622a0140e110040300600f0f02800c00e0360401c019481d01000e406107000346511112 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71576629 1250 71575379 71575417
    0x4080f0604110105180f0303220302030106060206090a1407090507031b0e13020d14130b0a02040506040b030415023f04140309210607090302061803030906 68
    0x401d00606844030761500e04004041203103400a5175940f000c10000c1d10103a415415603001c1d10000b0f0f00710701403000101d0003030440c14001044980b03c2d48404080324000e500070483c603500c58101300d80f80c074000c4450b103c01d0f5000001880001c1c000f0060842080741810540380480d40b10498a000d442e4103031010000240c440500d6038407076960100c0d035144c02d285424401e0b6603840801c00301e0f44a2020400284070340348d0104104108400e1504a003800c0755420840005510b071800e2032910302d0040c03d60a4a40781604d40015599422502c205c0741501c4c001080316007801e280c040c47c0e41c10356000030000c44000a00d1020448040c0d01800a440f142d10034880040f0f8207101110500c146001d0000c0b24400540341285a1107400800d050306030300303e40c000c01d0001c51380302c8402110386544a007109140d00940180000c014400102c181280303402c0c0c48030141ca141d900e81d0641150005400d0101941c0440d00b00113100e00b0042000700030381c2c101c6c4043c041d2811f00000000040b083d80050401c4019540f01034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71577879 1250 71576629 71576633
    0xf030105040b18010b0d090215070b010b04050904080702040207020a0f0510020615040903021f0617061e0703090b0a140108061009180204090c0e060103020406020604061104080f0604 80
    0x3004240d40e001c001d541c2c0840d011504002074090003c10f11030300400700000a520031420b0130700d03045080100d401522204601d0303041850b10300aa0b10661007a500020500b001040200e07444007203c0446100808204c040d071035030780354000c1c29448524205d07070255007044200016250b0341c2100300109100c2030128841c0d8a0401440038502c0c080000c08210341107001042080e51541070701e04000d03042501c0000d0f01d030f030b61303440d080e45803046000d140d0040c0310011021b03c036107110382c1d04880d065580c0648840c4c040321150040c4c1c0d80c1c1d41c0302604d402c00300d82c007010050f43e040f01040c0005548482d072460b001c1004a19074540d02c034580426a00000e44075143c115105224000b070998500400c0c00f200203000918255104a014072050b0045084c46621984030307000081c52038450010698005208008040f4240341c4080c400309144114818440c0e1400001d00b07a600910941e8201d480340d4000d0039690366540e9655000300000031402d40c082c1428440400d801c201008105a42100e0074000c00943c107180c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71579129 1250 71577879 71577881
    0x5040b060a0c0f110d0f03021b060316030609060909020901080c0105030a0527010b0915010906030e0a052509020f070305031b0307020d08060306100e0c07080f03010504 74
    0x19102402414100301c01c1c1c40300303944075840d2481d80360000a10044005103191001d4842550801c10768041c04060021042c0483c580800c20854840c0c3c007200c0c0c91601031600100c0403401c03903031010f5204000340300003818200c101450780c500c00c2491400140f00758171041d8840480d01e02d500b056282d80d0b41c44516000714240619030780d0141031404014014060340c00300003440351000a02400307a95132140040744401d0354020103440c4001d0000441400c940b040402c80d4000d00c0c0c1c0c070180e01d105611010111f000c9038404081d102c50100180e561200250070325509401130414200d6064541c440d040c45840444c0303050003210004202184442c440c10650307034440c4440425a04555111071041103440c4c3c0c038000020032514510781c1400d00d15120745e148402d4017032490a060031079008000010410440d19030104100f4508107042c0c03100740168460209240c1e80d0343c4202c581840c258000841440594640745146d07a00681c00700e000e0345084001d603140119078000d942c48441090b00800184014541 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71580379 1250 71579129 71579141
    0x5090d020f0105060a12030e030a0f0209060108060609060c070e0705030f07030606020703110424060306120c05010e030a08070b190b09010306020a230301030317070c03141209070504 80
    0x40390740280254100580000c00114861042ca4014441840e64004050144900c420509801010b86a00d50140c1c24162951031682108034840c107100c000080003503024404003030140d940640031604082e40701d024070405074000c8280310864415210300090740790142c05003a100e16510340c2e400e130b1a800e011080120031400580507105043c10583e00703001490b40000c5201c21641c100d0524000010043c000c50010b1251811660114203081c0542800c00034030180b400489910f90b40800c807042c0d0b00c9203050b680c0350b1299402400038594200c03c0102c0c0d0321031049504440b8000b015a8814103540e0b940c0340716540300e074104540101464007000038929401001c0c601181904070203101084650001400031801408020280c1d5030101b908000c184c40b500c00c075403001004180404401c00130821004060b0402d1004038001012403000e0b0030400b21500103d40aa002501e401d4840710b00c42d84c00351644c0c035500e20940c582440c1072091621029a07001c00710f0241d541c00c40605400741c00d003070a000035100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71581629 1250 71580379 71580403
    0xb0a080603060903070602130503160302011803150906020f031e011a1b120403061407030204050a0b090102030d05010e04050d110706030f090203030f0a09080a02150d0603050105090d02 81
    0x65020011802401310840d07400344e0740300c0c40040c3d07036001034554040640003a8000c40d405200f1126001212200d1aa10708281c80c000d0302d4a064038407000c00b02c0704102c0428000209401c0c40300e80003071155101a000f010700a44105409420200d20300d100d002c0c203030811501400004450008001c00d03140c004150741c094001c2c10a2050348415000724505144191035107488a41c42c83c00b0603108448080c00242c0d8504807229030b8a80d9903035241006005000e60440e5400070200d084040746c1810702a01c201e0701242e030081e0290081514190210390b082d0030404507107056000402240580311110708c95540607203803a84a000c603908090074258035010308011824103200c04044049d89001000540401f02c81040c640400c58681d02140303203001d0043c0c0c44001f501488045140340404031100003070564600555031740c40701c8035a1203880654035418520701a400000d4061100380020102004000c1c2c5800314101190055403951840e086503401c850a80240c3c204038400e445450b418008544814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71582736 1107 71581629 71581633
    0x220b2712010c12090302210409060e0a050603010c1d01050f0406020f0f19061a0d06020c10020301050901050906011101060801020d0c02030a02060613150b0a080603 72
    0x2040b03800e0440e40803c4140c1d0072103070f144900740b080020751509980100b181d101828107443c800d0311403400000100b03008000100707a01c04a401940000c14495814040f1031030040041012280c02400707092090741445400d001d2107070310902c5490f4241c070441c0b20210201000340183e500d0300c1000c0a6990b20308011400064a0f500403800350346401040b410344403980c01d034080494030303480e80410701c6c040306498100400218000b9400b018000326081115080340380740b02e001441e40105820210307129030f00098280303482802444021440780304510150304650508002843c2d4120501400340039100b5080083d1050f80300c2c0e0903181c2d071740c508840200901500c0e0154180130b0740c070030003482541c2420b08000c0400c02d44000304894903001c07254054583c988920040100081064032000d8000c1e0700d80d0480034603405181d4a07080144580c00c1460f40d205246980500004c400030540c030300c25 = true := by decide +kernel

theorem cover : BRFrame.Cov 71402879 71582736 := by
  have h0 := BRFrame.cov_init 71402879
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71402879 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71402879 ≤ n) (h2 : n < 71582736) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
