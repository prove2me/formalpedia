-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:36.26553+00:00
-- url     : https://prove2.me/submissions/70d8378b-3420-410f-94a9-94b5c7738407

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962949640 ≤ n < 963129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962950890 1250 962949640 962949733
    0x41a091b011d04180f05010504030f020a32030c03041d0408030a02031e13170c0705060304030c1721010509070e04180503070204050c090102120d090f080912 69
    0x484e1009000d80001c0c041c1c440038018194043c030702440c001c2d51034040c0c1007032000040c0e80d42d00041e40b008140745c409000c03140c104040590910340c111b0003802c94452215143c1a040c2c6560000d2000c0c05d619040001d00b00200c80f241c0c1c02099620130b441200c03503c0e41c9032130b80710799080f404010609034043d50000002056030396a184a990300a40d050651542c0d4200300c0d50201c48505240c0741159145207100541100400100c151000e41d07042c400100000c604050503c101c40d040600308500340642e2582e104001402030b0841c14019258100d81e03900c0d2803910101d0702da14602c541d8901a8007202400600c41d81e220000c4035940f0240d1420010305c110300380340104000b064503048054100d02e40505500411070080001c0c900d050003140d0501407500d0340c1003110142e2084140b0640981d00007403a9070811031216024240c080440b1600203200d00c1903072191072000700c01441c00c07034861b41c00148034452441d00c80099401030201d98001d02005886400f50f082c421121080c2c2c1c998040224042c003035030400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962952140 1250 962950890 962950931
    0x108011a070215040305150109050c04090b061e03070315030230100605030f0606030a14031c0f0e0d1b1104020a0503100e0c03040b041a091b011d04 65
    0x45940985a81390303924182645c03180c03120801515101000000001c40660901400780140c1d1240d103001d01d000d142034440e0300104414444507801c82d50901c22264a0071076440c0780075100041c02003481d0740303191102e001812190f11460300e40d0b001802d03000910140e1203440b10a20342c018424419104080c0c246448407100b000e070f05521405200c2c0811813024040c0701d4100d2422602c0942c2103a130760900d24500365855040840d181b9405030b01c000b403c030010170030b0303c00e998005110310740030340b8505180800341d400c0340c1d01c0507030b049e8602d00c0d00e9100d140540710680c400c050309030b10524080c0840c0d400e844801081008000c200c140c0e110803002c0a00203110440c0a08404600010400c5583e90100740d00900181c0080b030381d2041110343d4403400030f808030300c50512a04c21405140c0a901d1940c0380d5a0f800c020600c0504181c0e100b004190003044c030800040e8045000e900041c000f0520040b0b00d04c2150f01201d50320304404e0400280650001c02150559814001d402045902094540c0191010303918540f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962953390 1250 962952140 962952169
    0x2031905090441072105010305060402010801240f110106030c090510031101050d1d070807170c0409080909042402120708040309320108011a0702 64
    0x10725054894207801403c1d01103405410510b4211080c0340e41034905001001803c01c60900301265074400900401d10615401350fa0002c140220703040c00607035040c00b5007201c009030400c0b6038507404142131106540c0c010b00c1e40e500500562214200d03221042d003000400d000c04582d036105000400411382c662600800d00e55502107140f100800080c0d940741090020801a031103043e040a2400001c0751191162000120a482d0045a2200c4080080c001165960300c04d04c50045143d54030004089a0311800e02d00003600301241000b44400350802e11914240a0107502820310384021f468410000040440c8202080b01304070781c0001c1c0303440681811585841110150b0390b11110090410040100c8205001c0d50030714408001d44030300a2810041c012031140c0106503000c003070340800142107907102d4102d6643c00f900c285442e03c1d0003650764034603403020b60451556920080c00302070340e24030008902c9a0803600d11400d10302201f080d4503181c4420000e04c403c21115050350701c00541d1009540314854002e0021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962954640 1250 962953390 962953399
    0x316080c010c02100b010504050907050313020603071215080c1c05030a11101806090f0b010b0919030209010506030a060b0708040e0f0403140702040b0616050706020304060203190509 80
    0x142e00c0d800020740780d061a500c2d686641d0704d006984c1c0c115500c86c40a890660b8005810f00203e030715035040c2a10799400044c403128102c41c0d0b0707034480c00068950001850140b841d0f51500b40c08141400045803c0e2025000c00c100d500c00561400c010740740f800a104442540e0642d090a800b0840c0b81c04c01c01c649450354005022840300146000c0b41c20f5010051a03842d0715000140c1e1406080600c40da4180c1e80c030140154403004000710b040d00440c403e039101d02140e44c03044842c0d1845810503a14514412002d901c407541c0c511000c80c21411a0528140402c1c1425007140c13401403031800d550009041e0300c0d0602030f25000d00804000a5080c0041d03900403009072a20804843c1c40c0d082d9854032250305e50180c00b031030f9071528003280410300300c02070704503003501840e41a12554030340c0300b11807859020b641144000703903445074844019010342e03280c0c80018100701c13400c80b900805082d00c0c0c0c00c015280001da0b0f4000000c55104000401c00142c0c003200740c84150801c8501d030003915084940c111007a0041406581d0300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962955890 1250 962954640 962954651
    0x60a0e04090602040f0f150207090507021603030806130212040813081b0406140f0f060d0213090b010507050a1e02030609010e01050108030414100912050706021c020316080c01 77
    0xc0c000411002c4040320b050710011a0011f8403520444500d044107542c03003000d603000c0c0702d0900201c2120303007205602040f103104680d21525401c0c3c44210120041d4030070b03008280a6014025031b0f0070000c05081c00d403c1464410b44c500740410381c4079548000020006001c69101080c01811000e00c030610340b00410780002158115001880c85000c0a4110350007584210720304000069a134000c44d2500340e580030001c01d54414007001409115003044294a6a81c0c415010420300040554610113010525810311110301c4e000d0820400800720740d10000154103200050001d040010300016036803224641c80741898010035105080380c010808070840c001e5260158108203c074000c0150311aaa1104e2880f00a000700d0740d0782c0050b0390301c0f0310890044481504e58080900914100301034a0040c0601c10324258601654681300c191840070388005c200e6564000b08420800c00f0750401c451803400000c1d0068880807050b80d9806590b074841c44402da242c0d00c02e044a2841800f212109640955580e03900078080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962957140 1250 962955890 962955899
    0x1406070807080a050601170709270f02040302030d050f1308030702030105070306060e09040c050418170a0c020f01020a120c050609162102130614090402060a0e0409060204 75
    0xe41402180c01000148001001442c2d0160034001c01e07000d45010307194000c1d000c041800c800300a80e030081050040c49441200012404640401086405004014203289540901c1c10303500b23480c1005843c0408074010300c01480503036804100035014903030904100e550303205030b0118081240990310348000c01020014000581010100060880510841c020842035540350740980c01c40b01c51f8040c960011b07240c01c85490a60409052154005004540e540320650381c580004059949003050741c1104502c400081e03040111811402ea07900d403079054060308124081c400100000d00d203100281c42190800e1684075241d000388021451260032050812a01c5c001800c0075090328400341d001c607000d00c503400010714600702c04200110b000350342c047c1d1100e0803446c0c0648040c88032200c0003012503241c0201d5078800181d070b030041c2080440396004d0022a00924080d49284041c00d00000309008042520402c001643c0d44000c80310350742c0490600078a50031440700030400801c0c601c0d0004140c54400280801c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962958390 1250 962957140 962957147
    0x518010512060106050a210e0a031202041811070c0b270f090711030a03060f0501020f150a090b15100543030e040e0a0519140607 57
    0x28140c030340c1500d40c0324440078954140c9603103403002d01c40c107000030300e0601c001e0704074074803910f44d10108440b031040d41041c00811040c5002298504114030040354032050105007015023044015182c03549100c4210306151402101c4200a5070220b076401e00c0c035944201c8240481210b500381c0b10f039181c100b64102d0a0380d485031203144c00d950011103059180c078031860719180041c4000342851090b0501130078540ca030200c0c0340305200829402030035503410302030395107480c00503902d0410141016a0b66a907003c50410b140ca0707501e0501d058960462411500002403400e50038100068001000440240991481d9503210005004264400004000c01c280409100d90385440140313400c0001811100042c5032030001005440170307c203001510026005c8050340c0c00c660924072922072510610f405035444c42110342c1f00e0304030107040070280403000f198424100003014200fa10401c000d9141e003000600b8181703c942c0304c00c2ea0f00c00c40743c41c04202c00c2480c0e081c58410814a004c41c45000d0407800f040f100b03a41131042015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962959640 1250 962958390 962958439
    0x3081b0310081603050304050904050a05030a0323010602031209120703090e0c2a010603020d0305030f0601021f0f020d0c0903060b090f0103020904020d0206032a040b04060804060605 80
    0x10001c0c4605260fa038852503041544000700d940c801c005624151401c400e002142a005000395210b010300f017900004a81d0034001000c62000c04d03600003508142d070001840c00070b1002601c0403c80c841400c014044180c0000c21240c8080c250303a0303005841d5681c03c1105240118140380308140300000309003003081541010141056461401c003040c22a80c60902402090003424200c05c4410000b8203c14260900503100505084200c00041055a203d80105240010001c1c04500050000040208100d60b1050356600f086091018000c5003242c40070b410380c1c084001c4a5008001e40e1540ca00600352419411204250309058052024611030031018041d10306900c01031f21000d0420707406002c28030345502581c4c8100040000080302da4216001d0201d64071005100b240c00112000c242c0c00961344140203103200c0c00070303012a9884006241d00e24194160400c40d4085540000d010038002c0c01c1406058506840135490310360310a6a842c140003000e400e0a5200039003196041000132003155005203035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962960890 1250 962959640 962959649
    0x30110406051e0306011502120a09050303070f05011a060d021810030507090801090819030914240f071817030910020d0f14130b070605090303040302060403081b0310 72
    0x61340e1300e5170307030780d41441020100c440c099000681280140b000d0345062007000c1c0c075003030035075140a58060361188040307881d5520441003690140f01030105038042103800d0040c00781c001d052010000801c0f404202280050207511602c00c0c4090700400e54610407041c060160540800080000002121202c3c0180061009842c00310005010140225140d0414001c2c04125a44920b081d0720b4110900907140c0e50203801d8020100301601c8800381400b1411a0307481c68600410b0401a200203c0c0602d00d1100d440c110540040c40c1c484204100103600302c8072440c15034031103064181039403000704c4401a11031202a0740c0110040d101990801e017504000040034020601d000c1d0342441d081a501c5000360399800c007035a0b0030000603000001c1d00302c0c0039100e00410b040110303c42c13400c00d003070075440540c042c08004d081d000100c1100340030564100b40881c40c01429040b180c414055451828991002921480c2c000c0000d402e001c0071101040021074009000e200802c5c0c00d02d038203a140d00b4641418100701c4064403c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962962140 1250 962960890 962960893
    0x5090c030114040618081e0c010e1b04060e16050417071a0403150b060d090303090c0603091a07050f0a1d03060c16050f0102030903030130110406051e03 67
    0x78200d18520407451700d00c40390820f1001d400d02c51140100120301130314108a07182d6138400d111504055000b40211900d18410801404040308003402d907400c007040101aa03403082d42461404c0003140003e07200160441c0c14441c842c40c10081c00710040d2414411a8005406414101c00c0301c5220b20000c83c0310000d658940c40c01401004004228a0140c0070f64003000d02100000c40d2100c0752880180e00c10721307050101421544c100104030f00c00c00d080b60f542140590209895524500812002e141c03d4400f4060f94281044030740c5090302e40b80841003010001d90904010200410407003402417069840511501445558130a20400010305284022581030740d840d62141ca101240c1c17401084641c4208481c1c1e01007400c0002403040d8428144d45268142d407540038100450240c04000c0c0019071085980d0b10042d5a0780d490881410300c80107403401464494825261880008242840c1e1110000d03044202d24080880600000f001410795a000355030210030110050a04185515003070b0035180104c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962963390 1250 962962140 962962151
    0x3060605010e0913210f02120408151003021309051b03100c0c0b0901060e07020d08010504020315040f06060e0319020d05070b030712110a020d0305090c0301140406 72
    0x1590425400070761207501c410010001003096202103111a501360042c60104200c054040c2c40065410800d51120006801419100c2c0250780410500c00c10920400504e85014545aa015201c1d44101c20810f4104515000300b02103010300702c002d0f0302543d0028422003071900400703500401010318110844050040c00910344180703130309140c022030740c44002d80600380c907281000b1518000c0a10900810038450000317001c4010482200d602c51003034149d000005000c500740780001400c180014030010856110030340c1c0441081c1c1c00242a81190420394000d81c80b40c40356405a80c00440300c40510b90040d1608191591880032382d0400f40840c0e9083d11402d22408001d424151544040b024002402c200f592049006003030030441d01c403038140107a05446401c2d480e01205121075205403060b0000034500079407a100a0610320542082d03100c40552240303000080d0380003940b00c4440f102c1040c10302d541d8000042c1c51b25400d000c4890000c500800820441041f500042800070b07040d40e083e2900351428 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962964640 1250 962963390 962963399
    0x2d040b071b180f2009011101050a05060405010b270d0203030703030504110a0b070807140d0f0e1816031b230c03070609060209181e06210a0813030606 66
    0x611500b401c000c0c1c1594031107605954610340d400c0b01c2d0300c04807110303041240c0ca01c03000200103020301c5000c0c09440c000ae030101c0e07142080c02c100415140d0607000301403480700030040004404001e48076044c00c50300070300105000109580c0012510103000c1c0b0040e415001c002031800405516501c1180b01d036104e602e01c0ca07243c1001800b4490000c91a00030010040c01c01c000401c04200084042c1c080140301d0042079101c20700d0b100ca101d0804c0b0700b19881d00c0c041802d40b044258503e80000c00c8e208e42c8132084d900950005503402d00024203900c0a0a17801d449540f290000050a11941186d919103c178103c8144000c0d55800740248060610760308098450b0b200f0285002c00c0038480d00301c1d0100100d100040d81416120345403100101483c64040302d00e030764200000e400302e0f10740c800442c084408652603000c1518056003800724022081074012611f10403102002965621202100900f07080c4501d00141c1079035403192186840c0039010007904a110126088800c03401008134002a244640b4050060b00d60340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962965890 1250 962964640 962964671
    0x1f080607090b03060310021b0105160906031d070b0405010306051519170a02071110021902150c03031b0a0221070b010801022d040b071b18 61
    0x56600c0030005000000400036220141c0142d0b42044004059903180140b1545420483e444034510b40e00f56401807240d00400c40081c4265a84408181d035800c15a01700c400d03000713290480c00c0c003406041c1a40c0d18480f40c0c81c000e83c12550380c032001601c02200c5119403504449005900540f042a00090800c000450141090390202c6091801459490300b000500c1241a810f903080c1c0114200b0409002c134079207403400620010320f002d040580c00051f45c59182c0d0501c1c8102e40c02425925010b280d00300c8519074074540c00074620340c00044402030500c3c5402e00b440052140c1030075030a14080700704003052002d00c2035404401540074102421714110000000d03045032555005000c01030300560854103012403203503c058580110914400303402487c085c45940d030034003c41402e8114040580d030220705c200b030441484140c1c40d820b0110705281038003502d00c1c8900d4407041c42030303000d009012403010030403108202880341c160503801010500b03050400d032554a440404d0803200c041004140c2084500b1207008007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962967140 1250 962965890 962965903
    0x20705100e161d0c0a02160e0f1f1401020a02060c1b031506010e1309060c11030f180301020c0d0807020706030513140f0a0b0f010f05010518181f08 65
    0x7000500f514a961515001c2005800883c004c4055010305888400c4113512040d050700030b407201d1a00c00d4258101544008044c940044c0103e0400700400c41c1041406401c03d85d02c2c0884940c0010301412112020040342048541c130300094200300046000140d06c000440e0302c050300410580300c0b954004d00e0900305995140140031042d0041d034008042940c83d403243d030b031000c600c110182c800300c0c80e0b80c1641c0e07020003120200401074610583e13800840540561100b00e60a04440d0607004606000200034007501610a012004a6140500c0c0c0100c0c082d0700c003034054607004034442c0c040c0c448030780d100500500090340884440c00140070307070f100209c2e2a80c064407407103001e000100344171284848541d851141045c003c13003803010f661050000c64040301c00c04104803c1b100740b04090004850400c0b0162440f1404180c0050a182e0318040050101e80d03031000c00c1c1c503000c0301030406030700c200514200070540311030118018200c000c104200304048200454000c1c5104034048103c18452956502080d480340c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962968390 1250 962967140 962967179
    0x1003150e090d0e01080f060a0515180a0f0605070c030b040305431b1202010e0904110d0c030203030d02180904020906010c050102090303191101110d020705100e16 71
    0x20141000f00d01034608100951f58000c9000d0002040d003034a0700c0014581c0c10082031042070201d400541c000f50340b1011502d41102c501300352281f064107400e026031152290b0660041d107040040101d64603050110b4440143e005541080c610321240c10305040081a80e80700d10884014100c1100310741d002201d00380d03174807804962100313044260108018030030704500d0000d03401500d014016030480b102801d11980890011710b40041c81c116421014800501030b4520b40d04000c0c0314020b19003c00c401305000da10030842c80c1d0003c0b9940141201181ba00391181d04690b00082d401d44400310b581c03807890000754000d01c1032a40702c11040c020422404204650404115030082d004640d1501156031035014041c1414154403420015080c480b00d40c000c03d180d078200d81006140c0004103040c3d4521103400550040855088000a000ba610300500c2c4403140e115840c1e844070703a02e038005110340c144441413080c070049562014042c803401c4100c40e00c0c02da0b0b804100c9414a80983ca11100040d0080110301d00c0d0f0218 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962969640 1250 962968390 962968397
    0x7020d0243090e121602060306010201240f0b0c070b03040314040906050a080c130c050c0a05032a2518090203061008340906090510030503091003150e090d0e01 70
    0x17550900005403c0a4035590540d03403256120f41c05401081c0c9401410b681000e0780d841c41038a00700505800c0c10703603030b07100462030360b0b040000718091700021503200181d0301d00c46080b55503500ca81c03900310f0700000c2c220002414902d01007408100044039270040f070100c038400ca8940fa1000d0b15909c8080d01c9108841825610401101409054001a03000381091400c14140f00d03051002110b02242005843c1c48102e415810001304800e144242002521100404044009545407502112559a01e105000440c03500c481b1555542d120700000c9220081d0803c04159011070069180d80e00152109440892003400b807540000c3c5048030780103c142c01c43d100e0900400c5c240115803643c500e6810096104115400960200d0301e028206801060081594500002e0510b107840301420842d98007402c00d44001c2904142000480d50000030384c0c20380b04044660a104024100055000309140e0301101d916032004c0381d000903802444d6800074803502640d0203850708071103448012101c18a080c0380c82e9011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962970890 1250 962969640 962969677
    0x90812040b18120102040f0914010305190516120302010c02030a05180d170c010b04050609010b0a0306090c0908010b040216080a021203040b07020d0243090e12 70
    0x2482102c100781c20400c10203003c04501c03a0b450340403142640d125410898900e500800c0c2004480c80d14840d2408021105104030201e50540d954140c481113441d80c1d0b03024150070660564242305e803c0c00f80c0550785011244204010342e42d00102c040c00329040209401551034070104c09003e50000c81100c0d0101c03181da55113454a811710f81c016074101007a1764002d4001c0200740d540c1c0d0006a1320402d4a180920a60409807550740700440c0a09480d88801800e029600780001e00925403100350350103041d9100282c900d0340b81d020340c01c0b00700e00800c541d911076000c544c00c020b10300a8690300300c2415810fa4140c400240142d00d01c00303090006074410910000c441000000780400400e03000d001504e5242c4061040c2d640e000c0340d1541c0e46003150415602503070581d402a007408001501040348416144060000c2e00b944c40540240310340810121100c1c6059181581c0d0503800400480c0c041541d244030351080804d41c2d521510710000410354044650003611a03240d0110304221030038261a24840c440108019 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962972140 1250 962970890 962970907
    0x3a02030616080726040516080a0507030609140a111302040506070204092f040c031b1b0b010b210405030702040f02070204050f0a06170c1c12090812040b 67
    0x1e0400e01480c1d080c54030b1204d45403c0801000e03100c0c643e4042e40c0240014242401c0b41044c06d021200c859210720300740d42c800007091000074008244030003180e4101d0710018003442c5900340400b009036100300042082c0140340c0940200410b41004541c8164240c9540408032030210700601244114005e03903170f00c401c090060400518194001c0e41071244102c5500d61800318400c50803400408078442105048000c0100840d01c4c00d00f17125090405665103070500294141d1008075041401c011658010012117001108060070b211800b003a00503030102c400403940d0f03036429020000d03410001405055007107810f4550910191300e0000350103550800040c501d003116940c03c01004100c100e604558594017440b1007009a90b0320710a5901c254008044031580345400c480d20400c4070b10b2500210300a4600b401e0500620f00c00003101001080241c1d104259803d900c01904c411400b06100100403100303c0800c81034242e072101c1c5100440711420215440f240f0150701c60842070055004682001070148031014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962973390 1250 962972140 962972147
    0x6011701031e08121905160c14030c030903061f060c1b0602010f05010803030c07060b0f0319060c1e08070c12020f100213053a020306160807 62
    0x40550509106441c40916a58440d034150b00a013010365046802c0108100d0401d101409441d142c1c031070104200072625120803424503041a04003480100310300e020f442010805043d040c0c4004904807400c6a0f280c5a101c68440c1c0e80e5032260344924001d0088a0126200f03560400302d10408910240242e100107007003540840f07503c10f880c00107440040101c00790f40d00100c48d41004401070f040039400406d03d01540da40e031400356203060340308104d280c2c010410025594040030544158a43c020000709001350340a00040e01900c00c0170460758540105816006c00c01c00e044051104107100e0348044c8403014805c2c1c3c0686045010f8011000344e001030b62500e01c4000c1c480e01c4980d5200002d810f000c0305101043e250f0b00c00443d185805607015903c0b03060f0b0001e0f103031810020100305215441c0c09600e05103104181d4007c061880c400c103401000a90007a2526400c1c1462401e40340c1c0a441c8050142d03d840294188501c000b800c080e80030740104c0c4081741040041d000b42402c01c998035115544562507005049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962974640 1250 962973390 962973413
    0x30f0b010221040905040f03081005090c09060717190207050105390147010219050d0807031406091504091103010b030f06011e0521060601170103 64
    0x405030514100008942c9111318070489020300d001d2050700320310710f0799403502420b00399000d401b18540d4101060b040010365243d01d80e140c0e002144122042d20b400f002c034040351031401070b10340040c102c010000120301c01041100180a404e811004e06000c0d00318400c0c0c0580c0c4070240c0c1e0140740c2c0000c030100f10705042091740600149a8107041290100d000020610418261204040704e00b0a44d44540c542e0150b1034601c1044215808800100d602070307200c3c14155201016111044202c009500384001003036030080c00030040341d002c9028221441c01c1d4615200b5100c0c084018840d0215008101240c0461711070310480010000c2060390b14026156039041028030324005202035107030510044265882d031101d00501c000c0070311a01c03030a24121004c1e410542541c02950441d4040e920202c0408526000054200e045a84103060102000864545402d949020703411140c0c01c0745440c0320000750401c86083e00310400b030342c000545010740c40d040011180e400b104151941481884001400407440b0101c08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962975890 1250 962974640 962974693
    0x54010e01050a050717071a040c050a050a1502030f0331020d0609080d14010806060d03080406020306060403170307030c1d1c02030f0a0b09060106050d0b0f190501030f0b0102 76
    0x505d0406e10590b40e036050fa8900888030071609100c690512081001c4000d102e8050441159400007550501000c2500140d140c41000c400a10910325914640d0080c4101c40480722014140c039960f14108400d451201100c1d195000c0e00f40c80d0401440800e8012800f86070910b9008052a0450420b51601809031903800d006845280301004100b026070864400c41d110510b0480345805998034001440d401e021004124601402041140d0300010b68031a07001903105e5800000180c4944030000810501e0140d074000409402d6810311a1103c007000401461240485581c103002240100c00c040f5540f5146120b43c03030f01416914000103807842c003c020301c038250350f2003c0c4c0c641e00c00b40142c0019146c40b2035111005466040011080103000d00700c1d200582c886a0079000b440c0d103514285c0018800c1c42060302e40340c0c40f00d544480040d40c4e66a08104000c1c4d642c00200180020700900c126070540090700e10a40340413a01e400002d42c11106c06000b03117108810140c01800360400599041880340440414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962977140 1250 962975890 962975933
    0x2d10140a050306100509130308070c030c170c0607090303140a031e02040f0b090f0d030e0301050c0c010605030a350a0305070806040254010e01050a0507 67
    0x40c0803419031000c000c09442200c0302d080d1480214a401e0a0003c40c0d0009858081217041410003400400d81007510243c00c4040d900c0c0021a420050404880c3d500070560b0050200d1008000c100f6110f1040000d000d40c00300000c261511901d503403600385c4090344140710040115103500c801d02d5840101c8800f90140c03500c0d43c2000305000d146000c445060600311b205c4822216030100c0c0900203000041411406002e49800c054600305100000420240444c4c05040c40f0300c0702031000c0000c043c070500c45c01103904d40c0640280080d00b00150044400d07080048662030541c6485c00014076480c0c00076100030600c1d0441e004e4203809400788014501805810744100b883d4800e65001c141030034900000307108035800340c0d80020b41802d000100070004903014048500c51070051200d9070004d540c4100845000c0098400b80c00e851103029610544c1d02c0462a0684400c904c80aa5500303144019541800483e0241da9002ca40c10400005480f42e008a00740080050700c14040300001076620b181c1c0c010179081506 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962978390 1250 962977140 962977159
    0x20715030204080613050c012105041103010513021f0c12180b071505061e0111101509090b150301060504110901090b041d060d05062d1014 61
    0xf0801c600e4104256001d2800088500815040c02801d001220400e002442c003495038410146518803c000360b10313410390502c1c0d50b88010408006540c600c6010415003d8000d0001d482d0031001c07c880c6a162441c241d0150326050a261190500d01e1512145d000d601c1c1c480003940e191a13201c3d00180c06500d00d00f5004c0c409040c0000340b51610014204000b01301900361240d80f0003161070032504a1070800c0307110301c042e42010203100b0560740c1c0c006950148541c000e40f42d600a401e443c0100d4a20300300c55510030709400354080915052204e0380040c4045628401010a6155141c446c001105d98048014095403404004500501003204004a8095000f000814a540c03280002000c40350082c10240403c031001502c60200c1d600803074203d00a03c0ac0c09d42150809141c003000484600c0581d00107810460024000fa00c6a134862144c41034541c0c01400701c03070403840c0c038214801c00010801c1d042040c1807100185003d00d54031034504144500300c1083c2c1000c02070318028044007035840440c3c84d03541c03081500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962979640 1250 962978390 962978399
    0x210021c0c0f050a0803181b12071e03020a120308060909030706021206032401060507030302040f0308040e15100e0d0b0709090e15070503091002030903070606050d03020715030204 79
    0x10000c014016020f001755903681c2c00c08020741c480003594400d544020b80c219504003000034a00e00300c00340700e00e40c06a0b01c1c404141d40f00010241004955004001d1241d40c46480c10984515010f0702e40c244d0f0b200f600e80d980303503d03212895a4909500820b000380058025000a48641802c4c40100d030030400c0841140d00308191981c0b54026a042140410f03524030081c0104034140c50b0402c56058541c81c2301c0101d00200b44455a1007602004c140034103810b00c50005686010144a94111001804050710a81440b81c0724604502d25910503c10003100d2003194020810300443d12403000d170705250040c41408005421601a1082d213100d41a1551000014010750b010400000b1840d100fa001c07552192805410001d150701200c900390120701017031780909007101e42c10345e61841302174002c00a414a95140d41c0c0302e00d1000d00e04000800301008842c004424440540070020140c140c00307228000c00e000701ca84403018014021058040600180c2c00700c0b108010360000703404201407078019440c0141ca41503e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962980890 1250 962979640 962979643
    0x7080a050d0216061b021b01051c0605041d0319111b030f120405060d0204050a030f230d03091b141302040f03031b0c120210021c0c0f05 60
    0xf140c40094840d4650381ca000c1100b0381c42503e0317442060305080791181d820103800a6880301e5184c0c00510b03240c40e022481036640c0c040c4080d203032940520400910105511003803580a0300c0b95100d22800b407801d04840d80d12452804d8641c0c0c85000c4040029828103018100c01602c011404082c4002d0201200c0a10300c0c1c90f90500c2117000c4811603ca20041d080d00d25010b1610f004120601420b10350000072100307074000c441c401160101c940c00c0f108580c440c07041c403241e0002480307140d201d954400c4184030004200310140c604030600501909000041aa500d00b440390a0841d000c550b02041e0440c20010070014020382c421400203000300b429404000d01e1440d0f0700c1c5a46001e4000d070801035000c210020b407914000201c54620322440c0001d50525141c004d02809014007400003c0a0003107140140414200c140504030140c0e8120190f08811550b854030b403030400007001c0d02030740195245603400480500009200c80800403104203480c00b000c42e600d0845803035410301401c071030b04940c8440c0040030400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962982140 1250 962980890 962980897
    0x31202070b090d05030603070e0606370930020406080f0c03010b090601050f0d020d0902010f14030c0c030d0f020309100618090809040f021305090c07080a050d02 71
    0x424815a24542030800406107010408840002041130400404c07600d6200411003c084800d02c807043c1e00c40f42c41303140c00600d8500615803d20500c01f10f2003011201c901c1441c01c680010803072454800c03814015050200c1e000d104a000f81c42e0800c0004564040ca24a4204000141c07640250000ca403c440361f4001421f841e50350303209a80c40e9003d0044043c0011050108211042045008101c103e2004000c1203036407600030003481c1404030210f49080070144a0f01110104040140119610f241d6041d1a000808042200b81d00042c83c800c00b0300103541c000c0d111f404440702000a003e007580d84103203018504d41c0c0701c4503101480b40824098503071205220301803002c070070100c614096124903252102c10300d8801c1d401e2280d02d1250a062082042c0422110a0f0350402034041e4003003590070060070080c10502c506484550410b141c4203206003842241c0d4090000c9041c400d14040b11a5a81c600300642d200c03059605e0b1205080400c81d481c0012000380043c180c0d4801400d007681890340c09860324080342c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962983390 1250 962982140 962982143
    0x12151b0305090c04090b04020607410109050c060c0a0c09022206050a03020904020712020604032c060a1107030803090c0a0e1306110705160b04051c03120207 69
    0x303881d14184451141c051004400c0600d00b40c42c03c0000100a44403084040c1020b40041d0195400081200c180b041542d501080f81d00d0340c040901110080b10079040d860040030950703010020354003410998030001030007081c0b8004c4d00a001824100400300800200d980100ca0141182c803420040c1000920031380c0000c80180010400107032164420340c8400c151100300085c0031490410300b01c040c0070b801c1e004020344003511600d01d001030304d0b600c43c0d0021038001d1180c40409018401c2607100d46a403d40d00081c06c6104520941d641c0142502904058000071044000081c2c1e081c090382140c030a509240c00640302e05812840e11422504000149c20300700842a0025282440000100304441e4020060f00c494040103440780c0c140f0074686491100e03013200c040c20454034250035444180034004244c00290050201880850b5183d91070314100c1d503107c0da094030203800c184030880002a00183d443c207450807104040e100343c1d41400a0380d0601307103010b00c00d01d0403414000401402c0c0322143d042e202900409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962984640 1250 962983390 962983397
    0x1141e09090601050903070e0c090d11010f020c010906050f210403022406010305150405011409010f0518190c0e1801030c091a03060702071a0412151b 66
    0x20440c0030140081c5a800524060511500308102c2d0503e8a00181203c1110350f0107200c1401500e03030a1000c0790318490300080303650007002c4000d00b000384640703070451545400003600e901400004e00b034003d98030ba030f0010700c40303a0210b00011001c0018501880003000b00c25140e1070a5442c102c441000120310071691500e4020010700c0c54100410190100710b01410348441e40c2c4041d10b103452500c0b03a001040c000500c00c0d8109138a440208141d5030350380f5003081002800400074019036071502d001c195182200c8101d1441080c41c0c000000b40b001603800308000b1f070785000d8088031040e005099001c000703103000b410400a100d88404901051140da100b4100c5410792907413210440c0b11482c0030810901030000030350380b1024000004100196010250000f168a40ea1011901544000b102e100c4541c8241d4150f8040c064501004803403603012504a098a45818800343e02441c8640c1c1c1c04914012400fa000140f01203108210202c0d80d05031007041d804030210300100b2941c5a280c1c0011500c0d0071600f078140031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962985890 1250 962984640 962984647
    0x303010609080d09081f180803070e06090d080a050408123a11040801180b010b0708090402090a080307060c030605011803152301211101141e 62
    0xb440414000c0381210310103482c0a80c0d1590810000c0b0362a82c4001400240c21140d81d0034440d0000c1070f940241032a01c2e002090480d6040090800b0754440d44210b6407540000c9801c601140030703160500640706841809411800d03540c0a6640d410210742c0124117135018880305200c0040c180d5030801c22481c40e95808003a00b900d8440c903448400b6154400c0d1910b44801070040808035250034005021450200f82c9107020800310b0100046171418070643e0410a055402d03d00c0f5070100e05482072211142903c83c042c010041d80c0e0b1a80ca0f00140d001d01f4100405025080180915502d4240c028091120303000b40346000183e619540d291940c1c0c80740e40202c900c00d40350001d4561081c1c040c0700e860700518003800d00d01102c0e006d25005988100c13090000038181d0004001c940c4510310980c2c81400b0601000c107881c114001c00d9014040010300c2489040e4843e4a420326850414621500ca1086139034070451041c669100400103507a01460f001403000d00440604c106a84414003401582c511007080e1144c65a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962987140 1250 962985890 962985899
    0xc300a030e090403080403080612011104030507151215090c030b03060919061e02270604050604090f0905060a0207110f060f0c0a020d06020315010305040c060e060c0303010609 77
    0x4115400308405224890300020030010a170802c0b8226131260f4103241c519055903c0000040828801c40c00c0210198038000081c82c00c400fa02c0010001d0302c0c00b130b500312400150748031200300d00102c1d1400140005004071a0303900016100b50401c840209110702c0803c420b07901c4520a0044032511501100000d4035840044e0b2542010f011058120360307140080c01d04904401c003503000340303c900500103154564034201d407411444124804c00f9001c1c1052010755481341410450401d0740704202d218012039134080d40841c22803904804880071a6000f4140c030b403c051408031460f005005403900040760f036407686c1d03080e0300149003802040c0c89801070280060300c0c0d06090074070310305c0d00100d81031060080314040707210380c52599028243c41050b001440f0b00c55942407100303d041d05203100c040c0c0003500b100020101c4d504010807500a540300f2907420400c1840242201c004409485040d5406070948100400a100b910300c581103d03008194050b01d41c07032074415980d170b01c07a2842e84241c0c000400241d800c43c0510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962988390 1250 962987140 962987147
    0x5071a0904110d15030228150e120712030e0f0907110d0207050d12170108060714030421050403020a090207020301111c052715060307080c300a03 64
    0xc0220704040c01c1141103d0a640c08540301c880c40c01000542041d9a07414a00307c2540150030307001a0080c1c030300c170180c01c40040328043c0c9102c084400d064448c0f141600c108000090001e012412100c202c0d03000411940b01d07480071303660388080ca500a500702000c02428422a150825880d028103816a00c1401c96400010003500344061380d1070b01d9046402040c0104201d41c1e4007002c40306075980191a4040122001d803003030303a8510854a121042000350400050175840220b4001d20500e00c0c1d407203810020b0071980311507600e44000c94004107101c0107480c41c503600380c0c5420098958a1070a041041c45c3c662a42c001070400d5442d5805800b40d95000240300045040030300038002600c004140d01c07800c00d8210b0103609207601c1d50944c01d0120710391303c100007245903058100e446080c4040060b10401d10486661054071155002101608448180003152050070002459001c9400074005803080300d114031304010085280030305080e0341401c03051f6400c0b400d1900000413640400c0074802850349441c00d240c0503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962989640 1250 962988390 962988401
    0x6080313081603020a03020402031f09020c10050112030f0918020c070b090a0b091c030e0103111c05150a06090906092d0f0e0d08090a05071a0904110d 66
    0x680400d02e41003007005071550100c1c1002d4903411580580c0369950b600c1d815139109a051240c1021399114240015455095402001001381c038100740e9040b030000c12001d40c1995028840ca40d010102021a031000c40d110303050f004841c00f00c03894080e0180d5503a00c50880104100d401c01401c3d541e0000300e00d84c0c0c4040801540009103080c0e8103142c00c01c081c6100061128046104504400301d0008601c1140e0f0355034801c41900c6101000401e80c800070a080003480b050340c1e88071060220349415081820b100921080e0b81d044e00602101100310250500d009025110161860082c40d100d00707200081c1f030352601c66410203045596102c050991905829105803442c540c4088841417070400441d644030380c1d090314003140c49040001100381001e4842c1a6000f007180e044406d40035440d14100140c1000041103500c0c10300728a684101460b22209a00340d00c0b035030b0030b407001032140d4000d48003001205941d002a03803641f4030800c07c02d814190544042026503100044500223014000303100c4407810b40320322a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962990890 1250 962989640 962989663
    0x1020106170745090203030a0305150405150f01141b120a05070b091005010807062307030c021c11041d060601140409180519050c0d02040608031308 65
    0x503465a4036840101c07420035040080040b080c03c640c1415224400e0b290300494001c9130b0184c00c8070b55903030701e6803001001484159842d2080900f0341281000700c0ca802d008141c05840d490701c2c0c1c00d210441e107204019480e483d03107031600d040c082d041414806000181014240d20399802d200308411000a241c0d490134100b0f001d0702c00034207803018080150b0316035100c410307038002641c000c0c0e5151041c0c1750303007040318030380440c8801a004017803c000000c10340541c0880c0e200304941003519034080305103100e07800c4504250241003010301d01205201d1140481c0c0b207001c46c40760890000d003070010150442d00c3e02d0010b000c000300c41510450103005061002e4203051003034990741c1d4645554202404003500843e030720382601500a60410064407244440490300d801120000c0c031100c0340400c100342e205074981e50414008682a00c2e5406104400c43c0d1004540c0c0c20240c02581c0300307000d000030303155200422141d0031302101e0583e08956114804980884100300402204130011919510b8602e017191540ca058402c141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962992140 1250 962990890 962990939
    0x150409080706150e1003031202040509091501060302040513090f050d05070c050906030d180810140705030112060c05250c15020c01031e0c050318011b0e010201061707 73
    0x41002c2255044813101c00d403a4145010340c080c0581c982088040c0c001c541245601400020511004102c0050460007118000ec0c0c2c0d44840da80e00e0748160708a000300c0c8281c5412401c0b072a1100b03106403a07680281c064030301c5030504c00840c2c0038980380c0500e002068100c00001c2a03000540c3c0041c01001ca6805004140458100140346040e030042510b03a15209500018010661550600388507071100d0382014010b510101c804003240c0c05400c00c007408180b032914405c0c042c6000803e08441c85401120b06032241300200031000a95552183c00501c01031888504016050000500104843c0b10b2014440070300c07130290344440c00b2400c2c44000e24801e40d01c2404c280190380303d0350640716004100d0781d43e0f04409007000101038130095940002001c004400b0a1304a1034280c081c001690050080c602658000007501044541100c646080300c1c0c00c08400c0c0002d503400d1400b004528440c1046c100184018400400d00a50304c001000607168140c440c070b0900d42043c5814410b03120311107080c60030412001c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962993390 1250 962992140 962992169
    0xf111009030503150f100503040f240b0604060e1905090406020918070905101b0302010212010f05130f020c06090705040b0103091a0403091d0a0b0103090b15040908070615 75
    0xd0003c3c0117031046c6014041481030210000301440802c41240b1080e41d003080121804580c1445004031241c4d4468060030501d03d001c034020f02e0f41c1000300644080e100a42ca03003481c102d082c6420170030409000060396440e484503200114060311a4104240a98813071580940c954260208101c000c2d0007618921209010000c100b0010592000c119800c80740142c4082d1140c05201c00b04554440d03090381c0300f0340040224140042010b80c15401050b040c0540282c0042c140d0700ca0480940c1644188190755110b05901d54141c1920002e502102c00041600e8006207800c0d50002e09074141b06040301c2c001c2e4103400001c0d082100c3e0615004418010609180400400c07907542e84080110206a08947e41c0d00292030004040600074042d1601411284a6421010070300070a041ca0b503400071100b0500c070900707049440c141c65000340108130b5096445040d00a10359a011401900078500c14900c5500a4640c0c1070000403030803000083c078415000f06000b08100401e02c588040e5a070456010004101c1e288 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962994640 1250 962993390 962993419
    0x8070909030806030d2106050303031e0106050309070b0f070203010c020c15040b0d0209040e0a050601060e040212061909060b0d0506030601051809010207170a0f0f0f11100903050315 80
    0x320081481d81b00040c0075051610341c2c524540c000300403d804c103a42520000081c07006c4880400f960f600d2011702c140390320b0724aa032105000c40c0c49000c00e8802d81d6581c0e11400c0c060245c001040081c01000403040000fa0618420340c001909641703103003100310b0160300812840030f030320304106c144074035012030040000307140518255883c3c071544510780102100c0d80c4d01060070421a0398540040c5007403030b8154201c03482c0c42254100307241c41d4402840f404001c1000088400c0c0b03107003000e00a4403044240c1da40d0380340c403076501c0c10244081b070b04201012000c4080000400310700d0440170b10408010f44542030420b41c0303a0761588100021240041c01e5a40710354082030040105644070300c2c0b102d0350b0041d0310030841c1d0382d510341e0040540a80a10380c4000d001424900f43c4d801901c070b3350700280c25124421740d14003403454400030003510340c2c8103164000400030381206c882006160055440304001c00c122812a040d0401c882e18210446201110807000103030b0002c140080f034001507241c03800c607100c21110034040b0001f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962995890 1250 962994640 962994647
    0x501050405030a0605041703190b0d0f02190e010b1c15060c080408010203070c051603120f1815260403080c0c06010e160e0d06021308070909030806030d 67
    0x241c40c40104410f881c0c40000302045003d6440703c0d452102a61030235140e0400d0b80b50301521482e41c0041c150031a2402c40000e80c01c1c513080101c0400035403c4a404090500940c080c00350082d40c1d00420007540c01c1c0c00500007100346020b40401d00030300302041481d8441011004d0602a9407030207058070013441c02d140c5840d083c2c440a03107110003203544500b005030388500c8a02d410782083c0120303400b111044d4404400c0195072504a0301040001d88218240c94465440507455220800304c1d02014201d030040301400c003100750059586080c1c1020509143d015521050b08001d000f5100d50801490203441e110441507481e00b0841e1141003a40070407595241071078000081030341403001040603041040540101d00d5000c1e11134210f0344604448020b841d6950303159014050420340c00e1302d0002d241107007480032a442d81e2240c0050031500800800c00c41c503100054440306d001c0c0d006628004089000410000740090003080740400030090b904000c101d04c0e40034100500001c3c0d0060005002e90055051a084141d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962997140 1250 962995890 962995903
    0x110118080a030b0102120408060106120e2109030102070501060f0f03080910031811090c0901051902070f080609060a142a070c0510030c0f1b020a12030306050105040503 74
    0x3802c0c035000030301984a000407480c20200039014206000300103804a02c42c9008100141a0b031850b890382000c016101501360201c4a541c81070061075000114022041a05000420285d1440400c4181030008200000c0e00b240e12941040320240c2d520041042505200700c00100200b4040c42134011052443d29066428480e164189218160900350400124002d6002c4180c01880c142c403100540020726165014041c0308440a1041700524009030250b0845802c4514420040e542c003410019025000c01e03d44030349210b51419400340050108500303d40c01665001080d60b100201194103010440d10b0415101400c480d2402e42801c403042c0005281c10301c171541020300d9214a005058241404480c220240880d1803003003d000103128051001d80d20000f005d450007110010340c490101039064040310b035285c224a011901404200d01228090041401071300b88054070304c900c0308050b60006030040d01c1c90300100d05000034410200b05040d4035100d0140500b0003820406c1c40c1c6410f100c0026561035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962998390 1250 962997140 962997157
    0x1030605100e1f0803090d0b100803070b010e06090105011b230c0a120f23011b030b0301090b01051908160602100605011b110d0311011808 61
    0x3511031000c01d079059072011034100180482c200484160401822440810b02e0b00c120052406002c40b030f01040341c0342c02100b00c41c08084010310800500b0702980e0784c8a1a00300040007490b108140000024039150207000400d420380c40380d00c030070b00c0a40c14450b035a803003104017a1215018106030401030006036080340304034a0075107094000401191f4145001e54904404000c01410020000b4080c502d030503001980b078910300030469841c2c0003151244101c010050840704040d00c6038502041d41004141c0100303c1d02140d200c2c160700070304148130741d024071030070f64004d590170030311206200800703090040c1d042c0708160044004a00138840901c0390780f0346203450318043c0606489406610b0365076480c00250380164004007214402e844003120346082c0c1045000880c419140075024801000c1c00140d00c3d8031403039043e104161142041c6022001c000d0446d600781c407008442081d0781d080303400040d540d015960301c21103200741d45288001c1c444002d040d0130350310074241407500004031542a0000500c8801a9480309 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962999640 1250 962998390 962998403
    0x70e1e010302030606121603030809240c0a0c060e2406030a060e031210030c0e091b130f0504060b060f0f0334031d030a0c02010207051201090501050106080601080103 73
    0x11106d0b040d2810032050701c81342402000c10500020405402014641c403400c1c105003074560110034a56041d00e058080405500e0100350703480001e28071904a0064203042c40d0b1413404504c404001c0e503480c802c039441d001c03414501c3e134000291038800410905080d6008581400340d078500e814010040f941d1007441880007810107071540c801080c008020002d41e4086504001399816034245101c213001809001e01080d65031121821000c104006404201405a000d94004000103a0281039810141d91012621544018011002110b0400c4c0b80100010344032103142c00241b500300780c0b51035000c5803040c181c1c0c0d83c0030b85410312040c3c6a800f0001e081e00c402d9a588006646e59036294000c240c40384414070b880c2c1e41880b560f051225601d4181c107413808502c20b03031070310200408200301508104c0c0320b20304001901d20384c0c400c2040c6581c040c8141a9044518410700442e0000c540352000581040c034146334900c02a95a0304065007800340c2401494010940c034282f540040c21301c500001e02003481404081d02e00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963000890 1250 962999640 962999659
    0x609010c0f111009080f1c05030603010f0e0d09090b1e0a0509180c04061a0c070807060f14040b251502180118090f020705070e1e010302030606 63
    0x60025448048541810040460700700d14440800a05400c2c19400b42c1081c0780708001b15402c8040700011400890b0801d1040d0b00360201c04400100d07203680c4010720054055484400c00b0601c061036008140704590990041c20140c1c44902d002450116540d21000c0c0702424520031051607103d01c0072501140c1600d00d41d20306603c801c60301007015445180e1000b600310700348000b0402009002603c895414900c0c000766007070030921404010a54032180030740300241075a44104801d40034008000c000da12488001c0e03c9105603900f0703003c0d080079900e900030804a13202c078203401169640031420084643c01c0f0807030a4100703801c20210070142d0081442844820141c0a142013203009124611000c40b60320180d024207050100701c00034081d4000740010220700d02c00c0104000e0319170145542c0d9101c3c01e05110120301d0580340100c20000392000e01c10030498650300700a171001149003801010042c0c610b00c4a1b00352079050007036a401c00060316070044500c12401c8030040c001a50040703851a007054040b0b80d1181c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963002140 1250 963000890 963000893
    0x3020903010b03030d2012060103020714070308031b04080c06090310090602040e0606070b0a0c0309080f12090303010b0703080621010b01082206090809100206090c0609010c0f 77
    0x61003038030102da505100204a502c46000c01d600f10600c55030003d80c1c0100780d071180c0242203025004840058440c000040d0004003194420f034003900c02d640c000e501000c01d480040c14042d091003d140c00940c2e14540000800c5a524698013610b0b00b4401131028443c649407410850b80c0c1c407600400e802ea8810310f8002400481070b5410042c2c2d508881c49000d040122550602c0d0480007503005108001700e40c0710140020b005481e0402c04da03400039030031800a00aa070764400da15001808402803d4040c03569510121012800d42c801624401580025003070760341404103000f501c0e801000380950900e82c0300300010300c40c07040903209684c0c0311545801c01e00000e48130003001030b4644908242681c0c2c0c20070001001038003a00c054006056010081e02c0c1d82c0100d0b107405004840400d454155032080340b4450074a0700002d00181c1c40744070414021ba00700c0d4100384010000802000345409120010f82c40007003400a0484240300650a400c002c403809860250b5800020300f42008640019084005040c400d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963003390 1250 963002140 963002143
    0xc090e0f0408130e040606060809030d0e1006030f020a080105070507080307140f071101030b061e0c0f0714010513170705280e01050603040b07031e0b0111150703020903 74
    0xa40710001e03a034443c80b83c00c1c1c8070814038598800442c1c0a480d050301740140000c00c1d030f0003801514003c020407409503103400140301d804005080d6401d40c88180d032145c1002c1c09414141841400c029521501142c0380124060040000002ca581c12044a03641342c0000c1c00480d5401c5404c49192981c04010951242d4038042e09031600000c18020008408000480101540c40b110080c0040c0e485a0701c41d600300485c00004600300e80301c1c90416034201e041084010981520900040c514103400c846891400c006114620b007841e80208038610706910001082c0151100c0703024030814a03400703103031290605509100c0510203202610403c88400840561090305040034030a41c40500b030003902090fa40a543c1180b0054200481c10381c0d10300d20265400450902c1c5d0281c4802c3c100c0c1e100400762400c640b2a6190380a1445002e011a802c2c142d481944074030305195802444041c0c8000d0b400006e000f403140c1c0015145100c05800052541c00600c401c00e041c500300f82d44507400c030a80d0b10300140c03260f01c007a001c00e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963004640 1250 963003390 963003397
    0x4050a0c02031b03070f0b01090c020d0503070e040221160e150306271608011518030c030609150c02100c020f0709050109060602030c0706050d18050607030c090e0f0408 74
    0xb0342500240b001b00c5051040c02c3d6003850403510320580410400d040b845003262a950311301032600c0002c00800105580310300c502c41412416200810040c50b14000080e440040480703e9181b40b103e408010400c044507000e5030b248416622036040011b08100000009103075150400c00c0b0400154000c030214400382c8074030130862204070b00240411a410000c400c14000c0c2d540880da828124100207051f100034600c100c00d0203040b2009036040c9002d0308002d040c180c0385541500303016508000704010020108001c00f0710107005502440e4000f50020381c0381007400030a22050f040c080c1c070300d0038076540000c0b50b41e00259621141d200700d0300009004000c1d500480c02c150750159102100d11411201140b070b03250941c40a4102c0340c01c0c8038200645a6510404d0b600c0340030300c0c88001501e820800040103051300400051500c0c41c900240090000e1314202d0802c0f202d22140425a4603501001c2009080c680620070400080315600b0141203842c54441c00305240c00700200518030b50081000420100500f02054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963005890 1250 963004640 963004643
    0x120f04060c0609050303090a02040e0106050d20101d06070b0f07020c0d0804080d0f1202030c0d0606080906010f050a2606070f0206160f08070e04020406020106030204050a0c02031b0307 81
    0x3c5e0b80c4da90510031111640c64004a00c10b911403490721940340303114001480b6040440f90090840c00c001420380d2910706001c000b05800c040008a030f50741a8007030340e450a50040450100d500c5814075255040c0407450002d40e0a42e14500031201006010013003142c0314107071540596015865001656412400c038241000d11407031907080000051120100007084001e401a16009030172111a50a18034040b601c101d91a41c00c00d0104455084a2140e040c1d181c00855108020000852402e903006800604845841c1d0007640014100381c03d200b0f4402d41408803500404901c5003401c00d82d4140700000f1041c1d8541e110f00103034083c802032028045022035034841000711140040e00c01c01d1510000103029401200c00c6807005000710781c00034281c2c0c0d00e600880700207008913685030700d58054010740649440320060401c0b000e000310b2803009051662240020700190202e907002148480c5548180404d941d406080810018142070392a80d00607400000e036180100c199012000c024400c0700082c3c110f200d8140f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963007140 1250 963005890 963005893
    0x906050f07020d021323071b03111e0c0405070207061d060301080607170403020c0d0201020f12270d020105070314131d0708070806180a05060102120f04060c060905 72
    0x288441c1e10b4080750701c000c00e0440501206172410300074071891805220221041d0008c180c800300d48000320141c1d006895001886030410301006000d0041c0d0903e0441c6002c201101e0030010082241d58000078049003c4100c81034406001504042d40c0c041d407904a18083c8504001c8504104a038901e80a081401c070750b034000e000f40d1780e81d503103503280582c076024215041e101051039240904070f94051100345c00d20451300750b07000c1c02540000f03404000008440c048140c0c1103106040040c3c000001c10300805481d0490808199a02c0040303044501224a0142131a00c504040110000003610740729615510641d0920f0b015a0350b041d5407809582c041c085024010303541a01082e100034074400301204030140c6110980c0b41d400c000000805541c1980c003141d40c04001194540070500700760080b2003043d0030110040601421904940c10301015440449442c41041c2c0c03500c06004807960148986206003d003110314501d071000704c50b80c0000798071440c803501003048400100e6006210148c0e01003001e15600c01d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963008390 1250 963007140 963007159
    0x5070e040906091a0403140f0c0f01050f060d05030301031103120703030b0405060a051020010903080402120f030a050d06051302031905013002030105011e060906050f07020d02 77
    0x10b0180c0100f4032880e003221030b000700f0044803003660101c03000c05100700e603d9074a80d0280d40f00700c2c200d01d405401c0005000300483d028000006884030608c0300b101c4d100121800000d02d0f203801c024880803100060046401111400d42d6000852004400c683c1036035002405008a80320002c04a840c0c00a01e40d400101420003060794030405a06400589405000f00d80501454403214104001d440d2103210769640071071072502810516001e28116000341071103207060f65034110301c4140d40d425503040e04030883c001500c800c01c0100710f03d0446544141000220001d024041201c0c20195a80c403c5250a4007031040c0402c4001c01f080e20b54000901400014000108242e061395030070029400a03124800b0010241850b038030020300740c0c49502d04803900c5010b182d4940031100d01010a5803820505215212803600032200540c40c2405954000c16246049040380d5100010702c146407511500b00d401080741c0000200300c1158440b069035003001802d00c0c1d070f0341c1d941a1440000c1e0004242040250401ca004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963009640 1250 963008390 963008393
    0x50a02030f150606031302010807020a0219030303140c03010608090c0a0617090109051f02131712070201020c10050c0d031d0c130207020d0804030b101e060305070e0409 74
    0x1040800120307601c000e202c45107489401c200607140c001101c246051012450051000d90310800f06607802441600680d89201019000b00b09860300041000800e0511410304008040c1d040c454000504d500700d084100034140309116495902c010710074001000604004201030300c1c400c1c44002541c40004100800b81c030754402029080342204400f0b0b24590040c04002206a801801542d0032140c0c4140a4541c1d04030309013460000c01c448041c40040d003582801200c401109004080029101d880e600c006040d2540c080107160403500d0341c4642c00928180075050050b600042c60345002c000c01c592400803243c64140c112180d0040ea078800d4180c3c0316003401015041c1e09644410100c0c000851700401c803c2105605681d104007819096400c801d0013003c01004400303607400b4120700c9200802c14402003407551951415500180c0003a03411079802d03400c2c4010310110b118120000c3c40206554034090b20090803d055a11152256809054481c000255043d10400708440d00b41001441006031203a10b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963010890 1250 963009640 963009643
    0x39060c0307030905100c1a10030807051005071409370f050102070311090915090705010e150a0305061216050a0b09030a0f020d12120b06030121050a02030f 68
    0x50f403041c6030141409400d0640d00e40d1207504101b04094010f031480100020700d4642d08521180184058070f2107100b004080300041d200c01c024065580074400500311000c1a00016003291000781507442404230004021994400d46030503990f00c080304403440609030100e2900303044036100c5412907020f0748544486540f84410b1218204094840e4894011070355601d61005a0780c2c0d0f480c90001400310162090504814505107003074070340c0302e03a0007000e481c0c00404640c8442d02000b8195100c1e42d10703030003420b0140f02c00d50b80224150340b0a1801c40e08202c02e1802088840b003a403141c002d0303c2042603101d034002922512031086840d480c80c1c00d00100c8a11758090a16075507918028011039126199541000030300daa201015240340d508002d01a00900340c0c1e682d40c179072912240d140105d80001ca00b9000170046200300100001c4a1425152080149842c020348011075030102009449800b091005006540070711a03012811501c191800070103100e43e041907485c004c080e04000b036161003411030a00c00082d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963012140 1250 963010890 963010907
    0x60f0203071d0d17090406030302030c010e190b060d0c09021c0c020d080406060f0f140102011a0f030703060606050909070c0503030a02071a07030b0339060c030703 72
    0x5075680c465007001c003225048032504207190000c0340c2c00500d0881e400040b81e00104000520380324040030501e00059071001c10140d49040e071058000d600003003844810010b0138050f82c0307103804810014210080350000480070480e00b02c0c00141c110170600740015801c3e00e640040680e801e4014080341d401e1507880d4681e9000c0e52216900c0003138a111421203270140f9155008a261075130303047d0007400c0820031403407013244c21202c014016602103480c1d40b0006604041d0059844c0902610503082240038105500c400f10f51140b10980340c110fa262000d508070540344900222007003041101c01100100c2c2c0440085d180ca901608003814007841c104002239442d4100e0000d01e008401a60304032419034400b541554001c0d80220302601d0303a082000052070030755581c0e0051545500ca8403101c0301813100c250504045000444810000ca0f50716600c0e009145410080f00460440008801031440032a000c4d00030b887c00f01d680c04200520140f103111344103944200a40302607030152070071a81c68646a0400808084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963013390 1250 963012140 963012151
    0x30a1713050409081801020a060509012c0c06090604090e0309040e06160f050412150f110d0c05120a02090f040c0512060a1809060c0806100f0c060f0203 67
    0x145000c0c005a2400d080c000d03c0c1c006508804400c1c02c0088040c260424400103259150440c01140c00c12400586180308413409a624800005480ea1552542e1a1450582c004a01a030700c0403910300f646490300010121071803842900c10341e459a041c100803c40c01d01030780d0004080c035400c115000085460000252074032120031941800345d10100151079032100000d85060080310803c80c00c00e641e00340034900944c0022071030708c0c180d8540341c0d0360542c21380b4100c00d1500480c0c1c45c155205000e0240780e0781d1b004041011a000d034040200701200c00d00e1a01c030344104c9040082c06604d81c0c0e81644003500680503501c001d001d99400070550310701032031100021740c0208035442c8122400c02c0d8a8105017014810400e1102164845514040c0304a82c0002c40c00c10049c50f49521102d00c0b000407a00010ba01c142002c041003900e001325a100041c40c14506803146002440100300c4248100a0a65078603204501c020a060034418100034080c001110107803001540641214102000c0c14003000a42d8015131180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963014640 1250 963013390 963013417
    0x304050d06141b0d0b0f04050412080c03150d0203070f081f060b04051921291308040e01180b030d080a2c03031803091e030a17 56
    0xc1d40ca644185841e00c442400d909120f6070300344100c01c864200c0742d001031100180180030050708180180040c1c141e032000c030303000c50348000700784401ea10315034202a03400d4010107145403503800c0d840e00fa0540022490400307640752181840c030101c00f05548052000340302800303441c4518010140c0b1501101d48c1c40c042060001074554030403001104403102440b81c0c1080d2514001d2207498145030200308281c0d079031115026200141130000c0040d0600808424009141f1400b0545100d03a081d424401d5441d1108158020714052280c4140282440810380950110400447c0a4441c001d4208907c8a0103180c002c552000030b41e000214602c2c020040540a003480100b041c054690304009164440c0038441e1b00340082040480463b040c806550010300c0f01c4500460300c0b8000c2517001080e02180c00801d8015901c6410020511400c0900c81d030844454402542c0218601038907003000c07a0700040000e50030101480c6184034040c0940c1c09002d04464141c10408605074007802000100440d4421400d800ca41c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963015890 1250 963014640 963014681
    0x10609060302181014010219030815091003020418050a08040e25050c0c091e060901120f0c051801150c110f010311040e1504111b0304050d06 62
    0x31028200c055901c5881c40703000f140002845c200f500d40c4400b00c00d00d2900e042d8000c07040706610b0762600000c0c1048180c001d42c0d40b81400d083c9480219402d00044103054015070341d1000300700014140014a81c00c803603040d58002103442d01c194848510074854140140307a8060800c0d1981403000303450140003511040e9121002c0c5444001c4083d041145543d1310040d804000c0001d280703000d0284c0054180ca404020540361801d842d000004c800704021107403000c8690520b10304c1c120000010791a181d00282c244c44a0b41c040d41018140400409100c00042003186c40d0f40368181000000c9802900520001d003155002010032060000b0081003400340708a0555901c2c000e280091103068103000468200888000c400d681c0000d03c50301e125105080d41c1410748607101e14103011a21001000202200d12044c5103504103008442c10381525a400c5c03c0c440c07400d003800380e1500120001102d0000b00001c0381d8a034809181ca5a0b20f0443c0290303401182c0c0103054042090078001c254100401808202c10350309207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963017140 1250 963015890 963015919
    0x30b07030b1e0f03010213080a140109030903150b040f050603060a05011401110102040b0301030c0f0b120a020d1b020a02040b030d140a020a050106030c061d0f0103091103010609060302 81
    0x141120307600892040c06116040d02d5640f41010700c1e1601c0e0190020b8005840c0451011040c07410382d10541c04900c560780710012110600110081d4030490300401c5000b8000719005450042010000380030290807034000400001002c078103039100101c0301c1d0b000b50050104140b0140080010081260780c80d00070302a810016140e522071740b040034141d4600411001e13000f034a5200451f81c0b4110440305404a41d4204404210340a000003e503000f144a00d024854040c100001c01c65165070580c003c244401d02403010340c0b0440e10140080d0b03880030b004030300142c0b644c0c2c1e502d650750041c29107084100c0d04c16501c1c5000004080d400708416401e0b07030007910b003400080080024981e4602820140c0000500511a0703503216108200044c4400c0e04248101c030a9881076440b81800c4404030b50088500031928241000001e40180c00550b0340d80100540911444043c4080f5407101c42d0004aa410149c2d210312103010800403000104107107001800070403042d41c9442e604801805540001e900c282d200003070991 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963018390 1250 963017140 963017149
    0x60305010326180a090e1c090b030414100c120c0504080a02010503090a0b011e060201022b180501020406111b040c05040312090e06030f0a0b040201051201030b07030b 73
    0x24200c403280882c41c0c50040c400d050f8016900c803894030f80d50b011100503000180c0710007500a003842940500003910001100013140311060310f58080c00d6040c00b001c0e9008020003840300d41682e50080d00040961030002184162138280902100d03250300da5443c100c0780c00001588100380e0110106e5480c1c0400490039a08815103042c01940b041c604950300c0349004400551180015607004a02d440485541203003551b207686050009030040e0010303072912100c810992070300d015403800400c03090000b14038045120703a40d00110f203445042c1001c4090b04c001002550105648124040c11005007022081400c0f0700d4801e010303502034820500014502205500c01e074001045001c104901d010341540d49200c0001132001601c1d5449440c000e20405000000218081d0849568140300c207079142d05900d400d000c80030000d000c019154138000d90001030307810484200068600456500400b02280503941c620048890b0f120b09820070701049201000081000b0038160a00c1c00707107045840a01200708507100f0300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963019640 1250 963018390 963018443
    0xc06020703021507060e0618061503060630070f14011b030302090607030806011710031b030204062702030402060f0c12030709051504031a0712060603050103 69
    0x6035202c80007800048410700d28030300030f01c44240304010210341b50440012031810300b50b00701d61085112290032034000d90740100b8000507a1014049820354128810300c00401c4c2e03200c800a0005002c0c400c0c50f851951000040210b503007031481e506c083c030084010303008a400d450750290301c542d0741a8031840101045400742002c03c060b600d001a5a01c00031400076414440800c0700d90341007a01856401c11542c1602e84951004107070182c003d850784641403e010000402020400c10880b1902c00d44005006101410700444412a50083c20103064000f0308042d41c01109101e500080d0711a18001002a0302d03003809502e08071504c2460b0703c82c2409601201400140d20080701c00941c8102c0803c10318440542080140c07001c10721281c110380c41980c055242c880705900660b0703c0804606400010050762400d110186000c45500201c0e41c2003a1855440303203404c0c4212240e55000d9009103001a40e0684201c0404280170700414050050550710f6070086d0091200b804280c500c07102c1aa0074540904200d0440d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963020890 1250 963019640 963019643
    0x5150708040f06140c030610030501050603060d14190506160f1407060f0b13020f0316020a052406060a23090a0f090b12190f05030a09030c06020703 65
    0x500105a03160b94400d1503000c5035820803101c4951301c616001009031307181192441000080c84407070752414100b0030032034094141141e00c420107040800600444d118074042c0e9400c4042a030341000d03151094130740808000781080c07002d0343c0c034480d2450f01e950500e1030001c1001441c2c015016102c49480d65141e400f00c0c014181552000700d4030300d4088028041c82144200d100b003030f0040c0c0709414080c0c29239420042c0ca801c1d10f0024241c40d1109601000380c9011011101e41000f2403404600d4a10300e140d030300c00c280c04000c201395200345590b01c8050840d4028001172898503031050036500f2854140507200030603241020030401104000000a0440c00c1c008100c82e2140c01c103490711000c03800102d2400000071144551084885028401401c168485115a002918590181e20a01410285100119050880b45030b118000380311024107807040c0840c03150b841d040201d5468840396141c0c10040407503040000000c05500c00000d004642d03990083c80e07601a20b200e00300000300d07190b039610101d90f1200a0b000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963022140 1250 963020890 963020897
    0x8030604200406050d1812090f0e0f040f080a11070b0406021e030f0a0809160f03120309020d0605100603020a020312060d050d080712091e050f19051507 67
    0x70501800c4d005070040d0440710081c2e10041000e00312444841d440c0d440c00d403000c643c1c031600d1140031604603030021a40000340030014220052a40340070300f9807951400181480045800320004642445030468103480c807207410060847e66002c01d0000102844200d404c85c00f048d0180b004003141042d00d5034215400c5881e40d9001305654210009041c14001905040d002d55200410848560940403c0034107203a5100d5186c1d4042c1e4a841c441e010b0070550f0300c00d821500046203110605c81407a0300c143e203500381c94100314000941c14501c80c007078008250001000e58000402e6140100b000142c1c0c0101d072080041c1280150020340d02c1505406070300680140c1e00142c0c005000c0301203610004000c0560000000303040783c0744c21115407509410107007a4003509000421000c101305055401842013080c01c62080070400c0421041c0d21101c0051009070740f4441c80b005407011020500408004002e0b0f040291825a060044803006002220341a00c03170480b2240514019441c0c0c0040c11000780e4450707a10382c2c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963023390 1250 963022140 963022147
    0xb09010e01021c021621020c03210f091e010f0c1e032003030f0108120405060a0e0a0806061008130209060316091a09061012020708070803060420 64
    0x2d415030041d400051145048802c22182d020118800307100d4801c4c54504d5001b28002c240b40e001009042c405084041402a880002c0f209201c82c1701d6108102c550a51480c0152240b007090303e081014400c070420203500c5168503170003d07003100c42061200e542950988803e10b1076403414100380c0340d50302003590141c1050403490307410082c000a500d00e0242c7d1482803520400700905180700d01c5100c00000304a070081d1b400030042080315100141c005016200600051500752244070508880d44264050a4003c44000c41c1c00b5148034001c0007641c42c02600140003030101c940760503115540750fa04440b01c0d4452160070300d80395151402020702a02641c1c4104056449002507003d104107c00701604041d018801c0f01c1019168808504802001d0481040089408202c0800d45d040c9030300d4501e01d0620403020300c400d11040d0b540e2803010b500e100646007004415140e410050b100240280d0001401d00580010700d50100101140118440c0034100c6042045621180d032144200707411100c4407590078000c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963024640 1250 963023390 963023437
    0x30c08070818070b07050c0a0609030b0c090429091f26070e070e1219060f02070809040501081609110d060b070308160f1103040803070b09010e0102 65
    0x304210030b107900310408039a4900e0303565550300c0460b0320902081d58203400c041d540d005d051030b180c2083d00c004c0049240090169003544c0310300381e81d0003000e031000f20b24100000791140151166000a9a141580e005440303088078001e2000304071448002c10f00b4403902030140080c030040d030054032101e0b2010110380d14028241c10410a0300d2074105150032050201003c0c20380d910034040420110b40500b0740c02444e80d07900d00342404050702101400c10420f02c1500d004410104c2c05c1000205d00343d000d44550702e60000d0f070800e800e142e00200710700d030711884096000050f600306000101004140040e0142c0f020011aa40c50001e0394039181c07900c00b40c1103642688942004021904d401c5400158007404403149412560894a0216545584040124000460038405041e0400f16190380542e5041c1c1ca00c3e0040417445009210014000140b010700401d68406941da040800a42c0c02030540c40c402c403903460700c440c00d012580c80d1048604240707541c01d000e520103808406000f9070300c40b140d414000c0160003410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963025890 1250 963024640 963024661
    0x1905040f09020309030d051003050105010b0f030402220204140108090c090402100e09070e030c0109030203071e0312020105191506270e161805150c010e030901030c080708 75
    0x4d0585a8244020301203074003040024481c5500411101181c08501c6145290082c00c0d120160f00c2520134220034000b140d0504005001c5030b5200b0340c100e4071700142d0707410f2011222200c0400d000700c6442c248045808602141d07801d1680b19401b600341ca4446c100e54880e0390ba5603031007480e00c040540010480001c40d0050904040e00c80d041e070311500300309440c2004140411084081202c42000050481004a6503420f06000300c00e0711180a10700a1403040c19500825580c4150388105460b248501400c03400140207074071488007640d8040c030603181c034a141c0e000c003c1c060482a121003c04d01140e900d200d902014a101c0d0000704c507000700c603c8001900d054010744c0c1c12100c041070b400c01740003a0006031801122030086c00000c6c005100c000350b02c0303042c0100049441001e140d001000d0041100d0076050036040402e01c00202d41d01100c41c0d10700804032038040d01c00c6004040800c1c0f0250300303212007140d42403c040040e010000c1c0c2a6000c10030316040100c00c4a90580c2038609402003107088002c80d000041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963027140 1250 963025890 963025897
    0x21614060d050705190f09061b0b0601020c0301060f1502030408101a060c060414070e010b250305030f0f0601050913060f03060605030114010b030a0507091701021905040f0902 77
    0x711402c3c480d04024140c05a52021080d814201700002c07030a002040312141c01c0101c00380540801d20788441803005100c00c44415420f000e41c0903080440032800a1741ca0381c0700b04010b40050b00c0250090044035a50a03540013500050301034080201021742091541e0b520000c00c0e00c00b1200c0450050000c14220041017000b0300d1655046140c3c18119401809940c803400010080f000d4540c000300810b14190038141e103000c04040d10f0030002d400801c4101b09816916500905482c440502907590721103075460f19000700e8044401440c9100350301c0c0b03094241504200a5031190340200c500b0350250740c4803200c2e201403002c21aa05070205405000f50121414811541050301080c510001005a00c4080a00002090b0361003200d94903111141840181028011070060180a00c5012142d50400181c0451400000d0002c1d2516540d50000b80d041846004444003c15480d000388030840e40c614201c90103503000b2900c080c8102107490343c11a90a120710119000c0392401440c1034034640c20920340780041e40c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963028390 1250 963027140 963027151
    0x90b0a180b01270c090612020405030a050307030e100f110f011817180d0503070206120a0e060103111e150901110c0d060921021614060d05 61
    0x10010900c000240801a640340a4025400e402042040c0c03019a102c0e60145400312249181c20440341140039a040010b00c0150b40003410040041c68454514100078000c2e98411a454880e10b07000005011000c07004000c2c00c0d000e90344082e90186000300340040c1401c84014000020055440301c0741003803180c1d620340c03821200c00055950010307420f440c150a40d4003e4a180800c04140007200040040e1050001204c010080c452410700c1d0703c3e031000c8001400e01a1085000b181444202402c00c030040c022612103544c001c210741d4917000d006124010081040b2203d45900f451300d84595841e8800244940c101c80c0d01c1003c41209120350390910258510a0464040801d406401e1145603581d41001030b14404011102c940c82d201c2c001d00050012014160fa02c031180c12a01084240f6110203210f0be980c0c40d0049004180c10240d86044805203803610f9001641d8103082480340a810f50228402c0c2c1c98070090710303c0742c1c03c10b038079103540c01c0c0501d80510400d40e01400420100011010340e4000c41e9010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963029640 1250 963028390 963028421
    0x18060c12060303090512161a0d06030f03080a18030f1106040f021f020a021908030a09260309040b0409020a03030f120b01020c3a02040c03090b0a 64
    0x45046280c0341a501c1075041100031a008403001c1c0440d042c4030740c0940346112003400410030b03142d0030695101e41da0031030f0048100c550112090903c40440600444015041d00ca07070400c41c2940d20b0410158115800500b200080c46c07c42c081032001b24a4084e0b80340e0343c3d055282d003842d14415640c054440c5ca808030001c40a020010302d44c07961044003400344501c82c03400b078000c5025418a91042101d000d030303d0f10080f4450b250310000584031079800200e13213030540d6050340d40751203240d03920442c0c202c2c2c0b43c029804000351f0711000542812301544400000304881848820022100c111242d0150200c1e403180072a110381d0060164001a140c2508501140e90000d40300051103a017030f402150200c00250030a40c00326400a10b03500b6026401800075100d541c541c4000c00145002d00700003519036085080644c8119500f44244e98408000f40c45204000d12040340e09041c642c1401c48a411000403680070380c80780340303004e0300b503280c0500a0140c0038266030b02416034401035651801303c0b40103280c03400c28094074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963030890 1250 963029640 963029657
    0x80105060d0b16140f07230a08030901060b03012303030f0919031a2a07030305071404060216140d020d150f0b03160f09180c1508010918060c 62
    0x59130b41d084010400c460803000702030b43e43c11840c1842c00801d80d08042c2c0781050501d242c0a1b174100380001c9003480710b882d400b4214503526103c1c03c12a80c0508056040010040f40000002071541090240150190904110800008417500405449001d0f400c0010700c1584c04019802591a01003401d0a407004a00c2a20700300b40c0d05c0b41c8851459280300000407001d040054240246084001801040d01010540040440c60703460000d07403180c050340c1e10080034181c440011400f00360244c000028002c19150746c80391610707903032000295501190b045c01e270380c9400383d424003143c030340700c08003105400f1a80075201e04200d0800d603090201d064000d420a44d012a8104c2074800d00f11200c2c00781001081042c400803807800c80240405043c14182a8282d0811013404e40802000412510135002c070380e01d0540028924203002c03100f000c10382d0115802008210b503484041000403e0b0964441c6600da1075907465910707030700c3d5650801250071900744034400303c0c0c13809090310000350281c1003403660300247d241400c1c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963032140 1250 963030890 963030917
    0x15090f1b2107031e2304020d0b07120c0914011b0f0f0b0106030b011709210d060501180306090809180123010518011e0504080105060d0b16 61
    0x503008010350b41d400c0040d8035448900307650350849800400000450340c003007100b203940400c20b05042c0c040300c251101c12201e101c0010290354450f2110031625070000c1c0c40d1308a41c900010b00400c031a400c20b6582600625200401500c1841502d0900940700c8148801301c0c2c285034800155003034007000400b0060040d4200300480020b803501642c958040c80707000100d5400d9480d141c4159400c4058020f40205450138904800581e4040c91105100d055240118a40e848080e0352038204481141041c40c000041e042c0c04c2c5201117010b00403e0000000f102c2040820340b0341004403080010b80103e0108050021406c0c000328603540e218494181c8a41d0150b490503842401007865201006c1008200c04012401040b041c241000154504003007440d0502100c10014000307049c1d8020341d41c455280d14445440c0b09207a9014680307403524007206002204001d4140803009110394014010747e122f40d420440410b001c0e092003c10416075a03403205110f5841d507240084503074070740070b624106810041000354000703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963033390 1250 963032140 963032197
    0x9010c0f020303040b0f18060a0f1404150203091201050103231509030703030c032f0d1401170d0512070306090f020405040b0a27090b15090f1b 63
    0x300d040c00110300d143d1502049800403821749001c100304c90003000c040064111058ac49421404840e0380760070103074810000106254002e02464208860100070b007966503208540001c0a00a01d4408841c003120342c00c200c2c01a1400c0c2d52081c48002d2051040010a0442c030983d0f502d000d80c02414074003156214a1003181039810b915040c0c0e40001c5540000915409250749405800d03500307a036608003408810425800110b01e80c01c9000702c90106814580d8034008813050f00216600903000b18000e00100c4a44208000401030030700c02d0781076101403940d0440c56000d0100d051850300140d80c80d01400c1c0000b0404058480344020148402c00d03507580341c0804c000c40b0707a01c551603451740c454900580351401c000602003212800b880081c4512818002013008071030509140c5400c4401c115800c0340141d110100001a042c5079000034480ba00c11410045208c2200300b642d1051042200d2103007a5444131a146080308401b81c4004040c90f806059844042e040400200644a043d0b4000300c14600140e2182 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963034640 1250 963033390 963033397
    0x2211005070807031a060a1d1011060f160302070218010612060501030e07061b081606060510090303030e0f0703080a021e0709050714210c09010c0f020303040b 70
    0x102142c881414003555a03030511402684019142d9802c0100380c5030030006805008003060382003088031030003541d5400760800101c401d5049002d084e51041e881c21800c050b08100800c401c000040c403230500041e0703139030215600c01070103140a8214400540e00b096003c4000c2e601140c0242e802002c03030b1441c90b40d40d0302c82d1010315000780519503440d400704050080620650340385500442c1090300f001407112454034045000e208071500c90812000d5115100d010041e41c45880f280502034010105001c18200580c080d030050311446038078200103a584407010000c00701d802014460000c1c0e0140400c2c80002c1c000d52003491050311060450310800d0103540340914164154000f200c400101094201c000c6404102070800005200420300a00b1040610706550300414803948201c180c5440c0441e80d40e41c00303426040101c20f100c1400b00d9440d84c0044d0801155441c81d0321941c2810800030028818014030700554083d03e2050f502d04078840d916458080d00017610070750aa03410b01007000000398158190009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963035890 1250 963034640 963034651
    0x5070213020403121e030c080f15031015050d030516061820030718050a0204050a080303091e032d070b01030b0a06060905210d021006050d02211005 65
    0x5403600071111080314040303440c1c100c0c0710305c081c94184041c1d01d180f542c001d01113607030008007680085102e60b100003040040406060030290140123504191504c0c0485421410300440c0340d050803840980c1d90000d01c000e151200c24042c000803028020721403401d25207802d10301007902480d404a41f441809070a000b038001c080c0000c0b9031146418113840d88a54249035003418a000480150600c94544903900c1510400c42000d4884195240000789540c492581540d003d04000b0741503800e00c1e0f8844010656035402520010f0042c402e501c809804000bc02c40a50740c032908200243d42402021001e0076000700e4a1000e081150544100b55100c0e01810005051a28001c00c80c5000a5141d400c25102d04d1002611208079030b4103244e8113000c4550011003540480710107071103516607184443e0940c0700d034440c56003800015000f00040b85039860303400543c0148015105408204055840b41084000040d03110000e4100c2d04800c1d4210088003a40000944d0b490304800350380101c1c0340e00d6000404c071386e400c82d80c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963037140 1250 963035890 963035897
    0x216050303011706010801020f0702010f030608030d05150d0c09090c030b091c030b060313050a02040609021804060305281e0308150108040b090109050105131b060507021302040312 79
    0x2000c0750000f900b0080d090041c000b202c0210726103806980246000c0c428458080d061188022922000d80c0c803a50052006018041c141ca80b03e0305040d01c0c0001510301910f07410035112007020300418a20300101800d0b045940300240b41d00c01c519028256010344400d9030180d03100095400000040341801c40721034410030402018110504c40104030000991920f0641000c040c50055072078196150034044a4001600083c40e84c1c1e541e80b585001d030300d800381d200302c002e40150410800007115080740d0060000c4903020300510851071001c2c4103000880781c0030310000c1d141d5400150900d400d9015130b07540540746104880d18000b042000c2d254102c440c0c10314069800b9070304500d2441c00070700d40e0111010b60080ca0300048100064040c80000780390200244c4003a001c4c0503100f000c40e1900300250302142c6400c1d404002440705140c4024950403d0f50590307000d54100c80e00c0c0c01034400b2403820600030030544880d0740702c45051849903000c0c0001c1d80400c134000c1010366070030080030001c91101680d140308a6011354 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963038390 1250 963037140 963037169
    0x936010615020d050a120902131d0706051e090f060f0910090e0a0f0216030c1a101403030d1b030b0906010e040b040605100908060f07090603021605030301 68
    0x22000f4030300740c190401d080401c642803010300801640034404c0690100d0a80000c92620003074000203442d540185500c52110346403002c00131180005040e0400f15003420002c1d103042d290340d41015959807103a04a541c8401c148142c00ca20301030000c40203040b010310050541d4441c058504041082a070114100c44200003022a88000518101c4205407140c401d80c40d1908145103800c1c040c8010260283c006207031b4548800a411a412036641a101c1d103107007080d4800680e010744d0401402d8240110030640d9110100c54242800c1c00503100307040e01031258041404503891410b48070142c240303042e1403003a9050004001c00d014501e003901401158410700c03810740c600341c4400c0c900074048038642d19445024065003820480242e800c80300702e0380002030030380d40490340503440000100101690382025034803030b45515401103586d50091200c0203a43e40c11080700c006465074601424404000c13120440001d81400c030602215200760050013100441c0080f04080c0490b541d074490858000f6000101e11300701d41c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963039640 1250 963038390 963038429
    0x818070305150709061b17040b09010306081c0f120c030b0f0f01051602010c0209090a050d020f060630030d110304051e16030f1109360106 61
    0x2c021941c1c00c40e05504150f00064078060b80500554003500d20109050207012040c000d00003503c03002d00300f09481112690b91240c03504e00800075038010038007441c00285808004070700d00301c0000d100d210208080030002c030342c070304c2d0060226401d103804150a000c000f00400143e185140d40c0c0104040001591800f051003815041400110300040807442d00c60210748111064030307600704080310480b2428003030b4842074071402d00041e601036005640003500003000004002c812500483c2904d502842441941c03a03103003001308201e84d0f404802c02000413913042000400c06615100c00c40c0683c44440540344000d0075440211143c03000e09007901008a5000001ca02c6092a614464040c4a2859828440c00c504007034890680d160300495008142c0d403414200d811a010701004103600c8840320385242000c0300d80340d2425082181141004807071903501090700f0080381c42d007100c00074400c400b40e00e9288049101c101d08546003a10150310401c90701a62180844400c0080c0100b80151a05804407a40032118 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963040890 1250 963039640 963039673
    0x40b0c030d0c0e090106031d120a02010510031e03030e03070b0907050d0c09111204030c11101d06040512030715061206020c030f0a03090b1005100818070305 69
    0x2e0304108000c450681242203942e490540d0781507401901d80040c5480440001440700c1035000110b4116100c2c5244000c2010f180c08002c120801d030a900a0110b034542e542c2411502c0d540d4000105540711000241d11502d10b101c0c0f4512a103402440c011030441d0103412114216400700d401500c01d035101c0020071a50b0b0304100700307642c0100340940c0c1044095a00381c580d11814001400b078110074680781e511082c900003045090310f000504407011441c0c1810b0138500540030046224088449003400301c03110130185401c088202440000e9212074211b481407082000b2401150b00117940d219000f8080400d058580e46405440303c942d082c001c55903180c05081c030400211580452680b5030f4200031003400421900259211240d42c0501d01507102e00030401c40034154089e845861002d0007011501020741903050b0881100700c0c1c002c0403071100315210b2100344030782040e142c01265003201030305411880040c40742c0d03101640694a41c20711040702c04151140c038200010b582c004d9031203902003550014030350704 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963042140 1250 963040890 963040901
    0x8061005030c011b02030709020c03030a0c050406050d05100905190e0109020d080d0207060f0f0c02060603060c070c080d080f18070b0c10060306023a0b0303040b0c030d 74
    0x20114000e00c0440d00d8003000078418856444004804d00d800d046480c2191030410450010309034030f52003503403516400c0e03207402d42d40d400403515005003078240380d404110300d4000c3d4211000c0e41c9050390366034038251602444001400c0080c00030b5485220250340001d49011500c50240101e410b4066000032940038152181a00c45900304130303555907d040842d400580d03030034554010b119031000300b198540c0b1419030038078000d004001000e440681041040b00c2d0f0411980d0001d8030307460101104014823030328100105d03501ca44c1210030715055400030780400e600a00040281c0340041c440c01904040c2922607422a0a241c002440c01011070540c40c1486500708080d00c80b01e0703001003003032a4040790302c5a000300d0a0b03480031513100341c0c048540001070b4820805400d019003407030040d4006080c05402e0707882c546031000354071003070440001d080007050144031110404515002043c0304140c480604400c041d0845c0202071848841d685031104000000342c24050700041d002e040c070040081e41e15030600d0b8402130155007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963043390 1250 963042140 963042149
    0xc030b1e010b040909150c181211330915190e040b09040308060a060e0d1b0302130504050d0302121305160305100b060c0a060b0103020f04080610 64
    0x5000e001031002202c81c10030b032021110019808121030740641000c903c1e003407041d95040415410300b031091090940081c41000c00b0040d4240075100140da8a41142040058030700060060314500894022407a00f000fa0801034080074034048011400c400e0108032070055151700d075030652008280c3c04114a400d4021860061101084034508107400b1800744c800078101c1001c200384010861404420344481d0321040f500140a80b10b0881c5090509015102100403504c2d1440341284d00e10106985100d20180302c21007030060300c1c042075030f2503d545088a0003a098000c00c43c141c000c160004c05640c4090320300038a201d11010000b010304040c20406d081070b4408565606050040048500101d26007050641c004400305904418481e035280c6541000c04100a610b009110140044107110020490104080350303142e0810900304044240407440c0035069442c0c201ea0080300c441c00105400d40c12000600324140b50041c50181b08a05145040e001900100042d134040400c0002d041c0003480c4550180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963044640 1250 963043390 963043441
    0x20f27030123090f10090614040b04060507020d0e120114010e10050406120212010b0301020a020d1116060c050f01090309090b01030b062b0509150c09090c160c030b 72
    0xd5039040b8159a072030b605d8124401c03026503500070706014082698042c0d03940400c80701c4100084e0a150900103410381040d078050740c60600e0b10010403c6c0900010302241d103048c158a50524006901b001c0020940340007042e08a02e540310300040c1d4081850309415800ba0400c65070030a02401c10b2485d443e05001c040c0c00045c010b0b41b501000717024401c2a104028001d40c0e0480b450703107042101c81700042c0074200142c80c1d10f0301903001041e003003203c0b5001700d038111140c42e29554000d20001c43c88201030b0741e0100c0b0300c40c0c21300c01440d030700c4180102d5108003141802640030350200c030449914545807500311825410240c002801038078090001140324001e140401c102443c06000c80c2c40d0b55000a001e52003001c05e03600c00b09032103101c0940c00ca483c58000b01d4151300b1800c0204500d2408200c10f81c0c0700c6005038240c1803107410a80005079240103c1c0c0646584410144c00f40440b07641d092000e0400d42d02c55220260408086241c003c0040d80070900306026502c12060801d050a002c80e9004022904038180c0482 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963045890 1250 963044640 963044653
    0x1208071701030503030604050702210a11150a020a180b04060305070518010f110a06050f010b030412030203100302090a060303300c1404090e0709020f2703012309 71
    0x410b0f8000305032500100c08850019294440d0f15042c0d25110804030707441e0b501a0002d452212500041e4007806081300d280c0c48594031444a101c086464a070081108d040603508500800d5150b0550b90140009200b20b0070410070800c01c0d2a40344224683c1544900e80d0110001001e1048551502450b500004641080c0c2c2c01e00501e0190f11072006503a00e901410010403c122108451188601c18815044041078410792101410144043c000c120340300f52112303104c1000000c1c88015142105e2256070400300b42841c00320880d03006c07070180d400900258241c6000c3c40010015030382d44210103000b40b05410300068600d00e5403902030110183c04180034001c2800c945241091030005650042075070f0040800030300300502c413400b5146901d6241d8070310701d0714034040341c0805c2c2e040d031907070003d907480c0862800c5030011951214588280c1c8600e0300c84000c10a428003029210350001d858003126004001c2c4501680c0c50414080b0742190503440d00a026034803011210084060b01d20700c160740120b0400040d002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963047140 1250 963045890 963045893
    0x9030c0c010e0d15060f0e3108030a020909010e060315090c01053f0f041e0201120e0a030809030a02120f09100c020414010f09090f120807170103 64
    0xc2e06021a8010340b04034040d007015100c111840d80300c20081c26082022040382030f07c4040b14805007030110f51203000c1d80160030280441710041c034840f9000d503c3e4034400502d20000b0b135440540e00d4101034003c2e02515000d00014280d50740e540050341c06000340300340c0a5a1864a01c0c02c1503e402041c0711103121400e4040c051104200012070703600c583e1242800c299580d083d400c0088071194212030f00d190015250031101d1a0705070f10320009860814200415042d6031740f10003600941500c03098500410361443e00140e03001150800340c8081d482401410710104c500d000451003000d07035500d02c2c1d1f403078451741241c100e1104040c0c002c802680c2106080005508042248101a507580744c5002c02510f01d40700861072946040b01142190050600600448607a0b40c1d540d9000d400c0d8911010124407850411403040070700350b80000705504a500010540e24100e20b410016002000c03145801d070b422041d42060000403070180c1d580c1200400d603a685054113850b01d00c60003800c0301036004440d094082814010070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963048390 1250 963047140 963047149
    0x1e09030806040207050a06090809090c0f0d09060b04112a0c06160f06060f0b03062101090c12020108060613030201200a0b0a0f02040f0e040206040e09030c0c010e 71
    0x25800304060700c2c0180c2d80e903401e0078607524045140400034081800c0800880030010040080d000781074040e9034410094884415980d040d001d40e2030440750b025403c2c0701e980c90812841d04418082406001d0004400800c8000326040d110100c0e07903002240c86c0040c2c1c06d03c0c4040d02240b0303581e10300e400c414110010000001010344510b40762541030b1140b24049003035058241e698030381d50b800e90341c0b11010040d10651494010003600c6240b14030030b00c50031406030008040940d0310440e4031408009201e159980c443c1c241d8803801000088055401c0d640c3d0b07040c003500180f43c821070b01e0301503c808945e101003a01a480014900c01c00100301e140100e00520020340d038070304a034441e9400c1d02c0e42420051448901d42030032944203000184102c0141c0314104d44201440440f1000600a0b03290b00e2007400051150403e09080c1e104030302c44c5000f005443d20301000f40520318060142c1251000b002645040d43d03869100a840d00107071075242d10707508009500b44003594100a45c110300402070a180c415841e0450008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963049640 1250 963048390 963048407
    0x110d0305030a0504080f0a08060a1202030d0f03020c0a0c0e01060c030801141807080916060207031709180708060f18070e04050a0b01020f0708061b0702030a061e0903 73
    0x2400b4603116804201000302a10943e41941c442c0c0c1705540d19a0762400303000740b844509840c07a80c054032201c0c0002c1001140501c01141d1686c01800130010038841c078030704850b500301c0004241c0c02c140d401e0000510040080c13000c0c104650043d000340080714100080001c28090607805101803120124500d00000e81085442d81110641e221070708500409501161440c00b114101000d112034030410043c1d4560007219036030007280c541d012203805110001c0070b11120030080c0a040d000d6840030000304001446100e80760354080c080c0ba940340c00c0482500100d00c890807103254a1000790181410840c50b02c1d0322600c440da00c008100d6061030b41d0002c038004101c494201c601d0b103a03441550718001800701d60103901089190000500100314519001c20943d00418110791400d005001d0441440c02c3c40d4400610041601c042e070018003059281c0e10302c0c3c2e045038001210705003c00c400a00410002d40d13014000e1014a6000e0b40d8003281c2e800f2500030200d2442130001840003210724100b800c4010a5004031a13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963050890 1250 963049640 963049651
    0x3100203131b05100c2303180a0b0c0109030f020a0807060c0e09250804050316020310110406030c020f1528020c060708010602120304032604110d030503 67
    0x103202c0d0601180a2020200b01e40303801450b0032451001c000c0c00003544c4441e11899981c0503440d0241580b042101075100c000c15401c9010441d401030205a665904100010341c0c82e0744020003810480395550311404068008440c1d540c0f060750350300c980070141500b00201503002103151020700300c0045540d403800a940a91900500032a5aa221183c0c07001e024481900b10444c1c005c0a048162816117131241003100c005074a9500c5030044079200c04200d005920060140358080065414803da130f04d00d0003000001000c099034036100346913507410031400d5440781c03c007000c030f000b0354459840c1c2c10060003134280c03080a1078480455021010003541032030b010508690031414070155401513182c0e43c2404c0b425130708242c05d10041e402600c4040440301e40c142d0041200a500f8010744482d40c0c0c480906403400714092040c0780140e004106000981c41001c401542d01c648030b4108542446104005c00581c11100b01300740710100ba0000602c0144402452550352401d0304495041406507141e070020306c1400007405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963052140 1250 963050890 963050903
    0x130309050a0b1c112206050f040e060303040312030603061404050d0809010f0e03070b130c0608070201110403030309050606031b1210410c07030e1207050310020313 72
    0x281d52600040d0340201190601d040c4c121038845004420509050a016044017848410b0050005080340143d054612810101d032030350782000d1816608812003200200301c11750500013000044000394a11036010803000c0c0c955000101d00f401c1d0300d004401c8410613129540c02c599031808001c0003850000e4481c007601074a142c46000307526100803142c054201c3d88007a0060500705a9044000207001001d001c0882c0965480d00c000c0d120189400a01e81c0d0711103000d0428036080105006045c002da85041d00001c440c07000290b40c00c52001c2c00f80c1c041d00320781c1003140002e45a0032401c0c1403110412040c1d420010031000f4250309441d41c0c00140303100750100c1110307010388421505c48511701401d00401601d448000d10600000a1000e01141d6112500080d4a00d0051505441d64a0358025000424120301110181740d50340758525070b40314a40110000310200301c202c039000202501d13880703d41c007010351900c0001c291550030b01c01003500f0100410421080076205200300f00c283d02000c840d105101d03406c0b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963053390 1250 963052140 963052177
    0xc050c063d030c090e0c041104170a02180a050a0b010f0309020307090203090c090705090105041a09180702010c03150302010f0c080f2a0d031a0405130309050a0b 71
    0x8100c8400e036145502c05403200103110800201c200c3c0c96000340d684103061005035030b13107500180700700421158a0001424040400d20080c0304200460050011008c8281c089441c10681a40080d45116004900180e0100e0325403d01004001601982e070b00030750304400030b018110030b05000904200200200030b04140c0c44103030392015518140100009440d80700025540e1f031400f14900d95035540c2c0303461500e019090080c001185079101e40d00707540d2010313416900c25244c54a080da22101010024400040742c010402c4005c942d95180c2c091507800d0a04003000d410700307280c03980c40a400c5807405100341041c141440c52000c8440800d03140303441602d5090030440c2580803030000444040c00700400080c480c04002503208201c1c22448090680310707500480c000c214114032500c0301e0500c8090300214a01c0ea02c40c070049591a0f020b900024401c15034160580e9260004500082c140c403416a80005020a07d40b1032106141d400f0400001801082c1e0300324200a16050328580680b00d0710b04110120346204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963054640 1250 963053390 963053491
    0x2011817040e18060601020604150203060f0d1401060611060118093f020613050c0d030306090b040e060112020319050d030608070b04270c050c06 64
    0x210140d8002c1c0c104030140700c00340d1030300e12000301c0c0016003d94024050701c50035000854940c030001d016403046500944810341030015401183c00b13900b024107200ea1200c07101040400f42d0321000ba24202040c0500c0c041c008041c1d102011908580c40c58020104101070741040c0050403400142580c1107602500c018900030403d103205800410410070010046030030344146802c410010722220307800c00400b81500c15046520801944121150140140541c102100164882d1070f60010380e8080c40c000c20540302444854400511b03140352008080300401d40e14001030084003d584580c07590340c80190383c200601c403d0030002640d174040522960308040140010b010454400303001201c6081d02c042c1d03c03140190768500e4180c1e2908020b201c0c400020b45402ca00040034500081c0d00000c8071411400b0510700360600305400ba020080c4c00ca552404040d000701c080210b062889540041c40741540c9070303910752440440c6103090542c0540007640b648a96225040c418640c2ca03407030300036541c80c0c0e11500c2d01c03034060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963055890 1250 963054640 963054683
    0x105030604090f080a0207090506011706010e1003140109020903030f0a030905060c03010510092d0b0c010e071d0f0402040f092009010e01050603070203160305120601020118 76
    0x1d1000f00038202203000203080000c0000030300b8071451241c00340c07800582c80766000d50450b1000c64910f4001010910949600b00c05da003c80751300301c0410b1511004540f10f07140820b1307200810300c4529000070340e00c2001c80210010f81c2c04d074174003401d0806400c1d0710f450442c01c002542c134024203040802c0c8000008400d241540207602407413400354400c050700d2052401c0314511a454000344038050007660908620074040b407044001c0310a44080342d121501c580f03142c2c4420409a00040315003072420b11084800300701d00c40180043e00b107081c91140042540b6a24440c8181008a103920210128601130350052516454248030b642c002ca80780083c07002d5640b00c2c00040d029095004000f6100c03480c051100c814040201603850320076a484000e0845482038109120703a01609108400010030fa003001401f451602070000e51300700c5024412a4148002c2d8880044003d08042088011810006120700c031251040301495110109000030400800a446420005200100010120140843c245030304580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963057140 1250 963055890 963055901
    0x5160911130b1b0a060218310b030a05010603050c091005040915051501031109090f040c0e09031201060314060f0a09180c050301090f030804020f1c0c1406090105030604 74
    0x183c020440d0180c12081c04c000c4000d5200894084d15851a40c500350002d0800401c10440c1504102d0809082c003001c402209041108910456203a62110501081030340d04004e0351011310f009000009a0b0303032562030154541059071480303901420302801080000416882c03500100e6034259004140a20f481c0381200c49004aa9801c6010914000610903c070442c0100700500c400c0a88003001028040324000441d07000d0300541d15880064074000078140c82a0460b91908180308109211005490f0701c00f50440c2c00003203510a40551001c1903003000c0340c4040481c940140520f00341000175101074800078042034001400c0c1401090340c12050709031512491031603002090046410801d02d03042e80b03440350f004248400e0a50b03601408100106e0700e0b2030180714041c00f007a4860204080c144140d44e0940d844900100143d900c81c1c0390303104c54011902d598051564002e0703040c00030304a0310b40c5807401160580c0c2039040f00980703400445618109403110021100d0036902400c04685035500c00c40020040c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963058390 1250 963057140 963057187
    0x191106070f1406010b1309150306180510050f06010e0d080307050d0b0a08030a120e030703051908010e0112080c01020406090e0703020328020705160911130b 69
    0x800441e4003014040402c250244808429055841c181d84e180801400342c0070340c071250000c100a45804006500140d442001e000a0b190303011030f03900c1d44d280c50300d6084603424600704045410070409801000310602003049040c0b40d01508011030705109000c0c3c901c800c4024491418404d04200203a900c0e911b072103a0704c0c010b5a004900036500e00d0400802869a00000380a1000c00d090080303040303080c83c0c001050b40544035110015420014010001c4401950b180c0c441250241e50715038a03082100144010100b0500030380b243c9940d40140a0810309828000d0310080070010044014852507048004860440701c00310390700c20740400300d802d003540b641c07060900c06046980b0018001030110703080800300d01213400b03100c0d010466a580c0c01090341030344400c0302e030100c20138110000b5512141d5940f036031001001c0d00b0500103003404030a0f0340d020b250080348181440103a9960000b00f001c6000382c0030340702c1d05c40034410700e05040181401c1c1c400001300c1d80c2c4c01000d0032200c0203c0c1c2c100d0100307410384038045541c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963059640 1250 963058390 963058403
    0x80a14010902030a05211c05040804080d0f1214041101020c03070806070915081b04090f0b09060d08120601030b0603100906120f11030111040e09010e19110607 70
    0x210070345003a40d0384500c1501b100c0e03040350140700002140207482c01511410007156180c01580404120000010071005204954070001400085000c41040000d9003c1440315168002400d01c8100d000e0803500c0c6c0904040085402d0841030080b5011600100b5003040d4040030120002244e000142d00f444444600c0c16014424000000b034080400554036015618680701d2202254440010815030140c001420022881d5400400c0f9150040410104204140c0001764217042e00c4840500686004183d00d85565440c1c80192803a881c004001c0d5400c40c104562148800c42141d507550501d026200e00c541042c100b80c80040d802d640642c0207904001c02c01011295070f4942120440302a01150040345502803801c400450580c0110617030440094200c18034242e0300055a507200c03180044006025019500d40e5000341051a140d0040c001030008121381030054584100d2883c2100c180241706015035011140030b81c411210701f1547c42420750402d0600c10306411802c080340d1540b0407902e0080c420f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963060890 1250 963059640 963059653
    0x120f080c0f0105160f320306090f04020312070609080f09030106060302090109030b041104020c0f0d090e060915030613050c0901051f020c0306040614060a03051b220606021501080a1401090203 84
    0x51b580740500652180d202254942c0040c0c513152450030140204030b5000f905544000500d070812940030003d022481d2194501292490607a03642c4a903075006140343c02142e03003000c166548140350030301a82003c2c08943c6421400c041031400000e241032818407028007012078417401b190034420641d002e02d0b030390b14014000f50764130000c80c1e10107565410584c1c0411703141e014100904800d184100c40c0101118464640d03d443c81d203451081210101016100c01c44460010700c1c00e4010761010300415100b412050814413640e055824214100700300c400c0035078842c1400300010b0190750f0361070414091040906141850441d000c44042c0c1c58038422100056042c8944010001089402d4012540151032224481116103a080611180c08040e003c0100107402c8403120b00312520500100045100d40105210300100214155800d5142032525290f69107860f44420300002d07030100010780d5902072000c00c1d60322662402c04503a4664490b03500003410303040702a60701550010250004900b107a002400d540c1c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963062140 1250 963060890 963060977
    0x20d0b19180506060304110d0f11040609060e011208120f181f05150a030501020301060f09060f030b0d06020d05090f010b0a120f080c0f0105160f 64
    0x140d42612900054261a0140c1c51829819000300c50050b04003034292419038903295502003010318880c85081d0005462200040450b05c8008c503e80c01600503004514201043c03c2030005549040e0080700c00242844000c008048025804904580031414015405000b84c50300400301d00c20751b00d03615200049102806400c2d80c2c08a4140d0090344017113007070004442c652075940c0c0c54000007012044020501100c034a99010503810043c1d00c8000a2404c1030005480b030002001c125003034000352071681d4040010700c4600e401140d00340c01d46c4010305007036019528101c0014000500b40008030109a25080b00300810344403182c40c581d80c1a4004010740d2901c5800720708034004c03d021240d220551158450510303000c5070601c118040020040d0505500504140c00c8040300c2d43d2800f404c60f490138201c00e4803400316a0b000084c100e880701403005030406d4102c1c99000c4d42034681c00303000400c81c0b810407040401c145420600038019045a0b092060824000304003071500c0245011800c61500c4607048541e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963063390 1250 963062140 963062179
    0xf120108010e1005060f0904050f010c0309140a020607060e10020403051b060406050f090d050a030c0506010839040c171f0e2d0915090c04020d0b 64
    0x11954820000b2240303840d80542d60402034603011782e0080c2e00b00b0903100060341e0078146001c605074030501400441c0e420300e840079502400c450f400594400007a656220800c01c000041d003484010210a800401030038016400042d018071888100411317695441010000c12181072000d102074003501078045440b00c1d56810103076103840b4407509000202d605070741082807a1030182d055405462075a42c8080c10541d511243c03071119030144104a911880007011100014810081041c2c940c0c466900c101d5809130900c1c007640383c120103810082d05a000144403000319030988160414080300340680d00070800d114050903102100604010750000d00349202c03041c3e1550851000810301c10301643d1268266034000b01c028445400441e07003400051203c1c0104090144001120341010000092a10019034a00d0240c0e40495400781d00482c482a00b080200209082c0200100041400c0c00826240b0f0044c810715214202003003054400c50b400708040480b9281c0340c0c0110b007032410191060700024450818071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963064640 1250 963063390 963063401
    0x4030801060f4d0c040c0e030303010f05100c020102062d16090605031311060f0301030609140109030f03151205031e0a08070c02010309020d0b010303120b01140f12010801 75
    0x40300ca400740d082a000d50441011a10740c0c0303c03d43c1c10090711042200d1800c00003d0490303c00d0150400200c50070070340c52690107100450007010070011100702d192034035040c010310f16075007003103102030000c000c0c2c0340000360b6004255145d00036402207c100544400d082c00503039a0b409c41c0304000c54103090104001881c1d212200138490458a52665401d9942e6042c003110359100c100c3d40100c1c0122003910500004003102c0030600c49a000920780c40c1404d00300c3d01400e2a540003680240c40c0c076901c410690b018020104075442e41802c00800a0080118a8801606d4160984124010540d480c64130035041c040710076103000600720140700500700612600b0039694a81016403440c01001c1c0c00c2d42c503503c1c100510022609084003a07101c1c1311b02d940d0703120001e072040032080f901a41410746920714000140e48980c50094080e1040c5101d1141d1350644c100108610201060351640919011282c04541c1c0c1004208140300d10446110344e5908032500c4501c0640512180c002d129607004d40080f48126064208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963065890 1250 963064640 963064727
    0xd0806030601170712050111071a0c0306010509191703090a0509041518020a091a0103020906070f0503160c0e0a1b050d0e0f070509010e04030801060f 66
    0x321074841e41c80b000c68090f00950f95a03030107034662142c00100326801440707102d101070a000e0400041c402c6105080b03c81c039a40060004c903034a00351400d642d0b40880c2356070b50b2107801c9480c0302d50301400c0d85401000a0568422030000a01c640a60150710240c0b141e41c0e102d120240c070401c0303404003500c0c1d5460003090303982e040800b59610035028498046118180444c001e0300c2a0740040026290b0204ca0840c6c20040c00b80c52640301c036005030b80b2540e101580f602401080145014980091894201c280710a9014503060400e81050b0040100e070a81c0d0b030722541941d042075040450070681313031458a4683d1451003441c0844405040b448041c0b414042c0b400c010300222072811550f1102943d030400040101c030700300c407982c106284485800d01c1641e403080010b4200144110303c0040c01c58503810240c2c3c41c0103405206c8114503070124406000b541058042280103099142c07282489080a41e009005044140200310820040320341281c1d130148944081d00d90190f0ba2806005030808548104005181c1e4852 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963067140 1250 963065890 963065893
    0x1209151a0409050a021201060506190e030a11010f0c020d0803010e0c031e061309230c0303040b030601052206030b0f03070e090f1f0b01180e06120d080603 68
    0x51456007481e005466030598000701604803034402d0341c20031200003105018011a9940c6070008241900d0710402000f916403000007208420508440042c034024004040d54040c0d0002010800000c41c1d6150420381460242012424404250801c541d4551588000707980714800050702010700c1000390045040c0c0e106039141c2c00c5560340e6084460003911042d0754001c1c0103010101d0742421030344e82a8041d50041c000800590b41c12485241030810748951b440161861203000907644591010540c1c0907100a40d0382c8090302400000500180d120f02a600c541c09080d800000003401c140e1043c000c54080c01030400e03600c5280e03d030402176144003c1140c02940c000ca071404082140310b1130420254204110018001e0034158140504001c02003805404a4828031403910417070100c103001d1203105404580000e0360081d101342c010b027010640c3c1c01036071658144000200700a0300c1c0304403000c2110644a218200782c19580f5100049450f0180000c8024124040d148030700300c12036800845140110400c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963068390 1250 963067140 963067181
    0xc0610030209060a06143a05011a0706020a0c170405031203010e04021329090c04181109090109020901140405030c091e070c0606091b120915 62
    0xc0c01c0c80303003050030b501462000c90f90440c030701d0341002106d400600e8030812850940191000b42d41c00d6110030300103031000d24140c6090043c004200c4405120319030040200f8160400c1505061011038810302c6200b80282c50143c00160740301d0310500980700111026846800c036684058001c030100203582180c00f42d81d2090007440d03940c5896207104000e0301d058400300b1000700c1c00c070384807a401c00020110780b12484030308949408003542022103282084103000d240c241c05406c3c2240e2282003090b0364100601d640d50000c0d042c40144440e22a0080301d501c0080080700001e402e0010751080c040a000c0c1e0901c850b48080101c0000c642040a90003905030240281c13242c950540c60090110101d008038080c481d019800680d00720b40900c1e102902c2600040c484203100500003940005442c4041308540b1075003c5644c06040c68200141c2e441000004d02c1242810000c0b944c8c0c000003510951030a416602c200301600181d001104004e0340038a02c21a8002740840004003005205409000c044020524042545 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963069640 1250 963068390 963068401
    0x18030c0e1506040501050906030405120d2a0905270705120a060b16030c08071a0a0207170a170901270804030b10150e0a080a05060415020c0610030209 66
    0x10b07420388041e1901610b443d810300c01041c040c03000d1030304020302c184c88605ca030701407440d03405100c000108881d090022010513182491104602c6195180030020200600d001e10300b580103a21038284025644201c03044100100c3d11010380e41000440c18480f0900c0318420207105049800000416a5114104207101c480e981c080640c82105c1e114800d0b800d44407001c12040010240080c840300106100e4102040c03003654584401d48a80c10001c0c084030801407840c190241ea20701080c10a03400641c150055141000c65640c9180008a41e0f85030004004003180b41c440c02405000042d10340544149004020b10700300303600034060200c01c2c12007003e143c5007422043e0346400a00c01c4106040d008010030780790915650f136224500e407004014560941c00c40d41c01040c8480c20b5101070058940ea41d072840194a110010896011015485079010764050326440c00002c0c1e0114001d076020b0b401a0b003150000581034200350207480b541e014951540a1741007000900e8210726600c6003070320b0094030b0500b199541d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963070890 1250 963069640 963069649
    0x9040309150207030b1303081b0d02070c050a0b16170d0c1e09080714041d0601030303180b06010e0a0812040329160c08070f02040c051918030c0e15 65
    0x1001d00640056404000100c0c031222009c10151820a20a0450b10b0490100d1b107020403600300d4401181c2e01c0704c1e07610b000c0150346820b944030b8018103802c2c0841c0b4601168410401941c40d031482004224820015584040080c0c4009403a50200c10b5030041c4075251202c10014803c000403202401c108241c0c0c501e2202c880d115100440558400c00d00800c0514100202000340150513043c2c00d40c42510381001035492007a02c00d107200d4004081004006c2075040d464080d007034803d810010080045410a02008620002d21f030f00d4019a0a00b0001c03114442070f030200304d200803950070031445803240c1100341c88407001444c0280b00300d901401022000c00b0445491001c040c01c0044c1101c2080503030750208440f0b504070310504c0c02d16825424408041e01c0c0355a110189a004814140c0b000c00204124a065080078040c0098072030042c81c20714500218120540d4840c011621017900300440001202e208482c41c00901c0e0207580c10251b0714142e5540c1e0a50004d60003401c4540c540501881c2a201b90785041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963072140 1250 963070890 963070921
    0x31213020a320a0e10030501020403140c0f090606180402040825030201020a1509120906030f0632090f061e090103020607060209040c03060501020d14030609040309150207030b 77
    0x81c4030f031214524000344500c4021018000c03100e0080385020000c006102440144025803103005100440600c2014280c149000561124080d03a41d0a54140259569184180c1d212900301e5449407940f008640e42502041c4800100d41c2041c400900480c03050300001d80d41c00c0001804c41540c0d10802c030316100f05503481c490300c80280075034415524000000c0c11010885112256400c00090002c0d003071320744c16203107170303080940101080c1d070408140a22503150140100405600d00188111440c080109070301401d8000803c00b0b6100c0c80e5485100c491401000180d103850060004000c0e00300540b10b4003204000345c81e040d204074984004102c0000411603801460340c801419200141c0c031359000d00c1081e500400040360307103540c04c101ca0282a03450b03100d10585080d00d99000148103051500282c03601020040143c24005a85a00e150134182c0380212a400481650041c41d1130710345240a603a81440303600a18101401e00f08842a6543d0004003001228001c5112211544407500503148011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963073390 1250 963072140 963072239
    0xe0d0e030706110c0108071701030308041101021c0e0a0909060204090b09040b070c081603090305070803120112030309020a09050604050c160f11030708060a1a03031213020a 76
    0x410603109504d09601640040f40c2c8041941404a1407071440c46c099101c641c03003604206e01150b030800521060000700702004071124020700041624404840000e80382d010001c07000b10403c40311003a01d081a0312003900d00c00082c2100034042c40301000784e182c6000650482d014070b00e503013031504038051414038200340290b010b1500400076078a103488020301166540c1e254403080d91030000030855a0365184560340c1d88903602c0c1c0280e0342d8407a082d00307621b08103050598540c800d80942d40140614400c0c01515000b10f41160b0038160015900400303417500307070702901c0600806903201600c1140002d2441c41ea03080749124410488042003d035441c0f80450105000360b401100065810044000c0022009095000b00e140109a00301000c48038000192a028403a00151101d800c9681889070903105c82c01060025422000803414940c050008a69240178000b07640715458200300229100700c02030441155202d8000c1e0203441da860300c6140e07000c83c690000350f60340201044034800122400c1c0c600f10355500c12 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963074640 1250 963073390 963073393
    0x6060f12011806240c140d1409010e010e0d05060118062313090b01090e150c120406060e04200d021c0804092c1501090509010e0d0e03070611 62
    0x110014940d950713001001003040a001500f1260300209644090031550940548000e120100707104070000c1c0080110380508000c60014000f0164030703a00104101111103082c600032030248400800291074240c8030340c014100d80038010000c074100341000886960f00c1410304051003200d03074400030003840c80d04445540c0c040d6008100c040c10384d03241c007602540f40c889203800041030140070b46d200c0f601c9944c0c01703920603600b8943c1c8154000e0000400c1c0311684690b1500000c0c2480340c58451440203040c425014054000c241440000d02080401d5201c900607090998040c00c0501c2d21745028000e0045d0071041a50500103251114006d14002c8403940c82d0617400b0b40701c204151911200c420000e088203030200d40240050001060160345480342da500312414800072000000c0030ba5500088502000c03400c4076580107444002d000d5121207040340e04680111070000740703950300c0803882030052505603800e403001d003c0d03840b5580980ba031040c030120200360204c096465680d610729003580c65440b0781c41500c245 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963075890 1250 963074640 963074669
    0x70212030109050a09211404050a051c060e0a02090a05060f060d0b09190c05070f08031b13081006120f051513061b0206060906060f12011806 62
    0x1c06080740c1150760400158100490005c0300c03a0344141400d203c00c1c030b070491050b000d8a07200818652104415816220310581c0a19050800006c956150218091030340a1400558445841c40e072900740a50071941113401084815940d902d0b1903150002480140d00c191510000711b96070344030600c55075010f800028000d045401c0300c0301c10300409030021100025619030310422102c0949424445a00c02d66600041c1c45d01d1103141d02c05101141c2c050010f0340204182402110005203410100164040c0c0000119450fa85e45505101c9403035400e0b503400348900707000b050800b401c10303071041da00c0706483c100030648141d8100c05000008851043c0714110400e41a40d041d240801c2014040c0d19440f40180161540300c00c4044550001031400e80d0b034a00044c260200000074090b9622601c4e004c03032002101c412055041c0b0038000d43d10035002d840c05100e46a500023090703081c0d40340000c0720700c0da4410a003010340307951161040040a150904c40c0e884004000300b14000310f260244075030000d07103a0b5514603221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963077140 1250 963075890 963075899
    0x501050c09010215250201060f09050c0d0e01020904090b04051e1504150c05250f0b06040902030f01020d05090d051c0204050a0909020103150e06121e010e060702120301 74
    0x2134180c0161400916116000541c410b421480360008950a0150004502a4507210258203030100a9125403a0b8910303001c240700100f0012001c55050125224011880007001d1056500a20070032071b00c2d681c82840c20810204011039608800c1c0700b5400703032041d101d0113042807403220904016081c00c2e03142c6401c0306014a11101000031010742283c010042d140017a150305d0401c0c400c4a0341d040100020540100e00107045203088075410521082e910190603e081c40c90b03490490402040c40c00402080c0c1100003e412500c0d140c4c030803040075400800b25800150340c00f00300790003907004010007a01a82414001202c1e1107001807102039000c0d15684280c03a040b1012441d8500d503003030100751030400c0d408000010b126070741c50011001504032400c0000d009070b1140700240031290040c5408861780344c2c44008100c2c100b41541400ea200f54103841c1d0790005580c6403042800c0c40001090002d221640b40d200c028201c03015845440c1c11012003049a14070f4031005e0044c2d94500302079481503000e510400040c030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963078390 1250 963077140 963077173
    0x1050d03051e0c0d02030a0e0409080d05180708150414120f03270a0204151e08060702120702040903090513050709090b0a05150408030304030c0501050c090102 70
    0x220240d00070314000d81420346084400480042c6005210801207002ca4584405801444090800d0419000441ca0b01c0d12500e40a414802d01e01c054074840c5030340e55151000c0c020220101d07800c2410f12481080140303012040901c03c42c40300551000c2c60310541e03601007040304000845407000980d0289100c3d6a580f10380d01e110204d80c3c2d880c0365203c0360080d480410b05050044c40645604a0b1400e4910380b01d00e030420000c44c0c1c0300300000e10602c21805540d4841000d0802213101210b5580544c0d01007800511002c070300c2a4042660b001c400d40101c04281d0302d600c4460a03d0510a5610342401d40c3c045881d000c00032a5205001020900c00c10800c0046134014500742d402060300f181300b420000000c030340d10030008000c5154810004141516542000b000c10790142d0002c0207004044803c100a10324500400c2c0c1d80b0300503018950050760b0140c0741242c484080826a802040e4403000c803a9645003510f00104002c0030307031108032625824040480c0c9000b2040f420f9550340d0406900070818060303c081c407031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963079640 1250 963078390 963078409
    0xc0801020c010e070b0f030411030f0d0f0e0a030206090d0624030501050606040b0301330804120915050f0451080402040b0301021812030a140c160617060a06080105 72
    0xe526201d80380115034100bc0520182c0403030703205034a07200108410400c01505602845042e41e02c6014004810f00c01030392181d050310b014160503107658004101074a0f0040081c900700c003241803810008a21032312491951000e00c01a244507a009000c1619158184001401031340228a00c81909000620810384407040d1401e24007000c050440c051024040e8454030824110442d070001100345041000f0f0140700b48110a11910f0340c07408944407444c080d04440702c2c0c0703100140c03017040100c0011840401544041580c000e0714550040c443d02d20400c1ca0a012380000084805180c149100d5072030120f4441244003c0c92201009503142d2031003c1410111400903000300120f0b4000c1d40c401201003262401d1004d040341410355903e20390b0701030000f0100b0688989231483c4001603442005079201055001c0c00d5a40304d8070959014648a80c0c015044a003807031600c10301400303001c500800000d8015400a9070048400e1102d1808141c0d49800e030901005c14211300415001c141d4200040255040041c00c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963080890 1250 963079640 963079673
    0x30f03060105070804121a0610080a0c090807090c11010e0a12230a1209021e010504120b1b070c0303050901110a060614030a0c060c0c0801020c010e070b0f0304 70
    0x3c03031801c6c1e281c150415010075071500580b80b40a4206140304c00035100c3c4c6015800c1501115a480c160100b0000181207501c0201414a00e68807080c030f070f020150049010202070841c032001e55034041c0d16900605d0050030301031040c00016540c0701e02d0091248040c8100220b040c03440c8050b00001800d42c8419a21800202600c001c1052002a41c0c0402140d90081751544414080c00d075944c0c0003100300101142151030b14400c1e070743d140914140c0183d44944d42d41140010025500d41c60308150f50040c1d035280034542c03040480381c000048800c20400c0b1031740290b2113510440c04c10060190a102e600a040c02814002010a05034902c2400402d004001410381c2810501d13000d00501c03814006c403414150b0003001143e010761500018441054103407a05640c0440c16001800c40a20700e850384400c00d400d521803201403041000b00d110920a80d03501100291105600a554400102245a001300440b80c103003500da00410001058040c05d1a00315219205000c10181c2140c6071921006400c5d400c1841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963082140 1250 963080890 963080903
    0x60c06070201200324041805010b0a1d040218040303020406021b28081e0d0302070f060b0411040e150307081b0607120c1109041e0f06110d0e030f0306010507 69
    0xc521700c550760ba40604468446855000c0203502d8440ca8041e003034940d840040381c45182d80c42c1003440420004e00214445008071600105261681e0000c100481c04103143c1e2440540c1510030007040c15055001842142c2c880d5080381d46200034450188518940d80351010f42c4006030310000761082c610299501b1242c00c032111f40c448070a80d0740c4a998600542c8902c0d090a684e0303405081a09000180410030030a400d9040c258130703217500790b41c03a00b242080d0440c00400c0c46645010345100c6e6221036120100d446181140255648d48503114201001c40c00c803405991170030910b46070680d504010941d14100d90300035009003042610509030b4051141000601c54028409000340c01c0410104207101041d8401500e0ba0141d84505041c2103a00010004c4d0381c50090710020f0a02001510f203070b05002c050014480c81025403181441c24103440c101481002c1c00040c1449401c0c1008500c440c0240941c140c50f2004000714600c54484548900600d00320a071052001d000192181d4010801010303000e01c60031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963083390 1250 963082140 963082201
    0x1101030921030603031704111c1a042303030a0917210702010903020606090c07060c09300201050a0207080102270910091505060c060702012003 63
    0x1081e500c841c503044107480000a40301caa08100745508004e00c14401c00201d98110365500d880e88030381640c80a42c1800502a44417041d83c0800500948640720b64140d011a203041113160b000d5043ca42c10700143d6083d101c02c110710f511240441c81200049110b400401e0140d401c1da030318140c65000074114098242c86600f401550221a4442c4000401000301d01d00860a00c08851224410190f04d00418031410741e854980b0b0761012940000340c440c1d1281003200d02c0c400c641d84451540225000b881d0703000701541d0422500284c2030b138010307480707009407515000c01b21511080002039001020006125000e640f003c440382c0340245d48100c00401d80404903004844101e40c1c4d03400581d08a900100d0340c074050300c11a00017640e941401400044440c10206c03070824407070401c0349104545446503c18075070b000b5511768110204100d0a107402c3c005107030044c4281c1d01c0c0e102e00e070351594840404951010065280030500901104a0010001c03814520340d401425652240c411540c0c42552081051503440000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963084640 1250 963083390 963083423
    0xb0604080a0501050405160b0403081c022106061e0706021b0c030c090f06010e1201020a0512090f0a0f0206040e090c03010501060207080a030e24030415020711010309 73
    0x10004668541c1c819000001c0c01e14040c10601c0c18030b60441c01f081082c901d005410054543c040c000c0d201560f0304a00c0d09a528036658404802c402500d0100b60b1080340040741e1860006c1c4c40e0b88040c2014940e41900601030303a185020060244241000e61001441210b009200e24031994040d0003614840d074001440c10303140c0c1814125454801c1506001a4414009a41d06003400d10600e41c7e840070030380d807a03611410108400102d022000b06220704104030b015482e6155078881002c150802e0881b80215520003e140b030041c10b41d40080640c01d0f03610818000714034400300004045c004038103058068442d5880b95560440d001c810603078184d0344010148000b18072031406183e21070080c00100001c00e80900307103105060030340b68142e02040c02d542150108001c0242c0204641c0c4000e41d0514226461600c020300003030000a0261443e68043d80a85488810008000c0194003560041058901c40030105600304140e10a480004016000d00040c40c4000c1d40a50060f5a40a00c120480aa0034526 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963085890 1250 963084640 963084643
    0xf050315041e14040f02010e0114180a0506090a26011b030f0e1c0201020f040b0310120f080304050f150601170421170901020a1d130b060408 62
    0x1c0c41004040425202d0b5035a15440e10310411408406040079041e0b41d00d41074851740c0d00340300c43e100b01038184285030f92107030701e90f1b840b45c4a0149400035120ba1036445030095098640099015800380703020305ca0880300417550386441c60a071a4411001031824020130b05111400909020b24107494103026480e4504042c220000c2c042c00c941e0145840c90400c7d0041942e600078103550340c0512829207646445048801c3c2c030700102e074911b00301d951300201c00d12501079800708032700900c504140741c2074000005c60b01042e041e0b008001180208051884019000d0700c540c04801c0100c41083c0040c00808000c004200040e80700020b194030500813070075140256100c9072004d0410041000102d65004010104003c40d0b03045205411000c10b9070b10103a00034030382a82d4408030f4004d03c040b0701d078204000e120510f0740f03944100b245601c6d40b0340d03a4655000e24109240350134040d400001b02c1901292008410341c83e0240d4024040d0310550000341450a602d910b01900380c001c101054905410810070000804e07480300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963087140 1250 963085890 963085901
    0x2070521101a01080609041a13020d0b060901150f0c020a3f020607080d02091f030516020606150d0914070609030503030408090d15090c0f060f05031504 67
    0x1940c0c540b101d000421000040107040020500c078400e00282c02484007087d965806555012050096124030b921394014a42410b550310000030344c0145003080180030442d402150a0045c04140c40141803640c84000350f002c41842c1c407a01800141981b01d00ca0306452098120000c0140003074a108401901c0d5080201040f01120030002e0007240461100d003d03902102800070801034403240207605000b66400141644134548000e003140c540402e41c0f03c0503160700e604403510781d40000d16a0900c281d00300080e0380005094400d4501103413414000a010700340304800491802110340c040c012a5a0b00710801400c600803508510481c04144920151058544225070415000c0c82d081200c032840c6424440c9001c102d03402007400c01420280030400240004140d981240d4484046601c4810500c00303d003a0080c0c0c030030050301c5d50018810f9038030f0f20002c43d80a072800300d01504048064945030b440d2022107201034130501c0f000a4512005c100002c1c4a40003a641000360000124030f01150000020305a90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963088390 1250 963087140 963087161
    0x503061003230f070908010e150a0b12150906040c120303060801020a090f050f0913141e0105070305160c03030b03030406170a060f03020603070203190809010605010207052110 77
    0x100e1800c4c4400f0a81014401d4018502030009002c2544040f00310b80d10b400c03003200720b64441c0070001c002c04d42c01e40058000a68212000c0c4c07a012026481404c0e965503980070142d440c1c4810f0321310700803680c115800314003d4807540d000408068418508a0030011003001440d050b0205951040b020801c001c0a000928a000f8640d0340c01500c00e0810030700b00540d006590000b071003801d001c0c00c0030400b178540c3d0303100aa200b22a155940c0141d01c1c90b043c9400c11030801030080741207002d502801903a400c0c4a02400ca40e508810b00204620b80d51800c4c290304441c42640c5810070508010a070408941c03043c804585018843d10700490303c21201c0700880d2968200d80c02a601103491501103c54503480300b0b03007581d0b000c003115006000340d84c504000d07d00c3c541c101f808041c0c02503a0000c001001e5038020011182c020048032280d85034110f54840042002c003059a80c1805035080007400a49580f0001d000801d03208003c000740003442080c002183c2d40e899284180c2072500510b0039200030100035106000480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963089640 1250 963088390 963088411
    0x112020f0108040206130f051320070503040305010f020a080903030603150709050913210c0f0f050d11010b040e10020d0e0307030f09150f140f0705070e07050306100323 74
    0x803820902007080b100d9a022401c1c9c1c15903d4848104503c0c105950b42070f80328002c494006a81d03419604103e800c4d4030854001800940c00c0c0b40300402c0c0c41506900412145170603660b15400760f20f40700c0e2400c0d201d1109886199065200741c52600b00c02140b000010780141e010305186842c1070b91040460360705241180c480d5080503e103a0007000740003802c604008d03101000b400b500d082c1038010070094000031442ca4060402c0c00e61050f80010401c101c80c84d2034850b50000119040c0341e072541401032147d4003101407840796500780652910182014000c10702c412030720340050b1540810000154000303400a8200c154100c1d1038200d81041d40005100414960b80640d031044640030441308090110711807540046100800380030301c07000311a884410380403500030380d14104812402d10b060301c0e41c95002d03858401a240d580059213800700040040c0319070460350050203040555844110940e2240000c9890b150088510280714051a1113503002d4204003084840c000a05100e130742c40c0d00e84c0e03984120b9048005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963090890 1250 963089640 963089669
    0x3060b0706051f0608060f06070c030b04080706020d05090f011a010e0a270b030d0c06021c29030c09010b0c1203070801171f1d0d080105090112020f010804020613 71
    0x141440d00381c1e000e20748020707903100707141c14503a940d54100b072b20701d5101c0502405c4840340420100074900c81110a00c9801c0300041d9160300401c840072000b000f007074500030268440c18020070403021040c0104111400280c0c01340841c0900880103403441061a4806640101ca161010030070440101320003500c0452111003522020542610108139462400381b0307032003984020214808180e0050400050340e521040160725103082c6501680c648810780c2660204500700b22510740446c4c840c504909a0491241c46000703001e0600e000c1c59210481e03240039640090703190005000c4040041d009148051007542201da01d00020252034803550000d40d01d40d000142c100d401080a0003c19540c1c00c11080c0c0da402404240c1c08460141c640f08040300380c800381550b1241c1350005840c80e41140c0801c1e5160a0080d51001465003c1c0105400000d004462040320000c001041c910342680840780d405a0180101310f0703d01a00c0015502500010400c07079010504000001c0180c5c1c140790400000c0c0743c440d942c01113 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963092140 1250 963090890 963090901
    0x50c03060117010515070809120d02070b040e0a110403060510090c17060405060d050601030606170601210606031a04030906020f10050c0403020a06091503060b0706051f0608 76
    0x380406034076590660207258005000c580d59400001170340903040142c050b9600c0c81e40c5030803242402401c8840d0380c40079100f40d1a409030100490701c0700c0d54a2243e4203403000e4031b80740d0048441c1802140202c8400d501d12000290b03050900b60f0140702901045800c0504242d5240d0b00d0505440c4c5c101c40d800d405541c094400c0240758681c2c002c404220100341841034060811130903c00310503200800380343c411071726140403400d0350f21440150011140c001e0b068901c15a100c4c1013500140100d807003030b004180480c00c14280230640c04114a4180c0350101098641e03140754007130b84204c151400c2e00541d5055031751100000064402c2000a00a2540c64018040f6141c40d0070050803a03a96980401c0554006a8400865030400702d95948084130720440000d80b625a1400180240100e4100a4002051582c04035050b1340200c2e8040840e102100000c10000e0a46402c50607550a4802d45400c48800d01081c40083c4140c1c20156109032400c0c4803c540380b00034107021440d96813a5000c0e030b02190f4480103020303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963093390 1250 963092140 963092147
    0x150908040f050a06080106021005060a0510030b091303021207080f070510050108030a05041e08060708100506090d06021606020a0905030115030b01061101020706050411010e030d050d0f020d050c030601 88
    0x700204124140005c1310b614001002c2e40b2250310b0400c410305160740380001511a52074440c240080d1001030583c41070301c4000ea50203001820980001da01c0303406184005600c07940c0c0c50b80e01000c0e890b8154054040040d40280910311500100c2d02100c560f4000d00451609203142000f82c09110302440003042144036280f100c100729001078100d101e49030010010307a01815080012202100d1015810382c50080084044560507241a00034840e940200307400d01061075071280c040e074000d400d070f42c0b80f40c040f030341d40c0303404010301032107803854294000e6070f500310100126001e640a400310000e035000300c109211403551440100e034004001c0b40c000c280856020300c4603007424414801c0a4000a044148031815a280d007121004140f180c2c4003000425490040b001000b90192001180d0002c0b00f171100e0b0034180341225003503080210881c006621050007500d246070000e507041940310fa546030309107440c0218000d50054014440102c400a408000c030340d160074004c0c030451b4032643c0050350341916400e2800004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963094640 1250 963093390 963093409
    0xf0607120c181811040303170c0a17070216060207090b0d11121e0c181608070c02120c0114070506010b030a1d0604050f0d080103150908040f05 63
    0x20404a1001020b100814240c04000c0d610414502e0440000c5050040054401d0410031081c03084003003000400c0607000800443c854461000c1400c00b43c0c0d424007403180d00e020301a0248009441a8800c02040c1d220034103140d080350309841580e0401800f680d100a410856600c000e005901a4100304008121442907005149040b0740c4840d100d0302076140c060503642100103861041d0807450350f02418507020080b009551508105100396500384980058860545000050050f564001100d41c1ca07940c040015106500c10046800d030a084400f040744c8865000b8075413014031203c0001040540e444000103101c000c000c10041104624460006244865540c942c0300c480c2018048540040c4001c60258151121100d8240d12507a590042c000540010703401000204951400805141808660f0074802c500603801c40d84500c0c21a0141c5903510100034210001860000052002031140c002d1100794030141400802e50445980300c0a40e1a40030750300281215480c004200701c00d01700140300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963095890 1250 963094640 963094661
    0x12020705040b010c080c0c031b040b0d030503130203013801020d0f181a0705060105090c04091e180c0609150f170907030c05040c0519020f060712 64
    0x70b210008888001a102010b85030380202400d40224100186000402c00c07951070f000010101c0d8803415040c2c0c030f81a03214485540f1346006030b04080b2039100701e050a04110700034691513a501c42c81d660380c0e0440c00d44400d0103400201d0b450f54884003c6400e0860480360803c004c1d040c00e80c41c21400c41c00003050556a80c40260140c155006240e4031030145030000a00c4040b02600c2c10710f540b030150034450302804d0402603001103003544ca00400f080c8044000d1030290403043e103d00e045454a0340c07104104100cc600031580802400000c0100344603109494200340f044000c0c92140c3c1500804500b40c4200391280141a04090020401c41c01d0510056603d54030040ca180e0400341c0100d0b0520091b01c1c0d0201c5490803207800d001d1804040041c2500c1403566014000303c17400d60701e0b842e08020000a40395141c0e440140d806d004159804101c1c1e1409124500307021596803070359841e064a10752600d0007a841040610217500502103c03071a8404140900340c8510a56501c001d490100d9030406011162050324 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963097140 1250 963095890 963095899
    0x120109090503120711100207030813080412110d0f0b0705030c0315011b03080a0f020c0a0b060a0b0d1e0e281e02180408092b12020705 59
    0x3010200d40d0100441e00105001540540503549a0741c040d6800e14081c140404c0354412a0b203188040e48065001e8014244030b551401d54540f605900c0700f0181c0413100010341782e202e00b003000b0400300b22150541103c10307100316000e41c040303684136001440d808110b940560f113048004820208001c0022015903000d213650500d54294107200c20360b43c201e400b00500700d401c603107480d180c00440c83e0f001c2c1440d100b100103808101c001104091038004c0c803002003503030b11000c01406c2c240e1804048407140251401092404001d0207a18650b031a00399240c0800b52110f600202040008902e014500d4010450311541240105007004022180080865a60347c44103240d40f03018119400303840c000c00c0304000c030390f404c51b400d68504070050014001000c1070040104a00510150760000c50f141300b0303d030321096008484940190304903101c110032090044400411010f000c125080b010700d020003045600c2c05003e03121445000c030110403e60b440003d40320960340e80302c0058901e00c1c4503504000d02d2000c1c08083d00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963098390 1250 963097140 963097151
    0x1f0c0305090313181113091506140f091801061d0d0209060f030a05162c19020403030c1103010204080318130c080f0901060f060c06110301060302120109 67
    0x404005120b4261301520034496802e0742d00c0ca00e00042070b04242e280c8000304241a07622a21850f482c0184c5649201d050480e03401d0981c040740c60340001c04014201d694580361882d41c03025080702e1890703e512103040e0011014090046001c9516841000030f001d03040815111159410038001a0600b0b05840d65480543c00c80c1c02601560748500c8040c18a5680c1601c4a04a98440c0c8000504420004901c1a05442400d0a42040c40000101200302e141280120500c6644402050f00050381d40c1d03940c040e002c0030f0703403c0c07100c00082104946640141d802d540d684074407070b03003080d507005a074071a030300c1500002e81104040c02400301c10100d1b080e90b240101c0c000c5103031901d84100c40e40c403070140c0d001082d9a40d41d200481c551070344500030340c811232020b0254100104040060060b200c0c80e41620b03074020b004101310004600c800144114401d68548500c045262841e001084802c200441d100316003041d100c84c10452124000405140607000d90748000d078940351940005040d025051307001c903a0f810b0514 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963099640 1250 963098390 963098407
    0x504020f0405040c0e22050a020a02030a0f02070e01090507030506030c030613111003063b07050d1a0f0105041406090616060213351f0c03050903 64
    0xa03412503003103a03825540070a01140c0108260f5280640343e49940e0445688085961404640c0403c6070044808200801c1291154403000c0c049026882101015a100f0045100e04500440c140480d0740e840f841101d110a0f150050b007520070310203a00940e1025110800d001ca216054003c00707500920035030040080341903103400130b95244005010840400071142c200e0b8140401140c03c1c01c5184409404d1807100036079003000500901042c0303d12108041600140200c41100082c0610000d022403152152891071480030221008054a12028460104004080c40c410340c0034010f600d2108016007170040c0c2100c01444441c2410a40050411804100a1110200700c111820b001c0c8001c4c1d44081d22040b803200442e903140b00c0d080e09207806181000c584400c00515070000c1600c210309903180e9404035078a1036080041f010300146100c000c19400c1c600c1e20403a009070b080300c5c050076252089079403045d5180368291002c10740c240c24080c0c07151103034203400c27500d50540038150708900100021894003481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 963100890 1250 963099640 963099667
    0x1407020102062802070c03120c051002250f0b0703092406030203030c010203060a0f1409191d1203100303121104120209070806010c0204150b130f050402 67
    0x2003c144880c820416000c00c0c0220f0007203002003803450300d071045580340441c1c20200000c0c8001d100071942502201c0d10484c29621030843c0258590b840310040c03188400003c03400c00a50031910b04103025805000404052480101c1f61411060107004d22103030101d100d040c000030000300100a84140b6090502c10800514010b903040441501d908034402599140c2408201034145c96001a50511010480614a18040d4003c40c040d00c41100c0d820b0005541e42600c803144500c501c15041c401c01600000485402d00862080e40040c1c650310240e0b100f240c4071414400c560b200c603003140c0602c0004882c140140d10070040a0518101105010704616000c0ca9101400c40c140c000201000701076554090006050340081603408910028961501d40743c80c4165202d40611006911424080c80031403a2640100721031402a074060f5914450200c868092202a1003004048090700503056000a01280104003078041c00d0030903440c03490f045292080300007103003078a508040d108500c10440300c0a400c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 963102140 1250 963100890 963100903
    0x120606031608131208100617040b0411091006080a2c01060e01060f030b010f020705040b031006090c021513170c10020a0201060b13120c090c020a031407020102 70
    0x301d840d00c1450b6603500143c255480b41062002420040c040403038201c99a000040c59100b075803082224007206584440440e5501480721076802400d5806022802194505044961043c0181c4076096404c902c04003280101c04202d402003036800700f203441408810740c4103580d00c3d0480c0d0803280510840c1521041c200c02413050012840c842c1e9283c0d41e822120450a4000400920455580560715070707403220050400121f81e09070400081c0340613032a0540e903010746d115050610007940246031140c108003d00c401080e498500aa05114000d583c41104c1c0f02400f829000c1d22003c8070105661a1a4a01a1401c1c144034541d0302240991801c20000150207800e00072001d4110003103040c54040304407484c0040c0714070340d0f115507140146040e0400781c2c0f405800800350304129500030800e169a810f041c1c485801414009440180400300c1045000c1403058140103082c021454440919690034010b030440d00d00145038809a0440030090081c150050145149030001c0a1070919221080c0d000035140e49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 963103390 1250 963102140 963102181
    0xd1a03070902070f0b040308010f0b0c0c0907050903190c050a1505161a011a181002032a010f05041109090f0a03020109140f1203090313090212060603 66
    0xa03408203d100030710482603a080d00e0a038200d07081d5100c6043c02d082c014420303d02401202082010814005008170480b005c1f18040320400000d41105204001000007104020b054042008418406100e29640c1030044c044101010320140241e0056403410818207101c1d5480144100e00d141000c000183c000340c0c51810941d15883c04a81c1e4421508954900050758000500b81440395410104204104030102d0305072040c0c81d0703041c0341c002000894146107209400d580c00c0300e03800c50020394070682450804c0ca02141182c0c0140d80c2400a1011082c00f40c0d031105010b01e42c440c03000b8420f01d00406007841560001000030f5001d00a5281545450004420058205000d8004080003c041071010f1004400f4640480f00340c0ba8202d8150400a001c0c2031182415108c0480c104c459140034040007901c1d640340c1031000e01424246da84405103c00e6608001e00103030f07480c0000c005140c1074040f1800e0350000351005000043c0c076446403882d00b87c088200100700a005110800c107108010800005145081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 963104640 1250 963103390 963103409
    0x70807051f050d1e181401051003321f0902010f08060a032325060c03110109080711041509150905040c051e1f021c02030d1a0307 57
    0x1210011000b0b482e880d13005080504031890618130100e98090002041c80f200e015201c0d6a15034030582410701d08a0b103040c0e0760240007020800741000090a00402c081a00340100070f1480003069030520141c5e0030b256151080303a503811001d904d64003845100c0b00d02c180604000c6c010020050941e0000e0001500d06500d0300074401c01d5000940c036030341c0301103078580515406140e4003810180385840b011081e07031245075500507004600c2c0004821041006084418200c050b81046032032a120044d540c14000050950801c411084420b2078504c0c05d000e150007581c0719085040d502c0c0c0060610100089440011622460030301d08551446d201000d2410b060b61886040010085000000c400c1e040b5541c1c1d01440c140c0e810a402c0205120840314420200d82003070702e050301808200d03992a480d80302d40d104071030390041e1000050b100c40010000c0c4003020912600442d011541e0b0b003800d5002400281840200603800010f1440c0907800038007a142000c580480c15884641c507000000b912a9403034014420007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 963105890 1250 963104640 963104651
    0x60c0a0e0f03010906150e061008060a240908030a091404150e09160812130506280908071715010801020403020103050f0c072003070807051f050d 64
    0x9a80d1004203544a001000b002003192150320b00d0100c0141c1800d00301c45041c8080c45000294030b08800e0042485183d00030906441b4061107036090740c80100140c009074202200c2c807400b00381004584c03802d0651011400c00c5c1040d0301d001c0800180624010703044240c6d07640051141440c0c03a80c0200842058072802d0018001e48030714800828000c0824010f011940c800e00140016104001800a4021348280d0256421b159144020040c119400e11503507a80e40c1c000c44156082c0c145981c068050020b0310403090006a42c0c2c0d00018110b13400004110706109004801451181050524084040c6080c100000b940382741007502e64030303a980d40c41118442c2c9052000f0b4040140180030b040c00014079180c2c2114503584801840d4000c0d0000c1c04200c1c0440c0c40c06010071010443c0c0014684074140b02d1250b18a001402e13600e46142c0c1e005402070000300408603400001070350701407008001800da81801045031510b0078080264614082c20b50040c0742d034a0040004c01180c0c48401c0358501200c40602141c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 963107140 1250 963105890 963105917
    0x50105150721110d110d08011a0304060f0207030f1106090309150d0e07090507030504020d020402160b150411030103050622050709090516050f010309031101020c070314060c0a 77
    0xa4082d030f5980010710318040e1004402415402c6030819a032488200c04070b400d21050088146d41140b0203009002001405100107050900000000c1d9032080c818103000c81e0400b0b0003208101660841c4004602007100f41a00c1c5460960150401458000400003041075051100d1079a441e0320a84420714000d0610154500342070343c40c80202c620000b0520001c22250104035000358640813036014500c01c142c1000c000c2140c2c1803081c0240c43c001e58006021307280720700c1c041e42000000e510a14092803404046822040402d02450034240300d42d40a100d0700d110500c0340805c100483c1e001550303d44d0755180500c01440030a00000d0b002c0c1d8400d4100c1c07401746c2c801420820a421303101c0c11000040c124810b149020031011001d811011610b07204808a03001d85803c1900600090014002e0503041110940d00101c190720941084503090f0090500780d103c8081300340000e09980c4480741c45d101c240d0100c1030800802140c3c40e031000306034116201030710b52030030704034401c178580d101d489803400401407001e91004c2d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 963108390 1250 963107140 963107147
    0x71b0b0d240b04080f0d0e010c050a0b0a0f0b031c0c051504121209030e040209060f031003050d0f02030d0b0609060d06050906040207020d0609060204030807030201050105150721 78
    0x804a070300c401ca9641c055070340d11100000c1d8882c1c0200c21071405583c00e002112800020840c9081c0714640701c1c0c00c03004840c0401121065145002034405114140504011581170040760703004100184c0701080c0150703058408802d9448001c0d00c0740c000e501c00b4580d10524881d0382c8911040d24003034580080c080707070707103050841ca80025140c00400400e0742d80c0c1800100005109011090f440755140c10b15500303001d000e0142104c08904020300412852a4031049914050f030080100d00002840607080020b4106180116041261207001ca0601c080e001d009002c1c040000d18060300300c501d0440314883c12500c009481c0d0082c603081d40b13a81d6446007541d407020380d00c480580700780c410058126900c40b0b980105200c0500418403945001d0b0b4400008030b081d43c20540200d544282e0060000b50441e80d8036501c10f4001c00c11003c06658a9501b0f01011000407051002803004a01903400801c06505000070445003595807041c80d4a2040c2c1044010700040f00d10703040e40510008068086010307041444144c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 963109640 1250 963108390 963108431
    0x1020a02191a030f07080f060d0804080703031101060b2d1207030506010f0203090604030b0c0c070605040602121804091106031017031213060f050c071b0b0d 69
    0x260b91070034090189140c10010300050741c8941c2c40002100416254001c080e108518240c07841010040c441d400074420342403004a0884c460b1044581500e05513840301030314149070310364100b2000903084040040c0703424403d00900e80604147c0945038600803854101103044a030744d0007051880e1609035108084025210251b900c2201c0b1010111242e00c2c0a41c001402014116180c40c0400c031403140d02c5c1100d500c0001611801c140160a848c5442e0640d102c480f0350303040042012052950410008400c054140005c00040c6140e131640707611b5900741040a4100491301820781141802403017450728400700352511040c0b461098400280c0704070581070450144580c103c155070018400402d1295051030450038000300c07042c8041d1040e032148245403403a181d1080442c2d4282e4102c0c94404070340c140a00b82c1005540c188030701030002e2100800c800d041d0035204d00301c50f561038040f4041049000d0120810412404c1d0641c452000030743c50424004445500412410254055640350151648005000c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 963110890 1250 963109640 963109649
    0x1e1c020a0b0c04091401080d050c0a050d080f0c030c091302390a0b010e091006060503010e060607020d110a0b0c0a032012070303060e0a0e01060b040501020a0219 71
    0xc41c0c605252424075880d50f9807040c450b0880c21490710211152100611107110b050700c440c003010f4030701c00b403110368101c6d4142c200404c0642075000b080ca00d080042c43c00c106502040b000ca4407000c5035852310070851002e804004001e003a902604100704003000c0501c40456100300d0040b071398051000c0c40034206030003d0050002c1c0c0740002c1010720280d07040d05044d0800c1d60034582561490001000c454655544582c03100c0f80c004c01c000c10b80401481004142140c032a401400002250300e410490000c142c19100143e0010700030510000040c04115100e0740050380c0701d282500c20603e480001c0d404a03051600d80200501003003000284001540d584c81ea43c200284013099440751a94089000d868480340c000d1811808113001b140110134020031000030402e150050b07005843e100209608021066000c80811030030142d49402c0800d071800c16820f40c0d07024001e80480040c1c04e002e242005402c507502600408000c4000b0f000421141ea40020700302c259590580e000781c14039891600c01d003030700c00c41e0341c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 963112140 1250 963110890 963110903
    0x15090f0f0b0307050c0a0627020108010302090c2208060c0403121413180c0306030f060902030c09010e04030e12030f0c01020c0a2015030a0902130c050405031e1c020a 73
    0x402c43c0c03d107e02e0307070800b400c0000800e07220310b900e1480d825910701e4040f190318002e0118540034010005440e0002007150300c1101522030038a08000490302c00c00240548003510580245a441445480c504000e410f0380103009007241440e0904603221018006e403000d6081c002c0142c1e80c0c1e640800018000240c901100940984c810038a80701c2e21b00d0801c21464000b0128490301d0308000b44041c62184c02881c0440f0381190103000c41d11201d07107544c0054510040242d03014403900380452203507141c020a0600074110004028001c0c01d040c94001c1c0b980c0383c941d410703d11410304944400000e034000303c11105100f6080d102599140c205011080c0a80288044b542c0e082c002d03034200c4804c0c0603000856110301c5121031100702c02c001c20141001815405450906c2c0c94440a000051422156a0100010500081510890102d420850020f5400307400103280055000705e0200310030b0404000d03480641e40c1d42e4001d042c2610350070784141d540b010b5a51800c0101c01050340300810f858003d00002c04003640166 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 963113390 1250 963112140 963112153
    0x2070302060c011e090c06080406091703070f0c02060a0309170d060e330103140106031b050c062d0a02030403120209030c090c0405040615090f0f0b0307050c 69
    0x1c5443c0c000c06101c144200c101c3c5107034100d02c00c0d0720b02601c00c036180381d68441a5070014509011044070741d000c00900440c0d405550f808401d020031041e00c0300c20801501d0a80341303030756840c0609004000c0408007034000244803031303903403001c0050356080e0a454000076985000a14100c5034200700000b48695500040e0103075000403410001c2c171698003d0000d40e0200703005103410762204010782c000a03c402d031603016800e0360740849840d10f001074040c41061810515011564040412600192090030390009000c0b0f9604c521030031460700c2107000c207100361340303a41841400c01707003101c2d2882e07101d05000389030101070741600802421250701c15441d17854400040c5504882841c100011030000d510680e03064011550f04034041803e0012030080314101503018016180d180400c1003405101c810140c40c9000c9114140004192900c079481160020400558041d0210306441400b40904010307800070f8080e180c0401040c41007600e10000e080480e101499480e0750307540c42410487da60b010f00d0300d2401c0d0600405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 963114640 1250 963113390 963113407
    0x319140a06140a05061f080601030b040e0c1302090d080a0318060905071205030d051005060705030301094718040201081005130e0304081603121b0204020a0207030206 73
    0x2c91841d40318000b003240c10051a00c0380020071003201c2c0110f5400384040c004003c940c5009200d4028140c0142d410704002c6408290720340001c0640d001c6e02c000d80760702e038400745144449190a61102103420004141145842100804100d15542140c0b000d400c2d9000022220407141c0b01c1e40c491810b4031009130402100440c3c1d40b400e030001c1e1419800075a01c3c0d10608501082e00e02c1da4800000c1030030390000082d4a03218400403080042c060042c1000c50454550b04002101d0701c0b00c40003402c1881c880c4003d960b0740c5d814072114204031410b003018101403001c502c0202d20314503054110240340b208080c4903484071000e0221008880740c41e1610300303900441c511004032440051078036030300c3c00f031032003601e915045540741ca5410045d1299413007895401200154042a2152142e00080769041aa401d8a1400b82c0703400089150a1104ca01c02c1484642d809040003071220130003002242c20a24503059410342910b18120219410000019208950001d05d218842e8000c110b5080216405009152100c40f50b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 963115890 1250 963114640 963114671
    0x30c020a09060314150609041103100204091409010209060403152007020103050604050f0c0a230702031b0604171005010618050f03210d0203150f0319140a06 69
    0x80d800d401302c41d20400c100155082c10940c01d03244110806411900c1507520398030b4018444444c440001e40501500911081c10415400200050098498040f811402405151010b000010507000c00e03a4070501c0300e540640d941c0d0f0102c1e400c807038010304c082000800d404100c50007089101c01608000141e414240e454104100152031a14001d0300c04100b5560707a07506100554000700c602c100e81090700b4001605482488000d4024184289000041852100700d007001e000d402d541c0c1c82c00e8410000c200081145010800d00e1410300030170400c0c14448680308040741c9036000d14060740c0d000040d44180d60b14891001c100341004000225024026965542006803061030303d10524507003c2c12400021850782000c0e8118010400080c2c000c2032140d00707403d07080041805c2c0340c00d813a044403030410010130804d80030b0010754003030fa110f07122460118500c0700c1040300144615400034040c4d00320004202d011135400c140040002d400441011505007125185410001c0307059005040a2a111201540200c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 963117140 1250 963115890 963115913
    0x601080d0e151c0c051c0c02100612050715020709230f041707020f0906040605030a05070503010609061211010201020f0d0e010b312703090902040b0403030c020a090603 74
    0x7801020132150707400710012500c40c8192000103038074000c0c2180342e60550881e03600c00101c4104520554a5064012092074162401548a44011245c2e6001c4034244542444260300400c100030311040c29024080000c0c1d1281000d11403566100c0ea900d00c8920f500c3c8105418040c01c1c400507441204526004014000550702920140d41107015044250317400d000442c1162180c03a0001d0500802c04041801c1003c0d420004089580103500c0b6400020716480401c140c10040d44500d01500446041c0420701d42140da841d402100300b541819001c110158005040c41c4074280c201108500225120300140d001e03205066105480740030003d5150a691a03a5201860314401c0c1d00c0280304025000c02000b010940d01d5034910b000c6812103507090120f034168007400e14107401e401004607003000d10080300d04648040451a1240039018051030041551140100740500500441141800e084c400014654016400000c05101500413400c055641c0c5d4030728a001401c80d41004c0c0a1a83c480c40d00d240340e0034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 963118390 1250 963117140 963117187
    0x1503140114060a0b12040804030501020408062409010b090301112a010510060c0510020706050405060f070e06131a0c0d0c03050f07080702032a01020601080d0e15 71
    0x840d500120b0150301c1c0c200300000444502d03103015401c00b224000b1030900c4010242044480e00000c000000c000741d000c1c00604003d04050300900b00d01d180139440d07412100c000c3e04500c00080c2c41c644c0444c2c200c4e41d03501409411341b902c41c80d880cac0c0c5400d060004240140840109216138140c042240c482c1100d041110112000045032450708400e90340000ca030a968007928074814900f0050782c1480b115100746213107142540507004a8241a50040b0004220380c0510026120552180304100c18400b04105041d040f540d0341c06410300c14904144010100640100428400c0000141b103505c1141ca030b50b4000f0142c500500e290010024a581051035580080d0400e00507000d007010301c1e081c0c40c7c051203400b1403c0d50152a12458074041d0039044080782d000c004110307034101e42440141c000d070328100b1041c0040b070481d001c80c96a01703410490b560154182d101c0c0c640e045501c518014885201c0100300000b25140b2070a00c0021940d040001540440c1e0805001081d040e01144c8070400720b51040c040300c1c5c41c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 963119640 1250 963118390 963118421
    0x503070801020c0c0d05120d0b091302010f08070201090203070806010501032007060914100501080c0a060509190509250527030c04020f07020f120a0615031401 70
    0x8595a1044600342e000d0302d035030840c3c03503041030541c41d045040c007031208a9602d2040054501100345440400e020b5080b54104101d142d07034854850610b03042540c03080c0e42025000c0e036126200a01940020009100015400304001180011035075150003500030200341e950040960341c985465000e1203940724003d00c10faa001a0405202c154031407407208030818401d40080744540740403e01c1e1241005410304003800c660340c1d007203203070b842401d0607041c0802d40a48980e814042681d52601c100185485410000d01d88548000e91080242540010031256403020a4440d5010b00100d20100100429698000e0707400c9058403080042c07204004010115a0300c80060740425001d040400f19454012440f406a080c03c200d2001280115100310a554103980201255409007000c0c001c10183e0700078401c0d07a038490001003480011031030101d284a0741c01302c0544131440f00d0020a105141e07240f44061000e800c0640d207010880e400d040480001001d190000040190070041d50070450080811407007180b0701d0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 963120890 1250 963119640 963119653
    0xa03050d0b060412112202190f0c170c07120303050a0501030206120a06081b040b04090c2303120a180609090b120d1701060305061003020c100f060503 66
    0x42d01e07010041e20141c6542190f05500c0c2913940d5035040301d408003800801e0380210b4502c0d40c2c03a00300140001003003101c404602d0141e12094203400f452030304004811400103000a03080040c04060744000d5602a082e0056882d04590410400038045031050100100d15801040702c0880e85c2200840b5240300a403182d0f60401003551281086c4040b80d100b0300000b58044800c22112900040891105401c245113500010f121a80e80d900503103042250f1000400300b440d21080081c66141910604644030380a550600005031140d403030038100a5103015a2001c144e000c02492071004003405800300301ea40140841d14400303040c20030900141c1064801c007002520600c840300441c0b040c2c030004002c40d051611400e880c14141240c0c640070300010380035660888140c6d146180702000c10445504071110945503aa034200c07280d00314030714542058000c201070600304014404143c0b101da0134030400c070f5280d01e0016140c1035180d00310750a00346014880c2800300d007080140441c0c40910350200c0100c4804030101e0740d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 963122140 1250 963120890 963120911
    0x20307090f0f12172a0d0305090c0d03021005070915030b0d03050a1403010b21010b070b2214010c020f19020f030a1b0506250809030a03050d 62
    0x162000749010f043c0c180c5240e410349000180480558003640321409040909000c01d141440203642c0c580c5200000e0300c00301600c0c1201282c3e0a000e200402116481c05000d41d242011020b90b8400f070044a050165018250280916209000425943c00305400c144001d06000000400440f814054078600b2a01b20004050b440d009202c0c035054108d002c2c04002e140032030b84d181611190401d01c101c4c400c2c03120300c880c400d0f01032201e03030010741c06003040c458080d8554903103401c1d2002c0802581039012341034003a20010301106000b201070f184161f038481e216841a55410303504248200380540d44003a40f07850402c9071800c20000015046428032654000c00c864401c4900c12a40c41d041d0302900b07035154101c3e00c000d2807608050440c2040c00e90001c2c00c0c0c03889000303a00c0003080c40c00305568070955000039008220070002c2030207051032008140450302c00e401d001da00e8220141d4540300b030b400e6209a00d440c000d4a0f00b0070001e00300345e0750b80c13460017810756100011500f0042e180d070f1702091250b49410307d086075184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 963123390 1250 963122140 963122159
    0x1b0317090a29040213150b1b07180905010b040204080d0e030d120b061b0708060c031e0a060b1803010f051b0313230c0909031602060409020307090f 65
    0x1001c0c070b40389081d8110b994841c0e40900c080c030220413075848411611030824032038801c0000c000c07100600d246040c0301d03900e01e00b00403031540903a00f84a040042d5080343c101002001c1595111030101c041e200f10001d80799126203001030040c04452130458029001003030000300d0f40c1000c20410400f101c19141d0411000000041540302c0200400001c0411101001c08403030003255070190305c18110260146150800700a0009000b0036000085e250542c41080180440c0906110b000d0700010000f00040c2035007060600e0158510100d40d0146004000d04006100b81c3c01e2a0020130040000760780041c3e90740e081c8a800d0000c205980d181034001d608054905007080454441c1c00e108950604107524110506403114080c3d60020342501000061070350008080b0b04200c00c00489600b42c41ba1010240c041d0030601360809020002c190b02c1074165804000d100d00e004030403500075809030014807035008036038030009901e402141c0042400d1840802082084d40c0c202070f40e2400e441648107141c4e0802d65035421003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 963124640 1250 963123390 963123443
    0x60906271321021009030c0219210f0803131725080a0c260304060c02060708040201030e0a0f080406110f0c090a09051b0111030a1b0317090a 62
    0xb8001a03000c2009501041680e074458986241b0a05d00f40d640344100750001042c2c0c004e00034101a6000510000304079081000b00c40d135501b034241c8040ca0441d030b4082d8844141c480302c0302201402d01c020010000b0609591184403808441d4400a074900e810b03405041a40340e9000b004402e0000c40c4800704004842c050700003001e0180d5400801c60f46041600201200d101e41c01b00d1084808280e031040c598407281e00800e20820b8031050088041c2c8a183c5410000d081c0c8102644c2c50b004e540011060103000e40e403090003980d1090302070a0101c3c8804c0748444462a00111040140c800c0300c4080c001001c20100360014401c54800d0390340c04048581100740f02d9243c0a0380140e02c6170540c03155400c141c480c207258000c16400140b00b8000170700f20070941c82d118142404090711103920060200c0402d519030300030800044024240004608110442e81b024204d0001555508801101f00101c40101441903d142c104112503c0d0101074504140762031654075182c20740d04496100d03869001c0041c180c05107184 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 963125890 1250 963124640 963124703
    0x10f0b040b090a0f0b1c05010501140603040224130e01060806010207090e0a08040602030c01050c16080304051212011a030f1602071a13080102030609062713 69
    0xb250703640742d60310344500030b1612598550700c0756215410301c0d41e60303603521415030380c24042d044494010390041d160850031144145c108020403032050814051030b80b40c09060300d502943c141c5da01070035641c8130114a4451380d2400310480c6071000c001540d0440090142d150320444241400d2030b4440c0c1d8071080c0c140c0d100038007158841d00507840700030b00701b04920050300402110311000c802e035449144a40c4408545078810b40122002d644000b5a4101e01e800901c07400307070711074841104a403c0002c1100c402d403160080c1240038060754400710100782444000e200400540100c94800d690301c0d4902181111042c409120721200f020300b00b0011443c101c56102140e03c00c12228042060941d00c2c140403c42c04010f081110086200d804408503100038954400d10030210181d600325159141581c1d09a41e110160308510301503401841442442e891b602070007038024500701c55032040950190030324a0401d40c03601340400c2070700000081c0300800071200d11680c4014006c0c10540040038200355590313035070345c2202030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 963127140 1250 963125890 963125899
    0xf0905090a0b18060109050708090c0123040f03060b0901080313170f0106030308060f01020a0f0b0601050c07090b09091501170f0f06010626060904080702030d02010f0b040b 76
    0x1040015100e00580b6806903000f40001e00084041e041e80c0e1070402d0980200c000640d03680140303c074581d0006c122030b510003c4140186040ba01701c0000800030901c8040101c01d0b034201e031503032a0300100b4000035034000c1c00010506c4a003865407404d00f00302624170480c03440d00903003030100003148114002c811244005072070b240c412103180c98440c086601e210440305d281070074000c041c2400a104405e001e0000150700a0740c3d0407803581070031810000100000c1094034151340c04000303220001003072580c50144003034001002c074030300ea034400005980d5071142d041682e64a000300314000c00e120b00140d000c040480010340e98081c80da6070b2003900e030f07036a96084100c04290000101c0100501e4001207003040ea4071031980e050312010712140030300701e01d8a102c03802e9100564104a00502645500074840d5080c02c540030740c0e60721250007100700c4e404a140040d0603a4040c0c0c40c07600c00101446224003c4030003040c0c0c0501110b2012581e000001d00030980e09000c1d102582c10314180091900e024007900a04000041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 963128390 1250 963127140 963127153
    0x3121b010203041a0c3108010515041104050a170703120206090706080c1606180506160903080406030f110c03070308060306091b0d02030d081602120729100f090509 72
    0x21610703800d06d02060b0005410442881003c00d12050a005d2540160020380c1d40103032458900d010401a00c58049032800c402c0c10a200401040d500c15040004540c21440c5c50850314208102d6203050001540003d0118441484008881030b400684c1038411044802950401a200c030b41c11160f1754026251542801c00500400d40c118032680003107100355116070f0001441000c8100040c0d0101c3c0f010340156010381202c41040b0441e40014000e032110320162900381034460840c0d6651220780603031702943d02055520800c00e0320200c06688541d07101a20301e001142c484401101140d0759074007140c021070015400c0c10224a0505001a0702c500451441015016004230503607a05000004280c00c660700600c0100303100e02503201404a050b0f040842d0352000300301d1070700400714000e0f14036241c030560071580014000c0c0c801d050a0b800f40d0f80310710380c4031185100010070108200c208510b4491306000c1c04201105004004001e80704003c115544c0c010680d103002ea8518212040360400c030b0302004640c0100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 963129496 1106 963128390 963128437
    0x90e010b09180f01033519020c0901052b08040302012d11150906150a03110f061209031c05040203121b010203041a0c 52
    0xb0101d640039420480b800100b0f29505110142c4002000d40c11203907604004190304480d0001c188600c01c040c2e02128001600350322952807206013050b83c10728404d1880c00401d030b402030346800a1030034070160300c2c4c034007404400c2821010024541813403aa040c0080303101c040c01032201d01c0c014412192903a00310320015085807003407100300110214801c222440c05041c180c0074101c0c44410b10b404c0607181000041c152401c000816000840c00d8454108260003800140d42442070a40c0c10316400f030150054180240c0352905d00001c0e104a8070b401d1036038114100300c0c10210001002038129464041c6039100070180203c141d50f440b006820010302c48441d0040c00b45181301d400b6015a0410240c141580001e0b41c5414400c584410000041500031609414100c2c0d1002c03d00c2000080d9030328502841d204809081102010451414100100f400e521552040d17038040c1900214141c00514207 = true := by decide +kernel

theorem cover : BRFrame.Cov 962949640 963129496 := by
  have h0 := BRFrame.cov_init 962949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962949640 ≤ n) (h2 : n < 963129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
