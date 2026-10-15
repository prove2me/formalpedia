-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:54.543035+00:00
-- url     : https://prove2.me/submissions/2bfd0d5a-9073-418b-a0ae-aa3d9f731f2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 720503597 ≤ n < 720683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720504847 1250 720503597 720503611
    0xc031b130e16080601052b02010806040e03161211060105040c0e060c06060a09110f0306010201060302090915010605040506070f060b03251d340513050f0f09 69
    0x1e000820940d00400441c0306580210f451580301500400140c10000702c0002451260b201480c100e41120019070011185140043c1c1000b440d80007094090307039140c0c000750034019640300300c03580c0307020400c01d0a07014555250300340c0d1580340c500c0078500e50a01802c07074000c0c1c61940d407000c1d04441c0e0070131082000809a4060030002c00540d11105c040e1510742000412440c10300e8402000359182003802c000072801e1582182444a08203090700c942c582c403400075030300e00c0c2d054200101e4885d60384400403401008203900c080d606c040c18400340400540c01142c82007003405140b1182c04540c0c0c0740c8505079460320a5204094000e40b04000d0400030440321080c1c5481544102004a502000000040d242c418010749907110001c8003500700c0c6110312818548001490520140d5842c015000c034500c6104500400300040c0c803024402c2040c00020700c0c004022a403a1090b56030a00341d101d541d000f007403504529a184a0701d50746c080e01086030700d071001900d0460b110040c66010521045000d2144800f4040c18030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 720506097 1250 720504847 720504853
    0x31e050702041103061513050607060f09080d050f010302010c030f0c0c1502070911041e08010218011106090d052203061b0804030503040f1505090c031b130e 69
    0x8a401603480d0f005044044000349651510b905040041095200103600c0010342d100c002c00c000280f007245034034000200e800480c0d98039100c103410305200700070703055014202e00c1c3e03545801c1b5480308100b40103025040001280800700482c1c0e89100c0c3c5500512400e01010707000c41c10010000380024070800103101c4192180c500680c00341500c0d61200c004170303043c1c0c205842c460341c0720105c440305075410041100140009034041c800059154994011449180691841c80d02503210500640380c0c0038011000820042000710360341c642150189054042445040340058840190041c2e00071001a002e40250a00000350003d00d030342800680300c5503c100a5203580f440600343c030b400c90b4070171034841000070350084c1d202199140301581160440e0702c1c0a40340348140081c190510001c0f03640325007500d0b8020303489106203000c40890304042080310104891502d8032414201004603e40d00424007400745c41044d012a002d4046604c0292290681d41c011941c0181032102c8010301c0c481d035908502103620661040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 720507347 1250 720506097 720506107
    0x3041110020109052b03140708100b0408010504060b0d02030c0609040f0501080a0c0608010803030103021302042c10030f23030a0309050607030516030504110a080f0c0904031e05 78
    0x580c42c2001740c1c010b10280d20000040b801e400e03d441c034a446105452144c6810000d5440003a810310483d000501503804206444d800110202903001c0e951000d81050604039841d2a507900701c99018140465049800500f4004401c1e100c0c18070300740c80011164000d001d005180d100606000700343e00800c48440d417140c6c460244140408079441524003a00d1300750090581c0907207600b0b1003080004135074010004c121454004002241c40807081d070341580ea049807180c110405007000000640243d8001c0710060039211058030f000b22151205095411912079036002ea0b5580c01d4a00c00001c02a1002511f02d40e1881d18800004c0c1d943e480103001d1000460000620704602c01c110fa2458001030403a03030110b99210809400d01004004180d070120581ca02440305203420004410303207101d01c1c200402070645a00210b02000852000e60224103006401036640541d604412a600c0c10450200a00c50150500c000362908103002428401e90b0142c50f010a001000280000314881e0726020404004007484 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 720508597 1250 720507347 720507353
    0x20904020c01051b0703080f1317070c1a0a0c08190210060e010f0504053c0a06060c201e040b1008150d06020f03071403041110020109 59
    0xc080c28501140400000e458504425540e0a0508502ca41d080b0103078203200000000303030310803c180e50100042803960030f039440fa95910303802c2808214000700000003c00c5000700c900d07014805403d199015800b014840ca9840d076020310078414108034085240020000d0f01d99082c003030300c515911144034000b01882c1c07025000072201c080f600c84181e00010b805c2140e08050940d5240070b0b050203070001080c0d550707140d40340401c3e001e0b070421244106401151181d000590300b210b00c0b106a00107103541100400740025003020f080343c00201401c0010040b0b01305000c28400c491600c10350b0241d0700541c540c5040c0c2e00c0191114005200c50781c1c0351000402ea0081c1e421487d841d84900d4100a03031141c000b0ba00030074080002c00c000e4400d4259101d02a44148041c886220350041a040d08500c600202c040d9100345507004c82d20002003040c0c00381131240001041e04c01610765000940c440c0c0d01c02d940703160003500400f4440302c40d0f1006480180282a81030000f84c02880c2143c5402e111442d203000014642400e40d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 720509847 1250 720508597 720508601
    0x30d0305040b010b0306030318040e06100f0e13020f0a0f030812090c010804060f140117010e0304060c030537120c08011203050405031c0e060c0a0b0406020904 70
    0x10044000a600ca005200c2003001014940d405005120b210074150700c0d12202003550380c05610041d4028810405030419075440fa0791120300b100c0844010b80f4503030701e000c2030203c64000d06449400555800500000703004e2460b0040d40e40187e842e20305d12551241103800300a01458070b50401980144807090000e00e000c1d02c101c1c002c000f5889800c1c00c13903c1d081e00d422969068000182454959080351a210485aa0005480b13a010781d01c00000508560000740340380090440350502250560400000320381c03a2041000b20341c0080640b402848843c42c1503070019280e005601c101ea01254181e02840c000a020784040e024041d01140ca41c0502e840e01035200c181d6100c841d82c0c1d000018130381d10300e240d071450b8011085001c0c810704800070310001a1041c80101000d405210b40c50b00c40c0344040d041400c06104204450041c40001e040b00d54441c2c00b802d120700c2e1041c04000c0c1c40e01003459800c0d0100c550800000343c3d13a41c20035810250018401030b844185604100800495846500b0040101560350314 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 720511097 1250 720509847 720509863
    0x2403090705010207050411120c13081c140f0f1608120705040b2502190602010b03060105010c0b070c0215071e0804171525030519150503 60
    0x192009000c0c4074075220001e13080c8201e640050340150704100b2416121a240421104031154001d154005a5185c0d08081542e000e601d200840d070301c2d01100002003500d00000c2594600300c0c0b030400c1d0300001c0c5083e06e046c0d0f0002030864258420a200b4403031007000421520140c421410071b5145540b5180c06070045158000d10700404070761504011a0388228484a10070140e0b008003903060030343c82c20b403c2c1490100c49010307051140300c004600c0e10389500200403440119064541c080c0c9007407000c0ca90301d40b110200401038050310b001980307006a034401070b14000078024101e4506850b82d105480d61501c6a800c4100d00a00314001d10040002c20001a00e40e4140b8100d0031910034021511200686044000708400e4890600b903e2144000c00c4003044204003110100e4441c0c8108040c0580d212001034107001400c00c08442d40c3c1d070003500300200c0e11030b110340e01c40c22045648002078494444503400d9080f600203948559807105100011040c0380c08a902c00044070300808503050499030fa0303400003171414010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 720512347 1250 720511097 720511111
    0x403090e13150b090118150e04021003020909270a05240402100c02150c150c0a0f0f0e040908040501090b070506060d060e150402010206090304080c2403 67
    0x603039120141882840b107100c00c1c0e80041c0309014080780a81c03030001031140350180038a103500c3c101031503580b550b0b5940b58890503980d44140c80844000b540d9000c0c0600724103088900f64001c1041c100c1c0c2803134451117442114400000108252003d885074207140700310245060140a048104404425511408214880300148614003e00d9080760030f0101c1020146200c100a503000b00540034080140d031109581452480a17192801141c40e4900002c1e28880c0c6603404c184403e071000454036401d46020401580305400c0c01d0300c0a080340ca40604d8502c85124005102c4000744014004c600b41b14070510480030181020720b8035035001a22103002504a95200382c08a0b104ea0300064100302c1542c210307800400811091100c2810801e41e40c030344e1921100004e0119105501d104440c0d0f04002d8103900034541030008000302e905488010a0546000c102030701c040c2c2c00343c031500002410044001003100c0c00d13550444050b1245416031000e001a07543e984210f000c040c1e035414a9907829500c00406184a4030b8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 720513597 1250 720512347 720512371
    0xa08030313060b01020d020a062406020705030105280504030909140105030d0f050712120c050309060f0114040207020303091903110301090818040b030d0e150711090403090e 76
    0x1a60b442c00d0310880b400090698155000b202c00610b00d25008900030305010341010021a242c01002c0d2401904070100e07020400c1d9201d0443c0106010358000365500940d00103900820190b2925150032031610b600150140c11600c541540010842d05500035071741261090408002c035513107402c00402174070035144a003082900d6400040000b444c0070085240080360301d04103071000342d6448100500d140b08004014001d41c903615680107002d48140c5800b4410f0002c2c040402c030442c4c40940090403a03100361501c40e03032072040c040402c3c804202c1d140003504840c0c003042e0380c03d8130003000030510000c3d4000b006d050b41d041c0030900a190082d210095402c1c0c00400e500402c0f1006030451800c248204211030050340281e251550503030019100a003200e810b40c502081c0b500341640d2490000340a00181004141c1502a5042c1c070902a42c000002c680e101c81d0484101d0103440c6607001c809013030b000d020b001130107903071308000da040e810305251400680040c040e1400c6086903441e40181d0014103170954014950315 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 720514847 1250 720513597 720513631
    0x150f060711100e0a050d0807021c02030a0c08011b1e0909051608090118060e100905030406030c0e0904021005120705030a0b040b01080105010f0327030311070b07030207020a080303 79
    0x1c500821302d10050603040320000016802607d60342e00c40d015140000703010300e4251110704259400c1e40010614164000d04607803283c41e0600e403c1c007604045115020350380d801d00100c401621028010740c206440b03035503203000d84185021501225030103840d01860502c14604030104e2242118003d2910800d164181d81c80d02c507082c020000c008220041c46000350382d01d04400100000080c10b09851603e40242000c01c901151106150401c8549810420b01c1e600e40f6001804008000c40640100d4155403007c1040101d801c10a03125030301d002a0050b405561840084c0040c503001484440c8007055182c41824040740400d50842c101007540c1910102c1c001000b0410b05540a0180c0b0013948025181840078000075000a403c400c01800780c14107005007071003190b038813070311941c0014032040d408080c1107040e2144a4003040f429041500c02c0c0c000a04041d038685010600500300e440c0780d684030503580c03006e07940d40382c0c1100290401d10040341d204da044040017a9900302080694042c803039200803a10300c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 720516097 1250 720514847 720514849
    0xa15021305030726030f030109090305091020070302220b06070303020c070b18150c1501140a0f0b0304030315060201020904061703040b0903032a06150f060711100e 72
    0x1580500c0013004694801c200c07610a40c80021300b60b0741181c15940c00461980b003145410f48481c010342c1c5d5001d1700701066140017140b1030b80c04a400910080ca010b00d004090341d0020132140c94074000c0c00007a40103011a582c019001d00f0300c00c3d46c000a510110340025a0444610000364170354440d441c103400081d004200d4000c0c0c1c02c8184017a000030191042d88500d004412060200e0007a803402c010386c415101c110041c2c80c0032a00008452000c1f000c0000e441b01c0d59540f10b514012200203000300341c9500c115461662980c00c00128000c1a0b464000c071a0702c0365072504d00c1005c05540020301c00c0701055122031000c0c0381c100d540c45036031000e08140d80016032504070f07a20501c021101c0d82d50102c900c821014814850040c0007104a80540c1c28255030309645d03a581c00b0100c1c0c594840d2050444103000e010111848140e0340034a103d8050490806454558503010410340c424080f9004540e44469075a03224109854030400815100b40702e11941c444008549000039941c00c038008002011405010320300200f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 720517347 1250 720516097 720516149
    0x516110d150b061c0902010c0c122604120309180501230a050d020a08060a02070312091e15060923010810180b09030a030e0a150213050307 61
    0x1000000340c60361810034541113507204014074011190030000369201d2001095910840941d52840d80040903889060b40e03804090300d5030304201c10291034141d2840e030b00110203040784108400140700e002c031150405041003084620a4210f00046050082c004800150501601070341c0302c4100c0c0a8100003090342c03400d074205036815041035944840c4001070380503030015540c610384481690b8054039400c510240c070344041984011103170040e01c400e2055908001004030150024499240f1a640710131480d240c440301d902c1500d0344140300501c89044081c0840074001040402e80b403d03070294480b40f56550030301404004580d80c5402002000c0e0300c44a41c5080e415121000303503980400820541e00640c5050700843c1c44030540c1680c15000340d00c074451700341c59148040c45e190f001c90300320501103014108001e00a5032640a0020700c00880c0c00d140000c0e50a0602181401210740c010700748445040e40710683c003000750b01050380c0c1c80030804031042c04945034504000780e5014048082d103080001d1110000800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 720518597 1250 720517347 720517361
    0x5010b0a060507020a1707050607120e01050f04030807020414090615010207061202130b03010f0f0e01182f0310140d03030e030d020307050304120f0516110d15 70
    0x801c2c803208214000c01611070a000c14101d4590b1110600510404c05c2d100342001e0440e8012544100c2c003081c00c0c001d105a00622000103001a1502e035010500c040041d0368034081c21040310400e02c42400104045080c01d00107140540c4010000261034002ea05000428a805c0d5141c49041e4030040800c4800d0310a00d86488503078100740002c040142c50000008c1c8441e0b0000d40c03d1800c00c0c2c0101d0015207444c42d504c003100140c4980c90420761250303140e43ca070491030000d034490450019440c00d800500b086c02c0045050603982c0c0003a81001101a15240714090032604000e9030041480e040c0141c028100c0300000745021001c12282603482c105001618181c042039004040032800100b03641e10706070384aa15905201e545814045410b42c0f200c04c805080d80106101c10b00814000003c125803035600c400218421442030702004260f5903000c00880c0c40c0030751000e6441c0400d4040010044000d030014400358514440c0d201030720340305107c50101c0d05014019904032248032043c2d10241c0b4080c25401216 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 720519847 1250 720518597 720518609
    0x3070b0f09101a040b0d0f03050d2304062307020106050915030a0201140f1b1009151515020a152a0203120c13061701031b080a05010b0a 60
    0x4000f154209800c62403c544074403160b845940d40d4001414075442e0a03000400c050b82103400030400058605000d00140e000009120a41e0f180c1224072880d00301d502140400c0c06041a8046a543d9a695502d0000c1c06000858515178004e40780c0074a148a8204459112f44859800819aa441c1100b1f112a80f0030103400201e980b50910080c0c41d0640b4000f42000d8610380928210410b004c00f62802000d52003080e031450924403001859480c80555901e0f5500034400000803200c50b9032102e5401c0c1e0484561140c01408050b0b0640c15010000c40303500701e10280c10a40210b035001580e0742110700c50954840d02c4001c0543c115068410a00039038820605803102026400e2010341d000113a20302d8180d00090010b0009162007805001e101e00c2001600c05520380301054030010308081000e246540c00c400006601d001e0f180c900403400364488e00c1e10748170180d1851082600c903400e543d01d034620300d0002c0c48011004034141400240f0b58400b040529102030182c0000a030040310003003400b066211a130804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 720521097 1250 720519847 720519851
    0x20301080303070c1509031805120601230303130302010e090f1f031b051002030903030d020c0a080f0702040605040207120806040b0307090509010c020705010f080903070b0f0910 78
    0x108840034000c0200ca51040c03441c40c001130700140d1844c0000f07a4903111202042e0251070710301100b04048d004a81c031081e035801400c01c003000da0b87e00d808121501c004405048610381001c0c0040043d228007000c00040c80055008807000100301802103882e64208810040e00002d580c0001c0065581101440408000035101e034030351440c0001e607801e16080040c01038980769803c6207901542d040c0004070000515032009204006d0300307554481d56510b501ca4004e580c864030103401c801001900000c00c50b00c4860b00070f8065828100c80f101544000e400401040c42c460080e64580c1c00055640c1c001041108001d4a820340c9905c028018403044134090341109000e02e1040120002198041a41581c4900c2c9450b1402c090f07901c5401080c085c003480700011307400d481017800202c2c4004854119600c1040014001c005110b034220003240e4030740444c032a69022981d40454000f82070300c22140181c0c00100b007006c032071034010b00707a68000e14640300720b40f002038588661040c0007018401340400d5500d081c80c1d45003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 720522347 1250 720521097 720521099
    0x80f06010c05070308130b030c03090f030c1906060e0112120305130b042111160e0106050307051e04031202070608060f0406090e06100e07020d030f1b11070603020301 73
    0x911543c4098a02000c3d01001010900351000d02c039200c4a440502102030200f901e03410704c0c1d1400c840e43d81007940c0a01c903d004102ca8281840c50000c1a17803003c0c1d1150008000b002010740d41e81c02d80c800c0350b10701610b2040d00d502000c503020405034040c85c0203024040203007105403035a0610079001c0c04200e00d031208160400c2c084c04020b00054200c0300c192504148800c405803201d20340081c1a000040034118100600208156100d4104000c2c091040061041d0b41514182507180116210385011b08012110301d40014040075119601444d88404182010351529141a50b001480605807030260170118001406004021b2a001062241d070003a0000b4400c11b42880800fa240100003002940140c02041d41c0035907a80e40c030b82222005041070b207420048450070403009501c42c0130880b601c2c1811400700f00e0000c0c0c0c00c2c0304415074512690082d400f5040810030748030120058100c402445007070760340710036020101c044032802040402c0340303d8949407000190542451b04085081e4400800e0510600c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 720523597 1250 720522347 720522353
    0x7060912111003020903010903050307180308040303110a050703050604031242092403030e010509220504030e010521060102011e0b03060123041a060a080f06010c 71
    0x341404840300407148122842600c2d80c0c201c0003401744400760380d49036092004803814103400200a50150955a640d0f6606907c0503a00f104641c1c1c1c0b40c40300500b000c204000401c0824487e207100c4200f5103080c016100c2c0885141c81c4d86103803036a240c1043e5801c2c0c20110500080503040303031907030100c0402c4201c2440101c40f440d803e41d8915500c1a110700e9801c1d40402d071064400340000007221180c40d0446000f002c80e482d840e07144010a00d6000c1c4400c406903100f1018000c1c00c01c40345840c01c907607040e603c804140c0031810045034150464040c480d040500c107d201c941e40051602c004040041942d0001441e28081c20300070034103d00c2c40303087e60502c4000c05c44824040b012114203222907510504c501d4a540b11030f00100d0050010344180d050090201400b903100062a030403440b03034903e08404440c5107989542107241482c40700102c64418180030b50450341282880d4002d08500f040142da4486c006407101b010580799400a00404000740c0580704100322204901c2000e42c20010a103820400c83ea0031303503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 720524847 1250 720523597 720523613
    0x140708121302210124080f0606060418022a011d030a050f0c0609030408160e0f0a06170a0303051608190b030d0302191d010e0418030207060912 63
    0x482c058842c0702c81e990410f609a5800d4219000c15614142c60b0201c4d44181c8174902d401083ca8003c020b03041c0100303042d4100740c020010b2050300941004094616140c0752003450781c1589005601c403034070103400b404854501e07044607080c0b00032010381c0405d841c43c0d50700c4d8652040c2100c0020a40f5400300240d404c1c50700040030008103a07540074a407810000da0702c0082800c2100300e4090101400c032071b4482d1808100803400040050000c6881c403a048070803145400340401c1c600701c014024080360480d424001000110000071a64000300c4401000030030949482034001c8400b4850a08a103e0384448851340c00c16030f152240c02c2d0b12103030032041040d6070300c1c200134001c01044002e003a00044180703585042d4414103096110002a0030010112401c100031075401401940242c002d600449807240d075026180f80c0201d1080f81c040e660364103030914031500540156019844003903516040b42d6a9030000c0b150403072200c2c400040030300903002413000500e050710041000c0718030f4020b28820703410701c414000000d17101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 720526097 1250 720524847 720524869
    0x2604030e101b05010b030a05030403020a06031b0e0d050a060204080717030f03071106010315060b0a121e020c030315010c1115070501020703080106030609090213050403140708121302 80
    0xb100984220b56050501034054030508541d240d05000310449030781000340000080003103c0c803d0312109162961000c2c2501120081e820410b454858020070160207486030090170b080400c020700052b1441c100d500e40502e070601d10030003219544e82c0002d060120100412189005100503c01c5950740311098043c00d44030702420710065841d680c00b1002c03408050107130041454444010003260030560352414480505002000e0114005191440c0407d1506844040311081c9001303440740500d441a8040d440010900b40e02452200c0c0c1d03000200b1848690140010b0030394000201c0110388a0510300408090b0f4000f078403840d41481800d03508400001c107403401d4a030705e8020071240040d80150103001e40d001c038440c8800c020025480014000704050304041b107107041e64201d960401c14503448106031000c49030311010181d400080b4290000d444a0b8a811140d4003612a00e000c2a2044502c01d14610680010600702c42140703004c10318070403103c01c1d040c60580c0520038400207606005140c000c10005021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 720527347 1250 720526097 720526127
    0x15050319080c070506190f0801080d080405100f09051504021302162103050702062406091c120815060313150608060627072604030e10 59
    0xb00d040d81c0068000d03c0f0240080801030b08a654514400512560400440e48032a0204200340300c80e1a0482c03042c2d903502e0584085034020701c03001215141c2900d09210003030007180c1503c1810f41407a05044107000340403003540040300102d0252000d240060500100903071031006ea0910808000143e070705d18107511462030890700e0040e40d40004013070101c48d44c0c0b01030401400600c00c0112070200202c42d1165058440c105a604000b10b89440303000300e031101002d8031605002c6030716602d82c0c01100c05003d0214a6200c000f40305038a404201c40118503c03001d96850100310303070010641e80040c0328072221000340d0340c141442c0501142c42e0840c8100350820010b03070094058040480043c0b519030f031029808240c0d81d0400050400c02c0707207080443c4082c2055004507034480c002c6000bc210641131400c064103c0300c030200451400f0030550320070030389805802040e000c204000707403000c2107800c3d80e801c81e41c10410509001c40602407815060140528081d22410b5000309410410049a154040041449400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 720528597 1250 720527347 720527363
    0x90e030c0d050d0b04090809100206090c060c07030b010902121b0a080a091401020a110c060706230c090108090d0c03030b040603150b01141303032303070315050319 72
    0x4442c0d03410600130050300107102d420524020590051084500c0a0042101c04071014035510602d80c800700e0b160b100645000030140d001c100304000382e2801101130940c0c3c400382c00071186850398a46075240510001e030700ca080d0440d40080c0b2011013004818415600c003c0458080f00c1d600311005003101c007407256028a00800c4000303030208100711615000303001000d400528241500b011003200900030b50003400000301203846035112000030040441c7c2d40001c200c0040840d42082c00581f00e100203003114480d4001a8403600030b600260340d400020702d07401054020382c0b06480d00780042c0050402d260241c402c2804d5407201c100129810b601c0031002c807280b039142ca800710b0050709440204000d408036410050242d0050290940c0e10f00150744801039124007680c680c5034900d01c44e01e004005109100a159415001010a102103406602d4018501c080d41d9256100350402000100340c0e500f080d60381030002501c800c2c030342c1c81e010113070040140031740000c40240031100703510102c11201c082301e03000040845c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 720529847 1250 720528597 720528607
    0x1d0a03050d06080a1b06030603021309020a0b0a02060618061f02010b060f030609010b12070e180a14070906051210050405070507150501050109181d07090e030c0d05 72
    0xc03240d008080100f070201c044400c0c007180d501d010009004006101e44507100c403a04000741d501c2c070900403401100d030054003076440441a08851009444280000d0742c000a00900026050015400234007000b00b1541c09007909061010401c00305c850400048000c10006005010195440580e800c0c02c41c80b00000c04c003c0940f00c1401640580460300000e035200501183c0400d4461700c01c001507100d9942103c040103d40e03202e0040008601800e8203c502c410010b4000540c80d074096020b084540b44003c03e10202c04c0b9510035410807998040300c503040080d8680000701c640e40d800e0203040743c0100c035905045001a050041c000e090b40941b02c00e0380e004003941c1000c070b680c004407082c00e0005080046d10602072450301c20b901030001c1d8015507044800680302c54918040c000c16104181c140c550581d16a03028610301503600c0e020a8503000d420001729581d0584104518082400b4003102c4004000345c050649002240f07000c0340e081c090320309403a07041008209050791021810028001c014203200e0303165 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 720531097 1250 720529847 720529867
    0x5030714041e08010c0512100b1b0c0d120e0111010c080f0c0703050405060a030b0a08100b010507120c0c080d0804121803021201020904060e0702011d0a0305 69
    0x580406503101605180004011511000711070101c6440c002012140000c02da482031010300300c0300b03d09082400108284201083c1c544040300854010f01e101c2e145086540c1c4488199170a54449000001404901000d0704090b1406101040d46542c017102c150b140c2c5c04994840c036224044003402d141c00c00407412484541680140307228032194079102c00810001c18100401703040020b059440d0b81030704c580b035000581c05010780c8040f1980390ba0b0507513445040170b103401c050240b0b9030080041e9800b45030b2903c035480c0c034584a80c020b00c802070800c60024880d03007040f4058882214a4800d0060401004104003030220b2400b07104480e2b40003880c0f0740300742407520504080d03001d48025003000c082c0f0f0207100d41420346c89034440205805540580b40d030701c0f000a03040c2400c2c1c03050040790481c0071250295080810152406042903594a00710a0016241c840c4190006049030b031503801c08211500e5510621844a83c24803407101a000140000c100c4603c0b10410160f9805112034010100301c400a170514007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 720532347 1250 720531097 720531107
    0x4060902090f1c050303041a0108120a0e0103020d09060c180b04170a051507091203020c0906060d0f1e0e0a0618140307060c03020f1b0a0c0608010801060e0f07050307 73
    0x1030a90080300f170b02c1e00ca007000e00e010200d1100202c207070a40c0c140c01c1c00c00800c81d00f07804030f0aa40965021040c0610f03200400c0c10a86841801c03103101410f00d03a0034002017090b43c01f903001d02d2143c60700c0703400009480c24608501408646548022030700c0c80d900e00c0c1c010300403040c05100700e4003914801000f441ea51100500511700d03160311018000e00c54000c031140c81d14014400c002103030044d000ca0725118105a00d640c03d4010302c0e03800c104007034010b901009000f800c60030400450f50b0003100c040c2c035192902811081c0b130310680381402001082241c0c2d82c000c01080580d2000c00703140482040b5820302c8080c0c20362003225075551413900c0c003901c503654480e0040c4078400c44a50079040d955003d2411880c1d4000240e01944036040755000342c8040d401e111404203818424402c80703000258508806007000759030a00b14509101000c1010054410784c418070000c81c00400c0e94000600b003030741c2c07005002d40c10040b0807806e445481d4040302c1c014050f0001d000103140342e955545c1d40104a482d1658032030b079a504040324 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 720533597 1250 720532347 720532399
    0x1050f0f06040909050d08010b1309050711011514040c02070303120605030d0c060f0506100c1401060f17010e0624040903021b01080408030a0c1202030a020904060902090f 75
    0x43c01520b400c1e2000100b04000c00c005000000340e4903601d44e2aa80d550142400f4442c03101541e400303014003c801d21202c400c0d03601040c2c200c000391921654070780e42c803000c042c2160700c141c08518000003d00020854500d40d0101c080500301c0c2603d051040c0c407074404000e5038a04942c00020203201e80d26074001b80804007640302d1001400c0c0182140c4522210550103006c40e0707032140c0251201c1b400c1200d031504800071030042600402e8060001d02d1003401028040b140c0791644c24080316820180400c0381c00003d03090007854060011402c1d01e00c521468048443c810b4840455034082c1a41440001a5030032030105200f54054070b501e0288218846100c110b411825102d01944e501c585040c11100c10315500080c2d240b0030b9000d07280f850001501590064500200c03c81c0c005191070740c100009117260000782c100400d898031500313005c03420911210001007640c00403079280d901550301049400061a2900403400203040c0c2034411031801c17081c1d001155801e00500c00c1e690060b81610280012520481d20303039a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 720534847 1250 720533597 720533609
    0x60105130f03030311031e06030109151b1d091e0708041e0b04110301020702120d08011d06040c050d0f02040810020a0f1b020907030c02100501050f0f0604 68
    0x98125a156152076001d00014001940000d160903440075951082000706c9000750b00000c4450404a0f18800c0041c500c08010314017038040d500c40c0c590314009801c1e4186000030081461000c83c80001091080d0f1800c2e42940540c13040118600c411920180030510400c4121420b560050b0a542c0c3c2c0130304a00382c0700c55007005103184242142044165644580359600991182e015400a004851b44081800000e25805400303a080d94020900081c1c3d10310300c0b0141c01501a0002d41032001135000101c1c04520750442e0241e64004141007660329038071541140c003501304485040d0b080d044003c41c00c030b0030180082820340240c2ea2140388180f094082c009540c0c044803d41424002d030000c08280344003a4026201300d140d248164070307101060402c1c1e4002d441603810300b5610b0405510428004a9055641c0c01040d03540320b030310040d80f4015859078142b4522a900944001c00d034044050310003841d111807001c0c2614140c0c40c00c001800340e42da48410700c01c00e806088401d64001007140300061349a2186034007007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 720536097 1250 720534847 720534877
    0x90c0118140118171209060409181202030301180203040b0f041b0b0901110606060306151c091101021501050112140a060612020301140d0501023603070b0d05060105 72
    0x14200004a940c04e0809040d80076640c1d15001c0071003951140c041c1c3c0e100070303074070117000d200502205200350320110014941030001c41c41c0908549501d41385000380d5110b200142c10020050100b0050703507001d41541001d0344411451071405448108131b284019040007000b520241c0442c0a000001950102e5a503070307100e2013400680c0e40c42101200b0341c08800d0650224016105486251202096940c0f01b004050400c0c2d145079a4002045507400003180301008082c400d020102c85030301c11801c0d6880156140f80d001a0100c00303414503c440c2e001241c0d10b507045500c443d4421000300c03600140541112400e080c41d03c00f4412030710348130000d407213140c2030070007001001010405d0200158018500705c50568940d00c0b4011003480d40b902c16803000740505070141d14554165144c41c2031410007090218010000142012000078180c64000210315038501c11484010400fa04500e11f910403803000c2d10110020810145020005941e6024110032140c0ac0b580d01da0016a099000d074040302c00110b100494 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 720537347 1250 720536097 720536099
    0x30403120c02180702100e060f2212030605100207060e030a050a05030730051e030a0608060106030207050606130e0601030308090721021323090c0118140118 69
    0x1003c80000030481d82c14006104007802100c5d5241d040c80f075506919124000382250742d0300d80c81c05010403180078107001c01c090308144140d100c01c01d40203410880d10307102da1034104911940d940c1c001e0684109030442842104c16000d01c4006540000c3d003a800c9450604101102d242004006801d01c800d0100c050034a004030001e4408118001c030061540b2807184100261400240f81c42c081000e0600e2802c5203201000b0700c0e1900b0030350003540074040b65080d051707030200c494035145003100d4a5001503484400003521808180003901c0240f040a015010500d42141814025111a9564100609400d008107001e5180c080e10795001e800c50384000000d01e00312451941c0d00e14000340b100310b08655000243c084c4e00c2c3d001c104441034006046151203a01c640340451941e980800c81010b81c2e00f1520042180d0320035814024500159413500e1020480340c01c4000351410800c00d6042011b44a075035410004c0342841c4050340d0540101c2c440940e002d00550688849880e00141e40d4403405ca44102080c25850038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 720538597 1250 720537347 720537379
    0x1909030c02090a02090307030b090109081602040c0e0609090603010b1f090807030210031a03011a1f0903080a0c0f0602090f1906050c12160b18030403120c02 69
    0x1065600881c400c1d901d40b100c95070b4240c5001e0480c0100791603694190841c1e01e00300040b54114a019410030181e00c000a000252503603801020792041d506070070007a1079891114103515084c490711040040714180382c05240b1180c000220a440345e0b040440c41607408102144e00d9803000d6100a1000e00013514a40c1482914907100310a11111b0542c24002040703400040f41c400b0021403250210395001d070084059000c5000d0139409403003000061030b4190041d00040b961640c00740908048100b0b07410346000c520102809101300c4888640c40045400f02004030303061029400280002103d801044881c3c54403040300c0100d031100850800907045043d040050420300c0741c1076001b020900e4044a04800e06513180c3d06006504110b080300348421481113001f0000e4a00070802040c3c4042100281c4100800c0c0d203e038500144c01c04556401e05000c00400501004540110240c011200203100107101c46d142c44215035a11540c003004100811060407000c0141c0034007a09500b165000b400d810501c00800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720539847 1250 720538597 720538607
    0xc0c0f0a06090b220605060f0904110301061a0313080d2315090406020a110316060b0303030907051917010c030c110a0f0305090d0308071223190903 65
    0x40155510310143c1d010602c4446036440d6020345954985580c0111030b07264860300c005000060030340390801d0400003004425070351640c80e40e119034401c01001c1c4100544a0a1600f140c00c0d58004800404800080c500040703541000e0317a51041d940d041341066601035203401a09030040a00f030216207801e040000360101c0307149200e8169403426642200c4c2079911000c086c04100702e10f0007a01e03085450034011401050700b40d0000d0404913900c0c100303054a400c2204000746140d1065510544504048100b101044404d0158441e0082d0460055055091001c501921030200e84100c0307110340c4100601400300702d4140940c900804914003001c55518007550170038081c2c994011207500207171800044080150081c0b04100c0c000300840c004040d500c0f003075601c01400c2c518110040d0140402802580001d903612459640c80318440e41d50b4503000c2c1003042018081d07900001c1220031031404c2042d4100d0307038080319012a49501c501d24a246d11038541c244003084951803250318403075890501c0500d5080c180c02c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720541097 1250 720539847 720539861
    0xb0a02012a0e100f03090c0510020102030a0e060108061305120f130527060a080609030c061003030f1b1b03050601050d0206090d031101092907080c0c0f0a06 69
    0x64480700c0078201464104208451036000f0103001c80c0b80600902445442640034461240c0314036000078040d078a9900040465a20b501ca000050b1f4001003080010081d40c0540910b400e01ca034020503946d41820310f021380740c80009010089041e0480c0080c1c060103801c029040e1407100c10090255205001c26030304540781e2005048075065100341c80001607074104080c0e0081d001d6000d200d80300e40c10007000b040701c050348006008150b00036907022010501c2e8405009250040c04460000e56940d0415000f9a00f0148011b09900c402c1d44410130800200750401e042c1d40186a0702d2800b001d412a030046040c507400080d01001c2c1c03030013200555480028038945104005c2c0c0f802074044810684e40e132820003030144059100290851400c0c0151140c40c01c008480007103840c40f1b4108201911188072120f8210740d01d40f5015101c01224000503044254841483c400d6442a1711b20340900d45400c000140841c0c501800c4c611a142d000213011501605c00d000c012042c202e0602a14858001414110064114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720542347 1250 720541097 720541181
    0x5130605070e0907050711030303070309051b1e010c0f150e0f0c0d03020a0b040809041103040f02010807140c1e03040f0506072a09050c070c0b0a0201 66
    0x5040003041c04a03010700e149424815006040440d01e80c1d40e9403045804c4e401008084401582e05403401005a80c140003540c4030301c0450f40e002400c44200c0c10074501c3c14005c0d07142c040b407006040030102d036551100e4200c0c240f01c4000a1114070049290300040b941d40f041100081c010780c0d0009030311030402040c1c0556140120310000240704020700b0a48060704d840c4a13810111007988098581415404c006e2010b0f40c8580c024016201a10340644480e51181c0e403c96007242c0341600040c10304110714152181144603c1c1d0146190b0542c50700d40c0d21000c10301908100a81442441000101c89a10400000f44907881d080b110039280e038580c1d142580d44e40f05014a0513241d10850304410720385200081560119404d068050f510b05180009000c072aa009001c16540c0b01e44083c5c00a41c000c1031a000080c01504a94070704040343d15103403501046403c054080c51a0138420400c240c00300c2c0103102e0401c25076812150f8a550f1f000e0b1040d05a005042403900c5440da5507444100c086240c10070f03401c41c1d0503001c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720543597 1250 720542347 720542351
    0x1f121a120d120b061603200c090a090201050306130e0d0306150809031b070b0a110601140f04020c0c040504051506060307050f070c08120d0f06030201022e051306 71
    0x59080b00300340a07207a00d0001550000740034468980130300702d44018084040d000e4140b1555400982007006035100100c1480c0040d40c0c03050100e50040d090840d0600d030f2083c841e00c400c020b400c00ca0341c002402c80c80090328070f5224035012281c3c030800c141c0741e070301841c04804490f080302c19107804140040d005c2c00f110310070400c2c152858000c1400c424000c00c5c40510814540020b0340c502010b1104250b00c0302d11190640c11703103114480012074900300b46070080001405689802e1001ea04144905103821016004803416205241140030030f13407100701d80c004190701c0440c1d0140c0c0b100082c2c0743e002d14201c8900300f04d42d807050802007480140174000c03a88a21908002010100039940da400717000007840107039603010001e0b0042080010186031070014001080c801c0d44000c00c03c0b940c07044854500107104011040101c0d0002d000300c4c0391456841020f100e80300400c01440510703c3d54001030b4550040e0074011004c9401c41c150f8580c01c1154001800c00040f004004010f182014008500b60b4800c00d002160054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720544847 1250 720543597 720543617
    0x90f04020d0b1e1c0c050a09050406051f060309031206031208070e010e3d0306060306030210081003050703060203060906040917090123091f121a120d 66
    0x14001803080311018013603c40350016190b101691100c0718201c60690f130011403003101150599940540d2001045201d501007083e040604040d8101c1c0d101a090300ca01500700c514407044508550165000c40e00740d400d00144614a600b400d0b0380c06c000c032011a2600358684030000c003c000e07043c3c08440720741c6066a1142d819980e00d18040d40d0480b041c02040340881d20301c2030307884658039115a24800300342e0700f00c07180c55049600c00e5182801c3d0171284040e42d010010642c10815583e4948070700c0c0003c100b18a410300000785103030086540c504030340c001c6100700105071002804c03960390100c40100a5502208440c0c10640d23905041c8000d4009941803031141e144407000c100306180038010110700030342081500d1100400ca008030395855002000703590502002e4000c0c61024480c1c0307024042801c144561003540c40c1c031180c00700205005803401c1e03007920000c040e40c60b2a006500c000b000700101c0394104000340c107020243d00500c0c000c8917049615444031080d00550031696001c1400002c0028980300e1044903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720546097 1250 720544847 720544879
    0xc0322060224010e130f0302060405010b3f12040303020c0411030f0603010e0a110a06050a1202070201122409020315040f060503070608090706091a090f04020d0b 71
    0x10403440e8151160b484079000600400c2c410010040c1c0100d648900002901e40a43c2e0300d403001281074a00707501507000300081005004080c000d0f4101c54004455410501d4008540c01c02d110f0f5500e80c03002c103401180e04103641107130400840801d218103000101c0700b691101c03c00c10184c59216000860050140410070309007400e06008074252103807800e58007411643c6444580b019624020540b69056494513610030420005101a844046c0070700c5440210b2400d84007840220603803a0700090820908206e215100c5030300140d8100d03000447c0c280543e89400307074001259103024031491120b02a2074042c443c5038112420010060325025a4520b1080a6407000048201e0008840640100c244503101d8174042ca443d6103da102c0080450000841e42c0d201d10202c0d10381909600500003103075240c0140042000f0800201d40200385a01d4103007509070420761108111070912051401c443c1000c1030080e5143d8402241c4c00403500080d10440d16000464040782c09440d414110034061010b400c981080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720547347 1250 720546097 720546133
    0x1090614010f03022b0e060c0c060718050a300b060d0c0b03010303020307170c0c010804060f1118030601081509070306050a0c0f0809060403050c03220602 68
    0x600a0140c44000055550b142c040d006980007400241c03041c1401000307096005511101e0801d00034011900080e0010412041803030154058070b0786090304003e10580500d1200055107680c80500340c80e156625801d06051036411076107a03003140c0d9201c400c00c10081122018003002c0400f5100c107031050066180343c40b1889401c83c3c03003d1000750102403010006074140c2031000929102c203120b81e0b4070b8100705a485580c01641d40084e082103006130000141c010034441d0b40000d1140800718051040e2800750075504003a51103250340e0300c0c5818000700c140000c05000f00f5920015000e50650340500140d80b2440710b01c4845e81c00480d5180940c00301c880b0394a418200092854182c0f08014020400c044102920305d401c204020b110303000c00c0c4212000840091444e008290044440f908081040b1810300b4018001d41440c187d500d041028060070071181000001d04542c1154240c1409035940d11012800b5003544140401040400e4030903440c0c071f80c001c107a002000d04441d055801d85440f84081611042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720548597 1250 720547347 720547379
    0x10501080402101b050102040b070201030501210f020402091c050706170a02031315020d0b060901050d0e2518060803041707030f0305070b0601020c1804061103010b03010906 76
    0xd002901011200c0100d03010b41c040440c1071130304140160b5260002da481c0c1c0d007a41e00035044034070040c2e0041050720031960140900c03030240c82c0410060180100c0600544c40d2140302d00b4000d045441070b000c07401e040d51140d904480200310080c0c654030190b0701d00d9008514607070401c10210b4030780c03040641c0007841071305c66120061088903071215255684c84840c1110040d400103001007981c0c1d074002e40700380006402041c0c4684480703214034002d81c5480031803086404544944c4501409148200401c52090f0b07801003c40e040310001000c00104e0b1002044464500101604100000c101400450b04102c0c4104602c10031030303081402110360446558110005c1e1a01c9102d4071001d64024003050005880800d014200b240741c80c811260941c2d900c1d25441e9000b00e40d14810340100d0300c0041c920781401004115540d00c207500307000900c8081c481d1004600c0ba041c5120040b00394291101c0410204840e64010070781c016030040041c0d0300c0f5612102d606426610038031074407002900d0881c0005141c0c104031a400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720549847 1250 720548597 720548599
    0x21c050a030f020105160e1f122904090f0501112709010b0c010905120a1d03070614040e04111c12030509030903010f0606030b09131113020a0503040b010501080402 72
    0x8181086c0001e05550000e100788419034084505403503120041148c454a0040c60040e83d5244084640d0180c240d04071365142030041091041c0c9040901c1c4900c4541c00a07080791030945000403100d001d070820b10203010500100900c01e50134002e0704506140d090020b060032002c8075174002c95100c844204600c201d09800406504443c00000412041c844840503080801c0c1400002c603900000e0b988144c1440039820700c560b1403180200d800540d4591001d12610030b010100364508800a0000000341d4501c0544207001c200b141102e00009038106071410b541c0100000c4056110034105882e04001d0308000c101e2643c0a1040c5014080e0300540b41e0f43d110008540042c115448262504401c5003d042c0007000c204061004000ca1001e90b282440340c3c945440d4440c4002901360b003800001019503100301d41130380c4180303598010302074240500c0301c80d002144c1e40002180811380d8545c01080410015943d5405510310100d14a003c0d40d030064010b607c10303481448403480760303a280c1c8010341d010f6400b61406 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720551097 1250 720549847 720549871
    0x5040506070807020a15060311122509060b030a0e06040c03020108070e031912020d0e040b0a080d0801030501110304050c2e0c0c0f080a0b04021c050a030f020105 71
    0xc100c1042c01020b00607085091403040c0c0c0c50081c1d50340c03210f0b0710710f03a00140c03030181c0c090f034030300c001c00500158a443d0802880111a440714907070140c400c0503076484104640d180110b0802c8829680b250104a5103c000c152501c003c0c48029956200e0005507002103514820355810001051110340c40410543e204982c000c903c610f025045030011240c207000107040005000302201521280d90b020002c0300c01c00341c4060956500c4003007928041d4500c80081d0719000540d845401034202168100164004043e41900e001698110b44000103c60544692003100b0720b0180b0381c01070520661242290707050782e0080740240100c0016204030541807104039006095604203502840951400718169074442c910ba410b03003c03c141c0648001440d0302600c11903000440d81c981c0010041008049080c002032007580c840202491070000c902c1c1d1903e5003410010110464480082e04668541118041481550b81800c1104990340340c0256544500402600400c15103940f800f0035510500031503200d011000c241c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720552347 1250 720551097 720551101
    0xe0304060909020a031404120e03032502040912050d0e0318130e01060801022110031b090c050a021005040206180f0402071b1d070503070507050f06091005040506 71
    0xb14000030340100c0018403c154035400202c01a03c4040003145c0918026001540410301500c0083d00040680403106d029410602c002a4134009020502102585440070700c100d2884510010780248240e000051440c0358001081031701c99408400f8006900a11341d0411030302d440d00040c1a503c0c000d8000c0a82104040c1d18080c400e400c002d206640000c00d00100800c1034880b4200003400e40d880c94002d02c4080e1f40c08034a400d0100300000c283e220b020307060b004481280c202280f0130b05160b0a1070001601d0b05020024614901d48040c0c240b20003081c0d00d103010007441100007030041c0707507034040310014006201d102881c9031200341d18845e150045034001d121a1801809603c0044038000c4a4076503540006c001c0c000e844a0340740c40c00105042489219081d0698140c80c8a03c00517025a8201246214400c1c043c120a0240610304540155040c217000361265100c2d6801c0346c40d032044120050503802030424a10141e000050b4050140e400704060b10034800300704c1404d1084400c100c0300030b8060b80c0702c040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720553597 1250 720552347 720552359
    0x30206010b042105011d2503080412080408010608030a090b181012020d0501050a0b04030b13020a2103020c0f0a0902070206040506031305010c0302070506152808010e03040609 77
    0x2004400e80340301d94000b007581c042c186a04c0e2907410076158800c07541d40007c0c4100120207416641c18a44040c00034a0002d4a030943d103448010340200d0090008240c95021400203001900064800a100c1100244000b58803090000d41317a4001502603030101d4000800490403241e090166110001c002440b01220286071041000c01c190f4010800c0500441800d075480340308150000b80328a10481c1d801144ea54501814801040c03a203522a1324901024001440007a401c0e4002c150071900071090031840295500004000d0061a40907400b120b61007003100244846000002d10000d00076000d0307484801452060151250301d901643c0d9100c6424907007485140e51590250900ca40080c01003810300c0e854a020034000d5201380c940804c4429914003040030010240518643ca444914065003000d0080d40c5c1e143d500c58010704402c2210b05101d601a6054681c40ea0700580c030510317281c081030302d03000d01303182c0c410006d006010b03014065084c0940c001c9400b05c00011035040f12095501ea0200e685445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720554847 1250 720553597 720553649
    0x302010f0c0b1f1509080d03060e1506040b0c0f10050610120209030d020f0f0307080301141f05071109040218130c0f0503011a090604180519030206010b04 68
    0x1500d107002c40a000c240464442030000440c58a0113080d02c0d41e000c4107003048051840c100c11a41c40310100b41c149641031003000980f6070780e940c00c00d18805045400707040110014040e4091500012070800700805c0c1c5203201d03400002d0b140c2e0910b9401059031014190414550161039040310b010380c0120728103903400c00702c500c00e40e84000b9000081d0b100500349060040042d05145180708254010307480041034a103801c9090110440c09500d21005514003010350b0744120b840d0005220307145c840190204210b0b0a03441d2443c51421401c410003071203150942c0d06034050041c2e00280020383d1524031242c0c40c2131036400c00c282e0080c002e41e0005c260094500c5004c04030344031100c00804140b1400f0005503120002511601d084010b0240c984c10392030b4040c20030051608454844640e158045240c9003402c0040c0ca84102c07658020f4426180811002141c00d40f0405c42d11002c1001840c500c81e16031007400b01010034a5040d1707100d200b076003525482d0340d0b540b55030940340c000c9010760507608090344400c807020fa0032a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720556097 1250 720554847 720554881
    0x30e0603271b100c0c1418011206020a0203130306020c0d2a020d0b0109140a1b030c020313120c060c0308240315090c0d0c05040515190302010f0c0b 65
    0xb0300d0a8880c0d40380030f950310b00c1d4400030386e4080c0010b0290800c505009150410110008401000d44a104d42d0325103041da8003c0752000c20080d262950000b40b1700c0c9024400e10440d425041c40880c1c0d00c80140d520b00d810002076000d54462200350044070745034002d02e40305180b0312030300300800c415a4007174030103809811692040542c01281e020902c102d44100140e0006070680c020318001d0000901c048844000346004000108100d07402d03172401c8240070103103e440404552922585c86c0000320440341003c145c2c03444c0305820000d0206403100a0008541600300301920201d40700d010441c92141c0d03240401d9484411a01006000c2625680050201d500542011143d41e055414416042427440d000c64140f41d203001e03a0003500161481001400e10b01013204042d85041aa40b40704419456150481c00c60300a0003498031883c0c94101140c5004c3c0300040740141c410000300034181a00300c0340300260310015148800c90110b54400d40342c2c2203481c0200354854443e6000510000650f941c0a0011168080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720557347 1250 720556097 720556129
    0x12011502010c020601050913050a0b0f0f0637031b0b0405130e0a02060c010f050105030303060109031104021e0a030b01050f0d1e0c1701170d0507030e0603271b 70
    0x23042c0000c0c030100c0d1040000311400340c0035240981890914000070030392094001d003d94810f0410106200443d00c071640d00c5a2102c10400300e0b0710800e03801c010400d0303003100180d01e5403814560b840303800700522600c054088544489940030314405540e501d5200e1040c0142d1194580c04010350b0712104035104242c00c005115100c8105071141001c0c280d0010348103800c003485403805690b40302051036805070786110b250301409086000b5811032910300700013050b003010790000511512009204c42210340f00c68041da840e407540007460200d0800d20a0103181150401420403000a0500140700c00550085040b100122901c000e52841e0040d40820ba9000d07000c4820303661040704a1215a945140c520b219200761b070a8260707211152004058013091080c0d01c1a0000d03041c003a007000c2072041e00c0d0400514400013407818107050761a41c105080039540d9001d41c005041e0051000410010141519490244841804503100c40d00084040506a440384030442003007052000704400020b40c50034401c80846446 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720558597 1250 720557347 720557371
    0x7121b020604021921020301050601030905100209031216030807140a03022d0409060e0f01050f0a090c0503060a0803131e0302031c0e0d030c0215070812011502010c0206010509 77
    0x140e1040894880c484150380382c005e15840e02c0405046207001e025142c0c01c03e5003480d041c082d112440d1250b5403130b1031007083c1103418590300281c01d00030b58500303018402261140c51501600e51000c10018002002e13000070480c001003030700000550050265401040412101416a00303000b2074010a800030340c000fa620080c2c10b1100e00d0002410b64404103140200e070a8003440a403a2450b0181c44003e65280d41c200da0080c10705d00c010040b80c241c20444c0c031811a01c0864801c896855004003060075800c0035004040910f0503c1c0360380c042039400c00000c5d405203005980c180c2c25555114541ca44034041c40401c054428016601005030318001c0500c806200320007100c88a82076030f207900003464070945070480b012844090000d000d0258104d809501d40b0081905d440d183c121f841d540007032031004208130081c4114283c2122007080540348080d14551540b015140c1e6440071102c0a48200343c000744500b2900310031803075130800e00f907206000c1d5051081d40358004114a1b400c040410070100801849043c40d40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720559847 1250 720558597 720558599
    0x30804110907090e370209091501080708091c02030f070609060c0c0b01030f05120a0c0209010803040b0a030f0f0c0c0b092103060a0e07121b0206040219 67
    0x96901040d482c02030742641ca0b4910864500b24564008440040a40f0f80d5100703602c000c11800080301c004c05980e001d180681c9100d0800f1040f05078002c0c003031100069000041002002070500c41100c0600c0701c45400d80f91320034159500b080403034200c4070489072121a600100942e0b040081d030800c49440a41507801642e00f0622484050900764020400541f52603803540c00050038000d043c811515a0380f02458120304d8030b10345031140d940000c0c040c400140102c40c400a040207000301403114040541030705c91340350f0741e601541c0c1d00105001d08a01c0c050348100c090340000555034000204480494000030381081c01c0c508003050540003064400c050742d46082c0c0b9800c036408240b0b0316220b136400743d0310991240c1d101da503240e080c0301000c3d200040c0b1400b0943c0c08900c07102c580030783d0400071b00d0200c00e88030350140c0e8a0756100c02140c9030803072550108080760500d8062200081d0005c080d01c0040070500b104124040c10340440e0030702c50100780c02c2100960080000710303025090000010071002c8903071101220b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720561097 1250 720559847 720559849
    0x3060f090a0606090b03060a1509050d1202010b040902011d0f060708030712020a09090911030111040810060f21140105040618150e011509020d1b0c03080411 69
    0xc10300c01c5070040c1c403a07580c03240144281ca41003c809406850540c1c10340c3c3c01d5140c48004134155503054040c211130034086000c07212020340b02d01441c101402c409843c980d90601640340801c0d20b415103440901c059420b05001100710b0809109205c41590165101c0684104501d40340c003003c40c80c806250340010203192203200350344131034008052051184414643e00c0c644080028041e80d201440181518010007208003a650301082b401c080e16281c2c0400945454245005601c590300d0b40d8041d60103500b000c040b024008001b0340580b08407a80302c4143c421601c901a50001103034503038001c202422040c20414440b8840107813100c1080c011540908a000f00191035982110303055120f050101d80d1100200010009140210740310b4400580002800c0c0700c244e51078980514402100c07100041d91190701d8004c91030300f50006820014612000307003409840c5d962400295004038401c840442c2040340540304011254a444e540304a540e03500b0006183d941d40c2101c046501034000c0c0d80c602100b003501851 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720562347 1250 720561097 720561109
    0x614270a053724020d091203060512030f0c030c030301090603030e040e0d0e011202070506010e1302090c0307051e0306040f06050105040b070c0b1b0c06040303120203060f 75
    0x610404400c4034405807501c2160b540c0c29038a6400c5105116445554500001c4450781181001191140140011007106030188001d024040c00c41d400316003400e0881e424002c008405c40350b480466541440099110320505c9a00b0a8124400040e41d1040029010030054040544105c3c0e191005480c49c2511960046146410a820501459507100010402c0503004000007941e01007c0d2030500104120646240e152030280b00441c0903c4492040b44829a1045000c03021095040c0000c545030415401c185a80c1c220034040c0c0305c550021200070449034240c03444c41000481d8010329110307599030303445d2172035507903801c050101402d1141c180480907003485600803e4040c00c01c40c0202c03644031300d001010401540c04c0d00741e080d00103038a088030512450743d0002c1101c0949042000c11590782060380380c1041c4040320f41e801901100c1b000300300c102448680500c00c400c045082801c81c2d04007608001048800d221f14480200802d4190001840c1145580c000c1c50b0320110007415424254001004505 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720563597 1250 720562347 720562363
    0x9020903030a1211220519030f02121618090b0601050a03020403020d0f06050601031a0d030504080609070312020c090609091f0e10090b0601051c0f02070614270a05 72
    0x8014106440301c0d172a07440080946000070720040320700d001d01c40303950901d0b00310f4000140006820b0034884011142591079001441d140c8400b40c008540b050300c442c00300d108a40b05c050242140092480000350807114442c000d1000098000c210004c036500d80d4030041d101c540c060203c400600d81c081c880000544d40e11b1500b11000d42c014068a00700c0c0e41185403400480d2402002d4605152424032501c19644e40180810020303170003501c400c2c0c4040c002d400c095481c0d005591000c0b19512501e41001f020040110f1075204691081e100c114405101d21801e03030b12026001e2100360071104080c0000c545142090425401003008e405540c0010400c0c0342d402e400485134201009250f449054490b84501d0401c4000300340ca5440d2010446003200d6940d01c1e40001c1d01602550400074085941042d0524425001c8000ca0001e84104094220000700c80080d400020b416250a484c00c0282d40218030103c807150310030780350500354a01c40000c003068213040c031540855610542c4202c0c1c80e100d0010f81c080007418 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720564847 1250 720563597 720563617
    0x70c080d020306040506060705100f020c01061712030405120f09060a02160f0303020c1203300114100309060e0d2703031e030b2809020903030a1211 65
    0x50b94074a024400c1c0825a98007500680c09100100300d030740049140403e11864010700d001010440490303c240c0800039000c2d10303000b024554a490000508082c46090080005c1703481c80954a107504203199000c414081110060440c3e00000c00b02e002e00310401000303001070132400841a06120155000c2030b580d81124a0207009079120300c04610200d94141c032036100414401c5080030a550956034000e4a4174110400140500011400c04510740400c1c000c2d1620f1115200102c12000c03100030008400c00c800b00540506130340c00c5000400d2040720303c2d01c80c0740791000150080302001041c02d0110010100003d00744c0b40c4681c4e41480600c0300c2820f000b49090b02410381e49410010ac4004e0a0100005481d485c03030140d58110b900c00c2000030340203440350051b154004502400014048030030381c050f0141c805071950003906a101d03001c8060044003c04800040c412040c1e00d800c0d220036142c0124801d01c107200380d041e4428028816400d126030010204403003410700102d06054581f40f02c02883d00f00b11169 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720566097 1250 720564847 720564851
    0xf07030c33060503030c280f030207060e03031e09130510032001020604230604031106070f140f19051e0703090905130f03090512030301031208070c080d 67
    0x1e99486816401800050708040380950302c0c1c0740b64031245070703525079141041c690400100038458a440302003010a00340582c000306110407402d941c1ca002502d5466900925011800001b84610301d800d001083d40c01e020090110034092030703c041c814240c030340c010b01015940050401c0301500b041c0c02900880c1e00440003401d0504040341186840102c00c24004c015007200e0010800880c100da0f4002a15904240c200c04c221407000f455400600301041b2240a0215a102780340c180410540e101340886801d07240316069800070f407100325003122155921583c800004d80010a5100b25500490003031010351185160070380b070f1201d020f410301c01d0428050700b600041040498468205240c3c010318001b44645508010318000ca01c4e540942001d5450240a015590740c800042c9815541c40a0440380c82e0041020039502c251842c0041200c00703d030060a003c0e070350308000203010f800d00005803416280d00451460340c010140310f049664860083c110010007980d03182110120702a17400414243e6050000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720567347 1250 720566097 720566183
    0x3010f03062d06050a0e0906010e0405120a09170c0904030302160516060306082b0e0418021f140c070b0d06080111030114040e240405060604020f07030c 67
    0x208005240a580403410002c0944101f0034000b4000c05e90b24191a5540421040c03a1607606189241c1071a540a041d0548000505000c0b4a500010340340104c2d000d08a051100c13038114003140c3d4464007103624850300190008080740c0042e0003030700500003003910b040700d00c428454a900d825203090b02009a041502e83d00b243c0c10f1221035454000c48000e8101c41c4002c0542c094988000c00e681440d441a840c90015007018041c0ea45204140d04980003200400c107001180002c03409590101c00007030700301d2040404104000101c00c41c0c07181d91300c81c80e48540306c0c1c1702d00f460304209100c42c95100d41b41000c140e0244940101d545010310300135041d00000c0341400180d081c10f20100b10308491301425032016615042c00104107e01002900e400c9034074094070007203040c40e2090305041ca410f00743d103014842d160040c3c03035454400e40c0358003202d40f10324040c400b11006c0307444032402c0c0000c03846001702e18580d40e14204020400b01e4003440164402c0351007403801a212102032540d1158006001c5c40c483d5400707080b526 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720568597 1250 720567347 720567349
    0x31506081801090b13020a0b041509090e100f090f05030a2712141902031b0d0803040c03020603100311030d020607110c060f0a090b03010f03062d0605 66
    0x215403102501d1000070000b140c140d481d02c15800344d004002c074000300d001003001c00c21500d80301c40020040501e20f03030103502c990302c9a40c10322034050464241e00028550080008400c0035a0140820a1840d0005030000e02c1700d098101010344400703550020480d8aa17120347c0009887d0b1703940c9038012409032018540300c0d1307040c080082c100081042550304001d5505440580032000301d0a8104884014480b84c0c00c540503032820701600403c6504500550040f00c00c00c509112035400c84089040c8210b0a91300f000e0050186081c050070350000c403d0b0003114051050000490003401145c006001e2050f02c4159503a070390000340258012105807803541c41100c410030802c4601800f10042c040104e000d4451045040002581d03100010710100401611038040c03c42c0c2041405000c510b8040644003c2e503030031019840d081a544500e2400000075004000090140025001e5078140c641e0046441c111600d1502e841024100119048075000ea0100002c1e50784854294504a81e2058000203e00645424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720569847 1250 720568597 720568621
    0x150106120b090c37080411030f030301180e030405010e06040e01060e100305070e060306190b0a080606130315020d02070b06030631030207030203070801020c01060f030308150103150608 81
    0x10031a40c020346000c0100130807036107090b2200d814101061800b010f45503150b017800244803000c440469003501071072940d140c020202000840c10b03201403224403042201d812a003030017202c510259850071381d0000d1205000c01c2d071050152401042c401001c032800c0549174880b00c40716032400c0c3d10a00116600c40030302003a90800320880a80f45400c0d082c104503900d441034010707100d00c0c00304400f58401e0700008001406591640c0c14069022081051603030040c0c0c94500300b0300d85a00c035a41c800701007801480003490030300d0b10208440883c4960b041d206180d40c0b540c0e403140304000410720040304058003444840340121292002d1f2400f2402115000010300b84103090504255000e850000018080321008078071087c800b400e00a540d50754a40500d217100d260a00728240240d9402c001e5041c010a007000443c8241500903140007101c10008000440c0c1d41d01e080901c01015100c028041180403000500c0000d444440310603111042c100071560300c08a400214540031030342c0195010440d007805101e107c1c0125 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720571097 1250 720569847 720569887
    0x705061b0304060327110409020a08010c0e19080a0311010204090e010b01030e030a0c080f0c03070f050c0102160e0603100c27031e0303020d0f1d150106120b090c 71
    0x91320440c5c104000c90388590701c0541102c9207580c000c607103d400c41e030119202c51550900429440e00200130307040480800501c100300600d07800748036000251045500003a400f020354126410000181400003560f0b5007a902c681c008580440b141d51300f03100c0060b4071407050140343e05400141c070000480819000001d411a803116000c003070150b0040c00b9000c07003d070704810300c07124498016090070740f6200d1320000500280705440500500f400003048000c104030840380880c0c03103a40b040c4140c2c0c61040302c4400499540200c8075404404201c503240c10800c000c024040c090300709030301400b035039102450500500e01ba80c4036103503844001043e500f000706241c440e01c5400800020b010580c0d809413441c5843c1c240c021400200031800c118484200b000405019038102c860300b003c00c0800740003070900c80c55a000102800000ca2043c40d0314500c10200158010811324020301d0444e02c440c6040e400c01c4011258200041d010040e041d03500c11400116541b0007034818812000c03c150356641d0f0071211200ea017400700c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720572347 1250 720571097 720571151
    0x509010330020d030f0915050105030f03090105160f05071e060206060f060a1803080702100c0201080f0c0903010908090a0f03080d0c211a06040302030705061b03040603 74
    0x86200070000580d0109920508207254075012401020101c0780d50001c0420350401002e180c8400745d1345440d00066002107040358403c6040c0e95003102c5c89140f0544a01c109200240090400c12041d4640388274120414000c500940c5100f5070150345aa409240c0486500511150041a00380300035484000c0b40c4600038051901c041c0c60a03041c102c0102e003010310660111403043d03602054089026118480d50800c021126440210300c40e52420610b007075500c034000507130080c0c17503e283c0000c0c0c00d4002c81035283c94aa040e0b684c0009030741c1d420661152020054030301500540c0802402403d55024050703000d0160040c500f1591310424181001802042a480440c8444240c042000456007441c15076541881c0e512021840400e11202141c80c08644660035510000d22003440a60301d5071a0300405a080c000300c1000480707100ca030108002800303180b100941c96440a40203020f9814940c0c05005403840001c61696540142181130781590001c1d0009070010703651300112008200b01d0b041014841c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720573597 1250 720572347 720572423
    0x30906130e131b06090527070c020910030308191b0201060905071704110f130e120415031a06030403021b460816080d0203190905090103 60
    0x40f4016015140044030b101e0144500001682111414071440d1451f100c440c41d0608480a0319011201034595400c0803c16405600c104002507100c031401080002075941545590b0003590340c0000420582c1c1601c001125080c1e15501410f00604140c0b4000b0400003860300046402c50510700e02d14200d4200404940030044010910b1050032109508550420340203008c80903150030120200700303040081104907410110b820000e0b505000c030356203c5006146070005440b10040e440b8500c1d0b007035010754020800000c000c2442410068000e074896031520501d000240c281c400c1e4a000503510360030032501580540c110440311040440444550480e50350704480d0410000048070000080c80e08034080c00c1094003c0001d20ba007949254000c08032640c03461840c00c501c0a0711a503c1d9500c840d0fa500210703140c10b44090707002c04c0c00240410303e20011000380d8001c42c1403001c4100d220035003028a806000c240206182d020402d901c500b2405070107140280c5400002403480640c1c2d41c2d02100f600c800d440750b10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720574847 1250 720573597 720573599
    0x609090615050d080a090f0b030a050a05151212071103070603051306110d0c09090f060b0d0c050c030309150c0901200708070905070e0a08030906130e131b 68
    0x551150f0301c00c044541c00155440d100d00034140700f5a501c8041e1780190303c1014401c48000380a01c080c80046124055510084c081c0d6114040d580043c2ca0083e0350030190008240c15107899420040c800d0004260700030700320f41e400081e440040029901030030094842882c548184005810100300100042c0f925280401191820a43c2116003c1503290018052511413296003e500954001c0c0c1e010403c02c0401081404c800c039402628046061083c2c200f5507082c8045020006d005102d520100e50185a481d4500701000e0382140080c241034403000144401840360a1418070104042c42c495034103840203003103209058162022506000701442100f160030003241b55942d82c404582405000081c8090040703420002890b41070000c0c54018090511540000040000d02da8004a000e00301640710302c0c049180c58424000300c14498092102d069100300045400d42c20005c00806841026000403c04151240302c14800c441c410381e003051f030720035507e9440e13400d01100021585d110491481c070000340d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720576097 1250 720574847 720574849
    0xd0603050f0a1a06010e032a010c0209010b09010207030839030a08040510180c0807030c21020d1230050408070b010602031306050f0706090201020709060909061505 72
    0x10404403900b0f2264400003c5a01e0b07900583c000600300d10014160344140000014010210400009211110010800722929035000b0920011419000344c2501c0d20381e030034040304403000e601c03008603a41184103038034000000c220403102429482226200614800b05a00400e07500c1480c03500100c900b28000a804e564001400411200c0340d101d20305107508656a01e0a155051000d10044141070f2070510242c0c54400c1104a030301c6800500c0f5890700351503251074489403550b41c0041d0100070801d0046d004203004002204490b404d14103d481c0501c69000000d5003c954031030b00c2800d04071101c054a00f010344000707400014000c5500320303040e100c000240c01e01c3c648c0c1450040710810602c14603640c80204080c45050402c0315841904071004418a50751040d0003543ca51046401841429117000003040551042c421507444060892005050118a0725a0720040c5a50502241588600100090403043c03c0c09205c006240388100010300c005642810406d4910b407101c400039422443e10203003d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720577347 1250 720576097 720576113
    0x1a0105010503060d0f05010b0a080705010225051c050109032a080a05090a03080c070e0a05010e010501050a020f0f0c010e04050402030607080429220c03060f110d0603050f0a 76
    0x81c445c1c110785011300300340d0b480c100b640c0101180c101080c0c02002c0362001150040c000100882100c0007a402c41d605020544145e10801d040c000c900b50603400c80c2082001940717442101285107106200e11011910395955a003030845c0d20458040300411081e481d80c0f071150342e00c4160082244030316065419003080075a2104c44071700c5400050804d008011808811513264060b0312005160310404450390307001120310340341d0764002500c91940c4140340030002070440e08503801070310b0480b410300e03428040503401e00b40152007542045081c00c2c11841800c4100d03c0305203040101d01d1000310024050110782d2004c800040228104607074042c0500d003807900340801070310300003241035200c0450b140c0342d00f40c0e03150b52a25240c00200e074078516403001e58070483c074000d01040c010102c1c01184600d401291052017884101c8a03151604406043c1030066442080820010340211044070b5800c0070000300d440088555601c9a00003003a2840310316a44e00b03003481001800c01404c10f00040220007400f08031425038031148 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720578597 1250 720577347 720577369
    0x326011a1207120e190b06060c1c030902031504050d110c040b0f060705010c17060d02090c0d090507031a0108030406030b0f13090204050a1e271a010501050306 70
    0xc2006110b000e8000032252030b41c002da040d035603034000703030340c0b4024821000d0181c5d050068001d0320807400000210b41645401070485043c1c0c1c02e04005080d041c00d480388649400c1e150649090309268070794a405005030303810721080e40b5485a1503494021400c0505101d0302c4e24201024040c1030040b210a9040c2e1a040001d081c038230100e080b9408128403400a010501544803a181070360003c9001c11003500700309064014813001c0314143e5414000140002610b4403502e02916a1600324401075a40740240c2008803a181d0701210b8513010328580208030750700004035811103034240d4940d04806018000c00288107044152451607520b010025414543c0c0b058482c440d074860481407542d0381540c8501c03600c0e900303054038021100616030480f05280b5020800179201c0014103d100d0b034030308000034180b803605208081c0c00d076809400d0701d41042145100003004080200000ca60028500003101524543c0c1d90304d62400d9101d40311148a24010031644101c0030010381201c0c2c1800007c0c410009503071281c080543e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720579847 1250 720578597 720578611
    0x140603120d0e070b2137110f0702040b061908130639051b07080604050309090129031f140f0405150603040326011a12 52
    0x40b60100b0046240c035100b016441681d00e4000854860244c03c4491545000450003001d81280d580c2d90a00c15150f8090288003840700640300c08101041c1400c4c21103040c3d01c0d4141110000d007403140000184c0b210340102c92031528405000549004500f40380c001c1d18103040080c0d6420381008640c02e01240101856002c04e01081035000c0010400d080c120072810060b50040c108000c40d1011482002481b03110026403d251004007104807180001e120903540801c0359a03131810f0610010030030b034110900101800380324611442c1c0e404901030b0f2060040034011340c4154011a5074032000360501c080018140d000396400e0604041483c1c6100b0076100000c070303554103080e800796a5500c601280f84441d4411460f01a851090b8901040303490049500c038072580400c640300c0c0d002d000c0c4241003100380c400449070a4160081d00d42540d007a410701d000a150043d11900380070f84400f00d0644032540d0040034025050700340c0d614000420fc1e03414075801c0b042c00820418111880c1165244042c0d10080c80a00a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720581097 1250 720579847 720579851
    0x2090403050708070c0905040b280203060f030111210403020a0f0201050d05130501291519030203013b10050a08010212070315061d040609140603120d 66
    0x902c00300001c560440d00c0f030645c00030000d080552582a110300404045804855282148000c192151201c00040c0c44084002000c0c290b4611212154000f0b5000906034903001401c1804061059400f030091606403180c03544040d4440c041140043c28148002032200f071400c5c0c03030605201c0481c0e03011841244194020381080d5580e1030354070040783c0c107100310000002054980001e102c10740546144814002e40100000d00a0700d0120000c2040c0321350714200d815144044405520312803c1107030b20000b00b03841d44800d041c200308464030008032101c60340d8030f0708000a50000c01403101b80210415040034010303c20801c8000c030f5034a0012400503d154811350030380c5900000249034880c1502c64040640800740003145c9155958000c0e81c00703500701035000804810113000107183c2d5807107481480064100003821180c454079000b000c2d101480f8000940d00c9003040c03400801d402d500d843c0100c0d4010403940c0d400264004100b45c4990300c552000d00820b00c42c0d00819100794800c6468019100045820713940 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720582347 1250 720581097 720581107
    0x4060503190204030f110901120b040204020c1609140709092f07050f060606071514040312050a110306060d0615020a020a1d0f07021906050702190209040305 69
    0xc1c1d15100801510404001e0001801000304412040140c0805104000c1d071122003440c0410040104400d004a1240c01004241d90020462994005400a0000e000146020514068981054240d016402041b40e003140c04014808141c444d40301008440119000f0f0350419010043c400411031103940240da840310007009985201205a4040d201030500c205944406451210050703080040151501c0c00340007005103c54902188182c4904001445e65181c41203a03a209800c00140c40c03c0f06240d40d60300c81d03107140e08000c41007069009034001c0d1100500c417140028400290ba84c02400d80403100c0c00c0c800d11900d9095213605698211800704c0c1c0090300c520001c080c0400512055010500c903034004070344104001d80100c0c00c505054001e491303042c242031311790352281e10020303404514111010a000024480d81e07480d02e1120b8101d074682c1f0554a1100b01111420b10a0310010001d07a819075445040c4140140c0401c02d42d9542032540c02d0074081c4007a2034000881c0c0c110f0042015050100010b6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720583597 1250 720582347 720582361
    0x1080c12190507170a05072601050133020619091a01080606010801150509040618060f08010b01021b1c050f0c0409082a0706020105061e01020304060503 67
    0x71490050300c03000c080d851031103641081595078203c3e1049240160419030303186108400071540d1000243c2090050a403a8030380544d1502c007025041842151216034154246601d900303004036030080c10b034000b1102480c59824003000e659190b0a41061035080222540342c903060300441c80035884090007510800d1a03142c41c0440e4050b16000030003c100c45c100074480c650b0404142d1560341650100e100320703443e641e80c100c01582e07400070178016000b1541d80c0da03104d80760944c8a1801844041d40162000c182c50796907800302c0490341c41c480003880b0646c1d118003081c0308148082d0803d200074442e00c402400041c0c602d40000c3d40310b00051408061015525010a115031a0010552803203100780b241c40914400f07605207140c841c01c007044003030000e003d031420310b42c414a0300340a641d99082d0071104c0207140021980095504644403100001c00c50b01d041241810b405042c403600700100440c5d0008652454894100240c0341c100a41e091029000e1420000060743e000003603806494540c10200d13a41d4a03042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720584847 1250 720583597 720583603
    0xc0d0f05040f23030313090b06090d0303020304050606011e081b0c1606090608010e180f0d1103040b0f13033801210812040501050105120601080c12 65
    0x180102c1c5003a840e050002690030300180503002010702d058026030100710300340201912441140d10580d16486210300134403c03050640e2020b1030362403000308918500720140011404490484206501081c1d0220420051110500030280d12003006d20f08089c040480300c1a0341a9654000c01c0c5404000c10300001400c0382c5140c0f6120000c180030b6a60080d00e4440411000b41c0e141428405030321001d282e0703000010158040d00041090324010b0725210066030900c0340640701150020020b0302c0626540c26914032160b020300144442400460281611b9105188041c110925042d50700403a0b500401c800c10600300d81c2c600ba03c0d80301d41ca02801c0c60351384520086040840c94280c10103000090180d80403600c01d144e109080035020008241c40c260089008018844164244a102100085640c0d240d82c414815036a404c82c03144079080d4503040901c4070908281b01c4a0895080394903a540c0c1005028034030382540000c4c0035640e404002c18240d030401005540700c0007119101350044c2c408082c9070358203075024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720586097 1250 720584847 720584849
    0x6241203050d051006170f0604090633050a0806130f080c1b010806010909020c030417070303080f0c041406041203020624030601050603040201110303070908010b060c0d0f0504 77
    0x580c0e070a001e83d00703109065180c0b003500c0d40709585c0800c5801c000c075002540300340d040900c1003402d80da0000c4c0b141d90305014030000c1c1c80440402c0700c3c01a50f856400e9881c070860681c08401060420080e803103100c0c0c20f881500400e01d544c000500c681e201e013604000c2c0440000755140c1c440940242405803030f401d4a030031004403241d0b0f0380043c00150301090380620304d03a0025284650341001c1900316940315039100150f900300401d984030350004222480030f02200c503094004029210100b012246000d03600c00030411b1b900b045541030f15543c0c1010b002002030640c03100308141c100311401022121824042e260280c144914844c41004c06241c0c0d02d400e140d940c1d02000d503001001c1040f07400f0007005d8107141c001d460741d5040b181c0300c1c090b800f1001d06960842c08098200c0e4500b002600401e2a07900f040e04100710390708010412410001d40c46181000e0050a00c041c5010b1120f90b280c1445031400c00b0003840c02d551810110500840060100c0c42140d003000030301c4e0060814900f0b1414908801d880d0480e000d10175 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720587347 1250 720586097 720586117
    0xc2f0c120309010f030b0d0f11220605030102090a1502031e1201240e2701151d06090d050607020c13020a051b100504030305040624120305 61
    0xc80300640007100400e0702d20320982e280c06482c0038482c400c0c1d040307030400c2c65101e4004c40400c8800c40003450007540d0502c02800760f201c504d003403009030000480e00056840940994540c62101d080140400c0c00f80e00d0103498200c000390306052104011135031541203441465503403138010010012b00b500a2040300d14000588180b600c1e20300075444e05541d25809080c0c021400d1007100c00000f00c10700c003150f68445200e0300070801d402003081d40c0c0046901c41302c00803009a00c40d01e8082c58024204034207036040c8941c0450701050342170358900710100110307040000048040c17100c141c0004032000c0819850340e10035042110383c00d859440c10008989500f442c800c1c0209584900400e010446030001140785117031a007258600184001d28061b40c003a4003a000c0382102040c0c0c240f003000c60f001c06e500c4210242030004001c5440b006620781541d826035405480542c04240e03078409100511540d402143c2c0c0c01000c841c000001034a0a49021303030b40d0310381441602c801c0c10800b5445010544030f8400c840481e12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720588597 1250 720587347 720587359
    0xa0e030703060204030210020606091609080601060801061209080403080c0a020406031104111c0e030c01050f180a03090303080601050d050406060509130f0f0f060e100c2f0c 76
    0x10300d03860b103100207501c035001c240d100341c0c0a950401030407440050494801d40019100110755151039100032a0907800782803d40070301031030003808250300e001000b07018001d044590b690011549412006040000f001c148005c07120b080540d41070200d800360084a044980c0000401d64540082d10344074100303518080000e500c90705240000003072020843c1600e02c0c002c1e04450422400e5010324518486219802580100004025440d0503003092584090203011054040d01d182c42d028107007182c00c480d021a400c480319952030082c4040541f001000c911300702d4056009000401841e2005031983c0700c1d42c4001001c12035503800003010b6900c14000d8801d101040001440300d401d051a00b0005858a80070350750050981d440050b40108100c65940d240d1504a40c1c24481b800803622000c1b2080240c1400361400c110342c1c02d40300c00090161150f944501010340c00b4004801d01c89444000766220a00c0d032004104c070710380c40c1e1070010140221060441d035030305115000603401440d00c281012025040168002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720589847 1250 720588597 720588599
    0x703110307031d07120213060512010501060219021320040e011505120f040503270a15120f060e0f07030501080303011d06010c05012d110a050a0e0307 66
    0xe50140c0280c140c0f0440700c800440c101c0c90920030640c1c0c4d081c6a102c1c0071002d03030845c034155000d424450982007a040001070302281d000e480e07030041400c0152002e1600b444d03030b55400c01040801d906100707206003100301094289000740203400003002c002942c815960215500e8842d2464401e2807551203180844000c1510f4540da96100030005c942c4092080c00c0001e200401c80140361880349040300c4040b5004100c002e05610384860728030f8650320080c0219503900c002c121421007510400c20500d9142061604100301e005036009010394205198085007200200312003e000c51504414141004c00c0c2070a00040d10781e074030350b8160300a00301c04d5105072400d07040007052050300b82c50078220b240300f0b0341c3c1603d0900540c0d0340d030380c0203d50368802482582c03030008842d0160040361140d4178400382c01450514013859030522a0321640e007101c0b1003078852249103542d0071000c0069811041d080008804c00b40d4108078a005039420350301c03903220345142c000801030b00040c0300c05070600400b55002c0011014040b59401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720591097 1250 720589847 720589861
    0x108070921060b0402040308250209012309240a0504050702071502031e03190c08150306090c09070c06020a0801031104020a170a020405061c0e0a03020a020907031103 73
    0x94503601c40c0640700c0c54100083c031400f81c2000e00807141100e1b8064031071441c00c40c484c1c4060302c000001c90310340b24900b0a0740c040c00b00580c0d40e50b100c0502914502191481005a400000580001174280d81d401040704408000204601849840d0100e800d4102e500412440d100062000300c10303500000d0b407042c03810013031003911a800100003013075030f242410300c0d5840001d800b022b99590048540007400081c0d086004503d000552026642066070740f41800800c0d08040031a03400d840450440000060900c010088200300218541103103072010b81c0603100f14100124016120352010baa81801515114042680e0790b114214241c0702e950041411903c2d05000c61005000001c20301c41a2807403847c240345480d191515200700c400b8040a522904070440040c130340c0c0541180001c0803040f032141e003400f000031651140d200a10f0004a40300d10072184400c0d0307a00410803540110152403180e4481004000041d0700000c20022054045954000d151340740c0c0822006460701511341945840d001c0140008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720592347 1250 720591097 720591149
    0xa170106020d0930080a0f0903050a150f02180108150a12020118030f11100e0f0a0f030305070c1202010906030e190311061807030f060b0307120605090312040201080709 74
    0x81c0480c2e40d903207031f0a000b005401281d00101724000a0102d4219060150002c0c58039952101c1c1d03c0035101004c40c80404100c4c40604a80100810031800802510b01c0c3d00f030756a1000b4031540c0811281500900f9516031804a0400061409500c0c2342d88002c0190405580c020100e08541c88170401c3c082440c03980b00d1408044440c0f094804481e800968001301c000b40c500340b1034488031120140e90321406200100200010b0510350a4040d4010f01d00300d0000c50040c045e481000091401390321520740d82c40081c1341056001c203441e806240c40b1000c2d48010f400507170744555003004540d1503150205099036105082400c004140b2011030300c000000c100c0c5410540c0240d40700200000c45400e59400341c0e43c0310314070003813000728591a42103504040002d20001d950305582810741070182000081458018000c00d05c0d00300290440702d206c0201d031303003134000b088428001c1a50042812015605050030050650081030024100a0500425100040c9a5845420248003c0c009100d401400c10000340307030155 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720593597 1250 720592347 720592357
    0x1a0906150c15010b0909040f0f1713120b0f0a020f120601021b010e011101090501060e011a0a050a0c14100203060f120709020705070b0a170106020d093008 68
    0x500300b0710a000180f1440307184262011940c02911702d11459942d40d440c0c0b1912500740741b04881010612a903a40420f4015292071803150302c01000941e9018142c19804600d81d066101d034005d060a40c06500000346104841500058100c0d4a044c06403a500b0098000e0f008521112060003400314081c007400120301c0005014007000e07003d840221881c18801003003042d88070081070201c1c410380000d40e0107500c103008901d4014030080c00013a40050a0b500e1500b5110581e000c9402e1205e410014030a40320342d56003d07a465401c1500051420f0744418003d08107006801014003440050101c000520140c4030035601014a001c0c00ea480400018240030002e40081d1920b0b8001c14113a031180341c0303a09003500c0c006d130002460b100410405e464a640382029502000e4120340b030f8001c072080040e6002004014114034248e6440d903080150301d03903415440740d080580c0044115403042d80306d1000385030000810416200203440030340c1d041c2c0c82417846100b04c022000d12801e98041444805060002c00e4010b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720594847 1250 720593597 720593623
    0x3040510030b01050c1b010e1c110102190b060f01080405070e04150c0c110d020604030b1003140d02060a1a010e0a080a062309060c09010c0c09090c091a0906150c 71
    0x30425400723814030001d43c510090f10407807201c80e40101400306007020200310480c50140304a42004070030811042d0792801c20b00c0d048600c00f00c0354041c050103203007141c1c0303c169428003031074040781d1403601e5180c0e83e9655000344510118988a40003103410b1018000440b024049491018003a000c4900c100502d110203044040d50405044805005c1d1880c0200d000d0ba2002c0e0014405070800307086855070200b00f000a802115482d0540c98004001004210300303020141d002c0010349540c1482c0789000c0d0900200a0442c40e41624025001c03000115404500240060a180c018520298507001c1404000030350003030b1405205a9103201c0c100440f035080441103450b419032500c40d0b0640e080581e644031100f0755440c042d076044034001a02c5071280c617000c0c04488105250580742d02465440d406900c52154002c1c801d6241c54280078400e118060107082c00420301c5240400c9000407402d4030206820466143c0e500c2080b0210102d141a500c0708c24001e00b40001d154180c0e0b580c2c1c040c5101503a02d40c030240c544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720596097 1250 720594847 720594857
    0x3010e07020f030f09010e0616080d142202030708100c02070506250c030804090c081302010801090e03090a0b04031a100302040c030e120307020f03040510030b01050c1b01 75
    0x102e0440004400d035414481c4800d02d01e8180f64018005507601001d602d01c050304400288024003d021040c01010700349805800349548d15a000f00481050311001080742d540796100c0002c3c0b10341c00f00c240b0040c00101d9860300010403c803505200003410500c5690240003240b00e69103000d15580c0440d44501040e04147d001c40740b28a507988244152030040446c2409008507042c1d11060840c0c10071140390495110700300c1480391a07220b503030701c0305190465001320422681d244555141d140d0480191900400030b02c1540c1b92039010313580000e0200070140180321009460715050392280300c00300150f81645030006d0068502e251150f603407a042e90098403050303903041c6c180c03240c00e503001300b500c1c80081c001c5001c1401602c0c000e08540078400608030310000c810405540d030910422851040c0144c0030983c0310785440c0d03992410b004030000c1c5418a030100344a075a41080100300842d0340c80c8910044000d443d07050114a06d5658001603c4078010f660500c40c0502510040000c1100f441c4101030603113500740c0364 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720597347 1250 720596097 720596113
    0x6060a0501030603050c040b030f0115090f0e1209010207031a1b040807150c050a0b0103060e0312130c15020303040614061014040b0403050105180303040201080106030e1203010e0702 80
    0x46050303c200303200103041a00700502d4240c903820705401c070182050024080701c4c40401d0703c1c2940d5084481d801c0424012009101040c051199a8001d03501c62040100f4107021149808000581320071442c800c5241c00c00b00040d0041c00350f4001d1203540c0056400c110610000e140c03044001c007241c08100c85580c0d0344050417141c0403030703c2644000d407000d41d03c60710000d048540c1440c002c100e171300030200000001d01c031007011003400068040000c00203140c418104551154075600e0070300d00307680b0b012181404036003050000031941c2c05c02c0918035038003481c0c0e4107031a01040f41d00c0c1042c0d50003034440c0d004000d580c100070704c0d0414141d80000045000e00c0c8600c2080000003c81c98092880490030380703105074408410700074110018415111036410200741290640740c00e03660707000381c1010380c03059100302d541365141c5040000508a81d21700b51b800202c050061072651405500090044405005000c20f156a80780c1600d00304104000c0e03241c9152409a007a5070b00e5071a5078803150810f0086401d04010310464213 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720598597 1250 720597347 720597349
    0xf0504050c04060207030f02011701080a151109090a02070606030b090d020a0309150915021b06031012060f02070b010503010c0f050307030b1201020712080a3c0c0206060a05 76
    0x42102c04565066010b040c0c3d2504542d1800f082910b1900180c0c10082103007200380001e00004030140c020031200008000c91039013490160304031802c074801c400000d403825602200c1e106044013110300c4080100c030f0f40030440e52042e5610f0024003440601410191402d031000c03041040408226000740c038050100d8000180c0050103da075600c9000008002540c40e41080104043d0300308048000c44e1113013401c0782015103e00e14003c052207100d10950060703000300080d07009481315140c40080c9003400c2d200e10740785281c501100c10201034507101c1c0840c01e0301c030f4100c0c0702d0a01c185988150300300d40d510f82d410340d07807020207091080c0400313005c0c00794610a519001031004494043c402e009181c2d040c2c0d0310b5050442c0c4d5001c4042c0c006203901408a40c01003040c10010400010a00c000c0c4081845201103850000e0544401082e4240042072010141e1800300446c44411111600c0000f000c0041c01c0301c40c01810a0840804d04010b12114003185400e00c5c002000701c540126025101c0c3d6419100100c496030350700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720599847 1250 720598597 720598621
    0xd06061203090b03011406070206120c0310060212090d1406150f0607020907030b0f13021201060f0504090903210c081e010504200d05090d0c0201051813060f050405 72
    0x200c5041b12441c0f000201d03103035604140c170140c2895030008101c9030404042c036250840301c1000b11109904140c0002c10004c41c1c1218080c1c0b800540041d1005015111040e40c203040e051013080b001d140f00700c00368558a4100082a002e0000749000507080c0d41c41c0e030511144059801c482c1030407041c40707049542c00c01c2d062810150f0a5034200358008104020310380300d503001036005101c116605604050303d500008000d494014040c1c05404c0f80c01001aa1840320302c904101c001c40680051040000075500c50b04250b611a040d50305881404400180d074106134039040c0d0700a1984080303841c403e002c0c03e00030f500c2050580c1c410021002030317489004865403001184019522008022503031038040b076005025504040e807020340698000440643c01c103114403040c0509402a9148111982d10741040000000f000e04c00d85030040d8490410078500d291550000e40356020b84d02d1401510b003503600c040c084c3d50b5034555104c2030184810310100021603e03003800c1e00c00d0455901501380102d00b01404200c0c805015 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720601097 1250 720599847 720599849
    0x3011b021f0c0f0311130b0c060708010302060a11150711060901270212010e0303090106050f06040b28030e0717030a08040f02030615030d03061802090d06061203090b0301 75
    0x40d0f80e02108080840020f6005102d00f0020400c00d001c203002c0f100303181c2240441d4101408060b944261528410002546082c000421060412804100400040c4c8031403050340d4038804241064041c400246a11518004540094408904d404c5090104003a00b0064050a04a0060940d507156a41ba1446401e0b145090041142070700000d80005d01c1000107601c80d85070902c0200f040814043c400c019900b5906070074001c200c650000000d010704050248503c200501058449019092915000415601851040b607042500010b6948044005084440e0010480c5030044104c0120401d00400070b20701100c03090080d02ca001c40200d601c51464804445100c00000107600c2e116201d5001ca984c1c10380a40116409160382e0002d80045e501805002d2285a520103241d90401160341098900300312980d031003007810720700744040c801c5000714086402020500310b000750b40c0e500700c0404038a450358450806000c852500c6004942c23040702248412406000e55115042c0c0e0b500c03840c69500c58482 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720602347 1250 720601097 720601121
    0x4140d02010606092c010e06030d020703030806060c011b03061a181005040906080105040623240d141e060105040915091505070207030b1503011b021f 66
    0xc0c001c0420645103411707907400d004002178904a0022071480384280c041202a041707a00c481d0140c07410480e00d030038100100d10f0103100c14401001424910346014016400140c86c07140102c0700081c4660700d82100350400d8808606d910a0b940e171003081240c0040007028180243d0790803624032010389440c0d03100d1070140c4052090029051482101800c20441b2a80013046040140407080c000000c60040700c0c412403008180c117000101e10341c40d080c505001200d4000407044c00329502103010030b010034280038230140e020700e2803030041e1502842505c166084103620f840c01ca030700c030443d105503c04002c190025010482c21a5044030030700c1c0441d44260ba40002e41000070303015030f40500c00400c16441c090700070b0070040d03015200750350068138a0540380d0305a4100307040c20380f043d140c01c1d0a00c610f9500140301c1e4680c403944034809000b9190565071100620b420203081d00540c0040001c14500c0366501390303c6401246042d00303502041d840d107008065202d2007901d689030f4403094500340300b0440500034040e48040d1a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720603597 1250 720602347 720602357
    0x110a02060d0917030a0207120801180b040e030c07030b06010e0315070c12050c0d030506060a1103090a1e0504050c030c0703030b091e06060a020d0c0f0b04140d02010606 74
    0x6021281d0900a01442c08261100c108a06650301c01c0707103000004501402d80b040025907580341c141001c4d80c3d9070703c030b0441d8881040150350040011341c2895181a0004012035004100440540001005002812642d181d14000020001c1e02c14000045076000c81e441001c000c04181e070350a0041da0003200c04111203406411203a2703a50982c01e944191f1550140c0d403030400c01202e107103580340e0b940c2d080051644500455000681e04040b030904100740407420405207001c0c042d80c50300f607021075100d00510010300c0501c1030582d900001e1105c1030040d58400000600700900c49683d92400310b0010244d40700d00320201400a01c04106404c0501a05104141041c401c41c41d41c2c0b01c01e40c85006540c8070440550802d40d890034141c2055440d06d0360513006442881c0040c0c440c0380f07000c2c034481c1c40010141c16944505000c010350b040f02038021840c2e5181d02c4250411000d01e40c0141002110889218030040001030307a24104410001104a5000031401c8001100c01820099000344c0c01c84010780a1500850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720604847 1250 720603597 720603607
    0x90903020a0b1e010303030218100203040510031e02120f10050f060706090503090301061d1611070b1c0c140f0c010e0606010f180506160803070e01110a0206 69
    0x18484024541c03c40303034440700d100600030301000410340c040d000e800480000303400007820001060110718003449030300c040311110111224010081e44d00e110b00d118003406021a0b524801c9000d010303500c401020030402071030217400d1540e010641c00a501646070703032209889400c041b13544074026040d2184100143d5441d01544d41c00c000030008079415a0f10300aa00600410900d00040c17101d006610500c0c1c800d000443d2140c003503104060a4a06682047c1c1d21151808540008541e1074141250425144203401d052024070400498602600c000813036618815007100007180022030340200104042c0304c80181c1200480404071060701e06045201d400910b11011504040c07000500070181e05440e814101d20300151100d04e10300b0344095128402d01d54018200304144ca50700300c661580304605907e8034668003003c07086450541c1d8110f0007040c0c0a0540815a824007810405948040c0f603044a0030503200e20384004004c002900401060303001078101585000d84840014611208c50fa000700a28104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720606097 1250 720604847 720604853
    0x1170f0a0b040603150c020c030307050a081e07080403021504080a031d0d030206012904060309020406030f12092918220c0203031b0c1513020a090903020a 68
    0x140071210381d1154071955a810001c001010701c8002c814583c0030324004141403c29503070190030007032490220350081d04200300e1140000c00100b01140110b40c00030326991600340401c01804510344039008266900c800249607410b114950000c0c0044900c2100c1607060100d402104003050f000b140b00f0001140d0000f60003600003800380c2c00100d0300c0416206484035443c00c107000100c9185903c0c3c01500941c10250060244801c8400d4450b12201d03d208003154014002c20808018880c0d44683d104165079407400b10219525500321070300864000029030380030501410201744c02001c013070030340c0081a1203001c00183d0003043e2403080201840c014050002d8566103c0c1c8a03403640c40301c00e00d541001d0150951000995030030601c1410501c00c5910740c0440703200120340c00b00f19000400c00f4015540140104028603800c1402c1d0441c40000192050312040e0b1407180c646009140c0d803440001328541c0080280b1049038620aa41e400d008a540070540c45d5143c14035811903d40c10310103801a00140501408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720607347 1250 720606097 720606101
    0x203220b1204061416030b06071110020f0307080a030b03010b0a090213030c08010501081501121502071a0702160b03070509030f0109150b04050601020d080a0b13090201170f0a 77
    0x403007030240c030f070100b4410802429070700b603014122040070b401c09015a0b11070100364140300b440344001e4103607140351614200340c5404507030852040b080c0c1d224400d0641007801c07040c4240280c00307a0040c072170100c13500d507034051420b441150800020100005e180c03c550b10610314050244180d00b500141030428082e007405941e00296120340003241c050160110000006144070a85000030040c010000880394140a90703d4146046901412806c106840040c030401e00c071a06203807030381ca501a14440041c0890380c1000041e0094100281c240d60154101032039121506020701c0c4540040c3c0d007600d2000d94120b040404140c01805070901c0108e050002458990140c8014101014002c08036080c140c3c00e000140d00f034a80200c02101d1103080c0b00b002e608c20300c903140910040c0721403c42e0180014600800000d5171199145024810410758101044845030154414686104041c110b00c402102d142903140140100a50481c0056054804090803103c6648403a00036800c480d03041d40c450300c4500c54900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720608597 1250 720607347 720607351
    0x1b080711011e060503070518060f180a150603110f03061206130b160e0d020609040603030206090609210c07050a0e061002060712020d0b0603070203220b12 68
    0x45150b41e940d0103400e84400a02054070020004180811214106018182405070340c0c1d02060280b44061950b0102c80c05041b1a0355001c1d6054401c40030003403140c0001041e03400242070610030765418400b801a01a655048403103080642d60002020981c1e98504504680301030401e4907000c6004d201c00940c03002d03554000d5400100003414505803144040c500da01701300c8107031903440e50880d03440200300c20400182600da40c45059007a40008610b0704d04c2000c0d014003942c03c8994800e10740381301108215902c610a803100180060700420132203469150103591480196182056441104001382101000080b0030440788584145107141000d01c0d0880c4c400c5800403200e139041805840000b103116103542e40d90300d0060a000440f82e0301410488240000d812040e60000c0854000703130100240c141e0403040c82c180c0d9017a5603500617501d01100c1240801031402c004001e500800000038018010740c008050610b0402d01e130051a034000261051300c1d20303501e1900ca000c2d01501c040c4410b410100e0340740a407135 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720609847 1250 720608597 720608627
    0x90504020607021908010b10080a0216050d030f180507030f1502030f0a18020f061c0e010e06090627011803090618030b0c0a02071a030a1b0807 63
    0x15081c10076a0380010b41500e81c404c6000155000c1400811502500340111300b065882500c0c060351290303011900600e0f0160060510005540000790079542c1054036000c2440c0d607400c20140c40000045d800014042c040e030841100a10307041ca01d80c2c040b984d07080c1d00300b00031a80d03001d03000b4500d5a02c0d6544840c0324cc010858241d0b0140030042e44c4850008140c0015446070041045049491428590020031201d60030100700d034206a4210000060715000211420404c3c1101c030603031902d04524500303000c2070b0b190002d00c0c002404d1240112225005421403a00d0310800416a411030391100070940d039506003260201ea00c03107000c2c0c515904106c000309520b141a44810300114005c8111481e580307100c82348a034110700064810700108a515400404001c00410340c61a00341200e00d0745c0c0345c00002c20409014040040000204203076500c0c020130100d001080720541c0760407031441541c03040c00381e83c0040741da03211030500f0f042502c1146c3c0900061064041081d407590742c21503c03400c4c0e040717a0311080e6403150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720611097 1250 720609847 720609859
    0x807030f1b12021002060415051306061d01050306070203070f0303140405060f07030e030702100302091804150606050a0e1c0c0315060b0403060203040206040e04060c031409030409050402 82
    0x40c0401c0c80540e0050090500ca140b1590a40050f1041c007050329110030000f411500514140000180e034040b1480013894114000b00e03450701d4401e0700f03840c80c1703641040007411b06140800000e0700c8920303004503240344e0490340900026680c0c0d880606444001c1103c0c0710006070420486840003885003074010450b9070080c50000750444104c0c00188900380107032000d40e0541d11000400c4280664191071a030300090342d26091050480380425169a4000c891009104030f01e0b021a40c1801b80c440d6040d80e0910389c00415a8550740daa40a040704c85080540c1e0a03500704960f0246001d00781c0103405071008844d401e5032031a15118506804441c0503901504403580310790408840d006594110100c030907114080c04050005510754030740052045070008962024900b0080100081d4240e9016541101e40003000540c0d00d55840c800100a0b04c00e642080e90104a90300c1803200b484020b500c40b450300d00d4640c600f0081841d041d204c51003c55001c80780180d182c0d004000c18094001d031a0800d0f030700240b0203042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720612347 1250 720611097 720611123
    0x2120c130504050903030a0c0509010c020d05160e04030e01031a06090a0f060e4209040606030b030c09100b0c030f030711060106050c3c1c03060807030f 67
    0x50203941c03041e2a401101c5e4004406e0213102d2809110b0140e48480c5420100d162035000030010b08444031001c0301911906400090005000c018040c00d40351440440c4004800d50f01c078015100c459405403026000956044e4520106501901c142500f107405082d0003903401e09000200041c952240c4041030b0480341440f800501148400c2d2010040e0110b5103d5800c018424400c0c4054040b288001d001c5009109440e2105010340b0100442c0016002603400c6080c00540c100322524842c0c00c011a4101d031401d4000140e2a505a009541c4100b086050701c0d002c4004078200709030070030103403200141c0b011080d004005000003030001340701c1342805805582c1884881102c14129030400c5540c00c01241c41218020443c04040c00a03502507d03250034074030705084203c5d5000e680d50720620708090020a10813420821010449103c060880c014108044500e00050f00551182036460303144e100b05040500e1440d451b4000c0c002d8406071404000108145450740c3c41e0014881d89101d000e886805910107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720613597 1250 720612347 720612349
    0x1b0a02100f0204051311030a0b0315100302011e0806040e0a02061b070806070c03030f0e0a0c06020118050a08070f020a030506010e0f0403051611030d0908010b01020102120c1305 78
    0x488000101c10003005032201c1c0791a0903c0920f10030302c603800b11200d10f05502c0d0a0840140e03410307a80c0141c0c01c02c00000f000c01034100800d1401040c05800b08030502c10b2010130050a4000307203101c082d01d200ba41c03403c02420040c000c1c25041102d0007000700104015200007065410142d007d010f504071000c0840b01d500446030040303503040d484080c4114007040c0d50781101d101c40200304101030003480000c00509007490708001c000d01c612000c40c0c2c004d08050b04d4102c0e6907120f803100d401400b04400d08a0517209503155a14090100300c0c090320500c0f0255090040d09140071400f80c0c00284003507000700151038041d10b10741c0c5226190303000c240300b100c003011200c44510250300d031030110300040c0d880b03000205083d504126001c100000d00500d202c8803030000d00d04000c00031358000195120740c05000c1c9213484c403000520741024411500e0b42c500d501032050041900d2811782c4100c21070201c500a400810040c0070450049080c0d101d2040503800384900040800e441210200003401c0c0904540030019030151204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720614847 1250 720613597 720613601
    0x9030210181a0c010b090408180d0c0e040246080a150e011a09060f03100b15092d0402160317040c090b04180b040314031b0a0210 57
    0x40210b4007101e0011480c0424039100f4031a0450314941100c0d103d05d640382550b90700c20940f14100c0c440381104403004070004c5035201c24682c280300c0b580c01800381c620140c885400301c86080c0120b5050b881803a080301403d40d141c4c20200c0c1414418522250428108003455a00304c0640100d182641ca585600c000040c80c2e04013440b14040061044641e003031404400e0a4050550300c104840c102c15924150310488a02c0a10110b6622443c040c1c0b003103641c554be080c00007181002e850554030303018011198920f00081580d8003410b113192003110002c0a03091120403404c0c07a4040c4910b5103411030031010404600603140c2d541c0c020750350840703000643c62581450108050307800400c4003140e41c00c000c20f0740308100368200320600081028003600c0c4000f4a0140c80d1000720422034407a54600b2aa1060118800d456582041c200c1c0c0c480100d1403281c00d01d552030300000303181040f64190001800c0040030042c903084c410480780540800d10090754650092418103406501c9100641c00350b100d0603014006070500380c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720616097 1250 720614847 720614879
    0x3231e030a02060a150501030b03030909010e1b1204031116090203070f030e0a1403071407031a0411010305071106040317010f0602060c0f090607050d0f0903021018 72
    0x6500a19126051000007914080004d41140103007424240d03103030060465201880221902481c000c2800c200c2e44000c00d003503100d0400d050350000c6c4450f00100d000d0082c1e08842d4040c00690250303840410700f020802c0e40c07a00401107040c00c01140000405e0101380f1900203081d03144040b00684001b00d41134040300c00181d42e107501c45c003a00350b0040b040003005d6030400b0751083c4170421401c0600610034800315281c0c40b0303254181c004154031206a40c1c0c2c0c0e440a41002901c4606d5801644402a0703209414078561300e400920044806c2207020300c0b0a0791175910030001340d000700d0f030107007035400c00d0002e83c0c0055002c0c00700102201c0401031344040702c10040c001001018001d6000e0b4a403100c0c0d841810110200042058016820070b26000d40c0c1004050b80c005100b80e0301032038803403446032078031203803190240b40340310f00c1600355031000c0c000c25028140301c40403414205425150b2a141004400303c0000c1d5464005480042d52100988280001e51801a054018081c400e03003175060042c1c0e12020048071380c55017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720617347 1250 720616097 720616153
    0xd1e0308090105060109030807020d080910210209011d0102120d0b03280602090609031203240607020d17040f0e0108160501050a0c020303070b0601180323 68
    0x1045091241d1940284507981d00240c00b880c2c0301005a085444010340d41c42041c070000d00032480681050203003c0ea071810f8030f01c03200004040d02c2c403c00c1d0407400242100d50700400c1103034200304002504a81c212a100716804401e0684401940b10901c00300138106603100700c1d965040d40103500141c5209900c01c0c0017131400c1c1c403030310800140c0428544281171815042d030302c1d201d1030024140707005ca643d4585140140e007459030084015030740f0102400030503034030300490016540600c101c42141d01c140c0c92200103180701d2005031803000381c002c2e035844160101e407200398141908044200314090142c03c00b039000000c128020f00080442c0e10108480e51045d90055216488100a80344107002c001c10300c8000034010414540103101c504541615160040154800e2505120001038000d0180340254034104c0300540040a480c0c603801e00341040200440100c1c1c659001a50000d03c0800c000150101642900d1304041000c655203070781510014080c02e440c074600300906c291003900303601c1e842075182c030000162 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720618597 1250 720617347 720617357
    0x150f120204410d0609080304050f1b1f0302070b0f06031002090a15120203010602151e040b0a060306020315010e01020304080d051b06071814010203090d1e03 69
    0x20103030107100b501c258400281c200061158441e2040b40203405010740c0c0200c08031a2100550414508a0001c01c038a00c00100040804010002445000310308005c0c100711000580d80105424104404518002c02007240d00c501c4001d02e43c1c0800e44a4210700c91601d4560400503d00003003a01d8a00196604480d48100032001200300802410107111055143c844040c0643c00d0103100c00004038000040d000c0e00d01c0600d4000c043c840014414810920b01c203d0321941156a03507111000251250100580c0c1040b82081c18041b400302881480e004c00142c00d11800da64150701c0300e82d90503c8074140030703200030340072512240c0101c0420340310310055014034030074480070400d620a4000508410401311035103040d500300f44420043d141c0003103007048659002e403920a5441d400d50b803500d22484103219000806104100801001940002c6281500c60790030018804465072184000040c90310800c0b4980123030400e0103610460300740450b5244159114445001c800c18016130300c0e180c280132a80c401ea000030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720619847 1250 720618597 720618629
    0x18172104050c0103060f1202090a0902100336140f0d091a03010b04031104110406181a1c091e15060e0c090406031b05090f01150f120204 60
    0x9a01441740364000c2403001030550324240750602002ca241c2c00044040d01603c0f0302d400050300004603a0010304000c0e0300a08071454118008801001404030500c000d48144850000140318008484c03050005a69840d0042d400c04455980c000d55011500219a480c800c080f020410f0781c4d024400b000989555a58800110f4942040007030b444c02c0c0d08014492030341007000140540c018001c2200d068981080c041d00440842c100858000d244d164800c0b40c1a20020402142d1b265102951040300c01141c00e10001d4591030791072841550015042e003131940e80081040800310801c480314407416184604000030106016201d0114072494500500c0701030181c000c0c801d0401c03403a141d61a64203241d81c1c2d0b042017030f40e00702200340d41e401002030710011880c2e00104511007140d546030400360144d40e002403a000000c921070b00c0380c005100c9071300415201d40740300700000c0c405034036102005d4100d64141403140b2000404020a842c03203d0030003070f140b040095003480860181d015000402c024115404140005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720621097 1250 720619847 720619849
    0x314011a12010b0a062a02210709050420030f190807050d0e0108010f06090b07060b12010c0f030b150a050d020310090608060717060a080a080a020118172104050c 71
    0x40e06c48041c00340c802d0480300b07440c030158440303042401090600a401c581e104165500d40c44c40c0981c190300c617940d098201810441040445c1c4020301d0800140d00d180c2041035401401c140e11010441d00410320b0341c1c4058a400c9460501a1610207082e0040781c2c05440c060458a459092405a261590204007810304542180d40e100001c03500424103074664813030a60400d0300040c66150b6603c610301a13121301049610a0194075400703100c000740001c0c840c50603c84841002400703003424400d80004039000310501034010340640101c0c101224000c280e01c030031103083e101404203608542e440741c04000080c000b0240d0f48e01c8a200640c040d201044400c2251490030210b4015954103802403481d0750007178814000d011b50400341c1001c04a815a48505030741d030b104000301c0c1150300c10303921016003881040207502c103015056005048040701c541c003e0082c00c0c403841c40c0540e5007090600043c2254200003014003921000409040003074070001d0082d4100f01e00340c3c00580c5c0d004050b036007528142c000940c10105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720622347 1250 720621097 720621137
    0x40606050f060304050706081803070b0f070512060d030201090c1706060d151d0307030815030d09090203040f02040c022d1002070c0305070f0314011a12010b0a06 71
    0x1074168100d41c95031942c81c0c03554415440362114880c000034444501d01081440c800e4044242c103030080101101d4445100b030030b00c88c05103002510908925a070b80b80105500750b201e00200d8015000c1304030350082a440302c070103100d4410754020003602195a1441040c000820915000008103641c807140e802010b10354150a040050140031030f0700c41c1204402c18000100710840c2125200c038901e0000030034241c1ca00c69500c45440c402131030030441c0000140c8504041d044a15a4001e000d00e01441103055141070500d84d8031a0804100e1010900007042042a0081500150341c803520510044510115039404a0f080c1e4503501101da0260700070b500c105030484880081301c0c01c03003051000c214850031504618107450b8450390081c101400d400082140c10710042d2a0800d008550202c100c80708150b46209001d80c40c04035000454410200741c1c07212130a42414001c0c91410003124000c0401a002942000425031580f41c5014080d52280301024090b07035895100401010152134114118859018002c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720623597 1250 720622347 720622369
    0x1024121d151f05090612030309030408060a090308160e030a03030506040509010501060e2106010603091202030c100504021f02010b010e0406030f06020c030d09030905090f0f150d0b04060605 83
    0x40b200c91142440d072080115980020072148142c81440580d12843c02180100c0c00c00d42c10b841080c4400010b210240d0341c000002c0c0219040e00341524079a0b15000078030f4040d01c41e803c0015002400307050201d50284c40080c40c065180c3c10340d0030148602d10114011a081c0b60490340c085d00802d90b18400c010607030800f4040c140d8403424140082000390b06141d00a442c1c241c803040d0003802503145821010000120481c10b80751201e00c50221103580d81d441000071301400d42000708490105503200251140c0d40000309441800a501014105551400c0c241c04002c0c40000c1042e079002ca10340d10b201040381c615070844c10002c0b11b05c1d4004200244144009407281d444800d28a000e81c0c60701c4020008a0444924900c0707683e4001c00c017507038441d0011040780c91130245811010145203052606020150807040322800c660040d1000340d05503480c0040040d03451022680c40c0991100000043c498444030f5080040c0c48000608015071010161038004144400320340440d0310717656800c0c0601107803038040da11603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720624847 1250 720623597 720623611
    0x30c0f06090b13030809010e090108010c141206010e040b0d1b0803070f0b180f0c0301060b0301240201150f080c060702030322030f0b1024121d15 64
    0x1618250900e0b1031680503810f00c1c07101411032031004c40c84246580c8500070700389000c04000c00c12003640d41c444004500900003071303d00c00b01154146240345450400b040544649032410002000e45503151401540c0007200026110b601699802c2108440e503140c03c007a07001e050062040640c514032981030f8441003400c40c0c001068a034030a2006800080410f0040c100d82ca512001c40c1d40103481d480040442d14852103039000d024007601950310f110583c00906500100b03411802404179541d02c0b40015110301c428011b02d403450f0300f8010501d640745241038882400004600c0005090746900c94130003c0c000b03003a046000750590600c42089500307400c01c01d0f0034036404100ca41034500302c40350740005e50380c1c89003991210840c0440c00f0b001c040003402d5410034000310342001204039a400303545441d01e00ca00c0103c1d00c81800c9596554003003418203411086081d4072040c051910505501c1c42415680880c070700000c0c81d003581d229104080d0408401e11901c034880c41820081140c05200b0107a0108044028850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720626097 1250 720624847 720624869
    0x506060f01020f0706030207060b03060708040506101d07120f0b0a0e010806040308190203070807030f090b0a2a0c02100f080105041a04110a02160e1b04030c0f0609 72
    0x3070380c00703c880030a00c0c5003210054103005076180714070b00d041e2029264641c0050303490300a800400020b40d40119400340300d03920030b00a840040d92800c06885a0070308500030822a4032041988a0182030542a020b0308650306060a011015020005005981c01e440c40307002925142e40035481c4505040341c4490151000704c0140e59150704080d050f17580e44074005d1024040000801c0443c29280383d118071443d003904001000c1d543c0c0c0c80c0034140074044c000d007a50b1b8200001d04d0701020000000c210700c500326209601000b070a00c5500e641482201a00c0600d01340c1c400040d407944074080e00c0310f90318103058100e4110344804040c00242c2c010006100711145078141444466203400c02900d1340804514103580d005c440024414050072507400d244942e00e02e215400c1490034892013010388130503000d098605c4055007107804065030340c0c1c1b070180c0c1c4441a1058856120040c4d0214070340f0b006012102c48103001e0f517814581480d590781c031245550b050070b9220035020510744c50107005555102510340003a0090100c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720627347 1250 720626097 720626113
    0x702101808010504110906011101050705070201080105060a0c031101141f0e10031e120929070b04030219080403032d0c05030d060902030115140d0c02070f030506060f0102 75
    0x91060b14140170030804e01c00c982e04000120144e004440d072260410000008109500c0c1c5281c02504581c0544002d90208814000020780e0307140c20360484190506981d00c3c10344144041ea001d0359110007045054171507540351f1150440a07140450071910a402e4084102100c1c00154200300510031181c020074506101202004800850340f01c40b8400c5036844a03041c8812103140c1c01050894a881000600301c0002c0d005c10942c80d9400215281683c0d054000046808540305204002990220f09010b80840500001c03000c1010580e42d69406070090040e910b04844000b030900c05051001d10071940c0a0000c9010701c141a071000407030344055141e50000c1076480051151401592054140000b049a2104070404001c0244103031031a40032080c00c140f0021362203884250281d04240104003040d00307001200c1202e540301e00f003494a10a080d52109107007410410706a005040d013004100194458840001070803004209144021402200601120308180e42003160081000e41c00e07a04640c00044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720628597 1250 720627347 720627353
    0x1104020723070e0c070204110d0f1109010c02010c170415030c170f040302071a071104020702150a0203040302030a0f050d0e090a180c03110913170306060702101808010504 75
    0x8807103030013044520000743c43c0e00b103500c000b801900384503113441c50702031002c00c40207005a804d030010065440d200f4000c1c40612405c80d1201d829000c0c204072140018420440c840240d4000c4554001240c011345000495610140000056500a41c46000f01d6020100d4412601d0381c1071080c0d0b1510380852401c140d800c4840c0d0306a61441c1c40145c0311190021084004c9810140200001c000501180080e0b00345118501c94040b030680080e8810b9a12210010304815640f81034400c469049031b00400104120407184c0342d441c903d80000c02c0c00c0c400c0d8481041301001603602000750b904500c0c03091803144002500e61a0550070301034a0075851050040040907c082956054030075544401540000210031440480c2134102c086820310150072180486000300a1180f1542002e518100a49400b5104c3e2994045d04207124400417000c3c2008141c558015034540303203e0011a0442001840c8600b40700e801d07000540c841d482d019806000ca81d1002103e04bc4030a500c003054020219100200520302d0691 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720629847 1250 720628597 720628619
    0x1050307050901031503030509030d230c0a08032406030f0609071718010c0203040b19031e0e01050606090102060402101e09060e0406050319110402072307 68
    0x1038429414010701103086071081c3d00c2913101c003081c4400008004419a130b68200900b060340714600341c1e8001d001e06200e030300e219030244181c2e03a9104e040503c03006403d01ca0300e009500b20b8000c20313246800d5000b070703d407640702289610002e54090400041c0c3d141e811240402130301e811009800030240201405d0040142c1c1c000070b510b0382d650010081e61020115561f094044604401804440c00300c1400302041c48034000070700426142214140f4000c004c1e9031603940c1d050781c0d41d0050388103004030010200140f0390000c68500d0b102159800c03504011800500b01207000d1041c040340c800c908141d603510788495025060074040c494119205a0300305141c901d070100000d4070340030002d0000c1c3c01254910751750070907144603c0d03210311a0340c003622074101002500ba100500c5d1224911400c80007400544171000103107054400c040460300024018210300c10100700140901943c00170035281d200040d90800c0702d81e1200c0c0010031951344a58000d0400600c0a5402807480a40100d07011490380030090074082a8401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720631097 1250 720629847 720629851
    0xf030b090c1e1303080c01060801090c060f0e04110a0207060e0d06020c0a1403030108120a050a08060f21070f03113105090606040e070b0c01090812040c080a02010503 73
    0x100c001ca000c0c0031001c0340825118850100340c08100544610300105000078640905841b510101c024010590384e0079140d400d039541c820018082c107902000803c502805041d154103100d0cc00e0a281565204407800501100c1002c01550741a4000003050b500103a410700464000c0c000078100000300120b2040414545412003400401d11a8001107600040e0001c022189d005584914440318084000214913181d80081c8515440ba00c1503030040340044029805036140ca25090340da9034103150401c03000b00c4178024080e12207500b0406064901b040ca4881c440050b4416001d08003c0c1102e080c21480d040c47e00c0d2682c0d000280008118105000040c1101c201c0449401c0407074040c402c0b104800356214685a07802c107010011600d241181050003000d40045210300d0742d01040d108145d40c3c00042c01705951075003100210940111a00f8400d6500e8180900081c80119000141c50348181c2d48500041d0f0001c054044104205000c000070030411800c1c940203010008080d000000c0c4a034006401c5000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720632347 1250 720631097 720631117
    0xf0201020f01051614090a2c01060203031302010318060213050102030c03090402071a130605010501030c0804021005090405090120040e01030201050702060733021213050f07060f030b090c 82
    0xe117007000a02e1407065015201c0d0340c600101a00c020603a240c4a020040d03001e465041109030b03511000e00e00301c640c5456440c0c1203801c20380103589581d54100c0342004001c40b20350124140755451a004400e40382c514a0355501c580302e0750005a45006080c2001003280d04c2c4e90140c1d04551081088001b01c08001c001d0b244020002d17500561100c0300d13850f00a501e1000c07900c900984141d50b00c00c201d9902d40528031403010303030b018910070006662504011000d40d0703000b0300d42d0f4000c548180041401800c008800c00751915141c0750141c2021810b400043c10380d44191480b007000d1303440d10719103400d40d00d51030b401d00d80703100340c0c0301105103890f141900c1d40f45103c3e01440702070305100e130110306a0f0a6440c5e06c0100c0c3c45042e131101181c80e00102035456400d5801003011400c0c41d80d100002284100c01c02d41c42207072080c005030b0700030b1101540c40d426041498180d07da41110940204007000c0c0980d1410046200500000d840303e803084180d4101c02021950502401d0380b00c3c20100c0140041a401141243e030b540d19 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720633597 1250 720632347 720632357
    0xe100e0915121f230702031603081f050d060c05070c0603050f010f05030a02090903190f0215240d0b130204061a030c0a09050d0f0201020f010516 64
    0xa01c0540c00388201c04400101500300b201500c56428822010950000e801ca0000f0310f9030000d90b40c0316400080314820501c2c4c03901007520542c06000034110454140e44107503180304a900d404600080c1c0780c4165200801100811048000c0c0f00340c2e09a6403103407501103034658101918151400000031a0755000441c09070030700781e642070100d44046c41102182c40c00350f003003c46094040d42d00e002c010000d0000301c41a210807850440041100c041e105803c10807503100038028010703003c15030204440640041c02d05041d03440100b141128400c3c090071545140601c507121510104104031004e030074801410b101903220007040c410040010140c6200310561a800505003040603c4039000c00c8580483c4030000c0c0860070b5001c2001f015680c480c44010b1a18402d840074001145d50340030b90300c11062070310050000000180b002032290f007540000b800c220301c407038541101c10356501e00218045418500d0241c968280d2010390b03209558040004003c8618840001c0040c0c0c50106c1d00d11000ca113282c40b00340704000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720634847 1250 720633597 720633601
    0xa231203130f0f05150405010c020c0f060901090f0b1e030403022a03060406021909050f0f01170a09061107030806102304030c06080403080402010c02060d0c020a030e100e09 76
    0x5440c21000c0f03440e501908854005108804000d44e108003224100c81130341c200214945803a00c00f0034805040d110103020403465056140410400d070300028030482c1000310444000a24840415061006080f501c0c0140c0c1c0d94100120642100200800350001c448020001d110000b580054884c0030303040c6144421a51003034600b0b01c0320080c0182070302a41c2c140710b44010b0000341708040c1d004101b114030b45120f0b0048051400b0095a0b500c5083c4981c80c1e102094101050300c5003032505040340c0d4a0414540380110f581c40c1095150102c0c1e003581c141900e1070362200d60030b00b0090b003442240703481049035503000e003098030b40c0d5401480d544005100d28080c02d80205007441203401001040038000c0d1507001d110b40044258808003003600315110644a803c2001400120240143c00c01d602071500360341c0300442580d030b9400654a1300085141242c10010400480c0d01c2085540700b0115101c40c0c1da80a808185107500f0010411030780001a04c0c82038a4005171003041c075030000210700c0003090569880602d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720636097 1250 720634847 720634853
    0x90b0301051e0904061508070e0f09010b0d030819020f19120e0c100c050d031a0405071d10170a0207060509030301170c060406110a231203130f 63
    0x40000124070301c0e0000f41e0f030028402007280c80e0300403100c002030360740440960540d01c0c809195203400d10701c582038003030000c10301244c4103108004020390f0100c400300010840f60040e90119100040f05581030340001c03884000e1081146850490198401d1854400e60078002101340100d81c0340304110550347c06219903401c40d1442d40c040c940c0c142c100c0421580401c80040b0164802e03803509984404244621036400c08400c0c0140507426200c01a80c0190040c400d070030703042a080c1c0c0104060106100c0064607604804125551406902d00c54949a500c02c0920046410011052004200b01a200d00b11800603020f86c0c42d4413210500001c0705414121600b03444000400000740301e1110050031544c02c101c10000520000001141250300c030698402810b108000d444d03850700c0e00b034505168041000c000801009202d030ba20141c00403000070613524002c1c8143d884071108850801c100c1d2110440c0901003511002c2407109004c0c0c82443d0901600c0c1d03241c04000110484841e040041c002031000c280c55081c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720637347 1250 720636097 720636139
    0x4150621060b120a090305120c0f0414031b091b0706020f0a1701030b070e0315070201060816140103091e0b0f070e090103082d0705010606090b030105 66
    0x903448040020004561180c012500b02d074800d5488116807050440460b4440106100d5034200c680c140d501c050400f8007010406d000c090340a00030403840d00081c0100b52180503010000c00c010045072400d007000500300c106250401e152840521898a80450301500319180e8900003a400b003004000943c1c91910365001204a0242010282160384003095018180d214103000301180d4040d0307100c1200c80c0390308040310b41966038240001081c56000c41d02040e0a9406881229010440101a10058003402c4000d05601d0b40c110b0750040187c0d114030b4104026007090001060b0380500d100d03040003450412090760709200f00070340398ac1d04069482c18010140305400ba1040e105a20503400d1004c000c0325800c011800000c10341344052031609404c0442c044030f0040d0110202c0850103458551161b185491b127001c25045101071200034003003140314151100705514060300c2d035031500c002d250f10382015081c29401c54107150460014010281d1043c00f8801040c03003038070f04481d030454079000710705104a6401701c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720638597 1250 720637347 720637397
    0x4050a060f1d1005100f060c291515090609010207050303071203050f040f060b030f01150e010b0a0915210906150b070206070609020d03020f010506041506 68
    0x4156042c4030510103501000300d65a4904043c1e60824030090b1142000c614840d4030b240304058485640038801c004981c003501d01d403a81d4901403d034401c03800490100560881d1030320301c20705070340b400c141c4200036048025a500c028194010794194540390386444440145108460300c6911641020852045e9a8402c201d040040c004c058180e0380c444c0c01903d44162141c82c03104040d40482d041c0000190700140444007179106582102c050b050121039a2140402011148c01d10f0b03406008080195460060034010344018251001389040050314040b914194010f0603081141104420040c52404a900035200029510a9210581c0c0509900425506460190102050480d9414000280040a40c8403c800501842c41445111034500089429000c01e000d5904000001c0c4400030150400c03078040c20801c1d11a08001513003003c0c940000380307a4801e410007140142d00480702246080303004e0007815049807058405005000030140341d805030004a00400c020040c191007801100c682a0803000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720639847 1250 720638597 720638621
    0x2d06030a0609050f07050d03120504020f061b10050129220302010f080f1518011203090f08030307030f150602010204140607080301090506030a0b09010c08090604050a060f 75
    0x14402c10746881600c6a4082003039080314020300740009854100300d01c0040d10380703034142e551604031548203000c4402004054026a0442e1580442c101d060f00c41d14010485c41044c6c0710b10310b1130102c07455070785843e04904280034080281400010840211120b0b6031031028440d034504040506a441004241401521100032101c410341101481b07200d041410030094078000e0340c0d0380e07a000f1419541580c4004017a985010302c80034120010702442a44450781046107402410007044080303410042403504000e07001049060b00100c0480105900320b003c210042c0002c25003451482d2030040010b0312400000c00d40020315441e0040485030448a070b0210009120b181b01c04e108580d203801c0024003d42050060798012291820280440c1c6010f105039134205038420f0030f0700d2440e07080c10900c001900000c3c100d0f58140c406c8500100000d8484002944a40d070342400001e10840000c000130013a013005020502190048814440851004142c90340d0032a013004001c00e848080c042050000d001c4400c140b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 720641097 1250 720639847 720639851
    0xf0b04051c05012a051306051305090c040e06180a09081210030b100b0904020d0204150c0203100903020606101803050f060106141c020f0c030309062d06030a06 70
    0x80c0c40300080c00b526622100e40782c0314082112240c1c890a40b0f05d8810242403101c03513201d02c0c60803c500b40c451002481c00001d801061514141d690001c5103110b0b4055424000c032140106040c03280c0200c1082446e4071010440380da405129615000c004102d00142414410a8940b601c020601c240c22088452a050030900300c4000e251134450520380454a010841d902190480801c1c030b03111007101103105403071031070b40d070207140001c6602000003d60110700b0b59041e07036409100001e80b030f50059070245080c1c00580c8448090740114410941441c080354880140949841242c4020070f0780003820982c01541a00c03496102c12600e038080d2a0340001400c0e149190103440da01204000002c01c1c11621040c03981e00703c40160348c03150070940d40c900e0302c2d42d03610303200c80014032054600d01542c0e991080c003105400801442e0242d8050801201d0b800948001401e40c400018050480c6040080651120f030381c0004109040b145104c1c0e48418031a041d400183c41c00b4000490410743d021b0000180c129442801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 720642347 1250 720641097 720641111
    0x4030f020a0308181011120d0e03040602100b0603010b160609240e0a020d08030a1113180606270b07030806100c030c080a020124050a0f0b04051c0501 66
    0x7040c1483c204541018042c0c07100c0d00d020200a8007a031407031006d400715480a441040a121002841c0303130040b10618502c0f5483d0031111002c0c0360284003e101502e819030150945140c00c032003050603130724183d64a50103007004100412500f170011064135a45544040f04e661051000c0c28860083e0403079602c058020180d0b90341600d4440559805401e50680b01d240901c80a505c1d00420b0f0788031500043c0181d0001c059022840c001001c03480210f07840340c40c4c0c9000003007003268010000c078240c005100402041c0c035001428006880135a240e2101900a03c20a001450409000600f40400d480c00b80e54960f20300d4039103240c5424460303104c0010b840989202a1a90f00d18100103050340403e45030540140c07100d01d0850001e0348129209020141c042e1946c510020607a5500d16807a44000b1841f81195a42c02c20242e40181c01c050044c41600c606141075002401c000030081c1c1001c1a51026030180c01100c0200000c80c03000b070a50b0104c0300c04640400100180a0842000c0c401c0024010015481c0c902 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 720643597 1250 720642347 720642367
    0xc01060f0f0f08061302130e15090c01020715050c010908181002280506041202010506040b0d06020307020c090a0f0c0c02010c0f0503090a06031a010c030504030f020a0308 75
    0xc44000c44410110189079a640d41c03146454203081070059090a420440020f414464140300c90803405101604400c0d03082d80c2c0d80d1410080341c4000480380020b400c00c0d075481c0b032412190802d00e50896180406041c00d6800c460010f03544003854460b054000c0420501c500f1058040d0050703400501d9084001d0100c08800d00e440e00c0154410f4044030002c692400702d44901d401d15020718030702d15031250000d0486c0c5102c1450000d03000380c0105d03285141d901d0300d000f00000440078000103001c1c0744280e01e9440c1e900d00101c4040e0a580780100107900643c070b407200180c81d950724003580440c2c0d5a00002c0040e540d40300c840f070481c01d0407492100590441d82e45024880e1821b010740c03020f40c50b101d0101e0100103841610b00121410b0b580144081d00041100c0c443d04003040009005903000e51181c1d0451303103411404404107150007819440100405d583d040641d0b0300c02890400d40740060300074a0b09807555141546c024102c0d0049003c0908040a0281074408540700c0a150201850300f25880c3c0e40c031151070b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 720644847 1250 720643597 720643619
    0x415020f0f030910050601050a0507050c04020706020702040b030d0906140405030d1d0402070f150b04150501021b0108071413410f06070b0a05040b10030b0c0901050c0106 75
    0x9290400c0620900054041a091341d1107800d0140405030b540c0fa24142d14000111415008040155450300501c90044565a40c0c1c0c8001c150f524440c000c00750b160030b0f0034010002114900c400d403e0180e00a64110200141c0c0301c010300c0242d4016003800d120394031410003c88003d000b650000354061044154913601e058012120790203003001c5d00c02d41075082c1100c000303101c260300403000e00510302c6950000300800a403c8191007070f464030341041c0011b0398440000006007a50b02802c880007403404021004c0c000e95906021440c111034100308090058040100001c000c0380d0001d240c1e90410446601a070304440c8030600f112000d40080c40401c202c5500c66043c0401c8aa80c402c49503401010b0110b5000d101e04002c5943c031500c01e8801140711104a800140400603061a08131640140304000c7c0f01b0000e5030080f03005001c3d41040b0030004840c5424544811400b002800111507091048005c0001400c402249640b03c0c41d0300301c200d92115500e0300180c03018040d403050311280c0c0d42403540210760f4400c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 720646097 1250 720644847 720644851
    0x1e060a09170a05060711060103120e0301240b030402060906071a0916090510030b090a081209011116380708070302090a12140d0f14120415020f0f03 65
    0x2580070f0320b00c1170310f6501d415190000c1c102c0e8500300c0c540100d401040410640c101c07400c0d07091510708120015940e1600000c0c2186d0a039052f0145140b48040c64901c007041400c1e601000d4000b00503850700e903051135000115640100801c00e4400c405c0000d803413041003000300400c03200d50045855000d403820200720791510344107214144110390b110003000042802007030003001e0182e100790540760009030940c2c490400400d002042100c0d90300c2000e12041c00100030f040280b50001d09095031018900b040301d10b481c04e40d1640da03601c0400c80c20034081951540010442e90314903a600c00700d240314001003500711400414480c0c00c807400c032020038000503141e1080000101d215054030744c0c40110541e500c0c5e200360b080380141c425a40d0448e92894007401140021080002d0403402280466000044030300303410700d40307441941000c0004840c1d0b40f5603025103030043d013142180320007008042d08290322000c0900c81410001c0002e46a5620381c80c43d802d8800841c1e0442e1307000e02c1040c1c4015901c0c1d1155480001a42c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 720647347 1250 720646097 720646103
    0x2040b0406170a050f070f0e0a061218031e0c1202060a152907051c1b0b0604050a1104080d0806040c1704110301090b151e060a09170a 59
    0x6440b0028030b0601141c41154458200500c503d101502e0741da00c104c6100b919081c0c0308050086103080c2203856600d490603600100300e565582c4048002c01c0e03a17800e055540ca0b82010140d01d41d100b03407200009801c881c040e8080412403881c1800f039100654110b400c40c80c0c80f14007404994a0b902f084500d00c1e404130701a88100c00c035210030b10281c070808070800000d18007446002064817414640781811940382c90b00700c000390b85803c5000c1c10076030b80340c4602c0e09100c1c01400450b50408081c0860102e20741010740d2201280c01e00311a1107010b00641c894410301c9900510b030600c590b40d00d10001c1c0c00840c0903403090304000650401e03103888548600016a07200304406040e0041040d00000900504c0c0a000301c1d100d009445d07407013803222034101c201c424480d08050422100003d02c6185682c00d524244201003286006044220b0703141083c0722814429016440d00701c0c022801c007850f50200410602114802d020f00392078140d641d5210031012250002c81d03410032001d01000440f01062203200241c200c8260340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 720648597 1250 720647347 720647387
    0x90c08090c120606010c05011b050c07080a08070204090305160c0512060c0a030b01050412060c030507030b180604061701050403020d0207140118031b060e030c06030109020d02040b0406 81
    0xe2503000c00601c110324101c0b5510300e9000100060055204800748840144a20000b0540540c0c004402c0d0f0005005068200010700200b08641120f100b0440d036001406120041e180c030101c2600c4000f03552066000c044e000d9500c48890004141c03140007160b03070100d110100f84000780c000c0d141c03074400090b21303100d4548584902c14155100d0503020500c0c5d8025501c4407a210700c0c181141d5419005061042146030622806000008003881420189440c55121300c0d00002d003500c0707404002e1b00321400079044c01c2c2018078001040c052501d44900350401980c11001d11115550b58000107000703029144c1104218444e40c00c00c021741d0580c1500068010752182e000d030359403812402003c0381d0307500301449129110601c00f10120b000754015120710743c03c01d40000c10742001e19180c0c1c13581802c882503054102c3c0540c5001300c0400800e5031061640c001091b044010f4040c014190780081c030a4007040c040c40810741c0e800262000400255411200245900324100b52210b954460107000d542e00c40011002040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 720649847 1250 720648597 720648613
    0x2130f05031912020f060c071a01080307030e0f10090807090207021f051917010b0301180506041d060f0a0c080a0e07030615050411040b040b0c07090c0809 68
    0x701d004640980301c500a4056128060183e0310786404a82080b0010702c190300400d14280500c0b01c4c24041503200f1101d09882c542d0700c90281c54228040c415200c60070700344414000052180081c088103c600c01c03030b010701d01030b407880c000c51001550410701d0180859202ca01c098200d0441a004111401190309440c155030782580e40e03202840070b80c420400001d40c081e004a0542003a60608540851280068a40f9908210b41c480200340c440d2015250080810703401030703583d030151401601e0b07035000d1702d10204200d003554540700200c2894021501151445901c8000060f01358841d07510103005a8035052890480801200b5566102c52040c1c8900c0500c0c4400340014005140c18060501d03083c0056031400e116076a0039001c44000c1c0680f6010300c881340580748000002c200c5c80d02945005500a801c0684194a8182040100c40601e401d030280c48109200c100100501032041c2c40880320b4400000c0d41d0b4402a400da10305281e9542c0042c900781d4502458510a20703406001d00703100d81115002c40d1014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 720651097 1250 720649847 720649849
    0x3010801090c0905130f05150a02032d01150509030607090e09010605030d050a1e030b0f0103051003080a0c05010c030605040b01022e020c010207050c030c0a06050a0f09080102130f05 80
    0x82e4500305d449030403000103580c1010002d0083d1110441850065044d00d81c00400b22030114008176007600c40e444000e4020051211140c44003800301d05440c40408690000c4c0c00780311038030448240512818800103034054950b00c030640a2422a02a22002800d840452400c801c003d40048040e000d035296443e442000a14044014031440e010b49000400030920b0102460b03085800d030740101c04220070031a140d0760301d0304001c0e009200850a1001d540300843c0c41041a800d00000100003015a0b04060400307042c020b40700e0180580b0760980e500204c59960744c985440080c6c0381101c035603000808a40c64041001040c40c0d150340b0a0043e24021a130a02290001d64012a52100c0038400d01130919660700710b02d1034000a0f1590321101c905024005824410000741c8642281c000d98401e99035900502d4086a031b601d024864160007a100301c403c00340540c10080020413a005081c11981480000540c5400050140605ca001003202c4002596502007281004c6031001c518410704020000d009400705907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 720652347 1250 720651097 720651101
    0x180108010615021b0a080d0207030b1e040f080f070507081011161509030c0b0a020403030921140a0201080912090607060621050d0509060d05091203010801090c09 71
    0x2e0740b6a6009000015071844100c40681c21007402e20b42c801d05800c0d0010307a040082c406000e0000058000d803044519604000b901f00704c0c004d01c140580e07044011f0640d00d10f140100800c4d041504440902a4211903280c0314030a442411614200c180e00803840e0400c03c00001a0601611303e42c0003591518186c060203082901c111001c2c00a040c0f50600c2145c81c1c0960380e02d012540305001e41e0840e64015495003a0004840350440d0560014520094840a200c0c850600b02d4000640c80011072410f840e50b140201469130034018443c1090485200b07510b6812401c215080071034110b4000400000e649840c1544d03241030400882c0420f00200000361101804107125010010900300146088843d40c1001401e60020408817002544d8020114a4825030010034111b141c00803d04003107869542006031401800703a841000308001000190400d460704400c2e01c2c100540f594020030542c403012951070401003003000740d4100190200c000a058101500510511030050341e410140940322501c00e41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 720653597 1250 720652347 720652379
    0xc01060614030612070317040609050a060503060d06060f0b0a021005101502120a05090109120f0b06030c030a080a2a0b0408040b0403060f050901050415020a0302091801080106 77
    0x1003422001c0c0005883c50a00c0740b84200b104615005a0b0345c0709843e595409220307002c070f582c0c184904202180520506400543c03071406401e040b500080c01a1070050010300c0b921004207c2e500a40300aa030306400c01c00340d48c0002001d0140c800d60706180c55100d500490070750b003105c4a0f200052080c050740e0040c5034000e105035402903026444402c05142825101c10041c408070490400b18441d0450640390014210301030080c0d109240d40c0c06640f100c0b00ca0004001080d2a0410600c100442c003407503001030310901d6481001076200707120f00307199900c1030700007420402000c4889070140692003c4100300300f1001c00503c003101c0a500c40802241ca601c5605025012100b0382040342c004100310000803a41c445603850340300b44985400b078a029260b2000e031079070ba04075a0088031140d4547c0008040100305018541e4407011080080002c3d1829840d5004807a400081e0840f216a0000d081d40c1e101e8440c0c1c0440e03d2507040541600382c5642e10740c0b0140c507880d10034407030f600b059481d1680100b048041000300c2d034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 720654847 1250 720653597 720653627
    0x150e041112010b030712050a06050108101d040c0b2b18150204050d0b0604111602240a0e12010b220b090103030c1b08030f16170c010606 60
    0x1581a030f00f001d900590315403003c0c190f10103002c4040c042280c1d010b114005e040c81030002030008100c49140100240c000309010f444a541710003010828081c4108414014000998201041e403240e103032402c14003043e0960760400c80f0b01303000018285174410f6400900e4400c10321000d02c0e400c03468201c2181c1004507082c24001c1d55104400181910100d440f542050352200d901c01c10048c40c0982d45c800007060314a4030b2100311031820741d0808000c1d031403410b4440c81070f915010143c501d00e41004414042400d0a40c404002d1003004061030425103819214101e000c00a00003111541e54200d501014102c0c1d109007070b451f8070132403d101d986410048123004410201902038060034007500da41d007046014500d401d903e049030329540c4089072410340d20001920300950198a9044510311340341444818030702111500d4148600d85a010070038400c001046a100f1905000c0c255220313040c480b0010000181c130080a06509a00d150600103a00c03180c0042003c024208000c1040a0342c1e81d00c15511030310540103007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 720656097 1250 720654847 720654877
    0x1e1407170714121504060506040b0f0907020f06011e081605090405030712050304150c050d09060f0903090e1018050405030706090308011706010b1b0304150e0411 71
    0xc0006040c00140500700000042c1007400f12680000150300e0b0108a8103c50f004070182030900c420b0005600c56503800c1030003580c05001c09135400012505c04d010300300a2501030000c041c000b0346603610901248403080f2040051300c10711f5961b901420035520301850110395402e6809070000d01321038000b61484000d940d6499040f41c0301d14010403c030010b500244152214041080420700141c01441c810712508100d440c0d281e03c03400c250410308003031404055a09115860001d503600015000002e403102480c075203202103807011032403810784090300c00c0c00b404450309410880144205600800603200356003102134011541d603070b048031821001e09544648452216036a84c00d56100d0100c0d00305946c02401503048a14180c02036603500111000d4090540c0058201d030010700100c02d0040d801000c82c4c013132030000d00d420f50504407a21000d200d114444012200b070000710103080f1605005440080840c0034880006490101c000740030b8a1215503228410f51510718280800f0303032160f00341e135102c03d80c0c0041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 720657347 1250 720656097 720656099
    0x60905010503010305061b13150e09060904060f0608010912030c051603031a09070801030b0c07051b03190b010e0609150118170f07060503160305041e14071707 70
    0x107c81c3d060903030103e072040008101d40da06416447d048035008044591040e0301c5003024080082c0403069020101e0f2103a4000e4061007600d640702051942c12541102000400c0c01e40103620400509441e4003c0800d035081c24aa03d05200800c61500f003070024544090011a00400f401c561601c2414040905c4186088442e00840d11944c0501c0c280d400104286206450700700010705c1c0c0c4030089038050b000448940c0103008201d05c9070f600941000d404010103080c070255503101e82d01e5071500c141800008988154241e2507990030802a20100d03900e101c403411080b09824401049502401040c040f5030208012908600b00748480e148601c01c0c001d00f608d02458400011a601c10104c00e075039410380c0c902c00740032130795171040808480c0c80c10b1480024244547c0581445050821562000080c00002d2041100f00401c1010f180d484482c1440c0c002061350712403401c80c10010400b003a8100014045605004200c070321426040d048840f8000c503247d503961042e0310154010184403648081d0080d01c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 720658597 1250 720657347 720657361
    0x203011a330309010f0f020c0a080906070804030f0c081f020309010f0608100f150b070c030b0403050406080f010302100f122d020324040e0f010606090501050301030506 74
    0x786101ca00720801d12a184645103110202100d800c1916080220b9541d13200102c09080302e032051054034407401c082035050548054619440354000d4a019082c0000050b001d04969200e00c21114002d5010180a84654803424035541160404004445581594038003042d00d01c400240c00d003c400082e200500011081036445001e0740015007c02c00f650b407200070100d0507103c54068003024100101c01402074400074822041901c0b569060300d0681d515214842c11002015640c040a4a080381001d959a502519080c50204015031001d041e40c0c1a03a4180420907074070500520445145076100c0b10309460320326200c00114000c2c032000354000c16520150b0880c0d4050f00440301341215030f040c02105000000e00c0030007a03400c5038481d404481e001704801d24550010205115109002840460645c908070100382010f03030790308001d03800c0358030308424034031143c1d03a550030580c0040385220581d203c5415108696020785460300074140032490011000c00c0d2035100d80250382c100c94000c4000c2070907480340c1e6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 720659847 1250 720658597 720658639
    0x70524031b070210080a0c050f180310050a021201080c0330070f1205030103030e010c150e0109020123070f080c03040816061106040318090606020304030203011a 71
    0x1400c88282840100003580d241301030702406064640f10444103280c154049030803034508075038030700070310100340840b0304090050b0702030315140300e0ba8100c0840030710b200e00c002901c2c18034003520038010f20b0b06000400049403056006083c26040450405917140d80b035455554031860900606078040e8081020f400780440d1184194007962440710840350200031071a15492141e10000080d9482c5c01074040340f07820090f2091810024019915086040d941150740040604480000c950704000030b01031040c040c017481800120003030050707000030840726140c40d40c418060a4aa00e0aa000c1404040c440402c006140c0c0502404840c1541c01850510703155144001043e03041c800340d0709540240140203482c1d40400042002c0c3c14003d00402d0500450310248060f00c2e80ea402c4442000550920303444052400100c0307940195240c01c00a0485400d1864110304401640c858402c50341003000008000ba0040010700a80307000350020312920707801c00382e01c00303a0035020909980c0245140d8001c1d04422030a07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 720661097 1250 720659847 720659881
    0x29011701030f020910080307111201050f0c030a1107030e0103271b09050f040b010506070b07030f0f020d0603031205090703020915100305062d0f0f030f07052403 71
    0x17142c020103600340c81301c600302e1854000010480380c402c0d5000346003507185014224202c2041031030000740110328180484441d5008060310065a054010000c00e441f50103d4001d80c8010b00c40c2802140c644200d03080080000420100c01742c00301c0e1030052035075040c001c080006401c40b0703141e06402d0f1700e40101e13683e540961603c0702403100854414601c00b0070b21403014010355001c5d0240c0700c2c5125a40c01c160820119207541139000500ca40c80401070707100012160069282e20010504000401c6d130780044008025285044c0703500740881c80042d40c011841c80903408a4203880c000c2e0b444183c412800321820040f01d40c19281d0f009141e1010004000510340381c1402c0d540449410002c800240040c3c0c04681111600e40c40800401d0301c51042240f40d081000c00481c4100000c034000002c900a401c509210154090495004040341509004107444442c8c0d03d21140c003004c0c0446045000035141151560300341c1c06114800c030540e40c1900090024812814003c1400008a900c0d64860010000340d450301c3e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 720662347 1250 720661097 720661111
    0x8070207060f050c101515080108150618010603051906030507031103031216170f01061404050a081c1806050a09030506090f2404080d29011701030f0209 67
    0x4819500000003030500485108055003000b0890aa050030b107e141d04200241c011010800008010041803400040307014200c0c5204203000c0c03040d2160300c08601c800d0480d1a1800c400c1008400000f40c06034190b2280d40704d56203c00710b802a072049079074000c0640e00f0324407014107140d000b070f4402c0c0041a212004107820380f600604881c42c250b0920500c0090550441d10031150001d0391b010340d9441034025005c0d07815500d2030100074042d480c0c8103884458080703041c003402040014500c0b000048407180b60845000d4107004007050501036032020706036981c1d9822000d002108800840c1c6180017070045414504042c03809000f0140782d170501104845982004140070308004402c400000460f0050101900529614001d89020140c4402191030003102c00d0785c082800c140c450441111031b060b0148503030060351001d003150759460582d082c0b90140c00069800140105290700349504949100d160083c60403003a2610000140c0018048e44100c40074403015018002000c0308200514101e0110391303200d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 720663597 1250 720662347 720662353
    0x231201020909010303020309101b0f05012415080f01091e0212041703011401030f0e03040806010f240807020f030409020d1b0c140c04090b0708070207060f050c 70
    0x4414000282c20302c1080e841600980c00000d4511050b040c00d02c40e01454110f5810562205401c0f800c10540f6058100e10180295507881403800800a00f034103e1b156021071a01da442c02e0407981410030200c88042d104003407007091507400c02c001040c0506049031042070310030094110ba07031800d0407100c082d20180a82494960785030900d204220040c1c80541302054080340007441c00e1900389406003c0519400840d2405c400910040011035203101d2252100c500030300e0f02203407110300008640c1c003501d00d00500d030010380000304004c03540190000b6141d0494500036660400c42e940e402101a0001542c041e10b542180c4415600000600840020350810054811075203003114120707640341540c00c0b49e00725240301500095644000d9a9a00a407120703d600003040c00101000700401814441d510f410042150690505d04c1c44403c0060100c3c0c84080000f800600180301945000200010100c4602c004104820041074906100046403025210139803078100340e07801107038801d80d180d0700006c07031780841d501c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 720664847 1250 720663597 720663607
    0x20011a06070615030303020a110601030507140d020402070803060a0e0402010f0c0515070905040e030c19140a0b01031a101a07050316030f0c0c060e0a030b070c02030723120102 77
    0x3441c000380e03c4000314060750b0016102c102507040241090b8812042201c10742c404e00048c804201c01090342d40898100441c0e00c9810f140050200b46610310030030021358401c0c07001c107002c0e090001d120b004611034102190521403c40d02ca03048082c400d00240d0700a4002014168600c02e01070141b0030b00c0c013105001c2e07812924601d48494455940382d00440d8880001044d50b5420021800c0a00640c1074103498a40510300b4105104055a500d0b110490004014038181100c403040c80020014020302035100c605450705030130541002d80c1090820b110865032005075078003c0d41a821a011080e01425248155441103454050000c080c620684100d034400482040b190380090001c0000748502d88010442140c240e40d04c0c2009440000c240c1c2c0c0200601481074076480000e1801840303242680c2040c01c0404803840c000001c6050100d00b41c00062210358240d080c8504250402804210f0510850403104034640721380050b2000d200c0b600130306950051211000b552840c2003542c0b142d9a03264a40018140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 720666097 1250 720664847 720664871
    0x31e030c1c0c08091f02030c07120801060831051606020a0203070801060b0a03051e0a05061e0117090109050d050d1a060306040c030902060a20011a060706 68
    0x20009116041c00c48640e02c003424612030741c00c0141684c0c041c190101030030040031150801c00403036500e01c01c0d150590b135001001942080385041552491a000406003000d10351403440078040c002d0070300a0002050340d803000135140c0d68104030100d030300c220440007a003608804982d510261011080307080300c460146000450b4017109454841000f480c01b035005001440260050500b040e0a94201f401076905011083c051034820b581107600c07901e82b07440c0000d0a0340d66038040a0607154040c0c0c56030002c12820082c0b000d1082e0b5900403e00461049075285030740b812030111620481019050940440c0c5808250031480180041c0142c0c080c3d001400070801c00c0461750350714140080080300384013140003c141480280024421b60740320402c43c503403102c16030036020006661400010844e41c412070b1a0b1600040c1c4a20a800c507403001a40680840e880c0c132074460010705100c605240303204030186011035a062502d014001c09081904a064540c015044401400030681c042036081d106291501e16110341c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 720667347 1250 720666097 720666127
    0xd0215061e031e1f1b0f110307080d0b03070806071b020307030c080f0609070b030a20030604270326010e07090e0405062403011e0509031e030c 63
    0x16011100000e403545100b0184d01d05603503440c500c00c644440b403a0148408007403050440e0b0702c40313050b42d605090b503602500000840b00c0080070020703403004e400f010868408002001015141c0c5002995007844081071820500d40d07101410320440c4000c1c0c0c0240049910306000719071000030031619415080d051a050b40100380741080c0d40d402260440c01b101c900700900701091201703003080154100078048504001750300c1580e03040c40d8090700354a543c001001c00d039100d02d1a4044840e40510842c0161440075400481c1c4898204880c090b00980c10040200f0040c840504d11451288550700e90004900d201e8504079010105441203070001c0040030311750b03225504030020040c0249010111040d15150442004152014540c4084d8102d03240c401403000080002c40c0d030340da005100c585024060000c01c0313843c0d1110000c840c501c40d095440d04c500c100d5a046100508081c00c0e441400a01c4903444400041e581c0c1c0c800e051074100340d0440c0c0c1060300c01c0407943c100215040110451802d08000203034442c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 720668597 1250 720667347 720667393
    0x10608030901080c0f0306061813090203060703020f18150c0604021c0809010338090108070605190c0b01090203040c05100c0303090c0f080d0215061e03 67
    0x48564804a90a003141d03078091901544212680303625030034802d40311031110300c90102410061280c00d010500142c494208030309001c0d44080104444100c1c20f50a0b10407004208107441a070080c012417002801d154024000c6a419202400c0364a01e0120100c0c0341c0c09020303203061202503101d6041c1d058141c6145140014115001c10345003e0001401e00e403040002040080003481c6851340000c0c00c0c207010440c00001c2d0b4100403403e080102d540e4401501d04962040c1c1041d11011513044242d0240c0e08100da205804132600d000d03180c41d100c50f40c03142102a0740b80c0c003500c105000038400b0400c80d108034140c0d41c54800098041d09081d01c846203290307200c801e0b540c0c091b00290001d6901000b00070600000304401001804c2c06d881071003071084101c80c010840f181215021301455102e000c00c0d07080080c81518480101740701103400e41a80d460340c1d00c1c181c0b9034182010b400014407404406420740400c80d41e4060245000400c5904481d6820014107910880c2c5121a54540120703000c01d81d462904603035404c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 720669847 1250 720668597 720668609
    0x210203190e0d0c0f0c091e0e0f0a23060c032d4002210309040c022104051c02090a180510060e010b0a09090209030f0106 53
    0x100d18100100041030448100d4803404074540d00c0700c008210095040500c1c0b20b0f00903080000703407004014034201380c00c1c0750b0040c0d070107180800c1c80d005011450790004c6400304204008074074180031740003801900c3e5548e4010702001082c95000640c012000609801020929051031104000c00c2d00d40e01c0c94003414004200c80d090320b00340000041045848181c441e04503180f200c2440750f461400e2015029580340401403c0b03171030031b28600b120032090100076500d880d40481c0030004040041040401f5405000d032000049000701d103031101c0720f20305449989490003900d450303100860401154004100141c003810268074158001d0030442d0680225143e082c0300d40681c0c88041603581d500d05001e00040e001c121041c0c0c10340118000403000182c0d5101c0d0a0343c1c011228803c0407520841c002510703098001d010741c0c0100389111b00c42483c4440348003608010100c46e0700c10041011607a03074050810080c0700d602c000d103000588130750003441b4124803079004d800009800750803107600400c00c40a150842d2850f0b0411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 720671097 1250 720669847 720669871
    0x31c0509070528230603070905011103090d050a0605102103030b1f1e080c090301060b0403030309020a090c0c02010f0201061208030109050a060513020c01020f0d14090d020a03210203 80
    0x10f0414143c0c8030244c0f80c45104261091460352800c440c00802c4801c06005041c1041034060f80c11000c41d004205480c16040004c106950826291070450740da100a15012a030160400c4006494800895400804c0f42c0706080c04010200d040322643d903950944050403418140e072103020031400d0b200e005841e0140221040310000303003042010081c0026284041030381841014408843d441c3e90702c000d001d900410484a21b54842c0c0c54200042d014000b1a0003446e0401c60114002090540c50342101070f88600940354114840d07140c100103020348285101a00c04121180b0765200194403520b00000c00c81800d1000140c0e00e900c1e07869000440390b16074425141c001c004801031148814071b11034560480c80912081000c01c1c505030106060003401e4200e00e503581e502003040d40e0140b1007901140d00c8801904d000540e00c810607042e0500500c0110220400c2d02080e0000402500c00002d010f5040c5465800402c42d284850740c00303c03a0b4150401c0b030b01ca00c00e011909038100310b002034000356001e0180c0d0142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 720672347 1250 720671097 720671129
    0x90507020a05010f0c0f051b0102130612060f030b06030a0b1f140114130806070c03030b0306060105030109090302030409020708030108190201140d02130305031c0509070528 76
    0x40c2990418280702d2130407071a14040c45070700741d00041d400c007455007a400d10a88860000a440740408540341010b031541d400040d1550140b00301800c22416140c0039142d41140c1101511254121012401111648885001c00303001095804450755032082c0024211812510315603540c0c11150703425182c404d17400311224603058006185412080242c001c9580b010344407415900000c1c8044c4006594058501c40020440079a1401c070007040040c000c0340080320410700305514010b25545110401346e000038508907a0184902c1c0c0131594030f0140d04141c0d40d40b0304690038001c40b030000306856030040b001e41c8002c110016035201280058041140501c262548a62512419900745124071100040d0f801e0243c0000e07006030b0b0885080e443d000e03940b442e071549945600308014000d04c50343c100303600e40841c28140042000310010042040400c176846d0303800003e20070300d420b43c00c0e42c0702500e02c540303240c000400c10300581c00d112000e0548600c40f803244840341401c2901d84080300c0300b950041c0c01c0382012045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 720673597 1250 720672347 720672353
    0x60105040b0f3015010608010902030610051c14010807050117040605060109082d01020a090302131104170d1b061e06080c130603080304030c0c090507020a 68
    0xc0781c100c0c01078040c1c0d005084807011000040b43c03002600722012410954109061446a503003000311804200b1500b254140100d40e41e41809000302445030706c001451400011402c100640280c9000e840050401011000c41280546094114410311002e014184082150342c0c4840d0150030081003010b10f4003191075043c407000d01d0505405801c03807410b2144600606250444421400307900c60380140d00010581c4801340120f62802d100da01006961180c82102020f807852180d02900d55840c03030b02c00207540400c00384550300782e000b59240c1c400850303101001080541007000b04400001441400014001e0f6401003000c3e050300700d034200101003000b00555a00308201002002441c02017400c081c004041244040c80c160303120260f000346810348600c00c03003118640d0701c81034444e034100761101400304945480d4540d681e20010702e0103a21501c40c4502c1550140858070030358060300d40149501f469550745443c19104d14140d00c0c42140d00c1180044001a034004903c075860207103211b5030160000c0e480c242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 720674847 1250 720673597 720673601
    0x5060411090d0303020c1c02010c020c01080108030702040908041208130927110402220512030f0c030702100f031406130c05212a121801060806010504 66
    0x18034019110204000c510500d0b5180c05581c1c4107540d1628000d0396450346104114149010740c0d8110003c03204403042104042e4064101d0f5111651580c22030724ac80039504011200140b003031281c104a500208031040160515400c0803040ca0b009500c2e052400c1d83c2e8003148600c040c1d00c2d0343c003980c05603404112403100c03011502e040070040031a060140310300d900c3da000c6c405001c5204d02e40394240d940d4004405007000001200d46513100c500600c1107440d0f503003900d0501079642d2502d80944508103113000102d03540c0341c00d00c00000071008034002981082d0203601d000320a41c1c0139920703c541c60710040c02804016a6a15200d007803c90b10b0b41d860030300e401d20202d8040e09a9030001200c00b02007018004200d02c0c1d40340c90540e0144d039000720502143c8185c2109041d92075208141c0100004886a00b01c1000d02011518407409a50758070281c0d00c81e0900c1406804202d00c4a4001c4d400300202088a05240c80203c8501a00b0844d002d2103e20100300d8a0011070850700d03994007005c4550000c04c0100007034035280c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 720676097 1250 720674847 720674861
    0x10e0906010e010f090c0e15031504020c0312180f0d09080316031d060415080903030c0301091a04020d0e0f01060b120a0213180b0f10080a021c050604 66
    0x82202c11035075504110255002e9111405a8075445644100d945220381c40340501b03200c440000b52103c1c14041211989081c07a07482240c0c40c50b02180d00608010903420141700715024085a000510300782644e00c07014603c5281c000c1c00c116407551500c450402094024020310803401602c200a0081034600d4a016040850581c0480000d40040c4140700ca582c0038010900601039062615011001e4401090441c40c0245070581c1d8002d80c0200e07000c07400fa0704038205034201c2d000130348030003101c0e6131744501141c0d0301e20084400c9411412300f400100851503840e00890780c14035503000b0000e4411140c0000c1422600302d58612013016482d0404c0806208003480020001440c14000740009824103c00490074401c000f240b840b200f20030000591540c03210750598090b294540e8480c1c409aa41e000e401200c003c90401154882d440c243c00c2000c20315000020b00481074020f00140c00320000c8100503100644020000d0150715000c0200161041c000619041d5070f04840d40c002945003008820b000842d070356 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 720677347 1250 720676097 720676109
    0xf100501110a1218080a0b0c0717090f061c06052d03070504110a09120f2004150614071e0606091505012d050d02070b010e090601 57
    0x22840030504200c400b08501280740e4000c050310114150303599044980720504202203407102000d10021034035100c08180041c80c14011201010a0b842d10b40381d4918074860078134001e28220030120182820f010000141c070059200812440d41c0c401d41d13001180d20780d80540300001ca141e913030381c80d241135003200e5102d600e0140c482540c2407443d070300e0361700d00c4141c2d450044c201703895075400c520a401e042c5580410460000d410040c00c00e0000c40101140100340fa003288104d440801c044400c003051003040250101c66658000640350001002a1501c20406105140070801040c910001807000d407a10300a0111519452081e41c0d40c407840c3c0600144104002c4ac0e0400454104100c11408240d02460481c215080001100d401d0216860001c0051a60b5407220004038280300358100806141c80303042080f644280c860320900f807d0307032400d207916100c4800d10007803110b444115000c005100314007418080d581c2d035500528081c21a140c1d0305070100c00364405581812214200103212500b070040d00c2c01881c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 720678597 1250 720677347 720677357
    0x90f020316180308030f0103121d0402090d0807120f0f051801030b09010e01090f11090913060516080603011e051003080d0603050f0d0f081b030f06040b031908090301140f100501 78
    0x4030400141240c540342c030010138411500441d50809503500c04ec2c0d030b01003060380203040e540d0b1407900b40303807050694202115402c0490300b4500d6011455000d154042d40c0429181c0e51b80d490981035a07098100c51041500c09410980d66030055002503c603c225240600100032915883d5850060300d2416504a9a40e42c091141040036a0401180c020265000040c0854a20304d103691102c00704400c0056031400038140c00e0030700e41031000f0008003400e1403410311625510000c19a40381c00501d800d9132030511480d00412031103001c060910303441e9400f00c0e170001030f003a12040031180d0303d89031510035401c034082c0ca180c0c2c6a070f40c10007001080403c0181000c4004030313001500c4035a0a00130041e0500320900c0003402802000d1002958102002000c20f4075004103040c12501c030b0a14200c0903458410071a00c5a0113075181c043c201c0b804d032400045a14554441e1006c110522031595901481d03a0003d640a40d010f6499466201c6890b01c03c07800103208900502506415140072800503440d03081603404030341440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 720679847 1250 720678597 720678617
    0x905100608070311060313050a060905070e0c19110a06060f05010905060a0819020711031015050d110405090a0b150a03121e09090f020316180308030f010312 69
    0x140e0020b1131290344442c00c50346152250b0707503820f00c64510f030000c4000802a006580c1e00208024466115540880c0203004903800940c0341e030b045100407030044e51581002d40e01130058480034480c1c4079940680250070315000a0b90001d000e41079141c050302d168121005500c40d9030034042880217030041402443c0904e080708000340350202081452195100f075904100b4040001a40c0301098010840c210141c40d5007103584240a00305030307107036460050000d03119000d501000139108280d0f000701c041c820040c00c40400c0507031400042100c8002c0382c520440e0050401600c0883c1076445124a5224450101c0a4110592146000002c0d203000403c0a8036419031000c00c200035882d042e00820603070307601c80342c0d60041940c245410380324080783c0825801e03c040c1085030600c0b259400b0101e44200e50440f50103108500c89680f100043e03000c2141c818505106100b68100310920840500003601041c040034400c075501c9840350342d501c0d8800c0341c3c1861541030781001041000300502010328040e482d843d00c0040c43c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 720681097 1250 720679847 720679853
    0x20c0d02061204050c1e03010507031b030903090906090506120706090b091906110f1c140d0c02370201030b06160624061b1509051006080703 62
    0x10b000b218029066800810006800c00000704842ea01c030482c010f0181a0120b4038900d0f07115007500d200000390181d4202808101000e0207400341039820410b01c40a00d080c0c50303440008400901690000782d08101c0c83c0800054401101e210720000741c031401c40301080c2460100103000e2018a800074007402944000d10411a942c3e220a0010680d041441d04558605896001072001c1c68800040e5181405407100040c0d01078020381e00d903800a250000b44e400f0076100c6044141c5443c591420640c1c2015040d8984210a00c50700200a40c1202c4141ca141444030411690040751054450100540d0281d080503000d402500d07000c40c003900b03c403c10070300000c4046151309a64801a44001d06060300e41e80b041c501ca81d03486098842c10318003100c4070f014180c01410300e04041c02018406142204030400b40108072a268101c04e0162070040e2201d01184284081118000b18044403e81b100440744200798606503c0740036450426004a00500d00710304196907440841d40c0603448000141c0c0205410400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 720682347 1250 720681097 720681109
    0x40606050703051909031e061d03180d050f07031109090c010e0a09020a0c1b05030601140a0e16110601140f120316050d031112091606020706020c0d02 66
    0x1503401c1c4000300e5800707444d1001d00359149646604003c06c0c0f0f0205d8111000520300514010342d0b0140949803c1c802c09081c0f00701120070b1400c4a0b05d0a140d90010400142000000e10508070042c00240c03c11000c4e00c51921600d08001382c40242d4000340d003040c80104180301000f00d00490804045520601790300700b81850541e107140d444802418404504400000e90b60341e0312000c801030411140540d0346100503071300200f2444101c8401c680c4500000f110709030000f040c1e41400c0941d07602500a150503401c1048211880f42c121960941c84201680c0c04200f890201d507010f03000f01c03051a0b0203c5482d8000c0e1010340122166a20703100c07154020030040151109174801c4240b24041a0750660544541c2004600409000c020110084c800040c3e5680c007803e800d407848007a41d028009490b03166550a10450030b0b01e144144d141e003586000d0100d20701c042110312510b030700200b40e81c0881d02c120300300501c888a02111a032050700542c1098004100309a0140041c27a80500f04859104003400150b00140d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 720683453 1106 720682347 720682357
    0x4110a111c020c2b03230703031a010f081909060c0c120e0303040521070b0901020106210f03110615100804020d120c020405090a0204060605070305 65
    0xa4138940e0400622106445840c040056003010b44085034031500701c1da0001c42c081c0c412011080c03484c018200510300c40e44a03403000300302000d00a0200301c20305200361f09036050102e051442c0742c0c45648078240c0c540c01103142c1050702c0881e10210380c0000a000e0780c00020103040c84c11a202c0c0442d44c101440c08003503441015000d0080044040c216210352007010700903050f91081c00248003510700b4000717481c00641e07200800988614208041454450b082d07014050090300019400c0c00c42d60b083c01810301400303414640402c00000c0c20543c0c02032900c40a800b1304203110181c40340b000c052094400307014036002d04040351210304201d041300182002c41d400b07007840358208048d1850006d000d9407600d880342d40c00500c1d55040191940b160501c18842403140e01c10407070954004001a580c5214890241410200601411200380305000888645411200034881c00388001c40002e0303400801c0350 = true := by decide +kernel

theorem cover : BRFrame.Cov 720503597 720683453 := by
  have h0 := BRFrame.cov_init 720503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 720503597 ≤ n) (h2 : n < 720683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
