-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:35:47.103149+00:00
-- url     : https://prove2.me/submissions/1754091d-3efb-4ec9-bb72-f169b6bbfd42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 738489208 ≤ n < 738669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 738490458 1250 738489208 738489211
    0x16060207050a120c0315180c030b06270c0c0d09061b08070f02030c0607061a0a0e13030e030106060810050609010210020309010207060e06090610050d0201030221 71
    0x1198020010545000e082003184002d560098610150203822000803841c4403201c0001d0381e400050300c1e009503055a01c5a0010080110302c07000c0c580060b81c1000c10040c00300c81600440c3c0c00341c1c00c8071040c4c4c0c446504220142c15020414402450700c45c1005641c1100a0720941d4443c802c814414104804160300a00f8441c50101900c001024050113101c80b5030440489403401e100e244582100501e50382c0c400d5502e03c151200500205409007010b021903608000c403040c054009402c0c55282c45403441c2c4200500806000455980c51101c00d25569040c0b1142d00d000700e0b164150402d4503a151351580b51152108060240c04112040038441e240d034600340600c0c00140482e94451400340380800003064a03041c0e13600810711890003080b83e039080340c1e030014203240010b00c5000016035039103c0010032402407007504001003060b41052400c440d8400c3c04901030b071049600d0b40035541180d982903588040c41d070187c014030740e004102041c10740c05075200398042c00506400f50320f0788000001c0c1e02131084941d40c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 738491708 1250 738490458 738490469
    0x63103050a140f090409060b0613061106150d020d33020f2203061d0d080708180703211709030405040203091509010e070807080d0305070216 62
    0x400500d18018541c0912802e0703529900b22021401c02c840300c152803000e4880e84100780e101e50b40350409081031210550203091004001040300355541c9100182241b440300c548503140110f0b400c0c0c034203c0c1c800b51011942e144203104400f02d4076040c0e029507003080240881e50368166040115401e490740003c242041d0074200201d03210b8a6070f14070156564003401c1c448060781444240f40180900301c0241c0750720046d40c184416010760300c2c00b101641800848101c08950000e00340c0c6050400d01e410b0301c00304545052000d01c59105440300c240302c000040d030321f82c803041e0b521000141442c800101078660807114078681c2420b190589014940c1e0751142450098916120413554884000d1030040a411005508200451100000062900654154890080f4880c40d40101d40000000780e04500602001414850440301c10780d450a015413030900a152030a800368a6104258010500c2040025008101c4800034001c1101028001044001c1c1401a00c08001e610a01044082071003598182401421 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 738492958 1250 738491708 738491717
    0x1421040302030405040b060f070305090312070629030d03470108010602100506060415020705012604080a17011d0703020f0d110c03040f05030601140102063103 70
    0x18200702c1017108841101c001144900001c110b8001806031850940e84603d4140c00c00036100c2c001180031a0074040c8480b8912416140003400800700704035075014416404203010140000441000f6002d0524076000d5207a038590f01a03401200d6451003074010b101c010480b816000906100521219100c4050101080c0a0b005150142210310503102210782c640c00c092a00d1021540b410001039141c1c0503003e010040d56460304000b8031a038407003004640c0100b4242c030031507071001201500291078080c00c1c022030340002d589020884144c41c440b034055400880702c20400c5c0c07580e10350340c1e5040e03010f0788042144000e0006e2842071481500352140b9141c020b00e0078902d04d950360501c2c6000e4125440008002400303251062194440d4000d50343c0070703106180bc6120300024812040000f000c0c00d80901c8a8260051200113000719000c03100790ba4080880300242c1c100c0700640d80ba00d24221008500b5440b00380117901c0030002030710009801007000b003c68000603184c40700781c650110301c000c0c080800f0015004035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 738494208 1250 738492958 738492967
    0x14040812280204180b0a060827030315010915050d09080708070b070f0801171c021e010603020d02130902090103060b011b112713050d02030301030201142104030203 72
    0x180c072024a011038460741904000200c0b02500081000c0e006e40208000c1241041c00500e1203410764555900030f03109a1040e0202d10144004c080d901c0c0e0080b0740004010071201c18542d1907500030400b020648802c1c42221026500e001c070120340380d420070080c64010b10b484011010100356540010288580507000140d0f5030107140c00c1c840380c1140c010700048108540da0700c0b4114110341c05080c0d04d056650440103060001d40303000306589416403141c51075105423029001c4002c1c2e507030005200050740c0030580900344004c03440500e140c201d58042c40b01075044012140d80c2d034010b00c0c00c1241d241c0d959040300c800040d200429004a9050003090b0411101c059988100b91071960304000000f00768100704c004220300304002c0d034401c801c10301d105100501400c0c4100307040040c1c0a0040d07a849032248150220003503881d044452540c07140c00c0c4030f01aa8907001d0020070700502d80c400b0007107030305903501038403a00c4e48059a484007064560181400241e046d0ba903002c03003541d0032075a200140c0214060790065884 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 738495458 1250 738494208 738494219
    0x801060e1302091b0702210d020307051903050408010614092203080a0e061524040b090a03020310060e0a0606121a0306040f030314040812280204 64
    0xc04030151010103407401070314203040141e5840380020303841130221032102d84103c0c0038040e942d0103002e640300c001d500c650340300c6000d8100c018440b52001a961204206d5603404440e03403041c3e0b2640304d80500902503400941464028429001c0c20840711440380c6801c9103000d603544030003400c40d020382d0090f1210181c44a1800746c989480d41c00b503a000810441e0038a110380802e60b1205615000c444000c040c420008002903440440e54015022060f124084d10300074031b44400c0781c06c110408270941600c02d030021036402007009600030700e0489840e040fa03005880c1c1030401201da09281c0201011941c02001d807213000c00103031010301225200e50045000880c1c51410a0710360040d003000101880c1089160010030000f181e4031030601500180c0c0010b00140340000e0950b13280040c6d141d000000d8052040da42803204010001c050110814001e550422000700450b1610b0060201a10003030300e0703500c2c24840040c2d906403400c0d145030001d407078500322411034032040d00c204070b03418134074540c80041c95020804121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 738496708 1250 738495458 738495479
    0x2040807050a05010503270a0b04060e0a0b1504060f090b01110f0c0d020d020423360c090c0d1821020102040b030c0910300603020a080106 61
    0x141c003044840080315414076000070704c03900000388001414249042589408a076002c40071580013000b4042d104c0b1503056080880c64114182e8048034043c0c0340140c203c4019102080090300d22b035220309403562545a000d0142010580800001e17803040d540c00c40042e004c500403d010300144000c0e040412156980d030009031008560038101d04580d004a9020601e030000840c00c0c0080c0395040b50580305c44892400441c0c00e0300402000250880d00d0b1005e0402032180c110119002c822180c12041242e5071a02e4000c019401661800c148594200010308211240c246003809882d1402003103e10515034400002d0203a013003603406900c0d00c5800070300034140707102c540a8032401c080301107080039001c2d015030b4529008100c4503e001d410300e10061200a811031003034048600031710041c14a541c6906200c40c209400b0390109400c0c07881751841a00410036940541920541c81140c542c40015a20310744130420004e403c0b641c0140c4007203544035000b00050341c4145005010f45055400002d4403800d2682c00c48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 738497958 1250 738496708 738496723
    0x8280902091b090103090606090501080a1e050604080a0507060908031014030d0e0a030c27050601120c110a0b09010e06010b07080d060320100f0210091a0406020408 72
    0x2d0048801641d8072810702001d00311018240c00303280c001002216030420318020030541c3c2040c50b409040400000341c0c90f00000b0400d541c035005082e0786c1030039030702c2c2d050907982c0d2061008014002c3d004a400a03000c6641c4401404c98090301d03041ca14900300041d0340e5541103400101003141d01010200c00c1c08401d410442c2c041c005000b000c038a02000150000000382d8858800311001d08024400b400c80070a91a815843c1004540c4210610541c6840d0355428034205450316040c0104012151041e0b4241b0307070f90050034066101030311860a611145c1c0e801201401618102c030702880848442e030207148404116055a10f40030751100021402c0850b8510f00b950360309285022558407040c0184609070152044800c2c50750f0100c00d26a6494503189000701503c05944050407210020f401d144892000340c520314660b15084070400d000349042d0744140c0f0541c0341e40402c0c00050b03101c0a0790140a00203030307100300402c0e03005006070105001160382d800f18290080324104c400c290080303001c00c1581c00800004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 738499208 1250 738497958 738497971
    0x509010c03050c04210219080a021507151116140d0201052205010b0619090e1512030c1c0315050d0b072a1502070c060828090209 57
    0x30346814540595001769003600d000501044424106000842d034a0540001040700d10001d06090b4036a2540469120030a40304140c0c06190401080fa84150044c4120f61220b51302c40301481d82e00ac90959032070010452821701c00d0510408000c1c2c844002000c0c4a01c41c0050b01c50382102041410300d02110742000070468034a015603051000703004118516481e900e019110b03075030366110003039000c0c14018058210015040c0c1c0042c0001003100000c00e02c0303190140115225100e150040b5940d007582104114100c80f120310030a03020100944034038164405c400e1440718501101d040801400750b050803e000c1800c8401400ea00c0250030300c805070503004003043c602075240710000b154509004688180300744d50000742602c1005000401a82c020060341410601450410a00c056001d0b80e4020b400c2c01c0e0401a901c3c00ea4084000e801d0703a44138000c480100e980000703640641445c01c1c41c1900c4111002e0006113010000c070301d1000460719103030301142a41400c941d001c1014081801484400e00300903004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 738500458 1250 738499208 738499231
    0x31211071b0506030402060a0504031a0702010e0f0c100e040c05070c0e04020d080903160807090b060403050715050f1326060f06150706021902160e15040509010c0305 73
    0x1040155589404d43c1c1d4000d4058034030540d1214242e070111020b1089030401441c9884c1150f104040344802203d940c414040c94000304026140d0680c1640e4800007500c0103400f41d40002c1c54121a818000c1c001d000782101d40c14641d0001c480100003801fa101030411003400144003152010510068070000707801440d40320100507031414144c000c07402004108402500d90980020058402c0c0c80030095516400d00600c02c0030002034650348600c0d200d02452103200902400c1ca02c0709000d51406004660480e40e2103001410000c1c588042c10504507296507510080c0300c403c3c0811403513485054020402800c17848452620300c1d00780304050040f0b06041030455094003d901418012200024400381c01600000d44141c282d55007030001040003080201421064101240220410035290040e1202c00100409680d4802401004030307602c9d103826034442d40c0c0d0340d000c003410030114a10314401078201044948410b042000040858240d1340281c0c0c0d004540da41d590381c0500b075540d141c810f880c1c01c525501c0300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 738501708 1250 738500458 738500513
    0x70512030702030702010806060c0a1515080a021504120609050105131112070b0c01150e09100c020102040b040b090a0527090c03010509060f0f0f011203121107 70
    0xf0754900480348024140042040482d5080e920745040e1400000900104c0d80341551524000035200801d0104001041c14041c04240e660260440c2c0e00660301120009c01d55a1019002c00c4240d0203040b040c4220700c035040101242070740042c200c101c001c0707008040c081600001c501e40142118001007014120602c24041c1d9000604492803a44c0b107641d044403420084800c400a45003001c07403aa220120070030300010b03052810318040d00700507014040350401d4601580c4e242c0030382940200c2114030080e5038201c40c43e490150300c4607501c18034046100d440014203103500c800c002e405907030054000780030b100c01c041494143c130300d8008280360240c00142c8031900c2c100352500740d417000e84004a0000070000602000074000d040100002840c00c003008000303100c5420003540e42500c0d2001625414212464280095017111210207590b0084601000c245a9030b8030b007a01008844d60007c00440c20031441000d40b000d980360b107000e00c101c1c0c05e0258200541d1025145007428051003114014201480c0016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 738502958 1250 738501708 738501721
    0x61d060d0605130521041e080304060e0310050603061807050603010303120b040c0e1c020405041b0b1305270906220f030f170106020606040e010b0d1103030f0c0307051203 75
    0x1015601261f0003003030980540c0703124964181e0611801d41000f40c1d070f4480800c00107005940406294044242981950765080c0d41d001030fa001c0d41e6045520325051b500c4540071a03046254240b260000210441c1039600d2030740c580c0d000900c2c83d40280e0094000034044002c255003403229100b10044c0c800100d074100a5010802c41c098141b02d44592402d10406071411408001900c3c0c60700c0b140c40c5540103108021520f04ac0c03404c5a00501d440c2c030f500c54101c0591402260b500c8541086a001800360012020329520b0042002030f1110b0010500c1200c0032071020351100e041054880b071b40250804d101501c03a5260049503004500d010700345001d00284907007a403030081a604d41c50000255003600d41020221098042a9160102c0c2003240c4034100242c1e00001d003c80e13021a105000b0b03c2c04039404d01c040d00c001e4100700d0a9812100c851940108040c5000e00040c0300070180d8104c02c58040c054904103c480c83c0d8207e4030341c1040342103403100c1d080041e1210801405210440c90040d03c1d030035150a604150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 738504208 1250 738502958 738503023
    0x5060a0501050307020c0a150305090a0305030a02071505150f030a0c29070b060102010c0e090a1a0301020d1b11071203020703060e0d12061d060d06051305 68
    0x103104090500c0400004603d00c1e0f0b1017805482d18403072016151a890a41d10031155608004403901d800020340b61402084418031f000c02d0b425807554040d6951404d40c0c4030503902c00002d500c041c0e03084400184804400c0c003482080c0c01a14400ca00e000c078003100403200c20050006960520038440c7c0700342c1040550f03d0020341c6c40740d003550913030704400c10340300b0395031031502103e28008010503e00182d41c001180c0f0808104825401c0d40c45090281d00074840c13560100816198030200f64561980214144001060041c10758400d40c10788100c10500f0010945040120b400c990140c0040c103002c903111001080b01000104041c90401103034649624240400c000d1903885262500400c99042510f211420901d84208040740107550883c00401002d8800a40c081e0388107540002d02d8041901c04001c40f00c010098443c0000700c59034040d80d0f000c40c46600c01702c0b41c032004008000380d500182ca44984404074145200d418030441140e0a02ba00400e00c5003451854040c3c004055103a44042440d64003986485 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 738505458 1250 738504208 738504229
    0x152007060f09020a180c0507032c09010803120c0c0304120c0b130816050a090213080f0a031803030906080a1b08151801050607080708040905070f030506 67
    0x14600103000c501d00c01205000d07059064003e50f00500e00c0c10b021511000c034901c10241445400ca0030400a240c0704403d03102c42c0580100500802e40c030700390a03d403c8041401c0494403101120b2240d03031040f074450004402003405c0e040059140e00106113071070110020040590071681c84030780c2c24100344070300305240d40d130f03104030300036590600720082260040141d54078001010741000031111fa12002c0103808440700c10341c90710071014584100b54104031030100c11107002e8152440500100c00746401c0100b41000b0358081600310350408181c0308000f0380740c0420b1002070401c034000c0c4050080726200b81001082c41c16000208503400b0100070381080007076041081d000880300300f8181021a0360741c02d000c0300000c00d0a1040c1130440c03e150740c0d0813009103501c80d03052449100c0001d5202d41d130904550074881880500b4240f041285240001031041d8035100c4041c00716a80701e000007620340241551080034940084e84200d11349501e68060058180e0091300c0200341c16400c0c0380c00c00c0b182c5002d00005000410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 738506708 1250 738505458 738505463
    0xc1306030603081b191b0b090a0311011407060c0e0111030a081512060f180c090c04081605040605040915090503190905030d02191419152007 62
    0x10804140d001c11074041c001c4a224605c0c440c1c001101e42100d04018021802c0710a4a00c080b1003113880c085406046a001d48400d10000381c06040024210b5a8000e00990a841405c2c140007071920071a8101c5401001060006d22401c0046008070f031408024200400501c009c50602c9030b4120b440032090000001c0d21078a000901e050903042d2241061050104000d48060703800689400b009030719200e0000d0024098040d071040c00c40c1310b0ba14401114044003038150111026006010040c1c8070346850aa4503400a1404600a140c00d030703100c0c4581d14110380740c0b00c0c007107101e601d114081226140900c0b40e580104010340e001d00080c0102c0c1e8501444802d240007074401d465031102e604d01440b20400070b66400c0350020a607540181400480944058811322840d48248120714403081054070108004040b114182004a0450810b695211025405111109543c07140a03060441d4040d06144101028002d0381044003040d000443c4900392440e408506201d0005450a80c4040840108a420064 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738507958 1250 738506708 738506737
    0x6160c03080c070c031202100203060d020d05390402070206030604021c020a0e1201020a1b031103031005030c0a06021905010e100213060305070c0602210c130603060308 74
    0x50720082c00c48118028a04003a004a140950120421a00d649100205c03075107602211052140c100020301039100c00c491032500480200f40c250010b00b4400c1008112900c81c1041e52280c901e0341490068070600b05502c0c2d41400030340643c1c00b0210080b9035500004032000d40d003d525220440e0040360047c4405094030b8029940021485c10305404800c1100c2c0550070447c06542c0d03162166401040e401114050610a00d400e40b81004401e0341407003110407004290700d80140654804201c903810080c1d0480c19000c0c08a024100844401d00740000d5114031403120311920342c182041c1c2450328102c0e0604506009104501080c031600341c000038280d8042a03420340c1a202491036107005409421040400c0b80c2c2d40c8513000842e00c07000b96503000b030244400321002c800d61a5903120001c038162601616518045504884c245002c501c5c0c0d9002020000c2084840301d0080b1208501101d01200440d0200d02d21000030481040030003816420300001c014a01c3c1c1440710300e0440c0c0300c10300320340300e050b20000400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 738509208 1250 738507958 738507961
    0xf060c030c0c01290f10030b031212010f08011406120a020d0c1a0a090902070f1407080f01020a020c100306030f060213090e0a060b0a151106160c0308 66
    0x1e1088030440d100d009018009102003204c0307113081d00c80509180320800c2c03030244214001c1e425040116134600c41e00d000820394507130229400c0055001700b2105c00001d405008021031025242a240c00900c0f000004000106075507261170714115003498550024140ca90400c030880401d640b00c0041380d078101c05d04171407201001c183d110599260030008003009422900c42d907090700912a101100c00100c81e08560004650350b01000748007032034420400200082070320000244030541c0a5800740c60054891510342245800d10340741e903c40140140044062540940b00038070140340c0c140004d548261864000303508240e15401301035290340b10101c0460085125502111065200f90401d800542e0400450700e50030450742044c40103540040c400180035002900300007002c04c4117100e40011840580050041e001050f50354901a01c48242541c0d032000d140f42021401401219070101d000c81d06848262941038092841818100001e01c00c010800000b0b00f078668103600030101006459246c036280c0300a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 738510458 1250 738509208 738509221
    0xf020c120102030f010f080d030522060203060424060c0f24150e04030305090a080406120615090506130902030c0d0b090126030f0a08070f020f060c03 66
    0x8008486209590240390303848180884081980214024030811500c40c02d00da8072120034403206400d51068440640c0141001174501e84a03500c086e130083c00040094114503503203504803042840c807210948a0641c008141302052030702c0d11500c417140c0720400c00703580341c0d000c11001203880d0300640c460b590500481e001070104100508409011269020a0004000c45480c1045080005c0302c1d4052140034502111a2410211160f400003100c2000081d04516235841c0c0c1e0450113814042e228200c6886203e01120000c0c04030703c090805840300e42d683c0c02c000c10784054800192021940910010300b80c5101e280340c9150300094400c01e0b84d1041da11940d4031001d2805240700d8a40c2c561060000c1803011040c0500358501e4401010701500c4060140203080020f010802d05500a1041107003000251300c01071840150460201e450a420205a905142e01d52083c50002d5003c210040c0010703c4100801a0700398101d42e0301e0b020361455100400101c050484013941e1207401800d600450440480000ca0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 738511708 1250 738510458 738510463
    0x903090120010203010906080706050310050f041401090b2736030a120e1c180b130608010e34081b07051b03151006031b0509010f02 58
    0xd00d280010300866417586d6500c01500100760034014819280201e00b40020460f01c90b001b964054058480c00b1000d0600d04010083e0340c2c0202413045801603214001340c1d2212901c5000340b802820011004945001c0c8030080115907102e42d0030000111803111400c0003801140b6401a07400341d03615024090645d20031030305035505106101c01c95046818082d80244000b808005012080d01036101c58007844c500207000e40595854000d8214581d104030307601e01f00303103e0050001d481e010781802d01d13000031040e910741664640100d8018254011001032184c0c1d55540085401000701000e15040d1f001e5410600c1c40c201c0e0364400b40030300c008846850311818203600200110590a60540320035061903035a40307006000d94030100c90401d0705080b8060004100103a4004550030103078414040c2580205405c0132103042d41e0784400d02c1d074151140d8a000703c00300301b004000c903004032281010415404d1078610020305407030009490b0b12014501e2507401e0f040b15000400e40b07004034000d0800c0310394030110b180202d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 738512958 1250 738511708 738511757
    0x307110d020415080a1b0e07230a020a1a04031202030a060f121a01060527030d09240905092e0504051602060115050705010c030507080f09030901 64
    0xf2101003c001c2c00a840d4100094603c0604e201e40c49403d110700c95003200880074100c80c451104840d00407070008840c94807590151303080018003409030b14481c04200d00300d40941c0101140c8030160780064469130900c40f00d0090040b010720110000e1a0030f2409036001032141c04054560041c45d0b0300030010270300c011082d4108801800780841c440080e1a651005054001c081d03400aa5225403156181c1c0c0c14180d100c002141601c603541c0b149407521450126504580310840003035400a18241c800b10034030b030341c10301800144950301c3c3c0d20f1468550508404d0415041c0140d28910034280c203d91821001e60040021011a0001c841d40c2c0354564482d0f00203000b41d007071141868803018800c401c0d114900389191400741a50b105035010085903403488521103140503040c00076400f41e4000300042042c40007603242400301c0205403804900b050025a6045d003901c00b10000303040801d495104000000d5406680305900c1006c4031004400c2e0306065a4060f02e078400c021200341082503a803090320720600629001c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 738514208 1250 738512958 738512981
    0xc130b030a0809180103111c050106060c0b0a140615120703021b030708030402060a020a080304060219021c1d1816050a050d0b0d020402070c0e090307110d0204 70
    0x80e241d854881c5804012903000c12406441010b0103040400d203c4441c250450580368490030385079107170504001f0098442e0645a080507904003280050001a81c213000700c0c00100155210103250480603d02036410b420b0040c446010b81c0d10740a980c42a208258a00c1500000140c0e0051a107080385503070b1070200d11510311000304a001400904c01800da241d4000d1048409034101351099001c8020200c1e00c81c0305443d000303004050144045030140c0f501a0080030348a01e40e0040719104841561401c1c000e070400c460981e040c40c2d0109a12841032030f400b054541895161019103442c4104040203c1e004030380f00d600700c080241c480c0d444070914008110701480680c00600e03810000011040e40003802070100c030700340300b10155004030800711f81c014401d80f26000b10a840e018101181145402c005141008805a105d081c00d1a0100035031218401022218010b0001340b680a040c0325202015020242100c01e547d413041115002060001c01050444002120488100c18003400040c02510095034036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 738515458 1250 738514208 738514213
    0x2121305090a1b080402120c03060f06030703020d140615030d08070e040e0c0427080c01090f050105100501052d09040c050a140f0909090a060c022107050c130b03 71
    0x1030443c0c640c010b4030a81c0b00743c3c800c49000d9041e40f200c0440b151207191203c8141d40513807101c404681122501c0d41e0b07003a84a0400703412142550b549400054024458283c1642e154000c02401d1446a405100590f80824684044050350050b00e010a946d1840340b4005010071030303020085000c0e948603a64200003080c00910602001c0c05a845140d00c035001110761600c00d61034104421010f14815200080b0700c2c00c281c0c107454207081243c5078964035500154542a507550780d400d0190018800f40c2085a1090140000065034a0304441c5840e1084103908020706000342400041d96080d10410311402c200342c48406010043d10064050307000340500e041042d0b00600300b80c0086102c0394004083c0c0a469659030f13804540105d4504000d09030301c9a4100d12405080400c000c0b185030400784200c40d044800c003c12158150141d807285805c0760200c0c0716020058025104200800c15000c030440c2022850212052804940e40d454603540e1b0860700b4007901442542000a11061060340b040890410280c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 738516708 1250 738515458 738515501
    0x30c020f041d070e07090b0d0f060608041103060105150703030b06070303140109050709150e0a03120f180303080603070e0106020709110a0e19050d0f0302121305090a 73
    0xd820b1507820440c2450803280c403c907100007400c0c0f11200302050190b00309403100402d03581041032082455101c2100c1040c403d4482c0065000c07071f0301c60f10500d0020141039a85900e07605280c0780c050340116000700b11074401d5100710018407442e0f540c403a2150189814900241e6200941d10381500604078500e0035503403011000c03442d40d051640642100c203008403040810f00ba06d83e2102205812118240d8040340050419070040c02040852441d04482103154108000b100203500001284d0800680084510b10030b52098540340c681c000c0c02c072051901c1c86040001600c03064088070340400d107040c400501006801070105d000d54901b404014003410f13401d1606019980c4440d03001c0e5440c17500c0e01c40d0344925490240c001c08607c0841e0309035050399000350703a50400c0500c803008200103403814107400140240106000038481d5141d6000c02c540a11842d8800e240b0320341410040c1c1401c0005541c1e8628201c00c1100000e04001688040d003658800c031102101c42e11040f04040051000c0400c0740000300302c401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 738517958 1250 738516708 738516731
    0x9151a06040e070207060f170c2205010e012a0305091302121005100807030209040f052a1903021903330b0c0a050a200402031003030c020f04 62
    0x82c0554420000341d021240029500c401c02c6902140d400c4810000800700d13443c0148528856068a40018524103c10b00700030058600903141545804944800e141e016400c000030750704401d68401d01042400d11102807901d980140d80c5080764040d4080010904014000400d03008000745c5d0400f46014002407452030b40080f120009510403122400905049000102c048054031383c410143d80010f130800d518420195402c3d100c108001c0c049000b07168080c04184c0b90b0b92240d100b101e04245c0003900100d01400c0584c44020811900042c00140318448000f14010015501c02c81d0a100040d040d00540d00c0c40141040b4000d01902100c640e414480750f140c0f20040ba4182c120180000840c88896a01c1c0d0300340205c444001c0005001c05100528000c041040d1f07a1007002401080c2200c0d030a441c1e0103210317690b6807030401c08402001c4a10300003118241c0e1544003081140c2d03110030021b0700c04520f5428142310032043c03941a80320017000c02999001410442d22568484141840090000e00a96003041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 738519208 1250 738517958 738517979
    0x3070b0f030414010c1e02150c1209012a05122401030c1b080f0703091e2301030f0e1b0603041703070903080409060f050409151a0604 59
    0xa441c192100314000f0726001100e1018407460502644980b20440318080c4e20300c98206c0840c9401c003150a5002e00445071683c00c801e10b40d964820303201000415520342c14410302036200d04000d8813a21661785481e513a0550008890201c8115010300e2460100041c0c1d4000226607a12401c01d50745941091903041c40503180b00e46540f01e034140641038104100841e80e10045003203034407016400c0001503011140030f451f28010341c2c0d0790348400d004840180c035280c2c1c001c2142d0200c0d4003034541200043c013080c0080280c40c110072582d19800d110118842580c9142c108000741989821020426081c507180300552103a003c1d078059003d5202c0204140403d4440ca886030303071254078003180120303d01c8110180030110700c0c0074002c4a114540c0201803060140e89100c000c081a00010543c0c3c0038040d5401020000c0342c13410340584000c108282000c41c900341040f4243c460600c0591055004508000314040003480d507405010002c841d0305030002d08090310040101411002c1c01300d141d00494009408207005424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 738520458 1250 738519208 738519211
    0xf1413140a11011412010510090801140711030c1b0627030105010b040f0b03041b150909020304030e040f060f030506100b070f0609020612090303090105070e1e03070b0f03 75
    0x4d803107913404c89000b11800c00c8144075080c4a548140c900b000117001c123140002060004a0380f03450000c1d0055268910b282c02c46440e1054611298102d03410490090f07813019003681c10f80188800b65080422030150607981c1d000351039240040c03c130701280c407004030740b00c51050b0307050f03403185028014030082500404006002000d52550080d420f01002181542d0303004c00304c0303080b50415640490040d02e02100010a0b40000d40201c800304032540c0c080c14002700c901d40e10b2010f070034510420035181a1850015003000300701e600ca000d40d10700610401000c01c0c1c009c4441d10000e0000e0f500481d10b074102450100082c41940c20482041004d004048240030b40010101d00c540340c007040e4107a0781c1c0e4403000e00070064080d18000601c00c4031014403680c0021426001040241e10280110741411000c003a5144940400c03107501c8996400841044260002405642e421031540c2c149030031425480b10100b040c1c200403d65180c407030032800e100c000350350724200b10b81c500038210020802d0301d984002036100d106620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 738521708 1250 738520458 738520493
    0x6050307020706140f0c160816081903030b12010e010f2712030b030303190b09270319050712050903030702131407020d02010f1413140a 60
    0x4185010031801d000d0180c2d898070000c60989075040c042c40e40e041800740c2d4090001d030315050041c1f580c903004502ea10b51401010b0908280613201110302c40d40c203000740078150390003000d503644104000c1c4820541c8188258001e03401d0f14000c1522111b03c00400e01494681003546055032804071a001a048c0c10f42c0800f03203800d1907040501160140d00d10500d05816118051504211945900c00004503070412907058400d03a4103000c24024a160b00080c250707082101e4202490b40c0301e01070b403504106107104116520701c2c1200c0704000390505442c07002420311010000c9802d504c001d50380005190003042074500107021404e030030000f6600384100422a0708010802c413041804d0f00c6d210f100e424010b0b0181c2c2c400810182c01503090009540800400300301507000c0343c01041e920071144da8060150007980c1e2066507650001c0042c0800400001d003118195070244469614040304141e00300000240d06801c00616003080c0d03030509890420403262000340000d10458030801c02204100048031003038048654 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 738522958 1250 738521708 738521713
    0x26210a0e120f0d0203041d0912040e010515070b01030b0603030d050108010912091508041703040506060a090c021002030a1506020d080c090603070f031104061206050a0e0a020915040605030702 84
    0x8264000d0b6900c1c056802102040030006240c28040126025450b07030000070501200d2080c00030a4050030320762b0080d08a40103040000c1c1c01400725040c1444030301089030b0344189a52400c0343c41d131605944000d06000c002c050003c0007001c500d95540c1001550f01a005070b11080245594442d01107000788014801110410b8031065404c1c1c01038000c100740c5040701c00900d00140300f0390654404840b03900c002041180c1c075100517488550030000800195208910030300050909040450401c01c81c41942e600032a80c040c1400e5082e0a0103a01007107440060a83c4100581c42ea1a01a940c0c2c1c094400100c914030b90007406800000e0b000c0c0d0004890390410030320340f80c0c11f1050b120712643d0760040c0329160300940c2044081010403c15881006140c084807813a103000a41a1002c498035541c40c0d1050b48440e00195180e0501a002c3c0c40360301c10440101000c9558081e414a00b1882c82801e060003409800d040d6800304584071680c0392150028451a241009950f85585503c0003810703a4009440500051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 738524208 1250 738522958 738522973
    0x408010b03031c05250e01140a1202090d05010221060d0c0303050a12110903010e030309060712020c1e060f010501080115031526210a0e120f 62
    0x41c100401160640318115190041d44029091160064040a01400d0311201c001d100c000c01d001c1e400030b002010003a1a44c8054030404004001001040316040308004070004200f18120740e90880c017401000c00282d1400b603220041c20b40043e200b07500703c24001d0a15400000c038840d00f82e810b4002c0300c2045094641c100700545a00080c0300d02e4417070315200281200340d5000305001080c0030b88040e040c0d82ca8580f41c00d582e0303880000c40d401c00780c6602e10802c81000c5001700d0b49405502d0280242c0c0185620310004605600e81000c000f0354444015108005204000d41d4840c04c10505030110703915202441c0031507110310015003801e4074410021143c8151809070b013003c0340780c080c90099a1812200305075511001e0364205071711003191140002c814400e05503a03c60500c1828002c54005000b4101000f40140d4040d00c4010032814544066007504035410102c0c180e207580604125401c101c950111480c1e45035110b02005a84905940c500c2950011350040d0a05444000044408060891005490b0308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 738525458 1250 738524208 738524231
    0x1c060317030609130c0306050a0b03010903020c01020d210e0304120503040603050c070b0f150d0506060406061803150e011e200d0902010207120b010602120309100915020d02040801 79
    0x2130138011005041c0d60500ca0b08202003042c40d004580c000d00d050b0000980b0300400b00010b0300711703501c010088016030002e0300131f9000f940c1c040c0090114603500d03042400d0b54441e541000a0702410141c03000410759501d4110000c210005c009a4010304519281004e01e4256800c02c0c030ba40b03400a02c2003400190612000400320741e01c00041d182480c2e841442070006803142c04884034141c038010601c4101d01c8000c0c0030075016943d44425100c42c1d5004002804850400f9018003060703502a0300100140040c0070f03105030b4070001805414088a410522400001091000500141c05103426031026582404260310204034030102c1400143c0249004010840001c1044c10100b41e0300404180031080c1030103070f084680d506e41c00c01c2040c1c41c814030503528021b440707002c116014071072800e041e100c030f250007001804035a8040201180c5240455526402d500e41910f072180c3d00c0036280220030015881b50303002410880740038000c48003551480c8040d519200e02c000c4070b0000307400034401c44000d0f41c03e20b00c03100344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 738526708 1250 738525458 738525481
    0x30c15010909081819060c1e0b150d06020301060f0f0f0e091f0b03070f0804170a110303130501050f0106230904051521031c060317030609 61
    0x7040d40d80911244d040100d04003a81042e010b10074807680d00480075828040c949107075030b400400500559103030001030782041d0030300040354140f18040d140e07101020168034010403034070701003554006104100f120790303e5121008555140c1e4940802402d01d8004070002c11059080501c201120f6101d640b04c088001d403001088441c00030050040001c0340449030028114282132081d90b502115003c1e071000b0030325084400050450076a40031000090020090024843d44618080c103248000e1800441c04e0410703840d140c0244815030b2204401540001d400c5500300d0161044101c000010310503282c0364540b00c010b00189407400c01c0e013140d80d5460200003400c03081203020200c0c107071656503680b10000122183c844407110000d0091b500d44850600144100c0e56a9005440c4115000c019515845102ca8240002c48010141c2560046c19013260b40c001190000107807040c000b800d803d500750b20b514214180c40104010703040904508561801d0807400e404140c0154064801690441460395803600040d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 738527958 1250 738526708 738526721
    0x6110a080f091204061107051c020a0801050106140702030f0d180b0f0d1104150309151a0105090f060708040609050307030507120204020909161211070605090a05030c150109 76
    0x3e00791042400140155442041403846080e415000c0341d520382c2c4c4840c00510144814818404100342c3c4064010441c144245188001d1100600034041541481d00c0a0100c4281d001031051010b00410641c05558041101c6e00440036003800b510340109800724020031120000c071070b46d00d06a03400c0e0340018040e88500221280e89100044050501c041d52078000e0113481c0b040d212060300380041c000481c5000388020001c0040107503440000b0750b2141482c100703000f00d065806104404c2c0c5000600004c0c003460404c0307444883c000346030441d43e0761240310005027401e42d2800c800b9000703140413400104101200000344259001901e6240501c1c0d5030f1420582e0b80c00319800001c0c10340c0c01c5100108006001c1310000c504c454401000581002c85201c0407a510f00fa00b10740c4800304d40c0020520204c07058020b0202004401214000d01c420401201d844034148110f0a0003070171203951b0b000107048094103128017800c0641c0407003600d030745406001e4550b5507a08a840040c4000c100a400000c3c03946032481402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 738529208 1250 738527958 738527983
    0x7091703040501090311150c0105040309061b06053106060e0601050f0309010b041a0a05010521100b030c030f060a26070f060f02060a02040e1306110a080f09 69
    0x2554124295a01e140540c024a40341b150002e1980d40042c036000380c00e4001e444010680b900000300e070b10b09801e004003042c50651003801031101d05032100c110a85800141116030b03800c80404520b0740c80b01110700b4040000284448509640f0842c9000900c072240d102c030864902800062080716100c0744544510132094680c10301168041111440190002004e507a11540780400043d0040b807910109050b10400c480c0b0b80c07000f03501241010b41d00c2c5440171801014000c02c2c83c056040c0080071107001c0000030036080c0840c81d02d10403000915812440303014807002d0140c442c90103407682440100d20070b03141c10a86040c440921240e000074000e007003a44a0a003110101c01c2e44001895a10080320120444010600114000c0c5180414641d0303040041600801d2103640b850f00c43d104494000f814118081c1c4503c4c000c5004100420015940b02402e9030044030017000801c6a4a09207030540080c42c96101a1142010214484541c60303044024203101e4881d001d2402a19510582c0b816241c4807061200c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 738530458 1250 738529208 738529217
    0x9070b090d0809030106060903060507021506010302130f090506100804020607021201200d18170306010203070b01080604020f01020d08010608100302040501080c19060c0b15060307091703040501 85
    0x51035454945030070040719002c0c4020a2070301c19150040790130b449050b009400800d09003201007042019900c80c0c990f11500c41d00c00b0708410001004016101341011309841d040540100e4010400485413205d04020015140301c006016034a14a101c040c00e030031241103200d000c0d206500481c0c2e82c00741150501c902d41c01000d00c0d20305091542009440282d5038000505596a488071994508940000c3d5800050140240340c44084200c4050103403034444907038500c1501440e0664000913000c0311040801c00c0c41c018229103ea5400300100c0c42e41c0508030028142030300d000000104014003286240c0640d00954040a820140000680c0d80d0791300500883d001170b0000d0010400300e4803c3c400950000141c0c0c4058030410303601e4000030b003560000e0b00142040d80010130544850301c0c0018070038920304d4000d80245202c5180c01c45c0948090030110b40034004100f03200000e6024540c04190b840707504c1d002001c26880b81070003c001400e540c268000d043c1c2103401041c0100400c44000301307540848030141c0d078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 738531708 1250 738530458 738530467
    0x160215090721120c081b1b0d0c05040c230c1204060c140309061201051c0203060703050a1803030e010c08060a051e0402070b070f0f12051b0f0a0809070b 67
    0x411550705a03401001d40d0140024400b0141a504000001e01c0729101c5400420100040c00d042080e01c7e12030100711407003545080a0700307000425151008048070802c413000507840715511010b880700d081c1c1c0c00c1060250b1406030046002007000802801055042e0b10486640c12505a005001403203a030180c1c4001c1a030920900000511010540b8001d01c6042e080c0e030f062441d4280030031400e42103e074410340d050503450014015418840309030500101045c4421501243d035401003900d95002070445402c141e218000514242120382202c040d00015907003801c080b03422400d00400134009121002c2895007003807001e503140c602c10b85519001d198000c04520b5060325140c10800343d81c550000103001c40c01e400426061944c4c461000e081c0307960103000340c5016850414001084881c1c030f07052002c00c1c01110328039085030681c131000350ba44a189094000500b61554491160207046040d1501e0700e2500018080424240580140040003416140c50429403509440300e13484820324010501c11880038031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 738532958 1250 738531708 738531743
    0x170301050d08070c0806010f05150a1707230712030b061602150f070c0608040312270c0f0b04031104050709030c03081e0c06160215090721 61
    0x4003e1140c00d108480490038103580fa00c07803505090090b0311400d662140302da010400c07400c1000c01500c10750001c1989500d4001041e802900c0030010603806020b0009180004072014042c14400703280035507a0201000380542154a01003d91008404a400901e56001d0f0480c02c2c0c06401035480000c80200740754101030400f07100500d5108450700907a8403401880e11203960350b18000090501000c02420b403660303251607040c40b031250030f22a4002010882800104400b19600c4010b01040c0c3c0f5a440c000b0604001603c1f58440034559420850107400e85441d610040104522162080300c81c41e94801c5100c40c0c0d074808000481c062440042c000c00100e01d00300076141381641c401c41d0720281d107080c2494041d40300d80b95a80c50780c49540040710040340010300032000900b0042e80c403c1482d01005401d01c3d00700c0010b141911188060110108403070010f01006841c1e009108000306141d1111030702075545030172410036a0300c0071103100d5045000b04040c040410030b59025160020680c104400b10506a07001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 738534208 1250 738532958 738532973
    0x30a0b011518030f0203010506060f03010b03060d12081006110a08161b05010206250e130c03090b060316060e030319020604020f0a14060c070f0b07170301050d 70
    0x958810700700510101d00c60041c490344581140914080c1d469600045020710501d801c59102a11842c0318a80a02411003102020300889041d02e00c0c4401503030722901d40d00003090300b0264200000308182e0110500002081d4032511451162030702c088242d0075142e03108ad0503500c07111031011981d401c4c0c03ca1540c000206030350500070002140719030a02844180580c075122403410010f00b080c200303054200300411185da4104500394103c8551038000c210004c070449258440300e4425a04410f1162419803006c9a03550341e0784212031441100c4051101c5808450700900900034140c003100d0078100070010810303a040015000014504100b1031540a900304023023621003c48452540e40e1601c01040510380000445204a4107000c07142c00610480c1402d204104600c0000c0706100c1c000c01003e038041100402e0701d142c1041c6030005035a404d0f500e1a03a0200203090403ea904001e607040e02040000983c1c04100000308091401004928214030300e44194401c180f1080c810b50303521242e031103502c0b0b0225241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 738535458 1250 738534208 738534239
    0x4140910021e040b0d060f14040c02100e010213080f0d0c05030c0d0f0206160516060b0a031211061e13050706031d010204030203031806120a09030e030a0b01 69
    0xc0100e0355940001080c0b0394503400740e0041c881619020900c1c410716400380c001d1801030007000040d504081c0c2441020000d10380070120342403045454602158520340240300340d48166056040500150b00d030100078a003c4d60040c104618009000d0b00700103501900419409002559080640602405180d0031200800d8400007502c00f800200490740c4111420040080300c01c0c0d16460305d5202c004030b094080d050500003002c3c0075110030012000980c084d80201100c140980944445000e030031941403c8005020812402d6000081098048148101c124040101441654403024504119200c3c59241c00c000d850b180c110321a2903001d1040d84000000c11b0783e0014062a0490540000c2d031030701407604055034442002b1a0f600c607040f400701403140449050074540d403402903103041d1541d400300f65240f01e48040700d41e1001d60079480300c00690350381f412254918a0700f0200510f078100040c1040092044980490102704114030310f40c0541004a241040250008035a0985070318080701e4211303103a039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 738536708 1250 738535458 738535477
    0x2040b011205070309021005030f0118061d161412060d080a0f02060105030304030302071a0f04060f030614100c0c08120309060a050c0304061505041103060414091002 73
    0x1a08441d07802040c07801d1266030310510107130307401003001e2080d401400800c0700c0b01d031a000c007002020002c0020a000c100c2c040c604540c031038a44c440e22078414110110080041c2e41181c43d0825035007040224882c08007404030b0081c002141141c01c1c03000540030548140121690a46446009000c00180541402c01c1d5541c0500b002d060441a2416075492011541c402d0745040003092000c40700b00d40c550b80c100032182c050700050b03000f18601800c580303000e5901d150511a0075000c141500c0d40415014400d0240c8200b01c440507541e9442e59111000039006207450f190800000f40780000c00100552950100f0a041802031b00b011100c11800030211219139203886c0907030706c403540c4034000500300780c082103030100a49441c11500d40f6801c01180c40b80c01c2440c06004540160304050a000e400d1100c10304903600103610401c0011441c611321030003451644a5400564810303e0501c4401901740004004c503c10f240460307041000200c22000d520502c0010340d0140380030b1340405140c076203042e41c0341c0c0240300460 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 738537958 1250 738536708 738536717
    0x613060515040204090c1e0c02041121010806090316021908070801020403110a2d03150e0d0f0f0507050304150c0b070c0210120213090c0e04060f0302040b01 69
    0x850310002ca0b0507031384183e00440a0301c1d50b98181c1c0329182d42c42541d164404805035007041e0001151a4020120164100040e101b0340d6507501e41c010018404044a040c44000200494181908500b03806502c209220784d030b000f0301543c000600c54003030100c221421a8180c00c2c0340c062114140d001d0125a00800f449522001d880100120792214100025001440c032040096603030703410340c81e00701e001004000344140256824942801030b510200e009408180d00c951110011440c40000194894001d0b80040c0000d030383c00d80311031503041f515040702441241c4141210541d40d200c242c02c40740c0303c100d6820180000e8844c038a40304d45070b1184008042c11801141203c1c20070ba11516a00201e00741d14040701c0114005000440403c24900b111903805440303402d002408103103540101e101503020f40c7c852070401145801d81c1200c1c41d41a81501d40c503c0103a12200c01054458074000e004140c07050034a004220620304c00c10892800380140e8065030181034030a60504c2c40c640c2880081c00019907080d0601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 738539208 1250 738537958 738537991
    0x30a0e010c0f0507140a4a07081609051003020408060c040e0c0315060d09060509161e1205010b06030709141e0d0302160603140906130605 61
    0x252070401480080b81c0103801800720103140015507810f504285000c140103400611040101207100851b40020445400813a40540c4a00ca04000001200045001c0642d210345e900040481a5034905108001c00d4407091074a49034075070303e43c0000300c81c00002c0b00000c0311100140305909141c0c1440b03001d0010b1381405030815454007000703070402c0c1e004ca407090030001000c00c08002e2000c042900c60f8018046e000181e00c0e41c1040c05000400c9000c01384203074040d0702c0c009904420846582d0184a2040c0c001d8410000c905007010241e80b510010032809183c54201d103070129500020455040300c3c030003051001030860b072030042590414040c1c100251050b544e5104040d2950710340c04000c1d44108001c1e0344e0030801c1030604091192011b8a2104140505514120560b80003420f2005680003541211854611103040c90100c1c50030f001801c0f14500f0742d500e86800603a0a030550030102d9a098201003014176681c80c00f040c15540d000c01c4420350000b0150b00104404564940d00554000111000d0704400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738540458 1250 738539208 738539213
    0xc030e0a03140f180a05010314041709060a020609010515030703110d0602041502070603201308010e0c090a0e060c28050414010f2106120c030302190203030a0e010c 72
    0x359080310744c201c403507242140c040f4480c514001070030801522003420b00300a00c011041109008100c014001400c1407280c0c0f0103c07202c440c0c000d06480d101400244000d0741c81d00044c1d4002d40324031b800d0740d4520244d0b003801c021803c83c041d04044410343e4403015000340b04da84c4c0742d07440d005c440c440c043c1c104a8000d8002aa4500844c6890005001400034500120300c0142002c13070080c42c01c14141c1c0503008051070710342d18002c01d0f002d18900c5034001440500b41516018500001d4951103030325840802e4540c40d003280f5180c0c4070800320715405c441d07008a4580703000f9950841003c0030307114258002034068004000050121069601a080940b40d540c5480d118050700300340b40c0d16140d02d100c0e81002140000c241008521103400d1607e0068100b0f29001440760828900502184800f003031030181b00d0a42e02d048094251550b003c00020300b0175018890b8462940c2c03e040d0103410a41c002600180035070350b00c00d030141407030400902d01d0903070143c01140f400070600400c841c1d18039010b0320030b4100131004022902 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738541708 1250 738540458 738540487
    0xc20060910030b0a1203020f030415080703020c060a05060a050607020d020603250804170a0801170a0516030c0509070e0f011704060501061d030c0909071d010305010c030e0a0314 78
    0xd4508217800b20003600b42030501a10380034010fa0b8560641d070040000380151012030550211340729040c1031525654890040c180e019005101551015205510402001c011181c110328010802542c00080e690344a205221041c030a0050107504218446110001420418000c662094500b41080700401c10b00c01410003459000c1268030008190500f84014841c1c0030603410300c82c01081038191301e881d5503240c021b068040144680808003503030001c05002c1d00001e0040c000c1c0c10303504c2016200305510034500b07003000c1d0000340010340e13441210640205840c242044454003e50464545c00e100c186031008104100b80ea1400386410030410022208414800c443c5050240d4840e00003c156581004c4004140307400e0380080c0d010103001c20340a5507880c2c90100d0b01c10300c0740d20140d601780e00a9403503564a920300b5a565016034244200301a8001004c1d0003045030301d060380d00c90002400780c40d0b80d8941c200e0940b00841da02103091740200381c01c000000d001307903070107d07800e90003104003802d06a80c03181c000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738542958 1250 738541708 738541729
    0x60302031504030e040204060c0b090733020601050310020d110f0714060c0406261006030506010302120105040c020a0b0a0207030e0909070e1302100c20060910030b 72
    0x20781c02459003040c4420503400c01030300d01e484402a034046003010b282c400000d1000001c05000703064481c40c4004520401002d00030107000e00550b1421200b03640071106114210b0317070000034020000e028040c41d5403410b4404508981240c00040c0280800622110307001c009500c20f03c0482503a581c0e615842284800820141007210000080a03880c1d008030704000415a91407444440190410320400402d800d4a2060b074055655602d1300e00c200d440c580e039000d19130740380c0348141e40382000e0042c0812010181a881090a80b896543c0900443e1a5680154180c0c0524100001420300c480700600a50805501c0421007100d144100c0b500044141c444255400b429910004113039000507611090540255020004180035580007071146040003e0b01e48800c418005c02e60044c280c1f0000c50701d01000002c0d048800354005001d04400e896a040260001c000d010301150341a42d004403507612040e420082000c0628043c210034500b00b0340300700300420164085171075018141d0714110b2500c02c1e29a0300d03011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738544208 1250 738542958 738542983
    0xc070f06021b0a030f0e180f0711010b03190f0b0c0309010b0a080616211b02030711091b0d02211e041401090c090c09030c05060d06030203 61
    0x41c2e03129800400d107501c814002d01e1000b229401614030100190f4001004c0005103814070b03003160703070506000005d401e0382c5021444180c04111901840340102001003414003800b025250300404040b041011404d0f80c080c00d10b4a5070542102c1040428440c001c1d036400303042d80c443c0040150305045540c0d4044020b10a440716408400d012041081c28402407140361086101204c0ca2144549003640c0030380d44550083c4440316081d40b04030300c0702d01c1d1801241d40041030001d00380080002003403800700c20000c0815401040126100d00c00000c1c2245c0007204440710284c2100511205403115014001c205002405405192070001e541414841078032029101104a0f88000359484250b141201c14078844601c02003500010042440303107400c0410729000e20460801440c881c80c6d500c1d1b05008228540c215040b2000e5400c00c99001c0810034005404400e0340e5808401704800c08485e4070403180800c0600000700030790901c80041c4014a0000301804200c6002c0c9000302e0940e8980e0b01007801c0240034a030a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738545458 1250 738544208 738544211
    0x1121070b0d1122060e0d082101060f031a0d06110c12070611122d040302010f1a0105250609030210050a02070f0b06030a140705010e180f0c070f06 64
    0x403d40a5400900705001008285003ca5460300840c00284c0c480c0e1590000421a6800003880440c3c1403481010222080e0603e503007a889603520300340034000f80c0c03112125900281c54030061022044143c8002c03a418080030340020841122592407000405110f5002240b80e00117009608004908202d50200c0c04184c4180a44410340c03882d01000b643c2081045840d03242e0f06005074802c00c03550995440e030140c41400d034420149811640c907555110b4400c100c03000c1d580d02c01c04000915405401003480001c0142d020000300c001d808002e088940e14814407800168100081d4015103040700d44010500d1007005c1d0410a54030f56600c21003180c032003c1c0110003507000504003140b00f0565210f410f5010039601400e6141140c265541c2000381c3c48504010400d60039074011aa55440c100304402c102d1381d20181c6404e86242007400c4965820ba85e1040c07900248041d0907000d00e900308004500700003c0c2e01c00481041e612018150340100b20001c02490609200303010b0840071401309141f03402181d004150 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738546708 1250 738545458 738545497
    0xb0121020406081f061406070c0305030f070506060d0201120b27010608010806070219052103090c0f06160f0b07052a060718050603041121070b0d11 65
    0x10b00d034801c4a080840300751605d01d44407041101e284240c8907491300003400c485040ea91405490018501c100c10381000e4101c1c88041001d1080c2c200100c0103028403400741d811580941d032040304100d840e40303124000a00040103001c158942c2d5080d600030307010510004080010a0700c95072054401c110340c540200c510003083c43d00400c2015000a141070140401c00054546450302c1100655a625a00b00468184003e50414000e02c4400d1018400c1c1d181c90540c0c00c43d50740400114903c41e41c100380c3d02450036004038229028546000d205411049101030903982c10a410240c500207100e01f2040280c52071004182075000080b034009003140f140550b51030301612406224038000c1402a107080048090180361038407230300008005450b90340300c0c0c0c4600d009194880c0402c6800090203076a44501c1d0030403008824401000410107070542011410f46103102100c45640d5604034501318848d00b150709811010313085c042c02d11418004c0110b81c0110714085100307a00000c100c041507210741508a1744c020f03020b5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738547958 1250 738546708 738546733
    0x13060e0a0302132a0f1416050c030606061623030304030207150f022a030a030905031204050d03030f1107050607080901111204050703170d0f0203040b012102040608 72
    0x11403c03160a0202a04c01404404121000d400c1c0b00045088005110000c0024043c010b00241102c0c21804840040c04500b811490310545c0c41c40c0d20502103201c0d00800b400a19141046002e50f06d0011000c040c88400380003589502c1070a4410862503418070241c1c50b061520001c1c00c01c001c40c05103220b9801011058603000001c0300c1d880c0d04030608402c0212210410754bc0c0359001071b5040e0b8454110802001071080c0c1c44c2040b42140c40c281015405d030140f10f0112003859085207010382200c1064080e50740d0302e982418a1915480303203019142c0d110005080340c20100c0d200794440243e03500076a200152034410000100465008104121034907440a410010890741c080b98154000b0b921600a116903d2031203030500c040e0040030001e5a1105c0424001028002d04001e803000454200303070603d08409246140d08010390000c541d10400310f040201c12054040719108680c030594001c160018684d003044401094000407810244c402d400700c40080300560f5407446a000245901c01c0123050300503202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738549208 1250 738547958 738547991
    0xa0509191505130203060d1401140c070c170703020405011715100501030b0a050409030203040e160e101806020c040f05010302150a0c1506050a050613060e0a030213 72
    0x3031222800300e800d50710308020684441034000c41d1a10244005600d0359141c1000c02e01c0d40d1004600640180910380201c004a8010752049940320062540c40300c13183c0e20120040c1d020705c80d00e140140607120342d91080056260310407001704482003d00c16200d95503543c0e000034098032000c0e000341032003e880c2d001821840c842007241c0c0002c21407002c82081c9078078041c0042e140540461080c40c4c1456181d095254a603035a20707142a0180000500c00c00c800d14607410000e640c0e420501800308040c68100c04101c004143c400c3d030006400017580d07140540c01541060064188000ea610700c14024001012080d940e11815150058030f980c0e8010034002c08400204019a0000899100b071f0030720b80707801800580c0301c80c103076036400c00c490400099031a00340580c00c8030410a44039014000d0500300340110b400000c076411600c01c880084a1011140340c41d5810864240314901e1105c445810700d503410003406000e2141e407900001c2c02442c2e0729070300d503482e00442c2e03041c08036021000c811070340d0b200c0d02815121707074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738550458 1250 738549208 738549221
    0x13050603190c081b0a0509070e130f0f0507261b04120f15090203100c020a0b0f040c0501030e060711011506030203012d061416110406090506030a020f0a050919 70
    0x488401e01f0500b400310016140240c2065924000e02100e09041c07204001c60308811000e598220080100d117039441c1c2c000c40104000c3c1c6501c00007030300038614120002040741c419410b00300000398964068807001c80c42c10380b140350400345942c400410f001c0000e552901241e2094030a0040c05100403d040304e1600da00f001c0340c0e009d00c810607146407841c503001584000641c0040500e44078000228030b84102e00c03d920f42800361600400388401401009000c4130f001d10301500440c8030382914030441c5d441e40015030640e1904182d02c0780c180c2c0802c1c00128503902c1015011000d40b070304400000c1d84510302c00719411440030f40d004540441d800000400201051084207018004440c0002c07404c0d10812000c4464500d00780719a03401c000d03005d59602d500045aa04544150194854402c0115014940040320350b03942c44219109a182402c00030f144c040038000d540c4100001000781015071120b508001922072482c400603000100c4100c0440c40d512895040c03809070300003803030700c14501034003d0804007603e88 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738551708 1250 738550458 738550469
    0xc02060a02060405011401080a080711041503140a0213090c0b03091501090b01020a0b0a0e1009020f0a050a060c05070801050a020924030103080c0102070204060b0913050603190c081b0a 81
    0x20040010041483c0c08100709e05115800a407555458202d400c280c821030900c2841d160340715180280c075100c0c1001107040c540480e482107120206a07c0084110758035502c44130b80281d08410f0010600c0354100482d401064801c2c885c64291000e5901c42015a060342c108464001c0c250707000541c2c030b14010301400300c504c2c01813441c184180800c0358683d000075100c1f138001000612114a1034082034002ea0380341c000c000007a2100048400e48030381125100081c4c0021b0310141c0c0a03c522030030041190801c001944143c0e04050b0506400525000c021101100742d0441a1118020b41c1404164001c081c020b042c0120300451300907841740a040d0400c100342c1c82d103400c441002400c0f030f00201007588044c8140c0c0d0451b0b80199440d5114031610b00d405000e0700c00c03100c0083d07104d072804002190082c400c001130710a60740d00342c40c0c280d442d019003000f01e4100d4600341c0c0c45540c164481c100107480550a5a20720074494414020b5400003076681c648685821449074140c2000440c02580c90300d50309054003140000e11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738552958 1250 738551708 738551741
    0xf030228020d030818010905030405010306050f0a06051b0303090f071217071401051e010f061e020708070605040603050f06011b05031903060e0108070b0d0c0c02060a0206040501 78
    0x1a01940010410310b40080002d042c82002d80000d4645d080e110307441005541d24a00074030801200346407294403035005001d035a001c01e203003404c00300f00d80c146070203c1d0101071400742000c000c99050000a4506400603858100d420b0000180580c401c41c00380003460080007104014001160400305c0981050100e401c40990a0030b102040004640d45020182c0c0d08003621840c41d40e036900506045c070030203124540442d155800c20060000c60210030000e4040c0c0403007808002c8440e40c0710181e01d031001c480c03440f44100141c000001d00842c0d003070000c3c0454104c00180100c4034221f40d200c1000d8108a09640a83c011440120703040002c0c642600400c0da000895003050601441d00a001810003d00504070350382607103203e11401c04100080040701d02440b0303182820000c842d541f1200030050b0809008100c00201400d00004e000c820000c2c0c0042a1010040034500303064504041e50001c0000c0c80b0304400300810b9910003800741e1a00001015590441d901400240c034050515609458039070130200080c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738554208 1250 738552958 738553033
    0x106080906040b070c20030105010b1e13030516090b2b0c091b09080a030503040209040503040e0c09100f210230071d0d030c0f0302 58
    0xd51000c9a5694403a62140340c420064450703c100300c40c10040780e00010600300003240c80c10b6440802c8405141070074800c0b0001c0c885aa01e8800189860044d0340b1710a100e00e009145e420140c1c100d00026210449144584440c10ba0750398856a14011500c9903001c00e09440f440c0c28817400e4124000c0e4403441000340d90a000f0354800501400e01910b00c00b0152000c000f11402403010849180781240040c14480010b00207513030940854030070010140082000f0420510001810350301c0420041905600758883da03041d66110b0702402084180100111005d0108200200f0071000030100140505800102c1913107848461081c4401101c2144004d02801800c068800740d403640700340208082080b0301400429540e015950314082c0c050001083ca10081c40e412141c0c3c20021040c41d03040c100c1042c100b820480d112003400761292441464007401162181520380503505000490070b020350b200e0300c0c1c40c120295498468446010700362030f0480040e00424401d003882c030008903005120060803580341618 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738555458 1250 738554208 738554221
    0xe03091521102d0305010e070602011401090b0d05100b0108090c1e0a090e030702030706090e0604200a030e06090f0613050c0a0b130b0c150405011107060b09010608 72
    0x1c2c001c02c1c0728040c4204452180e504282001448001c07280e20107551600e542d0341c82c2e19140f4080c10400c80606014131507050000f40e802e01c140101010300310f003a23481030816400c000d4000c01620147e0940d5410000c0c4511000014804100210b04641c519000098000440c00018402c400280903241d00c1d520152405032142d80d00f0020081d01c1a03821298032012202d400410941c001c00d5200c1034246245c000403180007003001c4010203080c0d1088054a900b03a44429050b91030101b2405082507404030000010031a00786a03002010070642042d96011294591940c8400c03503202c520511300098076026410381c42c8004100158001007504041c00504c5014661035a0300c103070050101c0c3d082c0030b4071040302040c030030280038595090f00043c1c041e0a0840d04c0d481c500c4002e9001c21090401080c400c0c80004800d00c04c10256120410b068010f008124148621580440d20182098072035540e2188103540d584030390801421003900c03035100404d110700e10208001c4582d405038443d03400d102001c001c0282 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738556708 1250 738555458 738555481
    0x21306030b011b140a0803010302030d26061f050a0215092508030403031701270c02150a0e0f03090105041707050d0305070b1501120e03091521 63
    0x9444000d010f40210601d42420181c0c144110072030001158040c0c00000305c20b11000e48000e5042e2402602203509800400c94221900281144000020307840da00d403e5807842034001c0c003d44c0000c4010141e4080240d003480b003c4000340c00410754800320f000000c02d22016034050041c41c845010801950442d454000083c50700e8a880d948004612039810800f6400d510144012b90301600340102182d072900d48a10300901417003101002c2d1380b201c9032550000142400e4101c0407030b844030002c0c80c2c00c0105058032010301d0041c10243d1101800e501508480e0981c180c141c166042c4a24071011000c1611844a00b80d1401e0405c0b0300040d94540d08200407104260b40c1000448040f6800d049004a4182180c2070250038000c554101c0e540c040c0440c16050181944030b00a44100b5000b07501d20a41030f11000d00c0c900040c0164074080d40420740f0026000c00780d030940d510071101010008141c3c0d203031607480320000d000000b003090603c107820302c0481c4c42200f12070790541882c404010f818202c019401c044c5800c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738557958 1250 738556708 738556727
    0x180d03060e2a0d0635010b06090609240a120509030f0a140304030306090606031a090a0e0601080a0b181902010c080c060103111c0f030e0310021306030b01 68
    0x144030b02001884103000190f9038000c5009040345044000b0341c0c2da15003085802640d010003451080c000781980c103450044103100304034980b2801000140750481d00380900a40d6041a46103d84c013900003003914050326400c000c011420072400e820155907400c0030001518201404030f0515210f803800d03081210a64000085a100301c80b0044115140d110640041312032000c102c59503110300c403020003400201074058000c80c05480d0130400510031151510b03011030440c0e41041e0820252010410350300d602c0d050810303416410013500040412240c00c00441249091400e9000c02415801840d0110601440d5041d0725000703a40360381c0c0fa0f00d902ca45035031840d582c5c003012020318114501c0f0b0f4130081c0c21603000b0020f0f102059481001c550700c641d100300e07106803101340911080d5441030141800c1c0c1202c0c0790260f000040c030b49003070440b0028040c9544a00341c800e000c2010450501c442c070141c001c1c0640d41000003084010000e40c1c0503135035035035003002000d5090582d4009018182407101d5817085a0700b160140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738559208 1250 738557958 738558031
    0x60603161211041508100b0607082a011118011701090c210e0c04060b0f03041505040f05190308070e030a0c120b1803040e180d03060e 59
    0x391511851500081c0050000e449420201d85803020001120301c008030b906c022002d0403000410000d442c42d001d2080e40e108010001b00304000c00c20401d00e115158502c0b0300440c26048151030000010a0301040c00c40700000b48030481014041415402410300400300710004900f880d02320a000604100e000003a001030044060103900c1d14440c400e6684558640c05401500d2501c600915210604120040003410004240c80c01407280c10000b43c28103014601c1281c490310f10706440c11210500d500031f00d4001400480d4102ea040c010f0b51841050b5000c2e050080e8010703a00c0050459071454001d10346401000000d00caa80301ca1885070200b5080503019500c201c80c0e0511250600c0c0b210b001900744000034200400d18200d80c0d0010908103064528003464500c03801e0440070383c0e16001d13640c8140106100440c0703115442040148102089001a26041801c0e140904501d4968100c4d807410072042e0700c000c6000a643d100f040000c0148601c045030021b40c05601081a002d52201009940440c000e84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738560458 1250 738559208 738559223
    0x60f0d080a020f0607050a0f0306050a05040915150513090f03031a031608010b0402040b0414060f0c0606150910030c020724090b0c0a02101704050606031612 69
    0x507800380e18020300c8910710150900064512515000768041c085403c0703c84954001001c0300c100801d00380c0a80700b044180d840003405100a10701e845d003000040e0100000860b03000a00300c0000040210302d0140340180784501d485410420700303000510620001c42d5000302101c0c4c1c20051041c000c035030381101543d02a50140f5020548402800c8498101d50001041503010700c00c0d5582e6545c000d070341005107015581108000d00c0f201d07a045040105a020754000e800c2040c0341044100150303a104e505070111001d0150941d420408065401e11490f08580002d03036282c1c100d0401c12140c4d1410701103d81881401c1944682010751800c0401c141c00781082014081c5030303a4400b4010258000c1140d0b000801e24104c07441d41411201c000c20800760182d2500c400410b445800c0840c580782803200b5140c060740084010840e0111310b8003048541000b151261052113a4480b000403110305184001e0721460090000b03013003a05001c030a0500d042084042c01c803201104034424007640342d0141d0a40780e01d0750003299 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738561708 1250 738560458 738560467
    0xc1e03070632450a0506160206062103181801060e10030e010c0e1f0804080313080417070e090706050f0f0c06150a06120c0207050411040e060f0d08 65
    0x8080014140c2c00c00c04070f00d240c80c010f000c2e0400c3c01d000074030003900600c140c0a07141c06444490003890109043c11001000d6084540003607801d0500444440718013288100c0e26039603018160605d0700310350001e040000b00c092040050100c600f0700c0002e10381e00a01417502c00049614240c0001c2250520101486c803810307802c203070209034038401d42040c07400f5814203000b00801811a000a40b294107540503580c0a0900c2d041c450320000075054880042100b20740b90625140c5e42d40e50384011550008040110100c48040c07600302249003040508040e000b1103807e012440d81e0b4480703c5140c040d941c0c0c001c0184041030805c1214842c0003040d60300403139807981815511071000b02c42483d168065820014100c070404030b10b800117000001074081c040c415244100300c0c082008403d102c1494480e001c0c0700c0100d082200d41d0300b001c5041d5801140c4d5201c9074030507940540c0d22880064150342c02c8000c515080c000c04174062002c036100c0803880707401000440300504100341031030105107903610b100d40c0500310503408075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738562958 1250 738561708 738561781
    0x1051f051e031f0501050904110d03030e12040806060a03080d02070203010204120501021b0102070506010509070219080901030e1908030c070b0702030a080901020c1e03070632 77
    0x18032050794000003030075500c05240019054088010021200f80a0b5060000014050404a070f0090045800510340801844900180104000100c400301d04142d0313500a650441202404007640fa40000a075156a4600c0c1c40d01044c9440409440c051044901200820008400b00200c03070003203801980c05a1030341c040703000090082c0034940c44031441c00c8010060204115043d07009015221803403001003901031014900360308030f01400034002c08640c000c41c01030000c0e01c0c1100d03105034003c4251040310214070b114075400a00001c0ea400c100d4041c1c0c8003244100203580c050007010040050240280192982d005800d9078501d130218018241c0300d0000081208210b2081c12500500c0c0c201030200c80a0900c01c1c8000e50703d60101800c40000340c60103002c1480c880e018001c40d94600c200200802c4007a0300485a82142c11080c41402d9a40c170041050000064207400b6000c4400c120030804805e460306d00310303010480c98002c0f4901002c5215201001014440100340350700d034200c0021011000f80840c8d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738564208 1250 738562958 738562999
    0x4180b100807080c0108070810140604050619080603030a0519090b070b06010905040506130b010302160309050a0501080f1b040302060705100e0115120c030b10030501051f05 76
    0x58008210354010b5240200310002c0c0000c00101404081e610218181d45410040752021000d0740d0b4034020f07002c0618200f140441c113031103ca8001d07034010016441c15a45100080d800d503c51005100211494215500701e0760700030a54540c0400705a014518140124800521f2481203000c404101103060104281982c0b0031011000a400030380740317007940c0d801c90381040742806108507030044c00548980e401050a05060003030900848001e031000d080c442d074031040364001d0b100c04900c6c00d0405034280201442d0f2045440b007204000d00907150000064101405e0110b042c6a640005050281030f01c2400851403141d40c1c050740c00310288074416000e801d0b20240d442640b1556101961180c00401d458086c0038002c5510040303194900400c0003000740481125007614040407400b5003115603040b08200840b940c04d9908070300343c0715901e07007a034954aa80c0d8984461009507408140b4501f00c00c014000c004c000d214242d044003454a01d140c60001040d81d10003a23210b40d014050007071282a0000d0162100b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738565458 1250 738564208 738564241
    0x18030d03112d0406022a0a2306030a0b040f02131502030f0d02040905100803030c09040902090c03161713061b0203030a0609060e010501140705060f0f0604180b 70
    0x180d00c103aa80c9590744e8500941d103c1d008154240d0410301710404a03c410341c2083d91501602c001742211010305d02d0580c56680c510410080e81d60501c99800c0c031541c0b1070ba541030080d441041181c2002070003030141002d1008603002508005030f0103104004002000c2d40d06c80780d801c219203100c200d5480c84004030b4012401d5005007060107407124800f040d004080160ba80240003590980344081080b95174078140031840d02042d1040c103099800c1000440e40300c5a00d4001080c501d14060008905903800c0d5000c41c1c0c034148219501e4444820110134072001a443c0800c5140c3c1d85594a01050100600302001074900005800d0509a20104c0280310811405801c082c06039402d01800415014110501940320340c0100c0f20a65094074041010503240428842e0005031510000e8600280e0708180c015181444104d008508196051201400140302007003803e10074680c442c0c1c0c3e44910304005141d0006030350040c3c4014480c5040100040c0030724140091000d445030422140c0340305480f00c2c0c5070007601c90320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738566708 1250 738565458 738565537
    0x21170f0615030c071109130b06030f1006060201150e0121020d03020109020a050414061003020405030d0e01030506270712060e0609070305090607121118030d0311 71
    0x310400c02c251021002620856005601c0610b000c04e45c1c4081240d1a0070448002264003602280c80001c9500e0b00d0016074030140240460b03a080c5046e6011a14120701c02c1c9042040540f1000309002d820b9080c0641c14040581c034100c02c95043c10410100c007000014050b81c1c0f28045035035048501c81807100018030312650098141e285d00c61150030000e002c2c001010b410707806078480036400203c6052604c80c0030103c81c42070030144902c1d29081c003048001c800d00c010754020540c0030302006c50a941c00f8004084001481c2d2a40154070b241f0074005002d071000200014455000d0110000d41c0c441c000b03010005c4049550b07003c4000e5929238005403102d00b4030100601603189021001b00c0c1e416111680113009500484074514680c0c2e075640304406840d000c4034200700940080f00420b0380a4010390104504046070080030480c00362948207190356030404040d00709003000d0003050600505081c45202d9410300c02d4a018400103003044c03c4001c03180b20350401c80503000ca0060244180190035440105031b200b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738567958 1250 738566708 738566749
    0x180914100e010b0109050112110706180c052d0604051f11010605010507030e01030609021b100506010207030b070918020714120313050a020a1202030f2b050c060421170f06 75
    0x1a40400e040c1e00d408408004130350120300f2001c049464505241d8181c240033f42a181911900140c8138801610001010f48030f400202c180800300e4665100801c40c244850216801300c0585400e0600600325241d408001a0607490301c00e0a01413039a21104840e812038040c00c240c0040301c0c2c42c000490040549500000f01940b0200d041c0401510403074505018031203110031150002c60344805030040702e009403095030142c1c0c024881013000039001101c060f0f0285440c20712021440d5692248114207810440c1c00c900258006491420000300b0190500c0b80b60b41d060090902400d10024450366200140c04e560030700d1101c80c0124104001000640c100650142800340256a184440c0000c0700b8000d070220302c0f80c098105600d10b15040041c185a0200c502d0010458206991000c039024028107020b00e000c000302003010042c4a081000854000c6114490300901400b414660511240e050807494042198100d0255031034001045065040380d00318010034003903100c03040001c1221031458548106107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738569208 1250 738567958 738567971
    0xb0a051c060e07030c17042a080106030c06020610170a350f0301030803070c050618071d16022103040b10180914100e010b0109050112110706 62
    0x640d142020b40b801040c00d5182408003000841c8140e030003181182c04498103440c050005000b00f1081d040400181c14840e103a1502d030290320510809012150b00640e4590791681d00c200104159050041c00402d203600c05030a45090103c0c04c0d080d0540148908001d0860265050540aa050109030009a8000056415042c07404030340202f000701d44400f0401e40c8043c8602000c0880c4607000c8441150308a00c000d072450382107035503242654102511013000c00582e072601c1e20005800f000024003440d03110705e2816041303600076556850000903801ca080c0258841e0204d121484d1140d80241c3c0001d001201c40c10b4451a07007000b245000320034640300c00c4401400c14007400303008400000b540910b010301000d07445a91041d440c480d40040c28030490300070a90803e10545450f01941c003075611103100340c9a0040c041c441200079480c1001411300740c2e00140e6113005c49511f0080074428074083c0c000a081089443c0c0c40d220020b80040c41d041003109009c0d07180c5a4440c44500300c0c1084801e81c070750003081007002c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738570458 1250 738569208 738569219
    0x61210121a0606070201051606091a0610030e1f020c070f210f08180306070201021c09020904020607050c060a0e13060f0b090d050a080705060c040b0a051c06 69
    0x80840c0100c07090854140d0000c00e141e8100902103030a07040d010303180c080c079180c16000100c6901321101c10a80d05541e580401000161003075071511100c1460b040e0a0560741807002c10081d8107200c03000401c2c00d040c80e00c10100010300340400d04100c3c05076075101e0700014108100801c3d000e44915440050140203513000800d01c0341c0c0700044c03002921443c20751118504c1c2c0ca1030100001044550b000b40401356090030b44000200e40900410160f420752081d5218001c95001080c54100180d13410005071350042040c600010301d41011003e44541c1030014061441c2e2900451030045024002a000309000140c143c03e200040041d080959001707400685d580c00e400302d00a00c060400403645105041d1035000e40205001b50058106580300709421850386071420350100c4103540300300d40d010b4100c03051902d09404274101b40f01403488240600b42480d9a810303640703040741c18600010180e6243d00303030038403044c802d5030388103410f807007400203903080940c0e851801e070040340c214074008c807900f0f074a0074100031002c1078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738571708 1250 738570458 738570473
    0x1e01200a0c0e0903091302090907121109090408091c08070209010806090705120f030f07060c02150604270f0b010501091a03060409080d0b090703020906121012 70
    0x845009160703040c4001e480b00c000c001d40b10700507650b07400d00354010310100780703d4034000c030a410054003811801441c02007581d000c200045d100b12602c201180039840d00100110355402a11308210300c40e20100d14014800f40044c4c44004058409040d5103404160034405450340405681305200841440c00c43d0b101c180351000c0c865001e0182213003e990204000541d1010018007140980d440f00054610f0b103080c001840754541400300522801d100c0c002c1c01c0d6901d10418070090141200e8240c5540e03440855087c400d05544020240d6021540705210304442c544002000d035420a10031100490303694404038a0320300356210300c2c107450b040d0410780800034100010720a004141c035104951280c9d0507030740c9100550780b01c1c4003449603000d4854444100c102036480500210350101b0000c0c1b00040340e071459214000160040c140540713030f5658a003c401d05038030301145120751001042c13809521300340171000852000d0041300320306601c6925250110780d68401011007180039010b4808848210b10340b0381000c1ca07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738572958 1250 738571708 738571723
    0x60907091112060904080d0606050702040c14071401090605090d0914063c04090b0a18021308032208030a090b1605010c05031e01051e0120 61
    0x10069181040d020009401d050503030b01d0b19456040324561030303a904410b0100140c0020f00840d0200010030076200c1075101480b8000c0900440d41d0b0780c41d1a5a02031040c0070272104000d07646414402103424215101030001c08032403100d81e20806800041740205010740c094120034400030605801d105c100a9885000034000e14000030907a580b5021540c0c800800500280d48004560004800c0011804903852181c400c3d640e003580b4181e0600c000c680b0019082e0307440c50314140c1d00280000280c1084425501c2c0903031000010212080c4215a141c01162605002c0704000041c0b45500420f000703002400c011086001400c080003500c0e524a006604c4229408190a00055554a049020540d8000001035134551803864565010359030230200c4190740c5400400400200080074202c00d000210207007d61007090340540c58a035168101440d041402405003500528002c50700c80042107079a49090050b001500c00082007003180a61800480b21044907411084908405000782082d0420010350711 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738574208 1250 738572958 738572969
    0x507030f02130b060a0c030c0b16121505011110050a0b03160302061827040b06030604030e0f1c0804090b0d0f030f2d0f09080304090504080408060907 66
    0x70840d40400c030180000c43d001c031000140c0003103041c850104c00034002d0303081c0c0408a00030b0504065101a9560380a40e11030211742c03604800e090460402d040503000302c010805480581c20900a29211040740c003c1d8402c148a41410054925540001c0d031f042480484409403000c6401c1c001071070710380750040c041c1c2065003d450180c4038645074040164a81740d80030042d6640188090f190140f040351140109500101d22548140744005e44000201c15138410034041204050044840c0b8007800c20341d10403c0010403140c02a0010303400c00000990120800001303c2d0211802d07111010b10901041d52120402c0d000000341800714000010720940e040134004940504c20103200c4802580c061200728103020300010201500e107840710000074000c4d454902811150710f402c001c511b0507100b10024411800300048445080c4200c0031240070382c4902050300d2040281805414140f4006003907940b03201da4810001290f9441c004502000040f400700d900500182d001c80e201800c0418000751201d0081c443e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738575458 1250 738574208 738574219
    0x903020c0d0203060118020405030703030201270203060612030d150503010f091a06030a060519060506270a0302060f0307080a090b0105010809010b060c0f0705060301141c0507030f02 80
    0x209641d140100c0260041076001c1e001e800315910b007040070891700700e00d0100d09040640a000c003103441d03281003044c04001c50003036001241c003408010841e24101104640005200c60120070341001d80c50001d19141c0010050342c1c4402c50408944030700341113008109a14442074104a0380c01110340d2140c10340410394004038000c10144e9800c1c0b0b222404c8a030880782c010000f030001e400355031940c4a078407c0350358410005030a0790f50040256540100b19001201e0f442c0f400300703003503041c00710504c04c0d841280040e0400b551028641151701c074034502d4000c2503e00744810710264058040e943d8580405400007594080c103110703181d08000405007030301d801c12601000011240400500440c0f000d0041800703040d000b0442c045035900346070046072510030040c078144007903413205404262515020028404110010080c007910003400ca07005050a555030b0045104000600c01030280c151100d90b0190315050840b007415032061821000300b00701c0c61202c4003a00358028540000284003c026a005c2d60a208032070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738576708 1250 738575458 738575473
    0x4150e0c0111073215030405100b150904091406042a031202011805010606020c19140a091e18120e060c0304090c1704030f05070c080d03090302 63
    0x7265507911852040105080018040f40940600e00244004e4040f13618601114690010042910b1100c1c40360b00c01d507440400410001800014070000b40030003485a8180710141403c0c00181d980c0c1c0806107048281400051189076030760b540e42c00907030499400200141c100000051068a45c0e8003102d06482050001c45442010825940d08040f03041d030a14101702d0301c3d400c50b200d140e1150061031814003590b680340c0407131101401c0c54801c84049403040d8000f05141e0b0801600038103000c04128414018101c4c00e41c004500343d0f4480300c51040e68550240100100c4032800018807003c0180d0103c2851803410700045100c0714840c00c807054250402c2c405000c000302460410b485882d404034050040c0c005c10040c0d00009106a4103003510042c010300903424100b205a80d05c1c10740d8010303130108be080ca0342c5188120241390009640c12903d0782505811030b0780c0c58107403800341580d05c1c441105010000009016010800c0e07541c00c1d00d02400c00c02e01110380410610102600a00800780190301500c80c648 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738577958 1250 738576708 738576737
    0xe010b0d08040902030c09040f0605190509041e080d0c1704050615032e0c091503021c0606081b0307020c01030e010908030702030a09050d030503040b04150e0c01 71
    0x8a00c0590103a00801941c9040e1601d04818002c0d080500702800070402082008526521401008002c140b1b039840011558904410044000c03046101851180c5031150300f04801d6580180c207960060b0400300b020043c03131150310b204240013007845004002040104071100000d0785a400401409001d0f15181158155041f0580c00f950080754010a0703540004001200011520901c2d42a02405400c4070f0308401000d0b411b03840d810054040c404459410218102410002e00540b80c01441c1800c242c50607d0604e2000c6281400030040c442c1495000255103640c6a40455a800c482c3c074104002c0023075586030b4000030084641941c02c05090030500000c104100b40c00c1c1c0440380504602d07001450304102d00c10042d805000c0700691010155a9106001e0100307030344100841c41000f1540c00355903601421400a41540794540006020310080b24001002a07000700031203401c150420826800c603078503132812801c04981c00c80c9000000c3c0c20500a079120700c0d0001001c03c0039603400d8a81e100c40800c4130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738579208 1250 738577958 738577969
    0x4090f14240415060e0c250507050613180b0102010b040b06191404080304080712020607240608100b120705012d0203040315020a02100f1d010e010b 65
    0x1c500c4804144908010a00040300300842c010255034002c004182240e40b4501c3c400400001c03282004000780000e4442d65400f0000300300b0301880c2e103007041c0e1450f141803905e800d6613680140c0102406503030001b96101100903030140035030080484145d0000316803202c90719039002d84031943c06e0a026608080540c2002c0c030b00b60050f118061406400d10381440615050140c034107259080000600c24a002c8070711281c1038040090018250007801140e070381d841e10400070321b4908290700118900508480ba80c0050b0b88500446019035000700d50102d103000310100d02c03440f0004000707800346003e1605a0000c0d5219001c00c2d16042403080744000c11209a4400c240990011140350074035140c0c001541c144400e6019201000076040b001440e140c14900c04191070189543c42e82d44040540d10100c3d007003040000c03241c17425149200c402415401c10342c503004041c0da1076120100c984081510707000b0350040001281d002110244a040820300030028900c02c1500a02008580c288154203003400e480450420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738580458 1250 738579208 738579253
    0x403030311120402061e071101080c030106090333050f150d1e1a060312040806072304030b04110a0e04080c011b020c03010501090506030a020f04090f14 67
    0x400c030071000d0b80c3e03516400c000160f80002d000c0d8107807001000e0703801d00451065003d080c1d10b5214003544102d41d48407000250104400502c214820740d4200011b0080c43c0e4011810001c41368890310490b018100320a840c002d00408840007408000d607240010451082c0340c000300d024001402ca51801903e13286030344030b082d008202c0241e421034510942c00d00090840c5600c0b584c01892001031030ba411400740c0e143c1c501c2a44280b91203030342c1040c060900c80c09103800d216845500380f120350103600d414600020241c5440000300b0030400d025550110083d03e20b1041e9400302242d800c2c0f403800e6901ea40302c0c5010030000307506607410b481c400b036106e114805505229011006540c001e042c0d0041e540c1d595901c00080c1c1d800180c1c030208554a803601c0070106141c8200100030350501d90054018101e00405041c2182d5050f440740002c2030510052061585000c241a2400c603010745071340c4042102d200200d80a8908454014060621031040c2c074144088099280100c200d140150794412580441c001c40c0c4801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738581708 1250 738580458 738580477
    0x807031116060908030c070c080a121803320c010c12090302220506090f1603020c061f0b0708090904140d02030a02070f080706050c10050c0403030311 66
    0xc003040381d01a400030031907070840014402c1002051a080d29a6042119003082d0b441d03400201c0081400c000308100359240e240505442c2000744941d0020383c603500e0002c42a05c140f1420300c101860000556144410350700040d41e088500c201e170032840d9203d0008140c40316541c0fa1040c0d1000b152045a11a02043d00b4030811416941d818000080b9125101d00c006a60315910a10500e000008016214070302016003041c5a814102d0402081042410907100e0007000648112816020001100540000c4a400c1101c40c1c225983c3c00010b003405138000d1086488042c02d40c07203080108902c000301070707a80d4034604401301403010f1215030b00d2854180b580115000100a07500c14044940e83c1e0800d400c9180d48175000d20f1150500d1140d040c2524144000042c051006030000240040c1c0c0039010030544000307101c2070402d152054030b403280700c42e2140300d01c2c09940108100041c0c0569103410400411000581c0114108907070b04180700c60040e10340c0039200c12000f281c1450200c0d02c6440022069801200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738582958 1250 738581708 738581741
    0xb0426120a0b0111010606021c17160210020301030b0402010e0d05070b1e0304050d1d1f0201090c06050409050708070203070201140c0a08090a2907030201090b0c0703080703 76
    0x11961030050000c2d1000d609054108040300e10a8018000309004410050a003030b000380070300c8181c0460b031450040d000000c00d82400380304402aa901c07000e618010b42e02c1003901010941c4099410012420101c0e0219844030351800840084103124001245070700552003601c501030f14045240134412081d20441c0090002d40040b5810800720049400501075407400000c01034081804407031001c1c032a08262016103080d401430400219550f00404481e0f8584000c00780011a40700c1c941c005101c0403685403800300351014812428000764000d402048010341c2c03210040004c103407106401060354000b80b1500c0f403440c0c20000841d00490040c03d0007030007052141d01840c0b510f040358006413928441e20702c4100030a0300402203180300343c20510a0b0884e6501c9142026036800118042040d40c0400d030b0444840303a9a0020015112400742d490001d032038907594001600c4092504013640101030307100000d000103140c241000808008200140711840c42521140340c036480d498411800c85180003007000480c2c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738584208 1250 738582958 738582961
    0x1202131104260618100c0c02040603050102031005040b0f06090609061b0c0a030f0f02010207081e1002030c030414010b060a0e030609160b130f08010606080702010902090a020f070b042612 82
    0x5e032180d80056081e00424103003148207800b00d0707004c60201c0310194030070b50f00c0e03941c04000c0c080c6100031092aa0014542180c06001c1500388000083c03c182003c140c2520603c8001520040d82d04c0ea4000c1d03c0400b0310040c161354443c140346160f02c210140160a66566010382e0302c0045291070a10501c074280c03a00302d02c510f40700724156a207417000308031030140982c1944186c2c000010000b00410148501200062402c06180c3c9049002d0b864401c08035418800c440c0144100081603140600340d80d4800d820003480440c5821001c1c5182c01012006151900880300142030307000d4070382040c010400301c1800c0e021101c0b10790701d4a19842d10b4500d1000781036458150450700b04034074103040004e040c104061501c600782003071b5684d1582595a0442d4403a90b0240d44440081042c42e802896080d0b000f072040c0003d1014854a50008001c0040144801c5450f40e02045403d19401117000b91441180d0144402840707007410b0409400403450f0b08980c0d2042c11000c9403005c6003a550b40c1c103030b03408680d040c42004401d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738585458 1250 738584208 738584233
    0xe0903070f05011d0106080c09090c091003060504030206011d090a06020307170108070e09030a0203030103150b030a1b0819110d050a060609061202131104260618 71
    0xd0078040241c49039074803204241c040f68205010720003a902c0e0395000141003450004502e00305940d448a0750312802e00401000f03451800420308010019044640c059191f40d04440041110b4003900041c3c0110301e002d080004050300000c4040c16110001203013054401e8403c01340b0313480207013122200ea080e00426103000c0081ca1640145402c00824140841c1c029140c450522241c00c00340d228610a50000c4010081005d00201c200d8001d01140302442c900071400c10069038920061200504624482c1224400d160a95010400040009060301c0c04620745040040c82c500440c4020300c00c011000c800010300082c0060201440e1400d080d80c070820345066140c0c030342440b180000181c1c10128800e00840012014804021198030035080007484604100410301160801d41044503c0d00500d60070310056500e18040704025030308440007082801d00c036982404580915400720071040300c400e110718884e4404901000000350450200e0704156110f00e103070b00d00c00c0c0070b02c006102c0903001607491040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738586708 1250 738585458 738585473
    0x406050d110109080a0f1106070203061f032a080303070c0209041e05061501080403140d0b06040f0503160e1303030b0910150207060f03021606091b0e090307 69
    0x500078141060b07080d090351154030700e050450943d022502140e00200020400150320a681507820781622614145801a40480e03078501014106c02c04281c5002e41001c0084500c0b002c841c09164022103211200d061041728080d00100440350141d4080030b4080410074000c00402c0d01d1040c121903882a41607c00d503000e202d00c130705001d0010f0303800000c0710100d0740c101c407042144040309900c248004c101903d081121140a61800c2c00040e041241c0341f4244408260701c50341d03c481403140511415501c241e8200040000e00c84d204565820050104002070404640d10891040706d0080d030540b20610108022140141010700400c002c1c184400301041001d8545210b1800b558800d00340007548140c02c1b400190600c0080750382913011a00640c06120108548602d981192011700040c91180e040c072002520ba90403440d2908101503000c42c850403080200b42501c590903812100800c6443c11500382961007a0020fa001d100c642d0044c2c0001814200c2c01d00c650f0321611100024500b8030400303641c0d144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738587958 1250 738586708 738586733
    0x110c090721020f12010f1d07050306120a051f1e020702150d05010518070c060213050d08030108250e04111206040501050c0703080a0c050714060709050406050d 70
    0x107090300d50a0001200001c00440202400210005140c00075031405107041c808103502c2d00800705a441d0070700203412407007401c0340f6240c004080f030414985030f43c1c401c404900310840c88002907480e80300d0a01c1350030600c040880c08600301c2042219021000349400350b40c6040d1010001d0200c00400103090f00e100c000c0351039001d0701d5040d100404409050714128070342da0407900030301c943c682c103944c1d1a8010020391601d80460104544404000001c601d40404003130305550b00c40101400c4180c000032000c940e00351558a81e4098880189000304003511070921542c1c5400034011400c9a100d202d07031456544920341d07006603540754a254182002400e19159003036050010340b040b0366054110a000c61700e956022008000c44c0540c05c000e20a504d05820114203403080a05441100b140821145c3e000c603030b028224a0703002406003004100c0e00f5140404440320310441101624405081c481001c91110100301203001c1d1444d956401110b0391210200000c861a5100d81c66010344c0c103c402c940020903500300304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738589208 1250 738587958 738588017
    0xc011406090603030903120a020a08030a0c0e0f1c0c05041d01060609051323070c0302010c18051c050109080a08072c19060e01020105130807080f0c0d110c0907 70
    0x101c840031114bd944010030f42064541c0002d494940d5200540e60b6805190f04808000860340c0c4401c02e8031080114a46070301c10002e160b802c070300d042d4505080c001070744c0d800d40007010302800800100a611480000b012915409204203500f441000941648580010400c0e9000181880d01469000ba0150010070081c080007004040242c817501205d420841660710450140d1514950508207107002402c45200190f02c5041c00007040201c80c203001800c81030800c0d105d054440b1100303042e84030303a0700e025071031700c404020641e6003400707042000c04c040c1030007801c03503150161140180d54658441c2640e0b0700032107061030090a00c020b410318544018540c01601d00b0400606020054041c1c415030f48140c4003d034001101044d104c0510b602d003943d0920419a00903001d100480c0c04030700556840d03284d8803c840f0b000c1e001ea5004240d0340703005e8061f44126041e40102008844159540744000360852202600c07038229400303640b06c624524140b000c40d6a00c52031380c0e44d4030502d00700f200840ca0703501f140070180c94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738590458 1250 738589208 738589213
    0xb0a0f0302010e06041518030f030c0201080915071b02060406031413020d03080403031803022a0303070321060e0a050a0506012313090b040e03071e06020c011406090603030903120a02 80
    0x32489c1d10510300d100b41d01a03500c0d07200d20101800003420460015120074490b0f4440c440035240301c50a00c0d0215000303004c91030700c803501e00e590100000440381a40c40107580701303400007000980590960301000d150318005554020325600c0c50042403580d900010b0180d00040a194401300103441040d0185c0e100f88079007000164006160b21050700990036040480142c1d1002c940409e48980241004d1044106080454100c208440c0407903142c0c041d0410050501101c0c00100da410034900d07000031078018100300100b010680c1c1d00c0c42c0980708441550140901d80c60030011500c2c0140f01c0c040e1074442d500607107400007841012034900542c41005200200384d108188100c0d6135010140c0411002441c5c08040411f0101001b001c000c01c4031746e00000344000354800c0080c440000d0b01011030000e2022001d01d24291102103007400d00c042d100d100c04800d4994030f02070440b10500415003240c1e000780010354503815181c1e078072014140e0385d01c034440c0e000341c1c140c1c001087c883c90414400c001f1300480314244103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738591708 1250 738590458 738590507
    0x6041203020f0d1805010e0d09090c170c04060e01053a0c030203010905090a03120b03100608030706112106060c07060f11030304080d0f0b0a0f0302010e060415 70
    0x11000c0882e8201d507500d0114801c02c030f0500c4d09200090048900c2e0408110141c2141d038000d40001e007044843d071140c480c0c4070740c50b1030b40000e29900a00e0301c0c40d01c09009130820007039464204d8170803000780e005000d03201c0170401c0c60020002c0c070351080c4141e801004150300c54503c828039016965400c4108116080c03060205406062040b240500504004109035100581c0f2941000100e0080e01d034003c140079520303400900b010010950019110b035090203803800002d103507085000400d0821000e074005d90580c6060482c0090400340010040815a004072010000000c3d00d0703408610610a10507260812100c5440108040888038207040e040240180b005150000c810300203403e0040940c03020004c00c2401010b403840c0e0b500b0541041e80d0f00501800385117035241c10341d15414070340142c50040c0c0c69183d49022407507034100694014015654014110f1000e0f55658001c6207904080c0c0c08100c1c00217038a80700810007400c0100135a0282e6000781030614801c100c0c280102d8410031540c000c42480241e040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738592958 1250 738591708 738591727
    0x150503010213031709090f2d0412030c021b0a0518071d011d030f0604050601081209331323090103080307141201030c050306041203020f 60
    0x10041c1040785080c40c441c005a881c504210000c90511100500e840b0010801e6181a988003814a540414421412100c644518005a440340300c0c0c12003448123070070140183c00e2444d451551051155202e1026100c1100c10b01100f05c055501000e03007000036900c86c1c1030915010305a01a149840c000141407a004181d5a000152300705c0e078601d04d5003c2252048040c05410f540c041c8604260411b08441c4034410020fa40008282c680600c030380d4103800850801c4042207544c10300c000070411300c88034102c81d03d42c00d10b4242a41c03110401c1c420035210b0b01c01d1803001034000b02040203466191900500b2103104030000d034001400c00a80c00c600ca141110b8000c0c00700b02043c5144041d00300111885643c82036a81000c5001c800e0858001040b01010b200850600c015954440c0c0d080c10349500200c041c0c0c0301c0e114640140c500c8079281400c80c1401001041c040050380d402e09805040300d0040b000741250a65070010316403100d2054070050720210388184240a058040d4005000d4090b41140d0240b6013007111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738594208 1250 738592958 738592961
    0xc020d031d040f15051c020613031a060109060903020303031b040510030b0f01031a12011b032003071d01232a07050910030507030b04031e090915050301 67
    0x49940c000e6056407107491000441103c0e41130b0014060035541500100840f01145290040b2114000d200f040300061400b07104443d086100300940d44049401040000159502c092441c02c035612130000f002c0910000d1541e100b4802c01e01100d401501640c07a64544804100364023100640c800e100000030000000c81c0c0d03c9080d640800382c0d09030b55000411300c6140003007001103000f40d0400c504041c1010301444400246820600030024101d4004480d000e5401c2c0240c050240300b0200d90700c0c6075030015080c6440c0c0d05a00103551034445010020011181c140b0070410900065a5250000700314030b0f004a080114000c01d1030a83c0414140002a481c400d4521148802410415984074902094001e610481100a41c400310702c0501044910301c2185681d5a49110754851103104405980105402c0e0244801100c0519080010790f90019240c0c01c10500040c4103030340c21400112185284641b04209181d004c031085155640d9071745503442c0144600c090000b03c1d60107400d00424045c0051156000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738595458 1250 738594208 738594221
    0x70c0807060c060c2c0d080d02070c121e0804090617010c090806060f0111060705090112020a1707030f151403071217070b010305100c0c020d031d04 65
    0x1590351032030103079210700c2c00006907105412000113021084174080018882c00c0381c81c0c1d0343c01d03031650802c800307a02c0389100060742a1018100509400310001d060034020340a0b8006020641c01404c0a40c111540d404600d1000c07034000a01510301c1c9850f513051001c101c1401e2030801000d024102103403e09807030301d059170107c075210f60200c81080c8040b80e100700c480c00280201d0140101c41e04000c0280b614100340c0766181d04d4001c080a20500c41003482281c01d80c0100328106138071102e1022607016282c0207070045c006034414040240030450421a590b0b050680c3c0c02181c44103940f950b00c00310300440c0083d15802d801409802d03201810789036104a12550490b21a02901184542c3c0c0c4c00f8140f0700c0c2070540f0b1184e92070b00758854040d4200c41000c2c000082e04001c0519815442490a04013507003040004203d8090002c00410018603003000200b80400006c08207100c0301c1e4030104000e8440e030361074151010141008000e4119800305e0222010038001c80280a100c802c000c00070480f071400c000010200c481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738596708 1250 738595458 738595469
    0x9080d0203070210050306090f1803070b01060806091621050f060109090c050313020d080d050703060e0103020d0f020307080109030801090f0b030304031b0509041a06041b05070c0807 80
    0x102150300001d514104e04003804000c0c0300d00306103256051850100701005da0052040103140c1c510300118a2144511040b51440b80c4000250781c2c58441c42d107010440b0203070a22440001540c0140459901e16051032103a0198a0625000040c16234102003503454500d410b46460004482c1e54244d0818407660040d54810032122030510010f04e00381c0c0000d0401b4007a03070003144069240a45002d803540d0401c1c2143e4010500b80b802c17030200d94048c80000c403030300e005001c01000c107003000c130b04400000c1203904400c0c05000e807901d0a100d1691140741800501000b480080c2d4001005003040b00440d0041e11211110f6001509a500003078031502c8007800c0d00c258000842c00949a100104400318041c400d06410104040c0e00b40202c90261001039500d00840c00003030f0217030204a0720709100500b045440d0000782005821160540f82a040c03203040658400c0d8002045581c40c000210145450f01c19036003400c9200002c50101c280d503560032509500a42401c45a4002000d00401d10441c100f004d1802446e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738597958 1250 738596708 738596713
    0x250512090604140613030c05030d060b19030b01050901030c1205010611190f0305030c0d110309010c03060305120c0c060c010b10020a02030c0111010b21010e0303100909020109080d02 80
    0x82510b0311000c0e070502032646460350780042042c03040c49030701c0c9014a240203403d0303d0800f06200c150f04215027075114204200d41d2052405d0000607160821030050f00c0f200d540c034042010520102ca0341942580d11010301140005d00400231540ca80d8040e0f0320002c00b010552070314403550f031007003d022401c6403406e801001c0441c013903040801c0c500f4030401402c1f010038112150301049003460b50360711050400309107000341400804400107214000502c241c036010301c0c00800a1100840110030462142d0040d58101010350900798080c074440d00038060401202c0c0d00000400354140a030756410000e410894101713200740680103002026075650710140564000300c600010b240c042c07000c02c20103414504d8682605540102500101594020401c10070141c42800c01d0b01b03c809130640d0850040046420641d4846603c421540c000704500c144608100301c460000c01110280300313103465590000b201c0e080000559840d091015a10316000300c00d07101d1040c10407414a030b4a0341407003030404007080400001617 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738599208 1250 738597958 738597961
    0x30510060b0430050a06050106080c1e03101d07031401060c0b04031b050706111b0d020303090a090209090604060b07030807270e0109052505120906 65
    0x281268420300008101d540d50580c03415260001e00e80f4560041c2c034080c00c0c4182c40c080c502c2040065205000701c0542d10500740d60781c107800c1d4600003000b010203001d507400144440c40000c2c144030308401120754440203825461800000e15003031141d550310081031503246409814001640746c00c030044103140b1400c1216507482e1407804210080440d08064440d2640d018800010402260481c0e01610700741c3d0014216003550362a81801c3e1000300c0c00c0140082c03081040d84515080c008041003c6069410300e54030902d00b045555442c1c1e1752200051800d039403d1a80702e082003410f142146c40300c0e4543d44045c0560381880b90060018521403401d90000003490380000c2e41d8810351901c0880741c0d034070000c200c0d01004014240b4000d40810f005940005003031240358008120103a020f481542e030000000c605c1d0714049210044010500702c2c1078810304134030603400c40c0040303a17070a007901404e44541729401210405c90a145894400081c4459240c41881741c108111078980c080000700c0740c41503c0500c02840075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738600458 1250 738599208 738599233
    0xd05030309010b01050a050f070c030c080c040e0d020c060706060b2205101407050c090c0913050c03070f09090c091403010b06040911091201060f0806060d08180a0305 73
    0x35034060f0b840703860405c1010060604455000b100751440480410f800035140c200605d05484041c1c000c0c1c00c0034002203107614002031100e00014100b008076805035003d00510f041801c0b1a0707a6200311840b04030258001a80c1248182028000b070051140a078901040301e0b03550313440f00c00e1254454185004000f840100a40d4a6140c4191500042030180c3c0c1c00c00c00b0100780c282c001c042903540301c001496110b0018001c0c0070300c0b5041084080c0004001c01c044041d081440d0300150561003803217014000c400c00e01c40031146450b2849500d200e1288500311a1941d540c004040758041090948034050040c00d1401140742d9030107106034a6003850545900c0700f41410088201c0003040000c4a41d0b100341e0411a45c41000d4551106803000c0f11000180400c0103440b1354034030034071405071f00d00190b0440200c3e114800009415004001194001c040381c40c003203901c1c0c42c43c450319503108482841c1c100c800c240d81b11000580d948010603102c110a500e0341302e20041c0000107103103501035510030303200c61b404100d01c4c842 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738601708 1250 738600458 738600461
    0x213020d06061b080a0305190c0305150a080a0f0f0b15040e0313030312020d141806040818010c0b0f0103120509011d1c050106260303040b060f0d0503030901 69
    0x58080100b40303c046400040c0e4400c00180f00f08414a010180c89401203181296041c840210070700c20410184442405403800038001e02080355025041a00401a016103080c0b070719081c1c0a035003401005d000404e8107602d44031101a000030741142e10121004d0440d0214017400c54080c01303504a00d4090514429610810003503a12004581142d50400c0201a05864507481d031181100e1f41404c060301ea0341e0981e140d4400078001c005401c044e06041c000f000c0401460303440e45510401220007001011400c041045688070800c031802401c2840c2001284c0002003c0c16003180000814589480122160b81c1c03032801162055400740d0700d240d105070060040001101103040018054503103070381080c0581d40000c0c103009002c3c141d030f0399040346031132048016200c0140c4071881745028042e100280c155450040d0003890188501c0c0e05408000900c101c01401d80003120384868030340030086045031210b0300c505190fa800901030b1a4407010000344940c5a40721070010b020301c0360003030015640341c1c54412034450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738602958 1250 738601708 738601727
    0x30c0f1515051809070f12050d0503130305161415160f050f0d021b0d0507211224080d090e09030c03121e0615070213020d0606 56
    0x14503602081440281c80d0700c3d040c1c05140d40e511195003201d4aa041c0854208800d580000d000c96018240c0412000d9100345c11520070392142088921281c04504116101d000586104003543c0c0d04010010100780f1900281115540e04150f00300360f04070903a60194a56820001c0010a40210300340c22170346110804803960080c01a00300b81380507295490000c11440c1c0d110122818441c0c049141c00d900c071100390540d0040b80c007004003199542540050095400c000b440030740030300c0c030a07402ca80105520610030b960420b94810f031101c4881c0140700ba410b01180c0e40d4031b42e20080240d10421944a598280030342d400d17108000216a0012121700c1038020700d0015504040c0d10741e80081c0c020380300c10380e003c5901405c450040c0094940303502c403003070041e0441c0f183d640210f05070701c80498541c0360b40400c00e140c01d00585808054030051500145031405c58401203800540c003d04607410201051200b1000707207803291004102079404050442c1d802c0880c3c20140720218000e546100c1030244940000400c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738604208 1250 738602958 738602981
    0x504121a0a09050705120c040e030c0f0102040509010b0f1309021b060c030f10031a1005091501030b01050d0203040609060e15280e01050708100b070f030c0f15 70
    0x82c0100c0a460715400d80d074042c0d030311405001341d120741c1019451910178401c05482020003401071141c540c041c10180d60320340000041c103106004000d030307071103002e001403080f0340c04c0794000b401e418011783c41c0c0400c092640d04030906c1c801000c00200305089066000340c10400c00383c86081801030300d400d03450701040314403048000031902c0340c1e201400f07001c0d0525a0509882e030041d00810240c44e1507603081540d04d0201c03039980c0011300b40c00660514000d43d141012032284100350001c6500f002c01e94510400c0080001a2860110b42c28240c800707034203551094010104006044c101240742051810250040343c1c41280d003035610720350380c400001c10411603028036041e0b003480c3c100501041051441035103109034003030452140d110111002c0420381c42228024020b28803040c0080000f2592050140e0107401d04542d207000182c1c17000e000511900528201d10159000c1071800c60900005070b03074990045100c100140c0901541d4001c00c1d001407141602c10300018400d0b04140d041c00e107410000003d803220540704 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738605458 1250 738604208 738604211
    0x10608010f140612010204120b06030c013b030f0f010e060601140309100903020d0305060a06050708090604080a081305090618040201031b1115041208070504121a0a 72
    0x142c0400c0100c00340c19504080101c0d2800c1d10b04085141c8140240f00d513a00a11405149040380740038001206003080c0305580940548144c51800c9004540c1c885014111100c0780d00303880b804030b000120f6900d44040c8640141c5030348403964040f00000b89021900a40b004540e402004034842c0104c3c203000e10030001c61510300030611030401074000313414000e001d00001024107000c1300140d000c0800f00040d10288044900400c0704480606000307444001240c80f1201280c10403007c1a0142041d000e01e0048403525035404e070400e81d107030f40d500300554480e41c611035120307000b4007000c51800b10134040106070074801c14549070764000c455045041581c0a03030003e40301c1c0480c80304200c1e5a880b001c1d0043d000c8103004142d000a03070740ba0301c0180e0040100568031040c205121070301c0c0704455000301c0302c0c25010420601b180c0050b4505100040b070300c4811500184072502e425440661580a00c84c1c43e40c01c0025410014200358803443c0d04144114010cc0c103030341c100d1800172414490101c0401308c50300403042240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738606708 1250 738605458 738605471
    0xc09040f051f1a090d03020c150c0f0f0316021801060314010f06050711040914010b01030b04050402060901030e0304080d1715030715110616080603061b0f1b010608010f 74
    0x10f404585003d4406804d010380f14040303070141010701c01c0c82261660003004040000f070244500c08136002c0e4010100c2001d45110300400c25403800c100140791060842c0400043d480c140307006040b02050460001c0880e009031030515050408154422030702e000e40709568002510601e04020146110340c103a1100000850901003441080d0f0f002c4222034806400110703810007514944042030052040e0f40f0050030103050b40c8000190100190000911058241d0381807080d9200d0b4000c0104403402640c0003948500b041080c03001d5540207402075040c42000c0c5003501e0038141d0782d402c110308010710240408005902d420345602007000c054406078201c40d1005000380240b420b0300c080303540c1b603655009006e01c1c0d900c00000c0c84034043c411000e40c1d94290007802500e1841c2020f041729012044940c5020000c150444006005130400007a442d01c541800d0118181041701c151018603554404000c9001e1040c1c100001c42100c0c060341c50441c1401e0103080001001490031000c1e50031202c004000b0000c0e00d0070040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738607958 1250 738606708 738606749
    0x6032910030b04020105030c1614160e012c07030b0a0f05032e0f0e0d030b06040b03071b1202160b0d1104050d230706080c09040f051f 59
    0x10b4025511690a0a0050341d82d10f410114924500401c290403001510681c290b00402805403404204090101d0031604000400d540310030748010b02d8000c81c1da1010302c0400400080d01c9070b030881c14000e00c495482c1001c25440d030503a0940c481003100d00c20042512007030001d9072810540541c0340200038842995480c0c604bc4400251501c04a05c01106200030301e40500c0244c200684071101d4004c01c02004002110480803018080c000d5101c503003403079006940c2d68421b46030090099800c010001020380345010b003002d500c1b8449400240c404020080344484210700c406000f100c1c1a0198042c07420385100000d56030f03009140041d02c003078010b803844800c04100458608a1b05980c11101080fa0100e039a032807101c80d00406004a90240f513114440f148044240306007a08a400041c82c00d94540e402c0c07030001e42d00e403652100144502d100041401d0005014141034a002d809030480080004c9254064460f001007500d0060b10240ea218240140111a40320440e90210090074000400c051004820f03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738609208 1250 738607958 738607973
    0xc040f08031905030a111c1b0c08030a0204031a0103050105090a05030301090902010c02090a1d12030a09020f04090501050702011a0d02212d0f120c010603291003 71
    0x8002c00601c140400403502d1210141c0000420300c260103080354499840091290440e00b444c810300204030315000c44840c11035018101405a0880d0b61076140f0484c0303a540d40c41c41e0503880200200c0c0030980c240b1000c0b001600350b40010a08074101c2c85070204550440c00c006007180d0002d040e401c0766602c203010800c002080070050340d0444107040c40000301e8428034001a1415a00060000e601002c45000c001c2d001480d580701520458410b1800c602c1048508017442d61030a0a00da22541400280006040104c9503002190079500c09483d00c440525200c020030155001d145c000c0fa1180d448000700030280d9424440c4003485608010b0450130069144045920b86c1540706001e0701910320030030020300124001c401c50060030140070484000c80f03001c1068200e10b820908810000030300040342000003440004d141e00c146a80708028140a070052075101c5001d0380540c202000d65501d41400001040b040c1c0419610200d400030305400452100003000d40412008101000c6940300a0090020a014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738610458 1250 738609208 738609247
    0x2090d0204021b1006030303110412170f0a021b04020403080403060f02161239060e0d020a11100c030c02012c0301050708010b1e09090c040f0803 64
    0x40d01c1c01070741d034003c0c1c6442d40c0c030314003620400d81d482d4450403c010101d81c07a954050400c42e8000d54080001c41040100c1003903622440c80385500d6400b10100d840d001c52400fa4250303800c450450f01d510720b0108000d0004480d030b00b196406030096005800040c540030305030a81d604805200321011031600f8103503550fa4615014a00016100c80d54440c0d4500c80802d265046a030340520303038280406060514a0082018030346142c0000c00240030414015654100081c80c060b03540c80301003100c1c20414a01c00348001c001260354140c6034144c4851410074040c3e410300840a158206a010f13000703001035410f180c1400610024428000c041e05107c0f00807541e480040b100010782e00d8544180054030398001280c0d40310500030101c10b180080e083c0e100c1000d00e203200b201048003040d0300074481d030754034400103a5285000740300c0e030121904100310f40100b22003100358010303140410680131814640800c0218000740400c5404c10f03c001c1c0009014042060702800040003000258021440c0900c07603105008540c45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738611708 1250 738610458 738610463
    0x70f060840050309060f041406090a0311150301181a09040321050a0905010516021f0908040f0f0801020f0a110109020405070f030e060112020d0302030c0a0602071101020102090d 78
    0x100c0007010008103008964800c01c0041c1030b60346400d42515558900c2d40f09104000030145525245801814038606450310340702c00500c0070380f200d803454641c158412031460515900200030303038807031280b00c1040f030295028200b5184402403062602440000f01c903030000c001d0080c80b281076040811a90f410a50903401a458503018081859400240d104004c298011003c01402c000070070103414061b60140007158000d0b0300034400c86d01ca00d81058094a1012503980050304040685010404190f4035500d0381c0e0450800010300050b591984036060304542c02086026510020404c84500c00264050161400e207008514005003111031060034440c481046003442031000d00145403030402e621001c109a0013500a20080c905020001c0c000c0e8081b080315030100b450101072440851000a034541a04c0440c1400c0142820030740800902601d108400c604510040002500e82d8401307000100321075200c2c00380541c0350320342850103a81004480366000c0c11a8410710102000d507807815507030300c12941c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738612958 1250 738611708 738611821
    0x10e07080a061e090305070c051e091504090f052a0f01030e011b120c05040e040203030c1605010807170402041e020429070b18070f0608 60
    0x12000d6400901503d2102442800603180410620070304d40c22500a003500d5114100070b0761031948a104110196a410407024080d8005405051503820070100440d0004450700c1c10900a1503184005010340340e9072001294104c10400142040290802c46e00c102d01281000316458004105160300d51040030b845003a224039264003400240342d019030300800780010114002e00c103038000f620102040300c94924464000441c02e030b891029204080c400e00103101c500b41d0311140b4141c90900000300060b03002e0400e03030f4140001c10507211a10002c105501c01070306e910085150903880e2800145c01400000c00440903c081c1401c4815080c003602a295482079049800280720700146480c1c01d0b880060300c1c00541d8440c40003d000c981a00482c454007029440700305450b500110740a041030f583d003d06d5070020660302c2c007500400e50040700c4603055601d01c4007030411034141039616284207000c0c0da41da62002022680c10000c0c40740c9c00710249a00112000100f1512230140c0c1c02c99500542001c48414947c0e450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738614208 1250 738612958 738612971
    0x1e09150d02060c010507080106020313030f08130e010305010f02160308040317090c0307120506060d061803270b03130c0b1b06090d05040902280305010503010e07080a06 74
    0xa80d00d03012100c0000303402400e00ca803600b0f548020207000740310642d07124000c07400b94000028041e200200f00e451165a24a02d101420b06d595101c05618480000071203402e04140803a003101d80c20040418000d01c1170465031655949236040031405c580700d0361414401f9600400082903504030710b00810a84651514041016540e070f41003c580008007a50701d00c034019581c0c1c0c2880b11085001454540400048065404250342c600041510a02c4402c0080c415009140040d03101d240c00090803020303d00403a0049018188035541111003031a101003200844e04154600d811414080c030950b04030008901c2c16482c4505104403e4801e00000b00110142d151130f108410801004107600d01c0201205025252100501c00c00d096048004410074291031080c00d0020383c90700400603011011150f00e450b00d600c0d0034201802c0c00080d60003152229860382e080d680046c1920700404141009501540c1d000803d94188020542916036142140c41c1c0359000001c01d004142001c82c018a003d60700000000d1803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738615458 1250 738614208 738614251
    0x31716150f0c030b010225050d08070501050901020418200307020304080a0506011e0b0405190509040605041709131a100201020c0c060a270b07111e09 66
    0x40d044001c110030041c0d00300740c0200051a0180c20620340c244c0245c00b0344031880004281c0b008191108a000407055018400400580c24049040d042d868003401d2000c0c60314503e5240d1609580e0150783c20036490398000313010040c9000f00000e0b0b500d05107040b0020b00c0142e00725035003024041014184031104210020101701c88a00810450380105008800c1e41c900c850750303041140e12030109100300345c00d8044044500503800d01110081d803d03100d15014950506052109105a80e42c03004800e400700000000041080d55442580742d218030720850010506151610701030000d40303074002e0620b080c4282400703c96130710740c0c0709800c45002d40000381d80018640100140c842c02c26005000c91078000c0c14010302d10340c041e64190010700480ea0030400315a40c25101505100803407050b2406d54002500d450340d03080009800758400d00c200e801e456151501942c695500056642c4001c10489020000000c080c82905107201101c0200d21b101c202c40c2036240d448808030300d030703100010552850000340d0200f2100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738616708 1250 738615458 738615461
    0x20606100915031e0b0117040606090e0f12090112090203160e1f061e030b030f151003030e060304030c0614041a0403020d030e070b0706020403171615 66
    0x900d122402d030301d80039603410341c06001007415142409038160b01c5050b5440c2c518807400b41240c00707403060f92070041c2e8079400c031a103e280b0040038104444468a910b00043c24001c01d014000d480200703d00030789552049126010b18020107045140a44441400464040d0317030441c12707228240a900710301083c01d00c407520000341003090781d032040e11080c1c50220010402480d0702082d01e2089803041c01d58002403a0108014079207001038480c480000d06050030b0203001841401c0d00c50148100360401013012042680082c0c00e20a1401c4100b09aa2000307030112a02d40110308541d0304203000710f038031218035419074030014000c00000040f40c1c042c5130000302003000c040c410080904084d8201d9020000b04c12a850800004a81030354140d401ca040d41d24900710003c80503018502072a4150002d286960306810107601074084800c1040c880d0080088c00100d4000ca071006203c2a4401c00006a0f102c0c00c52030485501c050b101840828072806020004100d03c80b4801c802c401c030f412006814a0304901c0441a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738617958 1250 738616708 738616727
    0xa15030c064a060708041805040213020d1428050105090a09211206090e0a020907110a0b090d110a03080c0d09140f0c0108041b0b04062a0302060610 65
    0x83c0c200b080081d1850a002081d409002074a00d0801900038a190b03500114080c3c800030398000e54065160340401021407100c0d8000d11107203402a00110701d458880d000b000c01c02c10111030210203020f100b18003020720914100c20340362030801e000040000754109008503c1142c001000f9a014a594000a005000c0d480c1030038040041c01c10b20480d009002c1e942e005014040d81d24041e40b509041c200b01048011890182810b4143d0a8000701900700958003000b0960502800400911044820001c0d0083c02800a4181d03180556a201214202101210f14110410040703030104016441c4d12491381c04d000c9420f014261701031030548201d88500030024801e03c1390340d40c81c0c0400340c0307042444001c00c011f043c03050030040190420307168400307100350080351601c1160891a0004102c0000070303000805d07020b1400d00200810400d699a0b9883d51459449580a50490001b050741444203c0807901c000c441c411040d40034000b4448801c1d84c90750b01a54a19002d00302c9440b0308111130040034818840c0c005034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738619208 1250 738617958 738618107
    0x705060f040c1509050102010f0603030819020f07050c0a1a0a0302030405010605040c1d04110d05040816030809190b01030b06040e030a050d060509010e0f0a15030c06 73
    0x6070000a0544000d00704c584180724550165080003030a240d0f041c458030501d8200c9405403a038441641d40c2c03120602c421800f044c021004c140e0300703004811015059030050001148140000c01c441d800c18030404c041014a50302c11726000801841c5044100c921000351a06003407503007030158413611240f0342a409481d42e504040e4100f1700d4000381903090755001455a40708940045580d100c01100c400b88800d441c0d4410400140c01c0080000e6031031029541d100c0bd1b4458080e18459003000001d40010369030b40754009055000030340b44d0080c06070084042c0449c80f42550307030f0b030590b104000c4240e440c1014840148005081002d4110002e000c070340710ba403c905a0464540180da541d640000005071180d00028411181d4a16140c03010a50382410b003029070681c2c044440d41000d9a903840290f400204c8020088208191640387c0d600100d048482c0b50005584141740c0041000c0c03d00000610302218070840c8a0349402801d04401c1d1403912458440100d6001840c014104c2000e6400c1c601811040050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738620458 1250 738619208 738619229
    0x510060810031a01051e101407051501170c0f09220804150804210c0605010e0f06032d03041a1201080f0706052808010e0603030705060f040c 62
    0x5a04420f00b000201c1d060320022944030058541e100ca15015070340c3e1100c0300a8114a00d0014082010300522040a09101d0000b038036140450030b03070758a42030070102c1c1c414282d091034400c01804214590402c600007400e80100905c0c100902100090707401c0c604000f00e0b4090100d00e404a1b91031078140f6a0304071903c48100200c1244074940c0303810b00c1d203940a841410042d0f64900c0060340d820307108041060284c0e0300300601181480d00005004881700d81480032806100045006800050362805490300070a900e0710141810302e84a14800142680104590301c00c0c1c0150244041c0c00c0d0030b0702c43c0c40f410707003c451800480740021000c0031441e51145030440d400c126040c40201d1000503e140c010241c1c0494400071001c1e0341da80301442651a0001c6c00c40d080a0b07000741d001840306920603009001d904015030070350503c104c50700100d40c000410035600704001a100c100180018a0003c800703d8202000394001e500d05a0b003034940d1500c41a010707068822a4130494046401e00c101100c458000d007042621 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738621708 1250 738620458 738620483
    0x504060914060603010e07060e0402181207030512030f16050c1b1c120e0316080105090618030414062a060112230a0b01080706030f051006081003 64
    0x400e140e445034211a00f0748290b081c29081035006030302003001c008803802912013100420095080101075081020220004070150302c07903075100d40d110112003d00d042540e000d016001c1c2503082c110f0034840d2904081700c0072202001842020211403416541c0644803034810452a00c140404403460310031a88403040910131310302100c4011a10343c80c1d48640703c0044a403070b14003a0042c1141000c0842c4608094000c1c0d0424200c5004d003801412010000c040080a503100700c3c04120b818408403003c0d82003005141c3d9100c04101c00040108800341d001080c0310410101104030302603442c1d981c0b04a005082e00b1840041c1d80c0e050030b4462802f80c0340240080c400f6140c450000c9000180c0d1208013010f104614400c21000043d0103460313000445407150001c0d800000c0340f6840e00300c11003d50a941174030b1200d11540c4510404509040e03520380c007030004500034042e4a0718250000b810b40c1c80741041011594a40b4041c04a490704141114044416600f003807022642c40c40c108508030707a026400540516035025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738622958 1250 738621708 738621743
    0x13030f0903151e060602061906030210030e0f0c0f0105090a0f0b0a02071508070827071401110d1b0c030b070807180605030a0623040e160905040609 65
    0x3c20074400c1c0120000890420b030314480440c1c0c1503903500d100701d80150f08901e02007070342c101011400f41c0034040784420128000d59664003140b464608115083e0019070340722018540c95800307001c00080070354410002c0040000800000341101450b00d02c0b00d0620400080a03200d507100d41e01484018600c03400d04822940d543d1103030900b10780c03040000800502600e8000f00300f100701a070440803088551b5603100e41c03079a208042514400409003092003030b5401e101d100e200d0380c10a60f07130405411200e240600f96031071805504044244011460714140071044600160710b01e00041c00d00e12401d030615100c005a40040544580c54030a048050f00802000c0070220500c119451850302822940d921000241d4915408481e0000904541e44954011141c20031201d4815009507401401308040000d030582d42e004006408402c8240c02c894140c0741d09250780042c0b81c1803044110305881000074100102a01011204541c0c4a000340c090103962000420140029540001c00b416409210701e03800d0607a07003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738624208 1250 738622958 738622961
    0x60f09070f0b04050f030607090b03071407030f080105120a11010e0d0b040309050a080d110c03030c15061014210a151e090f1b0807030606030513030f090315 69
    0x2801914007624070300c1140060b608002509500c100c04641d9070342708031800c00404803001d500c00340c045004c1140711584c0400d20b0741c2c100020000584240c40760095090340d950013508e5000c05a1045202d03001c052048502401c0116054170310a80c41502801070949907401654441400b4044903045040d810343c6a00b0070100800d071600036800f03510b441d8481c075075a204004210082d0302031009541c10900340c00c03402e14090002007002c46074103001c0c2d07107841c124100881e1541e08442e101082c540d04c1600c9032110100e022005a0f0030080640d92951140c00032100602190170003c0c10420b4040002a40020101d044007400b070f9507a803509400e607440c01d008134614003074040415070405c0b00445000c0021004000c5194003800415400d05566040c508a092402000010044a029070300c440340151942800040b03191041100e03181c0081e641014223000b001c448003504410141031825050040a2148030f44403104182e0501c0d084000060381070381110141c0066100405c0d24070001d05015414080d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738625458 1250 738624208 738624217
    0x213140916050907090b1815040f08010c052b0c09080c010306060e0607060914030a080f13020609012304180b0d060b1c030806040b04090203060f09070f0b 68
    0x40c550308206a50b220002c104076903809594040101d10075080400517004810b0140500824101003414140c181501003402c0001111101407084030000d0148a10422607200e44080d00c1c00800030402c0107800c45000e0240e10401c100c0c43c01842d03401400101e80b00181025501d81806508140304065103414050b06c0c640c1c1900801d0a140503480424031954400c0c4211f0041302e02c81e40e03034140d0300300c03100c000c0c00443d610408042c1c4000b5102c070081030204014848c40300303003001c0c04d00055541e01040507006002801c003074103605081b4140002d0080c45020014043d0324690100e1307025984a41d44801a5101c000001301e4900c40081b0721044280000b05802600c03c94845070788540d8091800c0e0240303400c55040c40c200b250301c00c01825143d004103e0951010114040141400144004c85d802c90f00300140f04c090201c0000d040031041100c0c60400703010341488803506980500c040e40b45036000a403501c0c0020600c440d4901180000750154508004810003003c9c002560018962a0b0f91089201d511 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738626708 1250 738625458 738625483
    0x30307290601022406030f161a030912210702070503060703020a021c17090304050a050a0b030a050405010b0a03030206040218010e0106030c120c032c030702131409 72
    0x304030002800e650011900c1600524050921500d035508112001001c01000d4410350301441001d40c16111144204504000b001640d0601d8034424a8405103041d0f4180000c02c15a00360030608c24481c01410005982c0c10034202c440c0d010352900008054000e1221030b065240194511a1080c408000d03004039000d4241c520590680c1d40e0741e50f0300c40050303060b84209480e010050748016190044002d17400400b070401c07141d600e480c90202071203114908648400b50f62119054000250070407451030202203810050500fa0b4807035004a142c45090503050100030003d40c20240c448000508004081d480410004802840f1011064a905000b9038450007190102c0c060b2041c603c0115050030b6140b00b0324100d440802c02585281e0134200200c02070f140c082c1241083c000c07401ea182401c260036008800ca10b034041ea40004081e4514203034580207102040d50341d0000d25030382c07859001c40c9078007208a8140e2034056511100004001c0d2404004101b0000c04184d290029400c2c020034080129070300d40d5400c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738627958 1250 738626708 738626783
    0x2071202010c080610030504050f1204080106050a0f030609030c02030f0109050c04051b0f0c030a03020715090203101a030d0503160801050901031712010312122702030307 75
    0x74042da82680c585030155511588400010410460306110360002a4058410801d642c195140171075000e15000325144c48006011011501b404030000074891f080080000b00e81d01910149004400441d1181134040a010300c3d40b0b03504000c0505004603000d0403c280d0241c12101d0081106807110300030001c1843c122024066900c01c0304491401c1e01405000359145c41d612500200803d01e510700380d900034000660a5542409801c059004c04d001030a1400720b107807400b69a55482c0e20300f154959090a100c1d90205141610301d0015850000d00c4032030300c8000e0080000c0c0e010a01014030340c2088841340d2550300d4070510031a418155481000b550290407000c034400c0c01e14115030401d0728000340034003946400c0000040108046000c03280c2910448078002400c030300d4801f07929284c1010303000c02d800542c2c3c1e03c0015015180c5099110b10128400310380d01d8000c00600e81042d52014140c441e550b40000040d041801c20001c6d55000d00c1190328251f44401007645100c810410792061064603004501101d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738629208 1250 738627958 738627971
    0x50c0a0c1a03090312061305011d060607240b040603050a1a0103080a03230f0412052b1410140a0302010509010f02011d0303090c0328060f0207120201 66
    0x200541c0341981c0c010050100610b00b000d03408030050140b1403005241541c403004010404030502c149100b0341d4080c0102450b400256038494210944c1e1f400f010300820701950040000c480803c0701900c0c0a0394000d1542c070b10001414400403107034090405000041e074480d19020300041007010008420344464800c0c2c44800701108401e1120345099801d00c0007a0558004010880120b8460b521082d54840c0300c41d0b0500070000c900e42c0300b06030b00b2000c5551a0646a44009100a228145c100500c19401303501d00b940c5840400c4988045102c20f1500042110302d045124100c05c2d01103411110340b1445c41c0b4044041407418158284d103047c090711440c980c1c04410a511103141c100740d0081c1c02500e806840e41460800c402d00115200d50514100a00f155a14001d40d001c104d1018690100c1540f468021516810810364290030640d02000082c842d51041451207200c480e6001c0c075502c100104c100441088184d41402c2e00a0b10f0030000400d1542e10004000b020044000204828040b65078004c2118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738630458 1250 738629208 738629249
    0x1261503010915050c0403080a210c090e090a060531030c150b060a1205090a2109080303240d0213110918090d05120c0a050c0a0c 57
    0x80342c54002c0064907000005141c96400304080e007006800440c210b42e490310f01503913a01d0360300a42c0c02c085460742c0040c1c503a00e000000840c0c001940d41d107a10b04014200aa001e81c00c0b005024000c2a100b0402c0c40380003000001e4111300240f1110b01d42c160803080c18402072030300404500300e10403024059a203030034013400141b0755540c9a24038203c020742e1585459016006a8940310180385aa88050940a458000c0d038190fa0b01c03038001420b140c0700c1940f035500c410480c0900d81410348900801c80d02d0030b607110240c03c1c000324852101c01e10018010302c480700c41c800e42160044030615002d03040481c862000105002c0c4501d500945120340b0003198041c540d10b40207400410010904d03004001c3d6025481e006100c0722102d0a82c004406d82c1c5041241a140c03091030808030314850740606031300d1030010510b020448a4071082c400b80070300203242e1502e9072804207848078000282c803000d40401000359000c201400414041c0084840501100e4110340c182840c40c506440728400b075020700d040e045940c0790f0300c142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738631708 1250 738630458 738630461
    0x12030807020f0d031802100f0306050f0f010c082203031403190f06080601090905011b08040f0309080a0f0501240506090a17060a06060e010e0f0126150301 68
    0x2072140d401014000905403400124050100841702c3c01c00315213075245140c0140c0c0c581740e4207000da441c1e0751240d9040141031780028088030003d511460040b548021203018903603c110440070026004d08080c1200c0d4104d00b001c00c2140220380e1004600440c401c00d00446001000c0070b41d0803284a503481d01c2072404841c91842003400300780c40900034005040c2d18801111070507040244000d218001c0001c240e90358002883c5415020f0784012600c6540701c0080e01446003c2c0100c141d109800c602c00da007410a20000103060b68030041c40640720a600100600030140f01d03407140d000424004c1c0c2210012142410007440c03c8048a500b21060f41c40c1a00240158071034191180c40303c19103242001d9072502d0301080c0415a40310070211a4400c802e02c2000c50503100e159028410440c0300720050542c2c0c5801003071102100d005400001c148109010b40b90920303a40600c0150b028882501c848114514040060321600c0d0f050742c0c04010700358102e03107283c0c0c800741c1c40e1416482941442500118050348005250 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738632958 1250 738631708 738631723
    0x913120305013003120e010f050117070806010e040213020d0b0a08060903040902030a0f05071d0a030206031602120c0a050106120b0c0a0e19060f0816030e0c04061203080702 76
    0x44006000f020102281c001c021140c200c20700c035400805d2600c000f103515030840d2030446440c031406c0d99070001888440b4503814008017108600e4018201e050030507100c50396400c01485080610030301540058110344980400b0703500d00304c45031819911001000c0c1c2e00b60180c0624410540a440b59540c0040c2001c40000c00e01d004070940000740d0300e03290801601501a6200402c560000e13600e42c10000540c20b10746c814584581500d98803003415507601000a460003004900c20b5100300443c4a0610140c2c0e1a001144e4021038118101c120760451680240d0810808500d040502c4e40049010300ca0110301107070b6407050fa4400e030001c00c169a11036007082108545144064a030065080000e100d44015000404106040b420588003080e85003001600c3e020010a0f0100c0c0c0a03101e240400085410008a40b600e0401e410000c4142c9050b9030449581840c091280c01095118411107801c11014048120051300203001440115250b13881c01c484902030502c22800111020b0008030060b1002c58144d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738634208 1250 738632958 738633029
    0x302120f150d0f050a0c05150306010806010309050f0703150b01030e030306040b0d0b190c080403021002030a0b06070f0201020d140927040c05030601090b060405091312030501 77
    0x10a075400300605006200114203400c0b01c0041c80e041d4100301060007080804500c80c0701d5016142514188403d00c0000c0d914981d8030150304001303105100740340c0c1c0c210000b0b81d0700c00020303c0c0020740811b9505100f8640001400d5a06c5035005034103020040c0010a4074080e046407480b402400115190001101115001144210f6a40051002c5030386032910303402c0140280002080e020750380349982c43e14619284150380c0e0116450b10040403907040861800b4400f4500007a092066452500d074074003039110400d00c00c2e074004050f4000001a891020355128450056000c9c0c06262039005900d401d200d074503c041e1069000d8031070069240e003960f00c141110708082c400c5070740c0f407420103851605000ba5205070210501481c810080d81886030414a039003e80306501418041c49500e00d01818181403840607048030a401c1c1c20221907801d5915410100d07421aa030588005207955680c04403880012030104004000342d44040400c140b0344d90603086241a581402c07019503902d03491101400e40c181c0c800d0142c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738635458 1250 738634208 738634231
    0x18050a060e01060f0b03070206060409031e110d020102040f0b07150b03010207021f090f06050f03060406051f080f1509040203150112050c150f0c031303030302120f 72
    0x4840014005070461a007504100303001058098a5031581c070021075041d001904003d8002c010000c0095040001e03e030002826102004003103401e460040c030f2509800340c4103c61007078910a00c0010f0b40b01d0f000410307400041c00c00b40c81c0c4032943c04a00901035070143c400d0b543c03030602d8510046400380140003110b064907805141c01d9000325054400394041c220081c0b400e68155400e200d4040561910864500103143c038084440ca90342d0390b440041d0140501e90400365800442c52414404240c000007150a8054400d00c070076125514070700014040c0816801c11904540b041b045100380b44030904001c2c05020340703070300c64460580e1642405445c03d20116910000c00c5090032185015080640d031450300310780054140c44a031502c0030302e104040300d000e0303000005c4250503215002c02d01c5400d2011001200f41110705048890740015002d4548c041d024003445618400140380f10401000c10485042d01c004072141c0422036601e003000340003504040f0011070082410800140d1041c40150910f10a4a40120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738636708 1250 738635458 738635473
    0x2006010f05010c0f08040e0604380312131a0a02122208160803030402030304050f011206140f06120f07090308040e0702010c051e09010c06050907091805 67
    0x464003041c2191040d80e0f03070508120000302117070582c1c0c0200302504e100d1107901e103e070410b1818081114001c1d102c18604032189142e801114414009018075101d580c140524000c03180400241880030388450f9007103410000808502d2140c1592203001140d40200c0900d024101c10039035110244100c80b0031f0300058210100110841c10f850001d400d82200c500000c04040a000000e5040c5a481360005040f5510441d41050b61034154400303540a070064501840c11030416502095480c0a03078010240304900c508226680c59100345030031030003903960400500046582c1e82141300407183c041e07011405401000385508080c1414021210210054442c43d500d41d620620f02e10780d0700ba80a80000c5c100114448000007041860340980301030f000d4035004a12505084a000e82100d07a1040403106008082c05002e4a450101c0c589200d1500c000f81803079502c500003c0100c540043c040e170000d28851400c01030200100c1c00203000801d80e03840d007c0070048107203c080c15080d005060700b40240158007801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738637958 1250 738636708 738636719
    0x512030d36030c1203020c0d120c1b0809030f030d020409061203050d11191d0d0503032e06030902090603030319020d020d0c02100f02090d06051003122006010f 70
    0x540b420311541300b03450018102109281c0560800024011703110008182d045900803078443c0e4403e07505403010f18109414100401c414440c0c001c1c0c480c0303c01508ac420003003117100580e1420b0215035041c5640741d05581d44c41d2003d80841c0c00039081805015041c6280c0400031500d070440d4416400c4c495015200c00c0e040640e002501c0014001d4002d168081d4502404410f8400c201c241ca01043c0f10101d460301c00c0d4091440700d0725203c6049807600c41d4450380285e080d4001090001c821240c03c5603601e01c6221421203801e00d41000000c81140c18a020b004075071000862a60560280841900c00c440030603454592b2820503a807404240c4601045a1703400c841891080400e90081c80360070b007012805400c000304038903200102c0d01c80c0841c01002d40c120001c0a10608050f22a8100d60112061304504000780c420100b0150801900010141e60307448000c00c01030526488640020359000c201907942e803ca40500030001100642681c80701c5a4408080c060001c02040e01c03811b0742c0603c0c131524004d51512 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738639208 1250 738637958 738637973
    0x1603240b0913030309080c0d1106070507080a0c080301090624021902011e03020903210313060b040507020f0f06012d0b030901061517010512030d36030c 67
    0xd03038101d0a140e03941c0c0380e45c400607400307202811001420070081c00d080052214050891148224244641c0d08140100b00943d5040820743c0d9031240c101d0410b60b1034010090f03050b02c0d44120048040c0a289012000181c80405504000c0688906900d600340c0a04004807c0010380c10309400000517800c40c038240785080308071003120701003d40145880c0c0c0311101248100d042c1102c0c5000c080c400031740c00081d28105800e00700513420125a201d007404501c2c100010844110703000c05407101a411a071410808140003040e003000e2480080180100000d00b007084000c0d6407200008240001e90107001124400c020010650504950f04044400302c3c03d0180748204002d10f259046429409103815400b14082d84103402440c4036900c4640002416030030010399850307240e004000501003012941050300b50200ca1040305044810aa4510301154044a0368905600451503a6482c45107062444a4090f205000030703020858085400c50027844800300155046000540180c0803410400020b00084d40701c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 738640458 1250 738639208 738639241
    0xe0f130e010f090506040506010e01080601180603140a1101051201030f0f0c06020f070f14010804110301020d05060913020904112b03021e120c1603240b09 68
    0xc050002844200c503040d180201e5003121000d4a0f02d501100c2044200501001054058660300810911a6262507007081c2c2c2c07814140100e002503524550b081c0402e50a5800c0702001c1d40e030202d003000c840c080c0c4503207190b91030400203404da650700d00d03088000c840b95000e0005c54214150046900c00a0784c00e507200c900c2c072a00c42410031990600e5404040c004500700d010900003524955010301443d400c400045442c224494204005124410034104503036039281070302a500c49400c1c20103026950301c604108410907058103281c3e030903500010b41c070b0440c10f43d0307640040c1c880c802c11070340682c1a13261031811a5504814120007504500b1500c0030074041410304585504504d00103103020061444058824000d00403a00803514074018040c600040640500aa851034801c054903184900748410b21a03a86e040c060168421412000036604070380002481612005c50343c8011064109543c2d1408005070210b152043c8040a4601d000b9001c404a601034000c40680050103a0b0385521195491a00c0529 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 738641708 1250 738640458 738640481
    0x40b090d181436150d0210090b0307030c031d0a030c080c01090b010302041a011d04020409180312020708040603050c07060518010e0c0a0306230405010204060e0f13 72
    0x1400340d0602040000c0007a520303269000c1c0d00750065111030000081d0710241c1c041e14130a50002141031444854a0f03500e41000010740480d01108034050b00041a21002e415811059a0803000010015442d4054100203440505540e04001061202c48459415140f9114914081c0c12192401011a10440c00101c64030300443ca0755145c44104d8894500b14ac2140380201da65602050040055280034400c0920000c40c0c41e6040c08100c00340740000380762444502910254030078145c4414000d40b036940c1a41d0180071404001c001c030020541407100d48003e1020100c0c0010301080d01e0b080340050b24000d64025035441103056080c90300b84003007500545001402c070280010300b40016000300e411405110b000ba0540d41a024201000401c41d5007540c0d4000e61901031a8001c2c200c810080d2500c07405001126040103001030b02500c03485000410f0090340d164060004808002c1c002440010b50060080302c84580301e07419589010300c1030019401c8580d204541c0010580802c500c441241c0d044085c4104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 738642958 1250 738641708 738641719
    0x20d18090c110a050601030b01060e1503151c020a08031327020a09140609010219051e0d0f030e1f0b10030209040e060112060213030803040b090d1814 66
    0xc1e001d00c036910b000f44000050358a0340c4030000401c2440490010303207024040c50b140040203410700d030700462203003003400c41c45051640000001a464801000c9015003410000301203504102a20341e40e410b081c072035540164440c91300c0030300004070008000210385291050a0f12580d1080c0b03808030780c8007062a440781c050001d0011420002940381c041c8003c01012000b80c0342c0300000f0341080c1c1c104644601d07212021740200300030001081a0780e00007900071900a800d62081603222150329056080046000c01005d08021050304083d0940c2c010408031904075442d50b4845068400800807401d4824518824019800c0200101d00c014900d5065006181c1022808127040302100007082c5c0c958010741040c00000d60204480e182480c1030b00880043c510003070020b00065051960380441c0700c00c54400148040d60000c1c18810011a252580d80215080701c1244c1c0c9901d0076051258841c1c0302210048414018a50b424218a00403d1802040840081c083c4401420039080070003c05070401da05600c403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 738644208 1250 738642958 738642977
    0xc0a03140706241403120310090c110f07050d0305160b0112020420040b070c0503060c030601080901090803060d3f030203130213020c0a0b0106020d18090c 68
    0x3900b03030b00510300742404010258038a942c0480440c00681c003281c00448440049041d080e031180d070700003a15002880039840c11039503504d80c1c520840b00c807002c0b5032105d00c140d030030000920809904002e40d010345a01c100281c0d8001c0104040850305c0e04030b503010703440d0b00030b00018a43c00030070721403000341c0014803036040e41e510218540e854000c80d44209a0041c0b42036246900d40c2011410240180d040003100c03984030109140091240d144036004070700564203004c801141c0c10040c80303905184e11008000180a69849007803001094916900489889004c100c041010a41d0348070148a0028042d4000c442d4a040d51030314000c0103d8414044029600c11246c1d605010108040c901d001d040b40d440340c84403000f003483e45001c0b001901c1101d00d4810a141c0b0610805c1b00200e078038601000055411034400c0600c2285004400c0240510350007089103125802d039110401c05181702d035030305a82e002e40840742e25180b801300c211000d4940050003100b440c004581088552001d411000815042e4284003011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 738645458 1250 738644208 738644213
    0xe1b0d02070b0a0b0310050903040b03040c09020d0605040b090402130b0102010b03010515041104080d050901050d150807230603150607030f0e0405131101091205030309060c0c0a031407 81
    0x200b90644400d00d216a5801c9a2045840c08100900d00224a003100b84564075210780d08940305d000360302c103414500000200160130007500b040303442c01500d0300b0081151514100c0001c4402002c442c01006d005a28090b0710000c5854003840240c4107550007407400a200840c8880840030340380e130000b00d50542d925030003070749105d55017802481c0c40782001004501000c0710780f0341004180c8a090441054070b12040000703100412021a400114001c0c03400c1103540c03440c0150048400740309821400740150f1520045451450300001c101d022280c4d007204507170075039848a509000049100c0d819027000100c03800ca18040741001030103950701c1070000809030181c2882001168a43d841124220006031200e40c111f011190480c021040d1178805480802a51904041e40084c2044902000d0050000000b0f0740b00300760b02c9181b070031025040c94581d10810740107601d0b0850f5241c0041d0780c52503031402008001040c0703120605c16210f080807076078020f01e892000c546003690300114500107010f1854042050074003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 738646708 1250 738645458 738645473
    0x4020405031b030c06090913230a15110d091a0c070605150a052107062a1110230306030607080105300709060e010e1b0d0207 55
    0x1902050121110b101c40e4460101030404c60b41c640303194461041800186000c0d15465241a8030444a2400c104581d1150a2a000c003140314005080440070500751141003c0001c203003c0d005902c65040c0304030044001c0510310903a1034940300100180f000740444500b480a94100a000c1030040c0d1075030380400c007454140c0301c0ea8402160a0980943c0010f440410404036100301c980c8a0310141940b00f81c0c3c0e4070500001c1d0104454402e5500c1500304070714031071030700c200111082042c8075048100c444c25680c0d458083d1442c84440780034201041405002c14920b10358185075880250b1080c214050103901b4010044680c0c254002c900412821500700410000003000c80001000001200394a900c1c0c00010907140c02d0006003000c0400a407800108401c2c0c0320140f404440c0980002026240e0104524051900710b0495401c0b03a107111f01d0354001100401603000c0b0b070583e10540c0c078523101681c0300c2e00400170b40e29007510f0340300d5040700b0003210200072a01c0e40050a00186008000b41c03070310100d6101c545 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 738647958 1250 738646708 738646723
    0xb22021008011e0f05040209040b0d030f090f05060322050312180a0f060c0201180b01030b010b0a05090904060b1801081b01080f07170f0f0a020403051b0402040503 72
    0x10101d5000e01c0180324a5001019049580c01000c1c0f03042d1070f641c207000003541d0021035440360a018507000320f90f80650327554640000100e0280507110b0940031510342401050160034039070310f002003400c104020410311250580f10303054441c081e00c990b1035905c5481e1161520360f203909a000c4a5244194100d001845c144010401c910f40001d1400f542d003088800c3c00300103990829071211075488400c0081c00200e8134103441c0c00287d003000e4009035008240740240d001d0000e41c0e8120381a05040311505041201c1c00301e1050680c0d00a440d00070303503aa05c43c03200d1540d6110701056000402d400b4094130b41146040c0c1001503215109600c007045601e50b00d40420401d600000300c0350512600c0000501c040e407001c001500842228004c0203403140441c20003c2c0a682024003842400b003c0c00d8001031801d401482450300d0701d084400c5450080c40c000440c4c0309809415108620413106181c04587c40000600980301525042000752030344105031114150a8480c40d15900c0e001502480b00080c079590a120b0803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 738649208 1250 738647958 738647989
    0x4080102040311040e0a23101a030109030903080a092c0c04050604050618090421020312180a021e0f041503020d0501090f030f0f0201090b2202 63
    0xd6103070350442c50950b00d160000540d85000d149804031421440341d0009070f048045400444410200b2800c07000c14034481004402c0c400390348942800c0c80310f011055445285e162151514000c403010090f01058281c40700ea5402500190000c0c40900c041403407803008000d001c00504103600856a11201000d10b60b0a40720050210900c3c0e500302030408161440d0250b2116074034181c50b2802d0305101c00620b0310b021700d01455004003004546d130b0b0365803a188040c080c0e0f007440c0105004102d180c10700d0410240b03068280f000d681e00303043c0810408080d0000084e6074801442c1c5481d0035a03942c0708408100550408450403400d442090010b002586420600408603d100655088154400002d11004081c00502980202d00c9d056040c0721144103001c4c070303c2c29030f941280c00f40341c80890740c20010301520020714094029448030680c8010150401c0319000402d0340307a1180442d88070408401e900700c4640c0d48000e098400d168000032a903c1d0000614011802c900d40041160080c4d0b40100745107142103c2c00c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 738650458 1250 738649208 738649211
    0x90c031217013f140d03061503052203051b030c0c0d05070308030a020d0501050103151a130b180a18151e030b0c0414060d0e03040801 59
    0x90091140d03101640308541151906030101d80c0d454518a9450351446000500d10228070118090020250b00c0021408201d07400b00c62420b4040c5080000f140407000c2c04111407440341c00c080b00045402409860100ca500110b40580260010300903800b03848020010032564410a4003084804482e044c0c900c50b4501a580300f5480e1440000407c41000c000c800f1301c40c06520a0129045104d000600210061010340d0103d0b4090041c1c50110318214150b04001e01d003500200411180114581c05030000c07001100090210f6681c502c015400c8402c0c08140c0560a0011041481404400d036a0b014100e101c0030605860625815000f008112113604001811360300010b8107401010000e00003d0b118600b102c140500e2071401d1707240f06102600c2c0d00f86214098a642100c110300c3d0501c0101d10003400b0100344c03030445401d100e00020401c406404200c480039915030203e101d40448030300740c6007a40d2614802e83c11400c59041001180d80040480f00d884980790461440c1c000000d101800040c070b801d400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 738651708 1250 738650458 738650483
    0x302041d011d0d11060c25110f100c061e09061416080a0f0f0e03120a20030912160c09020a08010506030403020109051f050906160f03090c03 62
    0xb100d00b040c00b075079a81000c20040922801014501003006078004400c5104030b5580c0e0310820540d00100e40c0001100300350380c83c0b8400e08017445900c1c0078811005d40211f444503150324034441040034611f050b00903800010b4404007040700180e82588a4240d0211035125900c03050752403103156082e129060001c95a15490301d03c10310b00c051254440c550401d060301350092041c05590310040075500c00030032a081442d2501c411041011055000260081024000384944160401c20b19600d034049050401d100548500251803407801d0311480f00079121202411301030340e5080f5089240d0340c09c050b10307141c0b09016818112600754035200050072009804008542640c480d418040c2402e2025405041c04a004000ea1f40380c00303a0104009054410881c0c00c40d44036141e9090807401040710b560300503c544100640d0005002c020010300b03012503040207080c030140c3c0e140c030221380d1245001c0c0e800d94103481c9070041c0007004600030305025104050500c3e00085a60a076228152246800d50064418480141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 738652958 1250 738651708 738651761
    0x51c09061a1305160f09150f110c060d09050102041211121c1b02031b040b0f10030b1503070921051203070203070615050a0503160302041d01 62
    0x312580c540c5002c14a08004501d01030910641502a20740d202080044607800301e10240c3c080c403100303000b0300351100304004202c00e4410080c5c10f550010001c600403030941c10f60f103401c2d51800981c6040c030762400341c416810700d11421700c450f02034041250215180e540901c80800c00313112201c1400d920398040d20703005e1000810030051141072583d407032441c0710b00d0304680707042043c903200380081502032001460003051100814584e01e00d410203140d0001d502d4010380107080540c40075101e41d01402142120104400f100c03402c02c000380d0010520000c0d8122401459a090003802580148402240540041800400e59140e0305142d40b0032514000454201c50091101c2244001808140d802a03024070955400d035032a071a43d28030080303480c2c3d10282000000100304034424800e4526640c1e009109003c42c1a41440598804c880303401018010740e130141c00002c0c5403a0000d442c0586080100450f0038650540d000d110192501006111b80710a00040241d0418002d10a0f03001d54040c44a480d00a80b03807a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 738654208 1250 738652958 738652969
    0x80d050708070e1c08210117070b0f1c050a0b0109030203030d05151206060f0102010603031704050114040501240b04170106030b0108031902010507051c09061a 70
    0x1605400400441d40200118280c2141020001c004200c6484a41c03044824102d184454000030040000c0c5010581607100040d030b1401c2d50719103041a100c040070f40c1e290044003800d25601118a0455441808100100c0480c0030040400d40884401d092804056040000c40710b4142c01181800580d20300411055003a94030414401020034600401c4030b51850300002e03620302074440700010455407003011551200b1244c071a0308107900301500441c20055000002130f120041101c80074003c07180c400e9064429841031145a0581c0d9264451003040304519860310884840107004407050344d038414030626483e40c078855992141e8172600001ca148c54848001c2d14074804840b011080100300503000707210341302500307080d50255204d02003c280c1d507100404030305002d001e0039840501100085000858201000300007407480082c000794a151040302640304070308840341261a0b1002600c18000348001e80a03418541c20b0703200034007401003454030740c907180e43c1c0486200305101d0310300712064000c0e43d241f81001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 738655458 1250 738654208 738654211
    0xa03020601060305011a04030212012d050c0a0203040e0705090415090c0201060503060615040b130509090d0801050f0612150f01030b1c170c032502210c040504080d05 73
    0x901d03605c0d00c2074288001d420580038600000384159184004ac030f00a4a00351b20074115480c4150059242d000c10004141c000d62460387c1e0b4170900c1e4103000000780402c05500c00c4804c0c650050b802549001d19008c04a9007100010b0644002c0007010010b071910b5540b01e00403060340065504200c1c4445d850b0030709481c100c034000d4001d50256410040100002d81c0c0100f40c041c0c0c400e005642c2007650000d140d2201145200d04d401000700b48502107185803001e07110001c4203058980031f60304548640c9490410583d1041c40a250100217900d03c801405142840e220402d00003202402c1c050424000e10203001c081e9004803201c01a000800545030b003d0b2604140781040c8030020b0a00b002680705402c0031500002c112000c58155000d010301c0d01d410001800c1100d1141d0440c1902c0a8503006400d00b440d449034010503074800c001d02480c03c1e90f210310140ca000031140541c000c0484001210f848008a090f800c0c1814044c180d00600340956007036101ca002e9584204d00c00d050095640e220f445e44041120070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 738656708 1250 738655458 738655469
    0xf0806040209011406040b07110f0a08030a0c2d05060703231e01080c01090b090303071b081501050a211b0b040308070605090624030a050a0302060106030501 69
    0x448014080903844028115064841d02c0409840703c04608000c12100c0c46207038404200c10400246020500c007c440e605454a00704458a00c5101c41540800a100105004100d000d030010001c03921110f000b0080c403240c051150222100455000f000036501518140504664510708000442002414000c0c1c41c0d0044281c1410804136440d00708034419038900781261680d9030a00004140c0c0c94080f030100d02026005103440b500590b84131140140c6844240009d4bc1c00304d412220003140500d002d401340e90490601400840c00c0c00d826440c3d2484807801070701c54000c5480429004215600107000500c0304005104904045502d07041c2805285a040d13072000c21520f20501e01001118040f803022034040d40c21080c07c0428122008038920011200e50054172031280c00500081007045e00005030900ea405044104001d550742d95038952030705400c403150409840380c5440000a880000c003024000503000d03084569507091a07851a1a1901111058000d40e015900401600744e0500482c0e01510b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 738657958 1250 738656708 738656713
    0x4092d0206031e071e081b07050d030f1a060304020d050f01240806040f03030f020409060602010b090708070c050c0301091407170c040f141005100801050618060f030a060f08 76
    0xc50181c1010450302040c417490200207680d0085101c0300b007006822404c002e881546560340302d2452408983c1d6507200402040480e0401084520b44240e900c1441e10f100c03020720745400540010000c2221592005000302da221110032742c0900071407400c10090340c242078080000100c000303031220202c1c08100041140c8900c0c01e4900d0051000030000300c0d11b81c0e08550b0002070091440c110703207000d901512030381995070740e601e1003c580016030a030b060300900c08a80c0035070000c005051900703040c000085400c40301c0002088460011584c0940300d01000034259020f00305403401d84c10a0000a401e55158a4044e151540e1040310700442c501c051003564003c1818004080c1c1010f03120046540756240c04400c14801c03550b801030306140b11800d41000c030070700100c41c13114851854900460030010503103000380c9001c1c5c25040c00b0554014042c0711142e043ea40002c0c0458200700c15440012503009a07250000d800450030f00141080807a0b5501441c01203c0308240803d1090811810700d1410140d82d00841c0705a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 738659208 1250 738657958 738657977
    0x190b010609140a0e1306140103140303070807052208030a03050c180114161203051509010902250f120f320a020f070504092d0206031e07 60
    0x203990348201c05044800c07400035129503a6907031a8420010100d2034020384118189502e81e03039044014000241070303c1c4200e0000c214132031800241d03540c1e0300cc02c4941d480460442000701e0750083c02200902002444044841d003100e409038010380c800380255011403220b51010035030f0010650940606a800f20a02c1d16050410b4a140d14540c0303150b0b8502d034103d0501014101d10ba0380d2076590421540c4c12400001d0702c071142d000602d4041d2682400140810020349084042a5000110010001c6110004080b541d05900b400c00900003903114030208491005400c1010b81450401445030001d036004000031b0150080b81d0610034200401001c0c41c40400c5a0000e00c40101c680080180b045c0b400c0d542c0015528002d2150b070041e207100c1800c0b0034010070300041440000785a00203040107402200c641030f070303009580d22030511082d42e1104100400307a040500319411807012010801800f00e0030065150011032694012074110b0784259250408003400e40f080741d9000c000c00d00040d401000b10f180101c80d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 738660458 1250 738659208 738659249
    0xa060b0c060103060f090b070c050d0e03151e0c0d060e0609010b030a061815080f0715050f0d0c030509210c070515030106090f050a03060e190b010609 66
    0x100c0c2014040242205e984c1c246650003c80c150380f00e0710049501100314012414203200c00381081e01d104404480c83e1003801945540070348280c07840045052b0240051614841e4103440d12300c5540000e01c1290340c00c1810f400340e519a1104008280030350f09400301c5558174219030091000b95009504014801c1230000284000f6454442403541103401c0f85080e40d4907a01e407288180041e061a50001e5503c074a000a0040151003503405205015042140f152020b681c0e860740740d440342c0b81c0101d10b03460390300440c004111564840602050740c001e41d18040e4036000d074861a45a05030000f05007071000719070380e2900c070085a400d44a02034010014500402c160b07009000290300030b501c54080961024004140003440407003c00001d006424020b0120039183e522410080380354109201b40c10010300c142c40300080a19681040030256103010b0500a003080c00c50b00d9160207000540d04005003072080000c00d8100c5011000c28401140c440c1c440d201ca107516018008254581c141c108164407074480000252 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 738661708 1250 738660458 738660463
    0xc1215050f0f09160801151406090405072606040e011802010e01030905070e040b06010c1a180a05010f0e070501050409090807140f060112110d05030f0408060a060b0c 73
    0x34803100200c0704000b5680c605003050304002001c40501c071585441c803000f251040e0103400c0100f0001d048091074981d10342d00c0e030300807101140d504281a00050104121020b900b8590081a800180c60a02110a00018480c00c1380c00d0030350000c1c0342c08040d07180180310070f078030309401407240f0340050070020700c031a0740c6680c038040817044d25880003414004950101c10059019801c081072a41e040800c0d5156143e841e480349040300001c0f00d04035101d0603c40c0008525601460221404030303044440c00070150303824100703007000f114003505d4908004003850070a105228100100c81d00d092003030f80040381e00d001d04100038096a100243d00754082d0003651051200d40d07405000d8030111141007101041440c46130a00740a14400c08001400d1040c5400d4440780e8540006180c81a00c0d1030340084840740d0f81d03951103c2441442e400da00801c0341c100c65072800c10754034006080307084c46801030013602d14001c40240f1441d00703a4003541c00030b802600a042000318006441c4074000003052a83e074403d00e45500400c0ca982c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 738662958 1250 738661708 738661711
    0x2010f08060f010c05070f0e01051f091208190507060506031b130209030703030207170109030c0602030411090a0f0b03033a181b030809100c0c1215050f 67
    0x5040113444480b00c000d01c40d0070090307440144486984068100d80b60001450842d50900a41c0e014120b1240a1008000451803ca40f02c41881e0b83e0b1005890178114490241000880c007500c00c0b550a110a49d2046c0008850000390165500d456948046602d001420341c0d07001000f1038480d4012000704c600c2c2c0002101000304040040b0355098010a2150ba208000c3c01420000c64140c407a2020200400d82c00092034402e440081c43d41c03074840364030485803d081e03c0742c0c8240200000c2c20701d03410340006202070700910341141c80380800d11917002500d40420914001103030024205038403910010004075280c4960200210b060300030f5480c01d10041174411815070310403500c140e40c0842000410031f000c01c4403500b4001000800040c0150405c41042c0798601440340700940301e0b1b446c5444d48088000001c3c0c1c500c01241da21800b9641001244c4042100000c0440b14840600002030750ba040042d0201110b00080c1051038800b54042d9000c4c01c0c103d100111012032040c1d110b24001c14481c8000341412002d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 738664208 1250 738662958 738662989
    0x130603080a0c05030c07080705090c090f060a020c22060f03021c02010c051914030313030503060f0909030a0809031c0b0105040b07150b0d08030c0f1603090302010f0806 74
    0x3070180b00c400b4607005140d445292004290f5000b050b00100700c00d40c0100e0b18200300c0380f0881709001d03d920303101440d100c144110900c00364044d271103070100b66150a1101c064004030400340191080341114001148040e010080100540c200c442c62480025820344200d2001d0001c11030050708840c216800b145501c0800c3e80011000405050020116031103550191244c542c8401034546004000010451003030012900b2140480020340906094900001740e070301c41c0c440c2101c4031014206030f0302d050751a0340c07010b070400f07403c00e1501020300300700d8945203202c9014140041c011940ca80e9024002000010007910b1300c042c541007001604015801f00d520402000c141c400e0000c3c0381080a0010303a030b940304aa100d00d140c01c1003c01c1c080300340071034440c2403003a40007903240070f019403002c0008000b29503c81d0100100004414008103448456480c060104070b071002041600e8014845800d000420b6549411400501010428000c5591100108400e654281402422410118000381001c0300c0c95201313 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 738665458 1250 738664208 738664217
    0x50702090901020f07110306010510080f070311040b0904150614090f0d050c2107180e0f060916030c0909030e06030a090203071d0c0706110f030402130603080a 70
    0xc159607000a42c11601c0816821000590301d405600e04000505145001c07244a405030307200010341da0400e41c0d800707044020243e42e41c2203181c0d5000e220141040c07000d800d0b84101503452508a114030b80c064000c101400d0312000050719803100760104405d03a0000080d4080914000c2000c21010b9040f0300c0d82c0090b020030007500ca4584200d02d000c40d0000340e46554803a4030036000b14903c024020041013004259005847c4d8031225003078000d0311359024003029a00d0030031b580704030420041d01100907144030492000307550100d1010340c00f05034189025105214a54141c001c44144440750404001e80d06003104d082001c00c0b4500e146440e60021900240f04217903509441b100614100352184510101098004064580b207052444450700180b42a580132802031188500c00320382e08440d01303030280d516048078050b4429035890b240090301940002004944207902d4140010b1180c0410000d8802981500142034032490304d80104201a030000c2d29000e807161502c1420300c04901e001080340d202c0c1185003803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 738666708 1250 738665458 738665461
    0x203042c040807050607021209061810080702070608010f050603060301152903060901090b190315110a390b01050316290f0a0915020d05070209 63
    0x100303415151041015144080c010320108010015548081c001c0c1e00d0149088400c0d070f030b40f100410b0313030b450300c0d003002a0000c4001805690610703e072000017071005001c4c1850001071084001c01060000701c150501c0c00c08614101d0820a4481d0304210355002003049103060300c1c40c0c7d4948500c115200d800341c0a000d0158000000040341c503102500100c014450440185500a80d1800e40303a00350340783d10b00c0030004050010121516542c03000c0599000303000041c64611300303910704060f480082c01551135081c0c10030102907107148041881101400214010242c1c03c0c0c2810303110800c0400c80b0110f0010a044071020b110204010b03500c40e400c0000d0700b1010701c00442402c011402c4846c01b141c82d080f20842407401d1000501001801040e0354101c0d0025422900940b8a08560300d0580c0440d01811420540040b2014072011032809816074480303170180d0451400811003100c0d5015070103080044089103080d24100030050307651401d041c3c009003501c041c0c4a00c00344041d000700544101d1201900c510720100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 738667958 1250 738666708 738666749
    0x90506010b0a02192a0b28030b01140310030f150c0503010e0a15090204171902031b180405060603061b160c0806070f090e060d14151e010b0901020304 66
    0x1708507028001900042c1d03160381c001e0308a0501004854184080550f048215410043c06030207920409141616080000080403240d000280c01c0101440e180c00e01d004000404a0680300c448102c0c81d025040c0c0d804455191040b0380c1c16611202045c01c10000e040004000300400c0c2c040d0140c00140110f0042110700356009403108242c52508900700080c4000760000c0c010001c03da09941c150242e0042d1480194168018800314a403100040c0d0188c000b0361001c5010305a464000c030200c6c034010724180c60402911505082c0300e200b00c50840365139100350700344062440c04004403644120305014000ca0080442880c110600a0507612080c5107541031807981002041e08044011b400300d00202d50007440c0c0641c000345406000000c3c00089503408001145c240c0850301c1c503601c82c540190950340b500701c07030f5641e40080340c0603155009a9405086541c107000c0103038540050003410030038101500e040c1100e4400c4070156043c0d20101044404000401c42c80e60080309a400b2100e103c00024400c10412 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 738669064 1106 738667958 738668033
    0x30809010f0210020d05040521090d020303040b070501060e01140d0b070c05011506020d03050f070f0c14030d0c0f090302060904090506010b0a0219 65
    0x20400496694040c50301100e0070410351040301c2c50707240b01800c80c0040340c005902d40010310381c40e0707400e01c014404104250400300c101901d40000d0528203e00c801d00502c85c4001c0c5502507403809038440300390344d01403050390010481c070a500c40c0da54085250490003840390340a8003400303141160010400d03000904800ea020300300a81100b10340290341e00d41d072a209034000c00310b04c2007007003001c290f0002503403c0c000c3c040c1c0c44550300702c881074041c1045000390811400c2422403003018a05410846c55202880c2c94980080c81c0d0305140001072190754003210b0074100480080c0c000201102d00c41d43e02100003000b028112a12041041108403c610031140500309501c280c001940d9a04203101628020000384240b0070010000610406a07580301801c2c40801d9012019600000c030b4141d416030b4050100c81510414000070030842210340e0340343d034052203070300b00340c4820026413144040050011 = true := by decide +kernel

theorem cover : BRFrame.Cov 738489208 738669064 := by
  have h0 := BRFrame.cov_init 738489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 738489208 ≤ n) (h2 : n < 738669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
