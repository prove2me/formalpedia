-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2596
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:05.22343+00:00
-- url     : https://prove2.me/submissions/ac711786-a9b7-4e0b-a4a5-8d56dc098818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466726618 ≤ n < 466906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466727868 1250 466726618 466726633
    0x612060a050a110a02010c021b031e0111040b03061003060b0702040906020f04060e0a170a24110c06010806061311070f030c0309060503070525050f030705011805 71
    0x100c10003900d00140941d03405a00d800d04207101044aa0181000010907000462107004915000b840d041c5c10803981e80d40280003ea1001682d03d01040310300c09902e40d81110140c803000b98040c1809085219144440248000703030024141c0c7c40785002c2c50143e503049511026140c1c41d08401c40517034270140103055421008100352401494203038082800075100715030150620340c1400d045004c3c1d07000b560180300482c0780c69946044ea880c3c8201540c010b0600c0b07070001000b500c2510040c5645030b89206000304104030000e681c004012103000042d041d05008801448103d5040a582c2029003180b11034040c148209c0f00041a1440081800c9109641c06090300c50188642242a0060a0504001503490804104500200d0518480140803038001e44a214882130703107150040c440040e560201c000c000040c400d21100a9001048030606151148403594010500c502e0315213406a40340010954418400705014001d17000c8040c001306802540200050481189000843c000c04000181540c0200c076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466729118 1250 466727868 466727881
    0xf13030f0806010e130c030509072103050405040911270a0b130203070c0203101e0b030f16180e15100e01032004020a0c0201080606070609110108061206 67
    0x201c190340c0308205140ca1112000301002080e20801100c0c0281d070000d45900040c045c0d00c1c2c050103142d4221039032070001c0501c24500300d0f5080c045001703242c100243c90712503c2030009141c407490a450103068010810400d422440c034000c4108203a0784034090050080c4131082c1081c1414040e0202c000c4050703500d801c00355031403143c07a03c010040703008510b52121198801c0f5816000d80d2016500c11540c039140c9480f61030040c0101460f1046480920341003500301001b242600e81401000385942650842c0032502400920000b401c1080000c401340030782c89010f451095030102e450400d41240c000000b406002e00405200c0c03401d84080f200b0300d00980e40a20050600148403510a541c00a82c40b07001a0525031103054001503030b58203038410b482c1644031a0328144481b04013224050050b03000c1324118039250142c94003901e42442c00304081c0c140003071000000c0494481000320740c00310f5404038041050b00d00c103190001c0f400d44480c40144c005200000001c0a40c1400c205d0010707401084401085550b40d0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466730368 1250 466729118 466729127
    0x20d0507120c171008070b210118051302032a0a060e210f0109050d0c150f02160803090f0309030a060b040f110a0201110313060504020409020d03080f13030f 69
    0x1030843c4c21011104100000c0c0321900b400124080c2c2160281556a1107414120401403019000022540d06400c40104400601c82d00c00080440000c3c1c00400c607507032050610b8044a48900e000780d0540200944488071690031200b9991300380407400d000c2804946401480007581442c080d110203c0d003200c10505652400d40f0400010f905007800c42091500c20290007428007840e52030502d00c5030f4544400d6010080180005800b2503003a1500c818041e00070340300c0d00d00111800c40c1500c6810760311b9455070440c00854044038007900d040035001982840c0303840d08000c00e52080b244034295000301d03071003044100c030084110380f10b0307000c018010458030079207407240b10040440c45c9405034000e680b80c8002001849502542913180c90a0b0000350700c0351900030010b0309540142450070510f003000c004000800019240d504041c607004040001e1303554542c4007150003854518800303988501c1180c2080e04240d800039a0078400d19005081c14030765210b030008840b00c0c0840040081c04100d084200c030031840d114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466731618 1250 466730368 466730371
    0xa06080c090c07140a03030507030b010801150c0b070c1a04022d19240210090501021e09031203070e0f0d0609050105180c031b13020d0507120c17 64
    0x102c8950502e400807903911030100201d08240e070301003908000031070001d0507094880c2e6544564641414403800200500090840c40b05004600908124807405c481e1240308034140070460342d00205d118940c1c1440c2d10042d24805800c50100c0e124030104040084024107a2002405a0360190002408010040a49a516480c4031103e28101c1c0c103d21405840e907121419140681000c030703044280c035802d21015024100700580541c0c205c1c03043d14054044075030300040071541c1c541b884c00c000a6034142460604d001e84110708440b4823055440c4400b14140800c900140001442141140c0408040740440d84042c041160f1020201e401140d2401d03550611042038111004014028012900265103003001c44074455000d9446a54039002c001009501190074810030304a440103280145c000d1000a907030b50602c1c0c4007080400d01092100e40652202440d0541000c6115425501d54202c6e40d000b03401844100d40300400540d60071442d42802000e84115030410701940c0e00e1104049045000300b144000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466732868 1250 466731618 466731631
    0x29040603111c0506040b1207090c0306050618120a08040b0304020406050303190e0102030702091618080c0307120f0b060303190207170105010f0e0c0909130b0a06080c09 74
    0x41041001042c1420240384400c0d100408000182c0e4140702c818082201c0b000543d0a014094400654404c40c40c00100d4800700c54031079101081c01d080c0302a0803405080d950380f010750000c401184c6441050300e40190001d001c1e8050f01e0503c0b0340309103a02d0541d03031507215200142c401c0b501044280500004c000003160300c640080c002040705035444000c0707071071039100b84181071648000070440380a0941c04920520451403d00c021030411281e44c00054402c00040c004407020500140d00da2032050151107028184c00705524030100341a41d403103800c1d88602243c2c00036842400384c15804078483c0860b000c0d40354650307042103040c80744015540c1c80200c080005004240e0510041c0312a8044914015040740604125070107070805910380400b4096002c140b20300c0c0d4a0300e03418030006101c82c410440c9020203e070b9105196200c05c8e1520411440c09125001c4680d13040481c0d1001c04c070301c00c03021022200b081c0b44540d9415549580c0c10300102d00b2110f0034060240daa800100740415140f40ca07a0f1210b42225 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466734118 1250 466732868 466732901
    0x4030207091d0d18181b0c050f0607050d050406110307020303040c05010525050a060203010b07020a0503030c030702150c0709140603070303020c13020c0a03030e0f24070215010b0429040603 83
    0x503001500c058503182c200c0c0c0c0e0780c1c0c0011f5110161004010f001e20480c3e5560150310300410700c5040170400a00f45000b0030501340740f0299983c00241c00d010052300b010130302c00d008800700b070759a0500300c030005c1d1281e00441d4160b0f0b20385c110110005241d4401c0c002c6601550003209111400180d04000d82d082d4182107074195044c0c4680c05240000ca13065100a5008201d8071508a96403003640c41031010b9108940d001030b100390800e1001c600a07140120466108550444000d10183d1a0402c041c0b41d50181c0c82d04c5100610602c0d101080d42244e42d848010070305484407410072556161403c042c0d0300c813010300000700142c00c02c8040045904250300c00c02c00c1c40415500240c2072040821505141141d0740400390300180d1600304000c015402480700609201d082030203040043e001d0701000542040008a28100902440020b80c12a100f4002400c004001031903040543d40c0da54178a030507982140c0074800f209444d0407a0b220903c0240d076444c40c1c3c0c126050780314506091400d0825001807000c4034400c1000e1323 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466735368 1250 466734118 466734131
    0xc15140426040b0c0c09180d170627090d0306051f080a0621020901052e050c06070309020306010f1a09040207050a061e0903051204030207091d0d1818 66
    0x90b138078004100d1082c7c010084958a4a9a40ca00300e883e140c540130854080c0700d01501d942c09054103122900d030380b001c001d075060b00b04030544041d003110520b2902d8100c0e14841a040c01d200203118040703440221400c584d03405000150721481000802400c202d5407004498100b04444e10b803c2c010390703441e0790014080c2d50005640e030f83d07215502c200c488400c0c4241c8100c00821121700441c50229003d9000d410144c62410040300e10603202c8041000a0300f06940c503694003500c410907140304400310340b240b103006415501e281c1400e08018014119140d0100e05c40d00442f00003160020f51440c01c0c200b16a07607130300e0004c560003403031011014075031250100c140c01c55000c000341030114208022614040f44683c1e0f0011300c0500080c5001c0d80c6003400c117030340c0d419a4180b410382c001080c1d02c0b005440c1d03183c0032a000049a13032202e1505900d4110b99070300c111900e900b404d14107030f0010701503140c542d050760161055502c00301100f501225804880c03022090a00c00f124020b004460b80005800051540e43c100007408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466736618 1250 466735368 466735393
    0x60a0f0e060a0507060e01060501090308090406030206070b070f0f020c010c020d06051e01090204050f01081e010b070b0f06031906020d050c0711090114010c15140426040b0c 76
    0x41d60180b803462021500024255082080341d00c903110101c40c12800802c00b56042c08002003203803005104c0509002004101150980c0d15680880c0040d51300071f080076540d00703185c6400500101c04468040120700084588018503005000040d0030018a0340644880c0712004019a42600f01c001c060340c100360300b80d182c48005206031148038011640040d003483d03010401d80d01c1020654050b00f003003c6040c014001000a40c444440200448809080001490b034a0307000c046124206d21100c040c20914131400016808c3c6454010020140168180295030395021046101d401d07040e44c1141d01030340803034950f98124074042424882e0601c110000762418080b01d00c95415614259446030040c040015104c0420190b104651804036054814899640c580b10060351403100c2219002e0500081d14080000c22640c1c0c00e0070980b00c2c611840030485192070300c0c65011101000c9a048445c0701c0ca5160700e00049141c2294001689a01e405c1c0c9803515042c040483c0850300407803101e020700d11071040390f040f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466737868 1250 466736618 466736629
    0x61f020c0d060e060c070b0103110103230601260612030d151409040b0a05090a0605040b06120a080d0c0c140f2401140a050d0f0203100506060a0f0e 65
    0x241c076405080b000c590708410040745400c4c88005850800350310810810100019036103c0305604494101d44450b0061003000300580c058100b0f007042900d00240a102000811200807241e0f014140070380c2d400c50754030b0100d441450340c900d1b4101d1659070014850002411454034110b401c03004b10803941624145601802d40c081503900d600041950609280320600080c51800074030005514100c410020301e0a00c0e40341c0400e00eaa0180c001c444a6844800041c800803082182e41d51444c3d005004010300e1902c6d0800a820701c5058803024400c0c400c3c8000c04001080000390320380444d4100e1546e600e48065080000020000c88008009015030303500007902048008800d038001303010304006068101c0324440000d00b1300c8103c032160f2041103045121486846c0030b070002207041d90320f072000600824000314002078910312141e00c45a40300f03c1840f541c00400400180800841d0700c00d90449607044d180c40110000d580b02160300c950004402d1140c0c40c40340e841003192407076001003420301c9203e1010807800b040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466739118 1250 466737868 466737889
    0xd08061c141f0b06090909010902130c030b01210b012003030a0f02120f100513050604050c0a17091524011b02010513080706020a0c0f0803030115022b1205061f020c 72
    0x32f150f0360307180502e150307864050050070b40701c10091070702900400c2c21044015081160640c0064001d55400201d11180d01a500030382d0450340503164454000304d5a008555264400c030303180b00c019802c1010f1000c80234100d000360b0b24030449403a80c03142c496880741c040f007480041c02002c0001c05c492a4100140d940c440005040701c51601c80b03004101c0d45046002d010a490000d08006a480c10404c4490380c0150301030a00700303014025010f141140e8440c0b2a8081c41e002c000c07010640300d0345114080c030041e5140140f00c0013080145d142290f01c11001307140103640c2e600b107c8196a48421380005802d00541c4542e00030140c140101c40c0100d003540c5c55028040c505003460300680d0161744404140e4041c006c07034240071001840042c103003100c024203106c02d16484c1d02061084000270b0004144502e0800d00a004400140001214214403113401c4503140745841045000b003004200001007610f5040c1d040d0040d98071802c0050030700903070a0401d1402d0001140303107140c801c00318000c3c40b0060304555103a01070b00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466740368 1250 466739118 466739149
    0x30f090f0201180e0604090503070c09093509040e0a05010b0a140607060b0a0806040f06290f040f020f0306120d08061c141f0b06090909010902 63
    0x41003a040a84000762120762805454440c1c90340b809030803c25440070001040c0d00000507034001c83c400604e80b801c80c0c40c40c0216200244800754440000c00c0d000702580c4200400780c0254240400e450351804420844c090340700c00300c040c9042000a80e130203042940020000c100c1d0140001500014120100f410543c42d00012140c1da511158170b890107190102c40c0101404c003c1c1c2c80c055030070b030f08100043d909100f0780c64014481c0b40c50700c0707143c8400ea0342e00c0c0503171008045902c21781e40c581c6403600c4d1504d104010488200c45461510501c0030540c844904066078600050a500701503a00400410990001101e4041d50041d20b687c0a11140c3c1c0c07960000d8002c111161000544074200103040003044c90441d61002c00d1544881032001025038012000b540184050703941c1241060021511424503d411102414248800c0d1445003000b20018000580c0c030340e03c0524110001c507800010013a60300106042e54084d009200e1040e82e842c184002c00e8100f40203000000f0650166800b042d86c03001e41c0b5140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466741618 1250 466740368 466740383
    0x12021206090106030c0c0213060518190902030604260a030207060c080702061b09091f0e06030a03030e01020408060103050a0308060405060607080d06081e010e030a0503010312030f09 80
    0x9000d25420800d10403400340140782828850f0b0041c0d80001460b140c0d903807030040d00c240c080300824814085650700500107004041c01c1e450440c00c25100040141e1001d0741c451500d203900707203121101c0c41228459000d0b0182c2c0100034060b00e4403151580620019071060f00031240318140b0600702407103c000010312a003c3d443d100503032500c600382084801c030780d0020940c4c02406010390400175004da0100e00f43d0381c09074001c000001c101f9030001a003080340c010310495a801242850901c00c101c1603940100880040d0b4803400801641ca4143e040e0356102d0507102d583c0c055000600c0c240c0000d0081e009440300200c8000018105075070785c0003044c5804006e80c1b043d030311504484100710a15a0110159905c0003058405001c24140980402d0161140b8000a00509070202e0340a29283c4180c0040000308040002c0315001138810034206241c107014601d00b20fa40d0301c0c124203d440208003000f5500c0c140c0440d12220308681c610384681520245515048040607956104455107640c144900100c41740202c91 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466742868 1250 466741618 466741621
    0x50c1005010f1d040305091201090218150406290c070e0f0c0a050a0e030c04060b040f05010905030d05091212180f0a0303031503020409080c0c12150403120212 70
    0x15610401100c40f404120400040002c000c0841e401c00101d40742e0001c00d440324003a01881529240c01480740c210001d60040701036030031030917181d80860401d0048104403211680841c00d5420042211807520400140c2036550010a440030910280100c01e030f0b0300340c00c0315460243e07182001800d1080e10340101014142d040140b2407545050b00b12654407100c80c1004615021584c0c2d0003408600801101c1000c00419080c0041c4680301800141e107800c1010f042400740380c2d1a0029040c1640140c004d0b080c0328210054000343c42d40c4a10310300811100d0140240040b14200d20048400b0b501039403005422410700303401c2c881e46540c1004442c00c05698111816103407150a401c2040c56040d6180700740c4248000020314881d42d42e0720300030303a0449034941000500000001803610a03480160301c06541316107003144180c10320130351758002c20091061740c05450040c500303041044100620100c1d011101c0e800030910505040e503141c07406410030701a090540e9864101c28100050340d000c0380110003800420f00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466744118 1250 466742868 466742879
    0x4030213020d0c090f0515190e3118050a0615301b06030b090603011808070c0302090703090212060c071127010305070e060d0201050c1005010f 63
    0x108440b440645860500401c0780f42400c1e03000e17804140c0c00350910403c850018415050151030440e6a03a0701e90000340781217404000300240c070742443d00107032900a12545810401c1040e0303100324540c605407076825145070003003030f80b040130b000b006d030040d07a8940d8030350a82c0c816003c240d08010341c0c26484e10a41c80030a181d0b01031074011104c500d10341e1024401c04003141586e00110380203252010718940220224003515000e00b8407101071039442c1c0a020100d000b0200200340941c1c5034004020a43c825981828107440c0c10091600300c903c00c0d01010710f5045a40f545800049010000342607070350040038890a03103038881c0c001840d09803041d107068022130341e1421410300f1801e1060000c1d0002c5002c40c0503020500d040b4100154900c034082009009103040c0030100b1141d640c44400d4400d520309108245200400f00001c4607e8140c00c1c0010f450314441c14000181c40403200300424420300015150507a4100705600545840d0030600c42c28009000d20140d034a9042101e05c02d16000703202c0e960302d140b11b00d450070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466745368 1250 466744118 466744121
    0xd050f0d1d031e09010905041e06140306010e0601020a031808060c0d050a0c1b0218010e011802070c05010f050d1505040c080405061302151306120209150f04030213020d 74
    0x2000c0f90594a4000d100c0801141c0c1c104400100311481600c0110300352590410b210499215820000f041c0c502d0b0a030b01007880b115014845010140507000ca55207070340c9810722081289c00445507a40140e01c00003650000901c1401401c00090347c4101c801d0741302e0740f105007441c1000c000f00e0741d000d089400030074010045d090034018036401c014610020804c02405100044c03081e484841d000b00c10343e102e440407004648424141c045809140c001000055031a1142442050360038440c2a1074511903c4201023141903d100b00e81b8150742c08000da80169143c4401555185441411707501801828810310188034514010000c03408016401e0b10111810441003008881019102000b00015641044001071001031125001030300218054103054003440058224a00120071090700f600c0468003a01301d106030389407181926216201c0181c19030075807140c8000c82c06184101c0da0302c10f80304441809081c0b0500000c00300c1e403e0315542a0b00d4a038503500810b2510a103802c00035180f650005004a0682c990b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466746618 1250 466745368 466745407
    0xf05040f18061e0905180303011d0609070804032d0c05010e0726071805010302100e18060301061d0609010f030b040809010203300601020d050f0d1d03 66
    0x443c19601e5241c0755001040300400540540e1030050380e60310118030303121240424041c0744801c8400b100d5680d0f0f19000030501c007694403401c44001c1001c0c038000c00c60918020f482c0ea40706045030796500303105950320749007124010807001c480041c14034080740011101010701c8074a018001d068403000f03100e2120b8a400d908580100d032100c0da40f43c106110038454020083d41e524007003c12514001d2017940424402800d0108586c0b100901c1241c0d07082a0302070b45200d4100604a03030003180c20341503107540b200301070703600508406000381e2000c08400300d02da4141c9401d4041d03030080000340001071110344400c41c1e250046090758048030f511002404201e8613141c0302d4036007809404600300491003149980e4030060950005440201400000304090426910802c20b0390110304038030611140041814001c20244043d00050b0341d80a0100000962154000039820001501c03943d10240340c0300c03141c601c0e00c11a07007060080100e0305444003a45205840c02d1604c02100791048800395070380f019101d00b1031002c0c128 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466747868 1250 466746618 466746629
    0xb060a090c090b090406051c0c050105160b0702120c030d06120c0b0c03091c03080612032d030a060807140102030a080c070f0b061903120f05040f1806 66
    0x6040005071100d5012611108940c56200b10b00e488240302c0e000074010304219002a40c0103415001c1910425044003814036400d4054400c001c2d82e5502d5800450795440360070116003030a5400481039000801000d54030740d0150903481503400c0b409286400e9006a0700040c03805089500214029070741c00e1051180710001c140c00b211504040d14076603500400c0f810a03200d3b460480c4004259010400800d100301e074404c42c40108084041a100d48640e80400c08100c0e094000888900004600c0c1c249900805517410984008606040d0f00c800187c581810909608031201100000d400c8441d159102642c042c8000c80c134082411820045040e14247c11070744085503280d40440c1c00d09507079030084126031130300807545880203550b0f0b00e00485100d5440350a4000b003020a01c40c0c1c1c01c00c1880107a80d80180245800c440e810600d03c0d081d591880b04081501014061000c0c2851616085010311862480e110050030a142001c1e50307440e801c4a20a0349600052a189200300c4222000c609441604044c08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466749118 1250 466747868 466747871
    0xc0b09010e012102070c08031c0f0c120209030712140d020a21110f0a020a060c0203070902071e0b010602070501090b1611100c0c0803030f1306090c030b060a09 70
    0x450f075012003070b40000801610f06070350f400076046060000b010813503006400d826049913030ba04001d07005455641892001494001c1c50262447c004c41400d0140c20040240f03030361255241d40003011380c0c0b8000e41c48540d24541c18461a100003c492151400c4070000074040c1c0c0701225596a02482d180c2880d0000000b141150485101400000c185036a1400702c1c100400401c0c07034a400d9514241ca0041ca0741407030620a04c5a01c40c402300c204000900700041034801c3e500d011250307690b9a020381d041d0420480096250300310100912041c3c606901400c1164007031400017504200100c088071000204207008e82e103038034205c40184000f40d010405400241028038056000314541124401da80c000c001c02040300a245a00e030f2001e005910f10741c454003d1006000c2c000301070301e18001400780d406041040303c41c1041480005101c5101100b0b0364844c8002c3c198040ba284d84040094a036910841002c503080b560b51020080481c100f021400041c500c6607450aa6500f0312104019410401e54400340302a07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466750368 1250 466749118 466749137
    0x40204110313110a0b030103060c2a0b04170c0d2304060e030705040c02030a020111040303091203050c0613060b090907120c0317091002030a021b0301090c0b09010e01 73
    0x11282000d1142c072040d0400c0004400c00202c00004910f555194015442d41c080070001005000455020000c40415902ea801e59414a4810a4001d4400318040302e000180710610070081102c02d9000399100b8483e9281d10503480c42c072400e000780c64024014902c0c0c298803410420f40216040001028031b10003030b40b0540850805502664028404c5019036000c01c9070180f526010352701c0030459000a400010030600200c00322036002982c903000b036402000150300700b1811980d0049040211005c0e00c0c3c1540c7d07203030000c50421040d01546080c1200481c2001410401e0140007601031100b24040d04462108003c510054240705c400d440d0300d481014405ca08031001d200e0080c8000408008880341005071500b1044c590070321061006403940060001d003100c103502e94030480420010038000070125024500c5840c0350034100d90740d014a90107580564002c01c10700584d40c11180307040c655001c0080002c51844429901da040d0320310640e109144404001c15800c03240d40c4c000c60001c1080c00280f9042085 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466751618 1250 466750368 466750381
    0x7080102040e0a0c020f1b01090506031009110c070b030403030c110c01080601030e060f010303022413080405040207051e2107030509030d0806041406060702191503050402041103 78
    0x1d82c40c00790100041c2540c61858070a40380c000d2111a515104a005a80710100c1200c040d80101440503080e900152000c2d0001c0f50900c0c000041d01c2c00b81e401141d00c88586810058032400802401190100305501480034040340c4c4020800100a4844003901d680c50b0f081c503240180980f40304002c070300184502440740315102d1000103482e1280140903e00f0002644503400168010014400c00e542140110707401c2101500c88800603038103c9109034201c3e0840594080220807208020f03858500300000c070800702d04200030300d500b40f40c0b4041c020761410303107403a58a400180481c1c0c00900f003244d554100c5940c141801252160144001484402505001c10382d42c2c0900503070220304042c03400c111000f050080038180300d101525440d150180c01c80340e01c2405042d001c1c122000480c1c190b4880d030300b001c856502003481c7d481064003541d4060101410403207281d00b044007401e1151400c000b02e008503000012820b01322810403a0540c01501c00103800d0078140144019101f0845800080706002c0003440030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466752868 1250 466751618 466751639
    0x302251703010303052d0a030b130e010b0a06030903050d1a060307022a1c0f0f0507080f0106150804050f010c0e01020111040501091802040306020406030b12010606121d07170708010204 81
    0x70580c0082c0380c0041c0f00201c0f80c0008000c03c8030320345450040bd2400340b4004da0b00d48158410b104001085400c81d9075035a40f9441241505d07a42e0500400003082403004090099164103c207030511b4404498191404141b40031414941088070300c1001a40800154005088042101483c200c51a08000c84e14002d28001c105448542441c2c00310000c0804000c1040c0302d070282020041c99400303806c1400540c403a0410503a1422503008120392401400c0e070800c00c5c0d000501c0340c241210320720540c0c800d00c104504030035560140b00901c1a0390f103000320a100c000b0703001d0078400d50110400545443c0d00340440308000a0842d080700040c050030903420042403040760b8000030924104c81d1103007041c0ac07184443c0007501e0040c2c022603100030032460000c9801709601c1c0d0582c0005401500c1038408010840001407a58240c0310140f05202c0416011000c90001030060341124001000300b0200c4454040000e4101c4c0c60551154080c44059600403260f440c0040141301080c01404000001d50410b4200140da09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466754118 1250 466752868 466752877
    0x90e070807090b0d1107060209031516120f05070206090c06040e0609040f14060f0c030f061912080c0706110c1903150504020f010302251703010303052d 67
    0x40852004c00c0000f850000d9030003c4544141c0641446e45441c1c662400324003030342000000520901403000d20185003001c0303007092031045000001000601e07450b154151010340c942400411619241c401c50b4030180356030f00070300380070f4001540200306c90300c0c1150180c1c2c10141c45421051003502c08100400c5816052142c0680206040340d4030181ca031628034146000102c00c5d00000e10200f07120301030700c1032403802194040c802e405141c50000075580c1d00c502c0815a00c409c507510034544503d030b40400c0180c18041c5105001e201080e58186190b078441c2e40480b907070207140c0c8044568940004003c99042020f00209000302a10700b01448182400441b058031480b038099081d008444264092428008a107008801160040d84900b100c10a00a41c0009041c080382c043c2e0041481e1800c00d5100d500c01c1c0300715681a40b140c01285251001b482c0402c0c4044003007402910400c42c00c41d001c0e1412a4020000c41c000c5201e80c6500c0d60700d00241e242030190a180c852500c031070b0b1a844c034030500c803a400d640448 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466755368 1250 466754118 466754129
    0x23090913061d06011a19020d080a020906030f0403030f060f0302040b121b1302030901020a0908071d06040209100203031515041707080f07050f04110f03100b0a090e07080709 76
    0x212160308850514a00340c6c050002030306800d0038040b516810403034000c140c0c1000b004003555070088959580c900c0354140d00c2200059900030004000049440c0800101c0320341052081c40d011841c1065469000160386494000d000003001c51401001180340522801512884c03e880b444481d01902c15036075241d410325014005161090038213030080d696218200c1c8200148907804644a04080005a0007500900c000748081100141d02040001e400511030080792206040040d200756951b000c200b0240c1c001e0031064100d502440303c0c1d05580daa20098110440c403d60040d40c482c9003040c4501e0502d1020703102c02c0d000387d070305e020340e440c40c808034a00316015a2807241c2d501400088101d00c0320f02c0d0030060762110285003d801c0250882c090041076080031510b086075566a004081001c0004541c42407070810000e40040200a101c403007031030059640003800f04d140111056550b031001c00c10764400c5154000042c03d143c0c00340040b007400c516554000b1040d25050039076141918001c1c101c1613083c00b44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466756618 1250 466755368 466755389
    0x303040f06020d05070c02031912050d02070c0b090a24030207050a0204050f09011a1c0206041d100803071101050306030a05071d010e0723090913061d0601 68
    0x31032080c000c00d40c04840e240780807580200420b143c0404000d104442495040348240035281400c00014006003840002580140b0700c0084114203841c02d81d81130f400700300e8241205800384001d10101c0c0445110f1401810310391030160f0303140b018600b040088880c03500311403900b58141c42c00035240c04482500b5292041701c1c1c200160340343c500d07042040c034002220000940c41810603041155140c1c180d48081d005240d2840203110b595a0718003a0384241200d06040b50300038112850300c1640300c011240e0b0492550018001502c0d1075190500d03d1002c41e00f00c03072554018001c0340140302c82031140b011010014580f041c041d41c108127243e0b07034940a5020065034241003003800710108001c4e503420701454030b00b164010115200305988450502c018640c41164103400d0950000010b81103117500e10f413070b1045129640d494240c40c1c40b00b01c18104059401ea03400354200e81807020348403079210070808900607401c0c01d07082c0c41070b01c00c949030a03001e94000070020f0040044190009010150000c0c0c00d84c15604803005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466757868 1250 466756618 466756643
    0xd090e0403030b01140313050c060703020c0609041104060f0e060301031e1506030312060e0f3709020f060906040909050a051204090b0303040b03040602180429040509030304 76
    0x4076480d1080e0240e4070f2038000d0006c00c2c071425010360084016070501c110142d654240d150700c00c010032070141403000707005a0000030041c8000e15050b00140228030340203000066240b501c181510f0aa08250400d00215101740040d5004a800065240901c0011070305140f075581940e6030300342002e88150045600401d45034000c0d00304410410702103141d25070041e04000f45a6070b4107009140d070f540c000e0405103003403400700082030400b4108070031132086614202407415031321075030300071800100c80101c40c4142a4200c4001804000c1e95040074020600380341d804541c0d151b02c0e0041101c81c407203103c440303441441c4c00c000000d2651240c6060324100e6807070100006915055081a50030902e000e880202a4014180154210b030f4184010380300b80d9410060801c0050980e805240c1d0b030388124040c08080c0270301803001070001261500100102940303019107203400c0003400d0108007070781d4075090031440e070440d510b646004000c480c40c4609038a813030403a8140080d040810f0084c1c1c8030711000c2d1010700280742012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466759118 1250 466757868 466757891
    0x18130f0b041e11091305030d15050d020603070c0503090901170f070608150103150f1701020c031b0f1617060c0703030507170a02030109060618090b0a08030705010209030d090e040303 80
    0x7194a1171164224054a95410380c50410000070180c0e004000d8946504074808115824204240b200b0302d540a400340d0b1444d00c6011090300c040ccc45411080b1011f10040024400355122580050f00810304141c90341070441d0700a070344500b802d07003100b0023400c0d03903200250402c80a64405503541c0c001714043c0805c40e0024807600102d0142400011010f00700c9000c22001a40c002400350540171a0004170005010440744a070450070f03489002c056100903030081c080280c0c5001c2405403080451040400c503181c0301d03030308892903081c299207849413842c0d1214a40d040207034140d00400604409101c00c0a881c00f4030749013142542138014020702030b08055880c0c00080509024401a140d459103001c0300c04454580701103400c0195009001700b400d00f40c144072001403200e004506044040010300b10345c85581e424500c00720001c062004150790b00044214000a1607107042c8001e04040d8020300000da03032030314a4028185040704e0070000c6820000e142d00100318090b0898056600254146404070318000f094 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466760368 1250 466759118 466759141
    0x11107030b010803070302300d02070b1504050a0c080c0f13030516051e04051b0a02030c0610030818030c122a18130f0b041e1109 57
    0x150402400e0300c20794000031800f0980003001d800110300c25400c481782562104d4561242004041c000c7c402000c45031a880d4000300307180c4c0a00640121000d00604092842e100d401c4140019034034040d8440a403000360645003010b00446600840070041408070340b02c03440c8000d08594008080d00100d00c0f0206141c0042c0c06d890b0111102c132120801c40c580b041e80c6a0074070b1130b1240080007140d040c00d4a4035000190500b07082c0251540070078884441880094400e003804082c0c00d00400900c03c51000711070b5141c1600484c1d024200841c40c941c0150b440f078294182072481e000001d0310100030400d41840400000b166201255888544459488000061200031903d4013548010050b0b1010121000c240442e50018071140a16160704c1508040c03480e244040600c01c3e05800e209400c9a845017040d06500010840c1c2a08400c0e034103954030b00144e10351240783d040c0e08a810211102c1c05d0007000d100c1485503022421000212302d0340b05401d01001580c80c0784d040030300a11003d00850f1110001090801034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466761618 1250 466760368 466760383
    0x906030f010903170703060605030406200a0e15190c05010605130903030506241c050108070807140102071a091503071b08040902030613020a0302191d0111 68
    0x480001e00501c0300d1840c01600d03e05a0444894134110b8000c00280440d2003400f42c1011680c0b2900c1c1c403803a44c1c45a407100d60180030440c4000149000460504050020302c50044c11012451b035900411070b1601001c1204074105415010131100d4144120301091444000307a48444540d404c080303403002d40e540703480d60240405078030140d80041246981c005400303c0307400040b000c0d44a50750410031551000100505903283c2c0c00c04041325692916540d622840860003020000d4440c01c1103140074203041d80e00802d42c1c1c1c2c02d822110b17031394115803c03c01c40c49001300032403c0980000a01c3c40100a40400000e66030805881001c0e0328102a02080c8400c0c0b03617440032140b5500000d400c1d91002e80f410f00c4140903130750047e1020740c000b59500c0325241c0c100003004900c54400d940300d00150b2505140c01616000707500301800084e40314102d203405800358815440200401d59140e1009619206d404140d1201000e407034000c0401d04c40c6801690f210203401c0108005900c0b002d0a2411f0300d54001b103001442c0404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466762868 1250 466761618 466761643
    0xc0319090605071e080c1b0a05010e160b09060307032304031803020904121b0510060515071401110c1b0a080715020109080d0207032a02090603 63
    0x5040c040300c0500c1010303004188a42415118103110600880f0100e02d44942d6200b2800018111404103510042e031200801040720440714030600c1840004103603081000110302102c45039500c2061041c501c000340316440c10302d070000c140007041074540365454074184030350000148075800000028500310700035130242c40c0100031248a64080c90f000c050641c1c4150081d9820f030041354208840401441c120720000782540d501810b540c500340c40340e90300c90680c4004000ba50084c4150003070a000d0408403005d5440c10b4600810084c9840120084c0280459400750800390180c1d08031010301e00010000c00444202540c441d60038480422140c09060060510801c00c040001c000039582c06001c00010300768015100b5002d2000c014401c6074200722a00718103200388409038100b9002044500c6240d0001340317aa141750300001c0744a81c29036030b6880103039000000b10240154046590400e040d400380032500c15081c6a02010213540d04104524149001c5400092055010100142c0c0548003445054100c51 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466764118 1250 466762868 466762871
    0x603070509061908090f03030714090d050607080f22020618090a0b03010b03030c07151206030602040611010b130c090302030307050109021306030f080702210d020120030c0319 77
    0x843c08000422400b01555168038510507840103c448020120840e401043c0d2511040e00084010465074410780100610f168030034400c0d1030041c041503051001d64456030040d5505011880c0c508100c006420001d00383e41f00c02525801c00c5c2c0e0031402d043c9501c092681d01160382c42e484070351342d43c0d8408090307588084641c1c10065550a1000d01a40c0ba00003241d0303124110001c2c8103c450705c40a00d9034034000e030304100e2003d5210840c10088450f0450007082981507a14000d41403080c181d4420040d20904d0b4002c9400b42d50000b8100402640304601c0c224010b03680740244403c130103940002d15440000b000c14103460b90f0340c0e0500d85841d400f03800310303030010350b03001e001e5130f407104441d040890080040f4001070380100380e100c81c0910b0101041c0b2480303044c3c9900818110310307800c207611400d0207900018812a08a154214101010b80101200c0305010700c0e40313401400420f00000d4020f00b542c0c0000f5105c5000d9030502103d080c403000340010faa03400000e003007020f52a0341d00e00071440d81021b840440310302c450303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466765368 1250 466764118 466764157
    0x306060e040e010f0c0f030b01082413090f0b090c0a170a05070e0106081806070309031101180c080d0203040b07061104030f0614010302031e0c12070302091005060307050906 76
    0x454114106c4440d281158504105a81c0308400541c4c07180d40c100d480c1805400d20083d00d681824250280e4a07080c0005401c04244490501d403030401c0b0341080c00103403006003c0903840410408841031103540108024081c3c580704980324042519160704e400f412028106914290541c52410088451125003000031508196529610011184020701910000418081c009034800203803080780c00c5400e803000c0c014561769607060310803402403050a408401700001d00e50700801c8031900b406519000d88007171501110030b05c6c01d440c0c20890b0400c20343c000b06060f040403002900d00354010054804032112243d015070b42e1208c9281280091244501103441e0030f40108005c07060003401311040810310711400041121802c050341012245500b40300c0294503034055000451100b01d0050313540c0c1d50420741d10464a02c25144030010b0511194030710303a82e07404ea020850810640c42e01103081d90300180c0c07140880071000e04040120300d55100c010020402d010303000489042e00d0f00c40c0c004640a2503850181c58100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466766618 1250 466765368 466765391
    0x307030504080f0703021f1704050d020d08090309040908160507080118020f041a0306131704050f190803030a1e1104050f061e0310060306060e040e010f 67
    0xc03904207014040c082c0c443c48030600f500c4280040d0001c26641c0040405110130f003901001c0884001c0c40044000300081c445400d2141d0f118800040d00492082002c2c11039401c140c0d40013454928144111030400080506120500350701204864074054183c0d8040348010190a18008500c558002c1d5503842440c07011803024407002144030030940740c12800902c0391340d604194051039005051006540070101d541c5400807450194000ba00303090034408952058511080041d08140040312074220103580c4030032100c02c000e00c4a2003001c0003485000d10b00d007007909240200b54104c0c0c0c0f000ca018013400020050001080100d441040108035440480b99a4540f002c0080c0140034000d44806a0f520266480001c0840a0044900c00011210941c1c1402e10305403c101c103445400c00c4a03500200100701802004800704001200c40c03600d510031607600d090598042032003108513030103242018904181413100700e50000b00094818001c44012070f0713003600c41c2123560040076286d400e105c01910340380c5031086 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466767868 1250 466766618 466766627
    0x120708040305060c040e4201030b04060b1602211c08090d050f040e0f0403080c18060306060d0507090510020c090402120c0d080d0b0402160209090f030703 68
    0x603648518140c509613101d00404110a01a0340105040315075903030002510840e68a10200e071aa0080040700c01a900082e50850170602410072041c480380750800307032400c070350b003501441000503020f440401141e86003a03402903103030040c010702428445003017901c10103550310b88000717200300030f1011281c590214424101c19a154040701788030003e40d003240d84410205005102c0248100403c03c090000d00380da040c1e048400354407c00c91030400794800e200201d00c115000c0c0c2c00c1c911643c1980c01104c440d092a06000d410b80788010940008880204000344006900c02d401c04c014841c20744946840e42c8682000030114014520f41600c554034100c20000d405520010300c00884209480103d06818081c000720784800014420310b0304680088040350050407c04405030195480d1390607110401d02280c00640c420213903042c2900c6c1c039040419904945032507881844000c0300304581c01c61410b14a008500c406d00d1b00030b034019200b0744a260001d13550740424020001c070042c0d24402e80380d4030003082c500a0f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466769118 1250 466767868 466767877
    0x6030c0d0c08060102100c020f010f05090c06070f0807060609020720090709030b0c07081914070c050405100e01270603020105040b1c050112050d020c011d03120708 72
    0x90003810040144541c5000c0e07119203025000c1070b809060141c1c801e0f032102001c3c000e41440f4a00314410b60810118804013803040a8940103100c0000c0303100e080c40c500d00c43c608030411103e10311500040014600191502d802840d9481d1f001c0019500c851160400751700500c142c1d4004c1051354000520001040026114400030110341c00782c001ca0101c03400306014454008503100c1011030500002400840d065400d00c940c4850f03c1e04c0c0c402d00d014980e41c2c030700e50300c0e03000203004980e80e41e03541c489000c12070f030000303440c0303684640206003a800e04002d40c448a0002c1d5181c40f9950096035103170f0120340c001a00700300f103401500145802400300e5135034040c1c0881140020811417002e4018202915002d04580914011203030165a014201401d21903034040a40c0002c40070401c484101807007070881c142c28010b541c020b2940e422040080b0829081c51405d007002d01404400715007014071168156a04000c4501d880e40c08550b500e1068016000840d240c144803140c00c0a103041c0104a03042005241002403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466770368 1250 466769118 466769137
    0x3030703080f100302030d1409100908150f07050304020301141f050a0806012c130327090c09030c2c040f110a12050115052211040506030c 61
    0x1803180e583c46a224100f50412404002d525030014100c448150780302c2c0400c050b11a242c090298989070100f0b0009142c0084800c8000102e805a501002000418040716412030080325031005246402407660202080c02003403003042c04004408a001d41d10254440304400005984042c0903041c040e01000622100366515181200c600c0c01c080391070300b4065480c804403600c41c4000c0000e64200303024072004800810800c590707034031428405085264807100e942c2c000c814600704045210311034140100866425600c0190071243c0400042c0400c0070345440720100c03200642c0c00900b12015071001c071110859944054a49080d003003010506011201d24071031800c0003082d58080c5041c07656030b142450320b81102d001d4880c05403541001301058410800144580b1b0062080c00c00030303118402c1d100d181140c18825a0207a55510090011401c2c120b001d00240c0400c40e04a0041c078862040762154009144040d02c3c0071341c8607040f0221016030202a10050240180b80644a00d0300b031103014a140c2240508 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466771618 1250 466770368 466770391
    0x30605030105070f170c090324370608030f040513090b04060e15150925030207082506060501090b030c1308030a0302040509090c06041e050303070308 66
    0x40f0700214000c0344103034110507060700c820302040b03900700307203800c485500401e080500402088030316650343d018080481a40490041d000340c881001c404058203500003002c51101003554030407250694030b070201e0508115103150030b080400c040c150b0002c000e0b16040e40f01034a41d01c40855051440400d20014000f40c0e03d0944405009101e40382440f0b040d18181500074000040d010081400b2550f01d4003d002c00c1d64190049440e0034440341104601403804890100c0d90506103104e14070907140003001070350030107040503565070500c00e20700180110003440106038091541c001400c5081100040503210240344101203401140e040403030204909041d964100c0d181890144081055070151200e00c05584048040500f0f503030f102c1c2c00b1100306070302407030710481180f00d802c8001440c024100010041b03103426580c0540c5443c50402484510107000e07114800795040b0b141d05280944814046d101101c0700b003100240e2030459034811410502168001c5501400001111400c0c1a00310001038003c90f80d5062 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466772868 1250 466771618 466771621
    0x108150915010618080d0f1706060a1214040b01030203120f041404090c090e010e0c1e19030506040b070302130501031113090e070b0703020703170c010c030605030105 73
    0x40d8561140e0101c0c1c0304415071040c0400520426100b95070454803445081c80c1410302c2c6407205002c5203824110003000000034008990046010b50001c181c00002070b40c0032031302c0f406007041c20004600d4066041c11a040221110b200446503260707800c031081c006010510340d2440c0c02c05050880e00444c2c00d0109034000c2c414080009021007082d000c994030002000c2d0140d04050615115050400328411226400780c2c440c11500040340c041d030302d5030004106080000420044131402a42034422111400050790014901500d05846a03c00d1103444040c50b80322403003034040400082c46d40f11000035001c06a00381c0c5032020040010000715a030085000360030501d2140c1d620203040382640304901c0f424503500070200b0204100d5009401c204a0f200311001d400b41419584442c0c044040700ca84d02640f8501e0b1100440d0700815403e009610181c07a2102c6840e1408140d0b8130065603503503039440014001d10201310f410b841c89041c142030300c4a8981e03401c02400384021014000700a00001d0184520039441d007070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466774118 1250 466772868 466772881
    0x405061303140306060408011805070501170c2d030709090605030a120207210b010b120f0403030f0c030e0c010809071a0d06061205060406032d0803010815 68
    0x9500c00c016940c140c1d214401010b00250408407608003900164105606000102e500502030003a442c032001d070241ca40107141e040341800340c07038144254401d038107000f521810f000c03000044a41041e480300000841c1a0f4440654610001e00c521003103000500715100030704003411090100095008000564500001da600e4401000c00c0354101d10605031f050b408883c07078400151080c00d0091540025005980c0243e0380e401c142c00401041001e42102a589120160204030130140510b0140c103070170750b0301401d0401a031444a9815005412005019900e2002804161203504090900f001d0380005011a916070480074014080b25881c2d505176025200c0d100745154030421015103d070042c00c0040400510300041090388100c21a0b4070064107070708010f003510b000410301524000b441d882e0740c1e02c0850000d1980a0040b00e030090101480b49082090400119541201c0c12010880c0481405040b0b412490f16141e400341c0090014404400070000007500c030300110b00302055031180a0046507d640b4003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466775368 1250 466774118 466774141
    0x8030a0f110a030f0b0a0f080f060907060507050a0203030d1a101b060605270c03090a0b090a0b0108060a0b06070807330b1215040210120f0203040506 66
    0x11028810400b48010349070306109411081c07402031044800104054250081206554160044c1c900d40c42e002c50304201d00c0004100c90001021404041c01c550306101019986505030f078070034a020001c01080c8402406028404d80707060507401011295107202c10203040024003410305410106200d5681c41c600d150903c034014000800c41a41c822940b03600802c105031465584540550b00203994841c0030809403500b8641c8860f5005100004030f4003100d404682030b40080081c440c19140000b4401d0002060303001801075911540324030791201701c0e5920721a552400e1044a0041d080007005000050304035400700c0c40324040e140c5107205000c01010b6a051115921400310300030180c4400300054400f081550901c00c1512803000c0c8141c0f4401c40c8040c40111090020007150300a5586007012841803070300351908042559540080c040c000040e141044555000800c00390107801c9440b0007002007885000a8103040201c0c0c0400c00200015458140080d002114100c4040c4102c3d07000c0740d002d0005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466776618 1250 466775368 466775381
    0x1a0a08030a120213050a030503190c030503040201051c0f09150c0e0d050718020307020606150a140c030c01060503060708190e15090d120516031d03040308030a0f 71
    0xa6110704405034200b009407802035008a68204a0291240d0045003d60702c0408200c000c40c0110700940d158075502c0d101801c0501c1703c000748414441c00c041000c3c00240c2100560f41e1054090904940324902030814240080c0050511101d1510340340c1200144c2c035242e40a03110701030186040360f2000180d25401401c079a481085a008107541620764a814503090182041d018896415540c0b00c6c0d0303480c0320128030f907003142422030901c540110030004000c1d410080c841d8018002c07140303490b403814000414400c521440e0401ea00b042004800380511400c60002c650410500c1c2084943e181641d1040600828050080303501c20701646022907107085c86001510301441e500d00030544c4042400100e1f000901c1c140c80262107a01820488022044055941034443d051306805445450040c000c014000b11b5080c03544c940700c81c038103828440207020f0050b501c4c0f01e91116007000100007811140518462a80d014400c595200000b40441004020406180110300d00c0030b00344003914654030160300746d816 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466777868 1250 466776618 466776637
    0x30702071502030945060a060f030504020a150c060b0406030317090a0609060e101a0f3006130206160812010f1e050a060c0302030408011a0a0803 64
    0x300341300700b0b07541d813802c5401c0200c00034240100503c48040c0002d40c6007040040b508200c0840ca040000849200f01c1e45c195a0340000200c6d8400030803030816074090122741c20380603070404140e55000007a0440d00c0d0507481c003014001c40003041c2400020786900038100903c0100407920542000c0908403241040d005200a90340c0c541c44490362803090032a00d002802c40204049241e120342d01c40440800c1d0980304207a0b48a005003408101444178458007807401071450041c03650603107440350b40c608402000c940781400d043c080b03070681042040c44001441000a800e03c1200f442003140681980441100801d2881134020b000da801d541e80d8103c41e03220004281c20040d412900421100b02c00400f5051503c060030b01c03484006040c02035001c108102c1120076000381c00d055603100070503c8142080103070390000300280c00860041c1404c1c20302042d030005c0329105031002e02c0303031464683c42014002d00c15540902040c0c8000c1160294003564007840c019089501d5000700107030100850040404402c41c0c12000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466779118 1250 466777868 466777873
    0x8011b0c0807031103130b07060507020604020d020f06040915030c08030c1b0409051f0501120f1403070213140604050103110d0318030302070e10030203150c120c030702071502 77
    0xd9034901303440c0c1900314001d03e02d55000400c500c04601300c40341d80030400360042140a80d1100c04515103c0c04a46001d0148403d540c003c0d0104001a500d44019249095064448510f84000100811240e0181c2e07080741e246103060668407010f14a11900c4641220700849490729100d030b40b100700640f41d22410100e96144d41000109550055241003295020714016000094042c0c1d561a00350070001044028445907042c54800580500d06001d8280501110000340030041000d42d00c80e00b08180c81d20004101440145e9010a07840e03080c802e450460b50090040c5a0040380804110020070886d0800d45070302c00c4003400b043c224181031084a040e603610440b00311041442800b0080c03e90044076086040210946198401141001003070000710300c80d030001d1409a040c10407803641610010001002083e0300c04003080517aa0009542d01540d044520455550b120301d400414588034060100c10092014001d224a010355500114440e5405a0036201c0b8580c44644080e03590b902140e200c0c0041c4e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466780368 1250 466779118 466779127
    0x90204050105191b05030705070501050910030504020d0b0412080a0b0604050103090f170c1e19080d1e0e070e01262b02011107030c05010e060108011b0c08 68
    0x602d142140143d5420081c20400308062000f00c0041c10590440c00496454101180702d0b001c0180801400018040900300103060801e410003091519104c0c1c0b846504050719003010505540350142c2c1d05161642040d64002e0350720f410b04000740c00d1100c810040340042d0340300d800101e8035246445640e0b0085001030510740317094500001100642a0444195507400b9800c3c81c050000752060010100e4544142085842d404d103005420700f007072902015851004240d05802d42e4824000c00d02900e00351628800c90307001000c9061080c1140203803c5400e205515011245041074003100310104210990101031060610603040c1540b113101e140326004d224034400307006110500c1b10b1340e0915100c0c8140304244050360b00000569242400e4410f4101c100301c000005010524240785440c0c50501060009009021460800c51400d100c1d08001904000d1a07000d014104502900314071020b00d2100d00f1902c10796100c020042c028490010108418504d0f1240c10380e003140250000c09080e81c00c0007507107051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466781618 1250 466780368 466780387
    0x60909020f12040b100803090d06020a05040b12010e01060e0f010f0c0503031008070b03040c09020f0d02030f070318031b031701060e0102060a0e0309040f020405040f02030a06090204050105 83
    0xc1e4101d80c0301100c0c41a01802094000700c00601c6041c4118015007400c2a2803d045c1c20810500303400b9008050150410422031381e464417802024048941e0195005a4503285030000721307001e01460b0400040f1510000380903056042081c4584d058440a0b0313241d4126907030300d14080e15809100c000280d0407100c00981c40c441907000f4024103a01c5801c2e81000443d120700ca543d04d600719401281c2d101e119002d03c0005000080f01003152101501542d1a0381d861800d180d100c242d14411184918083d140c2c001501c980e82010039815240c0c55051043e040d5160700704aa10108081411103071003000070b103411078070a07a440000c009150441d40603142c0350700003440c6e044039080d03100c1071403400e909202010f101060a03d40154506008003620768270b040703a042901000905080e070141c40003421906082c101c1c0d102c00800f00407118024412100013641c03603000034024001c0e0165900c0285c0c000e1030140c0003000c000302c5070020351184245110070040c0c20b458401c00341c00c0703018502030940055414801c0420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466782868 1250 466781618 466781621
    0x903020d1e0807180905090601050301020c03180307030209010b0d05160c0602031503030301030b010314073501150f08060c03061309021507050d0201110306010f09080f010222060909 80
    0x300032a20345004c1c001400380310320100d082c10640d4884a100c0381d590003080314002041c4101405800200c00961905586c10710603a5240079403009003940c455a105071417000c0e074041081200442e8080e28800f020740e51a2002841c1b0b030000c48603030b900306080200040300b408540c48008201100340e1111103c15000d5103500c0007d41008002c00b11181088800090942e010030140d8021481500640d61030b40c107514002e00030400a85806005030b008240501690f51100c614401c8440250801e440410030040e00c407110180c01e1181041c1c5511b805400e1415500d1000c0040944035076080420106a91301800d5554400c200c3e084042c03903100703001080031071524016482c400c10014101050500158000411408007583e000019400002d00e1104008041c070003c000550303640001c0014942d0000602da20f071000804c5641000250442c3c0f44c403040c0146031400141c10307050300300e0b94142c00f00702d2001c0c003d5104070400b403129000c1f0300c150042016120189402c1e20541d41c3c0c0c00070312a00e4551100c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466784118 1250 466782868 466782871
    0x11b0e0f0307090f0902030715090e0f19090b01030308010f0501140a0809030715020702090a0912030f02071703040b090303160309031b0c031704081b0109180903020d1e08 75
    0x4a9242c0c05c4100160360200810006040c2d0480f101484000e81003020309240155880348002c421070f8800c002c44600340405450303111020485d90048013a241108400500c4019401804064018008414598041ca4182c1607a01d2501804a0291a200107440c00510b000311031004003010000c581181e407007400c1c004e40041c0d01000b280c1c00e0002c41d646800350440c101c02203020700d41d4081541d806502d4841092900071490042c10408207207180c4811494024881800d018036072200140d00e08140ba540c1101d841541050803040344020340700c0800f50550050303c0c21348002c5c2102002c03034000e590200071280182d6015180c1d002c8441d0401c41174010340310b072074019001d03c550641e60905850314081d0340a0cc1c0307445402851025811031801880c690341506002d440e41c80280400d00c690180000c003184101404680d45c03100000c08401210004295000b401600245240e480550903054014a80c5544680c09551040c52881d41c1101c190100440600300d28206803d070040c010300511485 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466785368 1250 466784118 466784141
    0x10021303170c0a0308060913030e0d0c1a120c04050907080910020a030506031e12070c0f060c1e0804031212020c0f1204050d080c0f011b0e0f030709 65
    0x7541030140e1100b00c14100041a02c05501084800041140314a0902d028583c02940450b042c032803544a910028135108a1805a03401040769030140c8080c07210210010005000001c00460641c14401e220400c942080c00f04007000c0d4108004540810410741c1a42e043e640c01610007521030303036011000c0b40e0b503080c0908041d04074000d43c000c0808151480c002419402a180c801080c0b40c1400400e1520b02002d0400e000294001440e9680c4030710340c0400d0760181d100b00e613511035458651900340761190700e215600000c030740c0e950f0001c000740581c2c116004201150040b01204903121b00326404580076882d500c0e008080440400007800041c00007a00f90049030260700e040000189440801c9040380c0c04000ca0030b13078590100e05071200b4554100701440c0d52000c1d40c1001428145060040340d50040b00d44001400c0780380c040340c07a805d130394410044580c03410005030003800701c9042c0401c0e80fa03002900c445d100000550402c507003401070508a0030806500301c040c0003002c2d8146004030b00402000074202070f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466786618 1250 466785368 466785413
    0x40503070210141303142a1807020a0b0a110301060c03050705122a070501030903120507080103020a060f02061914090102030901061e090902010c06020c0a030210021303 74
    0x59a120100761405040044c5035034000c04105819802c140b0741d01c5080d403805201070343c013543c0e11411040281044000100d406604140c6024403a0000b03441c5020740c103a541d1403e0075010400030b00325030010b000c00b0014040d8902d400c00307803188890340050f15001e104070074180800700010070240f032242c09002078645c000d150050034815aa035449081480c01c1107420345413032000c60301c40380744110031464502004115089440d940301035540e045c2c40761090b124090505552b44200406c2c180039420340c0a010b444450b042085240104000c0c0c0300c81c9003800203a00a185203040403078610f0107000211001801754009101d15036a9116060403035100001d0000415100c465490703000600d02c400038000c8410a00140c0c891418130541c60840d0041da100b02820300e420003d145903019020105401e8400f5940d02040d00b83c2c00d400182d400400074003000b418a803001078104402403001c2031011015100c1ea0070b4a0600700d4048010080c3d010304254003d590b100d2074420800201d20703200b202c20501c42000c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466787868 1250 466786618 466786637
    0x111b0d050412061e0b09071106010b03040204090b010609031502030103320f060f0906071e20030d0e01050c0405061c020a0207060305010e0103030c14120f090117040503070210 77
    0x11301115913071040d44000b40036030720342c0c1c40c4510034a0201c10042e8003008a1800d0b0003006808420f6640c1e0314410310480001200000120b000c4d902e03150011040305821002060155a40d00002800c48241d80720580c0c030403005041071410741b6824000c6a0403a43c01c805110700003030359031030061100d240c1c152840401d0b5804140c003554074141032040503204d41043c00500b0f65403030715146044402500800002d0a03802c00b808004a446d00151b5107000a0a007903800c006d20303010180181d800000b40c001c000360841c807000003080d901304000300070101c10038181024013044480012075420703a1804d4400070083d1320b0500c010310403070421401410301e140c0500a0049000300c400d1505049a100681e20401a0071184090000301d405000b110700420000405240c02d62540e01c004082c03119460004103480105208101c1c074140400101c0d6052452010f40c0b640c4103e200c1340705d800383d0f008040710781c0404d82c0c8203210b40f6440f9580003c288510f401101031860419280d003004100300c00a140201800303484223 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466789118 1250 466787868 466787891
    0x16110c1003150801110301211707061506140705150f010f06020a030804231509070e01210221010209090a0c0f0f02030c01111b0d05041206 61
    0x8031500244421501c0c0028045004a403420018039140c20804881c2e0511584a00c842d4034a01144e04440c1c09881c0c0f9060550002071441020700f0556002d0001103c900e1500b0005c1d030032000404815108110070060300215511440c0a0f45e507070b12a4034003042da8411000c0d4501c1e1000b0042801610443c00d550403108072a4409650f8038044e51400f4130001800010301c030300d04004080002078074160000380074032002580d0090400800030300c0208032506181c0118400c00d0028442d00b41022400c1c1030312413110f003a0800da048071804540081c0d29118001002644035220320310241a100f02c00f4642206410280320303c842400e40c2c01c0200e801542440384400790311710b1001c0d58005441620009a502e9101c00100100d011000c0e0840c0d03180c0740380c0785c1104440e980001c40110888003a081c4031900c1c042a60080c1d00f5070103a0000211a9400d14034141a0421a400100f5501c200e1103d40a45804200002030b990351810f10003070040340c0200020f102120001400d40115031003640041041c01014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466790368 1250 466789118 466789129
    0x40603050f060103060c091505070204020409020d1b14121b0d0603060606140304020f01210f05010f0b04170316030e010e09101701180b18030316110c 66
    0x5000c81c81a0002c1c40140304000090191844001c060700d0302000380e81c01d02040f440c413070441c0d0b4080c00c14004001441c0b0110349441e0143c500500181b41c04644038045c0300001d40160600e40d2243c2540544400c807004103078001d45030f06c0028a000844507060208007158144c10640240581c3d8104110034007048402e1620310003060701181c0c04401046003451880c04a080e500b0b0750b00001e00340a40c400c212650a4483e07415a50300035011a110500200c102c6d0040e10f540c2e64094509011031800b43e050101000f49410040b188203083d072042100b43e81e19040b00306a03011f80d000300500c4400400c020072502c09140e030015810780f40d038003c0c1d07460415903c0b0766a0101401e48002c80c0031a6003004a45655070300848524280a4103840c09542c0d407904904108d1801c0b1f05004207001d1204010010701500400d41c0300341c07142103010111204010700760500c5503201c0f508840d4070400b62401d06002d1b40400011041e64052110011801840e0031060400d503004059401c206890b4440c40c1015010b40d6030b40f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466791618 1250 466790368 466790383
    0x2d09100302030105250509010e130902131a09040201020307020910050a06120c030603080405040e01060f08070e01080a05280609060f06061404062706090e070e0f090604060305 77
    0x6603c404c0344405030381058206104034140c00c0c1418401b0a00c40d2002c40c1e6000301c3d001e04040700c112000041c1ca290742c500c000c01400c980704040d41049444d6200103607000160300c58146100346050340001c4200020410207251400c66000b40181c20900003138005081000800c0d401040a10309e081e40c0e1615007000c14000c5250f0760084001441c0c54a106d004454207100c5c1400c00c00c1c01d89400d11059045490b89900c42c491441624001d50392800b10303d501e01000c5d40000094030000e80d0041070b45a54045066482102d40a40c10301408400000100da81c000a0507004031035000029000c200241c0c81000c918145151b13400c0071515a1a22400004241d880780c40c849520031800054160300003500c1c50101c42442c0c20400a1008490600708000840c1054030100c62482ca085903012207001c0f4441d01000d40981c445c401024848008905103410400e100141c1c0c03041c0724442c1c1555a9000c040710303643c58000845030000d00c504038482c0740741045008503911200c00341010510b40d81e260f5445151150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466792868 1250 466791618 466791631
    0x11240603100507020309040e0c090414121602030105090a030801050402030606041203020d11031c0510051305010305010f0b1e01051303060902090703090803220b0405010b2d09100302030105 83
    0xc6240c4c1c00e00d1f0520070740c04003001010061202081c3c074400316449110207840034100c1070b400302c908043e212040140c80c000d54482501103864640088404603103000c071b110101c0c402c2d420b010014000b6040007645d0301c04070390156150070243c2d1074202404000d50000e480c0d1604064108000709081803200d0a2020040c401d6000300b440311000880205190328441d90035099401c104241018000f0700a43c10039842010040060b030398031090b8041404000070350145812002c40038640d1202d03c0c0300d622550407240908021b0100d9514403044800b2034090103226540450100901d141072500011300d00341054060504500c4c0c4170011090007041f42e110340c011125035881d21140000c50a00b10300041d04a4a14101406492001c0d44c0d0b0031101d00000380390a1417403034080010300c156445450081d06450308402c80350018103050401a0290010b8100c89000d190254a10511a91203440c16040860418940707202804e0030717000c1002824002d0030281c22600084000320141e81e0a1007920700550 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466794118 1250 466792868 466792873
    0xf0a05091f17010501090513230906040507060201060b0412060605090a150b03070c1e0803040b070e15040b0a030603061a011103071e02060d060f061124060310050702 73
    0x50302c00c1075410700780e0700503004181000010304040015417510010441c1c01c1003080c5000c15150041158881c60070140541c0d203407921189000e2220062000c1082c0380558001c400f82c1e075450744c503504280e013690713014414891305e140104020040300d4115100603040350b11070200803d0403961341000a880810030f540d442c242507502c5217500c0ca140c0700705040e1070080c011420b03420b086140c542c030081c20030300c0e100b00090495001094071036040d0003542c4040340031079031180740316489040c070781803090712600101d501c540804d00c00110741140d450a2000160090300ca110841c1ca041c0c00c000c0c1c40401d64100e040300d2000e1584418000c400105203021700c140402c200d52080e074030200700c00001010006070803101002508104000030120b1001d22529000300134000c41c4840c0f004507071011520f81c1c0b0035180b000050518200003c10000a0403500c80304549891341d40d114010100c0c00c041d500e4102c400c41d11041094144002c482d0403c1040c0f10683c8204000c0c1070b0fa0103503490b014840c1c1540c008882000068 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466795368 1250 466794118 466794137
    0x6010b090a0608010b0409020322030201050105090f0402091f080714040c09180c120203070f0207060216051002070b0a050d0f020a0c030311221a0f0a05091f 69
    0x38246241c51900070007071860004003552510364640700501c030398024145240d030000001604290984510640446084044144080c003410024002d090a0085501c14480341003c5056115074140807800b031074004110340502d440c3c01550302d172881c402c0104000d01840344040000c481e20180001e80040003080c1c580b9101e01058400c000c00c540443c44000d0500c1a2240f00340220300814504104c0410300b00b10000d0001e409040507107412100c1c009030141703a400002000070065104c8440c103d040c10b00c0e02100c450f0f0b0344880c0300384d803600e04886410101c0080e03075404210614050f0390440c44e074100742c015141e0194690041075a5a801002164089400040ca4501c40d40251003107901020300d19801f10b09210240300010140c0114920103000c0545032003005070300d00ba0704000c640759903d40c14550403802501419000450398a40b1070800ca81d07110b40441c4800841450440b4081c1e000d03105020f2401166450940d4290006050141c105a615083e4411450150109091010300743c4928100307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466796618 1250 466795368 466795387
    0x115030b100e070912020d060207050a05011a130b0f1f020c01090f060819051501080c03061c08040f060c0210142506051312030501050112050403050c06010b 69
    0x48503401e0b8080c0b0b80d0308120300c081110155000b03040c1e20644044201c10050403010740002080d00c100d030312015020754400100079040003c00211044010b10070002880020304101000c1404d0503800d06d05070b002000304119100c40d2600741e000c007501e61001001c2007400c003140000b10700440038481001490031400c2c01200000c0e501008010b04100c02403030003903101070500310240c0c0000803a00c200c1041c4103456000c80d00300c01040380010f4401148000401044c036104081c001c0010410b49410b0100e600000400c20202401303080ba482004081c14040e420340705601c2030311030040541da0941d02c2801c28800410840c034003118400041415903104226030350300b8010000c070054407a13010000e02c02464160340409103640165000b400702c110300383d102d03440d25148a14500310340ca03100030400c502e032000700240c036a00c228012903e14040d484640041910b50f0301034040303440c00c1c0289030104034180381900040030756400c800d500c20f11034604142842c1e000801a494080f082e00000c032829008511f0714030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466797868 1250 466796618 466796641
    0x6090e0c01090b0408030a0f0c060f05070f08010f0515070f230f0717030408330f010902090609030a0c0501080c09011d0a0e010603201801030c020115030b 68
    0x1503d80b806026280c680341140043d03991059440160034060504001504140602020364046800141c240038849101c0380782c0c4c004050441d108804109a01d0f8803000892140014506a415585000540500b46030422400c4100c032222050362a10800001d070000361100c1c041000248140c2030001c1c0002c0b8032108134016000c428190701950703c804082c000301c0a0005940023160f200c14030018001086000c0e00d805c42c8100c1c0c00c44c031030a10900081e0000c607034005000e44d286440c83c281c1c050301411194070155201d041924000001c070012001401008525401412f65a0b8000c02e42031400e400d01001ca401e02c50300d0481500d8101d01050104071035600181300320751049900c14058544000440041e0a903564110941040c008840d0200481d0300c0312803c82c0f001e0500c407400303030310325603580d4000802600051030b24210030482d1500c0501105060001d450b60303107801d603011036464100100114000c02030180d0703601c01c640d00d800309018100000c11048001d140a070004001e14030b0468803841 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466799118 1250 466797868 466797887
    0x32a081501050f03030a0e0f0406140906010c02030a0312060f03030e01110102042714090f010f020403021302160c170f0607080f071206060f17010b18030106090e0c01 73
    0x500582c120000025180d5000c002c1b640d00c450203050101c0744003103071400304229581c00302415400500d08030020400b50f0441c040e030384810310111100c204039a01c101c01100c00c0c2e450188004d41680c81070254800090140c9414504100c44440000c2e0255035940d21461070301d000d62042e03001c43c0240c2c010380e00d10759100101d00c2804140790000d41c0b902e498100070440c00c0aa20b00310309a4000100c0d0a16040017598101000ca481400040740786800c10555290301d42c1c04120300030080390700c0d109011604400750b00a603403c40fa0010450100c888140781003602a40c052503044540080c1c0390039000c0010381d01024071015001c988440907540d4144001c45140004030300e10b516042e40a04208403000d036000003c1136104414070035251098842160540d00c103030007403204014660800c1d10104100381d002050680d04122540c4a4000c0340742100503a2007940c080c0a04000800d04004400600754118071003141d2980c00390000445994840b6100212010007403480713001e4000348246001c40d0380c02991503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466800368 1250 466799118 466799129
    0x10050c0a0c122106211106180303130510090609170c0306041506140f010f0c0609120816090303140c07030804090506090906060d11091f0b0a0207032a081501 69
    0x41c130300140191924400c41c070000044030b208001c00100850303038008e9040200124540501129210307203000c05800241105806418003e4040c803c0ba00303100d500c1160050211030140d184d40411a044c00602540c401c1d5841001519106404803d103064900700701c1d4030311540c050101405100180c2001004ae610070341c3c400601944540c036040322aa407150101c00d0100401d0800f2403404040000a440364000341ea405002c0c5031414100c030090040340c03030050a80703d1a56803075540a60781d001c1b01e8414104850012800a408000240002800b0b46c40140804000c0e0620505010302c4902c071760b160003020381040f203031074802050400808801d409101d800060884081c0d5041c504400c0d0103a40e0300c00208000d101d00c5401400e4130610010140350070030050064039150940c40d1503165100e028445881e514004424548002208003401041d699103030450f501500178980f039a1108541d07400420382c082c001030303107122128400d0100d0108107030040c00c1d91006000e001c0340000e00c00780e01c4101640003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466801618 1250 466800368 466800419
    0xf010f0513020d1d071a030106020a0f06110c01020408011a090f0a020403021c030e030721110916020f0312010b07030e060c10050c0a0c122106 63
    0xa01450380d544511541480c0d840d040142c072500600d6000380600711540c500132056a20740038a5004002c013258800c00c0d00c40144542410410300c104102c07a41c4000d12448006822001d070560000d0030703080042c0d0400f03001704000300d0402010442605030380d000d00705203c120380d80041c0030404c0c09002e0003a10440e44000b0f0804031038107080400704180741001850110082c25050026010f0400c981c152800b841e000b803e100d000b03510020800c4e00d0b9800c06103007600840d040d490541094a40015070b017040e038064200d40158040c4046520700110b21030f8200301c481c52400303104e021407a1142e10754607100361710308041c900d044958003001900b00440d0400e9841d180d04104008044944291189411074a01004031030b5101c001d410121150075288450541c44000080c56843d00c2d4000901040403c01b0301100300100d031164044281d19100c0c40750110f010410b000607100114000d001c2c100340e86681c6041c0b4500c1c0c0220813031010351041c90f000616048e035682c0c050034001240840c006118485c2c030f40380e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466802868 1250 466801618 466801649
    0xd150e0c041a12071a0901180f170705100203040e180d05160203060a051b0304020d0b070216060c0308090c150d0b0a080703050f150703090c05030a0b0f01 68
    0x29911424002c21060602075070103407000d00c40500007003003014000c000c404c400000f500f10200004640c0c1e84404000c60002e9503034010244501d030202032050440d4144902d00c201075180440c02c2c0802c0400c0e00408001d1301940e02e000070b480d145c0f040507800707100d11940619560b03801c00d080c1c2c3e8109140503241c4068180e04c1950000310380000074496190b40c815040064850070b8a104001c1180c0311000c000b034260140c202408800002038020038000d00480b10b46805000304145901c00900040750043c1d80a6901510b10340070480c400c00668111203544155140c1d0075080020a59912840d8800c00c00a540030854209140e0b006460702d0300075130142c000e048011035032000210410701c10341100e00c6180000500b41c0b40740000d58850032200c0405400c90900f69503031341e41d140d10741c0c0c8a4807007a6698041d0164402e094500410410089042030303540d440700b511004000c50041c00b0180f8200d500c24230428010800c2e503070810502d440580310702007160f403903e042120b0151030700d03040e401003064441580 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466804118 1250 466802868 466802891
    0x7020a1a0c0c010c080601030e0c010504090e010e12071e030e09090c0a0303020c03010e010b0117062103030406060b0a0f1404051011060c070206040b090d150e0c04 72
    0x184441195600d06180954a581040d0a418468030451128940c43e2143c90b035001501704042600c949001d0700c1c00c01081c00b0f1b21400d1501c8603440c000040c00510200800d00041c0f0090340301032007100e080c5000154082c0158907240c03a00b06032820705c005c0004003296450070402c688030754044030400800c1e0140c14012550340035105140c82106148038800c968002040b1040c104240000d50400400740c040465072414083c0d110b030041c02c54103010f03500b1b019003030403a802c0500038404141c5045e0341d0441000e04040f05102030903c060401c66106030b0400c280344181034214040a100d507907040166a41e41410f10701401140e002e640b02d030b000404280445120590050190a0308110a0401c07540c58220801d100016101c1c03600107a5200c0c000103403052245620000e04d11180030510101c3d0f034103480d080c1c2c07102150f0080c903000079031101c400c21043c4003040518014050020000c0e2194080c10300c0d80d035036401d0342d101603020f25503804c1e560304000d800c0034410040060301c1142a20100400c24201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466805368 1250 466804118 466804133
    0x807080d0e01140a052e06110f0a021201020f070605010e060a05060f2b050405060a0905071a270a1208030a09170406030b01140c1c0c080d090201020607020a 69
    0x8103e8844c0580e030f01d00103501800000d00d061990b10036902ca207460348032001c6170718030b00c09124020640042d4a50489101c0f154000031000c02903040503004009680c29070f4204108010030707080380700c003554003030010016840300380019015035440380308086495030512002d403030400802040f03d40f0402d01d1f07400c200001e48450040f146002510300100d681e464000080e40880e224004d122013a040303580310501e0b20318406a101501176881901035a0306500d51400308410307128403503400744c050303081b900d0104410040b00c400ca00072000d00d090030508000708026030060080b03140346d018544001050304028140f400181c1400507000c240004070101e02c4988910040340401050210029501d8005805000460b8071941480320408440ea986e6078032804000d0141282c040d07481e01041c0300c103200c400401c1110081e240040c1e14074004240f8131505403441500030840031448024030641017a00800700d00c5100003400610030f03040f0042000c0c0c4003803000a2070400d005200c40f0441d040320154800060030b5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466806618 1250 466805368 466805371
    0x1918060e0609120303060a1502032d0c0a03020c03010c0c0f02010306120309260d030b13060306020c100b09070c02010219061e1a06070c030807080d0e0114 68
    0x149000c039244940300020650500c07490803115840100a0074104543c0c2c3d001008610880040d14a039000c10790340e00d00007581c440b483d4171850158200313001c1524202c5242c202d42000c1c090054440c0245410342c0d2810715a079004107120122500508014400c2c150100700001c1130040c10f900030420345d100901d0040a1195444000b41030707145044915056a01c6608148081c1c01300801c0080782461501d07000d490710203c0c0c80740c0098400e000074582c2e270b0300220104000b406410722000e081a03480c12803086008107c012a210790281190780034450003052032061002540c4a6000141c2e106003280364a450680a05c2c0121f1a903804d1183d1140262100c40c84a038002050782003040044d002c0d880180c0c00e002c0c0c10020042d810740c0c0021000d05100b5240c0141000380258a0f0304d1908040040d18042500d460668940c0030f05080c000f41c4007030303080010042c20118020405001d10030748940d00d040c45540410703c00d8807024004122501c9041a9200e040c881811200003002045a00344103c0c00b038210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466807868 1250 466806618 466806629
    0x140a020109211104060519030506010b0a120f15091401090504240b09040807021f020712050a08070803010618030b130201110d0201020322170304022101021918 70
    0x4031500400d07030f0b91100e410000181600404101c8001e0410411a0003091240300a4409102c0d21f0000070702c501a050446081c0c0b01a43d58043c00100840202005402000c40d5400041e075a8501003ca4120400085000d80115400420152032801c2c0e992010740d0103070400080c1d980b600007400300080e040c600c404070481c0903100c2040c4d1102c1e15403101c002085000b0040750040040340402c0100310901c801030201910031070303680d44d820814410707070b03102c60760202000070150340140014000c241402c940442c202e4820300071144201d040303643c0c254081c1c205450865201c0b5001c001440019004903085012440d0326034548002c030700e1511058211000a42540c152910181420055901c1000758a500c201e0790011640c940181d610001d0003503004540c04141581c14004000b890256000c80c0c200c1e0340d8200c0b4040301d001500c00d040308101c1e880500300b03e80c000c880d4045c00d0341e0000c0b44501856460081070005072120740c035541c0d45052806046075081004010300803004664507840300c0905407107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466809118 1250 466807868 466807883
    0x305060316050306310f020a1d1807080102271c060209040209040e0a0312151a2122151a03030c030306120f1018140a02010921 56
    0x40034030142100d202444a0240d217852034605910500c90383c03c90703220089100b07aa1401a0582d03c0c52903aa220301951104440d14027510045000100c2660310003010040000c162445c05036a00d0916003247c0c8800605489080c407110704555405405c4d82c25040c42e0025101054044040107260020300806070000f0300c190380c00b0403103071140d880c5d40c0e0585040702000350080180c101c0810038182d590b9110382041740004c07040111007008080358004e54465010000e07207a500b190038805c140c01010540714064600c103005000307516040c1e080036214081049405c81d140c00074100141084c02c0c3e105070240310000102040400400507280c1c02005c1071055803a100007a0050506580280d090618404142d01d0700c408155614081c2e0040002c50081c80d0884400d2490141085c44070740320030584520325403a8201802c80c48048440d500074110a05100140d035662041c0356030343d9500c00140d0040b007250b6900c0607021404658101140c0e10141c0b2042d0b400d1454040102880007001040c0c100060458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466810368 1250 466809118 466809151
    0x20a12050a020712150b030c060405090603030f040b18010215060f1201020c071e050d02010f0c0f0b090c01030e0d050d15081c0504051804150603030305060316050306 73
    0x1c510a1100d50f028000c0036414049012072414404100d0b0100c43c1042d001d10318000c4402d05518000403043c406a001038022410035140030100041c140004048580600003040b0128ac0c801c040700060001d40200089180c81c1d249401402d1300f8111150a41070556010380d0458180c03402c01d084040d40310008641c0440881c20500219001c1c0c4880c10381c031211036002094400c02200c010030382609484c40b480002104240808048a60b108c092042d6504410036121a0b03025500c0b0f481c1c0c01d60070000700e0502c1c0b1307418030300c55855034421010020180c0b0780c040754106000440d2824416006442003d280a21044908404650322103c15000040601100080482c904402604503d203000c000f195101396007542c4041990710f62002c05408a001024890058062401101a90152000680840f080b010a24550410030001074000e8510410b80485440220300a000b0701d805913209640200e500c1c28404141480c5c03803581510036420104100050007203803030009038160b002c20344064000c00c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466811618 1250 466810368 466810387
    0xf050a031e0615080c03061e0702030f040e06010909091a070309020604240503100905190203240307060e040507051b060f0a29010203040914010510020a1205 69
    0x8141425034001c000d9802c18030f006208603140c2d101d803000c139010b10f025240c00003180410561100011a1550800305070240c0100c5036526402e1241e41c0503169004a9140140c42c1203000d41c6a00241d01440a000c42e04040103c1c65901c0b00513070f00208118001400940c010b9566010042400505c003e07100007480001005980710382c02c0039000c29005441d2a070341b65180c0d81100c114043c403e100440014140c40345882a510481c1240c3c41800f010080c080228106542c4c900a06005080c902001c42c0655110412101510080d400748174152001750501038801c52028610b0044c1311414841c0d0800d4108224064005081010070b039002c90300000d8590b100300c0c0503a1140220320740041c041c5d428000500c103011000402d5400340d84c500404498560b80c51001c201940c031052115424500b40010442c610311100320744021500050041c1d80c205500d40c1058412203072121103031402038901750010041400c000000709040e804910107000481d05517155000d862200c1da0344401009400103d1240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466812868 1250 466811618 466811663
    0x2100e0109090e010509060f0c0d1e020309011b03020901020d0309170a050d050a0504110d0609050609100b0a0803040506131508040b06090403080a1e020d020a08010f050a03 76
    0x2d807408940410400e140800f400f4002d041c100d031840c00d42e02c204408181034100c80700300c0751721401c0849401403811a40c0c0440360302070110403200448400b1a144a0441c1d41a40c1c0055881403080000003e00c03a411040c401140e2a80d00710503400b07240c8100040310082c0d034003040010103901d40d800c0114bd0403c107803600c0700c01d4007401c0103103080d44200800c0c03c00c981e5074054020402c41100410501440c1c0f03c0628070000c44005070f900900002420340c401b1071030304042001e55941405190300040d40c030303c151219424110b0481d22420a80c01210103141c41c1161442443c0400c1800d070390a05042d13040040d6240d0781c0c4901d020341072040a0104008a42000c0d000e0400050301d010b6428107404140501e02034000030007590211444c02e00c060029111741003040801b485190990340b0f480c602e460703035091200140500349940c003800c0d0403060780e52540c0c1e41d40e00060140031800000141da03400b410b9001001ca00043e08242c80d0800410400c111554441d58401c082c0ea40140d00041450600103035241c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466814118 1250 466812868 466812887
    0x6100b2710080702070b0408070501080402130e0c10180b1608070b010e0a0b0d14030c0105040b0103021002070e0408091201090b01050a15200c370302100e01 69
    0x1684000301d00034a004a981c840034041c09082e00e0780071200ca090b12141150004e004074019600c155000c01c40170807407907206014654001d0300180c8510500c0d01c180b0700200581f00075844540784d5610080509101c0d0800c000074032440c2ca00c502d00841f40c05410704c400954400a482514400311011505034040780001c6035840f12a98001d25039544d56195190881c10f0b10000d10980503013801c0e420008541240394018038203403400041243c0c046031411354403c11911900102d401052206100440c020002403040030b000d2402040035054941c5035104120701121001000b504540180d4000c01508000340701c02900540e0292845032074001d5240418402002c2c1d034006583c0d582000080f9061040c1c0c892050705031001074a4080c860341e184c40828000c2c8211035100c00c00264032004e9201a101d4650120f819000711030162854080150006400c10a100b40c017060045203100820008801058441600d4070003041c006090b20f245030005603000c900e0100c00d0381800b90511488000ea031003100b200307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466815368 1250 466814118 466814197
    0xf14030123060d1a12030a030911030d020a050c0f100507031403010e09010b0102012f0702041b080f0c0403080a120606020304090b0a050f120309030307120206100b 72
    0x90f00c0780b05400c403040140c0320031042d941c10400450002610303400d0120009940145502c011464080084000c6004240d11103081e281e8000b802c50421040e9400c0c010351b035008600da402031284a500382001ca060007203d42c6900d00c1809022222203039031302c540020420609050420076141d5589040558a600200055480c16080000086459040001018003c024050003000b032180076100582c200c84c2d48041441d100f208070101083d41c1d51540021a10b8042e00d8900b00303080c0304295010500361840b000745980da0041420129101584c080003060340900d01340400c041d42c0c103003226031621500c580d00014208040020764508180e02410650411021040040000540d1110000c0d22604640950001d49081000f04480d07880e20003071040655030020001020080490100680c480d043c05541034140024800703102e4a40d01480549030716070050110340345008100328001d090480c010070300401c8800150007840b0201e261025988054561030900c0c000b0051103c5040c03c801c1d602c0400e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466816618 1250 466815368 466815379
    0x1211010b09040303140a0e0712020d05030a030b0112020a1d01051b0303010f090b090c0714150a0506030a2a030804030f0b01230d300f14030123 63
    0xd010405503da070040800600c00d81e1129030a1b240c0115031015980c1d12256100701c1ea100c900240300e88106540c03899a21403000300f00344500d084568500e81960000da10a0021980c1d400002312a0350300100442042c01c5119421403418440c1103000d0404c540d0311050160040104d40b400115901641c00c0310003484900c107207440000c14020549583c3c3c2d10900a0820045c0800e0002583c80d0143c05a4090320a005241c049a66070301c03100c5207059000354000385e402c0042000d081c40100824003003042d0a542859402544e460000d42c10301c00d1b104090807041c0a9408000c2080101d83d4990785a004410603011101e500301c45030310112101800ca802c00307031103c04006000401c00c00102c01d00f0311204d1091000000c40ea0342d50900500b03110369840361004034003841002000030b150002813480c03c244152201038080c0b141142c004012800021403044803c0032031000b421194002e400040d1498880c40c054034110200c00300d0f90158041803040c40c0b604c81d141101c3c0e6070081c407001c001280801000d0038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466817868 1250 466816618 466816621
    0x11060f0d060801110a0e060a2106030204180f1121100b031204120602040f08010209030f160902130b030c031f03080a05031305070801090203060a02071211010b09 71
    0xc100060003588101502d5628103541e890044410b00207440c3c84070b031140c55982102600d8800d01146900c4512450b040200141c0222042ca0540c80d407800b03204040c5e42e001a03d1411441408225220072403240390702d0b0011805000040c00544290200588c011a007000b60320013000851045414040386843c3c5801c0c0c40200f41145100181c100101c0c00c607480203110541e40702c070a00d0707260000d80c0384600e081d820030030007401a080a8101c036084030f4420500145000c0da101242d004d84502d542002546940014100070a440c080041d0340161011074044d00e03101c10191484030f400c2c1060322521090b40e4021848103504010f4291140003460000c01c226503d14000c40c181e10a54001c0354600d50b0241031f40100d031032420349100024181c0e5484010b035450011162010382c0e15800c01000c180b2000600710032803000035820300404c001041480e0010400c007016104042c1030840042c0b400f080d89105200c0e250110320360040701290021f00d420100d002c919181c290501405020507040e400005450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466819118 1250 466817868 466817887
    0x290306120a0c150e0d0209060d0330050f0f1303050d060b04081e060c03060d0c0807090c0302090a03032a0c060e01030902030a030806060d111b0d02070311060f 70
    0x50311040200003a50384c9402d0034180208005e04c0c042c4403003000c2e4206a0200025030039080c01c0b04010368090290a104030702144450501407261481c12400c9580c550410724203e104a2501806810210700c0001b04242e150291004042100040c52000903414140001c0140740c00781c0112200f600b46204103010f20f07900c0f034401a84583c4544500d5040e442900340755805a0702410105560b9240c98000d081d1540b1442000c0c0c1a070340024160981c88021504c1c3d080c0058040d0010b00002c001c1c440241c428949414000380498089813140740504d8010006d400c469521b5000c0072041d00e900d0704041c0001c400400c60903481344040307a040c14400c00b400c9502c01c00d11044400d80b000b00c4220b56102c234807400d0000011000c0d6110118001c1d0190b0114032039000290280c10780c1d0b03a00400c084e01440c14011211489816160010340601c0c160b0400200003405900003481260400036034401801c810112090096131441a844043c200f1b109011000006d940c0d10800c407400070786000401505d400582 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 466820368 1250 466819118 466819139
    0x1309050402180f0403051c050405060601180303080112052a0f01050a05090d06270c0b0c0312090c121522020d140313290306120a0c 58
    0x1a1420791148035000c850925400140d440e03a841260185251291a11035070741c192080d40180611401d40002c1c0b040002003000d02e8440c19215a000300028051424000b0000d8895580700003802c601d59141750040c00071035000003441c0e04403041044128111443c0381409410620724000c1c108400d1409406a05004a10000314400040848100b40420b0304500103642c20300c0b40702e03100404101c081c8088981850a0a8003511071070090300d010a048404011802c2e9840e004150713400d104c0d1300e01300d020341403200010800c000742c140017400500d41003240016554a00586007a03c60800340c41f030000d0301c0c00f0401c3c490784082c0c50300030b8948a00c88040780c81070703911130b4820304003580f900c0007e100007200c141421105c02c051a543e109280c42402c0c442e000e001c449a0382c84000d580702500e07440c00d00b4144070200003d00c0007021002e1031240181c01d044010000800080002e02e0050365400d6140148842c40101c0342c101408442c0010769810f109480c50800e9a040310286c05500b00e15800100003020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 466821618 1250 466820368 466820371
    0xc020a2c0c090907050c0a05031c05010f0b0306060c0712080414040c0f030905030405151e030717090c0901030311070b0c1b1207060c21080708070302130905 69
    0x948020340e855074503202084114020340495660204020000c40d150f18000c200601c84200e804096a0b55029a526040d00c0c41d072040da101071419866805103c10030309103128003800360500c1c00120308180d2401c4080c070b042d40000b0f0405440b40c0e00c001744ea00c1072400b0800400000382080b91002d524904282070192183e009481003407115101074103000b840345040d104081d145c103901e848503402170313500c410300f10010403035804212424801000b01007411b1b914288001c5001c9104011503581d44450300e0403025103c0740403603910f1300742c000b40184031409801c281d014010908103480700f2041c1c0d0340c1c401c5140c80c1030180c480301030f0801000c00020061582c000e04030f1442c55054411250596034848884440348205406400300382c202e04a500c04162101d180700c080100010444601045103407aa00e0510310554403580105101070340203c100b00007904908054044101d2010042c1c00ba620301420b01030005213088208003800e80080d43c01400307541035401c1e2a4800c44502c0c4055220303503812008190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 466822868 1250 466821618 466821689
    0x60f0c1309020a08010914070513270c08010608011e03060c030e061302130e0a0c090f0c050309060f0403031b090305060610021902041b2601050607030c020a 69
    0x800000104106c0032a001d29400d001030440d005005580e03540307044500e6080f0031442c00c02403901c0500042d01a103141d2107000c09041601078115a000c0318642c0e101110390103600102480403400041000503008800d182c1111a040725110a91401c0042105114421340004111074071b010080c203003e583c1a4070050100354030398205c1c0c260361a0151201402c50036a100207600451071180e4601c3c02419820001c04c2d1500c1e64210303845410507544042e80e85005400c0100700a03984c145011084605000791034903200d0394241107255042ca01029500d40c5001400054141e101202003030416200e5842011a2540d10440035030380304036900700800b00345841c0f1003038403903100361008900f191400c03950b464105586034009280c0001e108103884610554a0003d903406070b035405020840010828007031000d41e0790790355a511900c1c001d010080f09000814031400c40b104a180050103141c81e41c400311003006401d070501c1c20b40840584006040140c1c240c0101c84a4014074007000c0d0040840c1014005040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 466824118 1250 466822868 466822877
    0x90a030c03060b12070b0f07020a080717012702010f12021b1002030601050a0c3206073b120a031103030f06010f02030714031305030102030603060f0c1309020a 70
    0x11340b0102a1559455180504e40e15460204440da4803003601c60028a03080b4400ba0408050300e995100b00c07410040c0c198801c56224440c8003101009240a10541c43c3c9615103002c6a6010b40301240980407a04903900028140040c060705a01d10b180140044c10622200280541da680d0400048084119000800300c0d05071003609000c1e08151090300a59107d1303501070755214105142004c0c1201c07108014a0180e940340c0510040030f4808604190850b032800140060100100d543c8130b041d46004c40041844040003540407a001145c0d001c000d040341909000740f21903c01c0c0310180b070300b4400b08248a810303991111040d900c10103212004030f0000d05450094807000e0f85600c081e0100c0340c030391104544050342d030740c0000000340841d809503403060030028482c03044904100c055500c00c107496444d00c00034041d6a0010540004650303900d180314000c0d102c00c5e17000354154105440403a0b0364540c058594603040350b07103c0003e83c81545031000d61320926495400ca0007000d9983c0080d6009601043e62a000074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 466825368 1250 466824118 466824139
    0x9010e0402030615090112020a0306140303070302070e07030e0102130f0b07080d090f12030501030506060d050c0f1206040609170c0a0314130609091d1002090a030c03060b 75
    0xd203000d2003501d00c0382c0400340900020844003041034000c1e90220b114141404105c50222100c1c400320300c060505c0480544000070712a013800c00c003e40340d80361404d07214420b45c41006074900080d40070034080100c035144648240551150303070301a00a8107030b070741a40c0d840e5840800e10300d0b01155000c10303290442e620785036440e2415440344841d50403407061003c007070710200c4204203201c0c40074003650200e031049000d00d01c0c460f40c0c142160745181a540c3e013804c0c50000aa00d801c010310078001c0c1404095080103007203a004101c002281d4500341c40f5003e0301c404c988a1410808030b4541612600340004510040f4400d981c401d1401d8070f006070013080a4042920903030020541e80c03a441c0520b00850f012240c0c488002d0240506a60b0110b6106903800c10410800f0740c1441140e4525a0b440741c640064001600c80c541c0d13841c14598503000b2141428940d204e0f4400c1c102d1000c10800020920180c40f1882001c00369030703034140d4804110000c1a95100400c0501070300000400d000d5640d0110000000846440c07510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 466826618 1250 466825368 466825397
    0x20312060a080d140d1e05070302090d14070801140f060d0c030b0a0f0c020708060c03011505030702010e060c0408011b0207090f0b1011100c0f050c0f0a080901 70
    0xc0c8a1801801d2180c3d01840600750458010103190540e22421041d07945815421600202541c841e8204494006014264145010414050190b00c0409450704500f031000410000d540142d04050181c505082d00c0b0b040d0445030010301600b80a061000e000b4030000502501c0032040c40c100300c3d03100144500c032601294a0b4a0301d082d1040d440f0740c104090020345030858907141c41c40301e006441302004a83c2e8005038442400180944a8100c82c0d90b00070780642881e0800307013410300000809840300c042c000c0005000c180701d0500c2074401511b00745807442d16903076065402d86c0145040c04d140c6109108400400c2071244103030b002402a2002c0c60000c2c041c41c00c0c40b41e0300051802c2c3e0b000d0684096007140302e05002c40317880c81e40946240440d8800105020880001064692601c0c001245c002502c0c01c0c400c01007440104021034141c6c0b01c1c44030402086003150401003500703844000e01c40800c0170010b5061200a41000300c2041c181c00c04098030304c2c15080e458010320790b41c84109d016005c40c4988040204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 466827868 1250 466826618 466826629
    0x110405072a0206070b060118080313050d020a030308130506101d04030807030c02010b0a0806011a03070206061c0b09060901050a0b031b190b0705100e102a02031206 72
    0x3140d4054202410b0013003654591390700680c028681810840d580c0342402e00000400b12020041030500c000e55522800307005550200e4038a074021034029240203101e03000507250110484100c0b42c1629100384143c0b1208000300e4614403802010306284985c0d02404440d1000c00c4060040350700542d0200c420814204001e154034008640143c04240b00000065016021360040001119540f0000440c04850300011300070b400f907608402c900e40d000c103006004040d900024000a00d640d110500d08526211100075900c481c01000d83d4001c4115100040000c0030000032030b65400d6020089803510300d090748800c2e03a0384404540d00045503007446c01090304a04144035804c000c0c64050054614540c1a000000c058004a00c0450300000d903581412081100c43d440314014000d841c0381140d4401d00c0341007044c9801c501041c2205014034141224080a00008803907841ca0140e080200307910207500443c1c1d945403c66524070301c0c8404010703082d4004980c04001072000580d1441c0700c0001c1e4407503009101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 466829118 1250 466827868 466827947
    0xb0702060708071e020c03071d0105150f18090115020c09070c080c160b0d060b0918100f060c0605010e0906012607090603120c02010504090911040507 66
    0xc0414900c0b220b040e007a488a058413040301180d8011900050303041c502080c6807107040c1c0c1c09007515081c0c210011107000000c902850044c00102c41800d403812401070040d285101d060086061851b00050700041d4050755100e07201091070091038000d81e581d4490220b1607145c011100100140103080400d4024681084102d01817072459603505200c01030365540540c04c2c1d000d001e1480e1540b00b10741b4800358202044401c1d401500040021340d03250800a10001c0a54501d500000748103801071084031001d03120901440c40c4550002d070110700503250070310781e0b20003c0095040749040c0040307802c9c003040c0c4503080f240d01202c0380e03c168402c00290303070303540c00d09140c3d4001552040001c0e04440010007041c10620704a00e910100c0110500340640c0620081d40f902c0e61580c03040f9002500c0f55010418441c07032811041500d480360414045104403540028454441d074015101c1c1c0e103640391082003e000c034140c82d0308140a400340c8204601d041143d400740407604031403080d9508070141040c42401c0f2030b603402840c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 466830368 1250 466829118 466829131
    0x41409070501050d0b060a0f080a090b0c030a09020d05030a111504080c071706010609170d030c1b140105060a080c01050702010c08031008010606050c03040308070f0f0b0702060708 79
    0x4095181c10840112103d074090043c0b41c02c0c25448115070100c0c0e40c0c3d58070003483c2a01040d2584400010181c0026208003001003480c403000303281032030041c007081500714070b1544240c44079a01507072541c43c0c450042c02040104000b9400c206410140820004000000c0c480c0b11141d03100c22080c1660340020035501c0300341200076100350040b003010070002281400604000641c034400e60725120340300d80c05401e04144051265405a01000040000e55003100710075000e0408a081075008010a001c80b60340c0301d001d90365007000c0650380c182e001401d500c9444201c401c1140410405441400c60070850aa4924040c2140d865441c000104d88e051501c8148881140e00da4009401881c00210043d40d03590890741040c0e05201e040a02100014042e0300254403420410112011031400e0000042c02c4403420b40084e41844002c2064071003001000050710212a4420314207941c0c0c80301880c02c18050748102c04000d0a8500403070046040000c42c0c0f0400e88910b0083e030032107900341e841e040f0413074210b003064900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 466831618 1250 466830368 466830373
    0x8010501030c1b050105011701062d050d12030b0109060c260d0209120a0f0b09010b0d080309060a050c1c020c06090f0d0201140402120a0212030d0b03060c041e0305011a041409 77
    0x11502d00c032f0140c1c454034805200d0a4809411550755101003200054403102c1120349905d0510390107806509482400d9982c0000e1a00070703841410306102400d082034413500a411307008451100e020032012000c0c071502e0711003c103040d15211000c803140400a500400191882514005a03805070002c00245200203580c002506204c18030190700c40740360000c00038280c00b02d2552230300c244140948441500e040201d1051248650300e1070107180c22400d01c0c03400340100b4034013030804090050f400e401c8001e80e10b00141c4841d4000c080c40d0b07088403a83c020b1158104025041c001c08040120411002c510589054009000c0d0b4168132104403040303080310f0300301f910311602d0880d110200d00541004100c07030341041e03000f904580030b41101da00041c0d20400510741001855200240000c02240c00c1e004039654414107078000c2070715080501d91b1200901450180409111080b42a0000941105405030085400030000c101481d005490045040210b42e0441c1c0a10706102aa02c0140030295074140b20703828007800f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 466832868 1250 466831618 466831649
    0x11030f241f06111c0f080a11030105041a1503041a071d0103020c0a0c1526092128090e0c04050a09020306010f0f08010501030c1b05010501170106 64
    0x90543e0315607003a104801943c4070314070820041841400700c4140c00801074071040180400100c2c010b20481d8020003402c122420006421042c29100c0180d0781511400c4034003041000c590605840b0358840145069070104886040386801d4003004010341c050b43c011022800402d50503140394a014006907182400a400ca401420000070080801d134290b080c1494054503042d002c040306891700c200b5203010384100b40b07510820814132800e03d0542445050034100390710b49042040a0807601081e21800b00c190303464100001c3d541581c140003d41107420071160007a55286d118400c3d10550b0031a043d03003410400c541c22044041e0b868210000543c0c10a5a0303203500c483e080c049001c43d6290b001e440012001010700020400e40d880c25242e102074818000010307184c0c076180300010040e40b4080320382800c1c411684042c0856a038003180e400c0c1034070020300300400c0318044484204d888141130200c0320760b4044511564001c101c13040d08594100c0d88040318440703140c2d000110880c2260441c0c4a60040e4001c04503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 466834118 1250 466832868 466832879
    0xf0e09130209060a0f0b0a050c1e010b01020a050c120114040f020a0933080111090f0f01081b0d181110020a20040c09080601060306050a0311030f241f 66
    0x4018591003080786003450400c80d11500107484e014400c104ac5221503140300c11803001e08030034898844080300903c001d20b503203180303512030a07295208505d60b0390281c1004e0500301e03c00c010940007048024180e48540b640d9103800d0804a00d05584030307608071300c660320203000021129120b0103401e07075400724000b034072660301c2210b15901c00700b031450300c4043d04a034010900015044001c1c0f00700c490b65050301c61000d5031401780300e040003040420541228420081007503650080c0e6071055005602003d00d4030403540c00b2480511000c618010001d00391001410012200c0d0005000c11462200d280b064040318202c41c420020413141c141070307110080069000440303510220f842e040007406050101402c08014100c003601040c240e64490741c100c0301244c2c9030601000341e2030041003200c2c01002c003450100b088a040000280c0780c160184409000802c440102c610300d903900780300305840450180126102c070007001a03030a034054000007103190310084d80000141c2e5140090000c0c02d1202d402900c490740c080c18070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 466835368 1250 466834118 466834139
    0x15010f0b12090f01150501110607020601061b0f0f02040c02070308090f1207080102030403090801050103170c0c090118230412110d031407031b0f0e09130209060a0f 72
    0x20110b0500e440b0b14a0210140031081c403810112820741000d564100b410200050500c0c0b1483d400c991090f0300200c00c100c8050390202e02c032819101c140c0f40041030280d00800c0310161712480c00000c0e00c1c0da003600c1c1c0d1503000c101102042400e510710070b60307051000345c80451040c0d8617101984005400d084003000310341003600e019509802089002440440d808403620300075860440d4130741140d00103a60010a10051582045681000b004504024050340d0306582e0f90701b01c02811150300100c03000002c50b9464400a050041050455014055001946e50f566021249a003956010001d241c6400c41c0507074000711000411000344800003494081c1d0b10782d9550381c0d14003d05007203482d080000451a00101600a2100591480b9130f69808543c00844020392000d81801804850070300d4502141a00241c21440c2c013401c1c51010390900103103e90021400b560a40000404241c0c02001e0038100200b151030380b81d04841250090310641c115a40d40c409001c0103103a01d001d03418101d1000e407400c100f0b0301000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 466836618 1250 466835368 466835371
    0x91103090c131805030c0f0f070e041703100303081303051e0c15070801060c02100f030605031005100f030213020307050f03010e0712060f180b0a030515010f0b12 71
    0x145140001d94008100f01c240b071103207400008603055040001c3c040c40408080000044640b40070b40600a001c2503040340c240d54003490710903010842441c000143c1404244c003507000030002821040c956928204071482000d01e41c40c0001c0b0040780103400400c0c00c00c10308008007844507a140e11780070f280c8642c0c400c85400c12903c1000481503a4010000c60b00c00100078848031410822403060340c091400d1142c0090b00329541608000100000520b001016a8508030500441030711414030041c02e14480d042107000e00690b810142d003521980c000e102d411001c80c0e101601c5184440e100a890545803264104038020a00c4080d50244400000303944d88401580150741140c16400c1076403800c002d0003102c051300d400034cd00540094110f41c0c100040241c104d1400b8884403c0310b28100501c0d4102102d2101040d2540510358446d0b1a010340c3c4008400980d0000256103c0108541a4990303240f40176a41c9400d00100c0c015510a9000002070350801c0c00038103001d45489960b5203050552151690024150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 466837868 1250 466836618 466836649
    0x70f050d06060b070b15030102030606070803060f10110118080a120f05040b090609060420060d0e1608010e0703120e0a0e0108010b010504050927011104091103090c 72
    0x41e2504001003c5580301e00070500c0b18070070740e4042010f02e130210800006209840c1418000d900400801a80d6a145006c4980069115900c0c42d240d0300c4040104100707800c6000a250840501d00398000025000701060122200e0302000380300d9200d04135101c070a040b0240ea0b00801d00070060000854090050801c480000c0400000041c40c02d1031040c404152007060302c0903900010f240d018032070b00d000c051292a611601000082c012170030290b1380d051a94120901c068444840d070f01d44208030340e80f43c804a954006c5100c1081c001085007540302e80d20b4089860140c1913909491400103040e1106006800c22003034000e000d802c00070303c5d640390740580100b855818005c02807030802c410100d175a103070240b4018040000200b10190b040103107243c21140c00c00a081d042c04814030041110740e8500d0680c60f03101407940c40c51a10030000100d500f0000c4000302c4203141a50a143e5885502c15070030300079100f1148403d80c00d104044070a10756070030714402076030008441d40080b03040143d01c1c18500080004641c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 466839118 1250 466837868 466837871
    0x30b040609231b13030611071718040f0501150903030503070509061c140604110f0f0705030703021c080903180120071a03010e070e060d050c0a11070f050d06 69
    0x1040654140701c2c507807144c1000c2071185500d040c144284050b91141400c6503906e108080d02e031460540703039011115000e801f007403210800040c45a103000e02c600c408200030b0300060005e001c0c007110f41004001a00e000d020b10307850041c6040d010100c0ca4881c40640c0d04494040d01d40c289151148501207030a684800245a0440400c000020104040781c9100c0340e6144070120001d00b200d6840103007256000f0203030055210b1414140625aa070b03d400d011505200140fa200c1540e922182c01442014083c035080a0300038000810303a6824503801085200480c0648110b0a03128203191900f83e078100800e546510149c0e000b40030300c110f2103022052200c40e02c40141002001c0c8200b007948440f24542d201c0e110000d9402c62041006000940003e030704000b81c407040132504540c1003c1c50180c00c2e00c0007c01c50003c0081e0060880500d44641c82110550000000c046c8030034070700b50b040c031004c0741d000c0c3d0103040001c0e0010810703918120001c603145003903404034404d142d01a4a04010001c503580400800d49929 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 466840368 1250 466839118 466839151
    0xf030708061507030807020d1d091e13060f1b030e070f06030b010e0f010c0f060b060a0e120109050c01200607030b01020d110726010903030b04060923 66
    0x40d40020b024205507413096490140c90f28024070000e041c80001c1c080c110070b0100c2055080c00319010040b504000e0007090f55030402998440b81e251003c15140400e2100c0c221500d01480211006902d4080185000704000e0146a02d1514a08102c075840360115040c400544181040b161007600b0110103244880308641c080c90310b8100e1214080501c0d4002d00c0443c0c0c0c5c8550132149944c00c58804500d0700d0f070844d8099104141c0c04006804130315409801820450b54850b01420001e160740100e000c580054100c9844c1e00200b0406007100c40312516441c820012070200c048035000c1401600300640d4800041c020b00802324005444640310b0b042d40024030811448490154007041201620131001c40e0360108021400100284c00d015082d007005040203040880c540070b41d280006e6480480755000300d2402145850130030954158880c500da4001542043e03010014036515820603002d464048a04200d019074031741c207a004490b8009000740e0544c0c81c10380d804480310a070310a0a0341c002440c12145401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 466841618 1250 466840368 466840399
    0xb040f12020303070201060e010312050c07080d05091804020a03060507030e031801270e0a060b0a090302010908070509040602030606071a0f150d060b0301110d050114060f03070806 79
    0x494001006180042e48040108011164240a101c00800d4a001400015410358407890701c19802c0440320b81c20302400080003003d10104011503070080c00c50006072421000006402001c0e64030165000d482012000001c60340500c4401d440e41c001c542c003c11182d18a40b841e0b4550002e00f00090060302810b03614602c1d41e552140a0008060489180542d0b0780c20b9054907001400c0143d6002a0201c100c0150060321426040c550082c400d5440564895440795601c034141000f8040c2c9801c40403004c500480c514036503075000701b206400e03a40300740c0b15010b80607259940c00b40c0d1802148102a409082d038400f0070041102c41c1d00550308194050001c074a4409141c50b060459000b13005441c5c0c0c00c10b000c20802c150116825a9190002204888488400d241c0e40005200c80720802c000f0f0149030f660700d8480070b81d5400750710581918a9900e4082d46928100c413a07000207000c24442c0013840c054541c141ca0052501c581212031a0503a541d02d54115100c4880446404000805c5250410745100c1050034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 466842868 1250 466841618 466841633
    0x9190b011e0309060f180203070801330315050601090510020706050306120105010b0315060a210906050114041104050102030f03100315051501090803040b07080d05040609050d050f070b040f 83
    0x214071514000c408184406d481458a8103660790701000f00d03649010b05048505c0a071002c407000f10024040600c1000a060b03001c0c07104c808240d4001000035803801c101c04088101c0e90081407054100340c0380c11121136656814030a02001111400f001038001c6e4106204150041001c1d680100c80a05128900600b2941c040c0c2150b6003a04810841c580200400c016030300540d4100366544426607065080c164940d0001d0115090410707140271807185800070320500522640903903006900300c0b20074460b40d6540c4540d1000c24130302e460300601039401c1c0014902040c500404880840d80107074002d52410301c0300c01a00c0744981000d898007120000c603036000000310f00300303400c100e180500f4140c001a080c180048103000d0580152000c4d418000003080401c1040d40c0031094600715150046625510289450031603102d1180030003806440c0c3c540010302040c03081582c0015541c42c0b1804c126500e011065800b55810b0003900b440706084ca208101482c00104d40101d9650041d2084860902e859030560b150075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 466844118 1250 466842868 466842881
    0x4021318080429040e01180b031005060a06020a08030a050601050c011a0a08010c0c2d1b0b0f03060103271a0c1602120c09190b011e0309060f 62
    0x603070f400000c518041840c41c0d081070040c90740d212081000d04d0035141c2800703c500341c00144a109100401e00d00115210b107000d41102c144d0404c01411394004005410f04440102020b035403007406840c804d9008103034680001043c40c2910740000b070b05805d6503941030160005d0701e801001941006014851640800310034011040341600d1080d800100e45a22018002c8039280b550007035805a04040903040300b02c0d0003805001003650055041035441c0080805071100700c4c461140c40510f42e60804d01e0000340710f042515030300300164007015042030a40d19030001895000b0b102d458901e1781d0080000c140309600a40c4200d60900440200354070310882c030407400a41d804904001e40b07600c8003019081c1031b030540110015030302091000207141001da5940880c0f0600a100c00000c1c0140c00c000310401c80d00c0810403105081c3c00c0c00503d03410042c601108801075074080c000741303403015600349001d80407258020401d5815001c4260445983e803000304000700c2c0540300289054625681c0c520640590108500850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 466845368 1250 466844118 466844129
    0x70510020a0c080c0f101704060b03030406020f060a0903020601180f1404060606020706091a0f070302161d070f0315080c2b0b040602040506121e040213180804 70
    0x8241134420041840042c4040c400c4051150304c1d0105503034034007504060502041c02200200111940e11441d00c40001d10642c4800d03a894800030900145040d40083c0602d155050760b01601c482d07484d220543d0342590300c80c0030024091703084000188003203c00491203078000302d440080814a54004d180c05c1d400c840a0110350581c0d175803814200024095140030300402801c01d84020001a89000d100900121160007170002c001c4c003829801d17400e00b00325015600d480d401c0086042c0d6800251070040d640d189441c202001c551100400000d466940d850318018110701140e021721240d036810400c0740c001001003442c03c181640c03944440c6402d04c5040140000e802e0300d40c024500d00050b01c00b003040044480980c5038050040c15412580b0a00c41c3d4409030a403540200c0c06907441d291b81c54148081d0246801103500042c0109402d410350b400150244d0160500d40750401c0b890301c03c509070403640c000c1202c029400001c143e503210f041c01107d40c4004180f031a403080040384640030f0344d505201c6500c05d43c0309 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 466846618 1250 466845368 466845373
    0xb0310050105063f040b06190510050d02040801021b060606040504020a0201180b06032109100c1208010e06030604030f0e180109051602030406140d0f0207141c02070510020a0c08 78
    0x4100c01c10006c071040e1303500084c0841c2c4050940c200406242070405040c09194091071660441160050203001515260109681c0c1591183e40f940c0c880b074001d41100e000013225070762032844c9580074500807610900920000e8115480c060812041c04080e500c0044400215903031440016080800d0080e1000035512402c1c0380741640c01c1220802d46003c1031000c480d03090a0f891440100c1d49070b090340403507460480a48002c1c2040b40d071a00c064400800040c0007501aa40b15003540740e0301603100c0c06450581d4021707079071a02580c4401c3c090560b0703090100d4000300407070010261000014003400302c000e48854001d14a5584800fa044091216003003a4426a003170368854050140440c051010000d24030006c0c4000e42c1400c2c41c0480003080143c07034035000c0d00b4002d0006003480f0040e8442e00301d106e01d510921800c2d0754896851070440c8040b8000b111024031409280c040c0000f0b0030030a243e405a010580e402481c03c5800c000c01c0007050303014280d600c03017944901e0b00d0034000284400403202c003c1401001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 466847868 1250 466846618 466846621
    0x8090f0f090a0b150a2003040312050c160506030f0a0e010c05090a09110301030b041a090c040b220509031b0609010e030313060506010908100b0310050105063f 70
    0x52040441c01151100013501c1c00b4002060340319070001880034040c07681e000704618484000100e42c01c0d03120b01e400c050140418294115819600480107042c1809050101c03954030300b0018540c202d41c200e43c010b00740c3c004003c1011400300300c000071180e6003012112400091903094005014211200d0301d503d940418408541c0700017a02d48458513000a040054003031040d03130303080007042c441031105000007000c000c0424007040601800071152807008050216402d101d090a50b200c40e518030074080c6980c45141000110302081c02c2043c1581104610710305000204108031640c1009400010301c5182148011b0164103000305105030b00555082280016003002c0c209100064207645812031010700300d60080003480160b0f403d1200c100c0046d50030500002e003580b1107400403111216260301c035158522400f40030340c8040082d07038041108078004501b100d40c400400503445d403e952092040d26400707401804401400ca4200c007013420030000c06030194240c0c1c0786c8005600b84c180341e25926201003001c40390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 466849118 1250 466847868 466847891
    0x210201020a201218091f0501050708070b01030309030b2a0705030717091305060f100e03120307090e040c090506150f1b030c0616050403060e03030912040308090f0f090a 74
    0x5c03001070304510141120030700c00c08507001d550800d2609114050400200055500a0000300c100391071103507620113000442969a03080050105800e808191510380c2c0305404191100d01160110f10041d0f608038104244040c0c0080000ca150400c01d015241804100101400034400b1760412501c50381c1d00c3c510944803100842405107c0441854121009141c41c2c1401169610450300c00340c0b10308211240b12407003074418000c840c1c0101d0a03201c031f60588120242d11007002005c0014502c2a421545c0da40d038490356071101ea40c440741003950044d0000b89880401d020440b440c0d0800e41d40443c0c040c089524045000310303020600c1c0d1003042d90140081d00460f03524111802c0c20f0304801070f5165580154100110000f4494031235a01500079045a400300001d4410b0710302800980e0000c40e003204041001005007400703207440340d000300c0303c1038014080c0300d4840b4000c070602d02c280c40599410403095401d1407411014043c51003180c500d801e5010349164180716985d83c5074241a07101d880901c2c4042686075800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 466850368 1250 466849118 466849129
    0x6080613050706090b0904020d0612230c0f04020d0b1002010905010b060a081324020316020607120b0a0312121a03100207061503210201020a201218 65
    0x5410907000c005130118204a8608910b00380d60018804440040c0d8654074001500014200c9512041d1509003040304541404540a2620140710582d58000c1d05d01d03505241154070303065070360703c2507901030880c0071843e21a0401e580908201040759030000f8446030400006110300311907104401c0180c1d11154200300300031007801042c0055106403103d03400d03c8058400a40040c8008058800346050a02c59000f0f02400303c40801407000b0411110840322001880d080203540304440c20091210181e4400d84580c4c800074802d80704103035664880004155148000c0080c081d211040c680c004581d0a0101c04244255480315440340a80c1319840c00c200782001b2030042e2110130120100e41c09000180007120344000c241c1000c5041c2c00800103a0703480b01450140b008180b01807018001d4958510080108003020810310600111442d540704071042c0c0101c100c0c240c0c46000c08080c00144241c4490303c00c002150404903c02800005030707a441a0034a00503480c680001e9030042c001c40c0c52180800c56800c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 466851618 1250 466850368 466850383
    0x5010f0312140a18030602030c0403020906121c0c0c0e2203120c031103130b010e040f0209071101050901020a09140315130c030302060117030c0c130608061305 70
    0x1c50074034541050840822008501904803004280002c503602c8081c0300101e10301400286610610841d00e80c02c00c01141145500a808200d01403000354003c00c402d4a010303007581c22500b40d03540080c044152600100902c8100040c2141d0a1164031100280020348c0c1d40281e1010304208182e290f05854401510480c03070120521048007000e00040d031070046a0700039107001001e0105d042c042089441c10b00d08500510000740f0840c0741c43e002000380600c448209490300090b6002e8044c00d08140d0f25403000c100316202c00e460080c40d03421040840401818026a92548a032681c10301e41072041030f0524080c250f0380120350141950b50f0004148529a8111810401401c2505490f000805003980460382e40c080c150100310018031101d0010b89038205590003111b18035801751100d207910b5030340d01e00a0350302c070000e00840803c51244070074207252960000540e140140083c0040c941c44403400706100c0040d032420f0f030407005151507800c0440d044c0742c104881d6014803124141801d80c0340c141d0800a04019a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 466852868 1250 466851618 466851653
    0xd17030f071e09090c0917070f0f06050d1d030a0c05250b180a060f12050405030306011215140f060705120f0d0c02010b0a15050d0216020405010f03 65
    0xd442e0458040740741c1c04600340041ea10750714800a1032008010341034a00e520b03950710160074002410707400f0294031808240003045841510540010707135200d01d4440031084a41c011a80000c00900c030072000c44026400c0084c0c1038503010702808a0402c2007120a041d684600304200c0401d4072a541c04041280c01c2198100f100d410b050742c08a0380000520405070341c461031148802410010401041c0c0a0326005010180c080092200a40543e100700140809071441046030110f610034040c3e6401c10003d0040700e1081c0c2e4400043c602d10b80c0d81784c0055640501d44510107000c41c0e9100080c080e818040b64082c4080c1000d509030030704909144081100c00c0403150400d50199009200b130500040d000070301100d960499003032080c1c070b907060316030745983c0350180130300203009039041c2001d00c0700054041d8400100070304184ca40c11b01c81925140d000c41e94a00c9541c1310400210200b0071214180100e6000d002d00740384510b8400b0541469800040a032a801e0304280c0e800440c20204104100303001704450080b18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 466854118 1250 466852868 466852907
    0x20a152c1b03030a05031008030703080106020705010e0f0618151308150f040f02040f0b030c0d080a03020a050d09032d02060133050a020c04020c0604020d17030f07 72
    0x40c0d100030030f03200d0184500c02000d010703000c404205090041000030000d05501001c03603890364264100100050000e1041c0c5016005440300821154803800c690183c1c0d43c0080c20020343d1045010030b0292030790100140c09134060303904202840399904d0444103442125440785094565015500c8035031150402c0d0f20a01550344200d11032203c1001e4010b03003590000d0103800c0e0790007a80d100d0034190802c503e4850000e6000d8a051005200d0100360f5104d481e0f4640140d00322800602d0020910088905124010b4055582480090100ea10903002445c80f50042d107407490600f10701c45d912005507551044120f020501400c0003541e0f114200240d2070b40e0183c07136902c2c2c010003402c51902a489003410b020300f41402404e81007000c94400003402052105101c00d10b21040303014a0940108183c01585514006018484007464140780c00d00030744182d404140d0250030252141d600b042426203001c0380446a0b0340603500545800d0284402645c410b404e07803c5c0c2c804142ca010100241886109a0f841000c036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 466855368 1250 466854118 466854163
    0xc02071404090b061210021c0c0f021c050c030d0c030b0109030b0703020703031e06060807170a0f09020907021b060301080615030309100e090106030b01020a152c 71
    0x3000c00c4803032a04108190b40070035030410803c1700c003410a210511440105400000e80b20761905401c100d800544d02921400c01c0340500b02030b011941e1103903030344007200141e10002a0400225101b4924000090141003151130020a001081d0940d0011454140c0351561540040d5805e43c041c00b40110752582441e12143c81d41c11559810402c2d08050300107070802d41d01180c1c40c8100350003a0301002841040c40320342450030048040d82c03400f07080700d400f40d07000192a41020419041c02a15271100c2140c0c1e40ea44103040d03039a206e101c14002c1a0101000e00c00a444008900140c0c82d800007550150b046a400f4061004010a0a5030310030159400e05024100400042040200200d05146c100e06010030450f120078004000901e54000e0080b42030b4080b0522100424081d003096410469030016240040c039a1f0b41d0700b0040c3e007151080a040d9000d60483c6004100041340c1400000710000d0f0f9000000700880e421524420200140058502921312a0fa0141c0d008104210483c0844c0340302e064565903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 466856618 1250 466855368 466855373
    0x623090d0309050705060c010c111603031404030c03050f0607020d05090906040f020301090605130204030b01050d150f050711011a01180302030d0512010f12021e040c0207140409 78
    0x5440341801400e042603a901c240004008050107441c000700b0f8001e21171515100d00184d414000e18211a031240440c0c07440d0841c18507242c0208040f131300010300109a04585d49541c80c1502c0083c01e290044030640c004100210014406441100245015100900d03000e040c03070030040d142c100c000e44854290347c0061540c03010030758890201c81d031000056032036001d02e0700c501e00802d0107012291401090036002200200382d500c8554040d8048800413210040710005014201c41244613501000e40060030541c01808582000840c1a8000e4070802009006812074014201150300048003a050161150207001c54150b0112456503900802d200030404d5450324a200c0c0411400040d90304d06101d0150b070520341c807044c0c18503400300440c0c000d810ba590a8000100003841644031b409440c4031880158008520301d08015000d0b01982d5411000301f1001d00b0903001c000042c95040c94200194010b1626038034182c44a00034598600100d40082100f0380c102020f0340305800b1005210b501440c5003840e000301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 466857868 1250 466856618 466856623
    0x3040326010e0a0f1803021c03051603021e03041a0105220e12040806040201090e040f11040f090b1008150a020c0c060708040312050c0a060b030712062309 68
    0x204040f64410008403401400c10b202c0240c000a4121501d50590183c094203058001c1076004107203070b40c0046401001ea0059080d81140c1042d1014504104450f8080d004140a03034000d1485041c8050840c4e0342d0384000b40c8442c042e9100b258120360040c0d0055282c205100003805e1a07015020803144900142480001010082c11210000d040b0300e071640510208507000b44030120a4007442d50300d040d40c66490f0050703244d9844080d14200d00185074840c00280e041c092070100e078041d076404000d45030b1000361501d4900080350502c07d001d902666030b0003102c08500c0702d88241582d0030712540c4000315510306151070703600340c0c101d41d4805030041d0410900b403040c0f801c4910300d1a52140082c00c0058542c03200c00700e11860f000801c0807554101c0800545131046c0030034900608102c13889500e106d2042c02074064112814002e491104240d03a00c080001030010300d0315044a80300b80e82c041c00303c40400740d5400c98107109030030b883e01c03c0d41e07103da403190080c6035080745d400d0600c80884140e1504030070b030404941080c4d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 466859118 1250 466857868 466857871
    0x6030e030702190510110c010504050a092003010e04140609210f0f04180c0c030e030c030303131103010b0102030910050c031305100305061c02130203040326010e 71
    0x70f100b001c42082c104910500300340004003810002d84002c0c4074400d50000076190b039082401d802403605c19190000f10315031040782140c042e50000740003129403034541034000e00542201103000500c4420040e0b2030805a44004c00f031402841c0c2c5000105030790410303041c0791201080307080d48100c0c40c2e00054100500c4050000f116418118080454910400c2503081a000c900807110300d806c4080000840700000d403101000790060701e9180440c03c00c6030081d802d4000c100c444c1d014102c000302d103551a120340424041c2d840340804070704c080d05807403c0309030350720010382143d00c220368a4008222800116050140b01d142840e1a014150020811600c00f200003079624028088114820365240501806103442030701550010174001040f04d0304d03250102c100016030900d0b4001e603405140300b0182c401c00d481c842c0c01030a02440c4081d004440092036050f100408102d500382c2a83c022490041032558a0010310003188214082c0c3c1e40c00c00d0b0240001070b5461060b610340f106400700042e4800620510140d4030b40e05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 466860368 1250 466859118 466859123
    0xe01080c0a0e01050c010504061d0706080f0a09022206050301061d0712060b03041a10092012040512070314090d080a021e07030507052404090209090106030e0307 71
    0x1c003103000100b401200c00c0c0c4507692050103c2e509020500080011603000040d09040003405003002c41c1a060b84140e5035141c40c494600001c0080740400c142802403e111500b20321780002c0030403610302c10703008102000c8070865605043c2e0356501d158400c00c070a9105a102400c4110000e22141e440d1200710f40540f983c65010050050989000c00d400a00035410f4490448541d88103000741950b80503041c1168208890540b014040c00d02c0e03c02401c0000003085104030300e584c1e2089141390405c44100700408540790190301200c1000c1c515030103131200002400a404000f2040c0309149007500e40a030501c40d4400320004204014441500000d0700954440340a10702d03c03000c40c0d1034461800c0040c8a200c90303200c010348403513030005142200b59404034040860640c0344040084002050f4103190352100548005002a01701980c1404540381c020408000b45000140c2001568403001048601e0750003948a06d8241c1d170b00080506041c20446161401090f0f02e007820082c00704c417410025100c1c070800100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 466861618 1250 466860368 466860377
    0x5040b15190903020d08040e0c120f060102012720060409050402031009110f09061c060b03071205070503070e16121b08100501090b0c0304180c0e01080c0a 68
    0x14007a01841490074034011600200350004107006410006084d6000780280070420641400081d132100d60401110070080c1080c40d22030f42a581c1c80c041503061a405014603045540b1501844104d50710344580d0103101c64a07401e244034000d5a45840b911070300881541c994580b8401c1c00282c25943e0328415a02190010310b800f00d9185c4c1e84d44002030500c6003c41d403002c48035103030031003010500c40151b00040c60180265107000c0268240c1d000c100010000719400c581c02281a03244001e040d41110000282912070100070030005520400030781006265000002c58911001050041c41800c100c00c0c4020802900640107460600400e5070f50326400030040c80f42038140080701d942c51440360020b03101c5000410010040803030042c22005090100c1064100007650b40008600b28101c140614070440700143c4030319214610341003107189160003a401c0501980018403001030849a10f0300034600381c52031214002401040018090048907482c1c040300c2c10072000100b00310810412a00300ca02003460703400c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 466862868 1250 466861618 466861657
    0x170c01080403020f030d0506040f050402030c0d03031b081b040e060d050c0a0e09010f18030e1507050a0605070e010905010e06040f1806060f1b1406090705040b15 71
    0xb4140d2070240902c00007502440005a4071101c07640f40e61202d40108011201408806090300d59582030f21002e99000c3d5154001070081241031030804402e09600c1d211341808070342c01c484030020302c8001100504050110703401d0801c12480c0c0f2080b100c0d810382c800d08660b0550038141080c4050305182c400134180c074061a81c142008003441020080781e1000c01004001444450b114002d498500400340c1d5a0001e941c08d1650400c80308505028024148044910000b103460303103a142240c1a00516906682100400c1069035480d4883c40003070030b009010340b008081d441074902c1c050084801c000c01400c00c2140e650350301412a80c0c49020a41140c2091900224420000300020700c507100e01ea00c803180340e039000d0000042090241080c00c06100740503004101499444105550f5100001e503224001220070310020448a40c10030034058850148030b49500c4d0760006140180b40210a90301c43e50a94000c1c031003080300d49013900824101681c00d5420b0303070381d0200c44507404e401401070b44100e040b1050b0f400b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 466864118 1250 466862868 466862873
    0x5091f0506031b2b0207200a050306010e091504033c0c1103012d060b03130b10050102030409110f0a05040e0a020702090c1b0d02070f170c010804 64
    0x503015015400c00c618210303038440c1c03446240b031400d01c01540425528060808113524602180c0300b6a00c955810000e101c1d00000441d044000c84041035800341d41c4408040e40204040d20304110850180040c07001070201401d0801c45c2600d450029403036140d00c02241010040042d6010303000318200a141042180c041d40021292841c0203402d903800e1200ca14980c2d4a642000d502084841c2d03101d00404d01c07102040d0001d8241426201010a5146903641220041c0182441c0d2b02e00895018a809800a015603c8181c20b4074150f00c1501c081012042407c0b00405220070b99118a41104003000003280d000d18010003c0d4403802103200b100e036020350b1001e8420340300350240c0032140d03604142c08209a6030800320501414070f0b0401c0c0100d1a6400d5424002003850009208540d041c0c2e13002403242105079190351442c041e0b5403042410401c009186075040040080810140302505c4ca150094400982002003941440181e07078849002c145136900c030b201d104400490038841c203810a2030940410b69450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 466865368 1250 466864118 466864141
    0x121512030e0103060801050c3001030807050703080a0306080c040b2b0507030b1006050f1806070c0906061106060609040905070803030421020d090b09010c0b040c05091f050603 77
    0x117500460542d400c0800304410001c0b41c030001c111030142c804001a40b040e00400383c0121100d0201441c680c1c90550006102140d500b0018242092080303040303c41c91034481d59000c10a42204c028480447e07141c0d5030902c0340c0329060180c403188620030b031001c108400d4180000344c4950300100f141000100e000c8100c0401d07514442c214a003043d001011070b42d03a03cae80c0b454040d03508a0101c420030442d0100040c04a1401c0c07089003121100c8000c040d10a007000c004908102c24619400a500c0c1e00800c1041460001a03e421816004240041e0001803ca18088014282000e12040900960802400c001103030360b0b54415916924810b0741e0010b044626851f0062911f400c81d040030810f448080100410404948013036024001c844050b41c1d1148915071059076100c41405882000c1404040184403481da0b4601030420420149810f00c40e54029865521112000359010b0b294800765403400d102c1c1d41818941d19400c00442c9006c811299240c99150951550a00507288261000404600310403500c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 466866618 1250 466865368 466865381
    0x80414010212010305160f030f200d0501091506060c1209051306091401051807030609060f031a0618070c02040204081f020301060e0d0609080a121512030e0103 70
    0x4000102040356100d04200c0c6c1d03240308076600b02082e080440800701e15201200000d1040301e0f445400406011301c1c607a10385100383d00383e55590745500182850962540d50701c00307000c14410f010300000660010941082804454214801c4103450b0500320304002e03480e442132400f500d041e0415510105495a0030040310311299030751000c0d620104020011528103e10340c800800c07034a900c1000c024a220f15418804880001d1041d00c0d0f0290009420f22b020019000a80b5230041d10344c640000d00c3d6031102d500c0000c41da829000031700e044200d81d00500c10881c1d001101c0c91541c85025040c40d030f510700500010802c0031010010050080c0b00400703d0019400b0350492810154018001c3d503e1315144c6801c01c1d03494461103050500a43c1806803002180402d1080f06d0503100c85584851200c1e607200180400300b84c010504580b901d940e00d040c100441c1c10132014251911491399801c6a5048a0020006980c6069101841c0e4032010404000c11280e445003400481c0e03250030700b942180002001600100300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 466867868 1250 466866618 466866637
    0x40b01140312090301091212060e010501050313020f0312130801050408160503070b1513151703070209010b0417010c050a030c0315030c170604020a03020904080714010b0a0e06010804140102 83
    0x7187c2000c00d050b03e401c401100030400950000700222175440301c018182e81801c0c0308650104904101083d0012203a100c2d01c51064006010071456142400110f443e011102a00d0030311210003045150038a0102e061346402000c07204000e0209042c591100d03055446800c50031060031042050400400c0014400d68034801d1308021120303401c0c68100d007400408807036025403510a02c0385034032115442c403207803180504500302200454022400e044001c0002c580f044190341d0644018030603180180d886080d2203001e030a18203803854541d0b1800c101d5134000341c042002c080959050100d00d0482592000655032525614540030581d030b920b15409400801000d81e944044044000700030050044498402084818030711b405036840d00d44000c1c190b02d40f00160307402980560a2002007000d40f0300100c400d6000750141140b5841d10312642d07180385161100c541642c4585c0d448228007061482c04000c114000c044c9154044081e241050000300a1b0b000100002c040e0444480ca4900c4040254155603400c00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 466869118 1250 466867868 466867883
    0xb0102060105061b161d0906040f140a080708070201020606120d0315030f0c0608011d010b0c0c0a090501030b010614120703020405040c2c01050a0507050c0d0b040b0114031209030109 80
    0xa44403107101c06c00c80c19a03084001000c5115000c038000602c00604603100300c0d00204502131034152075842035090203240141d81074921440e2403500100e412500184a114440c40c14940d070303036100b40300190401c6001004a4886c50208034001070000c4081103035610b0524038600019401c4d00c0e030f2a0b102c5900d0f4187c00113030241c1044040c400c10401d8a00540e010780b845d070f03280c061040ea65650002c8905018210680e2030f014102c004000150789035010340340d13440810043e140f0009400e4041810340d8540d5021074104da803918010018044070b0300701507000d0905450545d000040380c1407112950b20401900081030240c5d500001c0c4158801c0e07041ea00684001042400fa0209820004041e1550800140da13000ca010201004105407130403030049008040c1c50702070414081040a940c15006001c00b901e80b80184a240740b20341c2e803820300c0d0500c2c2521500505065050034100380c15840f105030002076101103485556004c3d42e90014400040204000d00c441d522503592010034050f1015030303030050810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 466870368 1250 466869118 466869163
    0x7080a0f0f06180f150204080a0303050c0912060a0c02010b0906010f090e070f110f071511030403060603060e010c0219060f021207140301060507060209042d0b0102060105061b 77
    0x11082c00078204004d4014081164a00d0050200c1003c922a44c07142d80d030144d004d00b07903000c0040d009801403030340301074464195814042800046180c09a000d0b80c041c0032a0032000410280c1e020512402611095038030003040001c0650700440c036071a001410b010f05111041000c801c00502c180c281c00c026041240d9000c6240c10300d0310028001402d0a1207a0020440107141405007500010b01a4448503040c0020003443d0315045004644180c42d8488004200301e02d118001020401c000070002180b18010001d40c103403560400d58100c40314502d9652141c0d043c507614004541c0c0c00104600382c100000e51850b800100f618258005000441c05155014000303d801d0071170101101140744121080d490f49513820200c113010300c01c1c41c0f000340140d602085090240c01c022882680c058152103c001d040021800c001100068070481c0041c4804420b40307404159800c12011401090344c140e80a0009289550410300050031b140a0901c50141e0000100c1c1c110306808804c01c0040070002c112503012540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 466871618 1250 466870368 466870373
    0xb040c0203090a050105121513020c10111216020f1b090606030408030c0708071407050f06040807030b0604203a150f060c020307080a0f0f0618 63
    0x300c0e0031282e6403500c140c401c4074000400b0b50050381210781c0104420150411a9030314581201d1192042c01d0542e006140e0728840c41200075540b0084c9104080d080c001c0ca6408507105021007034440e1f10094112201050103240d940c0403001207282c2d0444c40c00744050310b14030000001286403492168401825105080d0810203150b0100c80502c0104415a41c0c0d140d550340e40c0040c8005441b05540007403142c401000011003021051002c0c1507010300c2042403520740591a140d000307128004241071102c640003120100304500d003040721040c0f965030039102c540c2428949a02561140f0721071001400001d14000080c080e51382d070b81e000c0c00760ac8958441d06400718080004090303540e00121612500741111000080070402041032080e164860181d541115003400300400740a4013550700c0003c3e82241030100421b64010309060030010b8903507580c4045a0343d045004151900000340d0051901c0d800c6000c004011440501c02c03041c14a0308070360070f001c5400440c6008001080c86a040e548541711041ca00801c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 466872868 1250 466871618 466871623
    0x10906020c01031e060e100918031103040302090906070e030106080d0c1505090f0c01020c090106050a1713061407090b0f0403150911010e031f020d0504120f0206010f030b04060b040c02 81
    0x14603135840211f03040640366035030801110600e4402c8589900d80e2000c00000030b12500c3e00004600869007624102603490b40031924541d01601d202c00580c1000003008000f591120300c540000108400900810745018051a22801d26000c004204070400d841581805003038022408156401001080f02d40340104c01c0b03d1304c85024420408141c05003101280c0503610008103803c66100c003c201c034206929060003984c907540084042030600900c040000009410390503141c0c81043c44642c102a207400038940082202c03848105c03411407408800070b0001e0341c0c3c0c4c0301c40204103841203a0b6000b0b0b510f0044034001e81540c000c2da840106209140c42210000b04441d401005942d442030703441000d01d0103400010758054011009164156104296125140d1280c10300b03100c81400800300140b42441e608103100a4410403542075138804013101c01d00400741d40c000508111040b1034400b030851941042160502e1030068403004e81031040c688046010b0050716440b035009600018000c101c01400f15102a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 466874118 1250 466872868 466872871
    0x10c0c0608010513060f0b0901020a020405091b0105030903040603050402010215010620030a0c0b073c050421410a03020c0402030a09050d020714010906020c01031e060e 74
    0x81c00b40c5008008072002c1561400380c48107446c625142200c259080c1903504042d038100706003450441c49010740c0400503851700c1c400d1900800e281406091030b4001c001701e2400c080984007071981040810000c1105a40000c415035003aa0321903c1c01191a0303d541c00100c1c44d2140e903010882003981c000c400050a20380081c0840107030500342040c02041c00c141940c151b1a80145c0e01072001085a4001190000300d0b040c0c0728560200813406c00ca01c090341c0402e4440f800510510001c2001d914855084200c00d200c03460451243e602881d0952030310703050141c0c40c0c8800d8082a54480ca00e5885e000c0002000701d00d0700d0320b0b0041004ca120054403550b80300d1943c0098010b6610301d0131580d10007000b0030000000801c940105980680003070690501541c00e01c8002d40c4001c00300c05205da900c80e007890005805004942c1000040e500504c0f0103402e00a80e10704580004410320305020941c0d20401209401080304000c4c0d900c00d09001551440e8462081280d0744440268441c0c00c1ca82000802c01c0000241d149 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 466875368 1250 466874118 466874129
    0x210111e04080c060a050d05071b0501020d1103011a340c1a121305010e06090607020105220c0f0b0c162601020d0f0506040e0c01090b09010c0c060801 66
    0x2a1001e02d07091040c00005e100380c03070300748000800821404d4101c02e2540c1055400c074944d03103450020300b260500031030701185100d00e0071281c9940009200002003418060f56039907510b040d001c1c030306d1035140407242c5000701d42c51001c4030505000468074104244070014481c044038401c00f00980300d503108801c0344540481c1140126840d0301000c1c1c01142c0101c6401c09024a45038234158689094880580c10409510090550361150611100007000600a025070001c2240c014000c140c9424991812401c0c04001030242d011a03251108000d0150f0700322010100d42136075218062040d11181c10301c00d40032205c1c0e401c00e01840d40702c001c0029607860204010054031540c0000e95030038056403020404403401c1441501e0a400b49039045103003100041c0c0d51040003164041c0014030b0001c00e40c0d020019249250300c034204140c0c0c2c1d6000c000d01401c16000300e00c84950900041d00c1c40000110010307200084034080c0c050035403404241c00000c0d034041c2c600d1004180d00800000d000e680c0c0c5010040c584103003400752 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 466876618 1250 466875368 466875373
    0x121514061201110a1d060408060612030702060301030611090325060302030606041a07240c030e1b0427050f0303160c03031112061507030210111e0408 66
    0x34589440040c403a0030702c3d5003240100e4900c1c0088200c000c0311956591140480301a9202111104546c0d03501c0c0200002d224071809040e2910b004400c00c034814007001042044c64004201500c01039403850304580c107407607005800241180d2403907030041c140d000302c03403c09805125480383d4410280510740341184082c1100b290b100e9050b11038400f11b00b607020540d01a0b421590a000911103601c1c40351020081c8919000c00c981405d0700c43d1201e01c010031641d8a400445040d140c2e041042c440c2c3ea0240000806c241c3c102442101b41d0002c0c540e42c1c640094600c80401c8100c0c42c414101c607502d980110240d4110890040440c02c40100181c0c424540b09104652a10502521034103141002c002e03a4403131500b20342d07040040c1b40300d43c1c0147c941d4403041e40101c08040c3d49281005600c22030304050107103010403040900852409a050001000c24100040c420321024810200041c0d030014150b03144007503c04d80400c6018000107180e2190143c1081151182c0010b200401d003030001304050300c115002c00c1c4c03c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 466877868 1250 466876618 466876639
    0xd03020604050c0f0d0b0703110307051321020f0a050d050102130e0609010605131203110f030313082503081006050a1205070c17090f12030412151406 66
    0x4c200e407642c0050324840d0016000740e5118003044041000c95401082410045140b0f602c00000c0320342980106d40e4403010580201d0f00143d0700500807131800c0940000c0b031600d480300e041c0e00c071703118210100140024480c4488a070545a1032b1240130000d0018500076103900c1c07940d0754510f8000c0c081d400c9110206210034030920001000c5500c0103100780900006041e030000e80c0d0802c6821134056100e040c0d900020500c0d001d000a100c100d040d100086240a030341d1360201c80a440807018104550f030144040d4607032041c020300c40c4541c0c0500d20100c01030384c066003840c0c0e240c1c01302aa01c0c00d44207140031100c5c2d00300c60650681d4141508034101038460f030070600b240600c994035010241c90a016440324080040c0c02806440200300f500e51042e6041903890030000c0d10113035180c0c0c8207121082499845007907200003060078100c1c2d04150381a000f411004803200042008100700c110f50ba0302a80c894020a04900c0006009000c46019082140c031000f08007400b82d103c509400004608094824501a408040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 466879118 1250 466877868 466877893
    0x1407030f1107020108040f1109010332030406030b150d0b2e050921030a0207050405040f080304081309050105090c07050d0e270601020d051206010c0c050d0302060405 73
    0x104442c010b0758161210303c495182c4e900c070061484004941210050038441d0210116950440c4080c001d510949140b103001c100a0461035508102681c45000c40c4460748424903800b1000c41a14291403072440c00080540c0c0c0003000a40e5100d055a02c40b61954001551000c1300c00a5000070425940649101c4010108040340400c07181c0c0303818110750500101c00c102031400b80701d60010f0200d0103008001c0b0454203645406601c02201d84465081264000a03090f044140c0601c40800100343c2100e0130000c030329168466004494481c82c4c024404103002000500b085018000e444581400c14502c0d898180c40d001c82600504082c0100c1e44100c11007800101c151070420202e07043c0591120241c40035411309201a07a1001c4040542d0303500c40c4002d001844240b00c2603a00001c03030000b0b04c06a080328140741c000603081c00a43c82464042000410400e42840d82e000892030300700f1000e203000303007010070941440e000082050b00210341c840c80d01c07a0b11500789980000c120f4025802841613416520800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 466880368 1250 466879118 466879151
    0x405070506120601080a0f02120f07020c01140d180804030c0b0a1d240d0c2f01020405130c0f05030610030506030102120103050706020c090c030109050405011407030f 73
    0x11400ca4042c103102c28000f40907940b00b20205500301140c1d41c008190031a00020701010b9070840788541c520115540308205d540d81d401c2d80f00c160403c4490025203050806080002e04075020455640f8550000240207458803070b042d400001441d4104201c580c680c41249006080d40c0c3c00791000392000c03502403502243e060071900440350580003548400c901d1100040081c0c0c3e2181c00507214950000c0004000a0100c030515a507064081e01840c4441c0d40341140c40c0c10b04c08903a0070407200020028002c14000b002e403078851607032090255000d04c03400c0c3d2640046001f806480f0720b80150340c00c801c0400c0c503890343e071440b80c1040f5025550703500c4480000b0b15410081300d90f400110390080e4003000304001300302c485000e03500898010780041d0001d85482107035561010507000c281e104a506902146080190075418080e100d103415086665907001e04100b400c4a80ba80018041c1080c116514070228003007100c00d500c41104001c0300403d1170303240d2401d00809001404040f40b0b124440703080090100949606 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 466881618 1250 466880368 466880377
    0x71202090303160302030a39020406091e110a140c0f16080f0a020f10090b12090607031a01110a060501030605061207050d11010c0b0c070611070c0302130f05010b030405070506 77
    0x150100c0884a0044080082d540344241c08c00303a822654a400100d401c2034280990b401d45486846100400e07900354030342c0001c998085c1c1c24283c0421080c00381c820020b0780300b8400c044611029400d142c6908580d1081820643c8040403000c142c4a6980100c640c40400380040c0202c46180003070707800080c0c12820361038481081303000003584035640012080c41490300e0281c50a02400d5440d21031501ea0315000c8144107540070130100c410140e01c0c0820009552000c028a80d80720080d864103000742d05180c00310300c2031144060110f6040c0840b2115807410f0395401c001507440c403038020005207c1d55944c0d09000d802068242d5429000d02902a80e80b820301e140007440c042160000f0b49402242030b119100e0f18130030030020507014100130002e111000410080d51190b809500c4030140540d4400c5031749000ca04035810b00c2182d071b4000f601800840c020400c010410401c41ea01642e50000c41c0410042c000018408414012211031070040041920a1a0800742d40300d58810021940f0040d1203d0400140b03026 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 466882868 1250 466881618 466881677
    0x8030a0e011d0a030b0705120a0b1c03080606091503070801091d031b12120a05060a23010201020c0d030e060c031603020a03090206120703060e071202090303160302030a 74
    0x80070101300001150f864180358041150f14000e410203080c100da1580d40d600589024a2954030351130714028510704503400703240e44a5101c014140c134210903907000d00200401001e4910071a0049040325007034036181b403c0e8021041d00404640d80707144c07000c00505522000c1c0184000e007803803c142800d040500b8081030302502040c500443c100307178001146001260710607480e00558040c412144482107902c50240c10800d2000041c007095184c07040c50f850450300700410192007407280402c104116281d1070541c031410494047d805c0d09203001100140e000e0700c42d00001890500c1603140441845500d80e0084940d40c03000030a0311483e80350140180703005c0c00251456001c22010220380582c09000ba80103040101d41c90074003003051070341030300044c002d60084c540091000c0d024104002c440f99140c41000090144802d11a0080c101004010042d003002c1400551180d40001c0c20041c564040090b0b568904a0070005c030501303289460004d446c0d410104400000c20000030b4501c61504400c000c2c04102da9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 466884118 1250 466882868 466882879
    0xf050c090405040f050609030a0f0e010909020703090f0810050604330906270e07120804030605070c0308070201060518040206120702061005040b0609091008030a0e011d 74
    0xc0d02002007100501014000711a080011400a4000b9409000d0a40308080d4100599103c1600c540064002c112500210080181c44200c2100580c0c100d505c001c16030b42002e43c0143c666229103000d81e01c4080c1034120709440000c0c100001010440058041461404079500b44070640340c060901099411419010480c880000110300740852400d20070241a0454061150000d03500c1c15810225100d0b608001028032404c0d5404032075400f4400314500d0b035040804100134a86104240075101d050501407040d00e002068190014080315070203542c00b640c1c100700308010390b00348800c000d40018014641200495482c4000882150040c0300764001c450010b0b02085042d028807041b22a8003e000b807040342d02c03e80170f1102054802d0f0f21040d5034801e808580003808a41021010386601c10900d50203103100d0380c1011001d51130340d1100e0041d1070390b02e0350658401071135417074808030b20204812940020b44188004141240742591107104144618000e80760300d800b420040e480008069801c82103540c101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 466885368 1250 466884118 466884127
    0x21207080403020d050a0b090604060c300f020f03060103050105060c10020306120a0c0e01050a030804090b030708060708190c0804110303040504060323010510180912050c010f050c 79
    0x50038604e10141e0914824810b0303c03c5981151740f09903040c4016100801654402000c107c10402d1522944689441e07905018a04a402c100403588500385540414a0000c02d4080200c0e03034441c503005070303802c0202008290749805510900c42c80540040718074500180c00c0000019441c00c1030f10490340b103640d001c8013402840407000b050710003035400504801d0f009544101ca40c1803402c0180141c00c1c19911945144240c280b0300700001c1400803040e046240f103001802030402c00100b9280498048410a07107004c00c0790410fa1000074101304081e801a0003d0013039400308420b1560000d0b59510039a610b911000e6040540919001120000c1d070301c09011900d03480114000c502c01c04518100c0e50300c010122031030035485001007016941d150b40304843c031410141d40122142000003290f1441c402d100003c00161a0015425518880034440c08101103681e0300345040d50b84003500181c90030380d0420b200b42401040c40900810310780c8180201040303946003003114a030800c070a00400e4002c04021344210b050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 466886618 1250 466885368 466885373
    0x1a1c06080a030302091c08071203020a170c04050a0602071719020402030a09021f030b09041a0901230103061b0905040228020102090109090506010807111905010c021207080403 77
    0x75030104207043c1e801407280e0109030411b02050059031a0070300c5410141e445007558642031465114580c00d1005050040c4400506558020605441300845034808001e9480e0111842410b2103560800c1c0d03040701d1204800b05d207490300060690102d80301c1e41c0c007a8145c1580b480416440d1054004041d007400302e030b0022240580740903000f6641202070184c001a0801c01ea500003000b0702d09000300d4940080a410f803280c001a054403070402010340540d41c4040074545030340c81c1c251440081c001281340c1071580000c6507040740300350300c18030082c0d0311000f00b12000c9103501c0c140100d03403009200c1103d0762424048400710308042c00100c41c1e458425502e41140040c1007100b00300294216440200c0c2e0b94a000c40310b109819844681540c1e01206a000180d44071900b60004100e00300d5a00030406071800c01d0240112a41e200081c160300030700c0c5291548039051200185401c01000280180300644000e4620050010640c00404404c00725002c44094941d10400f43c8150700401402a180d5031044c48200302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 466887868 1250 466886618 466886621
    0x20f060106051b010603030806031504080f280903151509231314031206040507110105040c051e06040911070206030a0510060c0b04110a1a1c06080a0303 67
    0x800002c0c00c1d0f4080d0705001c00c20400e421201e00350f109500103000c002c1031200700d04091250003144846408120468501500c4606861040401502440c07100042005401c0701052a45400c09803035114511011401d42008100041e213000c00e45000a13100d020031485800f03441200040d105081c01c420b10f19142001001c010900e42d4500f02102c0001200108204d4001d205d5038403c0c4140c1b540c0111000aa0400342686000c42d500ea1000780d2041042c41840001207040742d80c410001c0301c0201d42075a8115085420720b0000d91100344540c2080240f0040119241c000001ea4106403641d01d00787c61404208049101d24001c0315030400d40801c818401d0a003030790002e400144c0f0f80d41215203040c580364003150003540222101084103599000b84480c0d00300072120b10005054610f0122400c1d02e2545800b40404005400202100038542d610503031911041d60640003000305c5a150741c2070307602c2d00c0e1691079a03501c900240d00f040c048094800480d00344074400c51041c0c5491200274200c10400e9a070650 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 466889118 1250 466887868 466887877
    0x20f060c03040303021005070516061a040f020307020f070515090d0c06050d1a09060103020c123405060705030c04050a090204030b13030806040b01050403021201020316020f06010605 80
    0x6820050400105161031010801000110310960003060b00c400c0b03c0c034084003226030180006042102c1080758822000c2d90b0000909101c0d00b2001c001541c0341400f03194000b00c000005042c1d04541030810703a90038540745078051485144603400340c48680700d44e190700c0c54841c3d0311806925445464004484c15000224000d02607080c0c026080400c030f02401c0e180d00c10141502c3d0700000020704c0014940c645c0513454010100359410f28440c0611285d01c203400510b8008000780187d0400d54040381ca0203040808101c40d0801091000c45c1d260303a500481001c0e0349c0d90000c44a4110082180380711042665103001e2404e141d150040c000e00510b88a91504503500c0c3d2001c0c1c040b001c03145003030002045950743d03407012800901c065a001a502c41c65850320309003c2500400740c1036030040c050321a00c08207412903003450307000b5811100041c000c1c8443e0016500da00498102070b4204142d01c000312028801580250b0159180700341c034060001d450001240c1e1b9000403044142d0030703007185004000c8240140c001e403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 466890368 1250 466889118 466889149
    0xa050d152c15060d02030a0b030d0201050c09090712051006030b090c041401020f1504210903031b050106140f0a1a1308030307170c070f0b041b0f1406030601080402 72
    0xc3d49003072003020307503035040c1c0e0815203c2201c2036568501400151070200316070f000c6004580003d015901c0e01400740b90303190040f4016580035010100009401d0351089190072a6100c01010800c02d030b050012842c110241d240c050300e0040382c541008244c0c0d07031a044c0c640510030158400754600d0300d400d0500b4242105007044c0741a0652080e40f1058038054030900c00e0100615240011484074501030510403640c04504000783d01d18202d0407690040c8513448030b4100c080d66054140f6510a10140d0741c0d10f06041c074030a001400035441c002c4042803009000001110510086840c12683c038070103410080040b80b0344c40388a1070740301407426410f030603d04d41c3c1c081c0c2100c98003406c0c0c0b00b881542d6010b0342400e40d03200b01c4440001a0b213000505c01d5220402c1455500010005c4045040180e1a030340d4031086040118054103280b0810001804c12902c1e41c02070980702041e0003140403141e0741c8c2d01000440d4495010b0340061030000030340c80400d030401805a07842040165285003181e2910380070700c6882106410b60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 466891618 1250 466890368 466890379
    0x2090402091201140c1207211109040c03020f0301120f060207030513470f0c010f02090f120c040e0703060e0607020604080a050d152c15 60
    0x884201c0d40c1d860b089286040d590350004103204801c10070100c41804010030f01c1c0c50720300050020000130003d40e00143c0d0300c074107107040c0b030686c41a1403014203602881c030944503130301e41c1e082980c03c141c0302010b080a403003684402d0301c06224000c0c0140d800e80c1030740503c034105a282401440100010707800b500303100001901803100c602081405480f403a05a030b02070541940450400940052035406060854004000201070305103c1d2500192400000c82291800c1ba040c0c060212442008081110040348000c150302050360f0303c0c02d07613204207015500400c404103441d5180c03012410034020a8000ca4104c2c2d0b100130119440300501e0740800c44881010041e0000300d2080701c00210140e00e513407050f14490300d2880001c1001514615140c03051710402ca9102d00c154100d0300600115940000d00141c01580c400d17225615003a90540464403401800f1051b0640c9040c1038484005d145220410b20645002d040b4900600040d28010703002000c801a1f8081000014000944c5116003402071301c545a400501c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 466892868 1250 466891618 466891627
    0x10804030e060d0204031a010501080a0c0e0a03230d020c210d080105101b0803220c06082202040e10091407150e0405070c02030f160b04050a0902090402 67
    0x1c01d910350480301804030f0b1107600241c00e0007071102c14120104450007040340c081a82d07043c400001d00080c400303041e94400c81e0719480c0c402e440b2030040011801c0f10b000900b0508407945d40742828078041c030101403000318006402020249048000c98040c0c44202c09400a001d18074040c1c0c01c1c1b010324000554094039000414500344078100d0140980b1519619a5446000a505200401c80350742040000c00003402070200d130011407050708a44502c3d016402400c040d440c1d94030140001480c003030081d0010030502409248800300049242d4071b03410ba540d56510343c421503445c01d014280b444c40384425441c444510303480000052400c0e4100e201070b659120b058035000c00109402800b91740001004613009505c540b40d1011514042022000030001203821401021011074080c00c84d01b810fa80c400d02031510b4900290b01280120a0580041d0b4081c08450001410710036664441d0501d14104105001c080b0000809000302405d45d415240014220343c4183d280150800095000c0d58815801035001d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 466894118 1250 466892868 466892897
    0x12030703140d0204090e070303020c04020c0a060b0d0b0712060f032109090c0504031b0b0301090f1407020c03070e06130e01060312080a06090207080417010b041b020708150601080403 80
    0x581c070350340f4200e44020b15400d0702317502e4080d081a000c211000c2c0103920503c117601c1c0080300019048803841e08114005103600c1c404022030f403840000b001c081e2019142d2400c0c040115031100d10420009402d410402106481d43c1e4203219540c0644400380050280700c2d405080580301c03801c10140d040c410b0400c900260ba60751180c0064807003141c2000c0205401190400034420800c0b4003402c8000020036040119060283c0f00e590b902042c0180313031b81256240540c0300030820f02d03405208404401c9500307403ca8500420000e40d602c103e075081900901410b00e0010f00031310b90900a42c011400145034624031036840c14440000e0035004218010303992500341c00004100e02c58241100380109503250450341c5812240702c002e4403c03a900034000340344100129000b003031170442600d007039800960310320031441c2e41e11070010f014000e120002940145455400d07a42c0043d203201311860206103400b41e07910180c1d1030b6110343e11031070700c11071200785c0d407500400254603503100e200301c254080e00ca07040050242540ea03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 466895368 1250 466894118 466894121
    0xc040905100305070b3004030c0501020715021902060402150a02011806090b1005130f1d03090a230d1704030b06040605040920060c0303040804030212030703140d020409 74
    0x1039100d00c18405e00014825105071094480700d144d2009031010801000228004e0850310754020000ba0802940e24016400c00c00e085d012101200e8210950850340c803a6400d1000c02584000c2d01c50200091101ea84590700b13002140151155030020401a28000c0d9200c42101c0ca0303003c420003500315547c0b000020701c0100070002e43e0071000c2c050301000900c18102d2400d0460301201800d1070240d010400e4081200da5101030424030021800c010102d80e41e4002c40185001c2d01f0441603880b450f03c942c00da0116120b1000001e8215501d003140d81c5c10b90f00f6034407140a130b00344110041041003122410300d00300003414190030f0030740d649109580c1442082c4854801584942103078200300c4242c1c0301070040c0100ca02d014020300d4003a020445041110768200d5031100741c3d190107003e415000e800300b8000d6441d240d0303c61054403001c80307010055968a10b801d1a01816551041c042240b08240342c0c40c0001a41318000142c0b55000c1d0b0684862054000b040034400c801c0d080800100c01c040c0c2c08002c0840c07071240c0ca = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 466896618 1250 466895368 466895383
    0xc03061a120d02060f090a020d030509061c06050411070b18100203090111120f22050c03010c0504050a090902061303030309020f1f032003040b07090e0c040905100305 73
    0x800900404482c801c4000d04191001e0040e1004d1814034041c0117200a01050710b1104560455041780700341050b14043e50103000c1c50051950000d03003c51100d6558000c0c400e0110594a4039904010b507a445408010484d841036032100080c0c02c050012900203905800304a800c01101c40b0b0003100710145082c1c040c1341c070100000c0c400c10039401000340040440c00740120007e040b40240c249044c40850803015103a01d4008041d011180b2281000c02d80c140784080d151001c1601a030002c6500030f88a00f0030540c0d41540540942c0258640b4411425442c4110141c600399000180b1000702d1515001402018241d00501640e200c40d04001100c541489035110700002c5201c2d131004613402d04140100911500c890f111640540d60a80d80241c42c101e1100354001007004508000800a41c4404038501002d00c2e8200c102c8881c1000003480180034a40000b20705c00d842e1a924610859101e038140914071a064405001d00c8105000c180844486078000541c0610095001d2104940d03e03212075103080f14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 466897868 1250 466896618 466896649
    0x30c06210f0708060103180209010605070c0905060609090405250504230a091506080304050a140913020f03070e060102010b0f0306010b03040503070501020a0918090c03061a 76
    0x211410819644450010499109000c00704400c07aa01c0d05010280000e44020b100c141019a28103441c01c00a110b44200010190042e12031403042da1600d801a0480d40404000c0e40c0200300108005540111030040c1b520450000c2c100e01e0805a9207801d01083e450080c000302c40f540544004450040402c030800b0340c00901a000c882050713441e04090204a030390311490000441d444045c0a20900800010a138012031007c500180039089401c040c201c285010400b9007c20341010400650000c00001038029200200c481034100c41c5d440c100072561142c2c1044498101d2143c10000d05010320145011400b940042c0c200245800c0c200c0010342021303090f40040c40950411010701007156424410707542c2c240002e8500c0e4000d2010880000d60b100c80c144501f454840c000030024042040a00540320503a60250080d52107559809002c0c1600800e80651102d91070b03000b100c1240c60045004e0420400d422512811826055843e120b000c5d103c0300f4000f0800349080b881040343c3c0d85404099030f40c5000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 466899118 1250 466897868 466897897
    0x30c210207021305060f06131a040e010e091f060b0c1f0603021c02010c0c060c290609040611040b03040c05030a080f13171f0e0309040902030c06 64
    0x40709441001290703100101440d86083c0f501d02004a0343c5c0b51490b51041140c0b0841e0302e0341d11400d4940d1740c0384013030940750030000080180e2900f0030087d0290320041d00c143d8003004801c46032613803106050100840220707910a810381c031140b007181e5114403910b040174a403c039000021803155140c80fa04419503118601c1403820b5800701c1c403010246400e44001c0f224038a40da5900740030051568000981c03e03240c07480e0202400321104151401c580c0244030700c2c07c2c00342c1d100c401e65030038941c0d403e4043c0c18880b00d202c055a95071040c815031a1221604002d403c140c68805258060985442e8103101807880000c204460f40d46d40d903584021150710a6001d80014100c00091035031302c0c0380903e03220381c1c41003041e4400e5000b81c0c00f0240190004491400340c500003800e5840c4940c1b030702c95400d10f500303a40c4810380c02001c449000c428501941c180100d2546d85071400a00039984005800c882a0301700c402d100e00008041d0014003102c0002e03d001d0300902c050600080c116648010803c0c009807003503002c003c1050702038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466900368 1250 466899118 466899127
    0x613060b0d150516090501120f051312050a12200417010f020702060405060a030605040609020c0c0a0f140d05070806070f05030f0c07020d0b07031e0e0d030c2102 71
    0x2d88481c060f969100035505041945548400c0300035002c85401d004003414803900300d0b031340c40d0300c0e403280c3c0c2c054041210000000d0141e800c1c84000109880b5041d002542c00c821100030010005004504440d010700140c1d85441007095aa00d03004014601c0c0c0c03a2400c004485030000c0400702c00000c3c0500054000007440500c0028210000d45c00c40e100d80c10046056401480054050380d922800e0b40d0440f85c003915400d1b030300c41c0e01d0a003c070700a00d007541215612910300140030400d80450780c06802190490004c85215840003010490554141c0c82139402d040c8400380c0c00d0160013880d5004804030389000e00460583c0120b6500e0780d08007049074121000341d60001d020425481d5000d0400012a0b021f4101140f035400c4c400000c2c4d080020081c8220080880041c4131811500d03007074441c030044e6402c000c040b501414481c100a024003001003c02c0c00c0c01d0400034a4621540d12441110b10080d0050024000c0c140003440c25400707080844451400e000d404499105035488a80d80400c040045100c01a0b48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466901618 1250 466900368 466900403
    0x50706110306180f0a05071b1a0606030f04060b061b0a05060c0406021908090607060c030e0f0618010e07120c0b04050102030307110f0a0b0f060607050613060b0d 71
    0x7403194400b030010b01900d40806001400d41000e042d241c10105c46040828241d603080070a43c3d1840b8911500b80d07140c00c4002500341880142948090302c81c41d2100000707120744409041001c2c0e404162403400c036220402e000709000500942c40314140000c06801c141c18514070201002050410080b1020b20380c201240c5d04c0d00300541803100303a502006803181d181c04c03c0e06080000f903691911881036480d05480214803c00e02403448182c03108508e0040085a5a10561601c1d60107003490702c3d03502d400309041040d00c51034a00046801100d180c2030400511a6994000e8142600c82e8440e2001c1d10f20b559500d40c1c6042260140251000f800049810358505040c0e880c11820a8810b98402506c1080600c0103121980e8007100f180d03040500c9142402950689c4c41c04d40e8101411607004220520170040480b00308038488414610482c841003503103425584410501c05688201c2000078055088100028800b0301440c402c181c0b81d60040d0400070f404021040410000c250400b4280c84003002074604165 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466902868 1250 466901618 466901629
    0xc19050607050106090e031303030305070203190f0906030c0e01120906050103080c060c03100e04050f0d0e130902010509090a06050d0b1504090c092d09050f03040b040504020703050706110306 84
    0x311b444134801503103404038a41b00c4030303004003540c0401410152100007041d89144208165060451700220001518002080c0606014181c0d02c6c9000460400a00000c1c0540207101d2051003a8041d100c00300e07011820720044070101540b03031171001c195a440740104040750041c420107018508c1403c4140d42c4031040c00e03400740351100007441c0790100318081040101410070070b0840030842e511a0383c02d011a46403032411606260000f6213001f1144120b41c85034034050340c8003113000b5001200b5191100151081c0042c441074071000030002c2e000c034070208150308660400f0411541e100d5244138001800716110380c0010040e509018060b0745480c40e12080c00b152010001c408880644100c8081008100030783d03410000035800d00c501d00007965034030100f0b040c9500305080c11071445e80d09011031121601946c400d90040c802100c003580c00740b00304005001510000012107080e1040d025030741d4209841c0500b040301a612a0b10100e040102c144a610000b50583c000c01c0c80c400c0d401a01561240f0b04a0107000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466904118 1250 466902868 466902881
    0x3050a030c020a0e0408040e0604231602010e0c090711070306020918040c090506011826060f0417271f0518010c0b041a0601050c0c1905060705010609 66
    0x1000344d4600010b1100040c120b0741210100c03034414801e8401e66a03284001070007401c00c048802418030748450301642c10812442c400d8030400208840412a00c0c1181080b8202d0708529040c644560004c1841d602e903140c4284004c0d8070206502d80070310070304c00d4140018101901680201c0359581c010402c45107618104101c10403c810300303504170f61580343c40e0300d4410014105100d0018413543e2440071603140d034801d40020104005209000031441d03038030595405d0041044011001c0b6030701d282401c0100c00d07400300750140508252407600b9215101c544560001c298081d040d82c008141c1082000e1071403442030040080c40c0380c2c1c080c010072050300a4050100280b113a019891070b010b0b02c01562182284c01c03c090310520310340d420720b00c4464100340005a800c0c280b6054050408101c00741000100013a09582201414040403a51b100d81c440c1d9005468138050500100e038581c20a0b6a021010300707000c421080c4281680602d4201d9540d150080740d007640c00088182c480ba519464180290640b900615 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466905368 1250 466904118 466904129
    0x106060302090609040c050d06060504030510050f15060714010516020f0d110705030613030e0316060c05070512070305070506030c030c07171b150903030c1303050a030c020a 76
    0x951508040da000156248944641300f4403866807180d43c80740c014480c20a4a07440d50340c0b13801c1000b4240d200c2c00094130a81107444103c4440c898283c001003040c07214048d09010302e581e00369440e0356858034089801c00a1100410540080051110308086420b0310b55001c4840000000018181803203030308400e03406c800003c850195400b00106c84603180300014181c0d1308803841d00c1d02d02500f80b04200307204d09100300e40c2c3c002d56241c415403050140c44414500c9a2895500c00d4682c000b900b0314220925848090b0408401480c4000420411109000309650300040f44603d05459445494070002000e0307580c1c0c1c02c0030000e213501a40c41441013050070030140002d0401141d00030b0452030002c0b0200341d5480011700042128002003188001c00c07121b0ba000303000340c00c003444a00741c585541c030742440008207039001442c07030030300c6440306a50b04010300089403401081c41340095840c50b5541c001e81405540a0020078012242003000040480c0c000d22107260300e50f00c01d6488890b400300c903004104481825030081c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466906474 1106 466905368 466905371
    0x90606030b0a151208030103080f0c1e0d03050610030c09030506010e0a1a0127050d1506060f1d0d080d0b030715052a030a1101060603 59
    0x9190040d00d0059085940e82e500c01c100b41441e12884d0020f80b60a20410060011844000003480010b405503856407415080401440c60508940ea031251051310f1403045048400c0103100c0310841804515052203a414081300244071014411707030a40074159a400070195090040752142c0065402809455a960355641035140001d0700f261500d1840d0702e021190808a042c1c4880001252011b035540007018107036241c2c80f02e0000b880032007810501d1381d00000082550b1113410052103244203039161001c4180481e018030540e5025007117042407044411842c17085541c0070010074914080b00d00654584003e10003c203c02402c02d040241c01c2000c0061010310f280c5c810f0700704c050111010350840d92002e07903540f94403c0400b5101c0d045400201d08020040031207002c0f600740540d804181000010300c40d00e80b0040385c0b07142e01084002c2c01003890141040c10000c401e01c100d80081c10241070 = true := by decide +kernel

theorem cover : BRFrame.Cov 466726618 466906474 := by
  have h0 := BRFrame.cov_init 466726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466726618 ≤ n) (h2 : n < 466906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
