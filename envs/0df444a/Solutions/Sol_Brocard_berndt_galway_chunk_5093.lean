-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:43:43.917169+00:00
-- url     : https://prove2.me/submissions/f127554f-b482-4408-912b-af667ff45fa9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 915827338 ≤ n < 916007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 915828588 1250 915827338 915827351
    0x60c03020319090b0a211814010605100909050606040608010b0d020f1605120c070b0d0905070e010f0b0304030e0d03030605031c14030610051b06181507050d 69
    0x1c2c120b48008030b40e441056410310100c0c811941d90786c842e085030305542c044a00c403002403c0e00e05003034049549968011b040c40400941810005a03004509103100e908100000750896561020031b003031f1103400001c1030018034412810700c040c0182c0d104594004500381d0303002e82042d0500f4005000d404043c040c0da0b0b1030035030115028113600481c3d01103031460017a01e400240c40350404c441000d014400b14004480e940135000741c0d103136800e9403030080d42c1c808000580102200c0d842c10314440030310740c000480e0f1060b4035218180200800c0c410040d240040004080c000701c20740c502000296421800c6c0c0210503001020001d0201080d0b0082c410f240140301112403003800d111928040d801091242d020540500540c01e070b000a0340c1c41400c96005440700b98644080d01c00840380c0b00d0056100440f00c184d030125090080c50380c00b5208030043c010341d440f11308040500d48601c421441c6000b0048440c88260601507111180e102002d0090072003c22070150b6010071420300e15806030450198049001d20b4070b036240c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 915829838 1250 915828588 915828637
    0x1e070503031f0302100f0807020a0c15180e1608060108060f0f1207090f020f0a0c140f060103110402180105030c040f152a03031d010e16060c030203 65
    0x202400046a005204100c005401760300908140c1d0400305036000300326040c000550003400810000181d0341e200d96401c0000f401d00501d00b211310800c42403c03042000200e016103651b03c0301129000900b40701c410003140391500041013441c6800c12105401002000010303c0b030181d8106030b41a4100c182100c08503640b42c83c0a01041452024181e0070b03178048140c40080058003804200340040e00e6034848244615842c9142d408140c1c4500100c0018580301008168002131140c2c0700005c0c52841000d4500d02d403400e20010601c0c0072808140350010341c002d00010000c00440003401113201106580641c1085c148180b0002c4100c1d405040b54103004001000a4031a807504040b18090600408a0303070801c0e4640701d8050810b00b484c4840c42c0894003051554811201d43d00800e40c1c5603004040036200b9905d155400c41c082c00f8600d54003c00001c046031076041444081c047d1b88156009800102140b079038011054a42890307550009042c042c202401c440886d03408811a004804030b2440c01d81060b5510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 915831088 1250 915829838 915829891
    0x705150915191413020108090304180509010204032a051e010e0324060f0105071e0609140c19080c060903070f030807140c060a031e0203010b1e07050303 67
    0x150070f01802480d0050030004445280c04207200c580c1e000782d0312050190390702c104480d601d10460145c0c00300b0594401c1030766410891500616480a082c400241c141a9250740300000044540c00c14a01c0e80f13030517008100c40109614500001303080c200d402c02a0046065230f2486000f1300012840d042110420000e8400d8078100412480b40d2600c0e520360324100c2c1011000340701d005044c2d0f182403007440e04a5502c3c0c0c141d80316070140c0d0350351900100c1c40c81c1c450340c41c540a040303400c0d040402201c3c00d5807590088408640407101443e8007103000f1020b0700340d952120080142d00c0540c2d40b42d030100e0407102441885074000004003003440880607103e099495440c00002803500000d6030000340140c4403668080204901301021b0324046200d1640d0310841d05c1410002525002c1100c00baa401800c14001030280c503229412002c5001c0c05003074500540c62807662041c0a0760f00c00d80000200c0c0100007800c003050514030604802044a9001c01400c01c640b0703550b0140c03030744009809480070007a41e41200041c3c3c0383e42d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 915832338 1250 915831088 915831101
    0x60f06051c02181305060604020c060f070c0501411b04030807030e19050904030f0c0b2409040206070b06030325140f0a030f02030f070515091519 64
    0x2030100d850300e010fa02514031504d805000b15030901400000c0394050801c2d000f66442041c04070701405080c1d40390f4843c420420002007129007001449504503022407800e00c2034410100c0c02c80401d065074401f0080311491544100030304510710360041703190b030642c5628002c6541c00044222110b46841a450f0b20680c050141c2e0300f000c0d1040200203010002c06402c66042c10400000752050795001403070741e02c2d8020300c60b4644a0b040c0c100c54034a00140000b03101d40c044c852000e4550405905a03042130300c5e031005449003140e2040d0f4003100305d80401410440d0a02d9032680e844205c460b031a40d407405a001c2000342c003c20200600c44400c20000c24481d9400b171041e1440e540100c0741194806602904c00044031548100517a1303090b0b0f1050305401c074100301181e410500c6481500801150060381c5e000c50758003003096000c2c0110300051000004410b0710500611000c0e00601c02840c680b440c042425181c0d04010b40303100319a92014404200010301d00307039140da001803100091180b800b020348174000030701407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 915833588 1250 915832338 915832369
    0xe0906030601170a0213020405040c1416171306231c0b030d0215010f03200a150c0213050f0a0903031b050c01051005180406060b0301080307060f06051c02 68
    0x41c4201d011140c1c8006ea8041c0040310800c03581400304451050058410b420340030303510346800c801003210382c0c50910641c460030f200c54880c8003805078102081d403007903541e500b041d10354415000350100304015203580252560610700352141c0c2504070322003540344002144550983d0740c0c10614090802100d105240e4410504060302600307484001e4200c00c8000d413a42d45841008101840c0b420010a02c03925864480007542e6022004450800c7d40c50801e21015500c15803003548407404040100d81c1070f040b0700316140e00c5080d03a12a104116900e20401200030440341c007400d8031914201c1044859899070020a0b04000c4c5044001441000d90400710054024003680c0003038070000d0a0320209055100e0b0040c540700c1c40703030700081105880700500295500da042c4122076001c690308212134503915820507116089031250000150701c59503811034441b0b03600240d009400b01e0b003000c03e43c082806141c0c000d400c400c203004541049014101400540c040786292001381d0418401da038041c0464990580300c2c0841c0c030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 915834838 1250 915833588 915833599
    0x31005100812030a18151a0a08030c100213030803100b12060310110405010e0609040903020a02210703033f0b010203120a020f040e0405030403030e0906030601170a02 73
    0xa0041010250552040e20704011381803a14282d4411100d10150b25409a0360011604c807107400d102e404080600582c5c6010110744012035801200d90340c1c1d000b500002002c000014549844480d00000e0405840c24401140300e401004800700b800d049050100a81c1d601424480e100d0301c500141c00c0592501350400e4020903000100304c906c0d50900c0c1003041c4212001c6003120050642654034006560304940700b03220707201e01444240241e41c058003911100180241115041452210020341a95441541600507070030501c2020b05505042600d080030601d403841e00b403085040340700229901c80c039520016040190103c03a072000c81c070040741c4400b540052615140a0823080c0651400041000303d0307003d030580d2074080c90340b03003950020080c2d03a01018a4482c02c1469a91000c0f65000307580300c2032007010000010040400c103d546170100f240128050f2008680301e900354503018224108a05000b403003880c148041001541d8005001c6040d19400103e00d02200b5189003801e180c0341035000002c3d84803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 915836088 1250 915834838 915834853
    0x23060909090f061323121b03040b0a03150e041704050306040b010825121b090b03060a05010b0a0e03070b0a03051512030d0b010e0402120405010f02090310051008 71
    0x18010100c0ca02c84d10340195625003032010419201440d00009030794858054100d5a5a2818482c00801409580f8152280304904172402002c642c02c6a000c1d4000100003540443c1015a083c1c3c175120307d0325110f8462442c0981c0c0c5080c6401051280d00003000107150031203445200010007000c0c01904e0080c0005421180b05061515140e40814401d0107564401d01c250409251511400c0166008000c034514408687d5030402c452490740f2104404203890603568a81c115000c10016200079008086819000442c01122420141009006401840c1c0300c1e0914005000302911201180c620203402e007030084a00520f58003003410240154801e20403441c4c086000c0c1e40140e015003216219221081d1600301641c006030401c050145001c640a038903a2090181c0c0320900300580c03015940650506296003034440381000901a03070303c410b550340081c030040411300080010900417005500c00c1c50f201542000d6421010079030303600900604085a50b140c034042003031580300104420240a041042d034801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 915837338 1250 915836088 915836101
    0x3030c1e040e070f090f06110a0803010803030a0b010f09060302091302030106020c1f051b01060e0124021b06070c05030d080601020d050406020715020c030a050723060909090f06 78
    0x145102201d08202103213804010480d003d12541d5000e0540c0c040c080c000f901c2c05d080c1b103000c5a40c00007440201a4a2248040c00404a100d04000d1070080500000469403442c0040d20002520500c05106060211156104984c1c0340c1110306802902e415190061711000c1180025030035429204403400070030300c000b0002c030300183d000c00c0d040f2400307200740c40c80880e842000410707c0d02e183ca02042480001e40a02541c000e10b45503401e00300407a1591800410340c40d80320848003803400c1d800e034800301c420400c446101c4003241340e070504031485d100140094860070010203540f58074031040d40350321792050f00e0008040e42000001c031400d10142901600300c481550b40c00801600c1002e05031034403030162180441300340d40c1920860480b42030380c22580c040e061007840c11000c5000f00781e1405a03241076005001054100351402c200c80c459160054004203d52850314842c40c0c2c2d01450240d1070880c001c4205400d51007522010222041d0b10402c0e40c184190340c1d240c00701c180c1402c2d8084c0d60203d80340a00c0c400e00c4503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 915838588 1250 915837338 915837359
    0x30a0506011716030e0c0609040c051213021203090307271e0623240703031a060c0307020603131406190516081b0f190201060803030c1e04 61
    0xb400303201504c080001c64040c10070140d9903002c00307103030380d5120004000ea4a600d0a161b0440703600414030307040c8241003105c0e9000e05c4070050812a0007516400e0381c0241601985000c0d60b2103551b182131000a075107440c0c150400721b80c9500850268000849190031a00100c01c207180300c0300d180742c1c046d4004010382034181e000103003009502444070303050030b04110001c0741c48800c02c00c45612043d10381e03040c03002e040098818407641840040000e010380b40e42c0751104000b141a80d00030140d180c03095074001150300c402c9901d94400704d03580f0500c90280c071741405850700c501800011514065012207038a40c42e65a0110521480001d20200a120140700c0420080d5441f00140c043e0180c1070200c5030501140b02d0003d410120340040340c0a51851000d407c44465150040108a4010460802140c590000f0340c0117032189030f109280b041e1500b4800034011011a556501041111010b44002e10515180181c11030383ea0001802407200030100103942c800211042e480c01301d40008000b03109855030b548060155 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 915839838 1250 915838588 915838621
    0x1b080d021314120607030504020409060635030a052a0a060612030801030f1703071101051506040e0a18030c1b0f1701020c06010f03140111030a05060117 67
    0x65810a90b5103072641ea10340b0203240c003000c41c0240001c0915648a200c100e005e400050b0013a0303007050ba60780083e80400c2041c090b400242402c001a00c10b2701d91a010f000807004180f0703c20101c84e241e804503040c510000802252203060a604e8680d0300c8035204000c94101051040d2242c4000d0300801c0300804810010420440d01c900a2504211072a0380d0150440d641850a0b40100080d0f00300c1c00600010740510820101c3c10301441424101030102070624209500907183c4070041144941640019042406443d910461013421401c407043c401001c82d10500803401100182c5a030380c00029042d4507183e01034110140807985050441856040252584a9102d800d07141400380d001e50051a0846450ba1000c80714085020a080f030700d881c1c00b88141071940800004155000c002078291041e04202a42c0070b083d0700880e000d0349a00e1441c00c2c11084461611100036a414910905103400058040c0c0743c0c0302248800115665981c2d500486185d6405131071f100c1c0c80d4407a0010322500390070310800e00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 915841088 1250 915839838 915839849
    0x40605040c080f010807050f130e1006210b0402010507020d0512030f010e040c0306021c0515030d1803230109031d0409020306010308090a0806070815010504061b080d0213 75
    0x2080e640c070b45c0d20598580382c1a00481380c1003410280c1003001d40c10302d10120320303c601390544000340d54401e40c8842c030b08190114a5009200c0e44540c030910910142d148580c18100c4a80c43d07200251200342d0700d40d640120b0007040030f41404400b082c40425074032101043c3e1076080d44201034400b40e62502044450302c3c1c1090300da50352003007035420001c108120b41021300da000390740011081c800d030761941c0c0d0360030040d500507603e046049002444407600e90006014030350052040d900c2503650252820b06161402c03c0a54580c41001350007000348184003000010001500e030480f86440490340502c03d140c000104030a070f40b09043d132800e000c080c241540045c207030802802c01010610300100755000c0209681c0020f1001e541030308803800400c000741c6070a009001d0307007002501841c82c141d41c4401c51400d10b403007100c11001052035401003050711070705400384040440003424564241424814020464030301a000084080b100c0d1003110700b48422003090710305000b244a001e660300c1d040e440c400c2003580c01a1052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 915842338 1250 915841088 915841111
    0x709140f0402030a14010b040603030c110103050c070b0403140a020d0305010e060328020a06050304170304080307050711040e07030335100509070819060b0f09040605040c08 76
    0x118002101024a00d401203030000e00402680da1251a0380348058004a101c858643d030710700540c10680c4803801203000550090701d0b014012b0721103080c00200140c100c207001d4101031520f000c000c8441220800d4808503031f00019002807558482c40e00303a4046045001110b00e04c000401d880070b400d9400100b6285001507039400384016641e410900c60105070550b030050745608250810b100b036501c107006888101d8082880e01d141d080250300405e00310700094101c440003070340000401c01408004160503a0145c48025400e2a52910703031100c80b02808050501000c0203030004414081c07104c1c0190f481801e010003031040000300c48003861113644440c90311040740070940c400607008140d5241d80e1200752071183d4101d44840c600c12843d0b01c2e2040c01c1c004000821003402503d0100f81502c0c0c0c2c1040303910034016a00e4400140c00c0100e00103d4006003041c074548042d041c403500340700d8107951406583d042c117413552a283d2601c5d05038000402070207070b40d0040c40d0043e1400e80c9008803254028446801200321022 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915843588 1250 915842338 915842341
    0x6051f03090b040c091b141809010b040608010b070809041a13061a0c0601060c0213050f101401020703030315090e010506040c050c0c013c02120a09030f02060408070914 74
    0x1780202c1c4010400210011a048081051003015071000600c182c8d503c004402104000c40360004404a4007a040307007295080100c0c080c1701140d0400c18090140202908041c18415a591840413911485e21824040e540340c9020b45419a03000c06805641031000f007103071181500b9510402c00600300c5202e00e00d1404c499408a410a000c2c8408031100382440301c015004903030800105560321040c00d00c04a8114030301e070751002003842c42c078030500e8001c0141ca1076070381403414864a080c49424650704000c410040c00210000240c0c1c0008042080b6641b500307000c00c075640348414681041500d580706100480c240014800707036481c190f00c1144100c0045504218141152008481c5405441d2400b40158440750740c0c50a20340c011591035182c0084e6180112741001840060451419808400c00f500e003150300c0c1100360310f038040c0400001c40080d07003926400c100d15008020400081c510029003034031102a4040700b5034480400310f402600d0800c0071030b0203040d034414201008059800200f03070032281c00c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 915844838 1250 915843588 915843611
    0xc0807090b030a09020a1203020a0c0b04080312091e010b03150f0c0c0c0d0308090c01031e0f06082d03040609030b090a02030f1e0106051f03090b040c09 67
    0x429240c159880c1051080c1159035480d0f000b802041c0300c9000340d0f0300c000007240c0014a4207400102d00200b9200368082c0400351918600001d03202c1040c0c00965104009000c01d1104101c0041a100300c400324200c0c07840345890f0700f03140d1800c00b08490046103020710110b0400510b41d005410034502090260120303100b200b521050001e01c0c6005852112802c2170000200d4882d9012030091f019180041c015180e0b00150140003900d621010041103010a01d48020071501041c281b00b24101c00b4004c0c2030038414405015244001000c020702159040e6903500741040d60100281d0204024015400c1211001c450100e0340840c0303251a15000180304540c800400c01418020094600711021a207805030b060741180e4564810040007404440c0c2807184584100160360200f1241c041c1d48034200207450307140c0d80101e18a801c0081120781040507030502c042001b1507181c040d00d5104480c80000d1581c514822468110054030190700b000d4400d1542d041840103001c44010000111104150b04000004145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 915846088 1250 915844838 915844847
    0xa0b2d030609030a0c0303021c060918080a030908040506030c0418060b0a0c02220c02010e0a11010c050a1506090e0d0e13090f05010905070e101a0d0f0c0807 69
    0x1128002d0040e08240445500980904000c0041d584a41005400c1682e2454004c40254040c80041141d0fa1180030801c07034000a413082103401e0040440c0800c4040145e22a5026840780c4000002010342c0c400300c0d8070501054031b05036409404010007440e03907401d242078040280d4001d4010104501e12a81d204440361605101d0642107426034110903007002c000c803200383c0b10340d8422181a60070640303104010941786800c54081c0c41000180000088a0f00d40351030090031103200c0400010b540d402610500040380c10f0a84040100c002403801801c0f8110a140c92410580f0260004200390000c00c11540a848a40c20135025140642810401c031042449003e54031040c41c0b0b03a40010411080712440d00b0b0814040b002000c04c80040c5c00b060385e86440c2e4514007071030041c00c42624203954592450007009000e000980c024a10480c000f00c090802c0f04200b00844d100303216400d8000d4a00c00e1038030205210100382c0380700325074a010821000b50308240f884064220322601c01c00007000000005c171014040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 915847338 1250 915846088 915846091
    0x60b03030703020a11040f0e100b01030b0603060d1707050606100903030f0315080a0606051507080a0e040f0501060206090f010612030309060b28061706090a0b2d0306 73
    0x954010185a88151500f208617081c2182a40d042a255506107009803041d026035101400404002c110401350180c44100710761144120904040c200061501640c1d0b5404c20380340c002404aa191500745001e00d80036805101c0102c04c1480200c0c0400d0300002d011010403d1031041c103042d034007040807440e1458110307011580e07808024007007681880d100074020310a500c034801ca403112500440e166901c81e151246843e58020003110010740340d4400b8091030400c12540c2203154240302c031607030406076180c2d1030300702500804410008000e40400b160a043d62544c01c9446601c0c0030704c80070801d07541c480500035100c1d44211883e49040c880c518005140140c14410441202e0025050352021090b95800f20050588010160b600c0744d120015154543e5a40b50504801d07803020034020b250100380140c0003000320704d541c840342c184031380c00e070003c0c001002d001c1c4070701d600c08002c483c82407880d561070032440c00500358030340029003000036098100b2808441c044802c030031122038801c650001015108042d0344800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 915848588 1250 915847338 915847343
    0x3151c06110f04091a12010204140307120b150607030306061814120a081204020a0806070c0b060310060e061903020d02100210021912020a0c120e030102070f060b030307 74
    0x1400c120070005010b01d03070f008211170348070000050305580d018800205840405202d1103a21303540000c04100b0f42e0724030544020001c1d015405440c9184c41d01450b403400541d4580040e00c0c05041d01c00180740e01c0d0101003280e0b01924001d00a984403075aa0400138000e000d0b42c010b040102d034540940c203a4001c4101c400b1005c44030704010945003824124140400d8007044141c520052080c43c51660004035034002402a980080c2c451040b00c0c03402e0700400c0742d040d000ea40300c0001074206c40d0a01244c950b02c07030360001c0341b40c1d0003011100c1c2c140c40300c40100b07240c80303021105815490700d4000c010810701c0403011154040c0390110383c00286950f2102a070110070206200c000e61020394032042e00c00600b00320103e0403d00c42c1da1300503205003000c4410100141ea1200300c40e490652050341003c1040c03a0400318401c0b5904102c4011810030b104844060403400f210303240540000d41565848508030701c100100481d006001c1e0081d5120116850228101d22424030220760442c00c101c109021410000140c50f01c0301d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 915849838 1250 915848588 915848617
    0xf0c0501082401030c05071e1b0807090b06070218061e09040b0c04030c060e01030f0e3004090b030d0e010c0305300a1b0c03030203151c0611 62
    0xb10100c015001004907407034000c00d1200900c800804202803d059407200710000300340030b1107840c0310308e0950381c07040311010041401010488180218003000801c40c050b100041c50004e41c010002e8000780460280c280000c1d4481020540301c0060f60329100300306e008003015107078581401b0400c92409880c80d4004880d540055100b0006030100350300d0b00c8200e4104002c220640e1030251642c6844042c6e0030141c0141010400d014000c94003940e1502c11150124449002041000d091840442e121040346409400b103c0c08817081c0c1484401450791180804c000b80d13581a03607196100b450320094002442214424041c0220b1844070301d00410342103512000503582e030046100c0c0c2c1e5800f941c05401c2040c44400c1241e540714400b428040d48294161101c52650b101682c0b031400c41800c60985807121111111a00210342208c4e5580e0054240034501e40d01d401d0150322070340d07100f034400440c44a4070760185c1d0212100a86a4208015109022645000c1c4000b03000c0012110340e200d259106421040142c40e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 915851088 1250 915849838 915849901
    0x109140702191b090c0206093003040204110c010c1d01020d05030a090c18050703090206031b1309140a152c090d03150b12070203070f0c050108 63
    0x101070940300201643c140251148043e100e4200d1800c5904504104001d80e1114050002021080106590044d002c00070415000d80c00403801c80303a4421504114a00c0c0f501002007400c65846070400c041030076140005645641c12400454007811109a607040800c00400b00c420020705041c0140f044008182c0081c48403030409402100e081d44014413a0b9070b11955880b080002844809a00c0004c0010141c20500c0c503000701d100104891014049000b03040c58190710100603290320082e04e80c070a00d411008203980340d84e1606440c051181d4031404102040e0044045108150b503072145050030900d03015002e5907034800346040103e403007c10024844001040c400c2044540c4000880601039461642810b0016415200c180032441a6440e0390513420031013080ca5107a41c50b1140d810341e180e001080a8400e4580041c0345d000e03108004005400140c02c0d0f000410041c000c00c2100d4000d0340c4008040070444d140c0c20322404030350480c0169030014102e00d01181c10552014001d02400403080b506c01e460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 915852338 1250 915851088 915851093
    0x20101e093f08060111010c090e010b030906280527120409110730090303080f06011103070f1209030503191206031505010914131109010914070219 64
    0x5a60020f20ba1810000c294012802000c02805174490580d031a80359103a040f810020b005458600503045070154200a004000008a00156a0307070442c07503554018685a154101c1600200310303c3c2c6459000f24144414800078003c41c0040008000c0100d000ca407403040c9044845846064162204444410500040c401034400c1da00c440c05140b504914546418800e42d600c001000200e142d10035031803540d95112103544040b43c0342c0c0300155502d04d0204140c2e42940e03000340c19000054004054804441d0000b881640140ca980050291220440c3d456031b040d8035101c81d4040c1c5d8048122202d1b42c44000b90340701c20b4003d10000d400d881e4400701440c113002c000c0400403036000b19103030050704001c20002036810124031071150101550282c210907110b511910704e50016540c06134803000900345803400004840400340480b83d04040039070141c2104044900700100d107200b4880b8040ea001c0d044800010340740301c0703076400102c12000b195100700f01c2d980d035007006a03252085500d19010210a0080c2c1400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 915853588 1250 915852338 915852347
    0x4020409033e0c031f0204090f0905070e0c070303020c07090603080a021501380313060501080606060702060a0e031603061b1d040f0c02070620101e093f 67
    0x85c1c036000800c0060419541e00111000e40f44107071141d012840c0d0350414901030180c1031200c10050144d0107503003019814003441c865100e00c40c50341c0c05001c03d5400705021100d04002e000340001407015450511240b5140c1c1424030040c1e0010051a0242c0b0503a101990a40000c0000754122801040b0200c2c11030000190030a100000c40c1d080000002da030444105408103a80256000d115000149100c00840386803810860b581038100300725039800942049840e07960318044072420381d030540341d03292140c840d00d40076151005903082d82585402680050628400e80507907100c01caa004c2c2e60248294603540d10a0414041083c0c2c01100103038920014042c0030160400f42e40c0990405040060600f10000220080b035002c8003151005800c0341108028941e0300454212111200722150394000c2406c1c0030641e40c0302c10b8002014209529111810041c0c81d00010048918005503410300c020500b91804a0b2403031032511843c00056804584031603500001141d03507400c02c08812848804071041740d020384 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 915854838 1250 915853588 915853633
    0x10503060d0516050a090b060a05090112060e040c05061c0203070903050609071403071503050a020d02160b0108030c03090d240b010909021204020409033e0c03 70
    0x30340010444168070001281040802c000700284001c1590050410040141c00710f4a94040c4125034100030030048180d440c3c4080303070001c0113a410002c1d41c41d0710040060760084078003155401c08030702e0104001842851910014412449040707041206620ba004000890003540c00d1504104602d408000500001d41d0066801041c6801c15541980c0d4aa58140c40c01c0001c44503c1c7c03031341d0024241000140c0d0040c50402881e6011009000c40c2800d01a0034420307108a00078000400d0b4994010451f10103c41d4103c4a41c0d1345000400d6540b030002c6810800045401702080f20841240030002911a0002c0159000c85000d10051403410031b08404201454140301e070241c4201c0d001111140401c010420403541d1101750300008603c2d41009000500300c6201a4031408155004101b4001c0616042c120154015411940068420000c1c1400c444100355107546895a00d0328135215103100840d030300040c541035841040545800e0b525620540c03501c00d40c1d60440c0d0582d0118072020880e107441e080e4407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 915856088 1250 915854838 915854851
    0xd080126010e0703030e030f190f060605041121010f0e0618040f0311060c0a111609020409060b040503030a050a030221090f010c050a050901110a1b0f03020f010503 72
    0x10602260a641d0316083c4041540300710080303030b688481410241820311021008000354805001c543d9000c082c00040380b40d80e410002c000300c0401803071408100c071641c0980c000c1d01018000300840d8002502d00c104c113a118501c80b00d00c8000901203019080c0d02e00301c080d0b061f646101ca6a103105458131082030403c40010706803d610000e0490384464041c80006032038842c502a1404a40900075401c020b032507495440320b02d1500b070f000201082620304428048076003a00c1c651038451002d901e80303140b95040c030b41c03911480201000d03054800603151807250068819034141d0002002115684c0801e140203101d64816203405400c2400715054080c094006880c444081d81030252405007441c81d040a03c0340d404101c00d800301c030301800f40540240c04021040301c03005581b0080010b03201c0840090164000d488082c8108600010301e161036921461060500c10340342c43c2100d00c1034001e480c000d81a070241c056103c280d0307402c04a00098024024283e5011a50080e19043d0600d81410045171140d0004000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 915857338 1250 915856088 915856091
    0x15011b0614071701090225060917040f08010b0a031103031b0d030e030a1e020a0c080708012708030c070f0c08010e032a0708030a09080d08012601 64
    0x1008201c02000400762051407541c1d140c010400080c00d09000c10081a00000c07005031042c40429448890000e00c9412041d43c1b011690b102035640c503280014080720200185856104e1400c1c49000310a4406803050b140550440c07030304030344c41d2050305080364800000301e40e11400403a001c0001c110f00800b039003907030b410180030f507443c01c42c81464154201100c0c044c0d41c0802d5120310104c20074240c0c140300f40301c15504440f020354500700c414075005020b50b09108001007400305c2d0240460280c1e000300a89042d142e4020310051040f0365508515440b02010700c18007250394201014401d1044034080ca0702d041c2c0701010240b0004060750b8854045a030030080051014040420016020901d00600700305000c4c85400e201718210309100c0b54030300f52202d54a001000d94006d0204855903601c50f40400740030302ca02001165940741300324609241940e240d10581040c01b00080b14503419a12803444419510f2500c200c4455440902007104e0307882003403007080d007004828000c4540344140c170600c54112420301c100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 915858588 1250 915857338 915857351
    0x60306040f1506180b030103080d111902070e10050904110f060706020903070e06060d1e021314011416030903050319030e06130803181504020915011b06 67
    0x30048004003580c3c000002243c0d090031006041c0d002400c85501030a10550000c1c2103515503610f510340c6c3d000d000030641c0c1480d15103442e402d4510581c01641e200c030f0b900d40c070140412a0b00c0c0f0b01c082c1d141c0721240039011b40000c1c0c000000c1c8c1100c1e5130706901c20031150050100d0706c0700d80c2c6603145d02c1c00d0b01038000400c541c4010190080b004956541005d800f56034042c8500590341c0c0002c2d400c05144c00c3c4a0b9100800d2551100700300b10195603240b00741c42c200034404c040030079820503105075640004d000c80d561108540c400300d0301c1061407040c200381c0001e8400000c410500b1501400042d1740a2030007003500d1705905003c0041700680f0070549050442b0030320a003014a5500c2d101d940b46800e41e0030907080c20104010340114560741e20340c03601551080604a801070907040c1048000031000048130940500303e0b540000c0811a0201240003411201c116082610300d449500744007021170305c400343c030300740d10886244001c60644402208031601c03000058442166140c1d0340304080d03480c0320a83d042590204d0340d031700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 915859838 1250 915858588 915858611
    0x2107110301020a27081225020f1e091303110a080406201b01020c06070b070c1a01090603030305090d0806010813080c070312020d090902032d190b060306040f 69
    0x60984101071b18401d6648403c40c1d00016403075039100b030450300040170090100c00050780765200c40d03003890b0354207440d01d401251100805483c0c02c4a031840180e0040e035800200910f00801a0016118a110340e85034140e00c80c1c080402a03498620043c041c110380340c01c01c020000309001ea0101c0c080c03048082c00045a201c140e103081c41c2090f410780524000508122090300d207130340c0e042c440c41c500400c00301c074201e06100f001e48078010707010b900030483c0c070500446042c01000c1c0844a041c011040c54100103118542d030710345e1190405481c19100031404030381000e0100746465008920f42c1943c1c0180d070b50f80c1e4250350b1540011258400d0140c411909020074241600101d00198001c020290000000340b0800e451807800c0d2411106250180085421814545183d98ee01242583c22242949000341c0c0360303160086018800d00d584840000003100c01c2100c41ca450402090040c490880300e0180301001d190007801c0426501c50304441c5a01940820021382141341035840100080c403604000140a801d41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 915861088 1250 915859838 915859843
    0x1903050609060610050a090b09030102042c0a05060f0f0f0d032a080307080912030a090606090c02030703030906090209040b0406110a080a09052107110301020a2708 72
    0x7550590050340048003000400d00700101140022181807901a1500110440c001d120140600079030720012400038003e2441d9171309406850142c50766210304081d1880c00841c5e60013003203c2d50345901c1c04400c0d4100103582041140b14041c41540050300c03040b2483c022a0030000c10691503100c00e540041d002c042c404035900d42c4180c0808240c0f01c0e482e41c41c0e82d0300010403a0040c0190394605400c4518075004078038006071707a001c25241c120b0381d9801d051281d9201c0003042410078070714208803034940901000304030a48220350000348032280103060030800d0315150b0b203a0000303944100b4500b00c0503a0040181e02d00007407081d4003500b101405800002081c40040e40080d04a910a171026500544107106020510529200f591168044178040b945403861011000d400040300502180d0401d6595800c80c0038064288040f101c0a00c61140c2d11190039100001c4601d25040250140c5012250001c000010704051003100c2003990951120300c451a0f400d0b030300307041602d1803007450070002600d0000000e498804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 915862338 1250 915861088 915861091
    0x50705062b060f08010b0f030610050904081c1b0903020f0f040e010c030219020c0d030f0c050d030f0c031817040801050112060b030616030c090519090b0d08030619030506 75
    0x10013002280d074440383d004000d1541d2240c88000d2181d0498030030b02c6110000014440304540042c1d5400d90141e9803400d1001581c000c02d43c070740da4500000020540844002d5202d030700c1c4500c0c00c20071181aa1546801158982c07a5400000e4000e1843c60724840070307140455203007404620082002c19a40c151600003401d465150300d050011070740100b4020fa03140786c1d20212542c030089501c001c1040c4001a40050244030134040041c00703215902c0440200c0c0742c07041540c2e42c0040c1e0000c1c111800c440c0c1c0c0e400018000c0080a0800c01c0780381c541003c40841511a01440e5072045094003160424074241d00c072482012604480c0c000ca00d81e0070000000c2181003806041d0081c920480d480494a156051440640701910641441b9400c001d04000c0b500e06944212025002a403500042752410030038255010042030304681d0b0f101104582c44071401c0c000d002d400e010342d501c4000078048010340f0020f00422460218000f82a09000d0000a0b2982010300e80800e004074108042802a40e99444207420980d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 915863588 1250 915862338 915862349
    0x1021611010e0909150c160309050108010803070b010515190207030c15170a0e011109100513120305120a050f0601021b010e032107050705062b060f 65
    0x444240c40c944540c1c00c0342c02016011010340300e040307183c6010040700f17884a80100c4003c8910307000313901007054148400207446010702e1400010740002030390305000d40400840d04c42c05001411a000200b01070a010003a07508407a40f16106001d00d074200420172034011000041100a04814000c8000010230002c110090154a4007c1c2c451103013182050714851040d5041040301344070081c009400c95078401540b6282811811b01401d0703580703507203003d000070709821941031590f5801c0032060748281514100505040134200c510f901c200c515000d003621035000300c0e0940f00e195462614208081f400040062080d54802c0c5005803800c511202807140240c0c0c2075485100b199075542c00c200405800e501300c0b6421000900040c4140914000124650141c002985040104e00c8030340c1c500d2038400f040b01028540303d4940a803940c420746500045260841c06040d507480c071034210b001a081c145007003201d5881c0c4d01c48240544040300da0655408107003800040d507220944d14400061600c090300b058202a14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 915864838 1250 915863588 915863603
    0x60f1713051507020c0303090d0602031f0f170c09040f0804080616030e0106050307140a0e04030e03160e010312120c0e01030c0302041805131a010501090b0c10020c010216 75
    0x43c00b0b04004d24045002d41d9617406580f0030040e00704607643d6010b80110480d40002d01517641e5aa500c41d03800d00f0307188005050360548201c4c80105500b4500160201a03c00d500c2e845a40c00740400b14995a4019190280d608810f100300802e01148441c0d4041040c42e00030385070145032990301d40c071261401d002181d01d40b5044140d100040e48282c1e00d40224184d141040009000c00d508040000b074480c0007034401d00e484e01450890b4040c46440d0301d83c030340e401428450982c50152400d42030280040c900c2a206034824007c00ca244030b415901010300e2020303140000c2c01600142c1c00c56540f806440d04c0003444c00184060661404107035070a6002d0300000d0312096442c03900b18a1030340009000e940480820f14145801480b042c4005003403035038103040182040c4004106900d50a040740b01c108802203000c0c0400003207108504900248400040c1280d0007a079442e00341951302d82840c0382a01880081d41929006800d8101801d4001e030050a2102521400146480d10a5203044c01c1070550740e1003121800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 915866088 1250 915864838 915864841
    0x2070302010806030102120612160807170a0c0504050403050423041d0a1112032101060e0108060907031512120c030203160602070c03060203060a060f17130515 70
    0x1540e00082c0c40303412100590080d41404030109804010910007010715002c0d40014007001e06141d01080030703804005114014590340d580301c84026841c1c0300c0c907004840c83e03403100f04580980f20000150381d0f01081d81040114403c0790810007000050030000c1c0c030603020040b09000201d002c50b0031311a01e19018004071103050480c000c07441400169070084106510035142c1c2d031000d84002e500401d10f500e020b948100441108541240040c3c11544003000160a03840003083c000304d64002c0001415944050890b80a01c0703a90305d0300c040742d0b4901d001c01c900380000e91704004a1280e007441100c507908041d01c4d01b00450442c801d81c10303103003040c101c40d4000100b58440c056032505000c410041005a03010300d16024000e0451034402130f6a91140e2010302d0b40640300400f4220620030f03103a0540d21050340c881d0090135035585d00c1c14086c02940003961094032602020100003030290240201010780071003501c13159400810b00f40c504c041900d00910030f144022444045c540055024031040000f45120010305415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 915867338 1250 915866088 915866093
    0x70e0a0b090a0e0f0603281103120307090602100c12020706290a120209010501050c030f0712020c03071419080a03020303070f14030a02031302030706050301060f140406080903070b07020703 83
    0x70081f03004005001d82c082d83d400707610f01c00390800002822907007100d06002121380b101c000c207141003401c0f42d00060304c201c04414081e80a03445124042101c507140c1c22600a8094100980300704d8102142d0200451040c8a02d1240202d803034020f80703da10b004a200143e28090400700109950414844c2c10a0a802c08103604151500844540142601050b012084100c0e0b9020801189060046c24140840402c0602c02c81204104840003104400100c07915141035107401041c0c10070300302c00c0c000035000d00181c000c99410300140c61021501d0b40c140e6090034100150a005007c00642c003a10007142c1030040208400358100b22200303202c1d203e0f030700940d96494241801015890040303812001c1000141ca440116400314003900e401c24141840180c0e2030b2107408181d1034107011148002d4141c001c10300d0015240b03400401860483d00541c40d078241c81d11003000b04035400309030b030750380031164280a201c1403048521541056600c46900e00c00c0320720b80b0781d0640341d141541e03104840382070040e48440c00034401c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 915868588 1250 915867338 915867343
    0x90b0a060f050306011a070501140402180615090a09110405040c09120219031407080705010f050712020a0228060302070506040b040203030d1e05070e0a0b090a0e0f0603 74
    0x1032041c0c05400740028107100000307448404c180714048004030507403059090b000b01807080314841d560003002008904040324451420b090b04503030a03842104003a0300c00c41c98002908940d840f90700000e10600300d216011113945a25085032646030381044080c1d40114000728181314500040703043c050a01e80711494081000240c9040c40500b50030404861010014489003040d40d00c5011b0b4101c4107210700d02e0070300040030b0600e00141c0c006070071500311000c0307450300000104003602a5160b000a45000540b1407005443c0f190b075400107107001a204000d01c0d000f2441d444810300008045105450000e041ca800250341e003080240e0400c42d4083c08411003041c1201106258002c10703042c20254100440c030f03121591100002440585140c0c458800a8115942401181d1601d4920941000950040d0210904504a11f8218004680782c01c01003840310740654442d0303005000040c607400015040c440840d5450f000000d0b5160008408c4501090305060310401d14455904901e0540c030b94a4814200340c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 915869838 1250 915868588 915868601
    0x80702210403170a0c0b0a020f07060f05090714090a1506050417120f070302010b0402160c170a080c0c0d0303022a0d210507030b0310020c1009030e0301090b0a 70
    0x4540c03d010800c580786550001c0c01c007400650061380d140317010f0f922880200040e02c540c0c42441c5054a00103801410030034654002030b200d1030880003c000d150b0310301420741c2c0e4a1170a401014030304030407140513480c680307010141c1d540e200380c00010219007284555841015012035030048000700b0f002040c00c2c402c1055140300c0800b8240060004d140c20500303020700f29038512600d01c2036503180c0070014141c01410f000f500b06010540015101315512403076102100016100150100c442c10000440000c40780605a11119501805030190514401c2d5546040300e0350702c4074440b540705010304160b204490b556044101030b058081c0c1c9001da520414800500307071050601902484100020010103440500012091103859090038138003000c5500c07581001c40216800e00c0700c020141048200000b031503054004203800d100940864030020b445d01d4060301a400b5103120141c6907440003280c40104101d6070800918280a4209003201e13100110109003504c807400001d803007040c44030b010701844101600c1043d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 915871088 1250 915869838 915869873
    0x40e13121404030f1103070e1803030903030604020a0c0c12060501091e11040521010b060307081b1b07050306130218041403042403020a0807080702210403 68
    0x1120746900e010310901a0307010718000a00f00b600743c44028070400000821703c0020440003001c8441039540e0f601c100800701d904850103401164044403081c180000002524042e00300c402c05181181c1d5a6401d00c002500140958801c21200340b1003500400c4515100300c000e80b4034111050340b0491b103402c149050350380681c80030030114501100c80110a070200d100c100d80000110000c507174141001d0216000d0300890b00103d60110141842580d40384603490411f8032868070000074000c0c0c255560403c05280021036030100880d18440c00920b800c0035581241182d0071180da00c05040900340d48109082d0400c2a0030400302d82e01c60a014400391504120566000418664003048401268003151012110b8100310816413100d201180401680313660300600c0180308012282c6031a0780700c489030062007546c5101040f2910100c110810107209000702e48614403551121005d94071400b500f1151840c00404010850180c054045003101948008804003402d000e40c0c29100e50031810710a44102007081807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 915872338 1250 915871088 915871097
    0x150608090307060906060911070c0522020c0304091112010f06140f09121b09040f020d03020a02191706041e050c040f020409140606031902040e1312 65
    0x10030103224000000c9a04441d07202c2c0020030080001c1c9041d001800b8281c100c021194185540c000f425261900034049050064400c0c078180d035aa0014055488020300c0d0300c20481c1c0010040150010803500145203079404142100d203810b0343e031114403088556190702c61001030380c0000c20482056460402c98090174840b076402e29070b030b490103001074030310a90f6494610100c4804a01c03074118801d1282603c0107a1005071202054031608124240c0b41d021078210301282d041240300f001c1242c1484107480f40b150b070740328120315000390841d000c00c2150700201000b1801c52290710402001a00e0301414500321001da2403a40717010504000074002c5440d942400310398240d0000741040040f5100003c0705261750510b540c08054020141000c50400000a035101d800c1418039284000310f9400e40d004000326a56100104650540080c00c05003a040503520954001c00034000b1a6080000002d8404048100f580045c5030541c0d4001810321140300300c42c20b001194803081c00c2c80c00d0000c16601c02d0107006040c5030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 915873588 1250 915872338 915872341
    0x1050a03140a0f0332030601030903090f0602071d06130f1d0c030708030c0c01080903120903030115030c0e0103020d0207060f1b170403050d060e18010e0c15030604090b0a150608 78
    0x200800c5d00d00004100390b042503210780010060600458182000c0c045002035002d05586440020b980c80b800e40c4030b290a44c4104104071600401c8100900d401090020b203042c4481110031041c1c4007030981060102103455880c0c50260284010580341d4600c44102809407440e0000201054200b01c0e05910585140e0002c000c1d0007802c01d0042201c804021b82401d02491903115602e9a619500403254211000713803aa4040c00b603c004008091412101e213008405211100c21000701d01b0303114100040d02c00728041d038030311400c95030003034010f0140100001801410100c890700d0f42420744500701c0041071a00e030707140034070300304d608021400c2d041400c84e90501d40b002c0010041f4214050304001c1001c0c1c1008804505e420b0b03c0b141c9504154010300815200d46007605202f91221200404201035000030340c030300801600c500c1c1c40410048100000101084246c01c4c0c02c0c0040c40c0c10380d10041149078855a036110f9240025803902046d40903144020300002e804400d044081c0c0ba2a400c1d410540034000500c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 915874838 1250 915873588 915873677
    0x305010f120609030c081c05070e01050d0c1e0c02030d0e0a0b1804020406110d1d0603100503060408070c08070510260c070201031401050a03140a0f03 66
    0x30548003841d80c0b0200c00981c0d0003080c10120b400401501c1c1c010941c61001450009550450f0501489042443d000304019212104113507021185011540d01041d81400840c2442e0b18643c00140c8602481c10300c900094584c402c01d2001094441000011494080c904410350400308560741420b00707282401301603100c00034005804248141b0503d1035034a80001c00b2503d074403c9003150664a0b502074425505c0b20b482d43c2d03000c4c080c1509281c11013054441d4200d4084501d00c0340c81180030005a00c854039101003401c0060180940c001400c0000101400380b000880d030b101000300038851401800d9046c2c132201c80e45403c210195580e070003030000d40d00c028828000c0356a00807444001101d0350400d0881001241035180a82d003205450120103c2c80703100700030340b01404500920400e03100740da04004d482c11035110342090000a0180d6034100c07100b10410300014400c1d0107000e070a00e001000300c8041e003007075075124130344c00005940c200c001644084c0c111841c0c0817020a0040c806455140705032441101c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 915876088 1250 915874838 915874859
    0x509091006121106030a141501030c031a1903050f210711090415090309054617071d1302060d1409160602120d05100b130302010305010f 60
    0x2d43c40c521800f0300101240002090b54443c010000410083c1509807134046104410000c00c0f14945010904207000a484140b00303110300681c100300703e442105032207588000d100741c560441e0350194039030f0204500803003c41c4040040740c00800e1001c008047c004c0d40c0c0300b6001400d6886940084945005101c07080001e441030048410402c81038074409441e43e0b403410801d198a0818006400c0c981c90300b9909020715900001030016140c0c141c41e041204c45558220150482c02d440303802c20108a031945032400741c3c2c1e00b54034090f086107011540300030003612280300700006010008080703400c1d8044002041001556288104019148200c000310361420600c407806000564400902c83c13400011003103100111030b441800c0d0080c07850304104951801088040e41c0d8628a940c50300a032160038400110300d4400141c40700320002d8003000754141072081d0203190240030301402ca03e0303070007051120101d0f50001000281c014a000541460150340c510300026007201d42c1a0082c4a0001d1840802d10620140e03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 915877338 1250 915876088 915876113
    0x10504061517060a03061d01230606030711100605090a06031212020f1c0b03121207030917030403110d0f0513080706091a0a0f050306010207050909100612 68
    0x3410264542c664524001615681040c0c000405540c41e00c14910352400301680e02048030f1014900801200d40303625011002416105804181a91000005149418120080d5800000a01f003550054142c0d444035810050104402d0314150764907282007103e490088400c54008034551020005030b82142c0b1041d5510314000044418032a0150035008903582a1341140c8c40e0a400c401ca0f02e4458426044044400000c4182182aa030400e0482400d43c90f0201d05200310041510380149440b0f00041045603100e00100321030103269880c002400840c01c0c00405884c001e0303015a26655070300d4181740142c031800c0079000c2c003505988682c1e4030b8044030fa0412100c143c2c865503070034803d440b803807084055040324290707810002c0c0318007580343d00007030b8203420001030410f4800010074800d401c4128048074049000e0141c546002544803120030748524020801140c01c00818070544189681b00e0380401c501d400d0641350711013194095089944ac6000380d1203044094200600201404000e0ba120843e12341c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 915878588 1250 915877338 915877367
    0x50703090b180f1b030f070f06140904020301031a090c010935010608100c0905090604020d240608041205030705130605071e0b0408030601020c060c01050105040615 72
    0x20010150200a501005001a005100c00c11122202844130829221040d540810f600a1080810701e030101070340402e03000140d030040c07041032074442d2914508442810a0954000c000501006800c6d099151070006501840c020541e2000c1714140055482780200000c1c2072800da41c07c0f4681c00c190580e0b10074000d00031284282c4004100007100e0061166610003524000e08040d2445803a61421006401c44c400700c83d014001c0e00c800701c040b455081c0507505844140310010740c00d03400511851030440040d0f0340100014200604003046000c1200c101c1701c2c403400b0250343c4481074002c031080360031000420010b00602e180640503401c280c0d9a403400024182e101d079043c8140440010046403141c41920200c40741d80c50007a04582d0f90301c101070500e80c410350098a13599044910300b440e04440708032101802c1d501030a115071580d100c2e11307103058581001d04405d0460083e41c6c1c01c0f4044d50786620107400c07486c0800c0000178003545020b0400c4100d50340c660100d0944180201103400d01d0b900401c81542124 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 915879838 1250 915878588 915878611
    0x105060c010e011a0a080615060310080a060504060b04020a050d021b12040305070b180d06060801020a11011b02030715060e0a090b0c031515130e040501050703090b 72
    0x1030410986409028100c00404403580b0789000703070b0b4800206026107680840152480c040039a1100d0401e81c8031a000c07a40c600014a4010400100e810a04000c5a010506401c50b01000b501d661410342001a03150060b40e0042e1a201030005200e000d11a0200c0c0c004116811494080c56550240550040354240f031a5594041001201400580c07010401e80d200c103029071340300c820f030100c1101d06900207010a90b19403003100d40104002502c20100c4145100f00d00e500584d0392000020025a8107811500712078054881c1c43c0061682024005056444440d484140e940504078681c0b0f42103803a000e420706003800d0000d46180c0011f4020048991090300a0507009445941e42c86d804083c1c58540d01ca40c80f0700c2115000c01445c64065400200c00d10301c034189080440e2650400d5030300600042e03070150800040c2e808100032910b41040081c08074074458104905041d409030715056021220f0313004019410241d0100001c020081c401d20740d0000305403c3c05c000040b420385170108104001822820712a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 915881088 1250 915879838 915879847
    0x270d1a240108130506011d240f0102070807090e10141807030b010b07111f0507061b02070302011202040605070b060103140411010216030f060203130f0321050609010506 74
    0x3240c08000c010506400c80d085034101d50791404003455500310a40882002c40c07185002c80d2003410546031070a00305c09050301c05030442c04900e041000d80f14030869042d04bd4460390500103560403003403044500400e911072001501c054016402410446201c40c2e144000d0703c0c1000c40c00308070340c9450310759410901c8455600440203a400c00c8529080d107540001e4400035410000041c0340e0520801045094030841c0142144a031400c18400d8040c80c03042c3d0528000301c142c5105a42c240b140024100c010b0142c42c0101d108901b450050760803a281c0d01c120743c01600f01c46030510565810896a03070241c00c1300c50341145024a000b0380100203004903130000b4416801040130400e140c1c1b1940100309081d0240710309014905080c60004080640c10000b6400742c010f40341805404502c40c0b41c00d20440c1e400008000f03403a01c050352488002e42c0b00914008a19860b04e00708400703d8480f0342d81074619803094440d0b0251510f10000282c000c004025840b01c51402c00c0100081615502642d60441c0d60648065854 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 915882338 1250 915881088 915881101
    0xb040f15081c050f1309020a120504020d111c14013806120a1d0f060c0703021501090522050a0303092a05090f040503270d1a240108 58
    0x2144181720403024840b800d88004203541c11141d0040000c1012901c0c1c04a03102a4100103000b901e80458011b94010361419a000104407910a014200d00340104000f104010f4102c51050762500c5090586800f21000f6840301401424480c2c08412256801e401030602240c07240d422740b082009804410b05a192400c090442c0c0b10041580e03105018108000100c0c41c00d010b0200060200f00c058051080510102c200e00359004103100e400002c456014100a5540b42c2c0e01000d0b580c0990303c120214801d08024500521410362224064007034010003142038140450206a1140818225079002540d250080c4c0090740000740207081540c14100401d030284c550528032400c40a00039003060914814940d06c11060325034038410140d13082110b4603407081e20380b0381c0564691303181107800801c982c0c420808034101d2125103840c820100180c0d9a040c0002c522100841c10151300554121200d80105040c4000b400004c910309602c001c11031902e0b04060124012040140111400c0c20305102540020945 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 915883588 1250 915882338 915882367
    0x3020c030c03070e2a040603020d2a0302030c0c01050c37180503031c05011203050f16170c1504020901090e0a050f1515030309040f0b040f15081c05 65
    0x1560b40403620720a1712247ea507440580690700840d4032429003443c0c41d481c44c3ea03101d100c0c42c0401d0030b000d600c0d5074108120300108068000b9800030300703c64844c40b004d00c10f070790149000b405620310501c40040495101c031446042d101c0329140041c1c2c212060301c0243d40081d044540c100c562800e120382e51416034001070803080305000c0c00a1036040305405001c00940b10944283c500301d20305090010b0202004903a07030312136004003d00c3c02d040c0001c0018000300403210040680130040e06401003101ca42032000d03025643e0780b4484520f11080e4419242e008202000d07907070001e0040c1d2408c0c80c07516805c000d05140a0f4002954041c0c140100116550360342d14034000040c08000c2d400c2480d81c03003001c86a0301942c400c025a41c48030041590144404e1000009107001c230f01c50080d09014030050300450070400c0650800c0701600c1003405440c0480d0390345000004d5961940900307070904403518400544c01c3e04a090354090698550455801070388020910754068000e02c0700346174443c8086c41c01680361048ad03500d21a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 915884838 1250 915883588 915883651
    0x80609030703050306061b0c10080f0610020f031323010e040e0c030a1b1a0f03060d0f141002070b0112051501030c0509070318020f04061203020c030c03070e 69
    0x10240310947c100d0013040c00c4001030043c40140211440480e408140070211100001110824440304520b004103803281032200000e011014640142d601c0a41c04003107581c40c54000d8083c1c02c900d0480c2800801545481d07401c003c425503603c0383c0816002551000280c00160101c018034080c590713841d03015480800610075040718100007408e48101c01061b0034038441c00f00110681c040510003483c4009445a00c0c1281403060448020505040c01d00010100055410040065820061500310440000d210000304039146200d0a0758580e40d0318505c1001b454055006050b480462040003440b0206a0411520781100c64000d1a0b8007130419501c2c1590510654100541c0c0041040d4000b0040114564510341914401d031480c1d9820ba50b1160100d00b500e154400c0c000c50101402da1620150030400c05092401201800110f400f5949480c9403580b0f6106000680068004000c00c01042c941484002c22814088004004075402d144441c20f030000c018000140f00e022a26421003540806064072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 915886088 1250 915884838 915884857
    0x11060f0c0c1906050106170a0915060617070e18091c0f020105063715030906051806181204030b07080f0c041a0c010504081308060903070305030606 65
    0x40708a40702c1c841c082d080e01041c03558202d403a241043e00101d8020b114221010480c0f465000c090301940b10031140d0310007409680015103400b100b621070b04500b210140520030042465555040e048039001890b120580b202078002020802e100ea0300803c5555480522680c3c0c0c0c0ca4010448450780700d40c059549002c6100414500c40205203509941058018180380c1b8040c41035002400f181c0d031500c007000b00e5100d072000344101503c00506d104000f080241c846282d81000046040312040d01c1e80c81403007600d0b0040c50841c00207620307107280908129446c000c01d80c00001441c0d01e030080c880303440c030b5058981c10018a518150140301034064140e4000704482a0502d20724042c0e19a500d4803404c00e00c840310b500700c0303090300030440701c1010480401039441900c0c4282c0341146420700706401c004c1500e096079000a410007940e10103100308030001e0320070f01c1110b024610411a0503a94030f034400c4d549098003041c0d4490b2071103070011020070080c4a004400c8a020540c18540390b9071b00c0d641e440004040e0b0203000401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 915887338 1250 915886088 915886093
    0x20f0325050d0e03160501080703090201031d0601081e070302041509050f010603060803030f0f1f1706060a1809020a0e1302011d1f050705060c0301031211060f0c0c 72
    0x58a1040350070040c41d2541d11070503010ba85d880411449002e802410b513106541c005602240000d0604e4443c0d8440141540f0524000c28002140e410308528031200c8691841b59800ca170004001c0c00204102000c41d43c80e06a408003450310060301001d481e054244806405992510344160916010440c8540a0040c0e008100b0a42c104a14503504c00017090281da001310380340500201e04141c0000a8910a070040d0503043c500d950b88001c400320040014082c0c41c120000051102c0704260725421000140c10241c0b04601c20f245401005840c181014001c103010303d08140041c4044540c0340c41d811182404201d01240f00ca00d5031000c074501c00110f40c000070180d99800140075200003d00f2000350900c1c001da0361160341241d04411103600d042c1c1f00510030703070060054440280910114284c0460500203080c800d06200703039525494100a8101c07000440180c0c000018020040b82041d00c43c075081040c0303041c1c04001d102900c22965442d01070082c1401140c4200083d5020f10b6a804650081000c24103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 915888588 1250 915887338 915887353
    0x5060315060d0905010b06030613091509030e151e09011407060c121109040513060606180b042102130f02040e09011b142512020f032505 60
    0xb4403800070207000d01c048a607035003401d100715001c0c509007050324010840202940001c803407115081009004d00c103421140070b503a08440a118031410b00c13407150614003e444442150303000702e0402911078850545200c038240305000e0007034401007035804000d401c4000742c0c240d51340e410402c0040c0c602c0344012841c68414000003070800108106500010108a0182c941290140030039080d07400b61030340500f01560080c001d1010000c14501a04002e401130703032100c032500035400305407585015120181c2084c0d010499a0b217810322144001da0f6072500070901c1840d41814030342000442c003104800102d04031003401e8840d002d0010355a902d032440d803016003148002c025840d0042c0039038000e500030703118148d08801131074005004020180101807902003c8804940c501c51440030a4440c009030900c0076000d02428806000e50300450001041944114890745503520582c3c45c14201d007000401c03a200454000d11481c101700c040c00416101001030200280304d40f54180c03140d618002c811000003400c00d118a04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 915889838 1250 915888588 915888607
    0x20a0c0f060e0301050103050c0103020d06050a0801140108060603030702040b030c10091502011e0c05070618140a050a02011b0b15030d0f020d03021822050a11040506031506 76
    0xd006000c0320306a03120103042c40c02e5641018200d4a007440050300743e400c203c081d84015031080e0300400c20000002c000080840c0ca51012442143c0d9580003020280c2d5502d80b40c0d000e9028a6603c0c80c01021035000a0455240c4000847e071640101c0100038003031511036031121401e42e1300f4010340c090710b003021b0f03d1501e24000009009141da4800c0c400d6082c2c060244043c01c00c45441800760800552030f01189180c14110072018500a2141003032440c1080004d12a85d400107515004442188480204002d803503000d904001001034a04000c00040d035000010500c0058800314249105540900705090303004044841c508240d250098010710329940c407810003442d481c8200240c801d409080d800c5418804095805641c0c0e42c13031406031280903a02c405040b80e51148a60001c060581082c0d0305840c01245d40404605090038115808035080c940340ca03000b02c4640c1c6442550b603c455100310502c80f054081542d602036104602406025150000c000f0790214510703a10200095000340800b50b0310545503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 915891088 1250 915889838 915889859
    0x80f030a0525090e1b040305070302030613021305060f03031b071509150201021204050c12120a0e0333010b0a05040521070609030221060f07020a0c 65
    0xc030340302055403122031482c0c20540e22841e4036050b0302840303481d60401241007180240703407044000d000c08540ca1042d4a080d034075011a5014000641c892401041310f541584101401d004004101c185c204800130201d43c050790720288903e0003050200c0e00064542c5405010038000840441c5007034248c40002491008041c1144a80444080f00300a031012292600b000892260310f440c0b85100140060009014602035400205410340d401e0000503c1c1008840d001003505000f1101581c1c03d40180300c04d03024078180b40c4d450009030071414019000942100346004818081c401c69071040040015551039562002c00550741d10040c052611000540b500f01c40c012842c0441032072544c00443d18000040403800e0100703449086c0c03600e40362907003000d0412003071021504020070840c9003403400e1000105040b80611244010f80344940c0c23000087d41c11401440300c40b410651915a01c00c0c100412070075084004031302c554104003410807030500317600c03016012440c0401c01c40303003e420a941701c0000030316907803034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 915892338 1250 915891088 915891091
    0x16060c05070e010807230d1b03020d03030b040510060909020913092d03080105060a120e0102040602070b0909040620040905060a06210537151809080f030a05 69
    0x9580203403013014006c09055032907480307210516008030301c450300c103400a80420807108402a20358091030143d5500d40000b6440c824049040d40860f51f00d030f003246074509090041a60041424404414192410a00401d840b2130740c031440c9001540440ca503201c980d02d201d61000f05048540d0301b0711080840342042001243c2d540300701162019031102c100c0c2505180324640c0c00c4070340c06841c1c1450716032800062004e10f07032203260309004001c02c8004000382c180356842100e000e1076001d400143c40c1d070704010010785030806603044900140410b01002c03400b5034402d400c00707522650110001c2100981d61801c05962045859504000d041c049000314448011754440c134403481d012a50401640c3d6500030556170702d40442c8000d0343d050001030800741c6c898099044527401c04c03045894a4010f94042244032480c2115410716156080c01c4e55107000211954041d0210060b003031410007040a240840d640700c4890362520003803044e80c581d0481004e1025503410354a03045001d6102c60741e41c0c5050400e5200801c0e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 915893588 1250 915892338 915892349
    0x1090e040506221b050420040504180803270703080315030a020916080a1116142d03091f021009030305041703060f010309021207081005070216060c05070e010807 71
    0x2600e43d084034121004842400e444008400d188d21301800d2109101c05801c0c11500c0c08020500c0c4040b07a00000c01803401144030394140401d01c042540f80840380707840c205d4010350300c601c02d6010a506001040402c800c803608081c1030b014803810b0040080c04207080200c64600694009801c80411510700c02d880286410350b1025901c02c00d190740c489c288002258440b5007007409030f62081c04000005020030385080480e41c001d0006d0808203125411441c0790030064032840b2003c07981440078409501e580e007411948030402801450038500c1202c00300b803e00404400f040c409403800f02c448040c460080c013881c2a048030400d02408240464103016000c3c01c1c0584040f20409800780c01011a074051409036406000300601b0b0310f0030003843c2d400440182c81365010980c0d000d90b15619050000004010349002810407002401c0c84002d240d00394000c8687c02802d41056400c5540703801c01446200c8a00e000762203107800c00c00c2ca032078140e0401b5454120182c00800b211040000081a1100e00045180c03c0304c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 915894838 1250 915893588 915893591
    0x522060f18110a030504020f13021c0606140a03090b0f1603060320060909070201091a0601080402042301060e040c020705060301031113140601090e040506221b0504 72
    0x281d9298608007101c2c2c8a40b0040445a4184810044203109800c103a400500003806100000c0c0d861000484081c0895480c00c0d885034000f45281900011407032003646440e0020003000100c2c43e02c00058480510105c80313290b42d2400007020641d4070b000341d00c4900d41c10340025405006142600711005c103000b003907803006100914504041500c0d8424003a0909032544840940610071b102c410030303a804150102800e600ca1818003210700c040c0c50b41b0710403d10038200707a03002003814102c60030948442d0300300e0385001641011640400102c0c1c1d800c003800a401640c150303400111414268202e401c07031010009180f807404a540000511181d00c0800031503260011102000f902c01d40c584140e0f50f503120303481040c5d0488018401000803444485521a160002416611814902c14030660480e5194540300740f520310704106000c503950340072080c1e41c05032007228084540e44c10952034195071185e0043c01409480c00d1982c41c0052a41c0e0a03400c0000b040d41300c0d40c04801040440104001c6d92414000d041c0150b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 915896088 1250 915894838 915894869
    0x212030a06030c17120f07083708060f0406050d120206070908070302040902010e09070c0b0601080f0a0b01020c030706120b09060a03140c060f07170f040522060f 71
    0x208000a0807030141c1d10798802000201e802d0f40500031203030091b580030520758100340140d03000310760000000e0200080c0501c2e00c0540703002980000000200c0c0800d6804014045440c003489240c2050741e9903049442207814081d040c1c4d402c0d0000e0007901c26500003503041400050900e0800c040800340d41c0e240c20710b58082d03400590b151141212540c8a42c46490110361001c48100b000d4202603000d8441c083c010b1501c400143c0051010803440b5400752030080c00140c14800314014881428246500311100b46049070460074441461812403001814001c0c1a07540c406c00000160f00802464002c5c14014050318025641ca1201815030361307414821020460915044040380d01e003a00b07038213105071170040800302c003581551689000d41502c403084010600c550301034602503544260241115041d4199600d075111200e14240e02c01c4200387c0701c0080194414450308213242400c40985d0140e640a65020050f00d20b90100703694102c11011018041c60302d4a00c001c0340100d4521060b2094410708005400300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 915897338 1250 915896088 915896099
    0xa120b0a0c020c240c0d170f180c1c0b06040c0203071506050402030a061401020601030804050f0102011d0715020601060503180a0515060301110f0304120212030a06030c 74
    0x645140044840c0140c10441c503004062601e440181e00300302070a00100746651013820b10425562080440820603400fa0314003010556101d4002e40da9000f0041c0c2c04416802c00c84005004402c000d08088024556003029020304802003050400d03000c402850b007907030866405000d00c18003544c28025203071b000b0344900040141c141809500c82102d80c2d0303402185480c05070f8540c040c0203003480f80050741c4591911400201580c8500256014540704000001e01e1454600b20000742801540124155005500104041407158099404a41080d156800d081400c100104c0c01010f0180c0511004920b00403100e00805000501d031080d1180102400a0900008026a500d00e424487d0f40300069040001840c1d41c413030090042d5080490b4000c4919003100780d92154180040d924019840001c00b004101040c42d0074001d241c6000501d4101c06c0ca86140d07801c1030001403100900113401c10b842d601580c1d8185200b0402040315034500306070a0786a082c084a2040030b403001e44000e41c1d00c1100040040761 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 915898588 1250 915897338 915897341
    0x90301090809012007060507140d0f08071803020105090d0b0f1503120a031503051e07121104110f07080409050a02030c0a031a030a1b090605101d0a120b0a 68
    0x368101c0343c100910403145400001ca8071f540c0300e00b0080340c80c200d907450308050a5032304204642c401221520350194150724044014110b5100408240811100c0070420015440d030701c132010162074082c60400c1d80c1d00c0c1c4840c0030510048640354010031a0401c001080456490201e029004401d01203100c054094100308140d6100803400f1809503a4104000000d2018080d60208240c20010ba90f1104020307034a480b92810140c000d00302008460803141584072002040c0040c00203410043d008106c1741c0b800c3d8480c0c0f9121140e070901c00e1b0007150745000d129003486d4050f00340c0d01d20141140c0740503569283c81c41d001c07156410034480e103084581004049a1040c0c10b90003920f105000d0350030002d052603031118044004d440c6403c8140e1182d081c00c1c1517408103172010300014940c280540781d010a41001c12003200d0a0701c0d025030110340010705d00310044c00180d50303509a4441401051904041302e1303640c40102d01250486c1452150302503100a80007500c49015800034001c540101900d0100d540c94407030b06c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915899838 1250 915898588 915898637
    0x3061706042a0b0717040602030a0e0301152c071107140627040c180b0c07170304090f0c200709090611030f040c09140606030a0209030109080901 64
    0x210740480e40e00c00c0c0f112501100180030224003031048400204420700b0310031040d0f070242e00568010780000413440300701c40d000107a40600d02003e5008002c0c40c00c5111140201c400c4070b0142c04044c1100700d114400308403030041300c4044100711812800301400d02ca00c000d04071800e0003180003040e0082c0d2500040700c8545484850a074003002e401c41d450912401c00300c3e0403040d2848075100c02800c0710f4000c40b803144c07100e103d20844030a080d00c400c144000280748000f0b000b00036034004c5848600070060119441e50118078041240c0e11004c204458a415082d22400d40c00341da04070900d001c0c82c000300ca601d49281c030340155981000d5520b9541070984401d20000c3ca030071039049440c0c0c0c0d07903001071310421141c2070650019a0300d0b805071400040b101d8400100b044158025a0030744c14a07401881400f0601c0481c0c4040402013001c10010840c04822118140d07001c04024003181c41400080001000b100054048580d082c40040080190384d040d40392000d03894003d05940390002c1d0914215000e000d00240130078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915901088 1250 915899838 915899903
    0x13060509090f090c010c1a0c130b030c0711010c0f0b041e020117090c0a180506120c040b0109030b3c130309030b0709030605100e15010306170604 64
    0x41c0494801400151a005a151b008441e259101c462255a4052000d080b40c0641c210000b0507544412454111101c2641c0750072080034070b0300c05c2050100710301d440411550065809100740b0b40360a90140127903061506480301038549017030351120404208011907501c1c070480c400c1e140802d02904106524054660b281402404114440d901651030410041685d13401030440c0c007103070001000d81f008154020600c0d0302200c0014844101070315011100e02403d588400e058400c03149840c004e030140e60b541c1401908036809955140f40d201e4140c4d110301040405144c004113a0754050502901e03948860134100301d0040211413001903c12403000302c0d000362040b50b109043d0004980c0b6005011000d000c00180c1c01c4003402000640003000440401b80d09202d29090b032100c0001030b00c0c504000007910030091240c00000040d0606204420540080c1740d00034290a030300903031002e0018010303001016190002030030340340427980c0c0814152000810ba442144605480c455100030310024054201d0342c6880e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915902338 1250 915901088 915901093
    0x5011203081b090a17070902160b250e041508031206040f090302060103030801061404060522090e0f0708150c040504050a0504024213060509090f09 65
    0x110302a10626070200c0c00003618040024500b42030f110008141820983c4a80c0d20381010546420803c0818040c01c4002d08010703c1c107620f8048840c00b00d8141c000075101c0107100b030400c1e40c00300b20b08802424001d800f03100415098581040060005082158600c2125128034140811a10303148511042c0d6030445a400e4025414507040c5000305058a800a18640c0c12a54a00c51050407a07040d02805c102c40d400b90700a84059411070030024100d0380f05030030443c00d001d41c180394017031002a05021a0100c4003e4588940c4801c113401011303ea00b4080c88803007000c10251080882c40340c002c0d0703000f40b0f1001c4169003220408800310300c461340c944c95039106594554108400035800a5138001d01660701c1410003070814601921400080c040722000d542142c540c0e42d40e5020042181030000300704d10000141444d86160100929500c0d45c8241407204004801150584000c00030840c0c40a07101a0810060200c0919881d100000c08a03000490601d03c40d4100a0100f580342c0c5080441c0c0c5d014120b8a4007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915903588 1250 915902338 915902341
    0xc100905100b18130c060302031b07050a0209041b0e09070603200d05061203120c0a050705030f0c16031e03051b0601030c050604140d02030109020306010803030702010501120308 78
    0x41c0000400c01c407281c164101e42d00b06018140030750701c40c0c1d405103d10320f0020780800c0d01c0c1d500c2c00c059445110135000801494410400d000700003041c44c111510048594010f02e0b80c558070341c40e000d4145600e410300207400c40c40c80302c1480104880b40c040341c09141505001001071683c0c980c0d4030941c28000303490909086d0000b000620000d813081e08034000680540205217480389140c401261306a0100441c480303415680e4043c0500c03803030b000300500d0031556a50300031428003100c0d190900b40160f02401c410a40440010413004c050b004100b6220042d80100070303652101c00c074074101070560388201c80e0032a00f0301541020305950b00c80c1e24640e02c140d07500800c22142550754030414044030382d60b100080e81030003014410880120501c4500e81c0c61404c1f002c010300301c1e5502d1850085014180740c7c10040c800c8401340010b20148802d4580c80914080845584102180a001107801481c0004001e5014020040040784500b400001076004a000741d000f000f1503a42d40c0d82030700148980c004018000b501000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915904838 1250 915903588 915903613
    0x1404110d02030709050d050c030610060518030709090807050d090f09090201051207020d0e09221104020c07060905150a08071218060f2d09020303040b0c100905 70
    0x1d001d16400f01c16420825905a00d82d0000341c0e039184060811291684105a05616800d0600000b40c000710f03e4052214001c0c200603000d0402d00550641c6505803070000308022186d5001c015980040050050810080060b42082c04031a44412030980b010b1140e80b8401200b98440d4810760219084059503010560500b500a800f0308041c0509030b0400c002030004030750300400c080103903014103515001800020790811000d8100702c0450300b00351007040403070200031450088050540c6050f40d804880d0984180500d484aa110740c50506203030000d00c04a09001381303102c00100d240580f603403034031141c0100742d4800c2040103500b450442c4030328103902440041d0000d4040c110103034200045041410450203805442c03821034484001804201d580c2c10048001e00c5000c0c0b04910b10498121000d0085410b81195200b0180340904c1c400d10446010700002c0d000030b8140d22481d1103c2d40107055907616507642c1140801c680015280e0f041500409002406c9417280d481845041c81c0d0220240c1855118403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915906088 1250 915904838 915904841
    0xc0603060d0f060b060f1b06041110020a0f051509030a020703021509030d05250519050709060e060406060e03060f1f09050f010e010608041b090906061404110d 70
    0xa50803038079035131124000045a611400030704680c4044e06412911014245441c143d0a02c1456840003580c0040b0300303010203e1001071140b6082c00c400c0d52030701d0300144049000c9242520038a40a01b502c0302100c847ca08001d40030424182003020b03811049100c0e12800c18454591041c0304005015078060785e010070060030850b030841101b1800e85109070400c800000031a090083c0d0112840004400059040b981e8078442c0c110552078403800710080403283ca0796601556640845d145080c032a00e166280c2e41004010400c44001d01030710007052180968030340303c090144a0a45110348901e040c100040750043c0f044440070318046004000301900c2d04c42c4a150704848501404c6040d069215a10060961310281c134060700405618000141c1841d1140d085002c2c01e106801401082c500394004210282d400807550303401580009460032200c00c803060302000600540d008030701d840d0803c0070394401d01c01d10f0fa001c4030440360420025995108040d0803c0110741503c0040d4a00c440f0600040136484005e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915907338 1250 915906088 915906113
    0x16060b03070e15210f070f120f050f0a1101230904050a060f0323010c120c0e0d0b0a0f1b0e040b09180c03030432060a110c0603060d 58
    0x7800e00b4210340c01e0030980d81d8642d0310b81381001e07016074440020481a45401c21801c0018202d018841c10f0f800c2c140056040038032941c040c05000d18005000d40c00901c0400d007c1031841505010445440100518082c1140500c00c00000e0100300d07039064180c030f641c0308503800055002c14402054a0304110301d080100a01015016103403a80d0b80c0c0c00003040c203002c08011440503500408054480c0b02c00800503040785c1c1d9902c8801356031070341002d400c1e21216420052100040c1c40d8400d010038260300c0540100e603240c610100e015400860b0080010911071054100c0d409056000f0052214a0038460103500360342103583c03200c07001d145241d000340007903100c0d03090382d62000c0c0018400304000b10000300082e01120140c4540e902040801c1c82101c039203104000a044954054026600700351401e650104060313652031904d00500c800704525513011000c200e8829813140e00401c07481e1140102c1400600b00c0c2030070980c1c000103118900e5101d180d45041410380340700d060010031210050142d80d4400d09031010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915908588 1250 915907338 915907381
    0x2060a081f090608061b090d060b09040b01080d0206090706050715020a030e0d0e0a03110d050a030f0e090105060306150c0307110f01032c030405030316060b03070e 72
    0x103081d070010000040610980014021000d0100300103050020150400304050700310b51100e16440340f00d21078900c600c0306079121003a048400805850341810000d014004021106a1000d400e000304802c0002e401c507400e043c0c2ea1840201d0704098041e4400fa40e80701810f46052800d43c1c440b083c01c000c0c9078804e10081014611031030036a481c0710040c0721070000ba40c000c4040030380420303117030458884584010070a24042085034500701c4920640007005c1107044210340800b5010881c1801c1101280d161040026420382c2e00038100e4207c103007141001090320b5104060b4400103004070302c501d0b04a24128400c1816507000a243c0c0c1d103551100010000848050700400004034400e108403500308030b0031b01c003500000d40682c0000c800011610100221494a00d0070789060516090f00980709105c505a01022030900d180b01040d203090a100702c910310b00030307a8070451345440000341100b0250850b004410313800e407107114140140c44000b0109900c0350a6409200c0711000c141c000140703881d490703c488010140c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915909838 1250 915908588 915908611
    0xc02010b032a180f180307030e0f0402040506030105060a030626011b05091e1504050423040b040c030b0a0509060106020c0112231312030902060a08 65
    0x1012030000c6070a0030a040300c041d240c14600d00301501e5030a880e241803403031241e003142d24812402c040388140c030419a01811030030031003101c00e002986182c100b81503968411141070440b501d03120a4580241a4900c504ca164010f5142070307001400d03400c00703000383e1b420349800501090450b0300b8007082c00b44580205a40000b0552103520000f078603528802c0d0b0798a03030b00020001a404075000300ca4182580e50300d08019602003c8030040e03403100d9900600383d80200104450640640c4603039800244600681d6130001da2220481c04540d00c0c6c0580311008208555080d50140030070750000b440c4481c004074046031244103110f4034001800050311503250360790161007000d569402c0c075103c0e1155469190300300c4914010366a24414460350000402038180100154401854800900d4000a0191032000304800e040350b260b400894203c2d481d010484414690342c002d2a140c2d28001c110b0300044403000b041640c981404905401226100f40a504c006a4014042924284a1107800c03980300900034403811680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915911088 1250 915909838 915909851
    0x90b04140433031a1312090305010c020a03030f02030106050403140f011109090a06031104091e05010b0907032c0a0b090721020a091815090309090b030a02040c0201 72
    0x184942c00007040d80c01c032407080d14201070451034620282154141078900c0d184d609010003548900e0301c4610441c0b82d0780040c114070207a0300700c441503c4070040703034000030100d500308041100ca0550000b0b503100300c64043da400344a880c3c5034007286002c91100380120380004004100500104403e80000e241e140703019812290f454040d001000c3c219200c98542c454020700c00142c41c501858036000c55600310030480d1003040003918603a2804040481c503401030b40600c0e19540080280081c2c42070000c40c62a1400c0c140030440b03407614110b4024402803601602c24100c520215207021b100f882006091029282c0701010381c1c0c11000c0d00700c10581c4409500344203124014005002811211080c0d00a160fa43c00500303034035081c0702c84070b180e10300c1e215038904070407030b051801401680e00c02034030108582842c2000241403500040c8100c08046004c0058028035041c0d41c810206200d5501035403066009035100c0b40f000362148054130036101500c0006616a0140618202620b01948006c44050690000260b171 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915912338 1250 915911088 915911141
    0x307080705060105010e0306070e10020705181b03151908030a0e03010507030227120d020d090b0c46060c050903072705040b07090b041404 61
    0x1540600e80407a06a040b04004026650300410183d4180d2000c40107482e035460480402030121205e06100b0307220740f00440d0099840c42c001c0c020017015120180c03002e032011a912541907560310013602c41c9038001103070ba052185030384080c2043d01d0180310700200c2d01020640b43d4080000081d0b00d050740e0341d040511191700080c1d4450810003401d03070203000d40303a965501210307000709400c545004010106041c01080003a184500c4414112903160b800b20702c2d940d102901001040c130408500001c05100d101d88045003030788540000301440d06030000c0c0c2d1a10603480c0c4a07502414140211203610b20141c2c0050641c4004440301c50b03407984031501c21644060180b82c8200e2030320302e40003074007000c10130344500c0100790090160f98022a0201d600c030741003651510f851800070079034035440c511404101b1442458408112000038001d05001c2c2c5d400c0100341b0103403e142c00c00200c103101c10f0780e2500100340104030000e00a5200026101200e10340c01c0200c0080781000280400b61104411803200d400184030441b01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915913588 1250 915912338 915912353
    0x10b0c1615111c03050a11041701060f03170705150123150403020907051903060e06030703050d0f020703060c02010c170108070b0705100e0f0c18180307 67
    0xc0140e40d65103070072921400000350090441c80e50341129904226856050580c0320012848a0b0105240014007655105600360080550315090501c2800000700000d680f100c2840650041220000801c0030aa0b03e880e118001c00040c4401040c000c07a4400201e101c84d00308c4043d02c035440c000c1c003c0e80e0b610000e030303004210b003400c09801074803402a0f1405503807503030f40b0000a9683c03030b0034007036810f01c2c1c0107201d00518182c00d018610000344a41a04c01c000f4141a20410036542c0c540c0b0020b28a080e03100342090040c01510840c01480840e100c2100020072600d00000c07014200c3c4d4124018100000c1400800c403050000c030f0381c0d00025032007070040000004400b403007544060a000d03030001880d00383c0d032003006254013010203640c4a4441040014403440c3c4c1e011a490040724049584141c2c4c5800c43e1401c03500b000a00c3c44400c490507e00710000701500d1020813002400030b4040d00760b581001d5554100800002d14891900b04418128005a01d0309400903003140c4880500d01100e0406459564600d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915914838 1250 915913588 915913633
    0x903070e010f0812030c250c0510050a1e11060a05040c270902041e0c020705030f03070615030507060e0a05010f02060f0402060f121504050708010b0c 66
    0x1124201100d00400c1240c5005103040050000c401c0640028856024004d40b58000030b820540f100800284540c0e0b00c105015040c15081d61140311820421a5410f14199010700c62050310300680030188188085441a011521028501c0d141c144004000c80030440144007000b21120511000081c120704550b01000402e02c0340c85140342c0400c1d40d181c10301e070a0002c202c055100c174039a600d44461091207030b0003c1401d0304250341d03980c500041172291400010003528074050071540b910680e01c040f00c2001300903000720192032026001c40c1c0e0f04942d204181359540383d1403400c0060b0380d0000c4c051031000610942107000040703e28075140e108107860f611001d041410550144010644440004405061a59201002b0304090070b1850000114440c0070351285401000d00d000c0203880c8000504550f5100705880048121484039034641c421000e491440b01415140103003090301810740342c0640d00d403602820b03201d03034059a10800680d00e403021100c60f54100079050241d50044903000c07a841c450524251 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915916088 1250 915914838 915914849
    0x10905061c0b13021c09051c14030106020d0206012c100801020c03040906140a0603020d09081b060a06052d03060708070e030109050606191212140c1f02090307 70
    0x140d583d130280c4691041c00b400d500c1d6075485c0b075081001c40400b145000c10500f8050411400312051001000b01c104d030721aa01c581d0034000540044004545607900080c0d4803012806030f02204c000d070341c8403515100f001007513010349a00500c41010310f20514040c507000d80e82120076507280c50f0325191903c00340c3e426030b0403d8040d00d030140c0c40442d0070041038469000b80b00080030b0289080e40d00d07003074003c01304d005401e1038040d0000b41030300000c81d94110041a8007414419800402c915250300031500703d000d1070a41038031440e00501c240c6012900d004101c3c419002141c0c00140406449040381e4140c00c1c07003840307810244889151403000b1140684082c81b209224042c03690303500c0b00c1440e14510191592480e080181d00030ba14080148000810000f281600840221001450300103900c0c456401100c1c0340c0c002c4410401007903056010010408040036100c03901d0380342c3c0c4100781d44070150a0201e000355150040954840c2c205003108041c0c403a5014850596003001600d40114a00464905079850380704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915917338 1250 915916088 915916091
    0x160506011d01060305040302061302010c170a0e0307080a12020312010e0103060c0c0f031b060204091d0a17090d141c090e0f06032b030b010905061c0b13 67
    0x80c88807154825903403409820359040400050501b624002d548041c01072204440300a00c0403030b0030645e8040d481030344069900c8102400443e05a040e55842d5800825402c1c01040034141c0d040520b142c04100c413801d42d00c4020081010700c90710b4403005043c10107290180198002005100040308800c48104e01905179821000d8155146160910403203000e0f01c2140c0412500d01d8410703000540303100107161015018549080c0740541d101460201610011008010f60302c000b40016454030180c00c407541d240214000f0138030700210b0000c5d0644400941c500189181c080083d82d01404620741c1c05018140d801410405031070030155110140c0301c5513214000056848a00361a4501d03005e031015450442980c5008404245449540592048050700c10b03040041c0304400600c040e2820050b4046500e41e042e542000712142d900c42c10445105007000384c0010381032074400b010355409400031004680c0064001c604e0400c481910696904000b0f04002c1500d07120809200243d517072120101d03460065480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915918588 1250 915917338 915917369
    0x60405010c020c040c08060d11100206060a14060a080702120403060b09070e060a0c06020d02131706040b0a0b01020f010203090c040612240213060c0b07020715030216050601 76
    0x100030f880c02e030020207210b204909003050f030000365511045d13a542026041d1103041007800e0602c1c0a8060300c00da102c08a4200320224410401945e0026006003d10000c3d40d04184040c1c5406400e0903844019000c0c9400620411110b441540720300c8109070300100d144180c0d55445241001c12107580c0c4164820303501507440e84a05507c51400200482e001200c6040c10381c10001d0680c080b40541c068440714200f4001d00103c00014000c1d150101d41d11104002c030b04540d074040f6100c81c4503800e055400707030300a1100d11420140c1e42880010f606d0740240c0d0020303496407103a510808220090704042c202c1e141140280d0400c0c7e482c0e0b000900145014000540c040c00442c1c0c5500140b008032071013644107682e07440c88881c0744000b080d8042582c080d100900183d802280381c000180b500a07100319404010800307c58480000c2c04c90748600140c80703040c400c1000e040ba64461040407640c60801b40261188160b08403001440a8003e900500407600d560307001c101d8071040c82e00c51a007040f0007680b00740700301d914601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915919838 1250 915918588 915918611
    0x1009031a01080d0801230a03140d3e150a0b0118030206120606070c03050303010320031f060902130f0806040b1311030604060b010801080c060f030a0204050306040501 73
    0x4543c02d00750140ca85450158903000e01c005880600c04c40d50340b19503c3c403070041e030081d86402207510003a64100d03000030300d4403010f071620382d07560822010b11100203104582080c6c546d15500a245000c0c10300e40e582c40e682c03000c080782c104036106500b900305809c0c3c0c0309100c00082c01e0340e40c00400504c0b91844c030000040708140040003402004101d05225024007030754006000581e00d08040e501050340a210030070040c0c0da4880400c0680c8228040034085540c40c800010401100100071410307288540b842a580c65504081406940c8141001e65455003018401202049440514114080308210081591581c0300900c41c12a40202d00008003201c00503020300107100d44002c01c000801420009202c2403810b82c9402e003070700b040544807541800306030941c1001c0c0305000380d54840d0242c0040540d1282e04043c9850070007000c0300305203107010820300c41c00041e44200200d506500000c0142081e0300d065451001300000f5400240703039507822036082c080802c02d904d08111803031281e40f080d0700000c2c00c43ca030038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915921088 1250 915919838 915919843
    0x90a060f0602030a08151c060614040218040c0212070b0f0f0103080d020307020c12030d051f060c0f050a0308090709180f02130c090e0f090c1009031a0108 68
    0xa401c51000d65004011507036000307601244040d8010f941540741480c0c18000000204d0841d00100001c00b165000080e581c00c1c80a543d10031400c0303c4c20200041031303203c43d10041c0000e82c022544082c0e20001003514400660601ea007200313640d82168030580300071f01840346694115802004042c5c440c3c070706d034400300013201d030ba844d0300725801410000c121845585141d54486042c032444100d00150b503000310104006a00030800155402001040c801c1840c0702000f01075581d8009036a1980a1801c00010800d203001004811648a03c00c0c2048102c2d54282041a142103060701821542d2000700d48884020510070301000c0e41d0070340310b60745070305003030a00841c060715010094102c035541c945400744101260710700c1c201c190402c69020054039004882400000c00d98242ca1a510303c100b8204400203841903840051030094030ad05108513142a02e501c5080441c40c80c0441d54001a03900409000c001454a03000c0d0406031480c82c0b400785000f980740c2e0380e0100328041da150700d50200111a4014407052006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915922338 1250 915921088 915921119
    0x20a0206062b1403030103081c090c0501140c03041202090c030609361c030b0603040f0804031502030f060d02030705130204051203040305011413061802090a06 70
    0x21070b400c520a680407281541c2c00e0081c0210300d6008a2078441034002c2265a1000201c505112015240c0302d680d030741818000340c0d000b03490300552100490400d00003003015110300001d894120541c1c1800c0e50500f0010b403103000d00300811800c4031400b0322503940016030801c02000135000c90490000d05290030b2051024485014182942520040c0300300300315030701d41041d103035480041c120f07102207c5400c1442c0c1030713548900c43c01c0c040b890300c0300d4069080c0d0302c250004c1e14090032030054800c6c4181d1500880d045007180c00b102001c07640800c2c2000800c0119040080021005001d1506949010358980d14444410842d00000103150b40110400040440b40e0705d14992201c07003607429200e8108190700103074907030100780102032003040c100c8070b110f80d10209a8140d801030680070741012180d4440c5a2510703a03942080c4011200b960902d80d100c24169200c0c540c860080d80c4407001462040c2d82603031620003030304d00d941d841059180180d6564001d60349030441940620f0307880c07a00161250920230010707044400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915923588 1250 915922338 915922351
    0x424050408120f0c060f0103030e0102031201171c08060108161e020f0a0f200607030c0305070804140a060807050a0305150316060305100f06050304060915020a0206 72
    0x240410820300802280141c070003003000721116030300c031110044a21103000b1804d4100b5a032292204010500711202d460318140c0740079481d078104101044004a030f0b2403003046442114189014010048101d00c1c41c000585001c45100391400c0b801543c000e43d0804248414680001c0c0902e000d201a650700280099045035400c00004051b8041e0030000e00840c1e010039810805501c07207401009124403c0c004034400042d0310b03050b01e641302d100d0300300720880841d40300741920384000044903c030100035071384445665403070050003081c1840b00a03101503500035842c620640900a04010380400107250000800140440003004100c582c0124180202011160040c0c0240b00d00300d802d200d01580c0040c00e4400d254910310b40482c407030351008010380c2e00e00e45a00c0e54581510903852410703045900c2103044001d0b141e503980c00f086241e4901d00c1700007840c2c2c1e0f035110b8600054007100050083d188034100441e40b107409a2800b244403d800d80da1204641c41d06413202540c06e602043d07205540c1c2c0e0503c103440c6c01c901c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915924838 1250 915923588 915923597
    0x20a200d1b1a0f030a09080c0a140c0d03081f12140d050f090a0e0f1618060807031b030e010605010c02090f0402180c03040b01081911060f0424 63
    0x81e5a24600c0b80c0c0741c810b041442d0450100800060b84a5401d9017044502c01d074040d12080d11400d0050b003480d619100e641044a030041c0401c1200900c50001179140c01c88200105030b4000804680c9042d03c26040240c0000440c41d85042c204002e50804420a001000e404801c0b400085c11400d02d0028007200513443c01d50f070342200c072a01d84459841030940740701e0101c85d002035903070781c1c2500c0c00a032003034105a20a80c00c084000d400c00090b054945040351142d800d0321140000083c5071142100d40403d00007035024912802d2100b0b000182c4146142940989075007000602140400c2c442409481010032400c00683c0f264600c0d40c082500307000c0c0e00b000700300c01e00700007105003886e0f80001c401007001880d00d111030484000080c02e540c0c8170f20340f03900428a100a00e4903c1d083c640440c00013507104035420b03222500100000200b0440c000388247c1c650004250454003241340c0d990f801c45d6400c0b07080030598406c00130310040c480e1400300320042000713218404e01580c0d1305003404a00b00c80705090001510610 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915926088 1250 915924838 915924869
    0x90f010e0c01080c13051c051902120a080d09021305100501090b04081c030b0628050711040b040b22050901090312020f0d0618050a0c020a200d1b 64
    0x5240c0704d680c2c0061b11800c0314449003e0b80d4005c1442c411f07014032100039100d03104007511030038203189440c10301d002d2034000d03031b0600304034032445068036a20380c01c2141c01440f80104000004011049601280354a44020324001040740b0803101e0710140d9000f079503890400c2c2d0440390708101c01d6030040c800030010107405124504062900786440c6d107819002c0e100000d80b00a046119100f68803940c0810113050004116a88503221115016aa02c070800040b503014500f40c020340d2516401f480c1900e000300e07400036840710708000a60920000e88601503065402689a045d40e02159403000d0044c0c01c205581c1c08075088204908100c0c0081d07980c003601c10030f0641d1401748510082a030003501e80440c544050005a541d19010041050a22030020300304440ca02d40780c0c1c0407505080e000a030042185410034140040e8031580754020031240c0008850026a0114040c500000c145824812107450202c10032079a03282150080f03040d13800c10038801c448420b4504004c0c1c0d0000d42010103a4007170f00d0b00150001c0701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915927338 1250 915926088 915926107
    0x6040b0418030507150c0c03110a0b04060e0f0106120515130803040c090501090c03150e150102070e0f0601110706090924080303150103021908090f010e0c01080c 71
    0x80700408005400c10030005400014409404143c43c803d95030150104072a00303040c480180100385a05045002402d440180b010403600003840381e042c0e50700848510200d4586507110402441c0c0c1c0b4415103882c0c000c0c601c200036962000c2c410080200080016940c40e2607c0e0300d0240d040112419101c924424401c00780b010740c81c03505004461103580a50303082e550351154141245c09400a07030000e1400c90414002207a4101d554201c03200c0c20146840500449032488180362030440345000781d10400c5906d600080302800c141c05140002c0806005a0f404940c4640b00d00c011400c00300c803240310f024142e50a02c040f82d40c3c064640020b001840c40940b41860078820300801c030b02d61501c684003403c0d0b1240c110040f4110003000a5001a0b9400d685090b080c2d500d10160b91642c000311400905580c4454190100f54024001c451110b0000c0c0000c0f2404404060181c6020b078000e0190080e41c8200e01100c8181c810900c511100c00d008a402443c1e4061014001494100002d101c1e00e5411401d002010a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915928588 1250 915927338 915927371
    0xb040213050114070f0f290c0f09450c0a140c0a03090b130513180c1a070206070210112d0c090708061306090506040b04 53
    0x2581c0c024030303203000380c41d10040c420b00090007111005824900a007045008000106042e2035085108408202c403204040800040d4461224141c10340c400c09400014450000c0800400102c1002001d160400f11020f02040001c2d046400c000c5951a280c1100110224080e01c2d9804120500c00c1074509904038082c0b00d01042006030111000007000710380f0344845806405101c0001d61005040740d22210030000090f0703900ca10003401d40100d0a100f070b002c18507501101c00c83c2c3c0500c401419210846141c10300348030001c1c000001920074166580850206074021128041c1200d0294200101c0d0300e040448810504c0c4248a1080201800b00410360058640d041903e2026804948100110003005020f555554900110f1665409151400c80b40201514003075161401c0180c00c01d1f220030390200c0303065507841030142210340c0b102a003000a40034501c900c0f5a03682c40100540106044081c500c04001512100c3e0000000d80303480344e0030008a03041c18896003000c8032080364140000701d0312012018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915929838 1250 915928588 915928627
    0x60219020c03011b120515090a0c091703040b0c0c09070c0b0109140c1c0203070c140d0503180705180105011b081e130905061914010f0201090b0a06090b0402 69
    0x170b00c0c1a07210070000d200051a0101d079054120040e101c0442c0e0710304203c2ca40300400b60700c0110408100564000314010106203480c20756010b030000218a0b086c01c0c80b4001000d608440040340040c41580c244110305d4450510300c078010611600c3c5d4080340481d0340b61001a5080c160401c400a625201d98610031040d000c5500342c0100f1152492070740c0709101c07030002c500a421a03d40c841228000801c0c88062076100801030311a5010701440e40b504e06074800c10395240e0743d11f40c0218001803010320204a82070441290710351010822021900d129a0303807404200c5540030441803070030014060004000c07a5810980c40c002044125101c001c04141c0e0360b4425455000e05032451400560b01403501100310100c6007202c140010b80030f00d034490141c0e0b031740304c0c000509812112603005040d0100760200030b0b8030112400007966034031002c186c1d07007030f0288004481c042000c02c66401190340300c4034194080f0b10419001030048105010200b40c2c1820000c61600342c0b01ea610509014901c10488003810401c0c0c060740c2e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915931088 1250 915929838 915929867
    0x90603021c060308041706060f01030b0a03051c0906050a230403150501081e07050108060d0b0906150f0a030b0c04030b1608060108130f060219020c03011b 68
    0x1621010a101c486408261000351a01c6a614042d000b0080c4806007000c0e00464003451b052003140401d1544045d101c6400783e9125030400c0682c07a4a40c403a42c081c7d0046c600020380a0440354005640361500c500d007030315104001c190700c2480c6d80d03442c68256000c00150301a21150401d01e1514200a100800c0a035070101c50040340003000094443e6096101d040703400a507003090031190010030300280600200002e00c55007001740306100003090024a10355a010440e07803000041d081d4546071100564007084028840ba5000c405510355030001003070a0000341c0145c0410008200c14a000c68101001e82d02c1c0c1c009892180c200c030790071001c0c180c2c3c880b220501901c0e80044103507001c2c2c5847d404d0b400140510740000300810000c0d410044161108c184c2c1c4031400100d6501c1c0e503a103403100703030066a1400084c0c0360040c440f5202000600407070403444200b90b08903c28080145000c07000c1403811804002d118403140103800880100c001440c0034040c032403e1030075800c1c00d0304100b800c103400a8410080031458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915932338 1250 915931088 915931091
    0x50f060d2406060504081c090e070309020d03020f0637091403221a0901020c0a0f0e090d02281e03080a05040512131511120a090603 58
    0x10600e101c00d14908006036548550140000c41c2c803110043d125822030300803d51390b40700300f19940a000c0c071b8084504641705103a845401c0c842c1d040450700700c042072005003c5001d050b00c0f03409400050311010b0b02e031a20306000e42c2c0541144090303c802c0c141800310103032040c2c0703e0f03110360981201082440c01c8010495401103500e41c4e0080c00a040110141042180240820700c0140715007010b401c02000030260640e03d4482e90401c0b00d0010340480f64903480780180980c0c04402030240c001c10800c880242503440c1c05004a812460071440000d400084030b4010580c0e60820030810031140702030308849070f0090510400b51a1000b000c000003951004103d4003100009032041c109040c0c010039071849283c1540250b1300744000c025009401d003010707004031000c4002a204400080508406210b1b1902503507004000e4400f0b1076041c110303032680340c1004d402201c01d030600140000303941c483d00c0030210f941860b6840e00000c40c2e4601e0080c900b07001410101002150041000d480903c0d4441c100ca016503a080c00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915933588 1250 915932338 915932363
    0x14010c021002180303040b0705120f07030309050a0c14030114060d020108040c15030b01080601031404150b030105090606030f03031e0c04081518030a0c230a0f06050f060d 75
    0x80c4182ca8405514a0130b0b054040068040350f6064090014035200780904101c895031a5201c0c01034100e07228480141d40c0c0e640080c022040002e100c0c0e0450f066043c0604129031010308980c5a4005150700c0e50300506109140c81c50320310040c10700307004540048003485540c90707903031030503402140005060100c000c1c10081440e00040130884018028030207000c000301e251101c501c4001020b0010002810703000c3c0800d07815400152550710034081c0006801017038442d59103540740d6513190b10382800038010303052072981c8480003a602900c0922910344229000301c01400300381014800d040c201041d0780500c1509400c20010003000d120303800e00385900151200851101070703840d4032900c1c0b00c40c022900000c0060250452514115194000c224011032805540c2c008141c110018250740388075041d5114080341c40300e461200818840c24001c40d85001c070724569180c0381c028460482c14440242c10840d43c3c40c0d0011011414802d251107001d0380000711307245080b45410080d00040c14803207a2038005041c0840d055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915934838 1250 915933588 915933607
    0x30e0f01031d01050402043206060903030c0303061507020a06050703020a020d1b05011e110304120305120c030105090109020327070e0a0b010c030f0507050709050414010c021002 78
    0x1070221100c2d4858070700e519040024080d0840c040d01041ea0181d02c42c504000b03115100c90a45080c2d481000240d400700350312000358050403500d0100062440c3d40c4094203001a22442c1c806000603c141310281d8051079881c58020100190228082c1e801c5018000c02e000c9240180c640e1000c0c80192030060a02548409552408034680032010034025081030203421041c003001003c4520b8400300720b22460905509840c0c500446080c2c00840c24643d549048802c0c08100394042c803102601003a001094070b01d802d407501401c0d404040e030b5035000c034009903000903140c00c809100494035410120101c8485c1c07441d4907190000380d20ba0018051500407560010124101c0b900b90a00e800d00070f6181c504851440070412364450302c1d10003601c55142a001c44900140400e940340c0300c0c68080200503103920041c0c1c0380a480803144800e9801d03085050080412090020400411159004109296000c140c91401c3d1810003200e420340c3d03100301c0c010780c1003000b0700c500030342c001c103031002800c107001d00040e2552040c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915936088 1250 915934838 915934841
    0x170601120b090a150507030f090c0611070801020408150903040b07060c0507021519080609010b030c0d021909090b010207090509120301030f140d02070b0d2703090909030e0f0103 78
    0x42a008100942901d1404068070b80b0380c00180c8550031b10f882c00c0098034401142030303041d911425001090040b9030308050015501495081124002103011503030100c0e194000c0c282280c3c0709804c00601507000b01942c1d141d03c0202010700c3c2c0e011501001943c100b070710388000800140602c0d07000900343c41c0c0351f40000020900c5035040ea2451340e00100507080e2800101e02c0246594803a0b16000e281c00410314031007529901500c0440c4c01088081c01c5142035a01c3c11404240b16000500b141d070038080c041266404158450003e01402c0c6040d040385070203030080c901d0240070703000a07038008201e09061003d4076034180e0300840d0740c0003281d40c51080420550b88030740754241400b042500c07140c6248008000402448050a4440d0405100e1468080d07440c081ca08040c0d42d403040a90780d100142d004c0c81040c040c1c074000b02c0150941c2051204c0204610901800324a07410300700b58141e04c4a4072440352107070f0134945d1200001c1d0060950803010013040c4500d0b14000c00318801c903921240200802c1d507012205901c42d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915937338 1250 915936088 915936103
    0xb1201060311071b1e121202150a1a0103060b09131d1609020301030c170a0b04141204050a2705010f0f05030601150f031410170601120b09 61
    0x811000d10072030102020880c0707007aaa03401840c100c22540e00a00d031005d5060f14104041c0e42041000403402d80b410354030110300c001011100d00c00c500400440707600c1100301200c2d503030003401050004955030505681c216030621040d41040c0c1014203202081041384014003c482151005481c400104480d426000c4060921a02c0f81000d9a01201c1a02905640030403800201c00e20100d8007080c295035200808140d0000307000203400008405810010b0304a01d03521444044000030542d0003080346034075401484c06080703c0c15104003075003041104030f58000317010001610801541c2c45090a00b840086101003c080c003443c070100141d84054503810040c8036941d889400760341c50074060340d0b0311a200c0c914005030780d101d11021715002c3c41010a0b41d10f00824040c1c10f03124414403401c0d41b1103511800f1504480c40c1c00c11403050558941c03610081c00021032009104910440c071080c00c45251600c101c03100780710800c0d0420036401c0680188078103180b0403000307040f00d90071420141250f161070140300e052940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915938588 1250 915937338 915937343
    0x1020a08040b0c0c06041a07111c111008160201140925060c030c0f060606031a04050c04050904031205040f02040b04021e210a0906060b120106031107 66
    0x2010500195000380030005040030520002079130303540c000c1107040c01064010380c003410b41124404610107441d0540000580070b501d003e400012003400d090b80104001940c4900750407030110a24029400344464021440e045001c2a1040e200029484000428506015004a001e6501140310a101c81d01c00d411101c8250f60040c0c00d20300d0b9003040c103092560b0303c83da0720070804d00805800300e440300350b6052800b2034202e403100d840307180c006201590103d592a45008084a0b012403c0301000045120351040d1005000a07803000102c4200c494000b07800785103c0810075101e14240b00c100722000d1041d6003a5812254107440391000354807189029180340444140b6002200d00d007008000912020440c2e02c84c00f1402910b04228071404202800180c0c400c00741074040b10095070300392603501e0451100a041072242d0307585041186404103812444034006443c1c001c0100d84558035003080c02268419140100030100100e4a00b040c200b0a19003114414480d072401d25549076001041c1803036500460704846d6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915939838 1250 915938588 915938603
    0x323010b1b06091b010906080f1308070515090f0a1704031e060f0b0303030714090d0c051e15090301060b0d14090c0a090f0b061204030f050f030a050601020a 69
    0x540b07200314568980c4061103420004254040701134141d405400c25200740c88042e520354405035944e13001c0142d03140c8042c20745600c20142c0803003d40815400030280000501c600080c249103c1a15244009440003a10390b00d4581c010100f01d100480340045c1e02a032440c5c2c88002d0002c04100103080d01c03460300480c4d001510048070030011001c240030120b25000210300c03032902041440410019901152600340344070b50194010800301d00218015141034100301701d00649149012591000314500c201c0384801192406200c4c001441503203843c005c0804950f07c466040007400d0001400116414182c1d800003c290000182c1190161006c2d00b011010b06008140140d0300c3c16070741000c1005140d0840040f0f01b0f40c2510020980c080c03000308150490b9030b001403446c11410b01f003146100040c4200104440c0703e41e42d07180c1348140b0b03480708001752400048400000450349082d08015200c60383c006008800c00c003081204d4103602d440c1500b0340390016507141c00081c5c240c0c0c0d0540140d146c013a00100140c0701c1e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915941088 1250 915939838 915939841
    0x4020a050a03030c060f140f090a05030406021608010b0625020a06120b0a06021f060807080f0706050304080403080a03140405030910111b010c210323010b1b06 70
    0x190000182144d4030b00c1080f04010100700c1c030307060104661b504400717550000c3c90140412034142d0110500c80c0c100341c02c00141c410542e9180d50306071655006501800240e00003003c0004084101c4550100030200440240000c107410700c0000e04c0ea01c1016039071407030000140c9448400c1404c4008400d052540504941c9140d030f200c25010344032400055101c900541050024181403c0030341c00441141c100c0d0300108020b1920b040ca9100076002400d407001441c0da42c01c8000fa03c1401040240020720031038010340203140340d41803d641002c903c0d1300000140300007041840001414941160112900b00c010703e92262904201140600203c034602e6107041c7e548414001400070202c000c0c0801d0004480c043d02041d5981016107483d040d41d01500308541100385286516a8448180c544407101490040340002850f56032840140683c0d17100e9500c21841030402040c160584920102041001c81ca560503180070340c00c1001c802014000c6445000e008201458085403001d01c101c424407406040c2c0745513 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915942338 1250 915941088 915941093
    0xc03041a0109091707020d030302091c0809010f111b0609091504050601020f06160e030a200d1e0813271e0b0d21020c040b01051204020a050a03 63
    0x2920f9090360940b0140c0307640c0d0b12030111000d6082190303030603540030300107284d028282d0b2015002500100c8026420110345030340841007004a00b280d0144500c204119502e0f031840c40b00040c20202c0e0b0303080420034403060010348005280c0005585494520103400400f41e0074015010804a0143d80c4429070421200340920010240c0e103803882102c03200c152003c20159481500482e555032401c248a42c0b260021400710b4910b42045154004002c050306140404089040c0402d284c84c082180540e440700c0364100d40d0906d0a00311321400f13100c40d0300700d594a8020101d0744611410002041003800d50454500e105410002c0c004141c0e02c0360035003400d06000e401eaa50001e641104c0c411800210b8005210101e000c00c0403091180e465040c42412654140840e030b00035600080c040d0303c1d8950b0f40f14414008440000d24482c40b010789440c4840b142c41100703031440c0d00103860280001d0007103108038244440c25106990000903035001c4100705190f41c40589590000c41c800c0d0304207400c01a00800070700c901105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915943588 1250 915942338 915942341
    0x6130603050604240b0706062607092318030310050a081209150d050a0603060b0f0112150b0c060103020112051b070201030f05100f0503070e0c03041a0109 68
    0x400d580650f41030180b81c5008080ba08050b0003080500d011940540080c051040741801402e49030784540400200c5646034820f0180501d0006a044c0c1c1d40d050307103461803200c1c84044c060301004140d03003d81072040d880c44c00c070200b60101c10316103481e01c080340020005801c0e202c1860140c0c03120064605980e504c0c01d060300e00041c6840d03135000d1980500721411000407158000188030b4000741c000c0c1412420116041e00b0014000320b540705000c2034500600a04d41000550b00c40d6a0058910394000182140355140070003c2d20250020144191512611400b09980050b480000c00340702210001d58a21001c072030b044c01000d250400720481c1408036442c181c0c00e50014055040c2d0f4002d8840702c281641204514098a034115504423461000703001030f84148001078003a00703006105060220300201002d454500300c0340100c5800e07400705580801040040c405400141c003a100c160003420845007420031354589400041d15424400714004009800d110705d44030403199200600030b07500e0541d65290150070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915944838 1250 915943588 915943591
    0x601140912030d0c0e0d39260c011803050604050a03170408090904060b221b0e091312021c0318020904021309140c010305010518060613060305 63
    0xa030619058000c0240e9004030361700407031030100815180c07502c0c0c040c0e034950036848840089240342c401028081c108651142ea801e00003800015011050309140401640707580c1803002c010862810200c4880040e0240407030000a000400e0a040940f60144400b40a45035165031015095000c0d503c140310420401150031004907001e9a0f810105c0032207104010030305030701580d0080019008104881050601c072a00a601070f02440000889450341c01c00f20785445065080c1c10310000110301900d01d8081180f281c08481d0000341880902c46501c010080d000d491103e545074030503400000000c1520f6150919081c1070395019001c0d00720304001110180d07540910444000c20741078041d083c0d80c01d040c8130740301e1006d10300c158880300c0001c05280e07000d01250001c09002a42c0010b01d05079200604419130055155961056039104d1200c502004030b5414030300043d0400d41010b0038007004100d42c0e0344070702036446151888507820354151507920003c1c4051041c0c080c404001c1600e8080050090703099400075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915946088 1250 915944838 915944857
    0xe09070e030f191a0702070e041a0406090c150c02130207020d0305040f0605210901150602030d1104030c150528080603120d0e010b0d0f210206060114091203 69
    0x10300c4c4c0d0201240006003184c00407100f1900591092800b00024101c3c07181340c0e508036003c0e14103610a00515203070000c840c04200c1c3c0c140c61868030399101c0ba0402002484000040035103040a415011101e080100b0116a005001e48150b240c0c041c0d1405504940c0e0468801c03070750007046804402101c1ca40580180c015204031502902c1c0240005840c5004000b1034102d0f04820000e6011188001c140045503a80a020440b141d942c45692080c1d0301044569023010341080e400560b124041c00140d4415079010f0a80d04e01d41d62010702007040051000508602a5003074041c42040b000354406048a282c016000360301ca1005849a8080f440d007441d070100c4081c413607680e49600490b605c074001d050b542c0310381805e2103429520800c08202000d6441d0b000b00c420110020011507404a220005245244c0001301a11a9a1000311400400000c01c02480ea01d0f002c072078095143c5007980c400651603c1005040605021a42c20b111100c001e542e01201c80c40ca4008010002c00c00710f4501c00d90f03603a0424840c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915947338 1250 915946088 915946103
    0x105071509140f03070503072a03080310050f060a050c19110901051206040b0c0c0609030a0801060c05060105010c11060c0601030b070c0506150301060e0c09040b010e09070e030f19 79
    0x282040d894021003195449501b100055150216665403091424003403440c245145104a1075a1049002c1044c0300b4000d41c001c601aa8590420302c00f0000c0584841c1d02c8240310340550340844100e88c4841094843c0d04026003041601c4d00d548140d414203218525a001d2501c1544e2203040c2d04010040c4809540841c5c141d6074001160f0701c070018030002413680c0d8202502e40c0c3c800c000060000c0ca546035110392104013100950b0901c948603403907603d007050a85440d69950404190408640d41c0903109600400c581d203000c050f034104640310982c4a240c18080e00c0d0400c10702c0341c1c140c014003410313000014805601425080d6034100418603642c4648081c00704a80240303050002c100307094802d000751200700e07800c480500030b607483e80c10f46a040c4140078424141c01d0354a40100080344898050064400c91015150039030340c095007000c000c03c550000d6501d031705001204120003c01c0d210000c980d1381c080c4071400c041d00c1c0e101c0080300103460054424450340b064418011072910520308019500000c91140f1030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915948588 1250 915947338 915947353
    0xf060c05060a090b040f1110020f010b030a02060409020f070f0605070e060c030f03130f050708070e160c020d20041109062b0c110f150105010507150914 67
    0x301c10580310001d0010313151254150105e008550541640340310300e441085001c14858082022403420303500c0c10f00300405600100480c144507a000e001d5000c261000701c0142c4103034109940007803000e00450044600050380442ca072014070110380100c1c2c850a4009810103182c074030b54a01880a010201c8444c800a41000400080c3d4100a010b80e4040d861800245040c0b000e010b4103000c00d0380000340985001507080c48404003186102c0e2010707590700c0c020805051040d080c00100362600bd04c0381d200c103610011080801c88008000309102c80030109510b4054400f01082c00095810300501c40c01030404e641042800318178605640b446502410244c50034011704080c1b0360151894043c2000031a0403402c1006179482c03014521040c042e6803402001d0005002d8100a070b05411201d00e8400c41003c00c00340d212482030f080041094491404540b8000c00746011400802c484540b818860b5a05000c000304035003003001941424051f07030242c01c000c200301c0745500d400c0007121150b24000045840c010b019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915949838 1250 915948588 915948601
    0x4080d030920060d09050102090108090d02031e090306090c130207020a090c051201060504091a0f09060a09110304110117190f1d06060a05011e090f060c0506 69
    0x50120381c0e03504201000404249264070340c042410403900c0650001c41084840c0440c03905100d0488241c0c0601d00060720342034444005801030001400941c00380d4004111b4041c020380c000119401291701c500900007022420b81c04146038005c84c0790340340e414060941045400d9400050b0001d0000e4112500350203140006044802ca00c90440c004c0d40100e00410140034918880d040381401c01d8031071a0141c40d103265100306240005c1c3c00c3c0c00c80d80c0010000102001404540d01881045040000c182601401c103600010070103000c50b014140070b01154400144a075032100c071050010001c83c002032141603010310301c0c1a0b040d40216030448151403440001002c1d5403086190500c00d507031802120050f40c45c0c5618408420144d0320b5441a826140c0800c01c5412000d4068050810003450000006050000c012420302c040109040d000e8541c500e800c00c00c0344e0713000d03002d0550788141c501c44842d43c0484043c100d0b803e22813900301084000d00518005000d99216040404d224001c00c185d4140d9290356 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915951088 1250 915949838 915949841
    0x105060301061e03110a050a030605191404020f120d020703050d020a03120e01090602040b091203090f0d050102090411071a01061e0c17070b31060b031204080d03 71
    0x164000351110041a0081c00010b1170710200015a0034010218420266100b00040d1040c480d50411540103403a071003800209040843c0000b40c00e41640002d1021346c3c8070451360764042c1001003010384a218880220342c40b5840314030784507040c4440301c001d50740901c011308406561054244001c4609200c3c40b01080c2500d440030a078031500d103602d43d0712410511000f01000d000342000310300340d04065588141060010307010f4401400103054030b01c4d6190b140d907610000c0000f0348501015420302c80e001049202c0081c2c0d9903600b86010403008441c0100c45020031305081d4024064a011150064601494081282c0c1a5005841d1051080c0300c4c48441d141c160208040a0382c003845801e012030861440e5a020707000c0380031440650b802c20324240b407072490592902c0844058038070007503030b03112400560030060007590308510f548550005c01c08010900c030707250184028503001c1d00b400c50b050043c0e0440b604104043c0c01403900d00200408072584105c082c442040c0c168824400e0500e148990150001964040d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915952338 1250 915951088 915951119
    0xd21142706040f0b040305160c061e2c03010e21040302010f0503190507080907050109080604110a0306390c060c0203041814011a04090b01050912010506030106 70
    0x54200100f01c01c5950b8030403140c0d0013403c214103200041c80950f80215401c50032040481c095501e000a0514095000e801480d0380300030300c070b00d44446010210881e60445882da0146aa12000c11540d525003001c003a00b007a100c3d00c425515508000b58203406c0726000500b0f10000388103801d03002c4500d49014041143e0310840c88000c0c0070609180b05c0c240b16501900145a0210030110b59150a2040d211402c1c00c9403001c45100c0007051f0010240808104100001030181800b82031060354070381021031080d520a8000d0004140d640c46031210036281d00c0c1c80d01e109005507800202880061310451310200740d806a0041502c2c084203003c0c04c1d20000035005900010f082042d1a038080d506980c0d200c8402030300c103d01085055100c100000207a0f107a001004041101001500007180c8200c41e02d510702c112810f03030100320200e0b072011501c1c14001c05402100c04459120b10b001034000356490040e0740d01c0c011101065409012050702400c036207410b4020601c2020102d00030800680c0b10902c00100c240c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915953588 1250 915952338 915952343
    0x306060914011409030d030c1b081602030a050304060f2a0f03020c0a080a26030106050c07180504110102030f0a0e0a080a0c060e01020d2114270604 65
    0x81c2070554042540900465880a041210001d1501541c800820318240c881c2c0511070000c4c0d81c0e20382028299900c07035000004d8110303035103206440c2c3d80652520030b100c0c0100840002040c408010721400c40d50708120050072168007400340c0b0713102c5556007800342c0a228450901401300b091500c0314103507854194902c0980d0f10b510710f0422000c0156442d201c0307141a4444084082d40314810300d0220b0390303a0b42c941c1480202449001060740390081d103400e03c018032403d5042098580c04071500100c0300c0c0050142ca065070741502d480c0340c450948802092030410a5401105000011400f101140080e9000700703101304d000d1081d019003038a1000049070341e84121519607440000038404480518803030806e40c08000300003008214400d40b28843c807428500000003c0320756140b0110b041044a4002d00102c990510034005003c01c0390900501911140c4041d03040075011001d01900c42c00440c03280d2102050766903855040c03413140f500340307001641100094030043d501d508030441c9004601d07002a0f103604c6590b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915954838 1250 915953588 915953609
    0x1e0506070321060302060d0b01030e0303060307061101060b030c0304060b0f240c07121b0506030601030203070318140c040204030215070503070f12030c052b0f150603060609 76
    0x48940340c15106002c2c034180c0c1050079600d5103000005640c40c00e01410100b40800b600090444401c0005001c0310384900c080132080e0000e208001a40c0e40200c0c008003240e01a0600e0306100e03074541700240c01040107070001c03080c003900413091040d9440d401d000341d841140300301420041100180100080094101e0420341d101d00d481c014440140c40004440105844160405045c048403550f218107000480c4c011404d50710866070740038180500c40944c4143c0e44588a252280700c1c0c02c04010402e548401030406051540000100d030551340300f54424090004106580c1004a0581c50000960300b444c108200c02441141041c038002c1c5014800c5a04407540100654000303c2d400c21003031307140e400401090395940800d114a2001c28012088100c88503c61300c1d003185002a45c031405412500c6544406040081c1030041ca400201c01c4d0490f4500a0350b24804603900200701c02013400a02441404a034286080c10852120250300c2c1101c54123a07084c81c0c03010700c0086d40700d88003101c0e00c0f40140b15000009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915956088 1250 915954838 915954857
    0x120519050d0f050405030904140705030114060c011a03010e01020a0804062d05061903020319051606031e0903020304090209030a08120403020f0615041a0a1e05060703 73
    0x86009a000784401541000c0101e1244210039240003140d1085506070303115000040c0c4440540740600c11134040003181c10200f501c0d81000040106940014002c0d1042001c000d108288030f5515101038449803c543d5000303208920f9084501d04096180d0001c05010f58201284040086010b00a50b0404652603848400396901c0303032250006083c05016150344c01090328035504041c07059207400f00039001081000305407420b20400340401c80c03035055212003034816415003c1c001a034020980c0340308440300e400090300060700c45c100300b8180702c4020344060703420640d640300042098141e0002114001d401c03040808210480c1680020341e4407160700180160801c020a10840540c0d82c06807400050250441d8000200c540d22000300340e002c0680e860861015008001c101a81001070800d21881400507020f5410f1456140d12a84d516496541c4555110078110b03c24685410955070310402c010550700806a842ca030b01d80042d40345030380d200181600040d011605080110031030702c8041c2d141c1e03180d1008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915957338 1250 915956088 915956137
    0xb0a0207110901051018030605010f06170c070b0a0b1e0a1a0a0c0309080a03031b020d050f0904111206030f061303031107021503160815041d01181205 66
    0x46c018800350840210503501001045161048501804882c3d40c41e000c0306040c41da014143d13204050105100d800c4070303c10045000c27070000c20345440a5100c030241046891708104203001d00304020390701d908007000401040d112107110092281c603400580385240056100c80303004884285402c200b403014031007080410405841501c51904071400380c41c4c0301d525903446180303860426840d01d4040c3c0c002503e910505200540c1310300d40c8400a505800105010001a400038142e40100e6402c07261080010804105540380d64010513402800c140c0826a2140e10003500c9908900c107071125030080c851a9040c8040d440006040c500030381140c2d08030602080d080e03030200e0150141401850038910b052288000580782c0a040300d000c65100d5070320907141d10703080800010300f03040c1c0b6025000304807008041c0144101e40b901c00103444001650045004603001040b100c014081e95100c40040d8038102d4200c0d0230b16042d90642560b00e200f01d01e682264014281d0840385400f03400c080420003003403089020030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915958588 1250 915957338 915957347
    0x5060901030f021206191a0310020a05070c031b0b070b0c030a0b090420030a1104020d090807080903100207050607350a050702070305060a180b0a02071109010510 71
    0x10410f10003884a071042c640b0040c61420960195501c80c1109201100086c1c003140500561100c140c40c2000343c24504045d50009036914001d1002c0200543c1c0050810042d521883c21a6401a00400d10707104d220390ba490030031149010a008805080300303650020920803020000c66a1154010400c4041e0b62608508902d032540094421620b169807081940041d8580c0069240b10720b004860301c4010081c00d443e01241c4208242d051403107a00440c240e0f0f000241c500398200284507040d60016190700c0c1070780540c00106410380000c1d224400114407007041000142c01084616010b8007a140f102003045030040590240000c000c05a030054400540402e04c10040c0c0b44a02d840310316809a545040007000111141c005008060382481d102001010804c134010b10f0b420614520061185070320b1a20760684420015007000070031601c4911403030307410908004204046030005400e50f5582032041c0e030380000754840c400c12144e8000c4841182402d18040b056030b4100d440281c00c01c5080c00030380b0030448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915959838 1250 915958588 915958613
    0x60213090c020303093705030f040f061806120e010f0c030603140604031710180f0f05190207051204080607120e103911010506090103 59
    0x2040a0842100011840014000c5504201c03158010795030328107002e110316013051544c440c081107118000d41d854440c00c00c1012450501c2d80380f1160003107100b031035160050440c40717400e4070358240000108000c9889040e1503014011190551503a40d08010b07000090b1807100000e220315404610312210f00c9281014a802600758424107800025401d081c40c1110300883d01c0043d000d40029540d03400900401c240002550001c2d030742c0c20003c040782d1034640c0c1c009003007212001ca610f010403543d4000c0346816401d0783c00140685190810212803a84560060008003150140f203420b040c01c0140403034441510f4803605008140701c00c04945801e203804459001f1354803d0710300300d0300d510500b0507411104680401400c06814034402604603800d155100622041c00ba200f03000c0d00c90b24050085200c0e00000807242c07160ba4010350046200c00110080c10303580c0390044402c0040384160316544100001044280008414607229604003900e40304086003201d100b00c030f60a0300940c2280040c40859204160350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915961088 1250 915959838 915959857
    0x6020613060c0315030606090e010204080a020f01210f06090b0a05011407080c01050f060105130e0403050c100e0708030c0307060207111e01031406011b051c0c0203010b0402070f0602 80
    0xb19411380c0403c0c0c09150500707568000e865090365920248051489405113020741083d03a402582001d0800d06501c1c1c83d81c01e03180d0300900c2185039030394041543e4000c4c44600d12407180010015a0402010828006803155000b102c544925203039001c03800f040325115000702c1c0d06010304280d482d14201401035400c402c800c0c0001044480500a200029414100402c41d4406150002c2081d00781110f000c00c0824014145038180001404003101c1d6a120f040540d0450310f0010070b02c1c1c0d1541301c900302a2203a10844901d03102d203003c3ca080d481020031141d0007451106a5070022203645660300c450303050300c9025100c4101c1c100e401c108141030105145802402d00107004e4950f00000400050014078840c10a010031000035941080441e000c0d80c01d031103402030b08940000501103910703026000800307400c5929119056920140460014420100b00e4211281d258880b41d0580c12a4100e002c1c0c600c10628070203d03ca507003011002400786c2864029200b9180e404034003202c000500c2e0b47d030b03000690040d4a84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915962338 1250 915961088 915961091
    0x30507120f0213120218060f0d061401050a06050a0509031603051507030203061f110d03090213020703090e0a0e0304060e0f0409050601090e03040e0c0306030706020613060c03 77
    0x612036035600c1e11556000032100c04005070f441d10010202e08850b03000380e2041c04043c1e0882404005600c803107207803072180e03025244141419030760400061159084c2407200c41d0003441100c027000400c20b05501900054564111841c0f8683c1d03140100a000c031070901840d03002690034491001283d0051000d0080038800030203a5080e500c10600100900003c0e500540e803a6010422061000d01000786007600f0a4a40c9070039407440c54007102250f00f403c1c2e09000c007a0383d40900ba40500d03800744520001c000c02c1c0341c050280e4800d2621200b005000d00303044c1070f0503481142d4a4110b1002c607070843c42215604c50381521805003042c9003503054845420010310355994076843e00021404101c06100920240016848002029041034107102c174808024008074010f5150144401c0481c0c000280b050441d0b03190040480c035140d0f542d10321400d40c00b440c1c1c07000036042c1c90324083c403c0b03600d4102c3c0a94880c0c80c081d82143c2e5906d0351850120f960300001d8401c071124040600100c40868407541120314000c0d0035050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915963588 1250 915962338 915962357
    0x6040b031b0a03050a080421030c080307170412030c022a13060b0d0f0902280801020c03090405090313050108060a150801060f020c150306033405040e0607030507 71
    0x131a0303803d00400640844540d1000103080c410210000c15041d115640c0c4201c82c146440d6507600506450710421000d851644003100141183c0d1103280200f10400d040c96a02000b4103042c40c0c400c5d0150f02c80d20724480401d0402c4c4e12895814800201c0301034201d90850180d40d41a5030f807010001030078800301419006012040b882180310081e00450300281320700e0510680d181e035440b90720b01c219203841043c800014100340500000d03980c2d4941007118080028441c04900e1515500301450107a19401203d40c0e50001ca034401c803800c4c021003d444c081400781c03411300071030f0b0780d8240351b5840e48903400c1c3c6c40d140d960b02d0000600441d40325003075a40d4000e40252650713420540300c001d0561031601030301d1040001810f190041c04003130340c031844181c0340c181c00340001c001128020b0000b070865045106001000354001c00011b02d65070782040071014440704003501240904404d448805501e4100b0115040710400304000034850400344503025109200304d020b40441c1e00e8801d004c402902c009403501e01000b48045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915964838 1250 915963588 915963593
    0xe060a02030712020f0c060702010c1101020f0a1a0f041e020d020402030f161e08100911071403040f0915080f0c090117031608040e041a06040b031b0a03 67
    0x503c600308480d001002600d0340c08214900d0100307800d0050b40109001e00035400140d80020401440c00d40c403440800d0721009800c0100d28020688076604018450302c0511014050300080d98182c49403040302000640c1c0d9828003044604100740d90050119440c00c0d45004071012008110211510062205489030300e01c2d00000c099810a485072181101d01c1406d126004a2103140c0c00e00081050800c5007040390305e0000200d000b01107120580c1440541000111080414404000a8203580c03000300b1807d0042d50500403642c1000e60200c840042d90307001c203054080000140d03001c4908a203801c00c4558102503582c4054001d90a0014441105050200e0700301401d01141c1c1410104e10001d00440120400300300e060141070b807000c0100c0080061022150f003010080300d5130800c0a1108955280e017515201000d44038a0307003c018213a0744401800300700701c80010140d040d202d2146541d0b2003601c8030750822045400c008030390742d415841405001410303016101c2c20041c00c10000c0200c501030340d41742c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915966088 1250 915964838 915964853
    0xc1032040e070e0409021e120307081314090604090f150203060424060c05030c120901200a020108060301141303080106170417160f0501110a0e060a020307 68
    0x1a001550011005001c1101e000c1d4440c840f914910030444091004003c43c2c1c003c525072a8500744081010400d150414030a6210749140c0070003402e41d83c085a43d03460307483c102400141c000c01808040856002c00009920401c03d98900040400510000441d01c1e4141048000d154540c0c0407200c10510b0010f11001c00c907014907403910480300c40405640d925000d400c000482d034500e1003140991031010b029296503800071584805032203a604106c5145000307070420510b50300601102d00b00300d114000445004038440c0c0060503031110300b80c80741400644064120f40da8850f200d038481c9070b2940107016503405136220b0341c500b40c4c004001500004a0484010898800b8003044a01d828502c9584008004059002503501d0040800d031808038a5131707461208003094a9130190000e0002c0215a0f0b00d091010241c108403000107548003c2d5100c000540d18100904001101003902c05501e810450039400c0c00100481c0c01158461b030380c1040f20800e2404008186d0840e401600c1184828003982000074a83c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915967338 1250 915966088 915966097
    0x910020d1b03050405070512060c070206070b0a09020f0411090f0a120c141207090203070513030f020306010b04120219030203070e040506090106060e0103020a022b020c1032 76
    0x1558011545251a0a1a46c031700b000d180d0001e80101102c0324141c4011202080c105c2d08800f034078101503524080740c000500b40d4010380d0b00103800881c0510a200790350030560710080206100381e40b0008086402c00401084600320100032210305010040b103011881d001600c0c07075084200070310150203544c032102c0c0f10720354000e43c100c11580d02c04151018040b20120f07044a03844060215030140d001c907103038a005521481144a0b4042d199000710219803150f002d001921404140722550f400000e40d80c4c00c0c490103c01c03001d0000c0e402805000000310319040c41d4000c0f00d0554481e151500c5000c1025402e000e0405400181c02501c3c0002c582d005c00140d5050186c0e00083c81e41001c070305d0b900e05150410a007800e001504200c00c684c503102041245580101d5245c2c6070700401d00b40181c503800e00ca03201f85d041088010001c1118000703801322482d041a010f03484528554168212400550800103000c5440590503002001c2400703424400001401c070700000408034290452925001d803496020441c0c0d801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915968588 1250 915967338 915967391
    0xa03061d070f140a08071206140f01030318061b080c01021912060602060c07020f04050a020d0b01030b06070204110d181104050f010b1614010e0609060910020d 70
    0x10b0601040160510320110912070220840b841d40c083e41c81d20014603960601480f0300490810071041007400e010302603100314040c0b00c6004200115282003905908001000d000840204140c41c1c040f120000c50158102c0503038001d529807410204420b00100211032064008994501081022140b05502070020b4004010048a60305409002400103002e0b200c540c00f01c031640034a8014200403080e400200c00d90440700c1c07c600700d55206c0283c000304212035007245000d0303003060400050102405156000b020700c0c204050007048180319a000440c107980581040f1035100308180401405880d00d68043e00790368080e00b07401f82c64104401c4100c4103440340c4440f13100c2c21442c224194418402d0f0803a070341b1502a01102d040042d868144405048000107000f46138000e24085044a0b04803411114040d0198022581c1c0215540785009075010384040e1549049500a07000424408800080d00074090090712002c1c0034407405103409a8001d40001d029000b0142d11954100710040122995820b40070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915969838 1250 915968588 915968609
    0xf170705010603260a05181c0309030c0f0302150a2705010f11030d0903180b07050c0a1a16020d031101050106020d0c0b0a14010b03040605150a03061d07 67
    0x40d0107420f002404c030540002000d8402c1c08010240f0b01e994008201c0d20000500b0880744050407000001c550101101e82d55000e218441490304001e1580240c122030459108200c1c54440540780e80001c0808003d500c00290030405440459400810040240040c191507240207240c0305081c0d052030901d49402018a0311580340480c0a102ca960300200c401e000216030700f0b141d0254903a18454596920030a4894845596a101d40c2c3c410140310b0f03010003003014180001000184e07126190440d040d4010001101c0510076100c0e000d129042900311403007212500e04a0704410020603400e01d0107584800d03c1c5841141070780341d007500140d82d09514040c006029645404a90064020f00c0342110410380007942590f124022007102207503c04040c40600d03130b0020f03c03000240c4990f5485409858400f0544a0090341d460002c55000d2403140614844ca0044000b84000d03240c401c4e451481c002e0041e8a160000031124060010400e540c000b0814985280b0030b04480c42c09141e2071504205064025101c2003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915971088 1250 915969838 915969863
    0x4110f03220c06030e010b090115030608101e1122090c03020901030c0903050717030f2d3604050c0a0311211906030303090314070f170705010603 64
    0x1544d05201d4101d8820600f00204031602c442c900144a03500c051180310b071409400060141c1c950300c240c2005006051010860721084500c000c180c01401b4008030708a641c040803080440a1041405250602806c81a03d1450941035420480328203c00c02d0f03890003039005c03001b030020304004039200f2100400f003030355070045c1c54001e000c00040c2604d0071400c200007000740040c0244007203000401e02000321400c0751504c01503210076621060442c050001345a003c0c0ba80840c03a1410071002281e20038160032841b03401c0c0c42c005920ac403c0701c1c543c005d080007400c12070100f205940818088000d00701a070305501c1410241c6801041c009001c4d2401125000090000440d140c14a20f07018003401c0412803908180a007080d48204101103000d4080c031800c0041c440c00d03c08900010610360041c10107100c09003062001c0340d12414050003401c00500e0440024903c40412819104800161500c0035480608a01c2171035050f100e8000c205221980e1140600c0708111031f10005109106410045108901c0402030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915972338 1250 915971088 915971099
    0xb07030e0f1305220c050a0608070228080a23090102060c090415030506040317060f0d030e04020408010510090b03070603110f03150a0504110f03220c 66
    0x1001040036055000390074040e5000c07480d0781c42c8003400391000c0c42140000340030b0707440f8444c02d03031000c44d0139154444a1900907411014003041c46500803e4840c20303201d0001c4c4039a14501229141070850b40400181c0200c1c0041c80c0d81c2d03c000066090507481c040144019180d252508480da80c00080618007207078541d6000c3c120545c801000407204415150036500b04800200041c1d29900000c05030740d8010400a00503d2556a0303600a20b0381c803218429880310641c5a01d40b0a80d244400c2c0c90540114400c0250421403021071042c44e4030825000e850b01c880b1041c2d080a002c0400701584d022004d108c4400000d0007e9291440507100030b04000c0c00101d41810441d40c81c04480703107030360403121a45040290050094070001205001c407840d030314000421211407035810510b400ba07896510707806200041404503400e45444410600ca00c00c94050203640d542e0400c00c01118400760600b04918000e003c403034002030400c00510703805404510091400103140080c400c2d0001d08920407076a1407079110f0148003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915973588 1250 915972338 915972347
    0x18070507140115091e05091c0f030e010b061204050c040c0306090b03070e04120c060c030504020906031501150207080a081e03062b02090f06100309170705160b0703 72
    0x405908000b0807859011005c0c0f00941c0c6003116103008040d1700c52000c01c1e0422410003085a214494a000c0c00040488200c002c1c5080d6000745c200c0000382c00c0400450840c5018807501c500000020011854404010003010100c50020320640b420b002d1000c0840c450b40b41c3c1d001d0810081c64076540080e145040881590440700319488243c041d0340201d00900c8140c0490310307140d402a400c4040c0d003086500007030301120b01c0200d10700014201410011180b101c0c0c0c0c0c02d504a00d0050380b08076103180c1e4556861050541d100d00c071131000440030302c2c0d81004220009200c61074100d410050700c15200c43c50307190340b4103604e08610240c04540d2050009800d842e40b512250041c503d82401c4200c0750f10350709158000130418501d0940c1400b4110000303410742c00c1403e65042d0240724a40c050446000c80c5000554190540000c072105030241480d91071102030306119100303024031300c2c2d88200c18401100d5120b074180c0543d000102e08a41a20503218164035400b11040844010302070f860580b9a914410700d801030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915974838 1250 915973588 915973631
    0x3100302130f09120311030c0d0207021302041d0f09120a030b031c090b070804060815041b0f0e01050d050c1c020301052e08040213020408010f1109180705071401 71
    0x1101600c20300910023411004011141c540811220140c1c0f0703a070060000803513107280c81c0c240c140031a10001e03001448045001c41e11000300550410a45a41c0d548802d00c1803e04085907002e840390442100d090404103100080e05240c00c89180c001004111140883d01d00025008000300c00c0b0019200a2a400d40c480f11480260030b040b0506420840140c0d20b4078194001c50141c94180700c43d06002921407241d001d000340800000503c140640f042c160811940100a003c5000c002600f02654050701409105200e418217410fa5401c3d150070302d124014802070101804130072404400f00095a10402c0904880501c0e40c07010701c00598a5151404124000444900e5010344001d0005022000c4c52040c000e00480c0280e810300d18810342d11031000600c1a0035400c40b000c0c41c40d2011402040d9110305501c03034000d503500e04004000c511851182c080d01805041901588982d2910501a04480750200316400c61514205141442c4141d070720300072403038104144209140e40d0340c1e8034004030411242000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915976088 1250 915974838 915974861
    0x9030f0f19020c030d120b04020f090906010801050d0f0c08011d0c030d140c01240807140f1002100911090a06061d0102070306060602060f090303100302130f091203 72
    0x40c203010f07800e1030109813583c0030400b507542484804841d141c4910f181e030300904c00c1600010411503441c50500003e20040d00644007007030086415500040344e95006610321810380360001d10240304824996103107001490108011a10325170030601c00151000b090140400c40341c000540d0f8000c5075000110386250044415145100741e001c03400307121000d90001c1c01e20b010050403207a051341c1c8507030101c0140e003d4104074200a02c103040f400307510f040d024482c04c030b62130035210004140d801050350750b006c5c040c120300f020045651008030f08032000803916005d8900185600c250058034400c9980201070070444220081c15642c0d1007003800b8400c0c0d58680005520351001e15047d04000081c00c1040041c101c400020907000ba003c4102c407280301c80da0003041034000865104505000032501ca000c000c1d159882900c5401c1185c0c060404507081e550301000340c80c4943d40715408000514a0754081005805c030440c8895245a901e601d4030000c001c490007034100d170b0350081d48030011042201000404445000c51607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915977338 1250 915976088 915976093
    0x70905120601030b0403050711100302030a0b2205100f08010b010806182404021b060105010504080a031809020a0f3506060c03270d03020a0b09030f0f1902 68
    0x502c001110800505d400c280c140c54065215646803900414840995031f0702d59210311030b000400a40c5500d81c00462140001c040c042c0030406804041c0080074111001a451503103c0070350303204c01e004030395109039440032040160350282c55481030402c0206e104c54104a10903515505c6024455800050898100e0000d4a00d42d2090b0f100c400098071109010f002031443d8031304400e00510041440640e8030101400400c115500e494003010201001c102c00346111440c028403000150543c0604191011181c0140c082d00b2101d042d41c2d4101c440c51601c0042d180d141f40080350104200072540b0250030a60038a48918001c41540c5901030f0a48110300c5803030f0006c100300e03240c89501c44091040d41c4262011244104059100c060000c3d020b800f07901603019440c0f03c00329810b85140d40e20161412401304074003603045501031030024840d003d51014005409a80700c00c00b44030000314200c01007507110343c408080e00d040c2110381e200203105900001c02c4406004003c26403010450b0400d400c0b400c2d01149000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915978588 1250 915977338 915977341
    0xd1704150348050d0e060405010c02030f0322060609020c060c0310290a0c0309080331092f0405030a0201120b0301090b010e0f1b0703020c090709051206 67
    0x9500c0c0642e0b96031203502c101c0004641e11901054001d4044d140c0301d10303c460043c0300000100850030b664650490382070b40c141d820594038a01e40b5002100301d9030005060004545140d441a10030040195580310000025540148400c0800d1182c030a8002070700e4680d00140e60b964148504034a00003000d054291180810000c0c86200040f0030350702001c403024030401080071002d5441d1901784542101e80001d800a0002d5111851035005041c00380d400c1c07103a22403980040d00c8610165a900504094101d41d500b10220603440e21408405070b1407908005445000003503c0d0040d20080d00c4240b044089206045d07071b00e0201a1540301003a00480340080001420549070400081e500c401001c03020741032041c01404900c041003c1d41040301d88010150090002240c3c51500d0b8201c00001d20820b03880c41c4050020465103503071a02c2d12350055104080e500318030790a02c4205c003041ea019040450079132158400040c9141c9680d9000c1d4800c3c0515211044201d15080510461140000005100c0d400a10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915979838 1250 915978588 915978671
    0x509042019150504031a0105090c03042d12020c040e03070507090207020a03051f180203072d0816050306190f1103041b0909020d17041503 61
    0x5a41003180c080000e1800c400e00240b20641d02c0d0303c9540c1019040a4050120760a0703a07000d03004190480d40182c441c5181580c45040c648018002075400401519011000e1100154108151040580a500201036110f450f60b25105240240021000540c02100c0e0204c2a4502440359808401340e11028511303004d015514181c03038940b07902610002580c04140c40040d0344540391100040c42d400b40859445102030000c115030b1804c5a2740406040d03003804026a114180207220403070b015809002007002d00d0800c1510084580f04d050b891525134a0206d0301300f1042c0c0360305090301c001c000e2040031300746034407441c0301812079002035400803802a403000c014820549442500160340c220b00c0d20000400c44010111800603001c241d1100c0c070304100c080103000501c0310103801100644074620301c036450596a142101c09482922401a60181c0a0382c101404a403122813611484e0300040039140c51f081c1c60310088010402486807820001c3c0d40c0d55512010b40e8403040040a010520040c0800c500c3d01c1034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915981088 1250 915979838 915979879
    0xf0c02070e04060c140c01020c0c0d21020c0d0f020307050105030c1902150108010c080a1e1109040504030c03140910180e0a150f240905090420 63
    0x241006100d0f0395100d1030315540501c00c1c003101320000049456203645010480840f03000c0d410040124016005010422805140041900c01e02903400345681d02c00890086182c0d030510740c045104c006502035409031034002d0352a40c15040e45036208002843c1c019034280103151502e10380c0c1e00302e00c1c18404100144404012100141c840c1c0b0400a071601031a9407540c00e08906010010301900d0a0105c91800856011019005449441280d55130401c05039916480201611450301e0003242d4055014100e0035102c4003600308905484000c5821072801307010350040340403103e0859050f00016003c0310071504041d1710045c4214000301650540b42000085c2e400118000c641c400f60205001458960000d030040320301b81a80202007102c68a14517290a4000c0300c082e0000640710344484c1800c2201007082001c90b0008825a0f6000d00b0101c00300b03501c1c42454040743e0882200b042408400c00340007940e0741e01e145995200f01d01c035001c2200300c0c19000201c5904082201c1550341309010f44000020306007002d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915982338 1250 915981088 915981091
    0xd0914060324151b1c0f1407050706020f03040e0127151703031009180c1203091409060103050711060412020c030303130f0c05060c010f0c02070e 64
    0x1400c4916609000c01882e40b0001045034002c40d00986100d145003480407545010f0301c461035502c04029605940c660840d034498280394641d402d240a80c1000d0000b4a01c40d41060303200e03a08a0400706440c00d5100d0742c204c107a800c0104115819448450180149581130195002c8c0c1c00844006605050030450054200401400b584000c105501c603100050200743d012480d06425640c01044110401042d0848040d02d41c010103505a6042100a5a4040c00412288a0b100c00b1020b48841130516000e5000b620408001712070711402e001c201d0000c9044040514000d0100e111206e20701d0b000b904e0003421151072a884051070b5045a0303070070100750700c0300c25600c0da01184c01d180014807070f5034840050700d0000b0000b10440c200d1103260300f0402000340b044024903407113409800700d600c0f036000c00041554921084490f1401001c082c036040002031005800411610711840701c02042075160804114650004010104c082c1c0d1a80411801c000349445440b41550003480070700710142c1071241c2c085903043d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915983588 1250 915982338 915982351
    0x15031d070f05011b0f06290a0501180e2508071e0f0f0908010606050c011b091415030c0910021b060313080c1c05031302040506210d09140603 62
    0x40305c44d5031004001e0f5650094000d50b44085003c0405104482841050000340141501840500f000482c0b950701a904660480c00ca0004a10945041c15800e01400001070101c002d83e03c54566111005c2506420310300124010390340f045424640300100802041e400865500c007407440104030086141c0c0500402051141c0b810080001804114100d42020050b031200080d5441d001d0041540ca90190080c160104088024002c031204031307200c4a248103208116070082654804100b0800c8020b030181c03a0b020000402d811100d02c01c01d00404019030040f20303480c5a41c0c03400140b20540b45840191004c3c3c1c90100e03c0200360a40800e002c5000102400450901c00d10000c000548020440c1031381c0c5546941c000b102580f2980000b42c0d00b40d07581640350040704e07140003102e41d010f41d851290054921420031280d2105c120b107455000d0100030940135200d0381d0030242500030303620b03411705c1480560b0180303000c0401054440d6620b0360042850b83d07940c000d110b0440d19644041c0756550b42c203042c0c940161 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915984838 1250 915983588 915983603
    0xb0604060c1b0b040b122203110f030301120510050f01060c11040204090e06070215060d050f0d020f0c01020303010b0403021c170904180c15031d070f05011b 69
    0x401010900d4082e035a0381e8410002d0740710009000c9281d010f1000a0b0a5503060740100350556100c40c46072616118441490780101c0e01c000b107401e000b10340f15102c900201c1c200441519076152807155168115030090300040020500284540c08000c000c00c20030f522078942c10010081d50801c181550b5181d00c0c10b1041a04012003141c08405001c250b6080075910f8100400441d61503035140007070720103401244211240780c0514800568450b002048802107002040d0070800540d48a00801c0a000960b05007030f2441c2c812550300d00307a885810031250594030750176002080c0f104401364071103183c41d510b0000c2904540080c0010040b401d600741c10f44041c1c0382d045681c0700d10142441c140345410200c584000e4a046032012058010502d11002095490b0003541d040c0030041d0031001c41880c030071850400400c4007403045410006130071941e00403503440046181c08102e06010000300c800947c000100c50343c890b0083c0ca010808070460049074002000c0030300f460510280c82074509610035034010400340400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915986088 1250 915984838 915984863
    0x602030703120f022701090e10061803050f0f0d020309030304181b09030c05010c050307153206010801050604120c050a150207080105151210020403150b0604060c 71
    0x48030035405485041034071910300b02604129117902902c0001d00805070340841c40d242c0340400e0610344400318600c2103904800020b6940d141c03038822030f0812000c40f00d1042800b0b8520000c40051403d00980801140c0c0000400d5945003202b002ca062003042c1c0001c40c103660040080110b2511b001c0182d0f400c07030b021401c2c50055400d542c0140c8002d440050340003043c4000312004c4a00c401d401801c0181502c0c042e47c05043c046032036000640718502c016802a001d540240081c1e40080c5049105a118000340040030442c11a55044400d405c2c0850315a107a401d08050b2010003080b240c824801c0d8807080904e030508095150001245880c81503000e40c40040c41d01c00d20983c02e008100c0d5001340281409080c0511b0ba03a5280340d40c0d08901101c21a4034014018000300181d02e000c1401510b0098084230090070031020381ca0f0400440502c21380d01c102890149822804000e680751000d00000c6000b0288003140d89954601c50040320700303040c0c0182c800d1406020502c0087d40c0b000340c20503003e40c442c005500700c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915987338 1250 915986088 915986111
    0x60e060103050603013b01060e011d040309260f0c0306160e1e030a03050d050901090c050607030309080325080702060c0a180b0a030b060705030a030203072610060203070312 76
    0x800705030901c0386e4070641c209880040c2a854034040340741202c00d0902042c0c1032090b06941881582016200600000d0003c10140660260081c0d200c0310f01c0c10034000c0c06065903d4020807420131080e01080d4002d500030a0f1240381d22b080501201da400005420700b03103034032090003030041c4c46450885050760040d0188080e482169003c90b00b0040a090000c08907202080680760007801e0f0760160300c24188807405c040114142c010140131704840c10340d21a40c000d5940d0300780f1051048640208006404058407240d401d40441e1240700110f0003582c501c00160b9800e080024407240318000358058504000442007004401c55010a5407908402181501540c424000d142111803000000c622a00450300d07910015a009050005085401e01c588050160310b00450130031034203002d0301078050003e420800401c0c3c0e00740d07c01c0e4000d6500a0340c40c00d1010301140c000b031118484c220400d03207820311071400805001c01002484150700c02405103200840ca000555a4001c1c090078121220000641c1c0f1120700894 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915988588 1250 915987338 915987431
    0x1c08180d05010510031a130201050f09040513052802040209150a030603060b040c0e040b010311120603101b0f091e090e0703081615060e06010305060301 67
    0x860380e4200000740040c4c01c14441007120814503210480d010b01d0041116034050720b480c3c0c0d180384a650004c03500c00ca01801d540054400d6405030720303002903200c3c0c2042612100e90722445814014190700c9000540c81010b03240191400d079010064005080740050848004a401a400c21f201681941c000d41ca80b0b60a0010800c0c14421803003003100044003203550f00c2034580c1644200c0860740a0070042c440d084480b018001103626068288000075140420806241026008040e00c0081071600203240407454a20201070340211402c007e01d030b000c400a0240310301e420400c0140ea48048102007082141c801d06841803051100c0307491007401002000840c056000c0e002d464000d19000c1d8405000148504201803400a9402003004c041c0c07624856014120b0700003014010390f0b61100807070b0b10300240c9640da41d19610708000b0481d522403182e1009a035092550080c0c4000340321b0b2a00d1451070b1f0a1030400074056400c0101264080c1e890008144182035900a48500882880200c03822000c4941511203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915989838 1250 915988588 915988609
    0x80f0c0102070c1e0e0106020c01030914160e06011409041a0916080c0405032d10020903010b040e0c040908300a141501020a0f111c0818 60
    0x102154028100084c494020b8001161a01d000700300700012035440f210f01741c0b00c2000030b00a010040c1e024032040a0503502960207140564040e008410404031040c6041d89405d4104113803404013206044100000810140000d42000382403c040b00c00c1400c8080008050241d540346c28803c42e2145100002011788020805c07540c04c028100090603d0000e10940499903081111000215034500043d40950060143c034169103000700900394860f00444d61034400007525a0101d1409a5400148801c0904028041c5003660124001d601c54002c4000c150031139401c03080300d9000f1400c010200d41d01620205e01002c0b106400c490028800903142080c01c454000c0e00d180b248144c181c0d000d07010960b01041001e2190079800031080e244c40e0317502241d28050303c039100c0469150000580201e8100602e01c01d0412900006104503840072600303489600d0100980b079401e841f00c9482c4100701040741081d483c40700d2121030100882d8100d144564410310f49110b80c41103002248401d185140343da0362182141e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915991088 1250 915989838 915989843
    0x1002041203360f08010b030303040201111204060f080a0c020a060507090f03050c0a0b12070c0206430b0f040c080a050105073b0a09020406020307050c090103080f0c010207 75
    0x207850380c0b000403100120b03030140078064180c000d5000004100b201405074900329140074010318116103480e070064440e105582c9a00d460350044041c41081c000e800e4015100409855840541442c0760f41e501030003000015000d0301c0d819040284000403c0e40003c0c01c1c950140c3d101358001082d82e20710705d0440e0444610303040707002c0505940d00c0000c2484400074070341241141c1201c01c0e1186a81d0390604403440c5c807640c0e1061108101d000b000920702030040030a070117801d0000d0140c030325180b03190705200d8005d6400382c20400440100203c840500046010701c0e4440084100c0300540c690554640da281c4500003090145045501d030300080c100440c0317103000c800500900c07003241c101d48880d240c114040c0c8011100c9200051042e1144034188910445900800001d07008840c0c5003d003040e807070405d80300c06925550f0860688100010042400d10080c4002d060a60255480790b080f4a85941812004100540304443c0702005201140540003210f0204c95070285903580c030b0340403036117080c0039020b4400003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915992338 1250 915991088 915991157
    0x12121b110c0d0f120f09031203060918110604060c140c120706030506010504031e0201020a211205041703331f081b16080703021002041203 61
    0x10804101da0149503e00b000d1050f461000d40ea81803000031182e501030703c0f00741320000f0304200b801c2000c50359010b4844d010140d2468045030300380e140c1c0080000e5480b80c00b400c0a030148441c400000b07008050048104212081b580140740c64036286004100108025000d061034481400c0705081c541d0821200240400150081e5400a04002816140d02d20b070f106900100707041c1000903d8a6102e04121030550303a01c08250030b40c2c49414586901400582c40c0d00724107502c6480c81c011f000c200a80140b1008100c078014440880b014000000c15000d41d103a40010b00500f0302c400c0c80b002500c0043c079481c90312442d0008a80742c0e03444100c054145015080c00c1032034265030041d0750702010b030b4a0f00801e0114070b01f0380b4007046130b04004260040c80a03014034040001480c010114008801c5090782c240c40e0071007200341a040164203081c02402440010b41113801d550005602c40426030140060039400305600d03021400c20345018260004002c060500404021100c0e660130708807280300152480c0d142080c601c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915993588 1250 915992338 915992359
    0xf050402130f1805030a09140328020a0308181203030f04031404090204090605030a1106130e090a060b0a03050c0d02010c0605240f0d020402031503060412121b110c 72
    0x8044d40c60b0745c0f114451000003181400003041c6224080703042e50082c0806001000c9850141c20100c006800d11640058800005401240136950381c42031309020f5409074002035a80d8880d104114202c5064100ca280280c4001c0c6010201450101c140c1c0d500c90303100c8510219595030340c40c0442d50480700d00d0260180b0007000c100801c0b910b409502070700c155100c501d010031015880300d04041d540e40403014018080c0e1a44001d80c045820410007600014180301d501d041c215807900c00075041044126440c8811340e10441800301448940c1c001c10b80c3c40a0180c400b0030070075007162942d036101c20004000c98000c2e00610706040440e4440c8000d580c21a070449000c0025092600f0300720701140d0014200083c006625001005c545070414039104035460082030550075024035030905c4080d420090800d46040c034041442d001648042c804580310340d10031a403224102e01900000392100c0403000380e0040c00d516102d4440c00e020001e07030360400c0c40950b074202101d904c042500003524102c107516001d0340242c607401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915994838 1250 915993588 915993593
    0x1c150b0609091e07050304052104050402040b030f0c0405030307061e020403050d0206060a080c040b04200d111606050612012309150606210103080d0f050402130f18 72
    0x4007100401490100f0f48a03107841e0104211082d0005540140541d0000e0291070344411490885070449003480480300c0c10b069440c070005080340c00c00c0e80401200b81c0d000041203403114640c4451070344410100d41c4c4908246c2008042a500e0180400090400d075880d26050700c040610702c0300311104002d46c082595115124039166440d02171038040b200c00b501c81d05000c60b40030325194200d001500e001900901c859003981d0200405000d005080030341181d55030010892a180040000f03107103c054948066803980b00703511240445103008a040072030138052080703100c001c0041904085640e0401c00214158440d00c0000310b0342903500c07000004035031078030750305201000d0712241400301d07010400c131080e00f41d0b40c0700d05400392070750203190b421400c2102400000d1080e1910030007401e0a87d0303452a08031060818040c502c80a548207070030554202c1c174003180140c00301c106801414201c0b08441c0c41800342d0b0401e58046050b411310211001034071502c65030302d884003480c0350380b14004002c0646500c1032044201d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915996088 1250 915994838 915994861
    0x5070807020915040f0516200303090607091403030723060708011505130308031f060503180309090105010e0f03010f050402032e0c050d15051c150b060909 68
    0x140035141c02a801c2003c02d17407026000307100d1284640c00380580b50844030319804044494850540c1c03824103503d4010144220540e017003018520941c1194010401418034110290001049903c05568028000a42d03c1c454401100b6900c601da030205030510220300403c1c0550324003d0300c02c0305805038410360081011540c0e102002c03504942c8540a00804060100b000326000c1c0714a0300482004140c6400400000e0303a03101c0250ba01140341c000c5482d48a6450441d8842103e513944000006003012090103515484c0c0c0341520f0070102d55070029844c1c521340001191031f40c0c005100b91414801643c2c80d002664403260941582c1500040003040070301e02207010003004000584080e0300038811461000f020000b05002001c8011203940758507078090201c02c0d50801307080f062440ba070810005000c4680041c440380030b0708003010481030942c098182007809000750340c04503008052070511015140c4002c5803c00030034144a20010401054642d0314a011440c05c0c0f0a0402070b5030401c1d401d004005510112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915997338 1250 915996088 915996121
    0x101a0f0d0b0d050a120c0b0105280609050112050132100206310f02010905040603050c1206100303030b06040302030624010c0201051207090308030a020c0609160303050708070209 78
    0x300040c0c00c0c501107401d001c44041d06106c1000f8000d0700707401c00501c900e1078070010300103c0e01564058110300c0e00c1da042c0541146401d980c0008082480784070140550340c2c0146108211840b130703420420556240c03045680d1859101030350401580c6800c07200d014001c00c8194a0164058042c01d50301c0d01c881d59542c0203554103021560911080030031800c544010030700b5042c482c0400c102400c251404905501c404a0705079484c10101e0600104120004440d00d55016407401940a2000f070541326a6840601c5103038518107606441d15002842040313801d548121004041e2501442d001422400b070b0004101a8030031500040d506100c0c040400420040c0824030480100129080444428180700107403980c11001c3d170005d0200d542400100032040c1e404440c2940040307580f8002221542c1d030340f0703000c00e00d5000b51002e400d4150005244001c0a604004840e0480140c000522034981800e00c0c103082e0034001c3c00002c04004001030f030001445001820350b1802e64009042454900340350b211039000554 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915998588 1250 915997338 915997343
    0x501030c1806090f090c051219110301050306060102010c090605070c0e010e19090201081b072102070f08100e03040b0c0a060f1404060b030a05060906101a0f0d0b0d050a 74
    0x8944c9020035440b80350f000340505141551500c81c02c00e111a0000200da02c40101007100780c1c2c641d0180541c4141c0c09025070f60700c40b070380704205560720750606003850300300800200280d06680c1010510070841c0e0384a030425084801c0751404c0c94030780d030396441c1074401c1c449983d0000806220300000030071000750302e8101c1402003005048202c9003240344000c14050794040d0324080c1c04240700c640040c1e41d4414040d41107034590f40d20820b0500d40b00c00c170346e5002130501c4400d10460b6440860304480236041e030100007200c017920706500e51210091810988a50b9814210110940c0303a44456120030201000c0041e2005440700c442404d403a00394250f601542c0d40c0031244281c1c0d240d4102440600c900ca0288100030400050069011321696151500d102034094680015003510588081344041182400030300c0c0680801c6000e891386003032130804444400035540220a000020800207030815084008440312038500030b103007580343c03c05150b0040080c1060800c1a40180712501000308010000c00c01001851 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915999838 1250 915998588 915998609
    0x5060610170606030a02160f060b04110301180902030708061605121611100e0d020606360a050f0907060f030f0b040e1605030d090501030c180609 64
    0x401186085030007180103410701914940702404560729060031401954040c0d020800036280500c9030360040e1201c82c00f52029202c0845100341c5078200000f5002d2054181d0044806100100f05800386554510043c45040085040d00c006501041c0360394002c01c040d00c1c0c006040e03503811139a410441d034640c00d0452700d0b10040c4403191584e0340300b030f80140141c8141081c10214450350340c0c6c401c0554050126022045800d00003c01d0b1350810503c0104580c915480b890340300420329991480000b031500d110303604418207641140c01005625103c0003403a0710910080c192010050340a907440c1107080d010032880314040c0400c8010081200b51603000130703003c1c1720350840d554025980c481c0c0c201d44849280c014000014a41c4420558141c480d804c5090301d0b840194000481242290000d01110054400c041c0039820400d120000300e811009003000400040d07000c0d18521401140080171440030f4020031b41850b980341006036600c1e00c580c5201032840c2c0c51680308050b550b12984040c18400b000e05c81d03a131010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916001088 1250 915999838 915999859
    0x2107020d081608060d0303060e07021f0c02030f0f0f040b0c160f1a0c010903021f0c05120a0f09050120191b1205040627050f0409060207050606 63
    0x20a968160146488543e039103000d09a250101007060844110b0015410140c0303c08001c10b0210503280540e015a110340c00411006410000c01100f05e00505081c0c0361513072900450644682d0003008076207440400c80c100540e20f03925a816140d0700c2c02204507100c0c1c0800086000b0070354560307207001401141e131564125400e80c4010001c041e08e100c0c0310b001d0b00106062421081055000e050240d42460306c0a4248a08041506001900715681c000044d001a44044000303000300303044410390b82c90040c041034140150600600041c00d10b1040e151544c16000b50080001c030045202c1c3d00c8540040144d11080c0101d6207181002d501810b9050804001500b80240400750040480b0403103040b0244920007000e05e150080341603d0948000c0d2418204280c04a21031000a0201b81d00d80300c0e29a080d140c03252502c4c00d021700100b1603400440280200f02403c144843c402c60180d551504407242200d413a0301d001c1c1e40f031021502611031701c200200310314008a801c030200003001c40d045218000650745902c69 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916002338 1250 916001088 916001101
    0xf0408010b1201150504050a020d2c060c09060f0c01050f06100306032406030803160306050607030c060b041104030c1401020d080a0c17011403010507030b03122107020d08 75
    0xc80384c0400481440e025030500400650401d40c0049502007407100005084c464041803180c26640340c20081d11078044a80b20701091080c20102c0e149818070140010015807034003c03031414140c070801c1800e511503080410816403841280c8122183d05111034028001418848219182c04a05580c10f43c0b069507260b080344010345c80f9105640407282c121070b104440500450b400b48900c2c0c0d1103d00d03070004030b403148800300c0072400c4c440c0114002c000c100303001910210380b10b4005040f1501500064840c1c60200300b02d01c007013076100c208511010b800c0382c400520001030f400040d000b00031080100044c01000b10703001086c4984403c0300c1048035000380b11440b4542c1c00c4001282c442c2c0c0790000004c080380803140400c80075003055000c01c03118108da08201103a85841d030341610140409038011019014011151003d6003800e02955810000b00d050601030703030150800207604c1e42500c00031000c0d2800c0114503000e00c426502c2000200e41125034840e1050704015000a4031064240505d00200300c200c00410780 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916003588 1250 916002338 916002341
    0x32b0905010201022d0d09150f05060a06030e07090606050409050c1614030f1c23011415040e061c021003111207030b0a0605030415050c0f0408010b1201 67
    0x180040354114003206800340c104003103183c2c00e0480d82928a8801808006d4041000b8401c245219003d009000da000060304d0902c0c0a44543c3d8a080031040d040c80144406601d030030380c00b40c0903568223060220b262848144c0c9a46000b01a40c0024009410036100049441e0080d0041056603681707403040c001030f07031848440035280c031860300403c0480c0303808221070001c00c1070400080c1c50801c03a5402d81c1d00c1c1a52046009405400240c607044400300e0b003d0161400b1807940c4a0701d85488014501820101d09560825000090510421545503c4c0303150750000c5a039078001c483e5058000405480d04c440d201c1d04405a5100d080314040d02680380058034141141c600d810652601c0d074001c0bd600d2640070000d03030460142c600c9681c2041c00b07240070f02421480c6107062000358401c040079540025810032000802100001e030707901010030b2010400070700000c1043c083e410ba002e400d8080740440c080e100d0700040780d8248101d09104440001c00305020030b004406400100c44000e00b140e4103040345503010340d2a030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916004838 1250 916003588 916003597
    0x3091005030a0f290d0c0b0d1a01020c060306010309210314091209010c061b261f0b120a0f0e03030f062403011503020a0f0e032b090501020102 63
    0x46245a01404c80511681041c803000031080d0140410044020300d0313407607152144454122980a16003c900d080080a29104209110319070207540c840c0400001c1c0041e4035a0388108a15000700d000100045040e40a030300503008466103c0d4040030465617070f1201c0300003190660241d030002414085c19960440c2c20700303015401400d0f400007500d00411480003407244d0741d10a001142c180000080038801081080c824032a1510101c0c04810300d04d00700d0640100700340300c065903400c15088010510034400b11200030456004a48030a140101d4500e50b0300030fa0b403410191301442102c10700048072241380c0ea601e40040c1c00f0b50030590041c0101c09280080e001a205102d400040d140d0007032000034020782d00c81881c40c0c0c0007c0b010300078007405901c0d0440c03001820400350320341b8a083c02c00801004001c910001d044203030300081c6821802c00211440003041410060880e00c100010007043c002150b81c107000c400958181414002c9508190f00c60300b0429925620000700803840d00d00001681d5401070003200d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916006088 1250 916004838 916004861
    0x717070501021f020c100e0307030809060112020d060605150403050f030403331505130b060301030201110c06030f060906030f03040519080f0303181c08040503091005030a0f 76
    0x102e140e00885000f0710020741003940307403641602c50b0345000101c2c4c1801744a0340141442c420080c2d9550096820003078030010000d0034140240d81321200400189000d61204040d0b01e40c100c411803284902418100701500c03a0360051030b03000c0d4011015110b1030740080c006200300e80c821001c0d11140480714000325140d0041d4800a00251018070b03c64a00710300580000840c0807034428404000380702e00d04158100c0d40440c1025000036001101807100381707465441c2000d04240101c05010052a49000c10904d000c180710082c1070200d1295900b0002006200014a10102404140d22490b2404d030b61080e00300f0030340311640543c01280204d04141400f2500107031a6100310b005501d80343c94001800302c000303814158401c503000354450204160100b8054008501d0711500150307243e0804c0b103c130600c090804800030007694440e81c0c040755081b0610181a103d99200c0c01c11100703540d2a401d205085200703032040340b0340c000500d0803030700c9149070000050742c050301e1420b00811103d0095690082200d10030800c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916007194 1106 916006088 916006123
    0x3070201110310030b10030602070507050f040504050c10090b07050706080919060507030902030613051b0f0f0d0b0a02030619050f01120b03071707050102 68
    0x4082076120304915041c954104000e04100300d0f0321138800200110076502c0061040344d01c5c1401c130802541c011000f5541c40d110f501c0d2441c0c80340444e0160510a41c0fa40b00c41c021582468490648155480002043c8621148080003401400011582c0400c01c0d6001d01080800281e005042601e114900501d0003e040000c09043d0f20380003000b80d501a8400c000d00079080c2c2001602240c0550000c030300185545507000120040c000f140c01c0603401d403090405000000e6040740d1440500c601070340507107c051103c00e0481c0c1c2c9540304010301551012090001e01c20901e0304040904001000a0458640b129161348161900f28100c07843d40206a0200400903541008a005901c01c4405101494258240000503608d98100c0003640d04000c0d030000c11458400041d8031100584a0060895403490769444850707a80c40351901c5450010301549900241c1c82d400000c40340d5400050120 = true := by decide +kernel

theorem cover : BRFrame.Cov 915827338 916007194 := by
  have h0 := BRFrame.cov_init 915827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 915827338 ≤ n) (h2 : n < 916007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
