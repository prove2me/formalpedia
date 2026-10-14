-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:26.403008+00:00
-- url     : https://prove2.me/submissions/738f7df9-c33b-4e40-80f7-66f695e435d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 618705035 ≤ n < 618884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 618706285 1250 618705035 618705049
    0x2070602121207021c03020424270518010302100f140d0207080a08010839130e0f0f030c0c060a11030403031d1f030c02030403020a03050303071701140f 67
    0x17428440c142401d58080d0489941030b001407080f141c003145908541400c104080c540f006c00e8003500130200b2440c440780d015640405019510803104d03080950f103003650320000710314001400304104009910780710042c0214a00003080c100f1450700e51030501c08405c81c105021300000648880d100705480c1c0030079840400312080e0100c030005030f404401782380c03207240101001d05000d20a004203022801518008039020100841000b0394540744513030b0340210220362101860801a04031407039000180c241108c56550454007030701a940007080c00804109e44075202603414941000e01e46042d5030810840b0b000e009800003034549907801b003181ca1903914000c55006403a1034619040311155400040b03000001d154100c03040b82d0750611101d540c00800c011000030014140320007111007980101c4007900a81841c0710346e21072081d11040d030044030318040d180e400190101002d544105c4103584000208402694445030781102024446418441941002c1030b24819480d2804158002c10102244440558840c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 618707535 1250 618706285 618706303
    0x703050619031a06010507120806010302210f09161505160c0501020705062104021c0609060f05091903120606120e07080c01050c0109170a0207060212120702 69
    0x301e28031400c1039580c0b42285209a400d8252000301c50b49100250080d4011412242c209500c900b0b8840c13100c0c07080006968441d00a020703541050790038000000300303003038411018107450f9052000b10102d1411810040b00300b40010250300d03444d000a04003200103007000da00c0300c040d41c94001c0d04030010036096a08940340d0052103521611680b410851038240160209940103a4001380c0c2903c1c0b10780c0c2c41e402480100d00c96013403240c490500f01030712600a0300282c03086c6500607200400d8070071500035030911043c0d900d691101c141c521594480000301008002c2c4904851400141d805001e5482e2250f00292034070b8055009282d00314205c1a4041050300c540d40c000241082c0c3e44003000714580310440240900e1425915150a62505035081c1101c400001c185045822140c02820318041d4080115001d4001400d41c02d025922100c0d1800014001070448184410258a0715110011840d0003444e244855020740c0640d000006810b003e80181000c5400d1035003004c58540c0700d9160100300700c0c0342c0001c070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 618708785 1250 618707535 618707569
    0x2090f0d140a0309080613020922020406090204051809071511032a0a05060109090302030906030a0507080c07020d030507020303120106091502030c250b03011e12050607030506 77
    0x44440c080403d6000003a88051314103000c1200c500f40c0d00d05500b4441c003030490a002e94171a4a180c001010003404c060881c0074505d03858591000920603601117001d0362159088041c05030b030041030501450500d81c0b2142c0046000360301e40f5020b404c2403400e640c0c442505019124410b00d0500c1000409400b5403a1400008020405c80707949000306520030714040600005400c001d01605d031408001900041e20268468100d80a018540d2030002844000c0c41948030850a600003807000c01d110355114409148038203600724000c01c203450900c600400d5000018548010040180068005a00c0c1c0e05a900c8403154141845076440c101800003a00d180521120440034041440011401c194805903030812907183e0211410081854102a6141e000f031941c3ea003c558800c001d2402c488e0a110407452084001d904510071131601c0342c9054030582c0c4241c10440140c2e16081d0350034180c0824203541c10092402d000c402904900d680d85645d1a42006800c1004144d11580070428941e81c0e0304a9416440c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 618710035 1250 618708785 618708793
    0x180215040b0c06010302132310030c0e0105120f0a0201140c0303040c08011b0212031e010e0709061b0209061903030e041d0312070e04180c060302090f0d14 68
    0x210780002d0355070740707001d0108a005031b400080703001b050000c038000d41880001d035441e031408010444541d90301d801801062075a0030b0007800800004540403400c458080d040c0b4812900940d81400c1c28003244840d108100840caa01000c4407400c1d4910204044104a9092078494041c15800c16900c1c1903000300c0f89000991701002003804204854074000c1400c449080b0024004100240c9280b9108800c0700d8460303004da000310f4101c1040d0601c0000440e40070a0704d003c907000682084612501020098214519421601050101032504440f0341d000801d024500188007103400c8402002221103483c0003402841198041545a91102c520001441040006108040e5a400d0081019140d4400580110f2a0100142c4103892001c040f10119444200951603e0703684120322100d003500521744030405c4640000c020280d0766034012035040e02c135600504041062241484001502181d003c0382c18184104030381e000c03940ba500704095501d1412200080c0507041c5040c002e0185052100140142c05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 618711285 1250 618710035 618710047
    0x30f06051c060609020306130f020c06040b01032f06070606080610060311070201080112142e1506050d2004030c090504050a062a020706030b0301180215040b 69
    0x10040075695264040c03401807122a96440c1681c1c22848180d0362140c0186a0f05940f54080b0101e03000b03082ca40362068001071421000681d654100304003903c0032181401c507500100305000b1804101c110343c0c000918034843e940c0690b51120074480c9051708140c0920004a1000c1c14007181d68010402886034400b40c1da194a80a4650300c500c0c405401424080703850005902148a0800161070040342d06031a080070036400d140d40d20199071601107040f00c14184140341503550b02d20501254091720101c1c000c05000c0004401d00401d544000c80c03e9141c200d02d4400b80103030550444d80c1120888400f800c0007981d9950385402540507000710070f2054400007180c20030902e0041600c0081c1304580c0240d440c2c070f015a8039402c110059400c103940190496200c01000008202158400701009c61600f40e034480d4041d089405001c851130b8040c100d005a040701da82000007039018002d45114200840080152114400000c0940300007208003034041c1c2c407a90b042600c140070000841e0050203c044200c1d4642d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 618712535 1250 618711285 618711319
    0xd26060607200a0f0503071a0705030708030105120f0a031808030316030e031c0b0f030d03090b06100801030609030311161502120609090111070c0503010b0a0b0406030f0605 76
    0x403002245001c3e29207035a0010f8010060029001960401030160404030315003c110b03050f0400c0b0040c11407441400f0402a000244104010034149100d650010389946c504410800c41a40401d00409150800210f21081c0c040110302c50070f500d64507092094500b403003003405a410f28002e030080201c070721000062188141040d080c501103540690b809200e1420070f03600b810f880380111240307045103d0115001c802320031100e800100041c00301030603a10500320789000203490404003091420101e079580740503805214103800b51640c00a41943c040c1d0511305101401824006e05200142c481950b40052000b010300c00d80001451030f5002c3d124680b42c80341e00e6601a8010310f00c1400300c400c480c03400c4421100c4030450090310104d000c105446103442d41c03a0b9052044100004002200035561401c1001c40300c42484094076503180a1480b006807036052100f45821900c403515640d104019121007000341d94816000c0f6029101070741340200341c8514011602c0041c094a41211fa4007100c040a041454 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 618713785 1250 618712535 618712583
    0x140111030c072d230310050f0f0c0a02030913020c07150906020c060d020a0905030105130611030c070219030b0f09012004150923030d26060607 63
    0x24100303400e0004108000d0591050001100d0701c00d60240ca4101908070f880030314002580c2d43e00382800b4042d0380200c4c1c503022183c6d080300c3c0f00b11070382c6840303080702e00510443c80c03401003042d5405640024100e19003152010b0295813401140b01e040e224101e0746203100b1805140780c05581d0301c074415204403401c9513250300030040e03002c50071400c5500040c40d03c1e400242c1541300103448080c01e400a8180303858000351609450103980403401810520000d01800211a24240b1681e0b10070880507036000c55610791850303c18140c076450700c082039040742c050081c0030480f030410003180c003482c0d811100300c140450140d03545082e01025500c050b0850710200d04000c1c2008690521364440c20a120007004a0048180b0b410401640128640c034522010f01042c03040446480001d03851076010b00b01856032980d07a00c203c005441c1c0d60090440e00d180c1380340404c50903080412082c0403101040c1413994103104182242240079009074030039a49901c6000c0400d01c01d850321001c4400481d005864110f080c01e0048031a025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 618715035 1250 618713785 618713819
    0x603120f0210020901090308090d05061503070e041509141c0e040507091e050303030907030c080601120206161202010b01112103060307050a080c01020d0504140111030c07 75
    0x1d80102a42c1c910100b50520850f902d0440513101d10609608584800704035030060b1308001d4011100e5143e040c003040040200e580b1544c1144c000e0060b0780d42c0c01050500b412066031010114400007024400000c03258150300500030400c1500143d00350081c18404410085c12490301c0450084407007100001c40701c861660034144164442290039401581070204440d07085400300c001a488180c00e1229a020032a494030032584400500d03202a02e03100001e040d9030040c0c1d9110840c0d0700c40b0340d0800c1003000c141d121130f004002d01d01c090b060701c1d803615107050444141820000c3c40346000281700e801003800c0c00c0e00500080e8016418400120303069030064000c1409052050204130080b407034030904200044c00c6405940c0402030000c0902d1809070b0041e07103800140440794903015607100840c03a510345410410040c010000107040c2c003125000060700307106c01904680c0401c4010082405034980c0e0503603481401000f807034030804250a4112040c254001c4a042c40d4550050300300010302403902d4810701d81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 618716285 1250 618715035 618715037
    0x4060506040e06011e02030723011a0307080309010504060507172101151d0f0904080310060305040f0f031812031e0206070f050903011b020c0f130f0603120f 69
    0xb170200341d40f00742003803c1085a00075000580c01000403c00107680900500580c00003002c940054141280404e82581c90030400000740390a5000d00901d070f072901b00200c030014091200a145071205031800208648900c1c0203140c10302c50001142c400704510070340345d80010315070328001c01d407541c020b0b041200c5042090713910700c81c0010508002052078200b2200311120310616849031400c84548000300710300710112004256001c4480d00b4400160789a10030f0240c40707544200242a6240b5181c900c06400319a0754121908241c030340401c00000949422440030050703000008000e84881c0c520b030448054062030280a03c0144558000654808144200302031078441d40b90742c5404000d4440c40107483d4640004880180d010102141515010352040e00e000f1100789419440e00c00000d010900b5502d081f1905090f003903a200403c04e4507541404403179607581080718a070406502100014404400500c6c040d81c481c0da640342c081c0c0b04541320f5440301d8001c503884103c000c0d05d03c6030705201504014481c0000d00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 618717535 1250 618716285 618716297
    0xd0206130f12030f03140604110c011d0d0801050a0e09010f0f021b0c0f060307020a0b090c0f0108040b07030c2003040816030b0103060209130e0c0a0b0c0705090604060506040e0601 79
    0x1240560290040d003400144443c4031b0b0846503982c43c10000600aa1074103406000c01c1000386440125082c0241e401002440076130007051840704910516015245000d00100481403005010760b40c0c0358182e8108440400102080c0c0751141c00300c0d2801130401161240070249000c103110209110798000c3c2840984401010721092000b40c0c40c2070300c494060041540c0054100c10780341c42c3d1b262407005181c1110a030310444203885043c0da030306240d004040d9038070700c00c1d544180314444040ca00300d599a40e4500b0f0a2921841c2424555103015032600081c2c0080103068840b5010043e5600c2460b42204c0141c0f02d203582c0c03230284030074940c0d5500c0f603000340244c41c1c5500640946c1490070700b0000012088a50202048070540e00c0e50702c41a00940003118281c0e4008203901c20548221528000c14115418040c00f8195803525841040704214041e07110061140040c003000c01100c03401300d01d18085600c01c3c1c13102481c66660ba0002002044140c11085d4400f0000ca004100610340f5031055200b6802a07c43d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 618718785 1250 618717535 618717557
    0xf06091d120c030d11070804120605060a0b0307080912070c1d060d03030203130b010e070e090601021e0c060a09090506011706010c0201120c020325020d0206130f1203 73
    0x9400140704038489442254801c00451004000b0b59001c81c0c0300e0f802c46242542081c80e50380e40d81107103622689c405401d403407031659464280b00c0d082c0b0440d50000000ca0f20650b000349400003545140c00002d00d01f00a0000400004141c0c0c0b1003440b03149040d00303044100c15a41d10346841d04940c82c80082c0151100b180c0790b10681d50543c80b90801d0386000d400020424000c0c1015680c0c02c034043e40c002400c51202a00c2c0403d00c10004123510420b40c0644103503000c00f8001c0c940b18000405098186218500c0f404511303062001c940d070040390f00c1080c1c801c001b80207039103280901c4207e8503118450300001e810400005440001c203a029600740d040d0b60200c00107010300c0d1a898011070305d8030b004400e0b46e00ea003001030000c00d400d9800380c8a01d410082c4103041a00a1302d900f6107054007100c028103100740160304000307551a10b0000d12960001d84d003041c7d0500e01d5a950050f00440c04010b07507070307000a02409002403860603a03201e01350100001c0105003240014540c440d1541c44002c100b030842200860360358442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618720035 1250 618718785 618718813
    0x50a090f051503030417010b0307060c020907080f1f0b0307020d0207083c151006110d03090825021201020a080a0c140c070f081b040f06091d 62
    0x2008400003801030095080c5400c050041481040103004280e1b60f650745c00c0d80c0d07420b0361001e00040d0000d220300d031a5150207400c240180003813000014503642c10452400100b084c036511045086411030706804104c01d8810030304004400e0011709400002d5182004820003e68603400100306029a417a9429100c2e81e55480703606c242d032a666a04003015245c072800c1c2c9038041c6824074070303c41540e1003107041039103500300d01c04030290a014295600600300b0010b601084842c0700c2a01c0349000810040c03400b0300002044104240d2140b440d00214020107458116590074041c0c01401d0f96080011220200c0d840c8180c9540d50f428007000a0040740150050500e001d4070303140600c26680ba50640d84c6540803295564001d5500400f61280e500051001101321000120702040c094001c400c0e450004201d1182003c0d41101c0e0700740c20f9448185d881c0d0119440680b0081d0400c4040a1200c080e1808114400e1041602007d04a250088038a03a440c0c05101e9540e2204598120400e18225003070f64400c2c10f000003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618721285 1250 618720035 618720061
    0x10c06050414010e0303070f0302071e060f15120206090d0218040b0a0c08070c022403010807090605061801031803030515090709050108040203030c0d0c0c0b070b01030b10050a090f05 80
    0x14540b0080b4400d000905907403404ad40080496610400080812010440c40c0030443e20040205030303505035403440b0400c45180c0600c03d2441d1600041740f03001c04c0d90b1425844808090100000901412000c9100f0700c454440d1000c00d10312960040ca011244a090b401581c6502e204440580b100303510342c030100b06a070810744100342c603404090740c400d296550344034815225070403c4c910880e0000d40c10804980da200c034000c10421110304140b41c1550f2540b5088840b4a0655180c200345602440c02034108019a504130481d2052161800d061f0366100d4943d005a00804603a00c421103825603079042c45080603030550005104600800c00809004c141d102403041c8044101c4100001c40c21125041c401580075810590340248001c003280e1922211076001400c0072095401c00000c02e89030800042041080c140d800040d0150041450030030485803a580e08095040c03102801006641000c60307062101120b9610240c203020300900c0201e59230f43c10f64001040d030b119140006074a0b01c0b000c1032512950306 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618722535 1250 618721285 618721291
    0x12030f0c0809042a030b0102010608120301030b150a09091a0603190f0804090501031a0f0606070503090907090f27050601020f15010501030e031215010c06050414010e0303 75
    0x441c1150400b1441414400201020b48034114110542d515a61094803000000e03441240d140d0b0313000c1401c1c3c083c0000a400d5031241e411800c0203030800e0b4000c01135004058140c4e411a50403030700c100800c2c1c407102c55404a41301510308254000103034002c007244400380c0b500b040301468030a03410b001c03901e0b081403e50018110240c0c0c45603850b40008501031856a105450458424040c00d44c6400300c2d083c3d9074a508071a0700c0b0741e000703410460b15800100305214459048007504454903e40c00c20624101c0c0c1c0c029a42c19009040d18030800000ca05a41404000c201707407a4260ba014280c0b542c14140f40c200500385510900c14810017008420000c03441444548482402040948940350342604005079000a000010020741c1140b20700c1c085000e005100300600c0416030842c01c00a25254108000101511000080e204240c0d004116150300d13142030800f0703150301107808400565a640e1040048910000c8000d01034003040c1003806220038410396050018070b100100c4000c0102d492610000e41c3c40780011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618723785 1250 618722535 618722543
    0x304120c020114180607050c0901150801030f110402220501230a0c0b01030f020f01030c082e060206060a09050112060906021b0a030e0411040302120c03030412030f0c 73
    0x1d044007000302c000e03c038041e0003140244d03803071003021620420101e4425080f03148281c409600c50003040440f41071410826000d001d000c040f07503001c036058410145c124071040c070000f8031041c20303030403494188a070880713146140b1136006000b07640c0d814230030007114603501c40780c0000f076149121080002841d601809100078550300e04505146901d00c240e210341c0e4030b82c10010b13000b400d01010045960002c2c107506030890282d03114034080c8840115074014031000c0c0c04080941410b261030300506040c0550092045c43d4040f042c111240c0044842d018070807083d15220603550b0010743c0c0f045002c0341c44c1b80c0110381244030700425540032001c00d9032115142d00b6600c081c8640d040307280443c400c6402103601508041c43c0980105c90141c03030b03c405202007500e40105c001e81381c082900140001300c1011780c05540d012004c00100e6081c006002c4a241345400c83c4668400244208040401071074102030034480e204c2640001000c0e00e1321960f40e950781103190032a81c1c40c105c001444d070000e0050000d020b40d04040c030003508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618725035 1250 618723785 618723797
    0x411010f021509010b031207030212030c0909070c08040f170a2109080a06020306011d090c39070f0602030d110c251d06010e18010801020304120c0201 66
    0x1000320001c5802c40c041e1002030766540320303010305038075072000c00c100d2010700790213030107541d4840540c02c00030704043c1070100c504a5000200207216059206034141d902000003150042e049803164171003550a4812004028000d640200700001c2c4000d000d4444011241e0309170130006105c0c40060750cd80c840ca01203000600c0f0350840403400c044131410940c0000742000d14100703841c1c50798888541b18500141c80104030b620640000c108007040d41e1042480c032601c1000b004580300000108001500110000c0050f01c3c2c020000c0707000746000e40141c0101e8003036030040000c03191503400c03042d11541c03030b11a4900c003c4040c807903200f00180a2500403040821503050303501030350902c480000d04501410020032070f80f2041c0b209014440007010188040f0900d07481d0340d01100d484030700080480900219a6202100c2a40780032105042404400c1c56aa402078092030002e400e0300520001407400032000c0d2a5501c52061000041400311055000314050340c0150124806841745100440c3d4049502e0b030002c1c00500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618726285 1250 618725035 618725053
    0x1b1403031213150f051602151f0506121b031b070c090c021c0905280305030403050109031704031b03050d0207080d06050904021f030f02030a050411010f02 68
    0x40098100307510180b00e0f1404510010301d00012100303a0340000341c500c0d62103540c0e500b07200203400110780c1c0f00c0007240785002818988014000b40d51513943c0040c0281c44c404880c0c0c100703208044040c002c88000c1c090060682d80c460301543e0107145416011261080d11490f402d02441440b050102030303030301c94840080110f10400341e21036094507075000700c50b003201c1c801d80f480d2000c10300e030940e80281e44045210794003c1980e0b43c81c0520711050f244840307100900303000620303c00b40400d1300e81072071302c00d0200140d400d00c02010300150110f802101c810362003d01180008a4080100041900f208503414001e503940394030f2400c0c941000c0410758007601c000f004241d070f4a8a5514010055210b0401a8084e0a0290404000d41c181c402a46e03c07231070301112111000241e49044500303e2041030040c0a042d00c1034481c1e41340a90201c0d6803a04040420f131030080500c0015003000c0d200f60000c0c000604807000c01c1d5100d0901000780c1d0050181903030111400351100c0c884200c0b551145000042808035130f4000e0101e80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618727535 1250 618726285 618726301
    0x2090a060812090103020f04031b05011805090910110a030e1c0e04060806070e0310020c120f04121410090206190c1e030f090b1c091b14030312 63
    0x1503c040c1c1e032241403540034800101b0044a50b0050700085005000d004102071182c56241c10040f0507820281c14400e443c03c1e4030300112003d07070308107040d204191074603d481e071036050401d4035042030720401c9000541800d6001d5514a0100050a186c4019442c1800400030701c082e03a0391600b0101d00004486003414400c003069521034400c10902c01c10240001a5085d129850242440c1080340c800012405103900f081050034208036014000007618400c5007420b135005c10707407a1030300c00780101c0394084880401c00d21a01d00e1030b00101c1c0e0080510407440c54000500f07190100036a40c01c1070020032580035624603056801058001d0004090b401400103241c12185503240040007001c60501042005d40c411880c005849451195404004848130006818041c5002032040c039108019800300480580200300c5c800c1400c1c25529402000e4040400700c8014807190001040301c2d420280815412504132800c1042c0b1041030b070140c503415402e1003030f043e07140414143e6030300c1a111580110100040001e22107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618728785 1250 618727535 618727537
    0x2040903030c092321010912023007020105190e011403040c06031e0f050a0b100206010b1803010f0e0c060708030103060902031e0601050405011224110d02040302090a060812 76
    0x840040c1006591020010178440c21501640c1044400a50010109803215010011441d058040c00b100701100e68a48616950100207088107808040c4041004421a80242c00b80d558450303070901440301c0300782e952000030040f0030244403503400304142405020030264190201c91190341c2120240807014a441c0040300182503a001100b200718510b1400c8098040d43d000d5a03a02181300c00c000b081c02c0c1860f03c000c600700c1c0d520103001c0d03128400d003403100c034805a0085011070440c0d410001c100d17104e0715506196020180c15003881907040d4030f45454400007110a03840403104d41c0380e81003201c10a00200d42448124855440041c01218050004200044040c1c105800291015094441001c030b100014200007081c40d401081c83d0300068018402ca04140c8075090051800560016007860107844000341f060b04800f040d4400800410f138940080d8051f045000aa880d040c0d0907661282800303c540c00070340060100b244240c194801240034001d0728050030003035650010242064900050030002c00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618730035 1250 618728785 618728809
    0x40504030503060f010504090e010f0501090507140a03090b1f0b27040204080d081b03060f061602030715030506090903120a06030b010f0510031a1c02040903030c0923 73
    0x10046c0070000401d0040e4135006589102000200206404022640700c00690300140c002c4c1c0c01b0603140c0003c00c45801c3d40b00303100040c0130080e80d00d1f40ea07a82c100501c00710060840d40001078a0644040d003444040d1111070501400e11050b84003550845848008070040d911a400c4181d03203141d860400e029001240c1c0d4030105001c100104010b24043d82c48030100d06286002132900c001c02c0c20340c0c00304103116001e40004500178415100042c0745280410002d000304500b209000e0159502180d4412400b005d54800840300d44c0040856000541d0f8100e4001d015110121403030000741002c0100b100d90920228050241d02c1e041c021314200404004002028603000305807001031034030340c2c0c4000040b03507a09014a02800d818840f19210390300308010310422001146400d010145070503044108410032012868040ca0101c940c414100174840c0448184441410040d51240ca4412600d0806406030b002c9402c1c40e03880d8440f52039507595900411142529504002d680c580b042185d1030301c03441c0c000d52487c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618731285 1250 618730035 618730037
    0x5060d0c0b0a1e02010e1b0a090b030c0a23040509100207050723040e0a03170702010e120d0c050406050708030c071b0602070909020609060706110a0e0f040504030503060f01 76
    0x102103203c0c0242680d450745000880c01607590b4480d00d954aa409016a49424820a80f000c0381410460007240c1410302c0b902c114008255541c0c039002c000c0d42d040c84a441102001040c0c0c0d608541c40f9424071710713100440c00391007940c40030121030786450b403c040c02850f228280c0400503111003890303c02614060750200300100c441d806820408500d00114254814140c4400010702d0900c810f4a03043c40304540700c41410020f598000c0e021080081e620030544030034806140600304158458107000da0140c80413010864082c01021560340c460381009002d0802180d141a0501c0080c903040340550b0311340709a01402000803002c10090021511000045401100201c0928030b854903c1e110307c030703200c2021414002c4468440c034040181c1d9504018500160840c1c5108002d240000d03070006526201e0784c2e802714005e030300c041206010f001a0340e00c1503101c45030500102c0c0c0d8a90318590010320700c010002503d8801c102e180c9584174241018400c40e4412545600d68038a03584031501000101c4078000c490754 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618732535 1250 618731285 618731297
    0x904020111070e1009020301051e03190f021521040314030403050a0314070f120b1f0f0c080d05060f100203040801110a090308070f0b0c030a05060d0c0b0a 68
    0x805907100410226000f04104450040d00381024119030328541c01e241d00038212980180018411035540c100c03103080240340402e080d8056941c2c440030a050085d54074103140303680020801e8009100c105268102c1c050301c2150580031000d444a40103442d401500f032005003c42c3c03101101c01d00c001504520a130084c1c06428480c0b0340c0c10b04000200101d50044408400060000c20854010741e0503025103095582c2211040ba401d2422400080005455400120030413400200d250901c8910b0340c055000b00d03402900441034515018285105060741c2100c280003c0c84804d86101d04034420f030400304010307a000c0f0070580303480c0420106401604000c2e201a9002c983c036007a0412a5859407260700c0716014036009151118a0300e0b00c0c060844040c0200a001500d082140c0c841c1176038000e40580070b03a503010394003d894107507904240f109500050030003050f510480d003d21007030b84034400107548249103402061045540341d0091100c041c603a01001030454068140a001910200024000400c2980307405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618733785 1250 618732535 618732557
    0x801050127060c02030609071a0d14250305010b03010b0901270602010b0603060a030b10090903090527181510060206012403021b03031906080a05060609040201 70
    0x3078454074605030300020104081c00c3c4401c0860805000c02580101258050016a807500b0081c4545207403600c00c02084440026184c401c2c201c031a8002080d400c41c00e0061071075442c160303c034803c10280058801c0400003808000d00d040d070740709009072410b03200b44c00b4245045900e8001940b1054000c0c42d1940e040c010441608084501c1041c3d030b00104005031040081c5051420001a0850b040244964042d0f441001002a25107500c031039401101e80c000e24051255603484400050740d483ca8000c10681e508040c840c1062690125100c01941c20885105490390098105400c2e1000403e054426005024002840030640c91100e8040f04078000103a9105803c024200400c01b14100d5804424a0000c0010b006403a070400c00f080c0035261581c401001642c030740340b181d403060354511544000c1540008507034583c400342112614003203030030303c04580d200e051880f210041c00c14182082e80c003042c54281c0024910800040505403140c01c880605540e0310390009114806000520a1381801910210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618735035 1250 618733785 618733847
    0x6120f0231090b15160803091c11100504050c0d0609120c032307020d060f0e0c0a1e05120607080f0402090c0702041e020408010b0406030308010501 65
    0x641841110030001c240103411240044500281d004000b4051a080f2801030540710001c0094211451560300781c4c07640ea0b0140300d00e6a10000c603900901200000c4140700000100103002c1c400001d14001c0c41d01d0600d00381400f1a0210808003040240d64410b00f041d01c0c0f07105481c0d004907080740c041c3c010b07628158941c4000c5000c0070140041111080c0d654000c0740180212840314820310103540c6000100c601d02ca4400400c803460051000c10300705004c1d2040180143c0040480c0c06c2d20742d010b40449407089582c240a40205038090f071240905040841100420402103402e800c000700051842c2c92413402e0007010340119101841e88001c2401c801c401241d141e0b00e0310440d94882000d1001408145445140180460f130701a001428018411040c040142d407000e00455019040d0080c02d80c40e070005000040261801942c5406806401c50096144095a400800640b001a0003d200451881b018002100d07091700c0301600151468005001c250b110f2a8804a2008040704c1c807141e00c03854100e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618736285 1250 618735035 618735067
    0x3f0504051510050a080a0822080d03051f15180b04031103241b090907090816030c06080903071502070b06120c0f0319080909090706120f02 61
    0x4120b41d400300300c040304010900d41128840094040324001c0d080705003a6a440300203a0003018001d20105060519038101a990070b40490000c01c40352048030801d00c0c0341c19019008100aa90240d00090303810640e00800c0740115400342212000c0b00030480414a1690480b04200200085c0d150f4103010341d000039840340c02d07001400245010b0300740c904035002d24404151604400302c42002440c03512100740711146070728034649588041d910304c0303101d40301c44003d040c032034203210342001035920200e003401b4407010b5940082c18105407031095080311400901c04030340c4a800002c9100060990381b130703080180300c260300c1400d40320b0300000882c04613814400503664010101202c3c0c4540e210f45a4080389100a104840c1c040c1908180107031400810344418200047c0c41310b03000d1284c20700480c243c0c2601c48680d10b0400441d03900100d42460000c801c1c810386481e045550101403c1803080c9464008991000030100e100d03411540d9944880e40b81c0004550020050310003803a161224aa00307200100d1550f40300f44c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618737535 1250 618736285 618736291
    0xf060306010c08030a0e0f0a030e060a091e0303030606050f0d1a06030a2f07031d130509241b040321030c0503060d0803060607050106063f05040515 65
    0x41c4000c29a504c1c204082413420ba071001b5141d03070988c0140c071000e020a800003030141c0e808400b603c0b8070782d0711100400c0546d41c040c1146d102d0280e0640000101409001c011f0450054034869541800003030707500c0e141140c150103240039580d501c507002c1001c01c461501a0b8002c0c481c14910b500e8900c0c860310704000240340c6800840740032488549440b60f180382079028112660300301e010a081c0102201d410007005045020ba0140101845500304121a40d000301444660b02d442d0001e003200d101007004440306016003020b45125401d48501c1058201c40d02090002d0f28401d04251002d82d00d940d1200047c01030100c1c0200c03030300e207271510400c404408940e010001c0b214512000b01080c4500c9581c4400904813250400000c003004402d0040c849156140500d980314141c000c0440c07900c80d2035203000209644070303900d40103046601e440b000260ac182c0000d09440d9103581c44800c0e11007091a03440c0780480d60f4008a904a0303034034601800d6880400300760b10041c1c025010f00c00f159580c10300b06907030100b0a0b00603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618738785 1250 618737535 618737551
    0x1d04110d080406020d020d05070b09100606030911120a0213380102060c1e0903070e0103020a090e06160e0d14072108070f06020a0c0c05060304020f060306010c0803 72
    0x2d0280161a0104511061160b603480103100312039034100700424502401200405004055000c14441c030ba0421070410001e08803d01040015034400c0094000c01444804440110608080c41c01501c2d00e6000ea0b082d51000d000a092034a00039400c029075101c12600d000c91131a520140f015000c0a200010029408041c9802000d45405105c1d00d17601440b026031141194440002c0207110405503043d40ca41d2125400761076000203500f074280c107450042d03a440c19018410400009404c2400c00c0e0325a041f01d000307035a01d8052644548081098401c58003001c6859880b00c004652603a0080001251403801454a06d012070403880021f00c07038101f00d4500b900e14040c1e07101050b4000209000c1c410091402d074a40707402c00403d40d03000040b1900001806800c128020900c0c0050001e080100c031403166001004669908030700a02a0081407100820303aa200042c0001103000e08028080300d0080c2d400070642403008000138100115640010107183c108034082c900c410004036210050b50103030b03040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618740035 1250 618738785 618738787
    0xf0d050304020a17031305121c141c2405010813060c0f180303090b0306060c061602070611060f04080c0a0303020309150403050f030405010213060f17011d04110d08 72
    0x6c41d019808074542d8122900c0303021110008603c01e43c00043d10144401d8141014000301c58114050318a0350000e400c50680b01c00c00078500d20300414600c00708800b00b640c81c0f010441c02e0407070700700d0300382194034071000702e200c0010f54030248007540c0240c0d80e466001c9200402c0d44d81c1c00e0881d0782e0b40c00c00d803000081f2020104240302c84110b10281c100c00301d40b120381700d2164060141ea1458030300070141030492156052a160000108020381c540d40100c4a05030f8162045400608110302042c0e81c20f400e003142440103004610000c284140701b400640b0107107210000404441e01c4807840b40c2d056000c06441120081000c1200044c201c000340400c100250007901e0050b242c1c0380c2290740358100202103410f585241e540d00204030010b50000141c03085504902c119036280d0340c0c3c600d041070081c8100791501803414543c2c03000296265200c0c5800000807000d549031403c10070008040c44a000c403e005403003048a416a421603040034001c01540d11900800c09800c122001d500800d100406201041c1c0311090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618741285 1250 618740035 618740047
    0x7051303061404031713020f0d0204060303081b040f17010e0616180501050304080a020102120f010302041a091303020102070228080604110904020102010e060f0709080f0d050304020a1703 82
    0x1402035141e1040c0b0803640c3c020700d010701e420b240c6c021424030b4112000b03119850112801249842d40c40d01f02c2140c07070b4003034002c0252070340341d04000d4070040c0104d41452403011101d0070410910803103401e8034125551b181c0c06003121818900c00c20380c1844180d2003e045590707103210b41414064100400c5000720791018203505d505a003401d00134205810030b401c4d280e02c42030381c207002c0005903031060459500c25040380f0b000c0c0e220061200c049001e485002030140080034680c6c140002203030102080b40c100c0c0e200701d80801074201040c2e0805541d08500a040340d001c10000d00159070b0f040d2003075481140512910005103003408543c005400039462404c1460340da00c102c0d00c1c07080d10003040c125a4014260340e00c0240020310f41950f80e040c003c0d050b100210b0191090501160869000b500640a0486410141c8100380743c0890114030044d0700f207909100091012000081c090b17000708011000040c0f0f68007501089240103019141c50b0300240049801c02d0003000009680908d1075820901c00460401469a6607 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618742535 1250 618741285 618741287
    0xf03050c31080f2d0f100f0510050f151303020a0f03050a02040f110c06040c05120a020603180a1a0a060605070615090c021c11060705130306140403 65
    0x800d01d6000781d0301c01e50140c55040e902440024200f01401035200c003180e44041c080160743c486800d480b01d00f4030302e0f1041800b180720b11200800d2012086841110801c00e001e41e005e44101030700e0050310f0165120071504030a000c0703800c03d039141001070314001d004055080e540c00c00b03881442e400001c150741c0c052418602032086290054100c402002401c50f0a03200ca0b0954940607110340503540c000384195039801c260440500f0344c0d04012408002c1c5803025071100001800d05849207400c4800b00c0e01d001130f40c20f0209072450400c0950000c603a00c1c60003000651116070034401039503c082c090b044071441c902d00d02d0145000401c00070006512990010f10451490000c01064840181185540b83e080c90810f00038294010103807241c41ea0000800f1810314541c8209604000135500720002e61070a114001703000700d0b00041d24070b041d005600141d040d0350b11140c8040725491440b0f22096400e41180020841ca2481080a0280d1181842105800c0303540d0b1b40d2881c0407200c501070004104088041000141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618743785 1250 618742535 618742627
    0x809060a030605030c0306092a06070602071b060c080304020402071b06030614060306061804050a1a03030301060c03050c0c0a030317070f0f030f0b1903020a14010f03050c 75
    0x4045c041d001031445c2d040541c040d40c0c0780d80030b910f007926403682e90348080c9089955203002108220005000031307560300d41504101c400307584210002c0d910107506100c030b00480e154031803000003101d5981e941c803c400400c42c0d035400071b181e1002d841a0780c0243c00384043d030701140c420380e84c2c1d10201e11841900e1900f580f4041002e8241c40c0340d0303480785000c4041d00b0071240c0c540c2c4a05040f80d510200459001e83e4406442440183c24400c29803010703003080c540b40812a80202c0340d40b2400d00341c05088d101c98105080b0100301640c921003406020700203000c100c216070000340950301400c40da40745c8405448034144414085507120f0803c0d80103a001031a4080503509590000440c10380000040c603280c926620f00a0b0041c15000e0700e40c07102c00802d5a940701c20a03284465500800342000000d01c84a05440050201d00060b402400280d1107103c070344800203400c0d100203c490010080603150000002c12404099005040061101215400030051640103452091003c1f001d2551084484419817003c3e9882d040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618745035 1250 618743785 618743803
    0x6070206160201140606071401050c030703060e01030f020d140d0806010e1e060a03020f180910031509030302071b03031107030203071509081f0b150d090809060a03060503 75
    0x19645082c010301018407138091035030751100d03003a02c00326600d902528048074a02c140340740c0400d042d440e0000344815034091200440c02a90b180d9001d0201607129a0350a181800a120051144415044880040c105a10355070090340c0240345107011840c9000e030709030501340381480e1000050101d60801c4055a00050a10748140054a0400303054203080182003640301402d504510400002c205446600d1098049507007401d0252009502c0340319404106c800624440801e40c4102483d80c00034502d44004a23500701145d8120007030b4200d90014003618001400485001e50400d9000c000c01008554200e17a8200a814541074049801d455402c0061408882003510358264105c02c800b00b0240e540018500c05481d00b024060080c1a04040196030b03c40c195404103026018140c6019402111983d10030204e10860905004100c1c1e400104440702001c1040c01e000300e007052200d6002c42c0d4465120404603407040810360b01d0002040001170403900072420320b10010741c4500c414490382c2030a10582030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618746285 1250 618745035 618745037
    0x201090c14090a090203030c011103090f0f06070c150507051810410c0606030316060f0617010605120c0d0b13231c051e07050607020616 60
    0x44800c0404001802e1100181011a00325150703004101035680030300403152242c513048020800201608140d5685810450303107002d89002c0d40e60719014041001c50008030212000015000c00d9a909209440020481200387c410381c3c00e900c01c543c5413000e180300303071401001c15840c0c003500d07400c180c00d81400a01802c01158000c4071041034491905402c10743c0150307501440b00311422014009003c07440002a2400c03005c850a190102529907042880c0007400c1541d10030301034940c40e0341c030300c0141a43d80c491400e816101410001480c40403950903802103040701034402c808030380c0903075822018110280034a964030b60b41c2d42d504010001d604d00461500d103016006405810040b440000086620701c42840141039010f14200007404040d55201c402ca406900c0110041051000b800480c02c04850300d01c110814491144140c0c4104000d0600103541c1402d507840720318041501d512181c0c0b03140c0c12020420450020700c10600004c006110380349c491896036000308003034034280000f08500b6006030b100380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618747535 1250 618746285 618746309
    0x302061b0c1f0c020a02061e07060912260106140d09140c03011103040f020a120b06090106020c0a1a0c070902090405060604030c05100e030a0303050103170a080f07140a0201090c 78
    0x9170040c0c448005039601d1644010100240d001d88950545071131161a40051080f403a00b1004800c10a902c1c401100c07862a5595252004900d400715003845c103005465010010550300c0100320f02d134854010b001c220ba501400c0a03080c1600141041d05440040038101d81c1d201105000d000c209404201c060440003040f00280040340b48000004070354403020b040500311102e50100b400030740d101c51500d44014410000590351800c903508241081010507941c042c4255481000007543c1e610009103a188001c008080c28540c80c986000c111003a42c42664000f10703500d09204100a40c0400c7c005903005010001c1c0169489003110104012600001c00301841080b01384428004036450070742c840700782d80056800d80340b01101d41c141640c086032154242c2e03074140b18032a200c400701a8546c2155040300c2c4144004190042c03404000310b0302c0d02501e41010002900b41002904580e8110380c0941c0044490400c00c1032421001c0f01404580e10100d44080940e44072034200c401c00442054080082c44128016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618748785 1250 618747535 618747553
    0xa2d0f0c0806040e0703080a080603060a0504050c091b0c06102909130204090903030c0206191d0601060f090b04030312090c0e09100e06040302061b0c1f0c02 69
    0x2400c08480030300b80314025590340c142c044081000300b000d00c0242d604039070156161040c1c04402000d881048075014082d0003908007052500b030b41d5000c2d003409254030002400654030480180440301d48000d080c1d008960100d050400303050740d020300508146d82d000002c0c042519010f4113803200030700c540d400b150458680c1c0700526080105000c80250901180b42c11a5881c624035000808180390384c951400c003544001000107035088035501054245100307072070034032001c84c0980d01a13032101012110400b80c00e401c1c00724910800401da2020b100600d40111841d0942c3d07045213454a446003d130000400b080184988001d5150130560380c10082601100c420300c0c0c236003555001805442c4410304004550345030302004c0e00300b10f00031140c88041e0103002d00c0d40d001e40c07a0070807100380c0c0d5006180743c000596140100d5004000c00100c1c0e010f10441e05071300204030f40e4586401e2645000e0381c040d018150700d1814055050000d005012088070011508105018416480c0c1e00b0383c115a48c0100000540d03120400c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618750035 1250 618748785 618748787
    0x9020103060f0305121e0301090e0606090c09121009080c06090a0c030602091c12031103060d0b04052401060f0c1109060303070c0b0315090702030409050a2d0f0c 71
    0x1400d003171014400e9959441d04c0c91908000020001c81c4c0895848000100c001b182ca251a0382c8001145038020080300c1c0c1c0c03900c07000144076200c01d00b80c134040391a050402144030036007003411410028540501c00c0f11b0054010159010464150f2402203d024400103415143e02008014640c0c0040402001d840114260750715500c001e4a5031100400580e00400d400035944c2e284c010713107000c000b030340030b4030820100341d901c1d101d42c0400c0789140c0d070b07000b082c17170110404241d88030310b401d40f40700b250041d08102d81c0b0b408076191003c0d0060010000c0b034991003141c441c072a0201d0b0b1002c1e00318408800a44140c00d550400002038400355030700d40e000d0200100d500000011071071503050107080381419a02c5021503189c0c40082800e40c429894017a000528540001407103a01510017184501d44e076003102010304081c0c00411045400035540c00c0016031040c003007404018030320b600540c0c201580c84030018801108102046400880041620100d40b0a4115441c900868015400700c3d10a4080405c1741c044841c80c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618751285 1250 618750035 618750043
    0x6020d030b04090b0a2f04090905010209060d0504170c10090c170730030833010f020c10110111120405100204050a03030302070501060e0a09020103060f0305 69
    0x10150040644518401c0d00e80c0c0c94942c0203003003c3c1d07000311601d00d20f4541200248060040340800070800030196102c1c1c2d000001c803551204402002e40800c80c074103450700244d80054105100b09480c0355508011040e40382d500d801c010011601c42441c0821140b030304d414107a0390100811100c8658070810007c0c0d00b84980045840d05070909140b41c0000c2040090a0102448038160804c0070030144901202041c0c100000c0c01e0412600384202600000102451500e01d602910703102050301845002d0a900080c0a03561607544502c43c1000174465402d1102c01355421038404d642c40c401d00817900c940d1f40361564480c04001500c48580001e0085c40a00d6000c01c50181000079101c1c104034003040e04402c2c403542900a40300d412244000c4940301d24005409109185051f2421240340c4a111054900d900e0203000351000c0300d900038170101031079103540c4069001c1c0d031025104a625550b2220080364104240e00c820380102c0c1c01400010fa401102d20000d802c4822503003202000802c00201040040d00c001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618752535 1250 618751285 618751303
    0x6010f14040507020a062f07030207030b13020604032409350d0c02100e06011413050405160806060604090c051303030e04050106112116060207020f06040602 69
    0x41d81c0040c107551105400c0307080085110b002070805003018100a6004840e0f10212950011440d030000c40e101c500451400301d204030707000200540c012007000c1011620100280ea1b0007502c03640d1400c0f0b409903984c00218554001d40003141c1101c0e4828441c500303000c406214020303045042000308000c2c400d035100c6400490a2071001c1900358000c000100ca24150184420ba41281e44018141c41d00080c481a0014003101c00a1500500c00c2900309009501c3c02d004104c0e45d2039206d00541b050780d082076410011b0030f0700c040b0110b800c203c480c0c00c15508511036100c3c030307031165000e54080d2180745400f9210581102a6a01c0f8144503442401807001550b90307072040303038103d49011800186e0010700720004c0c0c40f00c0c0144441004012521040001407542154414810302002c8904104c0f07a1b890300001c0d40e881807010f18480075903010260350600160006a407890920011750481c3c01c110442c0008006013103007400459400350017080d04000c504101480d0140c5400896416050505000d4001c0d5604010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618753785 1250 618752535 618752539
    0x10c0f0b0c03312a0e0105040c08130201031109090403020c13060302011b02010e030a050f0c0109060c0b06420a020d0503040c0e070f020705120309091801020406090806010f14 77
    0x8000c03402d0b00228540c0b0343d02107002d201c4c03d80000385585805110808109200715030140b42455124481c00c2d00c40c04215104044040320001c4a54858004600611b018119110592010809103085a1390b488400d84514407a5000b40440090704042c00605442a0650440030b401c0102c14030061380c018800c1c201e183d100e05001041412603000488900d0155640e940d01809032212801c18020b002c559246404c020f901118540c04c50340004603006480d030310620000481c02550200040c11500400388c00c60001048081100c0d8000c601040c000c82404039002c50355050ba03440283c0820a2030300d03003501c40f201000b49040400811000c1c0d1a15925461003042000010005040014004041020b4200c80003010454607184070043c00e2900581d840304050f202d0f00100042c0381c6881101007000b00311003c017641c02e06082d130341800544c000142407204105551114402080320900c09480105810380d9410561481c1038010b50421006030400508804448030501100744ca01c0d000303108440c41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618755035 1250 618753785 618753803
    0xb07031b0f050a03081b07060e0a140a05102304060e0a03081e041e0302030712090e010803030105030a030c030e0a0f051c11010c0f0b0c0331 62
    0x4009262540d4100590000e245504840d0400c092000c00640c20700d000380b20751142c04241d1500e04021844043d40d036510f500c034550401c00080081d0071500b10451070100d110440d8034100303607540d82214030865a2003609c00c83d400050b00c1410711100300000d403000304100c1c4040245400c110b0380d1400940115103000300050001d408242042419442103000d20010010341d25403070f565160050004c6e005030b50340f040c4d00c00100b1032088000e41c0d10310154051680560030703d21206800e02140003c50000d001a402c0d40018405c3d00d000ca20b46081c040c0c81d01d1425aa403407a02030420025180b18901070308400b0055209000600c15903d000480a4116406062a5030be040341d500d02200c2c4082c100348200e400004a01c3e0002c0c001d0b2040c074032141030710421910101d0344801c5983c226640790b41403030058070940101e4101c550950059100c4004030b03000d81050184d4042c03586a4410402d0103489407060508000b040040d00c000d400c0410542030b4020345001d4080c1c049008030300503007800c52000f81c84124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618756285 1250 618755035 618755057
    0x30b030d0f050d06061706010e240c0102040f0905130b15151201090f0c020309060d09050a080d14091005070302091e130606050d150e0c180306010b0703 67
    0x100850950305640000c3c04144002030725000d0041007030412008804280c400a004201d5540c090404c2c0c002c416405404c104e001c0c003520300c1180f2075501c2c801000c400c40004010b0b6a1414500b03000400c003074081c04500700300f5180b0340030090088400080180403207400c0b841c510b070001980b0a08050b00b06110400c3c640e4a6a582030004081c400300b9220504185400a07030b039800c0300c210244141c122002074008000c45109041088280c40c01a010100140c104129a58092900d81c025140144150344009450242c80c1e98451814030b0312403040c0d0300c1c0c12012403004030040c124012070022603d401550320050412401407030390b4815202402980c41e0325500001d03000381c4281d0659201d40e100a100031820b0030b01c00c840880600e80040528020807001e0000040c0724018010300088411603501c2e14070304050441680010640c03e00654849aaa00400039a218040c5400d6000c0c0381d401c15469500d40007800522100c0300d84250a50098001c080100200181041070310307201605414105040c0b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618757535 1250 618756285 618756287
    0xb280b0f190509060d0e06090f07090f0f0e070e06030a0308060d060e010c0e01090905010b040b07060906090303050603060a0606390b090f0f1e010b0a03050319030b030d0f 75
    0x10060848aa800040c00304194000000316044080b1641240c02501c01c2511010782c1c09449d80451100030074540e004100400c80d50300654044002c2500302000000d59840d003071102c00598551801c2a0220307400a0020b100e41051500320765005103045005103040c040301d6501a000000081226101d901c050b008042400240e8002c01c1d046d081c0c0800810440c000c9a501406000100d01c413180040e09070000861010507c4c4581c0341038032081d8402505040c80d058826021380e1102d201140c810351240c0c059000249c1c40d02030820031a11945021a00c1e1500a0a06151407c02401d01040c035040400411490b50006040c24882e607400004000011640b041074620b51600809980c0c802c65030340400d0b007407102600703545000e007000d030f41511980850042240e50f20220303445110700300e800508a500030740340d82c0b2054000007100c81001246c101c480c2000070340d840404e50f00c191610781001a0141d81d85141829510f14250f190908000b4091b03260b0110ba5030380b100305400d8044c0040c2148841c095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618758785 1250 618757535 618757537
    0x3030906050f0904060303050a030b030303090c0f1306091b02210f0903060109091b0b03070807090806070f03060609140409031e0914012d030b280b0f1905 68
    0x24802800034400c0c0c3e1b541e843c00603c1540402170301c00000f031800030015154038004c41164041c404917001018401441d07804c0000e0141c001400d030743e100c00e46030540c5241202e42c1c094000103008030b100c00079100c40314121100c3c0003d1018080030440d000768240ca4031f44003d4507100b41003800c1c0e40105c03c1d00d603c50420092010300c035203046194107214000000440400700d8010008447c8190010703100f4440d10520800350708802c0c020400c2502003440040c03405485a10819030044003441d001c58060354606409007080d60548040c00000c400800c1c003041c464240c0151002002c140c41e20b500c8580c5060001c8038040080103da030310460305c50001700241442032440c090004004441c1c1e10304000344100c0903005004500c9080000746d4103610907100d960240c2540000c80c13001e03031070f0190100500105000c90501e04842e4506051b600d0000c0c0155484500c06080101c1d40403007540110140075900d065101400d45c040380c6001400c0101e00c10340001c44c41920111621401401001d1031198420b40701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618760035 1250 618758785 618758797
    0x304050a030507140d0b0703020c01021605030c0f0c060a0302220608041a060105031303021204150908070f0e130204050c0702041404020109260604050708120403030906050f 76
    0x111000c841008414000301141400455900c1c41c0030082c603402140c14018038011002c0040e01c1c0c420440000351643e402500100052101c80000614010a100320307610001d003074002c00c1c1c030a03031b00c00b01d8481680901040000c0c940c85042006140307200e0148002070706d610034400003604054000c13482ca20f0700c1c5081175600c64120000e1065501107501c441d401002c3c09000c550a8811b45260900010f24003400c0202c40d0045206a4942e443c1d6034414003080020081e01604400b140300ba201c0c0e803030002d0006c4010340040c0103262100c2803842c1a0107c0101041c8564000218035042003000300038082e0044801e1040318941c82da40340b050b642d808082c20b9409101c05001c0e410034200340c1040103000d00e446c001d00186108450030050780e103040c2c41500b100c61040700d0085c08070301c00304030905c0300114070b0007203c00840484450160070141c4640440c24a2810f40e011110b941c07040000740981da4040c81980c1500100780800740c1003519580f002080c0014074450b0a0900400017440180f800d104030440719 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618761285 1250 618760035 618760039
    0x180303142404090c060c20010206061203070c140a0f0f061110020a020a0201090e040c09050a091a060906191809050d02160501050c06061e0d140d0507150e030405 71
    0x1390380380d616200607259988884c0d040300c0480b03c0e19408015003d202c48460322101060380100900c0d552681800842c0c500c1200080582c80140140000030351140907210180c5110ba03c2000000d03046014042070700c0307070340d00904004100502c0900000c141103040c00100d84980c544450b004107140c02e2141031150420080f041107000240c1104ca16070001515040980300303070394146141c1c5d65000f0001240c80242c6005000b007a901100300070307105064010640110201d9000a402c035003550b101c503d880c08010841d201041c105041004074600b07000c00503844401a5580800001c500140b000c00605c00d02802680c08601e00c403142c8500300540c40341e14059448000c50315400e801c0c16006c1e6071007002c0c1d10141c4a01070701803030206e92940305205464685408200400045d04c6540810100d100c01c06c14034001c0c102260507060180c2c0e01c000002d10712600500e107003003400820152407820441050b403901c050000c100420000940122501e82190001d8040024012140c000a03800e500c80d40d40015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618762535 1250 618761285 618761303
    0x17120103080702010923040c1e080609010f05100c03020703240c0e01020d3609180309030b0702070902180901090b030a030f030f18030314240409 64
    0x8001c0008040c01007100900036210051031741d40d034402c1d00c801194448038180700300308600e108000908241e082a0000b2880d81042c06000c4013000c00302070344040c3d045440700003500c41010304c40c080c14446850382c003500c00700c0885911176040401041d52051b149044000b000104c030300f20303c1814420f0020002555111a00c1418132040302061102d2003a0400d140c4001c600e0901515010780c0240340c0540801c1042e000f6281c45c5808803025540360003441070011165014000c2c2594181c0f600c5003480c80195210180043c0f681803038043e0781100e20f81c10340c01b0901950000d2120229420516120403079500072030154241da60264204c2c01c20f140c6900402801d400441ca00140d5840d035021000c0c101d80646003502160f1762007248105446032918010b415801008004012034401d00c501040f0400300d003000f00e00614550f14042c116010a444280908041c1000e9030400d40c1c0740c098803c40345101c9000ca4100d01b01500c1c4c1042c20781c40d21404003916480c0030031a10301c54072035400554049030084608 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618763785 1250 618762535 618762539
    0x80d0c050c13050f0601031a0103020d0b1003021215060f091c120f09030209010e091e0c04060e152101151d09030a08100e07030f0b040e0a171201 64
    0x84003c0d00c03003610b940b90460748501c0040c2040d4440d00c20484408200040d0400c40b40d14000150025400b0445148850780c48880003044c64035009621301006030540e0340140d494417a40301d0380f40040405052240c51102e43c52400c2103503a212410303900c0c0b81461452956580b80d4101c0006e510f954035502c5100f241d00b041a508040c403084070a09100d148594440070890500305100b1503c00d8840d0100035400252080180311120440354490341c8406803008031007000780e01224600390070201450201c0c941e88400d10518160070140140801003020f0382a800701340c103095040e0a200c0d4507041c1240e020f0540c0c014a0700d0100c0d814a03c0c074005103042d200811080841841540e511000350041c20400c5e0941c08110b0441c00d6010000c602c6082c5e5039000d1030915040f40c5044480c0740018081c009141c0307480101040c8480300108050150320701c3c1d05d0000364002e07d149410143d80c84400305911951416803998100c40011810b40d203065030006080c06581d010040c009928042d55180e042d282c130301c2c2400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618765035 1250 618763785 618763819
    0x21803100b150a080a050403030605060d05070e01050304082b0204030b0405011b0518060d020a050d0b0a12021507080a0503071206050a12150c0207050a0b04080d0c050c 74
    0x2000018610603203030390b800901c28410502503403050a1a0100003a480400a51440000c0e800190414070a15010580c256503e00041190708030394031a01219580d00e06000c099034000024086081080c2003c0342140b402c0e845845484c0610341000d84580c020100260398aa0303c040c010240d06941d001c11510b90f92a070900c44060801100d007128598a42481070700c0c07803802c525500707828000c1d690340c06182c42c80f5070400c8601501112031840e08043c0c03c0c80540c023000e800d80050017110b1000d9560030740310314825035050147c17501110340c1c50040c0e491030024810f81c011603040c0310403140c065488422180601852403a903129840f406040d0f4600405e1600203158024001d5005450b11742d04c50b50b1200b170701021801182d50600c18282e21941c1c48504100414104090301006801446080200175441d29001d041c0c4a42a003500c005030800720050000f40741015504000d014031151440c10075007005d44141c0d54025100d544d80a2055406250040007020003001664030806030500b0301340420300d90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618766285 1250 618765035 618765041
    0x3050c0f0f0a06050a18170d0f1a0a321513060302030c1902152505030c09040b030f070f0e060303070b0103021908010e03030a05070908030d02180310 66
    0x3604840360f83c00d00c8089040210140100f00d4059100280c0a4941c82c065640e2082020b00012240800d00180710f1103243c3c0f0070b140f250340c0c0040c5807114042010904510364060011010a41c20f10441d10080e041c801091013013800329a0b440b801c2c2e6035021015055010480d18442d43c3c90441e1300c264205140e84d40c0781a05000352031400c5003840710444881d2209015001e0f400200c0780f0008500b414050400285004030700b200c405800b40c01903402d00c400b50b440d00c0c0300d0504e0480c0c4515482240b0380200e46100300007100ca111024540c680142035051120407818603100b0490220b204a8444060034400d44c1e007800752421802c482011620300365aa0700c03200d1400001031140302c10000d0390750001000e07070501000722175050794449401c5000740c9c01d584c00c110301d994a68190807a80c1d6161131010401c0c4900348100550300441a000315100e00c2e000c00740c20251a0001d0500003080002c1508010f400c10003c19940c5501d504900983c847c60f072008003100044a5002143e41032091001407103525850354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618767535 1250 618766285 618766303
    0x3031e01091404060f0e0f0d1b030210020715050f07020d020a0b0f150d030807080c07030509091801090b01150309020a0e190204091a0619140c07180c090303090303050c0f0f 76
    0x10709c444118055091840040f001c01000c0980035800c100380101d0300c11681d50003011a030384115201e481004100e070f5400700700d400032036060041c007030584140000c441d010004501280d0191005040070341c050340e01c0f801c100801902c44440300311210040f860020700c49241404000c07001d001d600780040c079424000e252003c161554804241028003260025201c40116040180c15454030340c0740042c85001e100601c1d00040c02c52002c80104000400001c8081c0240d00640c2e02515041026505288400940707520200d100800d143c40c00010340016141e08080004851046494401c00e59841c0d01c482d20740080500b0703941e2258800100030410f040346520000700d4003000d02c45813020340b940500b407014500c205800700d09450003a0b46d8898038544a400c1c80340542d442c0c0c144440c2804601c1c0400b900d0814039800c0b004484944440d084400c1101d842041d0482906207000e0710030500d180c60251107440f03140805030030044000754681100f41c040050041014205048450804484140d50344540c041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618768785 1250 618767535 618767537
    0x21090b041a060d02060403080d090602040602070302092208070807020a0e070e01111b1507060501031709061b21042d151103031e01091404060f0e0f0d 66
    0x91004680b19040c0b429072024425400b5190342d160a0464881c00d05603003110948020158481d04820005016400500010301c1036800910000b41180704102030720000611040c1124403a03079002038894168205001c1050300020101d46e02c0c0a1070070940c050b4401c8003401b0f500144074080020b6810442d440306441480b0303c1d0760300340720b2100c04001122340442c803688808042c4c0c45403603d03034610449241d0b107520052004080401d030008405102410f80c000c0389040c1c5107244c2c0e1720010000d100b000e485400b25645503c114610306004000000d441d400307081000c840345001003820760f103880c2040060f40c0e204007100b603605240405c1c4c504281c000781c2c4140101180180c0c034040340c41ca0107101018402c00c2080c4038100346922410408641154103107007894004001800d140c03040040d07014001940580d450b40c903009552440303003408136020801a803015168524082c0018030b4044000f0f6001d40140c0c1c45180401c40304108a01a0080e007164100c03210540111000044c050100003034220700101c82d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618770035 1250 618768785 618768833
    0x903040611012a020a200102010605180c09010306120b01180c02210f03091c0e060304020f03010b041e180302060a0915020a02010e07050603060121090b04 68
    0x50034541c1400c0c0c0c1ca28400c0500d01c202d541018003c4122001c0e00018842d00a10455003442455250042d0341001080e03420b2400d440d08640301d1003564280202c101030300303040d203a2081560030b500c0f2a801c5034100134426040081c01180d030b01504c3e07210340c004800804104c21a80c803039a0850500d4400c081003886000b01e60742550704680c10404003401414803014107a006496401124501c000d0000c0a010b0400c503500010025600240c05a07005140a0781c00741c07004101d40f01440500e8143d41e050040724100b48444400d1220142c1da07080101d0764003070f07410f4a549000c1d0080e03c010034094520382002c1031b405410420700b04041d51851401c1c12241c0b480e03034010700c40160003a54480e0b400e004140080c005800c000000740100220750003a2000d03602c00d113024910710148117460001c0b44c125400074070060351149040d000070801001010054001214180d03d54107120340041c214226441103415019106130810f00c0303d43e02540032005454100c803006000d0f1074940781903403815511007100c81d01121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618771285 1250 618770035 618770057
    0xa0209150d0f0605100804021f0c0c05010201050c030a09140d0201020913090803070809101a03060912030a0b010215040c2402100207051e06220c05121509030406 71
    0x2060f018030001c0b50350241800e01c601840f2070080755440c40050040c0e801142c811601442800794005201d109002070b50703500400180e61410105c0344034241e000d83d046a040109005900c020b00b41181e8002503408000511050240342143c105501110412118041c00e81991308958041d00100340c00c41080341d40c80300340000403241c04216112660043d100c00802d00001e4807103400b031200c0e5030301f2800c8070046a0b45151300740e108800b070758508200c070900e148003401260101d0904206240d04139003040041c0c2030800482a00c942540802450040801d0305da40c22050f640c1d000703004000b0082c4100c9420390303c500d028249a00d0508203842803120b00c210214020105d550b0038240280211b2440e4050425542018040c5001c1d401502080e949402125070524104820701d1180b006406020040c069520b0114102e04000c000200d226165240403580740c070002d050500707028143d6004480160200704442c0c091494080421b10710540072a14406003c0d603250004068402c540f559540d144080c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618772535 1250 618771285 618771311
    0x1e081906030c05100c061506080604140c1608040f0f050901061403060f1c02010201050117190611030a1a011b02040b060c01021303051902090403080a0209150d 70
    0x80c0291001410301e5950030400d1285181ca1107070803075240e20528088044502e140c1340d030400c03900801c00410300741e007000b4130030050790741c104540540c0602d0032070f82007101d410040703260700c107503240107114084c0500000380811401c40d900d6420a0081e4120141a0b1100d4444048034001c100724040d0758295041c9100004140c541205414180ca0640d41c9100301111000071100294201411444e807081c91202d82c81d440b07440e6080c81e914940d030050760303e00324803150303000280c2141c1c0180c00c40c1c90380e038200111000d000c03403000914000140022000303c200c0b40c2e150800c003001301100c00e0b072098851000014048081d000e07410411202d081c03901858900d081e404c0041d04c802c03005a500b25070b48a100500c80b4054a80340d8848241d454000c0c0c6424070702288032007207a00720b0707000d50710040c454440c024041c818031008006401c4403407090040001c000c14281c00040140c40024401000c01492500280e20119103406640d440d1202070b00d02884004440c0350722245411000100c1941890240f10180f90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618773785 1250 618772535 618772541
    0x80708060105060a14031b120a0e0706020d052104050d02010f051b130302031f0e070506090d0f02060a050403030e1014070606030b0406020a0f0f0806040b011e0819 72
    0x100200e81ca44000b00b10388842034003c1c1b60001008907a070b41905158080324049010020166511506409003040c030b8141490000c903402d80d08007100b141d02450f81032000c50780018654562500034141140c441c207800c0c40b4035825102e03501d52030f00b900c2c402e4002d020410800246161985180f43c00030f000000c114401001142c0c030880c0c0b00000031401484282030003115034000e1201c1250f007081c030514562240c01080c50100400100d06c00c005030589040520109486054119914800035000d520f2805001802501411071058070550007800340c03000300318042c0a00c0510b60380c05440d55851750020080981103420074801074021076501c0c1c141c07800e9450907108495002c80702d5152101a0fa50024420495400442e0100e07025580c0c0d5202001003604800744a118510a010160340c030a03107913000034139010b0f581c01c40360705200b41e421000b0003841e000484664003d4054030000740c104181401280d8800301032407410741520348044468819036100040c184120000b220350401a0840d080650403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618775035 1250 618773785 618773797
    0x9041512060b031b011b0201050706060b0406020f01061d0c04080f030a0e040e0d2106080d031b051c0605120604050d11030d050702030403080a05040509150d060e1608070806010506 79
    0x10350a0080344601e150f602c00c100d00c0c087c010b00d440c50800380039958280c100c5115402c002c41d1004d000c5410400280e0401000050101c260000d11120307203480003000b440740e080400002d189072200002104d944284050720011b203081e13800c480c00302080c00640e64a0f60320104050000464800c03000c4490300b440e0040f9212090800000d00030718070308040c100e0301a00700314040245803100b18030f045007400300d41c00780300083c084d8180038003140d80b24900c000d4116022907030308020b08005060302140090f00070080c0c5007900a4400900c0343c03001946142401415281c0141d07920007a5144407142040001407003134441d9200b0f904482c0700c2290501d054070004690002c003405a84104410803010f101034200ca40c00c24000d00480741000d07100d42d038070421500050422400180007080c20411482c06240b856042140c18822030718519103000407600204414001900c0a03494440b52500b4140070415016841c0034070310003480c2552920340c3d140c0c80700320a00c1006140e210b076000119041c0340c4131b021281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618776285 1250 618775035 618775037
    0xa0903022b0305100305061504021905041e06020d03111903020304021e0d021306051507050733171006030608122203051c03180809041512060b031b01 66
    0x14095955504548c0700b0460052039a070015000e00803048056002c626600342e02d500380c2c0783c0c036881c0c034241201c01030b070041c082c140c54001101c6a00b0400c0030300d40100f03c0c146002c0c42480c012174a4503ca181e409103a100e90700c2110140f540c1c480100400380d515a01450145108441c2d19900c008e889072a96880018607005d150b02c02c0105c03452500616144070303401d0301294034600110300c2c6541d5070005141403d03034090303100442070300052030020031400f0710002d00a044442c0c4000c1c0840300e80ca9801c01100f107400d0300c00c0c0c108a00d40805900050003075422880c4220a0712080d04c03180343c2801c0091a00c5910320418010905203007000c1225607011440b940140302605000c1d060031010507880980d100e000000710000d5800780c80c0070020036401e000042104000c001ca20602c400102001812284403243c401610f04625000c02f001401060484402907401c0310041181c01d0b2030345102c0344081c202c0d4818800460025005020070541741c00c4a0b4100b2800c0f01074940a0208241080300348042c518014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618777535 1250 618776285 618776293
    0x10b18010801030215130906030501051f0b03060103091a09010e070803120f060d0f03180b0a08010308030709180516080907090c110f0f0f070305060a0903022b0305100305 75
    0xc0300884000040c5c10000d03450503413002030650b650030510482c5c400d0b800072b8503181d44a908014950650020080105050210700b407075007498041201c00500016240d141090b07284d80c00d40061158442165090058006006c034407801c014040c94002c040d40c600f5605d01c1d001d4810700050300728010081d00d040c800113a0024081d69100c4075030f010781e00741c000d00c0c0700d900200703200100d404240105000005103100e07440e1204e000745c1c1340d607205c004680254040b5145040800c04203255a500440642c1129070240340107441e07840d100740659a419090700300400030a082011000c50b901a5000507000e8000c000d01041e69200701350040329521003c451405090f80900401c216a01540c2d104060038071140c9002151014a08815400c000032500c140140c6d600101c04408959000c0c8089000e42440600070400c2034607564074583c50b04001090303500c00c19581c40410040c14000c5c8107552950130300101c29280b100801404140c04c0c282884032000080c41c1400107101954a00c2801054a80003070081c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618778785 1250 618777535 618777559
    0x307113d140c0a17040f090e011109030a0f051c02070f090902060703050a140d020c060a05091509030705060c03010618050d080d11160b06030109030f0f1106010b180108010302 77
    0xa003084c01d180201540130920030040004c0683e05d070754440001d0042900c1c0441c2803442c110b074080c03d482c5040c5076041c01034410494403802c0c0d90000ba800007600e9000c0001900150281400c60600810403206810030880d1300120605a80c00300708403007034a0403051140e82e01a04d5141250848110395002504014200031000210f40540050421440742d8a840301003d035520802c402503811018a06100c184c0105000b1204441813100503400707070b40000700308003a01d008445203039a4031a2038041041c0640120201e4001c5000f403049421454124088841e90305291001810f254000d1060000040f802c000032141c00521821580451324000c02c800b00c1c2d0708154070798034403652001e170368803011582c0c50b140010f462070014040c09903910380040858818440d42058002440014031035840781c1d01d4182d201c40003030703006040c28000d05090328041c50404100e80044ea8100054058045603204050000400110a5009107007100764009514501d1392120f0040d80d480100303000080d44014054a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618780035 1250 618778785 618778793
    0xe03060a09080714031303060c0806040506090c0a0504170a1e02010507060c300c210b010507080304061524030e0c09040b07110307113d140c0a 63
    0x7030704c0c0030501e41001c3d030f460549000a4001c01c2100c56000321100c0707072100303c00c07151140c1103040c190348000c09171418801032800c0e600207140508002c3c07100f1006c000c00316a529183d4459419240a8610a030000c0c040032240700e00c0643e50220801d0031150b4035402d04400803000070011655101990684031203013450075940d21200a031803045820400c008101001d561201c0800d864102610244494048010036050039a002d555040d40b116050020b039005502c101c0d0300c88035410014004241d4005001d81d480c0c00100c0c0c1030b02c42c20348003505619000c003c1c4000e00650707a21400400168001001700750b070350f0300110340703010f8418004982d02840d07031440c500d00e8501980005a91403074a8040c2c482060384440000c0106800f0784088d142d8103403020401030580e40005a01d040c00c0d10300c0c0c00030341c1814095922041814204869580580034410b080355900395035110f00415100800000602e02c1a4110180701110400700241d0010b605d5540d00d0301c1039621030b800c903596014030303030094143c11640c0d4032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618781285 1250 618780035 618780053
    0x1806180b042006040b121305060717180a02062109010f0605010e1818030a030204090c090b1603091517060a060c02190803190f050a0801120c05100e03060a090807 71
    0x8030b1f010140124051140c001441031010302e200b0b0280341c6032000e0320200c030802072824400c014101304168141402500200030001505400c80d40e04a901540d1601c00500103245000400c02c0c528440e42c00c8411300c9190941074005102502d800c2804003c801c1c0d07620011a6000200d90f482c9803c005041d180c84002580084015400780070048808440343e003600703450740385038042180c0000007a400300d41402403030b82c0342c05855000300d101e141c0303292558240031100310a403149800c002c1d1001c42040085040500661940c1d0080940303100c00d005001c620a0302402c20101d10300c4c80501c1d43d0b28840020030b989070103008281641c4060365030700503030380081d030a100381c40384100c91201c841824140e00003030b400020401880920707041c18410703010044000020b040d041c0110000c0060110500c555140d00381e00c02001811500c82140c04282980c550504041c050704681145411084040704c603030b482600650308413283c000503021100613a9a0b2500c1c2d0044599804008040000030400c54000c255209 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618782535 1250 618781285 618781291
    0x10120f1401050f0402090624090f0a0b0a230412020907090305060604110d0501080706110d1d0f0a0905011a0403051509030412031709011806180b042006040b12 70
    0x2819440c8c13112142d0013080000003a256100c58090800200c029850428500c2c4200308001501d51010300380c10404054140e000f014445410804a6401c00240050800400915007800781340b00d40d8031078a0b00c0113400650301088041e0300030402f01c4046549a4402d1a0b040201e1f50084040e12058849400b0000988644a181d0032600014003010714445506c3c400c3d10b00804001000b011590314202016281800c20051102d03150408607490301440d402c8020f0b8079500c54520400303007143c8084000500d11b6603050640e03e80040519802280c0c5100c1036103d0303410394505c02c000c01308108681d0007a030080c2c403c0e4000100513030400001049454a0240c030b941d0003921984c140c0b400c15803a115103039108101c010081e03002400c4006516050b049180180b45c0041154009000d003010401141c0c07040420f041c002001035546902c449800d003110326030310380750607804008030825080608003101000186c03c05c406004a4406550380760386072610845044800c0c000440b420325081e20200e84101c0001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618783785 1250 618782535 618782539
    0x181f120e0a12030c03060902040f05010e1f0806011103030f06090c07110402070c0e0a02070b0a0b030c0f03071a07050f0a0c060509210a0b01080c03070e10120f1401050f04020906 78
    0x2c6c0740c0030076249a01d00203031015245002c0134010061400f0300050101011292060080d52107487c001201c221400d00030038000d186050100c042d0b01d540740101c41900385d54445c00d41c0d9002c00b2040c4040c04800e08005400b03442c0c225010119030b20391a000c0c1d040340c441e010b0010404c0100e004a405a420690041d001160054240c80600d070341d01c1e091056140030484500140d60340c0080e45904000b407031070025801052a580c10860b10401c003021035a00c079035002e0920b00c05d4400d0512580c2644e0100b201e030010780060485649083d144403010388154201c17282c100c990340185111502d040d0300c0002d141d07d8507034010400e0b1000ca0b140c00c0c030075689980302009c12508550b072103040e03e03c00819042045003ca5a000042000d0809400d00c004440c506800c00030098000c4004608581d600191810036941121401c6000d6250720152100c10f00096014008409081c0d404800b07100c0b8042d1502c0407075005050002d00c41d10304d020914201c4030304035507001551000344041005802e180100319402500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618785035 1250 618783785 618783791
    0x803041703042103030c140301050f0409050f0f06010905043206010b1c0b061e04050a030b0f0717041101020a0f14010c0c0206181f120e0a12030c03 65
    0x114598590700d4641001c2191040f0088481e00782010351610404000301194907002070100401d014440f280e03c018443c00d886800c0030044041140c2c3c0c3c99109907040d07944801141d80740410302199a854a2140b18803000e94005c04000080c1020b09010b258440c3d50712240d14080050042c003041141c610007003e20f84083c0782d110102200c0c5404100c0a8040c060f441c0b21f440e03d9084030003060b0311941c80280d10394034041c10482078141d03a499840030749450307110400d4010110849a60056042c0c000c40d400b0701e40c0304070300407030000a000040c5502401607140c0b1012542542c1c0780041a02c07904410001e060007201400001404180015070701000404144161203a610450711f4810101c2d0301c41a00382c2d50b001000d0a0004a05001d219a28210985060540e6907140c90b0f00000e0060080f000e040030b680f01c1c85202002d00395200c01c003a0450252148400607068020800240169410f4450302001031030580d07261a1b0000000d00640c0e0158030550304403143e85c000108030003405000108105040d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618786285 1250 618785035 618785039
    0xe030403050a061b0c02030601030b0606071e0308071b02010503071e030b010f020a110d02040209090109020c16032102072705060114030a0b0609040f02030a0b03030301080304170304 80
    0xa41030101d51034883c015900452070080e051600300d410748080318260140302510007050011307180030030420304494200c0c0505c1071540e10003010030741034420b000004285000c0613801c0004c3c0d18840e90002c1c00140070346c0d5922016910b050007a20a007901e81440320960301c0c030620b0070780107600c6580210b61140740c038902190f0b1081190744107000c160b80760714008086600d07450041199607100050b4560199280f005200b00e10190300e800408116204d192800341c80101c90b40c13011b40d01c80350116a1440005408051590780d00c540c004005c1d0403649900519010708006018000e040c01001170540e03800c121518401042c40385c143c540c210030514800103500800d0700014402c05451680d84003181994030941c1c002c904ca0a285d0201c0d00300400182c140004031010b002205c4400c01903c0c0e000c0d900403000509141144000351080c0100e011142c1d220781400d468405481c5242c025500880c0c15007021f00c102006201015103d0200740140c1c0102c0c0d005000030420f4089035485150301c2c0446c20b003a07a203015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618787535 1250 618786285 618786293
    0x7050708030403210213181508150109020901140d090c0b07030320030c07030c06050a1b0306030506151f0f111207110102010212013b07030e030403 65
    0x9003046400f54080307041501e045484c15122039640c08a552500003c62402c0881000c1101052050203410700250045241c1c2002c20070990007540726090311603d903c881607a94000d0f0f5600c880c15070400703015805280001601800380d009907035104505071a48520fa1403801c4285015401801030221040d4840e03d01d0004102d00c200102d0107800f141c10b00c1d0350760300d50782e0034040c00340c1c0c00000e1064031442e842e140d845811a06d1500f0f40350400204071b0410355a03602030030203c0e40d0400125014140e54500303814002c141110f0741c8a1501280c503046003400381c54024a042c0c0440300d1038440074203141c0040717000034074190003030044201e078070401018100e00000c0d200ea072112180c080b07000c440101e801d00c2102c440c0b26070846255036040f50182c00609050987d00c04018050046500080c501c0001203003c0d80c2983c002c2d0141c0703100350740400e010022903035a10741d924000c44841d0041d0300b01c852001e10360034016580915094900300f00325440039050b251100700301c1c01400351100806150100f0b01003c4005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618788785 1250 618787535 618787537
    0x20c071a180105071e05060108012901050319060807061e02070506090301110c010b010905030d0207030807060f050703060f050f0d1209230103050f060d030e011107060210140405100507050708 84
    0xb090081b0000c024540c10100d801d821268110f40c007421a1490405c0c1071202c0040052400806400b03180161f1240c4a40305440441e51480d0340045049040ca200070411090005002040b19181c0c3d80700b00c0c00b040b18030106103840700b94908a5005030425881806507003494801000600c01c050000a1418404840180103030071840d000c800ba65141d500c2281c0c0703980e2095506000c3d00c4102c0282c9041c40385507074080d583d01c400740b1004003c00404680c2a003848003950015040000e441d5080c09545449000280205424081c03910050b0908102040710b080050038400320b4400600109101000c5480300c900c04540308600c1c01c10020650380208496201000041c4160002250324211980c01c0001409403580101401042e4480c0d1042100640c0e80c3c420980f14240c2605020f0302019201004840d4144d000c5a14034082c4162034000840c2a400101d444007094110010040d40081c650120041c08040d01d000c2c08507801f00d40300220703108084c2d01580d000046401d2407031804103155905145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618790035 1250 618788785 618788843
    0x904050304181a030d120e0a02180405060c0f070318081203010807060c030c060213082a09010317030a02130b03222a09020c071a18010507 61
    0x121580b503040e03c1c0000d150b004000d10803160101c004e801401c0708014002c11a001c58511000031540340c4c202501340c0001400f0441d40d80b5000b802c1c214503112495102e960a050a940840d07040c0300380301c0040c11091091082c1c071884145001c007580380010030b4404030b61143c00341c1c600c40c440f180c00080010b1000001c01000e21132210608000f81c59600d00340202c0c1c18031031240d0048042c015150800d80010b640956113181250b403003480140c951081101c0882210001c0d0484485c5200380d85114a0145542903401c81000300c2d07414178502c1d6111182408032915081c44001c000c44002c0007098444c815aa02544d440266042d0060401d18040d003543d2410308203500064083c0c0340007041c4580580b04681b1115858010080742c02107090365915001419403541c0c01000c2d0203a00a50001d100311121500c1d801403001c00019174640900b500300580700c01040c0f0030050f10015002e003090500050138141c9951500700715200d6000c46e440401550b0a510204041390300c45001c6580d40d44503007080301c0d00d0300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618791285 1250 618790035 618790079
    0x11205070902191209021302070f020a080102300c0c120403081c050402010c060b031218010f080412030b0111031204030e01140720102102180904050304 67
    0x11410000f0316016201158121145408608111451002d6102c004c07000c585510b0b12000182d6886040c20308070001c4a48200080d441a40c3c4000007a03452415009072600d9400d42030000400c5e410031100001c02e071100d400301840074451100141c908040358018000b9111018141c5204030b0b00d0b03504480311a0300607001150440742c00701e5038014001c841c00112034001034040f03081042e400c00f0340010f048014108801015541c907050413015a44003400f465414043d64400f81d6101d1103201e40042e41113101550140c002401102402c549a20519031030b030145402c0101001225034502007103015181140d5118117100c0c1e608041c00c90140d0410040c000030491745011034803800c051400906003a2b08040e11070400c03103d104110440c1030220100c610041c0e100c03610310504c00a16800315124203461800301c3e03000b03400340264100ca0350020807d104800108141585105106003154228021001c80400314050504000d4135410700c81c01894100d4080c400702d13410207a50301c0c4003c40d0444030315648a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618792535 1250 618791285 618791317
    0x40807120309090212041b080a060209100c030c0f0204060e01330f080907091803080901110412020f100e0f120a0f06180b010e10030209011205070902 66
    0x405140e4024200b9018040c6208154582640c40c5200c05150134060409421b1015090010001c0110381c85618010407511041e24840b4a241c02d14400a4120302d0003240a2800e5042050005214070100a00c990303241c3c441d1072020139651a1948070002c50342c8100d800c04e95403007001c13a00d041004001802811f80000791034100000d00c1240c10b5804901110b20a10341801701c111031080c2d0842c0200d0141030b007626040c1c50135512009202e203440169445028918030b400f848070300114a02480c2500c95000303894030799103612050811401c80302d01c180400748442c010f1005110300e0070600c956a01881c0000c0c00490700e20403403400541010100300301040030030b460514034807190403c40b03514181c0a804640f408264001071404c41d855000c40e10004010307119002d101010800c240d4440b54001032900303d12440300e04030381780003014a02d00303029400c1108040000600c00f5001c0d02c00600a80341e01510b1070409901c2c0060503401003d41a1044403140299440812045268070180085000010f001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618793785 1250 618792535 618792569
    0x80c04050904210809031b0c04151508010b1b010b031501051014040b030601260708060d02030706050d0f1b11030a08072f060f010506071a070302040807 67
    0x1c0f081007000351280000d100150b010881c04c0000802a03c40030342101511803030b503070201c0d607649081642840c03030194414541801900c26402c0e0708580000d8404142481150000c1880706650b403036000d104002e0502070800407060000607100c0640321803207240b0000305080451100090a00b0503100381c4030030300740d51080104164a010303601074114403128200003285581319058903080f80700d00e0092860030080000800d41d281d03c0f5100803080c16285144501502d0900d9411441645055070f00c0342c001844100800d100780340001c4403003101a4001e00a18005180c041c0c143c440e5000301d070510030358507500c0d110004000d8803406050808145100c3c11095000184406031110b00125004401d44e4004e00031030050b15002898190021b40600b0b05504418403a81c8903100c92411000441a007030100d0b04804e0794050003d403040c0201e402e100b05c0c81c03150f070b228000e00800d0701034403001074500c55268407141c40022001011541290071032801500e02501c500c0c000346804a00da01442501d403011f240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618795035 1250 618793785 618793823
    0x16051305222f12060609030c0901060c0b0106030606050d1e020c0a02120a02090f0c090a0303021605010f0203090405040816080d0f0228110609010608071410080c04050904 75
    0x3100303002c01807480c41c06042400350108244900802458030740645400241e0079266942041003402c41c0c0e400426102c055a180e1342d0042440104030310841e82c0354440f0002040b6140240109401e88100b5562a82001d00a100040190140040200742141d003042924400b0031240000c0c0f00c60511000100f00d41d1441d03205026440c100c0c0b80441850750010702c0000c0042c0c1e200b00145800c20000c090b18503107a15442c0c41700c0818440c260104d50300c0030701054000300b0180c000c54885100008509a142d0040e6030b0380042d2011209401680700580040103051010f282c02e9014a03002402a5001402c01c03001d5500d9564613100c1c02e9046d0f0714420041440051864a40a01c40440700c00410a504180d00000c00410300084000030501503080019038450480c403d00d060280c40a070300d02201c2e403034100003650900a01d0345000d010458045c00a01086242c00d8200000c3c9811014100201421504034202c072149005801820280810000007800e50340e1003001a01035401100901c0000a0a8013 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618796285 1250 618795035 618795101
    0x131e11092b08071110080a050907032f100305041515031103011e1e020717090a090204030813140d140f01141605130522 53
    0x41462181e034030081c000d42154018921885076601c403001c00e859507200c0ca4000d43c0e0240c00002560450b440c10019110320b40c0c41603a0901501104030100500e071101c070f10040d141c030400c0c0400f810300c2d581001c031403440c00402294091a8a45a8110f0341138030109000a00b109044010b0000040d4480e01408144070265203008078510191008011000d0480c0d4102c8801c60f07180b00143c110f101c000800102034a0a400c04803941840c5440901c82450f02c001c240002c0602420801c6051030341030000369005400d03c01c0341c8005401c564502400f05581c14004c0341a07001200994000a802c03400040814990010300041c0d44100c50b01510703080e1600010700010301c02d500800c110125050301801d41c0e00c40c1007000b04101c0e0800034a000340f0300e580003d9840e0050000b1081410361034080021a00310f210b040060007410580d075039160f1310703902c002e0450350b034014140c1c140c14074940a0400c006031b00d03004a801052114103951111240300c00d00210084842d14500602150b015201070341148207022 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618797535 1250 618796285 618796309
    0xa0e03030103030221040905090a33091a072c1e01090b18030d02010509060f04050715050304030e120c0f0301060b03160e0306010302131e1109 63
    0x40114250340c5540c900954a8040b0800c0380e8a034115040085024100c040c101d502505403060288840d05001e51507950b100f1280c017090715501303400e0703943c44144151011498442003070401c6006d8280904280f4100038940400119003490210a41e04c0c180d4041c1f228851180d90145c64445940061480d8032981700d1201010030b1070340ca8141c00b0f0311036540e20003566400c415004840445108004401a00e0b03460350741d0402a1034000c00f103580c40c0c110b0b003030344d005490055080c2c0a40e5000c80d40c0e14800d1b400e0b54000e484122860304800009152a1000b0007169440f85c000c20407155803d40d01e09000d18541c1d079404014000450000c1008103041d04501005600c1d8415a07103c007208001c0240c2980395061146218400c1c005540030250507902508202c02078445010381940c3c3e402c049420802900030b0300c0e2043d000c42c84851286c2054907011419034100c0fa0045c00b1410f01911942e068001040c010b034622004040780cbc00700780304118461150309003001c0d0080307215031781e030403041d08001c010311543c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618798785 1250 618797535 618797561
    0x5151507110f0a0b0306031f0e010f05220317131a0f010b161e1b0509010506072a050415140114210a0e0120090307080f060a 55
    0xaa42c000b191294403068045480019540ba142d88800700000e062034802c1e0400d466080e52000d00300003c0c1703455404200c0d8030924600820118a00303401c244181c0c0c8080307803103070100a40c3c820021a42c1c15464040280c281c807925018844401d45ca80c440085841a24007400100e00e0403203040421000180ca0341032280340742c1c245200e5280001412400800502514040c118003040c1800604211042c000c406a840080e45c100414401d941c810042d40050040d81c0140c40300091000380c10b04007501c4c02c1518406804109580e00f0076007800100e0b8400071046942e00e000019000c185156850f00000c0120303d00300082c5818641010081642d8072035919a81e80c0085103010800401e8144044003011380c203080916040e002d5044010300c1d4001c810038a00c4114101440503901c040c6648124030034082c90744100308107281e90b0540343c200d8100116405c0c402c8446141403d10240881c003070b25010030000c00300c1d0f429603151303032809050161880d131001c002d500090074000d00b00143c0c00740391100780031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618800035 1250 618798785 618798799
    0xf06060310270f0506040b061603032d0504020111010c0e0f01050403051b0102011107030203121918050c0d1a09010212040f12020d120515150711 64
    0xc200851a15445188103405100c05401500c0800d1078603890b00c10981500101d007000b00021403180f680140104407003062141d03203424024000b0b440c0800a0341d034007000800e15a865030402c4e59040d002080071740b9400030351006c0745440c81c0706401c804460002d42120300c0d90105240c2481d1001600780300360344884900341e906000c031810456030b01c90b502c144107401c00c6921902030310740a00103072000d10031500042c106004001210018024103150003102c00001c1c3d008010180d0410050b4607076025400c0000c1c0140c10400842c0480f80c5040161500300e901e8140c07000901d418444480111a41c030414115002c0110703400c9814080244140b00b000703807069942940590465555128424154a00c007030003038622808110995030940c180e0f401c180e48110bd40b081400c29003013004030510990011505a2002010320300110310101d40c11402450a0302d803102c1d0352882e0301e0313020b001c0c00d8000c225020b0f140308550080440d0341c0c0c10044058020422a54540da5601402c03c0003502e0900c5d07540c1406420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618801285 1250 618800035 618800041
    0x905010b090a0b1e0d0605010f08070510050d1a1c063b070306110403060f0c050a0f1707090e0106023903160f08240417030c030f060603 60
    0x114075a4511060244c040c0c15144030b078044001503c09100d5500c0540601c4c03070000003040000406042074243e4501c941281e00440d40c4600f000410410b0407a02c4002413410300070241ca00d4020b0b0415504e03c1100401400c486d00f226010440813554a24024941c800c14200da8050065a215004d08071a8606c6c031708040500704600d03242c0d0615022215042c624482c0c0b103420342d00000b88401030103194015024407540e811036141a5041e001400207032030325880e10740e41c10303c4860140f29400381c0342c45503260300381001c40c008000d45855200503440c0050018540c040c8041440c1209103920500f22521010b52070750074450320b5a0011016000303001950703c400049552031a089115850303d4000085141c4040411a51140e000c5404402a0b0b058445c90324903c80a501c4188180159400e02d500c01c00c0c4a5075641000359603800801480fa00310164540140c51311500000c142d501900600e8048110528018141c3e116401150031000440000c8203000c00300d02620001500121708032418ad045003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618802535 1250 618801285 618801289
    0x51b040b03030712110105070806100c050a0803090111121602031201030b040c03150902090a060b0708130b1b10061d0703110c0a06050108030f180609040905010b090a0b 74
    0x4843d01c0c101511600c1c80e00c00c1d4549061080c07140e02164510240288014140240003030004e00090750803e100d200b1070810032078068442c0402400e0305030404020850076015868200081c1c1c40549007003525500c904800861350718240046c4040807034034164040d03914000d0f030041c60856490140c07408640042020032154020360303078020306494011030b081069840b5403a01307520482440c0d10040240c4003d4ac00904140a241d01c01c1d01c5490083d42c002481d655030700300c00011584030340030b050720042081c84100081800407000d0a45c507140c00a00241d40b5480700d048400541191100c9440c600b440103201213072010501042046c1d690601c420b10110381001c10100308105050111004480c048001030002482303500070303038150412110740b55660f0a0014850b9101c5100071403d40383d144c00c040c00080c1c042c0000085501400842d5101400c2034030548250524000e600c00c0c4990100d4244810080c0d9130b2030b071140384500c601c60000040c540780c81501380000c5c410020114151189040c079031170030503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618803785 1250 618802535 618802537
    0xf1003031d011e03020306010801150234030f0501150b030c0903340815161806050c06090109030e0f030106031a271b030f010504051b040b0303 63
    0x800148010400700203444401222a0000102c0414210f43d0038000194000d4140c0e00560140d002031380d07a19074a0387c0703404465503520640d80880340160f11044150001000102074500120b07070500f020907880c1c2c161001080161510303003095803004100000c89042001c02d1140f00d03810b003500c24401040a00d00902400d042c08024204141c0040003e03c41d003066905000d1a08800404000444640109241c121103040b4848049a60b14403801c0702060036003001480044407021081d40400959410250020725103c0202e20340900154040034480380d01110791711006001d1a50700c00b51204c060b0304d000761414002909503852a4507100c0c1040101c0d501c07000380aa400c40c161003803200010900040390040290f5400684100b50001e0f0b080c4154000a091a00401030301004032810040444020b150a03d000c0c10740055600c40184480388484003c024010400010156050700c4100d1071802c2c01d4500444045815800c1789a94800402c84a00e030138100d084140d604111069040c00440c0d03036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618805035 1250 618803785 618803807
    0x15030717011d060102100e0303070e060405030d0e030f1023040203060402092a1306051602040b01050d1a0a0609050325050307090603120302070f060b120d080f100303 73
    0x8401c0c078400c00643c2d16402041964800780c400d090070814a444600000d88070307041900c003031000540283c965151480d10000b0346094420041c042c02c0440c1c982402501c44011100000b5014054911285402d40061060500542c0c0444010409445d0003031442d10202544000800c804000710a10002da24000707866a03129a050b202000c03a621000803400301000d40d4401c01200d50185c0440c04004144400030303104d110b5400e0701d240c6902d900c0f10b00a0310746008100383c0340b840542a1502c04050300d080d0304680114441810100e01c2c003401c0034007034029618000300400740c0c0100d54140b0565170410b4004c2c58001d000c0c500d804007032581044002615000a8011007540c0300c0881030306412003801c02c8104000f00070040031200905da44008086c00b405581c403040d280064001d030758496542c001d00890740d0140c0e0000040c480410306079583c0009101940416810200001c0050f000003000c02c041920000036031900c910602d8100381d031458003030340104040303d103a141d40e4003000029040380100d85 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618806285 1250 618805035 618805079
    0xf1116020108180a03020c091005101202040e01060519080615070507171006090501150c061401120209150d02090c0d020414040f09050304050103090602091503071701 73
    0x41c5680301c4403d540c054101c040321a41450082081d81010542c0000348241207620a59142070705990701c10800c5d204030381c14440c0542046016221001c154492010308481100d4020300605050308d075500916a280260080e001288001070348170b41412960300e02c141d80d4401c92810445c149031540101301513141546038003441034004110b4400f041401d1080f01d000d08640c3d8040c504e0511010049695014071400c2c4803451445c000c1b010840001500801d81600c840345082403094402c240e0888104118070010340d031050b07039a01e02c1e1005840200300e40340208060f0762030002603c0c49004000700d02101401488504500f455000b0441c2c0b9032501102070070f13404076403401481d036034840201550700c00c51365081105840000c3c0825100308405403100d80c42000c0e81c0400c000c03031810040008a516520300903010303078028401003003950f00c80d0b00f241c0740e150700c50030015082c80c00040100302a69441010001342120110400461a0f4440318400a0045002d084c260a51400c0c025160200403000c42c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618807535 1250 618806285 618806297
    0x504090906110a0e0108072d180306060609120c090207030c050109030206150924030307020604090929060405061c0507050f0103020705060a0b0d0f05010f11160201 72
    0x106000a680c00384a1602c0080007065543c0d507444001401e5a01c4040308070f0200341c402c0007064803540b0400402c05445021034500e400380421011110784c03200740e094410100080d1150b01032080301051208030007140b0a11010030781c1800c0c500302a2000810b90804240c20518201ea640441c0c0302ca50440201d507401d100050b554035490400312215420000054019030030703d018841010b45c00541c1a10030070b0810300100141c41d00404002401e88299400041303504660455803078841400300465a0440c001d0803a03180c128650301017101078000e0703409680300550b00c81082c011f0241e0b04503e50702d01d61843c48006081c20301600e0880e02c0d00000b070103160207595110b0000e10561556503801d020040d00c1c150240f21100d8518025a0316520307400350502900c0070752440c02540d4020300950303a0040e032001c060301c5a0b41d58024075030300030264800100e82c04801411a1000309140c0c7d2004500300d401140041600809000c2c2502a00d600003105024982c0810049540c0400100f0144e0fa40783c1c2481d00c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618808785 1250 618807535 618807551
    0x6031e0c020712030c060b010809060f0907080708031201050f061c060b04080d021b0d0b0405210a08090c0d112b0203060957120c01050409 61
    0x1246041803d82141c40a40e01007a00c0c1014140c010f44d40c42e440a100e82d0090003021540c44c0111480c103015a4218000e61221010403030301105c001515034000340301c078112400c1c940e442c0261b40c40c06d0035660010101d60000248106100c0100340e0090240c2015210040360450500c00314245109001e0a4945c030305248008400322a1543c000740c005010b03030807000c0c0c0c4842c1c403030402e00d4640c087d8080b0301c2c02500c0350b1500300d81400a001c400c0605500c000f000d04407190015221035440f01c400a200b22841d00601c5450040842000c031804000350400300603031303199242c4510141004030043c1c000790440d4442c0110a180d5610044107600b41944804156000004a0042004005006040e03026a070302400d1206455128007491100d450089080f030704140c5400c3c11480c1c83d43c50145200e02d0004e01c1d80041a1b02080114080018500ba0841011441c0a0701404003461711041d208501000011309800b00a00d00b0b5408001003080140180500380d51080c0043c142d40704a00c22981d11a0301d130280 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618810035 1250 618808785 618808787
    0xb0f150909070e010612200306060906071401021902060112081b01061e0504110d0b010512040c0e071106070e0d0204240b0a08010b0d0e0115080706031e0c 68
    0x42c41c0c0140701a0031080290350f10383c1d00252481c1c070015220b48010346020700c01054541c041862030b00c001740702903900c0e00c0c5494903401c0c071080d41e024007111038000904100301400603c0c040e031003e8070002d10200040e10f642811080d00e4021010348801421540140014080300009000d000e9440f54892405542e449143c229034101c0320103200502080d501c3c00e040000c1314045010500123605142404a01d50b58484007080111100c4100a540024060214903402000350340b141030f022005040c46030410040103000c00b2880001c0300c048403041e52030141040800461a0104e0700700c1803d050800c446003a5480c1d80d9a00d400c01403201082260040307810505403200c0d030200c0085900900b00740b0040b08a208800c0301044103003004001c154154400013101c900c80000e1710441354460f5070301d0302c1036403034070600e410f45822840c0303241d011582d00da015000c104000d01c10710181601090100c603100c1e1a01184900300b002e258000c074180340c00c020341408036255194034501d03010120b540020344500c040b04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618811285 1250 618810035 618810043
    0x121908040618060606030506060705030f030a0b0a09020702010909020910030b0604090603050309090903040f0e0402130606200c01090e040f06020c06011802040b0405010503131205070b0f150909 85
    0x805080300b40c41d200266414804a6082a07042c2c54541c0c07030921007500d980003441024030a409014219070014000411000545002990000001f000101e0340e0901140055249950b9070710196009a00058020465820001078002080100b0045040800b81c202252034000d07600781e02410540e807004101030036a00d803820b84020380b06200080154503100c3ca801755891b071082c413510384152089030015140510000444003500c50001c6141c00c0117140c00b00c0c007235207000090000c83c2d0000c001d894443c1001224407500c4000c0c443d503600c000030491440380800d80c0d0303452049040210b411803210354a159800020510865604031444902a034503410f003c43c0e20441c44100030b250600004962281c1440090814180d40110f01911800031501c20000d0403482288030f02008094184001c01c00b071360103400590b5000b184d4501512140601c1e68406201c0030580c0203050100e400030a40c030080c0003c074041184c2c48801c8009032860780c00c080c01d04010281113054000d1182d01641c0c0080c20303880041c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618812535 1250 618811285 618811301
    0x40c140702210304051806010203041e0518070e04060521011401031b060c03080112030e0301050f01090608030f04030212150405060106172a04030c12051219080406 72
    0xc440c15648601071103503034a82d441481014810900e0340c14540706c08098005c0d0030b00968058000b1440d00c0d00e0001d4100005404c0c064503103000022a46c0010380d600c0b68035541c200c904041042a0f40761900f8240500850310a9018a000e289001da041c065904c490702c000c424203d5000a04414099030b4903031501404068159181c11030b8400000010809100c0c507040205100e9a042c41c100c0307444500840d0f0300b80300044040c3c0000c03210001001003d40780b1024410a6000e40340480c1e0072031007800440c1c2500e03016250b001d24418004010081501203201e1a0045c094040c051850000c141c2c0c0c0b00241401103000c00b0b4840c04040f00030302c211020420190300361415000d10f51900d4501402c006807100024814a000310354014020380c14242c1d5051581d00c28511000991051070a5601000700c4803901001221a50800c22001c00800c04d0051520020160004140141e500da403400501b00860080c91004a5001340500f030789091100f00c1030007030713159645044106a40c580c1400c4014103207107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618813785 1250 618812535 618812569
    0x603050412351e07020304050904020d061d1c050403020402091c0b071e170907090212010306060f0f0303050c0102040e010905060a060206090703020618032406040c140702 75
    0xd181010100c0100a0a45120f42805002d40100c800e054030b0780312010300200d61840c0103810412080c821494800e0f8502c3e0050b00140035002403092554a260448013503e2030b551041c0888240c501050f2000c000c41d803501d1341040d40946a010100801400324007850000900c40d50b0080340c070880b0342d2120f50340c02003e100003040e0b00e507085000f818a03030340041c8196103600010f020142418481c454000700840040c07803a540b0362241c0036904105031580e0a0150440100c2e0040d400009450b11242c00980100600c038000d02c9550f51540c90b2600c203c951035405180e03a880002d0080100414084800c03045075098204181c0c0c0e8a5405134203802440340303402c00b81c0c0000190b4008038540e07140758019840340c8001c0d541c80207440e40301c2000740e039a070303c04842c1e1008503401410b043c4018104003000e403902180010340b40c661515880d0000c1d0500d1450704991103100e103584550000765101007051900880140c1c1c00300700000300c06800510000f55108500d03c1024002a46ca0440d1941a00304d6100c0e160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618815035 1250 618813785 618813857
    0xd12020c01090f030f05120f251808060906010b18030105191d19050f06090c01080c0c0601051c0b010e0108070504050f06090612030f12010603050412 66
    0x11454040080f03890305105030001802d0400c4404181d0190307040381e0030000032035452159540c46050070300c0c4c60b010042030719600312440643c0041c048070400040484c004070f030301c403011603d1413144e00c00ca6280c615400110303180c1c0328005026007a2400300d1040e066801130141d0560351404c284002c01c041e03111111442d050340c41c19082081c048240400000c101015840c14064840560030302c8034204076050308403800f03820525a800c8ca80745480043c045c002e201c0e009603000c005228810300c0c00c007070044944144c10f07007041400a00c3e940c1e2000313005074421f0382c1290b52410300302281c001c256900014050203010300301c151400a203007050584c12038078859002641105641e110b10641200351740038441d4021620030781601103010314050107200d205100780c0c204003000e0b5581034104050302070082e0015811100ca181c880140e00d40070310046c0441c20044c101760f651006859250054004160710501c101450001403000083e0036507201c0d032007440240340141e4003203980ca81c44158520401c25080c0f142c50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618816285 1250 618815035 618815051
    0xb1c050a05030c030a0f02160e190f0e010b0916140f130614071106090f030a0f0c06030b0f150d020a23092412040f020a050a080d12020c01 61
    0xd0000300174101803c6903625a40c85405071344050303030358207903402c80d0240f0303a10014028461941054181907100086144100070031058000034411204143d5514240c00d44030780c44031613039100174090303044418020b650105040c5001ca104c000d0880610058504101c20012080056107201041c0d03001e1984e1141401d03501d0140e00c3ca80a50200b240c841c0d07401080e07042e500501860805c90070345d407480342c00060006c40640000204280d6910003640c0d103510200c1518490060f0f10100501449a0710840e860380140005081041107041140d05c44020182000007511071502d85144000b0b0805003901c0c8070031034002c9510040218054401505501c40c07012039003100059001700403007403201c065942c3e44000c04007001000350074425520200d8000408801c1406000398006854042d1914201d80e02c1c203001d40d00412024050003550b00340ca100311101038070000d504d000130244008000459182004c3d5184c0a030483d00c4009083ca400c042c0025201c0d811030740d0711150110760300940048000c101c03000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618817535 1250 618816285 618816307
    0x803090a060e0c24040e180105070206240f0103050613110a03060803040501050a1107030501050705180906090c09010c080706050f15030a060e100905030a030f0b1c050a0503 76
    0xc1800100ca0303204000d00c100740c0002c0c81310000000310300c01c540c8908a00d40b0742404410420038070b01508009207404a44004910100c081c0b18140c09207500c0d034050f04103802c0c000201c400f0b0100c48d03890410705000c003c41c4151240e480402e400b030024000e0070007058966900c8001001200119861031351b4a08080a03100341d0440b140c005c16801c0c4c150340301080016100e0403155075a0040d8015075021031001c0050000c41e60150507034240d81c1847d88101e845172030b2a55145800d58000751500c4000c900b0219441450807030350300c040ca500440c26240e00c1d04c14a840c400040d0060030103071201d050302c1000610384806900c54450f01c42c0d010f40000380140c1d500302c0e901d0044024401142c0c0c0144211415020031411446403070500c034004402801440c5103c0715440c0c9000821040e41800032511680d01400201d03645806002d528501810185480f510b40113005070503152115038464031035182407002c0150781d0f2240e05403941c003010210301c3d05a0820518006240030034891000e080d502c030104041040b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618818785 1250 618817535 618817543
    0x91309020d121b110603060307230f0105030601021f0b03070311010801080f03030406020307090e0412020f0102070c14062107180305150603010b060a0801091401030f0803090a060e 79
    0x1080b815a194180034124202500041c00002ca006040c02001c029281e114945000070303541240005041e101c13040d540f01e1030460b620041c449510211040b2800f42c000526200d440800c6210f000c2c00e0542ca5441c00e140003c0d102e0b0b040035154250311000440d4604900d070035501588204401174100d4080e543c070390601c080310514442e281c50008818a0021800c0480030a8107114204510011340c1147c4941d81d0340e802a4000404500401c40044c0000034441003568000707006a0180708202c95403541440003c2c00d20008001c9585182e004002842c0060310020702c030802c0381e85180102c1022903c900024153781702c2c0310f1040060008600b40c5690726118110322600442c080e44440102060701000709021441c1c03844050400e0f005064549905010045220b50110340200009401050000044ca1580182032a42d00150390301006003d1680b05124111100ca2000c61a0005614650328000c0c0e503d08c0c42d030b00a1500d5000702c0826502c14042018000c101c0d413003c410302550704203100c13696403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618820035 1250 618818785 618818813
    0x5090a1b0f210605240301060f0216120308090303060d060f06081614031506100e031f050c040b0f0d02070f0605190e060106030c05071401020a02060c040b091309020d 73
    0x1203a040c0607411700c58007034820003903494440156030307584c00c40c0e1a001c0c09546811140c8038040641c06081d1030300001500c83d9402d140a0f020080c544c0f003ca003000c4c2002007005800032700c641c407254801c04c2840754555442c200303995011b500800215079584414008009441d083d844070200d07209180c4941000f082000600f426542155020080d00d03000404269035041c805600c80c2d224050080406c282c0c0c00c0c4262040c4003954281044021545000082032034048018504c07a10b540a44800048020441c05181e412444010b841400c00d0b003440c0d144036a6200c1c03402100a10400094035051130002e50301a502c0d010707000020030000d02240d08214000c4d210458a103a0741300140450015981202d20a034540c7c2460200104182ea00f40042031340208031040c00c18040c40f105020b40302c00580070313403640d401209002c0009170700c4045440e0043d20701100901050b0b02000c00344010700c12034925800f80c560081040300c078001190381c1c031942c0e82c0090081d00400707900701840e64080700a000761034a00841d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 618821285 1250 618820035 618820039
    0x3009030f1005091219050d1803110c0d0c12050f0607030614031603021329030c06070302060a0c030608030a0e01020c0d0f142505090a1b0f210605 64
    0x900c0342c8801d04d100681c2e01c80c481c005c0307000301641280c9001140c4aa8080c107044c1c501c050000410001108003001c1041c407a1200b207001800b91481c0c1c1a20b81d83c1480764100b49401a103c41901c1d0040e60b541e030107402d44034011401c41c4005802c10009000c001c010301a044c920b094242e60a80c1002c0c28010049c0c071283c000d0030803071105208841028200005c2c42c09010030740c445400c424604543c01c000000010f824812086134981300707502d04401c1e504101c070f01c00c025964004680b20b0280000d00d4101000c2840c103e22500307007030203402c010a402240c010f61012002c000018900100c210580061031300c0c1e006400548408110107040700c0c0c01c402100a0343d03000f6021a8410703000201080080410030000520380061079403d03200084880d4002030401e0501c40965602c01c0e8900c000000d420170000340700c1d00c152003d00080001d42800000f064104003500e500b48031074010496100c820410743e070384030002c100102908201891140b0101d0038031500c199a06004083c4007a80c0328050f0809004040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 618822535 1250 618821285 618821293
    0xb0a0f080304091b020303130302120a0815030f1f18140105010e060a030305090a0302180411030a1e020a05091807090603050706050d060e01030605093009030f100509 73
    0x140004e010325484024040240e0003035246564030750385040c54101c000700c200c080d80300e00d1202d0341d181504840035005840c19650f4030b200601e45100c10700710031a194403c2d24080d40001c2a00d01920703802065070001b841403102c88480c0704034490401c00c001c0c02d0002c24000b200741076014443c200121100083c0e050051003000b400941d8807101e0120300300400b610f4259203c142c0c0e02e801c10000b4050f90103441c080e18002c0800301c206035aa0086460410364090054842041c20204400c01042481600c2d121500382c004004030b040d907694030089900c171240c004000c0b0325100001c80456841442c41409448050181480c2d82404600041ca20203030f529100001d000349103022541d2241d030f1003901c0031290454000c295062610400380c0703c0c1d510141d8130040541c2c841da40031401311541003040b4001c40c401c3e40001001e181428a5508000170344058000050f00c0782510001d140740400c00345448240a403855548100c010000b0b841c2c0120400c0c214031901480031080c002c162564451031040d00d030003083e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 618823785 1250 618822535 618822551
    0x31208042d1506050a050d03050d0608030a020d03050402090f190f0c02070b1c11040f08030315010309110103020a02030c06130c080a170310030203060a06030c080f0307060b0a0f08030409 82
    0x8019510359004945d00310321810303000c00c42840d255904030303066406403c19618002040307180801352032490300b000389075600008204c2c064541c1041440100500d901c0d0400990070550b0006003850009007030308011104000225000b80c036540e0503007142d800300e0710b030800400c03410900103400b0303000c0d21071954050300401d003000504114441c1100c1c030480900650000107581d254402c4000c021130f001c200c1001e041404041155038002a030310000c1d0528000454580ca04225440096404291172904041c10101e2900c005491600d070b058121000f400c005d612000c81131012803450140101c004030900c42e002c00d000001c502c60010684841c010024040074541f0303010b03c01c0e41c859580c1001099240e6503c01d030b400480d0190f000d1500240e8650032964415500e80000f444e007041074842052195582004108001d0302d41184801414800050714400c03400443e070a0712801120300181c0ba00351203048441c621b642d0500740c000a481181d2295251030317201c0788981c1d0703250042c0c00f84848042c90702d400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 618825035 1250 618823785 618823823
    0x60a091401020a1121030a120f020406170631140705040911210a0e0f0a080906070204140108060907030f110109093201031208042d 58
    0x21210003d0b070060722240300b14140a0030300202c102d107040c85100101e8030a0000b4107248041c8010401d81611741e03aa0800a01c41c0904101221460000c8021692040000304005500184880c040440d080c40d000c20301d550707650100301c801c0c1c010030300c00780540c00c0389811105561244954140b008140802001030301c419810080c40300c8001d884002c04130b82c1c248001c101e25a03807900002520744100108500780f0f00d00c03106039802100841c0381c582d1401c50000070020341504a11038070501c088100002c01d20380a00010700c0c1d450300c0d031088007d05841ca000610141c80c0d11901c045032481a8083c104120040c0c6034000c07402c000130301b8095802c0380e01444c80480ca40d001c00044800559400c59a51003401c1c45540d6519841d80007607090f1414805004030015010401e442040850941c900410500b0b80310007004200781d00200d200c0708000140d01005101107a5596560800140341d41008480f035112810100c42c0004034a11240041607480c60b4034588070080114401401e20542011855800306a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 618826285 1250 618825035 618825043
    0x6090914060403091701020405180103030f020c130b0f060a030e070e06090a0222061e050c190507180b0f0907020a02061b160e160903031d060a09140102 67
    0x180140018514080c01e00c580201740c0041404118003c000519195803200032030000e142c51348586000440c4c400041080c950441075500c49040584050a6002c04181c00600c01d803c80d0141c082d0ba041d541d00041800b600c9000340c91180c20310041c00b4a40b03660710103000038060040225456450b00821900207100c03542d80a80e00e0081600031b01403040f030781d114000036000390403120803011041c92640d803000d00703209500c01a501810459031a075103c14041104101032034110102e050810800b001164004200410b8418990b00540940e42440c0e81d40c0c1802803401c081508280c0f141d0705600a01084800b0390340c41050408420340b00c4030b4414480408109c08400100c800b040960054007501d4018913140c00205080100382d006a0441150892514607000c1130040c0c0303111106031030341701f441152400b40010303900c101c0d0010241c458a55030100104010440c0c4001000c1c403008a40e101c40756100707401c8410710082c0103400a920740131403450090074100c80b0703c2a424800d034084a07d4206520100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 618827535 1250 618826285 618826291
    0x60204170a0302030403031202090409060b102109022d0301060b0f121f060c0b060924011205070503190522080d110c01140103120305070e040609091406 67
    0x900135606203807031510180d0b1071076540418400d00c142d080044100030365443c451ba202c444d000f1403000421840e100140005499900d480c80c082c0318144900703080e80307800450600303040340c01801c000c0385118052011641d0882092114600046a046603040c9022500d643e503202900c1100203115403944e03000c8900700e0b481544003603c117000040000200e0b503024a00315a03003040c1e5032200c640207441c11405080000819401800009079140041014041c0e18108190450710884e2050050304081181d039958403003645410000c142445400c0c0c505070302441c4405c0810808850902140c41c1954005103a9802100ca1840212015458540da00c070700c0d1041a01c030345003003480e4141c010034503681440b0b800e9460f04212070a00003085018003a0401e8010302c44049100f6123000c0c3c88044410415003921800d207426025000600300400100d5100e403844510113455003000503050f241d40c0c40844102d42120075650308541170103000a400c840d6a48032104243c011100746d11081030301c854613600d402d800c3e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 618828785 1250 618827535 618827537
    0x100f05010504141f05120f22030507080a0c1a012102040204050604030503130806040b040305070f05062e0806070528050301141f0e03150103060204170a03 68
    0x14401404803240c1015400315403c0001d01107090410343c940000c0e104004598036400140020810324142c581034407029803c1031902422403818680040740d079844000b402c203500a0251281e100305c0905000c0c00442d940e40381c200017042e40c1c4030258640a080d00051410443e42c0c142070b441181c0341039001c0044281a110050082e072046d07602c00580d40c1200c10740c0e0006a901950800000401c1e58980700284011813140014680320b0411641d804e442e00110351000140b600700034200130001d00c0c05805141d115a05050854031241a0b0400c0ea10074145202c00400c24441e003020f01081000400c20840800d095140000019900010150301a0141c0c8142a80b40d0303c4480401d05060061014001ca00c00c02c4c912601046908078004110400a4600d8400f00c4e0f80000188020048203108100c81e22013659036161112612242180300540b91040d002049481d0050410f50b0303400703000c0380c20030805848a14983d5610b074108103000350302510074410380b1202002c944242d03c8001c583d0f4035a00c0d405d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 618830035 1250 618828785 618828787
    0xf05120c0703092c061207090c0305250c110402030f0108010b010306080705100c050d0309021e0f040e0c0a17010e01110a050a020c0a080a0c1a070215041a03100f050105 74
    0x7412808460004d0007803c11603000720000c1c40c1c1000c0007806c00c005402801c03c0075011074194090080902100c4003d005103102007150310344095504c0c0c6000f541009070019261092a0340303042d060a5808160100350a98054000810300040802c04018036050f50001e1000300501c1c1218401941102c8043c490346e01d0541104d0401c10840c601300850240c180c510303050400710b0401541d101070409890780b240501290307642000c1001d5040007401d42c13600080ca032002d400000e6252000808030302110b8440d521035030f140c01000103800001d1001203040e402c0603144c0901941c5815040480507144004403099603e0a006a001801c05018030000d0b101c07114840d03481c0840c800e004484c5680149141d80561203102a03120301c41c2c0b9000b4a8100505030b0354007a140c40740880c60310324003c07044d9900504042080c3c01c01e04101113110b00c02c41d071a042d4103c0764241110309078110000c0c5406141d201d034644441c0c0c640d130902845124030003103224003401440251090703154000821211424000c030b5000502c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 618831285 1250 618830035 618830099
    0xf12180605030a0e06090d09081b0f01120c030218090c040308030703090f030e0102161401051c1a0a120305031302040902090a021306020c0609010f05120c070309 71
    0xc09400119081842c04401040444d0903002d0380e0300d01003082d0740840d0581d000114007809070f42e201c0011000f0340860806001c00e03c0c1500c1e0140c04d1845041c00644c03042d0740070004120f02c0c0c2e00554042c03454424034101400b4054090300050000d403c00010010441d040d54400d00700d9240101d41c0c0340c40307107901881041c00c5c00e04544424540d50001811141496611900c3c40e01040100000c1c203a441d1003a9640305032100008002800c10903120181d040c00403031a40c043c0b1585c0b240a000005c0c40900b8039016483d10f2614041c90300412110110b03410aa243c00c846001da10349904025101c2c01c403c0d221500c419980d41d0802c640088403120290003e0301c00d002241d8021030404030905880e0004201140700d1003580c0010f410501d090722180003085d800034112404604242401c002000b0600141c100d00300c0810201c0c425108040c40c0504211000c0480b010250085062700e000700403030346605400380f80c135001030130301c5070300590301540492035111001a4031030010001881e542031090900401207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 618832535 1250 618831285 618831287
    0x306090b040e070909080f031003170306010e280801050915040302070b0304140d0e040b040606050d020a021e0a0b0121020409020109080d020304090c050c1213030602070f121806 78
    0x200705d00c801240e042400700100160403904070701460085114a031503c1e002451032800d2201e400358000078a00d0000c06000f04051a0303000700d00130105007000d0b204071581156448482000341a1102e41d010007140b0f40e000880c0f900300540c00580b003600c103035080340c041c149071707071100c1403c5042100d00900591040310103000d00c0c5000c8000d160010f100306030b80403070042c9000f1060304007200c01c41d055000800128401f41c0d9440c1500a4902a8800343c904001d101d040072401801e511855a40d002c6558001030041c0c900c920030800a03041000f544028501001c508850503160b04410700269054041e00001088203014043c0a0094100c000c0e010146007243e9403d000c00744c500c24201f40d040c0200a1030000d00c504c1c3c02e103c540409106540a959100e04040c204e200715180c083c44802000010b0220201c1e8450004840806080d00c0104544400080c1d8102c1c424214a030801481c0d1070000c507500c1c00b0000d5040040403032510408000c0203280e031804041f80c0c0800440400d1f40300c0d1035981d1b0100213003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 618833785 1250 618832535 618832541
    0x10509031606060e01062d0507020d020604080a0503031905060d03030f0b091008011d0c1e0316030311060615090a03140d0215060117090f0d0306090b040e0709 70
    0x720b200e00340200e0001c0c1d40303140308182c2c908242e001c000443c3d401d024608400020103a804d107800300c80c040c0a06034001a0100400501841c00e000f400340c640750b60000295620300e001d4400500c0d0880441c1c109012a1402d280c80750029104565941026100e00c000581d403030043c18850300d00509221a654ac10f03031412006480000121040c0c2551a04d403c401d6844203a9010301c6030402510f910308451801c3c5040c4e085401400086040c8105001c1d00703580c82002042c5e070f184401044502e041c60581c1d07410b1603001d04030580061941072180602c00300000c170030801c505086074041e841c1c1d40b1085120469198890301d04440881d40092040c00c0540e803841d01e180a0b05807088060304030780680b03469940d4510811018442d1029503072241250343c103c21340c1008001e607030321181d510300d21850400358000380842d003400100849240b02e000002e841034004101985881104a003254031a02c0921030180040046005495455080401c40300c942d04041c01212600e440420082465074a4105005c0007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 618835035 1250 618833785 618833827
    0x30813031d18071806020115050420070605041101020f06010504200f0c013c02090d030e01110703020a210203030f09011704020d020409230f07060201050903 69
    0x30180803a00041c071803a0402e540680700e280e06803251401240741c280240d41c02d42107544681c04580c146a4050200030720313001c400b001c0300d10588012407000209038440500800e4180b020403a04008103462003440f02c07079004180954001d0580601050b0780c03400480e1034480c2e100c503900c0c0b240e010100402c86410725902008540c0061481801c42c04508a95580c0c16400002c04c9140388201082072002844284181000d5214980d010b01c600003200b9860340c4215030340c0d40341041506448148081950250701110b0f07004a00510301d01c3c940401c1d1802412070780d201d01542e40000c00e20745480c5e544030800216181500d4000740444d40f40d0303150548500400c0c080c1001230803ca07010503016001a24104040d1600014079001c03141c80d91070400004107118003000329208011001001e200150f150091644001a01982c01081c03007550303801c0030060010415250906402d00f40b2441c10001e03804240705040c01020410b58128076983c03001203003641c00644400c1c2180c0c10030013001724507180f801010a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 618836285 1250 618835035 618835039
    0x160b040203071e051206060a120303060510120605010201060501020a14070f0803120f06132003100603060801021201060f0e0423090106080d030207140105040807030813031d 76
    0x41c0a51203c81085103101c88002030700740405020024851031030100d04070110780084d44010621460450000b5540c05410b106200c200e000080900c0141440380d00598003a0030050807648854240101c001c00c2c0c0030340344d840c0b42a41481c0010100382503206001b01c604650059009110324000364494540e98039200003100303031502c203075038000410782d0f20702226000070a80e09000c1c549509110b4040314031050010f20041ca040e409404104055075480000c1801c0c5004080004146104842800400448407100ca4540c017011040020450b4007101504c20b40b202c594060100ca41d80390b14030345c02d0307002c1c02c802e03d942850400014008a8440d500c800650016860710040c007100c0d81d00400c0413611020410309184031080078601e040050902600d404c41803000003084400d15000809440d603e140070194201500011100180051002007408900780c1800820007810303e450500444c0d4480d0034200c2c003103030764040014001c0030b403106140d102a8042e2540401c00c600920341c00000c17420110415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 618837535 1250 618836285 618836293
    0xa081f0e0106032103110f03070201020d410c2b150e1b0f0c0106080f150f01180e0f0607080105040204031e0507030f05150606160b040203 61
    0x46009002d00446000314010f4031625196029038400d49101402c0803e0f41d000d00d4241601a01824040022a8109021003800139229100d0b10b1040780a84580b40500c1000350800001e03030205031400c12800c81c2d002d00311007812210524080341342c080d854410283d48000c0340c0000000e03050840c003001480100000b004e840c018403001183d1408a00c410b5031302410386276441200c0c010310303d0081c1e00c01003d84001040f0413a5482c0590400e0300040d1112146400c400c408506020034842100079625070184801c02406a242c4800c02c1c20f03030b00c03e007120700aa0b01d131090441a40107d102e80380700720b00903020790308000a0340c0c1c24422003141482c502c00741048035540c0d4020201e440346061000e03049110099014048600741420000c0c00c250701a0403c610640c81000104000740e4030f01001e250080041c2c030401d04844960410504101d05544054202521a0b4405040020203e0b031448078001d405410001c54440703206103c001e001e2209400e540c07494240031000491107601d202c6501c148010121 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 618838785 1250 618837535 618837551
    0x1c0804140304030510020c060606030c071518060e060606040312030507181517090d0c050708120433031802041d06161b0501090b070c020f0a081f 64
    0x1031724280400e10030000c80c3c3e5001c902045882020f000042d0054411180b043c00c0d42000d41d00b40101d4400c0d040010043c1e4203400404100d00407507003017042c401c40078071120419085a410300d1000380c690701158240501031078001845a15101d01614292500301c80c1d108015402d800c019401050041c01c90030a0101b00c0410710b980032459009540078013229142c0e4000304004480c003a206401000c8480e00310031040c02000641074000440c00780341c12941c84e2082d020185030900b2810107034140c012042c51300401040d9695031100b0001481194a46400d20071030403440c0100d21000b140f14a18070f4803111001e50508040ca100b60030155940c5a0f052402d0462200c1d5800502110780303090010004014412403400c090005000c040d6000c00c0c1907617181d441074101b42d0014600d20401e05003850784078021071b4400c280038095028844a42c0d10481d02005420003010241200c1c910380d000300c1c461034013503440c0000e50420035540d00c102c0c1c01e44002044c00206814001018038051303211040900e40d18070309 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 618840035 1250 618838785 618838793
    0x40b07080411060a050705011b120b0f0306040302010507140712030b010318030e1c0c06081902040608220302100b040b04051e01081c030b0103020405041a01021c080414030403 77
    0x1003844c0a40c9840360b0740e9603450351030a24251146044e001c42c0b442c050b1040400c3d840d401c56900c400800c0020300009026960100041c050303294510683d41520454041000b010b0701584042e014094035100d05042c0f542d803120035040fa108940c00244050f40d4414a0030394035009030080e10380c52405060115140c45810704500c0d41510031002640058070383c40c04d0420a0074844400d5950740d20034000703020f401115454049108a452060b81c0c01c000400000074025230755500e600c000302c030b801241507644984d1502c00074200401035920607014043c50458503050f140125107514500d5142d0058003003c0d416603281d500030100800d041d90001d884003103462480c0e40380d204091144071445007a68003041301240c5250b800805800111403036200c5107031240e1800f581c0342980800011807601080210034580120068001c541c0217a030001e08052004030201d0000b84941c684210a03421118504660030781d0082181c040881c12010406006c00304020a006041c050107421812040b02d1500d640e03992 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 618841285 1250 618840035 618840037
    0x120c03091e1f0809010c0e0d08091305040c1401020c0918010c11121c02031003020405090a0605060405060f0f061e04030620251502130806040b0708041106 68
    0x980c50941202c4001c0700c0b181507401c000c0603a0450302c400020484484800300280050b450149002e2003414804484230070030a1040c210341030003c024008000280a9554a502901c810b0f00d040f245910102008036100c219030038500f48413003050740202600c014520034400000009001d5010303240581040c0d8584503070034007a1096520705681c0300044524a164818101300c00c103008403410b000304100c8509803520002c60003118028454006a0f2611030101100d40b289241d80020b400c6030900003004509500428901040741c000d06007030055551b03035002c01040310307021294194008000a849155030074516011144010007400052a00704e07a0442d4040741c58080b41c1c800700554001409104001140c0076101c000179200e00c0604183c041c01180c64603038091140200c644128600042407602043d4030f240c1080c0350801b203106009075011643d50065400b80801c08500c103920a4009440c1000040a030b02c0f49802000a0403642c07a03498048404074406482030303403485480e04030a00c03d652150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 618842535 1250 618841285 618841309
    0xa021e010908070e040b070e0d0f110f0603011208090604120201110f150a020d060b0901091a0901050c100e070e0106050a02060103020f04060b1b120c03091e 69
    0x110412429080001055050142c2082d1056080700ea03041200d11454420319811540c4007002c0382c1c031503441c0d943c216a5030f849054555803000c3d1410018003403000702d6002a0f174203030140508150007521182400017005441d0031058000004000402c448009a000c0510480c4500d02041c41c1c0700700f0400061b1683c2041d0081c011250300200d06904660304003040348000030b43c40000d0520000d03441c903000e4071500541d000d150310058100c00240c040c10140c2c120b0360881c0e031050007049050f445d550800d840c0d40020800502049030140c0204d10202071110100e0394081c908103492070b010502d001110107800450743c5a50510034114511905280360140f002841162030050404a2038444070300c0610300107a2010085c032204202c2028000d81c08100d0b01d0540742c05a0300e05010380d0207a400318000b0820341e4003c5803400004510365490014064018009107203582c00c0326000c526101c40d148603841900c021110640c002c01c2170b14201d091940c084007028034000e0400010302c18440100e80c41e04580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 618843785 1250 618842535 618842569
    0x402070803010e090613230a060b030f03120112030311030a05060102060a05070c140f01060b1c020f16080d06031203060608063d05040f050f0117090a02 67
    0x700040c4500e0054012450740510950010a080e04043c220003081520f894809003100051030000000000f9072102030350700032440800c9842c4110316040100091444403a010b00c01c0c01204490b00f0781900000a448110075025400c00703181c1d2901c50304481d001c5a00e44210141030310f0740054144a007a00d405036109480400c0085100d1170300c80002410000000c0484211600d07240a1182555014500101907580092a125488820121186800340880c0d00032035640c01c043c00403500c902580090240d080580b10b02a10000810244a06a0140081e1021000350510003284055094508d0300810380c020100b040c80c080600404c00305135641600140c0d83c0c011440d420340c29030350b8144107500c02015503140c40e1405050800010340c600940307481c074440344030121505400c0616030400700981c601510201c082c001c40e50345070140c0399401501c40c00ca440c60300b220000440d400d1080305200e10710341c1655442c120402e00d407002510804090070201c11407040f04196001a00c500d90742d8103a090340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 618845035 1250 618843785 618843787
    0xf030e10020a0906090605040b1606091e110406060e100e0907090518190903052205011e0c0204020c0f010f0f150e1602120d060e0a020304021806010e04020708 70
    0x1404c10152498406500520400004100400803826114155a5080c010294680e05095581000350291800040190040d038000104904118410181320b18441c421a4000001c03080f0b60100400c40b0214480c900c0031401100d519029031810204003522050141040440d0f42419030100c1c0300c00d0070454210001c1000341d0310a0013289400c4100300d020790390041e07240c0000d00e080640f1441c110000da080122060f19206080109030103501547c00300c2030100031080c08850b0303410083d88002114482c0c203003c15020000080748001501c01c141c00640c1a8a42c8402032806900f840025844020095014052130a1000b44c19900f8003402c50b542d01c1084020840034480c000d1501141d51840f000d1030340303111500302000800c100340500c2d50721008012041c112140f1043c800d80c2001e084203520020608005079a00b018081640241d0030313201c3c540310601840c0e172600c040d40200d10043e04c0c042d51104000301101d1404164100803984103030189400c2c003441c01400d0102c0c041c2c1c0c0210508884480d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 618846285 1250 618845035 618845039
    0x3110705030a090e060616030516170a080609010f05010f17070305010305301305130f0507030c2111161b05060f030702190f061b0f030e10020a09 64
    0x6400c507a0a03040785003111170601c5c1140d007d00f1694210a82240281400345c0400c00d03541c0c9160042c0c041c0003031030300f04414042d01d10000d807035144075a001054100c0411588004904103041c05000c0741d040e120701101000c03080d42408015103040c0d68411a400400403802400306552600d9501036000381901c2c0c0b40800c880d411880c0080c10308204040307a4070010016821001c0751100d05c0d2a048140000c150250780c1d501d180181140e0008a0350080c5400c2a0728110503075000e18070b60701c8034014040c00e00c400c200c2900c0b5400205c064849410800740001e80c001e0504e154100081c540080707a1201e0100021410b9a000a5445640000b200d460640403100010020f1014200940712284d81100c11029441d007410000307100c174041c8909511783d0110220006170150300812543c000141c0e903c00b80320b0000000c0c03401500368082d04100311860350a000c908041c03071000c60721101d01c00307a2546940801c40300c803e004400901c2102d15000c2130303108581d101140d0840328402003e400002da80d030303403030341c3c0b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 618847535 1250 618846285 618846299
    0x90e0a030c1b0e040b250804021c0f1406060a05010813050106140901080f061801090b010311030c030105160309020a0b0d021218070504050c090a140f01020a020d0303110705030a09 79
    0x1802400076000d140c00c240c1e0103182c41041d81001e000d204060400030208d131543d0000c185108140702002e45529021b10a18003407140c21046100d065104d1507240d070504407402c0c0d00b2600c0f054141d410680203d40154240900d600403084154003000d5001140889101501c94a0039210180e2051071400301c0c0c0c10080507141405104c5c240540b0240000340200110030030f0703a680e51000200352080c2078101d20801d610326030003900010490340e00680801801e5840b402c00c9007145c90140c4d1424405d10652802c901d06d800c040c01014071855070900305e03a64901062005034081c090000c012a80f2503151280803603c43d02c510b01030070802d0041c08005071240b90221403008505409099030914990084c80200c941e1400102c0e0001e90300282c402003050b88a40c4000f040600032403401c6503101d810b0f14004140d003071800c141d45444280c00c0b2001e0302000115401a6200c0003107130000b03500400310f06000c0303012034000d402c02c6041d80b81c1d60340138500c0c0c45104c0c0c403100d056400c10a02134002880000007040b41c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 618848785 1250 618847535 618847553
    0x605090301240e04030c050f01050106090e0907050603060a030803090d0e0316090f2a020d0905091609052205060f3025090e0a030c1b0e04 61
    0x1120882c081480740c001c00c911450b065007040c0c411120b60700f0300000004c0406102c0c01516181079030080885107190299009139000c0e0409000b28000541821000528041c841c944c1d030740565030001c041c10020303041505000d0036520061581e50400b0001764000001000e0500841c030035141400908241180c0e9a0024002d0200b803181074400e50080d610001440f4030313010207000b21109610009024266101c40c003024150f120100d00c0755006000d20038a007480f8817196600e290f69142c3c280d035426040d210b019100f184c15030142c240c108044000061014010100c0e001060348203040640c10700c0e69400005d020025040180c43c520b40e1110002c003030740c84003802426003001c8102c60110003040c5185c049202c0025a610060b00c04881c0829013884281001103410b9518480c0b0507a01f10100802c9249002c000017840e41e000a4000c110004400303040303110301c0e8071074000b02019200c60304d8030751002c84030410001800da440540c80b4124610351007004070342c00010480a074844181c4e2a190038400d0107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 618850035 1250 618848785 618848801
    0xa02090c0309061503210307090f060c02060c013306050415050901090503060a0e0c0a0501140c1519050702010c080703110c07080618190201031a0a0605090301 70
    0x400c850a00c1446038804001c5102e5610002c241d0f4101c580c050618002417402481d03801700443c1c94624150183c0072441400194414482c0f61504000301b130381c3d500018066a024428000001d10303e007031020051030240001c0c85064400c41c0040b40c03414811116103820101074a641d90740c0c8541c6900d00c8841c0140d032003c076005007402c4c01c04a0505180100001501c2d24007541d5908125000034040040e030700901d4417001500000d002c8400510300812880e0040281d074030490400e200c2da80800c00f451818060005c1910010317903c00d00b035484045c0d40f101c0580c01c480c1481515004001c2c9280c2c403a010510081e100d01649440c651036852400704c01e07001c43e0b00c0544442d08590510400900860f004841c040d0131407035501d400903d2503032501c42c021250080c0324040c0341c80d00132504001200b440000304e150290030300e2094040444c443d91105565a4405982d508410141c1e0403400003560003580b151441d001c40c9601d0400801000c8002041c590864015801040c0c000c00c40d01307120708007440f4500c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 618851285 1250 618850035 618850051
    0x80d1205010b040302041107172224200109060c170115050409050a0603050c0108101806080307052d060f06040b06030f1501080403120509011d0a0209 66
    0x31a650400300190020300c03d0b4080a4002c030307150800c11030101d9420302107a0100d5000800003141c000070259231a01940304007150800d1a8448032030900420510580400b11488100c04800701c4164031000c400b118000695a01405952254070701001c6001d144209004200e400000704e1480d24039140703080b5881d414003d400c1051002c034804041ca2242045411360316220b030741c14488110694200c0b6180305c1d81d00b00112a508110902120a501cad801050a89100f5003d442000c00aa001150f80040c11038050f609404414810401d0003141e800c0e50703c1651010202040a80d180c03a072062860788a2203048030158400d612500c400044440c0100c2454006490444911002400700c0c1da503035005061144c10400340720103c2c5050fa00c507880424543c3c030103400c2d03a40300d1070814040212078004407603a49141400d40e003440083d61051203054451075168503090480c1310141d04030b200404000300001041e43d6501043d42c1004d1084500d9800c03224110003d08000540b0700c140324020f103002e05480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 618852535 1250 618851285 618851291
    0x4050108010e06102d0503060901060c08030a0228170c0a02071701060909140708060f150d0203011514040b0a0506180406060509270c07060e0304080d12 67
    0xc2040c3da00c0603070072090400c01e4a41781911410241c2c09440618602844560041154510711001e13034015001e5485110700b00c400910982e80c1e0081501e120103400c40040203d402040007074607003c1598080c1c1100400e0400c60b2001001038140f0b101880355500f041c801113400c03d14146000c100408483c1c0d4070400d0211514104486400c010355500c0f114003c200442c1c10201d03548446d81800d501c503000801101d00140850281810424065071038010411201e0044200100d80c805000034094026a07840e80d031103500c0c2e039032000000341d808029908540d001c076035003484601580e030902916904500c6080d02c05c03200ea2a10f41e500054401d07042c145030166042c5680502c00d550350000ca00c0c211481500c182e542ca1450301800080030500d403003500e40c0280307010780105000d035000d00a000484001c2c0c2d00b81d001c031030720b030a031070201400c8a13496441141050000940ca068610010344941d511400c0045002d40303400d4038407420b40d001504000800d50101072115041070b031148204001c0c1d0f00c8103e0070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 618853785 1250 618852535 618852541
    0x4080f390f1b15190e0a08030a0c14030c010c030b0a080c0d060b0d05030a0e0f010305040b06040b0105070f0f1a0f01091802060c010f0b041112060117090304050108010e 74
    0x303500429000300766446040c07010070407101003c1d044200c91030424840b0300d07800300c100c140d00090805010411101e00805240c2c4020030000400021071b0440701a41d01c601c10900860b81d204c4441942400c0e06040740d0005000811580400f401600310f030407030307d840124400078544e0611a040070203174041c1e0807541c00480c00c4411070710b848150a4440d07800c03003008601802c000c0041f40c115840000020080e00c40007801000341544107440e0244030f0403c0340ca8480d0860444011030580342d050790050049040034000c12028903007603004501d294170604040f400c180da55241c8120707083c5400701c16240305085813001c07003c0088000d0340d03580c503441246c01c0207502d082550400402203014001c003010180c0c0c3d040340242035030710070880f1000503034000d0000390f54075581221700e170103071001c40080c140c00d85c00c2122081451a1900a440d102c5040b2000c50741401400980585400700142c0014140240c40c442020b41100785005a4441d2558900843d0303120300c0e140004041c440141d02103450240c8001c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 618855035 1250 618853785 618853813
    0x1e0501080f04020103140a05040b280e120c0f060a05040f1e020904120207080f0d031a1c0b060301050f070c17041205070b0304080f390f 60
    0x256600502a040740141030380c2c5620060b0f0040c04a00e03c0b20441480075070030403100c5100360304407610585c0f040b04050095220802840321100c1a040c1d070322150703000344407400015000e07640064203000824045485542c041030040c54198010703000500c0b50342042d40e90002003c410002c3d99000b0700c400d03404001c1490640c4440c02401e81d0044014031078036440062920311050308001c00c5a80360010407000d40da081030300d0030b60b900c680d02000f15005400b414400003a03024010078104174a40401016110322950000100e000b4030003032001c11200c034803080c074400c1c5c5615180d1311079014001560508860140600b84a0080310f40200018441c0e8140000c0019420a50031f1007504440d907400c1c01c04004520380361000d440900d40070a800074405c042800182e00c0d4051020301d0005000e401503441d0389448002046a51008940103813003170728200622410034005d41d005025042503d0b48010403021920b00721082000040304454404000303103e50014400d05001081c04a2040c0c0c004014080c01001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 618856285 1250 618855035 618855047
    0x90603040206031009020a0503061e0a06030b0d1e0c0f050a06050309031207031d01050411010c0213050c0310080c0102150613050c0d0606050c1207030c02030114011e0501 75
    0xc024010540440415501c4144540f407001401e1005400d43d205c1513881c0700107140e0f41084415500c075001c24030b84c06c0e502440c254a8240d40c550013400c403032201402d08a064014044410001d60402018001000400c070341c014003a65041145464440740000c9081c07525007664240c120402c802c0c00081c00b0032003542d03290707640c0c02100c1300c50030600e403a070752002440741c15802045031031010300e01040d040148090345640000c0c0c85040301d00d0b0702d1001111261689080b00d404440080c50b150120b0701c640403946c0031302d11083c60345100410741e28400210b0309480040d541d0034ac5640d2440e11000c400d10103924a002d03100d030060508080103046088000f00003d40e110008040901c0001c400c46c04510140c6801c20365105502800f2014003943c2040d02020b211544840c1d940d82200e882c00d4804500144254200c5000314074000091803c000d84518150302070b4024003048041c40400811030006803000c0c010701940c030a0005000721158034060303601c400e03c070840303e880302c00d00c81d8003c081c80a607030441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 618857535 1250 618856285 618856291
    0xb0a06051c0312060e130c060c05030417030c070e0708250e0f27090c0d031b17210c070803060f030109050d030f1a0910150c050111090603 61
    0x3ca000400a60201d201000500700c0d42c0051201030407950030460501c03840c0703074200105441425100700090769054100c400000c0d001c4000c0084c1c000300030400624204450309200c200d001d07400d4a103851a61541c0e42d10f4086984d02c4818450f1b92101049501600840d00940c480c82402244620302100b17000d04510000f469803107014000e04206171542526503075201c4c4400c41024100304040c2107662403001d80001207145840464078480c00160401c400171540094000024240d80410009564240ca06e034107102c000010703800742d21003003401117100001000050303281d01e8842030741e40da1400c240c0481c80c260107035589940400481445942c108010480e25201c1d0400c9440e41c403612071100141070f40091009040e4150700700f0900d1028440c2c045040d03c202c4801d80c900708000c11508003000161003940312107868143d05401c03030400c6405c00710070b820b0b480b0340226001240359880e101100b181c210022401d000096036a4001401c21100340300303204d07120350f2043c0d003903040060303800000b01c0600c401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 618858785 1250 618857535 618857537
    0x50906040515280e0f0a02090a060b12130803040606060f02070b0a0e030a1b0e13030e0904080c06151e030601051005040f0b0d0b01110a0303020a020c0a030b0a06051c03 74
    0x1c80c14048268000d54802180d44c0e034444180c03255140305154144d6160f400d04402d900c1112500042491444103100d0281210140401c4606141c68454100004034005080e460201e2041140301c1c00604010700452090740b1880d00040e40da410850005c060070205001c51081d9480b221080c000c01c2500c00c150b0b02031101c1407806809051f820790200f4200000c440c030003481001480b12624540141e10102415121000c000445e20323640c02d008940480390b008405008141031041c90111400c2c01460260302c10b00503007415140c10208008286041c104807001449405140c0e5545410b140000101d10305500b08404080e604100c0b00000c0e44540041c861a0b2080c045294ac502c2094000d0090303400410000c180200740b90780d90040c1401941c0800d08281c0d0b4a49060290130680d03004004920701d040050b0b0040051408940d4184c00a6110b11500c03001e51245003004100340c1d60b4101044095486114094880e0030490321100c03e844858200f10f12800a40c0c21a4148205103400c0103409a01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 618860035 1250 618858785 618858841
    0x402090f090903070f06020405100512070e060403050d020a23121b0304060c02030c0d0b04030c0c0801020a26010302010203071203110d09020307050102030a0e130e01050906040515 79
    0x412120b946940300300d844c004c0c448803d42407050144442903014108980040d9080c071001c2601d01c4d8100d44034800c00d13091441c500051000b2034050740c8500425510301c40054401c601d016104d485162030900c644000d50010703480386045504110b100901c0e82500751190b2500d4443c0590b101c08540c490041640d0010450004108480d130400e821010428050144058a41d1951180c0b0020107840301004280c2c0203101d600c3c000c503e50304110542e0071f141c035000300e58803400c5d880d1560110364a807085102034641240303100010400980c2032005012071031a9803a2142449100c0006442412041fa1101045000c802c01007001d40d030080704684a4940c4403827482d00400b00742d030b000e40041c020007a07408000000451203100c446040e034031108055000b1000c5644095603180120396a01c545003c110001e60703500c0c400b52860038100b101d10900303c20306401203004142c20f00a1421100304544800895004c070082c003062001c10b118031052505443d84482d02440c0034032070001e4800c240c00d05000c140780 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 618861285 1250 618860035 618860041
    0x70c080a050d09180515090708150102150705130302041104061106010b0a05030a02041d01171f1e09030305040c0b070803070e01020f15072c09070504031b0905060402090f09 76
    0x81503000d1300c04004000f4400b0b4040d040c01d803c02027a2280407034401d040212040701100030740d0b000003020704105090581b80c15542d6a518011102c0d50044110100080d582040110040e80c0b039000342c08810b403880181c81c1d1a40e181a00003004818190b06031803d54000100500c003040300d86c02100d402d1191402e140eaa0f81d240c8245c00030080c440c40c0d1000c000300103030201c03110340f040e0000c52990484201d91354100c200320780d47d41019150844025031a8500d08000d40340d44134101190414504060516091000a0103200421083d618115030480010b46d4800400c01040307220074600d0b020b000c84049580c2014070b0741c0e44000c41440301501c40c41c18001c010b81031000b00e038400c006a06400038440280c540100220031032009601c810759180020401c0390684500000c0710403882401e0320103814004034401e4190703080c03000890000c0d0100e0200102040040007103050480c008035410855098241801d142c2140c1e4005c4603805082d080c862801049541306507641c200c2c110410b40c5048450000d00d072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 618862535 1250 618861285 618861301
    0x10f0c0b131a010f060e18061c080f03160807050703050d0603050a150e0c0603060d0318060513052d24040509010f08060f090102070c080a050d091805 66
    0x46082c0031424041c241d450000319190341e615522034111281a2648010700c4000002c00c03491a40d00d8002d051780400b03d5000458510f42404c0d03000a140050181e1040c03100a91a140040d034031032016540710200010500503108022400c5101146c481c0ca131000d410708007080010420f2082c02e1029080110208180c10702441580c001c60013154003c0443d00748004a162444407030b442c1c1d000c107080c000d2030022440c1e624580883c5601d0306000c02444945159503c508014104441440560400402e40c000c403940280001c00b4a01070009a180c40380c0b25004200d002401031040e070000307805800740702500b5482072120103144800041e60401e2840c044a03e00c007140000da50003440640124030b0b075260000340c0c101640104241e540941d2a010307140e0703c0b201c840e1800621885071080390f0b8840350008202100001e0015000310810002500d060b0039a250440024000c0e00f0400464105256980c104803041019040d0141c10381400e46480b807403c1180d001c1081e0240500400a40319000607c0c3d078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 618863785 1250 618862535 618862553
    0x3060602120901090504090323030907170316030c0501050108030f0319150902040509010f140d06090b040c081b060a030b06041221030b0603041103101406010f0c0b13 73
    0x40c09015108021769110f03410011316810401f14007050480a015081c40050427210441f81300d11811001880e002c0d10303100c07907e0380d60704031060b07286018082840300341e8040c60a800d20403000c0c0e0190351500859270903070415508480041c1d010b0f0f1015441084200421092101034a07480790b501041c1c02d4452808400e0000640340700038400e86050312130301c00032980e507040303074080c105541094442d0320207030b1b88401503140d18101c540240c0904070f0440d15214001c0c0f606d0700040078007600c1001c01140b45a40d90381d03a910003480944040716172101c43c610520094000304002a03c144034001000340941c03443c80412400d00c52030702c0d180109501c1d00b98078001902c3e1081110000e21122a103020b0481d8607003002d0404c280c1c401c0f00798210300c480c1504014401e01c01d0140300d104000003480e051450b1150754810701c807058182c0c1c1e847e400d4010203080500c8218203201e84000201007960701d603070f80d1030650001440903004c01c64400034010000c3c5080045407500c0c0300d090344426600c0200c5410000f5040c01514 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 618865035 1250 618863785 618863789
    0x12060f0302120a1b0602120c12090d05101a0301050f010902031b03040c090b0a140603180a11040c050c150703020712020706020111070b070c03030e01060f030c060306060212090109 79
    0x80c1d4a60a0540d843c0780000101c1c02c4034172540c203860031020442420b03e424481e0744803100b01d03984250b1a103203108460000800d03440d80020030758111110150703503090078181c114440c03029069031102d03c1c0f5041d0306c0c08940381d0318550044008005524203540c416440301c1041c001c020400f81d020000076054014035000303070381d075400e58190306d612440c0c13a1138580004995405100034507170405004d1100f9045c00031030311080c0c80441c0300d1000c081444ae018004a500300400060100c0410103042d9203044041c80004d000601030074403114910503803c03d000030307102800702d1001000010480064281030100340c0e400c4c098183c0f0781400f1540c43c0c0c04030840203030141c0d182c054240380705922508841a0009101021184580c000f0321941070790800403142409613500c0a800480014002000248181104004940300b41000a804100010039900316401034000d500c0c107040b403020600a01403a081d080b8020036041c41c0501c142400c00400070740710303a4800c2c000d5096060100711910315038060441140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 618866285 1250 618865035 618865043
    0x70f05101d1e012904110903060c0a14180406050109080309011107170d0210061203050313060501080a1e21020a061521020a180e030c0105010612060f0302120a 70
    0x1300c0b40c6603070b8100c0540c2803005400d20b00c2949000c1c034035021920704100750381014a0040140c00d041d61281c1c025130a9901256030041040130f0f00100340d241c3ca1280e00034000f0901d0703c000f04c86039910000c0038081141c046410135410b101c07400404000b1040004100d9880b4142843c1002e121200610400c1c030b003c495070407132440c0008210007500040b034001400c031407a450503421201e0412034051a9011514030f0301440d001480d40c4600328000c207000f140115005403922100c41210310443d07c0740003c0b0740c001e030404c0c40707690841c06540080c08103004203001d164550980c001704240c01969044040d184401d02480c202c0501d844443c0218028418034198503000002400f82c2d182d0b0032512130740c040d171500071034001c0402084074801c4056003017901c0200581c007030f11481d985414007200c0080c1c80010600185107588980d9900f181090600c09014254110000440e0175410303c0c9016001174204026001400e14100e010400c0e101912804403c890701560410304007006885603a0070103d1000000d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 618867535 1250 618866285 618866321
    0x60c01090302030702031e03070f30030f05132405040606091a1810240807080f04020609041d0f0d0c05060a020f070f05101d1e01 57
    0x301410340120080a445108800f41d548101c82c080411119040310000c0f40c0544d4018031142001507040040307018441e00502c11200c20003400403031704d00351a5244058241500c2c0e9a10326905990309030051b01c0d10034502802c2404031b0302e030818000d4200d0003440030141010700240360640310400742c04070054500b160002d02380140e103000d00b404805030209125900c000f40c0351403841c024520a107842c5a00040340184000032240502c0c40c0d0261400740a0310304103e4050300709000511141d030b01040716800c15070200120b0849160301c4007400411008052105001d0b00b0800c008405420303042e00c0e86c1c072543c110b03a841c0e1103042c440d0125001740900d5a8203121801c680380c400d8105403001902d200310103110000c9800c0508140011182c001c035850b4018655482180891100a130395005001099015a41d0a00b01400d40e25160341040c241407090b07601c0d0704032807244107915413039000358100043c03030301a61100c0030041d0741d005a0365040c1c031804801358601301000502542e0f00b904143c4181c1403100d105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 618868785 1250 618867535 618867551
    0x18060c0a08040305070e190f060b0c010917090303070b0c0708040e16050f2a031306080c1303030507030905040c090e060d0b070f0c08040b07020f150a0e060c01 70
    0x40c0303400354090f0005607900d100f00342c3d0004840c10207114003403182099209003100c2c601008250005400c8a02c0c1c800b480b13544490012901640b018040e101c850f0109001240780710b0141803d035420314100c5034280081000304580305e642e841c00400c450034aa0301480044042e510300601104038061004010540207000900050030500c90034414010408070b81415190b003907801d0156998452103007070a03a01e01042c441215092a407982240c00200034481342c51103017414941040c01e42c1d2003041c56000301401c0070740c00e2000550085800d036121544140d106d140608080e01c3ca080e90384035100007000c10400280070800c140c49a00d8100c01458091301c1800600c1c49000090200c03440e034007480c1d80a030340b2000003078424a00115180c40c01a040f0342c010301d2035105d00000300c1c0d038440501c0b40e02c030a101108081400040b4983c00500003412154401510f902052040241c140003540441d4810f40d501c0c2015001980d100084504c000a2802c054274080300000115100d4050880b1414880d440d2040b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 618870035 1250 618868785 618868793
    0x110415030209030307120833030c09131b0302091b0d060b0a02010b010801030c0608071715090105012c0301061e0311061c090201091518080309010518060c0a 69
    0x946e554405503450b070440301d694828007a00c240549a408035282645400550103117001c5d80140c0081c12005401e0303400c6140f4180100c0d5aa27001955880055000d03840c2000c24801500041d0b9401a42c0b031414640d140d00d546c002498011010302104a54440428070411302c3c03190504603962008445000c2c07007102e50b14081581c5a4004c1c8074150302550038540e01c024036610400c1c0d8581601d80c00740c40703004a1414448214dc504800504040074080c4000350080d500d14081c1d15540b254040090340c6100707440030320a0001040e01a40f00c00d05224801c8444004600d850061410000f081d05403480b000b032015000138050142c0d41c0c031a040b005820803680120904110b915019a402940c160903403001410a0102510400c90704c40801c00c68002d80746559045e83c2c02440080e4014174000381c5150b1651419452020a04094000b1464000c500b03481c05081d503001c5001481c401e4040c40c00c01d09240e0001e00b542c41070a4075090000c1c178100d5000841e03544c10301a106145180d10844104c1c0000d498 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 618871285 1250 618870035 618870053
    0x10e0105060307083d170d050f030c160c141e040905070f240f0912110a121202010606270312020703110301060308090d14060702100609110415030209030307 69
    0x46c81c0000854001381c11542c00c000800e400100080d0781d03240c0c503140c2c4529103440c41d0380002c3c01c80212820f0401c01c1c020f11009e00e0660422182c013410141c0d03244c901d040020304185100d1500640503107c04800d504008805078526481c4071800d9901181035201440c109060103a241c01411941581078000f081c41142d1040e160400710b8039101e50017031001003101c207881021039182c40d200010840c540500c01d6003114510703280380c18403810101e2240d080c4000043d0102e10325070042181c4d0180165240e040c003480f07040e0400d0103013460008018541c104003008114105403100c070110107807102c240c00c3d07911072110090001180c1001480400c051510402500d5101e188415540701001040c41c88852a042c031034001260740c0301c40c0140c54954a0340c140040a600c2400581c0d0b44031a804042d02c46660901409110f17140d00c2d4043c00030030a03c00c0042d400c84949400480d1400e00d000c900b101c0303a44041045400352100400034180c103122901044003c1d103d09003c16400d8040400c0110802003840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 618872535 1250 618871285 618871289
    0x30f020a0f0206100521072720190c02061305102105090109020901032f060403060b0d1208040c091806230f010e0105060307083d 57
    0x1500303031415a1600a03580758501039030b004695108036a01025150a4504c0e41108515111b0b4016510800e5445007402031524000c40080c0440110191101342c10300640710302c02c540d402c440520040680c1d080c4220140b07024184074078800100c00d080048c9001c0c09202000005580182000d0f075a805006000f0b0049440340709840c010f440c2c0040c241c480c94094002d91070b00c1c1d0700300800d001c0004070380381682c0050900a4240084c0f95610903e002c0176803180c0d61820701840c002d42c007482d03100d0225210404151081d0800701100d0307031034a00b001070580d00d6030704860840e40c20110120b0700000c00390000c1c042100a50b002071000410300b43c0c0850454001000b14800c0d4081c1c020341c40e9403961050450705175080510280040c07180c10041100180607540314020001b048010965203c2c400c01121980d0350f001d50709820307400e8010004200005000000c0340c054881604d88500714240001c0c0600b0b007200141076081484458420401130303c10194130401c5010440a112102d101402903188a110143c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 618873785 1250 618872535 618872537
    0x8070e060c030c01141e04150504060b03160806010302130617010e1902010c1b08100605041b05030c0d0b090403110c15070201030203091002030405240f010302060a030f020a0f 77
    0x11032030048000784290568414000d4000c030031074101c402c1320601ba6072240148219a01c103202c02d4035840c0030103540300b4248503e11030800001d00703485803401c140c9001503103034030300d29048003000327052061000c04520581100c1d4151070800d00c0d40304425008028180c0c03600100080d210340302c3c2c605004c03281504003c0c44200224103542ca0f000d60104002c21040207494040d0101c0c652a011400051235a4104158031441803104202c90b80c5910b68107003800700c04142c1006090f1202d109010500d41071143c41e03409900e1101380c510440507244090a280401020340c00108404a0f50345d103c41000c1e0095440c503840105185058039041c5000b904c1105000103040c282d104501000000341426240008004400d0031614240000d541c011006540000c10111480c0120035144e4100c03c407030f00186004911550103030441001241c01c2c41e10035080b01c19050216444801030101c0300c2281600345041d641c040d07030404d940c0c10509800381e02501c0e1481900710307001d20004509110300d81c4010485e00b92101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 618875035 1250 618873785 618873791
    0x21e120c0d09050a050913050f01051509091c0c030216030606140901061d3d02060c040501110118261806131508011805090c0108070e060c030c01 64
    0x443d0305209424040b4000c050b00031003100c011585612464903c844004d100da4112360b10186411070441c2920020f81d5002811001504201d0451811090703ca03407207038061000300500e403450310b01d8641c0e074001d1400ba0000c1c0200080110107141c42444120880c40c22130424000760303a80c3e490702000508983c0326031007030b1203551000e680c0c1c0c51500840940c101d511607620181c580303c4401145550f11264203180340e0051a0000c0d030ba49014240107800303454900103807000d00d41c98050f035224003182d0210300300703104542042040188565030542070310140c071002e10b00071b083c0c40d4040071070b20f00500c20800d5008110306401540402c0000b000021440f2203030042c1000480c5c80c489110791501e01a50085080005448a03200700506085001c2d010140243e0001c0e0340407991a00703503d20109406000000180c007460050141000d499042c28a650043c0001c0005103000d414050701c0f0f0a8040700719041100f40700100e0895031180f241c1140e640b80040007255180310750744181e039607540704014001565003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 618876285 1250 618875035 618875039
    0xe0106141222050106080d1107030302070e040602071a10060903170c07050a09090b0612100e0c0303040801060315140c03040206070b07032406021e120c0d09 69
    0x58203409840a00000c440946907945820301401001007462102ca80c2c414110159034010400074042c13040106074400190034080301d80d8100078800214204103507010383c0103841c10400070f0341c0000c9800482d00e074030070302d081c003911940b40440180c450340e00043c03e8104000040461510f0440046005217001c62606074000c2d0b44143c00d4440c40100d100141551010000c10100b40592000522a91541c002901d179600d48540005125883e160030000c036517039171003480e0340422404042140d0004000c48400d00d40e00c0100320070640c0c4071480a4900c5001d910342e40900c04a8804100207500304070002d0990781c0302e41c0c03103055040c0280380303520055401c0a0386120080f911029031081400c44640041918800d961b5039528040650000d0801c80c0c12860811564000c02c0c00c0302e92540c0290390541e0046466096240703008030903d20b002c0c0200d2464081501008a290001801c0555016480c50800c030300c00101c90341c50400c422140d090a100e44001540307a074801c00442c0c0842000082d40720344059507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 618877535 1250 618876285 618876317
    0xe030c0411040e0c07050106030c0e0c040b0405010513051210050a050709050d03020f0307140f07320d06060303110606010f2109140c0607080a0c0f0506010e0106 71
    0xe100222880750540040000b8010520190306442e4008901c0102a190291950b90942101d9079640199544c0510030350503c02c034003030103403819081070400d8003070350600d420803a00700c5081c4543e210f03041c14400000f66401450b510303550f90ba801003400410180c01010003a0525458103006240d0381d0b0683c0c900400540051400d03c501d0f0300681c210707030f03e19168030b0a02c000d000108000c00c0c1d080d000e40c40b4015507501d41690800051140e144a504058141916014224a05030848080211507040482d0174094002c01d4458090041d1001526845848a081140100004c1c501c2000c0e04114070800c14070911645800076003caa200769100c011317136403422203460344070754054820074005070013001407140789486040c0500841721958864070301c004402840804403240460704551102c8c4501c280001a10103114094560314280c86481c603020f05e950b5010190302c101c1c1d200e1804e0100d48030040081c06540740c0d085c000307640d1081c03c55100f561039071003030f80640e24244100f9000800f070604990b80b407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 618878785 1250 618877535 618877541
    0xa0b130f0203060111190228121a06010c0b0a0f020c030703090e01030b060d060b1207090e01020703080c0a05070f030809010c0905030a0b15061605010518060a0b1c030e030c04 77
    0x1040d00042e640d848107813139a0800801c4000100a8103421501120b01c5003407100d04005600101150b1149c8251000d2516162018910000c0c139100c2181c0707060704100d44ea907049096815107640c800d19a14a5a452810300002042140d0708004814800704040324121800801006800d0003521289035180e0348840b0706024400900004140100e8000407510300e0514110b042e61041c07145401240145140021038141203040001001681c4803850422105141d03100e80300d0b0080d0400025803400c1c03074503180601030a50280c03117413401090002d41440d21a100300150b40001d0b500030050f0441e6000380c2402016848155005480c551a2200300c5242c0c40c0500150720441d180580030b0906c01c0d41c207450380409000010301c50652810800c1c0400c0c040da940400404072610b07581401c950307018403410207600311100100945441c582e60f40d09400811000510b459006041c540007254a141070300110701007a0880d0300900074680200c080604050304200c8220340250190201c48078540c1e500200415 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 618880035 1250 618878785 618878803
    0xc14040603260d0513021008010506040b070f0b0c0d1b0c0210170a0c08181203070c0807060b120c0109060e012705010206011203080a0b130f0203060111 67
    0x12040b2200c040c407040006103044a003454414007015041016001e11402526002c842281000788544120011403070114155440180700740f908a0066040c8000f051071881036004020b0441c0e40800e1038402c10000a03417941c03805034003d509038907a0811805980301c9401440038040201e0034441c11404a007000450f041d40823640d5502e00d07100011a809204503801c82d500400108944400503213103c030401c2404900880326200001078190150340b0040c00300c000079021132442d40b6001115031a0700c4000800440101040b101581d50782c540d00d5003601c404490301c00c010116440411814240f00c020740c80710807180c1e401d0b24040c4048021a08403500c03411406070040c041030000308140406842a03c010705090b4041c10300824001c1ca16610f000e41c1c0000000340b500886002a040c412560305109103401802d001c144e240310300805542c081c200e07d20050490510030707500d02e003015403a0349495205015506441040000a0394260500c01940c000c40320315000c40c0e034480030f8020b070b48400140499 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 618881285 1250 618880035 618880043
    0xf0e100209010903060b041416020c03071505030723040e0112030923030a06020307030606020d02032502041e0b01050f07060c140c0a030906110606090c0c03070c14040603 75
    0x254544c1550f8455006198200d9070350b81080d510302e0300b2000a00403c1c121400b81c41c409141c0d00c0c1201c0a41c6000740350201021107940603030030401d0100120b52410048610440040c24030540f00e40d1240000c955241109800c0b50900d040b1114102c0044c510700c00500654101054410480c2c0e2075852220780c1c0c1c055244024001801e4110070400c25060404e00188820319a0307039100d6040c1c1c4a070000b8502000c0c0e4006a80440c2e0010034001c8640c1c242c411000240141d0018240c0a031341c054005c1d480f07000c2c0000841110010740c0081841c150020310110138554000c0041040480004403402e0080d400b82000e1001d5203031040c504003540c040ca0035580c0c20b449040703a20345017480c00d9842d200071b804e40040340400d0003880300f039a00032540340310003a07c011014030700100500c0e550750a005060440c650704c95410300c5880594600900030210f0403d0307210409031128119070310f074004111054819021141094040801c01c202080841c040700c0003140d00304103060031078080d07440400c02100c005200c024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 618882535 1250 618881285 618881297
    0x90910050a140303090f060405030a03051206030109080a26090a030306050603060307171207050f07050d080910020717010c020c0a0605032413020c010c03060614070f060f0e10020901 80
    0xc5d2980c5131040c2c0140131500007030202801d00c1da0703940110b403800400759811400300740081001841031044103941c84d48007004400a0188c0324090712404078a1054102c01c500300001d01d6480751462540744825540b115130250380114510f0002405611800c2c1e810702100040d0030101c0000c0c0524042041c1ca005160080280a40c6c619082c1c0700e00422514503901e0116004040c0755a08040b03010340a040c40324010f202a100c441d941034403103409d0030140e0700302038071941d00c00351a1000306481405a40e460002545c0503508c030803c140059140031030503804102e082c1c0a42c0301089600c001900060031190f80c0d90200c4403c96136002c100505856140103030b500054003031002607800c40e410b1242c0f1032442d02e0b04540c0540341c4100c4001c42c0f000c000d280480000c0f00d40000c3c050b001000d09200b4206c0074241c0d803400700042c1f4106640140341208055140208040110706402032080203410940030740e5100504000a001410307040e0301400980c40343c0855409903000b0b5980504103402140d00190050b9200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 618883785 1250 618882535 618882547
    0x31009150207050f0321090105010e040f0302011425050f03070f1202040e0f070507240b030613260412030c050a030c020a0b090112020708090910050a140303 69
    0x540082d048000252001c1c070400e140034505040900041c00340380e4414100c0b4080c05a5007049130001080906400e4450b89400f00410008601c50220b0750081d5000200140800e00c0303040880c050300086090320103510901060042d543c02400e41e04d66640e40108001440701c04000060311180034200c0e41d510710003001c000040001344501d00c44102d107082c50034070329912580d58200e01d003260007a402c603c00c1000d121042c4240c0c1c203521804103910044514040703190180c165140034062040384101080e5005484002c3d030103a849402554103980054103c401901d0300c0341460740e0080c8046429100c021807031006c4001c000c0100c00c18003545d1124802c00e45400d16200c456200800104416801c015075288503400081040c00321446081c044c0c0c0e00e1404014180c01000041000d640c04942c034030500b00000006039130040d10610a41c4560000141c0b03d541e542000c945500c80d61408071391180b8841704110104048080d0741080d01c90030b44d07000a009484107142000c504038001d680381e0550050000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 618884892 1107 618883785 618883823
    0x80a0b06030109410312060a1d10060e030303042612190b0307050103020708070f030203040e0901090c29040602010e0c040c2712060209031009 63
    0x88080040c1c0403100c46659119840389802480c6c0e1580c0020720950b5400501d60051101001100b480340209144212904007120b130001c103081c480402040340d0b8401c5452416102004e402107103035445580b1120720121f800d61a400362001034008a0846424241c09084019924405d0411300c0c00c200d2000c2e014201d02c1c00d0010b0710240f600d07400041a076400555001201c1c000c0c28016540d842c681852100c074842e0401c0640024203106520040650010040c0115402c45000803656121130564500340c2c1c0e80888050100280034100388a01401c01450641404208003903055107170002401a9054015a10131005030b5522400022000c0041c01042c1c1c406d10101d404110f21586020050020110303042c50652030451328240d1488000b41104003005007042039076004c1d022240e480d00741e000e507005c3c2046d18000d00903031401d00c44190286c007403120309543c4610b0000120b409694 = true := by decide +kernel

theorem cover : BRFrame.Cov 618705035 618884892 := by
  have h0 := BRFrame.cov_init 618705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 618705035 ≤ n) (h2 : n < 618884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
