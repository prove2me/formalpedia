-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3596
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:13.343836+00:00
-- url     : https://prove2.me/submissions/6b9a197d-bd2f-4ff1-8b32-951b3e5660af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646582733 ≤ n < 646762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646583983 1250 646582733 646582747
    0x1207020c031b030601080303010503030a0e0301090206030f0a0e0303240a030c080a050d360e01171b013f0606120e07051302070507060c14030a020604020f06 69
    0x900c0c0c80c02c501c810100002c0601e04606a0303003000e0024500620044000310304650400002030386034043d074a408401c112154130040f20313994003500400c011075005001d1039a0307070900b40d00085440b00200e0b4407070292030402d43c4c8031803880c000008580c0f240ca64941d82c81c14581580885a0369290f50070410360b4000701405010012425404d0310500070020500185907940461601c00c2c2809070900c800410f01c141807241e0004140f80101200c00500c41d2003010ad01c0d1440c51911804c0c50080b60040342c000c04103100081900d240c1030608400c41b4142908607102141d100e100440380c071000203086070001d550400c000580301540780501025034051940d0400786103d4010305500d11000041c04510141c03181c50030000680c1218126400b40f54101050007119070141f1110b5407841c541c81410302800070010414a141250360544010390f0b8050140c590150380d46600600c003488412044d10191646441e113441400700004407106000b0603000b03410140c0e03441d020001d40c0d4403407413001504804104050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646585233 1250 646583983 646583989
    0x302130b0d05150403020708071503020d0f1109030f1b120307050a0302030409050c03311a0403080c1306030b010c080c0f0d0903200a0b030c0d05060607081207020c 72
    0xf440c1c8101040506403460301c0d0900900e00340d030b00c0d4080803140d0041102402049509000b4040200c481c0c1005a5501c1d0045401c3c0005c15000c0715000380d1a00d050055001111030743c0081141031400c5044034190740038481c0300b03038413078408100440d0348040d002d070741c500641480e4900d1500030301c1180c1580c2c2800310036260241042200c0d18110b005820000c0e00f400300782107600c2501d4003e5141c0c000315080d850300103028a21809030b550141161000b00503e00360b045035004116441e1750f80444107418850740700c500d4a070080d00c1541d044000c02c1303410001174210303c10f1400713803039482c0c80100c40b000e0441e2070120181c0080891010f041c0c104220303c0e0411b030201d2502c800078101003201100501d0b0304905050311074140301010481c0c2c400c02c0000801000401e5502080e2800c4600b03c0407041f0704001d0842c001104011075900c04141c240c00800ac00041810100c064240400b01502c24000b5554920421580d1301c01d5800c0149108810301c00c03841106200c044855020303403640115290500c0d03841c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646586483 1250 646585233 646585243
    0x717010e030d0203010e0f040807110f0621010b07020321040906080f0c150d051f06020609100b0d031b05190510092a09051302040b0a0302130b0d05 65
    0x602c4030020740000041107031200d0400c000741d00c8088000c1e000924141541e41040511a5500150403804c540104012564980741d42e01e4000c0401000240e43d03900e442d0645040510300588105546184000090482c00c3d6408580000e40e0007805072061955030002d8041600c05041d000e025540300303210220302c0155a02c91030700a0518100117100000207240ca2515140540c0355590003014407040344c652001800080c0c4000310340c0c0d0140030034159590712081030300c2c0310607480e121424a02180c001a00c40d401080c054065928081030b240710450340034100003a81c1c0321465068200c0c960310491008a07110b14500301c9c3c802c441d40c0d000d000510681c0c0750203280a0203000c0d28041c6019004600013080030400141c03204040d900010b02060480c0d45031170000e541d107442c0401c0248941c45440c8540715003056034038058082c0303010811050070f0030440030001c0c00c41020b007240143c0c601400324005141214516040301c0e802400107d003186000e1411000d4401c104090b50021408010440041e6080c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646587733 1250 646586483 646586497
    0x905090a17120a0b1905210a0b04060c180305060c03061906050a02070f0503030304020402090114121905040c1719050607140414150c01150510050c0717010e03 70
    0x83c020800c0c0450702e04000c0550380d01e001c501c1001c0c0703031000c081009407a071085c03c1c004604510300c504030806079410502d08101c2c407190018288902041004100681075114904c42441036888501c0c0240d1800c0091100e60640400f6102e07500401c0024180180e481c000e42d440030001d0200d40c4c000301d50000d0020410460380241c0d01151012901c40c455950401210000300b138500d00c02d520061411000c03e8481c4000342002e40242d0300001d0703201c0e00340d0050722030b40740040b400c003074803691a082044481c1c0b03100c0044d00c4030744000d000d008449800d10002d0080c00e0085420041c525500c500d40780c402501a103c82080d25528041e1391303140e1109516900421761001c0c000c0c0d02400c49440c1480c402040c1000000c2c0d00b58500300240400c2c0180c1f032031003111002005007511048050f081d5606034100b80d0007104e9940400d9824030010700d402c104801408000c582e410b46184045603c0024203454500902400000780e90000408020180d00813045048041206000180811014161b1401c0d03034402c079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646588983 1250 646587733 646587751
    0x1012030c0501050601020a03120902270604050c09090a0c0905210c190603050403051902010c020f01180b0408040e0106020a150207030c080903011d010b09010905090a1712 75
    0x1109903428041e0078000c83d1380c00a401d10250a102d00790303503006410740100b401d822003001d42d20a200e07402c54a802200c240e40031501c000751002491aa03101e060000d00445d04a406681070001043c02181c120301680c0704080010030316852550744001c0e0000400010001000300035148400040c11780700c0484440b0094078402c3d00c4c002064415412034a0150000a4103005072240444030009805444441c401c1d52154540411552150704007202c2501030249925404040400b0800043e501548603105050840e02502c2a01c0e0f900100203088450100800c1c00305000000ca10303000440c40d210340c0c0e512901c5a4522402d00f910b600da9102010300c00d07008480981d008a16241c01d00642e103d450000010141c019894a03440d640c0040000c80d840d1001040300601040701c1d81603903002e410981e02c40d42a0403403d20407403501004503002c0d14071100b205000740c0c6070600200305010540201c40c0b00720741c00300041a8908255441c0500380300d1401f10040c1e140341c18400107200d02600c0e0305050140d030402e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646590233 1250 646588983 646588997
    0x80706201c05011203020a030f02120a0801030b060f0a05040c170411120303150d0503071b0f0906150f02070f1404141005040209010509042309070605090603101203 72
    0x20481c240100c94040e0000c4d0600c10014842000290740003455030f4a140e03151030000c042e40f010400c02d91400c9240d41200401600c041005107440e030b4043c400f181224020f185800b2076803030b1f25042c00a02c00504a05a4102000701c5061100e820180c106030300e011002c6c589062007004035544504024010307942164200d60f142c02d1861540b411039030020b284907a0101451540c1046c2204a50032030310442c08030f0050910b110600140401401a1503c158000c402030603a060300080a410001242c0101940e8107122003000c90007016910440c42644d40e0403800d404640072407142034a00c18015159003085200c1c402e07001c21407081c80245280100200304401201c14651010003003580c1800c1d25004040d00c1c0c5008000c50031104482290840c0d0007030743d0050383d074200000100c61074031807420201e07009411702500419111000101a105000760704c0d6804494984441183d101d043c0b0f8031400340020000d0041890529000006580040e1080b0703040165079a21224800c0030384103070500383c001c1100c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646591483 1250 646590233 646590277
    0x90803010e071b0f020d0b092104080709020d1107050c04050a0c360b180919050a090c06030507091e06030e0312040f03170408070620 59
    0x101c440341c0c5420441600380598404001c46001041482620025094001e2440da08040d0b484481d142c064107500542001c4552034200441c0d035440c1c40c0746d480c103140301405801d07022000f81c11000340c806a40c0c82c900a440418940071051000e500b02c401c21403446070b1f80f50b24841c07100d01900000c21507103101e4030103008444800801c10003203074001000b81000600308900c02529551000810100200e071076000203101e03020130301c00303094100c41710300d041040700c40a00f0100e00c50145c0d4020308020800075028243d010a05002c1c44907003e426030351215500f80d94400310703104c1c5e07485800a43d800000184005208540c07a114180c6c08401603000501082d681c4091142e076a61092102d0b02508290700904c4840103004214101c0684d140304200400d965050320341060002403084403221100c0c0460031560341030500b001101a80c80b890118081200802c0e01030007001807092581c402c607004009a820a80c09440362805030481001c826004003800c80b00c1444000c030413020306400d1201040661500c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646592733 1250 646591483 646591499
    0x110606014803080601050910050a030e030d09020a121e0302030f0409060509091209040f02040f06091805092a03010603080301090c050319022a06271c0c0609080301 72
    0x28054800c2c0e04000b42040308500355210003230b03005544440e516040350390707012500e400c5000300800812400c05010004500b41c002d5256080403019500803542c3c00d590a59860f8080c042c1c08441c1d100409500c40b0240702000a4102940840c40c05d001e801070301c1c80c1c1903180d036412500360300c5900701080c0c443c0da41c1020f02490520f8000b15034401e094a009101d190000801c05500380280e4003800c0c4502c0c1c41d06c140c2c0781059070b290160b138018000702e50b90303a190380e0b1a9403019002c48035600850005498a04981041c10000d00590740501d5619025015107994402e40d12112491481d0541942ea8005000304850b20300b40b03e8900214000c1c1c10054980d410140101c061b40c405400c04401c00405200740007082240f0000142445001400145daa900e820301d07160180480c0e4045225812030fa0054048040c0b011920034440d0094508254011410b0041e001c05640c1c0c1c1e03100816103900002c501d00381d08200c44210302c1e08120f14207100b90a0700381d5a0b1440251443d0b4103007220700c3c08010004104000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646593983 1250 646592733 646592747
    0x7081801021b040c090905100e070c030c150626010e01060b030114041404060c0320030a1e020a031e051e061c0302010903110606014803 60
    0x2440034102c5280224410801e900341110039600c584c2d610212011000c1c003562440c0000d103d0700405000b6803070002c05003000300c000e920550002103191400640c0e135501c41c007440421305070b041c4c07600d08090007551506041da003240c00c507031050a035231000f010410000000c5030781d8110046005203660035181c000c2d150300b500c40c09640682076a0610009000c060f60400a40f4152213030300c0000001a00c0c5903001501809005620004141c0075405004c02c0c4003568210041402d1652400c1c400c00c00d00d1940401840f102c900222404402400851071599081d0000c142c07a4908101e0840b00a080389580012a401180100d000c42d0350380d90180d0b403003150703c2d061000720001c1d14420015480d000c1142604c110001c90a0340d4408178402c00601d8030358510816001c400c02001002107024841e01d4040d00030011000b041d0b02141c00040104c074004c000040705841800306039900d40d6600302e40f01d404070300c000c0d003001c1c400603c40c0c090150040420200003a00c5910b20015071900507503c076804c001c0e0847c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646595233 1250 646593983 646594027
    0x51902030a0c091502030f0309071e031b06080a2a020c03060a0c05070f0c0f060e040e0c10050c0c091f09020a020a0b06011b0606060e06072a09020708 66
    0x842d0040e01031300302043c1c0200540d0742e09503545105079980d503079400070113041c921a03811204400782841c208080c0c22110742000000d41e80b1600c040d4401c400e030003880c40c000b00894070903680010705460004001e500c0d036805c40d11aa0a54411988100c80c1107103440002961001d5203800580c80113a0041c0b182c80c0412445400402200c0d041082000f1004000d0041c414681c000c1c006001d006600420480c8080d10f180c0144800071140001c47c4c1c59a0f0024450945044031610542c20300810200d400804031701041c0079803000f01801c0da0700210703c0d07003651540c2100c3d0b0421158080c0f0005908191100d5544074855a000c1540e03500d0b81000c082110300011131504241c0d001072040c0040240709400040070300c0c001e134000342a804159202c800480b20f1080c5100d07100c0c030104500c4200070801c074142c0c008809a490a0300c0d0002d403000000709001c2c1a0103424030192001001a2242c0e0411440036010050907107640700c22100691511214401d903403140d64121881c9100240f030b401075001c90800f00d40e00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646596483 1250 646595233 646595249
    0x711030a0b06040f0902030c0907090801020406030204060f1d01030509030d09051e1c081915050901080313090f06030f0b0f0601080f1807050a0e090c01140409051902030a0c09 77
    0x245c100398001c079942d0396144401c00d000d403800c070780030900c414000e03040032004116000003555110b441b500300602a410904c5a540400c00d880c0c04d12854900803001d010f0314280d20758580100c0358040004401074880035200c00030901042000038030f019440d004d40454603020b0f070014082c003007241c10040006511140300352910741091210500e0041d50a020600074200e51400c074007075031520044004100703501750380c00c0e4045292031010300041031800e901400f2140304880c165020780e600e8040648902c64442e02c1b2411128801091060f00c0540c0e01400e1003d0200c81c0020304640c6954410281d0ba001200039a0403030340301410085ca40c02d040b80080c0c1e200c0001e1074595850b0501c0c0c2004902c280340a8820002801c06154440380c036802000310703400401c001000f00341e00c2e03503854210100d0b04a042d580a4664025802d503602c4950160041080070001690024a40b070b10301030004000700000781c402c4030800a03400507800c61400302d00144d4014501440002000c2d4000800540745188035808241c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646597733 1250 646596483 646596491
    0xa0302010203100e0f010b0d15030515072f0106091107120306030b191103010906060e030303010602031605030702090a0c0809060907090e0a020915101b06020711030a0b06040f 77
    0x4100a010300009045034100400e0580b11041c0301d04100180c43c0d0b8040e20b0303001c0c02d60127000000303120000a00690040c002d10556070035440707082007113481202140341c3e000c00d40bc01d00084030007a61806180591505401c0c0001140f94465110364156403450707103001c4140a001c01c804c0c060100d8a003020a10b00c3e0f240c101004020f1940e512244424402480d0154a01c040b81c0140c0400202c1d4202002548000c03582550ba0740e12440640000e24442c001c00300011810300407100542000001c5034144c40881e00107600b0290300c0c28100b081000b441001319250300003400700e900188c55400c0510f004c1c0d018070714045455501c0100003004084002d040c4a05a0b1040c024000c0009022070303500d095500500010407103000c54103000b4a00504054001e4100000d074007007041e03602c1480e030110107008044070042c2d0807070480d0300c04940c4001c08247c1c00a4000c04400030400042c071542c01801014032410b96041030000c81c0c2c000a0400b1100d80c4143c8690781c1c2c20041100920307043c45002c04442c0c1d410300400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646598983 1250 646597733 646597741
    0x30209030706052203050f0c01021b091b07050c13050f0f07110a08030103020f09160305150d1104051003050c1e100f080c0a0e040902040e0a0302010203100e 69
    0x3907036404140b241e82c060210000c0c030105580420003c0d58140c020464407a8103483c0c2d0b07072410542c0e81e610880d22100502070f08140b0b01086d84042840000c51140c07008802c3c82d14119410068010006448945420390440342e178000c0640910240c4070130344c0500044c081d0703031188406102c4200a40ca440700016480c000c03c1240503d040e0350525006002d2103640c0c1310590721807105440c0a49100d00318505489404154000c0000c02c03001581628400c1d12030b00600202c0c1410300444070b200b030b5003203050500c007203d04034140d0744603520142e4445c0c400c2d03e5010444090001080c01c83d20a500159007404480d940c204c880d04143c06410b41081c10420507010f5145103031240317a25603d02c1010b451003244620141c40c864101c550400d4004070000300040019812001c0c060a031460f044a0311004c00c21610018407407614200030342e40e080b21941c0310001c041100b101040010705040004a0b440b03903481c0c014a02e018010040024001c4c0309800050703484c280200d86040c0b88140b41d100d00002103d001c200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646600233 1250 646598983 646598989
    0xa0c060f0206041101210f0e0f06040b10050607030c120203040f03080d15120b0606070c050108130602041806081c0807050c10020405040b030607020c060a111219030209 74
    0x4683c4a5004a06000c1c3c1c034400b2401202c112201400f41030400b001c0710034540700501640c2c012800e4944044007000198080c29103180c44030f150108070000d0360000d10006000c12221441150300052050f40101d850752698006500303500003120940000e03084091040c02c000110520f910400400e0004608151402d214401c045905000080c000440032801e070081c009580c11010841b1524110604000d803a90207c40094042c031000b960740e070340c1010100740715040500888500320340041d020b4a4087c1404010348001002070b000c0729a040d1103420b12804280c10384040c0c4003919150000348016601c0d10400801d075145038205080c1c5070000320140c01c5c59001e0011100350840c0342e0804030070036942c081043d13540340151800d61240d40901014240c4480706075001b041542d40072581044018150000d160741d0f900f044a01c01c1c00341e8024018000345260680140110407014a010f5000c40700c1d004506003001840807110806c20070101c0c000880b43d4040400070b20003100344c60110306100c100800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646601483 1250 646600233 646600243
    0x30601081506161a0117070609030201091a0702180601090f051003051801180b010e061e040e010f141b030a11090d030c020f0406050a05040f06170a0c060f02 69
    0x145000c0c0fa06003031400d0411031003034024110b00c0b000010b11602076075030700c103440d64540381085204424001c3c94804281d060003030440c2415071ba01a0b441e110b0700c60510200e02120180c841644003030038020b0002d0310042c1d0740d9140b04440c40b02e68200c4003803142403010000d0400103d9401404800180381400c0c495a1070b2560304e076010803924035002c2500d03207a0b52011418550308000d078180c25400c01c6811042d00c560780c80c189403103911888001c81103a988103141340010b007068410316440b000c0402001103010001a120201c981d0040c0009070b00046c40001c83c1c01c503103c0681401c40d460f19508101104801001200d0b80211404103a40d0b406440c03c260041ca07100003400f284800e551801c010304c2400c0c005007900d200c480058641d0148000d036080c061310b4081c108001701d1080c03164a644544a00b082c0c09100e00300e42016011031081410070003004098041180e640049035510300e0001413041d07032141c100c1f505090319006400301001c1c0b070428411507405900034405110440240300d490b43e40c0014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646602733 1250 646601483 646601497
    0x1303110a0b0d05180f0607140315010c020f0a030c0906080a0308010608190c05091e06091e030304180506010512070c0201090f090e010e0607020d08040c1a030601081506 74
    0x40c0000d032540ca06190160300c28020392101309501c6a000c54550500d0f0014405020301281e8550002a4645001040c4075200484e03180b118109004c50403c01c55010306290a51144000e00d107118011180e40400e41200c034540c01500c001000030703000c003c100710030301c681b402400da254081c1030b54804a840182004d5018807440d01003001040001300340009000b1541340075000c403d410300841c40740c081c004281390051705640e449502c1071f0441503070030036640c840c940c071000018280c24100b5030b055040050802c1e40301040700302c084084240026640c0c0510042c00642104080d0f0301018407940f089401310340300140080c0c1401401c202440700c22040440040d071000d1146032a4102c19560b2004031404006030b80314525003001f0010100c0d517900e1a400001403200c0c5d140c001c01c07142d500c04080d941c0c1d510301660701c02c016811030070a4101c1684507502d055071041c0102c1c00740ba105a0707160103808130f4800c40c1d00d10315500100841071003417640c0c0c0403800c40e400c640c200c2c0113002251444000100c092144407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646603983 1250 646602733 646602757
    0x90c0313060b03010f09021810060f0302040510080f0a02030f0c0c15040c060e0916080c0f0c0106050f030c18150d0b25050a20031303110a0b 62
    0x6060000300280c54004811410b0040c00030301c40050b0071110300014064801007248141407030b015811b544500c40c088280315181c0026280000340c0b90407400e480d006c40e0342900038101034003003201240646848190304014103807552100703050304e069501c483c800380000d003410706031600400601c02e401030241425900a42d0308040f036a501c00c103c0d2002071a11072845003c2900072404010001441404d00c5c0c0442155607135154200644240350030005485001c486d055005285080c2c2000041d104d1050607a000b0341c151110380c60f1021f04035180100c0c3e000038041902c560b4444405201d6070928190224240d902500104421904103001400e20001010840400410480001c2c01c0904410401c0009030020748990181107090512540b1101c0458214410150702c8081c1403000c04071905141041d0015501c19041c06001c22048030402220f90404da0350755007a06042510110131b00080c00b640d030f03807046c41c403c209195151501e500f0700f004024512809207102c08200c03001480d822100c034410301d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646605233 1250 646603983 646604011
    0x100f03030e100314090606100e0102030d0515030703151b0e04050c0d06030f020f091b130b030c0703031d03041202030102040803160303202205091014090c03 69
    0x200d02d08a004010640005182c2210b4205014000c03002144480c041c1c0002e035461038801c0c002d0f61040d61b825101c2a011070059008000000b1140d200e9880150000d00c9148000c9030880580300080c07904070303030340c105580c000e4600c980b2a0324206a4880d540e2f040b03500c181c00c407440b180520340c05000f500b21504c003d40600d8460f800141e08207900e00403075020300c0303429104006040c0c49040240030500b441004034040c15034403014010300d00d401d0b5021841010750b21080072100c01c035006505407039000711141051324209500046440c8441c000a035105d00c030151641a2a0380c400d05006007a2584862291080362684441000814000c0211800e4039000360050f05100c10602c0440e0080c4655400b100b268040807034102190f001c0d001c80d207180540680d500b80102c0342800b0011a0751700303011012a0f10003904000c2240411144400e1b040804a14034605100c3d0760b546000c5100e5440c01c44118103d0ba070110700600070310103489043c80909030305451018403807915420b420b03032521000c1c100301c0c0d90703245c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646606483 1250 646605233 646605259
    0x5030907050a1401080105042016020409111314280501120c08012a030207050a08270306011a07150621030f0e27100f03030e 55
    0x1000a00028400500504401a070711040300c0d910200b0424004c3c0014040302c00000c451400740100c503010301c0701c010040307000e040400780c0ea40941e00025540b000c500380c10035400c01507500e92050404145c020841820040c0003681005200e10342e140d8508034092821f0301c2d00950082c0d07540c8166014403c9c00c00c2e4602440c003200d030040388d1602d44104480e01424040049103814140249440903031041c2801c002045d215071141e4266403c0d01000e180c0f07000d02c00c04c440c030141c3c1444c0d480f01d840c104078100180340440b07940365541001070403801601c2c07280c40004c41d035080a00403001140301d464103110b40494040360382c00003610b600040c4a0b021241c40c12541000304999850700322043c8035803183c01452480451a000006848039210300d030700d405c0301a0200340c10b01ca6003031160f0001680c5030361284a903501c140c00944610140e00c3e01d16800107204503000d201c54039807080d4035003689448480b14640d443c2201d010701c00c04c0c040c2e411560300b408525204100280d0854107002502c4000c8414007600307c5e03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646607733 1250 646606483 646606501
    0x11502010e0d1d0310060501230304060209010c021c050d02150c070309170606010306090203070509010c0620030402190501051603021504150b190b0f0705010c080114030a0c060503 79
    0x5500c0f507102d68140904c042d481c5460300030b503200800301c4000380c03a011004062000e07114a468410160500701900c10000a00007407150f500402c45407805040003241c803003983d000700d4001211f88800c004424017649082062000400004140c407840d440144030910200b40c01043d038100103011514a81c2022804404060144110740b003e0300b44d248417102e07070801401c1543e030740b807034180d0b00301d404a0300d00360010402c00a20300071644035094a84a00340383c80c2c40000111050814030360151600c56564001484c1a0314810121345010003100a640d01c6e820140100b000d009079001000725401c00303e00c001c00c16a600601601d40c20300401680000380d21581c1000d0342840c04a205001b40380c003504003000200602c1400315441c09160790010029180071605012180d28902d5003009203910319901049640320300030062002c1d1052030525400e003183d56030b415003510300300101c400105041000520040ca0155601014014114001c00144019846011041d005400f0f0601040800000039030188 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646608983 1250 646607733 646607777
    0x504061b200a080301051c0c30030207030821010605070510050f0117030408011103011806060f031a09010e100e0114060a0c0c0e011502010e0d 63
    0x21488015590666462410050100d00e622100d1144140040d0000140200000b101060140e01000d803d107940d003400200310109031060b0031007501132a500f10100018a61812035001000c04000c0d8616180c0110b19002d00e092100b100045180d620219100c0480d500081510440b900a103005a17941c810300b280724549100981d248018407040000041c00e1039111001f07180f490b00074010348910103182404001030764816a9070203054017242d0010f10041c03400594840e503441c0c4010449140c10341e01c450031400d41d40c080285049411002c8010403048985d9910b082031280023030400c2055901f0040050100d01c01c00345a24200355642034006018440341200030b582c1c520041c050f06a0390303521200e800198004036a00e44d694031854031300140c805810300000d8141c500740c1c2c2d10080d602c481041848003d810650804040242c074154440208101d8281880500102a0903880c00e60520385420404002000c44804680c50f007101100d0800e00825104882c51440c0303441c440314801c58100c85210 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646610233 1250 646608983 646609001
    0xc0907050306010513081e0c012021030711030307020712020d020306040b220c090207060216050109050607090b1e0c0f0606120c01051206010504090e030c060127050406 74
    0x520b11700400400e42940002d6005a60b504086d0380740e03211080d04000c1c5440d280c000760316a021507a0b0320031890481e00700d510003070007413003540048582010300c4145112026100b206402108a07000040c413460035803001c0483d1a0340781c108000d40c510706141d45e00035550180c5206030602c89007503006803403c540e103054565141a030010102d50881c101410000c0c0807600a0343d800280f02016244200340003540c5404024a036007083c02e070341c0403034a0400060040d60104170100e55441e82000004946041c521610300719900820000440c2201072800d1468a0780c0a4120030a2250720700080281c0349101c000c481c0310040c031440eaa01d9100500c189150103015615000e02c1501400d50b0300c05d400c080000f1301c1417051400312650200300321411803150f200c00b1400c0795140000e03020001c1c003004018294050390400e0045c50124609582d40401384211070540c501422160800600d04214580c20400b0354003518139014624008000302c02114000c030320078841201e88a07110000074044c002564841084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646611483 1250 646610233 646610257
    0x614040b0a0f08100609090509030705011b030c0e0f01031805011d1606051209070f0303080a0c02010b030705040905070b0d0605010921200a03060204090e0c09070503060105 76
    0x803004881c00c05084a00007a03080d200180b1000f00080b20b00710390341404411507500d901d820080b60308010408001d84002400200710f40310420644001810900c00c0384409107840502d500140a2140c0041c01c1c3c031100040c8104014400002c10281e45e2503c01c070601d960000d082c00941803424209948041c83e4903203011b446540b902c4503a00041103869801060711003080203840007500c20440c9101b1580080c01000c000900c10311030961900c510960035504943c090f0101e1745480d580301d01214a118540d04218000f031481000d001c16000c50f4010ba80300301c60180003d220200c0030b0800300781e80d030545204a500c42e9846102c00000c0c008140965406024441c100d20794a5121000c01d40243c22144035481c00154210300018869040b614802ca1440401000c104142d0081d103401c1901d0310a90443c108070740c5d061a0710001940c4203441d00300214442ea90158840385807000900881d80743e04002061604082c03601e41c4642e1f200d001d1154880b2503424070a4480d114900100d1b940c2c041c18008000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646612733 1250 646611483 646611487
    0x60206181c020102031509090a0f0f2001080906040203060c0307170a020703020c0d1e06020d0c0903020f12150c07050304060c020f01050705031e0c15010e060102060c040614040b 78
    0x1c003a4190015440743d043e035610038261084407030a100710b2000c21034500300181c1080c4400b000284170640c42d000c015015100684020802c0d48615400d0001e401c405440d04004407140110740d600400400d038044158005494245441d4000ca51509801400714600c502c00100081d5164010510668541140103880b1a546454030300c4000940c0000b00560161141021124080c5072032200c072110150700001e2081440e00701d0b511b0440709030380200c080b40c80980a00c1135190b001041d1007040485030155440414580c030714014445a1540591800d0082e9020b01020302803500005100040c920034050103000f59644483d19a00e60190f804003d00901001900040180d405401d140b031b03040c000c888101241134040c0066030240708000000340143c00c00d00442506907528030a040d005d90344d1800443c07800c80d4100c80345040000040300d424a6030740c0d0200611610b00c0c005941540311f8420300081c030032400e080c0900401c60149110324410499803044065450707480303100740c070003c0440c254116 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646613983 1250 646612733 646612783
    0x110f130c02030c01050916030f02041e02120901180206220803040e071e0507110919050a0c3002030f010e1003030f121104060e180106020618 62
    0x20b440e6401210b04000d5907080c8004240c1c240004900c04400343c600e29480d805c080d245a9074160822001070090b40d100b41d555984440c18a81c41d4404880d01030910401a510076506084011030381000e03214006a030702d03142c192000c6c2d01d103817030146401e00e8048828ad0388170040041301500c2101510b00000020080c00000900c1c00d0001020704240d40554541400b03607620300303600b150005683c111082c18410300400e20740340305000e00020200c13603010343c04030050b0048070700104121a800741d1714401102003803c8003e2034061144902c54000320b40400901080442442c000e2a0f4041c0000002500b05280c8201d0046030800c00250400108000705544a2a144c11007540d5080700344121101503154200103200781c81768003501c00c1500d906858203020072150a0048402d9850703203801400007030380c584915194034102c9010303000400311030f40d40a2015690b242031001c140080d0840d980385004460062211980201c0d01540c0b00482500750140d54900c0f5004524107064681661080780d503081f00d030703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646615233 1250 646613983 646613987
    0x3070606081606030b030c010c060e0124050a050f040b010504030b0f0604050f0417030709170706090605041203030c1b030e03060106020a0b0114121002030103020f0d110f130c 77
    0x101c2c25522128a100030110f65072401a41070742d407103052450381a080003440c070302258003803600c911105028200c001482020340ca400e6084900400c440644010b44000a10031030310181d0401c00500015603c3c040303018980b00c0464548145038080c0347c426a11a9034414180e40300b60155401160005150065030034041803441c0301031800c0d5242030080b81003500080c180a04105098083e55000d400c3d6110480003400310340150308003070480e4040140384c4600150384658143d4050342140000701525070302d850084054010311207a03103c1c20600c5000c0c041001410700c19012150981e4140c00c020a440900c42412194143d4605940700200b00740b4603140141503104100044292080d811a0240c1c1d80310501aa80c07036440a40c020700100704100140140880c04016900c0c1481c05072400c484096115449401c011110b10408041c560100042040d40340105488e04544019101080c1795038140e188d40e40400c070043c000a0281c2e900c00c0b1a100b041d1920181c3e406525084101040800400000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646616483 1250 646615233 646615243
    0x15090c0b0306030d0c020f1003110a031401140d0807020102010207061d010e01020c0a030c0c08010606050c120f0921030301060f0e090603060105130f051009150510050c0307060608 79
    0x3060300034818642c41d1079a49005d00386010900f50001c1c2200c400107218000c01804c1540040d14100301915086622820810680a814041004e4a0200c1d060b02581e1000c0110b020580c0807804140d000501c220b5503403034041410461030b4211803c0303541d40c01c4600060340a0310401034001d244616040c00741c0d2404040005c990080c1082c03200038491100e92044903400d038050003118451035045001b14a0000c0d02400f5090240380c451201e14030815500d110140c21a038491780a0345c086280040d00200c00001070240380c88900c64181607034188032458070700003564081d0303010440c00f030107200601002400d030010342d051014419000701d075965a141d140c004d0201040103e520701040309112008100e207003100c040362140d0b10140041c56942c0c03a03d0101310603071444000030101c03981e0b01e21140c00900220302030f032489010600a101045803402c0c04500449d8184000d007100241041014440740e030302ca982021055a01d031400300d481e000400d0000d400c500c03e044c0010020341c902200003402c0400415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646617733 1250 646616483 646616491
    0xa0f170c1f1a1e1c0803060a0f0303080c09010c050d02030901090506031306090311070909120c03020d0302030606041e26190602071a100f0509010315090c0b03 70
    0x140404007660704104034409024062950245803511070f081168103c14948495920050000740b03548428071508904000c11402661071036400001c000a0381440580c11008010f400b802c2041c0d14a507031030040040e18041d1001c09081f1000a102e1031681c0b090001d0b0940a40100a88088003200e90700a0741c2c070b0b88004495408600d0500001800c0e00e8180c05030ba2281100c800481c85d044090b6403917a0090000361003c805102d00700c2014202034104108a0000d03100012001444254034202014510354000c10042002300b100800d0001030703808524210300303440500300036869894490008616006030b130404a541d0451201312404015521428411280040354015010f20032000c0c1c042d40030740003803443c2050f0b4000080710a501c2050044103120133b0042d07000604046955440c55000e00c0020041391010510000344a41700407540c031184010515200860282490000414000e10051101074a542c1031200009008a82c07504a4084650701200300302455031103401600851300152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646618983 1250 646617733 646617793
    0xc300a05010b0f12060325051c0203100b03100c080f01060203090a060f091208031801050105030706051c0507090303020f070f090902030c13090605090a0f170c 70
    0x40005900b800100c1254658450380fa03038285042400d0000000c40c000103842185c061246042c1c800001020130000030201004036080e40e41680b8102c10012000c0c66400d40c4510002005076603001a83c0010715200d40c07040c0328102180c1070415100080c2001c00c1903150300c031640e04055544440703582c041c048a104105070003d80b40301ea40c885808070303aa409039943c420b030008110b800c1440707050f02030400003030380d240706103001007800f51120480740742c0d84500c1c0d208031410300c8081301f4420b800140e0102c9031000c004400003000f680d850140080e54803502e92048400b030100000710441c42c460010200d10612b540d0210500c41414050001000d449041c841031700103020b1a40030a41d06c98003c1014402c59404410000c00d140c20f1200c0c410041421100c22641807046e440b4401c21901c03290250030903101c1e4203000054803ca54107004055407001800c0059940150b10038000140140241c1c00c00d4a8100c051412400b0074444140018031490520042d148281c084030b0055001082c034104100c0b401e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646620233 1250 646618983 646618991
    0x1200703110705090705030a090f20040515010e0d0204020a0207180207050709020c1c0f12090507030f1a2703031003350c010605060f030c300a 63
    0x90814030b0785500541c05656800340115001c580f0162080000c2d50300a02d12050000e0049142c3d40c80140d42c01150380200c0c1d003504400d4140c9248000c0300b04030302d100101920700784694584603001580042c2c54050321410300003400d83c45201d644500c0c400940c0b0983c0900115510b44c003025010755a50502d2017450048075508171211041000e5000380c0c1c0d00141d102c401000c1041c1819100380294011b085811403a100315680b101c1c44161080c514001d60b40300703840f240301e00090004001c110210514004088174182401d901c00a9000118082140e4220203c890200401d240c00201c6004e100074a40f218882c80c018492644111440075500c015004220058004060100c036200c1c0412291038281c00d908000400215079429482e81c541d060000034201e06800402c0c164054503004121050b8020f00802c042900100034070030703400035140450382641044441104074400d480010b0001680103404035207000180c2000e0107069080042580901c0d81c013601e13981d000d040840880c0c09000c80c0d420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646621483 1250 646620233 646620257
    0xa0f0501170c0103111225030b18040606080a05010c1704030807111e03070510050408070f060b060c0322080d05130510050a030e01110d050901200703 66
    0x748406490881ca11001500190080300c00650082031643c0e4100700301001088140581034521040501c42c01c01d0702da010101034040646103610000000d5410f040c540340922034116660707200701700e0140c108054105181703507031989403003001741c40c10b03134040c3ca094810313940c9401c01c01c40c0c190007114490785075540e00c42d01f8075a012107402032840c2c180c9010300400c2600000c280d410f4862281c044002512108807030080e9031040142d9887c4c0f031802d0b03c1481940003c070381d84c41081401d0001c00d000c06e4042209101c2800c080e11a0600c503c02c4000c01002c190f403e030398200401c00c1c01d400c55940404001c04c03140d240c4d41c010441c5500c030b900609259030350411803107040d85402102403484003902c401d0401000c81110440d02030364213900550001411006036240004d4075130721205c01103040c14281c1d40b1151039030313011800a0706031240d505150310582d04054a56030b248001c0c006540041203040e00210720754903100010342c0142155200c442105241c01c1540551007040d80052910b54883c0e9220551101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646622733 1250 646621483 646621499
    0x114010e09010e0a110c0f07230d030c0503040f0311041401060c080403020405161436040c0e0a1d070c0222090605070e15030714030a0f0501 62
    0x505030500e68011110070061006400607a0b2803680034025000014524021780f04001554101c52071004082d07001c0300040c441c0e2201404402c004001c1060000024000704480d840424182c00c03203140621803045050007414400c00040c2d070500e42000035280d407280c81d0000741442c08900c1c04165000c030b040fa141e10b1810309007803040c0540a2445031a426099090602c11225429800303c1035840c0c101c244004000f59440f80718a0340110b01001c03101000130700d603d80c0a001002810418a84158140700c641070341103c1c90802e9804106c144090320104c00291000d41403113a5203070040d90800d14011001d0038290f0000424621b00004840c04040c2d659240d50410589450301c4406407010308104c0402c01c083e00540031407107868401081942000044041e44c0b40700c007042345a920b4a1505c81c0b12541c14016248181341d0041c0e038602d440c40e01c0c03100501c0410502c010304c22940117041d90010000722254031992548204080314120306075281455040480174242c201600d28055290038000030700d0361 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646623983 1250 646622733 646622747
    0x21e0d031b090506031009050c181e061309020d0902030c0f010509060f0f07080d0c1704030f03020c010207060f0e0303220303061206090c05100504180e030403030503011401 76
    0x15081d80d6a910b52400d11041c41282c1d00007038008450303100f07103c0300416203011501445210388900c0c42d07029118072041c515140100c07000c041c01801141d040c001c201c81d000315150b80020341c0101baa55103545592036220540c1d060f40c01d60140741424400b2031b00441d070300500d403c0000c4090013103044a8601030007008000424421201c0350340490820400400d040c1451006048450410340101d820150300004400f0345a22242049441a90025480255404922403010780148034501109850400c41c1e079040c54030740141001d410f00940c240d50780c0905100790125070311040480001e41d03c40601e890711201a2502282224144e03041c24040456002c0c000192441510301c516841c1d0581c07207110f5888078001c0d80d02d106904140d00e400000c50f0001140010504051013040c000804c0d0001e0b06200b000541c141d0005032060b00c80c250348000d865440b074191810769500c0640d481045081c2010940144191052440c00d0300011400105141c1c01102947c100c8040c03081c600c00711655000111345d81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646625233 1250 646623983 646624031
    0x10b03070b0a09060e120307050d1e05030402042a050720061e0d05040b0a05090c100f1803030c05061b07030305090a1704090609050c0306040507021e0d03 68
    0x3000c000c0200f03c0031748210313508030402801a00d101c8989800990300c0f411548211001c0c0c7da56170051a0501c0c140380d00044080031820040703940c480010034400010464131020b00041d11507a119015010050440300c0d030000000324042c200480314080d00d40282c015000000e041d10280c0001d007080b0940b005490781480e800324002c0005242000c80c8142007541000c00f049850b05c2d071014404034983d45058030a050203035004d02904411132800d140d010f03090b11710080c00c6051a420a691490380d40d16495440e1182d02003900700000e10107040d0364200e4140d078865451240d02c41031a80008107140d080b11012a0160241060b80e820742e40b801c9080c10080c0765a900d81200c80c2d020082c150101b44242d100a4100c010901603c840649580360040204202d032040200014005010842e050192044100030a0b07136000c140071a20b0a040f00c9a207600004103003a00864035040001d60b443d02c00d0100078440b0044040c1c0000c412782103100c155032040c16988082c0820314100c84c0c580c002c40312558134020707 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646626483 1250 646625233 646625237
    0xa0b100f1b0c121401050f04120f0807031a15070b090604030206061302040503061504061a0702040902060f0c03041514030403110c0d0f06050c090a061b1202010b03070b0a 75
    0x4a140b40980d40d4101d40e000c3c84040d1580b41d2a080201e400d00d030203004d481d02900781c1c05004a03160a150401e10400042410400140b00c0c030000780742c4456420902c103d80c400c006080004400d018031103d00b175850310807a0071603408103103041004000016680901074040c010003901c0031581e20711800d260341c0c610940300600560b00110008003a4600491080c0380d06250100160030b041e50340c0c022a140a0080c1c1c1d20150340590300c0380388c50301402c080c40b1f202c000f003030100070342080e41100401b6072a00e48210240640219194131030401507480340f10481d010403124580b5030b40d031841102c5040d03890360006e0088041003040c84120b40c1030310744603200320807254110f07103c494a940c41c0d42e5070030358005102110b609128041c10a65a02e070b60b0700d6004104d41e40703001c1ca01c486c00d50103c1c2d2a10304100c13900102f010b00141014031414203251600c0a820007600d096080145170144a50b0129600d03440c490402409411014200581c25a06402c96502c0c43d500750115602ca68980e85220380c0b0340941c0001c080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646627733 1250 646626483 646626503
    0x160e0f090a030c060e100c0e0102060901060b0a14040b12101a03070806030f07230a060c411005070f0c1a070f180b070b0a0b100f1b 58
    0x41022503211800d034103280000c540c6180d00380c03007017802600c420b07d8040e008110100d0b4000c5a5580501056a01c04080b0000700400c906103940c1c2817040c090303d2034980c108803110b081007a942c02d0f16011540901402041c3c2c41c1c40c0c03481c202c04061640d000f00c2d40f00b0300f182a155000100c8108004402080150051500d42190781340320701220068401412281d1501c101d4001c1d0030070540c10701001c006403040800d4000e041003908600046401c8680c60709009207211842004456402094544010350200241181107103103149404070943d07004e05c1c40210304403007410381030040440d01200c00b464402c1054500d2580342d40f0010048450482da0f1a0100e4040406a115584900c041e899083e1040740d0360700142c0307050141003144020495a407004102007490050419401c82c01103960401104540079009082031301d200d030140140a00140200346074004039108011030340040e00c1015001d441000744840010004240d1182c03941c0c0d90020429640d00043d468403410003103400141c1000001d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646628983 1250 646627733 646627757
    0x31407140402030c120702100c0809100e33010806060901050613080307080a02010e030c2a041a01091d0c0a020309060a170f01031112160e0f090a03 65
    0x40040d501c01031204d01904410056640003000300c1c5d070300310302582c0c407580144903450801c1710000440d4241603c503000d010f051030401904060000b0100300110034403401003144190b03a00803c0c03405072030400c106980c004100310001c031200344070040c4540c00c203103030031411b0365903030740c4811544902c001d83d112900905044010b01290400c03100500c2c5494403182c880c5a032650b10102c00317055401c01d01007141c0000000070790035109542400381101c12880c0c3d0015520f0080540b1140c0e648021050b58a06544a01d80d00400e03103607094110084c200070040c0c0140705400340f03409000742e860003602280340410302aa001150078480310191021000b0201034003006600c41d001c03217018503008000f2010452001b0480c424443d191440940320103400c985400340800609a03003656a007000a0840e56a910140c00400125090560500046009507072110342d12035000407981c2001c1942034229800c0d070010b58001600b14103d58510f10909003d04082600d845458402e5142d410284020300029004601301c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646630233 1250 646628983 646628989
    0x30c0512040f15020d09020f0a0503191b0305031b010c050d050c0d02040b0301090509010203040f0b070c060e0d0905040c0906050a0504080712140c1c03032403140714 73
    0xc90301180140c0d4508940b0090701104000e90f80803c0c17581c0541501c500e0544210708000b02c0005150204880d20003840b4108004a59074a002020794502c942140450005100d01010491482c0e440303e03540c13001064403030a10a0ba1b0351300050501d00ba202c0d03400548a51820184a0141000c505944091400180500d0f25000d010050001a6040410403075150442c000c2d100410003015440581c03a00c0c1e6242020300800c54500520390040b82c0d004004000c00522500e0b003100642c2d40c0010b02c100f550700d8500084071a99400000102502d01d00070451040c1e0b00e00207406081040190b075410001c6490300c0031f000a941d12102e030f003c0410000c2c902401084c2c000c030094a9511020b10b40141400c1d44e599490b464041181d1144c1c401c0c0312099491000d22442d0070b007040c2071400c3c0c0b000601503008080302141800041021040100d090010300004040c480c1d00241c03145020b94803588090b006080c0d0710030a4000c1c0b84000c40c0c41c050b5100d0a02900b0030081450821149003080c10001503c0c41014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646631483 1250 646630233 646630253
    0x70c031101020703030905210403080f121824010e061f090f0603090f060b18250804050c1003331403070902070305091005030601030c051204 62
    0x2201031060910102540c030500344041c2400a002c0d541c00302c1e06c2e200e903081160400b0140b203840017902040d4100c8010300081982214102c0742e2201c0019943c00c0c6401c0d070180c207030007030001c10300d4034411100510501844951300c048201c4004001c4d5484881f0700c401f41003180f014401049c5043c988500108280a0159142980140045c2811401d00460541c20241d41c820034445004251184400d00100081c552940041c017001c0c1010807202400b52298494090103200041c000341d100c80c0c94031502d4803407880103404151201501800f07402c05029480d4004820b02d0405200074094415125081c07141c0400b9002e0303508000604401041a420301600e6002d96070280c0a050b1030300a01d00703100d60805d03800180045c0a505880507001241d64249110015510070611022a0149a401c0d42d801068420848903090f00c0103075949514a0b09076a54001d500e5001d50213943c0c02d1280f880190014011441000240d034104101d1014890648090151404c041c103500c0d080700000b00040c0703060031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646632733 1250 646631483 646631507
    0x1e1c0503100b0d0605040234111003110c010f05060f030a021002012004080628181211062d0a060302060313110904030e0f0427060e0303090d0813050d03090312090b07 73
    0x90041842c201c3c822602e13300340d00c103000f9440300369034490003600c07040c009104458028800b02e13880010080d80d440025030350200c000c400391103215885081c80310303a8000d601c01c0420702c0d0001d00955594440c404546070580151294403002c0c050180003031080d180b40000400708401c06c20309002c03440004c07100c5c0c4c1c00401291051a224012165038003000c12048091035075200c1040d80c400c50620160001c203420510090001d82d1603207101c3d20300001d0400000401000704142000320702d459510480d03004060105076002135001400001803051100400e4004c010f146d0051003c11490f242c5c4806104069008450141c0020442c2c00010101e1800c003008180c0058000e0022a00c1501e86141c400c0d4501100b003404600c3d04034640079010070805009161b04a0000b0001d1070a62a1000c41203844c3c9403075801e01c1c400c101c0c2c410b0000d540041d044c00e08000190b00710048806919107581d004c5e00030460010217602151020b401114014524010113140300d034484081e681a4960b400305a40d0940041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646633983 1250 646632733 646632737
    0xc040605070f301116150c02040f0905070e0105030c0402090120010507091e05012706020607080112020d0b07021e1c0503100b0d06050402341110 64
    0x503c210720b1104040801d5032040310301e511642c04900c00c2d888050035134020603425012940018142e802e2108412007158101c07050b0105c098500000441e08a80c640c0041100035030081ca003c00b00e01800e0055130141c03400900c03440c02c8860b8103444076412030f8070350000d202e9030b075055101d440d54061509040e006410540c00604040c0b40d15050321803051001440e00d4110981695501d0402084683c414a000c005007212034246041a072800509000b05040d800f48038140500301c1b4040d40c14084004500890244100b40c0d8106240c503408001d403901029a14000018440c00c00402e0b2201d40642580103254018440300c00d01c61690b031052144000200900e083d4061110241900c151012022850311004809004944800c4140b21b03a14030380c5200140c00c21405200300108011403180c50001c0e6090740725040e494030351406030003014050907080340c2d4200717002241e0303c4c0800d0b000e01c50291850a0500100c09500c6540080c0300c078583c088080a000c03003c030490008585c4c1003020041c00c2c450358138 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646635233 1250 646633983 646634003
    0x15030f1107050d120b061801020f100c03050c040605090411190507050d020109030212031f0605031b160201030b0d080307050703020d020703030915090e0702030903060c040605070f 79
    0x1615040e4801d800c80321054400d600700c3c001c0600c080d98481225510301c560310b0410010300004001240c0d041c01011954180700328040d1940040768000c12098008000c001e04480007001e415640c0c0d8041d102a034011804242028081005d901c1c10b20143c0e0f05454a03903841034207001c411030410000c1c0c03500d014200e4032184100303d4113000110015a0788841e82c459140c1d0f5544142500c2c1c0b01c0d05d0410072010f08811039150a241c40e000030f82c041030041d019035071400c04648944071080142510b0403d01c21031284181d2071180000c1640d001713005135100c1c800d5000710150303062851012040c00d12602c10804605030342080d240e4010760082d40507054030440030b0400400d01c48140d88001c03950b4015101c240c0841c80111b002810143d040154100110b6a072004d401081d00c5c40d500500858624003c0500d0700b03810345940021503106103508001050b090024455504041c00082e449a0012121034024003c8200140c403042e1500304072021039000340e81ea1407600d51070351104524150f00030000c680718444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646636483 1250 646635233 646635251
    0x8070e2a040f030312050f07111203160f03060b090d0c0306060801060e0c0a02190807021e15131a1303060609052805060a08030c0102041d0115030f 65
    0x54680078202034090b032018040403a0542c14040e159030385120056101c1801d0208001c5805800340c0c503140c1154243c05d0851281c3d42d5480303d00e092a501840b0f2614140c804000c00c05c0c4141140721011450f0a40e0700c0d2800e042d488500c044050310b640e4080d00b450300e90100204d015608051060352051409001c0705400c20f500d0303644550594503980d002c20580d81d10340b007051003c3c0c07100d12100d81e0080c1b110709446161442180f0082d4071a0100909000d082c60070240100500851100712610568002c240480a43e00050034801e2012203140c1507006508800b1003941c988407240455142e048105152403a0703501c1e05040103102d0100c8540144040350034000d03024241a220081d001641c07040d4004512203003410390200845600400040b0701c0500524116414041d0440303210000c40c64400c0441d5a030344240106d4002c002c1544003000038403002601c0c0741807140641c0500141c0b0b06c1110b049a0342072020201c2e50040701c00380500c1048008041035141654044d0307003c802ca5035a610b02c0030a210f20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646637733 1250 646636483 646636561
    0x1b06090307080c100512041506050405040b0906181b040e070b091008040b062b0302011508010501030c170c06270907051606020d230108070e 62
    0x159404291140e00102d11280c09113451036a110a000d0b0341c0c6861810005100608000782c038010344060010300301d210344030245020540280c405400c0142c028040c0d4102450003485000e8120340d82a10b901a00b070100f080f901c081c84220802000d00b4006020308403280d203140d140b48a184510b50b0384180e80c0ca182030515902070003000d00400c000c088003610380c040382d82882008400c00d07041c101000a56003c200c0021208071459400100583d00103103001200c400d4101c0c900101c010510f07500002003102e10030503605402c0740040394a44030688a40c0f42ea10b00045080c0c034020301000344001a28603060254540000c40d0210b41c080382c200310740c2013040000c08a81c5960124045210400701c5907520f00200355070710f15251070000c059809028030328011300000c119024043d014100041d00c10540b03000c1c000e0f690141c5144c0b11075803000b040000c00e9810b1070b2100c106440703407030407440117841d0000548003030200b02c80d0103c40e13125143c660f85503160208050300f12120300c0503507041c0140440c10a2014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646638983 1250 646637733 646637743
    0x516050a030b06031c0f02060708040b0a020d092f09150d03030b150406020d081012080418021b060405060a09020316090e070b090a0308250501091a091b060903 70
    0x41039035141d0341d06e0848203d400900780b8400030100c20900048000f48000104504040c5900c501c20b00001a1107002c41c8030040003800218001500301e5950464010741c5002480026804040e00704020b09005500d10034080d4142c02214100740340b0192002100c0c6604002030100311091007858002400400b050002c1c0e05031030000c5518054010100d03060042c0361f010410b550020503941451a403601e0000120a5144c0103402150301c001c66040349001007126140565000e040e07110355068224521415560094100070482000c840c4484914190080046081401560400068511541d50b140e41c10013410104104a070940310b807003d03140b08020000351100c0600300740c000c04113284100c40d2101e464402c3d070b60801e00b0300680410030032001c1c1c2d035400c0d520f00403254058802525a42d44080a110200002c03821507018401c64440c502000019801120001e10441d000d26555042c84100c5d106078004860608155010100c0000c4420741c2d16402925160000c04140c64078001c0030109040c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646640233 1250 646638983 646639033
    0x10507060212060f09090a030f140d05040303060b030115140909130203010b120a0219121a160503040f060617060417030606030c0a020c04090b040516050a030b0603 72
    0x625600c0140a6103282807110240c210408481c010b0306030034181c1b101a21141206801400c0c00810342c2c2601d11207000b2940078441500002c0d4107900c842c103416202000c1d000c00c0b90228000fa28040d00451600d0005e403c0e241610004011203070186441281511410244404860491814495080940d68030301a0038468403c4245150f06800c20344140b50a48107201d100500c035010304401c4034468980010098038844d012154000f1140710300c8107001c0c40c404181c010f0a500a00b4801c41c0e000c2c41288074204a41005a2240c0c0580750303101d00b0300011004280c16403400140703080002c200815080041c91003c10300a0034000f46c0d10340e0b5180128070501001c0d06000023504001c0c104018001e408440020241031000c80c00e296203031540000f00c2a21006119040c603c01c0400c100d100d541c800c20100d400004050010000f441140c208040d02d10011241181c852085c041c0745001e20a410030100102c60000d08642c1030350381981d50700b0155040c014242501071091207a866011034480201e6802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 646641483 1250 646640233 646640257
    0x30203060a03061a09090c10051c110715150605091926010204060203070f06060f12060f090302100c0509040203040b0105150304020f0111241501090e0601050304020105070602 77
    0x1c10031300c08144205940014141c4480344c000140c081c019840b5440300d5a16000316283c83c55441c80c09144080140112100b0340400c40d140c041c1543d072424030f00c001402401c1c02481d881070040d59010607103042d9505008511103142c40e80c0810085940102d020b440c1002008041d0209000740b481c00d101c4440346903000e048920b1212801e00298005e0f000d1043d8280c4240000f54580750920402a640348141d0344000c00c141ea000041e00d007400026480b10010303002a6056540c0d2507038403029685505011101602c48a140c141209220800c61258107000e40c3e01d40c01070080020201320043c014502400080c00b40f150400ca00416940d07940b000f18400d0703101d80b0a108003941000d0920482030460500200070600410070b00015954000c500e40b07040d07100b482c01c0c41c50020010f91307860400000c11181000a0300241540b00000d0440407480e110f1642e2a19100c40c000c1000c00455200200d803290066061581011a242d54070400065a100380181007481c0b034061035030744030412688690300e46070b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 646642733 1250 646641483 646641521
    0xd0302010219180e100e10080a20010f08010501050a17010b07030921060902060c0312010503240a0b03071d01030302010f02073309030801031203110307030203060a0306 74
    0x3078554204400b4000b030030380c141312034029103003507143c80011045901940310540c64800c00506510100f0480d0300150040c00292a0003a07218580400628410040d0861100000804200c954485d0400380803201e20b40c0d40d8203030f0700d07480c0c00d0064840f030780040600400c01820401c0098201a007080d60741c0202500e0094541d00d071440c1c00c0c001d03c2c1d00413503005a03060000b28061141150140301142003800d410a40009a0035a0780c03001403121720512a80038814000880d0380c148244540e000d4904a50707040d800d8070941144e07130b071a02c41c25210074031440c0d9030503100c800440c06000e441c1c2d2103012a0040a400c070b0740722548404001e0000c800701581c25400100340c000501c105542070084128040a0000c29410580c15545060300030034200050104040b110720711161a2664181c40400d00c0072991040011b5800d0f800c004010103024007050f52000d00c04c40000c0e441074824450090380040e2684580d0841d141c2d45400c9010358030180082e42d00400440002c0086200c5110700d00741c080384409010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 646643983 1250 646642733 646642757
    0x10030c050912150c1e22090209040b1f1b0c121403131809060e01060e1e040b070e1e0103151a1b0a0506040525050d0302010219 56
    0x2400307002842903002d104140700308054400942c20081ca250f45408040d80c40c0c501c03100e0074414951254105c4604a54206e4000600342460380c01002030300d030140d409029001015050119450a0300b5100310401013802d01e09012230300c039144840701d00540040e00c0304100006c0c0c42d440d0070250650030400c12008a80c14210410815552082c00070080c0406107003003200179120803030800558031600400ea004480c40301c01d5809198802707111a039000714208039001d5415004c60007003295010f10706404c8a000040703150a180c0640d168400f140040a05040765981d83c1da42550410280040703060180b10207914405a8500c0c100308501c0801d6483c0317450600c5004001020b0f144040d995241401c2c04030030a10002420750469070b00c5001100080360340d101c0064076031250206291140c580760049202e01400c0041c042100f074042d038042c2084a440c240744403002c021442c1600d81920050313110300c0041100d810240c200e03405442c041c0c000113040c010440c110150f000200200b81c4005000c4034021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 646645233 1250 646643983 646644013
    0x90608010213060906050f0309150c04050307080109020a0b0c190609021c0308010e06210303010905010b04081f1d0a0b09070b2a0f07031e0210030c050912 68
    0x1007008002515083d41d04c2403801c100900907214001ca01c411025002000500005e000c110418001c1203c3c2400513052500c44506049508140141d40c4240124107002030a040140075120015800034400d048503868003440e549190f0040e25880e42034001c1c1d5028041c00441e50700c049079014010030300810306d00d400c1d1042207940348c6d17500643c0b6510f007601450000842d5100c0c18107819241d04403010403c9031510070000d645142d9440240b111a900800510748025001c400356048410321481030102d6601c0c0c04085045014501620480d58440c1d00045510401d082d0055000280450000f440700b660780c0c14000c5145002487d00b07140c0e4084128001000303200b0409a61044021015082c0c190030321100d1202841400040700b06001003880c844104c1820108481c84034540200310380041e000c2d0240c1c076407203202c40d200985d418002c80203880c03842580c0c20740c07101565900034018003450f280d040d0300383d00a245040745001009001d00003170382c2e1522070f0300080840c2c0602c4001000e82c000380f1581 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 646646483 1250 646645233 646645267
    0x3060c073207050616030807030b06072f0d03030207020f090123030610090b03121c05150f0d030e040213030203121206091f12030e01020706090603020c070906080102 73
    0xf103000f50802c03c000481d8000f500c20080c405a072500d800750752525100e0048000d84081107078a5801180091450104800c040c040840d281d601746500400c0f50074501c007d41c0d414201c07049203030410150500c0b40e002034401d03030042001c0c40c801002c0e01003145c0c950001c1030107400c0036005801c4421280300039882d00303070a003907003e0341010303007240204410714000031403804e21451803041940c0280c96150014582d907080c000e4400c445c01c441311144e101c3c148a43d17030400002148800100340d914050105001d000c551103000445003001c2c000b40f04007107406050010554462500760101300c12003140343c07200ea50301e0008025011481d1610907480e41180101402c209441009070010002040a400036486202c19103501c50301c209d83c50700c0c03603a4446892503160319580103402c508520043d0045404031070f003030f02c01d900b881c082d595101905114000581e51400b280c01400003180c841e140801049200740c0080006c50007a44c00d070340302a540da090100c00c0c1c5c0c0c02d07508481d031981d401040c0c504074040100300d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 646647733 1250 646646483 646646489
    0x1e15111b1201111b120a020a1205030103031403090307150f0b010e090c07140d020109150218040b0a0302041109010e090f0c0a03180c03140c03060c073207 68
    0x208001c1041c0440c502152150318041001406030801000804905202088005e503504058a036a42034142000b51101028079084511094040d041d541e00d5108109680c140ca615803901101c5c2c1030161480d8180e80c00091980401d8402040035200181103402ea40304175120407540851100005d20444066990800c20700e4108034001440c01c5080d81e4900c80a078000485041789640d8000380c3c204400b410003d00a40429482a850b40c1260640d05500000006000d000b108034180d180c82284d90a91160b004101d00c3c110308102c060800d40f8155024481d24400100300f140e960f0383c1daa0220f01a261048101c010070341d008154100c455030000490001c1107000c807443c0e030052420b600c00c2d001d890030141001074041404100442440c0c041e5102c920034940d64070b042c05039144540341c1055241c009001c1161400403004900302d07624000614100c0440004015100c1d40d51071045542c03054108640c191003e960304404180d8242c040303001000c0103940c2d541d04011400c503110302c4500d03203c1c09074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 646648983 1250 646647733 646647769
    0x5120702010c020d05030f070807060534021006030803060a05030a0510020d06050603010e060f1e15071202030d0e0604110603092109010305011e15111b 67
    0x2520040c0ea21041d003401050341103a000111000509050380395004e80043d41c1106440001c0900c103101c000c0b40944030061041c80c0500031950b0303507201c008a803031071098044a009811504603d080d12040401443c5014500c11219004030111454040d1600c6510983c3c09440c00014020b0350304203004484094401a00100090911a07a034903503034032810110890000d0b404501c0e40e0020915402c0000181001810325440f0f503103640101d80d60b01ca09888081c0b00301c80d500300c0442d0314140301038518a80341c0c40f200b000c00c0201c190410711135040b0002036030070903002c01088903100051a005445c1107030300d0207600454488400d10208000c0f41d5800d054540305512003010070000601d0300300e6407040260251110b90b169141d12090504e002151021040c0440170f0203d244618040000a010032420980c0d06001590361030f8255003051540750881621034044007070501681c0204459105000e000d45010404189120a03c41c24818500c9071545482d07222100c002c5146031070510724543d000c00c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 646650233 1250 646648983 646648987
    0x110708060601050a08090a080a170a110d0c05120a06050a080a081801030213030b070914100e011101060308030106031a10110106080a140106121731030512 68
    0x107000290660040a881c0401c105003080003c080340c0007440f030050120360001203642c4a591000d8013411000400380e0081030034030060000f60302c0061901580901d000d06c045181e01c0c06031a208844007500b91400c0403010303c1000c00058104490a401903441035000c6540058001c0c241002c01000b000c040d48809469030100e102078000c94401003c45001c007a560800260340e006140041e406809900c440d0040d9809102000041c00100540c051040000380d5960728026211100c0e001d140f0030000301241c0142c001001004104e004501c150442001410034a4100140801c01400d4450b82e0308200e43ca09004401003041c55054001c480062508000c8032000289001c0401e078240485102503007040342c1041c891b55000d0081d40984084d02000b420760b03034181060f0501e0340c9480148074042c98958a0700c1e900081000d49444802599030340107102c2c82c101c0340f2844201500c0d0308000c0414212151110042c0e61045100c0f4040710460122242e41805a05d941085070030705a8a4600352411001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 646651483 1250 646650233 646650241
    0x20011a010c030801050409020a03021242070302092116050d0b04060e0f06041b050105030c090a0b0a0c1b1404050c0904091505220b2511070806 63
    0xd0b103c1810340e001940e00083e0704070540002904810540d1002e0b4203d4107900501039200f001003580900c2c1045205403000c5800a4210000800c00d160340f0704480c590402400c0010f00c03001042da40c1c202c2024600075040400b46400103108042203200c000d800c0d1403000058070242000c0c404014503450b9096070903045840c100100c0c1000c0e0703200100510f0404c00400003000c00c00240e0000b10741c103840500300c450b042c3d054032503956115030942d003e958441d100d011841c480410a901403003550b0040c0d46031800c0da06d440d103074140c094002c0350110358080000e0f10045540a04030f0080d07c4c8003102940ca0000710304c2c0c2810b00c2800102650601c1c4541410001d06205003034045a4820121006a50028580c0d071000b00c0004c0c140900110701d540542424800313018014914a4152080c1040c6c40802850f201c4000340300010f14540720007100c10100d01d0710040401d200c54006503100541c0300c18a4104801a0300011030300c0903030542000400c00a0507200c1d080b581c00c03c080c8010713200c140007c0c800390170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 646652733 1250 646651483 646651487
    0x13140a1502071e1a0a0b120a0c0b03090120090906040b0f0f0102030c0d020f0d172d0c0c010b01050c0613051e030d0c0302070c05090720011a010c03 65
    0x418103049a2128004840130040d420810002090350340384a2411814220082005880a0101035200d40710b0803110f6062144045045030090b54424100d510b000d10340104502e1540004140e48215581e44210401340b44170162440704401100c5102e55840c0c0701e075002c01c1000e1401074010b50050f881c1030f5520380152200005100140e00c00c40f6000c058000d40c400403495032142c104111518041e0f017644c104259000540040003a0348103099507034480300024115910500c00b04540101524500410701c0ea0f000c3c0340d8101c035140301c9807225080ca0441e04c80500a100e00039a40e40581140000d45c000b200b040a1203840d6504a003407074503c0c9810034015a403540c4881c0230308103110703443d860050701d0100f01d010031581c440c03030200804614000c000762942e00d40301c1e004040007900c00f82c03e0003041c0328920700c01d2007101c03105079000044405140c2030030b042c4041400014071040a00071041002042840d03a520951320394514100007080d81001d1960f800d00c0c3c0964806040e05114074511a00b000035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 646653983 1250 646652733 646652753
    0xf090801140a110d02040b0406020d0512070c0204060e07080103260414032a03060106090503030d050721091403040e04080c01140702010203070e06030709060813140a150207 76
    0x2c1400000071500441d582c1c0d4203160381c071881d024410600c3c070000e000075041a2840190003100d007960266111859040743c02d40d114882c48003404ca02044505c001360701540210036100e0f5881c0041d10000c0c3c007a89a4003c0040c00100366238500c0481c0800c4010030401c00d1a054402d61005194040c001c00b1a150004038100d020300c1c025001c1c0c0c0000c05458040d1924100603c8100d1030001c0e000b00d251038041422502c1480300390500350b010380110300010450740e0169a424044032405030003546800d400b405002c0c000c1201030401c1c807c0040311020081b144a0083c240d82011051500001d050050380c900406036100e1b4690315001a00148410000c2c0103002d01c401d81c0c030030b41052601d0380c0c5450181125004044400390380c86440d61190030f21113410390541c0590f01c103256a1f01c0c1c0c1194488004200180c60004884110006101000a1011900c0b5030001c0740c04c231481e24142141d04c41255106031842c100f1140c450455440941d000c4180815141c2280f030112001c1c208502d0a00340351901c0c1918 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 646655233 1250 646653983 646653991
    0x5010e1e0d0e041112070905041404020904061b26010509060d03020102070f0b010e0f01050f040f06030f08270d0303020c150a0c0e0301020c03030103060c0c0f030f09080114 76
    0x30010440c40315501c1d0310f841c0c00000640310500582c036501d0b0000942400200410b440210016811003c0800d46007030502c12201d032040740001e203c6441e07895a0811240000007042107605a0312034400004d000d00c5400e200404039041c0c0c541315041207510340d41481c0300c2c80302c641c9a04020141c100411880e102d0780c07402d0b0742102003950f500704503140791b0405a01a1180f200c009103544002416402440075040d030142c1651210000e401c100e40b0787c004200c812100a004041d480030204a04814134682a030061016059400e000304030355540f80c8a1020704145030000351662140009c510b03521410002c402882c10380d40e203000c0445403110318040340c900060880020309059001031604100c01d0f04000d03031414590f40c650403801d0713450401c04000150003445c8841021811150341a09240f0303041c025030b90103500040056045a2039a19810050400f2106210610941d135500b20f0204e040d0312598405513009440f0301a41582880006040b000c05601c00166640b5265910ba03007002c07080755072500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 646656483 1250 646655233 646655237
    0x9040305042d05061b0d030213050405160e031509010b03010b0306040803070c08091207030203010b0301061a0a030e030307020304051801060c060f020405130f0b01050c060103060207031b05010e1e0d 87
    0x100d4040002c07281ca07502c4013007050005c0d40b0508000000842d49074008008400c000b00102103c40e5a035030078041518001d071140c0c0383d40c41d80c07006004071241c410b0710034900749a00182141c40b0000061100a00341c0070668100c290782e51598002c2d00745040900420049141c1174000b4a080c0c038040d102c80c1c2c800e000c0502283c0c200320489012400384907040090720140c103002003201d4030b0300200900190742d80040348404ca010794200b12100341c0c10714061180d00111103c85524443c072682004800c1e0195210b44442400e241c0e42d46082e01104400308040d5111701d000d60015503441e42400104284c4141403514007248042150051000d5540300b0b42c1020410f512020110740084d41c0d40c01d07030b03010740102e4001613044104030b4036840d021501c03238121001c10004004200001c11125004403005d204188030b200c42d90348111300400000f40e080d801080007501900c0e03da400d042103440b0200050b14100c00a0300c140c0c2d100c11612019003028403184500040b80074404101d2a070000c01ca50300d42c1035042a00301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 646657733 1250 646656483 646656487
    0x7020a06051009050c07030207091802130204090203010308221508061206090a06050105031c08151503150409030f030902190f080d0f0903150b09040305042d0506 71
    0x204120038400302e4405480c5000083c4031615140080b40025004000300f070340144950503002822101a10400181340600074845540120540a2110b010111007942e20015400c100c00181182280b0140d4040d512401e5401d40d074036102c25087c12180180c46100c08070070b00b082d008000011420024240503000b41c1001303c115070ba0100026642d00255507901124010441004114036012904151305441807604102c2ca903205c00c00d01d0703560450f4804001c00c100c9441c0050320414041d41d00540e0100300c695807101c61309100400300b14144983c0600240608001c07050016064540c8130310704296034182d808100c3c1d150700c0d48000308500605c1494809059031307050001c0540d182e0300b900c40d01c01400c944504442d25030781c0c0c1142c007502602d031269045500503020b504000e24490500e81d141466540c1c0c0750300000c0d05680f01e0700c1459000300052210b07550f8070300d94060075489003503100e803183e8020344039962181e10b0100346590401800c0404500c80028030340803803110985206003401d454003511700380c2e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 646658983 1250 646657733 646657741
    0x31006030209010f21050a02091305060a0302010c05120708070c09050402010905061305030a0b0109140403020706140c0d0f02070b0f3103060b01120e030a0c02030106051203130b0307020a0605 84
    0x1005d421141d2120610310700b03013010000c840c40250001c0c545010203076059202070060f40308074401c0303e5042d1840d50703002c03170526010405584520161200c8502807070543d040702513116060140c990020038210340713a0703e010410300c003440b80c00c0040710000d0030701c1313101400607181c690300007450011140605481900d010031240e07031011140c44581c0280c08007408a5800948500382001081002d100b00740d400b605007014003654a4501440030b002d00e40c150000e241e10303400d00c0002d44001401e140015080301c000e000c6040e40e040c1c100000c3c0b0548095480b00c611203c038800c002820b051958101e14500c40041099461410344141214200498031152000c0d40f41c1e250071b114001060003101d00040700e60b695022003442690740c0004010300090f00c070180c01201d91403848069441c1d1601c1241e8981050040300000c1d40141703503510807244000c000050b000d07210b400081e9460a8030010711040d50000c5101d8a174000c541c18030704054800c18030002e04624081500075500c00044200401080d10b50000c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 646660233 1250 646658983 646659017
    0xc05040e0a0c1110090605160507080304020d0f060f050a060b040302060c1005010e150103182a3803070f0c0507230a0312180b0f031006030209010f 65
    0x41c901940c0d04400fa1985130090840050152001010940d081c620340008034000902c110444204903210ba02c0b124101040c607140c0000f40e0704000d100b039800c01881440e900c00580141c07007000c8443c1c07044030000750240001300014100c030002040141540c2c985802409101d854800381c5044075812a1510f0ba10300d6010111350401501c02048454141801e001051205101c46000d00c01c03140c0c0307804141101d001c0c4004509581080c3c45082c040c0d0241841080400c2d030848131300703190f0041400b940012440048080e18040c8544c2e0006011215143e251440482c40a4410300102000c1410440c1d00c0071400c801c039040d200c0903008005101030462108800c50040c040c9001064100064841e41c9660b190007112090101022105420000c481d0000d81d244c580b42c04810399411141d4081010b4200790f0a03100c80a01c0c0c0e4140311591910000080d40104038070042c408890440d0401d0348a0a114205c81c0c032078840303a00702c0c03c207042c014019040d0a0342c1c0150100a00d5215191010b0041d941c0c401c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 646661483 1250 646660233 646660247
    0x810050f1501200c062d0403020a120618050d0311090603073c14160b09011e0c080106110d0c0618061d010e0c0402070507080f06010305010c05040e0a0c 67
    0x1210b0304000c01041401d0310300014801403d0981d03180720044c1000c140464595803910641c08002e50240d05c0ca0304c24028102f003081c1c255032451041c1c00008016041114102c0204503100d0121110b41c031001103d031b8030581c1802840c401d004980301880c00c0001d000001001d0307010007070001c400c01c03500201071906200403407035480041d051069030002e01c19590f007505010303440800b00480071641e4070000f82d9203e40603008035490841c100074802c4581c40656102901d44401404000f12907485415001c000c4074103e01c42405c510000f42d0008000c0e903040300180c114030050344410184003015084098a040215000c600e1001503c0c203503004510519202000700800a140080e0306850706448081040c254001d10300d0101045600500b401706075041030036110101c0f010840c94004000100e80303428250041d015503489141501d4549072a0016245420342241e4441c405a101c800100705000080c89264070300251031920910701400d1500ca81001c2d074003c1d10744c401542d950941251141c1c03003202c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 646662733 1250 646661483 646661503
    0x2060705070f0305060a0501050904030e090403020c040218090708040309030f051603110102120a050d021c1104030614010e010b07061d0f070801020903060408030406060810050f150120 81
    0x5980c00b003180e00c0382445907840c0805c4990800891610001203928903001c03801e144625030554070041d4002800003408080803002e4012800e500c68407000c1521a035881c0050f0032000c540d11501d607250200704040050311100580b400051002d05814000407950155106065079004044080b00740c0003842c1483c075012183d006150f10301c1c1180404801c112070603030198030a81c0241d0844100c1d485e03051100c5461311940c00d100021500820034070340b00c0505900500141010100c10010100f4141c1002c6c0545121955482070a40001003d104000a40c0714001042d140c61250b4072056040c034a614041c0503042c02140340c0480301068a00800c0507030f801100e44180664034070040d60398400704240d55107101054041d8203024241c00072611810510039070f40c1c020300050082035030382c903203840741e030f56540c806002500c005c4d1300c0d0300010510110411641c6605050b40400080c030740342120701ca8005400c0507250240d40b4030080781d41542a0790041041445911004a021035450400019403602d1000070b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 646663983 1250 646662733 646662749
    0xa03020114030417030c0909100f060e0111070b071a040c0521070f0501020f0f0c04091e0305270d02120705040603080408010606090b03010b0a14070c030c05010e09040206070507 78
    0x410018000c6483c80500002c12080c1c88d070000030785881c6020804c40c3c2e03860040365050001c1035804c01c0160f11511860504e544107042560f00440c40b8501030b810f21089030002820f1078000541c031070401008003410804200b054800340c07164101560f40c001d201d4110700c1402c0c814100b000c603c00f08954001e154002e50b8018008445034103550b01450a802e004902ca80c2d40036000d1064403002c9e82d40302041c0d401d2001c030450050041004250104001032507140d1080d64aa00120208000b80b40c00114a022641c000d407145507c4403c880e002085501d0080509507107180d204041043c0c0383c9521000c2c0e09000c1c0c0c1140da98141d00d5103902113518001c1d10b50302c410303801814000004140702c090002402544c1014009010054550702c0c2070310641040d1050008101040004220780c08000d4007400c9641501d151289041840900c1488190481d0100f03548a0894080410802920340d070039200528003030030031900c68402c180002d00003c000504c0079010b40c0740002d641c0208901440310740060300c400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 646665233 1250 646663983 646663987
    0x90d080417060403030e0c06040519051002061012030f12020f070f17030105090412050d050916091104090905030c0a03020a050c01020a080f1305030316030306050a03020114030417 79
    0x1d045056803810b040d00d058001c00d10302103111240c1000030941d140d0094000d44014545450b20041c4031075001c080e0520200c00104c0742d00400e440d502c150341524484402d90080049003048030740d4041c500c05503404076035040369801580b00040d4020000c0e2514031520305000c48506903102030078001c0d1140300001007140d000003a0f01c1c4104102010a043ea82d03000360422002c00303900000c0487d60b44000e0142c523601000301400940090211034032450561801d141c0f0506008810482c80d080d00c00c280c800d0305440e04270b0303071140b2028941860143d0080c81c42142c103001410001d281580720f8403c6c1d0103a5042e0544885d0814140102002120702d0203415108581821036682002500c03980e242c4070407102c03405018691944e56100194107000f0613000030515150400c4208210010781c800040d2a040350082e181c00101e55600b400070300042d2888003480041002d2a24009044900d2904200e201d00400300303042c40541d83c4114441c0302545003880b040c1c4d594495090074840303590110a589045100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 646666483 1250 646665233 646665269
    0x34080409060602071403060f1306060303080415060608150102120703030605180108030414031509033606130906240c020127030206030c07110a030503090d0804 70
    0x100358000030495080d0350a80314030305c0c4c9991012030454440c03003020ba4150f1105000c108103100000c0e600e0b0300210300741440140907070141d54100903a510f99100350080344c0004100400d0010030038103c1050100c0c8481007109505054002e0102400500031004010800c054440141d008008004e140c1d8102848282c0340e140500e4010b0140503540500740c016060385c00002c0001c0a00504035068418640c0914142030a00d043c1460340c500007920250f040c8100b9107040e0555180e210040c1c0100c20007000b5560300c201c1c200000f0100c0030401245030100d49480c00c003400a0400c150001000001210000d50b03030003c48400e012244460380101021034504800003846641c008043d60440c980c0715102c100181c141d16040e20417080000e07001e804600040905100260382ca006002c0034010000c0b40440640c40e900890100d8000326020000b00500140380d500388005501c25544100741114000103580c110758a49407640140c00d6100c2c0924031503a2060b08004000040d07901410b5000414190070309 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 646667733 1250 646666483 646666499
    0xc06030c0c010c020313051003231617010302090702010e1f1401060c02091009020d021b06090d0f170c0a0e0f011d03010204030f05030a02010b0303340804 68
    0x100c01040d07000103600c0c041120b140240040f094500c40b1981042c0e0030711943c584010f000b02d89055414120030181d981a080c90a0200c402c0080c2c0f404542e1800f03685280b80002420322080b04484020050105001110b41c545202c810b50a041d00e030b042c0c032202602d4484060a0b030141441c4004011503000320006074440324059010f101c2c6082d0910028030041c542050045160030b028040c6100092103a0422009810495805a0011401980300b08001da82c0d410201c22600700c000d000711140e40018004031031200f00760755a2a0500004060050750815221480c3d82d010100455420b019884103030006940c021540d5800e101d000b0f45640d183c502d02002405d1040d401903031404041040341840203017034246109c8182d08100d041e11441c2c910903a080010010f10801485640d1642d000c000100004460b954441a080e201d07070004c40d166010b42c040a1b00752000c00011038002e62080c0072070107208401c8011006540c0c01310365850350307102d44405940d84422101708040d040d003000240c0010075003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 646668983 1250 646667733 646667737
    0x60b2a01091406060105030f0604150807330203030112050a0c0b04030b071706150702031e0622080306011808031308010e033a050f010504090c15020c06030c 69
    0x201c0d01c2c106440c19682d80f80700544060200340c0300c88031001e00c1000000c18605003944411698401540101e101039583d209052800c600c41c3c00c00841005e1140d42c01070142e81d40103103401c1104950884055101010400079a81d000c14400c076804e6150540345c42c018800309005030188160090907680c1d445850340c105403151303402407004454840811000550b0284698100a405140c49001031051340b5880c0800c03c40c0030480031100c140c15001c2280780010b036000c100550034484402102640d6a55040c1c0d01400c1140040604120705056170306041104965801c2c0510702d0b51003002552642c0352580100c80441004203440740200d52480003045c12070b400005030407402d050000c1300710040d458003452800c3c0c840002c002c6005030f0080c80a648100e81001203441c2039840c2d0381c0003420f5180740e210540c413901001040e00412954500602c44020903c1e8400303805414107403030038008070305560b0381c1d402104494811140881e45114070034000900c24000086041d800800658503800c000c00e0740d0f0a2a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 646670233 1250 646668983 646669013
    0x70602070f030e0303070201082d0a0b0102070812040303120209030124050d17030a0b090a0606020d03180b060103060b270f0102100218040f0b010909060b2a0109 71
    0x1180020240d2045032400004a401b420b0b810b0f0358540750b03512110801c1501056103256040030100000c0341c0c40c65152041541d43c03140f020f0801c08101100064006810000a9001301025422520615a003100030004a40031a0f501d450120040340c2d210418600900640c42003945c19422300400d2906003030030b1116040400000301c41822465515420008014545100140100c804038a0400702035828405950701411520001c00c80d081d0010000c2d641c10360403100300c00b405070707142c200707001c1c0a0341002040000c080a003030801040d40d40d200c1c50b5002c5d402e400c0b4010a4150400000382040c1d1280c2c12050080c80080400350729035000405e40007d00f501c1c00030710410309400070f1600c803c5180c0b019004070f240d00d041c1c014000041c54045000065800100441e01e440800c0c0c138203268a8031540704210494046000028985e5030b603000052850a060307000e0000541811020321800e451201100c1d20007190b1801c03043e03408081c0c40500c4415400c00c240c00d0b041c0d4641404103003400400005076a00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 646671483 1250 646670233 646670237
    0x5160f02071d06040b03010507020c01031515050a08011e051e03060c07020f1c02010c031e09141915020106120b0103051519110d1119050c0d14070602070f03 69
    0x1179900d0401d060817203c08644807801039001c06d20640b1194040d5014181855201b030301c0740000d07500c0e40a01003e9507030796018040001c0000410f01d840c241e0024203540503299006d888414904141c1d018000c5409502a491288041d03000c50251044c82d09160003601e1409020b03543e0525010352903001c1c0c0d0300308210680c082c3d141c440d2002401d141206003044a0f211078042e00d00d00d80d00940044401074169035049041c080241100704500703501c0c8045520166a50342c51840160030035181e002501d03401c9111a005d155405a0400e140041150350320039668612030002a01803682c004901405c85503004080725103d40306a0401d200300303a01e0b200e05a90103142240c83e00c80048045820105044480041104e003045c503034100704080d0303008495030a00b02085c803410b01b4200c91640b012100c100f2a00680c8280c0000c1d03004c0150b60403400e01281207034071b0410351304201d80645466202d085004da00c000704201c41310440ca6041c0d00106031000250020b0007151500c3c1e041ca0300d00c06a004a40d42900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 646672733 1250 646671483 646671491
    0x70b09030705011e20121c200307171608010b030c0301030f03030f020d0c020609120d05060406170607080c07080a21020a090312020105160f02071d0604 67
    0xa07055000355500500c2407481d0551220020003c0d000310351414408810005e80e0601c022812036040c0e00700188007604029440f11641e5051214180104600c0ca15400c4521030a10b10165641441e144902484043c0c0010183d0359644804c8100e0b90600d029818800030710499042c070004054181001400d8480e60315883c0d203c1c1d0300c40c1d0003101d4a000c121820800c200301003005000007040c107a9217050b0360784a4180420000305002a00c4140d0f04000313580d50351303241d0b2500d031400d850b40c2c1004800e030426102000b825540c40811000011803003030154814540780c881c4081078413038031103908c40002040550440140c00012050f07a0380c80b00c400ba14404001155540070540c2804c4a00c00c44121543c06200d9a1828407951403d5a00c0c6010b21042d07952260002c0d201103800c0110f0004080c4000c0070b035120b0303a003c2d0441c580050014040340b9800c0840e0700d05020801001d0030840c0c4035042c2c01c0c590500d50303081940c0f420101c0c988000c030b401c50310303102101101c203589421101100d903004100840d8280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 646673983 1250 646672733 646672739
    0x80601050c0a0b041a010806070507060212041a01060f0e2725080106050a1110020d1e11030708100f14041a060f070309050a080d170f060f12070b090307 67
    0x217002c102081c0660385031a000040420302003406132000307200e01840b40d04058100b0f0405803147d03a24623800c0b5029a054880e50310400c501031400040203000d0b00850420b09020100e4840c010180b91009a04602a840c8101285211404030303000045a00305450b92100e20716203504224070249010940f449100c00030381036807110601900402d41601d1940d55140d0900d9003000084501645000403600c2c28044d0b03500341415444580000c0c001070f0035090000c40c001c0c3e80d8281e548544a0103100c40d614007407030840481001c00d10b030317800c4076002211403500301041d0701e03000d00120b40b0080c0350b0300000e001c06e1002800210080b07925040c50340c918003107070300300119071500340c0e4001041480818203038803e0080207904039484009024000150191a202003225200e10100f412403095030007890166200380064041e95500110040c1c100400c0014040c550505810066511101801c01e40c468820800c2000054403448602501e40000d4000c8492030f40e510b4500d50b140743d21000d405406030040340404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 646675233 1250 646673983 646674023
    0x12d0b151209060610030218031b030d0513261f060b030702120a05220e070908070b03060d0f0c05030f0a110402070c0513051906080a03080601050c0a0b04 68
    0x12841944d014000514000c010700080303009501c80d06012106050302400f0070741b1a00d0411440e13100c0c1d42c0b00032074481000341010805180800040030403007008420031504581818403c10001250300a03560400c010008801030f070315140c2032840329034061065520f55203840004006c0d0080e000654a403c0000036141c0e03a040b012440201c0d441d03405a401000c0800c01068881d00405400000d4540700d414600010300c2422100003100d0001d82d00141d0307007000e01c00030348040d2003150002ccc958240401220716140b00c003901c030f4080d40302c0e03200a40c101100240650b15103c0c12850250b0744040c649030040901d2400c6108410b50340140c03402842200c07151402018001001682d554105403914540403441040000ac2e521541d0112400501450300060544500e509940a20040a000f04540c901403c1c0d100c40c0030200620241d407075003000c2d010001a080420f503c03061b01e80514182403155074802c0143c4891084500714070740740c40340000000c180908000741078007a81c441da83c80a03c80740c007071002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 646676483 1250 646675233 646675243
    0xa03090c0909050a150b100302030109060501020604050d1101020912030307020d0f021908041a040e07091a090d0b0901140a05091e1c030b12012d0b151209 68
    0x1c015501c011440d1307012406041c80010b01c040c00200103d02d0200c0d01020801101200501502080d008001400400010302806028100030b20043c1244e25142c1c944695510402140b0307001c0c0035100924100304003083d01140c031123480c09014200c1c8001030340e000c0d0341d0b240c0c030440d0700400600400c00600203980c0b08240007400b2003d154000c0205164072210101802c090803030888400300c08003c00140800c40319202515000407814103602d5034941440b071000d070386005022a0070010000e806100c4c0d207942d04542c0b091444d05c80e00313554071031920501082455100c82005041104604100000750788150803010044110b1840c1d07a050381c07a441c0206080c1c1d101510564225004101c241001205440720f401c00140b4520868140544042507c5140c1d2114561407001940b40c000400c40340c10f0200c40e0294000841000304080308201a0151902c1d29400d080d051802030300306001562515a042350024060041c000c0e100034203414010411a80650000070184800200049003c0310200b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 646677733 1250 646676483 646676501
    0x5210a0c08100903081f1503090201140304080307080903130b1c15141801031a241003020705010204080330071404080a110102010f0c020a020d05010b060a03090c09 72
    0x5034050380b511441d408910012001d011810340b880c001304d0015000765400011f080c40b00d00750f100040c032010380340001045904203590b0a00410010014000000d80500c1103e80c029800d1501d1011a02c3d103610040c210301c0707080022900b034010407a003c2114001c6100824207059100e641c41c4100510540141c141d031100700c0c0b04401210800010412541030300342418070300b00b00400c812800d100d0955075600710303002a04162111101c9120701140c4c03282c041c2c6940d80180c09201840004240c90b50b600098181d800381c000d01500400c09420b010500940540c0c2c10183c0c40b50096403070f1511032880e01d542303400a05030401000640d07030f0440105d40c1c416400b07056020a507038580c413076555040780645000c41611443c0c1080e4a040000040d4420705200224249200d40300070004580450002400c3d51045501003103228a44054503174000d03000580301001e02c1e8107440544400345075080280c014503c00b08441c0c2c0100c1c0015a1000c51649a0300c200740e4175105901620304240c17250401002c8441c221 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 646678983 1250 646677733 646677737
    0x2030d02060702072c0604090206030406200f180307150806090703020a05030a0203041b090e0607092303070911040911091e1201020c030703080f1005210a0c08100903 73
    0x405d00030340410310b000c06500c44405000032030898a00e6011504030742c81114195021a59060501d9445002c8241181d10040308d49855003042e110f00342a0030a4420742010400010880c418415a6181804048001c100c0310081e5040352080da0030203440140b041356500d01c0b8404000009012900074800c1d25008405651980d06541d200300540d0001d42c000790056800100c0b1083d0310001e460b03d101c5590262002080c003042c800c510180061400b0005040303242401001c02050000b99031808a003001d520010352414021151070011a040451540107004040d040542c404425484403000300201c654a0104104c000404913007103482e80501070342c0d158880c01c483c1003032103042c400b03d441c0070340d58000074a65101e1103170b84018a80bc9920100381300b031503504045a82d005154202c2101a442903c0100318149442e20250348140d011580c01018460050305403840010804080c80951b9500c00f44121070b010600d07420245c0240a15101c0c000c081d1040c0d81c0503036803000c0b00b0300404144980c55 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 646680233 1250 646678983 646679039
    0x102304050a031b0501020a0507030201051b0d0c3e010e0304120302030903060702101401030f0b071223090d02060411150f191409130902030d0206070207 67
    0x555040f100079500f0040c00101e9001d102c040008680300b880145049920f9840d019600d00c102d213006804d441c001400f0788400e0140207580307510101000304852031078004250001e08545954020780f201190740108004010801061054150300d40b040c1c80e0b20905041e400309403d040100c4094241c0f80003d22440d11600180000c0184100050443c8040ca00c28010341c0c0c107191201011a242010403940c3c1c40c0140c5c481c00d4040195007842c8660b0300d25101c0003118468a60551711060403000440c1c0d80100003921000000c0c030001d02c500c0c4006410721303080c541072100300030102c241c00c0c0c880031144c600f40c44100d004002c103450316000501c00122001d103801400c9160b6a13501c501801800060300242c10003505405503600301c04410003040c0c00f9801c4a00c0382d4482003c03008100b54160b218102c1c505108040c6030301c44500580d94161148644100d0340403101c403140100e080b010b080062402034040c810003001d00b41d82600801c06900c210907a508a40030301b552000c44022006810111000c21444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 646681483 1250 646680233 646680253
    0x819020904170d06060306061805060307090302030604080703080601050403030c0f230303041e0b010b03100f06020a0b0708130b0406240914010608061009030510230405 74
    0x4425141507005000d0369030350610b80344204603407020340e22400407000c0840c1c0d0380c0310910002c0e070140f040c0b00103030020f450801d0342d81b03480d0541038903401c51500074144035803400320000714010310881422003d5603015050324107500f4645080ea6041e000403800f1008148074200084840d441982624100c03600340c0d031030006000c41d513110b10185501061003a20f60500c8264009d603010100c001d43c0510701c03501c4004681e81e1409040900c4907501040c5100c2903a0b072140300c51804250b821001905480703182c8262582d0f5191108204075400c010340c05075140d03501240c00018401e40104641e0800c600400d0b0600d03039a9a0000200c65010044403500488000710a0700c1000c1411811040d512900c01e43c000105611220700402020142d80d032440c404c80c00e04030050140007060300480024030300c9801010340c2d135410001c0c050304800b801454980544c58218040084030301c1450f88800441d00301d07081d03515041c4103200800107005090b5100c440030305042c4d88100c2807402c070540e0314800c680017005020701e501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 646682733 1250 646681483 646681489
    0x30311120318070e0903030115030905011109090f0105090703020c030403020a14130c021b010219080301140f150a11030c100507020604020f13022104020109081902 72
    0x10011051152091a60321008644000c00450188080c4105a0b180400052840e850b089a80d04000d800308045020b10080386400400e49055034004c3c1c294000785004440101c00a16000c00041d01940c2081070009001c00c1f000001e00340e0306001e03920688030381d60b0210030b900000703000c1c868103030003080b501d0000d45094400c0d0301402000d0101000c0d00d19165486d00050309005044d00014080120311064200614120311280c15500c07150300c0038865038800c082c0c013a4407405180030f4030a01020000c1c9440c15a0703c244104140c1111f42e5140c602091024100303294141c00c00d00503414607040710300001400d8a4404998040c2070402011034020658643e42c0b58415081102c3d054140b040c0f03914910318214060010f02002840340f0000c0c080c121040e11800291003010b44228150340100080c000540c94156a4206e07004c0d0558120b1146606580048000d21443e6452800041c0c20340407404000142402c06005134002d0340c40203045626004001d46030030a461140310150b800d05241c60040c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 646683983 1250 646682733 646682747
    0x27040e0a061e0501080c0117070f050306041b180503011a13091e020f040603120f0e061c06060206070507061e02030a05040309080610061101110a02060924010303 71
    0x4000c507029100000348840410b81552405c0e00518075640102601c50301d1540d00812003041c544000c401c07080c460401804c05800c40541c41272100402100000040958580e03801c510000741c5202080103070000400d100034003041c1c5004101000038462540081c0303600e01401811040404401e100d100c074a012020403a000f0711441c0c101c000360707403904054004071307000000c03160600c0303011000385810b080305204200d1822461b094161143e46016130500c00f05603d01010500a801c50030000489400710344181d50142c452000c3e554000e200061000e071b5180c02001c4c07614840b41a900500c08242c481070182d0301d40d0710403a0754100003501030000c20040b41316a041649124040d04102d0410905030161074142e9004841800d0350b42e407214188010564040d1000006000b042c01510035824000d0301003c0c02031652184208000d900c08054142e5175082d8010782d9141380c0414019602e44490308065102d0038100c5032129140514800c00889445c00e5102e00510740609001c603940343e0856900755186 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 646685233 1250 646683983 646684001
    0x9090a0903020606192706030f03081b0304060e160b0703020708030c0d260a060e0a0603020f1e090109140109090807150216061e140103110607050327040e0a06 70
    0x2106c02c902061010641c1d0300c0341d8806036001360742d18202440c06040242ca0705001510315001d50f21600c42140c12403003200c0c00da035005a07000d80041403e0f20b5600c01c4903d4502d0748a50a203680c1a1701e0000148000e0000052207002e100c1d409031482c1030f41d100c07105d90305c80c00380a80103a0b883c1c0010a40362032051065205010312912030b404000800d0035001d032291280001c50300d401c1000c1c0e4484050003000380081100c0c0e400440e4840602019003141e020a03581c103500c00610303002d11100078411b4a4002412440802c000c8051f1042210f581d50340740341e05c040c200801100c4450b028500000c221a0847e020f41c00007a5040050036140c2881551941a40b204185100c41d019034203003ca0300410754080301805005000702404540703200030a0083c1601c400c42d00c55848080d00e8611400441403525040d181125000b0b0524100c118004002c514280b140040050180c00005044080351400c8014200e40c0038203041404050070b4200188400c9a0001e40c205006502416050001a459070404490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 646686483 1250 646685233 646685279
    0xa260114010c15061409091b060403061e0e070f0e04140d120b18150a080f0a060b090601020a12051908060310051b0c0309090a090302060619 62
    0x40340029110700d100c03007200c01e058007001134a4110410005580404084101030304580000362402c150311050360b2545aa4005820b11a44d00e65980c040d50340c1c88259001941c001e54140703c03041200814110008546190401080c0b80c2a13151003c400002601c0c01a54001c5404807142400c03c112a001c3c07004c018001c03038103c0380c1880c1d1118103000c01d105008500710144c9811360700503220b04000e810340c2c0d1003100300c0c0c1c000c82084a041c500c42205000041d04a100d0707800012002102c0c0011422000c00f54001070503500c00c0c0c0d000000031540010340c0120440c080c10701000304119030410000401415540384c0e0050340160001404074150a04084842c42241011850811003440424400c51400445404640800100b008900b4180084a01000818402c10a501d0301103c4078125658015880c1400c21001c108000000302c10000c8544555000b4000a65882c05000003c090700940000b00d0060080b00041000c1e8148402514000001c07089203502090a140a50b006001c12003c061a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 646687733 1250 646686483 646686497
    0xf010e01061719090803040c060f0917010e03070b09010c030603080f090109080f0a05070f08032b021303141203130507030212060919050303070323010b0a26011401 72
    0x4000e19551291360f0210303100b114032903220300c1c003400c02d07094211705640440180141d940c840c1003000d9002021030181e071030b601d442601e240d0218890324010070116440c6125844001810000d1040c460075561084007060000c4c8043c80c45141c040b0181c50b4075100040020009201e2081e0b0760503584080c00713140d90107150008050765201e0155103410f04070f412002c0785030400100c890501806107c00c0b4090003a00c00300c06803c41ca0411350035a280700d072111212071460b070060783c0e01c1e802100200310101c50030203440640d280c0c0901c503e82c85050510b07100469851700d448030425076005011410b15403005421103040d0a507034915408403030142c18a9012904d900510a020006a0310704d240041c1c40c0b102c60b0000d01c024030304000981e103459540c0300c1401c0b048044c40400c00c00624000100c9a02c007d5a06d00800c1c00d0803100607100084400281101c01d52490f030001052610401d4050081c0d00003641c0c403e141d9494900707605000c00341e038264901d000600300c0010310400d207968845040424040c58104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 646688983 1250 646687733 646687771
    0x21002010227030f011a100905090a0203041e0309090e0a1a190908030412051204060c1e08070201150b07060e0309180108060115050a0e03071208030f010e010617 71
    0x181c2103070042d01e1146c4181c508404008001c0c200391040f544007504500b4144905410007001556034600203198030304d103580000000302001a0400803c402c04a0000030041c0c61003030349000760195001c2d0054201e0300d0b26001040d14034030000148074140b1508a545071580d400034460b000f80404009008180c00c0b169408400e100703107040e201d6120404d004210f45d035141c0c20035141a000f4244441d640d10100031051012a144884065901d034000d80d001030005080c449c0c0034801e0f50034005050b5071500340007654004815298010101500c01c2603160300810500d40301607010019a03946000c1e03544500c0e0305100d6100000d240b64001c080c002c030080212410840c0311400210300c001d45902161000d01d41d4001003000c10010407a207405892465410248030990310740003800350007050403041c00c10500d9001c0e0700e81501d00b401004050200403003003030f82c5030f805070500327040a030b00c141e81c69a00a84000700000301c011100710381d5810b0380c2c20760350b60120303407070400c061111910320203801946541940c12a01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 646690233 1250 646688983 646689013
    0x11010e030d02040311060309031803070b03011d31020a1a0703090e040f0b06130f060501200d0c06141501020606031c051c0c03020702100201022703 65
    0x75000e0003200c01da000da55036045143c40030740682d0304c04900c1d0060a0078810300101c07544c00f106440c901c402c2c003042c40a0b11020100003902d0214560300850612400100100e0100100d006801001080d00c44660250301c5142441c0c4811407003010f00070414903a5501c424442c8000158031178160f00050444d20303001d441e13025402102c94541c000044119001800c1c0007095001030a100c0103001034a075180325490b180c0c6a000100c0c103100d0300103040d21300c2000080d504c3e5490020391460001002d00c20000400d4241200b030061415028075804030340400316020b05009003000d0012070030800350180035003460b204010755011052000c2101d41507140c050003500f640034182d120340b2403005648400004d945540002e42021400783c000c0f8002e4000e401100114131001c00f4040b00d0241a14081c0d6547c4021001003070440c1d421070641c010241400314205126600d0b030003034120140202c0d0120900000b01e441603080344903a80740b054256a44100c1d0044441c218031480ca100701d400381c2038a040e40d04031501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 646691483 1250 646690233 646690237
    0xf01181509032a03060e1504080441031c02010b101d120a020d06051f06090e19050f04030e030309030705040c0908070602070603050a02120711010e03 66
    0x112000804004042003440141c40c02044a40c5103100c103c411602c860b46668100c0120380805081207480c0c034104100203008110aa01c51210720002c0710481c145032819500030745c814031400109240c10f1351940060303a03010305c440030300c0704013203061280c0c1c03200211601c201d04001204c140c0c0d26004900c031502d1003401100c100381142a0b640d00009210356400d0401c03441140c0720440c1d100700514040c03088446500e81030080142d010844100c003444d200b0164041c548003280400075046490a40311208110349600154080c2c6415012080068009807283d00e5121862040000068801d1020803100d40840f503513a0b0001c00032030080360b0f01c0802452120607900e0945080180500004c104000d0552041450490600442c051450710705000006982e40c516402450b2180b45e903199042ca03200d01800c0244000c016182c1034500391039680390044e464907458818000803d05001c009603005045100312150b0400101106001c1d80307814200b00d0b99103401c20031b051010341d69114902c0302c207901000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 646692733 1250 646691483 646691519
    0xe01091b0609060e0130180c050d0b0103030c0305090d11010201060b0405150d02040807080d030c022107052d1504050c1e0907110d020703020f0118 65
    0x11031080320900e050002000d2440952007070040024081c0074610983c0d01c868500c014181410401d0001113507210f098849070001810048041c2c03814850740c40f11103849503c01100d074000d4a04251032580e42c024061039810a04009141c00c01c0e1070014030010b800341c10035038503481c060304c0c01d9414000c1003c0402ca80c2c00454005880c441755110609000c0d43c2c0c24051a40074100118200d8102442c05c0041901014480030f55400c00700c001c164100300b00000d84c103460051071010112603689980c0c0d01d0041e02ca1075040482c0c000603092040c5d440c0501d00001d000759030707410b4912801d410072031800000030f004e42080c0011152070160344201c061103170306400b000a07140b002e03460289030145400b150524001c858010012111469002c000102c0d80c040303484501a8070030381d0080c0720b0140c5403c401140c482d440201d65804810039061040c1c884e804050f0300c580005800884581001b00441640d641603075107c004d51019110344d0310402544503410850300188285a003407451501c60ba103420403c543d0013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 646693983 1250 646692733 646692773
    0x40e0c131a03220201121e0603081201120503040b070f050d030516080411010c0519060207060605030a05060105010e0a03050105130c0e010e01140a030b0a3204060e0109 74
    0x1200384030f8200c00702c200409400c02da1000d25030702c0840c1c81e070020b00482000342030011410b6540c00300141d44040603030300405004c90200104161078681c9001829030b00004100c0c042840458004550b61400b200d6000240340c00900950800f4500401e0305000d9100c0d04d0101c8200c9024084a000280c0802060481d13a120761004143c610b840c080160104000380d0700441040303040000c0c440410480707000c0c41d046503000e10706400d014203d400d01c5403924140d10000b0820410414146091160b190b01800c040c9104030811321030306a03114205642d074440c104014205800403001041298001d041c0c541d007000000d40390501d159540e48419003107a008403580300c01007204900341c50802250f180a04003a1041400c40340c4e555040c0bc1754110580070501a2424400d00c01d0202c5800d907450308980c5006540c04500383c1000c0c545503007040702400b1040c180f40f201804038030f03011415030041403241001e0040b40041012580e643c0e11040c0c0600118801650039540c5c82d000e20001c91140040762000010714 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 646695233 1250 646693983 646693987
    0x60213060e0609090411190b09030d11032209110c010506010f14030c0d0204151107050105222402071e05130608100905070b040e0c131a 60
    0x68010349550884507045101d4001000404029540d01490903081034000f003a51108541d50804070300344614821000c0701040e0322000c00514003404600605405105030141c840f0400c1c10042501c029035072014080b02a0818080b242d00c50750b8405401e050300c803a108e4144880c43c0c1ea0180c0c8070441d0790340141301c04505000651100940380034091039804c8682860405c2c6110107440380240075501000c40c0203c0d07048000045262001003100341c4c0c032001c0c0c00010455a4982e00c45072888000340c078107000310200b922440f904020f560301003820000c560041c0c645601d0190050120389000d880e000559901062107030022601210240318640141022000160311152020780a0300d884059845170400104a035141d25090900c1d2011000b1140259104110307502040c9900e800383c1826085210144110912041d4030b2025070021030710903018205541c2c5d12903e41343d80480350f01c02d0b800b445080d0500b200119010785950030042816809042c1281c08036600c4000252030755890746140d040811740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 646696483 1250 646695233 646695239
    0xb012d300b061e0d0905160302131a0d020301020d0c030204030218060102120307021504030906030e011109010e0316030f020a082b0e0315070311070c03060f0207060213 74
    0x440c0704400040030210b4070142455080c4860f0152420b80c18106400100081342d521402e40c0340e40c014000a0758080c00780c4014039030b06031007a401d02c1403922040e03200d1441d107200c009119074242b04561843c0035480d180521160000240000140e060078100c1e05991300700f086c002019142e100b80703010785649503001350341c461543c01080300f03025101040303119064410041c0151a0f0700051501c2800e506c1060017a2a030390f410707006030f0500800b508018070740182402000105680035030817a050b070b40d00e500c5c20000010700c020214200d03082c0000c0741c1c2e000f160801006030b0a40c01416200d84a040041c110b07141c1c2d060f48a0f01c860b44208552081fa16140c40d071558404514020110b071000d00045401402074400021070305516625502c510144100d284a40d0983c283c032443e52001d012a020f01101d14040d424030a851a01104031445000245032000701805a2002003c68050750b42010844815504540311035004100801c4103003070036542040b01000050300d50001e001006c0d5003d03070f60071000f49 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 646697733 1250 646696483 646696577
    0x602010b01051305010f0e040c090e0907030506040b0a0e070e160c030518060910080405070f0b07060c02010b0904080c070e06210c0303130303030b012d 67
    0xd42403005041c40800d01501261881e000b400000710f80c000d284c0a64420702455080c2c50b503540b61020280c2041c28801c10140182c0c00a0242049980f4641e2600721641c64940080d01c80f02c0900000700700d80c01503c00709020842200300c6642100d0320100000e001580c406d51070745041c9007640b01c104075464003c104581c4841a0784030102d40505824a40840c0c22a680d00030035500c0b810110010408041c800c03420641c03142e0040d03920101c4040d1003401500c0942002030f140442c102c41c11651441850408604e640845605004551810f020a81400c0a44d915540a00f850544080840d0368239101441103a44a10b100d600890146c2c00b100e588442144a0504146182d0800e6010982040a020040c4c80c0c0c03111304d0b41408280b0f00c801c0602d40c00d03405000d00708040380b41d0241d410b01c00401d4609241d2000c140000480b8465101000441c0c4100010358104034102384680c03412010314608040141030604404005000b403910051084c2c001408685001da10300711820800354601d10411881 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 646698983 1250 646697733 646697741
    0x6080103030e09010b04050103020309120315040b04060b07080d020c061008100b03071809060908130f0302090a0b04140403110f01150303055d04110105040519060201 73
    0xc4419180704041d50706007038440785c981c0b1461089504142d0300000142c280031090040c02030001410540c0c50303982c10203035410111649a00d00da02d02c1103280c14210855480c0900c108000c0b1a85100742d10b00b40003c2c2d40314419550000900050440d03000c1000482070342050241c0c3c0d04c41c001c0c2007104c687c06410488624603100058a520302c046180844c092844d41c0d00241034412100c112a059550f204d01c1c1c58808003500c0c16501c001d12050900c9800c80401140002902003804500000d1032615502d003081d404000403840301030f40100040f400b10341e103c02a03030007502000c20090004a240a009000282c0c90a022501a40002c2030040b2a001d00c510600c200058030a07820000d001541c1d0102c01c1c10408507151100a0902c074000642a20720030b07011480d00740d01e40c40d540c051035603603003401c55981c0c0c24101c00c0c100854110341c2d180c0200c0810b5140c4c400314101c042c030300750050480e503a40d56126005080c01031030301d042c41028000051241c1d01c0c4000c08128504461241d42030b5440e05001074251 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 646700233 1250 646698983 646699007
    0x10c1a0106020d120b2427010f26060f100305040b0a09110904050c060f071209060e041d0d1106060303121b090604080a05061f0303050c0312010608010303 68
    0x400e05141c08070241e640c845440c6d030b010031a181d0240590000190040342d881c410341203000e03a0303e040b501c52081145002005c1c58880725080c2c071a03404100d0f160307000b200c00002c40d207031448803400c1d4600c015005800c4000340d035500100207080061000c501d00c1c0091200603c401d21240000c7d00c910030003040004c1c070003485402c00682d01e4240681c1241e41d030381141d4070480103030482c000d9048800141c28040104040550280003804c0ea940d201388a00c00703103449502089095907144540840c01c02c1d043e11411420702154096510360317041e900b244003080301500380401c602c400c004e2827600d069054442403046094296854581010049041100c139090000c01081e440c440d401c24000d4240054002005a92203503080d01207517030500c100169080d8900603503107442d4000740c2c04203002c2502980011250310b02c600503411202159560102581418101a0490004154060204001390044010349102c210102c02d03207081c0300350103403403080101c1c00340d00000026455030010414990030900940300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 646701483 1250 646700233 646700267
    0x803041401050903040b0904090611040602010c1e03090302010b1509040501050f301603151506030f02040b130e0a0903021504022809110711010c1a0106020d 69
    0x1c2c1d0726098104680301d002c0d0b4400e00000400028a002c4280c0e5654080c8144d5603108004002010034a000d881d8142c0040c00f90728003540c0390810074210359000c4c0441f40038558040140700c48081024030300700c014091448040342552740703d004000140e960000700041c10000450700e59202c1c0b03403010400040c1c03441a80824020307030f000c2d4046140c170784480d1404461000c075555691200d0000d884000301c2c0b01a824540400781c0580d40c100d00c60441c19007503c4045900944040c014421840b10500c11540c100c4800324003a04c1d0032004003e12030094104130254200c4244c01400d0a82d0381503000020340c000100c0c40c030304018080341440041080c42c991074001d413042c90100410a02c80c1d402a64500c0a48260071403450240c000608640c1d4844030a440000b0941c011041c00346c401c492090f0101581c040c903280c4a0910300042c0b888800c61041ea90940d82258082c84071110354001540c0e00f14007480300b6158454201c20003403a010104003041e00170500c940c0244501c03601c0b26030083ca17000e450000650 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 646702733 1250 646701483 646701491
    0x80913140703180c0e1e010602030d1413170f0414040510031106090a030f060902030615010c080a0504080d020a06060906080a0221010c09050a0905070203030708070c0f0803041401 79
    0x403450442884c8191008120f0899564a59000380c11040704140002e40380a210700f400403c4181e400701c081d12407640b003c0c1040c0301c000f41d85450055102012501001006030302410301c00400c100700f2800d02c0404412184500e464541d0500103190f500941000d2030041e112807240c14170381014420300c0c5d4441a4069031808160555584084a8441c10015841044041004d000c41d545183d005030040d41d20090b104040d184d18507020f009440392003001d0780b10b40500c10000700c00c050680003422207050141e680500e0450160360703400b400d8100c4000c6000700802808046640f06080201455454943c1c0040c1000c0c00e4500c2c10f04240c5101d600030001d8a0706205080000d050005a0200d43c1d66048541e000d1101e903000c00c1c4200103108060808841d0300f0480344002d4a07421040e00701c01d13a071080e1543c11542d904c0389400c200741e032429681e10f40140d108000050b00c041c410305005800201504c2c198040d0903040d19004100340400f40c00741c8000c03400209201c200040c1002616003005401c00070300c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 646703983 1250 646702733 646702781
    0x3120809030a030f0f020714070510050f0d09020a1d092b0c0204050a0c0e1005040e0910110a020f07030201020d03020901140c03030603120412080913140703 69
    0x7038803405219041c4003416110740480c1d5600007180c1094401084407081151940a00c2c2040c422458002c3c4025105008480703021036242410700a40848800302e8a8417440c05c0d40881c00042d03e0740c0240300c61541c5542d82c494520050307a981d042d8000400c0c0455256021140c0f0b06180840c008020300b02e0002d80c0e012010785d0b44850070b00006d00106030b332551401d6071560381c001420f4642c0090002c00942c0149032604015408030150300a43c2022001d980740c5403480000f4052000440d080e42d00c18020500600080005031030951110340d00c0034503801924460300c817446a0901399a0710800c05485640042010220300d5810401443d02ca501c00d0010154949550000303074a400c00440b41c042019000100b21b012640140c0200d940001703800400e0396240c0040010a460350025110310b0711a0080b1200c40e2512020002560282c840b5211038986008903581c5032034181d4010700c102c0382c014105400000703080007184a002800e00304440c0d07446142c5001100201112088012507060813108100c41c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 646705233 1250 646703983 646704001
    0x9030f0a051504050c09090d020c03030405090a020a2705120c0a09020f070c03110102160e07030b010c05100501060810061b060b10020304061206050603040b07110115031208 76
    0x38180842c0010303000305854a0b076003001801d11501032070958005110000340815040d0004d5005641000b039800d4800d91b000e00030030141c8034425031107065400301c004004121440130540c010003125910f0700f011141c9005813046c002c09200300119007400403003101070030400c034103100c91414071410124019009600e40880054866101d50145502141e404109916200407200031640c41c1c40c1c001400c100459502c0c602506040b07101841035006000c0c1c9290400c121103240200000d448000c04008039550b00c58004500503d90105c1090400400c08601030101701d050101034a001007503d000301c0d8039030400030044c000350409041e500c20f10515200801180b64070206805010f001e8040403203142d003090800f0005001d0345154a680007124541007511590004028400c4170944e0300c0e400610280c0c5600c5e0021906d640c032440e508450200000750004e10780b90401640941d007030a00a061300e101401d51800c68000800d1305d21100e0301e6580510501040c10091003400d010703441c05480500c0c041f004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 646706483 1250 646705233 646705243
    0x201080a0c020115092004151107030b0114010f050f041403070902030910060909020603160306080106060e03061f0312090b03191a0a3809030f0a05 65
    0x180014150307034550340d00819200f904250310395891003031450040741c2c80350b5a9000414181032a043c04440094480c00b000d90503000b44e9040340c2102160a00c0501000410303560b1401c00e90305051140200c400200c0024a060300341406045090411401d034031034080050550002030310301e1000c0c40014000c84001007000c100319419a01e000c2808880140104d01080c0fa24400c1d4122141d0240040200661044002008202da602c496024080c80760340b03030b038084c0c1210600c0d04040d40050080001940c100b07c2030380741d800604020300d00051a40d540d8212282154815089000001c0c3c88a594803000e02c0c082010035007203a4403030144c10300701640044bc0b401c0c07020184002441c012180003000c00b080c1c040c10031342005003207820b007065a07440c22100c103000384e0f1070000c1541c00491811602510f402a0000c0540e41c90601928000200741454a40d554094a10b441d4001d00e9031034a101190086045402c1001d0208a400c4d05840e0211401094100320a455020650b0360084055001140f00011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 646707733 1250 646706483 646706491
    0x11d060108010b16050a0b0406090b1302100e190807050127060f051b070e07051e090609131a030f030a0806210607082802090105070f0f1707020108 65
    0x13000c90005075031403a203076003401c0c13088101a10308108002000203000c40ca4012424031482200c00c0f440e941e43d220103403d0605400903010f0b41010030003400718103550090962060042c0001c1c03102610000d0480841045861070b000100d2940001c0d908100c5542c100e40400a001150110200b482c4030118000c00721301d00c984680b0080110001c1c400c4003040c09a030498100d80300301000d1a07245582d508807640d8813520751064503507000b0b001e000241b40350300c1001911a00b0030b040c0d0030060a0a09030440380c529400841c40c003a8000e00810840100d680c4103d035401100480b06d0380440d03c4e44260780d260300d0401981103014001c0d041414074410355100403084400d01802401d05086c0d0f601c3e0500803995440c10500d4200342140803120880750001c0015040c2e204101d565140304c090f41c0da00f400c40b1000c9070021501d9503000c03410400200c0e90507d030f401620b200750043c0f50031403c14205481e001c4108983d100140c40c01ca281003494414001c40d44840103801305201078441ca000312aa00003002420024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 646708983 1250 646707733 646707757
    0x11202180c07020604090203071b030e0909070b1c050c210c070f080711041a060d020705061014010801030b070c0f020a090b180105011b0606090203011d060108010b 72
    0x260000d00d0703940c6810281c030342d00c03500501516142c6442d810001d0080d0f00c1900d500b070204141e40003007407071420020092488154507a131126103040e460b0003408011310700541502e0150294520200c1c42c203c2c3c450282c10050400c01483e81d44144210940303044070400381250074200020841035010b06407952004110f10418003030b0420650b41c40401610703c0c002d129005105c40201800344d41405a0407001c3c260950090360302c15010b5118100300404c4602c40c5205078110a642038400c2c0842ca811400703441c41418140d80075140c9000d80e034400b4108001151940d992166880041c40031004408009403000c0c1c080c00c101080354110344520081c030310300402240400000b030115804124074100307145075265010301400e04203511a001d40d40a00740c1c4040345401640e400a801e4140e08400b26100e04842c2d068640c00d80f8440c2c1c032080300449032490041929003030f45541c00001c0410300d51004500a19504501840c455580c80003030512400150a180c10411481c1c01440a081d076681203d0411a0356 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 646710233 1250 646708983 646709029
    0xf0311030702210705011d0c09190c1b03180902070c1203020c04050702060105040f0b060301030611210406051e0636060f010c0b06040b040b1314011202 67
    0xc095003c1c401d10503000001d081d03500740301900c15030503030366198169252500360541e500c00e54401e0a00c000c030300040307030001e00700c1c40341d80000304449032664002c40c2c04501e686000550106418100030307030382003010030840005404401503542c04000da00c110b409441c1d1240198030700030041d200c0a8910342c036030060b517484042e160013030f10415008000e4a22414000380041c4036510b0a0034010751600424420980594100580700c000d200c218840d241904400501c03007810359086440b920700400e0a4850946800c0c010030860b900601c40400c44403041d0740984001800e482c180c40c2c004150740c8050a54412000c25803880441d008900701e0155010f6400d440c010200004040f182c120213504082c40c0c0012285082450240020140d549100b03001c00d4561665424101d401190040498140603140e0144c810100301c0c1403070141c0200d20f404a0082000c940b4070490b100084004022629032140e2a6070f41400d6905141c1100c03c1c28010082c2529081340c6848076008160b00f442160f480300200192 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 646711483 1250 646710233 646710283
    0x31204080c090f190b130f1a101e0507170403110d21140c0f010c0e03030403030309051e10140702030406050304061b120608030421050f0d0f0311030702 67
    0x910b59a0b10000c105800f0140700341c0d80b41f0440c0d50000d103810103d174152006024507038922818803107180719194149a680301d4110100d0044220b5185400520304200441004004041a0441100361542c00240d202695442c036600c2d08403100e0500c04e1086000c0c0d14207443d40004154a20f02c1e20201c0c0202c4800c00c0d5008186080c00c840f95000c0060140c02d4802c00300d446542c1e1100000e0f01030352151200020405154014004d490380144985171540c1584104014400603103e6000140501e11510450f04105200c1c0c55034110b4504c02200c1c040300382e01080946508030510300500c2ca0001d12100e00404d14104800029180d201d24021a0709015000001c20f080000c5940311b111040c640c2d01c5400d20740b83e250000100b0000038000082c0509007040070200d4000b43c08002c070b4003110510881550307034211407072031032101c0008000c06413414054500071248000003809070b0f10001c8503981d10324800c00c0e228a000350454071040d1b81403150070350034410041015000502414500400301c00503558001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 646712733 1250 646711483 646711489
    0x40f0f0810090f060f110a11060c0c0c1e0603010e0f1b0a050a09120f020a0b040b07061a04060b030604140c0d150b0403050304030606080a050c01050306031204080c090f190b 76
    0x80207041c01695002c0001d12104248d502810066030400000d09076881610f9a09403030000b806580d000b0016500b102c0210186403810300d84004090041600504c07603410b036400007a210380c100b40d1010380000220301c00c200f801c491028045521001c48540a9001b80300d00e007000541c1d0080504050502500050241c1114052400e00008000c003030098240e6440b1031525070511410707480102d0051041a0000c9820820314098500303482e00d15402c14188180c94807004058151a66201e10445103000c0c404613648450040201400d011070300c4998074201441480200e540c2150032200c100c52032070521085244e03030703011100c0c820110781c004154807200401c004002c2182e81d200141600000078004100000440a8800c403030207001c0402c886035850901c244c403440300d0f0000404903000051846d00540c01034002d150401c4002c1c040300c200d0f543d903a1441c0ba1981c450b8000c0001c81e44101c2c13201c01c95183c00301d00140e105860b110309003810706000f080d410a2000c41c800021080e9118441e15059417 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 646713983 1250 646712733 646712741
    0x16021903141b0a030e060c0d0f140307020c1e06030109021803071403070f032a050a03140d051201090216020d140609030a0512060303040f0f0810090f060f 68
    0xd40072520b41a842d40320030180381c1d24040e410302103010919002040681d490181d00790742d0b0b10f01c81c1002400580076440c1003111000e800c0001d102c2440100018880c031442c5900165105095680040640740c000754104205144070603540071070301c800d40941d51150b44420b819079046494100000d611151072a569a90402c104100c9035090700c01d200340001c2c0110310305107200c0105015019188650703240c0180103440f1030580000303040f4002007111040340c642d806141205900c3d8054026013143c1d04c84000940004481d0302c145d880061280c400070402d4001c1c0b1880381030003541e040c158078003c042101200903c90500c0380c684200d81c0464454a44411120b6420103180e0050030386841201602c1d144400c40e21800081c04644038603000100907410000448103403010a40b220390515008010142003440005c1480d60140424070000840402100b0040050321501245840c4142028081c0d0314080b05441c3c5280710900704a4100d0104500225450103d03410070000709200902544900c050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 646715233 1250 646713983 646713997
    0x906070215030f13030827070f0603110307082703030a060312030b0619030914071a040506040e040602432d0c09051602190314 56
    0x404040c01d00c803010a610100114807a040e080303541c074841c3c1c4507501c2c0d5032401c5120400007408203640c1c10209800b1444100345001007022100c50b40ca401540882040c201089079000e0381c50038689600c00c3c007059070540101140c0304d50040020f4198a88400004c20446001d4500311102240304000340307105d1441c2180314500032190007207a45e81d0174034180d2900104814401668882c0d20103015240780741c807030f001d04402504020034140c20521240d28140000c2c620b509420300f8199107680000020310000f120540c07800310303a07020f00089840c00c89120592a02e0720b0126154650400c814851a641c2c0b0094405891780000416007035521032900200034800d044140180c0341c00002c810070343d800e6900c159224044640004580818070440003c08180721000003010f40c0c0d00a44940300042c809807041c1c850001c4110b06104c038154940720103940070b1154029545040e10f807403c10107001c005101d00414511144020414108507410503500610b452074010200003044410f0b61036000c040e4180c030a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 646716483 1250 646715233 646715239
    0xf03091f120c1d01020604020d020118120501050a0c140412030908011a030106090c05160c030b15043e0408030d020711040b03070e0a0207121d100f0509060702 70
    0xb500040c910103882058804140c011840e814a080c441c42c2d440403e04078055036020700041000d1409034010b6610400c0742c1c85451801c48840c6000442c0d41e24050050700d03050241d030001030329091544030807050740c42c0100000207110b00440d03a86c8103035144400722402c4804030801d000d00464245001c4880700c040b544440d006600740240e018031880181219100700d41c00b20b008002081d85c0b02c5119003551440086440400c10900160320400038480282803820300c102e0305194031135142d035a4144601d00a5414560080c5400030030111403c20b032050441801d0245141e2499071500455540c82503038400138100d202d103602140b0715482003010203a90103806c2420a6a45403022000b0311802504040e00c16142801d503440310310518207080c85000442a000b5001c0c0c41010709100da80307492824003403e84003c10b54200000c0e8081405400d04000c12242540d81c0394001802903a900409250700e00c0051080590019030543c19400001400300d508003030814135128420100090750b00d0182c2900690 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 646717733 1250 646716483 646716491
    0x9060b041d0d110a082107090305010c080f040809041e090309050a060e060c19060e061b16050a0506071106130206160f21020f03091f12 60
    0x140044a1801201c0c00e058454101e5a00a02c030300011508400200003505003904100303c0390f000300700d194004043c00d840302e00024040140c28101000d104208440c40030001703441c41001d004001c8203014440d07070702009141c480d140d4241844c101c460513901520080c41c061000078007480a803980d420015041195040c0021300d40b50000d0214041c100c07100080300003d90084000c10301d442c1000000c2c041e1000e664442030500320035002e120340365102d03500c054110f12406e010100e00c40415500c20390768130310401d400b144480448922600e44003015004000c0441e01040d0151210310708800e0f05c51088242c2030011301c0030442d040860400a25180180c50348c000c040400c0b41c502d40081d0b07c1c2444034092400c841c280d903250b16083d0b5000d0540c84000794021005c1040d11585170403101400c0b10305004001d1003032010310a50340c060301c08040e104000c41d02c0e44501c80010000da014000c200403010010041d500d041845d40014000e03103070714010b41040b5a2611040d200e00b0b0300c070f00c05400e504210700360200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 646718983 1250 646717733 646717751
    0x6030218150d0b031507080403020f01020310060e041a0f0105280206070804150b0f030312070909020702130507021606090302030c01050f030727030b010e0c0306030d0309060b04 78
    0x50850b9200850012005007003121101140c100000c21907440021004510101d449000007100d222102400c2a011842011200703c1454020300c01103004450481c0381c1d00c0b4543c6000d9014140d084c814600c2c621803072400036940740d540381054883e0b1580000300c92007003035640e90b2070043e541401644200c0d0020792194900d00f040001988440720340404d15000c50703402d50740c1d0100454180504440c010000401c41d44814861000303600002c0080d0030080070030040c0c02481c0007003461074012100c1d483c0030000d5881031207003064104007000301503c1401300c25407800040c0c1e0040b562403c0604110322040b07039140000340a8503c207012160240c640030000d40100c2e541c0e2100200340c8442d0703010583c03003030140841d42c285131341c0100308448001c280d07500d0207402e40c4e580b136109a680a800c0c00201c01041c040000180d095070b0881c01510181d07105c4c9601030610350411011001071400148104004401082400310503500040d1920080085240124100c0417516008029151482c0351682141c2000e0b419 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646720233 1250 646718983 646719019
    0x1110304120807020a0506040315051b0307050a090602060105010e1314130501060501031418070902030c0c070f050d152705010507030525030204030c080a0302070608060a06030218 79
    0xc03c42203008542c0c0d140040c1d10780d01080224481c42c80b00503d520f260200090b10229150407042d4031840c2d821640f0f6100c40c0346455050303164800c41d90380c00003420026000210079000785681c000f03040c082c80101429810103002a06040c0e600000c1c901c14901149500c086250b0b40e0420030184100015200b030f14240303080302081c006c5ca1142c04849035402c4c40c2c40404d1a52180c85545802d4003909800c101030b0301c4e0320314100c0300080030240700a90743c0140040070600314054001075000d40313403d4000a58a83d03000c00781d82d003862240d030011810f0b14021401004190348110381e40d450340d600300140d00c0640362030000b074800600e034043e10703130600c000f4252084100c085170110540d2098080c0c002404150b0300c2c0d00041702161411214810034001c040000d4030448100b10017800d03000494103005150680b01d45031002c062105911401140d0701a80441040650500804008058174145501070b81480000111481001e00900b010160b0101c1c00c6a0214034030f24011703010190140c01c1c0f010110040c100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646721483 1250 646720233 646720237
    0xc0607081c0b0603191805161e05060901030e06040c06020d0509030715090f0b0a14130e07120e0d0e091e0a1121060a1409090a02030609070e0a061202011103041208 72
    0x29505130a00815030000300c489c100c040b00340142d0030305181c6440aa0405c1e041146640250503514101a690100c440600e80204215801240910000c04486180041c000c3c9000030001008003000750034031005a880e140047c0c010305454039141d881e0088288840101e8002070079900c0381d07909000c1c49000048020010001740000243c566800c0e64008451000f820107114898109542c0f07182403030208403504c089950b454018070645480c9545419a10401050303c0541c80402500c3e04480f14040d51507800055070a00b20009442101441c035280903254040c0304540c1c6020785446d17000d400a01042c0d2554001414120005da1b26512003250154018980850038440040e1003045d0003c5003180c80c3c8000304400303c80d0141b01c2c10f02158031880622250000c0500500c0003403080007150030050f54180803003441529058028650320f03280c1050800d086401504041600b45442002d2180700d021b000b0100c4601d40a00342034510054000131503285104a5200480000ea1020780c0400c004e14500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646722733 1250 646721483 646721503
    0x1b0224030c030103052e2403050313060c030c0f020d020d0b07030606020714041a03190b0c070201201e0a05070b03060603180c0607081c0b0603191805 66
    0x4071501c2112007041c251031903800d4031b00c42d581c0ca20414a50040c0d0030703141d007240c003449103004d20080814202020050704402c40740c008849680002c2018080c100c04191001c0c01040107251007148801c907607d0142904079050310290001021528800c15134807041c481c100055170140406400030101d041402252000b42c90a60003c2c0c14504000b891600c0000d110f8151902684c1000381001d44100300030043c0003079002c1c007000c0315041c20580c0441da81404842c05024000340500b1010185203450380d02c004000740000c40d4070f05d0a00c81c100260360322500c3c4441c0100c04099a40700c04802241c107525100da800010707103000d480b2008101050202144486c145403082c4100c980d40307526200c0c0161580411100150171a00900c005180030001701c1c1c1580541041200b515615803114001c50807039401a40300f03072100341001450048018401243d01d02180601c0410816080e41000041b0b640c0301c003521034115a9103a11405081090030b60024803412188664580102e03400e150050316001484 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646723983 1250 646722733 646722743
    0x120c05030d120b0a06050f0d06090c0f0f1707050a1205070306050a06091a030c0c0714090f0403020a0308071101090c1e0e0c070c331b0224030c030103 66
    0x11079004144e0901030748250680345540c94003410240c0d0207400c480c0c1d503001608591413454403050000b0300c5110b540b06046201a050f40c5070316003060360034800384c070300c002103250340342044101c00c5a55000c500000302583c10040c0392401d00e0382ea0196850488418040585524031146410207118503590540d0141c1d08490040e0f4804201c107540350800c2c1ca61801c14810010029407074640e82034003030304510003913a0142c0c0002e5a00c3c1840b4101418070303d00103294009030307440c81101030124168a030010b1071550080c01d1905581451800390f500070b40307a00354120002d040c808a0400304010901920b0b0840070a008030000300a40b04560401844140032482603100d9022511560072000812003040420380796454840c4010380c8034040d210f012a84006015a96900ba00710085000040d200c1c03110301c1041100e01c260f1341421011422414052480c04100600039a10707405007200202140b41442550111615410a049407102503080c0b0180303c00030049502c0002003001142e100e10185050ba801a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646725233 1250 646723983 646723991
    0x20d0b090a0905010e1614190806060418080702010305060109080a0b15060301061d03030f0a180608010501120b0f03010513031b080d1a120a0516030804120c05030d12 73
    0x401782d840d4036100d10501044030401c80070f01c14800280c07030f0a2400c0204030050640d114486001207800ca0304440768000180c19002581480120b161a00a44080c0c51444070301d140c8881095840c40300358400d00c0070081c1450b4562002861980c080c0300c0c154000d101a4042d22248159403070100d8074410102c8000e961014400c044014600304141560f06030399190700e680c041c004c0640440b020001c0310015155042c030082100d9500001144040d0100c808141c5940d10f08911140b0000c15000054115074200080400104001da900c43c8507624002032080c3c00168090300c01c0040740100b012114070701d800d0740c24103052100c6c0660000038403080078003d0b610801c81002c3c140089220b8071f580040640b0b2020103108180400700e0543c0a041d4211a01e00404403540b54030000c03c81500030340348108000d8000c52041003d0210a224480850b61042261040241140d966041a00540c0500c40010002c0ea00c80000c0020040880010b040001c00303c03031000c0804800103003965081e84170b41d13000c1810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646726483 1250 646725233 646725251
    0x40906020c1f05330607031d09190f090803040803010501090b070b0f090a050609100e0c0d080c07270b03030306010e1c080f2a030706020d0b090a090501 67
    0x100d103d0207008215030542502c088045031110b01c0c10181080445041448201800341e1079542e40009001d690f01c00d03102c00c80540d2103925201d0104c0c0790183d01d280900200d80400440e0000e85019031690450000c1c002450501c2200c100000d014190004204080c0081807200340500c180256040b070b44240e07161300c0300a8032003456010b2400f81c101c005120b109450702103058804c81482003030f801660302c422558412015140d1038a080e0303040d6079640454000305e42c4c643c101001406041f0401141000410400141001282c140307000f5a0024205640106420070344031420f102200041c400c0c45e007290001440d02552885400440d07080300e055901c3c080d9000c1c1141401f01c00d03240300d244140c4440070b690360034100303002b0381641078090011a80c51041035140050718030380180a4000041075200e44500c1c404000c803c070060302c0c281c0f550441c54940c0090a90341000412600e050350f00480240c0c0352040000400041c00340d0b6825030358003000c00c1d800c00510500c0d950202c0300d400d000e0300003031005c008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646727733 1250 646726483 646726543
    0x60b090106050c06280923010605010212030a09080a030c030c030e0303040b1906030812011205030d0e0115030302101401120b040f0f0b0123060414040906020c 70
    0x8664042000c081e00180001101c0b905408000c000e182d0740c028400300b80f11103282c5d9050032900703613203c1255541c00e41601d18109005030f0892003515800400204140c40c103000010b036640721043c4c4c01d011003410000014501c0541900501c2039642e02103041d0741c44908070200940508019001c1000007403070119100743e0144a8051010f101c2e41d040301462642d01c840d101c0a41c280c100402900802d00c82c521803101030420f5101d038400542c014403055403200002c00449200c01c6c01a8880b4409000b49090000407800210859886c0c50250030005900d5400100182c0585030001d03803110000b0301540000185600460941d0002d40e40c071f5010402d201c80000b8a80e451030007800b404020801c0344644400081d0510310031074100340180d440008a0304256204110503000c010210b500e2100391004102c04a00e02e134250040100200502450300700600107d0124090761183d000e42200c12003a402107030300d55601c00d400035a00810309543d03070f00548411503600d0a1034502588001500c51002e0b207509 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646728983 1250 646727733 646727737
    0x903121e06010206040b01060305070905060301081506060306090f15030d26190f0902040924060602030a2703030801080d050309071205160801090308060d020f0909030f0403060b09010605 82
    0x19500800b035144a07402d00c8c8044000784002400da805002c3e0044000c20780f9a00d0300041c60081c0040801000c5c00d04100708100030820000e80420b0080e8014001d2142c143e803240c3c9000d521200317020510410740e070782d00c3e2030560302441c4031a00383c0c1501410540c00091640302035004501000311020600200c003108001c4c40c411404c4640c2c40580780040c001503052036080d048941580e400c0000400c10642c0d41d00050704842411004030f40304110301e20140c880300d035440202d415002980a04101451030318001a48074800c0620b48420056050302c21031003900f0560064920b520402c1d080d20803286c4901c2c018118500a004d0b020440c49004500384031284948220303813240c09481d02614400e4a02194091444058142182c0c28014044240c010321a9100000300800e202000400c03a1440d07800c01804416000d0007a80c000c0030801600710258440103880c8000140a40e4051781e155a24604c0700d09501814900c004002d800090000074030080390842d0540400440e0414840e982c4d40e0400d83e864 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646730233 1250 646728983 646728991
    0x20301090516090501050a020f07090e0d02070317070c0b0a0c230304120302011d0a06050a0c05120423030d0608210a21150504020913050903121e06010206 68
    0x114240404e00040d4419405010340d43d04134011503040341180a0707200e0503d503d40d00150007559940903d00540903040100c2d01c03a9554500103084158215207820301d01c50b00b0000b86600034580000d40404114034403100a005052008a813030302c460854500920154101005641c1460b0803e1041e8484080c668100e020707a645800031440c0928002003401d20816008040d41035541e2180045410000507101c0c1d80118080009090343c6400380c41d03c001101e001030303d0f007090340d40350a0340547c445030041d00310341c0100b036240d031420f1301c1c0e998600d0318013180c001070008075010205c001031741203201c075000004c0c10310b07040d58a06c140085a100c010560b540c030403030308039418542c01c400c892500344038038040201a100e42d1071071f01ca108149884802c601d2020040492040d0650b0785114424804605025601410080340e0640c03502c8000c80009082c152000e03614449a03644201207010105c0070000c840c0c11540b9010180703a01d180030703105070041ca0411605034900b12034090002d0702139132002c9815403203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646731483 1250 646730233 646730237
    0xf060d0816021311040501140702040e060a0c030c0f21180b0c0a0c0f2907120b1e3d080f040b0919050f1002070c0308130b0706020301090516 62
    0x5c0c83c1c40c00004461a84080b5002150a002040a000540c94901030380d4660341c00c0100034080b0303080ca40c0030b45084590300010401050315221820082c0769000400b100c0014280c80c014140d04001c00303c2058600d8241280c079003452603c000400c0c100b0240f10138844aa00030002020241e84804984016200e01c1c000c0c0310008220550110000d00318a10100590f4021004039a251081008000c00e1140190010300c04032560030810185950140d81e0015104454a0a00003503047c10040703112400c0d4011280c140080611000c00c582e2501a1141e0720500d2512480d075244422040c2280344118501c0c2c21011001c04a0060301450f000d41880c90103201d8aa0a000e56035803140c03500c00203154040c2074144580a00709910040c05c030400d102c111200d009074017500c805018007860528040b02085903204040c014040d080100d5044034400302200d422246596466100e000400b404040d43d8020062640c4041485814003006a0240d416100261390402a40e29002002c41038540401030500c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646732733 1250 646731483 646731487
    0x1b112503030804050a050d0e04060501020f060103120315090911030303010e040f0f0b04061d0f15060102010225020108010504050603030a030b01200a0506010e07080f060d0816021311 80
    0x203031049010907800343c0034100f6074804600c00d644d01401c0c90b8187d600c83c0b0003d58a03034407502403031900707214240003081c090000349400c501c00b00000e6115401480090303d9603c1009801041c9030098100c4100c107030326251030ac040180c032180d410303005014130f110580d1884081405040181000400c0f40c2c1a00c0f01000c179045540d8955442caa06005006030441e07440e910b0078032040c000b0351440030003406a0b200c1c441c00b04080d10450340c40102e417041800c080c071840d07000348181403041c400070070700316482d850617003413280c0d03a6035542c00503800fa1007200030790a11810107085588410324103542d40c2340740900c00d0b62011200d90740c42c4100800d8440544041ea80340c6c03c00c10a01e0035240c0030381c3c8408103810707040c1452041004000c1c0c4075000105d600d40340200c0d0750000c0c00074000f000000d2051358094150382441c1e08550404ca00014100d1400602020102c20702d01c000c190560b5802044201a030b5001800517650618007201c0d084c00c3c01c40d00070490082145c2d600b04905444903000309010030b840c0d64a414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646733983 1250 646732733 646732739
    0x11a0a03080f04030c030602210622060f080604050d03020901050f030a14091609090b0f0c04050306041202010b0f03030d0b0d060608150a02040509070507061b1125 72
    0xc1c0c0554407091045002e12001c1100200207181031000c04021030090034016160760002c011001c81400600c58410000c0ca0b0504021107650390000700400310801411026018982c400c1c9940100440d030000c040124070390000043c0e250001034924030561061040d1001400c1e4001d080c0c3c1a03000da80291804598144103014055503018040e60740444107610100e040c01016019060494040d01c08252a80003140c0403d0340000904100c1c00800d0403c00400c042c2c102c50300ca100030582c002d000d084c05400800c000c920000c0c04401a280504002004d84031942001c0c54080030030703500d400701c24015500700180c000d12450319603542c603200b941c00380140d440d01c8420b15805004141801c9440c3c5d1081d03c41514401142c4640301e01c2d0060000d10b4020309010a61090800180d1801040042003500400040c4840e4a82030f840300c1c0c018415050050701e6010519200025150440c00202d4540010340c2100900382e20070b4540600700680801d0320081000079008200d00c0c0f44c03200d00e4620480000d5010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646735233 1250 646733983 646733993
    0x215010302130e190507083304080705190201272709060b032109091e1302010e03030403030e06030606070c0305011401091802010804030504091d011a0a03 68
    0x5140c40352801c068444c81e00e128441400d03450b101d402c0580d159401001c06000d507400801c260415914640e0f00303a450840800c074000f01503000800416000c14582003c42c04100c28081500c10302640541030711040040704241d40d0034100c10300ca09a00087d6001d0780884c03801d00e04a94459040080b400c10000c0320b041808400540724503101104203052008810130402107980f294204a520484001c1508125182014070f050028401320007182c03140f11800500c640e150046a181007c03c0d140b007141380e0b44501d0000707200341800000030745410080003042041d4070b04006801445200b40c84000c40c1003090030a055503401940402004a02c8145885040b46043c1c0003030b590211004240d1440d0a400c0d9803503d2040060b984116140d81d19612982103100b04040c4035405800080c41c1002412000248980080401d00380603041c00480b4000c2800d052040e0100c902500c00600d007880565410788070090480c480d540c00940c6540380040840d19080107070301c02c1d01e802100070301c580c3c18241543c9030307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646736483 1250 646735233 646735241
    0x301030b132306150a0b27060d09021011070306050405100c0f0327030e0a030206030106020705030c040e0705010f030f05190f0533030319021501030213 67
    0x1038401d88807280d0868942c080030300042e4078030304407100500000d00706010740d02d0200c0715074045a44a4200c46100b03110341000c6206590f54021910b80b21003e19a00300341900740007090000454101000048204111655412012140e442075446c7c0219410401c81102e4000d607900c0403034807907005001c00304085040303600166000b034042e5042d1055000311034101811603032001800300c00b160802c20402071141c2c140c03003040c101000f260150744804410002c40c0d02d00781744000300141803115076072100449840d411040005998080e0415a481d611000040c4d510802803240300d200e485050071042950809000b40c2c11b0700c0040500801025080c03100541d411f0581c4107001d0304141d503176160035400706100e004850007007202ca0140d580d07000c3c01e03010181c10750703072142c03149042e2900703020501080c400d02ca83d8400c0301d08022072071070b03d2920323410006079007890300d030820340c0d5042c0710104040316400e552441c40110017840703400721031043d1541030054070040c5017448042e40c0a80400b05410341d558403900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646737733 1250 646736483 646736521
    0xb06040b0114130e070e0a06051602030a1b1e06110a0605130c05010201020a080c090a1206051503060408040504090c09091109010803040506030402060724200301030b 73
    0x108055208010030380184503400c8050100107a201d4940100444c40108036110f4011441d8603155560031500d0f00400c600b01d681d0303c640e00c100000054802c4103000e885280d0120315a0003810303103446480505000c2c425001002070404200c0044030b00091811010456a015009009051030345628100050300ca282c0c3c0300e4401c1c110b5003d0040ea00d00040d013144140341c4203800c0554002c00741103003424203030860710540d00058150380c410007031254103580005c011a807103038411040d035969905541c04202050041d40c0080403424076812028100070707440e00005d2058810002c070300345912032070041540e42c0c04240c3d00542a074008120030301c80c60520707410488010303008803035441a2542e50b4040c44110780a11500352a43c1e240c0c03203416503030b5241103800c0300d00401a45c00114249030418000941e54440a40024450800043d0140401210403c0403030040801080c2c4039200042c1c14048000d852543c0b41860b82d54605010b00900e03003d0001507030306981d002000c6041a607140d02c1d4066040d48416 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646738983 1250 646737733 646737737
    0x5061e0904020604051207085508030906060a0303050708030a02040314030d0b010207061b020a260d0f090902180405010b121b191e05090111010501030b06040b01 71
    0x1001c1741544a00c8103800007940b03002d00809150b4134000b8000c0c1403d4050b150311050503110588103804079488041c00380d810504215100514900c6a1a80c0d00c48072902488040b07004945275030001c3c0601c03200618495501142504e000d80e51340f404100154502d4000103002c2103003404500302003a5480003541e4004110b101c0180b0b171581320380314911307095440313484407045500c00200c52683c0745c014010400b40410030300091403a141080409070070b4076181200070701c03c0d00c0d042c0c4084095681c2d902c4050010f0a4038402241800f00140024240c0000319580419a2107804004001c10b80705040c22410380e10645c0d55107820078144039958001e50311604603851080052a0101e119a48070710035103000b0074108001c20b030b0300e0070b00e2450528005001003601d09180207209901301140815811180900000502003a80d01c1e40c100040d62a40c0719604c50240003541e03074151410040e003180c0108070494003600d66188031600c15200e107090310024040200291101d20200724682031942056054040c14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646740233 1250 646738983 646738987
    0x408030a0b0607080301051008040506010603090305070b13031707021f090b0c1b01140105010f1709030d0501080d090603410606070803190608030a0c050105061e09040206 75
    0x10000190164101030f60070f40d404100080100310384c1c600025078606000300c0d400d001040c1c2c82c142d1241501c5240c144155001d041d110035100003050b10500488414607444000000a410081d5690741d10500810085001c50807aa0034000c0144c41d010f14140700b4256503004000134a5010803a4a1b419100d142c1c48540d0b40d222041000010301250149108074000d5800980b24000c030180240103141d500c00d0042c16916000d0040081c4a4042005054035000e0078000050b131030703c800c116481024980034031514040343c410300000d40f202200a1440076042c100a10072643c07155000c4d603d420860994034041003071140c00300001e90094100394500c20a1010000c00603446054800c1e00151183d03001d003450388d60b607070100340782c0c05140b07881c83e00601c0035507000303091030b0f010740d01c1c41081c1c400a0400204003106a01c01d103400310164004001801550068070b4941c0c03010007024110248075101180c0319420030300090303003e043c629104100c6109500c00100c0490130041440141e02000d0010790304000700b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646741483 1250 646740233 646740251
    0xf0a0e0607140d020d03150b090a030b01181505033a270b27040903021606030b0a0e0c0d0c0504060f0e1f030902030f0705011107030302060408030a 65
    0x1d58003494156210300c040c10f20f0a0001d079000b0f08028013658840d0602d440d104002202d8150995500c0a5817030116507195510b070082c001601c00010341e440103101c00041c10001c202851280702c0c0070f44062045000b813060701e0414003030400c201d420340101d581640c02505c500c82b0f00042e0420140c8407250200302c2c50f882040c00032a00c00d141d08403140c0b40011035152001c9645040f100003024a0081084089611803424001c2810140c401c0700c81c80b5100103401c0c0e14040c102000030000d9840301d00014010007130344082340303006500e400a240008070320803a040000180d1500a02554103e01710090409414905161000d851458050003074002e14200b0711484032010014800c1120301120740d22011340b561303d0710344000c1c032003114541c10508211040b04a812035071a40103810381c044101c001d03d201100000300003180101100c007806940341c41202a801d051220100d640c0741900c40070383c0c90703500350950038083ca03607a41d01d10302c8000c0042e8404030014000c10300180203160001c0c102d00d404601500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646742733 1250 646741483 646741493
    0x2031e0601121b18030317180105011d0f191a0409032c010c02010509031f05160908100203041b06020714031f15050a080c04060503030f0a0e0607 64
    0x710390b0480d2001d0b6424180402240c10110039500f00280f100c50f100414107541c1e00400e0222810710842e2003e0000d0007180b040032208c842210094103140c002c1060b90b0b906c440c21034107412041242050003501d6804180f40499509207988a50035190174842105070741c2d9021001450840b01d01000504054034002d43da0340c0d58020026442d0095603a0880c81c07407518001c2c281c0340070000c1d0309000300c0003030051900d00e66004002d2000c82902400c3c05c9844520010129040081f1040120481c6c2c0c2c0902c1c0f40301d01d083c0e01d80e000d1801350717047e07040a9182d2100c01e078041d00c0d0b010b45401250303519880b007042d40c20350803040d13001998001c0c850a6000c111408404d0441e1480559400910161708203160a000a800c0340c851500030503001c40090403004212654000d0210003004100000350301e5814014002c1c007030441240081c0310140924400e0f80d60317140816142d080810105100f60300b0007100003014036001007178a17680071079041001d01e800030302c44054400024a01c4020340080f4288013a0000c12 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646743983 1250 646742733 646742741
    0x20c03030c030105010201180f02010f0c0614010303180b0315030718050f06041109040c030b060705100c08010b030f070e060309100b060c070e130210090f060302031e060112 76
    0x12001d414036600c07035040000290030b43d12080b07014400030507211042c40100b91450210f0310095020b08080d50000050318049032040c0e01034401038042ca04011a01410258000b0494100d0b406a40c84c4900059600c500300907101e51441007010004050010640c001e05160003100078200080807591703003d540e03400c584440c0d46403c289000540d611020088041550220590b0101e403c075001c210300001c8200d4a4842d0080c0081e1500a0780c1d070750b800b0001140641e12407203120100801854840301d0300d14150365a115144240c136030090900c0440b0020300d000d01d61060688101d1081d10b81541c1d1180d000f0400c0c031100825410400141582c8110180c46d00c6c00118042c2c403055000d8a1078280a84066050f43e114004031401503200b0002c03100034940100300032069680380714141c122034031141c22407880300b2018032010358040100c4203100c801c80d4120010708201d503071501458500c90b64603c0c00354104d0004503a16017454001040381440d800700744060503885030301410400301144840c0d40f000200c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646745233 1250 646743983 646743991
    0x903070e01031208011d0c030901140c0c0f0d1b030c0606060503010e060f010e0409020d1713081216021903110f04050c190507150f0b0415050112020c0303 68
    0x4012807411003072558007003130460150a01d040d140c001c40c0d222a0490192600007001c5181000001c4007081281c0c00039000910034594160740d1807400d040c00c100b001020350044c400c600061103682e400c0300c1c1c5180302140703005c50f103505030b25000c01c110704106800007072114185017101004454020000020000d00c600300140c0034580e2069101c0d070600c2e4a07500b0340345014054034400c80519000711840ea80c01100c4001e684030580b0041141c03411440400c04440f1080e800600062818900000280204000d800c01c502800750070b14945585111141d00d131445141c40d944040d404100003172140b104465550030302c51028011400c1e0044a12440e01c030740078190000c440e4600c1055150440d440e0511104000c0702048604003e6070502c1f00c01340c41c49100c0c800361016850006500001094011010364203103a4114000b20300c0c3d0140454510010042140704501d40ca1802010604034200b81c0310341e110a41105040c145054107180054442180e0b81a0f0034044c03e80030824041420340c00e101542c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646746483 1250 646745233 646745243
    0x9010b0708040305032d0c06011a07020402040b0a031817070c0e0a06090506060901091208090306070f1407150b0a1a0705062203030236091f0b0903070e0103 69
    0x10704040340e00080c0b4544e0381581c2460406d4140300080d00550080b50340380c11910300b03041d90b41c0b505400d916102114081c1c181b0203580f01d48003050025461480380c00800c0f03106a5517400704410490f581640b00e4010000102406040c42d2580500c1003048a40042000a000c1c07d80c4a0403155112400003035031070300b202c10500c900d40f644800c0050500c18000c0c2600031108032002800c082c1e8010009040c1e1340c491041c070003a40c00e0034816030180050081221000300d406002d882b1705192150b40030b860300c80700500c0400083c40164160702420301041c1940d50b2250b102c00c2c4a411181140050b00c080d0541011042c2d0040807454001140da01d000c54003030354040342c5102a82c8a12007030030060305040004069503509138904540ca01c1852280d003444d40350135890304006840703002d020300c4e11060361502e805900700c04018400740f00300a0003001c0b20001c900400c82b20040d0a075a220382d0180d9003240c0100090038440d1003407050100c01800d00140c03035074950140c100e8104541d00c80e014440d421007a441520 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646747733 1250 646746483 646746517
    0xa1208280f030e030c0c0d060e03030717150f0f18011805060303130605160c0b030405061b0a030903020a0609060e0f070506160321060501030c090509010b070804030503 74
    0x1c1d036505800341140c1c05020300041c60400300040362503621074100c00e80152003200990419800c0141c41d5100e4041c4099134003c680c1c40e1300d4401d5001d404883c01c0101031102000c0300d00010300383e40b035038a04003c3c140006014400c100c0c00c131100b400107a01100441c00e500034400c100c201c81962440c11860300900e00489041010b40c00d2007d1841201e201409041c003a0700100300d080340444003804c044003101c240e440c0c8150350701c015842601440340f00e0740f40149201e032003910004114070600c000c0e60040d40150107488140e11180b000d0035801008a1420a80d10f9040c800c1d114218003a83c0b040000c0c501900685808400f075a94040c221003002c1406c03188503036604903410b0b0250041016040002d411401880030f1404c00002501c180103c0148418412a100032003040522549201400d02880c0042c1400060300302084000b4250034050b07280046e05d0301d900c0c90902c07882140382030129840a0840c6141c0e9007032403108030403680000f10903540354200f0407001000480800092600c6088090550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646748983 1250 646747733 646747757
    0x30c0f1b01030504020d080304080f031609081504170d02161b0602063d03060b01140409090302010905070303020105060a2c04030e0402041805060a120828 68
    0xa0500603880e0385190405180c5000c000c01078076640540d00034583c00041164803079a0f03d107081c0c022407080031010803081c50084188180200404044683d00446032907043e0403c0c1c4400b8415560380b220780c004030142c600c40c0041008a0303410151042c0844002802a14000121071602e0590b800030f20b003403414004a21001d010300c401d0300e90703060045c4000002c000130a441d00c07200070f603251805800128150034601c002060104424581100405d407201036080c021103140240c81880454070082c0e994130309007031414880c3d61284146440c50314001e04030b54201410320486800404030001c01701c007959600d1a40c00c000c52000c0111304000c0d0f20035400070840e450160240031296056030b024410038040c1031041d40c100c1d240c4204e00104040740c0d41e030b103440c55566410100c034000c560b4070009400a2000a02050000100240440ea5890301009010a4032a40d040c080b0030b130710300c0c408c040c444204c3d00c0e009800240e42c10010800071501d40d010500c03d226034801d0101628151280b4000314450420007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646750233 1250 646748983 646749013
    0x1d06031929090c030702060a15030f061401080105060a210b130606090504031e0e04020c030a021c0c1707060618050a050f15061b0f0708010c09060e03030c0f 69
    0x80360f01462081e04035080d418001e5001c0d654a202400034000180c95250352240c1882a4094400445d040f20728000300c03c03d1401c0583c0241040c0d90340780c81e40081000080b40c1500140145801920041d268442c00341c60180c11030440d411589801102c1001c2c61502c00111b11b5005004d0b00502d05440e035914114994039041048500315440640258141800c100100c0d4000c502c251142501d9605d07040d00703086010f0304032455070703030550071940c0f0500c0402c503c0c90070300c000400b90000c1081c54007160790513a41c50301425200300e44403140340000f40441b0140c000080700035040821081c000c0300590300f08002c07030395003c2c02e41c0c20581000d0310144021f994010146001d01071150000801131007009181006003101a040b140200b01006d001509510503000740c07248000c80700d018100340c0c070402c840000f4145246d1191492543c41c441e0b44105e0748040340b02803040c0b094001c3c40c0d2440c2c4644114925110060f125500c02c01885540750000380100c4a4031031051141401e81041d44c4003418180041c0c00036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646751483 1250 646750233 646750249
    0xf14010905011206020306010c05010c0f140301052b0c08060f1302150a181e05011d0409060605091f09020a0e090406200301061d06031929 61
    0x19080c00c0000401074103640484502400350010350150356642d4420040c0c270848240d1900501c590303e0700300c16000441c0c3c410f442c014840c0169459503020100381424940c11302080c0212030740022000700c12110900c055090a84401078408a0303101e0105644425035510190386c0054000e400140800c401c03008000c104a0744048004081c6086001a8002c1601801007000d4402030070400185080d205014200d0480d0700c0d100310302d940e012240c94804480300c1c24061494a032000409400c04207843d80070b00418992450401e103400882c240c80001c010180543d410283ca600d41e07140305c0480c06440d4641c502e80b08040208c601c1c2e0501281c00f80b204101282d651000e068240305200c3e581146a01070501201c10b0011180c0c080300b5116818100b0042055032006441d8404803121301d906250103e000c0c604940003a2107660309910f0001c0d41a030702c400c02e0f1400070740c80b810801c0019000700150350301c20601c144240c0002000f0050b00c2c2c0700c80b41510f00c02001c100e0f0818141d40910140b40100c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646752733 1250 646751483 646751489
    0x15030d050a1418010c0c170c100e06120c07060c0215010506041d0a02040e040b071d10050a02010e010606020318040603020f090405030f04060305180a030816120f1401 73
    0x2180d143c80f400e4000c1030b40c031a1952400504020060801c1c40500c600401000080e01403502030310406000d00c20407503518801042e9283c000e030001c44911140368005d001c2c541c48901d01900d1503103005403140b080141800010005a035044083c05590040764252262185115207600246290b41e1550b90544516405030701c1140f04000400050141009800c4c8003c58054180300c54606600c0f400b80c000068096034011a428000890811041c0042c2e83c00b15030003141c407510783e01e001d10750401c0d05010012a12407030350340002200b14501c10a901c100018514010350744000100810009111030960728181e010200581c00455a19001900e178a080d0220480c201d40030840f042c07560380401d0124810061292084994400007000c0c800d042c4102c5950001a00c9960f03541c94945201400030038080d540300003010f03100b40c0c0051f5031000009076114401d400d43c48201d625920303040e0400940882c0310b0b8040070064188081c0c4c00072031650090302c04085540e0800315074160440602030682c0c005074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646753983 1250 646752733 646752767
    0x1523040615030507140a23010810211e03020120120c090d05060109060603050a0c12050711060c042c0c07020f031509010b06040302150315030d050a 65
    0x30100b000030320000c1d400c002c0394502c0a035214030350a0b0394001034401603207610003c00c1200b41034060007031000b04c0d0711207104401c098851000d44d07202c06210001c900e500c0c4c010b04680340c029460385407660498602e2000b20781c0c45a10a03208030095031021f041c28030b8017a001100544e444400f60b004821580703c000c461800500402d80c180001070850f40c400c02c0001c0e0003c440684d0016091441d030700c60085ea84801c603082001c0b64005d50b580c100c0c07100200a85e2141030000381c0340801041d0703112098010b01c844100720b40c1d5a0003440c116161100002c1c10080c0c444014010a06489506080c0500c0000e101e000c00ea0807981d2a5407038281c16403070424510007100c85c080c40316015040965501d00d4803a4100c1071168415031590301610104044500c45041650700d4400c140c1c040710314018049406100e4080c04000b4000003000c0d1041c407036140100e0100a50151842c2d9404091258200c041c0d5401034506810b24030b0f4031032601c0030901f40758004400b40700007003002070642d44175a00074510140d04a001c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646755233 1250 646753983 646754021
    0x30e040603020607152405090718030b090d0504060e092a0309010c0e01020d0c151103040203011118010c05030d06080a0308130f021e060d060e010803130315230406 72
    0x5081b40e040420003900845110b40c100802080700d0500c280b0101150344628202c040b1520785030705049c50004011100d0340342900c40c02d101c084c0b009203d0001d550442c0d000f901c5000c0944264801c00008400041041040c0640c42c1500c0d40780d404800d485403020f81044040c0c1d83c0d40d00b0b101f450503003035405a9a02d0010b0007020380c0c403100180d0780040c5411910b11385140c810040300503450540f0645011b5904a502036080c0032114988140003001940590301c00c4000b000b1180c000d00c940c07030b4903014000102c0d080c480194006141940030b0310f4060b201622a4003500d103451111010b40c4100c0b9410b80207034030a540110a5a0105a000580540c0200070582c502e080140c040ea241200c44880500090149550300660000b0010311640c00c04e513414003d00b8107450b2070131107200c40000d00c41482082e010004039000010001c901100b101d81301d044014810407001d042d501c0d281081d000c05c400b981c001e15940c0f041011038003040c1018040303c0d0102740c204007060800b400e0140945001000380000c021320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646756483 1250 646755233 646755281
    0x1101050109060b1e09040c080105100f050d11190306210b0c37020709060b071202030403060c0302030103121d010e0a0b0d090b0c030c07030e04060302060715 69
    0x107940113036468940340c031421114100180040b001c0a010b03904c42ca54001c0d00b400340140c003542d003046c0e000e4107940c0c064802c010705440182040b9082210303800d107407010410401c608140c1c0036554102c1444034034500400c0d8074110384040c0c0c288200b00c603814010002983c1d460140a080207644206e54610307891a00c20041c801251680260a03402801c04200d100c1c0024600c0c04c0c0c101d40c030075048401c02c050b862070881b040002d601c41405001c8142c0c11340040c0030f20340c00819000324910400c1c069680000395075052060710380e12481c0003210746800d0410740c42b090100000081c031a001c0c04440710700541e800343e1030f03501d1898164026500f10013204c0c24004480a005107551a031120100d60b42024602101e6215412001c00c00501e0150001f903c0b1000000b0825200704446c0c00080950744102851081692443c0240609000981d1710721b411000800c21400840d10541000e803099000800005441741c0d40e40c001840382e800030340d007141c403000a01d0040c92100590305ca030150401c4108840c01d40610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646757733 1250 646756483 646756499
    0x906080d1b0212010f09050d0315031104240f1a070f230c09161209050309220506090709090e0c0d030203040311060901121a0a06110105010906 63
    0x201101544158029510565507142000b8480f03040702402041070b00c10080031800602040c61040da043d101d0390a4401c840e81c828403d0500161401c000125220b045a07510740c8280750f80d030700655110362101b4030001d4080f00d8080b1544015540360301718251506d041240c0c030011255610020321402038044240350400c0da8409c8501c501e50150580c10034213660701d000052031401e01104070501c0d100503528100b0040001d003c0c810728030b007164200250b99030303200014805148203191900041c603004040084075002c0d00001d082500c40c1c0c00740c905042c00030010682d40c140c00320f0642040181009040c1d40f12a080c0710761900182c003942c0303440311483c200c440605024810301c00d2410255036080e9101c031001092001c92041c10000300050b80d80d004074140250780c1c1d00700340401c2d101c041d240d00c03801540e894904129550140182c40340c031481c10301601c0d0b050003420110071a801031080920702c58125a01c44802001404068880800c4600501e4086084800503040400010315000b0203000c518 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646758983 1250 646757733 646757747
    0x51e010e01080d1404061206030b0901020a030e0628060e390f130906140a06030e1005071b140106050901080a0602030c121501030506010302090a03060b0f06130906080d 74
    0x7506500f40708500c0e42c0d1f0b003414a4000c0040ba407015010080900602a440c101034006008200b0a0380d024401c40e42404400c0b5140d5005458071120040040200390b800d07800504014171900e0480300c001007540c0c0d01c00d481480c0440440380000c4440d03100105403c0d010b514418415075029085154041409000c07420840707210b1159188200d0078040341c5040385080c45500000a044492810f0140340e46d118000300f442c5410152403407281c011082e0115403117110f803003149240c12100000300b4000c1c080004080060070054200020052070319009440c0c105045201041e591103080c80c9040032054140307060031034443c1c0c0c1000c0c0c401c440e00f800412401e01c0c0004c16805d181d0300058016903e4440c09900701c0e0f00d1141450329001d800400d401c21456105441c114940105e0a0b20240b24990359600110101c2c0304d00c1001650065481b0401d001090243d400000c180d100035011074101d100007000500540c1041d0100c8850085807035090003184000d000e0740c0020800d0100908404001c0718001d0590 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646760233 1250 646758983 646758989
    0x150507050705120f0f0102030117150c090d080a021e070305063112020c1512061c05010204080f0c030a03030f18030f021b0d06051e010e01080d1404 65
    0x10222043c08603841e000512180040c0a404801c03102d0322041038401c14040d400034840c003075001d800c8020039116010b0200303040d9402c0c140f50610b0301c0c0741e6654410300f4400740c02102645c2e030032000c0c00745560001550f000040c01c40f0780503a0020040d400c0020802d039145291503c600c01c036504100f2082001030b400007091a008420300d44a42c03a04440001611511440d1400540c9101c5420315828140b01d40c00c040c038010301036a6401e88000038403400c2030101142010b03d02c1421003108220299040105030704150300590014298a800c1c1ea01030034a4854245800d4242c8050b580000d040019100401c25407100c441020b001c1c10070b2044090000340c40b000418000f07030506482e200406910045c0c0d511040d01d260080100101d0303006581402407420b0981c403c4400035119040818106007026000c00d120703858002c250408070700d51955124043c003005000c4288076a00c104000b240c20340300000702400b82c80c5d0100c003401c2640c50884400e2501603025115024001c482c1541003880080d141220b050b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646761483 1250 646760233 646760239
    0x1406120a0f15050c040602060f270a15020c1b06090108040501140a1415130e07120f0506071803020909030c07031b0602010204123207150507050705 65
    0x81256504208014070400b00b030b8000034510300000c110706a6454030240c8151440355003194410340da000e281c240407540a50b00407524903406041440e1043e0010080e1103540038060035078031882d0640d035400155030342015501650035004900464040400c10540b4002c410300c00068070300800f17040100f1254428100b201c1c0c10401d082000078140b0000350002050401d108082002d18909241260010141509035800041c010008500000e50183d203000c0003020092228003400c4201d035100300100350580010740c06e405840f40000303200c82c0c82004122107038045c000c5d56000c802203140007400d1403030060400040c072045c1034414101e2680480a0400e17a070b410703280304005895401d0403502d1030240071414840c0d40300e5800701004200707a89140c1c0c8161041405642881519200244d080c1c0c041c50103a00a01c0b600c107040d040204480000e1514954080286902c024044c042481e90010760201400500d600c09042044416141d4040e0f51500301c95103089402c0c0802640c80c1c0e03403542014840d00d88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646762589 1106 646761483 646761503
    0xe040615202a0d05060703050a14090705010305070512150a05060d0b03010c0c030c060f060f2405191d101d030109050d03020c100f1406120a 62
    0x15140c0d0184c0917204070360340c00c0e004800410b0000c08018003203440f00d01c03031358016080e1000b440c01201c00c10042d01000b414680050241c1d00c000e032100007040b074204207407400c100000c902203401800034040321142c10909000121404d81a8000f03d80c004000180e840c0600d5080d400180c42c7c080540080c44849080740c3d007a604e0030b44001d40070340400d94110a940004003194089804125182c8000505944030680881c8a00e02c03a00200e05400c8144200f011103001982101821012441c1ca140f80a881c40d50800e640b1070510003007401c1c000e060204804140802220541841000e801c1409040144000400160f0b110840e0304a00300c10b1400c0787c503541070600620002e2078200c0c008015114a468084000f903103e400b102905010721600e00424500c00c1c0035181401c41151000700745c4c004e0706541070b484500e000c0c1c0f8091045208c1c1c3d1170a5400300020411402a58001c0c070070301c2d = true := by decide +kernel

theorem cover : BRFrame.Cov 646582733 646762589 := by
  have h0 := BRFrame.cov_init 646582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646582733 ≤ n) (h2 : n < 646762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
