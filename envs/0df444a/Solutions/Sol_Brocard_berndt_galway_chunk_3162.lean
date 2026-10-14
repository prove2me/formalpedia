-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:40.328798+00:00
-- url     : https://prove2.me/submissions/3d304800-7443-4f64-a570-dafc20e08a47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 568525179 ≤ n < 568705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 568526429 1250 568525179 568525211
    0x615040204211101020c280308071a01120c05120c06040909020a05040212040f050a05100b010305090c010503152214070302030f1302010e09180d02011427030c0a1104 73
    0xa00c4a043c0c0c01000000c1c0c0c442101340d9002421f40d0000f610f100f4012a41a080040b1b002c140701d0900c241e46007226490360384440d030a48030000074000a2030f4500b0840c0a0140707041c54a100c0e00c180180c181201c06031246000400c180383d04c41c6e00400031598464444230300f582480401040140015581180b0300b038600b9801101288010b000280a859942d074404140901004002d5405030414103680203032100c4503640b40240035480c1e02034003090401001486a07100461600f100e1081a100c451442c1d450310380c071200c4010700d031483c3d9a0010203a560802c8204000c00350313020543c2041c00000721030000a02407400c0360002000d0400309801082080b945420740780003160450780714040c041000c02244011b03943d4282042015401c0314112041201242e4002d011042c03000c2000160f82000503040400c03402d940c0200d416090500c062404500107640780c0440501c42030503030304040340002d5500800b03400e591003a44100d015074800903510082c4824184041651582124101f0419154004a40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 568527679 1250 568526429 568526449
    0xa0b16020f03030d0f1508030306030c060a090e1611030a0903030c060b0409230d08130302030c0703032f06161b0507080c01080601020615040204211101020c 69
    0x1c1c06a400041180d00e07648040040d00e00d07150510209010100314522540020b2440d6011501100c1e91000c1c0021425000310403a030240344040d01501c940c041d02014002e155000f0640c03441042410300001440980c803c0c1010b001e0f082c801c0c030041d1125490b4000400402c5512040c980681040203010707180c0e50400c02ca001103c1c1d250400e010a1070840c103140c4010320440050030741150505003100b0420407842d00718500101100040c0602204d07201034240c0c0c0b10700206c1440e0109000034080b4015a55000401c0d40ba984a403044070314000c14100c25a040011640c8118085400c00da80c050280d450280c0c00304c401c3d1610302d41c044091041da2035540d902e403809050078280c000c070249120000c2d48035004082c01030203c4d0320000404655882c0c000d560b40300d43d03c00c0500d540941140e2200f6588180101805200142e004003225110721310750b03801c2c11202c101290392260b0301300000600c020750140d240f824070000d012001d400880305c0c20b0800180302c603520601d0441d0070851070503004d0381c0c07041814 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 568528929 1250 568527679 568527683
    0x9110307210c0b03040f050706030204270e030c0304030c14130f0b04020f0a0305060f0931061a0102070305071503090b0a060f170303070509010513080c0a0b16 70
    0x18203040070003410190305008081d00308118007000003040000340510300e001800100c0c414801c9919041e501c2c0030480880c02903000d0119008058052043c072a0080d42c19214003400301c40002a5403240c01140f2403840d4802528264143c00204041080c041030884032002040c4201070080025203500018941112015000d00f1403592103a400c606000385030301840080b0001380085594525910b144480da4000c0f89004001a0038440000d200b420200d45031000035102030f1902090740c03201c96034000c10750780e50155010307084800bc0c400250f0140305690b42c940207010320030002f4856040004c614502c08810045410366010b1001040000d10001e91072088074074035800881c030361081d0117040300601001c40313010340001c961030180446000c0070762255046030f0411080300c2d40c0c5941c402810080c04054800f014558100780300040145000f440180300900c4140340161038030048070803070301c441e0b411a00040740c10313030105d400000c0c94200703125100060501040700300d042aa02500b081c003040045500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 568530179 1250 568528929 568528979
    0x61603081e1918021009090e030408070905130b1f05100c0201030b011b050105150d0b0403030506060d0e0c030607050403170c0f030409020d06060302040501020c04092409110307 78
    0x2c1c003c900c0d100c1c6500180310503401080f00b00ca00742c0c2250700606d1380009019603044c1c0c0e0703e0121555581c400010413101107801480c043e018852805c1c1c43d100003848028080442e4402c854044400102245242c501c01c640080700c26110402c80b41a4020980701508054002c0c102c081181e50354540050910069590921340030035100b00c0a401200c0d500780103004200faa541c4450313050b00b01300043d0082445080b14800d0100e209800008000030b1138401c0c0800b4041000c10300204020a10981010b0b60005000d80580e10308100403600d01c044541748070018507650031803c0200d1140ca401d02ca555045a01442e029050508540390703071070b0032107540f0726204003000c000551100c0e805003070002d81105003501e001e880e181c40d030b030300c2480e0701940c03100151041c40d42c84c2000100e0528020710070382e400d1b180103074028020304140c4410312004145504043e900404a913050410103005001c0c1c1d0754220718441808240100c145c43c000c6e1a1a5080103603a100780c2244000303004071842c032500170340c48041e1000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 568531429 1250 568530179 568530191
    0x3190c030501055d0c13020c2119110d200f0601080729070f02060a02070905060d030806011809060e0f0f011a09061603081e19 56
    0x14070980b108110150f54440c0c13850600f0380101d4480882030506941c0da44090209042c0f241c03000540380d6100038107041e07000e030421382030000071280342c0d000e003040a252401302c0e1a107011580d81a19800c2c2c1200d604008000c00040815040350306060140d444501c9007044880401100d12490325511000307001e004012000014200c52070440850701000110302d0281d0704640006140c154031801c090107204081c3c440c0c0c22000641e641049204400384448a04c2d51303201146008020031652b00041090328a0340c01402540c0250351640020702c0f000303c0c0c580080800510702203940040d2390008140501ca18080c040c41300210b604818003603400f44003440c12900340015000c5030700c0c00b240c0b0b5410005480d45401c1300030840c0840d4080060191002c0b104039401e039030310360203045500e0344240201e00c88040c510007903145508030700014214070000107100c142002d0622000000036100070341d0a500054404041c85181803005081510442c03c4c0e5130300e4a040e240050075500710a00c1304c42041180c5640f18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 568532679 1250 568531429 568531489
    0x10614090402040e0a090302070b070c0501211407030b01020705030a0618050a0c0302040f090c03081308010f020a110706020309010e060f03040605040302060109090f0f110603190c03050105 83
    0x2d41158054203940e00c90151a0403e00e05940080c41155021809031107215004118100a40290b502c01684071110700c40c42c07400c24004450b54061100c58038540c1c00710b0440f401c0604c405016004a0540e5074084000c0d518020b00d0003002d44040300405410b5402c0780710244480d44010502040a0342c03c584046100c1c240e5074002c59500c0b1300c1d20f6016005014122062007081032440c002002c6030300846007804040d40d02d414038401ca0340d49480003004a41c4841040001a0707049000c0c00c41d40082e03218042c1c80c5a6110401820750b0704040c01e02400350390000307048810320740080051074210385260062803032506009001e580c0b4800c0d00300090500c40303c2d040400c40b59441c00103c40a00300100d04c140d4807030a2503d0180b02034101500c086025014000c004100c0c01c240748100c3c1d12640c1c20075100c1d07165407540c0e1609002c0c1f60390880300307854540d40b2039051080d41e25480300941c05035080c1503d0514041c0050000c0c000c4403c104811801c050400d0010040ea55034640e0380c801540000c1c81813802c0c0b602c28 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 568533929 1250 568532679 568532681
    0x12080307020304050a0b120f130f1b0303020f0f01140a020f041203030203040b01151202030c07020307080307061a10030b0a0806071101060b0a0c1506030213020a12050106140904 78
    0x1a84c0034540c806070300c4001281100b003000250486440110042c0c1c910b40b1112072007c00700c0c0b01100d8184081810000e814085401c062040165501401801c020a00000a2105800480c6d041900542d00000400506910411145c45030000302002046880c150120310b8048041c05070040c4280d54002c100c2c540c200f0501030440d001010415504031040c000307454040c0c041c0d0000c40c0d0503145040c0c1c00e8000501010b655505004d030907401d81e103800a041e0303c001006c0003500040c09003000a0428000718005880c01c008110142001400450b1215024504071041d201e00b072114001c0c002c0c0c13807500000070341c071100e00d0f0000034a1103040c08280085030102056001c03009a00150381c610460051000e82d03504600050302d43c801140090020302e807640000400c074840e6035030107000144880501004500c60841c4a21014a94800807810aa483d000501c00011011000707101130389c00200e520946801074461410076100070424040c662500e64040c000805403001c00310302c41d10008070417103682c0d11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 568535179 1250 568533929 568533937
    0x14210405030f0d14060118060c06090807110310020a0f0509031f1a0a030804090e160e0f011d0105040518070b041a2502120a1a060109120803070203 65
    0x1110301c9880d101c142c80d44880004d003402580c0081c0180b40303400403c541e5440742d03020b01240c0802e019815001e0b841c100741102d005014003002e84009503215007000c002030f100310007044407500401200300380450140c200760401c000c0c68440743c42580b04002d51210150801c818400e0300070281040c41d02c61011002083c201081c141c052000000c0e2120010755194141d8050344d03142d1060198040d010241c001841100c00803404060080082070004000d034440079040308040d010103006451481c10304071035500c0d0803d0560886260403440c001040346d04c0704c070304072030500402014861f1030448020145595032010107005140c01143c031200010860603941d10528445c11401c8100c0b989a592115180b0783ca41090080c0000c14103008507280010044200f0303510004800051002c0e00f80500462000c400b40a40c0d0480c0c0010326500c40d0064407400b0302080452034010b84640b81801c3c00225406071404c0e00a10361810b000d14038105021014031b80704800c0115501807255503a17610780301d005a1841c00303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 568536429 1250 568535179 568535197
    0x20402030a0504110111120a0c12020604060f090b06150426010c08010e150409080d1a06031329010f030b09030a050a0323090d1421040503 61
    0x20000051114809041e440b2510440c040c24035090942d28000045a10710002d503868801a0b000b800030310445008000142500c0000b410040490b40c403a40d5808401811585081e002da00a90108004d1004e6401044007030070120400300710340e0605961b45c0c3c420401c00344c0603a0080166400e00c84446100400b11409002d0b0b81c2142001142038400c00145403210820b41da01e15401c00500010b0700b8061072606040c1c2e0240700041c160340e034610b2280c4420710032801d24940d000c1d07211541c600c0410a80c1c80100031001c403c0b00c01040d00440c4080c4071481032401100c01e4000d20042042020b0b0b406001418098603030b209070350070081540c0c551040f541b800c3e070030b40a011007a0003200010761400881406800c4a2207180c40542c25655010165140c2c0201e0ba03200000c5142005502a0701f88039501000244000d00f8036080d0001043d000c1c01810b00d0105c44600480d4481d903001d0f109a6041080b410054550241651401100c82440c0c80d80740200c0103025144100b20002c0340030044144281c3d03900f50b07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 568537679 1250 568536429 568536431
    0x50709080709090206030115230d1b021c120f0603060c0807140702060f0315120c0a0509180109050f15010f0504110c030705070e0f04030207061809091a070c0b010e0703090204 77
    0x164892019002c0d0303804440d0f4812036500d000f00b20701e5020050a2440982f0080b600034040c94034a8000740301915042103920001c0102e0103080b0442c40f03003a48500d401404598200103140380c211f140a10844403c403482109000c2803070208040140c0c001da81000f10302c0350074180c5807a1035071440402c0440c010243c50507024000441082446c110701d2006100740413044400000242a070220980ca942a01000c16003104950400340400e00f0040e00840e0010900b001c062040c0002000c0203007124450713081183c0503000162100c41500c0e0030000d01038610035400c4140100e52400001c4100c5552a104070340c051501d402050031003590040c1640c0c4c42d80007881c1644d50325002d500e001034580b4080c0c007490813a0006c1d100440d4440b41860446d03481642d02d60014042241012810b8416030306002d80d0401041d5002d40105043c11030b070285000e02072248001d9102d11084041d9031010510007011a001c000680f04040042541616070f1411200c003c1c1d0b1030012070312a100210040c04080714081e4100f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 568538929 1250 568537679 568537727
    0x109060504060f0b061c0b010c02090702070503010c0f0c1202250906062604050c0a0b03221208040c050411070201140c150c070204050709080709090206030115 70
    0x100059030050703e1642c100140410840d0445030400106004401040b80c111444078070308404000b00b50310118030701d00141042c0745807a0700ca40c00141032910440d44840143c001040030015402d007406011640c58960802108080c50820b0003860340040360710180921744281c0b10400014004d1007120081c00e5030b8840050103440c4410740021011640c840d4014242c90800300140e03a80c41406191008003401403202034044000c803004168190242060b80d040c060790065008542c3d802c0d60740e1004141f208001c1d5240e01d4590b901409214014400c8182240b142c1072010002e8146800d5400c02c00700340c240b1343c02c030741c40d00c1c1810b481c3e03030405030040c2d40c00074035040000742144910390240a12600c00d03038480314144008058800c032800740804020195200d4080303c48800d088804282e88200310094250605409400140941e207041c1c0301d8070301280a131003050102d1203013408140c0c040e01c200300040c000d4a000d03501045e080e1005104080c1403c040342030782007402d0301c55007a0300d80d0142100124403403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568540179 1250 568538929 568538933
    0x1207060608061f0b070b01030b1009050a0905010501090504080f0a03140106120c030c050906070614040b010806010b0301080a111c1118060303030106050f07060204090c09080616030e0109060504 85
    0x2503801d210540c20307034030400c20f88001401e0118030201c51146134440503106483e4655603411404100140070800c80130810000401d02c41c0382c2e440b07001e228083c0030b48040394202e100d0800b81d00311001031308171091103410034003004040b03410002181e5030002c0121181e41e40740c0c8907000031801803096400c82c0981c6035024000140342039112461103c1907402080030000c140151109800300d07106800081c021460a0005200b40d203411000f40090078010316000c146401c11030080785a8940c103e0b4100da000140c10014460b580c3d00b00310f800d005d8810400d4031440c40d41080301b030701e959528201e0028886800c2d2074807500c040c1c64001c1404010b14004c10780e4811010b1618000701d2040402d109035000b46a0002c085011601c204403442c02201c2c003402652569007800c4044a1030f5104150030102c1c40001c20088000078800c0c0b00920040404a20008041400300d07001800080103031300c1a8400e61101061120f240300c900314000882c1d030355003400206030f400401c0d55800b400341d0000151059240104001c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568541429 1250 568540179 568540201
    0x50913051e0c18040b0409080d090b0702150a0b0a030f0605090118030c02040b0418050c09062d0307120602181008010e1b030a09020f0f0102120706060806 68
    0x5240c0da51071900036003541e03039040c1c40c0994020560414648031a404003004141041d41c080c0c02c00032000751004c40e590300f0b80d48031040c003a803100007400030341031b5220050010301c40210356040d08912944081e150f09a50115025141e5802a10031170400750748914040fa0f40d80c5481220300195440f01e00c0014005c407508080008040448002c08154240824103e5502c9910001c0c501b40b42d141e1101c11006810340c007400002d010504886e9002035031010314107190004044d880e802540300350f0041540140d1402403250221010700702c180251001cac0c610124040c1c1000020304c01c84105800410b038154001c0c002490254140e10062032496503c9400042c400e95070018a206044801141d4241390b104040c4100c054480b0030680c0080c8059005000c02000e1600190308000d0102440e4405164040d2805581c0c0c002c0d81c078000007e0342c482e618003c608012102d00012007040f61032081030000c210001c0d46800003147c408a00300c0340040e8000401074180d100401a18a17481100d4607413601d884060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568542679 1250 568541429 568541461
    0xa0605160206150a06141b0307061103100302040c140a090635090f03040e04030f0c02030304090c14070605041703090d050a0509030a12030b0d0209040305091305 71
    0x1005006960000b0b04104480c02c4080c41e408010346120180e03031074484111006d208001c032901c041d000c10019100002d660b1142110000800b0300616035a044c103241075004c039140310160041c611004c0c030800c03409074507404001084a4056401051442c40240101c80d00340030100c810701c00b0300c0082070100c0510751251607107003540c459840c1c82c030005000c41c00b03800203102e04410030480b51200d40c3d02001a070200002c1c003600280d260080b51082d080004802d41180c000345c20841e6208145000c20042c9070740042c030341d050324800341000c01c00c4d045150046134030b0344902d006050110343c8600304842c8440c842d00c1c03c0b2851224412490352580b081d864000080e1106960641303c40b44a11100b4440b8502001164001c3ca02e40000f09030312003d40c6426a555040b0035014001c1c0300c0e0903c9402580d450030300041034540d07c1210b5800e0400c000c00c901030101e4040c0a0b01e907020f20380944103031005031103401201d50000e40608050307456104610000c0c0b042d10101200c4148141000c01344101150504210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568543929 1250 568542679 568542721
    0x50c0f12041401030e030702101701030305030708070809070302190306090f05060f0c042106090c05040f0603020109051e0d050307061803170601052b060e0f0103060e0a0605 76
    0x34440702d000030b40110244c2e0400717a001c52503034004001c00b10061901c40d10082e401011420b110400310620140d14030f10346003d0740241c020500010800c00c000d9401040d0f19403050040c1408840741c00d050095550310412030100a003d41d4280801071a07028246405038025030b8006018441113509144c401c0e070302005007a00304c1c0e544c82410049110075050752402840b52800804085c00d26146c446059038080c801e54000c0c0005e20034103a6070004c40c90320300443c40900d0050b412443c4803803406040c00203c0e0240300d0849502c0f4076100003800182c2e4441340c110101d0303600301d940c80e4500c26030007410742e901e911560540350301c43d16007541841000800300140403400d0113036204005407448421000c04040d00394500800141d134144458200c07456407a08142c01c107106140c2181003203040c07505109103c0705e624824213020400c040c10060310b10b2134025440a408030a08843c80342c2030100224540b00810b01000f8410b40d2144091140c4100400a4140c610b8000605205038105444403c5d0b40209010342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568545179 1250 568543929 568543949
    0xe010b03101505030d1e17090309030715210f06080f060f040f0b1f060c0209060312031b070606090b09150a0504110c0706020d110708070501050c0f1204 67
    0xf03103450003140b03c043c403c4980c0c660b0300c8021030015421207008244544a004d10011910302017042c44442e584078892054240250342c3c964064003010f140180701d070300031442c2921a0007104042d5600058010342c03030004624560f04090b0055840c0e0241400d100a9241c49203402c9001466a07400603080c1b1124442c0340a070340854442e10048200761208480291407003804407204000030b001001c0d800c0c2e01008030484414026005034850340fa000c010303440000040d288a203d403056141102840350064001c40c01402840c90810500c1800d00008001885205a82412091010241c021607510300e42c4020201b06081c0c8079003401004004202c000c1c0d0107a0b41e0320002801100e00c107000c0c00c650380c3d00244510300461400c5c04200c09003406180c4d03d00798200902c207070750f002e10342000030401402a42c0c018009080416400030000d09411482040d50f6101507420400c1c0000460302d034094510a10b8540e03642d8034204115440d00050345000740d998460804604440a4040054401d549c00011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568546429 1250 568545179 568545221
    0x20c0f0a0c0e011e1401050702150414090f040f0804030605070f08060f0916050c030d06090b190b0706142a070312020706090c0314060f01180e010b0310 67
    0x204e8554200c0405030400c80d8072640310501490a4200114482000c1494030b5858031089a010a164881090181c4001c200200701400a00b140c84460840303a102a03582e01d01910b40480f0040090030040d001400e0510f20070003050034450079500701d40196030854024400c508107250000d10306520340d1105000241380c007000c0350251a101101c01e910060003000e100040d101d41814190f91002003000d2020310031308100382c0d03a6601090024050320020648001100c500d030000c04c0c2c2c140c0c0c4850610380d100b00144003c6000e48004100c104058803048031540d0f840e00240d1400724020036200394000307078454071072042100321141d0309d609013a130440c1c1c09042044071404440050302ea01460f00000c0c0803507440318104802c8076982e8050410240900e5000c14011b03540e0715404004ea52540060f9034070420010020200d042c01c01030241c014408500d1408190b1500540c889400c05801800d121552182c2008107018000d4000405601c0020292a403c44e04061000c000300f40381c03050b29a402000b25 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568547679 1250 568546429 568546439
    0xc1707030807140a081816080115030507060f0201140f0615040b1b2b0315050901031b0503010c050903010f05010503071e2102030610140103020c0f0a0c0e01 69
    0x20000c1441e40f030729aa0903402d1810b45001a289094001c080111b561070150844030281e00070001006a808107804280c03007a4242240c150940b05030341c202c034000e24401801000018400130f50b1030110380c1145001104503010102c100e001d07065490710001141c09820621a040c080c41c4181400380d00111841a070801e01c4010264490245100d404181c59081c0903001c200150306221400d0145082c1c00c1c0c07200c01c0c00a03402600d00440a9258024992110550311150b58040c03062105012400d10404030313403494032000034000a41400002c28048009411070000c040d03c03410040a064001c00a02c22904102c10040003070304594602c0d8071941c02d04414071004500c0b803040c28141e0304054043e01420b814450100610a00307400c141e809102c0c0c03198005400d03020710800c1c1860703149075141038030105501d00400d89440c0e405010310f00c400341d084908002a040d400314064005100303080140e00c4468410042d81410022001c1103490301940710304008205411007490291450786e100103020341d03219 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568548929 1250 568547679 568547687
    0xf03060218030a030912080f03010602010204050a1d0601031a12030c010b09060901060c0f080a0e040f0203090705090c07020d3824060c0706030b03010b0105030a0c0c1707030807 78
    0x603c030250129031601e0017881403000941c24110034034040d540d002d1800510801280c81680b0907405003006035808038050203135140680c1d4600003002c0c0f1032003000c0f640807030045220100c14060149814550349503a09842001060b8606160700c00040c41890500301c0b81c02e800d5165448140c80206035403030401030f9005850440c2c02903010b1180a4200340d081d03800e0010944200c104103c4c29580c0910f0469103070009030301d00008005100340c59460b182440c0c8a00140800d548140310101c140c6c0c0d0060003041710008000403002c040740c404866040c89a2190480c8004510940380080e4201e0b100700c0c01542030200402d00b0004402904207108156811100c0d100700c103501c2c40107016200b00c4054085036040b00100b1481640c0314880c8142850201c80d2000501d05a22445007004143c115450801c0080e0701482007020701c50003038009100b80d00e00c0c2e00000b001440001c0266204555410901100c0c6105000f08021203074007c05140c0c40102d41b40305c801d481d4104010442c0000c01180c0001ca01c6803003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568550179 1250 568548929 568548943
    0xd02150109020c1f1404061e021c110d020406030203042001120c1205090c040c02060c090d06110301031a0c19111609060602010506040b0a1e0f0306021803 68
    0x452000350031441c40c514242180d21a803a010101c0c49520b40c40c0e402d1003a02130300b803094040c42c0304000005e0440e0900400290230003655003a0f0440e248148480d009100948003c1c090078030f4050400100c08000d0300c14016030740684114080c0561001c50082403190b0198021030040780503401c00607640710010301c0000c07404c030070030034190004000840c1001d48010540059007030400c50b0418115120103041010700310340088990078080d0f840b268a048080c05c10b40701e00300002c082440038001515000308100003a100e4040000e01440d481c074a180700f40041540111099060a80501d58a50f03490800001c05001c1c06007946006c0891004164500d5294044030407080f40b41405c0c0507046240e2005413040300710f0114924250151100c1201000085440343c00034281401002910604055000b421508010020790150b45081c504007610783d2540d4160b030441e0003007410001500303282030a440e41c810b4107030300c1603414100803c3d0200801030690040c1c1038851440c007800441c0290f100416070307500c035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568551429 1250 568550179 568550197
    0xb0c160303051c02040801091a1f060e0102030d020a0203031f0501021f020d05010611070608060303040b0c07090519051f051302040b0f0301080d020a03020304150903050d0215010902 80
    0x1080400320610038100790f008414030310000181000c0d42d40750100c2c255005c803441100c0f1102c0c901010790361250051501ba8000815004181c052a4087c000010031132050250506101040c02c83c80d0142c1e2080049a0180c2c0040c2d1040d51200d07400380001c0d50382e81098808610041010402c26095000310b2603441c103c43c0140d004002c14400c801c08801d004d10b55024040e4816020030800d0710340203207801418002c14480c0d450391011461100b0140c2825601c0d00040d00b00441e807024082a07550000964050720111750b041c55031044408810345c07405009a0100d49414103003810483c42d07044030601150b80d40600c45091005070ba40780c00c181d550b018000803800c54011307081c40030f02084c14060b00221110441030001440d05850b103d1800c0141c100200c614028080003005000d481c10a0205400c4c8000d00d000030001c1290320756001e9104c2c0654003540e80340700c014644c40323080188218002d400864114090300c8021107400402900d03001441000b003860000f4000006001046200f1030385840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568552679 1250 568551429 568551437
    0x30519030f05070618030f090b0a0e0f010522050a0e070f0c110a0e041412030a0b01020c060a0f02010b0a12030302090f090903030723030609041a010b0c160303 70
    0x707100c040c069901d034000340f00540c0d90700da070b4044a10741360900148a9000c580a9111480e650f61700d00802054030307036660803a08642405002e40d03a10240c200d89000055901120303880084204000101c6040c05069940b0981c407044000200c011030b4010704007010f44105175002030f00326481e00b058803500703d0300f80e408800040c3c021591b00e03017146c480c1e00312480c99071085003401d500000303c000103005090740b90048142024103000784001c029160741403144541d02c440280081c18226890100c5034000180500201911000740e200a43c3c401d20070b040e80031400034001030f05e40341026801800d02896488420140d0b1805110812510b4555501811180ca00c5808801040c06560490107504400d00d5190003070030030b5072203900603551a4046031281042c1070045880c2d140648006001168941000e00c0c1030b182c2c80c4106510000c2c10003181d41c0407100780d5882e03210303171214500120106d14250310a004d220b80e1000120f034488604000f40f01c201d40e01c100301e60b00310302c000030250300c0203086201c000e01003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568553929 1250 568552679 568552697
    0x90d03091e0f060f180602100b030d020c0d0c05030601030f060f05090303190e0f010e060c040b03010e0903121005120c31240e0f040605060f0303040f03051903 70
    0x264803410140c5241400c51401d85130903040c0641c2c40002d601590000000f58101000307000c140d0780c0c2340c400c10175049800c50080902000d043c81c00781d110a00c96034458014108803050b00288904124042c1c002e0a01500302c2e846981d423404e0804620140c1c1d441181d1090400724a1038a81109004540c0940f0142002e5442c6441c1c0015010040707001102d51074096459090465603840e0502402851800c0680007083c1301c45458025030810304020020f81c0303101c0042c001441074410340300a480c1035902d0710106c40010744070084007030319500441c0182c40007078400c0003c0044015000304270f041111001d0314140e880041030314010340c9921110180a4000030b20807080401c40030b410380030080720501d140b030400b10341d40b00c0205001a1031055842c01c120312901041102d0042070f8040c42c000920709110140700c0d0742000222641156001b52000d00355580701c3c000b20ba00c0303580d510102c0c06c02d404000d0850780e80c5c42d91100e4070b80080032284070580d07990007070380b45108103c000c8ac0b0100100d1a85560780e8080c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568555179 1250 568553929 568553939
    0xa051b0906090711010b0d081306110604020103020d0216061a010905150a210504150e030d0b0a090e1f090209010e04030e04240902040503150c090d03091e0f 69
    0x81e00107808004c4040b9034880301e0400a6448440010030607500403180c044c3d483e035880044004c110b10580c003d400b00442c0f043c0c000c4058401203042d030b8015030309180c090b940f94101c00989019000d91700c0002400100745100380b0400106034084044401b40c440c000000380322450064a00d445141701d810b801c02070101c00640c228485500a083c8400d60f401c106072400d1280000c009410b40e0300c001d050415507546c041c4000e000d008009010001c1c01002c040c0724507007800007180c0d26802075006d03500000d510342120070140c1d5215100036000d40340d161000c0000030502002c0075581c60710b000b0702c9051300d510040c80d02c0001059002d003451b05a0060280d40c0564a0700140a08549008005500701304881904556a41e1785004500d64814205903000e07110700c1c1701e4888154501c4c1503000ca8a040e02c100000c1266481c00f05000e00200d1101c1041c0c030995032011240c183c1840342c2143e442d80805004085001c054000c1c01c10340540d001d4110b6408074401c50203801c80500501d01034804154000041004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568556429 1250 568555179 568555187
    0x50108100504022707091a09010f020c06030a0914010203041122050a0c0e09060306150415080d02120f0f0313050a0302010b030c0429120a051b09060907 67
    0x10300715201038944139001040702a240054200180403008440044040c4074980c0c2d80103d204003d840d0300d075407407203110705c500c3d02a4005120700740d02981444000150400414001e01c00503c014201615071652450001401c80042c000e1244c103c881c09044910920b81c4541482541e104a5004e03011840c51001d0004001c800c0004401400c03600c21480070f03000740600140541400303888c001501094280303858102914148840507224042e05c41181040502d581c00641b0a030429040303140c080500e0300c0000030802601c0000d0000202032075011000038038010000d1010b61321030165007944c2443c00c0e03c186c0160b1034861071903603070740311542407140f142c0c1051644019900302c180c0c1c161010410000d031307079044d050410100003036015035940c25550501d81024030960030700c040112001c115842241c000e0b201d411981c0051000103a0444100c4e500607241c3c502d00c069568400001c03180502c21510304a503494844503030341c01c000d11103440040044c0c00c0484220340586001003266403aa924074200b25 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568557679 1250 568556429 568556431
    0x1140d080d060605041805040510020a030902060f0409060608090c01050a0302040e0a270803130203032a0c010c0317060f1206090c0901080601030b04050313060f0f030501081005 78
    0x24448110070044902214038501c41e0398000c01d02601e50a81303079894541e06401d440854000d480340309013040d04100000303c0115103025001c043c0f82e40161110301c0100220010b010a000094020b90b0000368441000844030250040300c05608041c4a4240c443c0c5048841441c10f98103080d0551102502c2c061075030180020300120355082c900181040e0340c49a14903005803080c0c0340f08840740c4d07442030300e00f0a1400d5001c01301101c0f020301700001203482c01d668515590303102c001c0081e0300b001c0e01d40300300404541e42801140c0800e1440e41002040d00030440041001e0064801400942d200d0b0718082e80c0e0319401a12a14a21501a00c44810030460341c840f10f80718100c010100e691050912034628007580e01c42c035461140000312401051640b83c032584040c502004035214a100301e00b8040100a88400041d425041d00d50000035010540c45900c0e040c0d207540201c1d608140d40080500011406a901002251540c0e5290b642c1c040c072180d00c18402e40441e030082c081d00746603030801d82d80311a100800350401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568558929 1250 568557679 568557683
    0x1c020708060a0c051303061e1503021c0f0503130614030106030203060d061112010e01081906020f0d05090d08040b0105010c05030f0414090901110304030c020d020405010806190501140d 81
    0x62400c171a11100d008115601d40040324000d40e18070882568490300c400d1200c030984519010001c285214170300c0003050855100081c030a1030301400300700c4881403240c1a02d4640382c0c003012120400006103400ca8890b0081c0201294070390080310005005449501050b00ba00e0b81e2140c010324590810500b00c0295100070645604a03440c2c9015100284551040c08000c0001110151301c518071030203030480081040e0f22100426000000500015002007800c21013a1140d585405078802c0d140380a001074017944c2180b4100a20125811159841da42c104a21401d03401055400ba81c07083c02c4d003542c0039001510b000c0c007c110b000700180401e5001d2041051000d018408980c14009030720085a040e84c419006130250524840c0c12590354100302c80043d8002c84440001e0010307480c0640d40c1d00c1c00303000080c4041d003004603030320051003551184241c80c074855402400900c4650386aa00c442e9a810301034450386540403482c0c03801e920310802441003905a50055582e029042002401c00a01480345c0200f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568560179 1250 568558929 568558937
    0x1e02060a1b0f080a090911041707030b011211010314180703080f0414030a030e1905060a0e1216031101050f040806040203010f05010b391c020708060a0c 67
    0x5400200c1c0022096000091141100f40e40c0c4100c901e0005141e004181c1c8001c3c941ca0810f42c12103003501030b0030309440079144407132044c00000c8a0643c08034600b03c03481c0e10282440e02a1070022a06010410040039051301821a03480c1411510004404032880000f40710b04010840010070038900100c445e038102d50400c0001c40314166129102c0d03140d254450140c50341146000070b01081400190400300310003410440140c0151129610098549814124142d2007502542510a071425074150420060540a8540c6495030100213005c2d00c4140c40c4101c40b0300c00e01c0454455200f031480001c0c080c803818613a00c1c903040c0b29480c55541c2c000611002c1c0c03505061110510401080000c00c3c6d02404c010000b050041030307141003e0051600b154507446281c601c1d00d0400d401030010030745200c200c84081940b416108112041c51101021b080120130380a40350103c0d0095668000600148035100c014851300c545031380c00d440c000103980e101c0080c4a1400a604120005100c040d9035522105401c500b0f401c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568561429 1250 568560179 568560227
    0x405160c0209040311030c0303100e04030c062403080924040923040b100603050411100c020604091d01090209010501051308010c050c0f0c0a12021212071e02060a 71
    0xc3c56421900b080001c1f0100b42d1000c42017282c4a5100345c00c1c1c1c402003003403030403594080c2801c1e2801003101000384409815a6119a540200014080100200340c401c1c6111400c03402d81780d152200d440c0c3d1018040b24814007880f002d6a6210f003445d007c05195590341a02030f80750500c0c000c603200281244c4a81c100c04410300c21000c0c0d49404400580b58444c6105001034607132407808922211100c101130b08420201403078071041200162503240381440c441030880f46c00b200468101002c841d115195400290000b40100b400241c01410385c21411045241458654524024146c01401c039004072001130740c424204401000254011001130460280c240e607450941d5455415582c20b6a01d4080c2c1c0700001440040d00010091003844a148080b85400c0584003903044100081c01480b414020340694040c040300c0d040c1155942c070541e610f0007070303001d094540400c44100201507980110750183e844000c2260000395080d100030075500e40035801007409082030b0300c541080380c010000303000346409200300c09 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568562679 1250 568561429 568561457
    0x4150513110c03091804030c1e0c0305030a030b0402130302090c0f0a0206070f0c030c03081003062901080c070b060a030b090c03070f0503100c170907050405160c02090403 75
    0x50001e084502c020402195924102403c0c400b00744102020340c603401c8038038418440041c0c0d03c1384000c0903040d04030303803c0511000d5804804d03202ca21581350080550820150002c1004408000740100c01065101040061301910a010a070b200b8880000c06a0589480500040c9400b548003900305480c02d41079810440b9a00072000700382d01508200c00960310034010801880e0f403089840396803600314607108100e040c103554090920141c2d48e00082c03d11202070002840c1c44807880341c500c000e50b04260700340582445000d6445110310012010130580f01c0880040d809940152892809110100f00592602965441e90741510101400240d8081d030701e0302d0004049444d20b100079019822040c05031400f8150704040601d800b4450344100340e807148802082000b503502140280031018160790214000c0c160791000c0700da12510145200e40c002490092284107400041c0c00d0007503500c269407c02031a1110361003610100e034964009000920105580001410310000f01c903041403090078a240008030340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568563929 1250 568562679 568562711
    0x4060507032702040513050a0303050705090607110a0905010621060b0403060b040f0509070e0c0903011803030c030203060a120507050907111504020d030507170d0507020c04150513 79
    0x240041005001c80c8101d15065143c14410160000d20f40c01402c00110302c6c903178500b80c4400341e0301005001d06554100160a040c060000c40d240c0c018020300c8540c2c0c4103420324012180c101040c0c00c50340240c50306000030070106141e00c01e85058030001d0b1940450503c5d81120a480041e40c40713108150161101c20000c0d0055410000d4805103100e05c80100f15440b00d8000c0c0302c201c4064201c80d0303090504120074007009a01c00308040040e10741c540c0c03440140c1e80d99400142d0162281c6140740e0303007640c038003507403036000300b44da26200c104045c400d82d070621080c0c20710001201a8042603c0b9035034084004002085161881c44001c1c09071449a0261049207607280e000403542e55048840401060100140283e10b102c00e01034005031310600c3c110720105080c19008640070f5604140001e0501c0303000a142c00c1480616840100c1313081e076500c059640c03a030003039a28001410044c2c2c2d085001d03119507105c3c1002d91a00307014805c20588500b40141846280008020340b4643d88500c0c00c00541d5070b4000d103811428a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568565179 1250 568563929 568563971
    0x71203170c1902010c081512070608190203010509271006062c12030c01020403030507060b010206090d230d06050f060a140d110a23120406050703 64
    0xa01c0c0070103403198034540341520100c950080000071645804505202650058071a60300004422802e1604658003800f0813100b10000480caa11880307102e500085807a0b02c403640318440e4403007100640414581c0c5244a05900080c0902d82e0320000c03050025421118440bd48001c0d001d4450b110140146001c20300350502c0901d020810380b490301d5000500095130851050441d0a00b0101e1081e4a107075907107aa4602c00d210050400d03c254181c500440340030a040080c0c80d0171001010007159116a2498003804561181e28115082d504240300c0130840e60010034218800e9000d90060081480104001c07034069400b5a9600c0b20295042d149003019034100010304408800000c00240b03103401c1c0307400c0003100d55034003810a11916003040300180c09640f140208000d00d607548241c603160039519540382c018001c81828195180004070b80c0711080c541c003580440e900748081c00d100780c1840c03140e41c0a41031481901d90485059000e040854009106940400c0d4005202d140c0041c0d07150740c6000700b100040d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568566429 1250 568565179 568565191
    0x60d050702070501091203050f030a0b061306170412080907091505040f110a0c02060412060207020f032d0f06090615040c121802120a060501090c0207120317 69
    0x10014105200079608032101d840070300303090300482c4852040d541c7c000b41103200d82aa1040111000700c085500324110750085040080010201c03a100c800c840007611440b1b80d80d124990000d5050a03110340d09114040c0190f0090390005403540c1c5081480c00c2c140d401ca038010303165501501c0b40004c0081c1c20000c0d4814004216210041080041e00d0300c410002a185074800f0032841030b180c0b102107050328a400d42200e6803070007942420412400140001107403802a94403445621600c010800d08020181c3e0040217440d10031076a90500e10b2200080c556603240c034107104044c0c00000c2c00005440c0e038004c004001c0901c600d8048a04819040d06440d050903001d84180307203039601840038052807200c0703220408075107982030350108144076144c0001000e40e0300c8000480b04042e41ca20410700080c40300c0d0718403600c480d00909444200c200d0b040b0b07030541e551071000f02543c41600c2c1030000f240c0c0c100c01e80900d0341104455401042618100000124903007a4a1011818021001c2c84c424031090888000c03032140d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568567679 1250 568566429 568566433
    0x1b0b0301091409010e0a020d03090e070908011503050c060d0e0a050a0b1803030106030207320d0e0f060a020f15010f060f1202090301110c010507171302040b060d050702 74
    0x30084480810310040b01501d0300781c05904019030148401c2d000501c1141c1650100c51500600c9624207007901c041065800070840c480b4100f0401241a400041c400101c1e41460020000c140141e6800d181861a500008180c0c4c1c011110032051407602101034580104154000903500050344c0f1403919102d101c19080307520f9004004101c082c04002510b583d400480100646407404015071021f489100c140103807010306901058140900451506005540b440c1c01400140c00c1034450405201407400580c0c51494480c150380d44c1c000c45c0c465420407400b414043c08841e5504080001c105185c0c2225040e9411403143c0b100389200380d8000c03c44414a0000c4400c40740d62541001c1c800e1900400c82e030085020710408000c0600b0b00344d132200b10000d1400e141100142c440c60000006805454040310110081c4000b08028108400661200d4008c1c505034403107603040c2601c9200781d0a0075808440c8060130491542a0002508064101d1039510304000c0c1018a8006c60303460b60340484809407400c01c016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568568929 1250 568567679 568567691
    0xc020c06130e0f0a1404080301030201050a03141f06030b010509120f0d050c010c0c0206070204091112011a010c020a06112103040c0806150f0a0b040b030708071b1b0b030109 76
    0x828010700c10121004070b070512081703440c0341584030b090707030b511040c88002c2c1005800105041000c4c4a940030000c1108001140c0b0420300381802403401c0204512040c0103803142404000484030302a01c034102ca4440103845e1217080030362440810241c00d02d5140d2501b40c5028529488801c00c030705004500030301c0050740382d19450b40002e0461508441d60050081c1c1488454440100983c2e00c01c41651103542d41260046180c406519140c0001b42c850794a0980100722841c0440481c00190400e20342e005101c071b8060800e4494400440e807402d018940a50010402d1405100310340c459000d0159100c620021600b00101d2406c40321801c0c0701149010542c0103000c4180010002117184800013414100e00a01d02d034100201901604106104200d121b03251504d0700d403100741c641070840700007030212800240d25181e6940c1400300c15802207c040e0001200714000482182c0501c0d026900134a6022206054010f1aa95051600c14140c010518020383e200d000520b490000700030740c06400000008030b01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568570179 1250 568568929 568568941
    0x221506021e0a03080103060b120d120b09010b040308030c0c030711040b03010606051b0f0609070806130510021602041506090b0f030601051b100b0a08010c020c06130e0f 74
    0x203900c6010406103003070b0004420314000c2944030740a6815603401c1070b00003400356144c10009403089000f40c0041e255000715584043d00380e800c10301c0613908450131442481205400410490301c56024040c001308010700340300500110b820b007070256074081103240f0242c1c50b0a05c03021446182d0b8010f04e200b116000c19980035081141040d026005520340241c2c000d11078281885801360050044007420030408009002e82c0701c8a8400304160b400c8480000107941060030182300d500d84801441c058076040b489100c010a03c1000f0309001c8454840d00700014004414040d803418010754040d00078004c0c3c004041c088207015a03a035105594200b02441d843c22003252414030043c041c106150300c0603c042c1d0050002d200c40f480301c801240c6d4416803d107030880d074551016062100c401000041c81e5800d218102140c000460107911501d10740800f1940d110b107540d0350303510340d500b44c52414600700d006820049184045040076009040e0702c10002059400041c3c441d40501100c0c20708039950f030101024401400b030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568571429 1250 568570179 568570213
    0x90515040f0203060307091e021204120203030c0307120b060d1401080f03070803100b03090304060905090c0a2d03061a120c0d090606060e040b03030922150602 70
    0x45841201e080030b60542c5880700000b40c807001e4030303c507030000f980e100d040c0c0031601ea880341d2200740181a201011911490740104a424000c0308603411183d2031b445402c40e05d0094000016248912900d020961440c0d0310140112030411480000203141501da1101074424ad403100090420103c80d0000042c0740110100300440d02481a44660245d41044400101c03a800200480b0314140d0084030703542e966228040c0f440703d02c40d0541d000f000b01c040d020040c002d240d2008001401254010b80e0780300b600c281c5071000c0002c03548065230524048041081000c2c0d10700e0080202d90140c038485040c56460402d40c001001d0890018160807002a96840050010021207910100d604400100140c05c21a03215284249618058040204450080b40d8103544062343c4e0040cc59080e441102400303003d60710000540003402500e6564801c1c0d042040b550194100002614032641c0001e18244904d01d00c002400c04031040303038245d46181919014042c011a5505281c0001410b0690040a0110100041130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568572679 1250 568571429 568571441
    0x114041401320a03060207170301122a032003010e01060915030803071107031a040b1e0a0f020c01020a0206061f05030711010b09040503090f030a08070803090709051504 74
    0xe010200b602598400301c3d103861a03118280c0794000340040c0e440c1c2c0d003400d100c4202c0f95003110b2440042c000100200707900f0814100604c607240b03c0c90028510b2440d510141c45034692a654105506450302e130300b040403c2e40b04c034001c41c1e032020000408210344000f40c00b03c1c0c03d680034400212002c0c0e454440410001004c0d1089018202002c5907040302d850441c4c0d40d07a00d00b0310000d00100c1c00c105225081c6e002c3d4030000d10080c0019644168115410b000c05401c41d00c110000700c0c2e042d203201001e0b60015507180d0580c50300c091424040a860150790743c44c5400072004128031038600d24515030a00010703500b000c092008000400054000700480e02d0403400b0001c0c0301701c80030466014446207401c225002600003040c3c0c0d4001e111801c2c0f83c80c01d200c5d1104c009004004002c001a4040f86220512040c403d000c40241401d000a40340c034484005060285503580c1614200182800c2d402c200329804038a02c9409183c000401d202603410042c5d9408000055072815512405d86480c02003500d485071801e0300c149 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568573929 1250 568572679 568572749
    0x30708030306060d0203060111031303112e051312020306060316030b0c16060f0c0203040e010506220905071b03080601080405100e010b120a0b0114041401 68
    0x5620718a03003000801e050b4040c29411462142d0007001041041c2e0113040540b84a1619004480d281d84041c8503050105000348006e85000c101202103201500b064503401096442c03860300355a05000001001c074401600703c0704107041020500c07901000d07a5254120000130110900c4e1000c40c0d40c90790040500b0b00001800940c46984031003210342c07942c480719903010b0403241c100007002180e0369807400865a6214992496000845400a842c10400543c1c03107060010b1980c8401c000800350004241d95074405c1d8050450f0700080f030401042580342a8004002c0883d0070044038a107076078000440100310b461508452510b0352100c040000e80d0303a201060a0010b10101c242d10001d80103501c0203416004041c00c80b45c10002400001400d00000300b158107000490200208122180071400310300802000303a0342e51250400c1207030b01c1085400017070344544982c2c1003048501c00748d00c2c1407041e5030700481994a164015460308504060740040c500e84a009192044003404510140407000700c42c0748442c112 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568575179 1250 568573929 568573933
    0x2150903031308090402041a0706050f06031f060503030a110c011b0f140f0c0f0a031703040317150103051806010b07030e0324010b09011d011101050a0605030708 71
    0x1008040400c0c1d1060310200d0343c100300802d50f1400440e01080107031103542c0050095070102c401400c400780580c40200440b50040804001507180c2c0404072100300400d90701940d1661200304000440c007040340000c2c3c00c40300740035400a202c90362980803034107541003e201000422254048a0003501060020300c031500d509103001d51460300c4d041e80070300642403541c4020b0202d6211190110070407001c10200b00d0500f034110120313411181c01d019015650395000d8145c0d80a00d100355004411400c01d0340c40300041e00d902c07a41e054400101a40083d185404c02801501000403a1481240300d40210040b940140d0039460350a1081c01003000140580e103020b04225030b080c07a440d09038101014085000e5066900e2410130356a2403000742011190083c14400182d814007481d58801000c20912455a07444144070505901036aa03170112280540260354070325002c54000c081d4150f001c10407124170300307441c8014100341108000f0101d44608503201103d000785015600c590a000e180f49c1000403400134100740b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568576429 1250 568575179 568575181
    0xa02010504090f02121f0e0405060105150717120606070f030806011101020301082404120807140a080603070f03031b020604050d0803060a05010804020105370215090303 74
    0x4002041480345208455480c0e0b6601c014540061003034048449615480c2c000c1c646a040c900c0d40d8052044030716900c0b04110204510000b03601d0b100000051017150400c001e04826032a100c1440198102184118801581081240c000800c0306e540400070219081d421910307100480d6540082d101c000e80140c1c800c2600341b04000006103c614684407007545440c16101c0d42e20781070010b0711100d03014103100b80b881d40044008503244400144e004d008000400c000c88000c0ca090204008060055402801240c8541b070000e0001e40079004070f9070000748601d030014524080d07204d8911103130031600c0442c00040c0c5050a01286190801400e400b800c0300c1401e4501840c43c42d80d000d402c12002440c0c45c940b00040b000e1220641d611142554000e0030003602c507260301c4d040c514200e000f65000311101d0b8070640e0421340c00b05d02035118096043c811a4107845491030403d87d4821140c550288040e1040c511554124800e11944d440071058460740c500d4009007216000744038440c900c004028050411540180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568577679 1250 568576429 568576433
    0x807021908060c1614010204180e2b0302071a01090e070605180904050a050114070801080705061206210309041410150909050f0108060915070302090d1704170a 70
    0xa200c954105601c0907012055078171400b03629000e4019a8050b03590900c0c0015070300300c0c0c04101c0c0c00c0302d64080b20107401d40b4002008444102982c046109a5080ea07000c040160400d07107020390300900071107000700744400340706031060700032400c0000036041010820344a040e2a81030070b0007044810702600a60030182c0c1080403602401803c0460f8a403001c2c0b00e5410200418148030061100c107820300d80103c028400500760042a66001c1010780e100e1001604900c0009074090010482c10180c070401803d17140380100c07154044640b40f0000d402d043e809241c14012040a41070780524481013030060f0051a03c540c800c17002c00040b10b10642e06000700603004800c112182c1c0d000c103400307819921200f1450039403581104088880b110340f50004001d492501040c40a03804a001c0228100c0d03036007404817406592194095600d80d03d950032a0710749881e2100100e0b60903801b07034001c0c00040e00040c10584266000761281020084c94420148440400040502003011000c0085c600d60410030000c142c0c0311119 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568578929 1250 568577679 568577707
    0xa0903200309010c0804080d1808010c020a02062104050c270106180801020309031b03130509060301181a0618040303050a110a0906021618090807021908060c 69
    0x48a10b1810846401d481e081007150070416100a8088101120088207aa96000e4040e82d1020489540c4011014000038501c105001e100031300e50555010300a201c015501380140c42c1c01c420210006c000d841101c0c00c1c9c51801c41c060310380c4a40e010344002d2070518404000d005911002010007210b0304100301040070082d40c9041f40a0459403940b80c8a01d0b042c1045508440d00007960300070307041315400002407200c2018000068040034030014095451400c00124540d0b82c1d220f045541c140300ca2090070704026031300c0d04162090740144040c0010494614003211404100300e42c80381210454a40d240c82e401144210080d02c4d84054240ea0708015000d50040c80c6a40d10703c000c0008042548400008441503d035402c400a1082181070701601c400000d88050f0030002140a01401441521600001213248000280840c0c12040c0820403003140540000040c014555040e14050010069840140c6421000e0310810410350ba000314802d0401c030407107092003405030018107100390900c8801c0300740c505 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568580179 1250 568578929 568578937
    0xb01140a0806040b0417030f0402090106051c1d010c030911040618050406060e25180501051308120316050702010f080a0e19030809060709150c08030a09032003 70
    0x4825130002c55501d0b031500500380400d0510981c410440401889000350550b006079000c0ca200b280e440303525a032503403001c8405006e220162405400001c1e8010707034144d8030780c1c00018042c421078080360502c120b10740e23120f083d51090704000780080d0359410382c0d1081c041e034808641d1521340204d40a0124514080c650440e00b6040b1107451031040c7e41e1000310b8100302d025403000c001440344040d404400d18102040c8200240e55130700f110000c0143c4a13040f8001c5206020518101c800c06080011084c01c10b07004450b141c10400300001c00358030417280454000800c1010f034011121003280300342c0d2490000c0e007125408040d8112001400707014014140180c0e000070640107100c0d0a80b0f4482003581ea8000301101404422501c40c1503800380e641d40303002c40c45e00d01e080d22246038000c4d1141440d0380c03660703848aa07541008964420004442960610440440207500085246189803103454004284c5860131250b01c142d13201c100513951440c1820425802a0031030442d500004118003142c80501c80e0161070f441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568581429 1250 568580179 568580183
    0x31e12092407020d030905030d02060610140708030c04290f0d1e0b010905030c0a06032309010b0109080a0c030212010207050a0501090614070210051801090b01140a080604 75
    0x3200c40340c5441c0e01010556015a40060084000d20864103000c3e0910329140603490080c001d0821241c03d850001802a000e024043c02d038450600015a080b1404091001081110101009483c0c04904400007541c0030759070075003009560b14944240030a442010071104120911a402501011420081600d0211281c140404c0c1d0345c42e500c0c9415070040214881c0f190703a41d0090038041e6141c640c103501c0390482060030b89600c80851380f0f40f0109a55682c115003501e0303000c44100424000035103e5044200458032800c180c072212544405c2c00740405004541946039030b9565400c0b1000da40e031003601c80c40200301d04800741071420210f481c1e5032030724101400080d004881c03c8290030742180f82541125801ca40040035241c2a0740d031803038041d000e0f101d040000d0b1071644c10300543c0403009010800e40c0d40a0300b90f54009200c030080611424015000061074000d100d150712200c050030090a000f080946481622103d1040d03041180780840d8504c00c0b60300c9070044002d050140140700c0e001a074290000d07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568582679 1250 568581429 568581469
    0x10807090c2a02010e04090c210b15100e030a02100504120c0906140108043005030a0e0d0203041406090d05100b0904110f0a05031e1209 60
    0x80c40e5000300380e6050b4006400039003000840d94115499000d000e501d016058400d82e20300e64503806250402c01550340e10803001d05400d403480c5040040003004051819211400c0380303001c0908449841d00c0742e03180300480f00d403c5072489541e060380092501d500840700181d00b60400c420140c071600c0109644035180f0400070f01070441030b028a1f105074054001e070350060004d4041400020f48030320f0484040384540c4241d9010034200782001c41c60000c40702c090140c010041c0e5440420742c2e12902ca55403c2c01d030800c850210074003e00b0b03440018000f014410080d000341c684817150b583c1050380e90241158454042500c05410020480c0301d0b066020040b64111114480d907682d03004005000a00c0c01d22070034821552021980001408004c00030516600c85004142c2c10001c4e01c4494042c82012681250001d1495012200c0c500e1700d441c018444220341d0b00b000d048954080d4507280400d00d40740c074588003072501c203503072051506425104120a0b00c900e80146111400c0200e91004038149900c540c00c410120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568583929 1250 568582679 568582691
    0x1804090b04140a050111041d01050d030507170706020a080a200c0304080d0309140a02210a02030f01051b072001140a090918050705011b020414090c0901080709 70
    0x30b54040142c85565600034000700f01c10901d5107420141a44544a5000d94070320011100b01019400c0310898103d50000d4403030383c0e0301100c0e82d500f1200e80d0f101c1ca000b110340140082080c00285004e1014101c4588601030040e5600c000d00005050060014a404030a50810b061811340f15410f01c400c040580740c500c2c0710350302d46041c1c00300c86045008076006800c0030b1150f9109070190950640160070b030345000b251107880c1e803000d60503200c0c2c4800100c0310207034200031200b00c0d0f00c030384124100710400c007581c2420580700000441d038000790402e0072504001c90144e4550050000132055580708a03501400380400c0c9282c81440c3d50b41002d00a100c102650b403042c0126005845030340260019050b00203010005a964981c0d82c0b0050001041400780014051900f1503440c0c9804240400a02541d001001040c08a103800011500d4442c0f169102007a0a07001c0170050058595000e400400c02d2100c81d030f2215032408180051402c1c0e410858a4801c14a19004000d42c45003c106075068880106005c140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568585179 1250 568583929 568583963
    0xd030209061b030a08011703041202010e090a15091413020f100804110a030203030904090507050d0606240f0f05120406021b070510180b0403081804090b04 68
    0x103140102540800000c10704288007550b410048024004481c071601c0d003d00c6030f45c0741d03100e03901140c10079449401d035584204814884104001c5151101030700c1450504800741c15140440e455240c1614005c0c02d481c0c50711318104040020301d000002400520600b0020100a4805c00701034a20162222461310030b038981180940d160181e0442000e4001750800d084820038240050109404407030549245844075903d510342c0c54090b10120840c0d8000f0300544c10300c4021001c110041c042844111800d01c101c0000090135140c1843c40341995005040005000740b500d40c0e034461101c01800098260426040d0781e00c50b09400265411241809103400d02180e26040b000703560f18450240e00740d5013030300c8d80c0d0100000c002c125002004c081410301e00c3c1c0c2c0d00d448010544250742c1c80d4540036180d07000000003203035020f5038881d81d01c000b0303240c0d009000c00ba6003c0e0399101984a9038415002a5103c0c1070004d022400008445804070b8928029141006403407290f031581c8602200c00f42000b0802d1503800d51b4101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568586429 1250 568585179 568585189
    0x150309070b030402030f0706080a06050d030c080d0e07060e12060f0c03070c082a0a080d110706060305010902012d2f1c0c080d05042901050109170d030209 68
    0x30070700302000458501e10740300c0c40040d00c070127030448500c80c10a040002c08101030410364211080c3c140d1603102d400090030540d89041d8540c0019000240159440110f0a0f025100300040c400600301c0fa01e9540031408150140007070300805001250060384054184048409044a00390f0320500001c1441d40f6515181811a00704241113406454000003045c181108180320b9000d0b41503068103c00c1b00c1d00215001c008544402026402400d220000d0101e014145c100340c0152015440c82d0381d801d4508411941d440c001c5403c0d90b001031300c3c260345d03480081c4110350300190700440c105841c11079500841c400f2a0480710b80103a4800490400065406554001c442144c40881480361100042552000707288a40d41d54480d51400c01c04082001001440090091240006107900b24800314508402008004090003000c0c0003280c40030510b0100c480300fa4406500c0120600340e40c1da8110880d4945000148080d4140c0c0088954001d034051000d0030000004211183e080ca5003405031700d481946c40003030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568587679 1250 568586429 568586443
    0x61303030e031c0f180f140f060f01031a0103110f0d24050c070c1703070b09010c0206100501080718050a03141036150b150309070b03040203 62
    0xc10f9021420040102e10010f07900010f081c0083c10740104105410414184506a40c0d03080190022411600c01408074642c15010000c04070407004551600e1000301c2c030b19140800480d29840c04644040c018001c0110031100d80c01440e40c074056055003035045032540e18a85030b041000f04d10030000381c9040710854982d162001125a00702000b0300d28040140f1004080411160030845202e1501c0c0021700c41c9901c5005035680c080d001907514002c281004192042c03500c0880d14549588000d000840008401021340d612441240d070010507141580351000c0d00c1c040c0c02400c041804060300e40d0610059034401406030f40aa51403404510511100c8a103c0c0c00140903088a504082c03140804000e000a044441010f01c0301700c0308442c0322203490540a000ca4001c08829400a21903514403002980d0319029524000042601141c0c3e01582d603a44012419048514000050700c0768400c01c40c629150303203104d100d8480210342c0b500d140781101c03171561146050700445c0c02c3d011000c40802c05648080042e6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568588929 1250 568587679 568587697
    0xe1008070215090f0f03030114040213090525020c330d0c090b030c0a0804081201030b060f04060312050a1404300b280507080612061303030e03 63
    0x1000c6030f050400007aa180e0b9000d540646241c410b02c0d40000d00310500100b00c034122020810400080d500c2c000800010b503210350081c3d101c29801c02000f1901c042c15200321800303503e49000f01c2903400d80e45154400c1201c07e58088a013035411504100c055a211200c603880344100003450040000c441034401140390f850941c048a01800100300d9007500303501c1e0307840034080858545030320400f41c2d6281100046440708590341282c2040c207102243c0301c24020722502d6080783c41640d1660404184030b2000a03401426030094451411a00c24403000341000001180203002c01c4d5814060181942c03242e08203104545141010044001410310100c0c0c0f0070303a03c0c05e002520b85c03000959100d0351208041411034501030424407401d05200b401130f96050f08807642e2440c3c1d80c05940c444040ea42ca01030740c861800c10818480c0c020390b2900100c0180310703091085900c22801d0307440b4000c07503041c01010311000c00000501c4172241ea100c04107008000e003042030a80600d030741c10700d404241d00300c0b0070341000d00f14043d841315 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568590179 1250 568588929 568588963
    0x80f06090601110d080a06080a020a120c0902030a1505030102120f100306060b040501140403030e0d08040b2d090f130908040e01050418120e031f0f06060e10080702 72
    0x45074203440e4404212401211844007d01416440b0040d03961220030280340250300980542d000c1000c06424220560384500a8040d0841d269603008640d007640e108440616104c1d0340c40711224140015854030601400e030603802141800c030020691040c680700035013411224510310000510207905104e1480245500402c14001c2960f00c1919103444d070414004c45001c10005c20b900200100900e0940302240d8165941000381d5450005000904802d0103054030400c40402020840d6210980142081c4141c030150130590180e0101c2841002512007400007070034010405d101701072343c4520781085850411107040140d0311490b01c05100910007a00010010080410300262800c0420f400740e04a40082d10240a0104424081c0d02d0300c9100e50340c028034402402666a60140c49101d01260828000c0c084034500241c90400314280701690701000600703610b90030060030804060043c07000500d2203090440984407403074000703150581240c844808112902c4000f850b400d00c07c02c90210500c2080403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568591429 1250 568590179 568590193
    0x80112151b0305090c0d030f11010f06032004050c07030e12070f03030f050403030801120609140304050a050a080a080c15040c080607081504110d0204060c0c06080f0609060111 77
    0x302401410041365113401c10b00419660340c4160410b4000701030b506902d17542d05e0032900c0c4d2140741034a080c60391503020140c640d43e480040d080341a01e40314050266009a00e07802e00c050303c035501032851144280d41203028900748401c0c8050b40d0034640c16a0144d03035150400350303a04064a00490300b284075604850b40b140c4200d000010710652044400c40c10351307001e42d8036500740319049442910148964880100056540c0b00100181210190020f41b05849404041288003140d2290200032050b0400155550000a401c0003e8034140c40d094004101c06d8851210032482c1009a030784a810b0a040688040e1001600d03028000c002c1c049507071000400303070808409013010b08058002060f076028119046c400c2c00d01084100c0c1c044c000300340c45106580010ba4202c03d442c01440702410f0f480d110503051800c140580e081e07640e00e03800940054681035031107545140321402c05103280040c0c2d91084050218000501607141024543c2952000064481d111991506401201e1401c1c4a00d146100c0c1d002d948 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568592679 1250 568591429 568591481
    0x30603030f0302210a020307080f0601021011070204050a06060219020603040b0c0d0912080f060a150203040b43020913020616150c022a09070504030201090608011215 73
    0x1b82c0694026480c640d9840410307500c64403ca50700307103c10703611140581d021310406502c04030950001248000703e040c0e903600b40080da50105050b92070554040030b04603103c402c240705070f40e070401031201ca01e412359400503840c0c6216000300f6174030b02c0701400c00f07000701110500040c1141586021103002c1c01e080c030b2040000c085c00303080c0200c401c0d0940300d48400048070000410a44000c01d01130b04c0c0101d41c020b02e00300f50145000300d405580c1091207009030541c00f05000004140e1240e80240000d048401c05c0c0312400045901041010f4207026003d4091304a1429025041911902200398266041d6044001900c0d9105050000001c07a60000d600020003c0c0e184100002c881803441d83d80d10034107001c401d420244c031b0400180c440c0c072080c2070010392207081d8151000548040c00841720440141608640360081e01054003220101d40000209000140410440d6400741d0f000006001c60f141500455040c0028050300d00d0701864040c151407601d0007058030100e0305600c0506544211502840000404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568593929 1250 568592679 568592681
    0x2040b070b011802270310090b01051207030305040b09031e0a0b0901020a05181801080604051b0a05130e0601140f0f030309060c0f0724030603030f0302210a 69
    0x24018014442200802181c0c1c43d1080d000b80c0784c0c800c0c0f640c042032071510326034140030441c20060040d03039925101d030a41c100104070491180000e0180592503030140c642c1043d00f8810b251003614050700240d8401039007080880e40c00f10542d0169480e070f1100c04d5590341404006482c240040c0c1c014200e1104031461340148003c00246040e8841c41045054103e950f000846400c034000d071441280850410090708521415664200d50348210042640020940c040800799840c0400d800241c0b0707661103d004d200602c002048040c2a0010303c0c00030940710400b01c80803800c007040c5485010300440b403001e10a24035240d26082000106080ca04407030496070340707062186010420304074441c069071030350610f2283c60801c0c1d907040c840071102500961910150505010155000d5881510240a07464405000b01c0050128200400d0350841580142a0010100d0017155007030b002003060600e00341c8100b0029800803040e42480ca40d90034010f80f030b10011110703175281200d002d80a050280c0900208004040c1c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568595179 1250 568593929 568593931
    0xc0303030117010507110c040b120a0309030b09030a1d030a1406100602370f210305040f0303020c01060f0b0406020601060f050409050712090b0f060a0509150402040b070b 75
    0x2ca100038015511201e00580d02c1c3c8070400c2030700b240717070f000800003c103a400c060f004807240c10405001c01c489804c085030f52034206490b90000b00c0008078410404c0080c4140d9043c8540c10240c1f00000e9441c2410408010303101070703900c12044007804d00c0c1ca540d029a075036042c031080c45116000502e14400301d90219100c0c0c0c43d00807c03140480c60b0118881c2c00b042c210f2000075100d510940c20903200c0f50022611500080321061540e031f00d0704500e0700c0644071001500002c4d0014116100d00e00108201141e044041d054a1441c0840010035280c2010400841c2d101c822076002c45405081c010307500c5024440d018050070494200241200c078030f140018800140c3c82c01001158820303401d581c0c2607621084112003410780e69410000244c0c0c00d020911405885510080d0043c1890400102102d041800c080a86012010540360504c5070810061107020110702580e0202003150b9600d155030500700060070300310010f03150b9800c1d0300302408289200d494903411100500183d2b11541d0300c40d0014501003000c040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568596429 1250 568595179 568595219
    0xa1d010e070609090c120e030c1204090621021516050c090c030f1618330507060b0411030108060403021c0509060904090c09060f0e04030c140c03030301 67
    0x1880a40009440a940c0b01d86505880c084d1b407140c1800b40100f1005024100202590f070b885d0100300100e1042110402c01d10300103951080300c0f02d880394176001c00481281d00641c441d4000d50341c030a07030f031700050410354013550440e0b54115543c4124150054815406008181704840c81540d02c03026001440400a076240c88584221b600894a035900074801089020580e8003072925141e00c0c0214510481c080305c48103050100d4508a286440e00c10f0f01c800d0b9440040c0d1144007642e80c0110352a110300c8000d005003044d0007441e803941000045110b0700034403c0c4030718840640500e958080000c035980e120341110120641103000d181e103d507101ea0300c2c55103d84040e501200540f01d80829441c1c072080310400320190304001d4981134140030301c00e400e10007d0b9202d4040035500c107513135507000800100303a00745507805481400700c0022038034207011030300742d68001c2a0880791200c604e034020840065484511154141d6200c0701d84510b0310381303c0807458600503e03645031991500001c000400c00c45800e03490540d000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568597679 1250 568596429 568596437
    0xc0c0b13021207051c0615060801090b04050c030705070204060302030109110127030206071a011511011e0b060d0903020a02010e0d0c0618030c080f060609010803030a1d010e0706 78
    0xa06110300d400e5a070ba4080c403610740c00000c03150140c5400c1215054080c16103011b920b01041821000d0f05c0441202869000900440c034180010320008c0402d00c80d040121406860030059030a0180c05031206000c001c3c40c400810800007568011921980c002400031035010b402804444181c2c80c0517202c440d110070304140000d820300804180c00307640e000140180303d540e402c5500203906503002d0240c241d00542040d201a03800c01942400a02196109402032001d04070500e40415407a80090110030b4a0740c1055440e03042c840c41d00c00e0140b940a00d9074650030000c00003e20034001201290240c0540c010160445141c07401c44c500741a008120028010704c00d9030f580030b29160040402c10b448c40c0352400904405c501d6601408198064500c14900e04070a1810950300380d620f13510200c091100d41c0115a01c2c0d08010025030504d0ba04001c020b80050044a20b040e1943c1801c00c0e0550700c4c00004c0155460743d8444000080d86071001c81c407581244103120081c010002e0003403642c0c1d910005440360780002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568598929 1250 568597679 568597699
    0x230d0b030d0f08180d09060311090906100c15050109060f0e06240f18030d39050c010825030504150c080919020a06030c0c0b1302 57
    0x5840c0200d140c00055034151201c03401c40e120802c1c210350441c0001d2201c00442814902c803130f0646004c0001034140e8540743c1e030f003c0c041400c02c0b00050548111400c0048419810b11079808580e90380c1352080d0340030b038090301d8017120307200c1002c0100c4440380c4e9124040d1011602507100c07100205a45c0042d03040e01c02682082c048503984403580c00d403411091040c840c0c44180130010841c1440c180b102d032142c2d245501280c5c0041d807083d030007015255100d1124010341c10301c002010004680362400035040720108034060580c000303000c0b40140c8161203400480dc041107a60803001840008407464610f943c104c44083c0c00c0c40801458681e030303034500081e003040c0450340b6140040c101500181c0306c10b03001d100c1c0e210031414580c4801401d9024242c0900100c0d20140051400d00350042507104483c0c8010712503440000a0900d004428103000c01694100c0c01000411412400341e00c520085608541c40e601d800907100e10300c0882191095141c0000800c41032992003400f00007540c094034178481c18021a072903141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568600179 1250 568598929 568598951
    0xf150f030f0114030d050d0207060b031c080907050a151e031a1e0f0402090405040605100806010308030403210f0f0b09010f030303050c0c0d1d01081009020a230d 71
    0x9151805d0b40d16100084e002c00c144109401e090300945001c51051b00d01181e1b030445000083e0401d1091580003910740800038a40404030707840700d0519008034010000d03244050820340800c0f103a030780c24005c40364200c40e59440003401034821035241003d050940341ca0032200720300d8080200503000324032051880501601c02c6484510b0309080c1d4440d00d50380015030400703a060001c24007401e203030502e0205500c568240300400b47c603101c80c0501446144141d000061502d824840c1e6652740143e5088500700781c2c8403d005000042c407241c11a60082e8142c14452039034050380448040c00103c0b0300001940c1c0707041c055440c08003034860b0400c04d0043c803100d00c03e103d0405410148080031500340300d07400f0040c000c20f0301040400e00a5100b183c00c00c608000041c60482052043d91901501d0a08d0b04e0001305d4a2039504400c7d9100300c48075454400901c0d0132110303414181038012051103d80140000554005803421000c1e0103540810451020600c03005801c461100c00700510381c020b8003900c100c031810400e41c020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568601429 1250 568600179 568600183
    0x7060209031c0c060c0e030615010306030606090b09010f2d0b0d05161805040207020103091a06011e17180703051c0302070c1a071e120e0f150f030f011403 68
    0x6d030560014000341200d03901c001c4140071001c1019040f6060541d10700b00800402c402d0300515010b0401e600380030504003459824018401d00507070004102c00e564400610208015001d8200c814072076105849119851200410203e00c0f503900c0f580f243c540008a11610a0142c0c1041703214036100203603180c204030287d40542d030045e000190240600d89080c0d0900c210310b000d13809810402d006150014100300c1c5c81c4d682e044101040e9503951500f049c0042082160344c0d1100c1408111200c401781131500c0d0040c41d001500c00802094210346101c3c0040009003903d14200500c4104106203086410b4240c0d07078100291035185100d0100300e01c00c030f419407894400f4000c0c022103110942c00301103030311200c4c6000509880c2e640004c000c006481d00411600c0003281e054520001912544840031500390032516245541e01c0449400b14180456140100c80c241c0c0d84900202001c5015140000780e0000c00d201603e641c8502d0503c556012004020312002d4440c46041034141c03015021407107240c13501001095 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568602679 1250 568601429 568601447
    0x1c080601020717150414100b0d020f150f070c0b0901170c0d0606030b01122009031929010b1801020f01060602011e0504050307060209031c0c060c 64
    0x15026034081d00040054810a025140d880903d40e0196800040e403001c0100a18900344c2c0d040e43e0742c0480d031600c0e8031904414003502400720030014040002e0203040c03012400d5410010030192090b0304846020400d600e4020010001c0440844101c0ea0b88512440c0d8406030b40043c4401d59804110b094041541d00f0390748111044800b0507101e400600032401c1c50708180060081c40501211810711100d6070741101402200041d00e0141c40201e10400c8031800180b95144003280e0010040c10002c8800034044e00e1070244645000d10070015503541090700100e45054252003481c507410512404a80601440d685200c000b08406049518600d000c0e102e0f1164071303c0280a0701d0680351003089901724a6050000c2e07204a0314060054440081400b540d00e821a0036a42c019000742c1d464010200e0f50450200e07041c1440e01d1048410003407410192540d540c0c2c0e0161080040c00e407940010707504810360301000f640089101d0140d040c0c450400c030502c02801c0c0322050104940c4c0c40d041821545803903000350080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568603929 1250 568602679 568602691
    0xc0c030105091c170c03071b02010e0603100b07060603021c0305090d020a080610090606030228030e0303041a0a0e0606092a04030c0b0a0f05030603030405060c1c08 72
    0x104190902034202c030781d42c0ea000f5100141404041e804441c1000c8840b07802c070340302e41c422101264803032400c202d01400d07908102d00352110f003018840c01d0800503070700941400702d0408259038940d10ba5030366805c5003981e243d681e000f820740c1d407001280c0d52041140507000702007603e02c280c2c2c034110396540080048560700f091603001030100c0d0003807041141c0c6040503051140c032180000d26240406640d55295030521800f9241181d2000c505041481040603901800d8000c0c80c0c0c2d840c00b14500a5250000e0f4064580041c0d41c0c81034007581e032072080840d8440d40080b50a014000181d9550b070916280030b20141d000d224205402a05460010300b0041040c810810300700d001c00003402c05a41e5150411809400c0140100403210f0052401b084c0f200c21038084015042c124840300e50389030301b581071041c8401c50b69840886601001c1005503219540290081020442800c2407a04d948405001038154000d60300942d40140000c80d203422915800140b078601c1559281440e03c440004102c00c40712454200d800c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568605179 1250 568603929 568603933
    0x3010608030d0e070303050d020f07060504050303150a051e0402040f0b190c02090601051605010507030b03060f150d050102070605040c0e090f030405011d0d030c02010f0206060a091d060109020c0c03010509 90
    0x252341c1b106615400615600e1000c041d01c51a1000a41d100300c100d450941e42500c16520100c20031041c407003420340d0451202c00448411301c5851500000a409200c02c12004100d038031f0180e4407071850348848c0c050350064982151030440d03042d1660042082a0040c051004171f40b105140c01c142c400f80240e0802d070719260081c1002c00e1540c0d542005480301d500000c8441000700e0710481c0348000c21020700c2007900900c4e0f940e501107540d100101c209883e2a4010307014000458203a01405070f40d4512440d10011000c007550018440e00c002e0504d50b009010307089001c0c10080c00c020800c020032015244c49010f41d05055a00380300c0d0340f900d01c0100d940d0031400c4400640c41e8400c01c01440b4540c00b9103000621620114030105845000384086070040e05501c0003100400c20f990b80716021980c0001d00c0c284c4510862008080c0c603d00303100010914019841110340c46607456400c04e040194910744440102055011502c0350752792102d005009600c01c1e0b20b00003282c041c152041ca190301d418001c0c18003560300040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568606429 1250 568605179 568605187
    0x20f1203010b16030c0c0807081203060901090b0310061e0605070201140322080c1509071203050c010c0206240d1515060c051504210e03010608030d0e07030305 70
    0x40000c41443d48682c09405100300d60100d00001341c64038001e40050300501c2d0203413007641d02d4415010300d03000724140005c541e403c0510400c010303900c5041000307044405c0e40c000802c41c1c03000040801d0804184084460405040500c046440301040005482c8100c160400c00c0c522541c40d80704903014004c4072402400580003450000c103d2500102564100182800200c5080c085111750700b45160100401c0b1408040420450303900f00043c02030488d120004c408090441c505554500d842e01818001d2000ea024001340d05c03020f05110b442070b9003030029008020400703c3c0b11240b01a40d00d0808980702e90003004810800c000d800400100d800040b80c0250018507894103e0341c84d5480080680306456885903a40300ca55182c1c47d02e51008002800c00d61a81d1859010034240715007001903d0405101052120082c000020048050303948801d001880c0c04080710b00320001103440038010300c4e00540c590b0900c4000b0480b074901000800f20403940900030447c00310309130b51294585d246888080e021030000c1c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568607679 1250 568606429 568606447
    0xf08060f0a020d060e01051003090b0f09010b1017072609120715140709030f0515090d11070f18020c010908040305010b01230a0309020907020f1203010b 67
    0x20300440e4001c0088070025080081165444084070b1840d4400301d1800c0e0000010011804d2141c1784403072000c103910301801184503030707103e1048642014249840f950783d0140005c0760401d0039800a01810303001400100d5032150100000c0c01c00340165170a000550904020541031401603100b00c41450724401040e50b9030552083c00c10b1031a40040000b0083d0241035500400b040c0100b004021a078480d400b159080b00d0844407841c122952a00c0f404c20280745070091100d55031308003441004482d84243c420420704103078909141481aa0140310b1040314201003840414800420b86901c4802c4d180d40356000008209040c60f0b4410310340c811980c0000d290042840900300069440340c016042c06070141c941103400f00300c00c1c2110b040d04c20580b0150300114042c4101b02081c003c8591050342440c0901c0c0d8132070402c030540382e044401041140e0b5048005030340103059000303402525071a6002881c0301c00318500030340041c0d12010056181c0c1c82d0390180400710350b07480e00c101050b68140c1e5450b1544038100b100d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568608929 1250 568607679 568607701
    0xe01091d0c15280809011104030204050604020d06080105070f0516140f0304140117040c0612110705030306090115050f030c1b010f0e0703200103110318070f0806 71
    0x1078a8101c103090100040c400d000c081c00c1e440c2083c0c08400b021091211a0042d0081296001170300342c1080364102010b9070706541c5584192415a03404490018890300c403100042c000748103404521180a083c604002413068040d84094441c141c0c3e904c0d007403a0080c040900326580d1140b0003402400c1600c8030848404168408030450700c002c441c034102e6840300e01c0c4103825461600140e20440030b55407150354500300b65074000c11040151200011881007130070a40e40b80340c24003805000d01b904200041101503c12042a000040d40c00c0710194500d40e070307821a00f020307a140c2e40211440d5026040c5500006450000070100869040785651110704045007190268502c3c3d10150208a01c010705118102d08404440c840320641000d11000044600c8110380c45819212403016800e400e8007e440100041034070f031501404500315802c0d000814910440050b801400ea00d00c81e070f807540000bc4208424510507094203d4034820000440d03107016500c145d8031540c1c0d2a01d0242600d1a00050082030490f480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568610179 1250 568608929 568608949
    0x606030d031118011407120f08190504080906070308010f0518011707030209010e07030501080f0706050d0608030f070c080307121b0210210203010302010f0807050d060e01091d0c 78
    0x14034004449152080840b00c03960010001a07c8042c0f500810001490304200b80f03641c40f0749030b4201104686002c86081650880582002c1042a20340000070304100d00350003200d0045000401441d2500c000d420b006213005002d0188482c0d8100c2c110003c81c540c07904940c0a11038135007038003240046a09001d031512400303182010f01c0c0c00700d10403203202000503036503216618040c0c05140d10020302c6282c02c0e20020300395181030340300c000c198101c1940d51a0203440441ea1506581283c200760b6951380d02103406000400ba01d50101d1400d000220b0881007009505006040c0742d4002d00b0150121500c1b210300503141d10600400804105007640d80180a90041100780101e08140926400c05000d580204c0c1c07800c44083d603132600080d098110030600c24000e5030020f80100048004605540c1594006030140c40f00160b02e20500c0280c100107001144030320100c0d8a50311545400f88085076603400e000300992800c1c092a201c0c1401c00c40c40900100b4204040c0103800b41120043c035032164108140980c03600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568611429 1250 568610179 568610227
    0x105070606030210111b010e19080706021f0c0806090903090d1202150105151e0d020403020109080102120103060c02070b0c15010b0408030403111309050606030d0311 73
    0x40c80d818000b0160756410f40c0c520300400d085c0c482040b580c40450701207081c80d2207405500010300391405100141e9900c680d411420706401d07140c0100d101c800940c079038103c25007903100e040d0f1441342030401300d00b4035400305102c4000603005000044544140c140803041e02e016108280025110a002403654030b0000d158039000b08640c02500d10703002108021507520810310350107880c00c00407400408541c560410120318000e81c001186002541040d0001d02d03610302603603680d400140082034046044030100007a54480440b045030700c0d520110340d504103000c0d4002e488280d01145001c040010805010b008842000b0b080413202c000d26807c543e0340302d0050100400280c11486011004207441156800800c44082c1c2c600081240c07503030203018802c226005821940e4403150a0001b0030925a0010680382541ea00c80c0c0c1c0d800d02a44c404000ca552040b0600c2c00c58007441c146078a10080c4280800d010f070141c4810303004d5490340e001014094090710200e00d030381e0030198010403401140040c1440719901c108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568612679 1250 568611429 568611431
    0x30c031b09030a0303050114030f060103111c140111092110290d02010530070c0312150e0c090909100c0305040201052b050901020c010f14010501050706 67
    0x210060021030b103014403d84089000c6681e4000501c03412a1202c01c64900c640203d00a2003500c1c4c2c03a01a564540006110060a4041c01c6500050035554405646000c8030440d4100f0594411410100010400d00c180101305510f0282d842c036241c0240811214895400380c1450f48880107240034100280300422280d1040c080c100c0340c443d18000900948103102c241c401001203100e03803220744820f03601803001040d2107610541ea08a0041c2d0704402580d82c0103212a00d0851616040c0c0d08d81f804408540f03000c401c42802c02000c010141d83c0104103034000b64040c3d07482240000e184254541100e008220182c84498000f6040103a050181c8010354030801424a007400c001c004000b20b480b000c410380300d030400e41e003000a2008050078a0301c14565002c0d502d140500c00d0303050980001c3c107244200e075246c001d049400300759200301c8000305013100051111071304108080e2504016090003508050b80303400142d402d15150103c80d520768058141e82d0440364801008076480d00005445540c0a00710486100f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568613929 1250 568612679 568612687
    0x5010f03060902030c0d0f050105030a08031306060308180307080618070f1202030f0a0314071a0a06080d0908070b090a0801060e010918050d051c0e0a031103030c031b 73
    0x182c0490001e1400b030013545030015186e4070ba903068042655a880f407403001741c52404c001000240d40014180380001d801004456690b15130f01ca1520704800d4180000c2d1605080c26000410096850028112032a112291000e00b544000030141c658101d031044104591111001c155000c030342a0030050410040422900340070390390056000c005102c2ea21030071800e00c58026090641c18280410305e404926180540103205a6640c003070041d05035040c402425172808161801045050024858042c00d280c2081086290550940002d030140d0301030071602e800360310448070045025903021001e490003140901165810401840b0941e08405442d0303500c001480d000003150b031020706c2144c003d40b80c040b1030215198109903140c810740e00b640d1208800c00844080407004100080342524501d801f07450400d582c1c6443e03440c0c0b072000040000c6c11b620014036040840003044130015210810301c0c801d48136a403403042c0e0720b80381585a010840f940d5140d45801c2000a20110f540d000c105000307140b900200b030030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568615179 1250 568613929 568613939
    0x10c0611040e01030c0518010b040b09011205041511160204020d140403080103030201060e0105030c1e041103100e07050a0c03090909050d09090605010504030f020406080f0706180f05010f0306 84
    0x100340b8081c0e20540e407840c000381c41440103040c125100c010305142c008059005514003400201c00748140d100d501500000807802c404168420080740b80d001c2c0791040240310908103810146241d10a05200030319a40c90640b1140d501700c40b541c150713002c5001e14030b059030100400b90280b0004c0d51110309000e103525900c0c4c180101d02038511200500540c040d030b0f194a025811442c0c081e0840700c26811056030f030f0407080010841d507034000400d070a8009c020303528041111f14500c001341c010107000e1281c0b9403144c244159484880349100c00b0b503224907101d400c942c01013075582c1c0180c051f0500580305c410005d03008000d50b500c40c0340580a81004184203141c98000d4507960002e0703200321010380c80704030385a402c03a074442440c466001c4200f00191450280401c829403410300040c16600c00c0380310090240c0c0465403a2400e40d5174981c0400d00030701101040d5000c20925119040d22111540140e00c041403000010070030011340304d20100251088581400ba203a81007500650301c5007004000c01041503256107021403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568616429 1250 568615179 568615199
    0x106090302040b0f03031c1a0d14011b0c02010806090c0f032505070308060102150a1104090c1806030b0f061c061403190506070f0c0b041b0e06010c061104 68
    0x40f008050020007034001f040341c02080c00e40b4140b8541c00c00c459403282c2449402d5440449026a20741d202c04818404040d18801501501900d180034241c0d01c460313404201842d421494031030703000d4400d90720a0182e035220300410283c41c4c810307108806008024001d0a0003850403c00542c0c0290b140c0c204001d60402030852203840c0b1580069100020741302089500c00c240d0004100343d00301009002800c042d40d80c1d24544400100f00034075031500c8644070800711800c3d2091078100e40141074145410b000440030840080d068000081c2c1214404506602c00a03000d4402c0c8030714491540000d005000d603001010070042d96030051200c11144c0259003051208150862103440e0091107030303900400050441c04100342c18107440c2c850140c1458040011900003075008100140d00c001d03182003c031517407101841c01715003890300e206005010000d00000e1105110b659011102004c01e0108400c2201d03880310200b04c0300700425651315011a45041c400340001d90190883e06542400100b00741c102a500e14800b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568617679 1250 568616429 568616437
    0x80a050d020313140f0d0f2d020f06090a0b04020f09090c1f0207030b04051f050a1808031b0c0a030509040b09010f120501022a0705090106090302040b0f0303 69
    0x200720f140705426041c2c2001600116010707100562005007200c01204420652902074840180e8100406041c0c132000c1c02e0700807801c16820740e150040303501a000a031500c5031441200390910401601c611041c6000b00d84001503058400c2e110b0001a26100443da41c481101d8031010f4012648504400a071442d251502d011141c410300c0244000e2403902c82020034040c25070030341c9240060241c600004005d21913000100001100d6010a58a650743e40745c0c1000307403c00080c400e4074031200c084100b801c0032074801500424002d41c0c003640100000d40302030f025036403088200c0400801ca1307101440059401d0780740c82040242500b00d043c180e0324204203842d00320f0518040020480c0425804219030b42a0300f0580304121401f03c09851440361541086c45001507080315200740702145003c68200d0040040a4054030003c42410300112407601a40340f031840011100c01c1c818000348a0024000383e03900d4410902c6040ba0b00035101c00034428107640910000d4010010301c0d58005503c81c2a0100a484c104010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568618929 1250 568617679 568617691
    0xd0504051005070503070c0f08040e0711010c05090a0311120f03070b3411060709060e011d04090309230109090507140c0109020916030c030216080a050d0203 69
    0xc0e090000c00001c00508581d0043c20140800c98103008211340c03660405204031404c0d400c0341d0350300c480415616201c56144038903000504c82d120501c050000da242c100d4044c02da0001d400c0000e2029050754001100c0e035000d1024200c0d4031104c00c01c030030400f081080900300001c42011b010350015807510518645002c01000c00030441c1e0744002102c800f80302c0c07480049a040120b00759070020740315030400d91201945000a20210401d08005000c1145000e420308400c2d208003501510584d00d050319000c0c000d904548500c0c00400c0c54064602c03000d610864490694410203d00395402c1d165820904c8020041d008044003840446140480d50904804d10040d10003203203140e85a044981c80c0006200e07014540c0a29500c40c00c1c0310a0054031604641e049070700a0b05d245015440e40b201c544101e014010050019400246140600606c4548104480501a810748003400030080c3c50500310100d22604640503807504c4010704040000d1618001403403048000d02d06581001180360000089038801e0f03400f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568620179 1250 568618929 568618933
    0x6060105071514091018020d0602030c130b07060513020a0e0709051806030d0207080d0503040201091e0302271b190519050408150c04090c0c140c0310110d050405 71
    0xb445944030b0f90f40c01145501c4034a5003001c0106901a40807488e04484000c004003043d0300400000c2501032a03d0645844089001c0d20800050355010304a0080c0e2001c001500e40c42d0a041c0016440c40ca0300c2c07002c4401c3c550280040c014546044c6543d000020040c0c01700c0700b00402000001001c0d5100001c1e40e0f041c044490810b049814194209480c4c81c3c4612034072020754006e07550400c00c140c008200648102c0e42c17410200c2d62503035070307200407500c0e90051340008480d1803503039922400401d0749c2810441503d00c00d441c94659807201c0368034100740c0c440310700c2050060049600040d03078000311485040c1300d2907100c502d1a0b04000f006004650380400400e1504002200440c0c0041c0070344282e0107401ea18000c0d4203100d8640342c10700c44019140c810702e401441e2902c101501061107450300000b140e0042c25003080400c1034000002c4010064966150241d4480e0100344070072018180c00320340d0340c040c0700c0003d0041081c000b1001481c80640b804c100c0510754020140030003078009a1900030584900e1007200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568621429 1250 568620179 568620193
    0x402091201051611100f0605040c020321062b0b090a030f05070b180f1c08010503010506010503070c0507050a120308090616110c06040f0807080606010507151409 71
    0xc00c4121500100001c041000e408204c00360080003007588112030f0720700130010440c14001d411a070050300480e070149811134900915006070710741c0032000d002e40c241480d401c50a24004440d1000000030103440103903000e4044003407403000d40f1b40060542201c282d030007142001814642c031600301c2540c048035044a507400c4400148105648412146c4455126041540c200303010368840851404004040742c6003000700502100c580b000400c200c1e034804c0e6500f03080300c111611800c01c0012030842d248030301c0c0c042107503039002082c0c1d4903041c01154411501a9580c9084da5500642220714001040c07081d6800d0003139400110761502c501c01c004011300b4410a00c08088882c41c500141502c50081071000f00d034012405011600b0201d403850074600700b180c5400402c03c0c00c408001e0f42820043c044103175010030300050018a030441001e03040c007200c0744c100a03911980d55441c28181c07525000c81d00381740020410006240018440d0100c80b5001c00c500758000345048600000c880344603002c0d05e850340c0d10b82c0a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568622679 1250 568621429 568621441
    0x160f0f021c1704050a0312110301032010091401050c0307060b0d06090b0105180f0103080306031e1b060c0a02090408040902031302041b0219031106150301050f040807020f040209120105 81
    0x1f500c0c003d8002c1c011001000701c14080c4100725018001070100030f040c0ca05400c0540d000340c1c01d0725440130034020001d0240c520146c445038003800410f1548940b05040c0c0500c01e85d5000c0d5030251040d91486156a805545041c9842c1c1e541d100904a5181031580842100707450000f050003031240c03171182485284c2c000580d5040c141048508140d508000e0b02d4030341c0d24010003091040c6007202d030b81180c1e400b00f203640e16074030cc050000c3d051000c89414a00d004c01804a045a400000940c03050b032486148215080310900400740328271071043d01403498841d800240d4900c0142418400e0541c40b601860203a0705064481c3d880708140ea00650781500818100c1d22a041503140a10400303034513a03803489407494000c0c000c0d00d0280d01d80110f0480107202201d01614079041c1800f8074a11140e00c104081918018503129154180303024554284900943c030301000240e0b10300e03241c100e01d801540c100c9501402c0000382d50030001135450803280550425000d000c04c4681e51661031520703030b55105030310001c03034146019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568623929 1250 568622679 568622687
    0xb0601030b0a050d020d020301020919030209090f1905011b02060703060f06090b0d0e120c1011040902091210091103071229160f0f021c1704050a03 65
    0x41040c8552090b1108000c581c2c0c441c4622404564180d0306600554424000a8020701880c0309160704103480e621441d00400503c06a02c064a200f100c80c1110342e00c420030b00c0742c3e84083c4059201034690022140448450301c00494840551080c40007149858090180d085c0401241019034096440007007444499901400381d54060400f0b8035050328540c1c60f10744018000300e4070b032061361300d11500007840d00d01c01c0d640ba80010101c07000420803580e2100c0380100b44140c650000c50440300354010043d02006c5d950050040c154080e03141c05c01a8106820620306400070340c031001c1c005511541da6034150a003201c00340032951840706e8181000130803800508100f01c018042c000c41c680700341c100407010b10078010105070305050160801c4d05098500750382c401d00c00455045080302100c80041c01e0030045041040080800e007884641d446d481e071002d001c501591801500c1c012000560000f5640c001d054800320304d20049010580f4040f4482e4a0600305590b1441c420f50b030586e1160018103802040c1500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568625179 1250 568623929 568623941
    0x2e0509090a0b031c0e03071202010f0203070b010b222c0c04030321110703091212140d020301080c030715050d05130203030a030c1d01020703081e070b060103 69
    0x40e001c000d121100d5031100080d114102c0c1c1060142c0d224030048000083d40c0304058900540c0e8001d07080791000c80d2182d043c02c03807113444200304900084c04a4084001c851020041e0303605240d001100f44070590800d440705c11260484900383c8182c240b50249201a01c3d080080d25000b8255103560407001701c00031038603a92151a0f02d2044034091804020700410a4004089404894041c903040ca42d035000c0e80c104403038140c120710801c090903040103180e81d42c00c040b40c40180380642c82a1a0741c161160707503002000300c0e00041500604801c1c448995806e12130b010b4104280034101c66070702e40341b40151065203201260000c2c0c0200c0d04540c0088442a4181801c000d02e6019001000400c0030410300080003e10b14803481500800040d12000401c61301048888001d5101c2d81c002c7c19251030342c05082008005002c600781703003000555066040444a28a05001101c60206a0141c54402e040d61038000b000d0703001e521921a42c800880290255502d1180079207481485013250b1102c0b800c01c500014203a643d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568626429 1250 568625179 568625191
    0xc18030b15091806061e090a140103110a1401080f092d060f19020f0d0207080c060c03090a112b052e0923010605030f0607020c2e050909 60
    0x4200d04000c6201d810051203101b070404211003041c00c95450420b200c1c09011240344a8030741420420000c0108000e0446007050210250740241b0b03055a2803250341c086400b6481c4e914042001000030400b54826010302c958460442d00440d01c1c10f590180c50340c3c0d203011403170803100d500d441000881c0900c4c00040c0481a0001c80d2a00e01050b1403c01c10101144c01404010804c01d40d9400126003101da09240180c0b0301d440120f030011521075003a818090f690f944040c0528405002c0c26000410101149068a028804820013003113100c0302a030b00c0baa0660812815503038450800b0028507251042c0038248105010400700c4108510b049240007850810f01c140380c82200e0203650341841c070801d280680000440451400823509208504103058000b15070080c014000c0090428581100015007010084483c00e50403210350a04041c01b82c0d4495805503014001a0400d6001d08224030708400241052040c032800390840480400380c0c85070380301c40e1504400c0072a5001c0386000c0307280340c400a0290310603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568627679 1250 568626429 568626439
    0xa08010f180209130c0b0a0c03031409120c12040303022404050c06030a0b12010608160b0304110135130f060513050a0b0a0c18030b1509180606 63
    0x1c40c0d030b0014040714002020b1a20b03d100714000101403107003d5000d04001c00b040203045a441d00414801003101c841c0c041c003034021908044a580d1401d0500d955144075842c081c016062000380180c181c2050790190013080d002d13108a0350b4026643c000c50004000552198005221004180000e0401c0010071415070b00f004d5102e00030003004c100b000c1a00c40c1907500403140a6542e584940441002740054071600707400007107000c42640d5240f0154000b00603118480c007111440c01502d4024411101c482c00b070700b9080300044c400305000401d4252a501c42d25070504044070800141007101e010079001d2400000e130090111004400c4003514108140c11803101c040c50a8840403680f200000c2d4051810000c0c0f01969540008008001095981e0f8100e548030041e9407603804142030001680c5400d40d00c070000c0900c0c08410344a40c0740950b450668018100303910320700191441c2c030707002c40e0a2030007031520f10f0b4035106003410b4803aa602c00540b1845298580c0041800500172a11540380c4180184030300e00070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568628929 1250 568627679 568627721
    0x1513051002160b10090e1b060f0c01180203100b01120905012301050f01050307020309010e04150b0c0105070905180912070803070e0102030f04050405090a0203060106050c01051b0f180a08010f 84
    0x4880303104a40c3c2011f800aa6100380e1360042c00a441c40b282c400e4840e00900307940f804620b404a022051842c07015a2b00840c1120140f4451501c410110344c3c0fa0031107507010542c0d6200d00511b14040f40c02168523140030790000181c549c0948071400c110b295003d40c0b0120f00c9040300061026180107850005100e00a20740242075140c544000381d60b9210b83d501031810b0042c054528840c130358564001490001d0324800e050006551894084140d40100c0d501201c01c3d4286070020704524410005c0c0011200000c15610100c10041d0400041b010041c00080440c0640c2c2c0c008a4070b40c200b6802002c1c998031034a40d4a50740c0c940020010300040801c01e001d4115003003007080080c005425002d13501907070401c58001901d07890b40c0041501e05000d0100080d018001c1d000009a00c903000b04c003405801d240381000340105c0e40c0d84020810740c9541500c6003400031400703000580080241001400308000c03000301d0501145100d20010365400c159501c0341882c1ea4480d0442e070042c1080d40940303500c05141303654132582 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568630179 1250 568628929 568628953
    0x31b06180519030e060d0b0a080c040b030f0733050403030f03090c44070b03010305060a0b030120130b0f12060d141513051002160b10090e 61
    0x102c402c840f4203a00c52400401c08403184106c1c2d91240c07112820007051955429590340c0c0c060b0722080300303541651086140450700c0c00c042c1000711380741c0f0281c030842d0003070100305003060110702e6044418604a070031704000726481e042080020010350210b12a03620b031240c41301c2c9145802402240030086044c109402c084203100003501d0103900c0f03c01d80310170b0b4900c00700c140c02140740e00400500c1c03016856004040700c461448010a0071041520740480310b0700382c170480354480c010140c11b84020710000b440c40d0301c4803002480a41041d804107031000383c002c0c00414010103143c2944051151480c2e94101c600e00001c00750207405100c103000b00100304110509040021124480105000d2400d0b28540c081980740050b1040ea2116081c003d81580500b0303050780c4180d00301101c0d0b500c035201d004269100c0320040214890b181d84e500da078140254130900030030142c4114460b14010b03410882249400c1e04c070250440c40050b880700906446859860380c0900c0c0b40d49400107400589040006001142e0051074100301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568631429 1250 568630179 568630187
    0x60e0c0a062c01050909010e090d0c110405060d020303071a1803070f020301060f03050a1e020904020120010c0e0406051503010e060a051518060a0903031b0618051903 73
    0x811102d0260981d00c41042940140c98500c40d955290750301c1042140003240c04000070701e649016a02d010f0890350120010b00042d2040109401c026040112014150103a86006d8005036231012001c0d10034085170b40c055011915580240fa07044500846210000c00c23100e410082035580701c249c41c003841800150b010515034580c03080b8100070b448007440c1c203800410f48d02d003500301c90300030b001c1c003107a410713000e0364a040040c1c84d03010440080301c2e070940c1c040b2071040da01d0b150550709101d107400034011a0350341c4450303005540308240222508219841c01ca01004011028031500c18410b0391030322030401030b01c803510070041200d045401407441303940890b41d400c403507501440640b41034441c5c071122034502e03441d4040050030413150f56111070383c400b02618a2024040402e400b83c10041800d02c00b1200c0043d003481003000502030b03040c1172400515070100410119104400c075031801d5410b064600c08144658072520181c0b2a002080135002040c4440170042040c1042400503920074651030000c4000c1c0340d03800030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568632679 1250 568631429 568631477
    0x20c0f0a03020d0618030221212e0314070b0703080a0b041e0b0d12030f1517070b28031409060604180b0609090a060e0c0a06 55
    0x41e000f400c2c0001c0b03040402c01d80d80c0c020704c03113280c8080c001004d08031945030080da92410f910b8a1034420140000a02c2d00342c20480c103903405150784403500304880d0307070043e201c0c403040f00c3c000d082c04014840b91413019448007180e031884400b40a450300c9078240034150b00f01900903800d0103842c480c3c02c0d400624100001e10400d404d0f90102a414a0f08842d55200d036403007800138028858510340d05c1450042d400511030012110228012075982080c050104204208441207221a001500c460592040303001018072035400320b042c0304011800003540200c03161034044e030f14440c0e0300041800c00801104d1203c0182c00c01083c0020011121203d140481c580701d10401084407003140020340c03061918a504441c000d804c9444802c034400c405c44c0080c60005040c65842e0002d86103503000e00e140c1043c2c01e0314807150360440c82032150808002415030712003009111a6100050501c603980c0100c610351000070f4010b00800c0e42c081c80d40001004505090b5041019044e11070b44580f041c00062281c507540c1601c2d0040310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568633929 1250 568632679 568632683
    0x6120a05061618060914030606030a080f040b12010602012702150c030c070609060e0d0b0408041a0309100902010e0f1909020d0c0201140f060406030b07080403020c0f0a03 75
    0x40000c010500d0700c1615215a40391043c442d0301a00140400c000d45e00100c0442100c4204500d00c41c103101283c00e140c3c441c2400d0f0340154154201c000c0c0344000c100150001d02d10107070050b18040c5056940c956841c0d4503040951003060f03083c030407030041114540c24010040c0c04001c000a410104060301c1400090b0fa10141000303000c1e60301c41c0704c8100440b60820585000d0381d038000980351703030360400d000180d1a06494041c6c2c078081902240041170161094a840aa411000e0080c4020040302d4562251800b0004c00c1120390513400c1001040381c0a00003901d03290401a0415943c40342401005d1b113041c4052400c518000740d261028445c050307079101100f842000c1055801900e902d00c5603011500303040c46550741c1c0422034184400082d190001f41d00428440032802010001540c0740f43c012070030385502c40d80c43e50030032503118081100c1c00201e200d000c0d0090350040c0006880c07030b03490341d0724151494115a48408903200800b004285034040c02401c40382e00003142c2d4421601b02900000341c4d00e41142c040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568635179 1250 568633929 568633951
    0x31305060f1803070909060f0e0c0d08090604150906080718060305060d080a0c020f04060602030f030924011d010602100b010320040611030a1d03010b040906020306120a0506 76
    0x242d4486071000d0240f140031707000c40c0d04d09002c08021410694090b1512048140e4032030302e0414100200900440c0c80d0300380e041d0040495901e102c0302d4071a520260000100d035076000108020006460804090a40c0380c4042900d4100c2d0003032610b0b20161a004e001001d040c140017225000313440520a0300303e518240e4144d4200040c550b00c540e0042a2450500980107052000009001d140302d60045202e01c0f503203100b00c507007402042c030141c240800d0343e0b118451500036130b0080c06407803200d44c0c0c004081c40e880b2000e8000c2310101082001d11038070900305100384c44041001607005024406105488919008840a4841c5d4952500c4002942c03500d0b031004400c6840d80c2c820241046030710903005808034040d030038100d41c8a50596140c500b0194454421036000c1843c1482075403082c03e01206880340c0c1109a00e0380d5140121107400d08000710400c0b20300c0340d815540c1d100002c00c25074403440b4841d0001d0054600507120f282c81000d010003c2d102c42c3c412402c0b44c3c0a11900c800040c1c1c00581d441e400503d001c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568636429 1250 568635179 568635217
    0x90307030f240e0c040921050c10060906060f020d1404120803062b020904060207141b0102070b070206070204020f03011509090e15070909020c031305060f 68
    0x510030514030440b0002d034402d140302014402003104642101c004807003218203803410f00301e00c0350401c01103400080b0020101e0f405500c0000c10520360061900803007229041c0b0524000e50310241c01d043c00d0071380c5a10790702c10f9a81ca0090100c81154030640c40500034604203198000144d0380080d40d103c0403144220100030a0040c10b002401943d0700383e5000b000c284015044000305850700c1000758100312401801107075803080100740c03c026040303083c515480c1c28030045040c08094080c040301900040042d66242d40820508000803408000b5020581c80400030b000c6d11f41c400d500d00e03100741107224030702411513102c020184001c400c001c00b21540c543d4115883c0395101c56910114006e405a0180120b01e044040000200030303a44442a540d9179015030740322101a601c903403800b41240d0615035680d10a6000700d8010304c10110980d02e00342c0000701c500700f05107200d0b6150528802d9070301101108010b5080032901010340500750a104002c0c1030111606402c01c500242704441c40e0080954607051951068 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568637679 1250 568636429 568636433
    0xa050d170c030c010504020315010b0711030c1f0e04020307050d090f080403081c1503030f0c0b011d01080708030a0c0c03060504030528081303020f0a0b1b090307030f 73
    0x2400c0760201006030003030702e4403900e155881c0c82c0203050440b410303402070040d4038000304d041801c107460505070381d5904880d03030400c403d41c0c03965080484558512605441f4054449d4402c0e50348603500d01030b4095401004280c0b60654400030002254150160300641c0148180309a01d5000015503940504401d00014444254201440d0800100e40c000d02034000016011090100380002404201d8081031003144075030000c000c0c00b04403281c070200004c003402c1624051000074800c4030004540702c09454400401c15041c1c0715540341000aa00000c1d505d6207030003421422008000c1c80d54011302d10720f03000e400907520740398060303480b441042c071080100f2141ca42e86004005e07580003104099500440100480e2401d40740c050001d520050054040180b0100048410315991b04a00e01c404a2541c030588240c03501442140c060801380340440541c0210000c2c1d0240450406c15550041e02400c1e880045051030007402c9a4080206c19502241d40100807604841c0c42c0064410222a84001182c88400ba64 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568638929 1250 568637679 568637723
    0x3021908190207060f02070e16030b04110910180b0a170907030215271305040f03030501060f0e150903100608010e0a030c060b1206071d0a050d 63
    0x25403030071a00350002803144068640d00007000c200343c03015900c55030070780b444406069940b90094455082c02c17048440c0080d1548a110410310308201981c03c020401907031050009080e600d035405c0c0605280030101d0f1385501031521b0a03484003400082d040055461200003412031402c0780c94083c0200c80b25000400c0c59000d4440c41c108040c14440d40311071407580c14104041a00c40d6010b200580c8529a00c3e2000614910800201d0701401001c944a03400c080100002200c501007910780e055102d10f20307100c2e00100c01c015005075880707640f1944502e040c2d40a00d02d0050704890041e0031080030130028410207000590841001d07840c9103402c0b00e0504054078160709501581c403071052072070703014095882e02c0029140030790070030002e4030b4406000f400b0f560764440020369544c0c644034028000504030b000c1b00300841e20030351203641d80c1c101c00b5004c100c410604c14403340c40c11000343d45500c002801c414444405040508040d00411003c0b80d950030740a1400d0300103800c1c07880340030000d44542e1810640f28004208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568640179 1250 568638929 568638937
    0xe09150324011a030c1215030d030f0e0a0b0c161a090706021c1d090f150405160807030905060c0d05060301020703140c1f06090b01030903021908 64
    0x81c020001d02031421010603250340203400e2055105103c1c004070304190400480080d03901c10705200181c0c03800d149942c52421031017800034000003041031454111804c651420301001c1480c0b0143c0e100829043d040c003084004882c5500c6105100350011900311000410840d00c0c10382115010314841e07210007950b10240d4910a03401c40c0108202c0709106a442120034805070301d403007104010f00343d42c042a500e00040c3d0301ca621540b42804960300486012030360502580c001c0606e0440c01c0d803100e0341c5215100108542810a40341009012110b4040280c085d5040790301d540720036000d0b2010302440c200401030340104202c815904007481690000905000d110b68400441e664000c000c0b02c585060804100020390301c040400c801d05400d0000062003800e0500840715030f541d25507500c14220b50094a1303a03140e034014240a40c500e0007054130301c0742d402140400c404444000e820000401a1820034110704488a101c00c103414182003181c01d10102c3c7d00800c160210080c3d802c0c10410407101460003202c3c500c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 568641429 1250 568640179 568640203
    0x7030302070b280f030b1807140d060e042f0d050a060609050603240a150905070e100201200f0c030d0606090501090b180a05060711100e091503 63
    0x181d01c10890322069101010045682d04c640703081204800714000d000380440859144400e1801e81c8001c2904103100d50001d026960b1111096401c100610800a00341c40703569200b164402c1d1000b0a20007400810841150151000882d42d81d02c0101003001d54030090b0341200e50ba1158045029035000d0001c01d01c013145040340d002804000d1607454030304400044c1001c0d504035003e403003200d10051110940001c2e0207a485040710700c48446070b803004901c4003d403026400325014682c01d00d0000420080341d000b010b0240711036484442c0c0e1701c5140000e1005256000810b1011a810010b2a100901c2c0300c403030030584a90001c4c401d599903190011a000e241c8102c0d41e0416030b41c40000b48244114a00da40084291025a6500340c01540d449004417a040024002c1d840d4010f4100404003a1640302413440000c514094019007110390307104001605600321913415100c110155641000d03918000007815003100843c01c0030420745031940042501d0140c01800d204401d1080e54101c036541d501000950540c803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 568642679 1250 568641429 568641487
    0x40609060e01170a0507180605030a1d0a03050316030b060304020d0203121305041407020312070c020d1209051c0305131e080712120305040311060106021e07030302070b 74
    0x1c1080e0814500170001114000e0000d103200801403004904440080e0483d0260340d2018290740380d0885120052a0f003155007041d08403940700403101c10800f07104071150b83d4002e494107034403490641242c01c0042c0300300c039a040c105032420700810382594030501680d4026406841d01e911090451010910348011240905900480400c2c040c10f0300c20028440c0007511000c0c1e40078000040e0180390590050410307944030740940c200b4000c1a15500055a405901c6002490880d042060a4010910000403401e0540e150564511031800b02608a50180020501501e0302610003149541071100741070000801000c1100015100000790801c42012015011464520104403e006c01884017071409206181c514082c84600240d07040c28403031041c4141d50803e8842c0100071182c2070440007041d000384110300344041c4d0b02d0061041d21b820402c15001e041d45030020818600c04008050041d070b0746030600a5550b200d12024000a5400300c1c0709400c40d600c0c02d00e1692160103c1c10a6001c1c4580220328001203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 568643929 1250 568642679 568642681
    0xb0703020718060f1202060f0705121c0c14030c0c1002030c0909100e0408031e0a022203051e070305150618090d05090d050f070608010506040609060e0117 68
    0x1506081d8403040848110b041d074400c015035605e4544180680007031001c1d40c00030f02808000c003001d82100041c0b00403881031050f01d503850142c01440e4600e401040041c03941400c0717140d40e151a10300501c6000b10564403030070700c00715010041c001407000d88402800c40c0081c240120b214102030b00b08102801015441b00310540d2280f030000b12586080d0060400c2920955a00e004114070114441d00002a16004143c2c1d903040d682c1c0c3e8441d11016880a0010015081c075481101c82890b00b8405d1140a40081e070ba000da0356a9524402d10701c2c040303d0341e04040d04003444540800000c0c13800140c1500003c445008049840b615004144c101101a030000e803541c065216520111588042070600c2050101c440c21051440c486840751003a13422920f0009517406080d140368928003ca025102c00000141075482a141d03507a9141e00b80380c0c6c151064081988804028880c858000041c03601408040e582207041c6880d000000b0403003a050311030a0107000c02d041906206921840519241c1d41a01510300381e9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 568645179 1250 568643929 568643969
    0x1080f0a02040b040209180417180f060d15031104020405010e0d0201030603020a0b0c060c07030c0201080603160801091203020306090f0c1306050a030608010b0604061b06060e071205010e010b07030207 88
    0x11100445048418903242c1c00c010100b94048000e459000600351072b44420500e242c4140b018855040041d5940004d0510400d07025000714060510081d800801d50810a499460b1500502404419080c400e130b005100034803450740e02c0303022184030040894058880380782a0005170000c112a410294120040712408694115200001d00d0034000010495000e640c500002410740c1c0980040140041d06100c1c00700e000d9886201e0260b00802d0040a880c80d110314001d06010502d940e43c032101c03160351038903820700c24000d2001541046100908065146250410015060075030041490404d8010701d0089020460100c0640d512a0704590361402c0c107640303500b0040c0c4a5003208007003800107030034940c000c45c0c0c0017010b0007038040d80380002d40f00c2801c0504107802500c2800d44083c0c0c9041440c0c41c150700d50041422030103000020840c03565418420304112100505101c0d00310303408120749080c100100094000c1c1801c240c1141e15010030305440384001d04d000c070308002c0301d0360040360380d07070351040c0001c00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 568646429 1250 568645179 568645219
    0xb04090b091b0a060801092318060f0408030f0408041802030a052503020c03090d06020901020d03020c15040f0c030308070207091103070f05040803120f01080f0a02040b040209 77
    0xe1074040c0b241c0c00c009031981c803000c200107150580a0000005e000600400605509420102c0c400341c540018070344440c1540c80744000c00070308030707a49548121860b43c80700c0140c0060007850742201501300030560601e0f00c1d49982910748005000c4603c1080707280001030500c0a880c041c0c8000d4a020910543c40c0101000341030003075003081d110303288103500e400c0200704030440840190030030328060590340c900e0301c402002c164000e400c05008400180000c000340c20803070342d42c1001e07221721070301c139200060300c1e0729800300020707e480f140c4c16054080c03500c10404003038010000100c0c2c00380f400100d41014100e58079480c0c011451000104001c1640303c0c00c801c00720415800584e028480c0f1010340c200c624940e40d44030004250341c220003508030501400c1012070640c0307101d5160b0110114242c00c20f1840c03d81e031202524556804404415103c00c0d04005100d8040680f5000f079005144030030042c08443ca00070000c548071812440020b11580c0d9030103040a403a240d1340c068403d6803000500c4540d80c14060502c1e54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 568647679 1250 568646429 568646443
    0x12030d02030c092e030203091203040b1e100e0606040302040f1b030216020f0a0e0405390409140102040e0a0c020601030512030a020708040b09011205010b0d0b04090b09 74
    0x50702c036602109180b004d580d0100b044402c82d080b00c2c042d0314070701e0500510076002940017070300215040c0a144804c1668040d6040150b025074410706c144e0031070389402820140d1070309581040c1c0d203850280d40c09025205070011848000d0b210405034030521621204000307440d42c403641d88029040760809090491038000303903000d520b07d800158044490358010600440480c41001308007803218040380041000b41c24232500c42c20041d4000303000d40d0100c9440e041c4031650190304540895007540030540c009801c1c20180c4c0c0c45002c0d6021400c00043c80d00b803d04141410030380c480c9641d8099540e844292090011082c00c4030100344414000f1540c8623194507041910740c60480d600041c09080c09c0f54080c149100203070048c1201c0c0c02c500130b40010300c00e408542c1000d40c005040740d10015001e102d4200030070042c400401c01465500d41441e90f5160000c0051704e0321140c40d0b440b1503500e00c0d1000405c0000e0a00341101c8440d8107540e00000c041d180712000030024045a040070307000d00300d0f500800402401c009006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 568648929 1250 568647679 568647697
    0x52209020d05011a22091118032109031c050918041e0f081801020607021c1b0f0503041a040f0b310f0b0903070512030d02030c 56
    0x80c4010384c0c03200001501052064040340300800200040b02c44c09200070201ca4803282e04032210540300742d0782e0380c2ca0410380c0c9041001c1001800c0008510840ca080c440c21006104010b802602092500024031604150801d1103040b007402e001072003100943e404e001080d4611240c00c081c00d40400310383c80060898007c110b080303000d010348694070010560310f0288580302d164004020010782c050401590a2200000c0e8115402841c552245000844100107001d014280c480d0550700300000384002842c005004d401e45041d034020b40841089a40000714160b5011040d003009000140d40b0070080d944800d40c40360113082c100d0700c0d10020301089000f1000f042101c0c441d074094041d58290441400c114483d42c0310350064510000c404200e0005480060252901002c1e0f5003208034840c140c050208103002c218000010541040621094840e11420780103404d000881504103135000010036507801c4030b40600742c03241100131003581250364108100c42402203248025500c03810481c190005c9901700c0301907 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 568650179 1250 568648929 568648931
    0x52409010f201c020d051b0309060610050d020409021b030a0c03080601090b0a0c03021006050d0f02040e0313030203071508041704050d0302101407050406052209020d 73
    0x41ca07580101c990007101801000021400408507030003116030040d5000c01003803c1500d41e0710f0100f0115010a1019084d400b140c414049940e107072801c0e00191104803019980c84141c0103205200c080d40002039030303590048040e21441a401032220090750742d40100d440c60804c2500000303001c602034106402074a605030600f00a07058941b820780045440b4000c3e80c001c0c4000486269101c0c011274461a07043c0e800403018180f80c05240e88401e00212903521803054000400e900b416103000301a0704108000343c6d551020400c1000a0502000429818192001800095807070344548150f507103aa1240f038000f02c0b2401204d65a000c0394041c50b1900e0b6107440103910078020010300041c020100c4d142c0304a04441c81c0e44c1c5a2a5666507503034100082d0680c3c0002c4801041440042601e03207030004180b010500039001402c114550844003004d4850315110454011582c0e018008126000003d48047e01c0041c07c220342c071202c075440810070120b40e850b100842a02c0c21840001c4401c1d4660051100c0240800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 568651429 1250 568650179 568650191
    0x2060d180c05240906040306111314030a1115041d0703020a080f0405010e070902040e13080a08130605040f050f060609010b0a030b04020310081608030a03020705240901 74
    0x104100410501c200f070a080100c50300100e144002000100030848005041c1420552a038907803108541c80e40515070380c0c1e0b510000740e140ba4040c40002c0340b4003d202c6030071496000c890100c08641c9902200c0340081072000040e4040701c4641d80d00314020b0050341854021a12540d40f022a030b294a16990390024107261081d01140b1010b03c68002c99943d203076030b82c4420310316440d00c200c0c44080c40c0c1d0080090b5400d541e0f840074010800000d002030b0000b8810024056216410400011081c1c50090a00302c480c58a60000900044010041d240380200c1070411401c6c2c1d40c0c5550384d07900b1841d000078001f40308070300e01000c00c0100006002c1e040d0010740200216220410f070312400560703a6400b0341d406688000120f004125030407540340146a103e45070320f0042001c04100c1d000c10706980003a180c18041d1f1b003008100b8401c03448100280c04482e241403420290982ca4480c2041c1c50b88200a803200801d500041c24030144001080400040b0040101b4182d01d44420b80021a02001c00c0c1e40300d03101942008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 568652679 1250 568651429 568651439
    0x15010f0e0a0302010e0f0307060302130902040f0e040c120f14030c060105130e03030f0114030d0f030f0e0a05060f090714040c0207080d05091801031e02060d180c 71
    0x1a103a40031180107004008040d0541c0c0040d82e80d407400304400d5610603a1303401c01c20010344040c41290002d00b007986015846940322000096030740101e4110304003891061104000d003111101c00d1a049070101b04600c00c2c01d0f2941d04107800e10303880f10341121b0441c1d032401c0310540c108140c041c01c030a03e042c09a002001e2507922940c07510f8a0703210b1007007031108a030f019000500c0f03645042010b000360042d409000080c802003050b51a0f0440c0c0040b207105000404040040200c03104454420b00c10380001c80c0917100d421600074006c0c0907246400e00070800c140d0307255942d08120304994403c06010300f1580445120301464a001c9640d0a070440744460400c0406c3c02090180c4000161641942c04d540c459009803a208414413006101c0302004070110f2003070400c0010807010a00c4004070b02d0301d80755505641d4204440070301c5114039100c00c4100c0c0c1c041001d8010404508101c2c4112403081d030004c7c07525030050300390000500074021000e032400701341d14004541b078110081007198503585100301e4001d42110307524 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 568653929 1250 568652679 568652687
    0xa020c04060e060918340605071a0606090a0905070306080606031b0303040509010e0403030c0e06070609030306090c050d0e0708060610090e010b1b071809061415010f 73
    0x141c3e501c9802c1a0307804042469000c0301c070701c1c035010b00c4c901004448207003182c01481d40f413600e0001030610552a44004032842c1c1045482540301600181c10901e26006069482400341342d5003910700024940e424002c54550381c5d8480498000d9003005004401d06138036040403500803c0305a0f08913000c2071600500141c404404076010b441404001d015050b440d00b038140315184281031107140b60381070204000c0424195100c104c03e901800c8000044045441c1524019007203079024044c600c00c0c04045824001d840c0e44050032181001c1e401040410000c1a0345004d41c054805500401c0c8403a04143c071080040d030b4040044d02c51290301c10401d220401d28411030686445080c0110401c0f9084a000122a03061001d044014800c1c48e19200256030391346e0b01c3c0c4d409880b800303822061318a10001440f452158003400c20108004140002e020391514010104c1d600090000521910503224411030080c02010fa2020f0180c0c00368507006001072800b08442c6c0c294159441e20305010070070b80240b524115110b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 568655179 1250 568653929 568653931
    0xf050a0f0615030b060702060d0b1c050d1b0c2c090604020108040c0320040b011d0910080313150903030507020f1c030c0c081609200a020c04060e 64
    0xe0310111401c400c203126801c0f00a00300c1d00f0035980d0821010000c4a00580716100103080f2880301d40b20000707101102900b00180306007481118051312078031203000e90100710040740c1001139040d2802e1070150945005501c0314400106400a0012001044c0c0040c1d45480d03c41440340c0c0001e401302081d103001c1000c000304c241f2241500c0c0d0400716400000040c0043d402400c01c19007240c015400c007070781c00b940c903a0303620032810700c1407900425040c06800300e80840c00c01c0d02074400c0c4c4107404d0034500c1c50b1401d42c4254568101045540758411880b0740042b0b40200002071901c40a4010700040c0d95841c0840355103200141030900c80c14031602d140c80c0d58038007094814038814046e80d074160348107860b0804035001c000c003404220300720651003500000300f07106900f221070b120303510391740b0a0b05c0e440020381d91400e104c00601111780c40464650000c01e40c00710030018018044e02542c41041d00020402d025a600c0403409100355200d40840d440090032441c49030b0009007066406604680510406449113a18108450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 568656429 1250 568655179 568655189
    0x1150206010902072f010806090702060a05041e080912070f060c050c06070f0506071b0f05010b0a181b0507060f0917070b010b0a05041a09040f050a0f06 67
    0x82006100e101415002090441e020300201781c0c0480303600711101d1149441034000e204200042038400e119581120a255000d103080f9220b1410b46003150001e0b4540c1401002e1120082e601c03800103003040880c04040030385600d403101003822038801d80341807007040d4050402540320351604000301c0302c00b160006403101030343c0100042c0703d15030345842002e0390b40c0303007580310112694060708459414948072000649405400323035008000304502820450300b000f2000c1c0510040100020034040b22400c00c02440d0362595101e400b00c0340a110344e04000f80101690354180f80d120802e00c02c0012807200043d8140340701d20b203061040200450b04503042210851154080340441c0080c05404041601540303c0050200d00c6039002c10a13040d95035556640184101c08030f181403a01044d10000d00c40400d440c1405800c8040c1281e1074040e1a64000d8071900581c810080500d441c03000d440141e460020644980c80405401800703041c0c1d091038902c001d0141141c000030321900d01040110240520700504007114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 568657679 1250 568656429 568656433
    0xf180603090715050408030d020a1b0203121309060303020309100201090f12230406270311120f011a01020a02010f0f210c02150f0f150d050705010206011502 69
    0x1070316003e41c02d02035850301d410090911106000c00a00703618140010701c0300301005200185e0f100d00000c1d000e0300c089030348640c0340c90302d6420341068001a24002008054410360306100c030348682d054001c580c0c0c814120b0300714081460a01c80000101500080502800b03502160000041216030100324222821580098221000030a0f50350101d440340d0341c0d00d01e0704052803411008013801c08050602c0c0d02140810f102ea03082000408002d580d0307228002d04201b1001d01c00d10040c2c1c0c00e0036640001d05001e540805454203180315500d003640d035106c2840c10f40314a105c2080c1c500740c80c40c3c030708500d00912601b00126654194003030607000a610105031103481c0e590503142c0120341c01c052441100c181c61040b482c1c80030b00036120400d06c0068808590814006003880010030344c10b0380801c0003030810b000110300b00d000c1d01c2e400042c80310714003000d920a035000c482c03030420b00c0069403440b0a45140103002d40404d9007000b6521001e4040c4480421100240d410a80032100c03603907a105c1d80944814003030f1003100016 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 568658929 1250 568657679 568657693
    0x30605061207060e0604030b040302070806090706020601030602090f0a060e15040e07081b0d02030121080a080c0d02120405011103071209080c150108070801060e011202150f18060309 80
    0xa40500854000144c001c2c107a03608054a90340d445448040c2991300380e0240e80418801c004540003002560740c0a0101006030841601d48600603689080602009000b50780102c0c41c0382c0507854111004455440c002c00301419150b9030b040180150050420141c0241410050000300c120304504540c1101c0c580001c0803071941da8480d0032140d90001030120340038209035008201c0900329990140801100d1840700503a65450088901e0b14468940781941e0900c41c2c032040c8a000c20303407102c203464540e00709081c88402c0d0782d1014409101d6120300710701c03040f401e0310100f640004498201c08031803040703110708003c228070000307840d1985040c08100c8803c2e000440340c440f150040d8501e40c0100c1101c5128540e100d0802c0400280e040c01c0145419581e5007005000c40100060581048010018070080000b00001403c000004003040b1050280700034400748501e484086403606240c428460314601c001640319081900441c4941e80f1071005072004031280e9404d6607171480c05108803405800c0e000024045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 568660179 1250 568658929 568658939
    0x30708071509060e0c0406090b010801030312062102011d061b030d1b1e050a081906030303051501050c061b12100302090a02130506030619080106030605061207 70
    0xc01c41000124801c40c94840d184030b0009419070154039081c842c200080c04143d00382106200072145558006050035050008185a5903044100d00e415603400d481c00a1040746030300341e00006010503510503103000d0b0307104220860310380382c1004240b9628400da85100d194482c810800c03c40c60342d8043c0070b5a00c0b050801070000211000888942103651240903a8100620707605810100e814109280150a90580d10071000d030b640b02e6242c80f0101401106000c5088405000400d0360003120050001e00030800042140b04158549a00ea00c846c000424010300d03440346001400f4060943e101e602e0b00e1001c849400e01903020f031064404200341035008001d280c1d42e1f0080310200000710b00340450f00d20b404212100082081010052065081203c00c2c0d0382189980306001213688001c05802c4c0580c4180980300e0746110036040d031000c0715400c94401d6100e843d0b03280016568915100001600c890745da10009405606401400c1143c4c01020200081d5071060188003058510079107000d01130300050400e000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 568661429 1250 568660179 568660193
    0xa050a03051201081c2a060209090c030903070f140a0501060f0b040b160303090b1e06120c040c0e130b0a0503120d021830010b1e0d080318010c0203070807 68
    0x30444030441b4440d021411030005441d0352181815003580d004e80c0010798084a03061a07036020360401c02c1c0c154641e203036180c01300307040d41c80b4001c000300142140b45407484042406003480c50340000650080a603541e501140c60301900805a03803180724210849000c0026003c0b641c0001d0b1000c0364000704906180200000d2103000e502100b0b20700700c09060392201140c0100e28440903092041808071000c1060440c01d000544000c41c0c0102505d04c1b070003401a8842c03440c3c4000ca40a0f0200b4415140800c0f41c1e05810801d071a60082e80103503c0d00a5210080d10302d400311580c102e0082c080040d100e1400c40c545a900741521245c138101034014418042140d82030b10f540903401441c4046041e200c49140303642a0303001030342c500505803494031451004e101817441e4404a00c6403031800e01c0180020407020642c0008500103031600c0b02d00c7c403da046101d40c0460a03484266000300c90a07488081142d60f4a0108006280c18a0002400313480303602c1c00c0542d105441c00001200c042d1171300101d1081c1000242e0707403a64 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 568662679 1250 568661429 568661447
    0x110c06010f05010c2604080d180b2215050405010e0906011709210d05070c1709040207060e0106080601090504050c0f0105071205030a14130f050a050a03051201081c 72
    0x50030070740c00640d0b207951740d0b04050060030142c40c3c0c400c05007600d14410340c801811100300fa04070003e042ca0850007001494580c4080301c1c1c50a2002441d0103900e44694030041d100d640a90002c4c56004552032000031103544040240165403003600c8001c1094604d00503c46000d804503003c5011034020361200510713042898403150311020395002c86030200c1c01c1c102c003400c400710742d003501e030b4602240480d00740500d40280c0170f0142d0003180c1d4a004403c1600589887e9620306c0d1030000c084c804034002070240d000e03448640441d000349401c11010300c00f511400c04980c5c02885035101d203400502400f0004101720301c0d1405140d026941150007030480074905800c10001c006c0c640041418400c041240000140810082441d0b0030700540b180d54403450500008010f0300d0304443c2004070590207030b04003c0300c2940c1c0703001c50195030b82004140b880d51005180c41da250501c2d104001d0710f40d00c81d200004081503400001401c0510b40305880d100c050b683c5040b115514050416542c0d0a048070100c000f80f4184241440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 568663929 1250 568662679 568662713
    0x907180b13030b060603060a050105091923011707030c0c150506030f01140f0c0f0d0b031203060d0308060a0902040602010603110306190e01090204110c06010f05010c 73
    0x2018000303644000c4244641d01003a21040c0e0000e4022080042c0b007149184258000b209440c50342c070754a000400104842e5072401081c1c18014041406801d82c3c40303504140030651014151014003584500516802d4800d03005070342a000811703c81c1d40029440380000400f800c810b810b2192050711800800c5d00504403200254082040e031040200100c0e94841c00200c54907103000001485003002802d02d400c00c19103020a58442c2c0c1841c12800548142100c0c09030b0080300503000583c00e4403000c580b40180d12845250081350803022030039810741c00326a4851401650100c044039040c2101e180409040d00003103400d0341e445a00c1a0031000402d004010040d80018001d121003185a124180304040b0b801c00c1d00a900140e5640b1028000c1105400d02c1903920b90041b8001c025602c2c1040741c01032540031080d00b002a4680310341c482c1e180c0050942081313401a0f4010401d20403660001942c442d103803c181e49508840c480c000000a0705015034050400b42c1340c06039141900b40f44c2c00d4071182d03480c0c4031482c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 568665179 1250 568663929 568663967
    0xb130c0e04020d020a08070806151b0a05061911030a05060f030d0e0f030a08030613020d11070b06090402031e19082703030a0f11060f0a0c02030304020907 68
    0x2544681c0d54030700c001c22840c00c1000c0c0050720f54840c804014003940d0001d010b802884400c2c010700c4600d43c0d0b203d50b882c18164420f41d030030f5a160882e98800c02400c944070f10081942c80751546600c100240881c45905c42e410904c1c1e941680014a00040140c071001e800010380e01c0c80400110352140710720780015600141c05001401030f545840f01003440e00802d517150300d000a883c9058029035182000021101c034004900400c0c00305210b40701c0c0d0181d0722001c1c01c8a48218404440f41010318055010365541c040d00d6134007004a149070812000d120342c4a81d000b1100701e41141e00003501403801c0081540550340242c001d100c80c0c8803490910740c0038142060040d80d00e10a4400449982c040c0600343c2c050540325882c920780720a99807901031208400310503400030190008036001e40780c0d2000015910799504501e400309480f0321441040d5440704c58591401d400c0d0181070100005c004d03402e600140164a003507401c01102a121000300d0700ea000c1036400039800700100d40420035851041040c000e0b80441445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 568666429 1250 568665179 568665197
    0x120201030b3102030c190c060e031c090b0115050c120a08060604030302060712090602130302030c0a0308121f0303030b010206010509040f020d150903020a020906040b130c 75
    0x904042200e01c030050365000008109140100c801c0808010344402c01066046003000010441d19002d0641d40012441d1045a82e440c42c0e442005114a103c1e00a10300b042501400d0401e552a548009810f1186000d03c02d43c7c0c00151007a48180720312150030481114035030b420400c1e03151340980188100001c0200a000d4002d070011305011800c0314940000a0581d00d03141c0b60806080018007c08441c41910140020800b10b5000302d030269114815107410100c038088428000010300c00c215001d8200c602c0803400341680c46455501070140e0340214100c501c003015260403c041020140002010004240108010030181c50740c440c4c2c0015460351809407803800000380201086250303205a00082d15803a5014082d6018842e039400340c90103458100d0503261170f445078414011503110080c0500041e00c004814411b10010460060081407000d0204010301d080c002c0d0755941c80281079101f40070241c0400c5a40c40d1502c1001c001a4005e0600c0103400b41c8034000c08020507a030010901071000e215 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 568667679 1250 568666429 568666451
    0x909070e060f0c01090501061205030a080601031811121204061b12021b03060115050a02011b17250f090b03131a190f1803031b020d0912020103 63
    0x24003d41801d00322000000350494041c181b040c20340d82194440901c1155024a0a0129070b0101c100c840000c418140929035844201c01200204a190250101721401c13881c41004c2010808111213082c030112881112581058112a1610720154041c1c041000420041120a0060b181a4071601401100451542c2c16807200703141c8552000b004401a04090001d4070407424241c0809034001d003d800400e800d41c1405c02c1d848000030700b401603000303120b400f0036070303110140c404d400c04014090940e00c03130282d1801c035010260880400c489540c400150b13510005480b80c1620728050303011900c40300d059003643c0300c801c1c064a080440c41743d640104810500d010076461b6084004500a00002031032913011740c02070a110000c50800001d4540d00c4aa200501c05540c61001052204e03c40145e40000c80030390811980d00180303404940703032480d1041c031103490040c11b400d41d0240341d262440c4140100780c0e9101e070303104030380342c04010086034042501000f082c080010801c8000c11890700c1070400051404800e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 568668929 1250 568667679 568667707
    0x100b100f0c0b0c27060a270602010e1203150d02030a050d050913020c06061318150605010801060f210228030218042d0219050909070e06 60
    0x1150405142000003e0588101e440c4181c3e82880507110119080041c1070310707001992a2142e0306480d410401d40406100500740b410201d1600568405c1f0340000d09603684001031f01800349070f004862a80901420703c00b41429413011030b4803c404905242082c4c0c14008100407190015600683e05403080d105400c0000f00c00300802c100b4440c0e81e07160903489100100401031400952414803c2c118014081120403100002d000c50b0020011070360170300c2d18804254104000c002e40354140c140b060302c1c900c500c0280b11414600308000c405a990078000d030390b21280152140d5000303103c0e079400192000c3c00800e0184c400c40206151203441041c4c281807401006031103007a03810084005012040d403043c0e920514000c0d000c8581240218141541400c0303102c0c074814400814030004034010303502d944a402d15603c01e1740f64003602c54000c1e5804510039804400d110f000350801612642c14883c041303941d0049600503400d440c0045001001e04085a0b00c901040741d04010001006030803000030f20180c0c0c511148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 568670179 1250 568668929 568668931
    0x60c160602161215110c030f0d14010518040507031a090106090e0304060e060910170906010b03060103020c070e070201090b15010e091914040203100b100f0c0b 70
    0x680d40280410003080d6482c42c42038525a100b4141c050044400c000040c840c804110802580304500060341107011980200d44d1280d180b1070061400700107003001001417180050410304084600420449465403021000f01600303026584d44501c0a11668128214488540e07030f01c58460000e84210a9983d5500c400c0030720301194114000c01d0a0042101c4c000003403084100400c000030302031007400c00080caa46d441744114080c1408201003001d5204682c0c0300d81003101d00711301006d0031448000303c1c0c03444014444518034900b1036a1842042c003040c55900d0002d80d039416200c06241951039510743c440154021f501c01100c543c400d00401350001104680800340b03510035005500042455403c500d400444c04200509840f50540350165058840c0d9100300c50241d005419615a110340d101c00303190b90444035280500500440c100120404158202000a0300030340c826412112071030110703c2c0040964002c034107001e0700204008642405d482c0701e1a03103450000d01d241000603aa5501e6242c115000f10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 568671429 1250 568670179 568670189
    0x1603060306090f061514131b1112090604051c0f03021b0d08030402091b04060c0309060f2c060318150f07030506040e1b04110711060c16 60
    0x83c50209003090110b9070241103d054840540d5280440c1031603901e040c10741ca41d0759518026882000200e00e041c401c0e91110b1043d00490041010700c0384803c030006c01000082000c0a05802550ba6240480003023006036003001000401c850305190500d02803081c80b01050341c035016007104043d228400710b580743c000e850075580254050102c0340c0702405a0b00c207503441d21144034040e0700c0580b038030302c0850299130030349801581c12035087c01540c1750302c0342402304441c220010108a40d00000e000520b03540000c1e6102c411071003a1280d40d801e950b50502031711000f80d980203940c003050402541c001d01f2400c5070040c1445005001041141d220780d44007203006078108583d04516010051446400030f0401c00c0b0030301c11131400814030300307252030080c44008228030040d10000c1819141c402003956540c0f95000806500e45900843d211402c0e004540d1301d4690080249a00036440c0100080380d25801d481180c5a050300300007068010aa040284a000d501c05150b0503914000c000075440807440105104000b44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 568672679 1250 568671429 568671443
    0x1c05061f0f0e312009030d03021911010e010614030709020702061603020127030906090602070519030f0506010f09022109100c1106130b160306030609 66
    0x1000003002a11441e07160101d2480b40341c00d150b48111202d20036140c80e03003203002100f5071000c14540030001c3c00074040c4078034000484c2c0d01c00710210300903104e0300b00607150703c800840480d05801049601134041703203d80c4910b19001141e518400d11a1405022800030038a4424000654101245030250840b0201d4200c0711142003541c52a070202d00e820001c0b81c0203800700b010114a410490750009402e8410441403d01c050415a1450107050003036001580d600e811950230301b510040e5a40e01c0503040035810341100461a0703a02c0101d1854410344000003602c0c0641c000f0300340326091a040006c0151072080780c0c101030031a000e012000032482c2240000151080004065650502e0548002a80d4503000301804030300c1030000055202010002894118240c03001c0c600d1601e84840c1035080524288416041d541010802c601c0c0c2d9501c00040c0c20700740d002000b40c1d8103d460f81000c04844800480b40a40600001c2000c651800704c0b020540c2d002076160b00340090072039030b03a9941c0d070169075612105850b01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 568673929 1250 568672679 568672697
    0x31211090109080304060c170906030109230108120c0c03011a1302070c0b090616110a170715050c070e16030506030604200d0b070e03031c05061f 64
    0xd941c200c02d03040050511240134605143c100380004001005040300981017445510a190703400d1071110072110121800351020f40d60b0360712001c904d00989449040c00c0050a002c1c01075284018291003018183d0305e152010b050780b5004440802c4803608108410702040c0180020440f180d54244601030720002c50780304540e000d4010800700402d640860001c04229401046030b1070004450172a41010707191400d00f01030310340303500d14081040340c0507140c2c000c40381e85620140030090012000f80d50140b0718040b07075811101a2150032300c041250360500091441d50014100b0b02c1402e0182c0749200510415140180c2812a0016100c0c80d102180e44480c101c45444424801c804201c010143c0111415040c02d2016003040340210795544002003002e0800c0401c240c0f058480c00f6004142440d584004010302912015400c0c41d000c141e10136621007001c2241c440102105040c080103a900c07041a100715019040d003011002005008006d14003a405a82c00c459100414900c0c01040c03154066070f51200a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 568675179 1250 568673929 568673947
    0x11103030906071d03012a02060c07030315081504120c0206191103040b0414010807050d0911041d0c040506060d051009090501020d05060a1203050708070b07080f0703090b060d031211 80
    0x7e0400b0b12100501190040010080c1020745c020440b00c1d4107a01d40781c0018655030f0035211500e003522940001241d800341c04141d007541311040c41441c0c00b030b5000d40103109024400344000c0d2034040440360000c0d08100305000050491884004400310600c45080902a08042030202c0b400c5030300a4101220aa60108051001c1500c04c000301c81815401c0c01d081c0114106503c000e811809092641981c61b0b4071080d83d0400c10041869900111002400510500c0b0702c101c0d80c00e0100c40c3c00070450001e4860b510241005107014000d56004460141c015482c041200c09140c001e8a0700900d0704c042c00692510000781c901e0140b00d880380840c050710005848040702d88030f10098440281c0950300c07843c20a0414001041d10100403148603505040165559a2528007855a401079060107454401010200415543c0095900740304500102607485244d5070200f040e0125500c1d00c901424426000c03000950505020a244000074024284104003156001408081e1122000c1061401c0c10100e02603170 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 568676429 1250 568675179 568675241
    0x3030d060803031008010b0d1506150518040b0a0302150c060705030618040507090c0e0a0305030309061014090702010905070915080604080904020a0909020d0902011103030906071d0301 81
    0x40034140c031718000c0c001d14078480d000860b0302c444403801814038500d0407456003000816a0119000388040c0441812154100001070700a8200444040441111101c905081d1504e4800e001d10a6030081c8500601410b507020300015444c1d000e504e0030042030800051003554400c100403441040e0342d82c0c41c2541d070304c0c000c014084410410780d014460488002d00b403000240700443e401c000e40d1000306000507443d0004400b02d454a401e41e0120360404519100030003030281c04801075108541900407a1480e0719000c0010b02c2c8240c4a20800c0e18203108140240a1440c2001181d504039410f8800442e4058003070301e0322424407600c2d602005a41c0d40da00840c2d0749006c480313620701005090840280256160039254401248650381f6801e2040da800590b00200350302070380480018010081c0119140c96182118a00410a00783c0c02e90129503000004800c1080000c00ca9224440180141c44152107005042d90444203115040321070303040c0041d41d0075841d00d0904ca2400c5d8040b50980740302d48400101300680b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 568677679 1250 568676429 568676461
    0x816030c060c05060a0e150408040929011409090f060f030307150b19150305013002011b0602040e090703031b050a06140601030b040b1c0203030d06080303 68
    0x107401d2080341d408800201e0000314449034402120340010074401000850203090030104400c183d82074001e04284014440294064030035a0a440c000700829992040ca800032074038a411900031402182681601c1382d4841c0350000c081002c2a100b15050007101c200280303400004682c19202803004070100442c41c0b800b4170442c940010700741c02031850f15080344c0700c5615400800140b41980f40c1c40300012003007900c4400714080035a1144051240c0c41da141c04801d55411503468103080040d040000204400d00a000454203102401007107081c0c1c04c1011141c500300e02a0707214183c1c180101c407803503c50402d150307040000300c00f88a10340c016682d5003084011207034228090041000380c0d01009007880003c2c1c1142960802d0510307030b40746032002e40461410318600980e446005111343d0500625280d40c010003040e440c0564801d0300c081c4600300b035403420311040380c1010301c816034890801d540d13003091140b509500c040864000340540703203440070032018002503e9050f8080380e0107910010400028036181d4002d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 568678929 1250 568677679 568677689
    0x715121e0f02040501091703090d0b01080d050a08070f0309080c161d0103030c05011b0c1101140a0c060e0604081e0403080d0c02030712050a030c020f061305070816030c 74
    0x450500c4d082400003001205203000341e1100761404c503007070a040d00040080d1004031400404d8480c45074205c0ca4081d50551080c07003003410f80c0c825071111418850054040da11681495501e140c02ea50b1085401c8a442c0300b245060700c01d050340c1d20100700200313841d040100100d240308001080707500c548a200c3c0e20a030301641c0c44190300d494408030b1408440782003103a11381140d4240c900340c3c41c0e0760810b0800c1801001c00381d00d0440f043c080b0f02c02c1c0c44260b0350401039103202140601c1d84150401c01c4480151548402c41504040818080090080344d038081c0595501c0e82d8003d0342c00061104103070300349500d4014140c3d01a1008040803942c06070390012040b0f00401480406001400c15186944a240381e01561400c0004680c880020900007842081503407646074101440ba00d41050940014042d940702441b4140002d09180c0e0440c181400040c0d02000c18000b01d0061165540d45020a24120b0301080701302c4050040c000001441c100420041c4c500303040c0d06c3c101c0724205155107040001d035a41e50f849 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 568680179 1250 568678929 568678931
    0x71403030c07051212040f14040e10050c1209010e06131e06091a0115030b0102060408030601051b010507090e070804150b061b0d0305090715121e0f 65
    0x4007200c1003008102e820488209844410740c00c20160801c0f41000001c6008100d41c01003c1350010301c80c2e410362040d1040b5910040c51800044a40d0240700c1541d2690540d400581d104980003035810a40c0d03402550701000f0f10110030305105085902c1c1c0781f10030080d9001c41460391036580030804440305000558120b0302d1000d030000d50b4140b503034424005402440c0005003450150030288103119030f9401100c8501d5200b04460a429100380c0c031548550020700401100d018480c1c03404085500074801c28007141e2058000708640e984554540d141540010302d120f0402c84244180b00581c10040310740490501c0b59800441c692526840003040c0350304550010351094070043c00d0011207074010081c1604243c11480d126a0608680d40c080090032403401318a41040000030780c505011740c0c02558651410000e000c0d6003604407020720440030f480d01a2500310241e00500020400c140c00c14802c80045c00a40c142854410140c1d92000225080c044038540c8049810711031150b2182e0fa0310540d464107400c120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 568681429 1250 568680179 568680187
    0x5071a03060d030f1e0206091b0f040506040207051c0807020d090909050c03060112061505010206070f1119051c08071b0c06090317070b0a05040218040507140303 71
    0x3000038041c03442c10300007505119130b0382008010103102d86100301c1d0307070310400070141007143d0300c000002c1d5103540484155070a80601d5122898032901c910030711001040c010002c103031001c041e60401c0000c1c000580550f0340035a081101c100060403e10544108040d9444010862401800050300c3d08a00802031011500042c541d8502c80b508103043c403040d40c000c1c1100042d50000c1d450014940044880710075454440c110000600616a41d0800442071140c81c2c1400502c0b00c92401c0003690343da03030003401d0241c0c000b500080d080d103106034043c0c0d1fa00c400350319044a140d030342c1d070f02a40c0c01c0440030342c102c071040c070101c5400109218081000c0e2107000710400403e071600d0102c0100400400c0054030740e00c03c102155004c515201820160741010740c1e00011124455607942101800c80003031880121428860382c003030b1490a0001805840d4603d4003d008017a807039581d695018004c24005204981c0400351105240e603030462800031910591192004211613400d1120328900d65030010000c520a5200300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 568682679 1250 568681429 568681441
    0xa140309060f0c12040c06030b060c0c1c1b030215093003040b040312080f010504110c1f1503051509070e07090603270f0c080a05071a03 60
    0x15889900030108840d101180c3c8400d2280002e904c9003000440e50154040c3c28007003444444000181220b205031800c1080e00007038000e01c00e590058080d0300200d40c00518902c8414104a00b604030481d08448814141707003216030300c07290b2080344140d06500200e00b0035030500460601c5902d00c0003606542905034200034031440041c00d403d0074007103c803c8031200354503075144503510070351016803540522081d25200d0303480f030030b40c48001c0c1c10502c420b68104000d10b004002503030280b4012070080c90070702d107070395140d070f003814140000340030078461564401d1020808182c0c6a5818045020000d4070022081240c02c100924081500c48201d060301201d10412400c01c000344000a4210103201102400412744da258407c0e2401c0032603070b90103d03107280c40c80010801499031241040c01581c42584040103011951504400a01f41c401000345800021100081c00310300d41c4d1000031000382c0700d81e02401b0801e8450b0307030742400c08407401812a680d501101c400d020141d007800b03020700700c4051941c103241946080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 568683929 1250 568682679 568682683
    0x50a02031504090305091008040b060103020c06151f0c110a081b03030417150a05010b070206090321090a05040b10080907150801060f020a2018010b0a140309 69
    0xe41070340c07090381d8516aa008142c01101915403040703004001d102c40030000a8050306000003120200d9040395134000103802c0d0f6010340f081e00c400450a8004012581d641210007011030040059564030010170840da1007000120412000035a1866844091081c41c03440c00260350200206440e21800001e2002d001250000503556580440d00c17000c00c59694000020a08605c103a1f003100300ba0007008443c0c1c22001400054000f2401d0001241208581e5080103500840314280210509414200b0118025151000c09021501030050507551124074120310b054641011980011406101140c0c2c0021441c1c0690400d004280644090080c40c03101400907040c2c1c541e01482100b03001008003c1500d620081001d84003074192010307030a00c1040d18800191a040c42407041c10005016600e030055400d20209900c001d1a038000da40103000b401520b400040c115100a2403034101c84140d00900d010700741a014a8001c020140303802e0741c0c885c0801002801e08000481841403907804005000d200c0f580 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 568685179 1250 568683929 568683961
    0xc0607022a010c05120702010f0201060807030b041a010920070c05220606031a030a111212070614060303071e2f010801120f060b0105130801050a050a0203 68
    0x3020740c0368140540c80000607542034911203400b8069100c0d03414001d2130f00032858003d00256000740ca4005810010700b20880c03d03216503024a00d81500b191400308009804002a650000d12a00600d03540013205544214111801da004251050f09c2d0108184007448112881c002c102c61b200c00d240c500300350790315084018002d500c00e46024080c10104030b200c03030b40180920103000a00080a100055403404010f0107000b00082d54454807808e400c0b41403a51500144c01c8044035808001c540d640a0301404001d12100c1082005545000788111850010803ea0040c041c044c4100c40000380800884010b06521000803c203d00940c410003005011401800ca02135a900b00c00e010481c0f0700d11546041210071886d07005440c0a044280892001880c81034400c00c0d0304002a1380b101c18036a0380350b00c00c103440310002c03401402036910702488001180d41c541003070780811410b051281c81c1c135242004107101c1c88169401050b03541d640e107050020b01c21081c041c05030010002d403029811410940c3c1c580c0e02c000c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 568686429 1250 568685179 568685233
    0xf0c0f052a12070b0a320612150a1a0a12050a020a1413020306180604090c0e01031101020c0a12020d080309160b03070c140c0310020c060702 62
    0x1d00620441d200d408100701c4807415038608a0342c9a142c0701c0c60b1514443d020320507a05170351034a08101c1c1e00015000c9001910b44110f90014041145001c82d02244800800181249400a080500c42e40c01074004004400511002c02c40051940c43d00c002003404039650b0f00c944000c0011884c2040ca156079503240c6131001e0b58240c4102e400c0c1d81c0d030310f881c2c03040c40c2102080d0029080070700d0000c0003a581c0721000130414170020503101c805008510000c10130881c1320450322264402c407012007410010300c04080903940200c0240c0001015209625400101010751781308460780c9000c2001030041280d040e18102400d88280010601c101001001600c00109805081618005140c0c401c05540c1d0f941b4010f0912038003d101543d0301e00305060580d4aa0010016424607002095000030300f80405404407407041c0010b035a01240c00e8416074500c50030280c51034042500344511541c0b001640e401b0710001c20814401900140c0c0c9100d00c210781030526400a1040e03065410214920000f00d04142d04040c00030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 568687679 1250 568686429 568686487
    0xd02090c0c011a01020c010c0b071107090e030306100801030c17100905010e07080a0f0227130b0906040c1e0f0e0417030103110d02040e010f0c0f05 65
    0x5034540303a000c511405915000d908035800c09088901801101c4180a2030500a90070b82d0041d440c0701d40150b50005803c20010b104202c140e0014040fa849100f0b4820651581c805880f03100b9950f06000054544100c940741d1140c10000030322400340b400d41440104034665042440d503961460311040a000802d10804001c08214488422054810711100c0c4c1342480e11081040150082e0610b10b0003062062010481171181e8580401c401000084c200340b683e500030009100700705143d082c82001000d18842d1080f400c2c20503003004407062a144918400d100500349075181c0409410488410074004e070180f106500218180004503110704000740aa940150512a40401d11b04808649000c5540001200c00b03200d0070105251003540d1102d40170300d000b09800d030a0408252002c901c284000c0c40002d2240200b4400c1140c2814003030000c00c0c8d030b1400208002800d800300c159050031368130704460041100c0da035085412103403600808400c0402105241407405d128156031007140c10360406038014909 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 568688929 1250 568687679 568687681
    0x1030b0f04090b0603061f14030708060a090b0703020a2007080a0302061501030b0d0f060b060403110a150504060806060c0115060f0f0e01050a031409030406021002090d0209 76
    0x940311900031a0000c80301800400040041d0300708800025003d9691600c28091130000c2003d40090560080030406803132261001145800b442d1500740c1c0c80d120b03005030180100b0b00c1c000b43c410380601c07803244a00ba8441c804200100c440c503040943c0e105c020700042c10f0502c14051310600540c0030b00c03e010003402c0e5043d144840c680c4070200c06c1c035000c55584403030701d640f18181e5044200340e400b06000d03000c0d00340d100314010419107200040d800c1d0389130b001f09550404038806d110780100d11900b031141c440714000d0307400042c10b00446000c50401d5015410950306d50242d046121758034203201d100600105460702c450f2005175034540c0001c1c014420b07403140a0400080c1c1001c540d2643d510707000c80300030726001c0008200d40e109106034081045183d01c2110080b41c1c000700c40300746581c0180d000b5010071b5a0345d5178407040d103140c1c040155281c0e04085c40440403d55181c1c054a898540141c0c454098400307580215215072030640b0003032030034034440d030515203050050080c04c0b082d03100d10164009450b170480f845112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 568690179 1250 568688929 568688951
    0x1050306030a0c0803090a0806060303160c0b0d1e0603023a0f0203070614270a03080c010b0a03020d26030103060606080109200d061701020a2c0103 65
    0xb90007682080030b4030b03903e102440041d11000020040030101c00c1643c8004801e940c6000c40c5440300011181d46400d038000700403d000412480200030100c0b0f10580c04455010340701c88041400c0d0b0002a0036102e5aa07660402d9640c01d00030846240f1032910180040c0318843c01c6601241c540f04c0102280281c0310800400030440b42d00790140039012568410005035001d00381d00313240ad94141441d5059000f4090a080461610304c640c42c401307206213420703008903d04000703501c0f11010b10343c03d842606122125603580b56080e42d601c0c20b00a0040d030240c0380c210345800c54080901d00f15900030b06510b201e8420054108010303140c841c04500d0303407a00021801964924150041311401d10700115070601180000080708114030b0754065800c0d100300340d4481407541c0c1c030340c805401200d03282c43d07200f80188008a99013600e48400801030007154048400031491030355a01480d08103200c600214050759401140e0240650b91051030010000c807016048040282c0c0000081c0d0000380340d00c501410903032983d841c011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 568691429 1250 568690179 568690183
    0x501151d0f0607110405060303070b040209070c050d0309051002040602103603030b06160b061c08220506040b0307031b1e020d0e06030405120a0c0606120c050105030603 74
    0x102010050001c50f030f0390400d803404150005031321860a200d5464a0040f442c070f400c0000070703554800d6001880c40e00c25200c1b81c08011240000918290030414040c0c190400142c00340308500c091500ca40703000c6406111843c1130b5007801d5000d0350a0031468418070080180640c0012010f020240c80f500001d100c1c42c403094500b1001e40101d8000c80079901c55008849400400d1102c5001d95020b60350410030706288104200c0140308054a9004500d8400128004a0003a408180c2c10410051547c0c0c02078501011085e54525081d80a4074075950114100d01008078030780808100e002080b42c8605010700703110004070640030314001d0516440021002030101d0b4040d034400001000e12210b413400700e542c03019005150b840070703031040356810205080c01c50a650002808a200294075114070060404020900000b44c000a00a0710b0512820f0700c10b90020060b40000c142000c0c841e629a6800c0300b160034800c049e01d009038007140d404041c4180c52004501107003a03a0050700d10910f449135403a03d80b030001034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 568692679 1250 568691429 568691449
    0x705041a040606020a0b011a0702040b0f09130b010e1b0c070b040902090f0f03190203191a0f07020601060f02010905160f0801051e04020621010302040501151d 70
    0x41c1e001841c1c0100499038a80000e010910b0134400d030b00c19007940c0c0c2c1341c00004003141070750b1408004261081c45200010700c0c19030018824010080c01d0654600c0e00d590005403401c03030540308045084c0b500a01703041486407412040b405460080a2070380141480899484131040441c03c003800350382c0c0402c200442010502401c001000c425507000c1d02c460700c0700080c0c0029800750300054030414014000341a21b04040c65330001c0101b000b40a01b04000c50300b00250420118880c049034503005228400c545908005550f4100501804046506c0d20036462030b44150180544030b8079681c0104400c0080d242e6002955906468651034003c0c00d04c000003d041c0d0160600d140c008045e07010f480400300034061001c40400498152a286180d055031300c404403400c8420540e03d40c1c03071031034a5000e44541880900b0303001e900a0720152800e850b01c108907000803030004800d4441280c2c0c080b40030040080d85814082c0d6800b400c007035100018903908000c4090191940d204128520320351203a40c10660350b403589440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 568693929 1250 568692679 568692731
    0x70926100c090b070615060f0f0e03010207080301030c09050c0304050307120e102114131407080304090f0203090c0112020f0a09030c06090308030c0c030409060e06120f070504 77
    0x44d210f0000d45054805052000c84074000d0354200301d400203059214200d0f03148103940584443c070111030740c0c0da812a4158240400355400d59000c00c0718000155003200198000c40c06034007090380041c20703d00f09009807800030b071031007160003028428040403032030100072100d000c1d5001481441500d501001901c404001c481c149911070360b00030030b804007660400e10080c0ba150390000e04c0710900950701d0380c0108440d4000e030b5100542000c20300264840c0c0d24403520307081d000c1c081c441082c00d018400200c0c41ca400110b40040005030800b10702002860858040c6401e0207004c49404d41c00c62505607030265072826110300050401246800c401c000340790030b134100e880d4507a174115074a41d41e00b40d11401030040c40d1544012110915038050001d0300c8ca100d1a2105c0c01d4aa114003d503146442d15880c40d46141c1019014144c107000c100700025185407544201c074020000445104c48034a0110100b1003c000e52524216090304501c036442c1380c0c080049100b0040e68012540000e07480c00146d0ba0402ca2080d08811b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 568695179 1250 568693929 568693949
    0x1a061804051605010f0c080c100912170121171b120a0203040501051b07090b01121b1101090b07020c0a06050c03071e050105070926100c09 61
    0x10300081c050003103180642032101c5014580311581d120011102401409a08000540880041c1d80021034010040520f0880c180c100c03002211004c250004489040c80304841040d41110302c55131540d00101a401840d1210740c3e074000c04d44c502200040780c441c1000e440882d6003002d19000c020022002c007040344280c0211040c070b8a808110000c4280300180c10021180c9109142c0c07001203859195003211040d003050350256040510b00401502c45402c03d480035450740a180c001c403001e43c1002c200f00e9000344541180441d1202050002400d4201014490242603080403442020452190030402904615103020a15105130b54805801003440c1c0100405000310002400142680058032030140e00701192000c0c0050b075500b6080da1544215880042960001d02819000c03c2c00c40c50404006a0b07118290183c10400303640726402c680f003c8a000c004140b0600bc14408001280400350303c00a9808000315404154002a56100201000081050b803180c15403611030384114402801072600400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 568696429 1250 568695179 568695181
    0x60412020a410102180418060b15030702010c030507030902010207060e0609131b05030f04080f07050607020f010b010212040b0c031b0c010206060d1e061b1d0102010501031a0618 78
    0x10242c040d40c00822140116525000800d4240c54071b40300e40250007a206803c010041034070b41e608c101a040000740c8962001e04000d11882040034440214401c550a6000280d080c064000c05812180b02400c48020903140848250060742c00048210903640300341820b945151780100018160f11520341c40c00c3c1c008171606e14005a003a01c641083d00c0400751410203112051014508592901007220310114102c0100081800300b01850014194550410a840e10340301e1280c940900d045010b840c0034005a0041d40c06c1070540c8002e111f09440000240b0107028500d2802e0745040a60041f409480c1500500094148051108000f141c140905500c1040400c6001e0101e00c0c2d00c441c0e000202902502842d0300140c620300e000181d090f500c5520003100e5111102541c400b0390b201c913842c0c00403610240c1c6c400040306841d401c90700d4140d21365916540c20342c001100e85540342103003c0c40c003640ba0544e810000148000344c500c03200303d0b03400c0410404d040600e07901d46000a40342041d4122400b0001140b034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 568697679 1250 568696429 568696553
    0x2211040e12070b01091e050405030708121504150501030b180f011a09180a2a12020405220204030c1202100918090c0f0602060412020a 59
    0x1010b42603050041c3d80140e030603a03079400d41606031340000442d241041e0408900e03400c51040da50046400900841c1100d00b400066514601d0030381c4820f00706c0c2c000d07091690400544400f80c0080c01c020710010f940a11084d294a64425544001707070241d18189a1070741c3c0042c9094444464500d064000c3e100c0720002c03810840340f2140401401e010f03000507031f4092017810305440080d108a80c2030010140c5020160345082000368868407010301804106910307001c0030301d007008442c6020f00d5010072251010a2000b404d00025090302c403482d140a50041c01408100021b550700ca4007003181045807480140310750138800d4000d00a10840d040100344a550040108411a980f081c4a410a1098900040001000505403001c052034413404910f50b10001c3e4584002c082900204031042c847ca021030010f6031a0403035250310790b015412140061784128200001e10095001c40b0754210300c42d00160000b10f131151142d5144074105030b035905420b031b0302003003d540340a107404515a8000d100c142e100540c0c0152 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 568698929 1250 568697679 568697713
    0x60f01020a0c09110c2d0a080d0c1107060f020c01081005010c0201020a0b0c030a0b180621120904060e101a1215090703180605041115122211040e 64
    0x30703c90750f0b4800b0f103d5800c441600c6c2000540d0024158104a2440c14060600070040140407002c100030100f1000b14280e01801404000000280c80c041d01e415a4007001035070b00a103031144c4841d0440c104881002885000c12402a0303000076980c003817901c407041d00250300060385407440081c002400f02c80e400b0100505201b0041c09180145240d0304244805005503003004002400d0400500c48240d540300880d10a00d0320028828400202c16901c60009030020030705824081400100460300000141c9001549803501c10840a800b902e441080703e41050403600c0404001800360501e12230545c80581401503d060a484503202080004400c40c030709030b0444002ca0b00c0360040507028940500106d0740c594000e0003030301503070320048901c0000030a8545032000546000750003a21500d191210f2419151a0043c0c2400994600308801c0c1d41c910b808910310047c0307035005080003140900754a4103c40643c4080442c811b041e005800c005070240e95400007801810f00840ca0101d6115840302d4603070920803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 568700179 1250 568698929 568698973
    0xc0313080a09080616120b01030e0118140703050d03091a071101060807081f0b04020f12060102010605090402120c0a08070611010203100b131d060f01020a0c09110c 72
    0xf074102500c0440d01d640c640e542075446a074040d400070a0466900d03142c0107a40c0c1c0c2c80550202014035011031007112002c1a6401c5030041d580f0700c00d1091550756148140584c00c41440e120000600c001c280301455600c80d980c9a0082041400825444001c2c6406014a155240080c079182009907100c50620481c0a00030340c0580d1200e110550038a5800900f00501045810071254076a015020104103103801c0365110110f2400007031820f940c0c0c0c00701350460712148054000a114504049d44c0c8004400000700b42c0c0c0c0c0000c08080c11a81460810b00050301c402040e160802d9059414070b1509018218039420040b20300d10440c0c01c0400a100010101e40c00550141156402e848140c07240c802029a11b081c3c0c8800c4950051800c40b9000800517140c1810040255030310204400c4261511851410201c10b01341c00d07400001080ea009110243ca01295600160b85090009040202d502c0d40d0b00c09086003c0d1059000351a0755000d1021000c1d41c56044401600740c0f007083d5503018071069040c1c010020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 568701429 1250 568700179 568700189
    0x40c08040b0a09030e0f21010c09080111040506210f0613150605030403050d0204140a060c020915030a170a0201180b0103061503051e0c0a030b0c0313080a09 69
    0x303100302041c0c521200e80704103c4aa070b01640c0354030460402c0740c1480814011112103d80041c0c442c0c003941100603080e6007044103114140004aa0300340072080003000101e40d03411848070b5034501106000c0344041007049404460054882c0e5032035100c004484040686107041505e405d0701c084040200d8a10380f0f0400b036100716011105000f15824114118084031244c01c04051000707591003061002c0c0c0c0c010030282d039205200303142c00752401c2ca403002c2d510f060740c000354414000d00d00540e28140e0503140a61815000e48010320f400000c400d200d40004850000c0500b00c1e0040c0d440c02116103103641c030240300d1100c0c200c3e00aa11000d41c4849480206110380c000c90141340103502e005883c5e828150b000c41d41405039038000510b02c0a990031078840500501400c410f502d81c0000800f00040080c42c1031000c80f440384c40180c0803007000620b28640c2070421040c1c03c03040f8842ca84000c0240700040215840c66007024000185d07a440303a88000746d8499400307406102601f02d6101081070681c2d260311102c160290340d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 568702679 1250 568701429 568701443
    0x30f050106030308090a0b06090c070f08090102120901021b1c0309051f0f05032a030403030605060f0d09020310090c080d170105090403021507030218030712030c080702040c0804 78
    0x1070344080c0c5d21601c9441100004210f80e000e1000310700715180141000d604408500384852402c555a61407610f00302020318110b80f00000400d0143c51503070180036480301d500340d15032010329146103c2d000030340340e00f004005c0703031032084d01c0303024640964450040d0213401c480c20303602801c5c00c480b0500703000c0c1038001c4c50302c1400c2c440c402d0904541c003614800d070200040e16841b92130707a20790403240100a8819400080c07116100641d001d148107020300c0e850407140d54044c20685000d07624145800c1c0141038580d95000b207801614100101c2c0b488540d190b00301d078408422001d000903483c18601c0000e080119140c0307100c005900380108201884120700c102c3c0116120f010032190400703038024040e43c0d81d007075642c0782c0c20f040031141c0010801414160b101540c80b6102c0d00c155a2119810302c0d441081803c152106400a640858024845244421400b940540850040c0040e500d00700c82c951001807517040050801c2180c400e40c1041140400a485074286d0003042440039100454004109407011034003035a0314 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 568703929 1250 568702679 568702681
    0x403060f0b030723090411041a060a11031b0312011d0415091401050907051f1808150a0605060903070326070c0e100e0f0709030f050106030308 63
    0x30100c98410200701e1103000d00a046418681803c40640c00030707112402204406403c420460b95403030503107503881107108501e01407813140a40c0034801181d00c030b803d6103d01d80c40e26038a50270856503100c060318011802480c14040302070492400c54158001d103914a0744406440c588072259045c0480078100d4032081c0006046183c3c3c1e00c0c5048107002103804101110318805001041c0454092400d0880c1078089a102044003e010343d20a9171003520f02c8118030030390f5981c10a115221005014901c02044c0c21113440d040c450b5003040003840440410084030038000200a425008505061850010048181980c4040b00268403582c040002207d4490700b5901e40f20707010130b007880c0810942d51030305400340081c0603250071076030740006640141d0604820089121080d0701002260f800401c1164498445034541a1170043e000700c0b1220042e0582022080d22502031001410f060b25a990004281401048548407004240e5502c9602e400c0548009041e035140c0b014024150401c07807c0346e1086c1d442a0351 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 568705035 1106 568703929 568703951
    0x50d0606031b051e03030f03180307120912050c010804110d050a05010609021c090c0306020307030e060109020c0d0c02120102030115030b0f0f131506020102040306 72
    0x42c401181c1400301c3e0070701400e8000022080c50700120541d200304002510b90144000e1403004a401000040040018aa48022030700c00d2605903990782c02d150800c105a202d07200f043c0d0010500d0102e0008801c1e0301d01090030f44131a0440061310170b0390b000e0801110250f0000d0001c1d141c0700c40c0800216a103a8a01600d80c01161003000100f40340080380c6040c500707549943c2e1112010754810300212282d007001c40d80030000c1c0d90407041c00192459440c64101444640c640003e00740c1c61012041040c00c1d90140d00c0040340703800001c11540c09a0ba6601600203070312498201001c541c205e940c10102c40b034062000007180d5880144480c11240c101e40601c0c2c22600240e1050300f82a4840d0112243c180d0584544000c0e0f210a41d4038100c0481120046400301a181c2c082c0c900501c1c4101501c00c032500c0c594403040240300070302007222090b0741e0ba40009002c0d400c0ba000641d0300600e004d02c0d03144 = true := by decide +kernel

theorem cover : BRFrame.Cov 568525179 568705035 := by
  have h0 := BRFrame.cov_init 568525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 568525179 ≤ n) (h2 : n < 568705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
