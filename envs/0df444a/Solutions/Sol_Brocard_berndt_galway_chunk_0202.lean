-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:25:12.107893+00:00
-- url     : https://prove2.me/submissions/8895adb4-770d-4aa1-bd4a-9637c3afc43f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 36151084 ≤ n < 36330940 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 36152334 1250 36151084 36151097
    0xf06220b040e190327080a05013602010210020c0a030e0303090d03080a060e0726010b041208091c03020709021c020304050307060c08060102190c0b090a090f020a 71
    0x4081c2e09000500c08007080a08200300c144080c1c0e941c0a03100543c600c240340352404040100c0441403050705001c0001400800090304001ca114a8503a084a84540d166041e03c0303002c0c507105001c0b40601d132002011005110100d000701d03000e130005074600320410440c148040e000050200720329102190f102c10103442911840707170645a2408064603801a9200c0329048484d401c008800f182c828042150800e07944040020302079103602c074480d005501103d2506c0825541890380070040d0b45902030098000074041080d8680d418045000c0e01031140f442500710a4040d03030500d2007402200000c40f1006d007001041040b185d02029010502c001001400368058060040005000b018900841d09810018a00b40c0925003d0600d210025080174000b540e6602c07060201d50000f40c0e291060071412551600e880e40d1625144000915205000d40b404034a04014034001000480d000108000d4405003840d6680b140740c1c0001183c1f083e0401d901952201c1d0911000040d07001142d4000d022030074040e511314 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 36153584 1250 36152334 36152351
    0xc01030e03090d080c010203010303170609041106030603010204091d01140106050403020607060608150609010b07020d110d050706080403030b01030b030309040c020c0a0b03090c090603060f06220b04 87
    0x190100c0d04040100034031604204445511031510382d48060b90300340b2038041e03d814007400602e4242241c20980003180455545031845269401c0b284821b980500100d5140025103017550380c9142c1980004c801e00d00500b804400310300282d41c00e406079406011524404c1040034803202c25415080c20b1000c03180925441c260001042c48954012203042c3c2e070080d04c45618040c519401c0c885140e01215003580c019580d00b0001ca1101c10071300041e00348410719540300350307a402d2000400400c4881a80314480f01e20b0104076000050302c65805030300026030881c044422551100000c42c034044044d02c0000c0560090050204241e90070801107030180b07010b55810008282c2460055085400f548146030f40340d403041c44503510341c1c640343e0840b072440c1d052441650001141d41c1b01142290f49076170007400c1d001c0804070030001100c0080200301c0101c60304854028090a022010030345a1001804400440030503000248103a202d00300c54800c1205840c003a0501038000d584038400030425a07044920540c20403000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 36154834 1250 36153584 36153587
    0x50906040203041a0601050d060803031b1303031b0c0b030915060f04091104060b091c08090603130f030c0b060907021b0307090207060e07240f03090609060606020c01 73
    0xd41e489641e1040c805044d02d00005412000c11100070310311810010100003105141c40140500c5004181c0400155241e04000364440441000c452581425031400d005c0c12a802040550580c112a0141803404401d25021a0300d001e0488a28003c0c040110b0030342c0c0091400b44030b40045110703e20a03030a03214005504905465810426901c40b03078010003542200fa05890940e00090304036105c0c44414a66074840804030b0182e515603880400907203804100b0344064100a401081600715100e0300b0840030310380707994050042c0181c000c5107024400200016003460300f84248501d00d50b8000f40c1c02c00c101e00d0b00e403400625500009804542664030500410301d642080400b440c021030560700a00201016800d01c1c1000038520810140d02d1701c58203400086072061440202203581c0100c01c042150351200003210314241c07017071b4030100144c000340010f00f00324200c55007641c0403401d59180850003000d1a941c01c030080d114082c0068981460300c4540f40810a05a0008084035880e030259542408075a00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 36156084 1250 36154834 36154837
    0x40e010906030b0705250c0f0b0f072306010f0914070c0209070c080f030703050c04030809271509011a0d2d0605011209020d0303050a0608030706060509060402 70
    0xb008010041c01004640702c14040c9002d000795030041805410b4240d1404020171000c80708030b4090b01c0c5075440c100c050100082020800c0050600301010500c0d010122050003858855000c0c00f03400c40005050600344600b00400f10002c640d0080120b80c51540c40b5140690100018806d40700301a2a122034095803c1e021034556106541c1519070041042140e0280000380800428000401c609062860000b40f1100044c0038200d86000d8001d40300c0c031705108064229080034004980f4034800303000030400070701c000044030140c0c40c0c10b84aa158004803806881400c190140c1c9070f001c031001040c10013802031150850715501403401c48078401582d0380c81c08088007140007482c121144200030801c000c100030b01a00220300c803002604812020358a103404200e2498040740c0800c04241c0c0700c010802c100d43e0b002d5100c0940465003201041100d440e0390008050030381820000701455250400124400c000e40d014500404032201520b0381d503000c1c6c0c039003c402003a160007010700c40c2020402041c00340c1800d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 36157334 1250 36156084 36156089
    0x19020304091a090601080a0e030c010911010908031b010609090609150b0a0308030907030f03091508130b090f0706050c191707060905010212090c01020a080a050703090b040b040e010906 81
    0xe040e0f10b80d90700c2d1040111009200241551441a2500011202d240e000c000510308044903000000d5291680d1030898040c02001d0110350411551110a00c150304000c0202c03100360040350000007802e074900c2c14441c054501a071044a1a81c0b0704a501e00910149070480785032641310365015510010200e05000845e1680e003100e035000529490b02b40001841c000081d40c000110104407410141c1c0c030354540d048152100c00407030008250010270813401560307120006100c815070401c00c45914021507904030f203220f15440a0000034403800805e0711050b00748050403020200030107484400340c41d18409801580451152085441074008030f00d042030340c900c08181c05907480880081851020740c0444920340062106540050b610300160300001c1003480144806002603c1c500354034640751107101d040520020006056420241055002410050486a59200c1801d15540390241814102c8998209400282c10014002004603034610710001a03c2107403600300106609a8954420405460152 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 36158584 1250 36157334 36157339
    0xc020909151b040b0a030b100309080f0702120706020102040f0e160f02030d0204080a0303061d0103030f0203091503010f06020d0e010302090f030604060e010509070f0b0705010219020304091a 84
    0x50105140b03401d006070344503050085424050820b500c40404604075441040b500c000309a507003482d030600c2c0c2008840001c1c840c0c0301717060800400500e80c594204510400842e4992100b00042c60070440d901e084000c003000d4413520807540d903680c44181c0079000358464000d401c4000c20a040c002005002c07501c80030b10074001d0452880800d281d0b484280ca6290181e4400d00550100f800751040d0710b002480944003c2074144024815000e0720b080107402c803030b05038002020042a080f29a45591031841450341101d50500c2d110205088440c4103e096000d10701c0c01c158070041c841d1b03a5041c090583d801650507101c0f2101d12120300fa030307201400d90740c070302c2c101961101081c103800042d4507940c02a8054408020301819103403100111000082c1007001c21a03044a04942c0d8030710303212010400f4869107a01c035401d20003c180e4141401c40908203410240b183e03165400b400600c00e400c204080d016250715840d0803141d48815551000040d499410600070940c400b890310001a41c4803607800d107900e5a99001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 36159834 1250 36158584 36158623
    0x20f0c06091b0f06121e070c06050705121503030913060e0108070302010801061202071707030f03050c0d0518030c0f06071e05031005030f010209041b0f2d0c020909 72
    0x1d51000300b400301d81c001c0c0300e134086001c1001400d06c5aa030042e2268800c02031580c0d0029002c095240910850b0070141c411001c001003401540c042030810401283c11003500303d0340180381d0042d030002a02d075104402115410491340c03049450380482e02d400100c142d0b41c0207c41203d250ba2101c40d5565604410710020307000030b03c45001048107500a034408507003041c4440004d0b107010020380703c03a61030142150344030458400010740e0f40181903105d41e0010302450300d0300e020b101c03c0c14001000b0000380035001400d81d450759201c010592480f9801091084a4220300903a0f03140d09400800e1500c4541c4030360314082c2c5001d00c1000440d038038410004641d00c2125095441c1c400c0b00201403c44498200400c081c041d034418203c049695a010490901070554220001d84d542a10205010a90341528880c5104004503010741c0c40480d000b10320030600031102d150042016411003c02481d030312031240300a840588110190143c1030b8071460710b191076030080d25942c200d512130754840c9656481c100328a4005001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 36161084 1250 36159834 36159847
    0xf0f010503040308150d2a030804051207030b0103050309031b011b02120f0102030a0c0306030b0601050901050708030f0f070507020a0e061306080303180607080109020f0c06091b0f06 80
    0x5420040c0d08200d600d450316000c014000040f402500000303405175000052450600c03110400301455100140400c41f000070450300d165a1a82140075601416101e0756904004c02142c0c0c500b0001b000041d9044004504207596908010782c03690320500c045400b034060b8126580d01c01000b0484241414010394804140501060380900d2421000e00102d0f0300c0045c0e650710320a4807104000c000500d18180d4001070b81c90030f02c100142c00b1101c80b2843d00e801d15062980c00c01c0403500502031280d00c03120a00b441950340c0c03880c1d00100c8180c442c0c1480184540008018401a16550f84c0098800e032000d0680031086d172038400c0d090700d15010704580250f0080f810582030000c4c1d08100c154680041d0b0140c4180320720901d203000041030f14020b80049295034404010001900340641e4142d1400740300d80080c018074108030800400744107050040e4613a858000820580c825412400c8603183c80400303003510410306040550fa47c803144000c0100e0751404048101109500c0c1440c1e4854264070001c040504d80320 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 36162334 1250 36161084 36161087
    0x40b0d0b060f0c01060608060d02030a06020315060a05090a0504050408090f03030d06170d2d18060c03030e03180f030a0c12052406010309050c031002090f0f0105030403 74
    0x50030038005400840c2070080a07014142440039294004440001103a42c60034514010f040c2c46000382a18482c964a400c48405a2800316040c012550000b401503500c1d503440c0304440d40003009003091600320301c002440e62a80c0f41d00101800400000703c640c501d0050751441004180c40054502910b1240c08100b03140007854911030740c8001c0803010341924184402e0241400407204c0941c01a1180c501e20362110640300c50500082c2c094117100d0800500100304240d030b501038040c0309071803001d0511944150507001030040310746180c00c1445510001c425511001c005001980002c0c3c220701007420300084038481c91002c800d0391401a628000200e070360410504010096204003401034050003a074008a0100d901154541c014003900b0420601019581c60020b06d04505a00c075910304000c01a411240954241c0001d50444003d20f0003041203d881e05189040c4210601481d52501c120b07000e103030300f01d1f00c1600540768088044540081c0c410510052150750054a119240000c00800020b000603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 36163584 1250 36162334 36162341
    0x1020708120402180108010204051c0b061509030604210906050a050a09090f0c0f020c030a0213020d05090d020d02030415031805010c080f01060309050a0803150306150102060903040b0d 81
    0x260004142c0d5180313002080d03048042c00d00c00c3c1c0110009940000b014012802c202c2c50401411081030030a5815903600d480303803410f1a0000c1c0245220707692031409a01074420400561b001c5140c0201a564642058500b00030b034403658020486030380d032440700d50384d000038000d00807041103030407030b071612403400764840001c917026444841c14a080c01722107540070403030192510800040e000400c0c1d0015105081e414007a0208140310207030340865000b074121110903180810000f8105905481004121390407810f41300c081e004940d04001040d14080c1004031100001516084103071190b000d441c04071401d810201c1e109d21480c000c404c1501d02c0101c070590f07009e100c2e07400103696440c2c1003040300305903003680d58150950705000c40d03003800520b0040070f000f04d0000316801c6500404113810100102d182d01c0c0e88507921a000d40101801c134820100004a8800d0b03511202c0d410350038002d050b03909030f142442035581c3c0c892015940c2d0b80140325010004800881c004103e0381030724031407a14942092600005400035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 36164834 1250 36163584 36163591
    0x60a02100507092102030c060c0c150f0a03050114100905060307031103010627060c060e19050f06010b0406020615010909050703140a02090f1e09010305100e0102070812 74
    0x1042040c250019080b0448800d004000f02032504d1842035914a0040616060240310100c0c402d8404000443d42443c0000f01c02c4502001914a10100c06510550f241580a840c120920701d40c0c0000c3c81d100c0d21030389039001c80d05807040503482401a900c2e00d414003403e6140040c0130740100e000c1003c140f115191503000345074060368914000c2041d005024054020b070700f007a031084021880a240060b580460385540c0350401c00074278a0071801d145803500051115810781c00140c103044d0750340c03c120a00e1500340402540d001c1d690082802d803041528009966040340c0c4072060640c080c0000200d001403e101c116030455402ea07000380070545034210003440d00c000101200c1d06001508a0010b10b40d10b46020300351280001c1d4a001420b0018401c2c0c4040e1040000c010139401031042180c400940c1d1070b030142d40c4442e1416540e100c2421a01c10555043d07016549401d41d000e605171000000308100050240d4086140c01000c0c00300894104825003070380075080c001450064184021400c1714651200355070b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 36166084 1250 36164834 36164837
    0x2190308060307120311010f0c1e17070e090f06011e0c0b0106080405100b060d1a130c0f020c10080c0909010b04140a0b0304020f010c170315060a02100507 68
    0x1466036407400803440c400d0505a08a0111b000b000074400041020310810403940402c0405100c050b0100500400c0302ca00c41d4480c405000c1041f1910500c42d2141c4041d0000c4004059403030003601300408041c1101045240f071500c60344540d400a65491101a0f08071301a80b4181c44130504403c4034001e07601007410b41c41c500c0e41004a9001040041440b0b0f0300014028140d81d2505401c600382424010b040000f40a50449440c1c181269142261079040880c1e4413000b1110300040d20000050b502c801800d0803a0680358407051119070781c405004941c0c0f010814000a03160800002020322050707031540003403586180c2c00301a41c40200185402110130990243c05040c52900d0011508005244228280c004403018a008601845941103101e01202601c0c1d00f02e41180c00c0501d40031002c0f0701c5200003840240110f89130120310040f80d008640c800315840d440414642c0c050340d64016201160400c40d0135450710240041c064001b030070404115440494658060009144400103007405010040c0c450b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 36167334 1250 36166084 36166093
    0x9030f06061e060307260109090201080106020105041a0604020c060a020a0e1905060304060209091003051209060904090201031e0f0c0302040602100c020c1005040306050f010506070611040e0c03070807021903080603 94
    0x40031900c444400c0d5003c0c00d071440d000270341d80240740001000c100c4140c1015003507a00d000184000f0542c290010a0f0110b241c10b09a2000d80c4c44101041c043e005da41c450002600c035a0b400c0c00340038029a006400f0400c05546c1d00b2111142c55000c11084070007140d4944083c07000e842d0103000504100000303580c803034010540945040c012034041b801070902202c1c1141805070407a0107108002e003e00000d0461070001c08102d04080c5507a0000d0010302c43d90100d076125640d1030034400110790094204038240c2c1c90095900b40c00001c1900840090711a8035030502c08180740c04404103805000340f00b940c00740c40d0300750300910742c620117403070484010f0a0314071140d070039403161a500144039907902c0705c00e03609200310760765071600d5610310b1401a0543d54041e00250b0720025000c018440ca48542041e54601a045040415114091000716940e445150000c5600b00d950008100040381180c001750b00500a035900e40309661b5610900f01d031124420491140c3c40c440d62003c1d0170200784a84a41d42c0c0004005095a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 36168584 1250 36167334 36167387
    0x418020702010e1305060316061710030501110307030c02010606170603150109020711030c0303191106130b0a0c0509040f110703021c050301080703080f09030f06061e060307 76
    0x5913845242900c080c00c1241ca0314100900c0f130074140701c034580c000143d0740054043c6041010103031501c043c1c04052032142216000060100f2074803000e0600450308440200a21102400c200c0050781c01160001d000c07a00f01010300d20706500c144102c4045034460341e00c0b46070b11703849124051032401001e0410795240c41824400c00d003071085000c0143c02050304640c016a41c5c0e82c80d00d0840310701c6d40101c1c9141d109400061000410791404130803110034200541c0c00c07190564030400155a95a80307000118040d1080c50204080402402c103142106402842101c0666580b00c81a00a641070701581800284040c01005200d081030b4002d501c0404030f0800104030071802c89480c801c6038200c00c1d0242e00680c4000e10b01e000b1000c01c441409501d0303800d481e02c5031440d030420203005d42d100d5503440001e040400000b44000254090000d5400e1840c00800f50b40d894414420040d545410655856121360b41c0c1246842e0324884898080702c001101414850460f640c07448140d80200740d100200b414901030030307400c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 36169834 1250 36168584 36168589
    0x1060e01030b030f031b03090a0308030612070305100f0b031f020903250b0a05030f04020109030803190b01030204120f0c12050303040605070804050a020d080c0d020606150418020702010e 82
    0x1813040804210001c6481d03c01d031000141c1180e030390744107a000c140c10401c0420070a071036201e00c52060304c1e0080e6006a0365112140892400e4040031540086401060004020414041545207022800c42c00c107200d081c1032140802d04442c2c010004640c1a03100b406030520312082c9045003400e20b08000d9005003000f01120100341480300318914108004040e042002c14003003103072450341c00792602c400340c03a0506143d400042e0441c80054078115400d5240030001e400c42e881241c03002e02642e40018500e8a905010b0710800d1514600700048408505110b41c0d20090b510a100b41c4088030852000e840000030140c544d0026441c41c9e41081c0c9590340d50200c003054001440d102d0007242481080110365070b181a003000000c884010380b8035410400a10f080c400818400102c2e8104136404442d8245141510701c1c10403490b00c10003451058600801c0343ca01012a008600148241c2003500e14480403c01403860f40071502c00c038007410608001c00603034180d5046166014104c400c0c0b040c14580c440c0d0004800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 36171084 1250 36169834 36169843
    0x20f0406090c0e18010e010b1312050c030d140702040911040203040318060513090e0109021207060314010b031602010b03010f0605010f03052403010b041b14040305030301060e01030b03 81
    0x8180003c5444401000f609080000c01c4040c50b0031804440c01940d4107100c0410038500e4107202e40301c02004045030382601d040d0b240c05800e0080460351482245034a041c600301e03403903071001c6200310301c640141000c0200282c0900c6200e010342584903c3c0034600f2045a023084010b020f41030b0281c911000c00d28805550f07440e180300544c0520b000b5102c002c9200f40658007141c21201c41e8002d0420054107200c1401520041501201903404080010518200705070019004000c42c2034042d40c0100070b802d4991031050003090710f4040ea0000d0ba0103001d58940001102500384081c802c0e109444000c00c0020041c0800c111043d20441240c40042800e00f0514002404e44403514061500309a440000304210342c0c0001040681c002035040520040c540803d0660340012038042c9030035a10107404408134903603829400380030108802082000003600345090b285d031000d040c01e041408100700e0581c0b817040182d010182c800700ca510100a6185a0808404443ca22807910391141850b44074040f6420a690910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 36172334 1250 36171084 36171101
    0xc051501030327150e030a0611031005030102041802071e06021206101710030206070b01030201091d0403030b06040803030414100605090a050c0c0604030203030603060709060804020f040609 83
    0x2915103403551600b082010f800380c0c0c18081e80d1016115680d0400c01040d0006051801d00382d6400e02030f0034114600b01181c241503443e4001000b071490b18051310183c0080c1c80180d4043d10a0f60f143c28803045d02c41e002e16080f8420303030060b040300e05e002161032100641750340c0062205c1c0388525150f47e10071f4403548076488003c080702c0d004c49000d41c000c03038184240d1403090070035035210404a80c1c08860b20115580903041551003c846804400d81d03100040c092405000306000444e400b90925a8500c05030403c00c01a403000e00049000a480100c0040c000e4410001c0480854015442003115103840d5800c0c0d00801030b100301503070051824000003c901c0c038240091407040340200080105174070102c50040c1020381074940c0c10000d9150980c240101d46520849030b6101e1b5131030b84005400d44071003031001d402d170040032801000d601c100c008010405501001540c040c840603001c84110740c44050040e111810035009400000304031400103805072400d91600c203020b500c05000040e41546038952602921900b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 36173584 1250 36172334 36172337
    0x1060e0f0702010b0a0302180a020405030d031a030a0b01090b0f060c0c01030605010816030216050a05100c1b0807020d0615030201080c03010f0b0c01020910080a05130201020d0c0515010303 83
    0x3804000d01c00d50203004a8204020840d800200d8500350741c0002d61240740d141d61020181000400204c1946550f811100600310003000c5034149580c005004019007030044004082c02102e0180c40c03171600700080c1411030b0079444220f07010a42c0c00c00183d400100601002c15034402e450011590060300c80714014181c40c01c141002d0024002840009402c0e14601d900036410010350404219502c110a00201c19010f032a140140c0d0b00c5180d142c90801c420790141021741640110f494002c200200019404d00410039540300780b18001c445181502c00c460111101403112081825010001e05a400100b40300e52000b040240026040c0c0c445100f107501d0300c008421411800c248c2482550317004000325500604160420785158180183d5010316141ea1060010340003010801d444580400e405541030240c1c083e15005e51001c140c40010031003c010b49000d10300916041c08192004400e200c00e84441d41c043e0020300781341440510458080321000801e55460066031100c0c060f01c0b08440702c0b00e0085000b0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 36174834 1250 36173584 36173611
    0x1a070b01060e040c0804030203180301090212150a0c090b03070314090d030e0303040c120c0305030a0302030a0e0f0c060a0c1b06030b03060702060c0a0c060e010f0b01050c120c01060e 80
    0x140c0148802c8507140792130340e03091007042030400c00007903800030071a8203c031400008c00494050300c0b40400e000d4181c01500960012030703101c900500890002cbc202c40d014134000580e96198550034104400c035404818281c00140640800307005140e03d0600458002d109460001031a07025251400d1404806685809442d00600c1d2000030790799040c02410346000c40c0b00091807560405640300d07059100d6a00ca0810031424038003c9105100014882a00454010040e60f944988110000340258400c950402c61a85030456a0b082d003800040c02080d0082c000e0014180c1503100c100f08409900244205400c0058900c0d80034001141045401c0489010042111825003044006810364102820080c000d5112004102055600042c0765802001044103a5510820010100c0303546210300800703880d0504140ca50b00900f4015488042c400e0240d01080081c000b02c9401100d5a02c11084040e0950380403070300c211a9403008000901c1d0f207003504e200000341c540c1d0300d07240c11010311003c80354480c13003824 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 36176084 1250 36174834 36174857
    0x1090f0201030605191503021207050403050111121b1306020102030105090109050c041202061611010e0a08100e0114130606050d03170a27140106080303011a070b0106 73
    0x2054003841003d010205c41da06000e0403020141c42c1c1d850340500c80e00400346030200300588001d0080c0d044031a0660100e411044c40d15028102800c07a9206200456456180441503440041c0700c0042d40d801004100c41700d8242d441c0c03003080088035130310031005404c0120f0410100c00103000c0c200f0020014400c540016807a03600d8201007001066050b4000001702e41808100800310700710712304542c01d86440c070440001e108040d001042140c020b025050031502c8001143c803040c03140211000759826000d90307801040d17811749010700c0341159040c856460164420400070707040300216000342c081d0070f0f0f00000010b150703400803d0754611103406442c515800d904500d80401400b2003402000c0181c80c0a5503c038500000c40d55000342500c1450044650504001000c02c40c5541260400111090103a0480040c800c02e8410708814508244013101c0c0d44c0c01c902c035031041c08034060203081d0807144031038041c1d41180e2070000305203000c041c1340c1b004c2ca20b2080100000c0340020408203141d03010341550754440c0210003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 36177334 1250 36176084 36176087
    0x30b010e12071e080c01050a0e13060305010c02010c02100b0f030307080a02061302060d020304080d050709090f05012d0810050105040b0612040206160203060406230106090b0307050c01090f0201 85
    0x1480249803603c3e100c030101c001d2001c903d000420044091080c80d140383d481c501d0b510122850810206180d45c401c04c20b4485100a9645130840c2c01640d00135030080040d01146d407030580c221002c0b0503121015030061400c031055400c0590004490000180c900c24040c08050b0001c1d0035540728500c00c450406010660001440e41000b6a592008401c1e410070700b5132000d500096403d00401600e2420190000000360400c11804281c03489559804401c0c44542050f1a014104403014003a00010600d0260f080c4c0c0b4030b0145014040c102c80d0311400d2842980d41c000661030081c581c809400c036080820020010301d0002c104181090792402c000c001440d03506181c03c00c4242c0d541c0307401c1513100e0607044c0051840411583c10460708140c6c100c13500c540e00c0d00c403400c1c445500007002d14040d51500a0780c0800003809200c0d04910f41784501418018107540c4900f0300c07403460580a009290000e94100000d0104080410003580c2201c4039040007030924004214060030741e00c50000031140c40f410720540000f1075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 36178584 1250 36177334 36177359
    0x13030308070804080301090c0c0503070302010603050c0103060b0702091302090709050307060807051909050a121b0806041205040e1315052e0302030102040e01170a0206030403030b010e1207 83
    0x48007a10340518a41056121401c04d4003060003452086591018280000c0b4011158040016803090659840b074405080c007070b00038803003071105960314060740ca0000711561281c4200c07421344030040800e0b82002419000e00200c1c5070014005507580014540c3c09000da562482c01034451200b1b42d4a0a030890b051009050511030b065000005000c01d60b03003800400ca400209950103009a00105000c0d003250309011a524807003035204039009a44a24007051b402e240d810a0210036020314003080c0c0700704094408219038021403184030013942044001c580007880708500340e540305040d0b28240741131685942e85400420001d1341c1c08000329a009241d44104410481403044d10410f03814104004e146c40c144610f404ca00648050f0741d074078071000317a400001d042030040300081c41c1c001c0c0003103460300c1e2500e00341d8503c15000c1c000c102c407200303107151001d8052000040e4070545603409010141035480d9940d0507401391801c3c0d5091030610002c040401d00f15210034401d4050014980e004040c0103103041c0c10450032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 36179834 1250 36178584 36178591
    0x91008010b0102010209060901180f0f080106080706091217040b03010303080603161215060e04020a0e0103080915070506040303050717060a0501050c031903020a03050105030a031e031113030308 85
    0x10344e4014000c2c412540e6a900590354810b0082c20040076001c2800780c8a620b440c16034000f003440700800031000c00c502e840400d03168242c840b01d00080010640390400155200c0c0d0922581c000100e103000140300012444d0000340045100d00c0f801c001c641121245d018444c3c116030481d226600002c0010014560f001d07525540194040c1c0107042c00044064401340108068090011251010340d2a14108940502c0c1700100240c9088104407d580b00e030020300900009441c1a4460030f8032050200300000400125812a58820740043c6414000c105119031001c04080c002d400340700510084020403010300c10305224610903030300007070315240220340038100301c00c0b070301240c1e00240c0d4072410400540c48035450312050714000d08103140c4507614110070a10f54031620340d07007800b40561011040039458058004e01412801074406011a81c2c94200303140d03840001410240c006248514414101001102d2141d00c0d07400500e03010500b00b850700b0742c03000070b9400850360310403040000c04100149a030003030440d41c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36181084 1250 36179834 36179837
    0x90b07092301030c12090f11060c03030105100c0501022b020705030304020405060402070f032105060306070f0203090316030512040e150a12030201051b1c020d0209091008010b01 78
    0x4207481c04032000352481c440101c80741e052554910720507841d0f6018049484030481d1181c010321100b0402d180c02c2e140001d4403a02180c0c0343c4d00f41c0c03400034103500d0706005031001300001c81d004500b5a80b800d410820801c3c030500084080c0310000b4184c40c0850000e000901c9800303401f1030b051400c2c445010300540e00c0b2034035590070382541744103100410009001004682d007084c0c0450b0081050b03240c0600080003803148040003041580c00102000c01c0503040034182c40f01c800381c079503042100d280c0d001002d01912404c5030700350780c59040140028280c0380283c00b8104031151a00c1101d00b009071020200303180c401c5884c0034040840c00c1c00b00410400c03500308021400240002c40c1c15062515040c1090070180000c1c5c038881c400318401c91101c0c440d8032004010001000a00c0000040c69140d041c040c1c028202580c0980030704000300440e00740b04500070200c8184058660350311400c0504400218001e42090405a240a03000c102c420690350700c1800c0175020364145039000f11400d02d006400c070300310b40d04000c600b030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36182334 1250 36181084 36181109
    0x80703200f0714060c0d020618150708100306060609090f1104120f0c09020d0c11030a051b0607110f070b03010513020706051008070b1e0f0409090b0709 67
    0xc080c071010480740d0481d00581c01103036000c0d0304030001a20600503401528154450681c0c00c603407140d80062614000c5072000141910380f0b5072415029142c5802c41404031007422020f0224400c0c82c401c400c1254400e000c801010301c502d0f120387e1a034003034841035840103001070a00754042c041c044113840785034681c00f1101000c01048031000e40c0440f0600944c8145602108d01c102d5003000c0c03004d58607061f2150755216081c000e1090312041c0c00700c02034000034540031600d071502407028544c4d0f01460346030451f05038003002141440c0000000704d600e98840c0701800701c94500c0d0344000420a50400002d406240d0700c3d21040d440252804a052604051000e80c044a5200c1c06080002c003000360222415100155094a601100213011a000e0700c00d8000092400707140808014002410002c05000c0d250784105590795a940c03600580e41700d000b0001001d440300510300d03610301c80f070b240b9000a0410104070070649003001d903100c09541c00c039810709009a5a000030300342005840c0341e01200b01c0020f400341304c0001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36183584 1250 36182334 36182353
    0x4122d09120b07050715090b0708010503010c090504020a260901050919020103020d090f0606030c141513210605010e01080c010806240405040506010f0804061808070320 74
    0x141020b081c050302c08418843c0000f00c0d0004c0c0800900c51400c074092542c401c1c00121510320f0407414101e000c47d06040011980b4002180038039060040d042d094580766070f80103540e42002e00700402540b00c0e500038028000c03954000000804641000924074200c0740043d5003524040c10340c642500d0000b0b210749a0344c0c20081a1180e20120a00c0c414800303602840c0058842e000b00e080c1e43c00520045070b014020f26280c2400d0410420540c001c0c0c01501d20495911012590351400000082d03014180725078000842c8414034914550a0054407680c3e044c0103940c80c4056032000032602123984940e20440c0c224080542e0340901015005030b900400e80c00700542c503198501106c441d02c4e030f00e48469080c10020301002290f81540d64050a42c2e0a00c0c00955070b0020300400c0c0f00c0310003283c0c814450b4500a0f410940021013070b6000700910900d00542d034807851426602e5aa6040013049100c0c5c4940c0e00740400c00313150010541130406000c0880c072a031201443c5541002201440e5056890a40895408180d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36184834 1250 36183584 36183593
    0x203070807050715060e0402010207170307020f04060504022a0a11010f02070801050709060905030304060c0b07020f060406060303110601030c141302070f02010801140904122d0912 79
    0x4007640440d003440d040703868505038544642e070314004d200c0c0c2d8000541031000c045140c0c90700d41c4520f4002d034406d80031985003555035011030307146000e88003481c1c486803c180078072009802c0004618642900c020400140c1d00d8503140060100c1e0031000c54880c5e0340030300f051007414911103192441d011448000003040c03500e14130394a0258034809000c045e07040142d0a900c0d4a0020700800408020b007000c50000e11091034005c00041403110305109010001c3c582c400005481d0402004840655030300d599050040c04840e01c42d0b04100a0203003101c07085100d01003083d400c058062209901070fa100d4400400c0d46465800c0c001d00080101c1d080c00070781d810480041000411004803d001c4404945a503105070030000d0001d0b41c0d041d01c00c4038001c00d2500010300c100805c4818003c0000c598401d03202c0403e5642ca800340100b0214005200300d0700840c0020105003c200c01000b54004c0c1d80c005d103042c62001045a040b5542582001d00c00031959500c00c520340511500100c2040c0a49180900884040c05940700c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36186084 1250 36184834 36184847
    0x120807120b0f040e010b090f090d031505150403060c031a0f0d0209090a1b030b0c0304030905060304020628020105010b0a0207140a0302030d0e01140c1b0f040f050613020307 76
    0x284511407555400700407505242900305c1510b46c100109645843d00d80750b42900043e880440d01020f4030300615034109520740c002c1c410303403030031000a0380240c0d40182800d0030720181c0412501e25401d482001c3c00f001000808500031043d400b405990013140c441080011882c00d15003960105125851206480c141600d54402858410780c04403284251500c4602c00c1d18104800d1000c003501d034491003152035203030104904000040320710801403040155100d0550f49420700003510024002400d8201c02c2203686403810285170441d00051155240c8480d4140300e202d0f24000140807925508503141c0c0c01c01070754080c0b02d124010f202481e00185801a050f00003516107005000320300c2518822103204081c0d03152412450040c560140c00c407410403808203400381000c0c07440401280000e08146800c3c90b1881800159003203002d84500a03d2004044103843c0102c40351400c1c45500079144829000c090340c0c940c0658448003009260000d61820040c013807045060a1005265490b8010030034004481d51000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36187334 1250 36186084 36186109
    0x140c0304050f0601080706031b1b0c050a06020105160e0a270f0b09090102030c0904020f0c0f0307061503030804030f02010b060a0c06050c25030203071506061211030109020c030403120807120b 84
    0x380542c8040d4070b9807900300c09030bc0054010300c3e00000704d22004100b441c1c0550042e40134582141d50703044e00c9a2040c0c0d00300c40304c1c14a962059049441c1d50780800018420f440d030002d0002221042048034802c41500c582200c0100e003011400d140c45801407041410007000c942e41001c001e0300254035602d000241c41d030091140d040c685010740d42c0020380d4080711050b801a2100852507500b502c9500001d84100d580d01c1d04040401ea0340c062400c004d8412120070844910304480c0e154846980c0b40d80c80b81c03015501815101d8820013555214001c070300c00c0d03940d05e40080c00d40e40119140c420390240c0302e0030901d080380d0000700502d5101c14100600c04800440e5508510341d5291001e0740510301040c0d160403400e5000308180200001c2410f40d22448566184d00a002074400b203a0750452900c040c0f201a509031450080000c00101d41000148851100703a0024a8003244180c1180d29086d42d0356240c0000780c4001c4c0300440003940410074008107603805080002d51000081081c880703034202c000042c4d628041782 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36188584 1250 36187334 36187367
    0x80d0e19081b1201090309080d02010501050f01030e010e0a0c080d0c02132301031511090916050903070b03010801110a020c100e04020c0a1203140c0304050f0601080706031b 76
    0x7a040c40d0b01c5640c1c0d8420b0b40c0104400000a101041003458050b0000c29940603402c0c540c011121021416032052144604840d03005000079014140c01c4010740042c001744440d01c0b0155210301c1c4245828408110046185100b11014203180386000d0440d82446d6020990030200000354041201594449600114500380e030301000a01102c4030803800403c80c201409004140ca0400c000802d020f03003e802004048440035007802450703a130405006032841081000c0d540040840082a40d0000350842203446100740d046c91031801c0d51a2000070301c0c0c003c1603400400056030000051140580a004034220740d40c00c019041d0401c0c2e030744400a901c400c2c0e10100b8900400c000c12004d502d80e0f02ca4044423862400141c42103685045000c0b00c00d4481c40310380020b0380c0e000789400c401e0108510a201e00400383d0f112544030440ca484040502c1c1040d03201410590302c910031080c0656054505012080c001c14945000b00340d614602079010f010b0b5040290088991a420000080d25540120b94808806003d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36189834 1250 36188584 36188623
    0x908040308030c040512010b04050a050118050c16050c040b0d050a03080c0d090b070905090c070807050a020405012c10060804020111160504290105070c080d0e1908 72
    0x180449607080c1e0080342e1291b079012951804800c4880c0066105602c0100c0581703051040355034441402043d90030038803c010038091100145e01c502e400729445160881080d000482c60302d0794540d00300d4400100102e081c0c9054001000070140d40c9018030925103c808292521112098035807030303594680301500b0000c0d090000c88400250080360880464800034503a1104210100741414401d21800e411600d0701e010495104001c80c151600d20002440743c80c403490800d1419500d60f8403200150070040e0b04450ba44a9003808000590b5140a04c0f406440007030345d03440c402ca02d000000384600e580c2000441d0343c40910b04c280171071058150851003c2c0c0d03502d820500f100303891741c1c0300480c3d0346805414021040c0c001e4040c2501c400c00125200000c0704c004860500a401800002d88054449500d0011030090198211545940240301620250340900003804070b0a9a42d280c072401d1548044113203000500c0382c204510725141c08095520b4003001294440621400c0420040d82e80140b02d401c0384100c81c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36191084 1250 36189834 36189841
    0x8101a032805150103060204031101020708190c0e01080c03061e01030605060303070501090602030109060512070e10170303010302011b02090403110f071806050913060b06072003060a090804030803 86
    0x40042c00d80f0421103581850080d039403400c0000080d04680400c80f141c81030941c2d00c0c200e5620010300e4805940582010f4400150550600c0c5150300454074129001c1080b803030f0020321440011403190003001e88102071f00704d11780100105400e00500030070100d5920441060130f046d09004070043c3d81500d500a20002d2292034080c00245503000e4403030000c0880d0300b4401080304101960b00038504070741c1714010900c103c40d1254104130540040d094000d42d139602510742081000c030009001e9070011100c00342e00e1281912110381076400e085c1880303000a16440007004104550340260082c00c0554058040c41701c1c100d150b400500503c0300070b00040d00304040c242c41d5102144042c00406101e001c41c804903400c540e5540403442c2000b568510880c0024070b003503000600c9040c20a00c05100d50503201094000d14165600c0b100144502c02c0c07082e400c00700a20041c800200c04144440ca00d2030814021100000c4c680105490204001c164002e05410111141c002540c034006450a41768000c880356240d64 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36192334 1250 36191084 36191093
    0xc050301030b0c1b0613030e01021207060203060d020a09050105031002040803090d11030106030b040c0e04030f030203040c050901090203061207060203070311161503060b0a0813020a08101a0328 85
    0x2c0181e40401e01401820240000e051303a1035503414410741f00b61111448078055500584c3c885d9980070072500005001c01203600003030410740c011540004c004000c01c004561540114a00c07404c16000b1f004041e030786e00014031552504008100040d00342e0b120a500d00340c1081007940d00c90140301c401d2401101c103941d441c0204030034101052655500900208001c1d070b40ca080051004200307a40541e40302883d40f00201c2c0380d000d0306040c14843c07a01925518000320180b45c045000754401041600e07070f10350103500460346681e0118032a0080910420161b16810500704100710b03403519844401d165070202104100c0642c000c0180c0d9082605401c080741500700c01e036451410035514140c04644070f100071398040b420300c01e0410141607400f004e42c0e00300a415140d10100b50244103600c8980c0101e8420700008000f6a2550032030035000344007030010f1507066580d00b00c03a413030441c1e1880f980c05265102c2021002401c40c01070600f00a1004900038030000783e51802d40142c1342150b00c00e140703070713800000e50860034407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36193584 1250 36192334 36192367
    0x60f0a0c021e010e09090703030c03050405040516030506010c11010302070809130504051006080a0803091c0f0e04060f03080906040e010e0f070f02060c0a0210021306030c050301030b0c 81
    0x54000e0300d60500d0328074103100300c2d004400c81600300d401320350380600000f10350405800171445803e080f80148003103400c2d92002d0798070510820080701004000c02002c500b5844501482d80a507103002c000c0b4407018042400a0181d480c020302081c100f0402901c1803000c61481150b08151714420308005130b07a16001c0c01d0130f04041c4103034130045030080d118085d200003a52146d80003074460750240302640d4440740710a00d0320041d078000703115001c0c0a9104142d4034001c40d4100c0c0007590402c0a2030102e90300e409039008100c8a084072202074002140d10264500d409a0700014020001142150100841070503c11200d80c0d04e562800b0241c9148000700e40c03840c554841c04200c4006c0c010003a5600001d603921603258007000f80803615002c5203c280e502049503107004081484003401140c02410069507103d1895106400903130805086205032110500141c12074030040000080004003610240d09220300a01030301e034010110320400c203081004001241180e041a038100003001481d50340c0d09042007205501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36194834 1250 36193584 36193607
    0x506040b040218030606060310030201030f1803030903080a020c030d0c050702030a0f0201120b0603040f060213120b0108061306020708040504050a051005030f0a030e120a03050d0b060702060f0a 85
    0x24400a0345090514030b414041000344804c5040f640250344400506c0701713500050b83e0070445d072904c5180602c0198060303004021080c9c44d0700c0000402102c480c080300c1d114481c1c0c00050700800e582d40598000e0640c4000b0603a17004640f00c405600e000650301c0901d503280b00303588164a00701d84e51303040301400030702c2407084404007138008044944410700d50070041802201450304a0101d01c0716101c01c0e800007150301034800340b10401000d050130759686443e51032024091440840f41c9640c00c04c000c110320064002ca0390040d00c0481e4212541580a1030a482c09500680180f0160350209081020380712142c100080318941c0040c01503103d0481d4030b401541c501441e000a81d102d42003100304071510180f540500d200b45c1211841c0702c0210341d03035414951650409610410503030441c1640e5000309006040022a400024000c640798407440071405080c10510482200000e500140050000d0131b0742c02000a07101c4100e602902d000e10303a40c00103c240c4900ca0b91180b1651011404890803400344115030003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36196084 1250 36194834 36194839
    0x304030611090a03081201091a06070213020f0901020f010e0601180204090f0b0319020108180304031a06010206100b1c14011412031c02130b0a080f0601051306030506040b 75
    0x10f000d03100c0c60100801d4201003c103d0061744030200000b0040390601900000e0302c089589030700104510070074046541c1c0440d83c02da0700240145204012011584010b003c424128402d0a480d007800400080c1008811504180d02d45c0c1880c1030030342102008182141101c0c1c40a00082e040c1c602c1301e20000181c000e0b58000d04d100d40ca4056444900e40481e00052000c1e04114162100304000341002491030900f904003a00003010440050040c05981381d05a04a99595003144d040039600c0c2e841d01e840c1d89100040b103890ba01050144501943c0400c007143d041040740703140705803550810b260303e1703514044c10386100a80070003c0c0c00d0480c0f00c0000d50003409880d03800b44800d0703c80d6849003231451414100210145c0210308640c04e5084070f117401b000740c42e01c031114000b07510358075182c80d05140007035002214451074502e00900b0014007000b00350000c1000100039284e040151502d10040c02207004014001da05204040100000d01c03550303105c601e001d03205030b402c00185c217440f20030100b00140012003c854 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36197334 1250 36196084 36196099
    0xb0610140d050403080c120601110f0f010207060b091506090a031b0302090714040b090312030708010f050f06031602010612030203181c03080613090f05060c0a02030403061109 77
    0x25000c81c0d002248518060303241e50709541c90740070078120180301b00081f0282a81d03e00001c9000d540c0b1031080001c00078032860450b032080510403061414184900c01c100150b03940051741f00d0401c5004d0140403404402141d496109140600300e22001215021030548144c00c00070302c8114030354504a4a1006c0d68105801d02c41400240100c01220301039400181d120380701d41d20014488038130074202e041d103010140f0003480c1000d14206150305603401240c050359240c003a2a884003100602003001c0c6100d22906e9032038402c6540b420701000000030302608440e002c2c3e017511810003c1501c40008607504202e001410b0803e0f02c941c07520890050419400c10142000011aa001850b41c00400303032550714108407005010f40c503040c081200c2a01410902c0441e00000140f80007c13038012812564000c901414100c2a07074002501c0e1001ca414280044510307007400f1800c1414480200002640000e07440032044c0f03400035140011f03549000354800109480c1c0c0300c1c14520442800c5005980d8085406484007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36198584 1250 36197334 36197347
    0xc1202130c0c21020a0b04050f0d02060a140f1302040b040c02010e0c0901120b0702030909010f0303020d0201050708060f010507050303040b061008010303090303110115030501061a04030b061014 85
    0x1040442c0540d000e440310425100c00b09802c07050240c200d0b184504580007840000204c0d41ca044500ca8024070549090080c3c100c0369841031014030a10300c0101d040c0d4094201d505d026081001200d1744003c032603041501d0340b002c00001c152403c2c8000c1d000f10448050000740d100c14400980580400014103401a041c0140c40f412039805400098040146100b41c540d02709600080c070031200d00910484000da1203d1007130b0b001203925864410b4100c07c00b40305591400c1c206d0380229400c15400c1c0c1c45071030301050680c1d0410074941d05104521261407184001c0c0580d0800b440000d081c50350180403540f1403ea2140a6019a80140d040700c141e954440d0a80791286000c1c20b10400c0544120f6845015038604400781403d18840c01ca41c078181e0b0fa05440f1504003d041d078a048448209000c1c0e40c0300c01d0365950f0300c40b03004443d07034200043c003c40c0f04000206285040810310550302d60b03d11060222400d0502040c4002603440b680c5a910050036155a0410213051134100c800c0940780751405c1c141c00c40001c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36199834 1250 36198584 36198587
    0xd02101a03010906020301140409020603040803130c060806011103030906040201110709060e04020f0d0b220506040506090d0311040e040f1713230904080d060b090a060504030c1202130c 81
    0x29604a4030240c01030521355848c0700a200c2680e48000c0700039403107481000003078001104980510381000c808149048a080e55030b45118104009804c0000801c2040701041700c00d680c003000b00b186004020014500390704040b82d5513660740e10040e10084c14001da0078450029031108001141c010014404d040c4106a96511310084008003034038140d009819070b0503418410304220140c110801c0d80011040c1c010b0796101c5645100302050343c0340000342104180100c002c65803c012250083e40280040c2c40242480340009180030155071001c4249410840304e140f401e003080c0107840444859074024603440c0d495250001552140c0d040080969100ca80311007a00d501c0480980344003420700829144154031100c4401d4894605070354031a283d0910a459905402c00d440f0183d082407040c450641003402c080e140b82d041e147d090308078800903d40032a0001f0301c0d142001e800070003090141800b40c6420b01b141c0303411040d500c0d00d01170060000104c039403c40840d02c80d050046491481300d80200300c2c44046240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36201084 1250 36199834 36199837
    0x1005130605041a0c060a0b130c0509010201060e060a0302060f0c0307080d06050402040308072012100b0901080d1809060e04030305060f0901090b061306020606120d02101a0301090602 80
    0x3980c0007043e14005101000900d01c00b00c0d101d05140b20000e0016a582e1401c000203030524400554000305040c1c1c84613103c05450040c2026001641c441c99260131a171000242101d0b182d500c284035030319545d400d10a45840340380f1004156074041d10440e80e601c01c1e540d100c0344944200300700d100b018800001c495050000010181600e074000343d505100d090f80d19000c00003640254040075058400030480100015007600800c0c141940805d40341d0580103c8000052c100c04400c401030819800041e120409040644180d84404508aa240c1d00d5941020319041d503d217500d419207824080c40c1e2806d9508180c2c0707a040d00c0f0040103290b0083c420182c5951211b0340c0d544081c1c508901007401c1c500440e0b0145003820b50b900c404500508289482c1c0c0c070b020705100c00b0341aa10481608580c003001095144251492100058260ba0b0004c02841c2820720500800c061600d4081d0704980080e524050b445a010032900285100f111f400300da0701d2280d0302e5248101144100140c0d156207080ca8143c00c0040b940c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36202334 1250 36201084 36201089
    0xd08070b010905190c0e030d050c101b030b0307170304061106040f031809060b13061407030f0e030307030905031b030312070903020607031106150f100513060504 71
    0x2586903a80d994841c0c0340240d881c1550407551049246940d80d49800080d400760460210510300390f00600f04040200707041400004107c0c000600008140c2c1040d135041058101003070300d1403000c0004101c2d03207903c0c003820b04040c0c500038200340d00ea03400780070582c1c0c003002080068090301c1d019505103d541d84155550340e210313203c1c050220303803006140c0d98003c50200341c032485903800101303042c00401640e03011a40819a02c241000b100141c200100d41401c1702e1140d2070242540014483d918440c451404000700825885001004001010150700941c50745c195600030f03505081000003903c1c500810b85401d864036a079581c00d0f00c0007040e0030080c554405646002c540e81542910252000b003841d080c00d1a4042d000c02e6059031041240d104207000e40703415140d200c601442c0c4801c11984a6001400d0303540600402c2d40060341400420201c9030090011a410141800d046600340c1220404030300c0130a6050107941c4034030508100c1c1685640a1412282580b0003c4514050036843d80c0014003d0780290 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36203584 1250 36202334 36202343
    0x402160803070509010219080a080a021606090b0a0225020102100509010c030608030a1d042018010801030b0103020607021503090706020c0301061412030f0f030106080a050c0a1103090d0807 83
    0x41d00c07900c1055903003416540c0d5081c1c122181030310301403042728240c80c100d1000d00070200c0ba65081100912050100c640c40303144a00c20310020480201d242059100c00002406544499204100e00c136180d002030020070300540d886104101c9000c0386400180d040c40c0c101130b84007411a041c40100080680103500c041c44420a80c1c074200070854581c5031641c1d40340203444843c0041000d10032407480c0c090441050b0301c03200000600128454020443e181590303080c2c2500d405142201140d030b43c806c0201420f04607013a010a29109502c0c0d85580c9440ba4001810b1201070301818001403218155180c034081c02d60b00e44a0744582315900d043c0b80610369a01c0070148500300042c000c0c0c020b0002d0074507042c000c030403c0305c099541464150318440e0820154a68840840301180300c1000300104020222005c1d007141c038031802d881900c0f50302d4038101030903140b401000740942c42d00d400b080001107aa42015214000744501c1d20700203000f00800350a10307510554810503030207801c6812040400114030018446103108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36204834 1250 36203584 36203593
    0x6040c030902010f231b0601080d120b012606030f0c1809030408010f1b020a0c0e1003061104170703050604080906190306030c060f050904021608030705090102 70
    0x112041101251050038000b0300140c200c0c030200c2c030350701c1c407034000d1007140400c0803040e41c1004010a49011154420500712540646001c19025440d03428454a03005101400217008120a00fa2005101400d180a01522103680b100c8004e041c0e40701d804500c80c520210249428002410000c0a00d482011501140310307110b1031000401144000c03424481e9074501904445034440c00c082c41d9001c045006200750001e200030320001a80790024020b000c00303049840e000003072000d11200c08034001882c105d40c807800d5611180b590000202100b115500b1248122074020451700c03010800040c0c4552680050441c509180720341d604018590001d00454011591924481900c00c1c0103684034002c40c4400b6000d40c10200004010500c0b0360018071050b0340003450b0f2840e1482001800f43c0d145811500f21000070b6440d1418003c0240f02e000b5000a0030260916040b080c81c4100008c14900ca03164a0740c1c011038010070b03061040005075480c8031783c039980070324072603224500742100400d260041d44509006124 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36206084 1250 36204834 36204851
    0x106060201060e0a1a090a0501030219060f0f0201020d0606080108010c0e10140708030a0903080601032c0c03120d050c0405010903030c0201090305190312020c031909030f0602030604 80
    0x51141c00100d0701100920743c3c81d561100c249000801100700c0c1c03c443e000035117140740d03165941c0c0704696200d50107003100020303103506500520034a40004800c0c03000300600ea06081c8811900000c122241410074541b40e210f00420325022406405500040340e2402c1c1005400300e1031642003401a4107039031804000b0403000182c120103c1e8181003803018503420480c2168001609485015012400150075020703038030300130040d0780c2c6503149d610480d8130824140e070b0352000e40101640300c44500c0e00400d091900f0301080c003c0d041483c0009000c00101480d071616040708400040051201035004000142691070001800300c500c1295401045403074035040c40c103400540f00c492000300703a50540710103a5a85d40b4a6045a605403178007001440c0c01d03814020f0440000002510401a18000108002401c14808024078002c0d02401011002c031150a00611040388108000000c2d54081107201d0042d146c1c0300e47c4072805031111035803604058010800440c4000900465800850159034144c4003009040f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36207334 1250 36206084 36206087
    0x1090215120c1e0a0201060f031a060d0b07030b0a0503070602071a040e01350c100c021c032001050709060305040c0504150b03040b0402030c030609100906110a11010606 74
    0x101e42e03046042c40043c4a04509001c05080020340000715050000168480e1a1003140c00026500e42c4110755044582503028404003404820540105c0c1c103641d26450f134080380e0340c0c03407505200091100f8100360b591254000641d0fa8009030710700400c400f4050380d0301191900300c02520b801e824010315001c2d000d4141522603c040c1c200445040f44d080410314240c50342020306d0207010203d41d9081a030b03180c003950800b001415801c060000030300f0f150402010582d0011003804000350704e140390b20007031050070540100941c030307412801c0703113660150b011f10714029a041c94142c40401c180a403018050145000141110f070301540958001c0f42562250139490303940340c608505440d030403075008040c2400300c00100310720308007900032048401140d100d0307089864840d10042c419400403a401d807800c0c0b1800b4140f0096003000c3c0006000f550041d07010341010720388100e8103603481b00080c2e003e031a40d640d910103c000740402079000d280c0110403508200d41e601c04402c0c0040c940072040c6a4040c080d443c1500008859 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36208584 1250 36207334 36207337
    0x305060906070804110f100e0102060a020403020f090603030c03070f05060c032203051e27090103030e03010b0a0803070606060f020d03020f090a0e1b04052101090215120c 75
    0x1018103030f035901d2080d625591242e9868141c100401e0b003080e001c5e121032800c1e035140c441c08040c1b00116900c202c0d0580c4e076440024075042000c0c20411050340704000c1403025031aa414218003180c4240e03500c6103207858660200b0315611500003420300713501010524108200540011b100d16500440440d0444e885d0b1f0704a20015200a4442c2c020b5054081d003180d007049040b00c3c140d02280c0c020f0900c5070908105840010a407038040e00c00d4412150009a80e107410740b140684002041c0c0030880c1e00341803803216404900c0300701060002038180070a14103000e00b40d030f03000d4011402049000c0c0000c0d01e12691840c4603a601d07004100700703d80300340c01c00c00c000c14124400c18004400c0c4070300d030b0f0040014918040c0c056000b54010fa21001c00e111040050302055116510710384020724207002c1e980740d24078159410329401000000701c2c80901e1030801c0308000c2c681d10101902420704d0001034202000800c200414018459003000035000380c800440920800f00c014042d00c0000c0341d080152445594440c44036015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36209834 1250 36208584 36208591
    0xd020d0807050d0e0102010203070f110f030c03040f09020a02030a1b0f0c05040c0c0c0b070201021e0d090e10090506060c0109110a05040e0604080c100207050102071a070801090b150c070305060906 86
    0x90244a0140c00c01445075401c0e212002c05030cc21303280400c414007115411644404a03c441079480064200101c5007403d200030001c040c80caa04604041c18000000d40b684120695a0208443d8081507a01a10f07181220b4016a50003070440f03661400920b000d1051600e0740c4240343c03180d80381102c0c4140c11360007034005464855220f45c071011b8041c28120a10f0300b81c3c1000e14181d04501c0784074207801c05131907103425580302010020001c01c284403603030200078282183e0390018640c202d0600c0070b006600000d0640c1c1416100c00f000b010034140c2d41c540129105000c0c113048080300d503003401101420701140c96041c14800714140d80410302d2603103400612056415070102ca48080d444400002d0103c0c1d4001c2c05003000c00318ac20161660140500c10120580e007010300152180e0350b0014801040090310f000303109001040c2c0740030240c41d1400c481301510401c014480c401100d91107290041c034584d28044e1702407110949100c12501d880c031441e0308982d1507a890004980520034140880c080100000e040b512 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36211084 1250 36209834 36209837
    0x80105190b0a06050c0a06090c050901050105040b030f06121009020910030b040f1406070203030a0624110309100302030f0a02090d030e030705060a080708060f010c020d020d0807050d0e010201020307 87
    0x2500d0f40b508208940700e50082006603080d005010701a000100140138100342c3e03500401d05002e50300d0400302005502d0300c1c181d21603030610070304020411144580e10240d0703070b114200c00c190b401c45548000204003820603140500312140200410317042081c1d03007540005080d6000b92101152030381d4600b601d159051983c0809400c800401e0002800122440180e18210b481400d0140c5180b42c2001c0c894642407040d1910809600301004100d6140124450600101032102c118a04000458041100c286400c0075510401c040d880b06044034600400c102d03515200050304c4030309182441d0170005c00a40049d50500c6498502c9000308810703403068000d654071903100400d0001c01c102c42d40c1c0c2c190b035040c481320308190701802143c00008243d9501d0000d480040000d8441d50a2850308400040c110840181001c0c411b218100c9040c049982c40700c2a900380c0c03a07065880b4a01d040c600d000007a8808040070000b000c214000403280c0400502180c0c4400f102040d4468100c0500c4500041e405d13030008584030300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36212334 1250 36211084 36211099
    0x90102070b03130218010e06060a091517100305010b0906060412050f07032001020d0e15091207030c0806010b0f030a020d0e030a020d020a05030a2106080105190b 71
    0x400807900600035a003003400c02201c0f81c01c00038554082842c002c5d100d02c0841d0102000c3d401045902e4400e104107920040894105180c040441405010781d02d141c0a840c0010b01c02064400810340212150149040c241005440c945071190b00c015208005010442302942414031480c0b140c01d00521642c098200141980c2c1400e0400c0403a19404600743c10559a600c0307500c49002a02c1e1081c045c1402543c050041c00b01d0002c00c941c01c810480984500041c1103500961801e0440c503030082c040000080e04455003140f11006401d0740300c1a000c2c003106150302400f1440440009480001c1032030407688921400506540d45140312600d41200f48102c04d00044200241c0302040d03040002103600c00c031400401400d000750505140111829109400301d1984006100c14402d6010403c00c480f1900c9072004019070714565649948a00810b0b4910003400403951440c01c80d83c1c034081001505401d00b00c020000e1990356420715003e0103040c0c805003952031001e0094040d07801940035001c0035000c05400907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36213584 1250 36212334 36212339
    0x1030c05060a0903080a020a03140c070902030a090212030304060c1e0c020d0501050f010f0902040501050f16080d0204090501050105030601020307350705061e04060b01051e0a110309010207 83
    0xc100d40d40700141c2c41040084040c40032000032150005042d12200d190b000305140710140c1360107059010900c24800040fa01440b107078882c2000060724000781c81c00c07028056203e4440c1e05040700036040487d002940700c0511280340d1480310000004e9072040d402000181321400c0000d505840700d030f81c6181c0c640000001c0d2a03c000304140980943e190652015282d404601200c0d1103031402c60764160390004d241d01680e0b00400084414204480142218107011407416241c000080c005201c0c020b2901d40340340c00480c0da405000036003a40800980e401c04116a41c1d041050602c400960041c0113410b08240750070004107441d40302e0001e8034441c1c10103130001c5140c0861515140c070080d64140f503900307500b2000807445042a028450301841034030005c1041c0d4441c5160f10313185013001c1009010300c03e184030180c11904c9108000c0150340d0043d0700326200007800c0080000407503044c4120000c0c500104600740e211520185464001c1284079050381d9181000364502d00025124072540d101c160041c1c0c0500001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36214834 1250 36213584 36213589
    0x1060206010e091509010f0b0306070f03050c0d0501030305070606080a0803040204050a0e0706020705030f06131509020402130503060709050108070f0207050a0b090108070314040b0a0b0301141005060301030c05 92
    0x3640c100081c10100e600138404a0341540b5149400ca500d440e05135144d0800c41c3d07200c9440d004030716981c0c0c3d04030041e1280c1e103001711006140300c40c200c04c8001015103c1011508040c21074003100c10f0100d0380341d030a1055603102c4c180a00b031a8000041143c225290000018606c6c0b0302180c0e0b001d015a100402c145181c0715034003000003a14001d4074010b032040d80c42c0b0f08602c07028030400c01e02000702026000340c0070803454501010700300318030303242d9009139034018034200400501c6541c100d481880c0c3c492000c220b194041c90001008240c5914002e411074400600102e4106500e03100c04101d62013101141c2c11a0380d0320308111070f07080c0f01d03105060114402c0d038003103040319000b46505c03001011244100c44001c0e071303590001200701d0801c0d40302500c0113000048944040d41e1001d049548104141400e0260368004200b10000e501c0061004e0801446032001c40c82000300d580280d043d03100020002e000209048252040e00c60050340c80204400d5001c00000e25410050180d9040702c3c2c003d8a6413800f00d01c8d142c05d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36216084 1250 36214834 36214859
    0x1704050d0f020312040c05040e0601050607080c070b040f050a0503010c021f090503030a0504030801060f1d0a0e0f010609120201080f07020a0b010803090a09020906031603060f03060515090106020601 87
    0x40300c50543c003040c4500304000f0f6040314050b00c10740c001c840c4c240d4141d203424103205c100c0300818031070790003500514018490358591030202d440441e8820b0f0003e0f039038464500e0117030401055401070170309500001400a40803950501c0e2a050b14021121030440300e80c0c482c2010708803523420244402503040b41d400c40b0040341e1803d008850b200358420f0040380c400c00955550382940d10489060718505d03519400d00c0700b450b03840310138580500341a0400340c4104480784d00c043e0418a8100d01c11460345480c1d54181c10603210b10340d103e001405203a04e06800c500384054095000c1109025410019001e00340009849007400401c4001c240c041c0c40d920026110400c842940e500c00030b00300801c2d845071180500c0003031800003104d402002300f5400b45488880035400c005401c540c981c050040d141c018801d801450f0784043c21650444d0a040b000c01440210329820307806007580d60b0281a02c50708a00c2c0000c24030a5580105116400c00400c509038840901e00f0880c007880207000380c40040e40030ac00144441d840300ca1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36217334 1250 36216084 36216107
    0x30501060c0b090f010606020609010b010c02010c1209050603012301020106140607050a02100809070b0301050112020306040906060b040303080c0414060a050f2a0a031e09050904030f1704050d 84
    0x10255180100320390401381c2074400d5944401c00681c496070820000b44400c1c400c58200b100240380501803070342190002005440c541d40b001d0080401c1401c0070303041d5400b40b01e035900148800303000300f80c40e982e5950400605540041d048000c2103240d2030420704962041c40b40e10169000c04118000360302141c0140318041c0c02c204030444d100e201c2c482003140540d40c0e0901c4100c6d036442d81d0361210101d1410003c59418403c650340f22501e555070030700040c0800e83e00701d0200621600c20040041e00e035038a03580000e001d01854080540090310342000850f80105800c0107000743c80c0203480303003000d64882c1403503000c0a100b070344220800705141c1840e0103028170b8113034001d10700b43c902468a10706001303031017801c1d02c0c080c0d0203901411204800f001c0b0f0340316180c152948000104203004041c00714172600340c80107401c40c405454031010b10030741a2684035055000e40c8207040500806414200c0610303080c80c01410020780781c080000421040140300319903a8040702841d200383c0d44403014241080c0050016104250140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36218584 1250 36217334 36217351
    0x706081308090406030b1009020c1903180306050a0b0901080a030c0206040e0903030403030f0902131814011a0307080a0b0a0209060a020a060b0607021f05040f08100c030501060c0b 79
    0x20804645203030783d5400745601550080caa18415814a018100c0081030564840c01c120760051010803c0d401c00031640603050361a84461481004040c501141c81d40b07042180c40d6889240400048244401c60380954422071700c03500f08001481001c4100400e41409114501e100d511119098000a100c0c4161124640c809488641041d403541540301c0c00c03440072075004910350b10200410003416414050070080301541042001448815004584410050b034074082280b5298040d58403403500340030301014880d03000300d500d8943d010303410000b602034003d81300a00c600d030301000d801580b1407401107041c5013280c80200c024817160400f0360325000750b884010700758071000380e080c4502086034903074400030101d507207442c1c2c0500400109440c0c00380031100601078503805000180030f4200143c841c103c842c0360200004500c8c2c0755450301d44604440c0c52166410070491a404a1000224120006401c00b0b18141c0480c01740811401500100e0880d6024400e000004101c2814900400d40507103800d81c114042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36219834 1250 36218584 36218587
    0x91f0f0201051b0313050f0f0a060c0e06030a09140a03030212070e010206040311010213030b04020306280f09021c050c0316060509120303090312060612010e09030c070605040302030f0706081308 85
    0xc0c00ba450400c100203060b100323140c00000060741000458070808141410701d0070a22f81100c200b0003c80e07524000244425025641c0d03503601c0c0c003030107201021045c20040813001c0395035100680c5070050284d0466405000d1b40d0441501099015006992000151906a004044030b03030300e03030300c0441c0e0b04006102d078030300c19541c20890505400c12101300080030318001c2d0082c3c1c80070b080c00e1061616004009000803034002e07141891420300e5480c805030301c003055418080807910307443c801c2d650402070100d0080254010f90385070403e40c0a003114080e0016648c015016260001c1d44402855115142000440b00d840150399081c848140280050f000c1401d0140003500c0206451030703650324551094076104c0d0207510104114118180180c0020b500140c00da807050b0a102c1c40700c0c0003200450040c0640c0003800051000601c0301e0004000b6184032101c12005c4652480d0350b041c01030701c10351090000f0703400f03402074100c0d50904010010780300c01143d5090343d803811282c4c2d4076178050744068070040c800c50f14a0030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36221084 1250 36219834 36219853
    0x12120706060b2802010b01021b03100e06160503130209071206060203030603120f0301090507050d06060509130203060d0b06181f0e0f0c091f0f0201051b031305 70
    0x84400b4100d000d44904843c0c00844100d00110a01400b03c44000116030500148030191790380400c0703200d42e51034405081102940d20b10006400c1040c40300e4040d00044c1307070584185a05d4400501e03c0c1c050305820160601040500500315081d10007210842403c1e170300c1c01550801410a00c1113154044260702e4441d204903410301e04130080d075503207030b10400050f4004410b118007490284141200c1340a22000781d40b4100d1103003800c000c02d0105126403407006d40d80744001901c0c3d9004a085072000071060004001c107540f07440010b80709420140b07506000c0c2c2c20801d10f0041900103807007200c0c01110018000180d0702040e940d1074008000c000c0030150840b460310340000e10301403201c00f414051100b1801d0f10805520444004081480f19805404000c2c1e20030180142c48a05856032500810407802950780c944032140850007281d086022041d510039110310001d10380c1c0d84401104c600c24100d074000d21850b158000b81c80e1107482c11b01d100601a0f0420000305000304112304c0141c140a20a10503a50700c0c81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36222334 1250 36221084 36221099
    0xe06031806090607030b030a0c03080f19020a030315080c0d02190e0609060402030708010608040f021512010503010c0e190305070608071106071407020d06050709030507051212070606 80
    0x150140c070b010026602510a000c20036406003d1241406419401405400a2901c41c40c03000300041c0310180108a0024081403108480e00072200314032075030810024103046000e4005c2d07940031a10002e0300000e28211040300d45610680c1070808403403812005045203401071040044800080404aa021030484d03100d000310114a1f607034100030903c0c140017000610f000c0c01840000400140303050300c23442c4100300304985940c02c0b56076541580c04d24903040d0495034a0746407009981301d050f4001796102c0460ba0860b084084003000500040703004002464036a40c1c0c81e03080c507085e03032030303041c8102c0c0403890018510445041c800c1c0800180e4185c2440f200e80160b50f40c403910b0400c81c6c1034000c00000f0b000c0d80d04000a16401c030480000a503070b28002040d551611180c024440f11002c03448110781070000032001c041d562242c20b403820640e003010007003016040064002c1c0a0a01500c41103465000d02e98000690740f401d21050031010310b451020b07140c400c03500540c49aa42c0c0c01004101c2c1d07119610b40c4041041d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36223584 1250 36222334 36222343
    0xa03090213061a070201050a11070504110901030f06210201090909050a03020f0c09040803070521010501140f07020f030708030403030f030f0e1e1e0304030201110d0e060318 76
    0xd034a500c200080c0700e810220044510309401c81c3c02c00010808008500050340d000d0211424640a4903000c00510541405603003407a00580c4a1984281846042603100c40e008000b04103464090b02c04000c4d92031018000d0040d65142e1040c180d81e00d18010000c00c9146880c1012000a0320500d8050519600c2d80c400741c08840060f0700903030302680100404010541c0400c0340540000384280100800000c04c07000501c03240c0010310040080740040b0110702c03c2400340044d114a40d5154507501d10040e40403070300784c5507030400740301c1c4900041456861282401d0400f003113840c103444502d107051401d142138003800a4200320300000703a0140b2070b08400190182e4180060005540320b541c030008407440b444002401d40d0b482c01c4803034040c14031b41141031500d032200041d01982d040203071464403ca801c1e59421a801c00c1c8038450a1030001a84000d40040044040001c0081e40e1003600e030840c509100290007039a9050100c1c00300003180740b100d403040152a00c0d102542d0702403250038103903000c561b04c0000079091 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36224834 1250 36223584 36223609
    0x11010f1406030c0109030804050409060207050a03021612031d01091503050a1b020604060903030f0c08040c090506010207060309080405041a12030306100c1b080a0c0522020a030902 79
    0x545458106218142c41c0c1441800452042468603051107030645c3c0790140c03144030b14400d07144105c0e40d600a440401103580c043d40c01c0603400c0700a50381c4c0160742e4103019403203044990140d4110b00700b200d030106030700c1c0641c0c40c610100c03600347c1e59200c8200e4100b003854840301c040f51b41c510305201c0c2c040000101200a54150a85a14542d40c01b00709410004181c0c0240c50f00e804130040c14444103d500300e0600c3d80061680ea01075003024000c6920841820141c0082070b80c03640040c100e50901c15940f080c19008108140141c0c441d204080b41c0342d95800900003110300c1070702d1150060700851010080c46120760003250809014842403440d050340c0780d0015003200d0503144900b1261402d041a0346e01460718043d24144404004055803840c034010000494192100d0300200521110042c0e038020f000304100107020100031000c000ca2603d8a07214595a100f8207600e0440c0c0e80c01e0181d001140604003262201c4072442240304151102284000b04000b07034011442e04810580e450300350f0360141e0342d246100d041c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36226084 1250 36224834 36224861
    0x503060108030a0807020703030c0204240b040303170708010b030405010608030d05060f01081504020f090405070206040b10080607050705160b04060f0203040b030109020a020a0803040516140a030311010f 89
    0x251104801da004d0061000140041c0035034110b20010000303c1e42011894610300d0341190005400340108080c55848002485c0800f070b00d1034050000708034504002c00401c142c03800303911010071001c0c840b182c20102060449800d000200c000700100b150340c8110b00a560003c3c45480081001910b03844000c1c40d5030040c42e232105900303445200b0b0110310300300703800190031078042071030500c001e85402041c100d00001c0c00c00700980101d500080d2210b00c4a105000e499000348020003c3c40316081c0700d840295126404e0b201070300c000c20b1280c007041c0c3c0410004240811508284041c0c0318a80d1860001d4a06801c0711406854a01480240407070489190f030021002d001340e050342603101d03420004020400d603291904034041d903000704802d01280d0010740940703046501d403101c0540d4444a071101242000e00c040801022100b02005100400c1404213000030f8031201e50704000351441d50380c6078060022036100c01d59608440e103920300f030011030310400101070380301c12a00000c6106030310101c0d000102d412000d01d829 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36227334 1250 36226084 36226087
    0x5031303030f031b1101020903101a09040b0604050606072a08070506070206090609030307080409050a1103130303150602061b0703050d0203090106030807060902121903110304050306010803 83
    0x104041c0c1254042d41e03280c096180030428900c0251001518203000840e01090201e408242048007109404840b03da0b01e000d0290f0320340c2c0900c0c042c4040035059801c4891810a582e021905903400d0001109200781c0c0c03c142c010503a03441e00e0083c0700003800080c1102e41c1090040107800f02243c0c02c03040303031901502000d02e0003040c9601d08a400c0c079608001c1d0442e02694000c80d1003045140d40b000165449660122402552038074a60002065032003000d45030703a094040480c2d14818010700710050300854440322418456a07a0f01e9511800320f800c51040b00380551000d06c045440c6542c03010603090003510900b000030b20080300058000000c2000e0307228200603071003181081200708090b40b0f414100f40c0c0c2a044c881c241321199501602d14000e0350056001d00341c1c00300004010f550300350081c000641d0040c4216035140c68504095014001020041e801202841102e40e0052000a958074540288070080c84401c8042e913030440e420590b0000c48146417100340000b181554042c400300b8021302001c001503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36228584 1250 36227334 36227339
    0x20315030c01080601020703170d0c08190603020a0b03060f0a0b09040f0506010f080910050a0c03051003032304081e12030603031c021303050304080106090207110f010507050313 78
    0x5480c0800070001d00d8100300c92039003444042e0340c00113880d10590b83e01c04a4480548040380c8a03540702c1c059131000e6501c542c14090101141078010010501038994000a80d00719980c110b030003c2910b0161000039013101ea0607a0410443d10900003854010900421442058809000050942440c3e4100c0c80c2103d40020b20040140b8081c480d0305269007400780b0910184c41d00300c001078600030710726038484280a080340c0001c1a10400b40004001208590420451801c160070410024000c0312400004a40f80c030010644010107a080380007182e034103a07280a2003660401049200404140e442c5169100920011070780721000d0014001e1800d295040c0321007588620810b178a410410074000c40701440c1001403150986001c811900b10b0740d8412803640d05a00c000010f00004c0c400c56409107031170b001d000c0010040000c0031005000320380c80a0020310406031542d000300100e21512030010705200c07902608001c0b900388180b1100401105041c00c600b4056240c444c1801c541c0008546034000f0741c014401d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36229834 1250 36228584 36228589
    0x10603020904060806011203111e06010302041a031b0103090b041a06060703051914120403030c09080c04110403021504030303140609040b0402130c1205060103020f030103081606020315 81
    0x3c40004003803290040246514040d001405003071100d03c003034104546c52807020701c117040401ca42481000560f092101d804401e007100e81d224502800200d1107a4103002940302e2090104811031580d40380240680032089200f03245500d07500c082080141407540362002c3c480400ca42d100ca03584291302403040c462116003140000308102d04000d00c0e4a00c2488180300c0100800d078018240c0d03496904200c8084d0035411030410544140c50501c0e0240c1c840e220010341098600200900c0c980218402d44092140840d20b100a482c5689180280000f5900038206282c0341c2c40c09400c041c0c2000d809010881c0303055100c1d00402c0c19800117140c0c469403084002000c104142e45445a1180ca00344c0c0340c140403040c1810000580d03000e8011700050201416100883c0a56884918040642d00c42c0b010411441d1150b91000d020585a00f108090b280d150000040c16035019000700c0b540195108082c514580c00d5959917081070f0082490090003c020421640009150b40b0003140180c0300e120b0795a810480700e904 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36231084 1250 36229834 36229841
    0xf02011b05071e080a0503040f170711011103070213060905010f030506090a02010c0609020310020a030b010801080a2a0312110c011103030a0e0f030406090611010908030c0904020d05010603020904 86
    0x140d0100342c9003e5160301e8041002141610b0302e0b80e0152a089540b611141002003020001900c00b4003492110f82c0151007200c1e0350001080303103a02c186451028444c0810055640e40d040b040c5a4803160802c004c0040140380400d401c403984030700c95000041d01a25a62650102e840c00d0b00001480030700070b00309005001082010030340c000703000001000780441650000740190704545000700385d10388880162007155011b000c400d14a0900351021510351841d10001000f914580360304c41d0216150f5000400c02945c0401c81510b0300e504050b4031100d524080d980103100c44e041108050760060f04100c0800001e00580c0c40d107000c00305a99901d001d0700c070303102c01e00c5042490b000700443c14048601120b80031b190021040c0c940c0054010000200d140074110703881e080c44488041c0c0902ca000002c5d0120f45590064180d4043d94030301c2c0c1d110030101d481d0560341400c07140c20b020068180c610510016011464050050003085800740025007070001081400d02540e0080e002003010030f4010a100085003007511 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36232334 1250 36231084 36231113
    0x30601080108160302040b01052101170a02030d0813050a0803040b060f0a03060209010311040f06091703030f0414010c080a0507021b091506040b09011805010f0f02011b0507 76
    0xe8000340c14503c42020314407100d4407000380a56140c0f0303008141a8005c2e010b464030341c0c2142c4000d8440c00480803100c0210f403402d0140c0b205480340c0d440d901c0c103001c07400160280c04943c05802090390040e9450300b500e100b40010843d20350350700c141c10130f0000500e0502c1000540d17813144001c10f03220305151400542174803004050703d01401e9241104140e41d1340789a0114202e0f6044080160b4500742c59004030050040d400103100303145000140001c0c1410056031840c100e07140c9030380d519840741d101c0002144010103801054080c0d0720500200703400c021001c458942052088942000c0450082d96040c01e507081c03506c0280200709c41c1410840c0d2075145000d80f56000c4024409060303068610300c200821a10100200d078000c4515900062451400036501219a000204510307201c2e540d80680b200b0980c04514150700281900003880d4205c0e58030384181080c1c1d41c0584400d0590100f41078205c4d59003041c880c4080441d9211003074007494156404100418a410391f442c640d44003628140800e42e46c0290 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36233584 1250 36232334 36232349
    0xa02040b220518030414040c080403050d02031e04050a0b010501020606031e01020d0905070815060607030c050c130c08060a060503070818061005011101060501090506070501060f0b0306010801 84
    0x4800c104030034922035405580001000100065907100c40a500368070f0701424028079004c1c4000900844c4203609400710110440d0100c1e0180004c1d180b0960444110381706560040200d00184600803a03442e1540107150b005c0d4081500c4200903c45c44500854084180d0b803c0d607407a00010084818041400609805846d0a0000303011078206607010030f0365102c1400c41103804800403a07000d0840c0e0700070740440c1d0300080d400b12709000701002400d203982c4401c105c0c03055029a200e00796400706c0c98407075040c25510910b27008005509207030b00d6441c1918811904017040300c1c0740c0914280307101c1b140d4804030904806500200c00003040122001d01410400000d40000c0c0304220700d000400c0f13000c0e8803104889e0700110a01e0040307083c1d03c442108000101204180104e140583e00030490454144c280340011200c099807800003500c05100b00030300303c5146020313560001d0240b280501003070808034010311b0703807910070307030001849d25aa807a22840c44001d81c0c100040550000050019541c0e0010b98580980b065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36234834 1250 36233584 36233599
    0x30c090601020607110a0b040302070e090a0201020a02120a0f0503040906050f0d02040e070b122d0714070602030c0901030b0108160e040f0c030903030e0d1b0501021306020a02040b 79
    0x2030000c2e546050040000d4100701d180d400c0d69005030410301c01403100325800b07041c2889604183c600a91107003070760b0040c0f0204d021070400045d04448002204510300b41c060f0090301408520388c084c040c2c4a00e22019a2002c1e10070100c4460018690808038440307680580040c58071b4a06000d802c00076210303540d21251088001011204288c1e452030b043c241c0c2ca039411200010b002881800c060f062010942c822a4070340000300d4042e00034881d015030244a040fa8070b0102101c94007045200610750180b0000440314061f540c0001d250714080c0c0141031000d0a5a494181031040c0c2d562600140c0c1c1c412034a6014481d0045020000c1c2c0d6098050b070381050009080a003c14600b483c4200c0200d1481c404200420261100c02d01c010380351343c0e001081c070384004c6034140a2200c0904002d030180031b60100072000a4a42010350b204641c0c0840d0407100c1011990310780100f80c03880240201c12440d010030543d5555401c0090454200300035001c02c004000ca50090448105940100310840b4104000b07036010310380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36236084 1250 36234834 36234841
    0x61006030b04060b180a030b0403030507021204150f120207060207050c0d0f0f0204090b070c02090a020a020304050103150801091b0812090118030611120c090a030f030302070507090b030c09 83
    0x7145801d03106172403022012903696108940015440d84069840503010007a941c06000600d54107400c17840c4998181e4003110340c03d81d44a01c20844903c1684101c1d510000e480d150045144c2c411444600002d40c0c42c41c00b2041c80d92030407070000c106c2c1d00100046901c0b90b400200e000401506101110b07640c10100c640c98811440340c0c41e880000ea8800200901d1903024002902c00c45d035980d8001d44103142c1000c040201441c0c5031001034000304070044180e00c0341c4ca82d04000f030b500d95810300855000ca0b5041d80510b003414940001500607000c00b44050201546020300807403694024461205102d004070079810318090340c0c0d441044c0074100f503041040941c0001c3c01482003000c03003c003113405c2c4140130f290150240c03c8000e64100c03122015000105080c2c10102e20400440d4008080c1c1000180d110b02e40b00b041d02c0390701c3c2076000740c411040c00c1500050f0454040005c119502840070903940a8100076203460019aa01801c01c0ca050700800000f554910f4140004d00b0100105502c4c048280c611005606 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36237334 1250 36236084 36236099
    0x90e0615031e01090b1009051501091a0903010f020406120c0e0d110d030206091b0312070305070606080d0905091b03060a03201f230c061006030b0406 66
    0x3010002050001c00310b4080061080c0700c2548004801c2e40c10842c10b250a040c01c03181c8500203201d41c8103070070a03a42040040b0384c24601344001c10701c583c4016111107807010f19042002c000125054443d240c010800d01c01800c003502d082c082c40c4c60b2070041d8440140d40e90308010014207010304000010942c5450528100903458011400c03035020f06c0d08440c006540390700c5240c107540002d20780100076080198000200300f0140c00080640c0680742c004240c0d00044041c101d498041c802c03d50449030700d0380c82405e001c8844030030b40c0e000301441400303440d00500d0556141c5901003500c550b5845080c440d8071072024030001c1544001e0047c003804003111141e07002e08013200749545076400500340640c2000008003041c1caa43c2c4601c0400b00855119500390504101c01042c0d5000c82c0140c00024040c0c10074007800c03000c01c0f0b4081c4000c11446016220346c280400c0d69414161074010983c2c0c0144408030810000121020070040d0714410a514500f03601514141200201520290150203001781e041100620403030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36238584 1250 36237334 36237343
    0xa021c120f0902030109060605040c0309050c09090f07060c050601120503090f03070f080303040c050405010308030a15050405010e042109060c080702091e0c040b070605060301090b01090e061503 85
    0xc52140d0000705940c0001030300c020080c4140c0000940c10762030408004100080c64108108940044500308181c1c1d840940c141c0c00c1c0c914100c0024000d400200e10b01c656450701c6407210360000444000c8400d003200f08201f403443c02070650001404502c00e12000c03030802600300314041c050900e08007409503450480e82d030f8540d68012602e00c580300d44034001c40e642441d01c0c1001140001c203010004099115981c013034031900ca50007600c046c3d0340040c045801154900b01800f4841c120f80e402604c840c550303546c02441c00000c0500b03103a44e00d2080500d100000d0f0a075501d02031170307000c4c00c40344c4908201c0303041c01c1c60300c802a68204181003026000c10f1902200003900b204e0380600701c0d1000d081042d0002c1e001d14103244284a46000203501c060005c00788401c0e5150403d5414800100034a0700d10251aa9011300b8458000c034420105010003c20800740001d0303c82d0480c540103000a00003084500e03940d9251000311100b41c0103106440e643e40d40002d2000310400c13170b4607041115180c112010800d104046504c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36239834 1250 36238584 36238607
    0x6070c03170f03160e0a0b0901030b03010b180408130f081608060c0901020106030510061502010608060106110c040f0506030c010e060d0c02160f0e01090c0e13110705030a021c 77
    0x280001c00c5105401400b441440a01d441700900c140c007001c0d110b080c0c00b50140c02ca4000d45002901e00002c1e4555800d051140040c0c1850041c4038111010600c00342010291004104030703204402031244030b0901600c6556813003d0103c507000744d1481030400a4441c54080801420003004040340803c105c40d840110789990409208040b41c1d40d184083c10040c1d01604a952000340980b04a24980702d0402442d4812070070f480f060000c0c29001c007401c01040b4281c94090181c0c15042d000a07004020180c040d45060f000c0c0d00c1510140c0780304007112000601240c031990f40a0401e00e850b501042010314061029a101030401d0910421042032000400c0c204d003e00700068a055507204441c0c3c3c0454000c0044c00c8500e00100c811007074458840400f0720f00d0395054801e40704041d07220400412003403050f02a810f82c1c0d0855640380c0c018409004100100c0f40400700141151943e10074084100004200003800c182d4080d2004564802d1500c000a2420301410744400c04014500414030310380d40e02ca50303010322 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36241084 1250 36239834 36239851
    0x90105040f0e0f01060501020c010906090603090c030f0c0e0a0e070306020d020705071706180c0f0109050303070614010807150e0418030c0c0803130b030c0906070c03170f03 76
    0x10100c0c1d088034076200070700036003410500d1445140802004000c0542107601516400e030300b80d03858642d40358019100e0b140300d4060100420700e010010f1003403600c0f80d80300071102402070115181442c0c1d00d461701342c001c48101d0801c1d150b41c2030f50042480b282840d43da20303941082403a4000c04c880001540020f4581e0900c0c00010400c03500040c2842d012030789601650380c816003080503160121f55070040900004583c0944270354502407500080c4540702c818131034540408282c00640329140c550401c0081134240c00301642e044c8150703040c0208240d182003004d0409280304a0b030014000c440d0035208050001d050313011013100d500c0458140311341d41000080085c020300c0c40c2000c2200050380c00024000d1f06403840315100492040d0488001c0c180c2c000e003203040f07003401010b8100c4c6003522803483c0d80d200d11920400c960b40f098010000c001081110008540c0050705200603070528240c7c4c00003585642c440c45c0c0a82e01048800e1041c014403101c441c0964006001007201483d040a23111592140c2c0002400d818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36242334 1250 36241084 36241091
    0x20c0a03080304060b0901060210050606030f0118060306110408071211010503040503190c0b060102010c08070c0809090a1b0e01091403010b090a0c030c020303010305030301031716060603031d09010504 88
    0xf41003100340e40014030400c0009008003125a181c000003541c503a10301014080041c10800810824103060040301d0041080e04010401a07003010351605040780c840a0b40030415540e10340000219071a80304e09014246800101582c036441c060b085450004550004100740c5055052200000d1408011410841013030a105450350b079241440350030b40c01925500740141c0300304203002c4c1e01c0396880b55030820341510640c2c0950503a201c1c000120b080358103d5000d42c2c0401d03800c1000c60358a500910b1085200e034400c05800b850002044041a40070740160b52a1007000d880c2c240c01030401d40038400701500c004c00f628000030103060041c002080050703180710380c00354030b120700688407101d0300e007900081e030302074005802400c2c0c07800c04c025024020b020315240d40340041d207081c00c403d82a03171004c070840303040b203030858000d508503400c541329014504021060380c182450104039854649024440009005018070350009032545141400b4012100980c403004003070115a04e0306540e99a1000b03594103540003513030000f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36243584 1250 36242334 36242341
    0xf061008071a0a032f0a03060b03040b01050609030a020301060311030d020f0309040207061b0e030106051e060306040e0a0b0709050a06020a06050415020c0f10020a080f04230102090a06020c0a030803 87
    0x941c03800d1740c00c407001031801c61003080140d0107140160062404620940d01003200590355075514040d80001e0342c0050480d4032501c01084203142820203000e60a00040030345500624980c002070860359241c2c400c48540d0b9032141910760902d000e12400441d0070142c005000e40050100e1030645912a0300c000c284219030114286080c0800c1e64068441e42d2580026640c00f00070840700505658100328189207c0d40c280b201c046031505000c9000c214510000d0710031818603110b1410001190030040400da000307582d0f540c0100d11441f0403c09011103a016803a01c1000d41400d4030024442109608058010722412800300503031070380001c4030030003541c210320300283d152907e10b0030100040080b54401034245c008074041b500044045450446114800704071480710503402d041000ba4041d2000404c04640820002994040782d188a140e00034425049034040c01c8086400300c1c1c0140107102c07841200c1e0760104040c0060f0600c0075844000e445c040c00100b001005c950001106410140401055841e005c40407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36244834 1250 36243584 36243611
    0x170a0201200c07060c0611121b090f0f040f0539040308072f0a08060f0105060d0e010c09030614010b1911010c05030405070e160509030f061008071a0a03 67
    0x7001c848215085080d60720742d451051003500301707009d0300c1420130360f040110101e2166a42c40101ca03620744000c0e04000d420190b40c02000b05407004045260303040b07911505035480316150b43c8156071080e46c418561a44c40c0e0219881c500300803020102c066820250302c0e07001c8406540c6c0c1350a442c01c4031740c400503c0b0340d02c0c40d480c9042102c0e40041003541105418041076100518500c6650820300744080e0b9400400796034542c41255601130070342e80e401d20405a0301c014800c50130408000c1040c10714000c0302040780b4009012440c21110080f100000190041005101700501402713510701d40c011100703040c445941020f008108900c40c141e042e00c0f030141505541640c1e2030040944842803040c100c020403500c900000050495401154221150b001b200c0010030042a00c1c00c403d400340e08804204080300340c2140d801d4030503501184144e6414407d240c400c08003044104003241c03291108141d0006180c0c074200301e05140c075107640c0100d4074264070240e0340e41e45191050240d0308603100500d8041005003d032101c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36246084 1250 36244834 36244841
    0x709050601020109021002060105030d1b121404030609060c0f08060603130b040503040f0506040303210906090f03020c010c03020c04050c040b04030615050d02030a0609170a0201200c07060c06 84
    0x1002500321b44800030200160b500400c506040394400d5081c0c50719140704200c01c0700d00050031050001152040030880000c41c202210318113204040f402d00c00d40024221040080d40c1d001640115007254580048c0300c00c01c16180218070090340c10382481c0c01090b1000b0400f0300200001055a4000c000c040006a0040c4440301071101194000d680442e050401b030810684a43c09405044494000d8520008032414a68111000c80e5016a02d03201050402c00b0612075100032092400e503d152205402008501540700e214202c40c403607850b140310852589406410610740c3e4000a041c0100c22071840082074020828100f41c90046400007410f82d901c0c0701f214468050754020500452001ca000720400c0450351203904071046801c0c10180c0140e68804020030f0410106000390941c000041000025449070000d141c51031140c0042250305410080702c3c1c41c260043c0320300000607916442205502481d420007100105030115800d07161141c402f8807a40e540d8814400e00d820047c0c00125501400101e90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36247334 1250 36246084 36246101
    0xd03090203120d1406030c010516080d1a0907141204021807050406020613030c03050c0a12020307020a050409020f010f02120307030603020111010509060a0e0106050a060305040b01140307090506010201 88
    0xb0407640c0c03189076078081c0c0c030b0081c10310503140c04400c003440d0041095850700107105004814140e4406103403401c85000040144401c120407030310007000340b101c001c203c0900d01882d01c40000d01110307240205101d50801c420640081c0035030080c0801128a10703504003502c42202c0b51a4001d01c00c0c0032007501e075440441c52144201c140c1d084640511810b112101e0f50000061080f1072055084030140d441e6401022400d207c03245000b000f1030418002c0c0c1c07001038002d0f00900070154000303060f40c2e419403c51304da944d407283d06d1400000040c1c02c0000d040007185000c051940c0986000d4070104200d900590126840c40c26005065052085452885009601c01c12190005040b42807056480e8180702c003028014056500040340400c5c60b00c000045240c10500c00c0e244114a51401042c040e101c62030b0341e400920040110303050554840c64046081d0b15100c1560300100140d0741c001034030385841c1c2002c0f80c2030101a04a040e0203954004000c0040e50001411015a810010001071640305e0f000107034014803150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36248584 1250 36247334 36247363
    0xc050303100816081504030e0316090e030c070506090312040308040e01050405090715020304030503120702060916030219050d030309020102060a090302070311040e070e01061b050d03090203 83
    0x800c44442680001c0d0001c882000040b10698071101c0c00c03031561145a0301440d0015842202c075110415441560325410030b00a0800c407500e40064408a410400c84240c6409110031403502004140c42a204954101e8102c8000e1801c200c00d08012548400c014883d5603c1014046600e0f4400c0da410b00514081e110803440c8a0343da80d0340d903e4200700d29082403083c002095440d078000140c508141c05003d108803201c4010b4000d05080035030100c0070b1481084400c003144403d1001100180c010001442c841001c64143e0728585007004d4001e2420b50001c098042e10b400c03060a825107400c55000f98000d984d0f04541e03ca1024000300882910300003503610066005401d542c810742072581540c005101c00307000380c3c2a15225598910341a09407890a24014010fa00a00040010034007a00705a480304000038070100b40d00103c500d5291034029940c00422101d00600c00404c0300035003003000c4461400c1801c0700e50800c11103540300c4588500c0360303000750001e05845858440441d9030a20440c1c040b40c129 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36249834 1250 36248584 36248587
    0x509040908090d1506050a141e061c060609060203190e0604090c020c010305090703080d020c0f06010816030308010e04110a06020307021302030f07120603061406010f140306010509010c0503 83
    0x5504100c40c40b80041c01c01351518501d03165005c20036042060f000d1041c1c40c0a20a0f81211244410030b01c103031a02c50303d21840940481851001c056a2484014009082d294100c1c0b0100140e007032070a401c8401542c071801c14000e0b5014100503a0b0307004005d8a00c1800c007054200ba401c0c1c01c0c807000342c0d0007884c9200065840301e000640424103220f41e90160321250a00d42c2180c0048001c4e2006504880701a1180f40c070315800400c040000400d0f1500502300c107054035102504004000d085503140007800b42490003036420a800500052004200c0a121688000c1e2002d104a1450b01c004e030070301c041801529a11a24800041c1c18003122a1680080d50030103080c5000140d80c1d030300c00940300d4004e440700320700ca101d40c9280f40856040d903009590080380d1100c51116952507081d019912030318411207880f40709494010000205956100c0d0b8100b0540f40e80b010b2840346003090006140c4a209400032050203010720f4151400c05016090b65849282800e040b0ba8900c00711006030303050083e03481c004001d40700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36251084 1250 36249834 36249859
    0x503060a05070813020f040e03090904060e1207080405010c020303070510060801060b0c3408030a0f020105100515040f0f03030f020f060f06150309010b031903050904090809 76
    0xd580d0045108407082d036101c040c1d585565003665604d9291160180d4000510010402140380c680d00124405140c030703003201d28000c4203402203007141c0c100b00e4003a00e5081d50b695402440820074025051456481c0017407528102d40e80c1d551004a01035409018104400103142c4811501d08104481290344c0040486141c004a0300e02c2501410751809001525401d0410011304030002c1130541c4ea080703201c4400342821501d03050354810b0314030300c06810188201e604c100c3c0725404005030000c6000b500c040c402850303580c00421005070018003441d00e020110382c9440d007003100c0c07944100107960540d41c0842d010b4002c146070742604070290107627030020b04d0b40300e4000d1000540d9443d8860380b001168860389904d4003520714454140c1e151a685501966141c01c088002014003542440242c0c0c0420b0081c0070092034840002c403402c41da0004c9419502c00e80d518042c1e0195440d0820150b800215040c501c5000000160b40081c0503019000c1403500482d103803464881000307050341c00e03100c1106004d04070243c0c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36252334 1250 36251084 36251101
    0xf050606010e10021002090402090a1e0b03060303190e030f0601031e050d030b0616030c030305010504051b0d230403030606140306060c010e0102040b090a050f01021510050306 77
    0x5009032030660100d2002d54a51155003481c240c20014581280c000d02480700740d400c00e01000e944030000d07150703119500700000a4580c0d9000c04000c007a02d040120458a0041300140242041c01a000019220310a200300b01403560004215004400015803004004102407008d643d02d8110111140d40340c06010b403030106c0403400182090403a40500b2902d4071400038407013009800010318402402c030390400b10000100b203002c2e800c01748452034083c100c01d25120204014086074055500e040300003509030010f0b6010305030b060141c5409010115002c000f5400c01101d0400350105100d4802c0c403030000850300880e50b1301254425050702d05840000d107222501102c900c1000c4500700d030304501091811601181041c441c005279250b40d00c00a0f0303c203246894900070440180c0000e4a002c031a0340d21410f40149614003800070304010321115501c9a01d802400d01085260070090b00040c5c01008c034104120016a400111001081c03c0e0500c803102507126880c03800781218494226a40601c89d040034045000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36253584 1250 36252334 36252343
    0x60f08030702090a0507020307121205010603062d0909020103020d050c0c06070503010f0605030a0f0c080702010c030b1302030414030309030306010f030b090a0e01021b0709060608010612090204090f05 88
    0x3902c02c540c03c01255032601c841c04112101500d4240040c1d209004038800144450300b000120411420502d440318844590b10060b03520076001040040e40360310003007020811504030443c0548864651042408854003081e5101d500d80c45401001920b030a102010b590195040ba5030300b58912909000c14900700b6904001030f885080110030a108400009508904c03400680f8140c030104e6404044180c40c0c82000c44450308080e092881155449942200f10344444c440c1445907516916468654600b045010307007140c0c0d207454803d05140c1840101400c55885180d441c0d8a0b0110910041c0c6944a40c00c1c5800f100c4d0003050058030134840001805403400e80040514410b030400d036509800c45040901c21810f586042080b290030812000100d202740040c0e400100308a010385c2c000500349003100a112490040d00801d00845402002040c0306803462405130001a10149c1000d40d41c40d403400000400380c003074a1780191400c503510001c8000715501e640011320917179017040c88408809800e00f04076465 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36254834 1250 36253584 36253597
    0x6060206010e010b0a051c1a0a0f0f0e041106070b0f0c0403020105030601111903120c0302030f0a0903020c0a17011406030a020603060d0b010303020f010b04090c1404060f0803 77
    0x1510910000103210303005400070a041e5091451380034241107502000380c0c0d01e40c0000c0c041001015003e8018110403a540c82800b081d00d035590301c08003c000010090008651803504002102a0801801c1c44841ca070962218119064a015060103560f03a0a1a14074600d14109580c1d2061000400e98148000914403078002d5006045480182e21100312010300c510903884001c0c04a101840022640d40c000e10300d41019070440d200351207104140400314001841c00e1607041700800c1c46000c41d8070640c1031500c078140410740103080071850340c1030100e10120711031402030814481945890998080501c02c1c0054240c0d0b80d0003505080c262515004400c201c0b5250a8400320250300c1c002081100b00b1504806a002c0c1401070041c0960358416000d1096640c03000700026008151005601c0004041c00c1005009502a0380589422800200510b096801840c541d5110b2410001c0c9840802d510040a0040b00c1464500c909032041c00400300700a403000f64050451080c08450000c0c1294022009201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36256084 1250 36254834 36254837
    0x60f020705010f080411031f0f060609031704080303010902180409030905010311090616031706060d0c020c040603060213050301060b040b0702010912030c1e020904030e01030b030304090606 83
    0x400001041089a68602601c1000d00240c40b844107440d0250203213500c543c00a00030304402900b80c0c61100484c0c40c0241e0700c40e03801200f0b08500030001f01c05046204410706440201018407000740b40c814001c2c242206c501014007000301c1002103c2041000c0e030212001403100b201030340c0d202d694900168000b90000880d0814060361701c002490549810303c01c0c50072480e40b60703c50209a80c2080c0046000340911070032000099800c0000c03980640c1d07901c001c0e0040c40c00c01c003030040071024245001010020350181c0700107080d000310148a13081e40c5000c1528443c0c0640540000d440d800038008030318085103201b5043c0c216281060100600046030000d041d8001001c9905192a0383c2d00d00349422101548203100c2d40341002e01c800e0100b590b81e00020300400d40145003c7d140343e502c40c03014075646141e4810440c0403401044888041010700d909071100c10a070034400f1302e40307124a5000b007650076400520040c03c216074400c81440356030080e0f100c0e010740c00c009030440b620b842e26819004000d1899000380340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36257334 1250 36256084 36256097
    0x305010512030a1d01051204060617060f0604090201030b0418020307150801031b03081b060f01030b150102010608030a0c05070807060c08070f080d0510050906010207051e03030f0406 80
    0x91003010004103e40f80950643d94140c115140c150500080d9105650f189040100400c0480c507200302c5403409a002d6802044009100c0b440d0501045490000103440010764000f0000c000c01d030f6003e0140b180d80810f0656011481030380601c0103c5c02454000c0c6020307403161410140300d41036100305c101e45194070310035421501c0d103944500e01c4040c0c0b00281861f220000341c210300180005244c184a45221072411103070840f407291a80d40740c1a890308480d003080e01d9415408070a80300080200112904140c0c622152042941913407100100f1520060281504409040c541100e59200750f00200007403890300107880d20f0350550000144000b06d0b6131001c0e220b80c40b4502c13004c0707660040881c442040b038200d511081d06007416a6581d5940d034201d03460503211103110199100c007140580f00100a000e801d624002202c0c5850002c1c40000111600502d024400c0b2008103e101d980002e502c0c010349404030741002004003c802c1a103005c0c0340000040d0f4260001003103407000160041c0262040e1020368031943c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36258584 1250 36257334 36257359
    0x6090b0103110108070e03211e180607020a05011808030c0a050105060f03191401330303080c0708040b07110a120b150f030f03040801110c030703050f0d0501030303050105 75
    0x200c441821b0104e88581c1038210010340b00070104c04180c16142c102c03103102040c3c10b001052031110f1840b4104104094408400160f0241483d40c0400c1c2465403981150070300c0c100f460a0300451685001d07401100c0c140025608c0408610306014034010080400100b1244d550035064003d0f500d8081710702c0101ca40d50300b07010206031285442c01a508850708040c2c000c00100d0350350f0b00d8000115800000a5030304506083c595020f0050078040c4500002c080d10402031310100300888410b0001d5080940110044d000d031040c40007a1f4071415841e081116541084d813694080d0510324050310482e44445944100019000c003001003001e00c00c0c428a42c210380303100c503030380d615450509000140040104007904540c00107541e600e099980300c10b014000f80501500e1689440401d1901c019140d000c0c903140d00104040264aa09018806461182c10442414161081d16459990045001c001c06004006c81d400003450400010f0b0340040c0800d00c0e05110559682c10b000d4010142130081e0f5014100c0700c07080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36259834 1250 36258584 36258587
    0x2030706030c031104030203120f0d060b120106050c0a2402030a050f0106020304030506040204020d090b09010603060b030c0a050409060212040b071403060607030309050313060e030616020303010b030406090b010311010807 97
    0x542c5e0440780c020b0b01804e00c4031070544441c4c3c05135100100f824401401844a40c041c8105e6100740d1014140311041145c0d038003201841c00d681400d059000c0d6041020800c82c203d0702000101c1c040b02080d5203c020088102d4079001c1c00a2040c82c440c1c0e20f454083d201000308000300d0b00c03982105024006001ca003006998070f90100b00c0e103074480c900028103694440300118005007059030080040641070038002a210320340e40e9030204004030644490201d40c0d107400d0244180041031041e1050030001b02c0061030032681d1a0b010a4a26841e441a188101e5807540501c0601c940f40e01205c0550183c0424040603150518000240d03050039110800022110390203007100c100c0319000c4a00174240180818105651564100c0c060304808030210fa0602082c002032115031135144000c400303481241c40b030b185007440000501d07185c000020600d101d40001d07010384004140d004800c0389d05503010110019034a41d0785040c550080c2c108264028480c00a210000041c400380e01407502c00b800d002d9840c3d401507151003d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36261084 1250 36259834 36259837
    0xc020f22020d1b050301030b0603010207080301090203070e1903020105031806070c350304030201091b05030c18180102040b0a08240306071b060c0f090e01030308010905060d02030706030c0311 84
    0x2040484c03010001800441d5000017103d500c02c500800152070600c8a1395240d62030307082a4480c0003110f0b0048148210142c0125642036a00c0055402900c821607030500d81400c961140310107410703c5000000705081d00e21201040240602c0c4108035041801c100c2001041d83d9540380041e258020040701d0780c40300c07201d100c501582210104d2030480903041d50322020700d080d03030020f0011000d566032400d000c8005513080d98040c0c0c6515045444c1d000f182d00d00b00a16082905c4907100c544250034802c8154a0b120325103400f55003002e0510314a0701460b044003078003402442603030800303401c071000419182d21055000b40820f10a030b42d0302854060168084c40c128464024400c0c42e10f905420038400074602c40d1094210610110281207003600001441d191541240e50342d40580e400a010f046a880341039401a2003a0010b180f41d850a01d031315851a2001001c1d56010b010f808030075519400815280c0d664074140c0b403d400d800070141d554135a0340f03010203801850b140b440e07039001ca4144540744070070034601d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36262334 1250 36261084 36261131
    0x3091e01090303030c02190c140306130303020702010215010b13051e040b13020301090f05091b0f010c0203010510050f030a020a090b01030e0d030b090a020a0c020f22020d 75
    0x868030701d00c01d4110350341a4041c2011644810443c820031610102d410031110f4542401e50180341e9031594075003441c090041900c40104818025404201409155803441e001c120305250140b90050b2104940e10040303081a094810b42d01750400d220001161a04000001f8a00000d9810506051542d95014403020030030184484003407001504a090403402c5c2034120341c1541000038030f40c0808224482c81c09089070001c2c1c11601c0c045070340366120004608103214194110b60180c0007060700c003212810100c401c00342460320a02400d1110044c0c0c042e64040d0703000003581940140280701038503028611610048981c451170384148401c455107070040c1008500500d0580e00580101c1455050400400c0a00341d08140581050f581b02c02c0c0900007001404100985200c1d0358021445040110402030f648201405420b81d007031040124048164000740c4025402d98191406103018071400001018146207111340b0110120442c0d07140d03000c403600d40c0200700c1ca0100b160104210280311110f1032260040c1d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36263584 1250 36262334 36262337
    0x20102030304020411090d050f0706020105010b030a09030e06161101050423030c040e06040b0609160c02011206080f071208090909070503010207030903060b090610030f0905070803091e01 82
    0x704041005820260054001a00b04060003172402c00350340c005c0340d440304000300142c42031740001b046070090400600c5001c00504451009001035410440750078694440035004100c60395441804404140c00f0f0100d144408000038403454130350700d410300d81c003600340e94001c0c0c2118803070650114107001d58020390649090b1141c0040c0a401200300c07102c40154607244074240c650620640440d00801e6503240200c001104528000c2c1049081600c1d02d0303043e000c2c02909a80c0304010400821034a0300c0701c000c14014090300c1d450708000c95601740c0010303200807491407a40420b45040c00070101e4000c03000a046d8610341c8507042120f90301a551480d42041c011608402001c22408024240c10380c0b030201d130001c5c4c00c21008010b94140a40d16000282240e1001e00b048022940540b01001400220701c583c1104000507a42504c43c1d2a049000418110f1003921610a160361440c8169402c0305952050700a1540a411a04a16160700016645e0f411030101c40c1d128043c142c4489803201c0e80700d0016141954103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36264834 1250 36263584 36263587
    0xc0f0806040b03190804060f080402030c090c13031209081203011403100e060601080106020d0905011b020d06050103060c0c12050304080f0307090503011a0105030408180d0b0703050601080402010203 87
    0x250320030080542040c1d80310300c0d410b10404481040700403000d0020803605201c0d50520342d80741d1a0003c00f80c200344061040500b03111408040002580f0041003070500a802221040d00e1551140c07440c0020f1300600790042c1584403000004001c100c41145060901d031466207c801d80195a146015940c42312240d040380c0958040c0700401034101049120550400e001741a9000d14004004100807200044490314042c0d00c00c0e0103212095821007000d81c01f404262000e001000c280304806071602c0f001c2e11405041000c0e1450307440e02441d0009010600650040c90741d01c5040f110b007400c4000c0c0c0b0081c082500e0300352400e0009408035000b00a50101c1035800015001100d0b004581030301d00703410061054a8205040005440e6a054500114420400350311140941070a00c2c0506003165000220b481164446200396010790380c1010a0760b512a6001212984d5021070035144010300700c82c89460303a08841030fa4504420008802d922034401d034950342d82000035645180044405520030356019002d60070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36266084 1250 36264834 36264841
    0x302070b04050f060a020f0d180f2403020f0a020703020f04051303050304080702090a0e120c0c0909010f0204150816080402120f2d0d0f1101090501110705010c0f08 72
    0x240710000c0d01c0171000f14010b03103041480a10216043c220748421030000501c507000345048030b0b0361891034040500728100003503084905018042d02d5524991a03800b0552404079000c40c441446034044550000d0024002030b240c0c10a04006561900c80d80400ca1007810a1120840b45007003a2260610507030390f510361710200c02125101940c83e580050415619140100585405a2250780c0b40310701030001c540b000038041030400d131244c0c02c00d150040b07050546441081814481e00002880c5101d1074000c176010200303500c800c100703107005007600610682c0043c004039000038043c00c90302e038105011a5030b4441c81125600c0340e4140c1740314001c0d1f001420100d14075002140c0541041e0065004a0700e501c030858403410740c07219599291040a0a042a0030000c01903514018420f103c402c03441d100503c801410140032154010b4446400402c9503030810400030b403120318000c004d40000c04001c1d08103000700100058160307004000d42c040d5005590b00c1d800c2000380302a292065803511070703103101656241d40984 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36267334 1250 36266084 36266089
    0x91306050a061709010506030a031209060204270b131508010603050618010603080a030207030c050105101706090604020105070c030c12020f06030709140402070215070303060e01080705130e0d09030302070b04050f 93
    0xf0105100304c403619030b100c826000041640c4024009040391032035240d43030543d44180011150a10507501442c0303604003a500b107030700d880c2c02c50070f009800100302d8041105040300400d00d014040c59844003174650300b484800030501c40d001c24810302820080a40510b805d00e00000d06091b00c0103444010010b40d402c110305c0e501c0d544030fa8060301000e4440c3c40c1c0b159001400707468281c250384040e01c0703180d41411004010803281d401c80d00d240d0420000302014002d1883d043c1d48a035110b00000b440a0f0600c600020300c00100904080102c0195600240c2c2c070070081d4482d240900b0004078844200c0c09000e000020303203040c0c07503c041079a20450309070340c50b219100e090508011440802e0355045800c5070f02072201c2c80c0142d80355040c01d00b10320b0010300a6070f00c80260741401400e54480d54400c1c1c11311001c030b900610880354041204010b950045c0e03451306020240c4600d41c4006d200d503149d514074500401c2520b00c046944960300004a9000f80e00701d0310360b1901c070b19002d600c134416407188030b03803000d8045070545c800e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36268584 1250 36267334 36267347
    0x60f06090603020a030f090b07120e0604060b0316240903050d030b03070504020d0b040b060f030f07050d05010806040506090609070302041e090813060503040305091306050a061709010506030a03 85
    0x111454030b00812001039112249090351f011902c2150306000b80010041081d9004224210001100e8400d000031009200000d0300d55070060800f901e0f564940e0150756043d00c041082c84541000c880700d40c50b0580c0c2e02c00b01200c014201c00b0002c030b500c520080701000b01d988184003800940750024050020710240e40000e038020060030610380c0d014042d0001c0040c045e40e8620184c2413440d668003010039080200c45c1000110f40c1280b00f0b071361080c1c4042c041d96a6020001d815a40c0c0f00c2904030034030390349854403036095030300d800365100212150781080700210f03802801080090190344500b0454019807100e6059a456400440b80c0401603880a88100050318082d00540c8a000a050340c001c0d503044810b09040c280d07007031460140d84a01002600d240b0441118040c04002c01040c0751207030450919903001007007841005001881030fa641701546071180c2031540000300418004013950035559450001400c82c0c190011861102c02c03003200001c04040f010b0040a10400c03004001c0c106964580c5d4058402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36269834 1250 36268584 36268597
    0x90112290f040c0504021b190b1902090303030717070206160e06040b0a0201050402011209050606010305061f0f09080604080a03020c120408030d060b09010909020903010f09060906060f0609060302 86
    0x10140d60840000f000d845d02d200400045524080784000404403c074006e1501c4800c42e1440554403241040d40081100149165000621202c1d03441402e0352803000c110190180f9a2003a506010003c140080b05801c40f0240000d480d0000288400b683c85c190141d8403241e0494900d0125086103404028082c0316030000d00b00058000c141900306500c413406520300b500b1111708540540e55600c107102c15036800c4079204c2c011151a01d03003480303105400e5440945801c0301420f0a814162940c010407080c9e40c41d542300d81181e0401160a00a802c000c2a000340710401440304e90010542540c001b1811080c00300c1c840c0c1c81141c114134403601e00003c1049c210000c4d40111603e031041c0c052445c0203420241110010f00003850002d00854450704015600401c40e000d95109035035400003040360141c641d800002040440e0140350380140c6421170540401e01404100b18000326261400303100504002c070a030b0000d21100d000c0c4404004160f21010303114241c0d01c244c0100070200b0f6001c4001c210140c40780c0c004205 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36271084 1250 36269834 36269843
    0x1203020a0512040b09190c0e0604090f0f11040c02061f1509060201060b180d03030b040c090e090c060304080a091205030a030506030106050f0d05030405090112290f04 73
    0x9030040c0c0000380d542c01c0200b0748007104c448403044140540d0007010040d0341c100a500b2005a12401825600c14000f120700c2e1041c102c113000c8060003d04107a80360340c0240f4046030480c8000050b0b50403403500060b1818100e40c00c0300c50340c0780c11804403428100340c40750900c1c010042d002003034180c84007c2008161f10443e41c3c02c0c2c0420170086c402250600380300300a25004100307034032080c1c4e100b0306005003c0d09481c2c2c19000f0b5003e042c010f100207060220780c0045604900030942d20003400e404542000c40c040d11800e080b80350094103041207a02400d5126080e041159903012022400e0b85459800588881951200d03a034005014004200410301da4001030107007503d00c2c10448582aa50901c0002c0955134032001d643c2c5410214a006103150107018032507000000701e000304465820300e8002042c1071100c1c003000b40101210442c1008000080040790040e10700106488495039541f115102d2112034100115910f03115408850303c20080c40c0c128100d0b003400003004c811582c0c0c4a141c05c85030440018825107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36272334 1250 36271084 36271087
    0x5090a020702060403050303011d040f02090601020703060218012003040b0c0c0310090308060a030201025b0c080604021606050c03070f080603060a0b06041701060e0c071203020a05 79
    0x60f60350304000e00045124001454503503240400c0c642510340c1c50702410b0f0b0729511410400002035001441ea43c0d140c0d60407646d81c00c81d0b440d5000100c0c5405141d0300020800e40c400281a0011407001400361961002662850456000102c002c820000c514144104a47c024082800200074bc100680500c01d2410304032603000d84043d00081c03401806580c51070ba003960f0307954108249540310310802d510403426640302911a10710b03070000f580d8103200762201120030841002e03000784c480346082c16044041140000e074440a8400800940a041034540341e102a8440c07180d16148101409002d503442c01c580c40d0030145640e10300c01d100c0030b1740c010150b250b003800e0700d031542000040b000d01c251030085005200c200d459151040d000b419100318040c01909001141040144540d0001003041d4400b410000215014041e00c0c04128903015540020544504002c012001800705511640480c0c1e01611107a0458031250800d1425200e172000c0984403071b4200c4240028039019400404c030204e03580c90f00700d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36273584 1250 36272334 36272347
    0x1501140d060c030501140607020a051314100518101206020706021b0708070e150a03080c0109060b12030d0903021f050603060703020306010207171c02030903060c04050a05090a02 78
    0x700403a101d980003803001c03da89030300500010344a40c025800888042d200589081c500d41c00007407c1710454840c05203d0044600400c128400c0c9030080d010304802d200e07034024142000346552a80400300d02805006507440c0807105502001c041c8001d01912030705003400003042c1409030884c0d1511aa070804e90301c13a50200618400502c0c1c601c000c2008400c444805101e4403c1410201d00300245035000074855030040800b48040307250194450303008560841d4000c1c142c03581c0800b0585003080355001814020000c80e031100b41c50f90641040720780911a40c1d00300031900d4001c0400404d030050810b200803690082c007151105984a80c0a11040f138000c1c01280c010b0150440141c3c03c02e10101d00c10302445403a0750034049070342801c003c00e641103034417828158158580325000030f5881c0114402c80b040c000000b5020040c40c2c205101d880b107a0440c600124914941d80700001e503990b4401000b242c000e200700800150780300950020f031420f9860060041290600d44000c10143c07280207024000e0300c0d5400c0085 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36274834 1250 36273584 36273593
    0x70c030e010306230a0506040b09010c1e050f21030402090a0e010204140a080d081f03050d030b030c09010305070b0c1c08070810120210020102090a08011d1501140d 72
    0x300300e944d100f0104c495000920801d11a0180840e84101d0050b0004c0c0400c0c8404030040080e101c40d4802882c221060442c1030910389058031488580001c1c0280640c42c15051110101e41c1c1920400c0541c00c6408007500c22240e902074040c500c02c2d80d800c0541c2070000ca801440c103062041c0e04003510740804101c500b2201d110908907801030b444460b0302c4640c60700c0704001d410702c1e0801800038038618014100301882c240014088a400601c0001070301c1c403200400240180201000003e190450101c0c0c2c1404007034400903000380140000c044c0b0074807500382c03402024030304040071303a05803070b40200608009403030580c0b9400c42d40c0100341d01d41400d020320040d0190803903564a440402c4903035507071190b105007880e41d0054080000a030940140281204040c8001350030380100b50035007030b8151050110440d202404a00901542c07070070650003800e03440b0002c0d600c1e50541241403101c098034038003200000c0100b4030507a205041c5101d60792a0780e10900411030100700e080c00320358044010b8207002101c001982e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36276084 1250 36274834 36274859
    0xc0a0303320115050301050901060c0302030c1f050a051501030b0102010608030c030a030c14090904020105070609050604060507050a0215040809131a0402070b0a11040f0e0402100305070c030e010306 87
    0x1120710300301c100790010401c00300403a003466860702490030258907550500e4007017010b080c4140104c070b040c0811003401b40d04040c420411201c00c80c103244140c07061283c1081900e02c0440c00d4a07055001e181c20107020400422041c82054010300c0389680e0040c4400c5100019405040080c00f414155541c0340d030006074001c0d0600081c400b4104400c05542c1d150250103028003150b51642c095800c002303e40500c6003100e01d505086410200040f600d042007075031a4401201c0d44d114010000b0802c500344010f000030080009105802580702c1e040c103110b0799942000449460040f00030b0000180c0c071500e0801c5030300c51802100c82e00940903950035031408078580d000c502d0780c048403412002c01c0c0da52100009901d4400b106908803500044400754608001c540f507030302c2c64450250024903040d0781d5010598200204800303c0d030041c0b5a01c01000c21055903510010725620045600707a018146512001360281d1003441210b218a50603101e06031107495546040f150030301400710381070516613600d0010411a00c1e090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36277334 1250 36276084 36276161
    0xe030d05060f04020d09060e0a030909020c03090604080114091b09060621010f0b090d030503090708011104030203011401050a0e07180e07021e1903023408030c0a0303 73
    0x21030201b100c2c2c000745018000c0340c0c0440720810681e0002c0f450f42000a03030040190089078461000503032507a50040d03504e8214401c0c01c0d105c6601201c0080d0000c1c03005010740040361503684008082e1191f0780c900045907284c1c590074500449900c2e40d03090480c642d1516956458020002030700781c0741400320440c006600061042904940341e074040c00100841d50115980402500b90424014205007441d00881c00c0c10000d10801802d110000c800200d100f0020042d0500500c0c8034802800a020344038180c050302d91003401700385e00950030060264086544010440e0403a41c01502201100e40390400032211140003030405000c01c240811501407128407519a00c025251451100300d007404c201c3c8019190050706421080201003d60b00c0003004030022031a40e41101d40c04004000700603462030100e0800081c8210300c0c140807100c1221000030b0b0f41484034441c4201500f926002925256030220341d0300d000c1d6540c14140d550100e107a000020344240c11a030440c4821068010044480d01541e11240c000403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36278584 1250 36277334 36277357
    0x12d0204030f030c0b0108070302130e010b0d20010c080a0305070203070c080606090702190201081302030f0f0717100b010507080a0807120204030b1308040807060908100e030d05060f0402 82
    0x242640148050f0f21744050050000000a281c01455039020645840030f40340902d803076581c1d541480f0303520202900b0000001d0001050041141a689091644040c400200da00d1380d00b68000c00041d19402000007080e03194000c0d04103401c080c00030404030302a0600a26400450109200c1540040d25107414070026111480280040d403030084140840b0100007401142154080850300718010000130612a0043d0203182c1660b003a50f0b664000e414030303011094000d40600c50300d4000e80e480003020903503a225032540e2044d40c107181d5580200c05403c18914261685c10740001d0030404400489620140038400181011414100d11751101000c0c3d0b0800903400000c50075000822218550004441c019407036000350031410282980c40c1c603072070345100400b818103840ea420000d0b01404806000d8a0090070244201c03401c4c1c1d44c13513003401004010b45100e0405130b4460b50040d001d00031014060450b010065000075800d11440d1004880506005800e1641201803081241f140e900e4038002804210401c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36279834 1250 36278584 36278597
    0xd0207140a0804080c06030402010c02100302090d0503070c0506090117071206030303020304020a09060f1205010902040627060e0a0c090e090102070311010c051b03040906150809012d0204030f03 85
    0x3030444c09400e11000b544a80e200e000c0c20000c000040c3c1c1c00c611908000754060300d40c80b0180d440c040c800c0c2c2c001d00c0b840407030541c01403040e00102c0c10007800000030321019100e601140c1001e980c0d00213000300d9000c3c0c4000c0c0c60100d030001c05068031100d80c0640c03d075400705052404413000c0c610010030408441c0f0030382068000a03000800c000550900c01b5507500140b8401380104506840d0105903412801180610714220303211040000a10009401881405030020420003c82d60780c0c81403142101514540010310404420a0301003d444d903114400440c1c2072691a1401a901c480d2220024800c0701c42450034070080e0b0102142031810316807018800c030203410005035203591505000c2c150740004103800c40c4503030500b81c0c10110958050240c030081c8500710700c40742400708124401400e50003150000e40d10649046000100751800e44100c180e14015616102c54644854040ca420f031454804014000703002006030320b000d10814050850340020b4140d0060502e501c0765120080c58200b0f440c00d5000030007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 36281084 1250 36279834 36279839
    0x90b0c0a0201060b070c06230912030d0f05010527061c05010c050301091113060c0f060203070903020f01020307050a02060307030e011d12031605030402060f03070c05071202060d0207140a0804 84
    0x40080c030030980c2d0010764010f234500048400e260726040c0b0a00a445004409107101c6010881b801c00688444c0314181109000c0d10306480780c0306008200912031705118102030b806400024002d45041c0080911100b238000c541d90b0340c2020b102c581c040c1c51540a40443c1003215100224200b03224a481d500c94954655540e545403039184410350f040c0900c17440a480080000b01500c10300c1c0701012084440300d041c824400031072400e0100510080845c040c185900000c10072107003980c00f60170282070303078401c5032040400c002442c0120b0303890150340002851746e070186891070050302e495070186601c0101d03494041908006082441d095441401e0600424801043d510082c0801440740b22658245c0c0c1d05000c0c2580391041011005200910100042c8080080443d0554a814084400c214a0203107980d60f241819000100001c0f04400180c4403030017502c070049020940100708809042c0c0082c00350707003002056099a0700035448640c08850307840002004820710700707080c170520103900c0c091241103403100d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 36282334 1250 36281084 36281087
    0x30801030606050102070501020718020708070b010807061b0b060f0a0801090c0512030a0807030204050402040303080703060803161103010b0a030305071203020f04140a0f27090b0c0a0201060b070c06 87
    0x6040d0741005066400109007401f45036070020711070b0101ea0451110030400340c00400120024818040054540600082e20000344950302d4203c0b07040711154400c58050380e40c1e818003143c0c01c0101110602440504172803d0005c0b441c5914030b5504407000826540545548000040c208a0140e0103100265141c2c824a0180b014001d50000103000a6400d1101c0140b001e0209480303100c0d2003e00c0050140031808074620611031b41c141c901402000c3c000b159140d48904002c1d004101c115081c0d0300103400c00d90b01060f01c074804419540300c5504040440d02d000c00c941e4540e21000340302c60300190151340c0d4070401d211513510304042100950190311030a03a107411504008200b404065556401e042c01040081c4070b202c030140403101100c0c0034500e00c4940b00d00c80c10006241500380c0d4001300911440440c0441c0014403501a0114036505400000c54420180c01d55015a80e44003400340400c043c51001488030444680100308d0304000707200014226403550001d0003281c01a41c4103407034640f401d81c03040c403146 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 36283584 1250 36282334 36282341
    0x6030b0901020306090412051303080c011d12090609030601030602070201021b01020d0807111213050405040803060105030603030408010c051201120c090e070503010603120212030c03010302150706090308010306 92
    0x40e0100003503246180c25000314800c042d0240008100315060142400414441d04c140c444205800c1201c03148107076607003410301031034000024104165180c5030400040d01d50450000b03507401c1d400e00c082e000911104042c13109940240c941140c0040c1c04204080c2d0554041c000c2c01c0c041d5200c1c400040c1c07601c104e800020710704000703a001c481203a1000b002c440c0040e030300007840c0861900c80345004207203035407071640446a99003110b40c3c1748000c1c0300e510103404111031520040c0a22940e100d4030042038554036001c102c142c45082e60702034040c0d00c041012400551080005652080d8003404403890a95584000c030300319211042a00700191012030b092034242d407054181030042203034000d503201340942512454148076143c400c03500015951460f01e812440144507040051400030002c000c2c0139541d04001c01039070f084040030b9005005500b1028800c920305002d4a00500d90b1449803802d5070b00750f9003030280c5c400642d85441c0c09140140305441c00610140181c020b054404d541c0e01109524510704441903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 36284834 1250 36283584 36283591
    0x6070b010303020d14030c1c021201050312120c1303050303190b09010b090d030e031516030c09031209050603041a010504060510030b0d1b0303080a0b13090501060e090106030b 77
    0x17040f1040360342e01d400648020035680c214044d01a80b641d079078000400d081422601c1101009001c0c000b1a0810440c10204000c50498a00381c050762012141903070401100d00c921000801e002c145000070445c0440503401402201c0003000068000036260340351285580c000711aa41d40e04081c03040002c0f0900110300404202480a4030681d046504041045c1d1080c01100d654034000c40c1500c0e0424240740c03040864a580442c09415500c6070f20040c8510380e20500110358600014240d001104225407091141000040180e9109030595086540d040315406508040c3d00c100640c110740131801d80d42e118000c6000390311507901c2440d9210900720182034448140c0c001e500c41c0e4070b086002c0206807190800e42c030108102c0c1c0b800080e4507540030005100e14440306806002d010380e080100058680e019080f4040e20b000f0b46856403642c2c1e0b00440102074401c281c441d0303078110034082d00440050329607400c620000b502ca5030000c21066200d144030f40d86030304100c80c0c03840746070f4403940d08000f0b01c414550307000e41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 36286084 1250 36284834 36284837
    0x4060e01020109080409090204090605240a1401050a051309050103050f010504030203030613020c03030703020304021e060d020a0e040f0b1e1c030c0b04030224040302060f0c04030206070b010303020d 87
    0x69a43c05407182c0380580691b20034007210b140c40d0600360085641d2540801181c651000042003d0b0070001145803200c1341c030901da05488054081d041c4001d2a1401e044011580c002c244018504411070046039141c20000ca9030382804011710000440341c0c2104c08100c040c02810700000f8080d8550f0a0103807805440d0041d082190349002c1c01d020229034040100c80d4083d0041d105100ac2c041d0301186400240300e80d50219140d070001006001c42190300d13400a5000707034000c030790520b08a0702c050035030180101200400c1d5440001040301c201400401e40140502030440c1c109840403c0840e400715090302c0801c908031506503034030f150303900007481c010342d04891090952100c4150b07146801c5c0451040c00340200c8501ca034070511000c0c0000c01d40300d03c8000034260f41c0181100524101450003035a0f4141c4a060040701c400d083d101d000340c00a003411090b1007a601a801003c903515007103481c03a501c410103444285005000c00020002d030700c82a00a25005e0302c2000010b07800d41c0341d0305009040039401c516040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 36287334 1250 36286084 36286091
    0x3050d020c0c0108010621110405030601030b0f010b0c060112060e0d11070801060501120b030111040308040e0105060a1205220f06050603060105010504090506190801050a0609020f04060c08070b090304060e010201 93
    0x35100000a0940301f0054040040000c0103c00c950b1070880c0750165078003055051107100d00200030043d00070402400b80c47c018a5642090344c9a45600329035010b607c080111651281004111074085e010f1940345150082c00005002c50f5a0700005007450b64200441011480140c1c40c901c0000e0100103250040c440480208915410100006d120058040b20b11140503114100300da0030b540c007076001c035140100000d106079035070b66607290851058115202d410754074050380000188030b08040c0e00b218405c4800da41c1d00d001c1d040d0b41c40704100040c10081e01040461111034801c8c00310341020f002c02d40b09170340601072503280c3c0b450300e140000640e20020801e6000350045001004566001006e80d4140d404884010400c0d41d80c000c003041d03103254403c11840e03a02403084d500142c8a0380642c807150040511300b8060010790f8417100720344141d119080010ba0039042c10001006220300c151092030f04284035a043c1c9140c40c8a507100d044d8000c100f9074020140e038100142c2004890b412280600100000380000d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 36288584 1250 36287334 36287357
    0x20d0e01030e0a08071704060206010303020c040c08010e0a060305071701051608062713030e0306010302060d150b030f011e05060a0e010302190509030106090207050601060c03050d020c0c01080106 86
    0x30794541500030f50040c020f000c040380b0001081b0b07041e02008012402212603940700e0343d4550000b503440300c0a10040c2c01501800d80d80d1050303810280110403122115440300012a441d140602a110000401520816a82c4c510101c001501400100300030300740541580c1403c2c0c0000409400c440000e0070008030000e492031065401e07900080c46c0c03130744058106c4001d10030301d00140340116459008420310410520140030050301035018040e550245000e0b54030028400034030800d1540d2900213010195000d0720a0042e0100400725801140c40003d202030040b100954603000c000d210740054640100082e640740041c40249803140190004e00f00e411500c804151421001c00c00c1c0348210015a410000b440f055154664003d40445d00c000c100825075181c07400c0402c600502a4000d40382c440e100c2d50902c00b00240c220f076a070080d65125900301e4050b00e120b9280c40c1040d500104000e10440520009104440800c1040e1001d0940031000350054030140705004001014540d050300848107110f41002030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 36289834 1250 36288584 36288611
    0x501030e0615040c020312070504150206100302120a0803040602030a0c0903151d1006080f010b13090606030206030901020301090b01050a0c0222060305030904150b030c07030e0907020d0e0103 84
    0x380310b00307610b00341c40005400d00c00410407403d512031440300c3c40071170a904003403100302a400b10042c1304462005525200b0148040303412615100140c60640700c07100481b20502c094a4904008048200e07800110b43d54600701d0f5480e5841500105c070203540c01580401005001071681c06001580900ca00c0d0040c2d40906503a1806c46060903906030712015540e4a04d0032411002c0518610345101c0b050741154034503a52105a80054001809a12214000c100c61214540c005001d1080442c7c8014246008112440f40200040450480c2039515035280c4000001503240d80c2d00460281003170200141c0d0700c1d030502400300b041c0c0c0c1c40509041e04100c0c0401c0a003840310b50101201425990460b22240441403281a0552052801502c4071056141c240000200803001000b8458070405803000c0c1708a02103014240141401807284120305042000000c0740ca00204004281c540e20901f8080400d24402012900079042128620056400b1200038010250007034080c4801881c02d01e414000d0ba09814603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 36291084 1250 36289834 36289861
    0x9060902040e01120f0c0305010903020c0102010516050c01060f2c04020f06030405070801020a03020915040807170316030e0405130c05040e1c02071703030f01050904030c05070e010501030e06 84
    0x1030072002585100130300c2d003042a0300341102c80180d080030200d01d580b82c503800c03e58024940c0020403005403041515480310781d4018014244250801030204140541801042d503440d803105030170840381d558645010661078840302c01e4001510310030100c407064420001d85020034210194030901903040f110100001a901e40c0c0507150407000c02ea4890340c0303a460300c0c60131354908034440e08140110b500100c1c0207850250b01d0350117402c020341c00301c49070800140781c228100210721650041079019041028240040d103547c1203104219403205044074071f444c41240101030785c01a881012000240020250903ca203814083c05400500f10000e20400001a070f494100c0544c252240d03c0c040c80d210f046012010805200e1112200920081705030703c13000a02c0000c0d00c0e81000e02901109100c05080c41c41c00c04c2c00002680e115030320201000003103034241410061441d1000b0012020403041c0100840002d07000c1c041030307000303042a01f03c00050354140800074003038949840c0114001d511110400035452036000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 36292334 1250 36291084 36291089
    0x60a150b0901020c040f0e070605070b0f061210060303113409050c090a0803030403020d0e12010f0605010806030a0804031b03080c1c030506011d03010204091509060902040e01 77
    0xd60035a40e405510006031300340b048140c0229401031401000c5c0c1080c18290300030307215420f004410f80da030740354a546e400c1d034990040407130240003840c034000001c1000c1c0845002a03008040140010b000180c405481441c08800c1078420b411581c44520810805801c071000c500d4101b500c40140843d684100340320129071f81d00301c1850040004544883c400d0000219090303014000450060120b444c0003849a00c89521542049005500603080056404000b005481c015a41a03020300750314026588110790b0000c451700c5003a0700c100808402000030764240b1420341d400d8030800001c079695281000260a10000506c00c074040c2d00a880d40e1000150300004540c20380758801d0210040d03804c1d08245d100c400815410080c003003803000403c0e00b00e50200080d09603081d501c00021480e0105140380031415680c09403206170210354085400d1074038402c1d2612030625070002800060070726940351000010707940008161b0522440507403040c001035159000781c0015066450342540703402d150504e0201c0185052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 36293584 1250 36292334 36292349
    0x10e010e1f05040603060b091b0f090604180c03050711030a050c07091d190c090203060102010f0c201b060304030c05060c04050f0d0308070e03010f0603030809060a15 73
    0x500c1220780590300c0e0080390002d0b10024108201058582ca8890300030034208544503c504400400500340d88401e00c2d80d40f0707907040711010040c146000c10b501c102103a00b0010070346610550610012840d4030b4003c030b00981c400300b0b41e0341c00b02c0c119901e000701800329800600013800f00082e0389400c2c48520400411190300606c1803800540e100d054071a580c0c140070790f5400c1510103070308100040c410900c007584605000380700703601520807007030502002c1e0071988800240280b9042c50060704025012569000d564801c20600021415240c80300000d403c071000d000194000c101c881c0c00c0400c01c40260b079110444506450000c0c041460344082e03034040c44400d80e010302d1086200000080030144200300650041e540034045a0315403e10440010071a00a8003409010742114a0150400e28203d00176440031909500c50040d41d844c1c10100703c8008604001064143d03490301c801c0d0400010a1041000960003a40d400c1030350f0407c4024035080039805010381701800e0400d104605aa80368242c2c00040f038560 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 36294834 1250 36293584 36293611
    0x6010e0f011112030106090902090a091107020405010906060f030b0d0b0601020a080304050c012703030f0306081203010806090a051507090e0f0907150c0f02031c020a02010206010e010e 81
    0x220340100c400700d1140441850b0750007480108281d2010b210059416135a10380c413541d03102a03e81454004a0040708103590b071009003100d04104500350345c0d2240d40c071142d6403010f181c641036490700818240e4070203a120602c2d00c0e549400410110ba407142142a03020b58034a003d02400540c940018440c203480e56020f44030b0841b810110740540e000304481c60300d00d42d010824646900d0203040c566100c180c0000000e011900ea012041600088a0042032031a4091601d100109083d40c40c121014440b20107084281680e070000440c80178070401c00300c0c2384401c050643d20390300c3d0b04050880f0304064001c0c0c14400d40c0e80c0440000340001c0c401180d03035000b042c00700f0412131441d910644200d5000c09240e00440803403280c40244140d0254440660307215200190032111a141d40d000400c21401c422048800000e25006d26000042e0803100c141d1075060006044138400070000568000c0c141000020401503400740c241e40d02196018800d45004003000783c0c1c54400340d89040b41d000410790004115104400d003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 36296084 1250 36294834 36294859
    0x10509090a021008090d0503010323071a130506040503030d020d020f0307030b1807090509040809030f0706030e0105040807030f0309052e0b0102030a1419081501020606010e 76
    0x4100304a221281e002869002c03881e450900c05001084c00380d440780314134003070043c0d85111240a2012281200da12070541e9281002c5030085000d4195a009007010f503020b025000110302e25903891614646141c031041e59a206100c200030841200365074003241c040e407400c0c03004204566010041e6280d00b0000e45002d03a0381e01c41888540d0081c480c07220b000030f120a0210910010580c10f601c0350036148419039514521609140c1c0c06440b4010444070780c130000350944001d00260800c9003080360003511400149080200001c0043d08228041207103480d10350140c03004020440d414043c40840007142802000607003041e40b5000b0151041d150064244130340013094100141c4290310004c6081e404c401600c03001d00010407980031000c882019020500d801000d41100a0a02c1c8075010040030141c00075072074081103003401d54062710121038101c8024820700a9a0040040ae55004014001c07076490b90f02d54130749203103c80c05140c04200010304640c0440100300960360401c000503080300c0c040754004900f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 36297334 1250 36296084 36296101
    0xc0d080c030f120103140105060901060c020604091d07060c0c0b03040f020a030506070f030203011401180306050703060303030609021204031101021303080a02060618010504020d06080109051005010506070b010509 93
    0x401c040011094000020b005519030f0100081181038a01c10082402c91020100c4001d00f40c039401d89400e035205078842c0041114a020f203040702103852000c0c0059040039034901580c0100c0e9480aa00b107412004d4a41000000d2424010700014002ca030a008042c48216100d0308181441e60103080d600620002c0400c090044801c0030607900d6500505a0846903102d03d00a501c1d40002d44101c0c0100700c0702003140521324003038026641030320b081c030141128a84041004580f1031281110349060301021030307400b2005c250540207082c822101901c0c003007240c40c91032400400b10f40141e80003c2c02e0034130511041104071203c41245421680501d40030304900c402a00300b900a12030100c10903071002080100004106000015241c5850180c00f668032a564002c103002e0342400080310441d0036800341d801400f1034036043d40035241d003410260340003c00c40c1d25604480d00f10b640c44842520160321044002e45d21140754040c40c0c0c003500c01030f0768560400c100c903a5040c8158106010f41d0340309002400000384102d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 36298584 1250 36297334 36297337
    0x207090b040603080c0f0601061b0605040212061302090703060b030604050405010216110f04060806130609021008060301200a05071509030908060a02030c190e06030a06170c0d080c03 80
    0x716041141c1554175030328555410b585e50000c0d0084005070043c90000a1074a0191050700056500442c82510070b20b4142e44044c020040104101d90160400190040d10750341085040d11969024030f80594600c880c2c01000090100200310000f01807d200c01406101603071001c2d0dd8100d241a0f80101c0c050303c4619020313001e801100c0710301000000f0010f095041c005240d09110201409032081c80d005c0c5040c2040c00150303001380c020719069502a034045604011070036900d0130b08500a890000c0d00d050181d0004d402c07140468002c0f400290b02009110715881c007071141c03403001460b02c81d1030b488118818205000a004101c20300080c0400410040700340600000c2000c0c00b440c3e881c40400118513030345406003040328280544d540902c80c80c0009841038849100f100d00400c5c0300740c0c0d86820001c14182d00f01c24031442101980030000600c40a41c00c079140c0d100914028850030001003002802d001c0c200c4241e092007030340c0b11000e500071a03600e48152105d0002041040e00051010b5646c410300d800549107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 36299834 1250 36298584 36298589
    0xb060a080414010e0c040b0613031b15050c06090a020a1401031509021c0e102c06090c040b060406030c1803030c060605030c1e0d02030102030f041109070207090b0406 73
    0x550030a400c801309014003040014800070100c0e410881036003001e0074847c06024803101c500ca040700da520240b004c10108580c10a01c1c0200040c0003105e00d480c1d14120b0009000c410144010a001086000d0210b0782804110760004d2480d005140a001940000c1d8810a182c404d90142200c80c44000640da40300c2e8205854680ea90600045a5940e4105400c029800485064080440510704640c0d40845009052001410034002c090801000544400038844480340280c800c1c1c03194a0780310b180d0701c800c060748145076211b0007500b4103140428140303007805000ca900c1449035160240c614020f40c0da80054605942c11481e00050b09102160140e804030803180e802c001c00c6811182c004109540b003e20b40c3d816600c00c0c80240603c542d0744060660f103202100801d644500f8090075030391012005001c150000c0e8008203090341c0c51509402103402c981c0181c802071440d246281c1084140800d241081869003401c1d0780c0e0340258542244001d4441945002e8144e9040d281c80c2c810300030b5562074102801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 36301084 1250 36299834 36299873
    0x91e020a030305220e04170307080a020313050a030e041109060d02090a03021e1005030114041113030305070209160c061518020a0201050601090f051207121a06040b060a0804 76
    0x805580b07034980105070b50001c546c1101c05080c03503008004241020703019240911103644501020303803240c1c01120f019400040040400d501100865000b041c5e0070051441041c2c02501d840b04481040e40520050380c45610340e0381d51002d0704201c001c1003a02c81c00c080705d0b1412a40c410050311190044001800785a482d800654049000d004a002d071140d10000f550500d81e003143c11004040300c2c0241694240401d101c0c485072019401e001302800d081075000b003e180024403003a6842d010148603000c104210700d0308141e0021f00045080300850924038101908510754a005103138034050048001c10511508100400960300d600200c401d0b007500324000c0c000303030042501c640c03c0740b02d010301000000d40251004500640c00e0074045280ca50189500740c050300c1d0000b15100e05d0504240910800c07519035040c00a451184040c00103802e0440d51038586011310407a00c040c0b000040c4084a80c0d0180041d2140380f0851070510b45a0341a520001161180034140c1031101503075039142841440c0307982e1a650941c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 36302334 1250 36301084 36301147
    0x3031a03010e060f06090f07050c1c0309060b0604050a030222020d050406050f1501050f12010305010603020118060507111c03020115171209030a080409091e020a030305 74
    0x412980220310359100b801c4d280c1c01d20000d5500e0302e0803c036003048140d60703482c140e031081d002160b141b0b4801d40c014021071880208a4081c7c1402e0141c4c98040c9051031382e80c80c0000d60b10504402081914041c0d45448a070444215041074200000101c8103907c40c4130080c4500751012618500c0341c048910448084000082117483e8026402d52802502c070840341203d07a2446c001c0041d80f00d8224900445c010405401c10780e8031135221100550301a4012402c0001c0450f091100c01400b400c14190036010b503116200204503603140d40700241078200227400d810704031040420f05005d6141e104045c0c45046401040c01a245003c0502003400c025881000c6200380580c44152428985c05421006000755003413181760260741c2d107822080001050003400c00868000008504400141c500030344621f410060a840c6947c189a850000741e038829400654800c0d25045050f080c405100c0c03000c494420b070180303802c40750301d07607540003425100c83d90000400b807100205284034441ca01d400c82d240d02252110304c4a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 36303584 1250 36302334 36302351
    0xc0f01020a02160504090f020402030601051209071a0301080606060a050403050102030a0501080f01140c070318090e01050601050f07060504061e0203010819031b050a060203011e050a06050703031a0301 88
    0xc0d10f844034a850109503110b4008000390f2414203104111400e6000090094407008507030800020b903001405442c10420706002c0c1d8840117445010032401494480001c0c001e16246c5a540c0a420380342011010114405000401501e000400d41d26401801196415500c219008050310180680d030406459507202000300614004a680030605030303060301d411201640c00070b4000c0ca00313a03800d6030101000780d1848004a010703000e104028125583c42801c0c200c81c6005994810031900b2925130050241ea51603080042d0010000e2044541040c803c1c07800a140c1416107000e0009841042c00c01050560740b040010b0030702c406c9911040c40c01d282141200008000c003000c02000c0d400a00418545004143d8003450340b4096640010312103905454444001080d12090080c100b030444055500e0700440001500060755440194042c02c03100c0494088100c2c140514a500c06207a00824001d9a281c0014009540c1100980d200e40e98585004500b4400045209078072a100e41c1040d501582411b141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 36304834 1250 36303584 36303587
    0x1060b040e04020411040506090603150301020a081e01060e01050703020f03040f0302091e040b070302071712070c030206010b1602030a0b060108070302160b0402061911120415050c0f01020a 83
    0x11600860003140c007484408005120703a1701038410b91251503880501040300e0001810800e0203164080c0c40703051115004843c4001003401e9038030201c2010000381216003005241e0011106000e46a818941600d00c40e6044c0b0b0f10150a0400e44400c036414000007207050000c0510030401c8961810308a81940d445603a50300c4131000803c1640001c901c24542100023410064101000302d91401c01041807210b5601d072922501042c90018024008064080012001107900070701c16286100b05411203a94400701c01c4540352490324054840010484120a1000480e0380054035a055680c42d00703920780c0d1380d0b90700002250000b1064000070f41601841c036200041c482e5201802e0700c01c400c01c0e03d07038086681c0c405400310200d104180c581103d405101c011f0701301081d030190001d9481840a0804d40c030b080c060050101900d8240740c00400001d00e04001074000c16014840d02000750401c2c894107040a09004855a00e41041c2202104001000c22034211901c41000341900c031203d034400865960b02a40300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 36306084 1250 36304834 36304859
    0x2030301050102010614090c07030c0b010e01090e060f0a18170301140d0804060806040204050402070b040c08160905061c0302070801150b0d15080312010305010507051201120501060b04 81
    0x1202d016518200001441248034200b59543d0100241031401c60303036648034401c07000c1d00024026405c000b0900c8070603000921640000b8043d021101200d0b0315903141c0394200e010b5880070801c0c12800d403c41014040b0004c8609922138010170907580209001d480344641902d82030890070060854100f18102d2220b00c2058001141070310b8010a012400c42e10300020700c804407e02242c0204007030001c100401c1045e02c282089504a03000070b00241c078155441c00040c2c140e80115400340c80c82454101400104042142420028009180a011901800c444c541e10f01a418032840c0202515800050700654461145001001242c9524540450903007002940c810301400749400c01e600e00005091003d000500b44000c5684030030606117403103040c081c1035001d0003040a080304207004200340441c1d000b6040c0090007400003204001c00300e942c55030400b00c5c00d5038000ba016005109082140c0c280704c0e000b010f801415902d40001044d11416141b034268010705c03084c2d101d60046c4601150204140c01c4010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 36307334 1250 36306084 36306089
    0xf040b061c0609061203050d18060209010f03060f05090a020415050c01050c03190b04110f090102061005300102070f030e010908030d0c030b030106030302031b060606090402160c0602030301 83
    0x70002c1000c0b54990605404032070060080740c812240c00400c80c400a441038004080c0e045044001040300e00104a009220720800c03007040b21110f03004205102156400703202100f6001d01807070280b21461409040301e03803450242c010580184500740028000710100d8044900400305103003030402221514400130b180c1c9d00315211410641d401e10012500c82c80c0340328292405900141e850b440a841c6902e101001002905040c640264403100c0d03c03c1141c031444080c3c1410f8064103151980c2c0d80444000a0410600a1582461117500c01d820b011580f5880c5214168a011f0100c405041100a0451480c101030403c41034681d800003a84c881003011140c8000074052090b00c607903031018520740055408111500030360145901c144400c2c048410ba94100028444981c1000030b02c88854101182c25180d06400039030150740b000074100355174138654a01040d1003072a04081c00b075500b4600000b0784188103904000e40b0903600420404d00d030460301429518000d50280084040c0c43e81c078000039480f1740091 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 36308584 1250 36307334 36307387
    0xa0b04110a03051605070312230f070f081b07020307090f021305090411040b0d05060408040602120a0503040f15020a0f0809030414060c16060921020607020f040b06 72
    0x2001138201c0b40c02141582c07a55907240d03da8491400c510551040104031005400401030103041000503003541411000703003e4000c03146c0d1982d4900d8602e2010744081c48143c074a9040126003410428500c0107202e48243e40740110b03503802d907035407102d0000030b1400000b41c202c00c101c036207007851440c1c20220a50041000c03424000b02618101e80e030310104282d1807000c507005458408407240c11001d40c50309500100c90510014178101c400c10391034691a103000d2081301c084941c4030b0001400d03ca945d404100514500603040c08051400d400d03054000c0003400090001404100340d00319000403c507070006150700320b00c040c1c1005c545403864010b00078110f20000c00c01e0f90115482c3d0000c250900c6010007220309950100c400c9c840050900d00600c0000c0e844802d201105000f04094019048000c000a00003094560b48044040d13041040c0015075000d000210207004510101a800588454069881c85030f011100c140030084074001080141c901c0e4240b05500040c002000c10b500058040207080070b0484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 36309834 1250 36308584 36308611
    0xb090102010f06060512071b0c0806010b040b07030f0207031a04120905030705130b101d03010507080f09011d150903030c070b190c05090103230a0b04110a0305 70
    0xc1496030110341c43c40c092000042c10070028801303521066041c980c0c220402d4a4445241c02641c0ba0201411040c0d000c11500d20140e10002c1224502c00c0080502420500e101a807515140c60700300d6400d446041801030074846003400301d001709402805910002d6270840b480725a01c40d5559035080c900c40040380c0c01ca80c019045120340207114422003140064510103170040003101d08007020000b0440c010070304003514a4584091600c00d44400040440c04802520b810080010000700c0401800c407a064190081c0c0c54030301042215540150416002032180080180607110000e081d8050709407580854010540c10358103060b007580006100078076580402c16501e003511a50041c0e5200d10040e0380050f030744007062081c0d00124110b442c0c0d40d900034000b40c2c4e5040c1d00740391880c0c1880941d001600100c010a0303003c11f41c00c503e0b5816002d61103c1c07080c010220540240260044401a4405450040703007a41e40c01280c085501d440e8001640e0b05035501070151070b20201c0c54018090441100d099098800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 36311084 1250 36309834 36309851
    0x5100509010e0d051b01060504090f02120d0c23061f0602121e040e01080304030605180d080925091103040b010e040c0e070309050706090305070b0a0e06040b09010201 73
    0xa011031241ea003d01642e50f22440c18a110541c10484981c150702d210b815580ea400010341666244241b54079079206d10708003141d001c254010021072551162581105412030000d600391580e022000d000d059500c00e0701d0070360705000441700c100401035100d070132003d600c55481841110840e420300d040b001105601250f200f0342d00d40034101e8507062504100e541a0105010312046103441c3c2c40c03e00310382c481030718200341455681d0700700d03074802d000a0744140c0894000160034001e00040c0e00819500031038014810b071400310303075124083c0d495524000003020440703080041340c4401401d1011010000e4175000c000480b41019903100055445849101111841c04052040d842c40c42c005485c41160403d02800490b0319007550070442c008000d0084407040140b91021414554114640e40612000c0d86c1c0040c0803086d40c90002e00d00701098200c0c00034400304502c20800071701c0000740e16090380c51486000303407105602c1400307a90800c003075900a0761051740420045100407a810140141500980c0207001101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 36312334 1250 36311084 36311111
    0x60213030c1a040b090d05070303090f09051302010809120706050603060a09080d0b060904050c090f06041a1c060305030703260c1803100b040608010e03071407030510050901 76
    0x50342d20541018180301c100a600d0106000c0c00100a016104099811255464905185064008034041014890280154103182c0c0400e8050880303c4400c01c054241040c20407010070401600034100032001c00014140241806400f007d201d540801c6a02d8008514018020b4081117814600a204000004003410a1402000041900590b09518041d035041034800500310b01e806007600a84d040044034240d480b507110325449009941f80d000d44402a034800c01040c1c01c0c80311611881520140300c140102c0340300343c0903040c1640c0383d0600107176241402c00c00c80002c1c51200000c05c3d4058a004070020600c0000300c020704019110b81d50b2402c0b0502a00c000c80103c4241d0001c4c40385a0070010001807100b44840e00030100007030401424007100c0302910000c0e1400c0860342c0902e08280c0c80307410030136290a017801400050042c0c130000b80710703203c07204506590fa030184101c0031b40302c4c9074001314501441406020490145401c4000e55400755098010000a400f0590360341c02c0030b6183c51080c1088a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 36313584 1250 36312334 36312359
    0x302210606090f13030e06030f15030a0302121305040204030b040b0a050f150d140d1106040b06011b080d09030906110604020103051005190509060108010b120c0403060213030c 77
    0x1060502d12504460300c40101138520008403440407400d020340110300c50916904d110107148138007100d03041c4c4405840c200744050102c1040d045885c4c085e0340094100030001e03401084401d0303d1311030042400d440e41345200c254a030b10103666005c540c200344001070120031b1140080c5114491800350120300b8064442c881800101c03841140c84034800001030340400c40b07694101c8609110500f00801c1084025901e4031801d00800740684c059001c1e901c800688051150400d18423940c62007184080e06081c42d040d2225055880d0040546040040350b5050300c283d000070b1070b80310341e0690300010b003640c450031041c50707040003080b80850a9000c07402d40b0400047c0603110300d44020440c2005806488592203590041d8084d0201412902c0404403c50020801e5251008140005030381214401e003920b00d4101401284640504000e04000d48680140004013804c8100e46640c401952400016990703881422450b004a80004000310f000080c28072036603640c0e0b0fa241003a82d01030b605d890752207a0b03280760a401c0c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 36314834 1250 36313584 36313591
    0xa15020c0a0b0904051302031902030c0d080306060c030708071a1501020a11060d0908090a1403060112050312010905090c040203090d03050a06150801060305070219020613030221060609 81
    0x881c0c82c02c10a4015508042d00865040f541840c0c9000c11144940d001a0500e0700d0b2540744c01c203512031114600c065181c20420100d001d45c0940b40c0c00070640709038842078141c0c400100258095640013602005405041040722b5800380c100176090780311121444d02e080080340801503a500001040082110001d0074282c1c1074030184140c0090410420f82c0d551440365041041e0420381c4028180080399840d071250280d018050b120700c0c0040ea60340c240a0030812852240c0d08903107041c1c000300900d0fa00340c1c3c0300042c3c4641550b544001040700e02040386000b80c03440c401c00483c0845401d108000203000c0155402840c02644150240e4203070220b503100b800100d0008903041e81b010b500c08800204a0b900a0388029000b0010103c007040094480c203560411400075010f80300021010401008810303818403074141c02c0005440982040043c6c1040308031240308608000e0b01c00c030710000d0f0007014119181c403c0c400440c0e0242000c80082032140b030300303200004002d0042c4000d0198100140c05031908510a610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 36316084 1250 36314834 36314849
    0x106060e1e0a0e070f03050f060306010b0325031d060903180a240f02010902010e011d040c0207172b050708070503030103020109052202180a15020c0a 66
    0x10002012241103080c00781080d840d90808841540030075880040000c1904c02e040d0b54888451028404000800b04c4800500400b11080e0711402e02203da41d001c9850b60443e00e40c0781003030743c49485000750525048078030389000301500485141035184a401d50081484026103403203401004c554402a9078a5100c201d030548171642003080541c1c10414210b170340007070300742c400b07004108416160000d00c030400200f098000366111040a00031101580031010808088041c8024440d0070482d5002030007910307401c0d91242c14080c2500045284080c90310011140b240001d10074450085024000303505da040074001c074007800716001e0418088040018000441310012182803d490850080d5116890f0740e44100d581000410094440400c40507000303005181d0143c80611380e2940b451002400340c841f07590000b4012015000c0c40d28a1070f52201d007000715405030000240c0c3d00c2105840d01c00b00711075400240c80d4400b80d201404203144c00103000032103c24206800f00ca90304e6030981e08106052080d88204607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 36317334 1250 36316084 36316099
    0x50c090a09030e060309010605030708061b13030b0403030b030a1506060207141003020906040303120f05070806040509010e10060f060c05030a0c0201021002040b070507051002030d050919030504080106060e 90
    0x20343c1c0703081000045a1010300c00c40000703241c07a00c1d58002070510803954081040c0758000c1c014485024050407080e6409100c01c043c0500e000b224031403101c1b0400300c0c0e100151110300580000340a060183d00710060f2140c00030300792a0050641c0c500740d80305034403603080460b0541c58414041001400003032604140c0e1500030107510110100c0301004075601c031450918003015004c1c03103004030a84a80d0081c001442c425240c91607a81280900a41186c40c0d00c0104843c2d02e082005014009421503030781034000e030302034170081450f81c3c801920b5405021410300703508940c030400c03015800c0302105900c403505994200b80b850003c40d0352880200d40c0c00305601030282240d0420044282d649000350038000c40a071040c01074840c03901c1e2a401000480e040360340850140000064840204003081c8180340140c1400c6031510340c843c030004002076990062001a04940d5510720100d15190401c01041850340c1a10350f00030703a44082880c0060071500148212501903080a40108031280aa400308002c1c280141009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 36318584 1250 36317334 36317357
    0x1b050a0314010e030f0408100207120305090a14011d0601031a0a150311030d0207030b19061a09010807020601050105030c03130c0e090d08010f050105030711010603050c090a0903 78
    0x140c00000c00305941e105640c1c0c3c1d10414004001030001c1c0561115882c0001c0c1c44038904101641024503082c1e01c15140f03841008128009048a65005907451651400090941c1c0f000f818030700e00034406002030f01d8490300032031905180005400100c004241c0444003079241d0b82041c105036840200380402403142c00f803080003a11402c45026003980c0704c6030306103010884100585c02c0c80340304640c43d002900c003043d0b0780b1205c0040341400c00c41c170350345001780d84000c0200c94915241d4541b090380180100700f12130300e40b0400e1118080c0d242c114001501205004222100814203010819400680641d020543c200d0018141a002040721070403110103840e80e5245645810307085904e644002c0c46100502960304c0d00c58085040144000007074845541c00d250f0070300f451107580b40361103000c00000c030410503a131005100c804e4041d807039a01103546c04e0800717070307181d490f144000d645c2c4040240c0e0b401030541c42c01d140001031000004076000d882906031117000c2d032038071422114816142443c101501240034805030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 36319834 1250 36318584 36318593
    0x31e1e020c03040332030301030b180a080c01060f090204050f1002280b070c030306081f090201020102040b030a090201080601030b0f0f0a1205010f0507090e010b070303140705071b050a03 82
    0x103401016a5000185c0310b00b02184130b881c1034030582c060004080381d00110061040101c40191660021690b038149020b2151201016985803000c80004101420120f060301d4100401d42004010f000e0400b01103140f01d45400c0b10000941003441240c1c818040003081d0101c50600e017510590300c2142e03601a0484a81c0303001000384010340c8601000c038003400611140c020851a482882c0141c1055403924001e902034140101982c0094000200d190401621500c140c0b02010f00308c80f0958000c1e601050002880c00141d00a001d546e0018414403c00803c1102010302c0758490f440c054800d80300c5e420304e900d0b444011012074205c840c4075500001c80e0300303c03c00349203031000d4040a0352100a10818085445881d040d65010802c07030112075a80d102c0064419480d03003130088680c007050038501082174500d804c40e9a09070030418071481801120004401083c54030075003003890381c00240c01d44030840381002c060042182d884a4030a40c1c1d603014044001e541c46006542450803664010042070206055885 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 36321084 1250 36319834 36319853
    0x91203190509030708030403030f060e070203120426070501060b090a180f0c02070f0e0705040b13080109080306041401030503030606090d050a050601060807111b01031e1e020c030403 80
    0x45000b072031100341306803400282d01100a6205620950300412107a1034500040117503a8142c021015044901d0100001d155000050340c00c642c1d80000c90340d06d1340c4c0f640e04141600440d169030a00410218101940801c00f003070000309409803144c402008256950307004403a0b240155280e044d4000c84802d4204605220155214140d8981610004010071074085a00031a07001c14042d001503080000100000e207510030f0180003c0503140b00c200c03281d00d4190f03001071981c03240340284114001c022600c80c819841e000c942c500a40b2041d0000c010a100d01d04201902d6081113900750302c105d0a09412542040c072081d0800d04a80d8850000c40c01d43d1207003000c00070a40c02c4580c060741c0103814000030b480440d07410811481c2180c0a500548400d5060510043c501a0010582414410400101115110f001512042c4901901c23040d000c0c03540240012805071540c15401d0401501c0c011100f90003000d0b6600030f41d003122407030054004040c0b01140f004c01f41d005020030005540c100b40000c0011410410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 36322334 1250 36321084 36321091
    0x1602040902010e03060103030801050f0303070f020103021b03040306051005030307170307170c030603010507080420060f0c06010f0609060903080306010c050f060609130f12140a03050912031905 85
    0x1446840514840f01207840e0941c03d0f1310640c0010000401046030b428102c419407074840d801c0e005140303455155290b250604c201c40a00034101540000c1801200030700c192440c82080c80c040940755610307560304050020b4a01a5240c219440301f0240000312071400104440e41c095200c400a0721038061342e402040540c0004240b40c042c840c2e09a43c1018180d4180c0c0554402c041c064046601d1341840c8084c1821508000d119006001c0c00307074244404194110142d004000f80400003440640c1403802040e13980c007481c03400f512054808109002199004210141641d01381082c046034541d075840103c0c1c41565611928006c0b5500d1401030001c100c03d08003d42e401070b41030600c0c4038135070415a0392501d00b10b0300d48070914144d0860001e001851038500c003842d41010548181007668007544d180c040011030000002005101c44855100010b030190201c540f045070760b01005074590300101000313000b40c00202d888005a00030b9482006846440030180c1e401088420740050010302d00c00c031058001c11018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 36323584 1250 36322334 36322337
    0x1101020903010e010f0506010302030408030109050606091003051b03060a030b15060f040303180f06052b1a04090c06080a020405030d05180405060f010c020f03070f0501090b160204090201 82
    0x80100d103030561003d0269902005801c00001000d079240581102125809441c681c10540100244030118620034142e234151201c1c00c600007950749807040025450710886070116042028803460192450b05548014030452107103808281c41844211103800714030048891a9000041070000d00205601d20f0904d50701816040c55821408121800201250030846050104100000b0306108060340268041303440c2480e40d0750307054014140104080f5800b0b09000d02c2c820003001040317003000e0a11469140030023801d030070b9070311075401c01c59a40d0707201408007620203040150f01c10100b03803610b0400b84180d00c0744d01e800001c2c0d4000349083c4041120401d102908048940b80c0030700c800305d4280d40900c031a80d18401d403074960a41d40d000001d00130b460041200318851159103003070100599078503032903201360f0b110001346010481e142d074510016908100107104550540328102001c5081040c00c5420401e6482c26200c1c844440d680d001c4c6440c451140c017040700b2117280d80041007401410f213600800d544a105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 36324834 1250 36323584 36323587
    0x2010210020a0c05030c07080d0801081e0a0b180712020306180f030406080f0a0c0e0f01050d0204030501050106030b190509040609060c0905011101020708070b090c0d051f180201110102 81
    0x5a40700d2605d5504021041d00264104400c100040b40b8100000c4441107000e0071300010a40c9010b1b01140c5605820014098003444494001e8180780103000302034400e94480014602400d0400030090326080110b0b102c0554400c4101c00710321107040e038807055943ca9000303008041503901e20403012464010741483e040d007445654140c0300000320600240020301020750350500740d842d1541c0e10355a00f030030282001425502c0d0880c0d007424a41e0090200c00100001c1c0c400038400070141c401220f051180c040c107004181c0c4082004810004103400c424100c4007181d4051068080d01020051450640c900541542244190400c81418a00b141541c0203006000c000340410180d201c810a44003030285600c00a0f061420502040d0b0f00007107042044000030008600f407181c103030b981c41a144109c0001800b4010b907940000c0c004081080f214144410140004e070030254140b4010f562540900807985108020b400c102d603802456100d001d03400c0c28600d034080313120402c50300191118800d011011005540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 36326084 1250 36324834 36324857
    0xf09060c0c03030304050a050c0a051806030c03011d010f110307030b03160303020a02010f02010c0e0607020604031209030605060301090818040605040606020f0615030d1107030b180d08010302010210020a 89
    0xb4240041c500c991302a401400d09404580b80c05410a10403400742c91094556920511650302d03040c01d5100400600c052001098861200092a02207a520307003540c10740c24100c0980011354078504c641000e102d40c600130b112680017405140c003911084401611940d405000044010b4803c0e0441001036030043d01341c0f41c2c8411030300d03481043c9074000c1d0410342c09079006400020455921899440b0403080760701c000c0025541240c00201203100024000f03100e00c3c40403404070306568420045a005641c84072010602407075810f000340001c2500d00c03042d10030300d00e814000f03409400c041c0100c0e010b0340c2c0d01c01084c9203410b8250703d101f03030a840340701901c6070803640c0c030f41000c905170700d0350302c510710180c08990002d00442c403424000e50b1401e070000740b2071800c0e0004840500304039200020a07010380505410400c0b00d50041300d020328940a00790344054118850641403000c005a0310b40c0301984c24100d101501c941024201701559140001c0c40001c0c0182d11421107912495130b182c1c00380c0b20341600313407030b000b45441c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 36327334 1250 36326084 36326089
    0x13080c060c0a020d060b0402070602071a093c060106020d0906020601060309060b1002011a030a020a06050702220c09060203090306040b1b0d0c0905030d02030d1112100501030c03020f09060c0c 84
    0x17009427070110346459000491806100030742c030050011806400c13038032035140b030840c030480d803180443e40c00005d40041c0081e1701100c04103001342c0c107034948003017890b4201c4d00d0f00c42802c0f42d607880d030081c03181e44054011006041d0003d031040070b41c0c9090340c002da001000c10380d00c7c012080300107041d4404141ca00c0d80e5110101c01e0a90740320041103400000b554004117071148802c02c0130070220a8054400e10a9202d21220b00040e03c40e0070a4000300c503a6401c0a41d05c03121a8001300341e0081d400350003c0c902e80070100203100308244550101c41c0e019526601c0c100d03119283c0405a139644158030f101641588150700050016500c0302c078155000e0030800307440707070042401d035010030040c1c11040c28081982c3d115101c0001d8a0f82c010500001807604800a10041b08220000780d1284500d90001400d2a143c2c4100358680000401322010031004950003042071a205c503501103031702802c0c000c1c28002403d04c914159500d1081c000d84a80d0f04c1203404041ca4020503100f085540c0d8080c0118025502803a070941c001e42c1e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 36328584 1250 36327334 36327337
    0x22406150a0c02010801120c03020607050f070e090c010f1e03110a03020d0509070509010b070309050d080a080a0b031207020a050d080705011103040809040207031413080c060c0a020d060b0402 84
    0x449a60302d9102d4611003e10014000c6101600016246110040d1540201d091141010100c98042e40c007a996203805040c06420401440791200f01c500c50302400090300810001c2c0d0303c0c898080e8a042e5400c41107058011a03000390075054110000f261180300a9209840e041c0c1c0085440e62401d0001d055661111140b45507001090312401190380072072441c00481c044d018003644443d212f4060801e00c1e040100083c1e18903410300a4800c0883e0100312101054000c0514502500700201100d098400c1407074000380c9984140e0a04c4000346e01c00010410510203070240407840311004005d0000d20016001d010700c1a00b2000040c2d030700206106002a03141c81e4160302c2040c40303004604142d6a800c2034181a802d642000c2c0c0c16013040d010400c200300c0458070000689a00403c01c07140584e0b02c003580c3c20126036030700031260071a4140340c001038644c4240c01c112940c070084800308001c0d120808029010050319028140d04040d60b6042144010018036200e049610014454800040c8010181d03000c14104e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 36329834 1250 36328584 36328597
    0x30b070c051c08010906030203120708040e0a02041403070e0105060705011506020102030405070e01030809010318060e010f0c020601080a080307050d050403031d030313081804050a05010302010e0102240615 90
    0x1071001e054901000b9807010f1102e02410501c9401c2c4003d51559001c0b80e0307944a031280c080c1c090b440100e5410200500c6108072030080c800d40900f01914203101290400a41c428442e1701c4a240440d04551890304000c03651908841542000d40c18507842d140c180300d4103a201c4903040310355558030702010420a44001c0808080c01c016800144c40340351030710301a0320706410364010b00315844c400801080020f542c00100e9896060a02e00810620303651a0302413800c03410040020540f0303041c21381c00c21860805611603080038607042c809102280c1c203448103a803140c80038041c280450300242000d5000c10b100070000c0d50820071500c2c1aa00d01850612407408580042c0c4003240005d4071841c5031800c01d1a41030031214a4181803018500d07505080c0401c21180b44600e03401090090040f511440e81c1442c148203800104024005000303d141040c003010051409000407404584140401c030140d52002031060036401e0015110107420035a02c5e012142d20074010403240d8030258903030341d030f4141d007000b8005080c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 36330940 1106 36329834 36329863
    0x3041410030902120d0305010f0302060702040b01020708070f03050d030b011d0f0d06020702130504020d0303050a0b0a09021b030901050a0804050307020d0507031a060604030b070c05 80
    0x15180c00302d0043d501c4460b04207091280358010a4807042c43c0c03407984d000c0045a80b20300201c1d664900341e00000e900460280041001410f0950120b1180003050040b21016581c1e4501103140842c141c02ca038200c01400310b01041000420000c42d800e17021141424090a0100c800003480c190301e50f200307189445000b2440301e1864484001c0c004000034060408440c1c4042801c100c80650b03c4200c08074060342c0b04603041080c4413a1880364500440d03004042010641540d10200c000c1c01d400340c58099060b65407a103602c407907925120300070002d0a86d40009a05c443d140101110414a08483d28000d50020800501984e911904848249045041c801d0194642d800c140b443c60080c598000e400014203003589051201c006401e20887c0d200d4068560380ca8450611404400c800751001a013003801840188009040a603500d54040b40320b140c9410780c210036407121460182414007286 = true := by decide +kernel

theorem cover : BRFrame.Cov 36151084 36330940 := by
  have h0 := BRFrame.cov_init 36151084
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36151084 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 36151084 ≤ n) (h2 : n < 36330940) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
