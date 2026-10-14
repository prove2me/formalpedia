-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:37:11.229993+00:00
-- url     : https://prove2.me/submissions/afc8d133-6d95-4b04-acad-caea2467d04b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555035971 ≤ n < 555215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555037221 1250 555035971 555035993
    0x207090213090e010b2d0d060c08010e010b0f180303070506100501051204022713030f030614131104060522030c090513020d030e090f1b07 61
    0x185401045440d90141c0004a0780308078107105150b4558140290140c10b07003010302c14990f0800303004000f0007035200703200626051000201000e42d00000e0610002420741c407080080000d8038414880084c800c1d00003880540384000c1a0031100d031202e04100140034100d00c681c01c6440c4400100161078840a01c0e000980403059204030407a010302001c200c8200f080700c00241135000d020051a02d0b580c1c00d032901f00450321802841c203081e100c00d0f54400418054208420f0003e074a07518030402c01c034074107940121503100b2041130b5815403503985003c0d00c035014168866108041c0002900e4184181031a100d110005408071040300c0303104203048510000841c40c9030340f2100c1c4000140c42d682d62680d6035004081e1040d0400c07204080e203a0741c001c180104040079014113a0950b035220b03101480840c1440f9941d002800010071100307000f1100041c04016a80304120750030524440da45c0d1006264420301449120740029104c803800b40240014407031060b40e8481075100c1c112000c42500d455042900700100294 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555038471 1250 555037221 555037229
    0xb0705030720121b01110307200a0206040b071101020613021905091f050f1f05070506010f03060e010501060f0507020d06052a0301080a1e12020105161103070308070207 74
    0x7030002410b0041c40ca407200021399184100000b000410222000824181710403a007010006044012250301e802103c4c901c00d540f00d40b680c007201c90745512680810034540c000c1d0440e01e001c5002080ca18200004001c1402c072888081c4040d0502e4200483c0b1440308200c8c12500070300c180d0003261240d0581400304039a000400004207250040c0c00c00312114250324401203902c174940c407481e072004102e5040c0500700068440014041540f190721113141031040c0003d810f0042c0801000308000004a0000c011380ca0103454403d8485170614990319101c0e0846212024501e56070341001c004201d07040e005028540c40d95054244290360320224400501e441e800501e005002034909000c0c04481208000c01880b64100d6a070710b0110992a840c0c410428002441440c01d1607201001c00c100144200c0a0781011040806010700c61150a035103401c1000347d000c035a0070040c1c1d5500204138203c1e4450032140b13003400090501e004580d05100d20545c40f0702c24240040d0503c81c4040100703150610810540c0010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555039721 1250 555038471 555038503
    0x504030203161101110a2a09020c060726040b071205010f080f07140f040603140109020103150302010e0913050f06160e090a090203070801060605070b0705030720 71
    0x18960a1404000481440a0440c00100210501c1c141c010002405410b00c5400040303c8481c4258240544a50f81036100800a801c0711f4040016103080540090000c201542c2c010300b209141c00d450041c1022441680c1c12400304413840d80e11000d040304022640c0054000300c001d84195500a4140c0d65200c2070854100d031075150100000341c61446500f12015600c4002c240c030005651980d049940d48124002c0b0a501d41d00041522202e141c104499a40e00c80003030004111075039642c450041610803c108203030265141e028600031903926101e00182c00907440c0a054030941503400007025a01d244061a018032059004078540c649200e0214049640c401c04480d07104403181d91032503c81206a03003010f02c15072500b0014034141e00407501440e1301c1e83c015164044580e9401c170352201400441e41e003070b6051300901501182a20f0f082c081c1d2400307450f2076292a07550f50350070b24060700e40800041036001081380a0040c401d031983d010180050442c4240d00f100040102c0f500c2c101e08040b0542407428075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555040971 1250 555039721 555039757
    0x10509040f02211506090109120c120809040c031806020d1407020f0c06030115050a0327030212131701060f0314011422060e120702090c040303120504030203 69
    0xa008070350f600b81403054280c1885003401007200002d00060b80540454a40869015002030020702c0d005699840d105014a64800c102582c40b4520809400c81210a440d00300b0002041c1a40341001e00034400b0018442c50308001600d042c402d0b202d070098103048020180b94001408080000d0b0942200e00c103180b80911079070407402c040d00040e54400d10400114114020755075071820614080d001d80b8107c44949a9413803060311100f1046034182d100316140018541d03248400c0500110120115504031101903080e066400c003820003a14009002003801c0381d0700c008001c00000b0140f070716440e0741103412011451044560010105025081c10b420460709061004000024003c009107110320140d0220300030404010703e000702485004045508420040516008144070f0300010381104040340a000001800180b408440b8101483c00c901c1291940000c11140154601840081c4d00030040d90604c07480c1525581d80503001b8aa003103210701110f030b5a0740c005001d00d0700900031107600d01402001050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555042221 1250 555040971 555041017
    0x50f16090b13022d04050a0b0703170106110f010608070e0912030f0402040e0105070c0b07170405030406020d02060114130e0613060513020d0b1503060a0906150302010509040f02 78
    0x321a00d11080390700505001301d0118404108108035400c0d200054100c42d58141000321800096004900840c100303e031005005c0c1003202010b01d8103018080c0d581d1422160104211100d01d0705080140003c4181d24100c4c00f040032000000c0c1c410300310780304922803c01e250781d03008034107040141c01e02c00c01981480000402402400405186110302e100321020007108112040c054200c072401c807070b40c070042203820042d0310100f1000e400c260f0b4000c00c00c0c9040304000c5001c0b5009914440151000c5981c0c2c3e0000c02c0c2130180c2030b01403140728900c000c0d0344002e0140c6d603d04021a0194180c00c000c003409041e110440800702612900014980008041221503500781810803000351180000240d03252490480400c81941ca100310014181c1c1d001404035024041e1500d0740d003501c040c00f404024110700c0041c007040c41914144042c9103c5e40d1000e40000e41012075003801c8040e01e00400f2100d124111820742807005030b8000d020798509440030750b800142e02d09100c0401c0020310400034003009621200c84011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555043471 1250 555042221 555042247
    0x1509051003050a061401020d031d010204090509010f090317100911190914060f090a030f050609010c050301031520071707030c0206030c16030903050f16090b1302 71
    0x280030300d079883c104110040d0703202a071032500c00c4840d04450050b0065211240040d100b5082088201d4281d2040e06210787c184c025242261b109078814001c8075182d10401003841002c0c4030b180f4514a4201091201060301e6500400d080240c0c0100014810000042944800c1681c8400091709028200700045201e0081c030f840c441c1c022112039404540800d9104650500c213015060803158400d10811f05d088040c01005066040110b9000c15400c003880b1030a00d039551090314a0007180a81e03181e441e440d07030500f0b00608084000384140d40d145e040007d000788082d80314085034116070b0440c110306414440c601031040907000450035442003146c034001407008509008020002c662240014001d00911000416030a0007860400760100f079003407603540098246500211b9110101e00350f0382e0700d0280c0035a080103000038025001d0b000240640c0c030602c00c2080030051060606c10f10802005000241680d0b0301c1808203074002c0c2c00c2403035100c2a2a111036114111050741e200d000c0e030402d544401d5102084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555044721 1250 555043471 555043481
    0x4051011191113060f0504020a0e100c150212060405041401050403110d081302150403121709060f0718120b0f18030409020915030f0109060b0f041509051003 69
    0xc18482e80e403984201e4110f080394411a42202e080e0035080d0344c16131401040000030341014000c98180a10f8011401c16541e440c1c8510590352140d499240b0804841e00300b081c5026040001401d210f40304011680d40740f40342c840e5460f40b2040481d000310b00d642c0d452030501c0c0d8040320580b0310400c1c5e60810781400101908110210f580d002c242003210309440104c0d500b00c8566005460b0761400d851903034801805800c250405203040040740e01402d00d82030b0740340e80e00042207010102d4900040c2c0f4503155812484105c1d6801d0790082000780003044182020354410500b00409060307001401000d510164840041004e0721001702005440c01c0c224081034282002091000c0380c0300000c5130030460009800200a008441d4400c413000002c41c181070411a4020082d0310000c07030164400b880e8046038114030582001148079043ca40000042545018607410550705c10303070000340003000c060210081c14044034040c1c3d0115500d100046404403005402a00c82d08190b800141d007040314083d0050b40541c00d6080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555045971 1250 555044721 555044753
    0x2160507080d2c010302070b070810050a0b030a050a06050a0306050f1819060f0f020d0c020601060509090a110c060103050c150a0809010e010c0f090b0405101119 71
    0x1e03960745281c420002c6559240019480c3d07042c803a004003100603121002d0301649403a0b8181801480c182441d211000c000b601110907030b0000e11a0f40803c5040041080008000c260540b055000281004005050340c04008c0c801400ba41d0781d0400181d28480603004880144030203022459500d0300c0c2c0c140440900003ca80c0e4142d04825400451400300822168610341d40e820805004408a0150f0b11608081d5405c41554166282c100d503401b844528401e1024203200000e0050b9130715044510002600d01c00c0e58100155000b010041028603040760407074145c07500458110329159544500b0314010801310704040032010300071440e0311003c140015001e06032805403007141e070040542010410407401c18815150301a41c1407002c408240e006000c0540c014601c0c500114001048000b00303802c6828040003000013410b000c1c207030070781a030300a106000a003250303e5480c0d1400c2e040c40045280720071000c2d00c9500304248602289140c1001b8000d418107215409503104004580382000c119080c07407904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555047221 1250 555045971 555045973
    0x4200d0903030509030403080f0708040503070e0a05091507050703050c060a090b0a0c0e04020a030914070f05121209190305101116061a06030f07030e030a02060c0d0216050708 77
    0x3c08a258400300200361801c0b0b0703a011080c2c87c54440d83c0e00070328003650403001e0122055201408040761a513014480c08010700003050854005182072070007001619005020403869820140880b01329175001c05566900541d00d0070400d9445519180c221424417403840050728600a0f0014041581e8064220041c40c90044e035840e6060b48600c4444c41c1150120806040407030411402c5040b141001d4003d0300c800400c6050005244500c0e8803107040c007980c00e03a54586250065002800500000798214002e0102928100540241c400c491030f56110001c0c1c00080d44180401c3d40400740c2d5591807030b100a003030f010b880309001030354a1800560310346118030000d4820341440b0312003030700004210503201518a0545203003e407040135180c03100244074200841e03a1540641890341021b80710100118003c0e030804100d604a80750240000f000c4900c041190b601c1c9400c100040c488141e400500250043c0c4648156039440300351000d800000c3c8940844081c000e000f0902440074048007088501c11108440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555048471 1250 555047221 555047231
    0x11401050307080601032711120c060d020c01020c0d0f02010501050f180a0f0c0512090708071a190e0406051f052a0d12050f010504200d090303 63
    0x5005480602044410000141c00000021842c0d0f2003900000c1c0c2c50042e000300380034903190310403868003240403281d025a840d08194498610f14109415000c1003054100c0250502c10038520018100b449129400714089402040f42d5041703403003e6040310041c5c03411608a40e035010701d0b090040c0001c1c40c0d403901da2025500e00340c0001158148600c80c10082d0a00030928940c0b030b152680103510741600030708410401c41d900c4136100c0340c481640c410083c000c00b65844180cbc1b20180c0c0c80003601101401003802069400c142000c1080d90000203d04055580c4c0b50303804d1005d4107c10700034014600400582c42146013150a940302c50a400418107505103a081d80c0600c0800c1d02c80d402c0c03040b041d114058140700b071036020104555191290f8080d05403014071500c04042c1000c100e144000344203503030a240d1065000302c10b409929542020f51584c044400d1802807040303142c500310300d003a41001441483e0042c1d0700d601c0c0020444c0355041c80501d43c200104650b503200c4284104410013030030b5a10301100843d10380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555049721 1250 555048471 555048509
    0x120601150201140a1503060c1d0406060806010f0e09190c081015020304030f1a07030902030604200d031e02070f1511010207030302180f0a05061c050c0301 68
    0x6014480340c1030007844040c0071945464113458000c004240401c4e8880c400c988022001640901901c03100c0c00103a43d54110300c9416189031402e002e80707081041e03ca1458200108000c9810070780070390b4484000d080103000c10303622410541d00c810502d20031941c002c01580400c01c0301c12000703440d8801000700072410041d011401e0410b40d4402015544440b2200b0b09442c10000c01e081040c110b00e402c07002e441580d040c10b590f90b0f900e0145030310110085605000d04c4034140030802005c0b100951000c518076060182c510b480d004a034171130f040900090140780b805c8002c14805490118090b10654002d0100b00b0b50503090b040040c1220f410f2440c000340d20f0080090ba100e80c910019014003501c2d030035a01503d1f814070f0401001700d62062182608140a101000b0700c20140d0700b0f1010b032224a01903100541c8e9540402e001e80918159a04031a12500202041081c1074907500190300c02d650041d01c0c05507540940040103148802118407540549090504200380505541c0c081e43c102c48088445004000d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555050971 1250 555049721 555049723
    0xd1b020d080c030a0e0a08070203120a050d020d1b030c020c0a03050601090f090f0501060602280b0402130c18090207051c050403020d03031a062110051206011502 71
    0x40c0800c160009100381010581c80240c890080d900040d1051000501091580700c580c20840b9840054900b984085490020341c181444000024107944001a01d00f90707510780098890701419014004495010419080b42d100c158007002e41858a580406584040c6030f87c01000303440e205030740c00018042c10b0304440803410640130300d000f6254418094500c81c0e081c081803100804042c4500ca500b55141c07a14440402d05500040e0003040c01280089102810000080e24008642800794003400c800104404180d8103e16507414107a409001050301c0c2c1c50358000070f504610b2001c44111210f1401d001d007154103401c1302c0c11400d84030340c24000d81c00c042d65941c4540102c0c01500c001500035003041110320100303400048100035000541c03c15a0400703889401140c01054940411030102e99240040905504219025000c260044842601d000050b02150340301e0084240c403499000d40795030214111110404c0044041c03c8080e080d00ca560301c81039060f03940c5240038410510524502e0b1708000220388 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555052221 1250 555050971 555050983
    0xf140f06011404020c1c0503070807050403030c020907360503030a0c12090806161d0a1206060518040b0f06090c0f130f0602010f06080a06090f080d1b02 67
    0xa0b240008000000c1e00c2400e100c00396100034000040342c00b540e41940e00ea95411400c0c130b403a8203844c0d900c1c19142c0c81d0402e0003034000b40c1c0140200e014401e05002c00c01c00039901031050740007140d041d0740381c00c00d0f40c40d451420303503200342c0300e0031a00c040f14404801941035081040446415a9003901c104550a5541d07051580340d205120081340020042820140411501c0e41c816101c51101d14180900b19a15500301342488800d0307035802d81c034807151000c3c10311180d40500950350399510040a424550742d810005913102480340300340d520038100c02c08030300d0030300100e03501c2800201009043c1c0d0601c0318102003801c04142c0304640031104030448001040c02c01407034142c0b40d0300c0b076070006c0c0c09216203455081048681e81c10000018241c0300c03040001180c2540786080381c0000744a02c402120200b41450006400d403060b41c104400500e02c0c00340100042d80340010035030803080d00068000381c00c184c2805d01c80301d8104503140161007120006503018003417400382e0104840300f60701c0410800c03e0322181000ca8881d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555053471 1250 555052221 555052229
    0x909091b0a0e18030d0509060a0501270b040e10090530071415010305120c100c1404060f120b0603071107080a050f10050118180f140f0601 61
    0x101c00103580e0540000360400040f4a241c1120309240555000c00c06aa20450780c14841c2c0d0088004e0040e45c40b82c4d03015043c0034004005002c1001000c030843c0345107a90704c0100fa00f01080d01d0708104020b41d11141c3c410050001d44005550080e00e004400d507002c4e08101d00d003203505200d101512b060102c0d030f0003540d0702c3e20031081c01c150141b0513142d00040f0789034002c51b83c03d4441011080101c001014104060b49410380c1c40f44450030251301d14100741c0d06000b100158100c22080820241d10391000100b40e207174800f0340701c407000544d070038480c1300817030b914401c2c800d00025060b40090040b44068001001a2052895a45003040001030040c0d08042d04d81c104040c0350020824008110303914011504d01207440751000444501c40e54504030240383c4500541c05480075000341002d5a90600700380001014848194400d205039413400300c021030100f9a40c0310400105507140e400c035070303400c24540480084c4e40d00030082d00801425814407602ca800c040b403c81d001e038800c0601c4056100000b2071031604032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555054721 1250 555053471 555053489
    0x1503190c060207260102130801050402010207050f060406140904050c120702071404091a1003020f0303090d0b0405010e034504150306020f07030f0309080306150909091b0a 75
    0x211194900c4e40c2c0e0350f0350405030b00c000c2a5400f402088500a408201c9200900420b0004500c5080a000280c145003041e000180034074559800c813040c82c0c0b01c06007150111516490308141c404982c801300043c03401a40140740c0d00034246002e000c0b4004008028203050701039210140c2c11a21040d40580e90b40029105540d01d0440f820f4500078a490184c0c0043c46090262075406120340c0e90a2004a9602e022588400301d80c0c0580e4080c81913007030805110034590001da0040d4949090100046c82050015000400668100c00040c040100c290010f980321003c000890752145101c0c0c86a2200748001e208800d6000b444030b5007102100b01c2e18001c10f001600c01c1407165200b07440c0303505200151850b42c4100b0b00200b1513590001c0003030428402040840700090000c0d40b0f50300c941c5030003041c240003c2d041d03d081504180c00800032440c40c004503900300c08111904201d110095135100841c0c05410010750b07210515004008091b03c0103c3d18018423030f205981070200c1426502008403e1a10340940072030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555055971 1250 555054721 555054749
    0x9060506190503150712060e1504020903060c0a120203040c0512010212070e1206010e01030209060603040c060f0c1a01090f060f1503020c0316150e03030f1503190c060207 75
    0x32126400b480190051484d1810b2106d41241e075114105030746e0207520a80c81e242d1800f00301b20088060200206070014200c8003513250403842c10010f41d55080203030001a0780880010704020982c020241c046c0500742d42c030700654481c602424959010a0030f071066900038a83c4507016110a00103108984060b001005040e03642c5c0c441100481c0d4a005030040c0c2c80e0007000c440c990070656202002220700918903001850190b40c1984180004030001500c0303503001e00403d00600c0700080280c1600400e441c030503d041c01a80840300b40c11942142da1800c05450352400800a81c42c0c0060603c2d45810f0b140180818440405902600002c841c0f16128000d44004440814000c0c074403420643c0b40a50003074a0058103260a491405040d540308104581407155003031090302c200701e00d14200d80340c0109880130400c041410010101c0d10380c0320041108100c80e4401001a00d9010310000400100d0006022107500d0141144c00300d101c0400034900795141c08801a001842d41d1000038036206440100b81c860fa0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555057221 1250 555055971 555055993
    0xa11060c031b241b09010516080f030403080f2505090d120c03020c01080c2a030d0f050f010f030f050312070e042003131509060506190503 61
    0xd410034102c0d0071509401000d200705020962101e024001d0460312078054032a0903c90211582c41d0000c100b0080741c94811300003600503030b8000c0c00340c50350b03005046040307441913003545448078582c4204000c070316210002109002c141030b030005032148200700d000c1c00035006444419803601c41d024200c3c3c4c0b054035420526003d01c02035100e040075003079480000d000c94401103129030300d0001070400d44013910009103c0030b00c404145a070410803800400c07020300b0301c6082c50500485401092042542c1c0c005044510703225100d08401c0100d000358004002c40940342c55000415042020b4254201440c41260a0001003440200300e207005c0c50407602d052240d0702c1d40c00c0c40c50360750a00c2e1154400040d965070006012290301d80241c84d5010384030b5500ca948840000b94901c08010485c0c840400340d4035280525012040b1604e201000c80b50808150072103034000008900c1d104400f0040c00050a02c0c041c205041c0034204900342d0025401007d0894a4100c2d041c00c0404042885410348a400c0c4e040e030144000302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555058471 1250 555057221 555057247
    0x108090607050f1b0d021c0f080601020a150609060506160b04080408070308030414061504150504021201170f0d05091f11070909080711030712050a11060c03 69
    0x2003402e0b4a492a00300f0942001c2c4d05080c00c081c81c0040c0d603d41001c4201c0c02400d505000079001c0001d0b0051214207030790b00381402401e07101b03038164410030700002c0004180303181e0013007000700f0440354032603803250b0a0050019040082c000600c200108903040600110711407521038140c409569140da015041050f8a89034041c0c4480040c005445903e810403000c540741c40d0500400d0091400b0b4004540d4900741880c5c0b0340301084000d038032041d00341c00c94000c1c8525207460701021000003800306c0d0302180d688580d041e2982c9550f40c43c2e0026504c544002001c1c00903806031a4028121030040004200340d40c4142071040c0c65030944c62540c007154211000010030f0a000d04050011140f0190038050340c442085040e952440241065001162501595102401c010040340019200c1244c09114040696607200038900452600400c00340c2c007070341c00c143c080d00c040003803034001e02410042c54001c035030034140b0580b070364000641641c10180d00c115114190901508460000030344100661902030340840c12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555059721 1250 555058471 555058477
    0x140f031501021903171302100305190207033e060907080a0b1902070804030506090d0e01050a030e0c0307030c030c0b040f0b130306110a0314040305040e070c05010906020403050c010809060705 84
    0x10b041b0003020341c450316015071980c050855020400b6180001c0714200314200c800410688624040c000d4010024440040c0d80303e00400d421100300b1510f6450030a01503202241e00c030880450503400301c0000030303d0034500f0000601d01d00614200c01566484c0f902c8402483d114603400d5800342002d134100c00416081e030414040003031000e059640041c01e0540359610f62107587d020b0751040d0b42c03a90007602404180c180c01d01034404a0000c5040c140f403242240740020700b45005440701d80307040c1507540303010300c3c140d240501501b482c0c071400409031050517841c0d140c0b01d0032842e01c50000350b030840c07000c00c0302082c201444001c0f50156801d0205048246241c1580da81160380030780240340c0c3c0c0095a020000005405009070801c00d15642149a1140f10132603000301142c12840b03502c4107541c5440c0500010070f4101c1c1c1200e082d13500207031110103d40c0e40c0b02d005540f02003142d0f10003005580313000307201130600c1820fa01078825280b0920564a40f48900001103503c283c081e40c01c1e00d80b82d0880004980258003c2e002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555060971 1250 555059721 555059731
    0x405070e0f10090e1008010c0507061508190311070803041a03060904020402091309031d01050715021303080f0406110d021b010309170301090506091303140f03150102190317 76
    0x5000174182e04c4586090075200102072040100307001064007800c0204500a0702d07250040b074480400041d00d0590303079680d03424403d45860788900440c56011305141c8034441c00c402020f41901102c501c1c0344c1c0e0f0b044265407a4854402c0d82c5c4003202840042c0425040b11003201d004100080c8a0b9100c1d8449030200300080d801902c082d5809540000c004001c1102d80c01a1403106000ea01c424601405a4048908001600449904105081002c0f0002030100300200c07402201911005840300d414448101c8140c0740c50b000a84900380c003181602500c2130700070041040e200a0b0751489001d0900b0040d26980b400040c00710400760700b00c0d85034100b44e03012803403d286003104145070200b440101ca8a41424840f100e5600d41042c050000051000300305500075260483d5059030014294501900131040d600500300c401001c0048004030460703112204400d1b038200840d020380240c1d607400c040402d100d01e030745000c4000303000d4002c5014098990041c0c2c1c0b00030700d209401d5200c07580707818019070000754a0000241307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555062221 1250 555060971 555060991
    0x603060f0411130e0c0a0801090206040308031b1b0c01080c120406060b0a0e0406060e060f090109210c0503122b060b07060612020a03031209020405070e0f10090e 71
    0x200b40c0b800c0c030b8514061a04c040114001924501c284141486560b03203103034101a00b141e0621941400603150070044070100d0ba00058181c1d26502d0300c1c54211705800c8187c42c050355007100403d071484081d15040101d040765041c00103d64043c0502c0005650405003101c01c1e20104000348006210b1154581c0c186a01070301c9000c00141032500c480c8140c80640000070306c480080e2041e406240070b40bd041c480c0d940507140301c2c2080c0c503400ea5030388000342091040760802d0410400200d03050b44130b6409811008081d02c103900c008a90305003990307410001d0a44131442600c007244090b0002030b0301d00f004078200700c01c180460200f615110000440780d040d0f0007007440703603103000b8441c081e00c1044401601c101405009155440799681c540c81c00d01c0416a1031a0b0003064510f8801041c0b080143c2d10303001c00380d0480b60325043c8880420302443d0383d68010502c80e44040d401c18140300c204212a544829440c130084022101d20200700c080105114105911038000c1010070300c81c010500011345200415540501c04030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555063471 1250 555062221 555062239
    0x151504060f1814150309060402010f0909060611010c08040314090a0e040f121404090c0509120c131b080603030c10060f090c020604030513091b03050603060f0411 71
    0x10b159041e4010841d407101600d81c585221034119440c149003845110f081c69040b16055007000b0007040e440b1040a007009041c0008400d030100d289000c0d11000c001824185001c105803643c0d008080d00300001c9140c40b170a503510704000d02d02d01601840c0c0241c05541c055603070318140100b40c0c2e0311520316804504550303800303410341d000040d10b0104058818411449a03081c10050f20a80c43c00303001c80c0000380242001d110402c03108500003032035582540e04880c1040c8000c103204000001c1610f55105910010b5084081d2568002c1082c3e0005801e503032008094500c44040b10202042c801102c40b2460490300c0d6038000211310007918400c00f100380d0803040080030b03245040ca40d0340d010340c94040100136480d001030321040100183c0c0c400c0c6c49030320020100d980e4240504160010029120400204020184500400c000012001418080c0080c1c00601c108000640b0140c0d4031041000721215000000b81c1080e002034040c1c00e000c900c1c14020b040b0b0088082d02a00c8030713500c071011709812081080c0c200c0c0b000c5c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555064721 1250 555063471 555063497
    0x9100311040b0603010b1b1906050709080d0c0201020c1e2e080a1a130509030d0903030203010510030204181806060e0402090a1e0b0303090414151504060f 68
    0x100001314002c010380480c171903850345410ba240d250211998003010341c40d0401c0482006001c1d030300c4000078180760f014600003926550340f0000c1c3c0740c1c41c560b504000494030171007600c6d100030b640104120310105d000340c003100d80340f00004041140000442c40590400c0f40001c00f003200034104030152138101c4001e1446001c040c20f0210380c80b411048050b489000243c103032401e00082ca0443d12410f11003046080340414140d9000c408121120340503104220006c0d611000502c06034020704c207552003015901000d000c00c00041c140100070b90400e000e5140325855030390000b910240079108840480300c01017940b941c6000c1c050402802046054210220398030b40345041c4001556500c80c0402601e071000b1164528141801805401c804c001c0030300303640c0c500c0c02ca02c01001860301050450300004e10480420707000c440c18042402c40c060b0b15406a042400d08542080200c091219244240b985980545090015100f0810074002420380040422010030040c401030384038a51442c852215070034680000c0b100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555065971 1250 555064721 555064729
    0x1107052101091212150509060d020d120315050306041208090709020301090603030e0102060903041208041e050306130c031203150905070e0307150507030210050c031509100311040b 79
    0x154500f00c034005413050b03540c2003102c03200e0b202d0051286101100c000c0c2640c20003021030a030010207007405200e4607040c0f401008650b9141c3c1442101640203045003000c941480c0c02802074000400f205440b10031400c00898107040c001000da20513a001182841911444041601d11841c007510740121400382d00c00205a03c80790303000450003043d07205000640c052a43c20010401e60581c1a114110f401c00d0050005214000040e902a52490440c080c0c0c00c181c235141c4005030780f0555200000e945810101c00310001144900d04d0201d950a4003030311115a01d5080d0255a14001303100101601c0c4408424408599000c181c2942d80c1c0079803d0015491071540d80c41c0c000300c240355200070020b541741c000b0408910760091929040c1c0d84254000c180050808100781a90300f04e44162008014000c1614410300d403003045001c6400388003490030001404c20b8910f0034240e5104072a5403031040d0740786100c0880d500785030582511a82c820110080c50300d0550381e803009101003050065134056159280c003012542d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555067221 1250 555065971 555065993
    0x81f02070c0b0f0405040606050901091401050d0516090602030f2212060b0301180206090621010311010207060c0b061201060b0c070e0109020405130902010c0b01080607110705210109 80
    0x2032104140351105d10f00130070030007034404a40008041100520a52415036040700342542a62403100d00741c01d150b0040c50040701c40e4085c2145014001f810321090040807003145803221403040750369480402d02501c5481c2a6500d10801c1d000024204040000310303074444c044132034551000413048048282d5940c5401640f1a0529120709039045650b13107080d5a107520302442604000700480701090f4011105400180380c50040d40704050003004000349103c1e40b002041d070848201d05004040500340e5849040640c040742c181c3c201503003d803203128804110356000741c01c1640f25503804181e0714070664854080c04461485c1d0a8001d96a648800c80400c11841038800b40502d84d8200d0010311806280c68240205100c042c2d01c0010158030410040c4080e80f02e08850600710480b1140100c1c00e0425440100c1d01c0c02188800940010405e40001c1000d843c007252080c0a00031a5803019110800a8485501d4485c284103550340600c0c04414440c102c0a008400c240d480194400000c03403c180d5120800000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555068471 1250 555067221 555067237
    0xb0d060507020105010f12060917040b0408010e0102070b01031e0203031c06210f0305040815070e420307020a0c080d050304020f030102131e081f02070c0b 68
    0x40e2500104500540d0901c038403030042803042c0f2030a000a241c01c6814082c400303440009400e442e204d004040502209503060540f9050000d5180e0352682c0d1141180304d0b03138005001e800115400d10041414035281402035454440c1c125803518616465640c3e40031001c9001c000c00864648924a107802583d020f1000e031070084d07000000711850076640940e80742180c0c0c00d60071440d001c030710440524400c10036020340080900d0b840f0707800d22a0420300c1d0901344c81c5405543d00504c100d10a000389010035940c2c0c041800c1c09141c050315181d01c0680ca0ba01000241c5c100054404100c1e0a070b50080650f00300d01c40040b0821008442003002a80311540041d8130691044401d4009a07100c803036090200004041070030010000c0f100940251a518a8010800d200141020703100c1c42400a251090341d0382035044071507400c0340040108016a0350f0508108050200765040d00d17082540c1400107000d1800305010161340d081c41c10580b03d40e210010944001e4000a0741940c02c440d45410100720128103000401c541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555069721 1250 555068471 555068483
    0x14090309040b01090b0a2d120b01030e060708150301050907080601050109030c092c010915020f0f03040f020909100c0e0f01030903021f0902040e010e1506040b0d 71
    0x18210450900096407214203002d810411012020850002d030081917405101c182d2910f0414611640c903444141c4181d90036070840b80c407003580c1c0100019002030030b5140310301300c40d0b84c1486203051b524010b41c21207014500604603038228100245410348190b17000c6038051800400c4840c1d6054210210342107078411905102a9440000103003c07200c4200615401000d00b468000080380c2169190349964501d44070f0b42d404240c8440c4070410030180c640b070300c00c0c9001040e01c000c0d91071030b0301c844014003a12103d8400e503007800000e00c040b605e5448600840d030140c14011180380c54804151000341071039100403c1941d5002c4044912801656000c4200d40100800e200805c50054100019000c8402c04020b070014041103502d118180d442d22100b484510f1424200000c0c0e1186a040c00c2c0e0a021000c010703648008071644240500e04040d62102c0e400302d00039501004522100907070542200c100c0d20600300a0382c07000c0307100300040080c030940c0fa51180000e400414800c100320042900101402c00813140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555070971 1250 555069721 555069727
    0x315271d0f070504110a030b0f09090615100f05030a0902030609061f050d0201081f0909050f011802090406021c091a010302211e03070203190809090703140903 70
    0x24200b15076409008211003c2044810b4009010024810402c0200c241a1502012041e07035460208020361804050264401403400b40309039505c9080c02c0b5a807100f4462003407142d040c02c7c201290204044c0ca0030b42c4a0b883c03005032482c800d49054000618440160352603031fa50350010385081c005180242d200800412003402c0600c10894880c510350890304501c9901d400c2013140390b5809000100080c0c0a00300003a082d218021010400c0340b40e00900145103c03048000102c051890703021403c1b95014070159403c1502d01c00c1c44500f42d92800ca465050780c240050f000c00540303086042103801a01c00d04005250103080c49400300c841103403003004c151155940310128148803100000300c03075008410032030042544c150f074000740085c4030b040c8000c003050b88000c0b25050740420410412098000310120349912020b0132440315600e07401144224000c1c09500510000240d4642c210105141c1c010f0b04182000d19150510102c28001003c0b1001c25442e42502c4250302c4481c00d2960290417000c4c05156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555072221 1250 555070971 555070993
    0x6071209180e07050f0301020c0f0601060207050901260a050601030807030311160b09160f1a180f18040303051501020307020112020d060b0a02010c0315271d 69
    0x2441000948490700000d04100c0c01400195020540a0a5600480d00c210080000c18080303130080c0521444202c0c075103c6e81110800c0c1d01c000140c00b50498100c2e40c01c441c0d41c240c6a00a014000400b886500d039425a001010600c2040d420110640e610ec0d810403203903031011a4603464500002a4019a0091000a1080180b65040c0a4501c01146010301a80307080c0c500d1500c84200c4008040c0035000e19011404100800350a002010f0801c0f480c85a501d00d4540760a00301c036207912a0b228021800c00020707480e901c03003400303a401d850312004480c500e00c0940e52001c0900c03c0b0310184e212070b594809040701c0700100780014042c00358001c0e4042c0d500028603140c140340640ba114074004180381035500c18000040140e81c4000c480e03403e100c0e0590056107541e100302491010300700300d8100203003084001c0380c0c07044a181d05510442d0300700d00c556418081c00d1001e44a01c5c100c2e0380380c0e0190181c6a11759883e02560744000000000025a004900003541401c1d244000b00d2081c80c104445240c1c2c0000d05042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555073471 1250 555072221 555072239
    0x1200309281d040308070908030d0b10090602120f131512020f04050d06020f0f12070804080d0203041a0a02070303060e062b150606022e0b06071209 65
    0x30081c0003142102101d48090b668590400000108001c2c00c0001d500005950907114040a4004140c00c5c8202c07030b29504640d1400020b00209240a4094140c13500d0010006110361091004c50b1220740203000c0c41d4869214a410395401040102c51040c02000303000090400500900000c0015003c1806000a0b02000420303071491040c000c1c00302401802041c0d450b0780301c401103504a402c02c503494440c8000074a400f074040e016150619001500104101126611800003850b03042c401c00c180840325074a810080d213060100b079a0150030680c0911018091401c036038011500280142018800103545c420b05802e18941102c0541005401050f2601019050b000764070240c902508003051524066000c10000d09991419040401018440e0040d01e0f1611f2000c540b560341082481e140d4020980d001006400d0501ca514018803401d40602401c0203075a030700700e03049829145400c01c1d5503400c02c031080103400c0c251850350b4003000030000400095100340625100c0703d165110780070081d25141b104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555074721 1250 555073471 555073549
    0xf1201090e0c04090c0603020a030608060c0417010e0307032012130b030112060c111209090f0402030a08030a1d1c021b1302040531090201200309 64
    0x480c020f60400000200061001c0846416160a0701d0016101c00590008a0242c0200d90000c40c240c0264001d0050b520030b14402030040d9090103a650032600c1c1caa04429080b5044507022006940007400440f00182c4150b882084002800c45240b10044009150a041c1289103e1211800c1000200aa20440c0913080400208400c2a001d81236600d811500c040b405c1604e000103040a83d80c01c405000e103409144500c88500c80740342190481c011407a8540c8069201e4040300d0b01c19000c14000802060700d8080356031180342d0250160240200694400c01c86030400b1304091807503619284074a5810301030400ba422007003030480042250707031110115035817050b2419004c0780854007c8100f021641100c0105414040ca0540d034607180740090080500c02801a6004180e00510801010141e01008248241800300200004254200c000b0300300040b129014402808104080c003160300a4401c50460041d0340070a03015203103050740880c00201d09502e107000780007000381c0c600b450000c490548081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555075971 1250 555074721 555074743
    0x1707080d03140402060d020408100203190603030c060b030f01140a06120203070b280302070606270515270f040f06050601120e010b0405150906060f1201090e 69
    0x1c200401c0c1041002c0070b00e9031030000d00180c0117045c0016003141740d150700d9040768001c000000c2a80c840c203800800700c1c0041e40c029903540040e40040d0070390040d440007510074001100da0544800c02c00415507a9450060456840000d0303050158010100302903070207002d0081c001500211501084c0340c1009400c003142c0311504101070b2840b03c49050300050300e0018a8205031607042103c640c48280750b03000c09111940107124000c0d00c25003450540c1c002a05030300a03046d00c0d48290303020700181e81c861005d1108410000f90a81d40740500c0b42d004001c0f2005a4413550300420f40344802c0c840308a03a903022500251000c410a20000552000c44034031500482c01240c1244a0746400740c0e41e0b0600e5110b41d00422100074014058981d103101145080e800b4642b85d0380150116a024040403900c401030328006c02400d540c1d01c0c0100d0800c0c00098841c1243c0741810300801c0000c0803c909600c441c000e00446401c500a0b0707111581c410000348200341c050034880c03802002114400306442e6031001070142000715402e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555077221 1250 555075971 555075977
    0x303040b1b0105060312030a02040302220c080c0a0309020409050a0b1b032401170903040807091b0305100918120503090a020108060d0c0311090c270103061707080d 72
    0x200b8020139a501054051440c01c144010507226110f2000c0f10000344600d8bc0300942c0850b0441100c3e041001b803940d562192000b0700c80410030512004400e4845110480d01d0341100c042c200a64210a4082d5101c1d05015001400003c0c0b18505555140e20f05540d500c001d480d041e45003030401400c940d06500f004000f6030b40141803030441c10000107942d40766029184044180413040d034542c400d64410201c0c1c1a14400d00b1845906904044910580f070340e005024000703150084032008500703052203004446014415000d001203150741803404800411014100381042d0f003548400050000090090050544140e41c1d0a804680c05240c4a4002c00d046101c13030040c00414002c02c62031000c0031035015401902802c00300140d658000014440340540c24000307018071001c0b9008000c0c481c82210030307110488281c03207115064031414181c00003405103910040d54030443e600900400100c417500401c054006042c0824040e49030018210944a030b008140d03000d40c081c031401c118901e0200050079a1206c181 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555078471 1250 555077221 555077231
    0x60a020f0f0a11150405131e0911010c030504031211072c151002010204080a05030702040c1107180207020a0e0a0c0e18060f100c032316110303040b1b01 67
    0x11003d40741390089100703041c0704101204e001481c61003640c009116001510328403451503809082580020610804e06030748100003070740103900350750044511849194040c0c0f141400d00385980d4614103500b039094111410408022902e815042c402c00004000d804408800d42c1d4990038070181c41d030842c180702c40783c0a01607042c0c3c06016002c9024100280e546505440c0351590001d00c0009030301a2003194031856103440740c1d0035048103002c0c0220190840c0c2d84200c3e014890310403200400c03a8400030b11117200040c0d40200e981000100d90309010058084a120000341c180030568000030322600d8168071a511400e010010031416210f00d100c0d101182006040050044a1006c003058210355282e50076000c1d0780041c0c021840d03a59803507400c0e51114000800505400f441c8020003412041c1d1081c0c105c001c150381c0400e1001c2a06001c0342c501c0d1000103101d00b80c0c181400224094088402050140c3d603034000304002446d5510180000d03c09401210841651034041c9031404210582c2c8001c40c241b141d141c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555079721 1250 555078471 555078499
    0x2040515042c0115030f0c0e0a060f050f06030c0c0f061003030831032109120e0102060a1805070b09030c03070308180a080106060c030f020a0c05060a020f0f0a11 71
    0x1041c030040c2900d8001074091b00e400b900389002e400284c070581242d41d103541550704201018265070040c1094644200001904503071380ca080c810000c40101c071040d4001c0f01840001c4040458501030b0202c50400c00840700c0034000460329a0400707005903010001f5076090750041c407d05800100964001c80c50105069010f42c0341c203c8494009244000031a1400440000500381072040184048800c07903ca0003426850065079071600070a8440030403503c03000400d810b9034403580142c545115041e8181c001d400c1c1981d80c0203000c00100600701d0b240188002d041d9543c0c0100d0010000180a04425010690b0381c0b8411020185001624825503210798009841407000406100650765a2004540d10900610b282400200da1101da03401c445850b610301079001414503070040e64501ca26000361074854241c4c00c8417800303d8580c650354201138284610940d041007941840b130b0052a00c1411441030f00e55411194a100e418101507200b004042d40c82507013080c0c00c0c490303000740c448403200c401c40f155103c820720 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555080971 1250 555079721 555079751
    0x6040b0f010c0b1b0324030a0c15110f0a06060b0901121505031504170c06040f02130212010e0705070b13021c032f0a02040515042c01 59
    0xb0100000307082600080206150443d58510b034801c2c0e0280c4a1403070780340d11b0100711a04010403401000b559044511814041d0707410301281e0440380542102800e0b5846092041004201c01007101ba00f0401c0303503000d0700c0c40c031904041c00441d100d10640805814540c00391f00f80001911a542c0095401600420010407144e03000405618140080d480c0841c4920071200300d040d45a03104d501054050040303400c0c2d032140a0001c3c1d06207205500c0380980400c0c0c24040101704110780500c0011148503804200031802180510701d00e00ca03038a100030714415a0702c9903c84408140d03040054560044a1040014403c2004030075802d507200b0410b182132410032045450300d50005001400840400070062201410364a9003041c40080c280e0300401c252108000d45002040c07100540380700d25407903201c03131201824150860f40071544208540e0060540c01380f140c00f044014000036002c600ca4110402c00c031105a101e90060107054024015508044044003490080c40003600340540d0b540d9152603602140da540c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555082221 1250 555080971 555080987
    0x4031b05090106050d05041103070b041d0601050403030809070512031201050d0503071205070804140f01020a110f040b0a0308070506160801061b141c02030310052e020606040b0f01 79
    0x640c041d000701c6c850701c0d13a082c1648102c0c03004817410b405028411001c910404400c005004584c0320020400414683c030f4042c004254068845a0004d2030820081011a20803a00e2030341040c1203070151820b02c0d58a05c0090118401c6002c030b483d0a80020401c4e60040b20010000e500500007583c0800e107a0780c01d0782d40c0940f41d00c140325004001c88110300b0102e001504c14800d8500c0325a001c20304580c0c0b19228580040d08003000a1494810402180400d5055102040300c105c80e079842042c2c205034000e0402004441c000301c008582d0082d42e00ca04a0150390f54100f40c0030300641c0950f40e816030b00c01e100d01700503060540050542001c402c00c8103040b10f003150b1044d4030a0443e5900c1c50260803000e0402c444043d0074410540c01340035400c0c281500742800c540800d030b04054464081401c01420b0100f0801c0e40c0f680411500850322000b81d080810143c24080b00d0407407030403143c101c00c1c08007006400100d09000368103140741e40160320400030040700d0705087c03066680d0f402c0101d0f05001c0444d00b8000092103a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555083471 1250 555082221 555082237
    0x405180c030105040f061e02070c0e0c130e0a0b030714090c03090606010e0d0f0b1005010309080d0b01030605120102071106180d03020c1507200604060311040b04031b0509010605 78
    0x1651240c001f8508003403514500894032442c0c5042d50b4460b0a0301701081300c25458052400c55040d50800300c5c0944103c03104070307003895000035000c030391551030007002c8a0f410030300a01c80d0f400192900c6900380c440c5e80501c0a40083d18402c41d004800c011000b062104040004280d0300401c1c20820911515080008074542e03c00001d2a00b941291841404100400c100c1c0000404065403e4170150400c4202c2100500c584618450700d00e030f4030395600044050b540e81100103005024100008914418aa0403071084120103040110307542d0340d5403000c29214207041c003a1013000c0c0d5000c40d51030104444805996160001207810310f042402c1c1c1140310035000c00900e1035510940e0307000b14240415000780a003150a100c02880d100840040003000c16150340b0a103401c48a03c084420640c3c2c240d8840751a4a07200980542118201410100c041e0010003c601070340f650048141710010320f03550040b0081014500c1802000944c100d2281001e5100060341c00aa2007103d2180044c80101e80c0b01c0151001c413 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555084721 1250 555083471 555083483
    0xc0312090102010f060801092018040f081c0b15160f050102040605071104140c030c040f1512090312201911070312110c0405180c030105040f 62
    0x12646500141d004006101c01320100e00c1c00c0c40800101b20b40c06521030102c0e54000c0450301e51000c072810469010641c000301c800c2c0d10030509645840740a04482d0301a82c07043c864401040c080032a902d542440360490040c01848064400524503001c8050190020451017900e08103100420107010440d01e02981c10440301c400440d4180d0014800340034210000681c000c07008558840e00d40708002c00355071008005481d00c00c540200f050709400c1c40c0c86105105000c2d00120006912500081c05651f0b00203041d95803403800c24031020a00b58080c1607007500500c0d05007802031a00000344005440c000c0b0030340f0380405162914050202198012141810340d4603612000500b80380c0e007118001c800048110040380c1694041303988682c11441c000f1454191141d6101c64000c010020002d554543d2075003c005d0a03200c0003610f06920b64080c4000500210750740c0c0503100700305030040106085500444014450103c4990700d1408884140300700d241e000420f60090001e49070940764403c100c0e0302600700030b01c0b0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555085971 1250 555084721 555084727
    0xb040302101b0221070e010b1204021912020f01020616030213030b010e060a08190b0709080109050606120d2708060f01030519120c240e0706020c0312 66
    0xb07002c46002c412080398024203a03120110399151000e461007407102040000e01c1890008588510340c1d9204504039076042409520300480b240d16142d11410140040fa0464519882400c0f4442031681c480041d1488059240a04100e40108049030f6450820310303042d03402500078001d8102c030500310080c00d20010b0402503540c4100c0d030001603003038240740c5c40a000105403200206030080200f007110b0142608442040040c2d071154001615a41071041040700f04100448060005001d10300c4c00360b102e40380e4108039800603a20440542503404034181158281c12142c00c00c4490300e0509412940401c0032030041048d40e021070790103031a40048014200603210105030070000c11411070351401c003803e403101c00d40d042c50406084c504440d00d82804225040d00401e170f034031b2180c83c10500d0804030381600101e2892510440202c15200c00100c00c2043d20071074010303854014108414080c0c005c800528010010724100d0f4203512a0401c0c90307540142e421500101c080c0a01c1d40c0d4000b0f89242801e48207502e4680e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555087221 1250 555085971 555085997
    0xb040908070308151509120c060a0305060d0204020d02070203010c05091507050319020a030e01051303020415090501140f0306010602070303080a060515090306070807080a0b15030a02130b04030210 86
    0x101d20002d5101c440e81c4002e4403117000300e510541001500c4076200a070f0342524103605040641e51102d205040160b084181482024480351080c2c000c540c00c604050803600d0030401e140c000c98166405200280312494001038000c0440c1001d101e140003156052420070304007241e900001d80d84070040314592400c0800410840c040c408240200c0f111200805008841401d01100107504d84406810541c0032904d400c04500647d40180d080301d207111030a1340f034044101d003164200001848040100e21044000b110f0105825445200e014060407010a058041412940400881a20085045009400420040004a8001a9220a50f603150512403050350b103103544000181881d9001550003884400b2074950000102c000f07181248c400c0c2c0a0764165030b2030000988030a2015520304001895401c0000d590403010b9204100c5508028621002038141c1c507003600c40c5130010b80b1030074042c40c0c0c00100e891008134001c540d08020404003c03081d082c580f850f0000348040b072f4424045800d2102100c1d410b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555088471 1250 555087221 555087241
    0x10506031305010b030604030306051305070e0105030a0f061e17210c070e1b031b0a030e1b0405071704030513080a0515060307050609040b03070f090207060b040908070308 75
    0x110b9240000f80c04c1b181c040c5440d050041c040d0006219130703406140010000031001c016070041511401f0151504403011241e070004503030701e61005007c184403559400f607410310b00c43c140c0180b500800203003104040f5450442c101c505268002c0d84580000d01d540115404840d00205002c114044a000d074206c40f0f80c42503070041424031942c40c070300f400e0b4020a0400301d204d4136500310050040c0000322007940c010103413114001603880f0035110b0035500c0c01c1d800d900c880400c60401c002c0018040d5450007180d10b20510a5861800c00a070703500c603400d00924184c0310706e40d04280c85a0707035021310641b40a5480c050f001c0400d1803928806800a400c210b0001504003080c2c0754108580c0007030042d00101c0741d25207003030f007055622011000b00c1f0220865030784022604a2500040da4003e5500042c181460701001d042044000d0201d0a00f17907405000b214400160b004242403c0802004030200c00360b507402ca2450f00341c00302c60f0150403041c41a481c12a1a801240c190420b0b203045550501b03006460352900c603400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555089721 1250 555088471 555088481
    0x10504091103070b0403212102040b04080703050c030601030b040b131a04060506310605060c07080f0706050301031209260f060c0307080c1303240501050603130501 72
    0x426010712401e81e001901c0c204c690020001c0324040c0006914200c0c02084a2505060070640710000425000720740c1b6021709a01c20111066020b01001860700d0394801d5440c0c1c0a0300580d0024110b50000b600030818404240300340603510404a018083e80d60460350381c01848480900094401d03600b400015004101c07042c4102c40080c1c101c4a040500d00910502d001d40381d0044500b140d01605001c0407955504100d40d03040c081010840043c0c1d00e1041a500704e80c101034170186140b80c0d448d224000014140c8400c5c00804114035108040e0541900340f200d0186010644042c548a581c82403108001450744801940e0541e07a00a0034100301c4401d40c0c03400c6030716003c0741d0044210910741220368503807070702103142d94100c28010b0001c1d15900d0100460303181d2030b50380031603a0410101c1c0800003d0b0301d4910416030241e102c0c1c8050101c509243c00198001541b85040e041107c5a030750410244160343c1d8040380115941400b1384040c8490360419020600b01d00019004c206540c62540c01201000b02c29002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555090971 1250 555089721 555089753
    0x9021e01090905091911042c0109020f13090b1303170105090a020912060c09120105160c020d08030103050a06051302030706231201030204110a05090904140a03020c0301060b040e01050409 82
    0x206114030040c4003090b540100f46080c145001d01442540c4070303034000060140c400c13000e4006162000c61078422051280d500c000001cdd14030701e26a0342440c040000d04441c03105006e00c00c18801c0c3c405000c40e40ca8090300141514886080c45050480100072075541ca400c0984d1050601d000507848900c5180842c2001c0041e8006450700e02450082000c1d05440c440a820040d00440780000304150700d9000d1801c80f00c040d02e10907070a0010f51051800c49020301000600c2ca403006e0a82c0c00280d4136078486400d650000e81048460b0b402030004101401000d0054a4218a4030008a1301014880d800240d95228610401007802100d442241240b0381070f108040310780b80c100840c1c954501c50290580b080d0007003400100d201d10301d00000156044c94603010340c0c01c010319070380b2002e240c05154010000030500003001124208580a11011210343c14016108024465001044130403040f004050a4a030b00b80c202050040041c80100100c0d039011036124111203080c0c80010310f41c0d6a5040155032074440710740e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555092221 1250 555090971 555090979
    0x60d02070b070e0a120b0a09020a080a031101050a1406011d10050d1a0901231005181906110f0304031b0605120609070309021e01090905091911 63
    0x1c020b01183c00c10031180881c1c0c000c403014000135031200c03868501a408105c0103044c107103041c0009041080e4075481500c1003030000f085c0890351750380c036a08903103070051080c01200010800c400e03400d145c074001d01036030f5004030052005101c2c4c548030282d10164160024640c504010341441c50702203d103d1640460744242c006442c580502c40304290190190b400350080c2103485282034000c0c1e807042600000008a080c00a03c0070380203034a48140005414000700382c5040c047c1c0c5100c076800d060303078070321802c1300d00d02e005d503152143c4461039110b07030f90103038031000d4941400303032803651004402c6004a600180580c4c10a043c0300e10f5840d000c0d80706915103d601400c146042c480040c0c044240b00822041410f000044c1c20b03191451511214111841d000b03502c1c3c02c04521145001288041c9844945d01d54840c03214034000a410046400140e18040703035010042c0b03c0c1000c2c0840600550307000300c40002429103204140514102540b80b02e603115800c40500d2003040760488400100000d000c218000c0000080c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555093471 1250 555092221 555092243
    0xf07050a030f0f11130b0c120a1205010f0e090a0201051c0b0d0302070816030c0302010509030a0f061a030a02060403030c020a090e1b2e0c0b040605090c010809060402060d0207 77
    0x29503011140c1c07040417440710030012200005030944620f8202c600d85a0030b100a0010450312440080468104030900c0040c4811181c0000481d10684641c074028120390041c0389610345090200708030140c001d0300705841038010394000390150360411704940c80445101080300500210b140c0100040400c03440c05940545040240c43c02e01d6400110320b4103652004060300c4d00140070307820f020440006031000600403800c14408102640c09100940b80b61b01003d020748114000a94441c1401c03884d4000440e50280d5500c0d4854055030400b0180400d2501900244180c500d01d0700000e4540c0582c3c4801820800702c2c0c4014803c645070b0010365001051000e00c01d100391aa00224141c0f61400301c0742a000440e01c0d00d07124105450080c482502081c14140c12401000007403602400c42c0c00c0380030740001808100e20340d500001307821458462141e40540c81c0041c50b0f040500d030150410240100080c100203802c410302000030790102d112a003007541140c549170345d10a04131400029000e54040900300c2900c00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555094721 1250 555093471 555093491
    0x9050f0307020f01080403091a19031a01031103060d050f061e070801050d030e0402130303020a0b01060302040842090f120f07060b030102130e0f07050a030f0f 70
    0x3001e4031195108840003052200c6001c01103904440488010740081c4451004004082d0002d0130314065840300f00c196803030030000a0301c001c10303003202e4441040000d5031882c50b07a00a621768000f248c0362a0003482c0500075982d040d101c0a805001c0a40360510a071550055002004010011140102e600a0540d0517616010b0008801c00403020158102c92001100250744240300e41403150607150000d00394401119281c80444220014000681c1c2081c3d08100001c1e1000014103100015071003a80106a00d4106180a40020406074060703c28580180002d000009010401c803c05030b107140440503401c52160b0080c40c201d41c0c005001d107000f511540a4429090601010922900103141141d6900080000a0740c1e20900c5880e20403220300c0600c6101411103240c402004618052580802c51161150000303089034413440129003080041c6600f0880c4034451402d10b0780c440780c50142d8141070b01d080310000d07045200344078162040540d07440050400a282d035000014a04203100200103000790 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555095971 1250 555094721 555094723
    0x30c0622030c0f05010206010e0c090301091e05010f0203091c021207062309060114030705030106140901060320032203050c10091208070c1704060e01020a2409050f 72
    0x42c0d03000b0780c030903a01c2142010400f035000041c1c082c12a88840310540e880d82e1107101b071101c5500a0a1b0003507040d502d824008001c180036a20018010722190303285140c0380b603240f40c240e0848480d81d02c6840450300500411110711000315450302801803181c1e011440701c0c000702c8100c1c20410002000011034402040c44800d102c803079030201504150300070503400141c02c100d1181c0100070040301c0054a80d40824014003281116640030074140d8400b5044460b0161034400007401c0d030f60650015451946480c80b19000391901145140c0106801d060410071001e44400c640f02e0300803102143c80800784004045181d00400300c064400b05440b10420a50460403840e0040060b441805240c04038032610501c0002d0f240c1c2032041c070890a80c0200408001c0da0054030035103080e10300078014820310480c1840d15000c02d15070f4400e111100031b2118200d03552400d203c03018010364140318120741158011140314000840c0302d0020b000000c41945114074080803000002d01411104c10001e01d80d0041e4640d20400f908 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555097221 1250 555095971 555095993
    0x30d06060c0b0c0310090218030a0f05010b1c1e0501180308100b0706090305071a04050d0302041503090c080109080325081306061203080402120309030c062203 70
    0x1108040940e03454035290f9800c11a40826128210032035070340c020800076008182d00030f11304000d802c4140142c01c100300300061b0400141100590310b4440c01902c141c1004000c2c843d04a00707071021980b43e0403004e59901c104a450101000080c202034120500e655141642201d20008552020090084802035004400303c40100c0340105c0205841001103050070310300340d5a2101365031181d410981415859100d520181030030800550600c00100842c00128810324400c18421080600344880d03402c3c6494224074041c01145c115041510612050040d000700c8d01d8620b62695070b82c5030208258030360341040180c203407079940041915842c0080c8401000542001380d482000900c2007005854100102c0d0410100801a828009901d0000240d01598000c40410641e1302848000482c01c2c0c0791180d40d6022241900154007041400701040300711302e80720480c1c085521b02e22015508060039180400e50390f402c890282c522411002c59400e05144404038460043d010501b8013800c003a0f541c0c1490700002d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555098471 1250 555097221 555097223
    0x9050a0210020f0c0402090607020904080706020f18010c03080a1a0a0801060e09010204080601030213021603050c0105100509070c03030e01060f0510030b01020a0f02030319020105160201110714030d06060c 90
    0x40943c02011139689028420360b581341c9000ba184525201250342003000d1000d000b1300848003043e0a01c0114081800351001d881c4c0b211408004a584400721500c1c0400094840e08507810069069140b0300002d51000c3d0460300b10480e400046007400040c0761041422000351031454002c0712010b0001074454054015804039844031200b1034803034540a001c1402d0344075600910b003e0b5801140100010305107032038841c000c14022100141804550921500110b40461013900040da01080318075a4000a02c40d158104017582d040c054903501d01404a41324040003490441444a11a0002c0500d4040e8215a00301d41501c0005c21000e0f80310906c404030034900d030003030320b00884100d01f0310300c60280a4840d08982e00c1058006202c0c0c0a0f0320303510769901c0c0c0520801241c0602040c0b00c810412004c0e40340320174020209400202da103152030000841d05980001403181160b041614503038130009013030220360145030460012103940101000d030a00c2d40c03156004106d0300e28540070000841a5015008400b01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555099721 1250 555098471 555098473
    0x304020f0415210c03030f0c08040603060e0a0509070302011116082d1f14040c06030f02040605090d05011404050d03050a020423190b0c010b0405041509050a0210020f 73
    0x4540f4070181c00c0e8446111807001045900a6401880480d000b80c00722582d4803294600040c030820300345c0d12020140c125611481c04251103003000d0010354104410b50758440c0420004203c0c83ca084e40446941d40d510b840042c0c140503200e90061209801071181000d8661684102c0e00c1c0d01d80c0c0e8071100342d501d03011a0142510310504201000385082090140c0381c00b0700c080001005002d0303e0b84010b100505008090f80c0d9419070f225519854603291040361441035000c1c0301c031845881c0c80e004000e010703100c58811030460380e0b104100030300c075443c0c205003518402c074402e9074030117200d407010b20f4a41c0c01030815000c0d0741a025944d90030031040210001c1c4072040c01c40203603810300c800e417101c21064041e405107001d8011100324a1036031a820041820241d05d40600041a00a04107045499066401140d41146008490006003900c802e5024014000d81080a850800243c03510f83c441d100400c1110205602c3c8035151800302c803d005040013803c1c8020380080c0390900d9206800000f03943d80e08200242c90385 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 555100971 1250 555099721 555099749
    0xf1706070302091f0504180f05060a0501020d0c080f12042a12050109080d0b0114070c030212010e0706050a020c040c0504260a03020c092a0304020f0415 67
    0x140340d10a00070b40e80701c010040e020011034030b81042800401c0d4405500b410400000348800207001c0c1101044108003544401300140d05824060000d09845e00101b1150152008030010001030f680010100610b001902d48240c50030400d241c00d64140c82115203442083c040410713041003911052084500881c803d181e400010b580c059011841213355240c11800000041020002c0c2c601141503107a115120720b000051600803691400d83c035401144e10100300076030702d056003111541c21994109440c0c20b4464002c0c201201c40c3e0b030303400700b4011902009000300c13a403804850007200c0035041028203032a0842a103001c80d440e2071004010381c020080000052041c12002d5803282060702c00c1075507198042d6115898030303003041c0201c2241034000c0014001c040c006d000c4d51094130030030703c448081e40384254040c0c1386201c200010040c2513500905141d80c5210504d030583c80c036646000c0039010030103460310016141d503102d0000810030b2024484441d0080d0402d110040301c0c0040414140c1950f40d51144200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 555102221 1250 555100971 555100981
    0x1050f16172a19080720010906140d09140a080d0f020c06150a0302030105090609010c09061d0d060c090305070f03080702060304050109051e060705090d060f02040f1706 74
    0x4021903000822100c3c0d0003804050315480c0704001c880c51110b02070f40c000d5140c8049562101c5100c02c51301d0407074541411211042c1065a030000f80d20009003420f20f0166685000011150b50360300c6644d50800e480d69a54059001700101c2c01900201c0e85400025111140424204207800d42c2c0488002a5041c0c9442615100b0a03401e109071503407120000d005104940c1c41038442d4052103c2c40080c10b900c25140280000182e03024010148982e410030054009401d082075401d00790b132404a512800c0c4032400c10180702469018904100c0da00d4540706515442c16010081343c0300d00843d02c40074001034109800f1604142c2c00c811030300c088034400c3c002c031106286c0e140d03184540751034075000c01410402d0802c510009441c1a2001d113402c580114000110920140e5602c2d140c4150a82021071000c1482c2d0000501c480500003658021290708003a85402e0700d40001a10f2103401450003410540d881d5841a4440c0d81517054070050007071000b5044501d5141e1090801e14540400524414858200020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 555103471 1250 555102221 555102277
    0x1030b061c03120911040603150e010b010212090d08040b2113020904020a09050108101a060a0521070e04051506040b07060f05070c03170601050f1617 66
    0x50b41541e208004005039500000140039034040607140721200414004e825610392290320000d51254207800c0e001d4512003600001d640c0c2210b0514416450180540f070503980103d054101c18180c1c1104a50312b00302c175000120118144080540174800c04103000c140d000a08008021050320340f000b00c0e0f1040794507201c0301c041c22803c960001c6c043c0074407586000141050744945401c58401440c080400740c441d1614001c0320000da0119105502540031088040441d204107404c0d45c3c42d1512a1449041040101e4007510030245114200708000469000451602800a800c0d440b080f45015042c28021001858254109107140c07040346494080f8200744c03002d0940110091020b044c1a080528103200000c003500100307400e880d05911008c003205948942c2c89070900c5281c036625081064409800e0080008188000d0469a024110180041607070004152102c24425003092036442000085040c50b040002c18020040782074070300f03420b10910000f800f8000c078247c054506c201000302400d984c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 555104721 1250 555103471 555103519
    0x50a050d1508150c0f1b0a050d09090203091506030f061f0b09030c01050f0d0c200625020109082d03040f080304030302091801050a0b21090a020901030b06 68
    0x4d45082801000132200204050000d01140507213040000020151024958144080101e040340d00da0010680503015a4120b401c2201070070300e40b20114113610700130021680e211411001072811000348000201700740d0307040004c2144c460780242690040e05240300e465100c0c1c808900048442a480d02000c00c1042115043c0c894040000b4020040051ba44005685c20b51200c80709122180e800c01c038030300503588140298605a0b580355121002c01c900b904e0015001403541040c0c6495401420502c8905d54044c102ca41c503884070704000c40309404a141042e4010420864001c04280003ca0b810110b8800c02218021030428503904402c106600026101c0910040354014401040c04419070082a55140550b038001e101c0e0800515082074100081d2000400e8001c0101e01100b6000500c05424001c0c03101c0c0081400511141c1010304005004800c105030044a094011a243c0040e01d00c4000704064141290041c181a0965850341032050260104480c114010b92907042c40d42e00ca03604080007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 555105971 1250 555104721 555104731
    0x601050f1c0321021204021c05070f090b0d02060307030e010b1503090f01061508070e062d0a0504050d11060c070f080625030609180b0a020c0d050a050d150815 70
    0x205e48450759542c2d007044844c0d54004140c40c049411a200c400000da003c0003500c000e880200303c02c0300d4551804070008155251008010b0041c00c1540071000181c887c0d07020380c0c0c0c00000c1410301080400c5801e418500428140c03521640c4240c0585c02516188582002180298480800e85600c3c1d80409621401c0c4c410358880e48072082d1900d103103414054802c1201603040324851500d0500c4000c2000082e1a5422000f0420b55182c03d00e26960504416108007100a02001c5186405c04c440300c1c2001e880740c015482420700130070308203203403000b0082d0100b154160010020401902e0b01c80201046554400c035028002840b07000c00004075981000055040c8104c2520000c1d030310310991610740392403401381402500305154540001042800300ca011340c00391084000381e81d00c0324041d1030812903403803c405007104461074030400990540e250701045501c3c90107080e0600390b68a007008002100d85101d91821a00c07668500401e402c40117680242e60030441c3c2e0640201c900b0301e415811000d903481c5068072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 555107221 1250 555105971 555105997
    0xa09091409070527040b0612010c050307030b0607060204091d010e1b180c03090c041e020c162408062808060a0b090c04080601050f1c032102 62
    0xa010846071400d03c81c8400921511303024144030f0300318545440384248098030201c80000c00780c001c004442c10300044609401030050000d000702c40400001400724400a0204410035495030f512050980310f002c11075002d85c0c0e1000045680750303611001c400040c4982001c0710a1080e42d1134100b85038107414051302451400c0c0001a00c03000743d1403030311342071001c40801d20a5006160700400000141d440341105100700d50381d10183e50382c2e203003040004e81001405541940f10b280b41c01d004840741100c0e00b400400f80d8003038942c0145d40b11140d0f058503240522412480c84030380f03020741000c110310440080305246c0d4043c01507040c0280304401d83c140d512090482d030842c2c104d410400b01d403550b81c1d03c6c4030032203045500c241460040c041c0c6a40007542400030464481059649035058905d9900b0a420500c0d40121081406800e107824160650b88601042c440c4520070300c90b503040c581c05940c42901c2180b081482844084000c036461401802c08100c0b0159031740b0309110a100c000213901c0d01c3c000c45442400c070790 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 555108471 1250 555107221 555107233
    0x50f0312030609041e120306170604060e07080a1a01060305042609040207080438090102010605041d010b0613091d03070f15090b070f11030a09091409 66
    0x4050005030b240040003901c0301c079040c007080a00b0070f50403c07040c002c284c010170300011180000c086c05030589403aa8415409101c00201048800201040c1c0a400540c00700c40840c41a945100240c503008454101010034001e00c510941044604203014a80c0010301e514214203a03031340c54080d400c4580403103018021901901c04030510101c1651540000070070f401030f681c100350b01400071070126000036404551700e2100050521140b40d60103900c000c0f1040019054017111514940406081110407035103507001400305035680182e00079045000a840090000c01804041500c11100003040b525075040325441c14809255034244141160f14030a03031500007a01e010700c1e10641d80000c00e00b505803c80c1e2010f08201c9e490745020306100420a03030b4000d03035090030401c03110700380405040b4180c41c0101c02689409081000210a6201c0d540d0003a000e06003010107540f1484250340d410082d0724051458040043c070040c145402c4480002900c110f543c00700202840c645400004000030b40e01072071160700c95 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 555109721 1250 555108471 555108481
    0xf0216050f060a020715120b0307030201020a0b04111f0f0206070516080d14040203060f0933040b011a09060421060c030501090c0c0c050f060705030c07050f031203 72
    0x8000c1804141c07600c115154280d403407201c0c081c0c94103010350b0701c00050f0300300c607d028640e580c9010303100300a030040700a060b160385194001b0b550f07000605802454400c01e40005018850800c88841034160301510010420002884c0e40c20604401040d80d80840e0900011000c19880014070512504158481d245042a50240d4040b50303220030070b049494410070000b5445807030041c0142d00c440003c41c6451070003410a0700c109401c2c08002803181564202e01010080d803090b0000c2c581c1c0603405c010820021504488800c113181d001b040e803c461841c5001e900740420084610700290481c0d9510340710103000712512001c9012032080c040d5403640b0000c02c0c4000c0c402c2c00340400d0400d084014107110704a95031825543c0d00280c400c0c0540d002c01182c0d03900c1c0100200c82207070054a95159081c5000089074900d41c0d6400003441440c01258015400030702328052a032145012190700c40d401201b1a03856402806d2920354a03002e5000e45401513400c0d800d01480c5080000d03d1884504024880d5821540c5e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 555110971 1250 555109721 555109729
    0xc1d0f01050f0405150a021c08010909030e09070e0906100512151305060f0a1d0a240807080105040c1211090103030203030417030c0d18050d0f0216050f 67
    0x2120b0040b0b0260201040300003030b40e50318003045d007100304905400140c031809000c00c081d0420a003440c10500c04281d803600301030300c01d900152940c1500c4005500090385282401c00b00e600326885002c2c00d0b000352010041c490001d400001c200310348241282d01140720b640300d00a10080f9400c403441103021030410b102c0b0420054014008660000c000ca5a80b40f2000c0300d040000e480d0821030b00c4429450341e0716401c1c4035040c2480d803074034486180107591180119141402000032008101d100c0c9058214000c04268200026001407c1d008980307c011681c0c140242f4230300249900c2449506018820b81c880000d4114060145c04d10071030304200e1940b14146054200d100d80c141644d0100c03050100e403884541d455884e1096240a540668011503c0785030500d00300451180b814901c2e40c480307000340204048580300404541005e0080314021441c9100000c00234566581000020300502400f846a014aa4810940f206600155003210030f034690250300402d04625500400e500b10150550b10081424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 555112221 1250 555110971 555110977
    0x1008030901110f0a1202010b04150902070501061a0a02010608061015110a0312050612060c07080d02030703020c10020702010905060703051309020a02071409220b0a0c1d0f0105 77
    0xc1e03002d0a48500d5520607101c1d90500404c85400c817040e856820b5410500d41d13091064088603142a101006070f50b0300030101112205081c400c041c80c5540026a040c1046801e4004600134001c4078104001d40070140c01e40441c5400944c2d40d040150f103003d400040c2030000191490090001d904610185420300c86d444040301c000f50710000500c591805042003d880c00c000c544000d41c025a581405880c45103481c2c0c007640d802030700d501e1160038016a0500e01c200c020507000e400119151016a40310100d203002034081c02983c640c17001251010007040741e5290190020617031101c1d85ca081da4000e80700720384942d00321b009008003e40058840c1030b00780083e007042d500418005000e820712600b801d80940e144541030241e41c11600d01c264000c0340c042001f43d010003c12020b01851101070f025a05001c1c04100c5004c8000d004030702c1c0d19150025160076024110942c0c0001c0d0300b01300380d003425141c00d10b9140041c205101c402c0380083c405010034141c1c1100c0241a0103c1c10000b0b003140301070034054004548030f030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 555113471 1250 555112221 555112247
    0xc0306032a0b030a050f01080a2f03070b03060306010b03091c0e06030703061802071e06060b0408061e04080315190e01030606090e030d022b0905061008030901 70
    0x1107603401c004102441d00c940a10b1258a05603000703c2c480c03920081703140d081e00c0107921016040d40050500c0c0c00040c00300e82c07003c11364590602c1c02d581c0300405051040d049000c0f40740b11900340c080c600001c90401d0030031000350710031030040e400c81e03a10340d03a100d05104840c403049882809940003601c00c40203510440400c035404207400d1a0840c00c614105001492651003610b040c0c0100c0d54850003000a403003000f0b00c081d9a20403e41007182049400c0e00d4003104540300391003da0050000440701c10812840d5132002c0d01030107140415584507074580c0d0109981328019034060b110450314102c42211801c4054030075124a034894806411515400b0b0307416a001100c00589070301100020600700c6451001000c000201031458001000d54910301303000c01210340e83d4000001c0c650030801c2d84098820000708481b0701d0700c1003c900503641e0816508068400c07281c2c680c10801000b440304800f05106035600000e014a01038000d60b00d058481c50082428101e083c4200c001c1c0350801d014200d1a907006401d020038503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 555114721 1250 555113471 555113543
    0x9060507051e010f0b0927031b160503010c09030303021315020721021014070b0a06090b030a020a0603021b150f0a053606010807090c030603 62
    0x21001550320703080202d514401c00d8000d07995520100b0070900d00e80a140c00b4840c00751703504500d50500d19050040380411a6800c000940c0007403440b02801820405c0310840e203410b55941104001403849540c6542e0594031955404110610104080c5018401c07080c2c2c84055840f00e030b0b000341c03443c1d030305078040e400141c80300c10010882071000450010302000d105061401e41d015101013400e0058182242d000482142904001d2401850060301c44192498000a0a08013001d80c1100344400d03140301d105440d002041f15801800388034000c3c2c07507034111206139000d0050034446040c3c500b0030b055603030054901c0694051a041820001103020354000c000a180d40c100c086001c075080d801039850b00400c40280020a50800d040156000c0d101d030400750490301e04c500070f12690504c007010138014540d41c07902820052184d907821961220b0841140c44061002007991030381d696907541c060300e99440e8441c40c271142e801c040b4007246045c4a48160020350754000c000c0340c50303820444007003009050054600040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 555115971 1250 555114721 555114733
    0xf0a0e0109060c03020c01062102010305040203120a030c14120123091501080606040f060531050a08030a020601030809040e060414071a0a0f0201061a03090c060403030906050705 78
    0x100e01a0f01901e01144004c0c0c0b8007603542e9440c468180d085a07059171003c0d8080f036441e4080c1000c040007420840120f50240380210305030321140002820441050062070f00710400180d107600c0340b609600803060340e4071070b521901521000c56459100b00d20500d03103000305807150a001840044003400d0b940c018541c0d0203102441d81f10607000410310099043d5103a010400142d07084031015a030003400e6a521000949006080615103000e0f83c6103a01a40110024054086420035403100e0214203a0035400322030741140d4000c80d5102e01d410b40f5042c079000d0399029041400011a1080b000011500e418030307181e005041580c6161034440c0140c01c0340392a103074400e845107902c04500d00e04020a81c0510700441c2c4500841e10804d600c0b43c60088994000240310840340130103060707010030a0603034080381140d0400d4156201030400c00c134014100ca4010000d01c62000342007840115800d0050741c81f414001044484240040040000a0183e0700c401000214000003d1001c1845000503218a40c855000c6600e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 555117221 1250 555115971 555115973
    0x215040909060506090105010c030504060e0d061a18160c050703080408030309070501080c18040b0301050702030a090e0f06060703020f06180d08040b1303090b07081902060f0a0e0109 80
    0x205072800000d0941e401e5441d039061010500e80078a80d07a0050034242000903224906560240460155100301340601003d9980d0080740e44852010390f401650084041007212009a24407000300341140c500c0740540508140b280314062140d1846020b00981d181d40c41ca0a8038007542203c54584081c0c0440f00707809000da00000003810b1001401c00b40040b6409151280307441c103040303880c01300c036139024034101710b004410b0003000c40283c0200ca484580e0078000120622440020030081d00c01009031039090743c60601004589076011000d00750380000380c2e0720b0030a10fa565403180e84250405a58030042c4200060100c2d21918000b401403c0c0540310b40181c03003004810304002414100d0443d040010100000300f030110700401407109021007134030b0f810140010705140c2c4441d407500f43c004203c0d034500d00c0141e55000906004401500081c0301124100d5030715100c030b10340381301140c200e03917004843e89186a106128072800812400d20410f07415030441500d5a804000c031016004031000a100d0795a030740d240b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 555118471 1250 555117221 555117239
    0x1c03051026030d05040506010e0c041401030207050c030f010f0608030403120305040311070e01030c1502070b0a02030418020d051305030306040902040b0603090703140106080a0209060312180f1002030304021504 92
    0x1911a40c006c1015000540c035004503c0880c0c2070003041c00c01d0019040005001186200900d106514000e1800580700c4215107002460100c10000c101d5042c402c500c2e5074800ccc200150481c1c0e41200c07034030b60f081c0401d075602c203006039480c0101d01008104030034401c0c01c0b5003c18400c0d0300040d40a4000d00e0403818a412288080307080c0395031a008805803056110052040c402c03410f803907200a02a2601000c0d01100c0094001c2d1a80d03154002c9107000d040001ea021140742c03080066801406c082003281c01c080202c0312402d4000c1d07010301129600c00c0d040500040e600090b01c6852034030b841d000780c00386142d40e44a03820070006080040003283d12503a1603a110760300b9201c0802071403092030b507113004001403420f6080c012110780450710325000c1030f81032100601c25904049040c0705010340c180d640302075507210400003900b0200036064031482c0d24408900182e5002000c1580c428280040d0b8000c074924424a040c400700324060440500580d200304041401402d1522108203059207024090741000c0d16207140c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 555119721 1250 555118471 555118481
    0x10050402060f0f0414010f0c1202030f040602030418020a081503150a0203060f04180605150405070c121b110f0303160519120503090307051c03051026030d 68
    0x459850000400d0500200001940070205d00d102421304081158005c0380041c076501d05044000e2a4008900304600d0142c000c04c1996840348010000c03c5c0c8494980c100250750b5000713442000b025214842c00307000303001214400c983c503070340d401c0e0780e1408583d44103c0100c03040055541c000f07030184901c00e515a0000004c14805001d16001100542d8a051107001c0040144003200514850340c40c01d510304d841001c4580042c44900d40c001c0e0007040f140e40c1c40e40c0404c442c00e462203019800071308110410001981c0003020f00c2415100d017a0940d225440713403800716801d45000010308031042000f03002c81e0100758159001451110000c0044041e041c41102003410354003c1800c1e011808401201c040412805011a11408103606240048418a030f1955140714048103000e00c10b00030000046000381000340120340c0000e4120044a0b4108030300d00b034200740342c5c5498151f540040d00e80000308403400340020105e411a00c40202002c80c5004542d6421031509100039143c80b20700c010840b001400c03a0f18050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 555120971 1250 555119721 555119737
    0x50406152123060f03030d0f020904060335040b1602450f0402120a03021014040510110d0e060103021206070206010911040816170d0210050402060f 65
    0x1e10019000c4400000e42d08400034104520469803207400c4030494400005881010700ca507140410b4034207414140c030000713120b0084001c1d0040c3c14030901100380b184052903500c03030840c035440441500b41c45011908402d071003100fa50321a804108401c1140d47c04000181404040b42100c0e048080d45a0740015080780c14807102d84c21104c010740040b00d4202c80214607810407030301807102030b14800c450242000000b07801400e90484c0840c0c0340104e000d6440b11185804a01e80307040440700000c01908019685414101c20050518200105001d1346264803074101e000e694007100608050b0fa2001e4982d000e40400304002c01080c0d800e00a040c0094010300a0585160021029202550440c01401180c00707030040c1c0b10045070700503418400ba89a00003095411944149000101c465002103402d083e0710079a4001c40040c07045210006035410008465070403181503800030200000c0301101161161b101c1c0083c030002d03030005982c190b00040c182d00041c0d44030b07100601c2145015440242c0710207503042094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 555122221 1250 555120971 555121001
    0xd060b0a0309110607150f021204030215070e0d0303091b0303030b093301030209100302090103200d1a04060f030314040b090607060f1a09010504061521 67
    0x101c60b0107020701c41d15030502d9440103640c0c3d40d1900640361900c2e00c041d000f00c82c100001c560384104800d10405144d0560b000100f48051420380350034035080096a0700c143d464503402e000b139000003150445001e40451402c101c000b4041700000005a14181c004148141081e00d0b80c0310840c2d6a541e0303903440d031444031001c1c5201e500d00050040f2501d092100703a4500400802c80c90a40102044040001c911f042c500b01592003049600f030750203680120302a0040b502500e13000202c0c400c4c0c48240380c3e0903801802500c9402e990400c18403a02c24144404c2d4800760703650846e1b15000300410ac40f802c1c0b054020003072040d503101940b6200001341010030111039003a032041815184002003442019408100c240f03e11015918050500e0f007001003040091040064151144030005002010847c103504010060360402404000100070240d54105d0309807014820340c0f060804100100303861601d44034110a40d0048050441c006d00000707000d40d54070f1105410508031041540d88800c0103046409400382e0315029103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 555123471 1250 555122221 555122231
    0xf0a02071104061d010b0a270e01091a04110a0e04110d06061101112704090b090d1106060108060102031b0c0a14010c060f0b0607050a0b0915010b0d060b0a03 69
    0x413141e032408001a0041042001c1c01c104403409540d0040c1501c0741c80c100080c01d001d03034001c1131014082d8000c0350351101880480351400094084a540c2c84140c2c00742104a4040c48030704408104400c40c3c81c03408050300e20400501c2841c2100340300344400c1d205004007600010b64a451a95074565907008024592140c580311002400042d6208440088080c00307480280620710303002c10324074000c0c0100c4d0300704d0030100d00b03104c409540005001055201044090b00410064400d810700400300c200c01c1b50640600e2068a0f00d180d280e074441d0700f1004007403c10402600c601e8503071000440d80c4e1000600078074110300c802d2001c44220045411102d405456440c02010300c0c0d1603041c10301a00c00241c1d07003c3c0c03d00c140c0081c40e02c422231f41c2284400c1c0360750768800e100107036907221544800d0042c00600d00f4541c0210f0701060040070400000340080c82c86002d00c1c40d0b0f201c03039614440e00980d1840108007101180c030f401c1d00101b11050311240030b0240701000480100303601d912504800460380010a200000031f40b64 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 555124721 1250 555123471 555123509
    0x4080f070c0e0406060807030f0201082e030201110c0915010201200405091503150603010e0102120a050c0c1f0f0f1505010f090509040615060504030314030f0a0207110406 75
    0x161003170070000d14052000d030240c90700e0b61f03c3d0402d603200b52480c045e042c0a4690001000c0c00030309001c41004030028010b62182c82001c44080702c0c80356241c04228042032030844410002040080c00b890030150003000000c00d070f510580b4030303c0002145481e05055648404c1c6000e007808801c00460220541408540d41380c0d4584400c1024400e405025030410b504000c14194660728003082d504494000f640d40071600b0b485000110b40100423208516425505c00328105055030380c660402030041c00c00d82000e002c2a100c849412010b8460b240000c0300ca03901c12600f01c0b85022046a00b025a10070701480082c51a08241d04201070f510b080895040d0103a480d090040b104c0001d0040d140680004c7c6411080d149a0030005410404e00b8022280724030002c10000c0d042150907000b039007180ba80003c1d000c03100c50b81ea00d00900f0580041c0403c901140d10924071450010700c0b0811349101e404000c1c40c4240799100e0300000002507021070003d40d05074003e4900101e158a503402004001c1802d42200201039030740c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 555125971 1250 555124721 555124733
    0x10031112240f0402010c020910050306070f0305010f0f030b0a111303050f06091e0a02040f0621080a080402040902030a03050c0f062a1224010f0804080f070c0e04 71
    0xc0206906a40b103807890a00000d43d034040c101e5081103506407410b508546501118096203010b80e8000340d85446410200502c107940111150801ea00644040c407559883d080341246d0b40100d806014214001c0000800c08070320a80c0180e0b40000c6911000541085a0006080c1591200174544d110107683c1d02e0800410004015003404603403007002406140c18100c0c3e1443c0c40e504902c95242449401d4001c1c840d043c103081c071403400401d500800800a84c003015000398098a030b244218640100c0b04401004401d4541d0081c1064aa004403102d140c5003c10905032180306d030140060745c20070740d036586200c0140c40402560304000c0c003035283d140d25041900501881c019076281d0146050b00603505110000d81134480e02e1100f02c0003050000001081002505d51a000b4190040d0f02244018103209084446e03036514410030303541ca0140740c240e41d509001174a01402000b001340000d10124006004202c51030081c290886d40d0405251601c41d087d180c4900d648955000f078070751015104240010040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 555127221 1250 555125971 555126043
    0xe060d0305130915080d0e060a0302160f0618170f04090e06042906060702040209090f070e040504080d0b120d08010e09010b13050c07060504080d05010b0310031112 72
    0x4246801403c000f450f200000300244a01f20340383d40500400726800005030702940580c1c0340d0503240d80210700800380c5c1e03050503144000000b50640b6854a40045044440c203038545052129820200d84c4102441c200c015001c2a032210101d000308034410f110102d00c0040a028080d98401108000d0030203003040c0c2440c45074071800f098107104a02074103d042d44803101c0b0605240e400901104c000e61604614004100179100c0c00540d1944008540c3c1048480a404001c40f8000c40c07a50b51110b40400d0400c5c1803008851054402911441050060509550117038010000c8044040c01d418030f0b01a56030321042c644140c03c0aa82c0110b482d101c010700a5807007040455506c01e185000138445001d100700400c040501180082c02500d407210000b998500d00c040458011039440300c0100107e142c1404c0c140c3c00c0b90000c61402070403501380800055009602e400ba2802207010481769511346155030b590843c152040340b2080e41160440c1c2114100c10400d0210311610001c0d140580038540002d152500951 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 555128471 1250 555127221 555127229
    0x3060903020d0905010c02091005090f3112090b0c03040e0a09020a03150213061d04061401121509051b040b040b03130b041209050a0e060d0305130915 66
    0x29000c802004141e07404100c40c1b801907010340e80c1441c10713181e441190201e00c01e683c004070f0f08001c480061244101c0100d460324820b11048584a060221010108050700514409004021030150321400450720000566010a03181e00300002d41c2c80d624440d001d1075800c21403501c846504042010000814204000365202800800c200409c881f5603000070082001404050b140b045269505500e4892a0341102c482c94540c04190881c2d0741e80b5680101602c640e410700050910005c0c001a00c07030b0809000b601d0607151080042007124000600440700040c0d002000da00c11900c4551420303108403d0f005010190101e5540400c05250a280860109107840344000030100d040000b03701e0a0b0302c030f40560b010742d41c0c0364281c03035a40d4403684074009a4bc1d05038000a41040c0b805000c1c8410050b10003443e41c2000d0301c944841c0406030317880040080d5107807607220b4800a011040002400c40c5400b46203140400d00c203040150400c0700f2a20042911283c5400c8005081c0d540c1d140426858043d40c00a4010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 555129721 1250 555128471 555128477
    0x15010917070603110714010f0b09041a09190c0501110609030f07140331030312052509060215010b0711120313090e0307030203070305090109050a03060903020d 70
    0xe20060214207940d0701e070034400e0324101640d51200080d65090201100c040340c0d0081c40c14845a00003407035880c002c101a40b400240145030030340c000006d080201495210b250080c000426040504c420305502e040c000300980034501684012081c03060382c4000c41c0d1b508500901044900c6410000007518010400c0180700040e407004081083c41d440010440b481c90303a0035281d05489251900d041d05e41e052003085848101c0c0004a200c2a0145c05d80e54085a1119188203903c401c000c1c1d9500d207600c50741c4a0002030001614440001240201d0390020361308100b0307400c08070485814040c08964000810001d980c002031400108000c020703030400040c82589005003800e0f6144d454000d40900901c18040000d01c8e2000841d03000d180e9581c0d00b032000007049000010b80741e445114001e4140505043c4c0a2144d00b6481c20303548515803080001501c1107154141c00452802c3c4031134500783c8403070308070780d544078104031030300502040300c0e121403503004004c502c6003402080352019440c0203802c1c5a640c02004e820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 555130971 1250 555129721 555129749
    0x91d0f090c090a0903090306062702040b0915040e0711100b0d020d030201091b031b1203050c07050307060f03050603060c031803090402071a090105010f03021002010212150109 77
    0x60303030b5550403002c0e820070f003810b100054240462401381c1d04d004550348040c06a40c45d0580c00035491103a20b02c0701c00d4031020215014151600c03010020100d00840c00340000e541c50601271007030117042074200c082545100c1030b0540d040950724080b40020a00403200040015486080c40e0030000c070402c440b81f5802004102401519110300100b512480f542d00080d100340b4107050b0000c01e00d4000c4d401400d000b500003c040b403100015600881d0709000c60301c001c8441036a800e44a56a0324141c0d11a002551240c000c1080c1030801510304075129080901c458800d40980c1c0750001c0c0c0382d82d00300540c100800d13481d26071881d20100740d54003404403200189214003d4101d041000181d604000480341d009804207041c90040461901d01c901d1030250880700c03500b092000400c0010721a100d1b1a800c20700d0350218944010703a49a80301a03007641c3c420300c207074614044401c1e07060005103080304600182d035240344001030519450040f421164241510047d01903203034603482c481203591101100000d4180324002000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 555132221 1250 555130971 555130993
    0xc120f04030b1b03041e05072402070e1506040f060e0103050c0703080703050c071a181f110d050a0605150c1b03070506070812071d10091d0f09 63
    0x900d02c0018802091002e5112405180b07130404003086e81c9958010085510f1140c4840f032008400911b15400365102caa0071600098140c80080e2007019140c06072004d030182d4a03044520310340144420803035507100d8814070000c030784200405240c0d0000d0290750b4a00d900c018159001404442016156002d100c0041241c034000c04e420a0b11160881d080307150000b03040d550300e6582c5000f8004c0c41401170132052071700e10b44070284040c0e1401c00e0241e900035840035881042e10700300c0760355101d000d00150300511400c0c00c01c10405140d944290114a9408142403800401445100032100110382e4201004c0d5544810b005c0d07410300c06000d8400388840c9070054035100407607101c5075680056000541c0034680c84030024406403001d015200003400040c00c42c039240d5006281070070190304480c0901c40301001050010b00300034800c2e020407114060059501c0e00d50100c030000d200d080104141494184244d0315000110312404605030f182802d01c11a08540505001010700d0098102034500e00c1076602c0011280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 555133471 1250 555132221 555132271
    0x2030a0f11071b0b040801060510020303070801060c06110406081603020c0a02090c091f020c0904030f08041a070c060b060406200a0b0403080105031c080a020c120f04030b 75
    0x1942c080e00011000400d42030400703144002e00d1690003801c0d0046001c01c00154950054224606482040751042842c104a600c100d07034900013100c00c0c0300028007030001000040e00803448501128011074020660490803800e03030232030346d105a000c0710008621104000300040c03d00b003140c240d03400c245802e6282c140a400c041e07a8171000060003a00c41c44401002c074100f2492070003103650200d4054650305c01d12100c4040e001003450101030000240c02003002c00c1e0341500e040c08800d4880c0d60306446803440d0600020302251300e100010300031614401c0720400d0701203600345148003a1182000d81d45041d0180400c0c904581600c001c420005d028620074482230090680003501c1c031040d92901c90481c00400103000c83e482c588190b811001e000b9464800c1030009250317024000c00e059810941c02ca030b80050b01044001611404030304000c0c000b40820001c03e07191b0307270a60010455111058222142030400c0001d1111680c8881d404070b21481000800308100903408840690280006040742d5288181c0d101c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 555134721 1250 555133471 555133477
    0x5150106020d0903081c090b0906041e0807080703030b09041209080708030904200708070c05090403020a020913050f03030a0e160504020d09150905010b060c030d052802030a0f11 78
    0x100d40c1e01442c0c4020002906c903a0101d100b40e50400103942c083c0c10902c122030b848820681d420340d041c180d803124100341c00009030300c16041e8031f502201e0135180c044d554540b4121508813101c110205611001140031581d09d03a0022030046000320100c180445243e50040c103000007d038041005608469401c0024190120070f841c29001d042d140891000301c61000306a085100c0d41d1b00345a200c1c80410284180903440d006001140d06c94205240d4803038650041020000c000c880040044c0c0c84a90060014100f030408a6000350f0102d0f04845201c0ba582e031140d0412900420041640e40302104001c54540b107802044181c2e091b00c0f0140103c021844000c43d01040c05000306030003036800060395150300155900c00075030260001c101150140c420b08804018020b00c6806640940c04e0000b4125a450300c0003c481c24100c2d00070003580b03000c80119102c0054500100001c00d51810055000044a940185401d060740c200b000107a4906d0512030100803a441c1da081c5c107a4092a040a503100d141c541411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 555135971 1250 555134721 555134737
    0x237050705134208060703291216090207051504030f030504050312090d02070f050d02190b030903030906010e04080418060b0f250b0403050705010905150106020d090308 74
    0x9042c07010300c3c00c03e90b00d0003954070303940e0400390820003640e002807025804100b40d405100c441d5818490b019992400311003010145a0070715110080c51814031461601c040d1040141444d03c0580320003482400708892441036941c8094081a0009401e908200082c0460341d2184002c0004c480141401c1d02c005201000d006200310903d60340c1e0f80800c060107003c0054405201c3c0c410ba084002e80b8200807002d458604004444016108155000c0781c0341d69940500815920702130034108501030146c00308511a1141e01c0c1c1045034046000c0081400e106260055219002c004001d5170340b800e02d42c0c1110301d002016800b07040e41c807042000b40000a40c1000072201101c108035140c40c8000d0a051800d0024812584000c0e150f64001843c0560407001c4000f900074685407040c4008460034a000e0b40c00c40340c010510061110000000103400a0301810140480c18040c1000040c0d042050b80c03071900d081807081d8281d0a03141491f00411801c3d90400030b480304c04000d483d01d08861032550391030700824050040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 555137221 1250 555135971 555136031
    0x180607080a060806040f0b09010506060f1606020706060302031519022506050a0c0c050316050a0609081e180907120f02040e1006023705070513 63
    0x204603501c400d5007101010b05518001c1d180b003402c2c81e2a01540006404808841c030a40c1040000d001003010320070f90384a10b4010301102c1c50035001a5118039036a204860b049081a4904102400700b0080e1000c1c040e154403c580000d6540e041d80105490403d000c51013041c01d00c01d610801110302292129081802d480e09030150b203c0e901c0b45c40d01425960951515910f0030104666481805650742019008604105041000640a100c2284c0c40310b0100c1001d4110362040242e004060101c82d1810009030003101550080e41240d6110810303036181001c00c0c2c5116102082000d045000c0303800e0b2041d0140065109480c241002500241c48110030106911a80800000420060140c0030b1001000d042c2401000415440204907000350814000c4250386101407002405050407201c4200c159689030b001081d5548038420710440c0646220390b10b107000e0170810143c040a210111924038420b01c54409001a41c0c1406c0500040c03008095081e2021400d03c2d0803103038001c0f2103260f110520760f0100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 555138471 1250 555137221 555137237
    0x10804060e03072123071106030408091306050d020d1104020c060a14190e280b25080606090a151211030a020918010f0905180607 57
    0x20510300020051007420070124040000d0480c204882150b01e00c05400612046001c41c00055008503a174441c204802ca90814200c49802104060a006803855612500080c1c004104000100d03106030401e44048602500200e1a0801450517400e84400d0107103401041051529240016150344030003400a4000c88040c95003070300b030004640e510041104007500941da10841c5100450303549404a482c054010b1030170b081e4103500306812070340758014090107500300072000e02c03d80110002e00780510181034910030030000000307403081c84010081e88aa0700e0400304841c000ca041241060400034805140100940074100c104030180c20030203514421071030425040d0b5030790801328032284940f02080b941709a0100f40000e004d400700040541440b000e07590f00d50000c0842402000b41c51940d04400100241440042c007444c003194080c0080007001030407085007a4210303040d001c42442c281c000022000744820240a806414000c1c40e401c00303201461021800c440c07166550f1141400703003103202044268 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 555139721 1250 555138471 555138473
    0x6070e100c050d05130509040f2a06051b0f031905120405030c15040f0605190e01020d0e0a08030105040b010504030b0a060e06030d08010b0c15010e1e040809010804 72
    0x501c1240d040294807500301c03038540400b00c2d00039089420071440001c2c0e07031000380c1c004611402d20600090245600050800e0501115603c0103643c203001ca181e50340c8000c000755441c4c2e580942d21202c00c001c0c80ca03600e601d41d840d0701582003004070b020325284408071a48107a90a040080c0e0000c03c5a0015003240303003002c01c2c03100c01d0100b15810b10805149101e504036000c14801800b10202c002c02d65051588211002c0e94210000e400c801002180c0180080c4d8103260036501140303298010311b511213810f00c20031940c02c505810300801c440040b14800c8072071798040707001096110103101b0301c9181c054910050601c0200c59444c0f1465205c14000d90b4011a10707506030242d01c0e4012403c0d1800345a100031000640c1c680405040b0081100d84112000b2503041e001080a074200800da5003510001a80d030600701d0780c2042c0e04c502d034651200e910b25489205400302c03a0004040400514042d2a5030500c2d1042410142c140c41c69440c000c109180c1461002d00c03c0c040007602490468a12000070300300100b10b42c0d11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 555140971 1250 555139721 555139727
    0x40c03062403241e03060905070e01060504030b0c0904021603030b03160803030403110c060a09030b01060822030207090603030e04110a23220807060206070e10 70
    0x65035210910450312980e00d4500c0c085228242440641c80756420482c20783c04800c9103000140000c9007048001c80e40c0d1060051210883d010a0495442c8204050403662a075407101152103444059466401c1014180610107800c48418014070340d40c0751590605003181c0720600050030241c0852860400003c0b003560030703100c94041d42d80001c2c003d00f40401d560418200a00034114500c503a82c4a40240348490301001c809004070340075550000015804d641c0e41eaa815102c1c600700b160013281c0c0f0720442005d104180e4940c0020301c0c06941070f5441524691452406820412041e0005010b100342c1c481082003180e01c0e072260100100b154540310b001c0c85001d0030140d00340070003034000d842c0040c1007910200c24903802c9021046a04025038040100c440000712030040c83c0190141c000001d0000b424544d070707940c4a0350b64811006200e654040c0f42c000744502c0d0120812940c14852170388004030748200101c480c24801c400c0103060034000751155190003503000700414a501e00075441400715032841405184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 555142221 1250 555140971 555140981
    0x80304060e1b017b180c0f0f080c090708071809020c060603070f09020708090a0807080d02071a0723032a0d0c05030f030a02090f10020a02040c03 64
    0x3a9811a1440c01030f1280c0d070041070450070401c4e00b0420b01c1510041c0020480c0700303110000341c1100d01c11483e650700051500c40b01506180f029410071101150b40c08000c1518800640d000340458080281c01a26061307010102d810998044525504192011502d0381c0700c200c0c8080d842025403070b101c501645c689030190341c00c080c0e01e201caa04a2810340707000304441030141e0091282518460403940301e55240c00405949803484d01802908000e100c03400c0080e0013441d0041e10101c0d100300c00250410b07070310101007452641035900510890744410301c01c2060b81420710034144d28210300d2018095503070500741403099a01016480300d0741d071500029610240110004042c0002003601101c0b11b42005901c0d02d107030350741c00c94941d4412924040364505990389040d00d134030744e004450b20080c100044544030151004e0310b0148003914240810000c1031107201010000358461003480a00584800014040c0301601c6100710055001d041c62610345080c1c2a00011001e404540c1102c020030440c0840b201100540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 555143471 1250 555142221 555142307
    0x20903120a05040303080132010e030f010c170f01140d02180412030e06010504050601050c06090102042102010815040609060602030910030605060712020703080304060e1b01 76
    0x4144865070a600034001c1c81240d009a541c040242d8a07181e0009152040340d10126402e0005a50820b8079503120b05d18012003401410041418580c0e440400c2c00c00c52000200c00c8241d5450107105035103070f00080e28a0583d24800072084107071400241c10744060406004002c0b800390750848201c042d80e16000d403040e1155018110300354106d54540a9104008203690456009101c10740ca544010300c0381c46100d9171401000024009640790006001c0103000203450366042110810142540301001c014150251040c4130005a64502d03024100c2d0f581401c9260603504843d9003014400541c0c0c0c028043d9030070035515004c001c000c2003c48001001030203a43d21070318905090210000300260044060400c5100c10386010341440f17140e020407800c9540c13034043c0a42c40b580501c203a0000ca600400e821800401c1030040b54141c3c0d17100d403910344860700111400c895040e2200003500d0107100a000708001609024000102415007000203800c940e11808409a1848409820407110380711541002e880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 555144721 1250 555143471 555143503
    0xa06020706200d050603122203210e060a054e0a0204031a040305070b13052415190305240609071d0a1502070f0315020903 54
    0x3100b41c4405400403508541c02050120b4500700018603981800b081102c901c003586d60f030451800d0300351003840c14110b4000b1191100c18050f6080800040c105090700280c0f0b80748120345464606042c0302c000d00121104141fa40280fa0038041004501c0e001001c0d180c0c07025814901e800340d0044a10307001c9000c482c00689a03220386000310301300d101e544030b80080e10342c04080c1c1494810540c1da0300c0c0315030242e1040e403000a21010103d809402c0481100c00c12070b421034071a00e0128601041c039112450f26035030989094569101c801c84600400a0030803203c0c0385036401109900103c800300003951201352000317081e0203001050140380c44e000d90343c03072000250340c007401d21200149507200e007002540c810011002a8545a400d10140351004000207618804c4c2e030000c4c8520070700c0e620340008680c024981901051100790108840703001d561241c4070200903200050440b4032040c80a0b070300034941801a4014030179000840b000b030000c112050020a09d0500140025954401140100e480e022411f68208c0d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 555145971 1250 555144721 555144761
    0xa0506030307050d1e030e1222060801050a06080f0c0307031508030901090f12110f040e371115040e0105130c050d0507140703080103060e010209030a06020706 70
    0x1d000e400c20b12035804c0310658454911304040705d490580850751307130303002c0b2403083d62118002d403122013a000020110009080c02551210600c11103604440d00e80e40c11003000f082c503100050105003080c00072038004140ca403410030058240b003c04899003043c098070419034000000002001c150003034110300c070300d42d016003811102c2540e40e80105460b900025103090000c0e141c4500002c400003000c9083d000e07144903c101c0c652008869841c11340800300303806079981040c80b84950100c5079442e071195640c0018104090003000306000701d0154441004550703804900e102d043c00e101c1e5216051104800642c1c81406540c3c504403031000550852060740040f954a0000076004c00c00b042d460000c82e04841040d1181d01d2000010304004c02607520007480040011020b014602e0b049003079800194010005050004141130785080c01005a4003800007900841c1942004000300b180391700c100d903103032002603000f1400d00c0c0c074490000384c80d02160100500b20640210b203040030b2091691000c21110302210341c2c444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 555147221 1250 555145971 555145993
    0x405060a0801140409171e0a050703141603080402030f01051f05040209100e0a05040e240c030601050c101802090a06290d0e0a0b0c0a05030a050603030705 68
    0x42202024001c54031076018800721070103d410280150740d40e445d40049050540c40203448950b80c25000000d008101c410200c0911901c044140000c01806215944495442c100c90130043c0082c200e106648901100800c00d01610310b208104051080741e0514240e00b15032210300001e403806400d8400c0b1031803541b901c401e00c841411141402025190340000c40783e00a581d41b020403040f0f0007002d82103034000d0b8030f02c002c0c50209482050007084100c4000c190350461a252030100342155502902c10549900019000c001c0b03040304c00d00601440002001c110b042d29101042031030500014140314140b090100d0808030704542403041d0284650740d00d10400960061089102038240007100990113007030382001040112000780121020b86202c0079038034421880320b02501c0030000c8210207030300507428140036441c41c5074038034054001d091444400030080c0c821b00d41045045880068011420580108048862190814280c2e5071140c505500040c036a030790500483d00311302c6540001880c90299510bc04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 555148471 1250 555147221 555147227
    0x601120f0516020706020303091209040905060a1e0501030510020c03040e09033004020f04090611191b120903021c030e0418060c0e1207030501050f0705031503030405060a 75
    0x50100e64050f82240c440c81e40e2030310244e032284825690740010341c11400e004000f030040a0700400b8488009400000e820045072242ca041170b1082d110468042d45a40c00c02c104804040d00301c05882901c10010441303949140e8840e40d650280601104c00c1ca500481e0890508000f0700568006006d5002c802c0760b41c0c42c100300d00b582c80750b000394540006400198182c201900d2541201c00608040040340000e90b1115020842c0d103252207000711b540325031a0055100000c0c250302807541e200b91000300079612041348004040c81000705003001020407a0303085200307405441840c100b11ba0705420060146902100090031904040c203a00007942003800301032481040c0c080362181e02c50040c02907503001ca200060104201c107076181c8003900304450460950103000300320140c1c042d0b203400e100ca090440b01c04030307903201107100038010046403501074004a800b0410701800380500380e482a005c0c60072160742d140120001d070490201400310190003004e0412216a031310100100c801070800204a20307100d24541c4001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 555149721 1250 555148471 555148501
    0x615051306031e023007080604020a0e06010f120b0a081609050709061110110d0c030c0903260313051c02070e0c0910050711010c08030601120f05 64
    0x44440020581e210610710100b007203105034165000b0505c041c2400032240006a2600d0301c100e00c22001400074031144040300c1004101c0043c5101d02c05400d6034a81401004003001c0558403880740404035508114560380d01c00c6604a4a220a05000e001040c10704402c1c00200a09203900e5001100d2040c0862050400180d042c0101250400312000c642c49038140f01c1aa0400d468480118010750001e02c5554000e02d543e031012401c0e001190b0018585c0f40c1003800707903800220700900300b500008845200b0291b034020000b103888a4102480882a1490024007104851201808105c91807032910000ea0082203011800854411364507101c2c1081042c030180b814203440c04444c03d11a0384c5024a030b0b0420000340700d41e80f84041d000341c2610340c540841c0c1c15903035500401104481c8802c0010307500c030b503841da94482c2e0000c210f5a2029200c00d96031801c10000341144a00c0c3d4144102c0605540c0060300c003c00300c0c2e50206080ca0a185413070303004005240940300d0064002d00e5542090100612880c5480c42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 555150971 1250 555149721 555149723
    0x2d0f1203130209150918030d020c0f0a080c0f07060912080c0109150c0c0b06010f020f060403180b090a0b1806040816060c0c0311010c02130f051005030a061505130603 73
    0x101e085ca844001d000d16000101802c4080300d031704180f0401c1d940090715409000000700c0e04050300c1c10a0f90309003809081000e090b8080b680c1c080007003403a04e120b0b5410451a40380c0114203008020141c14580b024002d0700b000d2250086414074101e4000c07c1211010568241101241c020301c001c0c040b914109000f8201280a0451280703040c6442c1d01c29845101c803d071000d03800000e18001a01d502c0c00464000f0f549040390703000e6210b03d43c000d40d04840d041020700d1255000b0394914400e41801000a15001c030554801503002c0d0080c010000c031647d8a004031012242141482a81d0b5041200e009407250244805076500c84d8000c14006440600400c00b8140c80d0003910310000050385490301901d604840c0c00001c5d00f00e102240e01400010010050319000c2d00c014140170306001a41e500050250483e014540300c40c685800450010441034011030342c0000f501c03e000c480850510780803035a10215120040d01890316000401c0401250b480c11a0182001502d807000206007010588003801941c48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 555152221 1250 555150971 555150979
    0xa0305090c0406180e01060317030702070f05061b07050a090209131401090903032a030e0c0d03180302190e0a11070f03030e2d0f120313020915 63
    0x101c00742592070280715041c00e445044103003680f82c04c0c080302d454009100c1c8488040d0343d590f039440e02101140003260312124421f0300745a1a50b5034513200e50000d0400a407907201002c1c600600703800340b01a55505069803020031050700f01d200e0600c002400c0a1502c0115804190404030f10070000c1050310380c5030010002071900f174400503442e005c141d1155040f41c10302d00380301080c5603400005103c08002c40d00f0850405000b40f4021590b4060440100c050b4114103c1c1518014030380c0e603035980b4590f0907004099000e99180007401020240b2404502c108220560040402000301041d0b00d00ca0081103140001e96009440000403c40031a0b000c0c43c000185c8c0941c07407140c42c40500180250340c00b4040d282360802c0e40d00342e190074051107980d00e50305456890000c0701419202c038102603002c1400c03c500358412402400ca885041020011100c126400c440290030305d1f005a1914001041c0005105000d05071807080e9a41d01d544019100c1c844d82c4462070002d6000d00e407042032041c0c8940340821081040c81c212 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 555153471 1250 555152221 555152233
    0x70320150a0c23240702030f07050a06060603020c0c040c140c070e091e06070207030803060102011820150702010c0c0306020c030a030e0c2805030f0a06111e1c020a030509 75
    0x10000701821203048405c6401a807003085000391480030240605900b521800c01c86058401c1582c0ea0016503885801803400aa40440c000302404020400e61008110030340c0d0810128580100040911600460006500c1400280003400010070414040100300411b484541800e024490a855080040192204048065903a102e44001003226401040103030010b0240d1890f60380c60103c140c000030300c4a41507550b501060005501c40c000045901e03440781810264020041c1c203102c00c0c14241c8540c1d180580c02c40460105450314040c203c0d0205a024248000c01c10607624007510f000d01c1035000144414000b04424040560000c050000c030702c001d80f41440303c8000802d282d0340c0d41d08404500c0e644501c42c0d22080801c400d8039001255600c59140c4c2d1250300c0c0b0340341c1e00030a10b05030488070f803800668001e205010a126a510800d010a085400c1c541c1c5060204605040c4501448001c10304044001510607030400c0540054003000c0a2200255100d03c1407503400703801004201c4201145016403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 555154721 1250 555153471 555153523
    0xf0f02010908120a08042117070507031713050307030c0507060c1214190207030b01050105041211010e0d0609020f0a06051204050f070320150a0c23 65
    0x11a420b1440074180c51011300f016144201215107000141c400e40e403032a107807000e40c0040d44003450b046400b00c1117902e5084100d803ea00b580e0169034001421501003200c1440b0220010f42d00603172482401008070704114290303ca0307902c20380e15540000c01c000c00b50b1000156590805421150485060780540706503100b0550701c05007968450100c02005100c0c44945451002c09070103107070945000c40704403110030709103844441803525a0300c00308508000751313001c00320400070891402d2045000d1b00007883d1850915281451240000000c02001400c3c02210755241006901c1600d075400400d100416a003000c089a0414100402411800381c0c062a15103801103ca8101001500c084641950300e03240382480b00c030403041e43c4000107001180c0b1402943e0324442e15400400031000034602843c40303407031101c01d559030260b03211403030701140d80c0140b06c000b8202d052000d1f41d5003907444800c501e080900403422681740520b0400b05041030b000b131042440c040c04c21034401c009500004101d240642e10814015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 555155971 1250 555154721 555154723
    0x10605040b0304120315080f011802030d14070605040812090d050a21091b09060524130f090c020f0c0d150f0b0112050603060c03060303070f0f02010908 67
    0x8500a0109552040000c00c0025840c10801130241c0d509107800030b40800d11350081d1516000650103254580d104008100c825002845024901c1d151180302c10780c100c000742d01280c4c5406450759100c0900c6001c64a034079040a4a50484182c0c60b445203080285190a03d00070440340c000c4401c6c2010703030086030001880d0b14000200200c90000d280c940d10704110b0a100c00b01c820012165100041b01004401d0014002c0c040c02920f115606c2005440c045013080348690079000700952015031030700c1c14088100328a40f00c4080110b5003d40d07500d0000c14400101d041440140b29100a0038402c0810780b0380050200c94000280b001d03140349078400d104503804018220790303070380941103048001e070480b40485501c0d141c051110310105101d110006480070f40c40f400601210f1111021401c5980c82c0c03c0118001d41c2d00156600d480b0510b4401005141000c80100351b4070a401426007000c0d81e000800301d41305680400503502d07030036486000d80c2040941c5140c680b40440e42c0040827408070750755000c0480d103000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 555157221 1250 555155971 555155977
    0x102040303170f04080906090d0c0905060d0314091c0c0501021905060a0e01110a020703051e030a0c0c0b040603290108040b04020a17030309060106030b030307020f0a0824010605 78
    0x70f1012104042c0d030320f443c0c480540540c0403402d60355024a080018940c0d944481540d048610302440008008928023940324042ea84001d007034511650b01c04d425100020313004100300400352509100c0c01c0d00c0b180305202180300d900d00c94400698100303903441d4540822509002d9981965020307400d80b071900e0003401c0107140c821350603e002465034110300e00060b0a02c8042d4409a000101480041640f40c020b05c0300880c2070b400b10820800580180c1014010f000e0300f0422040034060710072444015195505003240c80340192001c460400501040c5502030290489515015103006015503640e00d940700360180c02810849040c50804150102484504050419180c0d4186040e16598526039903583c1c1d4001c0e038140100100e80c812060007004c110490004280c2d040c22034040e000319546d0030428442803400005a22200030981007400c0d256154a02006507102940c0c1070303170400020f000e23150001c1c0403604c054001044500c40e1801c031a4011180324038503a83c1400e9694102c0e0b0f140d0300c4070703800c880c030788 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 555158471 1250 555157221 555157231
    0x50d05041206051009051f211b0305030a02010609061706060d032c120601061b0303020417010b010f0e090117010207020405161101061203050307050f0c010204030317 73
    0x403040c59000000b0074015080150703c28031000301c2005003615034841c44200e03242500e42c0f80390102a10351400c1004800a00d01025284607441508820344038034124848448140c03000f00401035405101094614441b001b202450703012058035114100c000c0c0090081030203204081e00c190401c0400100c21444a4865034035002d0b01c0c0c00f600030342c3c2e60032040c0028038550500481c00c000c032014040e100c00c0000084036102c1013226114004004003c2d040010b008000140000c590301320400421813a600886200804d082107520111030000d1810180d0080c0030399803184448244e900c00a5002c10300640c4103180c0c2100980722074076522180c3d0021251000c11340202c80d0403281c040d0062041c0000342c0f5050012001107000075240c07100541c042029201e00340c0317108189040004010400f15044003082480c14090700080003100d01e0a1903c0754214000d41c1d004e0180407000000c9180c10340301c5c100b1609042e08070280250384401124010b03000703610620042d00001c031550038992524203030007011b500407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 555159721 1250 555158471 555158489
    0x1e011b08160503060111120306010e04140f0606070804030507081501060906050d0608010e0706030b1008060f1c0f120f051c0b19030b0604231005120a050d0504 70
    0x5903030002400d440c83c0e0300107000581400048282c0030b56000080144001070540304d0040c1d6181e007800b500160504a103046a984960b0030314041700c1013850480c007142e034860100e040441203a00e917400403603032610400d50042c1c600140001c011007070000001e003680803145c8030001c8818004520a10300d06912081c0560400191241020490380b4419400b500c04034403801d000280a50307a0702049821991003c5002c42542c1242104000d00740d0940b00d105846d22040c1e540c0c03c1c0324040c0c40401081148002e0155128401d894280140d6440c2c10009680300860340c0b004103d400344900f49081807843c5180121844080074001040c1c3c03611580103280042415156a400c0c00800a8409200a11480301065042d980d036108051503840c4440400d00003180d403a0b40e64490f042d070626150300b08004200d50b0080b402c00c1c0320341a2517820703056503415501c40c0035181c80040d124100180020081980701550042c40400f11030501070f40414002c3c4a03a1181d001c40e1100403c00405441e00e00840c030520700a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 555160971 1250 555159721 555159751
    0x1020304140319180b0406110c04180206160b190506030712080c10020a09080c03030a080402120a080d02090f090402010206010611011b2601050a12051e011b08 70
    0x546805103e641c01801c44c8880054a040d03115400101d540d04a80e000c1d0000074441ca5241030380c04000c6c010300ba145c25040da02406030504041c100d080080030348000a00905000400c840c0c0240d030701642030703800c0350300404610341c9081403001c9105900000f0403030384080303150201041300e61500003000d208858643c3c0d1900240f41e000e0700c896105403c0f088141d1000d00800704800903250301c80c801850220720369190140b117141420341172403500c1e0b82e03d43c20b00e000340c0c0100030000120750081e20381584a681140c541a6485070111503508250380528000c02068010500a03201c40468015041d0032600f0380781c10301c003004404200260301e0341c10b68000e40960010801400510710030072043c540300e10010300100381d03038800800915034032000c4180100000c1072803240f60030300f40d80c40b2003d0240d00d41c0159449025410440019072405041c030884508406c4020403601700541070100c100c10300e54243c10344c40d4031700704268818040c203507084c40544500381d00d845142885001c7e0500350301174555600f4880b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 555162221 1250 555160971 555161017
    0x280204060f1d0a180209030109050f070501030501030b15030307120201020927040318030b090a05011103091f09051501080d0f1205060f0901081513030e1509060c010203041403 77
    0x604c03121101e494103580c00300004903040e10240101041039201e0401460b800318090083e80c01c1c10a070703800660401d400d0000410205004295480d0042003117041051112150b00c0002d00c2c40c410300720010003800044909048494041d80500890042175445141c2c56040002240c0c0030003480841d09002c0001d9004500828420034981e04156141e51100c942503840f900c4195520b0030885201c4200d0f0302540c1ca00081003030a000d001004d0100540c00c605600305540b00c03513110084c0d846800141e100a04141000350483d810403e03481c0c3c1c01400707484e0003400b40c00f0310b66401c0a00340140b81041c4125000c140f460f0344920484c031a0359103103030b403a540103928040f1850098007000c0c21055102010150500e020380d5080000e5009200e50320061004c112404e02403000501c00412407200c5000e00b416140219400210303070782502c3c41c200c60303a00a041e01410140c000c0d01402070300d0780d0031002c08180a401200c0560086000f14081e8070f2024011030301741d1070349949124100964002c4401f0740c80c80c003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 555163471 1250 555162221 555162239
    0x9060609180c0408070b1b010e07120204061d04170c0703020f060906030705070c0608060a0501030f0e06100326090d03020304050d080d05060315280204060f1d0a 71
    0x550401c50b44200c03a840c107507480b40c0c1d2030325104a50308450144980000c007113540d0b0100d81d18400584400a00a211040b40b801e012511000b0706d100710500210b0150510f001c65440d0fa114401a1840c4e280041000e10310500102000b10111400c8501103002580d14116103142030a0320313070501d03c060042242c0340c10f5a00340400306400442040e0401304c18044407442c2d6842401a6104150716943c2c02d45409003420039031190100c0c2c2d40311005000c03601084c0181a2070360301e2083d054a01c04e007008141000802c00e604010241411492500d0040f10288106441d5503080002140d001d030001c803441c0c10b10102200884d205400300c032840040100054241d50401014210341c1501900543c0c1c02d1903503170745c0071404039440020100d90351240016206e500c0c000780d2142c150402c1007030f0000e040548401c200d56050301e4020b40960207000e0314003a1218034880102c0c21a000d006204010754449941d040301401d0603400c801c112001c200303161420a14000403d1219a400400814210015203000320364 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 555164721 1250 555163471 555163519
    0x1a0901030c0b0d020d060306150b07080304030309050307051b040f06150f0210050f010911030403080606130f18060602031602040b150c0c01120c09050405090c090f0609060609 77
    0x103d40c03807035028800c08800c1c9510388200030082d4082c82020030140a480e1409442000b16040a100440b09100200100b01d01c1800d8030352060b81070800003000c500c00d0401c13034514001e007100203180740326441c0c1c00d11020f090711011407610401543e040c010341000d40b10903c03c0e0350060041d070503343d900340c1e5400b084078071442c030241d02601140180c5008a1001e03142400b651421201001c05040080040200e8045841443c482c10b54444c0b15074190f0405540040c01004044c00c2c040c4070321001f14001100042c010041001000d5031415103002c5540c4104080c05100d9600d0600c10032032405d0b5001546600200c12902000c038220023140c018140c81d82000010b02c0c60441094000c0d60100e201000d10500300300801200d00003900030039000d03c0c0388000500f82160403401d562414204112006c0c80e50b042240401a188100c4010980f5596907214500e420b0f01107002550011210003400162525403003024050002030703561601641d540804c0c05110b1180000803a0801001c104035100b0210900c0c43d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 555165971 1250 555164721 555164737
    0x20a020f0105120106081b03061c0c21020315132004020409020c0d0207050d06050a0902100c03030606020a0b28020a12150b1209010f0f1a0901030c0b 66
    0x1c19414810b00116205800714245c01c8100851141e10a03c0407881810410b80400400d40c0d4500c4d04c2c0d807400ca03011400c0700c20360b05020701001c036040402804000d410740f09a0090081180400d015040c00e401034014180c403150168081e0181e07030207120102c0e9407000014411a103200c05804110740342c0c2d594101d4904140d4061059600e100819015666940010001414810b10160300d0303030941c0020f58200154440300c030017035510192003002580c0b1090040c40b1119000400080e4980d60380da0351101801035a0002540300305410340782e82c207080c2c100f40500c40d12800bc2d43c08000300d035103c0740c05a0b034a0188410141039007001800184807010f50035003042c00700f6080c035000b85038155083c0c03480c0240c0e000007914a010501c00c088032400c062451045503c0d070241c0ca40208441c4d860508404003903c16282803600d6007042e80d0008036001002d4010000c200e881c46810480310000206c3c81000f1f150300c00c503060705400c08912803901840c02d0031081e810303a904103000b95461407400d406d045080c1e0007084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 555167221 1250 555165971 555165977
    0x30f02010f0c0c060f0b03070b09040b0307061701171902120703080a030c0e1c1a04060902040c0201050708180c0a0f050a08031206011d04051501030f020901020a020f01 74
    0x41046600c070a9402000c0700084161501d2410003494a01403040d1055101940704640c684200300d16141e070300180e203000702d40b202001c0d55910300419001ca0040d0501a018980510070443d001814943c80341d102008401151920400c40c7d0301c4074000c150340351b50703000b8102040e404080201c4540031743d0589008510301c01810400c40021640703481d401d1042c95802a5440840860032003504c40c2c160054982c4041d40d45810042c00c0280c0001504145807034000d00d584651901080c4104503c074607600c04d03104c00c0080281240d207031030b10304600a0411b0a104a004904140c0410140c03030050103034078003544194852040940d03d0740a1244021a6184201c044d8400c0c4c07460b540b00c5484c2c00500e1009410140d1401039114200300c02d00c03001812503400145903500800444440b8400000d01e25008102441c014040e0443d038498502d61003c03041d00d85a02500d09000d011400500694620340c8003000c1e00e080c4100120949080c0882c0249115140940c000144410062a184040032442d441c141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 555168471 1250 555167221 555167231
    0x303051008060414070f05031002030a0e030c0102070611040b031602120f120c0c1e1e0606090606160311151e13080d0b0102150c04060908010b010c030f0201 69
    0x94201d01c0d001040e5020744503044c2490602e040b9030307410b0103d00003038485000c810018a18200c0820390b1400f4048440811550120107d900200030350010b8001410352404c407901c5801c2e280005000f903216000407100c0c01d1400745400540100101138400710396554400a041d9950305a8044225410b1807030074007180990080c8106052075800901415000000c45035100e82c02e2154600300180090141055900144491441a94001100c0707a600031071510000039aa0900d00c02c501d0404400b54001d10523090f4403944070038150014049200d21411070b0725600584446090240d03920814a6110b081c1c0ca215840034046409040c4d04000915501d00315442080b1089501004140603108412041c1c0c3d1001c0c55803501c410100b500e904026404021800b504443e9a40c075071622441900c1c4c841c0c01c2e1118a1140d490b80280645411001c0c40301481900d0700c0c01e511064595030250283c20301081c111140422412030510417144a0001070b114101c60a000c3e071825038100030740b0076207401159200d07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 555169721 1250 555168471 555168479
    0x30605060412110604050609060a090305060c120f040206090d030903021302090a080118031d041e0608161a0c0f0109031b020a06320307020106050a1203030510 70
    0x1040080008003003106042d9001e48079442c00b10078608082040d10310800d0184801c1c052030f07859004a0b00000d5044803d41e94814a2220640d60300301c6035031000d13000d405214100306851600c1002041540c400c107003c1c1c10f899580c07c216040f4008191000f80d000340b401d10414009003005a917903c1100c0c024188211f15070380c0e039800141505081801144c10a4001c02e4211341810060003401c05041500c00a00c0100803a803489500f20403144405010801d1645100300726488a281780603807220068028032000c0c60072400803d48944140c112141c2a15100c40090020300c003207614400d42e8619591104003e1900100034105469802000d004207030400a01030342d41000c022200c01c1250240020800001a050150841c130320800c40c2c15410354032141c1100140d444031542420780b184d5081c0f45c403030100c1c001880d83c5101b01c1d0070000700310200d20007101ca041704404005140310381d04540c001d00c51251580284030401e15284100041d2840118041b0002030190300b20503840354034501921106035035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 555170971 1250 555169721 555169729
    0x7051605030c0d170a150801090c05030c15030c0307020106180507020118020904020111120a020f060106030e070902090d0b01230a081513050a050d030c0924030605 72
    0x11661044465510029041c840c08805002c503005118550400445003c1240d03880000884003d02c1e80014660304c03049824071002c1804540007404054000300514889458400140c2c40b06002d160f119210742000c0c00542d2400102143c220741916400c2419625213003c44a0750b0f410141c07004040d55240c0c2c401055400c1207820045800030440c078007082c141000310001c2d0071902d56a4000300180c078580380a10160301e8a00015400a5080c40d180c0c030f019801d81106810642040d0281740d0040c4c0001c1c5102500c1d9001800c51301c3e0302901015220181d03a10743c400ea0480d070303c4403481c00640d00a01d104002401a5501030310060304040c120a0004445a41c6c2c0c1076010340903040003410820b400c520072000310894002c40700000781691444010741c00e200040b0b0b078441030741842103241400080003c03225410025440c4a0640c0082100d03582032042c40d1030b6444041d980c040400082c030f0701c07501c0c2400b103116685030383c05c40c0e0002820f5003c42c0c41d10307158155440c01d6002e40307106050302c5040004840e29 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 555172221 1250 555170971 555171007
    0x1003051806101404020703091e0f08030c0106170c090c0c0304030804090f0b09011505070203120909070203120f0402180705030618060603060103091a0702010c080703230705 76
    0xb20b903082401c515007400c001c0148a40203030704543c0558414048840040c1e0020804c0c07040d603010001e06104041070b0240f540b40c019603500404200d151031217002030941c10000180034201a281c00901019441e0720384c0100c2641280e0344240b05500144150034a42040d48425801c11070b03c1c9412460b09107501380d09032450780170758400c40704568001400c001c501c0061291740c41c81050490b047c00041d5061000800741c3c607060040440c84494810326980c1c00b409101194002036014050340e0001000300301301c40407034201c52807860140e913102001807546072010044900110b03131004040599241c0d2941d09240640c02003081340c0040c00c00d50b80442919000c882c1078468080c5948440e038a1800c0001d004c24040c4030902d13010030201010600c5030300e07942c941c160303a4051003c2c039000607500c0ba281000c0301030050048820080c07482c1102031022060b41074010f40c85501644d1180010f13034890042c01c034112aa41c64030000641003141d04114041812016036070020451720300303c0e003005040b41000101c0d83c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 555173471 1250 555172221 555172231
    0x1050c1b0f011404140613060b0604210b07080c0301060f030f1404050f012a02070b1305090c070b1b0c0706051315050703120603080a0e120c1003051806 67
    0x30003c80070082080040149000740c103900348058040c5080c0307000d2581190311408002490385440301c0184c90b0544420040e10000c062a03410640341c0c411182c401c0346000f031a020291000110f0400003030740e00c0e00403401140200d02d403111040c5168070702481210031281454014041580300d50301980d0042c100d01403066076621004002c9841d00f01f91400780e1500c83d681d0003030401c6074140095030001c003241e070741e2a410b500d203d8000035900181c10b0720200c0c18038200b50031500e9160000305580001d00e1860f0341000903100c00b0ba03040d81c01e9840d10358141e103680c01a81d0703008140900e038400280000d00c1c880c4841045d0504010140d051141d08a1564102400c3d9000305000440c0481c1c210880c86040140d640284609804584082d20a1303400800d14403840c1000340034410310144c4400790140aa10000043d40c104818549905200c0c3c0c004203a004682d07100c034801d114092101c02c2c4440f0210710003880e01001082800402c02c141c00590240900809030b076103440b2072240400d6042c41c02d000031840b0f9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 555174721 1250 555173471 555173501
    0xd0f0c0306090b010f030e0709050c180a0b0304150f02042d0e01170a060516120509030a35070906030603030813061e1d01050c1b0f01 59
    0x141861020040c100c1d0a03039444144030900b000c2101c0d900ba42c00003c4103545440c207260104e15003428100c010303e00754031640120f112a01e800c040101c254800c80140506101800051403d6402e44040220250440c003500c8940c1c0341c200301250004070591040a40c54083ca0700c041079480112402200f00c3c1c2090340449059546038000b0344100d40b401d0034070008404016420b118442c00c0100e1440080c030305005902000032000c0820010020070000b1484080e8400303070510007468500039800e800032005074502c1c081034920342410704e40d040314080c4601c00c0504400450403d42e900d4400c59003041040d04520320307601d003070800c040b803886d80464400c45411001c071040e0080c00c044a005215054a031701c0442010f00e803c409000095000140c00c2d004070489003490881415800c1040c024510400e4024246e520740401d085c1c0e075485a0055019a6031050200a8090407404000c0c2601c02c1102c0c01d010018003084050208034015a00705c035000c150790103d60007141404100b03400c4408450b880206 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 555175971 1250 555174721 555174731
    0x903260a32010812280203270130020307050408030d0212100e010b07111e0108010f0b030a02071106040303031a060a080a0b280305010c020c0a0b07080d0f 68
    0x24400042020030b01d8262400b215500c2c1110a14041c200c21000080301401701c0c1c80c041409240510070015030700700d0340c01c4001208001d00e0440c2d02c64003a0394074030240790214a138841a560040c1c001140c1303a15092401d900704c44400d1840310400001d500003014102405410301c004142d400041015165100c0109001a86c03010b032402c03103000141c4020012a51090b19030000c1c4480c00d069000c142c11a0302c400841a220880c9140001e404450911280e810079552070180c60900445c8c030300044c001d5000e0301c03001c040b66217400c0d84800b030303c1031401284c20800f0f08002164045040b580213140c03040c01080003a0808124000141c6d00e075100c1da00580c0000c0c0c4030400505100780c1e46d0170f030100700c090469507a4542042500e014090000090414901071b5171b45001c10f240b511040384002c41180070400c91240c014014040300c200c100b003030206440b41c0d0710b041c4286142500000b07410144070380042101c81d040d032070210040c0155021000440e1901001e00c00c0b4242c01c05280100e02c508651210b000c0380c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 555177221 1250 555175971 555175979
    0x30c020303161b05012406050418060e0c1209030c1e010204031b03140106060804020f120316031b0f021210020a050903010c0206010b1b0703020303030a0903260a3201 73
    0x400c070105503401b140705a02c41080000329002411202290a111100402d42561181e03c0008105c90f520522865100800700160300d0b40440080444001c001c01c03148890729400540360352406400b1400207240e00081d0f0700943e6150b40074030340ca110000310700050702d06500c030b582d41145201c1c4241040d56410081c003090003008030220807010520030324002040f49520f8181c00801c208030103040640105212911050709440d214001c3ca280c020200c1102d81d0b0311390308801c884d60f45030034203000d8000580c200f43c600041072030300c065040250f40200302c10520031400d80800500b60b806940903961480f805044500d01003107800a044051050340301c1c0f40c0c4800d40c101c181400d655901d0004000c5401c10001801500041010780d190854205a92070358400e004050600c0e00c00e094001960502c40442000940c0580c0e070031154000d032107a035460703000d8031640360b15007030980800c141d003120104110002190558594045460400f40088402c2c1c80f151140c0944002c20544190902030444000148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 555178471 1250 555177221 555177251
    0x10e0d02060c031504020f1e180613030206090d0516030b0711100c030e07030605100e1e040c0b03090105010e1b120a061a030412030c020303161b0501 66
    0x1a4000c1d000e40c942491131926080c1d601101c001c40300058420303980804c803c4004a440c10640780e494003e1100105e25220b00c448181042c5c0114812002e1000494200c1485050180035642d00d201401016986a8116820070206d0781011031150341019002d460040070a1081000042030343d000c8026032005130450a11103150342e401400709090049030012030402d031a00080481d07944880100c0003405082c914800c801074404040b03901094400c400c408802d0100642c040e50048504040d000140d40da60304688410407001c5030400ca880b040002c110a0283c00c0c20806644140302d40c02e945087c586078004c00605410645041907a80e66410040c8101a80c01c1c004507009480c0b1162540c0c40c070b01e0b44c000c0d043d003481001c0403510b2005141002c40c0150466801001c0505210508000e40c10301d000445d005940044038155030140c440c284d003049d118000d101e02510050507078085d52031a03403004150302094201002188c02c0090b80548080304814040c1200400b40c802c01c000319151102e00060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 555179721 1250 555178471 555178483
    0x702130222150806121506030708010507080408071a1305061503030d020706021b031e120a020a0c140f15010f0312050c0a080405030118150b030f010e0d02 68
    0x12103582603100901c4041c4002001550b40038440c6819141940d0307041c04200c20444142c50581350703200304292554201c803d1001170303100d10020340c11620455038920034a0f01b030f59000d58841010800c0040490081503041000f86001c1c3c0c05030021844800034a200300c041110200e801c0e51003800350704504c400308001800707255004044c0c00c07000c00030510040f0003e82c1b288141e1901071340d5560700140b54002c00c00c950301541c43c3c40004130145c026950745080d825440707501042604040c503130301030380c4c00d10081760030010b07104500500b00b80340110703035500c4000400070740c408034900341480141c81d0071000140780c0f0707800035503085003010250094200502e40f0074a48415401c9100229107035100611000c003030f416010003140d4000c0b410344038400302810103903014854200c880034103004039001d04090040c56001070040303035016802040119030b20810100054001d400c0101070411301003140445c101c00c5d13004400d61306001401e45000c400004a42800c40f502e000040c1160307001100d04a4840c0d405000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555180971 1250 555179721 555179767
    0x20a050318070803030a0b041d070b090d050703050c2106070c030c020a0b0408120301030209060d1406010e01060f020f0c0f03010b12010f06150807030c1103070515010605070f02130207021302 84
    0x8600c031441c501c641070391641881d004007078100b1008330f01c0307038074a07507841560000c880e800405540409440b030600c2c83c0c0302c6d0820b043c600d0140003201803404011101c10703503946001da4030101909039a00c5004080303803024198001034042040c240003000c056612848143d00621112240641d46e51421000d2030428a06031498501c551040c0010005070b126040740f1648030703100301d03402901031140d071070510702c082c2d800948800c01e07114040021402d59a4240384905a43d10ba455000e0040341e43c0b041203903102c0109081c2c3c01240c000700300ba218030303052081d400c002800b40240082410035030b80006c40d203c0b001607815410305a44035200c1c0c00c0542d13258070420700130705a03a80b280c1c0442940210041d1800002030140000c1542d582c9050003410310480d4100c211004000542c0e56800d402d04000ba9210000f9911003c098002d8000282050180040b2074040780d000154042220362502000605588062180d140c035130204842130060703a40c5014000d54244c20000142c0b00c80d2204400c002c10310303401807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555182221 1250 555180971 555181001
    0xc0501050c100b03030c0a03020f060a0e1e010b150702130207030507080a140a0f08072f030702030f060a061208031503100501090b011101020a050318070803030a0b04 73
    0x8068510600c000c1015444810042d00100d1800301c49804a442c0d44260300c80d40281c1d010300080982016170110701074200b0f50050301101e269032203d06050f4100c40d601500a041075000e0a41d02020040612a5289a5100400029001074000c010031120160700c039180b0030f40800022428210718110031500074040d000703001141083c91954026180e40b040c4140505107038000f19066031901d100e0390b65402440040c0300104e40702e01b651507015003407225030603694000c1010f010004000d1403241462019518440e0601d4400c410401000050529441c07039500d035500081240c0f00250f10104880341400140c0360060079145801c85030502103c00c180c00c540c04001d448551300380800c20701e80a582d0003211110040c10f020b00418002440d00307202a15000200341886e000280b26030965024030680c0000380c84110102c2c100b90051401c03232082045441c08140c1c1400402c5034030801c4034180c8000c280d6801102c2c903068440c11090710750707001200e0005485446602d40700e61424180581b500c0640098 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555183471 1250 555182221 555182227
    0x90204050c0904110c1e070308040303030f0b040c080c0a0e0a060801080f1c030c05070c0e09120309032b050a0c1103130e1317030f0c070f030e01051903090c050105 72
    0x100056481b214803c2002e4024428202c0d926020361091001c0c800840e80728504607a125036900e400b0b00500041058050703078926003031f510542030601e40076030082c40406988215469407090417400464002c143c4030340c01c01c528403044c000c280d11006c1d030680141005842e4040c1c5580345c103803120710f81040070800c034541d9003121846000e010380c00c045e65140c4072a94200403403002c100740c030100c2d1580690038010b8164001000c0004000d81d1012849005442440a6640360010f5509495042c84107985078122603000704000b01c0c00c1d1034a25805444e06e00310100520407440403c161106a1b032040c0c1d80c2488940d528107070084019003000300c3d0305a105144028506140361030264040d070b0030444c803a0700c21031040940043c002d00801350500c60f01030380c4006c1820791283c070120100c0c05c0380c108070b030070080090a03400450401c4100400b40c45003213038082c0002c4c281030800d03501101c421034001d201c10306001041c03003208104101540340d0002d12006035400900c03015142808a0700940d030b68040c40c1440010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555184721 1250 555183471 555183487
    0x31a0711070b0d11160b0106020706080c0703031b02010209010306060f0206180f010903080f06010903080d020a0525021906140c030d1103070e030304060e100201090204050c090411 79
    0x49403440c2219202100c0703945a52000340d44030f000e40b04415900f84040c00024040f5100c2d00b411090a02450180311012400d81c4c0714402a40da40c100e600600300403e503128001180e0390580c000500d03c0b58800e25011800300206092009001012040c860260f500070840741090350f81071040c8030090400389004030000658650207912504068031005040c030411080000f9207030304100c1a10512822402009403040c90704000f0304d1540140c80946604404030b021400300e600c1040d10600317a9030000ba0891070100440c010303000a50009514406104082c0815280d510301400100c0c0b08900001103200d0380480c41c41001035921140030664250140c0d4102400040d9100246007085070f022840c9a603100c95841c00306265000b04c9904420060402564207000d9a803a005940640c159849645080004208054803070103680141000113914104140c1140f82c10407202030540150300001500308816000714042d6202100d1050100b00005070182d886e0505126030340c2400003d048071387c01e100344 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555185971 1250 555184721 555184723
    0xd0b031207020d03110d17010806041a100f0b03270304171c0e03060a0911060307120c0203090117040b01140111010507120606080618150406031a0711 66
    0x407000040d01460140030020100350040304086440b000140072200101c1149500800c6540080300b2100c08569800000517003802c002402da000d80d40c484135120000401c22407c0800d00300007481d9503020b6a088034005090080003041c0d01c00b510044000e17a0356443d201c000410075000302d4103800c5a0510700100c0511051012094909841d0042c210783c030925400c021051420700d102c1d0301c42d0000c0720f8a5044500e040d070441501d04189801f901600c403e6610f81d02d40da03080300c020340d130017503d61090303943c4468a610300140112740c4103149040a08210311000c1e80f110881d00c0144070000968000a01d0310851340c5c22035a03190324010340c88040d40b03181c41c065444441402040c40341d80035141c0030782d440c1d640c1c90303000d03404d2480c0d02c1c2c107104001c00a030b00d000d072001420607514201104d48246410340c003041c44c51150900a1041c00702414600c1c140543c0000721481c04002000c8051034560701c40007924582e04d40c00340c20300540c016480301c050380c2683c41d0062440c180140025003401000d030704007000c2840c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555187221 1250 555185971 555185977
    0x150507020a0c050d0c05040c030b090906060109080a0b01030318031b030b0109020c19020301091416060c0b07080a0e0a08070b0a0207200a091103040b0f22080705010603080d0b0312 79
    0x7c1d90081015130790020f007a0040e008684002c3d501c0b400000400c41ea48000140640c0310320026681c986926585010884d1510354045001e005c150310b841c01400070902800780c0480e01c88010705800e0a455480c2c41ea000c1c3d243d01800700b258a0301c65080c1c00c109100c0640201d50141c00c5c40001140b03020402c98190355104c2103004000864210170300260190740d004c0d8130440585800c20400f200e2407048515140d11080b0801c1c3c0380407000803101d00401c003548501c14030000550b0010aa1145464909007034508000050000141c0d5481d8008010013a07002d001e1081454442e41c9640d48400c5186800c18002d0001011020031074818000200881e80103140740c00e01c004200030035801c03e4007210114a841c0c0e081e0f00300d240050309080380f00c1c080b48082401144a240205207484141d1034543c00311902000507240c0005504d100703c5098400c0001e0140c10381064460501d6a00d03007840c0d641d50a080d6107460740182c0d030482021944221a8500b03000e402c060500032000307801e15040c42e0202d229030380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555188471 1250 555187221 555187229
    0x50102071b0501090302040b0f0a0b0c100c08040f051e0312010b090612040314030c0307030c09060207210c06020606010207060206461b02070b030a0207150507020a0c050d0c 76
    0x10346449030408c40343c440040c100c100c072a021f416600140d4480f03c0c25200703588040165070039403050b0050130044106c284510410162640d0307c81060b078036580c850814117402990141c5043c0211402c119858031504003041200340c0103406140c460400d08e0240348500816403001c01018802c000d025826940d030070071203803400300d1403200c449551200e0a085440030340480130000d00500010600ca10a0305e448007a61241d920780d90140188240e041c000c407895075080c40340f5000f6a01c402c80910164441b44400502c0702d1070300110040003040c540350320340e103080a5844100942c200d041401055681030180c030014104c503000820060414003001501d100d9152500a440124040e80c0000310f000814002600382003100d4021052128846030b0001388602c291801c0c0c44000002c410000e540042034100c11103004601c0ca03419503544c0500b4034003075800b4060440d00e03490003c01a40c0341c501d90b44503a9010303c040394001e185c51606480c18105902c001d800042c442c1c40000900c00004044002440c151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555189721 1250 555188471 555188479
    0x70f030b0a0f062a110411090a03020f121006030b06010903080a0c0201052b151a0c0a0c030809041d031c022104021903020102060a05150d050102071b0501090302 71
    0x38146440080e40340c031304000011409200b0308040107040c4540307003660320b800c40e400700c404000c0c0701c2083c0d020070118840c40303a01039000344000c038080016242c6202e41c1400440c1c0036045a202110015605041030500c0800a0400313554403014004d103d070354442c1d03580c802400c1c00c11036040380c1152100d13030349030249600311030800071300410b1201164422415540074000502d68500f2071008043c91340b18084082945240603460320040f060740c81440d4181c076003120f000700c5184c40200201c2000c800c05070300400d1b1158880c41a500200c000901c0c05020000842c0106081d07030303c4011400c200000da55203500d240601181c6031245803249440401200d41035611000046c00c513881040d4004041d0041c00c0d0908070f01d0fa8410a00b0500d02e8a40613210b00ca94801c0b41c0c04482280030034504e80300203001d030001a0040c0d00160000f050300c101607000e1604845402207018040300304800050160409a07803c480c2650080f480750b04000104411000368080b03a064642650b05000c0000d10340144d03848003900c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555190971 1250 555189721 555189737
    0x203180f100c14030c030f09010c170a062408100f14030109060608010b0102010b09070503010e04053c06280f020f04060801120f1101020114070f030b0a0f06 69
    0x107a400350f02031000c00300d01e48543c980c50786006032032880701d90400ca402c00c0403c1c144200140b007180f03042c0b0425038018495210040024101e040300f4072036040c005c0003690380954442012454484040e04c1408410a15018504000700b10100918207074010740448203002032210140030312102140e161064420340711490400940c1080024054001170380043d01c06ca04c0c042003c44c84002c190008402044280c0080c401c0b0f103207c40601941c11011110b800c0012410b000600580e070780c11350301c0b640250281d42210000038049001812101d1003001c0381007808640e0b020b000d0300d0b4045e51004203c480d80708020f02640c0c5000c08002c24232982204c4140d030050300e04110422150040d6200b6504030020910854541c0c1200c00200584d502500030400810503240001600460300d0110060441e4401210440030315980c5d42d0100d040d0050000a065540302c2000c4500d86407803040503481250a550354044401c44c04001070200e504100e030b200d0041d000078909200f00340b03e070a4000d080f03da552030040c075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555192221 1250 555190971 555190991
    0x30f140a0305072007080d08090607080c040803030108150108030304020d0228080c012712020109081906181e230601060e3c040204090203180f10 64
    0x4a05134080344102500002c0c0fa03102641c200002a29800d5403500c00c2125260b280a000584400b40300710f40c04501a0b001038001689584a1703074101e500100340d0410707941410340300c1040a0950700244c000309500d5202d10f00c80501000c0d18100180144100000b0f1891401c058000c1009511500c0c030203800b50391541103125114420741800c000b1115000e00744e0113a07584807003505840c0c80c4480d04560000b0700c1c0c00c8400c506076210060b4400d2140700013110741c4d41245403035100722042070480810307414001c00302000152003405004641d11404291201c999811140c5032440444281d0441c1001607085004080e0009076522010042c407030121080000d035984a20300521410744900b484403503400b015400014001001846138142c1e025034442c007104044203820701c01e00b200441c915903946041c000007400c910004610b000c400406191005004920312004a82a0b900c1548100d690907800001c00281600ca111400d000040140140070401c00c0302d400c040d95042c00070200c40821f5500d03c02c200c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555193471 1250 555192221 555192227
    0x1a0a0e01050906070f2406031208160c0204020f0307020606121606180902040e191517070906080709140c09091e040803091b030d0302250501020403030f140a030507 72
    0x1700c0e0401b00810407150380d1802d00740e4000a80b4140c402210b016410315500c45035903001c0c1c1c207601d205a620004103c04440e001f50212401c7c49450010383c0c22903030801030300041c07000003001503108000d190010a03c0b41000418409080c00480382047c59420141c1100e190860000030b80c000c03600300e480d10210301303050b207600303100c1080d8942d20102c00c1520020300068044107960f0340c1481107480700c000e000c1d40346802c0d0300c41d019540c9035900700910020041003800b500e101c050408043c1c1500d003040340d49440e2102c145070101d61803604254426404220100070700034070343c003804210340e01c031412a00403400d14030311140710313801503500c00b6114072680300029524081c603c4070f03444c41c45480c02e4050083d05103405c12031107030b620a0354202c2c1580180740c180303511524003042510080001030001c0c0b152601c4002d0460003074010800034040b80340b420181c1c8000003606020408854024030006940b54079601d00a08003002a2081005100240c08541000c1c10249c0a80b2081c0355039090104113580e07204011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555194721 1250 555193471 555193493
    0x1c080c070611120f0a0902060901030e100533060702220c0302030114010305090a06051b04030503040905180d230d06050a170c040c02071a0a0e01050906070f 69
    0x141c01100046102c0040d4001c1030700040c0507103094000800d1311380700c0d07480340820340351811406134200740100203403282c65200340e0019155034012001c1d2503c0200d103c0702c00703003a42d8050300c107005480c0b08040007004913304031201403102c10a1007014110030748481d010a0b11b6003d008400b9228811440b800416128901200a40d000c540101040070034008400a00250000c0c000c0b02002b1b8081910400c0700d5002e44101c900504c005c800030643e50482e035603050082c110007440c148800c0401000d0b19081c01c14030001e000075501c10409903442d182000103440490704000c10001c0a152a130195078401c000208249445004503d0040c50b80044d010078101d0600102a81014113000003400c29140c0d40300354411016034001316940705140340d5a094a03d407043c82824104416086844c08040300c0c07400303500940c0942244c3c0103480c03926541384200780301c1c800004540c3d07d0b5030100180516030340b0b6114000c0f81090742c0900f40281820341c2200803403d070f8080c0381001041204514011000d01c070f0000c3d0b00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555195971 1250 555194721 555194741
    0x718050109170a17220501120509010e010c08150118030b04050102040b030a0b010206091614032806060503030301241e1d040b09060108070c06020313051c080c0706 72
    0x28440e1002c0041d548444c1d02e6100000c0700d241101c080d643c602c00d03401d03000c0700f01003110030595a440303c000000004c200280405000c98480390741e54000100f44802c28007400d201640301d0340307401105182049403169120b200d990f1160410200c6440003a143c07685052040c2540d030843e4084006170b40c0c5160042c02440303070303801a202c810004000c01400b0130450300901c0da0060203034250395070fa40b209449d01d60b581e501c000a6510f451110f1409000045e2002c400040005d4010100d03072800714000103484000c80303d070041405c1ca0741c51403840c5080c02114081c510040c102a4020352466260803044200b20030421315926010640c00c908552151040c589100013440716081d0985180c5200f201801d2520040300309610105865184020383c909442a448554400341c0301c900700785d82d5840110780c0980c0c01012981030040e200109004124540302440c030031252194103810704aa1784c10300d14038004201e140500c8148242541040e5550b102103065080020085030a03200d124a02c0c1140107040d207110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555197221 1250 555195971 555195983
    0x1902010f1a01030e06013206040b0301030210020601141c0209070305071112040306020307050708040b0403030e03161502071d0601110f060708040f02180718050109170a 74
    0x5403404102103007415942007030001d807400c228030701c070b00d15402da1189400d01c56034009920500d42d55821000074000143e8000c00c03ca0100541c1c40460002020703608640c0100016001c040018411130410b036a0b103100d02d0034140002c00c041d41c54000b886031380c50100c44216024080200e440780701d0782002e0a6071002181d000b0480c00503498001c60003001404100c96150004544550200482002003106440205058145860a401c549a19000e54000f9000d0401c12400b000504d010840c850054005006001c0d0303c5a03030307245141070052000310b024001c10f110380c002150b0503045240f200e41e05401c8031000c400345502c02c00d0000c3d00342d0902c0b50302d9103d654503a9941504200c1084c211383d40300e1146000362503c112290110820b10341d5540417500c440b10360380c810000318281e40e009406250b4000e101d03040d41280304103980d010a98070020030b03084909481404007801303030a903044142d82c03441485081c0d0030342d680d80c030b410002000b500b0180b040700c0d41e084500681c0081664280300000c501c9030841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555198471 1250 555197221 555197231
    0x70b04030c0507050d02011202070305041e030b06150d1a0411131202010f080921030a1a030c120c10021c022103070c150605091302061902010f 63
    0x4100500003403814072084809004208000c11685070684040c0201501a5521802e0000d6209104002d41c45108141c092200a00c80010b0384426060f455501c5050781400c548020f2440c581040c481d40e010304541e10402c4540d40e4946160720300e000b40c03200303840347d00c50101c0c0d00741c0050005800040c00e6958603400c541003104440787e0340e107258010241075500840781c80c90240d40c2c2000030424000c0c54402070001c0e80010388134444a100d0b990740c0c1d400201c048140c50343c102001541210038ac0040c0c1808a070b000020042100100d030a00c102d490400460300361004098149000980350301d800d5013114485e00c098010301c82c40b140c041002c1c0014190251004040b800d64502c045d681c1e200c0d0007501c0b1a41c044e000108a1b64074408141140701110b04d103c0325501e80030f0840c40b04c0b520f81000740a4002c20040210003008a00c04e40101c591000c0700c0640081c510b4140418048803150003402006169601017001c0b0040c0c40700f1085501c0d2814802c400c00201c10600d5080380076040c06038441401d14181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555199721 1250 555198471 555198473
    0x1202070c0b0f1209030702010806011815080405060a050c2b0905010501030b010911071106091906020d03091e031209030e180f01031e1704090c0c0b01050114070b04 72
    0xb9801003808980312400a20f1a55400fa42c4590300e1013000030090004505101003012940a100078105000d035007114204582d85030000c2607028803401c0c0c451000034130080c0510051290511071785400041820b800d1001c0c0c54074a00d615220701c60715071544503148a006803802c030006001108551000181307002d010362500350070440d010780005e00003070b250b2800500000962410034030443d14084444900039003082195160803500e51950081c95400c0602040304416654543c50b41008000c0811078242c0741c01d0a108000385080c0800c15114240351600d207030f403c0400d041035100c002c2e94490350035400280c11140f90888240522030050108207040c140c0000030180c1120b0300440512054420b9100c040b004034140d01c03d482d0640b2000e0002000c000117001042c2403002e0800640c00e4190034400070101d5694490381402e184885021400700070070706004140040c0240b4030300c12403a02d84100c1b04400c54842c820301d107206100b400e0500220f081d5980c83e060385041500c4529801c18a255114609 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555200971 1250 555199721 555199747
    0xe0d090b2b0b030f0d09180605102c01020312060a080703120e01080105091503030c07080f0c061c05041502073207050103050915070207241202070c0b 66
    0x2040c0b0032522902a100c07111141030800500e46141c48030355540c4546d844e00c0c10649100c1e0560710030300d05881944451012a8584540402d01428106951120003020201e0341d142c1030421b0420020079034000b826001a696130f4000240d58940b82900c81c04a00c0d0344505c5e0010790101140d42c004400707409280c2000003409448c00180406003941d4403104652143c210046580c0b40003401115400200140030540c0f0340b4410081481c001409030440345801100442549401500d60240c2007c0d48407441c480c140440034400b40505101c00c0c0c400c5800c0140c1551090300c0042048109074001d540d071030004042c80101d101000d00581c041d101190369844da410404009000c102d01718490300300d160384010b085480e8051101013102d8039005400c0c0f080c14140114054100030300b0a031038502c2288a0ac1d50203081600d000350064150790018100c0320700d030400800c0d0786a01d43d4910504030022400c5462002d401c20380007600700002604c016510700b4989002403580b025508946214000806c1003800c50803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555202221 1250 555200971 555200981
    0x5030103140105040c060309052b021e0d08040816080306120c01051603030e0601060809100b030604120519020709140402060a0c05030d020703030f0e0d090b2b 70
    0x80a50051412254056807040c00d030f035802c0c0ca004210303c26070701c400c00009100780d003c50700c0c00d4170031419600010302c040d440500003240e4501840b0004c160307078442d0140c3c98040086446040e51840d80099500c0a0f44d525519401002c240301700307002c40c00d00013904100002d001c6076501441070f0aa44150300d114280011250021500140141540d1381d180441050001d04d1212145c41651090b00e0946002150001741d0130b8440d00700d082c19180c1c40c0340e6500400900040b4082c000b1542e504500d03145c01e250951421031048004140325251140080c46038038082140c0380d000d9003142c461520710381e20b80d60807074203403185050300b00d80300c1500c250032054140d0104404c4200c1d50120fa003881829540c41d03800b01954001d0f80c000358440b0040000200e8140224001d02003139001d102580e05200c1004001e400342e900c03010341200029035070f42003850301d00c2591040d41685400750b4010080c5904010020300080382e03a000d8291441c1d4040b440c0d03c4c200380c0380144d8600c18039061516610151101401c180541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555203471 1250 555202221 555202223
    0x30105010f0816051602040906050a110403051c1403090c091605031b040503030f120c0306031009111509090114010f050d0f060b0706060801060b09060d06080601030305030103 77
    0x44004414445261040e04418001c04000c1c29003e0070900440301528142d125142000790380781c0038009a005a5124880c14584500402000c501c92416411890484070071000590918400b8001031000c501d00140500a00b8800520244c16594a48003620743c40701c0c4d10909200b2600000400c070107080e0204e00c8145c0c564080e90395245030346411000b10b5001085014010002e2014000166000c080b0324011200040642d0036628041d15900401c1c159406022000e4401100040008040d0f940881051707002e41d5030025103003582400d80010752204002803000c4c2803540c46a2114080c0090f0150b9944040780040c600d801120064400c00016084034682c0ca100f076480c18000200100c600c03843e03109001059441c000326403280c1505403a6600103104e0099029038813113040c40341140d14880e007409460040032464131121145481825200ca41d003040e101641884410807010f4260b10503603045020444445840302c113410100c00003442d03160b110384018440d81c00000149500540154180c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555204721 1250 555203471 555203477
    0x11202161203021c0b1c12020d050906070605070e06030a09060b0a060f08090f03030a0b1f08010504090f05010614090a050c0304121b060b010f0810140a12060203010501 74
    0x44000c4050b0102e00030140c0c00c4c800a6049207208107024000e078489141d0440c010005461128891080f0b82c0d50b1117450380441d24500840040b0400b980c0401076203203200c58600d40b413464200d800b00864018029490010107264859010811030303030080c28090100341014241c00d80724605000c8020107440f0300030303040d0394442c50010074000c64100b0300103034410342d505600c5101c00f0440050040b07900150080001c00300d0b00a98600790074041c803d00040d40210503441d03020a185441e80100411a1200c580400d020161440c1111007103402c0020141100c0c0704443c0000c024100d81480c1031000e0b203044005109518050b00810700c50040c903003c2115036800c0d00d004d038043d130710120541c0c2124000e0340c0d08811035502703000007800035034003400d41c85c0300011500e000c2c0b003030b0510034028140e45140d80340111a181d0b10342103070031829688044035031030144182c54040254104002c0220130400f01e8007a01040c801d940404081640b0340c03245100c014001d02c40344040c50501404e180e00250020b000d001c0c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555205971 1250 555204721 555204743
    0x11010b0d06020d1503050c0f0d0f0b01240f11030c03031003030e12190201050702040e0d110c0904060b0105130f080c0a060e0d050f030705070915081b01120216 70
    0x13002401d408040207680c3d011008081400c1c5001c108041c46201d11080c940c401c104028400002d10701c4540000030502c2590f07500025410b0441c200009032181c0f000103030046d490992044e050343e000700004070040c80c9050a0001e6008a007041d4158442c00344c42c0c50152200200b8090428902e400e603800300d90003070343c07082c900c07200800c1004003201c0541410700d0036520100c00f410a44900011036444c1340d20504101e8035120790355000c941501c641948101c1c103074010741e40e8414520340080b01c0c889c0148403103000d02014421180012040103014102a007001d980d40c1044d03019034051000c4640c240740c2080c5032b0400380d0341ea481c2814000a1350046168900600b601406c0038104144554107036035803600d0388010850f002007409100d000801c02070307946111743d070b140c0e41c40141d050000b8505680a2806009014180f410010070390b40c0030019601140f901c0042000703400d4001c60001034148501000c1f11a07609010012503120300404469030b18136200261000c98000e503401c7c914420ba100300c070400c00b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555207221 1250 555205971 555205991
    0x5280801020415050901050d090302060601030b040c09290f040f080c181003060216051b09061002010e0d050918070815040908030406050603120f040611010b0d06020d 73
    0x100340e000b00e2081100600601e050f840007180902d01030208a68185041d6017480c2ca02c041d40026502240c0c01074015030400014850a5640740c042c5a50003042900d0a01603030780707400c40003004403070240304030741c0160070190180b442c200d010850702039411600b41002c1e843e04800314005420358064070460600c40d40d06080002c1c090000714420104c1d10f4020440404804000f0781d1010740e1034000c0c8460315214551001000181041c406454861102c048a41c0720551b5441c0403032070108694540b1042855001140626680c1c141029911140a072049201e4840a03070040c3d02514025580c010680582c142828010380d001d0041c0a1041c011510000c0704d8449812441c01d002082d142c3d039000520100019034a00e40c141c0080c5040c8102500004281000f42c40701e02168000b81c400f10788107900c403c18040c90386010803c0600a03002945a1032030440005048817080c8035500c68882403200c0004c041c4440f075420340c040b818000303000e44200700080e080c0c642171009500c4291281c003400d1420704114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555208471 1250 555207221 555207223
    0xb220f1d0601060903051504020d0b04050304090f0b0607080702012c090a18140307051e010c080c07060b2e02010612020f06030405210301030201030501050f06030f040309052808 78
    0x1044980001c083c10407d0101c126069803c0c40040060340c1020003402070743c00040c60240024496401000071310b460701d041c605c0c1030381030307801e00c440c100c2040341440a90000390307481804890020764498046541d8107010320058032049140d5405950052000303014400c07a81228512014112084412002603900c08540d0012281044003240c000c440e0440d0220020312180a400001d0311808216414901a82d035442c1c50b200c0900c50103540c12040d00000c1c2101d0f1400d0045207580d170f507941030118051030606e444140c3ca0080540c00348c40e01c2c0e01c595112034079403604541e05c4446d44000c40540c0303c03014036104114030300c3c1c040ba0160005618241d00052211801f07010140704d1030703005200d2404e03e55001d041040540002d48151583c1c05034003010141a03038011058440300111150542e144c1d855400090b044410580c02140140032000c00c00c001665603000312940145800d4503082c1e01c0d101e904007141d030000c8070f403c2250400c1c1454001c1ca0030a0b02078130020380009400d030381080341e552125005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555209721 1250 555208471 555208487
    0x2409100c050c0d03020f10020d060602070308070807061103011202010914012001060e04030908010b0402040e060d030e09090318030a230a0813090f0b220f1d060106 72
    0x1901c15004020442035a107040032465541c24040c4c4112000c08500e00303000c50405020080f003d000c00d5000501a0010103a40940d00c024540c81c006009007501d503840d40d500340c4c0b0813941c0040a0311710002e050410003032a58460000b01503d2102d0a40700d6840d40440d41c188599584186d010880b00b410009520400750000c01c1d0f141d0040c1d407181840005071f045410340c60341140034044555250030703010881e5200000c0c035911032400383e41c4800e40035150420903404c60b00302c40e44043c003c0b801080300b4000c48140607512600081c00f42c540c1c41082006003400c40c0c414140c8c21410780d00540a40a020b4815400030160150028048040302d15038220b03810140c3c0c80d403034078500509076295031039004c00c0c10078215245034039488404165081803c0c40c1e1f4444a203a440003d2050058140040c07c0c03080c0c40803442448140a00d1102c01c014030740c94000090b030303c41102078244103100000503510490f040d45401007040d42800d88000c0c0094a44048080700084503042811000c0c840d100000038003e10810304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555210971 1250 555209721 555209723
    0x6050604110913020717120c03010e0403051803060103210e1302032a07030f18090c0504031505010e130b37200405061204022409100c 59
    0x10745180c10340352001d2100050100954108080c0d09001c600041070040141240507a481407459a441e5441911385225120141c03407418a80d5050005100c1c00c9402e0034075a8001e90103080071030700c4030740c03d0031000c0d911f06211030f4440c1c0500442000208100200c281d40342c000d411100841c44030080742100315915505c0100c8164402000c00c41c600c01510158000c5801500101034511021041000d0141601c001d640c0c11180810014054080c9642704c0d42001440c2410b181800440300c00d2143c01d0001007085c09500c4450b90b4800032600414000d04c01c440c011581b0503054000c0d00340c500029402400240300c2c0340c0c61120400d00092040c214800030105150780b0126010146d1190004205600085086c4180400a20f0320f542c244060207a51400e00404003507001c690100301e0303200140c6c04020040001101c000601080c0595611842501e03c000300c145000005991140006910410794a6880700d0710030348440800e810b18036800c0184202c40080d50309642505408408942441e12484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555212221 1250 555210971 555211001
    0xa1e050f041e150e0306010f05030307060507020102040f0b12060303030c0f0927060414060a0e060402070606032015180f04020a170f10060c06020f0a08010306050604 73
    0x110501c02e0342007080d000e40461000008803484151a0403005030181040f6904101040303002480f68a14a810403095002d01003034640540064507103c0400e50f04e0040c1a80240940e84034030003d0180781c0700350b040d503000b07011403100e02480c1680ea280e040d100b0307441038904d901c850708440b00190071820f00004407402554031412607494a503101c2c1c0808400d40140402d241d0041d42c85018003c4500800b94841e80800030b02c00d03665050514004120803034140e6000004401090020880c450b501c0c83d07003910403140c181c2400f600a41d40c0d100050000d21a011004109600d80740c404020f010716808190704988030b0f0003600000c541e4860403ca03415910380c0e980f0a62950802510510010413203d40401e000003500784401d00e200000000d0590b0002d41c0310200054003000c5682c0c2c1c480c901c04001e41c02116040701d244550a081018002c05100e500802042c414950242c20400031683d044030941c03c44100180d40358a101c41004211107030030f20043d81c004c2d040c170010800d1031421740700721048145804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555213471 1250 555212221 555212227
    0x306090103080f0c01050c210103050613030201090b070201050405101116060b0a030b0604111c110f031e0a020909041119090504140303090c13060b0a1e050f 69
    0x180d40c5104941c403c0d0400b100b06807091141c500c070346409001e218080e4100180c450b40700d580d00040850000c6100881c1d500c130001b400010004a1808075a00d03802c0203407100c417250a118907007070680c0585800328000b09403c20740700c20403940e164194405800389100d0810b0350110b210881407070080c1c4a04030603c040c01c40d820030040580c280890741c00016184550320110303822441c8000184000c51540c1b05a440008080811425241500c252025400110b8107541002041880b010003044240e021580b0395945400d440c0206d040c9000390b410a0b00031280840d03a03850f001d10400e03d10b88410712031a206d90a9039000c078504040714000c0c0da00420000c1c10114103a641c0d42c0303400c4041d4940d4901541c0161140185007100100030003603601500d030442c80410f0905113498071a400b0710200f104551039400500500000031804580f0300300060040f40c1903c6c0c4101d050301100c00a01c074030307030226442070b00000c0d40044050300001100710b0386040c2c43c0e03500301000c0c1d0800e05072250720440b180e00c03a0500e010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555214721 1250 555213471 555213473
    0xc060804121d091306060f0e010506030a0204031e031b211206080705030c0a12030c08091002010c0207060207080721121d0d0215030406200c01110306090103 69
    0x60403502c40c0200c0380760224501901d0300c4041080554140c0e04070002069460ba00c43c140319040c0100e00c010440c01407042c858034079042030701d12100c1042c0181407041000001050318201c0c0b54054070095074100d00044400c1d24042c00d606100d036640002100071501c401000c8a11540c1c4100350040242c0014807a000000000201582c000542d0b01e0402030050240c0c00201d202144d2007408050480c90000b010a182010100752a1662010302c0c0343c45200d5110040c094240f840c0010b1045941c107040039030804d04603180001990054404842e0403c20810369130388907035415000000c04086035002d48044030344550003241c4038480d900403081142c0c040300b020030200211a024240503000d41d1f001000007100d6541d9444203078234074001c0400145225016035034001141641c0c2d20128011207004c644484198042250303e0340f81101500c4643c0301000080c180003141d00705040003039403d015145000084a4032004070b800400d8821410361034200741c40e00d1801354100312402500010a000d0450b032031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555215827 1106 555214721 555214727
    0x90e010b070c05090a0917190c0b0121050102030106090509090d0f0806190603061814060d02011119020117040309030201031a120a0c06080412 63
    0x82080007500040300d030400b0104441c0d09850351000755558844003c003c007142c01000e0211810564440c000801c640000c3c000b040c00c1c0001a07103803030f0b8a08400c0341c0c550301500c4010b0060907990018803102d01000222061808107a004400924240d9205030a90708281d000c0070100e001d128060201d8586500e443d5806040c0b04000c210002660368010828140701c50100c080c001d0340c2c4041001c0381c650110860b990150040e000c0061035603640010000d2200f8407642e488860251003c5001c4802c6000d074070011205c3c2c6204144d0798850000308040302c0c0320034400f02e050000e483d469880305481030040440030b468940d030032062515103000150a02110b102c82c00703614100101040300103500000d83c4010717030b0340a1800148901c0346000e404070408400105507400104042501d0340d1300c0c000980d00c0e41007031144c2c0c030320b01500341da683e019900032000342d400601c0840d00c0128580301c070348 = true := by decide +kernel

theorem cover : BRFrame.Cov 555035971 555215827 := by
  have h0 := BRFrame.cov_init 555035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555035971 ≤ n) (h2 : n < 555215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
