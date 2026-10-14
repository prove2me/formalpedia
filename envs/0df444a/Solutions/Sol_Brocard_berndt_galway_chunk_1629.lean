-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1629
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:56:58.507974+00:00
-- url     : https://prove2.me/submissions/2a5ffb5a-82ee-4c25-a15d-097142f30137

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292805755 ≤ n < 292985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292807005 1250 292805755 292805797
    0xb0a0f0210051302060a141c0612051f062c0a05160f110f210c19020f031c090e0603070905070504030b090c1e0f0f030c0303 55
    0x180c108503800c0700c911a05010822810000303980311402d4862400039004034000112810424410b60944031040600d00c141d80d00c0760802c2e600ca41c25456002d90344428142004c2001c142030203921588074810307503c90001c00d15548824260805000c1c040030708001c0d19500c1c1030016010030712400004070008018000c00a4860700030310814540805820f240c0c0712441d100030084002c81c0324088142800300b5043c10b08070041001c0c03080701d0b40e020302c04030031455004d40c0380c0c13a0407000800900310307401110344070a2030445920304051001074003d508850031a0303031024090407003501000349031885e814005030424180310390b0000428600105000c000c901d918001c59040034254dc004000d0018240201e00d445490900070006a03031b5203564064202070556a0011900150040742150300031a4094515500e1f480e140900a4481400c400241d0141145864041c40745d07095541d440709450f80200b1050703002c1e81c1c80041c4030240c1d000316410f94061003000130103030065078204098407413040d108095034003100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292808255 1250 292807005 292807007
    0x50d080108010e1b0a090e03090f101b0c081e10020403080913061203030209010f0806310204090f060501030c090306020f120f07020c120c0108040c0b0a0f 68
    0x141e01a95880c0d00d009615030002038080340b4107041115840c4207941200c0701500150480c00c96901c12418107190411030140c04a0210140040460495100104160000a11641490403104240025111380d18200e40507003411510003082d01902404603171a4640111500d41801c107003600c8895440214100c00016013042001c580e60401c650940c1441e16650752040c160041c100a98400e000300e068207003107800f09501c400010071001c4020f07419124141000740003548050420f5001600c9245101600350103541c01c18051040a0442c80c24049180e0810983c5003450030417419014000040020010090001d803010304580b0340001802000104540111082c9500c101d0500d0f0510811421080c2c004103071404130307500203a000d40d480e6808646402d040c480c80d512510201070003000d11a001c2c540e0745406101c4d1804d9007c540c0341c0b0040c107041007060202c00040c14101e41c001e854150865104201b210780142c460031405c3c0900b40c88081e0031000d600003060b0040002c0100d50b904c0d49003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292809505 1250 292808255 292808267
    0x603010501050303130306110708040b1c020412030c05010b0405010617060d0c12030c02040204030f060b090f070f121109011707050a0309150507030f0e0f030a0c0c12050d 75
    0x41c070045004600d4030000c03403040c2680217803500c40a0b0240b5950080b441904c40c50310201c070425680409003503601c6843c0d009160081e0040081804003003841c0e9101c03481c1214034401c803001e440310b00c0075101c4a0405540c085603c014030703600459555480b200071070f00e5500c0e40c0c080c06001c2c103056241e134494800b0b0842080300303010340203000c41d00c118102070204010400c1e00401e042038566002e14001800c0041c207094032480c040c01002500300d031000500105100702106110515442070809020885d195001c1007a0090152000200700e100b03400070804823030040c0341100d64041e10341800300d0068a0b442202e4119900c03000c0b414241c04d40010754400d00c0d03030f001111005844041c0610600e608010000904078010040c03880145641c4100480030300001031b42c240c0803600c01c0d440602c11407804480040292a40303402a02c03115040826100c5407410100da44006a03d00394021810505200d40c211805080c2e01c105aa10142615002c1000001d1140840020740610010000585408001005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292810755 1250 292809505 292809509
    0xc03050f010f2a050412080315060712180f03050c010f0503040c120201030603140d23070f0204061a03060a06080610031d0d12060b0306010c080d061d0603010501 71
    0x81070f00d8180006010718025041c6070002103034071060018500064015079051085401c1085007101d0100c42e0ba00300140711008522031003814400b041c0c3d02d02c2c140188100750103005030040101281e401c8015001c1d1259400d00d0001e03415031042a0403a50f2080e050303190f4090b6410980d0302e03400c812034a800e08d5030001504815016070340390840c90744c03030301e44c66501c440c01107030140941c1c1c000c0c001100019680310350800f5000d180c00a0041c010103526192a075a030f41206401400400c0850705074400c4c2029002c283c502c2c4400040030b0f2480c001d05030342d40440200c500d500484e44036603a06800b01f5034000700d20f0104142c00900740a655a418181c00b040700c0c50185500400070807401c40104085900e415401d01030400080c00c020800b503014070095440e03080044d1103004a4031840501d56895540210b100c2100700010310100912904d034141d0116902c070407030b10329003c1071040619500041020000300121500682d002907090384a0000c641120750320f10007900c80c20001010f00015142c00e110b8140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292812005 1250 292810755 292810781
    0x1908041e0b0a0209060706060909030905060a05040b09030709020a0228081b0c030f070504050f06031c030615050c0607080402030c0105070f140102070b090106050105070204020306010c0c03050f01 86
    0x6000c030880e81c6020111030014022030500c1d401081140c0142c40e0001038039006603010100344002601c98104200516104c10b0560000b031500b2000241400c01c04219030720000a0741c0c41a251904121152505c0d0b1701c28014650940709a600018040009102a18a20110307030b004d4480c0a00010240010411050321960004000c03071020000401c441c088644103003882c2d881d0b1a88001c0d0500c01c509000714901c0b071603014050511208024400800c10701d0075034004440402c090340f114102103a8200d4100c80c903d4250748850302150a00f0401540c03a4182c01c001e00d0b02180075600c03511400d0071007000604100c04a00080340300c0303850005c140f18140c1e06c049076150a21151400b600020754804d119402d0f54140b00b00040c400041c0400c0048041407150003003d0340d40d02d03002a0302c2560007036110901c140c0340d003940031020803084081030080c40300701c82050b0360f010b0071f20505030200002544090403290600c03840d80307444000101e480310600005e42c02800a42030301d604003810f050035120f102212070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292813255 1250 292812005 292812053
    0x2607080c010209010909270f0b01090501080d050310030b06030f1504020406050306090a261204050c10020a0201080705160c05041b0909020a030b030a08180d030210050c190804 77
    0xc413440240501f54241c100e0700081c0d20f00c4416981054821140850070290181c50b0000000c01d0a081c1c40d008141200c2101d800c8405165901784200c0d070b140402e581015200b26207403c1003000c150b1a00381310390000c1d002806c3d9440b981990445c075142201e04c038105c9143e51811400c102c01e61400d442410003c0900354042c00251070304264140d11102c01c0380d40100006452a8001003003442082110350034603903640050380da40303030b0301e40b007528107201c216011504c038424046070050909200c2c1d0f00c880011101c2e001809010503650041d00c2c28070004005c0402c00109020700307a00c0796460388d041410740703015004404000341002c2c00c0c001030321810341e545000e4030001c145804c1800d40c0864414100c034000980180c80c0c1d0390b000310031005802c071501140d50612441041c0030900c1922002801c100d09607805c1e005603031740318500f400321404c400003000d009600070b00412107a1084a42115901403105041c080ca48101c40310704043c0c80031000d40304030000e080802040f04100c100b112080400ca00d41d0624 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292814505 1250 292813255 292813271
    0x1e030201091a07021f1503050c040e070b03070f0e040c0f0f0212090409110307180b0102151305120c01020c12041202190e0c1206010c2607080c010209010909 69
    0x2941c2e40b8100441d8003268045d000c000d280505169205160048904485000407552424401d03651a01400320b10312603444c040c8c848011590010340e180803903c4034181d0740e0850740c0d40030007900e080c510110b2203c1401175000321415560703668490b1000710307041921080c81c1188401402408a403640640a00f551311082d015031034844078006540302c03c07101b2107000c40c0d0209141391460200e0544403d15800d449480d17404514203071000c04a0740c0e8460a00c00410102034904c0c01269503030f4580a00001c0400080c012800400082084090050280c0100c0c3c924130607280300c10115500c55950000240d60101701400308210a000e0003200021010b01c1c00d081900301580710305003220b8400000c2c0324400c000c404071036440c43d0341003110050400c09150700c140d241600c2c83e1400e81d0b02c8400803d20f103c0300000040c4003903001c0d00164603c25005401c20140c400c00c0ea0a41441403481801a07103104821320003c40091400c200a09960701440d001585a0030924005051000c468001680090804000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292815755 1250 292814505 292814507
    0x213081e0721050d0c050d0e0918031306080a0605040608120a090f06020106030201110a0b0c03151302130501091a0307030f090501241a03041e030201091a07 69
    0x80e00050b1941c040c8040c00d040d04580c2003641d05840904001c0440c00340415800425801c40305103941c960094081d0b40304200886012110f42041140d40c980c0000b052021840c040110000b2813802d00c600b6084a2514982c50203905400141340c0c041000035005c5070420860b80014014140248025142800b00340d00b01060300c1c2c0c89806020508000035000301d00c4524440c800c8a01e007006100e022580001940c460200030301804007408142e000c00c0b441a24100303a0000040c15404060b00310001503015160580c04440700c1c0d02c054400000d450742d002e0840c080740c0c0c40365a0b41c1c1744200c5032000140d541e160403540e110046000d81c815414025018800c016000054280400521800004603500d54032403606400900d2170a80002c4c650b45081448020040154030040000e500d40e0000e480b00c009550295450382c68502880e0401e10f090603001c108111904040c682040c414014120903129100c0094200450384c0d8063780180e4480b0040014480c207c1d200e1180105036030b80750240c0d4941000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292817005 1250 292815755 292815763
    0x1b080321060102160807030605100605030a0c02010e1009120806030d0c0c030803040308040317060d08090328030801062a031205010915050a0303080403120207060213081e 75
    0x9184120060300000800c1c40e0b00c20300c884514000c1d02d11240d60407945400e0030960b80e007142d00044544524100c0410118108641d51004a07034095840b07600d140d8809180b40f01400c0c00f407001c0002d5640301c0064543c558002d2101002170041034800141e14140e0f130500d840d1181391520018248003842050150507200401d070f5485a07405410007038910721692030500c900c2c0c0001c2d40050807468022040c1f204040c3d020300702c0b6004902994854041d030b0201d132140742d0b0800065860a500a80f200b03154400240424050600408001c0c26138518076030503541002c03c00d0401000e02e10020f00524000c1c10150082c26440c050000c0c0e1504000c078200750115a00c10614140014105600d01000b00c0d0405101c0c20709200d0100f51544140060350791a00018054403441c241c4c0101108140300100d0181001c50002c4216901a621040d050300c491b01d0607a0001100381d01d82d2142d42c1c00b003203240b01241080c00184a50980c4550b02e201d034a150030800fa0070158050302c640a2000030f01c0c4507d03a0003078005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292818255 1250 292817005 292817047
    0x6030302120c07080604030f0e0906010e130e010c0c1407050913060b04090305090f0d0b07030c0504080a05100b04021201210212061f0305060a090c0b03041b0803 71
    0x4003070190394442000380c10389020140c3e80581e400d440303507100300010154400704145000d03030607448500000c0194010030100c0c02c0308079036050005014494424041c074201d1203444000c40000000a4000001c02c040c40c2916455102c00c0003058459510304100080c8800d007100d47c00ca1100684145030804000604450019060211a0031001e1880742405610340c4039000010000784104011401494060816000b030090039200c0c030041580400c1074149000d031003200590082207180b060355a80029001049100c030480104002800301040c01d010810020305004e000700d00a21840a840310a40b00f655203080c1814021401448802d1100114810031415121544140c201c01250451030042121440c14081d41c0000341c0390f50807220240101d131141c0950100000107040c103503d241c00d010f04d01300b684402009039015600041c0a446d259102e0900d051055035803484181c0e9440c1c06120b650402e503010b42c0d500d042d068220407012421140d80c0003d2100e84027071410302c2e01c1c0d04e040c034071605445 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292819505 1250 292818255 292818283
    0x70e010e01050f0112090f020913080702060304031107060914040605130b030c0a090203060a0801180b070c080a0807020c032a0d08041d070302030103020d0213060b04141306030302 79
    0x482008005a8004d481c512045005c850f804c10458419040c0044070038806001030f800340c02d1140200e1079001c590220024465044281c440c41c0807201d0f401d0000b2030b4402001030f4200032140c010f181c4585820b0000000900c0c560b50780010b80c81c1000c2410780c010400034502840f540c40e0042c00c001c66194140c0343e008410350741e0070001d80039010801281c203000081d40c840b5407240c08010301054402030b650255000351030640c0e91141040d1102d01302401c0729600c555502d0950700304100b40000404019803e5413014a40c80d00642c0c1466550f1588500e070052503030500414020030800c10405e6042150400030072040b8028410300c40c4150001d4100201c03000346984a1041142c04081919090070744620340303501c4008940c0c3c0e0b583d6440045440481076840e1101d045150004c070360003d200e802034138145c2e0340060034485c0c0c1070000e80c01c100a00e18003099001026031240400503010369950058001007440c03c241c0b04c081200341d001c1000e0b4414504910000515000c02440840d40c0090000304000e45 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 292820755 1250 292819505 292819519
    0x90c0c1103010b010c0320010f0f051e0115110615040c14030106050906070206120415020f0906030402030109020d12022a0603220c051806101b020405040507030203070e010e0105 78
    0x800e0404080700d0710030307205890b05600300109c9034115003440e406111800001d210811264807034031100080601502d50b4614000b05880c01482016046486081c00a010382414810020000c0065007011012600700c030301e82c0f1020f84001080d003045e01500041b0001498100184081007925040d41d00060040408201c0b000c11301c3c0e9140c0d19100d00322011141c0080c8995115002440c2c10003203004121000c8801148640c020922580701d8000d48074a0f41a20140906040c050001d1100380d0b04001c0090b070340340d901c0e4040c080242e00d450101d00328060088179007c104042c2c10001a00e4030b8415a00b083c40030500d1020220301080c044d03aa0401ca220468040b51740341c6402d241410802040c180304c0441142c084450b0042050740405c00044400507941e49400c000d2040403c1c02c01d000c115602504254a8440c49402c80e220f0a204000e102c1a40001240c44200d40c000c40c0480380115411035060b80076600600c1075240811501d8002c18401054241540c1041f50724855100184101c41c001c2c41c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 292822005 1250 292820755 292820777
    0x6020a021e03030106030e0d02030f160f0b0709060f021011040803040b0903010f020a02100c091d0a0b0402030717040204091502090a060302040f03030e0a090c0c1103010b010c03 78
    0x4424411900042891401100030041414240342c03682d200788107031008039180c2400341007400c001080c4041c0e81411500551b080000f031805800306a0710481c0c0f4203032017040b11b480d0540080d0500d003040e070712a4002c445103401481d04040103010ba003400e4201c1005d110381c6001c2d0700300142e40020021000515074101254190325004090030300e01071034200d0b00300c0e40000710f400714548248101034991035104400a011640c80d200404d0101c0c440c082c240d4005170400190b1440324003058001c200c556015103071402045603142080c101c83e0b045044031000c411400c90903c0b0480d400c074050300b00e8005044030114654205440d003c0c0074881c040d240742c8901105040080c05541d03d81d8099107102d6082010603020700e0048060350001d501c132070b110501c120b545c0f0340f01050040c82032080c0c6080d0781200c0c143c2071203641503440603112030801400d40341d408100c1030300100715400c4900564584020545400d54168402d03d00054682000a00c86000340e143c0000100c80360382c459440d40c0829003500b06440185 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 292823255 1250 292822005 292822007
    0x101a0c031e0a02190b04140c0a1409010f0e0402010c08070b040303051e010b04050f06070f06201303240501080706121e02210a200a0c06020a 62
    0x1004415000d040c1c24015440e206520a03076030001c1c070541c0c807250709994044c910360548406400e00300c64007802d403c1200c0001000210188880c0106200c1381f011656503654442c0001d1480200d41c0041c44245084480c0c584141050400d00c0d01400c0902c10b40e400560802451403c1001c004001074100207250b000081400540d004440802d6084258840c442c0b800f800c014024000c19612001495400158150001030402000b4181c80003000c1203441e080c9440304021400c5e030800c154079403000003002500f0002d8000c48460800d503114007030101d03c1c0820000769280d60007480b00024100c28040001502d503205008212050380d0b444500440070700040b800148062003583c0c07050420302e00e003500118841c00002281e10803034102d50340b401c02511403e4485802d0300e00034210600030b04111845000390340026009001034143c010300b580403201444401082500060700d02011580c3e0715400365001d403100313489190f40080505115450100307a440d004101300c1c0e845c10050444e5a010800001c41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 292824505 1250 292823255 292823257
    0x1050703050d060b0301060f0804050706030c05040506030a06050a06020f031c0b0301050a2012011401020f0d0f021209030c0f15071a0a0b011b1509050d08101a0c03 72
    0x80b01240004101080c0c44a4200c50654000c2c007031100400c4e420b40101107842d10a002041c4143e03800401b501c0e0071842c2500a0b400f500b002d02180060100a010105168503941c000d0341c8603400d0104003103042031525041c0500a4000c0c1c0110701150800d1391441c910b13010000407100c001c181240e68040c1c1072980c0b9401c0d40180b0b12409282da1550920f41440401c0d2003039013040407820907031340380e5140942030f210564009110701d031001d0700c060740b032a0300401c2082c000c1c0000480342c4d42d040c01541c50031f04022303281a04103003207032000714081a10807a0211181b13070b04005480781c014190340e015251020f14000030355960f0451500741e12030141c1c150302c000180c44080c5220400b42c042811142c5481061070000c036850110407810031545003403400113440c5039184c0500030080c44184c450380c0e0103218102d03900802c0b0040e000d080c2c401c0082c0b1100503070407450921031170000e01d00801c007520740f850a454008100b410041c00e1030794500c0300c2c01d005200d0840e0140400c480d9084004915507140b8a1901d01415 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 292825755 1250 292824505 292824517
    0x7080415022413120509040605011d0f0d0b011509080a1a0403142109010203040c1a0702030613020310060503060c071e0c0f0f0e0c0702010e0307030c090b030307020d020105070305 79
    0x104130443d640590480d8100f00a04001c0c0400c8030144540e903240c1e401110360880c10012082507481000c0c2c891054204403100a11300f0030003500c1403c5581c40d80c0c80340f40071030b242079002e0b44031001e94843d0f02031f40c10391100000c0c0c003906003034000d000b414240d610707001000b0034000441c242c10802440401e08050060b4039101700d10381c941120b1a00c1d028082c40452480c1145040c50310181030040010b14118410303c01c50384580d80c40a52041280d007040c0c81000b5181000a081c07490320810480240540d07070030464144038440402ca0390400c9000c138410315007403034081041140070604040c42886142d90110381140d00001d407070071581d221040d60a00101c1c5d07020600b1540c40d22101e4000032020b2016200103003090710400214044215038070300501c202d00480740b140a8041300c401d0301040c04815820f009014042c0140740c0130400e9010540041d003061800c0d8030488901c46d02107410040c011841c000c00d050480b00b01e0107582004050380204450a8500c10002e0400c400040c0b000704041c0030324140c43c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 292827005 1250 292825755 292825763
    0xc091201050c09011d090a06080c01090e0714071401020304030e180138091804030903060b121b031b0109050402030405120403032a0f11130207080415022413 69
    0x71b041c240000198000c058501038800c041c0aa101d845d00d00d1350007000c29004503058404040c095640f140c0c07044498880001800c40136640402c0340340c0100d080c2907061b21406401200059881c1031910303019201d5070110311540e0180110b4006800a42004221141107c0704900e19a003a0500c0e20406100c1e00d03005c0400c40f022682420302020341442c3d20300036243e5064240c036502c141e0780303c44031601c18641c0209c03001030003d80701c1403080c00011440d821000740900003400000f45504940e110740d08000c07082040140c000c184002003640c0c3c0c58100300c0c12103e0300048950103c50340340c9800003009059540144c2c0d0080d034001011408001080003132041c481526440b260301c5685a1400524041450b1a01e90008004500c0d000c0350900303c020710351740306034041158103c040c1c41d0366484402c5000c0b2411036038400d6245010807510b0714180002d02d1403501c15620641d480c3d0803c0d000d1220074480303022074000c560103c200c080702a0009140c00d0400c44400100800694552282c4c8845026a0310010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 292828255 1250 292827005 292827019
    0x111504030605061002010608060c0a021c030903080c09010c03030e0c040903020a05120f0d092f1f020d080a0e0304061d1504090e010b090c091201050c09011d 69
    0x10078031016511003030050204459040360408404022030a0740c880c1c3c05111802d801c01e0000c2601c12107100d006000e050003900580b080c2240c0707003411401d4807244203424030100e0388485000e42050b03808811a680701c80481e41e814184104280028902c58000c080103080c903a848501100d40542000290600c2a0080042c040c0c03294501d4001c2d01c643c98000101d0382c83c4a28080b400540d50381406072020034210f51142c90030401048100310181100600035200c0b44400b100c2030410300392168040e122031840c002502c600920540602a03400d07054408a12400c105e031b80000380841d4007095a800300030031441c00c0c66a42d10380705141d00080c11f400a0b0480148800100020459084408155920700b865501988812030f0010b0041011241d030f00b5031100b400403c001e000840d00d0f680f1143c2c88000c468000101c050b920400b003a0f55032010f0301d140030700f104042010841c40c0703401e0700e01e050000f81710720007402103003008600850f15004601c001414005012191000400303888541105000028031003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 292829505 1250 292828255 292828259
    0x906070b0103120206070e030a02060d0912030501140117070e1305010e1006020a0f0308100905010914091f0f11030406051602030f030a0203150a0b030a18050a111504 73
    0x4540c0c880003d8441c40243c010030001404290289044190404010303011300f641180d281c1c2001800c0c1d0207880c0d014101c40d80c80100d54040303442d00b070007556030b114a5200020a0350500e0201d0010068882400341041010569103142c8140418065040f1603903003060401a500e2000250030010080d4a8041031403410700001076110f0b0720030140e03014400d81c903d800c0f074003500d440b0201d841e0310481c40040e0170420400c10b900e0000f0310a94040340d220f080a010314401c16101c00b081810707a14281d21061000307464184243c600c080c89040d098001c40d00300020194411900e5403290000c0550351241640d9644490549000707060b500074003284100b94880a58915051800c1c0b001400107448411440003900c4003481264000801c4480002d050846da03400c40da2000340c040042d520082c502030b0424511103103c98192549070005001d800b9541c2c9036a102e160030043d00c07044540b0361341d10380030450030f01c10000045600464a0156950061207d00c0b0807121840802c05100101022000f204000a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 292830755 1250 292829505 292829513
    0xe1510050f04020a0e0d060605030a05030304020a060206091b010507080301180e0106261c0c11060a0e10020c0910091406010206070c171c0b04060305120906070b0103 73
    0x39618100c410515046014050004902901c1e0225011800b8a00d121005d450f00b0340018104c0ca01c03600010540603103a0780840c1c10303c1c410100c1215180d0021082c07008618040481c080502120720061035103180005884d640e070000c000240c40800080b00d030303030900d17030740300d6000c4416554120038034640ea965500c102c8240e05030411a0381d0141c6140617180c55944106000390070450340062112030840781c420100708504070341b40080c00300030b100b20288120b120f0341d040108110a9415141c221000700070f403c000d0310800c0c0b00c6c00320a01c980c0081000010980d0040b00035565100c003900d00e07003181110441c050b8036141941d110315a000504004008200e08030108107029524401000d00102e46148043e440e04401990824003680010703000448817445148503100450140704060000344510103050460781c08179485400c05015902d10415020080c001c1e2144441c00b500e0030000545551034154584042045800680200103511030300c55449900380c03910383d80c101d444001556900e2030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 292832005 1250 292830755 292830781
    0x9070c0b0f0403020c0103053c0103050109020108070207050a0b1c050a020a0306060903080706091a1e15101803051b040507080f13030507081611220e15 67
    0xb411001881010050034055209001c1c0c00d004880340740c050b103481ea006242c519820a445a5141d60903100d0b0403200740780404044503180214090000010900703400d000041c03180100510040965000b0350f0100459101c040b0100300b201e8588000540741c2c400e900c070343c0da0500e01c00500c86410508000c10f10054480690043c990429261810401c41c2e503601d0099900b03881501c00038088000c1440100003080c9543c1212811700c1c812032840101e502501e280c000039001c1501c2c00540301e03001e901c0f4440c00711a1480360301e8102c0310b21444014118500400140c401058089890400c02c0c02d01c0c0c4124404000c0e00c0c1000603507446001e80740021740c813144104c6003d840258252007a814400481c500034001c0d41c14a000d200c24408849055403510302e80707245804420011010010104aa00c01080b10000030384001c5001e80403210120100d810b2610780c404a00072800e120310840c12400e04081201c084289403509111804145180a102d005080c01124088096501803240420400846c203003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 292833255 1250 292832005 292832011
    0x525090905070f09052701030b0f1e15010905061c05010915090b0105040b040801050f15010203071e0b0705190903020d06021b070f0603180b010509070c0b0f 69
    0xc402048950740b80361040310852064100300f004144d00510510803810100903003000181d000c000d00614041801ca000030f0030710247d0003a200c4000a009001c018600544410b4011400d020080f00c0c1e0761074903986000886020b40750040e4952080c074040c250b41d0240f0072100041c94024180d07a20303080d50100c114114002210a984a680b80600124910f8524400c4000e000912895482c0702c03410002514000e1000d1820241030003000e02002440050900040001d8419100041603a0802004603000010040c1280d601d17520b0b0340d078041d80071740da0010540d062103402001c40c0c00c4d04198080c01d10080b54509170050b140c05281c13010848404c1e0000001c00d8880e0200c0310314544034022010461b690031407408002c0d030002240c54003030049011038020303081b220440c80d6030086030030716898000d140c031840c2c1c0d0084880c41e070038030310030000c85030140b040410010304000810202d03015540c0c0c0c0703542d2b400c050198910812440c400305050500c40c010020340c0f10741c01111049503081000580040072411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 292834505 1250 292833255 292833269
    0x10030818090a05100608070e0306070e0306161b2a06080c0415030203250e0301150b030129161127061207140909060415052509 56
    0x107180882d201000c0d62054500c1903805000c1d0084040c281041152841d1000e000c01c420800b4a0181e00c9072680d0070702555000f01020303143c4a1004901c01c09150501714024040d0400e0300c01400031300861600710148400c0210a101c0e4140e07120f08600c2c25000207840001002000c1e01d000c0352603818120b070500000180c4142d6110460156070f038521424440c861409000800362021f40d410350843d001c0c1c1c02654002075103503032030040d05141480c0704000c164015134500000d0407000b01074104d41420312070348640500b1641c01c24920381c240240c14400380300612452040c1c2d01104e4002c42940074219241524800441c80c1d50303564001001012180000608151070742001c021401205282c0f031800300c124011441e4410007a007483e6a10328091390401407505421040445450f82090024081d08021340109003010b40d4503106481884180480203184051030752184044c0030100700041405a4107200010001c201581c440403080111107080e04a1007202c00d1421455440541000da480241c41300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 292835755 1250 292834505 292834519
    0x905010815090c0103050a06050907020a0605010f0303020c150915120a0903020a03030c0504050a0b040f0518151314041208011211040204031b080f0105011a0310030818 74
    0xe9401001000c2000303540189450f07100e5011448694043c1e082070b43c5c403c1d500701c030001c0c107640d0f2000843d400f17031422503440700140c00041c1d021082155612600740500886071030190610b0450364080c0d5502c1850301a01c3c845c4200e840c3d09400c0055180450f4500480940b502c1070940c040c03c0548001d40001c91a0004484240c0002d4111a002d00c29000ca203501a40246403469194405400031700c240418001085020000416103484883d2680010310004c042c0643c0c3d41d1424171303a0310440050b604514411039142050195080e000e102058002000c0310391542d000030800c000800400c04140502d00301420320452a10446003400428800c134000d414881c20701c040c51101315901c41c401d004030409000c180c009103000c603a240741d44035040398018000500c4c0607140d44850302c00c23000c20840c020a5840d030031001d00c40c02d4010710072400d003119040000d210035410302c402100124481c4501210500c80400020744400410060340011504440b42c035a449114041034512001703446203e13409850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 292837005 1250 292835755 292835773
    0xc0806150904060b03120a0509090c0c071509180506031b10030b042702130c090501030f021e030a1d0303010509040c03210f020313150c05010609050108 67
    0x1100480d00d540c00030041c1415280c0d59a40c1c0d90314014005400a00e41511624509060a00c0c0c10700040580c900940c13501a01d940c000005c0141c1c0c0d180017090002d0b80c00c000d10890404580004985041d14000001d451140b45900c81c1110764041641c005802980e4444107119071100650225020b11025401da9074100341104200fa0701203050000a50400426442007442d18071030f174080d5038503010040c008204001149185401400000318500c1010101500203046140c0580c15404e851082d02c000d020744020a10050110700c1188215414940c654420701c011b0351040c0e049400c2140e030360040b40c00d18405100d05031036903041212001801460544494407040c241703c200101c041000c0011882c40e0300f01030904c800c00078042c1003256038006a02000c0300051602400b20144070203a1aa500e43d08250a401000e0b069400081d1003590000c101143e00748281d4902ca00a40d03420809060b50003565210880703200d008141c01401c10f5182c6040419030060350340000f4101c1c0d801c0000c45107a18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 292838255 1250 292837005 292837021
    0x60102010c0f0e01031401031a07170604052203080118020f090d06060503030309010509011109011b1518050f010209130e030403060911041d12130f030c0806 69
    0x20034070107607100841c4200d01e450341080c0c030607100192100018940411041c40103d03110300c2c1c0090a81040b40d8003991412500c031102c1800c00076a03808a09890300900300d210102001e0640803010700344a0040c4d840d54001079485a40420704c03a44611904280c4400c07174080d0074020020a400e0080100044d4044510b0040c28bc036402641c0042c2140c1d4682c0d031400018004000207401c104508541c2c0b942c45000c0002d0a0381c090018600c1075140800210700761404940306130842d6a41000d46105484c00d00000626981c0f1803105000e050351180342d110792071114240100545051030b204503805007000b0f42c545178003000001075101c1910880840344071800b40e030f8869081c0e000e00b1001a4019041d510842c1da000b11f240c00540c0d00320440700c00d882c500354030b135110081a5009003c09550b407101411113610f40d42080c0c499002d4020f490103100d400040803190103621100c00c0c210f1600e510708041a160b0150214102000080030340100040545950f031400d800d0304441442040054080c09000500711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 292839505 1250 292838255 292838261
    0xc100c02030903030d0b1906050406090e1905040303090b090c0f0a032d0506010e06090609010303231209160b040b0301060c030201020715020d0b03030702030a060203090a0819030506010201 83
    0x41c000203004c1c41c2080384a880520007450003201e1250320040714900c0d40d0a15940c6142d204c00b600c01d5984131590f8170308120000d0015012503018080b004401d004011540d5050100a10a81e150407400306090700c99080c100c01501f1882c50280100d60000c042c072050134400a03007170351916425542000e980c061181000f1501c0d0799484081c141d80c000c0d4241203803104045814040000641030140094081c5032a00f901e002e400b41c0001e440342044c42d0a010041c0b500c1d07119564088801c5549011035070455600810600908400d04441c04c040017401006407400000c1c1c5015141001d004c1409142040181d90303103240501c8001c0390a801e5840105101288608079010340c0c8a60320020300e0741c0d20f0144211a5800446000d408655003480a42c0020710b4010144551050b03408001d03845040ca0742d07225045586122540344030f540100101c500607200030034a5401c01d030300081c00507100c0c0d03a41e400080c14900340800090400c500085d01000c17180c1a01814176a1940703a680400c0b41c3d036980801a422 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 292840755 1250 292839505 292839517
    0x6012001021b1605040e100e150c09030a02090a110f0322050a0813031a180a0b06040e1903030f05010e010b030f19020a111020030a110c100c0203 64
    0x600b0004240c14413060806800140d000345108080b40d044100109605040311400c002056aa4001c2d5411600f00034800c1041e0750410400d4400d0707840c142c030b070900003503442804000007030055490000040700003a0560010304443d04030740d9034641c2c1c0c242005442d1080d51044078004d0780c0c164800e1000e1200300074000010600c550203c010a0140e03044c1d01c0b124015004000d0700d0091003c8a017010000030742c1c0c11210a8107120300508694a81003540e2902001075402c403083c2b800380d01030100f845c0030900403102e898000708262000640e0300103040409007041c0c29512002091001c036501141017541c140e100580e080c511401c10041c030b907207039150341507016001e100d50000c0540501c080b444601c0e0841500ea00428211841070040341e00100a10030780e0020800b01010400c012034030307040b200007070004500c0741040c440100004800c9a000c038142e48003850101000d814040001819011694030050742032044000e01e030388035030500986582c0c40c40c0c2200c0252580c2d082c41240813040380000241e41c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 292842005 1250 292840755 292840783
    0xd081e13030f05030904020a020c010207061e05030405010b03030705060a05060906010507060b030f070f03141618020d02042c0103032a0c06050301061106100e06012001021b 76
    0x42800d14645030880724808190b0b0582c0e080c00108007002d074580c1c4610003484103403441e802910f020700400c0c00190412420b907205400748505c42000f4080d0780e4880009200d04407540c1881ca403641c0b11410128010421980c0068040c070000421030103011000400621030040d21500707100e01c0d6201000c0c0644140c0c00d69000740812018010340000580070380000030103d0b80a021600c20607860792a41d40b410601e035000114404582070203005000440101c4c40452106000400b075004940112040d546100c2c031404041300b078880315080f81525550112007503581540003d5481d183c0f00c032041d20740c9002d4180d00c003000400440b003580c01e070303031b50818500c1c12260582c54a04c1481c1d0f8614000904244c50f03401c000090072116500300001780c500055901030201ca540c0c09890390b0402e0300c040e103a610706d4226a481075202108000c60b41040d0342603041500c1120030021419284c070070040c0d07003502c2a90030382c0c2600000c0048980d10024158098005207151412100c80c4a85214441d0303100c00c88110000f0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 292843255 1250 292842005 292842037
    0xc0604080a0c120e0f0609030c0d0f060f0218040b0f09090c0603010b130608090607052506090b010f0f141f0801030515010b0a0315050d081e 62
    0x100800c140c080a09803115850074000c00048103070361144902c407006070310103000c1101e500300311100f030a10820101c2c55a10503188139141954070701c00a55102e03030b41d000c1c2601c144082c803042e0307040206402960142d80e902c18401e2000b440d43e00c011601035004052041e88000c05401074030200e181034094070100c89800b0b00040100c80c001020311000c100010700100b00742c440c1150480c820f40740d010045d0b00901c2d81411080d261a10500203401d0321420b0750002c0100485841803103c503031400f045040e0030000c00d050881c0e0343c2880442426102d1104803080d020b5150a26184007840080c1d001303100c209101e00141441d85c0c1c0c072044518007220050086040d140303807441052142e82c01d880d4041e218200d00070400303010380c1604a00d60b03071450302e4071f43c42400161980c0010010010104554201d83c40390105420740d07581040a10400c13400b410032008109511014021040085c1c0301c00d01002d000041d210b18960307003040c05d1070101540400d0041c000031542c0b10362011210b10f40c0c415612550030660041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 292844505 1250 292843255 292843261
    0xb060319080313020105040b0706090b10060206010608040c0f1205011d0c1201090611120a021602041517030c0609280507091505270121080f040f08030c06 68
    0xb524101042e400b00d050142c07c110204c0d0180920b400380c00c2607840791340042000700305481c04c5100342c20301078001803041c040c50030107000440d0007083e020b065480514000c0d41e01d039100e0908034800107503513006000d080100740c801b01d680740b2644210385086000300c000b4080c0f01d128076402c04103c03800c1080c1c0e0701c075a08614003d48091600c0b04080340c02d0b08010300082a03a88043c0c844404540b0413041070790901600207004151020f10f803009503403003d40040d0860500450401c05401c1d8000b80800a100d69541d4a0036118001c5013400d01d00036054400e200c6003400c910510700f503507030b600c01400c40019200d0500003503201d580c005119902d182e07081d030045001a051210b94000075100e080201c500d4001d0920220300c450341449400a011181032008211030300e481c05002d60030000035810394041032400d5000d4811007030500306a04581084408142c0580041e041b02d05d0011000b00090025400058403522038a03190054410b80d00000314115074107550740b40680c0c0e00d00c40d6401900c0c40d41c000c0000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 292845755 1250 292844505 292844521
    0x403140f0712060609020d02040501090e0f01060503040204021204030203090406080106080a230d0905040f0209012708100f150f0303141c05090c060c06010315180b0603190803 77
    0x42030b2051841900d0101d022a107030040b01082c1e03004061701034070309907000c81e040127203607400300005004080700c642901d40d500745a400c8010303400050148070140032000003c2411511998100c9404410510b42d81c03034036080900d4020b4880d44400c00130b0b4810f504012012546240c18850841224000340043caa00d02c9556101400e1030040c00d000304041e4184401c4000910050020081c00c100c603940c3d42100c1d50900c4108000c5501b81d403100310f142803040c04052081d9810100d001d00780d003101380202d51582080c003400c0c1404002a002502540542d550328600301c80355030080c981c0960790b00700c1400100c00a1034481d00310a00c61142d408000900b900403c0800d000c1da041c42011240c0407078291078040701032510490810100c00c08600e056540c2e003040345c2441c00303001e128041c45080741c03243d00d000f181802e20790303460ba0706001c05040300182e40c0349a540b1410a511070401091040740d280b0082c02d0609110124060448410f40a8081c05005002e24140750564100d99a40003101b2030450301c0e142c0c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 292847005 1250 292845755 292845779
    0x405040b0d0c0605190305010608070e040f0207060e0f03070305191b08180118090e07030c080d020d0e0d030e421810050d02030109020403140f07 64
    0x1000d6044048404000d011694032641d9202501041d10b5480e035460388604035009a40d2603007031060406182c080144811540181c100e0f0300000c15141039012002c0c4030000500030108683c140c641c5520008440c42045090b8014841da000d0721000d4902043d1203450343c1e07480e03202c0c8480c0140060000c2101903040e180f034404249001185113030a00320110003002c100c0ca002a81c0c00c054448090105444091541204031008101c00030720b011100410700004410385230080e0301502d82920b4403000d024603d01d40c1004142c0082d07070000919000384c0c1d07aa070001511101c12512480050180c542004ac0090085422807561580a4a0048000180c2c0c50442d0707031110000d0a10381c42404140741240c0440d0070f61359070b00d41d2100c1060304c1d10400700d2501c00041d10542c1c03d100340503640d0113106060107407402c02e0140c40042c0c0103031011800061414011240340c800d80400c08030052011001080600341e542c081e00036a072188045034200039540401545d1104121000b811304c1c2d202d00028480c01100e02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 292848255 1250 292847005 292847021
    0x60106050c0316061e09031202070302030903120a080a0501060801050f0f040c050c0d080105060d0b19030602120c1812010207050303040f0c0509010305150c072a0f0b040504 76
    0x40c1c142d9041080110080b1210640440305580031a100e100c20501c04c08081500c0f00080030744002004420b07526940540500104104c180c041c0c0c0d808287c40e02818000c3c812144084401400d4503c010010701020038a40c10000c1c10100140703107000019200e156900c00d41d03060710303e16150111668600010010729100b0801140e4006a00344031031360803030715a0f0040d030802400f180c4070903445421403c46246450748491140013000710390310040203e603e0300342c00c807515804104000b04191030f03d00040358401e25440484d09134034036949000000d00020740e000e00142419011044926140c13800650340034062500c0020544e11142031361f005c9072034028401600030007080005400d06030702c3e0b154241940c108039401e48115000050702410401d0f4141c665014200403140c01643c1d505646500f903680710b00414003182ca40802021072031443c0244203580c401940704502a06500e0a100c0070802c0305070000341780f440345d12040300214044250540c0c2d4001d0350203420019041c503240070200304c0070300080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 292849505 1250 292848255 292848277
    0x1103040909080c0d081609061d04110f040e0c19122c0607050310151806021e120901030b060c03161208100b03060406080708101b0206010605 62
    0x1000f2120302680e0a120a81204c411a181d950709440c0010203a6143c420082d0301004024583d001413001d160045c03201181c3d82941e2812a20380051301d400716008100c02c042590040c2800700d004222145400024015500c409110020941361000c0c0e004c458051400c0104c45030780c0506074503050a1292700860a84000c2d8000404c00412141400c404d421420740c030300440c2d1246000c202ca104908001c9150481c0d2a450a07602c2c503d840038040300181524000d00d94002c149a4010740c4080c032442c190166800c018802a500c0e82d03076228041d64400c000c00783d2200150301900c481e628082c0c04a40303481d00326111065545494103503001180117020306c0020310752014081c404030540d0b40c4104040c1c4030310707421240704a140d10b110b82440c0043d5081000741200b00800102040313115441c0e01601c0c0103c4102c2c503c45a11b9403a403500150160000360130031072030b03441142000640703120005141042c401000f01c04001c0da05080c08000c5103110140a02c4000d42d010b07000402c10f05200b07100824401c412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 292850755 1250 292849505 292849507
    0x40605011421132607080304080705010c080105180103020604151e030b010219020d0605070507060905061501110c0603040f080304030206070e1c080a030b0d0c060f110304090908 78
    0x38041507041e40d40069960369249500800243c1c100164540c1005081607050340c03070701c020402d4070080c001070b01c98200300601c90400030002c6000c001a00050f544080c6d4880002e104010300b4100c000c004610034807840d4459520f02003800285090b44080d00d058940240000345050f0070031200428411004550500304001d00c0d0a5000b103401c5120802c1680000381d03800310ba0101001c1c0024a03000c0402d600030800c406081801c80140d07105500c290449510090100d1540e4071600140c1d200d000d2108060446414090500200b04c00440e0007407041502c28804003400c1400c400440b0146061090400950f03c10b8800d2001441c01c1d4002e907611030310400e424026507000e559a00c00c25081601e046003d07074003038420301040541180300d44000301c0040d100c105070a1011169402c9a1140c00e101400040c400107a10008034400c4e00300000c007102c003800360b1008282d1440d00780340d101990710030800064524800e0013401d500c1580f0140c021200c2c030006500b07180c200001400180280d850440d800c00c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 292852005 1250 292850755 292850797
    0xb030c031b07020f09062b120203041401120902040213030209090a0308040b0c1c02040503060109020a0f0309110307030302070911042702070c0602060901111c0e2b0e0406050114 78
    0x90103410f240d01f081c900700d1804482c80491408580089501d0000d0701503401c140300c1805603081c0b0b0f291070350040300c003460000b030000c1d04a41e040d802420041da0107034109000140030070701084400710080441344280c6501c1e50030fa941c6014030b40c48070041d940060011f0803440c041804034410861041d041700d45520100e01d4181c500d020140452034185407400801e801040c00c110600c1e0074442e00740103000035501075207405040c050040c60aa115401d00c400d0541e0781080c03d00f40301e640d000100100002804650410f0340380d0070069541c51701e5221f010035141c1050607880f00d154402080d01c04603a012a00030542e007405082c0960b0010b6010305110146070300b40084c0c00072900c11004c070002001e41d6000790111741040e501907802d50fa052020009007141c204040c01c403055010100b80703284940340400184c1c501c104a00181071800b44450700c001c0d8510900441c0c5052511100310302d0824a548607610516054820701c82545c0c00c0c1d2003107a003c0f81c00044104210242d410060150158109054407804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 292853255 1250 292852005 292852039
    0x112090c0b130e060f130f0f0c0302070c0504091e0f0b0a0b180103080313080405030706031401091407080a1b0908010608010209090412090b030c031b07020f0906 71
    0x1402100c482d000c012a404400c2040061102941d5001542075543c1c02001c00b428000c43d4225078a0880d880f000ca69032926503400c0c45480d40020350324500a9018040040c0c480e030005d0103900101000d642280c01001d001076503140511034942034641c41b064940301c085508051000c4001e6102c8156804a080c01034100000d90786110035215003900c81002441c40104014008104070003441302c26016074603801400482d260320305492740050704001603480d280380d038500fa840d1402141d00c615054819428042020368154000101c445000114840141c2c0d90307a5500302624040c0c00407501e0804080b01190805101c1c2c00e03099880191a2004201c80c510b1180080179041031000c8180041d00a035002d000303000e020b000701002460303207000031350130325042000107507150380b010340000c040f005801200f001c824000d405600c010f01b042c8103c070340c58bc9403400c1541ea01d64404c0750b8950805912000d00414503240c90240ca640c99005800c0d805200044018043c0c0c0080103071416601c408400300c0207000e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 292854505 1250 292853255 292853257
    0x151e0b0304051e0c010221040308030f0604110f03060103020703052a0d110705090912180406050913020d15020c0109050705040e0d050a030f06030809100e0112090c0b 73
    0x114402e000910462403c1038115a07a210f12110300d41851300681203440b1a603a0005400400c1480c40c40c0c41c1d0340390035030fa1668034041e100300d520003404108040100011107004007802c034072550081e00d0a00000110000380d440318404c0c01220207032640d05202242c3c580d4469405072610520038107100d1710709440410951404903030b1101186404904445401c0070302800c1c4501d034020030b02ea0074656004411001d4140c0c40d01500d001d21801080128001344100d80100541080304280c002c0d0b06a85814580400440c003541000d140d01980c200341c400034150411302c00851041082d021141c1000c1180d608202803200e4109060304d903044000102002c042d09031005040300015407000060a80c00c6190441c107200c171950080f442940340460301200103030080380000e2170030150715200d03584401e480e00503001005015007215080745001400300c10802e0ba04000d081943c001c80f210f1403180b814680458007241d042401a0004203841c05491001740150015145144619030400e2050346500b289030103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 292855755 1250 292854505 292854511
    0x10306090f0203090d081003020402031b071208130c05090402030a05011814010209060304030809010207050706050901022505040c0c0203010f053408091501030c18151e0b03 76
    0x280382c0c00400d00005042c10000c440540046080414291400318140414011b442c40003a006540000000d00380e00c3c0034680c01e4200720f4800700410b448031110704060981140c1d5801000106d44064007061000810041070303008141e00101d10390149050609014000d200500308a81500c11b00241000280081c0203040920b409400402071501e83c6081c00e800822016138074808692041021040a85071041160f074000c1d058240a000c5172650504280280b0401c139000c1c2450103109408078580e47d1103c001d180c035071001d0713003181d11640e100c003001c003080c0b040400f43c07508050411804000601301508443c0c40001079080270342680150350042800e40d0010520310180c60703960f03000c0049100360080016080d80009103c110035006401c803211a55506840c0c1206100c4800c00080c01e1480401c548000304101454a1840d07596a14048c403000c044d0f8011890300c0b46440921300c41c1040390f0f12031144403603044107100b002c45242111540000f142e02c01401900d0a0a00010400c10655001140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 292857005 1250 292855755 292855781
    0x6091611011a0301150503060f060607081812010c0f12020d0e0a03140a020d1d0607030f080a0b090a020f0f0403050c040b10120b010525020405061f05030601030609 72
    0x1002e0307507403010142151060320303154440843c03121041c4501c0d00c2c001203c1d030740007003080d150040070780304d84d80003541900581c0c10081c000c15000509103030b0340a040c9001c0c580030f0810b6400d0040c01d040d480341d907401d8410780d101c0800010340003007000040c0c6115027441c421680b542d440c014a044114004007007603401204070000e190f48000d1030310f8100b40c0e004c2007000c40c10781e601e40c4030342c18480310210080d1a401c2180400381000411000c60030f540c241600d03515044030b801019160341d42a50729014100c4198511610040ba200d540040c40e007030500e009100c0324400062103100305907a500d0408009400030040040820414091401143d8a0030014809103014400070104185201c08100a840c48407814034095003568680a40b4250008090085503503101c1c5c000c0f8100092600490300d60295100c80e43c11000c0d103500c90000c40d4100b140e10b500460083c0c90601c03c5641d60b00c1400380704200c40c42d951625802c81035601000c180f181300910f4103c1414500424181d13a5102500156414070180d10303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 292858255 1250 292857005 292857041
    0x11041e0204260a08031b04090f050414060114042f0403120314010311030a02030111090a0902040608061201090b0f160305010302030c06090a090f1e050609161101 71
    0x241c1c400980015000c1001000f080780b44a1955003044a000280840b034241c02103050109242c1082e60a840162201c1f1608201944c1100c0f80c2c0000340c8401d4a050705c110b1544404610007080100d0a01e060300d071040d19100344402c0700c40500009001c101e4000c40d00a042000c100304503407490600d03801403004404081c1d1114190309002d1a9007980b00032050616141c1000e00c80d04201c3c1c458103a04407504003600c0b094503102032002c01d0070f001c410f24001354154a0480d44002c1d002007940034221503101135603410700040d1a819400128070880c0645400300d019440000c51034600944241500400200081042061036441140f00d203000d44c1e2911b0280c0e240300c20490305030561009020302e0307413445c9014862545181c0110380c83e9115110078034060440010500c1c09502c0b1244c502c001002034800c100152100720303e449004180320f030201c14002110b000e518002070b50900549010302c41c0180341c20b4035503c1e5194603c0c100c0c00c87e801c42c40c082c042c0c01206640302079170030f200d80034408403415540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 292859505 1250 292858255 292858289
    0x3030906110105090606090a090c0608100f030507260a050a030f0e090f0c13090b121515041107030c02010e010f0c080a090312020a021c11041e0204 65
    0x20700990141d08481115038941400c001c02d8140005000707811a2060b01c3d070f07203240d445914001d00602101d0b440601401e584080000360310b5442224148541101c5841559003610790001c011000c0c418030000c0c0159120341c1f003d00850404021303000c00150050444071220902155039401d100c20000103407601d4200c0d8200d01c0615421070381e1072018840d1442d0501511310300e13400140140c20060401150301181400080e07100b040b0f50f0072200e48410010720442c080b40e643d44010007601c0e000c013002e4002c5902100c148000c80b80020010040140030403032074810340e03034400c60314096901c40080c603500c9500e9800800345503003071100500c1070900964030480f4418040c00003620f8025245040b0381001128100d04c05100d0384072822000c0143d01242c1a5562141910b01f2070341000250405000c002c4051904520b01c2c0d0001541c010b4141300751403501004000110340d0000d1041d01902418001c101c0251b0941441c00358046081840f070046c0d06408004405508001c98020b5044800020822003503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 292860755 1250 292859505 292859507
    0x1602030f030319020a02100e03130e06030f010c02060a090c05130f0e0616030905010902060c1609090c0618031e05060a0b0a051002071829060f090f030703030906 71
    0x410f4003107032600f8006600e004250301e03000750f5600e030030307034650b90469654403d082041d0003c0c002c40f08040701205440d481c0c191602549401d6101c1a10024868481c1d5407100181c0c1c601800317600c0b0b4914454018254590f0380396030100c0a40509001110401003403000407810743d840100d000381420520b2400152101c5102c201421980d258612503281e80c400c2c0c00700008010b4100b00512a2071103441d0203d514480c0d85005070140800f0302000b581300c90040f031710411951700060b1401e600050700d00c02903440c1e076840070f180084030050100900b070300d002c045040c0b02035405100790000040844400c40e24142e600d440c0c03112802c11002d000341010315a0720180c0e041c00030401055400c0a00040100240c41601c00050103824042c45694000d00c040510001d0383c6000740054002010200549a1981e100114680041c84d003540300d1409105034000340700c5034182d507810380c03c6814005085103140c10707200300c5490f503150800d003c219848240700140c84842d07241403100d03038015446511602007150a000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 292862005 1250 292860755 292860781
    0xd1103070b0a0507031a060313060902040606080402030706262211010909050c0d0507050d150e010e070804060e010b030a050c09071803030e0d021c050609070f0b1602030f0303 77
    0x54071401861b00390400c0c0600b0360b102821243c0004240070b980c9202c503014907018000c0d0804840280d80b0916003000011000e402020003403084ac0300720160390800c0c1d180d84041d0b41c07683d9203e4000c071211180e8501c00d490041c00c2d004280e0400e04040d00300d620b22041880d0101580c1a50800315103548428810340c000b9600060352202030710300400c00380180e280400c450b01c1c0c203001d105804e281807600c031030101c5c5607103008200300c4081c0b0007403c0091020080c0d400204454070081e01c0b41e45c9a100c481c81c00040d4004002c94200c0c02500d1981c0d8101e215125501c4003005400c114440841175544c4001c40d0303940396820030910703a21a01ca075003e04014039a880c00c000201034001c1503282800380d1104d10094040080150400781d80e85820124541852800400d8209440b502c0c000c0d00000d11015108032225640c42981181e48640102c030352503505c1c1c1785aa51038400c1c0380b03c0e48a0151107044107115032081e00c0007400c031042c803451010281c07014540002c0e1800ba5880e8110200d90400401d120004041030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 292863255 1250 292862005 292862021
    0x40e070309030512043005030412030b09040606080607050702060909090f030a0c0c0909150c02070b070f140d0903020f060706091505060607080405190b130602011401080d1103070b0a050703 83
    0x40c9046c45030340c0c6207160103419407000900041017416071035220a110303400b90348105240725000e0a449080d01e010f00c0e0001c000d06080c0030350032880c0328982c000758001e80302e041200c040544c0507117120705050840c01400783d460340117000c1d0f40482c000c400c106901f10f80100701600404540760340c2c28006154604008400c101c40360031a501543c01d00c0c2000300418200c0c11025038a89005000140e4904005000c9041c4422074000b501ea200c80006d00301c00f8048000c0f100a1050301030102d40070380b144902c4500d581c0f40380c51140e6001003003994100304051300d0700000610ba0b419000d880280381c4001a59100210b8030002d408688203a2015440380702840c41c1d100d8154000401d4034a6850401c20752140380e00360046218a034890140c2e000340c3d0540d40341e100090300082140018651b02c076400503401c00100d5400f401190019807900381d203000d0946000e84510f04a4807150041c10a22400701c0f01211307415100300c405900c62108200e00c4d00001d480705901445412000400030311410803d500805a604003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 292864505 1250 292863255 292863323
    0x1207090c0c031209050c060a12020304030c05011503150c0c08031f0f03080316050706060e06040b01030504020607020105070f050d0215160f0e0d0219090e03040e07030903051204 78
    0x10a10504c0060400100070248880c200c1d81c06469601a90007110040140b08140980c640080b00340010990041010452184203034001c0c0701c0d000341402000080080e40c0320140c804003082201226580869028401c462030b180303051903108800340c690030704650080e24030203030740031075a0340e0310a00400c001051030180ca40100348401603803460702c503034266000c0508000d8401640c99408000c242c040c5040b0b5a5959001505204107942c0340c121421420086940500a03410510442c1c8150320a1050030f200700d9008182c0350508942e41c00441d1103401080085a924500c00c8065012510801182d40c5945555000300743c1d00c560b10403100c4000c00098070f40100c0302d040d0903150032402d07040090750320559454a840032030016940c0000365051008000a508500000340c1c0d0240e0310100c40040d0151007520b40280000d0901d000180d80d00c0c400c91088680508220380420146403080e08010400d034024035105041860b10b0300e80328040c6038242d60456a890700c2004440e02e10050741c3e0800a90088 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 292865755 1250 292864505 292864511
    0x40908070f11120604030e0117070201050a0b0a08210f030414120a050d0c1806031407020c130507050409050a02030603061602120715050c040f080613021207090c0c0312 74
    0x34284200344d82e81d002900003811f000c00c48070826601d03480f8026406907481d180c0307031519281c2040c00010380240801d443c441a5070b800c1907207001071803d080e030700d0108540b1058000c100a4541c032218031201480c034a51068035900800070703010182907000c0a1406a80501e40c40000f0072103111040e03103081c2860950480054080c00044010380d00701c0280c40042004020209806a6050703040340c02d000c103d1a0950001c00c100340c08907000340c0c194042c02c2c91200c9003d00c80d04d00c2d150020141d80e074881da0220550712002c201030f12410821250001030700315003281407040c01d0a40320180e540a88000301e40c02c03500c80fa0701008000d40c52a040007200e030000000c0300200d4000c00e4846000b0748810f46100c0c1070300240c0307000070050100720044140c1e010000b201d1800300240d061800ea01c50081e8060301c1082c1c04ca00c21480e02140d52200810313103501031000780d0206003110007540d007445400d40044140c4423440c041d54030006030a4a1902400c0c0c0725074504da07241442c0108928029041400ca00d060b030340c41500d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 292867005 1250 292865755 292865779
    0x3060405030c0f0c0a050402030a0b030d030b09060f030d051602060a0309030206071d010c1406010e100905190b01030b090405010507141206090603190503070627030e040908070f11 79
    0x50740003040054038400d560150303483d43c2b040c02e0314000d0591810b030300c1e0701840703541c24100d0305a606600c80d204d02041154501c5464607810b080060707550301e000c4a10b42c182c0013003d20070134860040c0c0090503100c91000c0c04100000321a000100a9040720718242c020070b441e0100349003019414010198000741e075040c0034100c1ca0081e040c1a020202e000482410712450001e2a414020203803403c1f104600c924007250300a45e151610809001c800307030350602003030100c5900451403003d2401071520505000090404c3c2c180000d01c5c000c041c06a071942e40f41415943c01c0140410745544516034402d900600020600e810a00ea00404441ca6040781070089041402500c43c4007a01c026001d030049021183d0340c0c0309444100000b030074140300c00d5518081840c464881c008102000c406000c01e140201800c00c0090148044518858412010400038007001c4645000003401110f1a000c50000504005800040d0b56900700c132590002e28251081c4001d0708007001000520300280441d030105503440c0c1c41d002c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 292868255 1250 292867005 292867009
    0x5070e0109050c03100611010f0614040606020a03021b0a15111606050d1a19050117060906240d02041806060221070606330c1b0503060405030c0f0c 65
    0x16014011b10b41001041141d5004c0c0308001d4011b01901d002c400300070003034150740e0b912001d101000580402d00a0782030410000e1854004107803011420f80503006410503500c0d295500d00b801422469040e8002952800130130010044041814202207548500d02c460207010f88103807803c0303c413040c3c01c4114801c1e01014040290300c85c1c241c85811490010220325017248002401040d10030b02401c5403c003007010251000b000315030b12118219202a02d80109400c88002e9070544d40c202200e00c190084401804a0502d08000c0490524501c01c0c00816a6412200200182580c0f004030820383c0d094001ca4203003e1008800e042080014404408100070391400c070020751a40b52829400003095180240110440b03c2001107901e525440641048550307150b01c80c41c00141c81c0d04c810090071255580c1d2400e41500200102c1c00510600d0b2586040803d1942e02d400080f1030702e885100f5030300440f58000825890800c181c1d0302036403241018507290010f41e007902e032800301c4500006015920104a0403066 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 292869505 1250 292868255 292868281
    0xe010b0f0619030b060c030a090303030b0402030f0103140c030d0207080f070e0106300903320a020a0507060819050c04031523090106050906092205070e0109050c03 72
    0x400ea09001c41c2c0c4c1a01100013035428000c4030b0211005000c00103400f00043c0c2e0040018068034401d85082110202071400d201c100d01044845e0100d868000d00148041411500e140107095070403c11610843c2800012909000c1a03120800142c0d010060620101c41c040c40201c480c500014018054070780342c581d42c400c00b240184528000e0056000d00d1400440001400c41c0e030f031700b400c448031207561780d9032081c403000514109100340c00042841c0790800340c4501c4600085c0c840b83c46c00106082078000390358203450607405070f42107000754070030b85d0500c9000070003e028890003400740b0b44800d01c036854104031303421000c5040c62600b40c8180c6400108080c8680c0c01066030181c0740c0202c4c202c000905000010402007180e0a0354550010300c00010166118080740d100e8032401c180f000902401c1d58900a0095001050f24195400140b450002d48006168451075102c844e040311038020002c0c503a101c0d581800c69a8105131584d1b104640140800400342c0992904104007001684c59032920b44521041c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 292870755 1250 292869505 292869547
    0x90f0e0a08120c0708070c05090702030c0a0803060a0305010509070e06030607020a03050f040b16140a0308010504020306150f07030806010c05030a08070e041e14010521100e010b0f06 80
    0x902c000101003403070072074810b0580350950b6108003400d42c0c1710300c0e44c1000c1e00440e00034462035101e5126130002541c0540f02105036100318000030000e28214040b9520b2454603040101440d400024004001000c07803401d02035140510011805002c02c0c0c2d0401440000e582c0009118070f0181d8895002e1145203075001502c214150b805160441d228aa8004068502e2045500140e02d400c1d010a040c0992096208450105031143c9a50007a050902c00a00d0f100c0300280d0b8083c01113005000100494140b5400841d40003034001c088200803207140101c08415005030a0783d01500c03001051040400d50000304198104500b428905895281944e60f255039114500d202810045a01c000c54107090107050300c5405098001d0081c0903010390002d44150450010303001420041c10803004440031482c05e002c4c50705031480548800181601944840028080000c511229208508544050012a00c03071401c04000c1107001081100d10101000071050b8103040c49441141704000032020041d0f540501c17a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 292872005 1250 292870755 292870777
    0x30b01060e06130611100507170a060803030c030f01080601030f021309140a0c0b091f17040b04110a050630010905010e100506090103020f13090f0e0a08 67
    0x1521844000c6846405840241c0195803d000c41c0407078050380003402d50345030795070990488032422103d550350000d0b220107179041c03404940600c0320046800103815032107a0101ea4444041211650754040b02d140d0790040380c02e101c5140d004014001c0c000318810300180100090700081030340354110340780d48011111940c2d00034411100318141410811440e0002c03415180c10000d00840c80c20180081500c0e00f00c9900d0803140d00004000203e52a034183c41901c5c00b507400070b0300010810a01c1c150350801c0c00d04403807085052180701ea0785540402e824500e8648a06c1c400c1c0143c202c60304203460701e0018030760404005403084003070340400d100988401d011784031f902074000303c8030000000c041d10100403401a100c60b8481c41c440d11002284444803500101c0c101e4590700b071480741d190364036a0311010154440c091a6070000c02000130341e80561298019103442c0132440821841c01109080e800c0010403541d00040390103440c0c0d9007803164140d00307106030071008007002e001d0409804513070340c0d0321030718818911954 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 292873255 1250 292872005 292872017
    0x1703070c0b07031209060b1206130201050318070b04060e0102031903020f04090e030c0f0604050709110f030a060305010b040c0c35030919120e040209150702040c0504030b0106 77
    0x50600c240213054402424075001c010501c11070a000000d0f00c1c804030924002d14403540c11605290001a065201d10215020701414061941c011600c550024006c80401c4c01502c1d40e020007210f0030f1046400070320050038460b69681c903120015201d0119000e0580c1950014444010941c1d0a80301c1a0004806480d006907500d1000200d1a041e0045030030681c407003860442c132400072990000c0203143d035a110004503035010f0740802c40c03196208012500240b90f074120160400122000e5007040d40700f04844040c9505225000310740020306d8004032216003c541e1212410028844280308203c141c00e825181030205810344c90010b4401508801d00920384510f002da03455070035500e250441c0802c80710a03540d2900c41d41a22a00704107130802e94071601580146501e141c9a0300b0040c103c01d17002c6600c1255a00c500700c02210544071a1002d00e00540c0054003000a1100750303503980c94024100300c501d0384031911143d150062004451002150741c06201303040100b0700100d0408028981150700d64074001d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 292874505 1250 292873255 292873267
    0xb0c04080c011202040f18060807031208060301230402040c02030415050c07030206030718050f01120b0d02030303101d0601020a0b07030906091401050714040501111c091703070c0b 79
    0x3c0001d11682d444280860344d041004900c450b560420300000100001c824069951540141741e1a02e801d48801881d44400c0c54010051031700401800e0b6100c10020000980c0303503031070500071402d0048103204400e030344084c034200011460288a10714540c01d0b00e00c000d606040c1020315120003603094000c104140000858080034240007000880c0c0919400341c00705890342000300700941041c043d50388644000052600202c0c41e0301340754181c0000001c05035203403107001d0443d104002c000d0940185d10340e0000313800302c4040c016031000c10007540181101010902c00324900f00d6400341251402101080c0c80504106000c480ea80c00601e84080e10780001c401800c1c2c0d16055410707802400c0c0c0050040400e401e002400080c80a1b80c00403141d214035601c0240310303aa5580c0c10841d4201e407101c0c800d0071b1a90b0103100078030085d40300701c0b072225518400754216240601300f03e040b0300102628403007034800901800014440f00381100108413401080200450612642e55180c400303e0110780101c0b00640c83c00314030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 292875755 1250 292874505 292874537
    0x10f0b09042316170109021602092d01030819230d0b01020307150507030605030318011b1208070306090e0a03090f031109040615080a0b0c04080c01 65
    0x42c1d038058498152040010001d6000341404000440c0d070101501c0100c54a068030500905146103003d403030f451020481ea00300390020009402001806295007a10320900d001a2512180240281c030700c22070040700d2004001c440d0ba400e2850610301070000103490b0040002684500030350344496405203a4012480d03001030200c0301c90840901c024010500d80c181594900100c0c00181203410000c9014400107010300c0c016030341ca1050315001080d5041d90b82c801c1ca004925030b2702c141c1d0050610700d408107040d0350310400686150884c004101c0c41da881c0000380c8013250b0300210311340e45071040d4030910050055117441d00300d11520031110309070500400c031000800d550311903401000586030203281082210b0800d040181d80d18500c40085005c1039000a012602106903103415040b05d5002d000c03010750400020a020786024090803c40709141c9400c0c0b81c0028600d89482c00c0301402501000f80a00d5546041003030441c2e1018103200011030003003000744580c3c9400f0031540707400002800c084500c8409049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 292877005 1250 292875755 292875761
    0x70b0f0a1e051f030305210610030908090604030c050301050a05041709040b060c0a05060f0c041208160503280f030e07030b0c0408010b1002030306090703140109020702090708010f0b0904 82
    0xc8200f000003602c007408420140c00c44060060610031610090a00c601d100c0d050b141a0010346003954410440c107940c0307280f0351082e044a0344e181c0c803c880301c070704200d0000e01140b00b030340198108480c0c84036081170500c0542001d1080d550720400b015810300c03481c1010f4441005610600301ca5507212107001070078503240e4a0310340203080402c2001d80225a141301318a007040c1c90306000e07141260b480c0140b60205443c0840303140d08034041c0501180703041c9064981014800006c2441104441d10b42041c000500c1d100b0400c020904407502920186075030300c91004224040440d000c02820045260300010500e0f55032003500d5081c0072816080004110704906427140c038041e0280e10007001100c0110400107090b2940c0054011965180001e11480d25400d0070040c000480d52923010050b4030a00c00107901d4a0081e0070b0307981060550600052000700311200020f0040240c01a518158002418604509110040581c44442031408040a5051505480387c0652601c5003041018001c61401944e98990b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 292878255 1250 292877005 292877041
    0x101107080a1a070e030c060a02010f0e1c0804030905150705120901030b011412180a030f140c0a06050711030301170607021b041a06070b0f0a1e05 64
    0x1421109040214901241451207201e80b4a01018019011031919802060f4005140600038003806210000303009000040d008440c564007151340360b000205000016110b14540c100300307100a80051600145120209590041d6140400c0328541c10803020907400b40c9040c05490b0100e03003500c0710300203004c5814a10f0003a410301070190700841550890802e50707400141019138080c0c80500140305a1801074418881c01d00399111628070800080443c0b01054480700c1c0e0010603040d880280c4c240481c2000d10f42031543c01d0403008103814a5010365180e81015043d0021040711144614002003500440e80303c01a846000301100d17190301c040f888850007a50301c0540c050426088a49070343e55985000c0011102d490003040d240524400318080c60710100300d9252060f00c07070b025602c44100036003d0000503c1076a030f007050179a8510107032000ca65a0000180b42c82030040240000386e0505801039810001b01801030707030760a80340050140c40701002004d03c0c400e000039080001890356800507401c0c5011524 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 292879505 1250 292878255 292878269
    0x4090b1513050f10020a0f050a08030405160e0114010305040501180b061203160b0402130203070e0405060a141e04050f04050c0603070e100c141b090402101107 70
    0x40351200c0598a81d01c0c010088850480f260444030003010144040340a05140d0240140c21494000c0c2c0446c01c00c0e0560300b1583d10035422115072040c20307101c10b040f6030401d035000c80399031300590030b0521143c45125001000d4903900d0714916665141c0450f060241c44008450ba05047e21140083d003413200070740c044503d051001c44034556412580c034091011100c00c5921611880690307003c0600c842001060f5102641a251014807a0500792a41402d81c00c009008a0303000c51604050b1100b00c4550001e5800340e580c58884901c0750340400104400d684c001484180204442c61040020310b1281203440000c0e1021348168601261100c0050700f00105181d42d00e802509101c03c0c071204520240e0f449204074040c2040d01c0307101040d0760400416210030344200c4002800180495490b280c0700075940100081d0b414440b28085d1642e49044115404a80a182c1c942068065030620904800700d00c0b4503082c01c440c00c1944c0e243c1503000410107180301c040e0030108888001c0e103140d045002c22a0002038048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 292880755 1250 292879505 292879507
    0x5040e04051c0c0308010801020f040b0f0904020a120b01020609060106050906070f03020a0215070f0618140d020c040608060a0b011214040201032301030206030c250c080304080304090b15 82
    0x340b8100039015485604044001071102c3d000010380c08010310036030720001d0f0380d60030291516103030044820154003c001248004102005284410b40e04d41c8020f00b2007c5103078940d180100d14040c10701c802c40301283c00c41419074000c0002c11810500200c0d9240c10755500c0e081113034881e00d6207008100e06000d0200300500d030040c5102c40f1000e2580004800301c0d40c0d8400c50b8000d80a242200c200c00080c021000000c00500d09865184001291500138140c140c1c0d080342211010001030300e4100880c502454403290903001610341a00c0e9603030502a0414011003541d007401000d00d0490859a50b40005121884059480500349956031196a010b03d403401a29001c0c414071f044103208089249064404074003081c84d0042d0b94034441d5180e00c883d91000303003443d00d0800d40da10310307000e0100329800203003809500380c01040f070100201c40200150008901c1c2506914043d06076117040c1c084564580c2120f0501d2740144010001410300004030b0341910051403020906054403000314980300c030018000840104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 292882005 1250 292880755 292880803
    0xb06070c0905060a180203190924020f030406091103030a080f0112020d11011b0c09050f1b0906271305010f140f03030a1d090705040e0405 61
    0xa460020040d100704607020030150720340070b0410220074000d11854090100c540004501c1d00742641c00703164801c00c0340420b10201019002e1120840740d100c402298250841074010511540800b086000001d40031000c515100c80541c0c8005030b800014001091280c0741e90f0b0b03a000f0170140b42406103801e000a41100d8482c406c000c00a04404802c039002e000d00042d140000601d00001040c40003001e4001e080003800001c50f444a0002d40e20904001d41409a100c04c0214074030501c000c540c07030316401100c803801306a0a04100800b91a8040e04205000a049050090241e405080072070303107010f00302189540e40c060101141c258010748220703039903480340160a8240c1c03001811040c90041070440700b0610741c50b503103034105c02111028000c03006070801c00b000502165440800922040b1b90007400291200100e0002a00d19446003030000000b40444183c4012115a03802440200da8110f4003050301d8600140c005016000f0f502c14039400c80340c2070303000c1414480700b80418480ca510035007404515070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 292883255 1250 292882005 292882013
    0x504050111121f03080336010212060f0a050d061514031c0203031306060506131a0a210e07261f0b060c060f06040c020a11130b0607 58
    0x140044802072842d8450030908180002c0b540200f1090381c0c2e0103000c0a08549074101c80c4480c0007080c1c5003a82c8041c40100d28486821b01007030400d080c10071100b00150781e69207807480c0240c0050002e00020f000722010f00350001c1c0c07907440342c0c4560151501079485021a13069401c000000d00b26103003130178607040310403c00424010300e008034011683c00d0a4007221120030301201040e420018440700d02d00103800500220705200b80310a00703026001e010304070100d82d01c1d440f00700068850303105000319541c15112036400c001c4121a071300d01d0604180c0b841c010b01d06150704030340042c1c040145480d4030485258200301300c12144c045039020b0184001d10008a40b80300d52500940f4445038080410750691503544600310341031500c0000c016081c4804c03030802900c410202440ca00c007400c0c42104103544a4414015106542070800846108842040f1014160f052040611080b2605a4445070440d00844140400301e04146c602200c007074020b4421801e01000350310341500412200c03100c1c03a448040060002c00784 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 292884505 1250 292883255 292883287
    0xc0c0f0e040212060609070e010507051608060718140402040b13170c03121b0f03070c0509060108190e010c030b0306010609060206280507050a1103030114040504050111 74
    0x198802c1d9030411101d00140c1d4010768a0004441171603205c0004400610220700c19540462000c5042c1409810442c45680341800d040d842d10950000c82107225041259600802807590486424100485e62084004813524120514001d209510100400c502c04548560b411200104000348460b525603030010000d03400a0030a1080d105031070b440000c203e4240401186003810138000a0051040078500c0d82903040c1c44d04004060100383d400640042c03075218041c021780e006140d006c0003456035607030140350050f61001680c00c03040c01096000204202c91b60000c0c2c84a8200d994000300807401c03100c2040e0080170f40b00920910b480c075400c21103842a425019006201c3e81070044054454603a01c07990110380440340c9115034030042e840900428000a0b00301500e2006800c9040308240c03c0c4500c00300c4205941040c2c99180024500042b05462542d00400360741852428501039481c1d5490504441c069105103c5841e2055a540d07020404015096004c0e005044865275120f40f510b6003003240c1110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 292885755 1250 292884505 292884511
    0x601090b1c050d0e3010020a020a0b0708070e060304050a0503040830040302060705010605180124020d0315031509140102070b07030902010c020910081213060c0c0f0e 73
    0x12940301104c18146252002601c2c40544c40d140c00c40f4644090580501d02064610f00042ca16000d2a800d120340032400380014452150540c005183c0c010340e07860b20204410740101010200000102404100c9911480302504480121481c9450b42c955080450a01d402070030020070900c000980000c081c4400f04914004090801605a201c81d1031569108030161078061001c01c1d000800c405c1c001890000c01410441d13002e0f0000007005a2240007040c2884003803a03008512148000c01000141c4141c4803800d00400d480c0c6031110540b48100c8084d541c1c500b00c9041800749616203c40604c01002404404029070704501001c0c481c8010241e500d0080105c0c40341680c0d02d504a00b0100f8402c103050088911ba0742e03001541d4000d513a60203008500400d142c1030f080341005074603105800582c2c1c6852145d405025070415070202c06150211140c904a581403500034440424080c10700381e040684018030849525007090076a080e52890280c2d41141d642d0040340e883e00550001241681e0b0060b60248 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 292887005 1250 292885755 292885757
    0xf0c23010608010e010605030309090c071202100c0e030c22050c070203070e0106050301050609040920030106090c020307060c0905120705130504210210020a03090b06010c0201020601090b1c050d 85
    0x1042e0380c240740c4d449003654003034040c03140c26074410405c40c0c82c941406411f0a9000c080c200d00b0505105103507550341d150a12a03a040e8005a0000c6401100c6010900c2034030120989414002c2201ca4000d010070f8440341d01c01c030070a2013200d4003506060040555400c0c0c020003e8410400c2116103058070103041d450300800303030aa001c0e02c0780c6800030910a503030814a5040e40c48985401c2e0450b0b292008011481c0d1154040c03540003034a0f807601d440003030070341d007203045107000740020000c1450040c101341402c5039042c6d0300c01140c0d0750824008600d4107402004035071540350041804203000d20380d9802030300c91409650010f500030300414485115a68082690700a4540c05c851913011a4042c40401e41070314419500981075030301c2c1c4014042180900104c5c03000c4e16200e4015540640c0b1140300510482c1c020042c180d001ca6100d02c4940c0400000c000101da10031001d00341080070003074a0700001d5890703105000d01d0303404079592218895599030740081a4214980c40006106010007403900d81d8460707d400034014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 292888255 1250 292887005 292887011
    0x20415091b0315090203091207061a03031c0902030c0315040b09010c050d090c0807141906080403121b050a170105100c0f0609080405100206070f0c2301060801 70
    0x400e02600ca030080d01050a851075009043d6401c103900c0000950019080484078030440015410310310b4610301a00d40c1c10b02070140000d814114190143d603541c08006903070b21a400400c4804484580091042c185e40d41400c0009426801840801c3c070b0a5030214415074513102d0b480c41100c15011880e50180b20b10310400705032042c0d441c1ca0006500360342a611032000464801d103d2402d810140d940500801c034043c2040c46040c40e5501c501606201080c0c11020021030b0101c650b48050800020f41140b144022659520031468441d00074820710703010b00002d08000e2502c45041d45201160011a8129203103c416400401c44100c090540e40c0124200c501089040e0000381307240132040b0300207048030700180c0002c4102c54505001c03a4201c0385403d048494400d84038000d000f0449502c02d00308070610400560346d8460404007041500f100c1e0000c2c03207085500c11410898503603840311444945405900340002c55a40e02d250091190b05440c0f41d6003104041c0d0145544400d0054114a0440d0800e800030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 292889505 1250 292888255 292888301
    0x90f0f0b0625061119050301050a1503140906060333091e03090a1502060a020c07081606030b10141b030a020105010f120c0311011e090f050105210402041509 69
    0x15901b82c04240700d040c1d40882c1c1841e081010154030001c1d24100c3d00c0c64070300011801c1b00000481c42c084d60030340c0c038041380e580400100b200358101000003060030050b40312060f03081c03911380039564060554940391002c1d490040d808a01150801c005611801444c480ca59030320243c46800c055880e081100300a10035a07070038800041c020121302007900b890049a01500060340c0b140d01c0c85019503c40e0701c940d1424401c44100060341c0c2c00500145188400e49034200d04030903c1d0000c0103003910b030018042c520440200c0d85000c03042e03400558041110314000040c43c2c5442c0310705415402c000041103803001c10702000a500c025654103500007410781c0e15001c0ea2030760107601c4240c50040010107203401080455800e4081c0003142d8035440345501e002c0145002c66504d0000000b0003080300c0fa07140204080341284209201d0001520242e00180c0401e1074000d0409401508039146e031800e25041c10b60102001c0302080c103545868100010b840340b07154450050b5540c40d094200103100000f058154001000a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 292890755 1250 292889505 292889507
    0x4030e1002030304020f011e020609060a0203090a110f06040308030402040614150c1c080103051b0d140703080f04030c1208030615090406090f0f0b0625061119 70
    0x20303094001405a004606503502d550a000c00907616800f01d50500c8004000c0c3e2594400c0a554200c0340d800f944d0180100781007080d41c0900d07100e0060082d1a02600510070001a558005403080503e40c000a04005641924010541ca4841d01c0e41250300030500280202c1444000700007540100d20946041052664640b08844240b2a095601d60310103500a0a409070a009001600a9408040642e00080e80140c40800141c100c0c0c8550804180c5010040060003414803005410151031102402d142125000041e001000b4000c01480b90381d8207007200e0080d40c02048040061680500c88030f40d45c80400b20060001c2e001031008540d071700c241c140003044030a94101e032218040c3d0701054403400c50f202d200c1003145c1e022100c40540ea60042c20300c00d40320f09030307903070f0140300000c00c2c3e003e50010f2405050341e1180e0559100310042843d1500b000c014035142e40350a02158000440508038819440940c915006c1d0b0059101d4082c0200741002d8100c05070080c104010324000c1320702654242c0031200d0b054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 292892005 1250 292890755 292890769
    0x3061908070b0d0e2b08010b0304080d020c0703060e0c011803081605030304030e0108150a151b120314090d230a03050402090108030403110402070602040302060a020604030e 76
    0x2038500036420041d03041101c04902c0024018414002e8404200c001818075058641a6202000f15280301482c81c03d0300c035840c000010905114262802c041590304281c40000c10380301c003400003800b1000c0019081049080c1e50306803039900760841c0943c0c2100343d4070706180f005801c2d030b91000ac205009408408109601a1040003085a02640e4501507246551200d0078683c0100b40b80b030a100c101400c4007000100107100951080c7d20988034000707034800c12800105a00d0004010307071440a2440074201c0795903a107150f180c040b144040b1803103980207400001154034400d100100c61000d009143e04000304860442030795840407281e501000318121a40a5000381001a00e6080b025006900a508074512801d000e14000140000050040b00d4500340b41040b0340c400c18101002980d540d085c0004c6281400001d8014030064006506003415620344003510084d01d40b4280c4110f0340001c4041c00c0110a80540d40110380042400f500c032010003a000c0d440f04003c0380c0890003c2c1c841c0c0d40c1e00040b407500e55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 292893255 1250 292892005 292892009
    0x16031209141c0e0d02040603082101050604061d0103060b0d051506090a210209011403071a0d0902030c030715030c03140109020a030b1309031202070308040f080c060a02030619 77
    0x583e408200c8548202808070301d25180304c00340d03001910f4040100119102c240103180410240d40034200c900080311000700300d0241a00120720a040070041005901d0b48101d401d0400c200d68255010300d1001140140d0050140d90302500040c00d01040c040158401580700c1d51103150740b4240d1098403010380e407c101803441070710b0540354000c1180c031090007940b0700e102400392000c88001e108203550100c0c3c6c0001b140b40000340c2c0545100c400580075912030b4241840340f0401010801407455020031540490300c00340c02201c0c00b1149413a6100100c0341550b60820a9008880c00641a070341c005455801c5c812045c41419201c0d80403c3c1061500ca10051081c0301340b800321501c000c0140a141d017817083c800d001c0c2d0722410820b020143c40e050703c180160b5940d8203501d001030b40300030001a80501803070003038050f0080210f0b00f40c0703092042c018940804d81050400f40d01551184c06440030b4851072621002c40d014107c07a04a642c0308000c208007115080382d0095001e4281117500c000d91703035010794004085807254 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 292894505 1250 292893255 292893257
    0x240702030616270f092f1e160f0302060705030403020a08090d140f1204030b01030b07050c070306090c080115060e010e060715060e04030516031209141c 67
    0x250b0080c90f1402c10f9010000c0460020110355000c15030b079120b40140d110079941159290640e500a80c40010300070100007841502268560b202810040303031400e255005040350b043d90805182c0c038000f8600030101c21148002c9503120481304038651030405025443e0040c60403405482000f0202d045030b07001d841a01d21882c0c0c150b0081030000090f603070740110dd4000040007a0040d0b403085405000405881500c20300c400d4160042c00441c203135644440c90815044201d0700c130b003981000144080f820f080c440506407608010042c9458440200480d601d115010400305180200e80001c010400390b23400040c9000e0250b800442d5144d22100a0b07405c80b021004443c00c3c43d0782201082003042d0040618040350758050400c4a02c0b01441c2002c82e005901c080400c80ba0000c90358042103142d1600d21480b40500100078040c01c20740360542c0c000d4030343e2199911001607a04651215010144100d80480b024840018180860a130301d00e0019606442180118518000d0900c1000400c8190014010910701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 292895755 1250 292894505 292894517
    0x2131e0b0f031306091e0c050f060d05060303371b060504080c0a051005180304180213030305090405060303130b03090f06130507050f0907030209240702030616 70
    0x62031189140b00d204410342180d20a884e4401e100c0451004900810b107031042688064134015140b03400f5547c07541c560070151207011402c003003018503200c81e02520400c000e80d0100044544950001030301e180203003440d100920b054070341d50b166011001600c45041c0d04202401c51202040440240c803100210490000655080d50a42020465542205410901441c1045d1410703052103422424104400000e0302c00380d004a0070b9249900103482459444075100c03490001070061440c0d2140ca03445280702d0b82420940701c40c1810204d0011340d0485040c1ca0f1041941c001003662403402070300c1c0d0b410440440d031040d0b1618000502c1d80c00d003c01110181d480da081c0c11a8581c0c104a03481010750000307002c00084e84500c1aa028a03000100602d80c09202c500d507034441f20b10740500d84540340122a801190141064401d000348a440d103601d00340c0c102040c0d04001da111100700001c0340f0720054880c940c60300058400d000c46461140c81008150707081c02039041c1c54941e900c0c40040482642e59107400000110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 292897005 1250 292895755 292895761
    0x4050411191e0921021201050a0c02060906040203030f0c0c0a030605070216030507050420130f06032a03020c0d0906110a080d0b03210d0e0c03120d02131e0b0f03 71
    0x40b51300312607601910007480240d050180c045440d0031200b04892000c001c42e550312020000c2038042021036881081d2200500ba6490258086500c0b070140010311901004040785160290341c0500c44142440c0b4043c04100702903a490600306d0240ca0156111030140c00307110300312402a60f10482c0c0f20241c0750000c0c0248640e03032a000c10f00c0700905100d400005c2c810004241240700c4402c19008240742000c4507030b0094101c0c20187c1c20a0984075540c86003040c14600030b1341400d41c0155880040740c000305248001d143c0c0c0da0010702500070b8400d0410491803030180c00c41c00b803001600500d9040035100b081d40c801611a2850f504a640c03030986100191105d403040c02503000840d40da0300b041640640140c1560300c046107041c1040350040c40d20006607142600420214031116451081c210000300c01d0000b00b88511247e070110b52501500e10b0241c0840303100140104111849804803035500001030365248103070356184015911580803450f50f0590240f980f100040c1c0b0b007034000584400c24a13040c407117441d40d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 292898255 1250 292897005 292897049
    0x18050a112706090d0614240405060d1b09061e050910150207051009060f0e04060b0d090204061203020d081b0a0503041a0c04050411191e09 61
    0x3115616400d640b0a904000b40440c5441c0c1c5686604424400c000215001410011034070781d070b190080c048244c4400c0000c01441500481031840c92041c8140e80000d1700e038440b00040b814403152800c0150050500b03802c4214804c420480310b404481e164074040241640ba414001000c1840d0001c815500e0b02d03181052200e0b260a40c00b546d08980003a0300d41408031b6640b00d84441000c01038800c0c5000d0b0b04501d10030040b500742000391681c022500d141098005003040c40203400080c0c01040d9200700505030381118101d0b121035100c00b010302644a02142c44911008140c00076010901003203004a040c0100040c1c40e41a0070b00c010402980740c0c0140101d084a8442107895400003405201c070a50448200c41403039203900c0080000400c2e95071407035580c3c582418a901d0841c0302c40342000d10900204100088101200305031030a403881281c0208000071010b00c5c3e0b0405000c0c0d09081c40030800e542c0604403000e500001240744040c0c103041020a10058544291800c0000340f040140c402d1011401d0302c010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292899505 1250 292898255 292898317
    0x5250f0306020c071e030606051504030b191505130e070b07030306030206030109060501032004090e1e0c0915031b010201020d09062007050d0507050718050a11 70
    0x42c464403c22a0040c60380c5e20621226440c000301e10404e009151070050007440818010a000303000d0613075403a801c400100b000303036603284901e2001610780c5048001040d01040907850b802c84c4460030040904c54000c0c0100b03440d00d9000140708280c8114081c0390741541e4000c2500510040224120180422a02d40180c20105a01c4070004400b0543c0c0e6040100060340c592020f14040c2580e01c20000303102e41450009811240300108280807240025150003002c1241012030302a2280b41c100400d65030000d02100c0c0c03400882c610f4200301c03400a211304000341c81c0002446802c1000c211080001600d0f0301e0752101500310a0400303d03415070840b50900d02011400418001040c0061000600c1d1040e82c01c83d80d4101d0b5845a41214001d445510390403040480746080c1044014a0b079849140c945d80e507030740a070b940c02d40b000840700303010011400c0390602c00103000c0d01c07000344506c24010200840c40c3c100400103110844604013154901049c588006056106455560340107081940108180b400440c2035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292900755 1250 292899505 292899517
    0xc09061008040c080a03080f0606160312020d05160201050c070519150525090e060906060c10050402040f06061b081303050f070b0708030406020703170405250f030602 73
    0x3e580202d030340040d1801c410010091414001e0b941c81203142040d441070a0580d0700901305501c900414001103c3c030650031a401480e6550509180c000c1c0207224442c0c0c0042d02544400c64184d615200c20000e21540c50380009603001c029034020000796032486551903650041780c2024005501ca00340000402c04100900b40010340111410350050100808003c2900e00032504071074200e541d201c4581c1d440d00e0a11034102c0188640c20041c451500300110355040d18401005588660003a50116150344c45070780131a54400b5002e810b0703561100124010001509094500300c0c01613141c840401180c00316403145009030307016950380c1c403d88692110202c14201d150300d800d035030340e4008009000c032188585500c0f0b8010351080c0040c080c24070a03546c90505000442d0b11442040001b001820b00090520040b00c0d80181d01007401a10b0302d08038207013102c9551703100d440131349050b0a0b0b20502c8184035001810100103100421015000043d00c0c03100340024026100305031100b03a0094007840050960740180c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292902005 1250 292900755 292900763
    0x302030403210e0f060702101a1c0c0b0f03040305030702010e190303060e070e0d03110106030c08010509070806131704030c0609120302070308030919140c0906100804 73
    0x300080b040c04894071444841c0110034901e41c0c5619000c03100c80d080c0010b000300f007004da01610261400711400f035203030f40010303404d10900390707036a0900c44800604509130520403d001c1c0007030590f0003088040c41c0c10b001c1c000c1c40549102ca00d294000507041e000768111000c03c10740102460464580d5581903c640e007015241d481595298900c46203012002c0040072494240041101d141e054603040290840340f140e089041140d851200304a01c01c0e4105010005515054038010116181e43c1011503600840d0000b805483d401e081002041c880300800005c2a0380e0510700801a036110803901c40e0340c0751014131a9a8080c1c00c00c00001b11f13410b680c070001d900a0740c005d5003a071075113014203d814000350b81f02d0380088450103442141400716682c00810007000d001015500c81641c540c1e81c40103590f620291200522400000000424000044c0080543c1812610904000c0c094a03d8042005086000d034007041d032090314803907405417808a580c5402803201170020380a034440c2142c00c4500c007800920a079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292903255 1250 292902005 292902017
    0x40506040e01091104110702091f17010203040c08150106110a0501141005010912060504060612030905040b06041208070305090306040312050c0f0a0305090c0a0e010305010b010507080a0302030403 86
    0x801181d1081c003c8030b40e014130606480d00507141c45410003044815a84d01d1041c030400601c03000c2c0060700d0b22102142c001001240c5024000c462207607241c1c6451003900810300c103190345405000c5030386054000e1401944217041e1090010344907125180e0301c022641d0071550b03840da208010044a0b00078039440c441298082c060781c00d0300142d0388410f825600b4a904001985220b6410820301045840000340603040900e00540811b1508040d5140013560100c058491a55840880d08000c2d07140c1c400fa000f800c05450b40e505288281c24042c2c54000d1500c140d90086040c0800b0700e0a610b0200100d5003515503603144900c040d04c594441c1211600304400031024007074200302e68069603804001880c880c41c802c1e5590740c100c0b403d04448206a801c0135140d699040360500c64415880041415a40c11038406d02d00003407181d440c486994544924041a1500092142c00204001440a128905030b030300410090015001d401c0044509104504002d861040e050109001040c400e4005580090107803802c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292904505 1250 292903255 292903271
    0x2061204030e101d0112060605041403190326010b0c010f0203071d0d080319150b0a2d0c170405180408070204060b0325020339070509010b041404050604 67
    0x340884075150043c1000c40c502007010420bc24110009020404055014050000541c2c0c1144040996420b006041c041107401c0c00c0c20306041c4000030510b00110785118105941d4546580e00250300c060140b400035402c090801d035000741c06000f01e070300489440d070794114581200701d80d0408105011008580c0038030480500004103042e90084c40c010f5400d40c5900484500384c1d65418202c0b0000301401c0e080007540c0038104151519031094442c0c540703417818080030926011001c02c000ca0100740c2ca2400102401040c1e0002903405569020924812840005040840b410109150040e842600e40c004800ba491050484e0034020b020340040c070610f00b086c03e0520682c0068180c1d201c64200c45c0c0d003000f000c4104011040143d902c03444200c1c8440e1840c50032050448029120721400390b200140030f503070150306100300308400980d11b05c040071b000303800d0100c8aa804c6500d4440c4480d1280034444d0340390fa00007040c1c444007201100d04075038590050302c40b0b0380307101c0050002500c0b00820b600da00c60350710210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292905755 1250 292904505 292904537
    0x30204030b01171006060c06020c0f0a0506100f03050a03140c1b01030b0402180603190906020a020705010801080a0b0c0405030d1e09030803040b040f02061204030e101d01 75
    0x2124060f00c0756082c585800700c41d0f410b6061820600351242d071145800d0035400c21043c0d80085003a0390980e0882005139842d80360076405860400e90301030150480c4150390741403003800000700700346008007180711000d201e20703640b41d044111b04215800007806940100c444000001c0c00f915090664612040c0d009050500c525003027802d21940310304031402c2c0b2000620880f20342d030703061140f82e0600034200d40440c1810300845103402200c0c6820f49640c0503101c0040400d2841ea9a00e01c507918000e11800184480e1002d440c0400107500203640c0100035100c2e60300c002c1019070007124181c1c1600d4840c001800c5800d41921103050815024043c512031000400021416440c280080c12860032117441e1020070070583c1040c90400d0040c1d0340b0200030423150350700c1400000c0c14241225000fa0300701c0650710701501c031405d20050b01d841441c0008d62050000a500c2500c5005e0104c1600c5a40640c941c40d41b542c2c1c160003803040015050304040d0028841e6444807402c0504500400d034450b1040c98428001388480c61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292907005 1250 292905755 292905773
    0x70207030c0b130f0e040f0201022a1f08150a0e010801050708011e03020f03010f150812091008090f0d030605120f070317070206031003140c1c020103020403 69
    0x20400350b004002070074510707100c0002001c0c002418212420720307100e894080440d92403200503000800304800141d400301560310800520048010121342d00e0a9408505d41d17540ca0354a207289254040c0503e41d22101202043c1e803070505034007100d03858101072942d445404404c950006410b03031ba440807c194011034401c40b0006850f02821032000001070604100002402c040e47c164440480d00c40c50710680707030095442c080c15208680e81641d0034078000070f2400c0080d000d007000e01c1180041d50300e0300c034142e141d10029683c110212040102a141213145140009500d03205c0c00003190f400000c007180101080f0322a20015520036140030a64110052607036800c4c0c10440d4048160700043c2d21403d0906c00c07403030582d0001d12003914410080060846505003a602d620180c44090042c4000340d088243c48060720302100da4441d4010b06032580c078074068151294199940c0810f80e103400e480814861450000a2240711448000b800001d400c0f00a4100041600042c40202e04040c0c0071f000003c0062102a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292908255 1250 292907005 292907009
    0x1150b0325030c120905120c0f030c010b010912030801150509090f1b0301050a03061805030d150b031005091504180308090303251b110a080106030503030f070207030c 73
    0x150b4007140d00c04050070700400050a03140320381041c51038120340c0c800082e40024084000c0c115220416201d0220302142d500308000e070100d030300040c00002107003100d600d810f501a012000c001d8946485d2300f034545030024440907030598028003265102d40180114518070100740b00010180c5402c80c0307000480ca000c98003240b002c0c2e07581c68546102e0001d201c808400340034940030f8940030348400707411036242c9030024004000a02c0098038040e0340d00b42811071101400c402103001034122040781d41d900c0c25406031100800d40e01521440d41948841c9c0800c0f02545481228003400c440e13a01c0e40e0601d0704000401100b0080a40229801c404002c06140c00e07448900070b40d440c00100c122042140807a07400c0141c14540000c02e600090f4100300100074100c080210402d2a50401d1010315621841800040e1111172060381640950070300c99002c1c40400440c84c8103c0741042060700c0011104d0342d603141103402d0300c1d2030b800010590340041c40081c3c503c05404190341c2e8032004a01c1141c400c0d07580c139282c1c202c101c07150b5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292909505 1250 292908255 292908257
    0x207090b0d12030f05061804020405061c030804060510080c04050718030803090c09092a061210050301060f030305031f030503040812070b0403050901270303020f01150b0325 76
    0x21384100010600520a1303a0b030096054a0358041e01c60602546012400d00800c02403240da5108041049a244c0106240001c415000001e0481c03519040150200008440403510f4908040c0020992081d0800c0641101d1100f00104130030942c8070200300181400130020810003070b849041e0b454030b0b028040c4800086d80660310090b83c0341000c040c03e5040c036116090340c07402041c200050100da22000203c54418030024048a80c1c403615030940710000d007003c110499480303803000c2200001004007000c028003540069040c05001559042858240e03082407140d02c1000086043c20030100c0d02400c02940d000c8070840505049540340c0f103041e0841d000581003910b0980c000300d020b12402c0401c000c2584132100c40b4030520b003068026514070080b40d0000380014100000804e584a441c0d024000803200e01c142011811042d40040342ca40d42150b10a200c2a0014403c801445402c950103201e000444d00e0051401c02c800740c02d150001d04594809040500700f002c043c04024800301314500801250704a07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292910755 1250 292909505 292909511
    0x4290703090501061235030403050315010f08070e010c0f1a070e030307020f01020340180e100207060501030303270210020a02030109080403030f020d0207090b0d1203 73
    0x41e80c18241d0840341300d50803c0980000d003546210120340034800350000700c54107842101d40703030b290a280304500500a5600c92804200802400101500031029505c07560412070b40360b4106e400765004449107440001240e0105007a06c011406840c801e0040d0088010107050035425900950380310803207014a0b0006545081048801c2c405e41401c0c03105258001711646000d00c10f540d03103200003a4580c49105402803140b00000bc0d401c507207034028003c0c2c031440c50105030703654514141040030650481e0544280301c49030481d42001c0e40304a0050903120240c50022001c1803408850001d0b0100614502070a002c040c0f280043d0140506031b01d00007410458880c18020442e035146280180a4130320500c201d003403040c05280c000941c002c000d40085001070b011103240c0c1c0d0070f0b864900d0136401c00107201001394155091030f84100601003154002d1040b64403d0746d0301c4411040818040b601da84000c001400141c22014041040780c03010f40004010000c001e10100e848601c42c1d031118641700304036a0040111f51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292912005 1250 292910755 292910771
    0x1112010207030e1c23160b161e0b0702010c0f09031b08030711030c0114032701020a03090b150a0e0406020f0406120f0501080703020904170301030f0507060e0904290703 74
    0x800c0c40350142c15110407441b000c51600303262009480c0e010b550290300300992001c0030a400e0044100c01e101410020f400c0d40310140d07106080441c040c007030407150700c0059030030311550034840e5200c3c0740c0080560b02079584070003e039030039a607400c3e01111411220f83c40e8400e402c0001300b8031f03840601c000c1030018803039140c8c4003440c1484418581003510003103100b03040c44150900601e00c011044100e0781c0c40072001c0c0c18101c40d24a010800c400d4680040845805503102180c1c0885050b0154481c466990180300c00c0c1185980c2c00d946074407000f0110f924107810a407a48410410500f8022040c2d030000e101c0d4001600f04910500d400411350410b910034030020b28081031045a0210b244500040300e031b1290024402d960414209a0fa20300882c44001e010300141d40c001424415030444003e07860070f410040d566a56500d080c500000c4110500c04c0e1180d02420f6000142c0b640110742c4e200082e540a440303e60107540707944811108420303400f20741d60304c4900403c08580600300115084d00c15001620005980c007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292913255 1250 292912005 292912073
    0x20a03120f0806030601050603010b090a0f0914012301050c01090210030b10141b07050604090c090f05010c15140702030d0f050c04090b01090306091112010207030e1c 73
    0x710b0180500340207400c66401440303241c0356203048030305544480b50603075030b00c42014020030403d10141e80400c6014802031008941da20b02c5402c5580280c1044812001c1662207403010081c2e036000340c80300601856040d00c40b20707565000394080e21071443c0c0a00001154000c1e0380105400345c400c1010700000a585170100040c910300001c0c0c0712221007092400c464000760024035040030f4032480c044507403401a90f000c0f26500072000c101540c05808060411601c0313540c4e5a112501420b602e41d4440d011403841e05000c40c030b11402d0b0400343c0441d04141c0d11084913504c1911512210340c0242981002d454a9480c0c0b81116019107035250300030305050340215500c2070409016070448140c00c0e500400c9600388003c0c020040e40304030a80c2e0170341e001107100150011030003005032101c0301141d00c0240035905040c1400c090052201010382c01003011354030159665002c1000314200e1141d0800103010951210244906041016484180705c851007590390301d5624540340c00c80700d9103400a00c008401c041101c112555 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292914505 1250 292913255 292913267
    0x121906150b0703020c0915040f05093d0f0c0c020102190506060918100504030e0604030818060408120c0d020706050313170c010b090f1e04020a03120f 66
    0x10401c41d61454204a00da80e4020340740e510792409a881a070804002c285440f0309624020b1070441c1c01081000b045003070304080c00203000c04640491f0360740601507940c0300b400c800ca410350307850f030586820800d500742c02500020707901210050429007180d03440d101441419040c0c40740020b88042071f200d04a1030703640c3c0c3c4002841c040303d80031100d2124503401d0403280000d50000d0070981090080300c215108ad620960895000c40c50031900c180c1c90703c1800300100904920b64040e0f03004600a03a074400b41e0400ea85e0501110388200d10000b07019510800202c01c0300800d24081c000440300c0185400c1c07405581e10b4071a0301c2d0000020301c0c1305c01c036640016403400c02d060410800c0c0241c14180090001e043c0790403000b03480b0340402400c0c00582019520b261003001400c089408d0790000b6004a1031301e440c040d0000600a0404910040c040c0d910480418401140c1803a094421420250a001501c00311b50f114010130318050700403070b0009420f00001c00000d51a2500c82d0200c200b0b0381d50842480340c159001802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292915755 1250 292914505 292914509
    0xd09050105040507092003061924020601032415060f030b0a0305070501080a2306010f0e09010513060305030403060e07170c040504050f06190c0e0f12190615 69
    0x6035843e144071100301c80d00c8900020402c6c01e100d51515140d075141404101c241110601e5041507028105e40030460b05c0044441013068044110380b00c00421001905903512042808094000d42c0d5800f20300014010702c104000303a400d6080c5001c03070208100c000202d07000240342c10003000f081851150b0002a035061042d1040b5440c11141c1c5c22006280d5100e1a4130b410071409510f04200d0302c1000035154000d241c001450f01844180c0b80c1c0314110b149900c170300021200351400c0303000a200310392804c4074512505ca22601090000d00c1410103910384400c001c10304040d10760300106903132242000404038000344082c000844c050400890090600e8400d1410080250801c41c0c3e84c4150041c2e80700c1d103901c00500b482d00c0460039a80000c46403240d091180c03400021804003031492040d00b00f0483c400d041d81c0700241c50090001d0b8107118200a00d2001da8110886a5146d40c12424140710201c8a141c10584603524203950002d45515644010160b4031048a4000942c2c0003a00c803900345d120f6022240c10900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292917005 1250 292915755 292915769
    0xf03051b011b0c0f0204021b06010b0a080604020c06011707081501050a05091302010e0f041b02010f0e030708030a020f130501090b04060c020f041e0504110a290d09050105040507 78
    0xf814003499654040442d07140c1d030040d00a50707001c10854121103007031070b00010000000d400c94003690b03540c0d101d080a80e4465a414000034442e0030228055003068006d0b0b0b40b0070040b0001030700c0720741c2c2020003600744c2c0c00c000c0482c1030744ca106890000808800503ca503007d00c84000400110369030504051100a044652106010304404010840002c16110329602c030035509182c8007410769405000201d461503803514095101d0300e04011503002c54480395020b0000a0300d50002e0120801002510088036091501c8040c00d410130402080041d000d070300215400b1141810050a00c41181c0d81129a60450350300d180307101c0c14080c070602280d0f8211502c1c03c012f1a501c40d00ca45440e040031001400d2100072035009002d200b40c01c50201181d41c0d290410301c01c1542d01903070454111413248006000e40702c1610300b1703126103454003542041800c140d103800007559031010040300d11610b241189a0300f9544048102e42d15441441001c074400e040e40901c0c01983d010320008291802c0c90f0030042e00b80141d55001302 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292918255 1250 292917005 292917017
    0x60906090e0601030f0606020604150501080a06050402060c0a0308100b030114010c03030b0301052703030108190309030f0c060e0108090d0c0c030813030507080a0f0f03051b011b 78
    0x11980618240309480c000d4507014155100d0740b006030040c0c58a0296800040e04058000c200746500042c0288621b0142010f008400f255444800c00c48100380030340307040c0e5000300c40d8090100700a82c1100340c105101a064034648000400b80c43d04021454000310000340c0d1060600c0088400c001941025008a8040034515490301040c4030054a49074403039414800075240c01424140241e00c00001d81d84085c0003401189003262025502e0400201c071215501e103221400322034140c0000a50381a602c5031401800724504201da04061180e00c54412030810041000120000d8099407801c07408622a41c4c3c03039a500b40c01d000000d0210405000100d040000b00001c102c40c000303000a002a640c102801c107441d15205a08086502d54120f0304041c01500c2c00150300c001c001441580382c0c0840b4021400e80303094980300d4080d103444110000c1c024007039030314181c682c8010600110701140024401e00303016152943c600c816058503070681c08143c4c1d96075941e15007940000299541d56200183d685091 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292919505 1250 292918255 292918259
    0x1109010305071d01051008060409331b0e0d1401050402010e09090a0303050c250501050c160809012a03020c01020706021203150d0524040f031110090605010f0609 71
    0x41082c6e131040880c1c0310200079242000c1490b0392200d5216a91084d01300f001070b804904403114040c00917081a00c80e84500d0584951744039044624070841c0499003080d030141c01030003850b07a01294982002c0001079485000450341c180043d0760001900c0003d400f600c00070403145043d00014000416034180d007030040d68660308000e50804007242c110045913150a0029441d115030700400d07014055880d807600303801618000c0c013000ca40000318040030700348640024080342c0d07100d68020120b401507942e4120b6060500c259070001030804801b9081c040810307d000030b08401540c11039242061034049805500c00031400d06001e0650503c0b0a941d00d100a0000308002480c140d03000395100400b40c0280c80b0300c0004000f0480400c90f0469842041c1c0000341050001211806d241303854424103003011034080803020400e0218000341004074410344d0485164030380f0340319603103068440114030311101104e4040d00e0481c05d00d0300e005214195006004000001e02c030741c1071001e018480c0f01d0f20b8202c181480410700c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292920755 1250 292919505 292919509
    0x61306050117030d090c091503061d0a0809031005040303090209010801020f2a031b10050c0a030c0c0204020f070b06191a0c0a080307020d1e03091109010305071d0105 73
    0xc549503001c5184e4000780102107410008107080035600024180c5041c650032840d6007840d0584581980d00402c002c115918003200c641032010b000010102c442d8020129020200b4098000782c44129005015580440c81114030b907000c0b50800c42d402c41c0441c1d130b5141c03288190b040003098280900081b2008526024504400c0a4240034680c0c4181580514030b05c1007401d44580c003d404040b90414080308e403510301040d07403600404a45030000b50306205200000640d40014040c8500918044400d18a040c40000c411405020100400c1d418000150389032001a1654802020207000b6101c07504d40307552082c50155130009000c0c0000d4401c4070320340032000100708540b90580450700d0681c0407202a031b10301d50030460b00d4080d46a0038600e901a80402d10b00380140d100c0207502c50038055082e50303042da500340c0e0159900d80600c010720751032907044008401d400e80681e00140d02d079809800b961200861210000b03034584c40c26003086071142c01c001402c1040150b60920380c2c01d5900d400664039155818000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292922005 1250 292920755 292920757
    0x1e140d030516020a03080c032205060703120e2a09060f0402161208061c030909020d0e030c100b01170a0911061201050f01030c0917010e06130605011703 67
    0x400825404460350440b4110b40d03039409498002d69104008036101d000c0d10604030303200c0d000b6803d2030100c40d28a07d089141024002c5d00300702615801003205080c03801c2618101d481c04d0b801004602110b40e10450050400790030098070500414059030600c54551880c1c44005a6008120081c000d0381c0940038032119550340e25514a0f030100a85005031500030700c0400d0f40c90303150003000281181c8011540420001d9100c000180f10b00d0094400520b6583c10034000d014000202c5000350004050400500021391b1640082c14040880d440204030041e4000b541411a800512a02d01c01c2d40161815880c88034680107039841e0f484242014442d031014103c648034846402804075981c1130f0f50300409070811074020020064040003410050f21004204100d4503020401c0c000c0c94440c4054100c0c0005642c400e0141151044141da202401245400b143c13a04c0c1004401d070750750495403100801d040c0100108481485600305c054400c040307050078113202003100c5042e00700030010700e5112105004150004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292923255 1250 292922005 292922017
    0x8070e01090c0519050409050c0301050d0605070e12011506050c030415050d050f0603010e0f0a02040515060703090f061b12090e0907140405090a120201061e140d0305 73
    0x75400300c0d074a103008100f118984035650090305a09620350001146a60040203001030f41d8940c6000c00a42d00e0729940c911035030209101d002d600c013021400440000307003260060768012181d820030180c4500d043c800034007410304000041d4a140c0d550113601142000410301903004042c1c17400c0040c6406405280b054407403040f03008135440b0610900e44043c07164442c408072100080d0b80c0e0350800240c01d286020900700781007964120b01c00d40c206120300320003d201050300d91554107000028031450f0382640c01d02000d0310004007024a001b818000510340c0381ca1711001400007602c00d503110000c1e5820a000ba1010580b10742254007081289007540384c540d16992402d90380030380c0000001c4d1130311211803c2100d40050682040a03008083c2c014094110400101c200603100d1050221050f68445400e01003111000c0f5000d40c620343c00109202c010584841d580200544103100110b4810f0b1100301d08074170b0400340803403550004040041001f03907400f501c80a0308040c8040301c402e11043c5070341d18028850301401c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292924505 1250 292923255 292923269
    0xb13110603190b0a0e06061c050a020c06070e06041208040503010f0204031a0603030406031802030111090102100e033009061006021b0603130b040606031b122409050f0708070e01 78
    0x60038150011142214800401c01c236201802140740054034100a9009154400003e1282502241c02907006507007050702204044c08403420030b89000041840c1c02220002624031180410001c1840e45007070054014119100001595951071468251031054001900d680740c0240d000901200742c7e8040101d80442d0320038680032507442460007818950009400000b035156207003203864058401c10f50080c00210901b40c090f60690790100b000030007980c80d03c1c420111140c0040220001c0b4203e1050741081650621900c03000d185c000c8401000a0102980c0e031003082d41c0504104100509803000361000b07401e283c80500345107825000c0c8040004103111403144101c9001c03001852400c040345036503181603041500c03603203d070505080000050006020640e50784c070754441c4c0081c281394540918401c0700d94030f120f07010f542002d03502d41d81120720401150300309030101640f01d6529070303500f4001d4248150050f805070840400740300059251804680c0150034941241e03908100055401086604680d08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292925755 1250 292924505 292924507
    0x21080c090a0e090703060b0a08030909042901050a1401050a32030609010602120d051504090302030c0c0306010f0b0c03070516170a0b13110603190b0a0e0606 69
    0x145000240359142690440030324600c0c5a0200640000000390910844c1e006e0302c0100204130340c1c44c040c01407400b144d0088a41d01d9104109045550030000000e540c0180100c031404175000b0445140ca10f203d01c148903140c1845081c0c2c0040c4014541003808170020b01111400450f610b220000107401405860102028001c0f83c030498486110a5191817004140001245400303032940041040280c00580e116030041c5e5603e400412913500001d81001c8040c40a003005044c125220b4001001d0300e00101000074886041c080340c411307a2554040c10100a220f600503603210540000411700c2c000307101c09843d101c2c0d1b201c000100900b603101005002a607001c50100303555518400d40251a520800344010198420904180168450001c010307080e03840b0000e40000010110014591390311260001406039120140407410203600b094002411600c00c400d842d100028100008042d03410071504406407141c1c0e021b0780d21901c1c400e8860124540d5003125400161800c01d09448807101004040c1801140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292927005 1250 292925755 292925767
    0x3040302010923100507050714030601031205090301020a0521010302060306130b120c0306090105070206070c030c050d021f0612031107030b010311091e0726010306060321080c 77
    0x1490200c103440703d030701c0034100324107440e02c40303200030030755405008141c6650042c0000820b11085801c01d1002c000d10003002080131340d0964413202c20090b56401e041040c41010402280303251020300207002c211030103464203500d40b14071160010f01c0c011000c6442c15001240340041c070043c1d0b1000d0990350090400d6891000150100103410b00419411825075484050307100800d22241000484034501c40d01602660381c65114014940d00380c4030165400d80c050380051000480c441c0c07040e00b8040e42107019240002000201e40c0302d450402d01810001e4006820241071540341d0aa241e4820004005541c07040240c2843d0208020503142d0303410004041011340a00302c176101c0000c00010018540020310002c840d6924500300e0346155545a000d8040c03804c150001d200d10f0305014030b500030300c00c510211030255915008101c0d4500311b40210f54120010022041040c41003801455028512030400054418154100b603207030300c4c0403005c0814820007050311618a017644240000d41101c4541041c075110030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292928255 1250 292927005 292927049
    0x10f05040e1c0302090a03061b02030c100902210d090f05010905040b040915090209060a0518040203070801021602130605150d0b090a0f1d03040302150c160306050108030403020109 79
    0x4480d03185072980c400e6001001109101070f680c400c40340748003854030109082801d02701c03d90712400f03504066a110340054140710307982c4103e03402402c1114030041c203c0e0078415407140c50106241078690700c110359501058001400c01cac2c10849034030280000303c0705140f5440c50701c00000d202c000da50041c503010799110002c0044c00c0d20f8070b070020040d0b1a802040e01c86504580e2060304020110118164450404034005c108941089036200c0c054580103400340d4850070540ca0024205103000e0002c0341c140c81510f0b0300007094502840a005021660101540d40242d40d00400059009614101d9103903483e1400070003040d03598011a00e012258568440d80f1034034144c410750018856400350581080301c64041045410b0b25502c49490540f044004000d00c00c4980310806040074607404207022927104220034400b514100a01c01e0718010950b291500d05801079034040d0601d650090b061504010050701842000040d014440c0500212001035060901e141c0000300b82c0c20440c40743c49241d25459075450f0402e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292929505 1250 292928255 292928257
    0x5090607030e15070f111804060e0f0f0f15010605030f09010b0607150509011401060507150c0806030601060e03030414120d21050402031024030308010f05040e1c0302 73
    0x1154500020f80d00e0f89000e08108090f580030241c02c440a582c03900c0741d00300600d403075a40d001a0031140e811181c400c0da2550317266030050502801468181c894098107031800f000c00c0140368480d4906801400282000f01d42c502c0c80c2007403005045180c00d070f01e08018030105900100b925806400790800042a8840c4030700c1c103006100091303490b900b000700040e10205200f25442080e014001c4100c04204035a101e15245080703a60481102c1106844000104a5a4851005401428010a01000d6640e0500ea0003402c8a22000360701c00860080740402c40103250030320074140113101d01c1c28407c1c1d00072004c80000e41c0b40e00c5903000b07840041c07100005610540d150241446c0403192403000300c80000f8540c01025141c03901806840c1222170503010082511010b0303000d014005e56004d0001c000902409100c00b000d00074440214101c4d502e1000c02084140350b0841000007140a42c41b5070a0315410518014030a15064020700d026508180741e40201c0900011103808008601000044244a40c5006c0f00a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292930755 1250 292929505 292929529
    0x18061507061523010f0509040b120a050114070c08030406140a050103141f05090f100b0906010305070c1b0503121909050109030b0402030712030305060102010b0105090607030e 77
    0x1032920b0300800007a02e0b00000c1840e800c0d10a2810f00e60300001486901929116004100600150707203000020207040c0164060003070004028408206180d400c07010442a8181c2d450225280c4d000c0580c04085c00801e104581110000442d44c4009140980e8003500c0c11480d00001046054000005424410355601105005040685590035814080c0da0100903000a000a0754007040904450140420014854403810700300002d1104400c070745514140140b100814940e014007e6808880d0000400d01a241d0021002c000006441c9010b400b88035140c0e00041170241030500e01814408001c1e0400800c10040b82c2c40720012a050b00d003060501d002c04041d50140d40c141c416501c0e40c0b00410052805400340a103e00d001311301c21071600b4800c481c14112071285038089100d01500b4030214446900c000d07481030000e0700700d400b210b40e00c1d003036150100325040e0254006503446080c44a507690a01441a03485801d103002c0e81400582c0002407242d00c07403d2801010311403804601c54103911010b0804075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292932005 1250 292930755 292930763
    0x40b030405010212041101090f1406070602040905040b071112040b07050a06060b04061119021207050d150506010206040506070f02120f070c080d1202070516080708070518061507 78
    0x641002c0c58801c1b800a500b6141ca800310300c01c0c40020410f00400f422200444242c041d4030074014504500b031000a50004906480c0c40f90200404141010380c0e002d5240254807c1040c81c441d0f10301401c00502c00c11006556504330b03040880481c00c1c11004070300780d405407a41c0b101d01590700c20151800614200600780d0081456041910015040d02607501030f00484045481d60b80080f0403143c440c503207441100100d1461407104409860140c20700361800a1f204035003400300c03000710341c4510016410002c480411518405000300301c4010200600030540c100d4000c0c0020003541c01c0079559a500c403c0010a2201040034410310408174074400c001c2508481d40c003403001c0d40d90b2003010b21a000c1070703403003e00180c1d912420301100081542d00001c92034000350791707607460000510b85240810080d50100f8016100c80c031826511003078074110703c003825005101001c02800000e2401e40d22908001d41c1d030780590300c41d4003043d4800c40c0d000c50504010380d11441c1107034220396425410152144900500350050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292933255 1250 292932005 292932037
    0xb09060d06030b060102010b03070806011e0306150510030c020a03080a021606090c120c030b0705190f0207150507230f0c030c0d0203100b0a080a06052a040b0304050102 74
    0x800d204515510601a40086c0c1c024800325003c0b0007495540d6050f4410341c0b007141d100b40010480121104103160030040d0035485a2160380e5242c89841c2030304e5a1960a00403240009820001c80c40d05400141e810b1105090601030b034804040301030b46034140224054144074900d40007030002602d40d41103c0c5002d030461807240700c44280d410800009c000c00341003101c4e0301042002c042040410a11030140301507002c600304801d50b06550300c001c400d9801800100034058107000c03040028101c0b5003000c11000e80b5a0343c00c0682c40800c44024904119a8400540071003c81c2201c944039500038200c6036401d40022400c42c2600321030368004014a01141d616041d8058007054003000302c0301007141500950100d04555100d0b00450411010700c4100c50001d62590182000d565811050f410210b001d0340010803040440350b4484000341000031040d4121001b580d200c040011070000c8040900180310485030034206424480c1003801c103440b0f107000711402c100e4080009401c000c0c00b50112041d40700c0180c020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292934505 1250 292933255 292933259
    0x27061b08062803200d0321020a0f03110405060a080a0b03150a09031e05070b011a04030305070501061e1401082215053405040b09060d06 60
    0x200201030a903681c03480340c1c01d144400300035151042da0190346030070000c11202c0c0d1546595586104890010340e4042c401103c1510100166204002081e001e40070b921800041d0f502c43c5480310600c1549150804094030600c2844c0300d0980c044c03800303503248005007400610041200800303240c038007807035200560011002801e00ca025a01070455030088000c008244001100c850406468001241c0c0030303d00810840001841c8860702d03000f807820b46001c2d00f41212004082e803100890054030500100100d100054a40304009151010782c1c0101412300d14107614412404222070107210390f210207002c00c0008140081802001c4d07002800a208030b180700c0e0701401b040d014280e907841803449031a0601001c0c0070248840d502410341288181c48804080041110711402c4201c0034201007401d40d4080c0b0b00c49240c98140610340b04150065400ba10000d01e901090002c2c240e403120a0041134000f17004c81d13411034490940003c250f8050b40d0745024180d49841200012070b40724042d80c82da40706028104100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292935755 1250 292934505 292934507
    0x1506210e07080c10020604020105030c0f12010b03070e030a050c19080303040c0905010e0f2403030d050f1f030b0c0c1b1504030503040b0f0c0303100608060427061b 72
    0x110f924540003034603015003504a44500340c2c0c945c2d400310b80190208000b000042c001401c0c2c5e00040c141c0701181203900d400e108140c03c0b1100c8040e4240c000c5d03106480d00109103d107081d0800c002c0003036400114024031065030b1642c1c0c0c564849c0814010350f406650342c2d001400b00950724107140d0700508642d0003280e4491801d410005017185040c0300b09003d01c1d20b00000841c00341d040c100f07070501c600464210103542c2d0f1900c070030108100d80c01001594841c030780002c040380256400c0c401004038400c01440810b5070308041c000d1820b0800c3c00340842018143c1503c291204c41781c03d6031480101d0b07400800407038060f0341d0f202123052640b01e804400e19a03070158590320004840203d0188103d40829030b0038681c0e160320200c012209200f00c1c04040c109a10500c0100603509408009045e034141040307045040c01408864245076401c2a581403041c11407101c014030003584c1c0481d006610506c02c030340502954002a03502c0d1095112140c0407640d8120280d285424007800fa04480c10f10340305118444c01415000f90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292937005 1250 292935755 292935763
    0xa0f02061e12072c030309062a070513050717071809050c0403060f0216050622020607060b1504090c18081513080d090302011506210e0708 61
    0x88010300702c90030440412861446400a13019072800012210f00c10001c4801c1c0c0d41d2160070402819034180700400032000d02d6200d043c084d08020001c1a80101d90307020303141c0d42e0342924221043c42c1c006e6500c0140d0030005a5504160704100030b06080c40015207445e100d00c1160300644110310100003282120a2222545c0c0c4140d1540d15111a401d51421031500d07101c0d4001031b100d094518423400c081c1400203001090079075100102c000801e060062900b007c00c0e400a106248028080e10140c121604000078100102400a01100d0013201540054096070004e0f103c4d0142c420080c11069640b14401c41031748581c403404c4200846403400c143c40310b075100c40c1b0340040d0021140400c00943e6a400040030505005900c070151140100507049948080d00b541420100088c01c0b000380d0405001c003030011035841001000203180e502c0012441400d10b0a010307081d07400c062035000074207450704010000e082c1d00645101d900d21440071300b40d955001c0702d074881010741030a6019000601420300300043e034642c005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292938255 1250 292937005 292937017
    0x110709021b0c010e0109180e071508090102030f010902210a1a0102060103211b03020109110111150a0b1207030b060a030b06010c0602040801020c060105090a0606020a0f02061e 77
    0x1c0101c4240790700c40001102d220744110b0b035882c0403402103003060089011146c103000000c20b550500240c0c40c096400c5081c0b80030301c2680115100e200d50700341a100302d50312000c02a030000c0424020351640c14090f0121291490500c601c10400794080750b0120504e00c50250711595100400602619061040b03c1900603d614204501d9904201d4103c41d00c6500110300c07039040b6600700256000303030449450340d118100350b0304070503908000d40c0b1051b0444004101100c40c50b254080c0d4000100e8004034a0582e0b2050500c4100340d045c40745e040c0b081e0305096400104c0018241c803641082000341c5035844400050304072040103030362290034081e0510008100082c1c0c501124001d0784030102944130002442352584c03480c00302900d40e0503038200061065009504038000320b0303c41e843c01807a1075a50320702c40e82281c010740d216032403d0b0000c0004100d640b0340f40e4600e61b0010030308441082443e240c0f0401030740d0346c806803c0040841036401019401d564170042940c1c5100600e1184152040d04d4a090150320361001e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292939505 1250 292938255 292938307
    0x61407060e15160c02090c070c05030d030219080433022709040201080403030c05040506030910060515090127080304150801060e0f03120a050a110105040b0711070902 73
    0x103000b810f403d0070300c101c0180780f0450f0058000252529031060f40c011941c03041c401511442ca020300000780070745080007902c2d41006070344ea00517220220f110f2015003d0402100100801012000703100200341b004540111204685402500040c4401a551032284202c48400030300351000c00c40003030302e005190003034012817050002030103000c050300100520702e502544c3c0680007481c064001000070f40030f58088400300b01a424a5401e0030381e01c10019041da8002c030b4141d0340030b0700440018182c00c0e00500030740c000341c43c0403941d4041c1e101c0e043c2800302543c0100c0682c41d04014040a48403070b00103a5081001c0c0d0300f2401c0407000c0780300e07449000d403a5a07580648165640c80c4540c8407a101400e00c42c0c00301034141d410540c3c030b28403503d54407400c12031201090340055a04d0f00030600780792243d40b030040043c1320440c000e4582a4948880c104050400b0491910803c4164144020440060202c80500f580225241042150034409218036803400e1060b410403c90507100141d44960407400819001c0c260703842c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292940755 1250 292939505 292939531
    0xf01060b040512031e0304050307050a08070308060f22021b03070308070c050a0201051c050a150f0b03010501050304030c150b090a0912110f06010b0a030c0504061407060e15 76
    0x901040684e01e1003900b11006180d803d545c403860f104c00d2500000c58215015008407821300350f0507201e00d418040c040e44102d905038000200c0408054101d407100307610400803142004528045408a0b260416003c12028484180d0321600003041c801d40c140d0305459031840f6108145841c43c0360342c969a60007030b40140e01207210744000400b00352040c03002000107684400500b4030042c3c15401034600d40c002555030900c803400070f040c00421009620485215080003400480e101510402c960a069126040140e45508540307081c4040b4861000b101c0c11900700f8a030183e0340341e0352402c040b50668000c4800800e100814150941000d06e43d0b00051a41a8216403410141d00c4e00840c41044034052540109020341054550a01c10700482c83c0b00d040c8030081060350a0782d80000e801d14180642600000380c00e0348089010700c80b140d4544960150710101e41005840c080c05c1c60b9001d80103010207a030191104000181c0d2004102c00d036000f014565101c802214403551304c00d002c00650780c078125003030404095 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292942005 1250 292940755 292940779
    0x110303101406070c09020a090b1603030c02030a170c040f08010b031212060d14010c050c0606010305060307124404270b060c030a0306080c0a170f01060b0405 69
    0x2d411412182c0e0340342d0054a0a68082c58407142d80043c0d00998600e1003407000180000601c0c81c40103006203010050f84058400c05240340c03402030215880c0105a400b103501c14400e0108107078000c016155020504080f150142e9902c2541501d244625009840c0e4508052000110f080c0c05400480c070b00b00048042d01d1400858000b4601c039030064041101468403520007140240c141f02c004500c105029030b00150705080700103030703c070b0070350b03207420301660001e0400109044194003e00009070031040901e4140300c281007400001c0d5031a0750310300590000e0722601528804000000180c0701c0740031004841c5008403001d4894490250b044280320043c2c0d000c884940c601d00d00c0c6008101d409403009242c0a0b038014100340b00200082c58042045410342c0c0d078a0a200d50581d80e0700000e00891040f15008580d240d4aa680c01000d0350501e6001c01039603817141c10500310030707910031452009942002d0a044c040074001c07100c091420b42c450405000c0365203811000704807281ca04004000343c030025a510f940302d031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292943255 1250 292942005 292942009
    0x4090c1502031207110f12070c0e01030b160c0c2309010b16050106030b16110111070308070509150d0e19260a08010906081b0405071103031014 63
    0x4440d0300300c3c80700c800d40380200213400c035801114841408103180c012500b2101182c59101e140441441030b8102d8a400030038000c00304a6001c44c0600542040288412103514583d200c25400f80040c22908000c0150035031180e005116507400ca5055030400c0b03504a51726500c40d81d0140301070204140f4898442d1001450f41c590070404411812258854642880c1c15451288080074043d006000c481c0c0b5522408004040303103003503070341c0d034001e0203000d114500306103041c8c07009006858600d0340221740740d0411510303024451000040e14111071309414585415070f64842c089a2601c144195250f10013044141d16800303407888006810360094100701009030903405103030103a642050b01032020302c08000c1c055000000f1161480c0041011100000e145040107250465140350401072180c0001940b8100412040b00300340103072002800c01001070b08104148420621024054215031402992184041070000d446460101244080002500c1d22402e00c403280746480c0c090747c030a066030304484d298448424 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292944505 1250 292943255 292943257
    0x6012607030f1e0b1c0b0601021903080c0306010e0301140f09030c0c0d0204140a0903030c0509010e1203040f030803040209070306050d150b0604060c0209011401210b04090c150203 79
    0x129540312201069154420f00c00701424060894503000720b840913961801c0214070b42d0010b034003407180c0c82600107450683c000a00c1c0c50414600c40c0071070808074070300d580030035004000f0903080406202c00300c1c0d0720f07a0b9000050710440d2424812582540c6004a010903551018071404d006480801140c8180c0c0c8984109590b2401800c10b485201d8011314a44500c0749416801c88c401c0b0b43c400340000c1103860072044050014442100d00c140c0c501d488422031000c05506104560140c00a0f0400c6424040341d040000d02811060b01c01c240540381d1040c85181c1f01500704151801801d041c009100c0c45c81c3c4901c2c0a41081d0829038040b4000c50031035002c600346074000c1c0290700c184e400117031040f995482c60341c0300c0f4241190100000b2003c0c0d035842c140c45c08192200e600410240203141c40f1081d07140d00354410701c0110301c130580c82000c204084002c2582641c1e8485030704405c07403070701181c4200784180340341920340106003051034039078400d08d031130602410089a25890030440c1c1601140120420307270901c082c2c1c0c80e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292945755 1250 292944505 292944521
    0x5060a05060a1b050a03110705011716020a05030307030603201008100f03030e09070e01140c07050a0f0806090109020d0227010b0414010e1806012607030f 68
    0x211034000d000c2c40c08543d115800303049620020100c03c504144407a2102814405568000d400180c4200218083c182c01008210000c3c102881c1016a032140e0b0340d0043d480c00300150501480c0714000b01c681c04000c0c400c10070320b000660004140c0e03590341084040500141540d00c8121400344210302144880540c1580452680c0300242070000c4031840b0300c03c101c1d0b06001c02011a00e21072130308000440d48510f05040407015512949501c140d00340d60b0703401c000840800030050420000e02c150f6a05c49030360303c0510340d1040c01061220580302c4046201407402c08030079401c4160070240c8600000740f50058a5681421551042d042c0c41568503501d41d268242c8000f004e020b0740040282c40031030014141026a0030744118040d1482c0b60900c6503907401154803001b80d1000c400300d040420117016070115403a500452131000d080c2507a41607168400b240400c0c003a07003d100520500040040c02e140d01030f000b12201106100201d1252000c41090000c0243c003c0e24031100180c9042c0c9034119000c19071041ca10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292947005 1250 292945755 292945759
    0x9010b150f03010510050712080106030e0a201302120a0c1103090904020a15030902010f1817010608030703051201140f12070b0c010501050405090304060807030f021b0d020105060a05 80
    0x4516800c04090145c6540c840c415642000b800300070150200e01a00c90500882c951030b80c825480394940517004043e50405412041203412086003200042c09036010310354001d2400c1203030b003080c402c1c400000304400703c942c01500c20640002084051400e806100074410900c0e03102c1001450110301c421100d0184614001155a10811003030b00b042c90018440e03030f449880103084040c059201c1c1c04c4094140c00390303074a120200c2d407580043d404640c1c0181400d101c45400f89001c102d52454881d035104541001d21580780c5000741c0e1000100c8418081d0005800f41900030220307a981c14070351500400c20307440305080c0383c450654000041940070601d070346800c141d04024140019814200c08201035805080808140d0341b080341c0c3e000550b05101d5010700741c1000e4480002500c0e6140005000c20340e10300030f003010f155410070030060080310b4000c0c02c41900940342d45800100001d10701d0824009104c0ca010f44d21100c0310700106480c0342c1d1000680c968601c2c00c50b41c000d200a45800341480190780142c05015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292948255 1250 292947005 292947007
    0x140705011b0507120302071e05061902030705040911040807030b090f03040b0f0c0c040501290403020d0821040c0303021b0f01030b030307060603050109020a06020f060106030506060702040509010b150f 88
    0x10402031298018000b21070042c074080fa040f0118421603074079540b40280468271a04040d04008540d444a2100d4002c005a0b0344103510314a00b03503000505910443c001e20280c02d9075131050503c0300b410082510301805d440000c50703404644034100103444040449404009226210344800e8100010050394100d4a02c010424108160005510300541106000d07800510520000c0960b86d941c80c017546c0d00034100c4041c800c0c10710304031814221208200740c10a00101e00c08100c108016110b20180340b8a00d60030419103a220070084280018080011551050701c1c5642000e12061080d80c108040480f0300c07940885030708021321140e501034204c00040c80c0c0c0d80940885000a2554000d80050484500c01030a41e4a00413040c2d0b1000100c4000307030803d03600d5030340d103100003011410401c030708901404a60008102c00502400c00c0ca540d60b00c140031f10030426450340081b5500351651000c0d00d01896005105212500e4005a035500030b200001d078071803140300d50b41c41b07545203100740d0011a207901428915075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292949505 1250 292948255 292948283
    0x1d0304290a09051026011511100504050307081207080708040218071b1506050306010e04080d0b100c03230409200a17010e090a060c140705011b0507 65
    0x1144041d804056401030041465048280d281c10303500078060a0785c203120b00349055041a501c0c107036581c405654481403000d01a4000569500011000e1507444816800309155550b85409415406480c030300400303011001c56140c50291840e41c070390340324206a40e0b406134582d6901100700d844050540340690441003d102c004030740b0769400e2440c0e51288030381c1000d4150303003010014542813501e0b0030400d45d10344012000a43c684c1d030382400b5020040100310001d00f41541401c081d904141d0000e04002d1050f2000602c3c2501c80d4803542107546070140084c44200300c5c2002031406050052440c0f02140000d0100001650510024050f104500000740b5110704141c01d003001c50000342440c0400b41c940341d000442030003494489000820800900e641c1c4c0382d118141c2d00110301440441a00201140c2c1d2003482005100d840001d0b40c9040c0c683c01c000041030701c000826080c0c0312032000250529603c50006160b00601805400100071940008691603440c1c07001d8208480c2402000c1006242e1300c0080e486d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292950755 1250 292949505 292949509
    0xe06091e04020105190801030606090e100e01060e010b120c030c0a0c020319080c0105160c11040f0203010f0302010e03121b0c0a0e070305060102070303050a031d0304290a0905 77
    0x30250301a00c10b060441c540b5000c0501080c07400d440d0050080062480c000500811400d805240c00404019005110001d0000394240e01c0d45540320450074a60303a04c28a48010072000d40080c0c008116850308009036584450011609038020b90501b00b00c02224400b0401124000d82142d20070400700410505003443c0100845408856200c00c0ea0305105209031941c210807080358004000788191030444d59001700b082038900b07491000b400c00003454a441d00a07604903030084642400180c1c45201c800299102078000717070041a6119100401034804000403030f400303500c00c49200c1138078002d0f00e5028100100404040e61041c900d0505145000184068401c50803080c050796075400004e0141d8101e08a044041030306101030b68400500501400117100003107400d0321615412120a20103007d0a500303680303002e0418400d20300700c01c1c1050ba4442d090042107181c20540000301c450403040d2a40c40c3d98a04203503c4540e5001c0481403090f00c600d1540c03d107a103800d8220380c80140c40703131100c080c0d1501e8102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292952005 1250 292950755 292950811
    0x7020414060a0902130503011103070f020c03120c01151404060503010213030807050a06110405090115170910090c0617040c0608061c05071e060221120c040e0609 71
    0x1700004d000c621012449507400e016a00785022580318203612460501e80041c005140340d030020040d501f00d4503006145441c00300d0010301d5001148030305a5990580c0907c14010882d80a01c1e80e40020050008140c0c0c1c416503000c103902c081c1c22201405002d446508060803803050704100182d03119000700c1040000d00300005009420700540584080d04499102c0000340d0340010342161890400042c24415880c055000d907014100c1c2c5451444114604c8101800307080b002c0414802a13240760001864440081190044100d40d125052107140920300d0180443c4c50a03010741300202d40e030b1035901d189016000120718800d0f038009420500c0309141038026a84508045c040389e8000000c0c2d0b528088131542c141c07011007000c3c442d03002000d40b603181098150241d4800a00308035401110031041002640c0024510419206003c2c403d0311980060b000d40c806103d10703030701100d001c0d44120410a04440b204094012103110320600c0350603607250020400d03050012100c159881844040115007554009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292953255 1250 292952005 292952017
    0x2270105040806100509010b030108033f010905060418061806020f0a0305060306060a17030904060803121f06031a06030a0e0c1017131707020414060a0902 68
    0x204115240a840e000d00500308101111600a4800c40ca04100400e01b403c50b0003031300400103000101d08650500540381e03241d200d15106001c0004e208100c2c042c508070301c00002c52042d1101c0c2d0071203102c0310360202c0000307441c24244038000340a0701d403000040081c1028060030141c06540c00441c81020a595296801480041c0b2144100181c003041500003d1440c4004c2941b001e85540c00d42e1178220b0307800b008044e200000c1c00503004e504044148001500e40181002c203990f40040411850034a20095924501401e84625409414410002102d01d00800100b9007070074030703201e8134003c0e41d12601c036502200c001e11031944012585c2c50041146a220740d0000e407a0051610a88420381c00407000200c0036042916410340059079401d00340c115040820440500c00000d0729503000300508883c01030700149031088200005000d400000b10030b5448501c4451449030700c280345512240d001001810150002c09080f4041c9241c0840da0a407820300c06c19003441400c009104444c40c904040304180a0b4000c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292954505 1250 292953255 292953257
    0xb10080c030a110d0b030d09060905060c010207020d0609050d08040c031101020a140c0102011805060c0715050906040c0605120c1602061206010e091005011b050d02060906010603022701 81
    0x1c0a144140d520f03904000c0110707000340394010a0240c44201051b05080403030159005000e0f44074420411541c02038070305401c59800326402506c1d20750381d6107014060303c9960310080d0b004030308040e000100310b59076210700c10341030150085074140702d10040140c074600e0003a03601034000b02c1920070800003d41554400c600e100410701c141c2d01803800c6660f4036580d142c1100034042e4107411010954403256424410701c03014130b034081181d001d0300c882e50301c500b42c403103401030241c0e18803040009110b82841100311806c4442100c0810070003d0b0310707018007a0794036050f0036101201d0784121500300095942c4514140c400340d0071071740141150350b100c018500c483c1e40d20030a14a070316910126455805a5100e402504d00300c8442d080c29801c901c3d0800004020b50303c560101481800303010140710b00d40303554224240558000b801c0c10715840d22003403800020700d111540003e1940c8900c00040441d1075021800a019110380811280640d0301c2d208154181d00902d00c1404203180801c80c2c034200c20312440d10440c554181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292955755 1250 292954505 292954511
    0x8071d090a03020c1309020d030f020c0d02011706041104030b040b181e1606120f06030309291606051602150c130f03110301110904020310051002010e010b10080c030a 73
    0x4582c045548d240e01190141c02003000907020040054050169101d049011202080800302d01c0d40080c0c501030b56541005107600d00400002c16689517030740100110294240c0094070380741c5c3c5c0d14203800d84603400c84044850024070000f080440d044d2201e1b10742e482e240000070348600396502c00030103020404e00c85402550303c25041d0f006803500440d0303092006096a681c0340e03424468180c0503402590003a01d031311690149482c90400100e079000148005480800c1c680c0c0d10b009000304040e1401c00d2102071640000d8900007010680c42c0c5210040307041c4103100b131900f0304c900c0d541c820305081d45043c240801d5025070007070300c11905806101201c081e0b00806d0202c0e040d003000e074102e84000700100c00350410307082241e41042c140f052010380c00c81c01800207411402400512900302e070382da1036030060400450055801101240311004d51103901c0c13010b081c0c045e0801c240c440c424071000303001e001040c0030f6105551a219812019003403207916400700905507280c00e285034540000000465000038281c0300d980d65 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292957005 1250 292955755 292955771
    0x30604021e19020c09070f050310050a0e01050418150b2e02070e270c0d06050615030c030112080c010e03070c081c051308071d090a03020c13 62
    0x441c180a040900441c0301100445003100ca0080c2c5014101540036205d5000c81c004c100d5400c0e40030b02c0481e003100151600540320b171101035000c80c14410315048542e0008034404040b412036505c4030f2850489104443c00c0c00405103000c018000f20040e1710018244c5100485c04074641541501b220f01007407806031854070510101442c00560a0a0603070f80e0b074903002c1c0b5020920071980d0400a4030701601c001456141c407400d0200f2104070105014600551041c100b0880c0034602405008412a040340600124500c164500d018001040211502c40c410a85844149629202501942c2c0310740c1c4035012103469a402d0100c1a07182c10001142182c0440c01004040da65620038011656125910402181c6403180e62a1000199099400001c80e9070302100702d2101d0703039800401e90f061545950400d1030340c804002c20000e00c150155002801d00e0b00c04c80000040864a266692000000703a0501c200c0070703107500003500c0d1a0589440041d005a026008501440c0740c00304600c0c40740311064500241ca21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292958255 1250 292957005 292957057
    0xc0108090a08040803090f010f020304140d05060a060816030203070e0c300606030402010813140d0210060806010e04030e241206040e151902070f1505070503060402 72
    0x143c400d0700308006503000070800350124101180000c0100009017000301025910f480001d56900a501c204004200301c50b045104a03118030180228281c0c12000303850700c500d0050403c0c400b40a0344e00ca200e126108121170b07007255400303010184083d213030b000740034181a900d004200041b0b800c003e00401d0f01c1d601c040100c0c85110001c02a190600200144c40d2076801e4807100300b800e9181d100030300581c0110410020400140c1e4042d201c15480030200794106490502801d01c07642402c822540b10b005d078401c00b906020007940000c3c40d401c2860401105000c0f072a202c030b0400340c60704c02c00e2140c0c0030708019007404900000e009a007000a1560040e100a109041c0c8507161010024499180012910000b941e1001000504800c59100c2025103090200e01501030304a60b4800d0680d4004524040b0580030401178003213004401006104444250344640b010304001c0381080302030380e00703da014031041e140803200511401014415082501c50504590783c50050002950012050072504200241d800d0588 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292959505 1250 292958255 292958257
    0x1903140c0f0d090b0f0403021311041e08030403111011010c030212150112020a03090b0103030509030f070b030601050c0a0210080a0b04110d23010305030d1b020c0108090a08 76
    0x100c561074005207010602d880c0040c020560b560003454400e40100720885070490f004046070203ca0341034070901e441d00c0c0c420200400a200c1004a400c8100001500041c00f0741c050f4194400107102c00350001103d90794041041da2486540300051860002040c1110380d441c0490500342d00c0d9525061040500408d00e8082e402c4410031030326140400e5011510410f90440b4003029039001d500c0d80c0b601200300c100c031740010340100d540903036080f2819000500030303150610176040f03d680c2540c4007070014055610b914029090f500017088241c00ba200b02c02d4000006500062024100c400c2c11410502c3e6441c2c10004640036408940998205e02c00e1040c1c504c01a200c10504012001003031b5500070381420300d4175009050b910b2800e50f12784a40d0500b2000440c848410013182d4250090b0640014031004803040400324401220f264002c107080c003000007050204c08030052880d1450900c04100d001c40100342d8441c8106460b4444c0c0044e0700c283d05248465001e0341805070002000c5048800300d10580d554941c80b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292960755 1250 292959505 292959523
    0x30b0c130b04061101141b09150a020c03191101170a200702030303060f040902090106080a0507030522060b060708040f060201021c0f06120f02010e01021903140c 71
    0x1181c10001000c1080690015241440042034402400f903020001c48207103002c0b0010304025071300c0c0c890421203a1010361120440340c0c0454045c24250070001d41115044094001c4071400015015000805e5194600850440340c0341c0300050040d032907407402d6106c5c280203c0704c0700b10030360602a00400c20242c042100c09101d00c14000c40c1000304036200030b0546128010140305040c500c0c2042807009400507035021099a510031001c1d00c09284107400c1100040c0503044080c03000e034000c504c410012070020b138005030580c41035900000520064482c0003084007100c200701c441c56400d0f8020390000320881150405d42e01100d0007103c01140c0100711f0341c002026540b1050048a03030700c2c0e00190801005006076000340040c401c0b40000c6041820140030400e02221181030f0a2429540d10600c0c1d40410740c070f0f400140580b40c1d030041d55600d6001c40c94400d1003104500310583c045200890b805180398400644106104504004503050f0300680e902034480b81030000d50505e69100902c058050800d04000c1160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292962005 1250 292960755 292960769
    0xe061c0609050d090f141c050303011e03030503011e0306151d010f05010f09030605130b06040b1f0309140304060f0c050307021c0212010515011701030b0c13 69
    0x80720241d07440d1040c90f2410741c2c0800c200740402c00804102d02d64400208008603882198040600070344030000501c42d50121210846404600c42c092003131040000146059610855640507c00401c40d0001d0100c6041e00c0000d0001d08100f0041c0800d9481001d84d100f056407250b01e01440544a98805c070644803d03d840c090904400e2500301711001d11000902d54400402079511215410301c042a60b200f011805160b060000050200d00a02e00c40e078401801903070000030801590403c2201c40c0305510385000183d43d58143d0b08041a01881e26206d5070f1002c401c010001c8140f0515200d954180c10b40c440b0000d0281a910068600403808200c0c001c8011a035090145a48508000e00a4115000321052000300100e201021002030000000c5960309a011252038503504518a42c50720009101a40250015a803030301c64458110150040343c021207400c92030132046070010004492265240e54000100e4140100400c041203c403516941c000351b001d960249880c51904000c804030a281c1e05c145 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292963255 1250 292962005 292962011
    0x9010e040b03010e0d3c0228060c030b010804060f06030503040306090204051305071206020408030a0905101d060304061d07050a0b07031d0103020c0f06011401090b040e061c06 77
    0x70a85a446a8240903501c103260001c00c00390360f42c4400824015a07084502c840c1c000301b1000d094014020040000d0410080d0250194020007240040d080c0c02032001c1210114108580041c0b020300900071044d040e50182e448507001c0d07441d40c44403000f2b001104a0341c03018a03501e41e004400b15034188010300145d0701512010890282a1040c0000c80b072005180307003604d400c545c11040c00902c01140d00f800315503081e1203503107000095040810091289034041619448001141c440882d0000080400c441c0111003240310901c2e4030a0540b00880840042c201c1410380540040d843d01e405000365400500500c00002d803d8003040c10804030200c0d52022a40c00e903c44d10003001140750103c1c006010f8100f0601c4a814000f040d6030180c807420000900041405910071440d00591003a4159071340e83c140481161204121043d515880c0e54003802000e603500c20b145494235455000f40040b1040b610400180b503d06440d1500000340300a0250403190301041c0c80409c6017401e520200154030850040da000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292964505 1250 292963255 292963273
    0x9090e0a150b0105030a0c0509100f1106090c130b0306010308030f0702030a0503070309170f040303120e0c060a0504050901180b030a0330090b06010906050f09010e040b03010e 77
    0x101020810780c8261021141c20a000c2000d16640a82525040700c0713500000700e04c84c020500103444600a00000ca6040140d41c040d243ca25644004c04640100554036145507a440d089620390302c0311002c40d10403881e40e03c110300c40c44560030030900b4a0090041000000340384400040000d0616400f07901c251000340e0044144074492240000f490b40208650005511f0640e8204010f0040d00001344030100b130559680014061100c204012560780c1d080c80c1c0415550302d0010049400c13600700e404150001941c480c84040714020b107200b04400c0d03e169100a0004c4041101048415400103a500042000038480040e132500d0303106265020b080310710403a83c2c001510b0000a01180d8140800c11700c02c0d403005c610b4201085d007050310305c0c1000c51044100a0a5800c0711003003159660600c0c510300b851890005280107004030b4050b12070058109aa541c0380c140e070348680031a03450203103200d001042d0400304003404031580103020700b40449001a0010a00341008000642190315580402480360004c1d050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292965755 1250 292964505 292964513
    0x20a03090b0a020601090911030607120b040b06030f09070e0c040306050604020a1d011103070b1006020604080d0b0a09090c090b010518040b0409080a090608070822020109090e0a 78
    0x40d100602014201075082c0348041c0030080d903a00044c801c06d1a8203564048100500c030050302c010f619550301804848103400c0144004000150540c61418800c4c5066440c20603403038a8080e010500d18010041419a00c51a4104410704405041c42c5500d11401c40300040300c04500c02214440c0e00030741c0f24143c43e00c6c0745040040c01e03904000d0001e0f2203a0b10400624402a400070006180c0c01961001790017849000c0005a540082101610b0320074800891164202310000b030300e041c0300c0d9900740aa28030b9a41d98600503030f6181c1041e0b030000e11005050001c1d943c0081e0b01ea0000d0740c010301c003c003000c800940e00c0851034100c0e40404000d5480640d41c12050084560078010101c28402c00e00c2d000b03140c0211242c0d82c90b40100c4c0040c019110b191201e0b04600c90343d5507900100129038205d486c0d15900c88111740c0207807052540388908408604101300290f4070701e0048645501c40c000d41c0d02c8c1c0e04210031149441400401d0150022030510400d60300c0410420803610950580030402c00080400c0015420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292967005 1250 292965755 292965767
    0x10509091e0a061401051c0602040513020403110a0506030c161202100c0206091207021810090c140405120f0102040609080705030307030e011214070f030e01200c0a12020a03 76
    0x142d800000c0038070134010000741e00c0b611405600c082074004410046405442d2071406403045510039940507a11103802140b002a0341e0052044a2041d00707400400340c13144050141d404858820654071803400d00000d0404401503005198101e25050360f8141100503540d14824441005001c100583c0f21589030a454010782c03042902114044c0010012841e001805a40d516020811141d00441c04075120085454041a00c5a58580d10041804034070f003401105504a860348a112103007800d05c68139580c460b0007070088180724401164820b181074105803d102982d000c0140440d841d100c0c1c0321600d10007040030310203030001d88469500d40d01050304e00101940341030403a400084c440d8004111482c0000c0d00400454030300002801c00030120103070100c0c0f46008101000440092020441c208407249600030071450301d003015601c040194030317000380d005422100020061051003402c1c5c4400b070080e6080d880a441144040d200f1144000010790341e224800c0c035010082d00241e48103001000815401075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292968255 1250 292967005 292967021
    0x2d0303050a0e160b0a09090603060b01090b03040f080a111005010f241103070c080a06180b151201060e07080f0903090103020f0d15140f030303010509091e0a06 70
    0x801400006140441c840c00000390f4855070f13420700f0b0300060980905000c0d00b00c000c010070507090b0810901d503032410000060101842c003280081da10f1503010800302040001d80380210b400500c4055001456943c0c1c840d103900070602c6005001031441e41905501c0208810000001e021102240c19490b0404051060407a030b00700d4400307004500c8440380b00c0c40e1000003070083e1b81424036142c00d00c0140400d0603401c40c8550b0f00301812200301000702040002c800600119071510a440c20400502c26800b000030039180101c00410303849402d00814444114040c0c2c02c3c0d4070100050600304102c104258203421580c065000a0702050716001f00300b10b0750b4208401580c020240c2c110002c007403819918180c0c9038400c030000b40b4145a1302180088079250000141d0f12100080f400800151502c5040b03501940041e00c5001c0c440081141070f03110b43c0c1040e42c589040310740c0c064015801c5034201400c0013500701008060903858451410800e2000b04c00c484410f581058080240002c00c0700b50a140040d50707040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292969505 1250 292968255 292968281
    0x302180402070f020a0b0a120c030e0a0b040b0606030903070215130f05150c15040c150203090301060603020c151b040e040b060301090c03030507050a0605090c19030f2d0303050a 78
    0x3486a06032080c0c010081415210f4912800203910200302011340042c001101030010398410f5007003800c00c00040b8004140118000c0c00c0381c10942d42d0c1c080c100417442c84111100310341e0750000e008110050800e039070500040902002114180410201c0d224030290488e405500544107403d01008142061882c0d00c0880016981d92460820081c12496076400000010607070340b00a01d0015044c0043c1402d0800030748810600c1400380203140400039602c1d08460b04c418442c0d4640940014160300a03c00c0b144400007200103020b661070b100d0410111454018200035090500920240e020038540e0b0040c809008150640d50442c1014246500c0110b0001c080c140244c2c900102070000c95003405100080b01c0d418980160385466511b40a400e0048400c03004104c01e0520301400110640814000b10764070041e64075601e80c030841004415002d0107440094104070038000d40e10080f44114150751100e43c020300c04241280d40e401c0780d902203102240c030140c000942d140e040c0246c00025001d401c00e58003070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292970755 1250 292969505 292969507
    0xa050103081207090308030a05010e06180a181421041a0d0e0f0c0f01020105040c05040e0f0304030b071205090d05130503070b03010e01060504060903030302180402070f020a0b 77
    0x11941c1c1c0c504148145000d03030450002140024034107034400c90049001e103911800d000d48a0400324031a101400302070055148100c1404001303009800c00340181150f01b00943c074010b00580b60034200c80024109004406400e180560105010804d410040b4281f658076000910950399810b9580e461000030a008502e42c250402080144140e0280003040102040b00b0181c1e4814280026000504084a0848070b80c003130070318442e816036000b09a148080b44250341440001034117100490072150b04517802481d210202d44280f24034105075000c50310a0794201c0488504080701c0c0216032668001e5481201c0a00044d4204900960301220039042003458000600c514204610843c4e2a0501001c44104202d008a45107480915a0301c3c18401044054240c86525882c0d98088106500c24052038402d40c213400000030316988240211021500940c0d070b140705903030031550100d010303611101e03480d2032030141001420b1a0b503a49100400c002071140511007101d01483c8140126036400c5c1d44400042c2c84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292972005 1250 292970755 292970759
    0x80c071a0319020a09121407060f05030f090c0a030813050f0d0b040221010e1608190f1e02040c02031c0b150c061f05150a020705061306080a0501 64
    0x5080611402030a074044400f40e1101c2615034125441845030b0702c0303810030307101a44001d0280008110350a81d0f2590200903640c60035280d01094590b1101d4007081c400003030040000942080b8048a800e0700301c0d00900644a2a022800001c0c080640541040e00d05c40400136540d8800c20b03d1030324440003000e056854540100d0302c0400110b61203200c1c00094010b50100000904654440d18000c1900500c1850400d505040c0815540203160f88141b40c50b1700e210749100781602c0704541e24010200c03140c00004089031408003a00b280102c00450302110100f244041c04000150b2100901c0c100d602e8800140003188200d004000644800c0d0700f1500640d00200712030140002c810340c445001d080342840c0842d003c02c003074000c03e1004404183c0041c10100c04903142e411060041b4246014440755007425030b5152006143c040005110302c510f65001b0400310700101c681060328040d00320080180160381d001a5100041003180d40112080713104841c00f000c05201e5179400c004840d4029403840410080c0d0341c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292973255 1250 292972005 292972021
    0x207080c0a03170306012a0203060f040c180b03010f0c02160e0109090f0c03060b1509030a1e06090327080c0415090612020a1202010f0509010903080c071a03 69
    0x2400c036010400803020300100003070a590141510385140304481c051004c4006800c00c7d5032107202d4852034201e209004040114807803a14060340c40d0301568001c001d0045403440d107a07080207401c032004c007494541900e555030f104060380c0038420030b085074140d8030f8045006000d602c4001d05010745150000318400013020240220f85451101e1410b43c5c03000c0100050320801414802c441074510a001041c108e880c05c0048201b1103517801100105209481c1e030036000c1410344910038580201c456142d09a44108014004140035810500d00b10a4421118000200c2d94452800741c03440b9003026400704101c14002550400e0300e00401c2101c070ba000c0c0722805103905116000f901c0710000449148182e4603100c03000c03070200450319400d00611000608201055652401042d0114540d0f800e80c411000300d000010304d2444217039004c4020760b0582d1354482c0580141c80540361074201d625540d042165240020000404200c02081020b02c00001045080c2c0342c071000003031889801c5d1016112400900c14840c00c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292974505 1250 292973255 292973273
    0x3080108010c0e19050604091407021c0807050903010903030504020f01030b0f1201141503010b010504060c14030c0f0a0b010501020f300a03240f0504050a0f0c0207080c0a03 76
    0x420f0b04039a60040b116140150403a080415003100758003050000b40001c0e1b195056020200c403180d500b44105841e5510340c1d050ba1100301030303104500d01000180c04e00043c00d101c1e1240320b43c0081c1d00e041080c140342004020a007141e141230422404207a1f58030170310080d450b150782c05510150003440c0030301107c0300e404041403c0841d02d0604074001c400030160071482c039100390007111504000818030076007458180c065480308911100401d01a518182d443c00b84c55100d0401c803829503185031201d910b48001640e840d407050022801d1100c0e103000034407802c15000420700400d0303088100707a0000c04d10f000090809400d003640682c0b200f41035510000403011031100102d401c170448032a04910030702c40c480d642c13402000c20001c0030900c00380a60025a8101403509940078460300070f8ac1c081030684001c0b034056030003c0500c8500502ea00000304400c200010302e81500701d564449508000401c04c0f0208001c1c0b20300782e5071010181401b5810906003070098003030411107918030b0f81d41150300b4098907245403161002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292975755 1250 292974505 292974527
    0xb040302070f080d110f24060604060f0806040b04020c0d09241d09070527031b06070503040605030103141b2803030f1803081204020307031e03080108010c 68
    0x10300c8a00b100c109410141800940002d22500c070a83e61301500110a101c1003c622081039011f03200c0c51400328145007084410341c2d00340c40c802c0d1261903c55280b144161000c080080c10b996200340c0781c0d01668000d407502d00161050034400e0008003400d8a8107031700503202d0340d401c2d00042100690141c041c3c8022105040c0340102d15500d040250306284c2440001580c448100803054002200c0014004100c1d441001403034100c2d010219001c01c0b1517203154620744100310345c45aaa041d0712aa4840c6201808880000c0c00b1090081c0b803d0b03d84a81591820f0450f0845d41c0030801050004c00108103000440410b0f0f9114000c0201030004464034804141c4182c00040e88240a0706954020441c2060300c0381d500303120740c0b600c904d00e24152541d07440d000b881000d0880c501d400191140d40d0151226101c00c4039201580d038060025810140e005040d50040200104141d91501c22110008082a400c031911007000721100b42049400c00e050034082c6c04004d041e806203003240c1c5000d07010b4238120381c40b0341c21840c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292977005 1250 292975755 292975757
    0x5030118020607080f070b0115180e09010f110301060225120c120b04110d08030606130f030c09050c03040b06040b04020d15030b0c2b09060204030b040302070f080d 72
    0x91550301d1030805100710300648800500b0303100e00040b0311052111f0304504504a540f055400080c0c0611510110358203940c0205810810b2641002400030508244205611075000342c00040ca00400080030010381d10040c445c0c03118010300200510540d42d0500c00300703114020100c1c61810f0000c0c0005100e920010502c510601e80101c0f0b000f90b002c0000b1800060010305902004401049640c10b101200c0c07082a50200e81181a400344d440b2141820041c00c400550011003503810760303807100107000455100c080c0b00780550030350001c01300d18001e000f90640003850043c034000502d00d0604148504960340500791407120001801000001090500078691001d4240ca0200f4125003c4001c0f402034006e0010f070f0340a032070400c2460001c3ea10f22009d45c0c42102d002d0144164161a2029041218420300601110100b00a2a426962850080302e0300c0c003001c0c82907001035001d0968507480100d0b005500100c403203103036403000c1c03005040e8100020000351065404210090340f418407410394684906000300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292978255 1250 292977005 292977007
    0xc0801080c0409121103041a120f09070603180c06020715020c0f040c021c031a1807110a020a03080c1605031c0e1e010912030813021903080a0306050301180206 70
    0x202c0b9030321040c01a14010042305510120300c8002450911a903007280c203442000102c1d250020b84191200c4030018040e802c0100582545410004224007070050a80448000320304c0b081ea13100003a13040444100107091941c060f00105041400c001401d54508482204650250400c20100d40ea0742e41c90300c005c0311045900091b4403ca20f08164145155094212240a94020109691a05070704590b903d02060b204501307055094004000119584822191940020500107818240281121070500e800c100c01c0703544140b02a0f00023440404140c1080b6001c02002c01d4120200104100b00e02042c139540e05250005410075020a80c0c3e42c000d4a0704944e4240201e0b030100d949809856950480c500242051081000041c40d41e545680c0d5403c0b068000b0700b40c04000101c424001c095600c00c0380d49075994180648079101f03c0d06034085005001d0713a00801c101c504a410a410b0701c1c480004500c54810562204201c03000901200d4980c1d000c94000e034105401f0b100d4100c503442481c8142d940c101d45071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292979505 1250 292978255 292978277
    0xb0a05071b1226090f0f0609030901140c01060b07290403030c05161109130803010e0717090c040c1103040e070507050d0c0c05151c0f0c0801080c040912 67
    0x8884042c18502c141a100000f200780300c1281004511401c83c0c401d607104959030301c0c0d440c0c55103903921401144d01001d070b41c0042c040080150302c43c82c826801403101c18015418600c1c40041282140c0b00ea50103a8000c01000030444100104603099600b45000500c0385641a44601c483c15400381000b0300c003c0400d80e03501c0503144554060740c2950b01e0700941585510308140107141c0240c19080760310b800e601c20111000020480c040c2c1e50700d0f4065085d4401d64040c21a441c080d880540c40c50301030070000520175003000b283c20b0115040300440c4a0310180c00103000c000007002c01e00003210706540302801004050f210080d60075400000b2a0112014801d05208507542d20500310340c82e01139030100401501444030780009040c0e004c2d0440800341e00070321031414010766420030004000d40350a00480400c03002e00801c3c6421441d03d19038403010181003404207130b40c15564201e00c2120300c1c6625590200300044010b01070403804111030342c0c250030156001c0205411030380382e41b460340200e5680c110801c4030610403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292980755 1250 292979505 292979537
    0x3080604020d11030603101b030c30050906010503120d0e15040c090207120507020f0a0801020c06010b07031b03090e0f0604051609050105160b0a05071b12 68
    0x484000c2120501c0c2006018840301c124500742c1e000b560132a111f403140346640302000621f07214071982c5110580c40f15409016605060380038040a0907020140094060301c450100b00007040c00045042042e031a00c0c00311844076031102203d0010704000c0c180e60003030006100da610009050340d020303030300c81465135280c42c80b68402d10083d0101a030130401c0c60082c13800d50201544441c3d40315020b148100009550340361100c001c08101d001d10700007e041240301920b64009280990010b00e0403900203001c07003041c0300f060408201400d60a0340701d81d502da940000c6d07408581d42d09011250140011100c200d1402c401510000c2000100345901c900b041c41c00702c1c20b60708041c000c0960b1801032020881c07035000352030715185034414175008807421801141001d0014034038801d00001014200ca10f0380380c000960381401e004543c260421800310604000e03004060001c11160302215108584441010445d494401c800806107244c04030000031260381030713a05c4000110891b4003645640c440b03103855402e003101303190 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292982005 1250 292980755 292980757
    0x90402160602120708090a031b060b09040c14010c0c03020f0102150c070c0b1201170106030f060203040c1a1c1d0c010e01020d050412140304081f0c0c0308060402 71
    0x10005001c0c510004443d0f008004000105104460036202c0c1e00c095654138800a0311601c00c00300041c001806911045d08217001108041c0405014803c00200d00b960000031a40a002c103880503542e142d130302c0504000d641c01c0601f00143c1500d082c07074103440307480c11681e91101135005404003d108001070003d0760342d103901c00c0140a403580340f500000e0007a414031440000c856402050141c0b0403071010400031a07100c00d040d003100d80c1440c648500301d40603840c00b44d0b80b4010400c2c3e0170741c12006540307424001001c14683c0012081050041c1401a0345c2d05007441c101c0c80e464900e6100c5810711403105000362100540303c050b16002d01182c01d41641404c24420302c80c005210b2201100907150252242000419000030800c4507080c00382c9840800503c45001640c0c2c403104a0320380400500e0410051021524524400c1400c6204180c0300106011607014242550895040703540c280e4031044800004403c4072180e03110250500c00704102203464501c0c0102803220a400260600200602144440c0c490758 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292983255 1250 292982005 292982047
    0x103080d110301140a0617270a03030501150c021f021e0109050d1d15070b1e01090902060702010804020a0902030106030e060f09071512050114130908090402 69
    0x14181960700d40c1c692200c840d40d01310b40c04c04d05001d84003000c0041034860149420030740032001700c02400d5550382c070f0313412580c2090410080e50309407010701c04425890010804c00c56040500c2a100410250704090702c0303480c004080c1c0700f5001042940031890000d40c4613060042003038180103200002d201c0c90300300b0030fa1400c0c61a80606191340140a10744040c0c0f50194803c1d0607a6200f00241c400d0905c0c2207204880c02000e41152030381c5101e05441d03450040c508031800000c00b10700c05403014104140c0d92905265140200c0f8862241e121055003401d000000c2c0200038050406201e041054500c0c80d00491510700440100a05224030240468150f40c0e5000da071700d00800114005542e25a10740310000d000d8280c0316043d050603c5144003088180b81c14106540c811f251240041100c5845e01d00210001c1126400b03400501040300000c01e40e845041c054a07003c1c000c60158000011000401e01c0307105d4010b0032184020301d144c810302d400002e4491048815110303080b900540c44d108001001039038503c5907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292984505 1250 292983255 292983281
    0x11d0c040516111c0e01120b06190318060b100809030403300909110903060610120f200703080609061c050120040b07080a0507051b10020d080103080d 66
    0x4504484130003580000203015401082e603e085003d010b000114050b60942008258800c80a02c003182c0340f420b039240e40083d100404c1c600440c0e80b071843d422103540342d20100030540e201920b8103107070401c0303061800090421255600d40f915031443c10140c0d1607143c0c025400010212911001c4a001204041d11615011742d400b8245d98245c0ba0307d101701604020300752141910a5060020403240c80341d11005843c45080050040e05481d81c9080070003078111001c2c845031050190240040f15004031038132034080002a142d400103241c01d84031004400b0380007110b00e4488520010869040020303802103105400c00c2050714810050344809000034105a42d072111030b914418047e0400050000541290182c0c441e18640d10401c600c00003003c81d0988030f140070300c04a681c020015540003415540080980b880c007486d00074185041c03951000d040c40201c80c440410800c41d03900e0003116103405101d80d540410f143c0010305070450900760140a4400520024000d01804140c10205107500d42004000c0184 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292985611 1106 292984505 292984543
    0xc150f1a132304050705011706030a0b060a18051906060c030c02011205130302100204060c11030708030f0a120501030c050409050f011d0c04051611 65
    0x282c0540e015411254503144100c0c40240b452034021481070016040301490517000400d81410407101e60b00e21314202d41880415500028181000d43c0c0c4a2410140c5582d04400100140e2040e407090340c1119104013942007800c09540024410741d50584500310a0b1054038441d81103c10a0050340c000c210300300c3c8001d010a00030034905e9902413051400e0000030300000101001c0d207000341c4506011042600501c4105a010b020002e500214800c0442c00c1918040e40100380c2100010054807d4034544142d0049442c184282c101819030701040781d640d81c0c8640d20300a002e80c4052540000036418615100704606180980303812240c101481c414441c0c00c01013000001c10183c1e000300c90a05c201c51118070120020301807c1c109035000300341818482c401c60141d50030305401c104450700c15440c20041001a4074006140c01845165261012103030800a0402d4502019030803c8006040 = true := by decide +kernel

theorem cover : BRFrame.Cov 292805755 292985611 := by
  have h0 := BRFrame.cov_init 292805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292805755 ≤ n) (h2 : n < 292985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
