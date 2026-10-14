-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1867
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:57:45.27451+00:00
-- url     : https://prove2.me/submissions/2dddcc91-4053-470d-9612-bdad1ce57c02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335611510 ≤ n < 335791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335612760 1250 335611510 335611541
    0x21605061503160311010e0303040b031005011b02090c0c010e0109140706091401030b0f030d080a06150212160c08061603230a060f14031b280b040603 66
    0x142d030300a04008420f10680000f40c80039912090702040c5605c5000c2d010b00c0214090300340c1c0e003020360761046e8082d00d40041d0350f030054110303105105200a50303000101c10f0038110042a00c1c0c9645440360049040070101030008001d804c0b000500682c010003d4014017031000c0884020448080d641c24807130715842203401c41500d40d0281920016102e4400d400c2c010a8480c95004c5151000003c2c0043d402800701e480102d401035542c0d03070f4440c13035035405100001e42054541c642c2900781c40d00c504240d0803100c0c0d80e08414074680c1a00320641499900085601d441e644500c0c541e40e5580e0b11006049054801120007407080c990703c5d901041000c2c01050803401540b111031500740144074840700350160b41405010100408140a0f8540001a0303041120b07040003405600080c59500e07000b1280584400e500060a84441d0018141d020f0904120000f980c803066032000c91456a04000594420744000140c140c04171000c0c040c00a0140e1200100c1c014290000c0c40c076510b0359118000b801421141d900d24a0070f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335614010 1250 335612760 335612773
    0x20405090903040501021f09150b100f020a081b1207030813020105091011060c04080f0a0c051014030a050a0e0705100f05090d0c052809021605061503 66
    0x19030600000f0794080d224160080d0543c05d02c51101595504a04480d24804584a06681c0e001c0350030342c1a21511400c540c00f001c0b443c540b180c3c041c031103887c02c10311100040241c0000281d007803030b40c0401d01a43c1c0d07036071041501c0da4900020068101d1a0700d0304408c070300d00780031b003120303005444c41404014076203a071190725004455501c0c150704050483d010079003e804280c003000321050783d01c1d1100480c03010300118141503800041001c80d56240c13103000c0b95440a4800700203401d0101c01010424003085e54450310051590b000c85075a07501e14024113110711405030f00e005c042c9031955406858000840507000027190344900d85900050003030b00e01901c0000007a4a0b000071814140f801255441c1950f001a140038804684050103e43c0c82c19240e000504200c000e0003540c40503511300c111524403602561031360304460700f02400c04c200000110722018400001c003e2340884810100b10110480f000030b030006841c2e2102688007d444006904018005c0c040c4008004030248442240a1101003d0f01144d14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335615260 1250 335614010 335614021
    0x915010b0403050705040b040e0607022103010f0b0a0c060c2a050c010806010917010c17070e1306260c01030209030c09040302070b19030c0311120a0209030f0102040509 74
    0x403144103a000241035600070303030030030b10035401e1940011021060203800000c42c290710b8040d10781400c1e001d813114801a00801c18514480c5c0681041c1701c0307400001c0f400385241d94581013209100b203c85101e030a41054002c038061440030702902907050070300d8021205000500302c0d140c0090416a5446c800e01034103d6514000f0120340460010b440c429621500604034154008015600d00034000c3c1528108000f014002c0340c00d0449529014603800341070004107549025000162035850780400c11103621401008100b81168851002006000305607046803c00040340003041c050070950b08100e80c0210702d590001400100d1030044150022500c3c244c0c1c0c401214840118203a2180b01c4c08558182c1c40003641c16424904481000d800074031a00407103410355a0355152107800c0d0000c4da0085043d585010740c000c1c0c03958060143d4103072403041c0d01e02084242c803c0e0383e60365030300d000e0b140031020041c681c840041c3c0040c00d20380c121003100704001d00315a134a8800d20095800f0354068000c650180d000c0d9004240c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335616510 1250 335615260 335615279
    0xb07050d0f020303060d02030c03010c0309110102060402010504090f0f0c0203091005090d170c0a030512070810090c02011d030c010609110702060d09020d0c081c0503070e0a0e091501 80
    0x8181c4910350140d8030b140c40b0781d170810185000c03200c1c0c280e906004039618004659824800c2e0840580b00b5103001c10b0081543c14078a0001904203075050554211400f0040140c0c0c1c4007040313905840003030000259080b510b600c110000c15020910120052401100c464a243c0000c042c1038014402c868019041c0c4001000b214203005a00410b5004102064074800080d910321700d01410140403030009003030a0340c00e44428680b510380207040c1c02044000405980c1e450250000d03550203002410f08030707040e040174402d0b48028034061140271070460341d40c00c104031580c0c401c0d00103d03201e901c4c0c040070a80000c604807405449512003400c10403690310346400001c0e51182d9004014101c22040076050920a050302803010541c000043d8a601a80e105d010f000107030303640801c580205010304014445c2605006440c0d00d003100308440d203920110030010740a4a40c0c0c1c4281201d6203d041464903045500c62603001c140714000070b030482103151424008101121400041e03988910b03590f400c8614103a6039860548 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335617760 1250 335616510 335616527
    0x90c030221070b070218040f0516050d1514040c080106060e031002032802090a090e0c19050315160c0308060603040807050a05010507260f04020103150b07050d 70
    0x16642e007200c0c030108580892840a0011680042c1140c1240000e2502e104655441190220781c0195105200018400b040150381c44021243e0108481d2030300348070005503c25600c00700141200204142c4140b51006904031108401001451001d1b43c01d11345071007100040c05029000c83c035031a0020005d403a81c89088194002940500544114102c00140001070b42c0000e00b40e90180054138119080600248030303104039800402001600c55142104009900000303600c100d0f8600c2c20200304040b24030010500040a283c02c40300c11545000c2c62800f028440f0459100680c180200e10310032440f80401c1c22418400e5007170650001044600003019141481c2901014001a6070b040004d07030182070110013990068081c114044c10440e9641e591880d00240000c00c40304c1e41d45490600042d01d8000c00c4481050881041d180c602d0401050a41e82c40c3c4402010701010141c008045010340e406030340000490110b080c05203071102d85642c1c1c0014a58441d04085403030388120003840010714400c8055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335619010 1250 335617760 335617819
    0x7020c0118030221011812020c010f05091e030a050604020f10020d03020c010605220c0e0f0108061309051e0d080123100914030a020a03031d04090c0302 67
    0x14240007419200f00c0c40c1902d140131010103903603a010b049200038100d000c10301085101e801c28103600c101003040207003400c03030045c3e545040c007180301824061981c2007019140405805e8031403800c4581c1d090b0101c1041054644602c1e007600070403107094184480811054030880c000d483e8500c2e0204d2010611801291030908600141c10603115203950381e01c20780040c0003010701c044c00410840d8031800000c0c14010b8501c038443e06220164410151001140a0a660381c032050402072800346140001c21200041e9000310b6041120340400140c0c0360f6614a0f03002c030b070103001200800c0941c9582c5000380d41e440211001440d0040c0c0c40b10341c0ca40c01600086c080b120b030610f40d524051903901e0316940050401c901c1c0c440d00101030001c203106c0e40e1501c40c05040d40c48010241d80340100760b85000207001015685214641c041c0c1c108111100c003507203072282c6540890fa418600003580d5074a036202c01407003c0d112010300d98042d00700040e11042c82072040d42141500c0c0210b4005581101c1541031040210302d4101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335620260 1250 335619010 335619019
    0x51801050615091c05030d02030106030518070b1303150903140f070b042907110a05060606090105040e010f0312020d080c0f041a0304110a120b060604090507020c01180302 75
    0x5004182c20800d0f007103404c80880e003540a103203040d01c0d03640740d045801140b1082c1c1b106d035000c40104003c079803500070507404c81c240302000c80020401100150b10344965020711251868000707a42201d1000c51003200d0000c60300b024a05e2421031541852901802038104240d000420021030079031083c030314408807000032045642841c6044803540d50705080e400d00030b205440501803840079445c0448a91001410000b03055a03881091a0124015142e501c44424010345036110280240000e074000038581e410000440e0f22a0b180c01c00c040040340c0314800c0c2c0e0481e07000c641043c0c0000960391144136080c000d40e407081981c1090004c00b030404a039102c8035500a42c0002c1c242602066411410344000c02840400d601c00310b28042d110b01c41c003140e40340042c086c410301140000412081c0710300c04592998114040305c03010f441d51701e0845024481001001c0107007141200384042440b45c0d507000201d400070700d10f020381031116140015020f522001e49600140c041100005113050b9140001080b10a4070360041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335621510 1250 335620260 335620267
    0x1d07050403150615090305012f160f06020c01051503061503010b0a030b0f010b19050a3e031c232a0306090402011b06051801050615 58
    0x84070402030420191440c800c040d40c600300816002d103040c0c6001300c02d00480d101e0031002440c500c3e020b82107030000c03100000d0400c0300e0483c1c1c03404420b9203c403a03045c1d104101c44140c0c07101489114101d1070480e910300101500c0302150460100b011903000341052440312070081040d580c55080700b00d03901c0425200a5070503005000040c01d401700110100700d44040160001131006641c1b00440c05052441e0400d48805441004004c20802480718660150079080c00aa081441203481d00c0074451108001d10103004012920b015514030942c600c41c0350510040070000e1140c80c0c1400c032100c0c0c001407617804090503c4030715a00c2119200204031001c0450b814a02440b26115004150041600c0c281644c002800300341c0c88240c4180c0030810301d025803c1030180b40b03000c001c40340f030b00c5440d6140c201d04243c12807014000c12030103548614102d81c2c00354080c00c16040c100360328051006c5d030303030546600104594903250a003d00112014088006620704400030403040e00c0c2c20342000301b00080c00007000d18500d803c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335622760 1250 335621510 335621513
    0x3031306150b0f071a0c0c010e0f0d08071b1212090308060d140303040803180c01140c0307120e0a080714150403050118060f150306200f041d07050403 66
    0x1000181e01525450030741d07241c41015040307243d01c1a10407411b071070340c04100011505000c0c8a040c0448500c10001e050114400903859103919814004600b40129500041c001c80c1c040c4109c0780d04000190f8505c1480045868819005460401034400041004103081c40905040c4604240e5a425440380443c0da40d0300001c00c40c1c4504030800c201c078000d00d500b1945007440410070140d4011480f175222592280341014070041040040c4509440b2640403035000310b0581d8005080342d048961241459a03039014201c440ba16510400b00010011000786508510460f0310955440344400e088420324810f07036441d2111581c46240740a183c0440c1c021403816005850040d265002492010303400c2820b05030349071902d07801c459891000c2c0d0441c6170f4540b629800c0002d60f10506d001c0203112002000f00b07600320b5442001c0b47e130702800002e22840c0d880c0303181041c201c01d0803483e4002da1150f400303003940c500e540c141403c0683c000b4401c1d580050000d5106c003803c01088000603206410a59810b400e061a6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335624010 1250 335622760 335622787
    0x330105030d020604060e0a02030a0503032d070f051b01050f0714030a0203090c0d030c2f0121090305090306010602011e0c0302070c03030329130b0a0803031306150b 72
    0x140600d410040c03191f040d40c3c0c0d005880c1441000d0146005a01a5449190201600310506281504501c2000e100742c200198040100c01484d0403140c07d2901e002402c60310b01c8265040c1c0703e20b4410b815a01000380350044652415003040e8419150a8280340b00740e228a80f023a1000626003403a01e21329107050000034421403059024691004c04401110580302c0c0c8840400c159422415007540062104802003090084c21101900003a000080807698450410721030880d11203184c10301d0b4100940b441200b81c0c0840c05882d4585003d001e40f10800c807541c41407501030b02d2684085d10141c0a4040c0030700018101e030041c071900e03c694180580c0f10118442c07801c0340200503c0031040d00018164284840300116075005280006144a5240002e0080148649c090342c0d032000703090369010304a032002100868961a44100c1d20701611180803c2100300d03080000e840c100142c10009180c4804010000700c600d4011012601500a59003008102041c40c4104940c0016004e5480c41607410446048202c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335625260 1250 335624010 335624021
    0xc09030303111207020f0d09061d040f11040503010e0a11090705040f06120e0c010f0c060605120a031d0109050d05010b090c0c1002250203330105030d02060406 70
    0x142c901d6018030b4a5811610261403000545544005034460390040480031010441d40d5464506030030b1012045160030b81c000c1000c007010120f4582003100c1402002d0340d0315190410342072401421428000c416070801c100b0b003d44c015200e0240704c0e6003000c8030300c4c00c209000324241d645550004004001c21450b8821701c2041d01e009070500301042000c0200094542d030b040c44d448080d0510b07548248420038140055005d031080841146800e40000c41c000e2126a082030f005d40b034010300380c00c00c400b036401c842c280170000749004e9000e9900065240a9004500700c0424544540b0f4400e444214440315281e1403802508100e03408c0350301042d111071091000c0d24010044001c5d41e03220700b0020441099407000714005020039941700801010104d82c14102000503c031030380d4101c84510085060000030348a482d0580d02c0511186203040c031450310002036440c01d04c4a071024001da1403040360000c04000401f400748000032400700035000030b80d002059910700030410780141c03c5550b0041400f0703200e07611400300a05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335626510 1250 335625260 335625281
    0x5010e060126040b01030b0a0e0706110a05070b0406031401030c0b16050f0d0807020c030604060207020103090b040807110607021818120c070503060103030c06020705010f0603060b12010c09030303 86
    0x41d40d0382d4503051103900d0076202600c01c070720400e00c41400d94954a071004032250090038003ca81c0e403e200060100540014410040341e181e4a00304510b86001c002083c00c10700390200151950040c1030b07011651000c01c100a100715001594208040311407018003042c286401e00000f44050a200b9013080500100e0300500440300620b448d448074801c05070344191030003041040b45022078000c0c001d00343ea19600040d215501c20b0290016003003024042000949030000100003c10056011841600b964401d6004241655000105200c5411310b03050524580d084010304840980d040100419141054030660701541d602a01155030204142c0da220b00050340280420107a0040090f2298001c804000c2100311101442c0440e65500c00d00080500784103054001c42d000303034416401000040d60140200150b10342040c1300580322400340c03070030b140904040910801c2c114189000881444600d81c4203a030024001c40c0c04010310f40034940c80c982a6480c0d01c0040012401801023000440e020350003031107034070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335627760 1250 335626510 335626547
    0x206040b22060c0210021c05070602190809101a010c170d090c0503070312050307021510060806040603020a18020f0a0507051605060403030e0d0c140f010305010e0601 73
    0x4008800c1100807008080c0d21a00024031208881c0e0203500303005d10030030156141c500c040c1511191500b440030413000030179a924100400001c0400500c405a41034a12320071080044240885030300000501591041e102c001842c0541c5088601d42c42ca14424464616624583c009040d6400801510004413400701980e00791001c0c1d4003400802050001003482032850f0800090111007400d03d0340300b044083d00f2050003607124003800e20203e5001038000030185610701d8680d540c1d41da1031200728180144400d611102528032004e114110303041403580d000b69802ca41d1543c0c0d0382c4c0d8811302000b040d604a4480650040311480041c03080880310052046007208440300036280004c2c0700902c040d07950104070f281c00041c05c0131a5040401005002d103018064905c4888480300303040c1000983c2c1c1e0720a50cc0001c090022800c00200710351030381c4542d0121143c1003400303100702036a078884140c2c0d4120000706a0b80706680d6041d102084e0344c0a8490035068401c48500751400780d4070140192081040c208545c140ca = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335629010 1250 335627760 335627797
    0x10f0302070b0c0a031d030d11040806250806130b0303220510091518150908060115020a0f02010509120c04060905040308060114040816150c0206040b 66
    0xc60700e0241603d01030103040c8034840d40e0700c401500040807241509401d40c607a4140200700d000456000084d80d091031340615000401140c1c80880303548070301c2543e0000b10180215000c02c0b02241c409070443c034040c181d115401c0740c05040810100d60000044401d01d46c8001e80401881100c401c0b40e100c0700340c910016003164a4207942000d135000d0031030020180100d108482506009a040c030b20748019000346941090305005062030003020007811910800c000300074051241022008030785000200611280142611302507030075000604143e0580a0440079202e060000555820000252422125907901800e2800415950400000c04112041c1e0401009020021080d502c0070181208014104004c0c200c3c2a11082408156070b61680014600707440c1504010100e6000b503040f941c131802c2441c0c40031080700c500c1441d4034103010399000038185108000102402002d510140826514400c8000c251a14200340c01c603400c2a030828000e410003c107120030032446600070f000d0500039000c004407411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335630260 1250 335629010 335629013
    0x170706080a020c1b131422050a140102040306060617010608060d0206030901060e010b0c010c08010b03040b06180703020c070b09150f04050310020924040510030e060403110d1d010f030207 82
    0x2e8803800c41b01d03a10058181410701c00a444040e1200d0441000448483c075425007076202c00303031610b00d403e502414200c50841400110803080d41160040c0d50b21540421181d92240001460950704895520180c0141d00000c141d2a0246440da031042e81c004050b0586105140d00b8000300b40c0029005100641d20b4440114500082c18142c0c4d018003030341e4150a8441004c412880d003980c844001c80c6045c400328000610010301c05604483d80700347c000c0515405601e455010503114483c50f030084480c100c03c1802d0151180e4180c004104280f2200122100c168940726035190501c9000f003d0380e4410000c0380204c2e03024030a00042c00e01c241030594141d0415030b540300428200f8608002191403142d0020b00c041e41441e002d40c0c4162085040305001d06940d862488a94103480b030340c02614407401e0fa041c0c6540000f03200350044644900050142c4035541440c0c0b138080c08050410b0306031009402651800d44107544602c40f507014503040102180d100ea51100019034100400304074107001c16070200328400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335631510 1250 335630260 335630299
    0x1080f06370b03040c06030c0e1e0d0c0503011104050f04180f06060611161703071a041406040c0905100302040c210204080c1306170706080a020c1b 65
    0x100801d102a43d581e00e401e140209262405030050b0090600d02160080440e62000c14429002000c0e5103800d51074031188040c12042d900e6124450b0b0040750103e20a041103049000700c41182e5041e4000c0c0601440c1c2801d45000d4050f80c014160010880c0052002921b415004404400000c1460f40d2500b400e0307850b050344283c02000151400e0b511074104100441d4060281c5a8a2048a0142004113a84900740000742d0840c8070300080c43c1c0c0d08503050b01021105004842031594001d1a41010368110000c450085100700d40c00c0d12104014240c01ca0500c6004c298070b80f00d00e44c031001c5819a02c1c10608114010b090140900a0258801c14040010f8403544240720342a0401d4a0300592a042903110100450b01414a085880c0c0140b108100c481da0008105074841404c4580c45030000c0a0300c000c400407e5a0ba0181c01134002c0115064001400400c1078000e44070541d441060703559645825506912450110000c568000314144031109100c4c0d01c5568641c04c010318402084c8501d0382d100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335632760 1250 335631510 335631619
    0x40c05030a0b04110f012c120a110609090a020706020d0507020f0706090b0403170c01021207080709030b01030b0405010914010b0a052e09080709060501080f06 70
    0x44425900c2e040a0206210108298107940302c01180d0162110a00b000020900e50301c1c44403c0852880c04001d89041c03c60340304c21004801d2007d0305480032141094200d0381d8520750030505591100e00c501030010241806401c85000720b02c05030070082d5036110075034060003d52000c001a14940d07402d201c04a0081d086004440c0914416401080c180c801203415034140040c2d80e000c002840004d0b0410099400170f1000c0e42c088a07041164480c50640309002c0c00300c14441d000000009520005402c01c041d09054043d0380111310700d80e00c0c000b203075036003031000d850941c81c0340005072210700f003503004000140040c812140d0052040c4000301e2110700c2c2c0c1e914400300d02d01141c503055481e511402c250801f42009254000284021585d42c02c0304444844544c1000c0150501110b200120400d080301d040d00490260005124982c01c64001d1580c41200c480200140e000c4c0700e000a44103004180c0090503049043c1c0103001c000e00400004a64a081d1080320400c2c000e00f400501e0b008006603420b90080d1000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335634010 1250 335632760 335632763
    0xc030117121b010c032a030e060c0a090602010506010504030b0c090a0305030301050f04020310140a12030206071b02010207060f030b2101050903031005100306030605091c05090f040203040c05030a 86
    0x118000c0d0b0000403203240c01d441c510000082010314241040b811854106104050385820078415180900c84107000c8010301051a00840c0612a00e824041d054a00348010008459190703105c40490ba00c5110490903503000f80c40c8240010f0043c00103002103610150a5074100301d2280d8540e24040a00000c1024404168002d4906410100040041c0e003001030003100402d004450462a5190080700c00030140c0e02030003040410552980040c034140c841181100c040d0145101c0801e400c1e09a16000303560f510102c5030240010841c03420442d40050204401081d1a4160090420541018822030782c02c141290000304240c2c40d000700740c40c2c1c0d0b12000001a20002b0841c100700d40340e0180c0d0500c2d42914400380620f10703154810402c01400c4551080180b0554200303da05842d80d02542808501a05072908003903c1940303014244442130030f0001d000240d035601000626810401c80b14280d84174041c001c03c03103402080c0d0010448075031910380d004603030062281802450b019100c00c0800d01e0588981030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335635260 1250 335634010 335634037
    0x509130b0a0e0a061b05070c0b03070311070c0503150103030c110402040b070c1a120a09060207060f0b0109050924121c08010b130603090c1e05090c030c03011712 71
    0x700802101152006082c415010b040c000d1030070071a41c8d00c40381c1c0904e107885520002c15012021400541c03103038120043d10840b52007159140c0110741006210740301c480c07040c6407007441000070304015441c200c5011030403640c00d51299500c2e1a4152100200381e0701418000354003580c00c0202041e106030308070103481c034103002d6010305109a00340720791850390907407104216081250074401d50090944007400b02b98004c3c8200da010441c0f0900b403408801070300444400602c11070038850104040316043e80903007402c6000346e8860f40482d84d11800d0000d00c2c94192050101a00c42d200b03040d014240020f41c4c01101380002d4458605042145115410010b9080d01c05071a80210f4445403041c551054126002d030a450b0380d0240741020044100111207003900c0f800c0141071300c410f050401c0c040780d15416001424014a0360b800c1c45c1444801041c2d900c441e0003814816680c4401040b00d0720000c0c2c003034910030042d24200a2541c0d08210451403081800d00c000e800301d00c034a21658602000040240c01244c41c00c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335636510 1250 335635260 335635271
    0x50c0f031302150403150207020a050112020d0203011508060d02031905030702030102031f06050c0601060f0c1203050a14010510110a14010506040e0c0d02040f02131d010509130b0a0e0a06 82
    0x19286400300c0c21100311803101401404443c0c05650741c80c80e14811502f0900302070304000000441d503006400b41c41c100f000d1007031012000081710100c44404a030841032995550a0b03c1d07944104002e45440c8208019415030300160701340c0d203024010407550070a030f8040c00c102c2c0d041c0443e0b40d00090a9a2040343d030140145850580180400145950f080141056080c01400c00883c094240d68800052296008001003092015221400b4003401c01e603850300180d80c001c002004c404040e000e080c056039030317490b00340ca04500c40d02c0461114040303038140c0304010000140c984c82494216440c40304404001e42d00e003d051001400114414800c80d65100707010000708092034584100012101815180d296540001e2618441070380c6000e03e04070081d40c1100c0010765501c5c011604c100034010340c50a440440d9103034034041641c0d69640d101c2d06882402900c0310400381e0720303202400000c02069840c1d01e50b503849079000400240200803841d43c804d44c51800003c11142400c84e561915203c07240039540b10790f03605c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335637760 1250 335636510 335636513
    0xc171008010f0f0b030f0303040809060d180507051915031401030b04020306250f09090207030201020409060f03020904030509032b0306060e0604050d0c090501032004050c0f031302150403 82
    0x140070303550411300d007100030701100c4400300c4c1e400d52244001403008010440010340f211451342d41205940013151b00460030400342c40f12120310424078010403000da0f01481040710010712494412910f1420801054017040f11781e142010f4502e00c1034400d0801d00501d5168800304002d038616140503802907000d40d0000030241460300515060040c0034095801c0c0146900000e038812090707040308854681c843c501801c25151480c000c68401c1c80d550441644540005241014180c2c15005042683c8080710b041216980e141c00400222180f0f1000035080f1100d0300c00140403900440103030101170000f0341076815002c280c07802460200e040d02c40700d07480c0c2c091162031036164030307030611070500030b044142081c805514072000020500d001c1c502c02c4070312480120414100b007221404885004115160045c461541c681c604801d561a1b20b030030b95080c2d4182400020410310b000d009245c020000300d240c03c0d20f800c030000210000c1d0782c0001c4c1200c003405844512200161180c64501e00d8407201c100b00b258685065 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335639010 1250 335637760 335637791
    0x8060427030e06031012020d021314060d050d050d0906020d020301090b040509190303110a08040201021209010f110a050d02030901030f0908032806080c0406050102010c171008010f 79
    0x88030b40071802007805004119491480c42c0c444810303148144070f0b07103c00120314400510200c0b80c1501c020b401145002094100c411240c20201015800d6114945980e49200901c10f84411503403000d4001c0d4018216494810f0281c001411070402000d0f000c00d40182684900050b60320039490181102e40c0080100080c500c0742c89180c002800840b418001c60030700403c059600c400f0a080341e64a244c404c002c04082500903440002d000000d00e9801d52200d03c5403002801000040301c0903409801400c0e040001c4c42a01001c0702c02e100416180d240c0316a9115104480b00c03c03220750140c01e140b1500420401240041040c9500d481d8964002d42c0d552008600040075110b608a8520842d400c200b05d10340000c1c120310580b540031800b8140c2a8020140b51140c003421803201d822102404c0c50207001041240021446100c174140640302403002c0c0d680c1e20012401c0340e04a503a03420000c0d00b1340d0a9180702040d008412500b0000304800700540d01d80b41c5114500311410040840c958a40d40c807a02c0d443d0700c8a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335640260 1250 335639010 335639027
    0x30d0b0103020c100f1509050114090121062d0e0708030d050603070f0807030204051803030a110415170906010806040f0215070812010b04150806042703 67
    0x400c0c6400d608143c1e03064101c50b42c5001e003001e81001c00d80c45a4170304800494940c018032860704141c50704181c0a5a440d604401490280595111913424400f082498140820418103c89a10207244201100c00c0352085009030b2000c41243c1440c0c4481904440c0740c2a000400070b8a0a00b0400c48041807070300342c0000032228403110202d85600418003c00c10381202000351070b2860662003001c9165a2a040001d040810b036070025008100146004150081c0c0000c1c3d50040d0381c400da40410403501e4502d56060340007a90044034040e41e10410001e12880c7c05034201c01014807407144d001342072988980c003003110312103a5801000000c440e0305a124480080704e13034003900f080911014080c1e47d41423400842e25001d0042001c0c2000d01c0344c001000031915400340d06a0042c50194200307841e1135013850860300710342c88103840c04039a825070000419044004811141203031b9480c45041c1d0a503c1a61084e50040001800075034495660f0014403c02c0711102861400003c42160114000c015850054000300c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 335641510 1250 335640260 335640281
    0x10b03071509091104050a030302070e0903070b150a170a0620030f180a0f0203100b01020c0d060b1c02270c0304020d021005040602070b12010611100e030d 68
    0x449201900849400c0b41e0014242c800e84000418039030b5510304502c0c0300e845154041a0071541410000040c5540400c400094a100c0c22551907280c40c2e0890079a03172405400e0000d04505180c60106050300b003220501300c01008090070303242c0e180750f50301a02054620410001000f03a0492100c0f0700c1040510b209010500324610807510740f000d214482c10520740401804113600b04403000c04556051690750000650307400c403204039a4a030035646001b4107868400203049000c0c0c400c0c100000403490060190081d28941139000700040320121003084030041c400c0c0c0040e00d080e580c070750146442d91030310b000441251103a00c1b001c880c9071100e4818440415807004010349401c00d140000500d120507004299005105010322135140c1d01c0780d000203031055040b090001e611850883c428040039030028068401c8410316020346d85440d41d5010568041d00c2920000c10741040c0440050111a0151003650800c1809800729024440c178000000b0440740480c2000807160710106405175040b656000c1c565025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 335642760 1250 335641510 335641529
    0x20d0f080108070614040b0307020714040c020a08092d1017010303051b01051003050601050105041206051005030a0308090d110c121002040f090506030d0c061a04020a02010b0307 78
    0x56140075002c0d9100d0400d40a401c0422250f4000c903282c0702900e0084d14090203100400650301d082c10720000e556005680b040d0130019090104064444c42d00303100349994010940c000d008003800559032440c42d58414464568800440b87d0007059034800000341c5020000e045005241c008a07802c00c001c3c2500400c49071030104403400c500300c0403070014500d0203030460754181001510340c118900d080c15050b1140301d041c01c10b5864070040000380104191000c0449000b4000d031611642c81d40f00450341362182e401070310704ca014058101070000d112a80070311f0340036008084004204d5164800207040c425074820590002c0c0d0710b8414807000f84820f100210119410b410030508004c00200c04903261031001e607203648505031700e035082d058071034040c4441d8650040e5200d0865075903803035140e9075001c4002c0d4000c43c000c07103190400081d103d08001540845000050301c802008000c1c0c0d82e2210041c000305001024046096225101107440d81c0c000707025201d6042e0004200076444006251610080e6405580c84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 335644010 1250 335642760 335642777
    0xc010617010c09120c03151a0103051302091e0c1824180402030c040918081218030f07060c0c0c090e0f07060804031701050a12060e0d020d0f 62
    0x180780c10012034002c0300c0c03c0c940c184c11106080d040004812a035a07001500342840703d0030881d480300c1c40794003440540c012000164a0403000c003004408070b032011610001c8c0f0b10403042c02c04001d86032002c4810361006a29400c220111aa101000c58404080d01e82d4078a421000c81c0d400c020007004481212172610036104501100808080085075141e56100d004c0c62280000e000d0400280c8004500382255000d4029552414000341c000e880364024494110341c05d20f03001224a0701b80b50340c80c4036415507400c00515824500183c24900c010040685030a230010480e8403410141c0c00c0c280b028109907031440020303903110101c81c20140b007035445c0b04000341c04003d20080441c0000710307881030071020360b558940700040340080b0900700da151016607103842601c3e11410701e00107001684030200783c0c03246219680b61207083c01f0080095508a100b0f020b00c3e54050000d03102400110074071104041d016016a01c00300780ca2a11901083c01d00140c18807000040e0404445210043c0d00806401222089864507800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 335645260 1250 335644010 335644031
    0xd0f150806040305070f030c02150c070602070b040303050c03040306090b0f0705070b0c09240310060c110603072703030e0114090411120c19050406080f0a020f0c01061701 75
    0x107030f1241d10802400d8412680030001814450342002310304a46c09481031104d00c61040010100e90800380103680940301d6600e003c15418408555103044500301074000c1d040c50b045a030190741c2d58118102c207c84a100c24000040868200d015a00c1d4042c010100c411702e9044c001c0c5603078803102008180740305000e4100800b47c00181c400f800e4a80c40400700d4021902c483e4038070000307400540342940e8200c5c00c0d481030308003000c8041c40c400214020040c00c0c2c04080e8060380c0c0e81c0152000f811202000d010711850888890450503e00c000310b03480a2a441e000749030310264800c40d2100b0f04c3c1300242004e030340c2a0440500425801040512204030b003424801c6100e07040c0130909803684260420240100e40f03582034051101444801d45000703c102d54405080e0746025080c8005541101c05588a04211195103011090050f821901504c055507144095503440c5c00c140100c0c0700000d84240c2905a081211a8078000c0603400360a28218010000c0f4003140340606150198400d40001d4826914005021a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 335646510 1250 335645260 335645267
    0x30f050a02191e08030609010915031b0e07050702040b09190f181401140421121d0c09090d0f051c0905060f011511030d0f1508060403 59
    0xb801d10241021990039406150502e0303a0002d6000c0c000400e03008401d43c2d400c002c030031005940301e00003e490040c00c51ba030301d402c1c040550f445a2030308400b007140110240017282202410010395402c05031030004856680c40c035403802440460310400042d40102d40d0400310301d40740c012900d00201c03c9500040b941401500f80b00f035031000c030740c50400c1241e440c000550810202d0b005243c141001102070250014541010010b9080c042203000f01c2d54604450000000b0040400d603004a130440c044900820304240301c03050302c800c00f50210080c00240c001d11646543c060103030411070b030000d1004104c001240310a051900301103802c150b102e865604100825003c0004035080252a0b83c90f0420741102064003e40d1944a40c6481d11090311042c00120070024940d08010030b0107212350121140d41d40c501812008a08083c02401d8400c0d0400c01c50700d40d064400c0b9180d001429619095070315008580c000e050031038481d0b0086090540e118090085240ca81e4402c070001006000084d003618503196900a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 335647760 1250 335646510 335646523
    0x8030a0c080c0d0b040905010204090209090907060206060d050a0c060f2a2a0b360909030f030103120f020d08040305030415090c15020a030e060a0201090c0909030f050a02 75
    0x300040c641d15980720b111340d41d0b9604400d8010741c00a000310740c1c3d251204800310280d40007420040c01a5041004206e00903c0052050211580ba5001d0700c001e488803004c2111040c1ca8904c26034041c4115101d0310301140210003000300500403501e03080d40460200c03c0143c02508088100c40c441c10442945201080000d0310610750030b0f9203c00c202c0f4581c004c010b05082081070300c4c103e12940750000b004c042005460040100b04200d04080f100814620000306a0400e0444a20009155a0714446100346051600715250450501015207041c643c1b41c451490003030700700760300543d110400ba2400c14034854005412881600300d902c06041030a044d024003a150600c00f0b40020100640080010180402c2500401c110701e501340d41486580c1c01380c1040c2200180314014245549540120040b00500009030050650f9040d11400709403a4280208100b6401407407080b0159500e0329601000581c2094540010300144500003c0211407030030001c28242d510b008510510404102800210760001140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 335649010 1250 335647760 335647777
    0xd08072f0f100204060e151b010e2a06030f1b0403060c0807120612020d050a080403030c03090909031e02150903070b13030c200d08030a0c080c 63
    0x540da1800c14090030185429002203901c609406402003800144403550014022030f6402e643c0d03080000341c40c00401c52200300d83e24103c42800e00c1042a01821980300003c4042105608000600500e814107454203240f42280144a48403007211498112055a110280075000c00e80d01304d801c526000180301003451703000d400380503084503100300d000a021818049401443c6d0114040c00004000b80004e481c400b002d541c403201003942502c0794048491540710340822a004036400b41c01202d459001d000342c0c0074005c64140c9281c060102044003150b1582c000784000c0d1310907510071000300b02038200189807031000d0f00034041080c00d10b06400007103580003c509000302c1080380c1c0c40d91450380c0f4240580c60311440b0415291004004000c0088401c4003101418000e409101070300c9140ea41c0345044601800a4000100802d10656044000c60100f007a072004420f2040a203000c0700d10702c41e00260503000c107001b08907048a400010031180017914003030300c101c81d5441c0c04c00b080c8a0826942c00b107a01d000c0c5910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 335650260 1250 335649010 335649077
    0x507020607060e030f070b060d0305090d0c05180702061f050907021009080a020c0114030c03040c0e09010501091407021b031f02030603070618030303090812090d0807 73
    0x1101c20900c00c0d1507005900000c19103040700c1c0c0d5020988107443c040d4018400c166240c00c0d00c0c0c0005191824045504054140e140d0703a00c1e8075000c00e103804c10019100d081030a4600510500000c034564403aa40f064030101e0303210300c07030200700c1c0742220000340780200c0103045440c031010304144030f144d1002200580d8191070003140d403080301e5600c400080b40350280313511340103040500b840001c6040c0031215009000c2c260056003620180e441b090019981c140c1042e400c018000070400004140c1150700000d140c20501c100300d00e010146c0c0d038015810021070190398644e4241d66810041201c00e00d0b41c841c1c82a45001d41220301c810b407070b141d031000c1e44500c501024040007040390030354517910b40e400303018100142c140c065400c50001e2050402200070740046401ca4068401c10300d010603014000d48081c1c10141120801c1030203103080d07a4040300070300a0344204a030303220b9060000043c000c05855003540720700c1c0018020049442184c0e00101540c00c054660b00500002030010549114840d414850304610300c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 335651510 1250 335650260 335650267
    0x50f0304110d0c0905132f0d03030f15080a0209220501051b0f0f090f06030c030a0b1e040e0304050301090b1e06012109171e04050105070206 62
    0x70000d03540d01140c41c80c103070b120b840003400c1010420007030200001e449500508100705e6580c0842d034600041007501c05000d2207150600c1e52510041d140e446600d90074010341d005642c500210215058040040c0100d0100c0e8488441c15907401d4103204081405c1c8103030b101420028504011545c952408000203400341107118005441268a5070240c7d9040e620a14007040800b481e040050003080c054400c3d00041301d44020150004507030030203481c50781700005100da103010018808111154800384c403207500304103028040f2201d0340d101030166200b6810f0b150055075a1509260501c111080910b4143c4240000c50703c20100400c0511007079841c44080d140020215030b094400341c51400359500842d8150b0818580307604010010704503038010400b0f180d01034800c10720f401a40c1d0080c0d4044a009001607004144010035090250328080c12200030900020184550384a0081c90201150402440440098220b8581030901070761462540410905402c203800d00000034854403414101a21440012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 335652760 1250 335651510 335651513
    0x3070b040902090f091602060c07122a0b0906130804061b08040f03120503010e04030c02010c30050304020f06521203050a06080106090b03070510050f0304 68
    0x102104251135002061021070f131400d0a14480e000314103003590700040c01884d0219002d54807c2e001d9400261340300e64400c40c00d809802046840024840990710594142c071646012f01040d014034100907809400480707118585036241078a0904c002e00f00b044003809803d4a040480c80c400143c03801e580c2140340941d6007900006101e4807010761001c0c0908100c070001000210802c404a1030411070307200780d03840d41c9242c0c0420420f8500307000911601040010314000100081c3c8130303850244149105040520603100c040c1c0b200c00c4100e15001c040641110a106030b410b46849403440c83c4049e071174602d882481c2d8a484c0d40491080c840c07080340c86000da2008107520790030b14840e242d4203074405030b8a24454511042c2c030315504a106080403800f085011412204614844501e040720020303900302e5030000e988002a5000c030024003004040e03a2490350380b0540030171403003828094000180340100010516103164001c25040490503448a440360551142c4822407a0f0031000340d590702c180c001b0744641c803076550703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 335654010 1250 335652760 335652769
    0x5100b01030e0f0105071b0506190e150708100315090c0308030f0f0f220503041a0423030703151b031d0c030c0d020d02030a0c03060b03070b04090209 66
    0x1604a000d5050281941c00302c40e45038150305c01442100f2a81c0d640e0402d10301d900217200101c1c00440c020304903070044000204012000c110282120006003000581100f4902d941403e2a1103a8040c21030f00741400c06000d04250320650591300140620909544c09207941d848081d504540000740f00210b4a81c5020000c0c0030034030304100d0040d80c0001c030b02996850700750f01c440310718281202c0a291907254140420581d1a90f00d041078071403000181c482d9064140721100c07280002601030b040301c49100c01c000c041001c241c603016103405000074030142034682e41004508411580c1560883c14140e0541c5008407559800040c200c00300e9400c12902d4850b002e140103140b024004034114070409503032200c10b014000d58503034000e6261591210b0044407580d805800c060b03c42ca001c0035000d41c160300c20a005a12481c00503110440e19200401e40c02601321194042810b01ca2030307100036111542e1401d804c1042c00424092039603d0101100580010b500b04160401d1900071401140c0c240303580420052419182c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 335655260 1250 335654010 335654021
    0x504050f061306170109201602030f0f060f04020913050312010b19020a020a060516051c0f02010b01020a120e0d080d06090915020f0d18120203030405100b0103 70
    0x20b82c408030841054444401415680c0403944a00841c001d00c03000260b1141c061084081c840b14060072904d803502604841d4206401040c004103c68019603084001a5010880054034015220281001254800050f4107000f40103000d20034442c0d40b0400c2000607500c1e104215404090241980b400c403440c3d090451950281d2160525146804400400d401420002030254610b03100c0c0918402e580c81c00c0b04a032904180740b00250001210507083c02014000d0018000c6c00082c56611064255952521460180c00c500c031058002c03d000180c0384803943c0000242200300076400240820000540001d40d182180d500150031071740a40310b01c01c00c030351041560001e144801040241c44481d45d0402c96100e41c0a03200c2150750515190700050351400c14041c5807003d85c0c0009127480c18540440b1101c000c0d5100000040c2c0f07800041113030f0200c40449100d880840c04100c00c200104501c0f1b0b28041541114140001040d9841407041200061001034503c040901030800801c1a400f4440140c010340b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 335656510 1250 335655260 335655277
    0x160501020d0b0906040903120b0f0316030303050f01300f1101030f1404120207150305160305090604142118010c02150702060f07060b0a150504050f06 66
    0x50000801d6040e038038142d08003614520003140e0308020b43e1107103420001158460500180444c042000d101041420381e8400401680d021f490401d10681002c0040d05120f00d02d2507a80d02c1001c90740c000d105065146c420b0302d5004100c0c0700081da03a54140843d082038240070415040c01c02c03401503801460160844a03c06c0b0140d4800710303c800c05185490850000c002000000f40005d280c407070070000100c03940c02040505582102080740780d44075501c03107900190044401c0d5083d88600c443c002890260010b02c0d0780b000300c0c0d60340c0000300e608114030b9a1091500c050030080425092505104040b400410030b81d81083d4000c10548070541e00318030490400c010141c1c004051400950700c10540d061080c0286078444803030740c400d480c5d081050015160a0341412010b500b0152401c5007102c2d030031124008013907450004020500740150000e01da102b039400200c00b01c880c561a01e0b0001d000f0f050071940c8402a02901807881d0703184484100051590045100d214458140d500300b140316a00c0b040100d400c2c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 335657760 1250 335656510 335656513
    0xd061e1e0f0e06010206060405160c30090b07020f010302130e16020106080f0304030201080a02040b07030f1142040f020108100f0603022b0e010b0409080409021605 72
    0x20755121520414240c08443c1c1c1c602600501000411794581841410b224240c1d40070303910ba9080e032410044844220407030013169605940c8008408521200c002240d48403600e4551110320030203d10b0080054003254883d1034004e07018404c0e0342c0180e40d080251111004203203401a1a02c80120300d803a181d00a40d17206601d80070a0400b48020f043d0044001a9050f4207034009000300340d035540e0038583c0c603204d031040c01c4420b810900081c001903114100903034101e2a036102c050708041d200e0383c4803a010b134032010044011540c140c0c0b01265650300f00030b5424a805007003000c2c1900017440c1c018202d01514584541301e2042031090121200b1809400c5c1a03d6100c8403000c03080c1c01e107002c0c1b804401c1c03410304660170b07800b1445c82c1001500d117054164003502510440203440c40e070a45003800c01d80103034101c46001880c8100720500c04036614001c0d400c03080c11034214180811070440145050342116102c0315158002c505294603040811903020807102124443c2c400160799440307220740d0034a04102c3c039600900c203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 335659010 1250 335657760 335657789
    0x1090c0305010f0e0c0604090209030f070e01030b09150a020903070305060c0c15070f230a020d0305011a040506030601020a080f0a0201060605121311030a05030d061e1e 74
    0x60000540c0040341c840603119003044094144203032241d45a204102c0a68006c500300010b03c007a84240d006410200806012200202039011481d4181940f40c0c01c60500050580c0040082c41700c1d0250381d0b0340011805c40a003440840b60b001c0076030004002080608000c1d000180d071500350700c040222400440d00102514428201400c0301f5003507a0100c64401d07028841c0140d078100469401070b406004d803c031510760020007242e0032025900500c1c1032400101c10b481002502c00c81e0101c580c01040d8903090f940c0034085482c3d0941c2d0180131190103030000406074000d1401001c03920000c00440b8140e0300102c3d421074403039a1b0040100d15001e81b481006040040210b681114911100040d0002e010903400a110540d140c0c44110703014020303074400f60780000c850004142c425500d5150103850314052000c80e550508042c002c0385c50078070f00c070400304c2d070640c40000d003241c49a00d03501c00c1001610440070102c6580061206051051105004000044001e5400a1f580b0304048598100605401e481506e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 335660260 1250 335659010 335659013
    0x40b180d0c060b0f060d05091908120702010b0f19080f030a03050627060f060c0c0a140907051c1401030201030c03111602060d09060603120302030705040e0901090c03 73
    0x3140c080c1c61080703580e6800d0042e0f00005140240d40744010070405045182070408901d01c5801900010704582c0703a034064014400650154000c41e0400a03004000060362440a5884201700c241c00030500011a4948030038088560b0320412041002c070805c40310b0090340c07004c8000c3d03240c001030303035900c00300c0c0e0382c840d41d02200c21859010019054000303035502d08000d41d607036003011f10400003240000c4000b03240202207124079010750107401a030844005031610354841103c0780420b01700e5002c4050340d055036201c0210f4000e84e1030b01002d03210140c890031880301d802100040c0403070010b860244c01301c0c082c4103000c14914070007444a11842c0448202210074480040b403072004451081c800c0c0000c3e800030b814504103c2000e030080c000c44c807000032062803103454a8100140c080e481d5034141e804130f9020604100c0300c80c0045090146003407050064500290403072852030960700c40210b008060341851300500c00c000481d900f02c1b0540e4121030300800352803808c3da20341000d0f0b0300620318100000c1c140d0440020120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 335661510 1250 335660260 335660267
    0x914010504050d02070807050303030601031d070303051308011a01083d080f1209040204031407060201062709021c1b05010c0b010b09060403050d0f080c12040b180d 72
    0x9801110340031713556195101d030308140c0c50380024040c07507030581d00c100045800d5502c00da02c0b8082c8401070080c000d0441200c1104a41840215402074000407001300b040007400ea5800a4080103020f1007000300031041c0c00c9252103144aa159075400c0c140118440024800c83d04606100c4010047c2e90389107901c0705603140c0394a01c0c0000d480108141d12904200403801700300006502415a492000805000f002200e69520702d03845083e844e40c101350244000000a5605e03200300400b52446006070520310305000c00282198100da1051082c80c4001030610940c400c0000d0348504280340c9070700032840a42034000700740a403140460449004103441424402d0003050340c07a81484003410003101c0c8030559140d00440b4000d0254102034a0280410010404c24a101006003500030020b00b4041c01c140e540d45804d820140e04001500208201c0110345400d00c0e400100c20307911200c00080a818900191010b00300c1d9580240008c000510380300c046000008085440f080304200101169900d45980390001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 335662760 1250 335661510 335661523
    0x305060c0c0f100c02161809170d0207050c01171914040605160f022d0102071a1e0a0b010c05030406170906010806060d060e0d030207020909010e030d091401050405 72
    0x3a006000d0091281c018000700340c018070459800391f078140d40854101c80d2640c0100b014481c100c400f41c4000f00541a44600c000c00b030561003120f10300c010b80751102401c1060070000d660313a80a04001d1240945110011901c081d1504000c0c000404001c0c440820744200051441e03103070210940c980001044100701c180d4125900c542540000a180141c8503001603c03001105403803900035810260030962904041e440600880c0d2a441c00028003040403507003036007240d0244d203041d00c904148800001c02d440c6516003050304082180d03110180490605030b070840018024261985564a0720a041c3c1168842c001d52600c1a400c401600d60341c1e55603000c094008240f4840301124041c005000030301044020512504881052010f00b0349a51400c04106080d05802c0f400c9170b24564881d88120180030401c80b01c0414411a100107035160090700400482c003070000d02852040e81004014a000a0b000c026a0040c0c0703220000400c10005d14a07003c14050f030a12024450303580b0f400c0401003800343c0020030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 335664010 1250 335662760 335662781
    0x1051c0809090a1d0609030a05130e3904090b03030d0f0203150904020d020904150510050a120c03120c080d0501031e2d150c0201150305060c0c0f10 65
    0x13028252846005116201e0100b01c5001c1c040d60014050341e003415008000500345405c08880700502c13651105052524032605070f078502c1c0400c0000c101098842902202481e01000d04030040c19181300703913409030015100718002c0103080f68540202840d60f4038100169041c61402800030700c84c4825100d050300007500100c03082d114007042c036082c008540c180b44c084680156009080300800c80342503001e001010380c1c060004c81d221001011801c400030494450389000c0c14002403050b00c91407410040044114042e0040c000c1e050851003440e00192103c0c280c10b0480764880e80303070b02d580e8102180030341e050030b010320000d480c04200146800d0214030303a5111506030303841108400203529103607440b0040798800040003841c107500b0403803401060700c07415119810f0000d01101e94800d90029510840f11004d914454080d690300d0706c18460b00c09070203000342079042301400540792886155854090752050003802c5151300b0710000400c0403c0d070f0002d00194140344c0b000030840d0341136218501002e005041d014417 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 335665260 1250 335664010 335664041
    0x3091503090c061b020603040f14010501080d0504061e030e03040e04021504030203030f0c03090a230301020f22090c0207060e03030403030e01031e0c0903050708010501051c0809090a 80
    0x2021524a0042c860141e41844450b030030f1360b000520f0b500384404c69001800641c0c00025052981000030054008840383c821200d0011a442d49000e0000c1c1c50035544040d40b1041c490180310070b00082d40d111511a807103100000c49800460300f0b24806400801d241d55042c01940000103001c2403c0b404815481d000d40c1c03080d00e034204554250301c1c44844c03502980c04000e41c590001c01020b040411004080c003050320394401a24a4184030100080c0044581c0d4042d01010078041c60100500d80a904101d2484006a000754500000c181b20714040380315a03030b007074100720428100c035622054403070121801030f003941c030b03800c000c10300340d5100281d50360400d8403403a40015085600f980440c103020050301c048a5050300d491180c002c01400640241840925100c0043c0000340c4912140f000380c000d1280071841c0d80c5550410b5030650030400c0c01c00405070040201607040c6401040780d600d80d001c00c0411000c07801d00c00c902030040d5107081071030341c40340401582e030145d0000c05004c0c00701e00503400041e6941400c1c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 335666510 1250 335665260 335665283
    0xc1e090c020703030f1716020123010504200c031207110a111c030305060f01020c0901050f0a09022b09020114090a0e0c0a090e090a030c0309150309 65
    0x610000035141012850401a004120200006030203901e00083c00384681c108181314560f01244403041c00350840d00d184420404202c0301c03a40c150288038001e8010b01da00d0388440d044020040d107460b888010310a8a0040f60340303000407081600f84a8200704200705039925680da81c0025503043c0d41da6041128941c840b441d0440100e003540d401080f0400d10000b07070b60084d0050369269183c12111451401d80140c003c901c42105422008003011207540b4944a40c80c0001e55003499020f20a800322041051815540a02079242082c0c1d201903060341100d400319508080303050b942001c1440784060798080301d4013a00100740641d10b80f2003c210140c62500100d1440c4850040d28060000d0b01d41500c4041d011559001416144001d144010500b5070005410001c40690740c4c5096004900100c2c1c07140031301d90f0082072140c640d40e4007589a0004188002e28000203041101420703440d07000015009040c0310034003004204140c0521403480c005c08816003130740790304602a413002d006170048031001c460580291 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 335667760 1250 335666510 335666519
    0x30210020303090a0b060d02100c0c05010e03060c0c0c06040603060501080a140609040204020f0d0203041505041a07020c0405011221020a0f061506050c010b1e0415030c1e 75
    0x7924420907000005250013103e40d00c4503c00504090103441d0048801550303800581c48041804a40f000c607991401905092414030305092240ca0b000f89040100384c440c8003a49a6001901c0c942100c040c42145a0360500f68102130700d0b2440d03071803d0340e4201078007280005010f030b099401a011141c0c00e07210807a259a55550490031100c5e5907131090000c4550038007040e82410031240455101e84040d0006140010003248090741e42c11282360210002c7d0000100000c004c51040501c0f11450451810b00160402c2d50720920150720640c44020843c980800148525108100503070011038060700c20805561108041a13014100410a540d2400008142c0c40007603103001d112106c00c10300c3e03406090181030660790f070f006452000700c0c00d40b0403035121500d5440032840c4100a100404480d11410742c0c642c00c15407400e081d2100e0802040c858035201044114841c45640d000744404011a000141020b20310308061520b0f895400c042d26060000700e000c58007000d06000d8800e01c0030181c1c8280f03543c0f50348 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 335669010 1250 335667760 335667763
    0x80a091a1b030606040312021f0f0f02040b03130627051903090b0f0c010c0903030207060c02060901030216050a060246050d0c0c0606060806180907170703021002 71
    0x790f030341e03d4110008101c10000b00c0c101c0c90f0188011002407050307406504940261031500c003d816800800c042e0f03114210005030a0030b115546040024800039030901c0d2070110f20403070b0707400020050028800010412020400c1035030001c51035120303000801d4441441203601080c46050990110386030f07c9040a209003842e465100d600d00d2a0f8199038948115050024038800c50708040c51b203414115040c464100c94140a002e02d040503500b5030b03a540c40c2079245003402072601e01030364080401d11200c20000c4016071500c400300c0710016800e01700560b481d0111079261900200c030480c0030344603020b04004681000348a80040214100304004608104400800000c00c00301031007860f02c0c40300145400541218000c0c042d42100081030070301d98141804142c00c1c1c0e00b07039050221007000194000e829042048910b1090402802042c607000c101d80c608007000c1351003403071075030580265080d0610006456071030030403440f0040d0100031014241c82130003020640d51000d40d400102c0c8602c886041d8003000a10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 335670260 1250 335669010 335669017
    0xc06020a050a09090b090403030b0d0f0f02180907050f0d021003060608061c0f060615080603060c0a021b03032101030203070503210d06050d0b040606050111030a080a091a1b 76
    0x11b04176030498640e0b54068004095804101360040c0d411003100c80442d00050502542600510f4a0041e070701c0c0d0b80c41001034070304c1c65080ca40b40710840c8000740039144000048880542e68251649812180b010001504041600c80020b6120078038110782c04901354140c2129044a4a0752281e200742d44404082012103840e011036130400035504d0040b08045103070710460603401c40c0184800038103552280c0b01240c3c10014040d068010400c1d0300d090061b142410005150301c100c4841c880e80c10300c1d803141802034490320705440f003110031150b041d540c0d44941e07403c1c001c072145041000003440d41010b401c041c000c0580c1e0709110a0f4820f0056210020b91401c010817030f0780c0c081440d403c2c1c42c104401d0000759001c0750b411100c200036903903590352030100d01c0e81c4416002901460240030802e01518052503d00c085d21400e41000e070401c4005564a010ba40000064840c001124200107003103594040d0310400412458030054203690018500c0d1340780305000c2e82c2c00c500492400a51001824920811156511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 335671510 1250 335670260 335670281
    0x7210f110a02010c0c0509090d141608030a060f060c05010e0304060c08031003080d0f0507023c01051003052503080306130c0305090f1504030e010c06020a050a0909 72
    0x1003181d40750000640c803900e4248241c038440d88591300d040d6280d20204580e10000c03a4813400d6a4040e0b1001c15001e5041081803501d20f1a4411040c50114003110002c0e6182604000070861500030000c10b808940c190070032805002d0081c6081c02d9143d40c0c10004050000d00441540c3c0d9501c3c011003009513880c04001c80c0c0a840c02510ac440b040801540c2c1d82045600040028954a80c10500400018240e174000e0070802c0c90800f0226110007064000c3c2d040391005002002954800c40024815445802040401c400441049482032101001800c8001d42c40b00029001d035180c00100411200a0031080041e030f80600210780110124100301c6607817101c4841c1c64082010381c400e0801c000f0b81160011a401440940f0340c280080c0c1d1a400701040c2c880e03081808020030b8644040050b4844100068600841035030010100d4080a0041030016030740076202070300b0402e104a403512030780d0268441d4540c16510070f00465407a4070b4890002c20356007250707401e1030016440c00f0000804108a014221004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 335672760 1250 335671510 335671513
    0x1b03062102010c290c03100e06011205010e0f070908030702130219030b1c080d05090c09040503040603050c0f09040f0b19030c21120507210f11 63
    0x48680c4920380303842685000032410019040c4140c80055403031643c076401804003101480101040c942c22038910080103001d003508007002c0c004c02c003006103010320344001c9900d003c201c03003030b5500d4403001280c0c01c0070208166000b1a060400024240702d0320002e592003070305c80ca0421080e03a2036240f800c40b444601e40c4502e40c2141d000b842810098640040c0307503885400048001854800020b50380701c68003541c1c111040100e41c0c0c074500c40489040c98910000031041141a20b02c4140540e0340e666a40e01070b00c00c61018165031040080d40c00d83c0d0400007080c2c040c0c0002d0071204a4940340c50050760b00e0b403050041d0400641007074086810310246106888080100031f00e005c0c201030441051000502e2140381481690340c4680c003400181d2145080d0706032413101c035980103d0660650520380c54410096200d02d4508a46a40043d003201c424111500490345c040122a204540131400f110217000f450009000c644442d080e6600d000c5903418444030805160b11000d0b01d00000c21815102e003074100c0c032200c107507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 335674010 1250 335672760 335672789
    0x706080f06040219080a0e160b0705010204050d080a110d090e31020f09010506030415060b0f04090509121c0905011109012304030f03021009061b0306 66
    0x29164902065074030520150006080c640001e0030345841251008040f0007150760300c0180002c0320f10501a030802d030010100104800780d44804540f000d44130301d201d0f010041101142c50401c00c0401e4046600030000140300c07080d03d004900344030742c0583c0f000302c001000c1030b100d429505802401007020300c03a03448992155480d49203051b140200360180100600780c1c602d4284541002ea00c030002c6071103505491601d4500300c0004034030500003402e9590741020b1141c249080100402d9507445c003101d078000d40c85005217200000c18102540030b00f03503581107104102008034400c01c00c66848800340c012503900c4002400381c1c2d2130300b60940743c071a00d2025584200b6081042900d15400407c40e6481180ea01240002501100e9484032808c5811169903548034480020b008a002e40c2d0240000c0d100c1c1c001124590b01d0395003044180b942910903407000821201884001d60103142c000c2c882882041d80305002403144103007900d0320400920035001150726001c1702a411000092007031182209480c0c4100380c6055 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 335675260 1250 335674010 335674021
    0x160909060b030106050a0203090a081c03020c28050a030e09070302070b062b050114010501090803041814040c050406080d08040b15030307060b0306010504091e080f0a02030714070608 80
    0x200d0360310200440c6e003544410042001a0f8443d914a42d0082064102400080f0a140d010281c0058459019810140180f202d005031110110360400c42210203800c45062964145480a851000600240c40c6008038142038051540120f40710000d51001c03988561203580705c113820740407401000c1c0042c00440c1da0500160709410401c00700651403040d54049500d0b94400c010b00d28266100d030508031140d94564825a80d00c04c0b915078458050070007420110f00d4a401c000392550750340118400c18400e0714002501604c0070f0f94a51094080c24a0300461005c0c91034a410a140f1881c1c847c03107170f90701a0385001400201c04c0c4020892844140303042e80c3d480c180303448603140c403441400c0c040c0244182c0614104c540580f590108018a072452180074040755540640c4105414001d0503030042e40250305058800c400600c07600010343c50f41444640e4850788030194100301c04603018002e55410f100100040082c1540e40000207002994843c01c1400d00007480341a1460311201580f007058041403c240101e403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 335676510 1250 335675260 335675267
    0x102300f09030f0a030902090604090807031d09011415030114130f18060b0603010f0e2a04090b120601050d08070203030a0c050c01030603110d1a160909060b030106 72
    0xe400078035520840f4100ba0446441c8840307079012262640101c0d40d107812400071810207804042c0e01c000d0880781040040050b07219808188580807008080209204041129880703068007030303000880c0a00030011940c0c45e5040f00041d1414060304502c600740d150f4000c0303200200e5404890596020705011014080e002d0144250742588040301e091041e00e5910414803030b00548102c1c1e00d2259003a240040e42a80303400c0030400c032021280f00d10f00900d000c20060090b0617466800c0f4003200d62449420125980711000d4041008100d100c07125407007100c039161200490050b02800035605980380800150904008010403810101000d000c1508070b00010030051a1540d261039455016101c0a441c00890364006400c55000e040004046100c228190f8280700080140140d80380703080c20100901e50a40d15610102924140028030540c181108001080300d00e01c90020110a01001c1204074144044901002d06140c1c00e03000014107000c10020380456580590021601083c4550b072459007080d6044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 335677760 1250 335676510 335676541
    0x117190903020c13150b12070e0102160806010602010b0306041101111e01090c0905151e0a08060901110f0706020706090b040605060312040e06090a1b02010230 70
    0x1d078154080c0c48041031550311480c0c0408940d40c1c20b10400503030004440c205020701309803500102c0300c83e002402090308003904034800300d41100c7c290515015001d1440c004030710300200d6800d105007040e201c170000103030000c000545505990141d0024019090710500b40b5940d5801203030080c1c003624016201d250154000c80300c9405d0090400c0940d080429050b85e00c098490b5280700f0209169914100c26052014058401c0050480203906216906020310b0700c500828001904911903082c0c85a1102d4800081400000140c0042d0203032031260356031806192180d508449865540d403c080c240710400c8246411159603000400c050307410002207441e4200250022002100c00320781d20b405038400318411999283c03080c0d116240202e80c0f40340c04414503003072500b01c0e203d01d0502c038414042401018855554183d02c040c0a6540c10b41e2580c40004001c050040000300441d100481308000c41b185174190001c015041901d112010381c480e800803410b01110300422840920f04141010800c00350a50124 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 335679010 1250 335677760 335677763
    0xe010e060d02090604150e0609010c060c11010e10050c0a080a05060a050411070302160f05010e180717010b040b0d020309070816030b0a051015110706050901171909 72
    0x1418443c030000070840e240c0c0250007810021082072a0512a140d205074104040300301981e041c2d003000703400c070000303408006002c400078050364483d9100241e9078030482440f18010300c000000d1200144402c4542d858004142104100c0c070306001c0054440c5030020121014010f20355100300040daa20340c01c0d130b4000e1401600c03240d800000b10b9030001e000ea840c2e000300c0e0511a10200d00b0356652645142c0a07280c103440320450203208910785c00400181c40143d640100301c51017802c000203a0320310003000481c125060b02203024840d40740001e200304c2c81d5004a0340c2c003844000c1811400c05036200c4448210340d0103a84100b10005a0401c0b007031000b080d40307802031034100f44034200721a0399a40b40c3d004141010245680103a80c08400c110030000c2c000221000d43d0480881901004103007031485e129507d00445000300180c0c2400c0b00c821417031031803040700364a40c1783e1440025200c20130f03107c0c00010503651105200600092141495180c01c48032660000e02a0540703c0c41c2002c50440d18030003c002d0060941c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 335680260 1250 335679010 335679037
    0x1020403080f03130c032306221b090b090c0903101a0a03150c0c050309010e0118150f080f06280e160c030203030f0414150f070e010e06 60
    0x10000090000c0d08078405107100703008070000c4680020b1b04a0b1401c001f0482480c1d568801d00c240041007594141c9501c01d444480c2c21489000f0450030040e00c850303d220401980c0941c60071000420000303a44c007500620108070f448000c0764489204c0803410303028030251140c0c10341210405104035001e5501c1480030000110b404400400001c0005455071a10303407055402d15035100134550501d1071441004004106803d10040550321030b02c8069490048249040c140294804001001e030b0281e61125400d0407a0028800b100792a290f0490803000050500310209003c88800e000041c010100184180414900c0301c2c0681d8400c0e08000c0169074404558900c134500203c0c01002440580d582005400140d42825071404c1801c0300303001d0131a80981d21005c000241c06020b0000b5804070403a80c11080d5040400c0303880d121800c01070104000d04a0780b0109105524400c0c44000081194a01c6403100a154202c43c0d50390744002e13507a01c0b0715506420700184502420b04158501540a004c101c2c0c501ea1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 335681510 1250 335680260 335680291
    0xf030709120308090c030304030c0b0901140d0603020a0506090d03030c0302091206010806010801090803011505040902040e100503030421050a050a03110f030a0801170a0204020a0302040806010801020403080f03 92
    0x40890070410480c035090340099200c0e000c004074900100a10b41705c1c900c068005618251940d15400340600ca9405071080a440000c1d81c2461030788203018440c94903c00d00301c1e450b030b145009034103400180000e220490140003000300c0041d0b070b45449810740d10108409058180c84a40c00c0d9021002081d4042048040c1a420b01100031107072a121800c912042e1544001e1407103506181e260341c0741200c1680a403a444c0e040c2012403000403051400d0303c0c119136201d80e00032414100310300140c999006541100403401d201250000705030421543c3c40c2d020b1070040e2442c140701034aa5003807640301d00c60750284071403207410313142020790044090060b03440042c05002900c0170781181d640e8107030426100c070b40283c00103035003031070341101098040c460140c00301a264011441c010080c44060300d41601480782c2c0903144a400c400801329501072040d4410f00e54001c00443d6200c41075403002d0004d40150240c0540c81c400d250010989100510844065076000146d150500d1101440b141055000801d48221285080d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 335682760 1250 335681510 335681519
    0x501030906090804080a03030e06060f0114120a0209010315210312050a0203010e07050403030f080a020c060f07030609050903040b03330907031b0311040b13050103060503030f0f030709 81
    0x43c00074002a1000d00090702e003504a5090080680e40500c040f040385400c0502800319581d075074225140740030340a0030040d070042442804d826440c080c41c02001c503442c44410030030110511513402010702030026201040003443c80b400c002e401114070300402c0e0203014601d90461400741c004050100300c1e8803a29001c00340c0d8641c44202c40646070140e40110040360080300501c50042a141c6066110741a031604505085c41d40d1001458181c0d0344100c0b1040c81140c001050380043c03a5012500c001120314100c5e9128241880d00b04e8102d003086a2000000780340240108664102d806a1400b0b50481d0340114280360070072101003082e40c00584085109114084030b0410105c46041100b20041341c458000b8941007440244007400d035006111004043c9050030403884820142080e0042d00910300d00000c2000210354803418500c1207400c0340350408000b152034086a40c91541d10010b4403030a81c0c1c24400c0c9640d420506940307002e588201241d8a0080c00141150102e00000d9580080c042c84d0424849075603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 335684010 1250 335682760 335682773
    0x221010f15060e0d0f26030f16092301020114070504030c05040504050a06090206090a03111314070e030c0405072d0e0609040b10110d0513050103090609 67
    0x148070381c0d0502000008100407003900904034440b00c49040d500000315003055942c0da025881c1e0040000d050504075548291664440303200022040c4142c1c40d505e076281402904500704030790480381d11952290703000420038060b00c14241042100c110b41e4400011848650741c000c0340715000341d2181d04540da1041c0880c0d98043e4a00c400d4054451a100da5585604604208001d040160007441c040e40c2454203010003d600000c260881581100d40020041d45038030004901d440360042055019605481c08818000f03000800542403008482c141e0300b203c80354186109880381c161200400e1a6690001450b2502640d008c4620440c01800d64051501920000d0704641007950700c100010054801912400d0020003c03c2900c1c0c032420603200d81d02c0555800818242c0c0d03c0c4143c40c01403d001c1000a40790b201d40d00100d0052b00c0041001c6814004800b00604050003500fa088461088207003090445010300101d440b00c00d052203541c5481810040150041e299150003190200d65429601010441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 335685260 1250 335684010 335684021
    0x35030f040f0e0901090206030a090201030e03191803020a06080717010f03060b121f0e060f0717070c060e0f0f012301231305070201020d0e06040221010f 67
    0x420115100d41c504021800d0b820394401080081160716284900015035101000d5070380c00480d442021030308650500c0120040c050990641406110210740601d90b980100e01c002c49249407030341c844980c6140700304138480e100c44512010390400018501071090320b116a024641c00364250800160007200002d01d40c206403400d0b40600f0078182501402c1c02006000c3c0103425082201f210740e0480701d1115200c0680b501062110b801c05001c19148403d5058480d8120b10f110413002401e8a15916040000c24450142100c40000103101041d6408940b148174a0003805002190b9a030380d0215074a55483c8010400e10805100c117100d061626410170a04001d80001920401c0000c00c01c140c140075035030000d10451040d1b2021090071300052200c0c4100495000992081012a102a46038203000c1030b804240c00921040b41e034180030400c651160150018091210702100420130040074a080b140c40b1348095800a42c032404a89060100c0c1c407031404e07403401e200c540400014107030388a1000d03002140e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 335686510 1250 335685260 335685269
    0xb0405211c09090212060405090708190303051b030c0901120e0d1e05091e0a0905150a140d020301180c090b010504030c0902031302060304061535030f04 67
    0x14500190015450b40324440d10010700c10b0369030035400c20007609281c1c00c1414009200314040c558030000114541010441c150052021005032015041404010040c0354044d407015008681004040380c0607030104a4041d003442c0038101c40700d0540e10f40301007110080d448818150f0401203841ba11a0241801d440385909140c0905c00a2601c5160b04101410101d20b09060441807520348112440d040d41090807580b0225040f145415503c07a088944000e00e200705075410780000400c50301013505540f0390700a42c00380c299808490b400a6055042080307001d894011103d4800c059071001c040742c2002c2941078249440100040742804080050401e012091201a6081203103c5010082c409044c8181c03141c0d00020300c0e2441c035090440c3c844640f41c1382144107038016290b0000003d01c0c21003001103880e48076a801081c8684d01d00f000d040a80180282c1d05012140d081c580350001111111500c010401c4042940310184e406e00b101c0c205504d0b0700b4090a50a030500041012440d0414010010f20140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 335687760 1250 335686510 335686543
    0x60807030504210815040612021c060203090d0912020f010e03101803091a0405060c0f010908040509060409150b0112020a170907121211010608250b040521 68
    0x5d18240b891100380c55070340e05da0030303000300d2038503e0134090305c03450503c401801a01070380c00d0807200c007000c80c41450703071680b864014020601c0171050001c001404556450340e00456a20b90003150344946583c000d49116140095000082ca000c4000745d501402c0a0f00c000e040060540c1c2844480350320f03042c1900c6110803c0300016010714070170410182c01540140103001217002c0e510b4581841000820544600c2c041c4a00c80d02c3c0c0440c9050445008010300c280c4030b60214000d00040c602840c02c403c4075081801424496516000000c900b810588650346200c0d4116806154181c2c44007444001003203102501d07810010440d901c09080d1420740010301d1041c05503611000311058110b1000441030001d8806921034101080c00c11014001c0102d080e0515080078000001920303010058030800300101c0400e00740c0d420520000b81c03040c000b15241c2a504140d0b0400f641c001d0320500410003241c0640134200481c40306001c2408542007002103400158456407030f04243c40e42807030405140961003c1490401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 335689010 1250 335687760 335687777
    0x5100c141f0e061f0f08060105150a090501140702030604110a0b030127240602070803040503071208071e0203070b03070f0f0e04020a02210406080703050421 69
    0x4210003221102040000840c204541000c4240d8161110f801400d071007454000c0749089440301001c984040c00801d01d52405828041c0c1c1c8136800d80d1207a409100c1c042c403400c2d2000c000c440c00040c0f02c080750600040c50f0b590000341400c040056641c440c05410314441828140456001178030304010040c01203002d1450504414103034400c0082c00d010700d8100881107003040c0b004101c192900390b004250080300c2000c607110f03c802c031624180109021030820701c408241c0c95129402c0000f140200098600d00c1e821340d280251a001c0840c0c0e079216504c10607400da40800400c1010f61003000c036004440e03201d0b6031642d00e010840c0d112032808590701681e01c0021000500c00744114030702041040c00405004444900310310704080058101203007160200113202d03036001e40c14400707442040d4901400c10020011921048a420020750328a441b4902c5400da58200024a145650300c00030381d0200c0b066565074204590b01c4a1007180982005001100d6920440404140701c00c013400d204c3d000d03181143d0312a041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 335690260 1250 335689010 335689033
    0x309090c030f06060309020d060b0d0b0403050a020c22050408090d120314011404020922020a110a02030a080c030409020f120f0f0a1d0a0302010c08010b031005100c14 73
    0x40301c600b0b40c07101041c51b142c440107000503141c1d440d08540d03098100400180701b0800c400030030661000f100008109602403c100803c00d60444043c18602d0f54503400c8130703242407070038044c403208221240c43d000d88403d9610010703500e180c0540141d41e21504c00d609007814103c00e81c01055207400300c11710444801181c8403c0b1400d895040c851815610110046407015514154254081e02c1c20024075500a0b50006066030305a100c94017140c4d8000340d01030b0500b00340011803d40800030340186500390005074a85903216904603001031032249103500200a00b01c00304080d628110345520841c5d0084030f03808180700004803070420340301420710312007407244196480901d424080740002d8018032a43c0740c01040307001d2210520040701300c903600c031442e0031000038640036045981e28205070142035650f0911070010031104240c0c0c10341051100600c05d03292034a0503601d0b08080403d90004440480a642c0503c104202034507010b4000001541142030007050518140c4500081201964440203c0d5000503e040b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 335691510 1250 335690260 335690291
    0x302040c050318061504090503070b0a0b0f030f0c010507050a0b0702011407020118020105091c211b0b18060708091204030203070e070905090a050714090f0108040309090c03 76
    0xda80c0d20700d00701a2130350b03142c010441c0383c51203003d0806070300a543c0c80c41303c5000c0100c10002c482d900c03034000ca0341e0783e510720300707088480003420352006401c0c051b1040c1c244800880c03c0025a43c1140a92200a40201c400050044031076400080042da040e11400f107044022490340b0b030b08180110000d6002190415406845208010f400b5002c6000c6a1400d28032040c00400540350445c803a81c2480c10315a10030241000a13201004600e0400711000703500070a408004920208040c41543d41000020001e108981620322158a06d0140ca01001c80c2d1b4009000801380f000175a84003000e080341449081464450615101044500c0b40100d16410107008900d841005421541d01c5162003151502d800c60780400c1d100c800030700c58080f8000080000c118600e025041c0000941000341030280580350600788200a40401d03600400400c0c501d500d101d800070030a0048804044018008140201928004580144008005604001c40100c01090101035800b4842c410001998046060300c87c188086 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 335692760 1250 335691510 335691541
    0x71505041e05030a0804030203040503120c0706030b090412140706230603070b03060a08031611010305100311040e070801060302010801050a030507062007030b01090e010501050f0d06060302040c0503 87
    0x50076815000002800000c20000845503400030510700300318140c036103240c00d03881d5004581046030b050242d2060461001c40d100050000240d403a0100da00c01030742c41c06d040e41110f24841c03500390481040000540401c2ca600d404890004107864081c41c0c142c41e0045010003078000e614102d41d416103600e05407034a903003110640c0542d40c942c080c03d0b508504008000960f11021031080a801c0c4001200042c0559942c0c03050200030005001075030341c0e6014082078807882c405900800c032501000310115107e954403078802d1621501985403654040f50454840214080308503901551083d01d402c812102c90b8400d100c1c20009085400021510604600c009010307240c0580080d4000c1611590402c04100005017000c03c03601141005802c2c01080c40c4000e54001140082000364801c0d04c074000200280c1c0d900042c1224491102006000a170a500d00d00342c0f107082c030031141d1005030900d00c51001e1800418a020482c03040200003000c56880c1c4c00f04d000d0740c158610400c0884c10200403ca120f0300d002c0b800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 335694010 1250 335692760 335692793
    0x4030b0f06030f0724020c06070302010203070219030c08071104060323060f2d04050309131a041a0d0501021e25030908010e0109060e030c03031b07150504 68
    0x14019071030178404140d803075020111628100110000210000500030b00c41c0850703903200508940d907959070b01c0c18080e02035401039446000500c00e2031000c031051000340007000c41c01585a52003000507807040d2140c510304d40000c0c4050f14050190002c81d142e0390f0391880342a00840c0300e814420b0604c1818002400350071a01041459103811074001c02c10300003940100c10b80d000d00d080f5401c1c3d1540290015465050940300c0d0b408200320300e042d00384001d10400102901c100003045a00006090a040b540025200480312001c500070508000300500d14064100000140c00b440390418400800000a15481141d2205959a9500140c4c40c00182c1c0310401086043c1066180240f0f040c1500141c3e041140937141145060f482d00c0c020f0301e00b058425408080100b41040091082c002d011075200d00034650354000b169101d11f8141ca0300c0c90101e000c0300307940c040c860f618080c5007540d8420088001441c2e90003d100740c01c4000b00034090001d02c010002d05019115880002020300e050314000f511020a44c09 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 335695260 1250 335694010 335694013
    0x60c140c1b100c0215090d03020105160906051b1614090f0402060d05090114160e011e0302030901020c070605030103200901050409060f1a0307090b030a080a0504030b0f06030f 77
    0x8000b668214010410113a815252440180c030040c2000200e801800e14035644812400400d0042c1541500420300494042d680702c4590f010120b820780b6491041d02c51200403070030034014681c25a40c6a50500103040b0101c0a90380003c039242812901403995400c50400d2198848100c092810b100642e140c0c02f01030401c10785018100390300040c4003405050a120862900c4800050300c0c11401e40000fa0b602200c00e40c810443c1c10000d20170b00401031041c03110000150b65440c0040d4a6218403100300c280c092a1028083e641500300088020b5440140f102900759020409000c4407041003015400818880d0740301c1d5180e50551512280b01228444ca5540b000034004607013580f99902d814141c1102c0040780c00040915551030004041c140e040ca040c401c031450000520780408000302c0d02170000500b282525002901e84490104684030300c09003503010b60040c5401360009503000c0050070001014104a4141a600c4e510400a4502110b2103009000b40c001403203c2810100086103500f0140b07030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 335696510 1250 335695260 335695279
    0x9170705100b012304030602030c0c0f010b0a050d0f050a0302030408060901060e15010c0c03062309070303081b0409020d0b0108190b0a090e06070206060904030c060c140c1b 76
    0x800200700d200c0010100740b204c0301040041407600c81c903004031001503501890544d02c0b864940b008082c03d80082c010001c0078080c68030980b0200b00e040c03041441101c070041050401505000030f001048100c81000c44006400d80500c10214070100083e442444c031960042d99900c0c10304540c1030030003401414450a503818001c00340003c0d440c01c8034051740000741c1089212208624001210990074141c4041c05607034520030080207000075a0401c0c98284207264890f6441d41c0c00c8180510040c1044a01c82d4042d00501414400603119404683c0c11460742c04080b80c11510301791500c030143d8030650180c0640342e40011a071600f188139000e44c80155009003800d003d2450300e10a444408104520708104469403800290181da40d034102c00c00c003908101808110030300e0303102c0010b07640e00e01c20f03118180944a40d80008140340741881c90140301d998183e90301d4a01070f80c943c0d5120043c00e00600554180806022500f05010001001d0031010000038010320021107018800108030703a08005540c000e80300744 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 335697760 1250 335696510 335696531
    0x714130f06110d08131a0601090b04030b0f06181e16021906020c0304081608030306030d141204050307030f14161707210903020f060c010917070510 65
    0x400c090003da2441e0800d000d540c1c3c1d4001c06003010100e50f6000810f88004002280100d40411070101d10031882a00c07480c407090f46980085006005070b210040c0402a00000a100ca00f140144680c000e4400360074084403a40c0740054038950001103400d401c044031010152410384500d84811078001c801a0742042c00200b00c004001e40301d2a055020308100c0036003c8110b0200039460341225142d01d00c100643c0d407a15120301000d510380500001c1d0007106056840003180d841004030499001c0e0318018001d0400500c0e030b007001c1d5004031400c40444020003043c40081d945010b000b20891045104601440e074800315403a010704407a02c601c000c0401c00c0210341c209555107034000e0841e030301c10080816141c42120607240105c1c141005d10b40c0c65069240c082003900800068001500d8580040c00b80c14400b91702c200000c841d020f13000d101c0039502002001207001d0070b0a00c50010100c07440c401001194501603078880c10050203405401c81e2a4900011304002808010710603004c00c0d410040c814004090071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 335699010 1250 335697760 335697763
    0x105070309050405180f071802120609040c120f142107050307051605030d03020910050c0a17030601200c01050a0207080601081b0405040b0109050714130f0611 70
    0x3401a14002c42d91040170540710f0803000c8482c4d42804011080340d1140c00c1583d1141d8440e10244181240d01200300410b111010050094491428640f49440300c981d80c0c030000c20143c50380c0500709442030140700c40301080f4180030038200900140100119015040d0758a88003000c80c0e9405e518014a8100c00a2464400a0b0100803c0181200c40d00a41c5400050600340d045100c0d0f4400100184100080001003940708440d00e01103510803400d1f5142e0100e01e000c19070503403255001391580080c000303403240300700ca0040f07020b0b18489108408075840d01085a540c689180b201d014480c840d5800401044125a03008c1607200ca58258a006500488405020301d580c0e00c0d0741000d007a060000100e2040c045510030828a00244003074000c032091540e5540c102615212140740d100c000d0102082c1c84000e900341070181900540c1c0c080e1079000940c0c40c00740c04500414000d07003200d003000f603406804121052007070301030001828201c4c2598000d0b85090100072840102d41c2c000810301c0344150064400540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 335700260 1250 335699010 335699027
    0x109050402092d030f010e07060206010b041a0c0609010609060b0c150a02071b0504050714160201020102090a06120c0305040f030f2a0611132702042301050703 70
    0xe481010200700fa0200000050255020b9081c82c2c242c41180c50b003003281201504001e031a06148419503000507100d0310100d0300c0c0c1a0901031401e4440c000c101c100441d0035201800010149042c44035030800410700301850030704030b007502e041e41560b44400b01400415103911510008105070180103150014402d81c494490880324400d80705030044000040360350354282c0407204241c1c0c0c8035092403d95100340c00d4010f0560300c540101c5015a01d004005541d841c0520308044068101000381410001104060711a40300441b4040341195000d000d90394551b100e001d01c004c090034190303d8480038010f085521a00b10780c0360f0024a410903051400388404910b03005c00d40030303805030540340c5207400702541c0740d090707440301407404a80c0b00c42004103104805618071091081902c5114110600020601c13520500850144803a030f003a200b0030081041004100c0b000c004080e0601a82c0407070103481c0c006003010126080b40d03104029803c0440c140c1e1403000c1c485c058004c130f00502400c0c10360030710b1110f4070010302040c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 335701510 1250 335700260 335700289
    0x1908060310150e041b1211090103020109050607051c051c090f0305031510030903200715110a0807051204030c05130f0e030904140402062a03120402010905040209 71
    0x1061400884c0910040d4100d071a010b007541c00300040c1d069604c1140315a90354402c0c10589103d5010802a40c0500d01013021904a1303030160342e40320f103460925042042e10b62012a08a82c40c2c8925290210b45201d400380c203609400ba04d0702c5440e01e40488800800061895680481400380b40c1180c0340c1c0052800c040403c0a16091308e8055202c2c0e54007140140e405103010910307540300d42d080442291980c1d05801c59061203100b503803480d0400080d0180e40c00d80181e0601604401d4100910038082400c4d503207a91a0070800c0c0e40b80c07100e0011004d008541c100101002c060b644650000742900a000701040740701d800c507030b0b01c01302181b0701451a112500002094001c0c10310603442031000c4420907105e5081881012000d64041250600802c66585d0306d50090420a02850074103038a4079090503140180c500c1542c014003002d2030011041480150202802c521905940403d03101941c04003040024000542401034032103082d0406000151150780c803540054442c50040241d00c0c001d4550b0441c2a0a01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 335702760 1250 335701510 335701529
    0x90b180105010b040b0f16062009030c01050a02010209041103061f0e010f121404021009180b0a1e08060a05060315041e051b040c02070317190806031015 67
    0x5440a01c0410341c1d51240101f984103003102240004c00740003080d800039400b841c400c0d43c01c2d484603500c260a4900c40c0648001030364142c01c45500111294041c40090804030181d200061901800e00c0c00141110061903441e80d8204c0048100300450034950304c400603041940049007070507520408000c0807011840581c0c0c0c100722400d83c0c030080e9980210030f41c21418801c9501400140c0550400b08000c04040700e0a91045454480c2c80e4800c9008410f20310556280400000800281c0403500004c2c00310304c402d00d90080060140010606050068004140036207040090660b03e4440031500e05540901078550941c54042440642d0354006101d80300d00801c0c54824440303544600385030a0074604002440003c5d0500b106c034ac8c0400c040131840450391003a49140761000c4030a0801e010840e9041d0708001c0260780820700c00d1001c2811103000030554000700c1e180a00d80b1001e051004800e0003a00b0141001c61449010b03c803080c90207000013807002e03601c20030030440441c3c0c980552840008520680088 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 335704010 1250 335702760 335702767
    0x207030209070e190e06010306050a06020c01031109060a020f0f010b090a090312020a03060305191e110619083702040302120606031e0a0209060d020301090b180105010b040b 76
    0x42d511800b1a400d2009001c4410300130b21651440c2c603982c005011503d090010b481d004020a007450840303154400c0d201e05500070048040b282005400030041098007000e20401406501c486503a00001001d0035440ca034094000310f0007800e070161410008450183c456414840c1d005115181c07034280c1540800384180100f115010390809840785a8110041560b8500000c0e896140c00e0705500035000b10380c42102111551010021903080c502c6e03030003000134180c81c40c0c00c0c456000700f8004c4084c80303146406600b04040380300040c0e0000b61030360b02910038000d4180e64409264041a08240002c0c0e00100c2e03003042c1040d080c1106007407180402c04048020500c0309103600d1003825400b99040e900915805411800400d86c44410a0b550380000c036210b903c02d10420412001c0c0c1240a00201002051100142201011a42040b00c490401020076030410340401d142e00140e5424006c4a812900072444401181403e00b1440c002c00c00e050380380e8161f43e04090040122a81503811101200d9640c20144d44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 335705260 1250 335704010 335704037
    0x12030a050d02091c080316031401060e01090b0304030305100b36030a06050901060602030a1403071205040f031211040311010c080f090f121f0b030109030c12020703020907 75
    0x20485014404c200f444120302e403140f04014203000250b0043c1d01400b802c01540c0355202007241901c0500d450021000040401082a02c4c082c4541c04480401410103940740d40c3c648000c030040c1d803c21a025000240c071001405007420018400070041c081d011021841c0c040580d600544500c0345001c0d041c1080d640611403405103441c24145000c0c2140201a15240d003150704001024105c195100d50700b951130080000341e1103000100310340c40c40c072060700c812044803540132501490390001000b50b0306102e0b091500c4006140d0a116803803250380305803182903000300345007001080c0200d00c44003440124601750f0200c80d4060301600740c03030403260b01140e044000b04c42d010040340c91022802c8028018030700480d6007d003540780e4801a10543c88143c400034410381c154000c200c8644503441001d00e5a400c55120314003601207242ca8144071110b00303480841d441c075411020908480c8441d00544c00240d0300042d00c0e00b0072540590311100b170030a500c003c080003411500023802d5118050103040502021400611 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 335706510 1250 335705260 335705269
    0x1406030c090606040f030318140a0308130e1905010623091503040f050f070b0f0307020106080d0e2707050c19140c19060c080f0c0a0212030a050d0209 66
    0x3d000c2c00e1140e9450358030580c0e07031501070f202c01e51048c03828920f8050240c011032101501003503171140070402845085800c0c61610b526405601c4001c00141d801c501260101358101c0040503503002e00000003003180d400f107442800c902100c5044e0024030400020310038502d481d00300c0808000308030340041420b41d522140f210000b01c0301c800e1207200310506900841004103128007854010a26030144c8195840001c12000701c54882c41c0c98050481c6040041c0500310b038000040d006954031103541d000001d030482d100c44220b86000c001408100020740403540ba003ca9040210814541c1942803201e0807480071410808002104000c01100c2080300102c1d0308010880200a0f800c00d291051641160455032414a11070f00d40c8400e10107009440384101c98044c0741400d09500003420880103820503403904002e012900d110614030140c8001a0600801702c00e440810018100c404980e4010300c05003e951042c009084107000c900341c402e41003032203012511900034044681aa20348480160f80c0ca51070380006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 335707760 1250 335706510 335706517
    0xa0201061a04030b0109090f140a1406071b020f040902010507060f150803070b060906150310050a08030f0405150705160501140c1b0102010e0607121406030c090606 72
    0x1084400d400104080030701c485402442901e0060800206903031300c0f400d00805a50840100500040031050078001058a0003100d00342c0040c2501614000446034030b802030344014801042e030490b04480180288190010560704500307044c0740994600040c1e40c0c0018000103051005e1a00441d00d5804501c1160708c604101e500186e0f1000c420460355603000c0c0300b64010500c82e6540c003104065a58049404200042075030300c1c5c80d030f01446458043d0740b041c0502840e0880541802d820080b0f05031452800405c10015601c03c5001d8010305039060f01d007008101d5111070503404480c6a4004111076500845180100c4040e50403d54041801301c007020310b4841ca0344030303140c4041c020b40114084c6048203501c50300321008441091340c8000614041c0c0081c105d061140407140001a848010284010803130b400c91002d03400b905000014415500d00d01250405404842e501c00180030540780c0344d11001d803842404525101083e19486e5458444003003641c0c0c8603820f68035440703000820001007040e500e01048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 335709010 1250 335707760 335707769
    0x50a0908030a2a031410051e0301061a0c0c0d030f0302090604031a040209061f12320717010b03090c0a0b1c0207020604030b07050d0c050307170702060109020a020106 73
    0x40c3c01c44440c0003d801401001d11341480d80820611034003140c14681038440000580300d004008411328400d000b40c080d5800071240e160f68042d501c40c1c00004121480240d01c1c94440300301403c155883c194000418140180e02211038442c1c0380600e000303000309510003688808405c00d41001641c4080c00000902c0c0c502441e03000030442c801d400154000d010004c140103008901c2601c04102c9034884004010904001c0e0520f282044d00c0500da59102c503200740c41d985c80d041f100c2c40d00010200e400b440d03442c0625110a8442c1c544030307140c50781d0b4200070041150655008029141903134071030199509100104106214800e0003030000300101e503003200e0a0000c0804041d005210101540d81c55404448607000b40919074010001901140401110b9008844005030f00800075031400c4e04595403001810005400c0c0c2c02048010301c11202e2444151103260280450f40c1c03182c58480c075200c00002d140c00d50702500908038a28000a00c0200c90b00000c1c19815102d2020b00962604a80d0008038014000d6500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 335710260 1250 335709010 335709071
    0xf0c0c190603050f07020d030902010504120b040309080111040909020f0a030303062c060402071b03081c0b0904030f1110060311030607020606040207080c060f070201050a0908030a 79
    0x106415006862121000c40d40541c40034401c550713500d59604468041224500d0143c2c10402880f0001b82c801c1c1d000d40745041c41414420b04203030321144103c8041003112030031034607003c00b2001d100515412030404001410240024008000c00300740118040c01140b0586403241d4844003c80110364468203922003a5102a00e498030f06a901c2c100100a4100c07845000c807640c0c90a1300c2c00148000040b00c0800ca1500c02040c051240c48500500c002544000c809407650b10700711806840c118642d040c1c003070040d80120501500c0380f42d100c00a074800d8484e090100c6c00d80d894040c29a589855001d17070b542d03101e0380504100b10080401d81083c0c94080000e0710f482082e020300071922451204591180c400d0728042c910030300282d02c01409040e640c95055501502607803100c00010910320b400d4009020091092106604002101d50b01c80c3c9400c03404c0d40e80808030348804007001a00e81d8244143c951100161009001c1340185480388040c521020340381140c1076440b00b00322307500a02e0581d05070031031813003601 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 335711510 1250 335710260 335710279
    0x30f06110d05070c02011b0302060f090109020a0312030c0302071a060102030f211b0d180b13110a0506180307080a0f031403150402070c030606170f0102040602030f0c0c 74
    0xc90007088100d00e104e0403800704580b2070040d950304003c501100343c1280c0c560010b20094449088020b01410010b04a4003151348849031100141c40e45404800110721462101d0a09101098090107481e250108102058418407000002c5900315624403010b1060940d042c4080c0c4038240104e0640c8a4a540c0c0e901e100c8000500704020700c00ea04070a0411101d100145565403281405035485031a0303d526005032500c28031100d01c480301650310103111901a400072584100007035035a03002000040b02c83c40b076100e0f4451070000c140581e4060707a0400c0d00e021114248081e0510b80003c046000e440c0907442101c0d00e016501d07403a910200501e170090044081240ca03541c6d02c030720700f05040c3c1d02000c00071400071f01030300c0104880f100710806072030041c0340c9103440541c2d40c0181424040250040c00042e00c86110f00e000000214800344120000741039a180001100d904004c0d403186028100080004180c0c0304000070041c4542c00b009a4039034600c52880141c0e00c170701001c14240380803070f003c00340780e40310180d40e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 335712760 1250 335711510 335711521
    0x2031519090b030a03090e10050915012709020a030e030f09030d020105040f0807081b030414180a0e1e0c010807030506150307021204080c03010e07030f06110d05 71
    0x200018200d490384030062125a0402d010301d603c400d00f10b00010007250342c81506101c000e0010070031030750240000080c034404555403000248062400e4822028000c1507110150302035034445182c2c0b44004904034144a800078529544044040c03030302c1980c004950100b001960b4500c42e030004881e00003184100c989600404403141596404041028800d200705c00005481d540107000b084e02c41d54125441034031450300c40d21000441d0b8040305088452a000b0032030066081d00030b01d0084a0f81580400031500d0b00d04214401000358400d81e00713940b1500b80503490000262420018075807201c0c1d42039000c12500f84401446240c5034581800c1c40010f410b005090b4107018000900010b0884242d0324140544c031504001c3d01111000e403032041d0000359107802ca0350315910044c011500404148116100901c21070009145500703d50042c01c0150003540488000b85024060426036114005c00782c500d5524565030b40d07640c88004403006000d02c0e2507480500d581c851070400e403402c0102c6081c0074480c92422 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 335714010 1250 335712760 335712799
    0x3040b04081005060109180c050c0a060e0c010203070c0b0a0903021f1404030f1106130b030406110c0a0311100c030b1305160e0409050a03020a12020307030c0204020315 74
    0x2d101000b0440307440c0000080856200342d903c3c004880d1805c240c5000f03010580111405420815070000c140101004111b00c248810400603003544d0140100003410110130520504010320708400904540c4140100d00c0441c9204021000f00c50055007e147d0342c2d070380940300b610486601d0348003039844001a100c00c0d0000c00320302001442e02070303a5581c41e02c43c070381d0b202d0080f2054010382c0400342c045060240c045e00003410b0100d11494140b00140610b042c40f0103481d0040301020340740c0001c0e032607035004814841009205e00801c90b141007000c0d0341b1401c0c86065135000d9604e1040c018040c003000f002a81c0c0c1580f5070414000580c2800d01140305101c021134020025000c2c0c20b04000c6a0300480840708076403034420441c8606070090b1201d44041c44030b02001002102c4182400415543c080e64a00c030050000d10100a54441148a9005802000058184034822a10b54000c0005640080040c503000a5101c5025149658101c0d40180c03a40c450a00d12010040c2012081c0d13000905001101d540e000d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 335715260 1250 335714010 335714023
    0x21b2707021f020f04031b0302030d09080f0a05120a03020c03030f010501020d0c03230f03010e04120e01050415030b03010507020f07060504050a12032304060f0e030604030302030903040b0408 84
    0x75040281e02c06070041c4030224481c1103081e0f06030711814001800001c02c1e9501c0350719241d480424801c403160b16900003030304000304042c074403011490640c3c0c1004060300c140281c485055a100103001a00c0c0d090711a6a1544030003275540d0b12074100090078600c2140aa07054414001d1100100d980343e150003400c65001c0c0100b80240e5016204038070540d2002c234401c85010781d9540e4180c0e1400040044042c0340c108480c013180c4400c4455400340000382c107108403600513500905120b0607212107410a8140179102d005891245010007400110005490360801d084604981d40590309481b0320040c888102d00400e03c0b180c1c80c1e6415420701d8240100d05900203000500c681100c1c0556001940d40e020a864621a500c281360300205460020885056082159844103019081c0f10141d030040044c00e84058ae00130501080c4540d01150500100f0341c003071705c405a444003508021000840d0000042d075181b00090000b0b080640000c0040c901e68010300941b0300030719016182d15140c41e01d0340651a103513031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 335716510 1250 335715260 335715283
    0x210c03050f09011b18030f061a10080712141609060504140f1203040609030c0f05030613031e03021c152d14090106021b270702 56
    0x740504049810860107100310550191154800440090464404d48213022040d001c040b054004c1c2c6800004203d080c3c1444185500c40c580000c0c0e42002076041e81c5a10101c0c025139801010300c20b500900c50354100d00101d400619074204080109000281400600480c04503546d00701c41c0381d0309000a01c845103422441c021019120541244e442d048100d803540100d10800f04003801001950300f0600749104034504000024044c0703000d06d40c0003421180303142c0c09540204002050347c04d041060041c05c03a0b0580c09070911400d44000c0d0351a100000f80e41e00b9010b01065001d5040c264041d08060055103000d092280a15200582d00e0b03450380054025004440c90342c00d03901090117100b00c180614070800070010055854401c0c6a410b100310f00d0b22595403510074201c4980d10b040300d05035880c9000ca88030010b01220f20120302d10b6081c04c0a2044d8013006030b0020065502050b0300590454040300f0648003401d090301c480c0305ca00f0300c01c2082016242e80c0041c1e42030302401ca0061041e0294003144208442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 335717760 1250 335716510 335716531
    0x3020318150d2309070b030a06030501021c060b04050603011403151e061206011806080106030c030201030c0c080405040b01050f0d0504020102060f01050112020c0f1b0112021306210c0305 82
    0xb20b034414a400d41c0000413500703030080d034100301c40070b0160b00380c0360014542115140800084c20703600c0b079541d9402c90344100030205940380b440301050721030300c580d0280001510b07031080d0007801c5c40e142c48042040b502060040e80e030508504460103515460410400554a0a10544001e03078201000344a8034a000204000c56a01c421000180369042c60a40c49103290038a070000c0207aa881c044240889050b5081e01e01e02954692100141d1400240507007400f13180110207003010185184005012110135440312000e12507a0030110010500080907503049400968001c610364104030f004840300c1c0310f104841680301801083c0420404003c0c2d0081d03110750720070380031103429454121000086080c00d00c00c807070006111021902e1420500d40203800101600384c1143c0130648003405190030844188200e400c80212203510905543e4004c54030804491100c0d0118641500324514880b0503209000c0c000a1000300d8500903040d0100d003101c85400c038440c070800c011025400c04020701402090701c011844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 335719010 1250 335717760 335717801
    0x901120212012c010803040b0901020703060e06070305090d0210020a09050405040b090111040e0c0a0e030a051b0f010512100e0411040f0b01080a0b01140406080f0a02040303020318150d 81
    0x340c3c1d4a0301d0141c4c1079031001c4000714209841d00300f00020303c1e8080310240d4114041c00d44000002380803400b501942c02e4248000d82140c0c500044010100c0c5d01c0100f10a10580c0440d07280c5a40c160003040c104ca80c104041d50150340c505003a0003d65681010358441a000f80c43c1208101c240320214242d24065109038009101c100d5250380010424041ca0041c3c0180e001c6510100e400210004014080003980d802c3c80006409818006800e10008070b1050707415410083d2030f850f8001940403400c045c030318100e40c4500740056100008143e07005065842001000b1700001c0b0301124554000c58000b01040d480308101458949040120306000911084c0254100540b03107020014a0080120885043e0344100740c135603841307154601a0040c03090303007410310460b29452010307000c03103000410240c046901d400780035043c046031a210020008140e17500c01841803105000080d8040121030b03130b00c019440d03000100c2c03400740009140b08280040003005580b00060026201d00d140d000004041d425200d0f4a81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335720260 1250 335719010 335719079
    0x30f0d091703040215030a0f020a020a060f05010b0a03111b031b060105010c0213140c04060e030a080406120615080f0a06030503091e060408160609060203090112021201 74
    0x5000c2524003d5105c4000f4031004150044040510360102804401041096404d441001241e02000c020300050308410148020321a580c0101520002c070182d003000310b50b1402c000e001c480e000d0141403004058035428401001c2d4060400d459582c18441e9001d07103a20b10581c4801c2c0d495001070400700280c1c01c0c006410250050101d0b07164102e8034181c65810403050700d0303800c001c0c0c0c0b2010502c1901310a42d40758121100b030b800b0704100750321400d10403c1d2266140e080601c094034644ea01101203200e5801038101c0740018004009440440d94030f401e00c10018099109041c0280074140c00c141c101420080400b40c1181d4401032a42c05240300740074001c4140c50b6904924107441503404050140c1d8400c00c03800d00682400c03213040314000d142541c59020a00650b0002e0700c5607009600c2415168840c40180000820044907080204002d09040043c145054800ba4680c094400143e05100d000c100c9100d0040e490f0301116000441141c0c00c105030b40c1c440e0030070200b4070304040070320a040e0f11040e000303c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335721510 1250 335720260 335720303
    0x31b090e10050a03170c0a080306031203090309010e030708250510021510030f06060303020d050c06040f0c0503030706060906060309020102070e060a0e0a02031b070b1602030f0d09 79
    0x2019070b14040d02e07941d000d80c00c0d6219600c80380b1740024690848901042003020402040c0801d2107005e110303c40941d41e9013003030402c251a000201c0c1350302c0c4142400304140550100f0000403140100710a003081c00c0c9069012000a081011139807011002d409142921031000000310f4284281c82c1b800b00003000d803261503c06101480311801f000f0005a401400351540c01c001a00c00190300900c83c0d049117480755101da44131070801d8140c1303c049581c251549014800c040d01400406241c542900c1c201c0d041c401d5000384036580d00c501820242104c000c99040e1810b0104491186010f000040e00703c81d603e01191410800810040c403804500320b01d40702010810364031901817415210f0b016030040520700e003003501e0300112600c0605030a034400851500044e03025138142d14a0304c0740c0c115103001603d07071a05d1800c000301e03241001002d0180020421060001510745c06810740c00a000420707034000041c4038202a49113105080c1c52104560000c2a265612035541d0010001140308500d4055132540d4198480b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335722760 1250 335721510 335721541
    0x905091605010f030f0e07030c080f0a020d1101020a02060a050a090608130b2a252d0605091e060108031204060b04140a0513030e060901031b090e 64
    0x80c001041800e071070b203400344203400405c014002c254000954034010442c1d43c0c0f810a4a5004451500b80c081c2c040000400a20049600400d20b00180001c006141c0c001003030000040d50040545142c1804860164401c01207a002180c0c0541074540da40c0d443c50303000d0030f580c1101c000b040025001410204035507110709105801106501c000c0890b0054558031454401c500a04600603004240c60329190100510103507500e46800207140b47da87c4000c3c0c083c506100301c9100c0003107080f24481d00130f00002000e0a0010300e80c450405241114500360740344030804c2600c1070001030201c0c1d080405220041401290301c003a00e44164001d503800c5000745032907d0b02c58501b4803a01da1550014440131390700d80c028440071741d403151184c000042c5411040c00001c0031200714003203508082c0e40c1e0b1820030514405a211302904070301560440a0b04080d02e070703001000c906502d85c4403402200003103648229640070760005544e6500740111801d0454881d000201030720200d00c10344951002c0000855000b079140c8214 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335724010 1250 335722760 335722769
    0x908061806060f0102010b0a0e01031a01030804050105030a0213080f01061a190c15022a060a021305130e0607050406020a12120513110a05011d120709050916 69
    0x18003200e546003810440f00350f01006019040d9502c402c031142c050b59448030a000035020700543c0d403102e541141010b170500310503540300211984101c0010f201142c001d40c265011918246400d550746d070340d00c05803180a4002c0d071190f000414002440812100004521900070810000007081580c5e500d40d0040d1180c2d40398003000342e0300b0201300662644407140d600200c00390071039810450420071030b503074800c903a0504040d004a500d50340440c0d0725407500740b1001400e103108841c0d044108861804011b054403181d000e8681800703503500051101d0361140c0a03103610f0041000500c0d00d620f48002d9100345028140c4050b400016002c0e042c001a2014000c8060b038043d115942d0080c18034680c0396a403104603005100016040c01421203000d0040315640c05498415110440d013035006d0440c92401000f298103104465101e44c1002106000340c0c0d07405508100e100c0e00b8498a11740100017480801e400403600350500143e4000c20602080a2242d44c003e58003426550702154910300036034154021110746e5004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335725260 1250 335724010 335724013
    0x1305151602040b01200d03060509040503120a060513020c011508062a04141504060f030f09050d080f01090902010e040b18180f16060507150c09080618 66
    0x81030001d03040c9540449010801810143c50000c1c0707171304c100070410b026002d200c1e0761036006480102c0d103958503000d15001043c080e500e06643d0b007002c0d50f801e601c2e03002d2500c01a1980900c00d000034900085a08840014100507241003c0707081c1c0303119400065448028804950b42c00c000c020420071140c1102c0108581d0402c010b0a500c1e20388030118860001d032001402c1c603d81001e400c85040e0400300c4010700c02040103403262412500440c2c10701001c01400e09400b00d2908060100f0131001d900101c0c0c814000e215464000740c00d11003017802c8030042c001c210020344144038442880041940251002c0d005103241c1d80729800c0c0340c0c2ea80b0581e4080e10b1641c1c80c001d00250030001c0c036422508040d082900c00b110018825100900400c0d8180200740046903000907800b0f01d030b1125601203000b4412250540c4590020700110140f4500700019020307648295000c02c00c0000325203003070003071881c0440c8610a1690302888030640c500401080d441c0d0b18054a2950f01a01c0c000c40d482c030100d2884075500700807240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335726510 1250 335725260 335725297
    0xf060809061003021e04021209013614100506091f0303050306210d0f0c020f06030402010c0c0905012c07050318011e1401030b040b180102130515 64
    0x6003484002d01c60000d84035412617205441a03072542c0c582c0007030300007070020900c0f03c002490200441420343e628014201d0166803d54005160381401509000022555002440c0c9035030340340c500300c1c9400c203007081c648510707000d1840d4855408125402040c0681003c466140847d100c80d40743d03120703465500d24900e40108210b10b00700b000078081c002450380140018008034401d44950150345414a001d40280d0641c0c002d83e04d00c2010b02e400140e1174150741031030714116012103200c0e40131518440c0b90002e0540706580c048000b40840e8400c901640d4a168451400d081c550798135110b1001400080c0125034240d081d000d440a41c0e0b95419402582403d8012404c041e00d454801069945500107040306511404640e18003507403d209000300b45040007580100d1920030320243c81101101c140b82c80e50000252030000400209510780d01c996003017600601105165101d4a8221502d91842d8484041550002c1741a4155548039000e02085407000e440288002e05000c1c04201c1d50b220751800003802c141c416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335727760 1250 335726510 335726513
    0x6030412092126070606060801140306010e13020a0f0303120507080609070e0a060909050a15031b031406090d08061e0303040914041202010911040f0908040f060809061003 75
    0xe50034118400c91128149241c6406400040303d42e9201601c1512400e45801d01001080d500a41081c0101064501404040c020340d002944503030741031107560001c00c85203001c1245094501c81c075126130fa60040050303120595420041c1003440c0c0c58803054000c14070141c2c0c01112200d15005a6110740000c0d680c1074800c0d907560302005402e0310058460010040b45041d0240c1e0b03600d8000c4101c001c1c00751611004221441c0c00e0030b03d0f0507108002c01c903211841c01d0041c8107044040011254040d203038044084003181d9150480d050988003144e1028061702001c064544444001141c0b082c0541b2108064400c1000e22081c01e590041043e1f80740e42d08071151a03080c0d0300c008400c0d400e4054080008060340c0c50f280e0340d201540e0030b07a5030000c601c150941e200010300040165409402100c011030b800203008030340f800c1c0c03122603610305114003840c01103440ea02d0503c900c1751035500c61481594000f42298950742c03111200d0020b44558002c00000c10008404100c0c0c40e43c0016445202d0b00402180e4a08a800d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335729010 1250 335727760 335727773
    0x5040b09060d14011e06080d080402130f1d06090f07120203011b02010b0a0e061c02120d0e0a05010216090905030c19030e0d0c090c020309060304120921 67
    0x40c03601955040f40c807902c0c80721018004c1c003c081c40092004501d40f0441d03518203000741101c0c0b0a07130160700d0390713800440c40c118402d40003820154801d0301100c00c950111041c3c0000d038007400d00c0b80c0304180010315081044080b0360020000444010071041103440301d90f0740d203079466a40c00c401800b00300e1640c0a03008c02c01c241c4081d0001202c030148003500104114201d0070314503240e070080410007400340c0d454114566440c1004800307030000304041c07000e018403402c29002141c4041d070b2044003580c1c03041c41e2280359020b640754820b0005803840080c0444481c1004680d0013030101103030480040c41850a44c6001605620019452100c0000201e00b22100e42c60025150000c00101004850a00041c4840d0814460074400102c48500e80a56151003019501c0c0003848a4503000400b44200b844141107000300b1014141441a110150000030303c1c80b00755642a0f1540c0107a40440e980000000100010800308107000440c810346915402025901e5122200d171030f4001a45a9248950008041020860 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335730260 1250 335729010 335729029
    0x905010e15031801050a0b03150403080712060b2b110d0504140d02060f1006080711010e011d1002120c09190306150e06150c0c062205040b0906 63
    0x203c3c5407050040c0c40501d00700301d003951001c0b1169050213075241e206080600f41404038442280c000e1414148a180c40c0d5005008440c016126a0030041d146000f980e45640581c8071201625244005989400790546400c070700e810b102054070405c1107180d500f00c140a00c40d0280d06c1000d200d07000748a0519118103442001400001d0003980c03000c040311041000c0060520604802e0b040700d0b4083d210f2451304403083c0d4140b510113007a002d10540c1030f00c000c001e50340c3d10a80003a04212103250000390034107a912114092304a4100703410b12946003081c04c540003d08081218840f01d070300001d803035481302e0078030400c0100c2c0500305201041804020001d880e03403629100801e00d1050042c030344910130072802060b0032150610740086a1066480c40024409128442184002d00551405403060726103039000c070391a03548240c030b85807403030501040d283c50800e0180310805c000440586425290801651040210001c81c2070060628070b800001160720304190085040c602000b07050206281c4484d014012141c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335731510 1250 335730260 335730271
    0x201030f11031602010b030d0c08031b03090d030b0d03020604030503130606030b04050c030a150f020c102f040e060d0f03020d0318230a120c030905010e1503 69
    0x1c0d95920740c02411248a800355003c1c02100c0b40040f0108411030700030f42121103e42c1654443d0780700c010425122390b07010310100002ca6100043d07546070344a8880c0d90340d0303d000341e01c001c0010150100800510010001c0c0701c0c5400085660300b445110154800c0c45000d0048010280051b0480b90028000c207002d0001560404005595144d0703d214a440d0351040b6281900105c0d25010b8030b00600042c04003c00155070580812009410008c4e415074400300114070340c1d940500803a480707001c00700705940f10782d043c0c480c03440000c130035200f030000b0405040b0010b24140c00c0c01480c410f800850031540c48212000206d88050000e4291325207401c2a8455002541c010052940101e07000da00c00c1c0010380807220b0540061007a00140b24000c4130102c0913050399648080c0d89141e1000d510690003090f42009030524108060110310078001c00c2c0024039007007406c003860182c07107043d02015800f0312603032048101800794002d60b1a041030b44c2d1120011160000a102d076541d200006495080e0300d6250301c0d00564006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335732760 1250 335731510 335731541
    0x160f03080405210105130c090209010e040b0f03010e0a0c0608010b0304020d02121510060c081c0e0a1212050c0d0c02100f091406070f18030206030a0b0406050103110403020103 77
    0x750041201c4d0a40c2c00441d8646580a4100c2000303040040c840161800760802d20b2041d400d240c05980002d08020b800300a00e440342d529007440c7c441c03a440307208000c405101d001e0001c6c08204008030300d8030b0b907442009004481100e0310301c0e000078030a44101ea03918103a0350b0b008a40c0b85986c680d60204586100d079008281d0740704003049400c2c0fa0702c280400034a00d002e207000350024038518107456003c80101243c0d10a90900c00780c1c0075040c00094054bc11152559801c449815807041aa44214011b100341b6404c19524030400f0a41c000344116080240c51452880c2d0b15040350343d420300140000c1c0d078015500d003030383c421050080c0c031044061a000181210410b104a680301500095004180c80d0f140c2c1d10042d801d687c070030000f42400b03240d030840c940111110004004a041101f0b0003070240d074140c0c0a007000c1200c4c12003060310345114001d5601c025500201041d07160304214110600034286021801d111f140b030060300048a5029000b0078607150740c04138901c0e0801346103400540c0135101780810003031070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335734010 1250 335732760 335732809
    0x409050a021c02031504080f04060e0a0501140403080d150303110708010923012715020a0804080c07032301150503032205060f0a0224130f05060108160f03080405 71
    0xd2301920f6010b800104041e0391200710589210040c081301203416002141040103040651801c05290000c071801c03243c1c0060710540c0d0300403008280006020400d114141c0040000380001451b92280840c6504003101060f40c2c15a580d41d6501401c031460307264002c226088000429083c2d0191604400c100200503002046140300d040b40d40901d284040d403018841850001c5160901131688400c0c100640382c89000c504d81400502d02914240006000801c8900c1c0001c1c071a00410090107040c0041d80e0020740308601c0103140040c4400725181e420b001d080f0f50319105c5170000e07822054029a084400290146103000354981c0300e5454441c03244151990790b02002000142500d6203001030030a0401c3c140ea80b9291429208024240308283c1c105600c04018894070301802244d6591080d0040450245803000e0b901510b02125400c1c200380300586640124400020824404a0611320040040c911903144030340b910010940c881c514007000d405603409200070b00060400c400010110803000441103030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335735260 1250 335734010 335734027
    0x120c131109090f01090609020f03130318060e0f042306010314091c080103051906110d0e1c0909050c1902070906050418200409050a021c0203150408 65
    0xc00d20b506a600081c42c00092004005040040c4180f0300039000c4144150326294070541d0362981400064000c807180c0c5007044a4004041c0196031100c0e80702c0c2d4000b1252010b60b80e03040c000d000000c112040d40c0c05442c00044440041c9094810800148050f401000e80d40b5200d0074206140740000f031219040c59034812035011500c0d150020b80c0e11504290006040300d40064615480c0d2036403100354442401802e10040c000079102182c0100c0300e4020402d1903502010608140028201101d070407076205500140394500c80c1b90075081510f410541004607401225559a0f10600700c805004104c001200c642d002d000b80d450035000b07940c212182540c82c0d4103140100030387c4040b5800003a000400b40e0b121402c204144009406948024042150104280c0991007409161001c0480000b00b4001c10b40007107036003144280350b403200750080140040000d0300040c90300656603095000140e100d0502c02c8810303c0900c2d180b00d00d8060165010f80540403201d41d0190b503071422400600100d44800b0306009080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335736510 1250 335735260 335735269
    0xb0402040504140402040605030706140c070b03070e0f03061b07021810030b100b0403030f020f070f06030501140a0e0c07021e011823030a150b120c131109 68
    0x6100c0409503c200d890500b44100001c40e0001d921a5000760070041c3e0070445c1580100004140040d40d070040c9039500c0c40c92903101e06203009a0000e00050320040280014190311101b40740000b0b009544034003060360b03514109551600101d6103091002469070421014464410203441c019101910b402d2a01021340c860b400000b5045801c05075046010a0030014088441e601f580c1003011000e1003408541400d031072840f144074600001c4d051001c0d000e10364000520802c001f02030510401d0a4640302900d4007a0101c001443d4400c103000241070400201d2440000a01940c40003001003201c000c1c20318004001c046400002e14050000200780912800350312500001c1d409449441c4d140c120000b400000584207402d0150b030400c0c40c400480307080c007056403180f40c456443e60a40803813405100c04200004e19040c041400240220010800814222406e82003800c030403070304807503800200c0701044510b41e0790209c0703100e0641c5c4803190b444981903a0209030320054024040744c66640c6050541e03000f06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335737760 1250 335736510 335736521
    0xb040b1b180a1503020c06181203041b0b0c070929060708071a01090903021b0a080a0b0108190b04030c0311030307080603011a0a0b030a061a0913090302100b0402040504 74
    0x5011940001d52480120424801d0b281d02c0085404402030016a00b01d12356903881840d010800401030000c0170600303206034100b0042424480c03070341c40f0820540303880b4802c5103500300c0491600184a0f1110102e01e981c0320b0300602c200004950040f440c401d1411600c0b103c15210420f44075040311007000801d001c00d400a000b440010b003c0c1c000d0540300703a1040c5d00d4001c582e0303059021004070f501e89141800000d60104110643c19207149000c903210100200040072801c2c1c0d0384c0400c90510526100c0c204000d40c100301c081c12035032044159541f02042c0d40c10398142101c03541004001c00032903000280064054003a444100703000c0d1824100c0342110288040c51907100380c81040100f51424200901480e0900031744000815103442041400080c40114028074034500031030106500c040005512014198020401825174035240c120032240c25000748869401811000d00625400580c0e11054617036000e501307001d0350305034010711060304a100c020006103444049107a120f5003c01c4002915910f90049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335739010 1250 335737760 335737799
    0x21082a01020712030221070905060a0c110607030807120f0207140105011e030303020d180b01031a070905011d041b090f0b040509070306030c030b040b1b180a 69
    0x40c0d40380b0382c1d410300804480d41d14100da810940100210f000c81841c010b400440031001c0c0740446c0e480c0d00c44180507038440840c0d4201076000f000c0890f41c0051951b0101000000501480744030785241402e105210092081c0840070300442c42c502c0100780310b13601c110329074510640361150001301d1084082c0c06e20706907440042c00352905108459807044064080c819039005014880414007050006200007210155034440a0203041e40400c4082540400703400c078000750305d99200010400300940c0b800c5107440c01d00f0702040e00d0345100032a080790101450000305000c3c046070340b5081d6a0900d42001140d812041e19130ba0054030000d07290341005521580134402e040a01e00d586021004a40d8000510b9040a9480122601d8207403000300b10032594070089030103a0304241c9030300038169283d0030141c0103130540c2d61005028070040d180000910003980c07240e5005a12680368511142c03290103010103880714900d2001d0340c072242041200c1c2814180f00e1032082529010f005a20500d54409140541d01103c541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335740260 1250 335739010 335739013
    0x3030d09030e0d0c050402070813030c0f141c1416152a140a0b0415090507060f0c05030309010218030a120323090c030721082a 56
    0x5261007095088500184000000d44120481412a4a50381c0c05104c03248995400749030300003444d105101030081201c442003001c840002e40243da03850120500d0103244124036100300c1405002c140c4e018041d000389841540149074603410702d2480c21302815116400400c0f00d402d09043c0c0c864618580c14132482e0106464140d9000d90640b41c900008040a66091003004005040d060070449044a902004045462140c0c00ca5070f00c1035440c00c90440200d810b002d4a1522944584404104040c0741c2d0b184624843d450902c3d021034034610300001c2d90f80d54036000308180c02c080c000b80045032240d218200f001607986040020a10700b61030b520b0a6900a8900c040241d400060128204820455214262000b58001c041c410141d85400c001c1049010000342050b440fa000105858000e03041e00302d160000581111040c01c2912500b59074201020450b80a80651040042e9070400707210884814055050510b4000e506076461841650000c1c4401e003450254402048100300c503103a514004503940c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335741510 1250 335740260 335740271
    0x504030206060d051005090a020a0b0304020f04060302030a060905190507080f0f12090402040e0901240b160f0b0c03010f14010e060c01060509070509040612080901050c0a0203030d 79
    0x80003410514010b09590185612504030000a02c0000300700603618004c40d00040c80c0c1c0c075240b101c28204081620003951200050350045026a15100214000d0f40301300d505100220282040c0300540744c2d84d12019600d50001e000000103d1029008000f002d071044007941c0340340034284110760340d2640c5804c05031001da000000c2409000010003400c0ca8003500b03000107200c1154941c250540e07480301c00959006450000c216014603442e940c044d00c02428168844800c2d600c0c008102500078002c05101100f080e040302c1d110200010020340040a4528500d161454202d10103840366000000782c001b20b03401095618404040741095041c02d0149410406c3c041e81e95240c00b001f4400d8028030b8103d86040b42110340e800c40d15a1700708280e035141c908140c0341a9102d0101603012401020ba0ba40007d800c60300c15000c0011b46948400207002c200012a010000c650302c0e005500228030788e00000800d010780c00c1005805941c040c0340a40b8000c6002022922220481d9020906581100725500341d007a0720303031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335742760 1250 335741510 335741513
    0xb01021506030307031409030604210f120c1e0206011d0609040b0613110a1709030703031d01060803030a0507230f0c0a12140406140307050d0903030504 67
    0x18010944100a540111001801c010000a071648904030006046c40301a0514566224100041e100540f00080c16071300c1d41d15240c14049181800101e05c0c100310f0341407603000b034613660103030318040c142c0ca01560f41d200c900c1800140b484000d0a500d44000d00380200182103032005c001c0b4042c04070800c422580070b0541e03945400c20082c3c4185c540b00c1e03ca16251071030020044151528208240d00c1504008000500c2d00c94002041d082e170280259100d00c98100060070100e00c0480f80109150031042d40c44145606061402081c1c00a0030384000103d034204010401c0032904c2a00140070003c21000903034000036036094413503b10307080c0d0752000e00203400c040304201c1d41d04400e10a09234020001c0c24a2001441b000c2c541108015254801d034040c2038020aa401c488000603040d00c1c108040c00e0100c1c4d401e1807590401e0414000400e0034403002400c000800746003903880e541641c0c201e4819440f11800ac0e841c11a4814150b000103118408104050040c521103541c1ca000340701941d8001d442c001081e0829 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335744010 1250 335742760 335742763
    0x7090c02010c110d08180f01091203090302030d0903050c030429070503271905271603021c050613060b072006040608100905010302130b040f0e010b0102 67
    0x12416080d040c03004035400010400c0c030104850418001e145007100c5c59941c1c1c030900c002035860035041c450003032160340c002181d0b10805500c00c1c00b003140074420035095210901c104406603000002c0043c01600107100c11429401c441d0420b0b6030180c803034285a403c0c6403428041030300c0c6403c5540f04d50502d424800504642c410086846209689134404e064505405522819624816480103104010a42241d540c0842088044030300020b001441da40a190361210b0303070030203498a40100b6200d0b00381092003005001a0062203602c3d404200d41020107991880c003080100d80d1180b8051003407603001c01c0448450b840040390001c422245500003e001d01b015018000100d107030194054405103405410301c171041d100e1003a202c0b0183d020317040002d40300ca0f030100700703030f82520f60390050ba048580803030041500e80d00800d0440c410705000e0328020085565504a400b601c41c2880069005400350403003003095140c9401100302d0500190001c100c0205c850007070b104840840203000c105940d2106002550741c1e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335745260 1250 335744010 335744021
    0x105090303190b06360a03020603061e040f0f050a14011221050a1101151202040207021e031b01080601080915010902130603150e04020a0b0a0305060a0510020703150e07090c0201 78
    0x1c06e883c0190060b0031030340480c449210107000c07140b007001507d824001103030700c1c0c284036510a2000b82042c401a0748100c06d00001d012480d15111081e8200000200000090310038001c07070711500d140204040e40b0308203800b14010403032101642d6040c2502e503100100c0754480003108200c1c4059a81c1913031100c00f10700c0148503982e40440705840b641420928081c180d0454a081d00b95124072102044804481c40010b0081c8600f04c1c0094200035a442d54030f1103102d20313070b00a5501c40030690545125091100d411103003007140100107408620351b20003007140c55104020050340060702804413030f040700c01500c090741c171803009030b02c00102d003a00081c42030b86411054041c40c00a103418101403160300c1a00c003050021003843d005203840b1404a100050a5584802c03400340102410b408440c0d071022401030050142c0001c541d42409a80c05160000d01802c091280707035a50f240c3ca07405002c0b0a0f09503039602e851610107200075860300f9201c1d035074044440d0052000d000280f07400c0c280080c0550704144061b00350380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335746510 1250 335745260 335745367
    0xb010602240a18050c04110c030307120b120703050106090c120f110a09030c050108061e010201110a050c1207020a030605100906170105090303190b06 66
    0x10041c25400c81e680310655001000c072000284910311a585500b0b10700020f10555560070001d09669010f0800e202003c542c101d41010295010b0103004411300300c168452146400c868155841000060b014a10501c2c840c100e02180d608007103854240030000403549015035080440a810241d01002006024498280100010300c42030081c22480308016000c40080b1001c02211900e8512000b0211050351052180101030b40100b03490748101130008020103014001165501603824011400c0e42c09403030401d119510040003112507009042510000712413400344e090541d0740701c034080014078900c0000341c02c0d090515620b643e00d480d104411246498090081050040c0c2c0411025000d130b00c9605007a02525040040422107850780b490380d0030043c203c1d074441a1120300d00b000c0800e4020449075810380f0300181e030f00280308036141c9503560345e242e1000b03640300f03d40c10710720190b01d6444020540003804050002018141006010302059401c024030f40e40d841c42082e10586542c000481e40c0244075000b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335747760 1250 335746510 335746513
    0x12070e040608100506041a010c230d020d090302150c15070f09090507020a0b19060b04090c080c0301150306080102031503280b0a020d06092306060702060717030f040b010602 76
    0x104802030389001e01820080c0050304100124006d9014041101200c51500030500c281200e0b0f0305181d00ac164a62034002d08250050151b0450b8041443c40b841c4404241c0e50006e100b10307080e107682541c10a00d0f0b07110380c9412403503010b00319110440c070301d1006032684200d00729260135401002c4201d004082c140c450304961000c615010a21103100c0c0c0c0016488a00c0750704c5040c0c103c40d070311000da5401c4050302d800c81d07024000f4244180400c1110207007002c0c0040300e0300c20303006221499005209507000c510803103403645070310000c0c00100200746030543c130014003c007030381400641d103134440e0406400daa000329045041c4054000b281c220b5410100701100912181010981260542101c40781c5484154131001d8134000042012400b065038a60450701c0d0705071a06420806a55a0f0001400cd1300e442c910b4102c2d00042078031b80a01031410303200b0451140c43c00804452510703005500300a91500403d405842c013040244c83c0045401d03480c0c0045018000c070400c07412944c40c25140000032004142c0180085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335749010 1250 335747760 335747771
    0x30b09010603020307033e07060507021f0c120c030209130b030f07080d0507140f010c111207080d06050603040503030453280201090812070e04060810050604 69
    0x1c4819a0950b50740107682a5180d0341f00d008680e800005019052000d040289070000f801440b40d0002403030304d490354131086c884000c0080b051410b0201c4444604e004082158a100e00b001c2d007006034000b00c0070700c05a040050420401101245150000c1805140c0e0aa52070212100c0c524080101c000c50041d4240205401d0303080401c99602d50300311004000c280400800d2003801c07c140c0c034400b20003039840f1500b1901c0e600074165102d4060944107503a00085182044030224401c0041864103010b4a01c0b103800c3c0c45c204159441c40b0181d44410700a0740d05030340e50711000c120360f50b5040007035010302d000e00011500d9080c141884200401240c0d0712140c50b501d035850522940304060310980041c4640001030800d01000e0b049068140406501d0b01c0b0050000503050480700c80d413010320300503a030100501c15103540111300c06900300c0309107a0005d42304030010310003015034085040300e07194404030703e03d001080001c1e5440400c0c00c2d41e00941288866810411546c25180e94034851540d00100440e002d02c43c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335750260 1250 335749010 335749061
    0x105190812090301112701090503030909040606080d050c07050607110d050715020f1b01080f090309061602033007050c03190312060810020703030b0901060302030703 73
    0x351403145411070300851102003401c64081c0d07070070740c40740015000e416051565803500a05030440c003200d4032071152801d070310310680c00e115510441c1c6000c1615405402180740805400401c103241ea00280300300c40c075586415002ca500401806001015501911402d407100c0344543c1d0103050170b01a80100740904810700401000c100c0d03201b0341d004469800c0e00c04500c00551410000d040081d19040034108a081040c058040c982c005104d06003184d00f5000d8502d800c5080c1030009480342d0480320380e0700048070940480c0c8800805503602d41c10450603000c4910744610000400c1040e040b24400e0804040c046c85034106606061041c0700000f06018080070540b90850084c0f100a02010040c8032600d42c00b0804100b005010800c803406580010704440e405109620389904107030100e0f0080380001c42c0300c0144580140c880c000d5005a0701c10b0b402501d00301010001c1040290800d00040d410941c82d5660450503445021903203029001a68001d0f070380345007448014017541c100c0810001c03014400c462040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335751510 1250 335750260 335750263
    0x8150307050103020a02010207170301080c01081306020a0903120201060611061315090b010905090c22112205032401121403030c0414010908060f060111070e01051908 73
    0x4064941c2401d0058403080440000c03802070007044002454403014a504c902d203c42c1d03070400f460403074410744221203020001d04011107036540280c07401c0e03400040c00d40c0c03200000b40c03194000e04600026460030301c01c25a80d80d00c0700010005962145d002503552002c05004d10b903400313001895640348202c001c02d00c1d0700b081344110101c29001c038800381c1100039031400711505c0295600203c00d019007012101c10596114181d450083c141520800118400c03419144a242001c545d202030b8004815600c9405800c045c9518016040944c005401001d0802c44000702d01501c0b070058003101c100c814441e0f6880d081806052174018042800d481e00e180c1c903004170040c080032110243c10348622404843d240d80480c81d02030308140d8503c01000701d6000c0402000f16102d5a28060811186e2040e26045010500030040d82c84400500030b1280d190081d00009612080f07011400350400d40c18503040e080c1007a05014181460a10b81000940c0203210004101c2840c00000d4071030400c103c080c4509140c0c1c0f9010030f25 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335752760 1250 335751510 335751523
    0x405010c0e0303090103090c12110f0f090112060b10080916150522060804030801060507080d0e0a0204180203150702070509091606090302130c081b0c0d020a03081503 73
    0x345d0426450308281c0d020803e11230001c600a11301419900d07404140c62500da103001420101c064002e10003e45c07e60364078501012140754100010317001000c00d90a1958950581090400582c2c10302c1e1143d071004500e4442c00c40d00541c002050313641d000e15040518089083c41289005040f690001c00c0381413084201180074032590301181e0074895618180d000c0f450080e41c801c81c40140c23004c00304102c0082c2858104213214031841c4a41d0354400942c2c1c840358140c4203402100d1025018100602800821f44003d0b4020b5a89075900812511042c4c02c03940001e05035105581000000c0c8021603009045080803c03d6024040c0b044031480d19529140100a548443c40c1c40741620844a03036010482d401010710801076904e03100082009480d0f00e40d44040d100740d5461108a01400380d43c2d00043e2008214890340e074446105039030b40340c815111201124000130790f100300304041e01340c10000e0f503881d0b10b01000691082081e94018045c0303003031542000b404051000703040400e12070241940304032640d00403552 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335754010 1250 335752760 335752777
    0x50402130f061d040b07020f0c0d060207021302180f180408160812010914010b1c020408070317030f04170c1f0e011a040207081903050405010c0e0303 66
    0x1e802240050300304082c0005030302c00d010010500003515916034075401414030440c010b40c107495241d00d8100c422030740c500445213443c0c101c0c1c1008035a50307018a03081e4040001c1c2c5025850240c180080c540003c0c450309101c0c008050581d500240c0000000284c03080201c1ca807000700c480c00284440140843d92001617a401d510040b040f202c0014100719884043d074280b408680400d2a50080926010809910035540c941c1c034172011400018807148940070f03c101100500c0740c5445141d1801c0314000141c0c10014825680700b2181d68403480a900a201500c014400306005181d218a1405c1400c01a800717070b50300721a0074200300200080c0390700300e000c2907030040c1d44450010030183c90180900c455000e80084050a07009451006403c48012141c0400240684c5410080f9400903548203088a0800701589002000a05034401600c0c155001e400e1640c05040f1051609006a042000c104000041e000200350b8650078002841030910074400c480005080000c00d0041d6000045e960303010382d002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335755260 1250 335754010 335754049
    0xf060c110103060e070206100e04050d110c04020c16090203092a040905060601140c07060c0f08073008160e1009170c06040605071403070f0213050402 66
    0x40d510003030340729601c200020401042400304608210200a445a80640c1c4982000d030a100005c0740c211700100f2080d0290754424010710b03800030380c60426581c1020000740b045050084880b01149611240014a02481e50700003a0900500003802e20004a0450b00410043d61042c02000720031000080d01c0101000d0304101c11060700710842002e1841159031510300c0c1c01c117060207181030030820f0016195000d15008d8035511003500e4801c0e24040c0b42c1c000e4a601c0e03245680075000c1007103070a0041c40c2d18200380d40030302000b1412008646850549600c4501c08954900c1d1141c0000340030080d0f4a481034160403010741e4003400b4a040d40c1c2c01002154060442d015421210440c888681c0c000ca04406141c40044e0008120a100c80400b8108440038421416261303400c1d2941020700ba000304e40c0041d8060000c1405003001e04100d400ca420b50081401102d444038072029807584e01800300301038403a03141b0518609400c112907105112800181e01840c4802d6810403042c000103070341b60403503c0d240450114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335756510 1250 335755260 335755283
    0x3100f090b0a0513090c031a07140d0b0a050a03030503180f060c030c090301050403020f120301030c030b06010212040803090f0907092d080c1c080a0c08270102070f060c 74
    0x4072401c001c0030410b030020b08210741c990002082204040407114042a0102c006640e5a214003055550032402440b413039822104010100302e030b80c80c0307034403060124cc006004554620703100e5002c900e40c409160003d46c0460301c017004010121f00c60011811b050307800d007005428040c4d0740b1f5452503900d410203418110982e1000c4001856809000151800c0c070b84010002d128504260401a481c1c0691421808a900680350b0041d0040b4610b400c990403258048112160980b4544559000c01d00c0504114118080c1518540c104000c00d0b0241014040b03038005075954058110812010813038030603009001700c1d8030104000199030400f4031035040b1000740d104103028560580c481d10707021090042c41c00200036a040049000c0c08005040d480714102902c00c0030041030010582c42070f100c0d501c48000e01d248410845501c03400e00c00d84405400364412404035040c241080d4080000e1031301080340030203046c4841e80840c0303191b9041100d04024803501e0040f0b840d19041040c0100302c082c0d5004040c11102000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335757760 1250 335756510 335756539
    0x90b0d050c0f07150f0204050d0b07110a0c0608070c03081f08030c1e060621010225150b0a0501440f0105010807030b01021203100f090b0a05 62
    0x100100d409852807031040b00c1d520310480c81c110410385000414401040d280904450380360303070140300b210181c2e00010411100c04100c0e07500c032025580700801c07a03010040c60040d4205281c0040000e400014403800340410303918107100004004440050180042000d008140340102c1d811048082c0c000c0d40d801026207040e0b218a84461b03d1014541c80a41c0380d110018484410240204140503d107150400000b90141100b50099440c00c1c25244a6072100c0c51013030b800143c045001c005440c8a04110003d402d200f10b01407998940030348481102c07442d03800d1170200400c0291070540072141010070103040204040150110f0410842400b4150500c405082020004148041700010703030000403010362102c1c1c512400220301d0305072a0101c041c0c1303414001c02042e4000b0920b074189040c0c0e14182c1d40c3c6110341c4d41c0d5050480141400400711415801005000340341006d60350000c510503c55120070201c083e10384503c8034503000040d400b441c00300e85003142c200741e41d9407442c408204490f802c50b22203032240c050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335759010 1250 335757760 335757781
    0x20915090703020405040e07030201090b0a110316020907080403090b16080406090f0f0b09061b07090b100806030303040305070302070801090501090b0c09130c1b140c01090b0d05 78
    0x111400550200d4203100304a680d66041c2c0080c000c0d12819541400200b41900185507521860f0000a01040301c92030700b481204440d6020300340030809803504910790301c07103c0000c07402e5911150300d440781c005071a030b40c1405504120842c107801030380700d1501501078907181d240100640d501d03014103c0f40310400980c50b0b5803209074041040c402034010300101d6596660300301c0603044208c14400c0414040d00400c001603e1400ca415040c11140c8130f07003080385803540030002c000f02580311020300b800244140f0303103150020808005a50280c0a020000622a03e0740001c001034120803981030003c20400c801044070340d40b030100549401c1035040c05d01130380320a280e2a0990404c10b40d500544131661070110b4a50074040150000034006000780000c02c9a41c50315603808503284120b01d64150800c04040e104550002c1662013801050400d10b402103400310394140000700e00c1030080050f11100340d00a2007a100750410b00800d031b082c0302c007400c2945040d490310440c0d101601039045a00317250342c3e0f102c0000300300908 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335760260 1250 335759010 335759041
    0x12071b050601151b031b06060905040f020a0519030b0c090907090905311e030804020301050105030309090414011b050315010201061a030606040e040503030a0f15030209 74
    0x6014094504542c0c4960f8a02da014020000510001d000800c40c0c184501c0415080c0e40320940550b500504c1070301c4000c800c04403000921049807100d680b40000100c8412034454580603038801c80560104030540d0041048060050300304510a6180003052800d8100c244042400c403503000e590307498283d0714450a070049001700320f10280c0104600003040b04c120381c440e41810aa5142c604100141d4581c00300c4020082d01030896400c8182c3d010048800e00560108001c00c006c1c80303400205564848070380d5001000c502c441044021a824500748400c5240a0260358003500c0281c0041d8101080f0300c00050035503001500182c902d484885e0801c403400007e4000d1b0100e0b00c0ca4501400007540f50b10030082c00f80d07108841b840d082900c443c000b461a98410f00981c2c0440f2421003d805c4803894a4260b204e86034009041036505c0341c0100400a840d81d010511903101c2d60040010755140e00e4440d10440c2a60300c45090603284c0c614082c04188030740c60012007001a01d4050717030b1112a80c3d403424907100c809030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335761510 1250 335760260 335760263
    0xa0f0602190c120504060906081317090a0b070203120d1503080a0e0102120a2607050a0f08060d110303090916020d0203042303071a0703030b0612071b 66
    0x5118004007296141c0020819075100e100c0e4110304420300c0b48260443e458000e5000780e20004001c0441040000e201c1c5c5041904600018074000001145a0350740b20b0b40c0241c2d0341078002e2008086214040d40c07500c030002c00002d0002441103442c222283d4000307900c1d0f154404644140e22000b14130400300050950040000d480702d210703d41103da4032801c0041640d005080303240300007503200502d601c0a5202280d450070340030f14103038481e00704500c0c50300030780f20104800492401d44c105400071080c4501048403040c01b82c042d988603241d0341c85080000500440014540e18180600001445100c1d2107600c0100c81154104450034800c0d0b103010300107411486108150350b84a9505428084003507038400081041d0041d07a0211044420040004d030713242c0c0070758801e10a14500108590f040e1107540348a810b843c200c02000c3d10940d68079003601011a003040c3d01c0c12820b42c0300200301c00c0209a01407241d880548404c44110b41400032080402c040500000c02c27040c100a060311003186003114841c0e1080740f05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335762760 1250 335761510 335761537
    0x110c0607020105010306230c1635040e0601230d1b09120b060103060503030d020304050601230d0224031006080603030412050a0c1e0510020a0f0602 65
    0x14146240d0090182c01c1c2804141c0380e00c4c1c0b400800742d000700769000005c6640e2800c1d415102d01503841c0c0201c0542908400403840300782200048840c00590110880920345070751001c00103545001065240d60202c1e10100d20402040810040c0110b802079006642e0024003403074808150421514504030000c001041866201c0c0042042001002150041c40c2c4503292800c0f100800e40c2906011603052280340f00710114080401c4041011402d1008015803004040c100070400035a6000031a1466121540469a00d9404018030041207010310031207005010100321400c44120300c0b6260170600c001418698807078030342d030680c010464a0b112442c1560b03c0c034001d02c0b03504a109021640209a004660f1151820f0200d000420002e008d03200e59409481d028004500303103414103510380c890320391807401621140b0031a112400080d0f035000c03458001e000032034070030704220b4402c6000e088101d401e034002e00d110314001c1300b208001ca6800549014400d4100c00340d45265202414480003e00c034001029510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335764010 1250 335762760 335762773
    0x9060218030c091303030b0d12080403030b0405040309050103051503030a0504030203060901020f0f0a0e040f0641060708040807030510060f0314010e070e01170f030904110c 76
    0x1498005480001190020740584280455900c100325a00c9001c6500c403118100c65009600420701c81d0b401018440c0000d000304400e000c2c55200d041d2031846c5c0b00c10300e10000341d8182c100300805505000d400300181e000d90f401d0001d401c0683d00903084400f81d000e024101640c0f0340001d44055140d0b114901203400c05025030381d80c0c1d0f50082000780035600600040e4001e102e07900100b01241c5051088403400c203103c0d0304d4031b802c1100313092300710781950b110703001802c2040300110000c0e00c59030708c61040c00011440740600082d000d1600c41aa030041413028114404e0302400b9195941001c241e4100c1444100c0c07203104800d8440c54080040d0503801500c90207000c100e008070f0042054440019040181c034054011542400240d0100300140e480c43d002d620a102417032081000065598600300da40840d0030030001c6800d104501c621340ca400b240b640720386100c9050b440100081d5681c0c2d6802126080b50b100504484c204203d2150b540c5c0c0b045c802d50302e004503503410300d403000d18441c2130580d0070104069061702c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335765260 1250 335764010 335764027
    0x10e04050108250812091201021804060e1b210405071703070807020402030a09061b03050603030909060d0203030c100f0c051c1109060a02152a0d090602 67
    0x41d03c141c1c010484030540504019406881c00407003c4008a8010700001d0207903070f5450f001c4001e01c1d0801e03030741250013805880201c1c02c0341d0020b00180c1400e203881c040000c44460341c01c0400081d141c0552100301c2490150b0148055544c0091100540031300d00303202030340d0b5418219a410680c9100c033400710301c0d0b20710309401d110400801041e060b049070a04641a0422144880b0702c5440e072080610090a000041050707000508041d000303990300038440c800002e8030709040d8a0322420f0b900b90000d21601880c0000820715016018400c0c01d42007901540190305080e200d0000c03500c0148080d00301c40c0306480f24002c80085580c1041201c804042810036203c0c0180418032020142c001c0c24060700ea4642400d0180070694414000c0eaa00f00c0d5140d180e000d0404880341d80078009210941a00c2c072280030400035000d458076a58014000d6080581c020103081c0210444c042c4082d6028050010042c140c04880082d100402220340120034030880c440c0c0da0f0041c990400700100651a0014411b600103d501103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335766510 1250 335765260 335765263
    0x140606046306060e09030406030507051c0207030f02010209060d09020a0506071505130305030103080a110102180a0905090307120509041a13050f01090b060708040f1e06050414010e04050108 83
    0x16001c0c070400043c0405038990309035507000300701150403140d29481031004004407442500459001031050802e1031406041001001c0038221594480303642d0b9400003031500415030b000107440c3e0416024402141803194500004005200d03421817410025199400082955120000360000b8200180a15581d20072440e21070200e401c0c06056036a0140381000082101d40b007025520703242a4140c1d07540c1c1c5180e0865440754920340107590000c080140d41ea07031801d0070640034801003c82786010a50300c1e800704202410810400066040300030b450b0b007010203010b204200002aa441c090b03018440b4030701407045143c1119076000742c4441c5a0b21a0424254070b81c84d58035848c0c00480a842965040c0901e14003000404c1520803c5d1054202c801107003004000f18400c0c0d6010380384219004140030b1400e8460344520b146500590004031020704051410072031000600c44e9502c03101d01c080b03c6040b90303030b1a00a000c1e02130f010b588103a039110940b00e01c00b0061a84994003000042c07400400030086c0d5610340800d03e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335767760 1250 335766510 335766701
    0x40606030b0a02040302060909150a0306020408070609150804020d0b01150801080a050a030e0f13050609010609080304050906040e0a05100b010908072114060604 71
    0x690710740c8049004208106594000c64003503a8020f000383c0d20b010b81d50741c140000d500d00202050283d83d56502d03174559995842d10203500440c01080003507201d81c10100c219080c100c1542c44a020700c080b0100400c240d808860f60a02506500d0170961415074981c004943c1c05015018001d00da04804000481d50100080905440310503955641c03070319030780f92030845940314117500001d40185e00000d62080001d10980701d000409001510080ca2210240c0c0402c00400d101c0904050300e0b501c403000c0103802e00b032240200d4014071041c507281504902d0700c9280c0c0e440748900c0c09114051046134000400640f9a50466031111011070200c400ca01c030700d81811600c41000ca0140d54100f41080000c600540c030030124601900c002e800500049490040b07202c110361010310300322020107020220300002c1822240d90030344048507400644118a070510801c1704854140220440400000d84600406000c01100e04020381401ca001502d41804900302803191040c461008164213400d411000c0142c0c41d030351b49 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335769010 1250 335767760 335767763
    0xc0d2103200c060a020a0c1b0b0a0e10230f090d0510061a0d0513060608060907050306040809040b01020c1c140f0c060d1524030b010819020c0604060603 67
    0x3d950310740e00d03404c4001091384581b0142e00e0014094583c208080f40c44d4002030b5080d20359001c203400c00c0c941d640780c0c201c1840e0800c11840d03003c110a040070a22504004000c0000e6955a103020791070b0908485045440249040ca00501c40c0c0d4085107502100260717070200c1e52100c01c000e001e246140c03000c0c5006641c604240e02442031003800c003e8000f952041d954040220880d44802060510200d1001c0c04020180145002500700100a5a8010500b18401d150107010b140c0040d0044c2d20746a0398591908410307a00242c02a80b018082001041c0407000340c0350034000407140401e03041c064000403031a02c0043c1c5956988240102da40070f0b540400c00c08800d94843c880c252540d01c800c00c141d860b50f100c42c5107034161411900b216065402a10b4402d00500d5080450080003d21480d06c8035000d2a207103844c0c10504a40008107002440000c816085605d0400c5501d030910000035484d0000700244800341981000f80405c80e0304070005001034040d6001880f102044410f00c0c0740500f0701c070f0040c0100e03120 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335770260 1250 335769010 335769013
    0x3070b0a030f0501050a05040f06030f0f0201020d18060305040201050706050c0c0d05090901051c060e100b0d051b0102010e10050612070b04060c08090409060902030c0d2103200c 78
    0x4000307202d9440340500b41c100e0300c1c0207002d16013051804040c0f1000e04098510b000301c039a40c4440100000358030480507000785004002c00311000702d29100281c44c04c901a1030001c140308064200c4050100c1040c0154180c4103035180c0412a0303101e034070050728a07000e14000103112504081c1041201240c1d00041c01045032503c04071940580c090324159114421444080d8101240d0310050019061929244a0400ca00750320400c0b4038849031031300400c03035a0703810241000d90485841070034408000e01491710750140c00c0710b111140746c80d1690b4440d030314180d0340c090901103c25117400140680c000c1d0f100c0e00c2c8400e0910180e03100f40701807102c4040282004c56540b0f1107070105603001d4251102c0000d885041d1801d0081d52461309082600503244481045812624120704010740100b50b1140d000700900e8501c82c0101068030210707481054108804843c0f92406001c42505141c0441c211515600c120a0302040c04403031900744030400c030050300c2a0001003648440c542000080030b110b203001007001a40c0c560 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335771510 1250 335770260 335770271
    0x60803030f1f080a061503120c02010e0915040e010b0a06020f15010617040f080d05040b060f10080a0605030123090105060f19091112090d0804140a0203070b0a03 71
    0xb4034440031180a016a11440e8020303000200010696404441c601c8860100c81c0003c0d82c0d40d55500a100c4500303800070000603480611203045503003042c2d12013203641d402c82e21542d040c5090b03141d0201c400514502e8912030368584000e5074045100b9070015443c00e0020301400c0485490302c4010b503980030b0342e41038a09940f0654084180c1d0265640c00703607060742c800d0781c1c0b800d5185100100c0c550510002800583e401103807800608002401d03a0028103e8001003200840c080c035150400508074500100b505004012000d0064007070b585e01d2505000803803030380c144030400d5119000358034000c00e019000395400d0341ca0400001c002e82503541e036400421501708040049a510340d4400e900744c5000303076000d42d0003102a02c2482c00d140340400040440859402c108100d060b5120511010340354604228494484002001072942c0380e05000254481c44030b0300140360b01031403100b0003000c04a00500150030002200c00c1d09a9855090004507110398005044403102504c40d0015401d55125400a9002c80d00d001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335772760 1250 335771510 335771551
    0x70615030c290c060103030f050d06030b0702061e06010c0c0e090105180a200d0c0e090c0409080313151b08070806010f031a09041203050609010311040f060803030f 72
    0x482103030500d84143e0302411440e469a5000d84425001d403800500340b000502070f08600750b8851241030010340c001c8041c01103505020401034203141000d04084510b09003052040348414184100e50b401c070070280780039007070503005040500c0090074a0f044282d02d1a10582480b41c1c281c01504198051035003201d07041d800c0007000d0407a55036092088002407513800c17a502045180300e80c502c0f41d00aa41c2020f080300c0e0041c4425980c1040f1012150000c1000c0c0d0b0001e81030045030001001001074042d030070746042051150580740d80180e400010081c4030300280004080d020080c1a82e06070001406403501803005603071440c8074945054051041100141e46c1070005011144190040d9010702010303150845a03101441d000c03070141a00b02c0b4420080110071100608944400302814880c074000e01e030048680044100040c1030700d2001c2c2049101d04091401400031a800581c1c0d220030110440d0006800000d0f54a803001506040d40200d145000105c200107255200c8600300c2e10961081c0308241c00007044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335774010 1250 335772760 335772839
    0x80a1d030309070f0305191a04030f0206060303180d031e0f180e0f04030e1503010806090319030b03070f090f110a020a0312061a0a120b06070615030c 66
    0x1301d210140843e0300203030b50301010a0b00c0c00da885e00902e010346c400c024910350240841304280d02c10342d401c400140710b00020140081e8188903180d0080340c2100590b00c2c045a01c0200e0010310340c054415031081401d050600101400340008011a8001014950407500055005001308005c3d656041c00300303008180d882c4011a007a06500d054440762000c41d080b5031030b0f5050a4070351038402081101800002c182d40025555449141100c048a000440d5a0b0f5030500500c2410000d010b000c0404a034400d004c035803401900d0039840e404090203445c1c0010310b41081e800292030054140c0c80620b00001c4618081000002500b01030301c2a040d840081c0800d0000c4000c010051003445100001a0891004040082d20501640c0045680e0020100b07850b03454001d81c2c080700c24201445980254000b03810b5006541044c2c0c900c2c00713501185010840c038403401001ca0918890180c0c002c0c00669103040002ca82802ca40c0ba0030055034000142c41c54054132600284030303d8036414a18001c80c9041d151410031a0803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335775260 1250 335774010 335774039
    0x150d050f01060e03120f071104110403140102040609030210090e0a05180723040b130c0f17040b071b030f02120319090f0f06050105040e061303080a1d03030907 70
    0x400174a0501c1e0403582510544950040c3e0012105003020107508001541e4a010740006111140c1105985034610b18002d0345150784524542d90030b90040c0400c10115030070407a2001129019100320405002c0054110b4800b40c1c0b6803c0300700000d8602c000e01442050b41e5008074403c0480c01380031803440c2c40c07030780c07101c0e503101041e00c90b4104680451310015625211400311118502005d440415070107180ca0010302c00346040c01030664013668440c8000342140c1e1082500889005034144105110000c2c40065501c103030052003e00780250380c3e80800d2005108440144004070003520441d40d03a086403400409140740da04d060710051080381c008004a8131a40110b80c0900c1100511607180c00405005070301a00c00e62005403052003400d41040c000c600900c6152006a10520380081c180d8108010001110f49500c464802680000300700110511100c40c0c0c51070b543d416051031100c9580380300204000e44030b07003c0300c40400c6540d4900d030380c84041c001000d5409903800d030701601e035155211143c0560300107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335776510 1250 335775260 335775283
    0xc0c120a0b060f01050c070e040605011e05040b01050d05040b070f050408030301050d050a0210030225020102062e0b041404021e0708090a0308030a0608120702150d050f01060e03 78
    0x98041c00440c90a1514820b002154001070400ca4200200950164140a0a540240002e004600c100000c02c20070707205031800b50044030441100ca0088130003040c808002800782500850342d5904a83d100ea0040050b06d02c1c000390001c062204c0e1a0601d00300844260588010703000c2000f04403007031500350085c01a01c003a05e110100843c150783c601020017055144150303013079405024018038039001d43c440082291090529071400b6a80d04901240304c900035001c10b03c1542c904130142d024200603070303002c41d100da04682e0070914441d031084440300c051000d607121104001c10300343c0c9010004a030032040f000340089820001800ca107050100c01404241d10414101c00f009141c0e000c8035400012114024100f2503000b0b11426042c03d54040101d0400300325908181d9040d94027108200078180c441c06544042c15207280900b00c1d251601c8424140c500449a00034031070401c1203440440301001c00180c85d440170103c901030001d82000c04415072800310a00034500000e2680c00003101da810006584801d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335777760 1250 335776510 335776523
    0xd17091009080a0b04170a02060115050313020d050f01180318050a0b0c0304090f1a03120301050d08160b1605070305040315091a010612150504020306010507080c0c120a 74
    0xc0c3d8007642d55400c4084000e00031141c2401500d038038090503c60030040c18581c0156001041c42c1d5041520400c0138117000080c1608001c4104100280031881d03900211040b50706407000c41c000d070801e2520394141103c24014210540c0b81c0001404811460850b4a80da85d000f40c480c600711310000e04195554001c203000f0140c000440000400140481a0007002c443d00800c01356801c091300e8214400942d900302407130881d00b40d00c1d08101f1404000500c40d501780520221f00400c03e40688022002240c0030500c00e0502c514a072050310300c113010030b07082100c03042c11258000d6080083d403803522101d4041c007903c0c04085600250007844425005d001100e4180740c151300d13042c0c1414510350707030303103a12814802910001035150a2020006100e01e107004492008081c100020366050900040c0300207100344014400c40d00b0007082ea1695002d1004210940303005840c003598a81d02d44006950b94030034800000e2480c0d20024242000840114186507050411698001d0140300c4d440f0241c2d80398003016020f001c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335779010 1250 335777760 335777773
    0x281b170a0f08030702030d060305060a050f06010e1903080318190506040f0c08030a020f060903040f050d03050f030a020c010b100f0e12150a11130b07020d1709100908 73
    0x2c00d8004014507449400751045914010081d00c0c0003044d039060f0303841110325038400414490f6607a418020143d100c0d186207001c4001d850220002804d0382d01c1c01035524080c00781c5807840a80c000052040a01468000c40c3c00b690700d08005a4030400082c1000c00310030a40112074541c204404220b106c1c060460300f003401042a0b884940300c5088000d90ba41d002c0b1030340b0001764400140031800744041c003d205007a801030f04989603900c0036281050b200030114040364004000c144202008000e000090311005d6480402039011460161075902c68224003070303078804012080000900750b80e001051000c8600700203220b10b0380c1e03140c01d1200c050302d0b40c6410000302e10b481c019004c3c210b10078100c56800c0c001c018125120740000d00c2086090014900c1c241e00004511810803000c101e0b10701030000c451100e518514074014080304500d40340c150a0040010410300040d50005654950740560310b902d03000400000310850b103030030100081d8000d8003618004e466694104141c940200090b80c00c880d00400035000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335780260 1250 335779010 335779013
    0x200913020703091703120a0203040b15150c1501030c090c030606092c090c041a010504060f0e15070506100506040b090d0501061512050405281b170a0f 66
    0xb19004c41c0400004640f1003032040d170842c03c0c02242d080e40140086100140d5034102030a22249450000b0319110921940810215090b107070060944240401c140003240c90b84d00d030180690802003c11441c14807592010300100c207204002e5180300032210360003002c10006040c0d1106030140c58840c8915000300f00c504008100003500c4c80f07092280700e4115a00c03a014141c80e0541a440644162904255507200640b400040c0c1014482d5294560111040b104030349402d100007422841070f4006c20040100ea8045001c8050040e040c01c900e0034401015101d030614051481c0340e044c0c125030b0081d901882034401203000d00c0803001a00d815140c0c081c3c03007249018182850203450741d03c620310194200542c00024804644284501000b40070b0360300c0a81b94050302420b00a1006140e8080602175502d80014000001d03000a00300240080055864044941d566004080c2034a207803000ba00d0024885440325801d41100e004c10140c6000d0090445026400d20000d96030b55000c0c5002000800700209d00b40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335781510 1250 335780260 335780279
    0xd02010e01051210080c03010615050705210a031109010f1116090b03241f050d030207060224010b03151e1005181320091302070309 58
    0xa05011060410902e031128158889a0203481144c48140d03a0981c1e48052120040a0100211845045000b48110740c10007100e41c00b4901040400710510500052003004c000080c813241481102c03482010b00d0a4201d074900b0321065100c01d030710070002494502c45d0551401080151085010180c0d0340c3e458250300c0b4542a14240e96804964115220310341042510041e2841004003a00d144800450811422000c2c545811b10740026034042710005841016000050035030301d540189038071900c1e1505026503446505520043e00410b822040303002100003450380010380352003101c0d200e500311020400b0344944083c103540c2040003240d1002c0e51200401c9440c401c2805540c002c4c00d03c980c40001001c1060008070b4450700401005080102190a0016894150507403052032a060501c40c0c900800c1010180b07155100820740d0b8030a50070a140e0701d40742e40055020203c40c41b0064000c05c0c00fa841241201160b401420b401c3c0d00c141c0b50a03543e0781c600303c014002e5070360255142e1158030025081c4556030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335782760 1250 335781510 335781527
    0x1b0a0e04051f0c0f1809060f1401030b0d150b15070b0708100303140c01240905270f1905070b040806070f0203130609050405060a0b0f0c190b06010207060e0d0201 71
    0x2481300d101d0045e00418145c02e81d11a040041c9000c3d00d030903540c1480c1800c0400d4078143d854185060603e4094240302c0c644032810726882c10340c0d1015500c0304d140d1150001c0340042201c14207035601318000c0c901c0501040704402c01021440d01940e60640255213003d8225076080c07084542c1c2601c1800e00800b000000d002d0303070350312030280c2c911500030382001e8000007010300b1034104d2100f08101c5d80c0346d16000b20140c012004114050a001c07402404646411103000b84240290418200d201e05604404201e000d01808240501c00800c004d0b184886400344040010b641d0b08503041d603160003103500000b00000d9103000c640459500ca00541810b0f5036030007085d1000031240007040b055010030420000c4550440e12140c0c064400c80d00c0c1d40c01c0540c101420302048a038010030050141558407401d002e1900c1d90300582d10034035441c00080707940f065410342c1d80c2e00741004544480c40b12104030321400c00300810081901d100b00001c0c0e0803654610b950f03260460321301001c03540158004901c101c2142c09540b190005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335784010 1250 335782760 335782787
    0x140117060105060f07020a0312271d09031201030506071d030d08220c0e070c02031002310503010c0c030c02010528021e0109051b0a0e04051f0c0f 64
    0x201e004540d2511000b02c689040c0c2e28410000d1482c0e40203007041e80d9601044a00500c5c2d49a02a82d15400c0c00c0d1424bc41d025003501d5090075200c10400981d080d0780401c102c0300f400d070544111101659583c40d00d1030342c420046d90610041204050549441d02d0600a02d203c5180024010036118441903010b5a51600c0688602402d200c510813519001c402404415001442034072901c1440f85040110072140c0c0d405860748007009240d441040141e60000303001d03a00007016a00042e0703240b00300140c601c8a080c1d2080000c0301490701201c183c0130203490107510411503400758000d0100661041c0111a68030840e003005000c680c0341d1060001551041000c2c0c0410500e44c50f1785840d280d582c00201446a0b160000300d4010b911104040c00e11241c080307102c01020141000a111007203a5a0704c1d05d442c0c17844040d1042011031040200b20142d5036002003500102612064142c031420142089a111055110703508080d60100b040303421540c0e424401c002d02d0341c041e995250b18001c2c5218040b103030006502c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335785260 1250 335784010 335784019
    0x12010c080a0b01110f160b0a080a1d070314010506010509031c030b0402120603070f0f050105030a09061b26010b0901020109020a0803070605091203061012140117060105060f0702 78
    0x110050400041100c40740d81c2940f50018189100346c40a6a0781500143d000020030003010f20540806580028009030031040005010030f8010b08034400f400d4006068078006501e20a13440000140701d070300001441c4408041c002803080345d82e51401580d16100352108281c05510280340803001041155180c03125013410319012034003d400200140aa030801c0c0071800c03418000d035041c441d46180402c007502c01401d01900300301c1c210b071522a184800b44401e103d400d0500c00c002000541e181030a03440191160f80c040810000e1440b2990890340c44420070501c1404a040e9000b00201c2412042146000c040a404610050313130919041c07841e150004520700d81959212065000180e982000100c041c0c02c040c401191204a9402d011041e21400303012a02c4a410460751488400c00010072170340d0116050b9402084d0030580c030000c0310085050a009030801e490618162403c0980028442c100e03100f928010b00343e20212420191146801e20815600181c200042e0b03c4816140380506240c500081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335786510 1250 335785260 335785277
    0x2100f1103130b250c080d3608010507020706020d05090d0f0f020306160e0a0302030c011103120709030311010b010c021309060912020f0f0d03050a0f091112010c080a0b01 75
    0x944103000b80101c4c0400b144d074001180801c0c0500001003100b00c0c1c010720249070802c130492005481d100518141d404a000310500800d003000000d0860038600c005021440c003c22140c940b080b0005c0d181c81e150f00600005024144080c85000d204000b40d58003490f00a200e4041120b083d5280003804100c0700381160000c076030071007035005642e0600601e0b02c60300503480039039081900c90303100402c1d64860401c0688520001a0705002507140040c00303943e00b0301d003806c3ca10f10181d60003580500d14041d40b03a003220b0001c143c80801030a01d51080804040300e200e0340355480800c09640c0d40c5400c0ea040038140c980007482d000c030700c40c0c00362900400d65150399030143d40008410b00b0a444440640b100d4020030350354402c5018401c81000d504000711181d02c6282009010541003071401140c0354416801c005003010f03120004100c910489900408480c030090404120683c5985044a0a9420241c2c550301c90264401505186003060056010385402c81d558110650365081c40b01d0004c4c000500f82074100503200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335787760 1250 335786510 335786557
    0x20a050d08181c050c0f010c05060a09050307080304060903080123012001020d150e010b03070807021608150f01080c0d0510021c0606030209010c0206090d02100f1103130b 75
    0x24403c0380e01400342d805826107545d01d00500458030010f00d100c50401ca01601404042000440c107035400c110211000300e0340d045941820b0745940645c0001a005800010501041211560001c80d04901c02d488514403a80d175000f812003014181401c102c882c105903044110369608c40e0f03182207840700e07140300c00200c51641602ca00307023245c02142c82c909000b40d4900303005075190b400421080c000c1030181410145581010801c24441c0809031850091108601c00f14078114024004c0980c01104d8155041c041d030781c1c2e05842503031005d0f502101d0101803036080201e1040500040c065050b110300314014a0b210300c07520107000010b110510300303541c2e0b80070f5031080004864403800100030402a98624a00c851110141d90045607580d40c0035400340b510400c00b0182782d0742c00907450791400350101c0b16240c031102d40b4008142c0b00035915030001c1d4060103031001c03502015040b0340035024095207540c3c0c025540580c010429942c0c812078404c0289c1c0f0641c0c58080000f40c0010005000aa03180e04c031004074030701c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335789010 1250 335787760 335787799
    0x403030905070b030a1a0f0612040c031208070314040302071208040306060b1c1a01050f0922150509011517010f0e090619050c1b010207020a050d0818 66
    0x2039858032174040d00d400009010000c1d0780700480d9080c504403884078050741510700203016440356402040030a50b0140001b4180512440c005000710f0b08003045a9110408a9004110942c1114a0f2000c40d18001c280e5200c00001180c8a218a40c941c006198140c04c00040c01c5d00414008421102e942c410080800010181c2c010200140b01724040306071a1025800714011205407009001c14140c900410401c02c4404070140050107203003030a1180c0c2d074903140b5400e06076034440c5c1803003d500401521014032400d07442c8654180c50002960040052011054442d21110340f2881400c0d0f0010b0a03030010300408000440c12188460f141c109182c1c4503940c9410540d210100341d00c120040e140740c05040164407031680b1100e80c08803501c40603103c00d140104183e03070000c407101909850f0a0352800012240e83c0d80d54100ca503c80d50042c210f40d21000b8200800f4043c0d0710240302203019180d002c03c0003038030303003050250316041650040c3e080c0d080410020f0b101c007812001c4000a03a20005407550200311401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335790260 1250 335789010 335789017
    0x20616050a0615080d141c020313021c0305030a0c03240303030606030204061b030513090531121809020c0105010f0f0608040c2103170f0403030905070b 67
    0x71407400852a0300103d080002c8090a0303621203a40d603089050b21100d41e55124154088000c02c110300e42e074560300728941d98034158099000c80007070580700000703004600181c140c401d540340f8401c884600004a051403980009005000020003058050000c140c0c136003025045600c01c443c4520300002d0b405203031500c20201e480d46c201050b02c0305074040c20510034943d16000714005442241015450503140400c002d1825000c049035080c2210020000c00c201440b5001b200d040107c040d900321a0607444d0314407c2c00600003928000c08080300324000b10401d51a2101031068014182104401c0a40f251510700c079030307011140304108116001400c0d4030881e040046950240004500061302c03042c1e01d000160031181c040e00840c503a900002c204020303c0e20a013100c2c0080e0b0360340385400049500ca610706180304002980080031059203038030700c841112092014025100780260394085c21401070a542c80000d0100341d0308103d19800f0b0f400081c01282c000c1d04420801440740046400c42c603980d402c528190381 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335791366 1106 335790260 335790263
    0x903070f09151a0702031f0606180501081b070c090f05090a05030f0d0609050705120138070b0414010b01080f0703050c0c0a030228050703020616050a 66
    0x44050081f2a10200403114885111000003076203c0940f0081c0140c20004500540c0882010f030703483c0c810b50803140c041c0c46143c0d054035492a588071412441900e803400d0fa034100000340015050301c107214020414568002625601988450305840d0b010388207011070f60102d24a840466404800c99a984c4c184d50030041e520752402d402c81d07003e800f0701d6210010061900d0100000d49410000504040380d925072070020b02d81e22103001d40c00c142c0504a00701c0024081500b141c00200306001e0600305110710460040c02c0580980d10544072907402c03141190085521244848c4c02c180034000c8141d41c00b400d00300704542e071405d401d01c0090b2880003040e80003095102c0001c14885c003120300c2101e0121810380c06a4080280704d040182d0744102d86002c904801840400c0c0043d4403040240c402c580075401006080ba0078916001c10502d500071501a411344405002000700042d8204050f04149 = true := by decide +kernel

theorem cover : BRFrame.Cov 335611510 335791366 := by
  have h0 := BRFrame.cov_init 335611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335611510 ≤ n) (h2 : n < 335791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
