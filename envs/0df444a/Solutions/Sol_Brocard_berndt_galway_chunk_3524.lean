-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:36.915834+00:00
-- url     : https://prove2.me/submissions/c91e6c04-eb7c-4c0f-9c1c-5ab7661282a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633633093 ≤ n < 633812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633634343 1250 633633093 633633101
    0x110c0d080c0609070617041e060b0627011806081005130b010801080105131403040b030f04050706020d0909050612070b040608060f0307061d0301060303200109111003 73
    0x7403900d009859039414501411559007403640f05002c041035904120a484140f040c00300352003a50031800e80c050007041d101c1000307a038009961088902c5c580c2c80a002009032500809800b86498104040c801d00160380c01e8048400d11514840d81040380c001c0c011110941e40c1041c1c00215807103400c0542903601c1e07035650303860391980d160822a0000450050240f1045054101d40f40580003a02c961039182d8036118064240c4500700c580c40c0682d03128440b5070700001c0c1000c2d140200c15202109907410540c95060500160340180c8031006c60a610400b0b100601c1420302500340281030500044c040002090000b5181c0c046900c05c0c0508195910000360310f40e202d005e119000d003081c8405071001140c03a0108035200303421900403100041c2d0244001402400e04807401000200c004004100162610f842107643d4112118241000d94200302000d2039a1002d001d4100a11f1094a504002c2140b02901c50003410021400118913810900e813040450ba460115107001c45040c1c802c00c4292150501c154090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633635593 1250 633634343 633634357
    0x22107030e01051509070809060601051605030406050702120a0203101a03070f140a0f09090804231e18130b01030515130b070e01090e07120c110c0d08 66
    0x10794280410400c680c1c1c0880000c03141c0380c804403801d00c101e843d9100d01f00c0740110304a41801c01da6004001107a001c8d07010b41c01412031030700381681c05054420030396500b40c1550029402407000c100c011605a0461031710403c8041d00300c004e4002000c0c00c3d811b0360002030761a90441c0b0400c004583e5441e61644603542c02e1018448100d000d070440341c1d03050b0f55681358085a041480782c003031840ba104c00034580034580180c40078219000c21400c100d0b05800c0c13482e0710000740a1003504589020701004001440340c4030201400c5000003828000340e01ca414501400f03503120708112000d8400c218608080d110350360303480190480c8050355441051a42d11000a8490110784440c090b051050810002003042000940c80c0034011843d040c00303059890308080c200f820824900000d1020f030011000a51152260f021000320190524240d5410750b503a80b545040c506060794a10001443e02c41487e8080b503450040b2013040e0b0562038007255941d0860340300740d02c403034041403480d119044042d146010710080d48156041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633636843 1250 633635593 633635621
    0xb0a0f020a0e010207050411030406020d02040f0305011b1b0f03090504110304141606080604060906090f0b1e04020c0f0f0706020c0108040b0f0403020f030408071802210703 76
    0x66005091000b03001640a52451401440b07084004192810203000d0079050812044140d41551290340d07410010b500f100600c622125400c0c00002001601100044000c50103440001901d951426200c5010f00b04c00306002c0a1003407941d41e40409440c3c044000300c4a40c2c00140e000c0030020203250803640140d075030744242e90280c10712030f1a0255031100d070000c5000e540b00c4c540400b15a4051107909445950000042594469461040182074090100c0561004004000051154617441c149003202c807203801c040c22003a91800c1d400c070001180d110782c100056040303401c400800326030090340d25441c80101856001e1a0080b48039070040104200f8540281c0c1030005031103452041d4003100741c2d915034610034100180708130004405194050614240201c0d00410080c42c03a9803000c0d9005031406020340210110b206048180d50700c500e05001504c042c0845902402030145000718020384034010300e0070480e4040c41089442403101e05180880d0380d1202c081142d6078070b940e407604140c00a1021030440a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633638093 1250 633636843 633636847
    0x80a020a02190801050a0902010e01080717190e010515040b18010314060106110334050f010c020f060115110a0803061206060f090901060b0f04080d050c0a0b0a0f02 72
    0x2000500d5000d41d0010f03607980d90000c12a95441750307046825903502150290100d002c460000c2025482258110360120041c10b007145041c880d440003698850044542d04070b0403c04c40c0301da84520f040780c0540145403030840d00030302050400d000c41080200718903070020310495079141500d08644841044441c0684041d240001660756418488600c2d050034640324214006c810000c1403041c0545484a8410142c034001c3d070800d00b601c02d400c1d4031444801c60465030145035021664984403820400f1203103900c00d00240185075000f900050964000e040c01070195001140040d00c2d000e40010b00078115082e0b100300d8071038000081420f440b0400c1c40701e00143c860003035091100071321410000440c01482c0641d00b0501400c409655107448030350a0703840c6540254100c07411140c518000c40c4a07608551480f000054680d03491081c0e880c0d940c003202d855102ea400200d0100451700c41400411400e00e002d041891600380c803c8903e0741c49030080c000041420b844031020646070005580301d50150042618115 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633639343 1250 633638093 633638119
    0xa020f010603300e0f0a09020d0e0601060c0b150d020a1d0c070203060411060c030a02011e090308010612020f07051006170a112716090f03080a020a02 66
    0x8003448090141c03984030001c050b103c4030158401d02012049041039940f01056420b10004005030041202d01207a0700045002d00861160203030310060160300490300000071245069855182000380507400401400780400e207002c0490a0302c80705907030060945121808825140002542e000f101c018085c1d04030410b040003107940048821060452030380c005810800350b0f14041850910301c0b48400094050300b01700081030008001d0042d541c01405d00038011424560f040101c02d03d942c118182d0000140e445004610440a0782c00500240c84000030081c0040202d40e14050318000041c42240100210b21018a01c0ca1020f54103035410225820400c69a44040303080241e5206aa44010b09010b40350490005039156402d84c10544400080060400d00340d25481e00030034540e034840c02c2c50300001c070b0004019690a100b44810104001d12480c080c1e2410b103101d2a40c01100c0c00c000c20010b00040e10010301152103a0510402140d41c0710b0081641c0c0c1c0030046049013007a50149000b50000210507080e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 633640593 1250 633639343 633639353
    0x809070e01030f06180c3c0504060b030403090e0c210603010f060e070c0c030c0b2101081207080d0c0f032f0306030a1217010509060907050a020f010603 67
    0x882c034144c041c034414464280c031250250300665803e5401030900484185c100301c6118001060a903462000c1e12051516120442241c0d02009982d0001046540003100b400b0526091007210050b200d02c0302c1c210305510780b55a018018030075900500a4154210000800c0e20500f00e0441d542454540258400759003c1c1c410300c0b80e1303140c0558400e4403d5003842240c0f0303049001880341c0c0c0c08450007152001560b440e448002c2d00c08080142c000d0320803505445020020881400e100c074000c2000024240c0d94500d00c40009240c0030070305042103545201c01c0d004000c080d0000a66842d079030290140c981d0f8455071450141d03082d104524000e03c129051985010b803481d0801d6680400b0070383c949040c0461035140e0300e0745070342c0c42200324000e2002240c0c98544101d40d088030051640248090100c60080b140c51315030b50301c2d01d004a0152000102c2c0c410350341c00311521200200c0d0042c9004d86215400b82044000942e90070390060050080040c003040b000c01d602e00c00c1100410442d6000002c01480c5c1c0c9a042c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 633641843 1250 633640593 633640613
    0x102041a0c0307050f1b09040c090c0c02040e0a120c12080a0b04090501140112150f020f0309070f090608060a0903091e03050d021c0f051215030c030c0102030a0809070e0103 76
    0x1400c6c01c001d40518412981c100714805c540703d03907449209203c5c080e040040d01801400d509000d0b800300049c049108006803070398842c0088284101c030040c0700d4007a0b01d00d801040c900101d98010200141c13083c1080002d000c040e4108622481d40c1001e5540ba55103d100e20001c11a009041ea0b03c0340c1081900018404103500442c450204800508031981e225141d058020381c5c20344006100c1d0300040035007410b5200d90b6001c0350a1296008025103811110a610385098100381c0e605a02c0e81c00c4640c08000360b4440114460042c9461041440104c0c0707040f00080c0ca404000b80040d10a9844100c11000c06224034042409849400710b981c120410341e03a010f02542640d8001120a0b10690b080179009900003c0c41480752808480056041c0b024403100302e500c10189a2194144403040c400b9201d850380061348184640041503c0c82c0000311030a080501d01000891880c0c00383d001030200c20440d0741d0210407107078030740100d0402001d2a2a40a030040c54100c03598040c910280b1000004400c002034120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 633643093 1250 633641843 633641863
    0x39030c140d02072001120b18040512120a0605040b011b0212031c18020a030332190f0e0f0d06020c0303091509030d050915010f0501020f0102041a0c0307050f 69
    0x10300c15003215902c2c1b0120044840462210341d014180305094000241209404c0383c0c0a07110f182528544840300011203c0c030742100c80c0e0368940c89880070800070541da40f84103400c014042118140160005840042e03d260303550702d604001820310b20513841c01c2d501c54802c100320040c4c40c8011260703a04080e500c1e904507502d440c13554035022801d204142984003054801041c2440d001441e41030071a14664003900d1200004203140040402c100045420704d24488403000406010280c2650b544003030469452043c4440d80050700b4400d142d00b160420307a41c069440c8400d40d20036034145001c00041800100d0102c541400188260b000180e4424a1603000c030196002c0c040c00ca0440d0840441803070116206517044508000315402800841000d10342c2c1c1e08215040b0b0622829100304815206801140d80c50903040040310140d404820032841d40d0401580d02d4045551008506107070406072170b180000029101c00505807000329042024003030034000c80d0105070b4820111030f400c00309030503103e4607043c2c010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 633644343 1250 633643093 633643097
    0x2010b031e070909050705010e130221070503271f020d05010e04030c020f0103090f2102010c1d030c0d0b1b030106050703110139030c140d02072001 65
    0x180300041c0b0302109001e5038085035030245c0502170b0b080c2000c0044583c030180068a40d07020801c00402611000b81d032009007605c0c014281d00f003403001415801110384c000e02070041402c2000810410a1200482101002d1101c10060741d040310150748010919010404426443e00080b032a40034204202a6004000c1100303141820301141c0e83c0c03000c0031118920103d034040c01040c0300da107000c0010719001c1a00044010141800030351503030340e52507060300c00c611382c00100c1d141c1003030100044520020f01d4003561168800e2000b031201944011004165680440b0b42040b580c070140030488140d50f09000c030116121001e07010244620740c50501c0c0181480948e0003000441d146c49003990280300301d1701202c0c181d03112501c0700b40c60842541c2e41104c4000020b03218a0803550b80b040d8000741804110098800b4410546c07004600c800141d90003002c05180c0068030082c14900031f2001c42c016004642c082800481074074458441c9100c0c04100040d20407410000e04e0030440c5c43c3c0d0301c421540c4542c24000e0009082e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 633645593 1250 633644343 633644353
    0x141c03020715081b0c1203061804050c04110301050f0d0221031903051303300c08010e040c0501050f0d020301090204060816051b2a100c0305030c0a02010b031e 70
    0x1100540e000f417050f8048003849801442c0403000142d1480000d60704260094401c95400d100b040c089030300102c0a8074110741c550024403401340d50303250501030847c0030005001c0c00d929652410000590450718003100c180221000001507080d9900c120000e41d5000032610310301060b0700c52418680d12a800040740300101410202e14852039842841121310481c004a400700a00c07480b9241a9110b80d400001e07861f034030400020340c2059039100c17203001160306c0e100040400c6010f06c28002802a82c0142c01201d0075180c90070400021070007004031142110000e00b040ca0341e40c01e44014040c01e5202e96540c80c891140000000150760645900400441d07240343c0c2c1d83c000544032401c0455241c17594000784e1000840c1808065140008160410a044026000c950b030040c0040864401c1400801034151005140300c600030b514108000342030004125482c00c07203040d6100d42d6025049003c0038020f88620540403e05851843c000d5110f003510181c010101c40c0380c00010000c1400b002d050120610340340c054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 633646843 1250 633645593 633645631
    0x5040e0a0c0e0f10300f030305180109110d1a040803010302041b0206060103020d02070501050a050a18030512040c05130e070609080c040207021c0b060307141c0302071508 75
    0x84503000d00305490101d520054030041d5004242180c240304000440380c4178170300080c840050802c030040c2c0703540c5120340c030045402c1c58202d2484424940358581001103034145144500002c004d1031115075101c0f030071103041d540070320b090030112100d010b54500c003880f0312240c000380014480b20001840c1203901c00c0303409020700032034400c485040f50000319484000d40e0007140458240c0d8080d8000c0e058602d00403030014200440b54440509413041592010701c00b40e82d580c24480f090100b400f0305040fa414240038065121030310798004009109000428100c40140400f040400402da500840188801042c42d8043c142c14400c0d04000d106000d501e6019101e424000101e90740202d10765012158000c01403d0130100c0c42d014400690f02c03805040364015030090703442c801c5a0244200001c514011078810340b03189415410305240261a400202d1407980086c654615a5a640801c1070036060104d41c603200b500052805038540209908a4070fa8503071140300c0d5401a90b4803040b945e1140c1c4a1103007040405070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 633648093 1250 633646843 633646861
    0x2010b03060c0702100f020f0709020c0d0f0504180b0d080c0c030c10030906111902010b0d0b0103082805090102060c12040b0c0c0d031a09060a05040e0a0c0e0f 70
    0x2050f01c800130341010305030140245460084541d40d50201960055514014050540c82d05058441d00100e07040c560114501c652118100300c10381540d40181072201081207850f002419501481c842d81015558420380d0b00c001548070313000341e081584064404142ca40792450a814aa00490388941c124410320229010301d140008a141c00e030b4502820f01200e03071a02503c1140039080e1040c0035a00652110b000c1461202d150b4018524100d101e0b0801100098540009003521240c180c0386216a01174050700002c112442140c41c1101c2d801620303150788103410000c807200b041e2041b10f80c642c1d8840014001f00081d80060040119040036070950b4026a0790703405c3d68205000d42c00c086443c910a9100040c00105540e030715507001222035118500f003410300a0b269180840d2000140300003078031180d21090b40810410324225028049400d0903441c507101e004100c4002040c07003224801c40e12003000e031072510b00a000741500d080c0c0141e40703c41004d845003061180814181c1b014121600c4200000e0941a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 633649343 1250 633648093 633648097
    0x20301150320240c060103050606010f050c0d0f0e030724080411010c0c080d05040e06010e010c150b060d39261503010510061202031008030a02010b03060c 68
    0x82000f0000c9a926000e5450007141500f8980f500c65040010001c2d070000040402c2250f00a40c807d000600452904034001002c0900e002c03c61024004240014a0540d8000c40e100305503554a24041913003000000d4200c480c490303107402142c2c050198107008502403503155003501c002080c07080e0118a405003a4000c8070546800c44018202c200c2a492805540d8411110401c2450103242c8202e081500c510000e030800e1400f0302040049503001500708420130501c040a94050000d0030721030b0102c8507035000070306803c204020041c00f002c46554150600d0550390b00c020700001000d0015030701d84160300f1070980100840100b500c20603029024001d00c100d07169040b40300c0ba01b0705800001c02e03180320b06015141f0350f0501030f00c03088240d000304003034007900c44c4943e00c14402c0307610200149113a1b030054285421554040d010b05c0c0d100c1c1c140c0105000c1c0c103812114070003280018180069a07541d82c07200d5510356600540008900b03010004140b9422641500f007480f0010702103040d83d845032200d40c0207407854 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 633650593 1250 633649343 633649403
    0x2060f041514222015040602010905060112120f030204091805100501030309090b03010906020c1b0f2d0a03080c01050a0203010e16020a05030a021e060405030418090203011503 77
    0x200d5004484d240d250400400009040100030b030100520443d601020160390f0003079080f8400503035683c08082c00740301c410044a40104800c80582c61059950748070425034141d180300d82e005114058010b401c44500c00d80c101c500a0220b003400300003800c000500c2c01d08060710b030441035500703209801007501310400500c2282d041340d506445e00d10205203809601c4014100c0e08030a04c0e815583c03030203c4400324580380018841007240700080d08400010f40340e405542041005590300a9102040f140340e0303610349540c17074040c2c0c0500800540800d090944120750414500048941005210400000b00406140039005500341c2c800280201e988244400c003c9005c00d1050204410300030b00032032100741c949000382852010703170b205403240200140c0b02e81c3c1c41c5030700c84000800180e002c0c180030b814a2030012185c0b600501540007030440381c2402d40320f40c0d58030b028078042c2c0710306401c0542807a8803174946540280342503a409070003032095030720b04201071042c03010394441950038030142900b40b082214454220101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 633651843 1250 633650593 633650603
    0x71403030121050a08120a0e01050601020309040b0f06070b040515040f020111030d06080d170f0f090307120906030608010c170a020706060902090f03030a02060f04151422 75
    0x342c862042c01d41a40c08030020040d1868003807074a6000c00f04800e04001c1442c0781150040304910304290000c5000c0b42d4104803032007000c1c2d02d00b0003808821781c1d01008a905002044030301042042d2560005402150b1031440c841d40060300040b948100034008540510450060041d0b0300e000720030403000c540d4403c0440d0b006000701c21080c0c071070006601440810b00048286c20403603080504180c12481165440c0e003010701c01d0742c0143c500c0240e050380300906d81044006140e81c101241000100d00c1031062020341071640e5040c03010001840b0060070801e80304220b0300103081040344914036401501440c010300801002034101040420580c03414000c4401d80c1c281961200f100080014186842c01c00c041c00041c2400d40810807000130403000e02400010300050000103139034100690400101903001e016041c02600188916620245c020455a9000c005185101810b59951405030520561210706240c020700d04101d80900d01c1010704164490741200484810300d081c1c451b42107031401201c03680240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 633653093 1250 633651843 633651869
    0x7030b0606030414030a020a0501180c0b0c03091801140904020919230609011e0611010f050901150906151b08071a060603150f180c0714030301 63
    0x140c241448401580d02c103000d806240070055030701e4a1103080d90311111442005900110f40803051180c03c2c8904030007820340d62012420807043d56200d0300c03559042d20a0800c081000701c4c1803110506c0c1881102c2c00c1e148010b004183c510301c03900344403018410a01620003003000319141036000b418036611440c0100d0f001050521695202d840e400d49100d0b14001040b1503540b40c0d243c4095403000010300c401c5507807280c10241601e15103e01440b080c1c00c3c0503805800440a1100f00200400701c00d030f40703d020386900d446c2410031280c1d03c2e44040e014141245880b59400c2c44c040400a941c00d040d400422817041d86101c05100380d13a500e40c0c460646209000d07008086030580d01017050350340101c0050020b2102d0715441c880c0480c20341c90f01c2803250800da400359031400d0500005556106a207041c41e0348601c003192087e05505161510903c00941c0d20701841c00740b07441000d0700d43d565950300e00c18a412650311007030450503d42607207140000e400040007200c982001c05c2800704414400b200b640d0680d19080b180341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 633654343 1250 633653093 633653101
    0x5010503150c1305031c080a06210f021905010201050601020a020141030f13080304030806061903020c100506030a1112060109021b060601080420090f100807030b 71
    0x41d02d0f0348524281c6040020282001966807001e2094001a40202040308818900081c0280900c68014500e86201e45002c0092100040c0c503001480c0e14040004002c2046aa80ca8a0307085112641d038041d50250420001040003800c0c0c0006000340d850aa0017401a43c68400c010ba0781e44140c828000d0103c0c14810303020030303c0b541020900043c14180200100c051020701400350700308503455042c0350107680c0041002031892044080036006080011501c4043c80c06448409080c080a8030003400c020030840801c0d03580d540c02c4107031844403a907201c0485c0c0030010154060004d500c20000600300d4001d5040e9440191014800e0070720810000d00645500f8504d541d49071210f1840059550b40802144048990203204203c458044d1610420050703541044105440c0d241032000900d00076540142c0070000310740d911403d12500642c0c0003a00f5202009207060039504801011007058004c0700020422141d2460303548070600034290b499211098640b0707909510385901003030101601c40c0c01d8843c007103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 633655593 1250 633654343 633654361
    0x6140f0a03020f0a09020c0c030606150406050a0302041e09050c070506010e041b170610031208061f03060306050c13030f031707050703090b0a090501030209030709090c08010501050315 81
    0x60b40c20031000702000c894517124000d910172a0004240030303803282d210340208011818108803068000c1d4040701c01040407210040d4100003031182e4000c50b000c0283c0810a42c040034025015079000d086551203403e0390400e6043c0c0080c0001e50761081030000307401d150114212100240c103d504081d000f03009443c46a080400c0204000700c0071f8012105144031014107404c0c8001c02e03894070050a50038090407d0000402402c80c64030801818000781c090f0324500420003c0d242e60848031014515081041d029580d404c005170005204107130b52000b900b0441043c083d03ea0717141d8410b8081d40d11030f80e801c02440c0c85182c40b6404034010710703100621200c10b015040c40031400000c45051994403d00d04030000009a02170201c0008003036629002092002c641042010381003941c203000b515040079100d0801004101c000c0500b0781c94440c180c1410340c0041c641106844c140403c101070941c03010107204c808114944440c09003000d1242c901c555180100116880c5400326101c01c0201414600c501e42e91104022 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 633656843 1250 633655593 633655609
    0xb03010815060d020a0e0a051b0711010c0b011413060f050105030a020903030a050702040c03050405280501052509060e060c0109050609010c0f1b0b190f06140f0a0302 73
    0x4540d8890b8803001914016502c0e4840e40000d4a07504046d81c0399401c111004105403280039107047c0081d8000749080c3c0684000e01c00f60f407082904060b440101c424111b0042c4d80818070040082e00e00b0b64a81d0001c200700c403030781480b0603241c10162612142440828801c0089411074090005504a40201000309601c5079001c0c0d80c000c40c90307500c014506000e5a0001385940d00c61442c4002207080840c004040d40b92500c40d4030700103400c030b081c144032624142d03465607141c2c10180c005003031500c5101e85413000903040b64021081d80d41d20200800c941d08007140083c55441540307030f0003d5400c0c00000010149803103813070b000c0110b41c01038550400c0c2428010822009030440780401044c1d40d80e070008080030403010001c03140070322840d00000511502c1544014220729450396900103104200b02c0311a450901e078042482d03825001004408141c0342c0481c01c140e0f8840881d90020154105440500300325019440b4008a0300b44a241129010159051003038600038544225881a0400c004002604007490 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 633658093 1250 633656843 633656851
    0x90103030315080a120e12060105061615090209060a0f0b070215070b011e032d050604050c01021b100c02120d030209040b010306031205071b09050f010b03010815 71
    0x41c11010991a100b1092811140410545540c1517420b040e07800590090700d00200d4a00540b002c24001c02c2000c80959917000600c146030040308009040b1400c0c40d2075203150204540d00002852a030111282000081d007516402680702c3c00710301c00030900e6490100b05c810200c6024980c0003c40a02d89200c182464000c5c4006a80081030780104c1980800c0b1280200f030100d100340740c110030359414102c050740c040f00740510000c2405028a01880070880031150b5035066001c9400d4806420750b0515007512500400700001e02a1013002e09003c2040804074040c03840c88000c4e421a1246d956400c0c1625482c21a0710900e500f12183c103031b4070f40019204042c40034549002504801c10160a0707105280380c0800c540b49500065404201558189400d0044800800c0c0904e020b0242c5402d40e11000030200300d04c108a01440000a008400c014500c169200d400c54507000c5011035542e9016003c0c00340c4030859902c8400464040080b60304491602070324140e071045402050341c0417000003043c103801d4000d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 633659343 1250 633658093 633658121
    0x1309080409020f0310050402093a0c170102040e010b090301060e0703060303020c04420b091c0510020711030609012a080604110c0a0605060109140901030303 69
    0x800415a580d07180003c0c0700c0700301852062956850029043e2050700215006148124010000c40b1030a03659a4803005035426030551070028882040090300114011425441410741071041d10824403074040e5860040f11981c02c0030010b020300c250556401c0b8030450050380a510064070041c072044080741d0140080c00300242c00017650300c0d1110381185e04c465048550b0400a0b0311914103104040d0b0610091000c3c0f50b09075801d11042c00e4808521641c5407a0240400381c40e500100200707443e200b10304080c098111420400d02003281c4404034654a030b8001d6240c20301510118007562007520141e400c2c0c04840381c108010741f8596480700c150708042d602074842a10b00c40d10900c00c07888c032683c017401003a01034034010700001102c4100125408440400c9801451800341c1100c503940441d0300704030002d0380041c0c00c540c00100c11020000064003030040f100c040c3c00301d01c16002d162003040f9155024a0154100b6243c1140d0703a40c0c0d42c0c0ca02e2540f00d5001d90019004118400108000b034002e03004600b0ba11042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 633660593 1250 633659343 633659347
    0x12080a050c0a060501030c0812030108030318070e0705120f071403060d0c180c021501090903030f18050f030403050a110d240b040204060c031809020d022106130908 72
    0x50720f844094034003c1e04140e5564087c181c00b0088180c0800404c188138054078009801d5600d0486044d40704e000003401c80b40700304100040f05104120500584d0003420b5481d51451860400b000010215000980303114110703810700f03002c180d803079030075140d500c2c03151200f56904207c03803294005484442e00042d000c250400f01d21941000007500040b40d03080070340651003204120958070803860040e20100500001590400c11840000e540c0d0f000c10a030540d5003110740442c080400b840c08400070b2220b6007146424900c0d003002c50444803001010307041c140340104200c41d4510b004040340760b168402e600c80105198000c04030100000c03103038101080b80d4580145003210300320203600c481c001644c40003e0149441010030617200c041c00144240c091198003541c08505042c2090401392031002d021b980a0140500742c800c10802d01c0100c2452800781c52800410754454002c111010040d4100390480031554610010b903240d5041d40184161184100030403250051b060404070300010300742480151140c03881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 633661843 1250 633660593 633660613
    0xf0504241b0305090301050a0216030c08070c080a140d0f2f031b0106050d150b22061e030b10150c1209030203120a03061d04050712080a050c 62
    0xd5044260700902907120789640b0300d8114209400c540004001004181c414072180c001910f0104180c6030065040c2081900f00a440c203100115000b10a00140a92999100414140d0b4040f074203400440c46106134100380d00500c0e0589031a056140601c4001404031028003541ca842100c10400540030108500c0e240c030020401410340c80b200c1d507142c0500e54000910301e6840201140000720401904000b00010740c01c1a0008044210408000c0c2c00d030345980f8a1041107111301e0b8840d4501c2000101001d0b80e03071810640351007601e1503031502690414540702c0009501160352101b0324051084c0030000c10082d045a6030201c0c00203000e448981000480c480204041038042e00c1034003142c0c065210b44482c3c1c101840c140103051039003c400c0040219844040005072400286003251040040c007960b106d040001c1c0403401051282d000047d1284610941824810b2040441d03015600400a407130342e443d103401c4440450751008400408813241004409a414031850103040c940d0f078200300b9a008044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 633663093 1250 633661843 633661877
    0x17151909020f0307110a050705010e01053106080606030a150f060903060e19110414010e07090501080405100203060d0204090b0f0711033a0b010f050424 67
    0x1030b1181c514205030000500c4110798010591140d0302880030f006200303186180c0c0e1101e480d00300b14031489050007066401444a0713030064065500020305000014003040090360003415074039608901110000b00400041009841a03c2c0c84c0c0c415240a0300b5185184c1700d00e80c40500414107403440280000d0045400704014110304405c0b00188100c3d501c07140610308508003181191202c0341d0701a80741d44141d42c0000840d0400d001c482a81c0d8200c204424941071010208000c0c00c00d40540000d0440e080c03001244682c5440c00e800e000300c0490765610384054586006442c001c1c410b880140c031603886100791101050b0950000c561101d030107444180301e01d4066000c5130607260040030403140a2058002c00c00c45491440503150300c48290325110601096a1070b865460344075154500f20070109a1804004040c2007803041c12a50300718400c1212a600000ba40d100204a0b40106a00040a507603034070362194801d03029581595141c2d55500101c9540300c80140c460880408800280f205040100c464070b9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 633664343 1250 633663093 633663097
    0x3010905060906040507060c052505060a031b0206010608040803090115090e0c0105030601050711060f03090307030e0a05060a0305090a14070f0f030503030402060d1512031715190902 80
    0x56200005208500741841c0c00b90502c01c1c1b5801c580200311100341c0020106900240e040f085000c0340f4401a2a101b5854812600c0140d0b604801d80220001a11000181e49a44540710025114071107071100301804404070b8958500b0b100d80000035240001040c04128003000542d08804040c0000030440143c0754460004c022540c001110310303940707120a86002c0010301c0809a03901c800d10b051807461030080700282c400e0003002e80103003600810101c044a01e0310b45a080b9421540720054164407850500b0b01aa566403001000310006000740d0b0340070429081c4250302030151407009001d03606081c0d044200b14000d14004280000c940f06900740304c40071038616101110780b000c0d828050700d040f600305150318251007460761051502c41c220807010004a4400300c1644d8001e0380c1152010fa03030b0059001d00a0150800800c1c13420000686031001445da895184255000c80c400d0f00c6400e000340d0302600343c41000b041140c10b00d40d505c5c90381081402515120010100c2d01081c440ca04d10160380f07401d1380078126 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 633665593 1250 633664343 633664351
    0x605190b090c0a050d180b1e010f12050c1309020a0b03040b0a0b011803030201060609050603040f08072f090601030b0a21080309010e0c0a030837030c1e080c03060301090506 76
    0x1c8000144000d48d00c03184007801e4000c20120f11500035525203403040415144921a03181148401848841045028007840c40c4480c2c0040102880b01088034000c0001c0680741c908074032901c9541000261a41150103a038031880c5c00003107420140d944c902d03242c005000301c030290318108003034564030258141400710000d01441c0254000241c8605060002c0c02402c410382041e8441c3c4414000c000000c0c1500383e20950700c50340160342d191501c24a1610741c111039003070b04040719009a003c880c04401c0b0f000082c03e491721201203403c070080341ca5500054085840c5043c1040d000510004107005500d42d0b242500320622a174010318402e07034601d8440c10441c1d04203803034807000340c0d4654448103400a41045510070941048071b0380c041c1549560340e40070441c820240040c07071240822807141139200150300c4086d40e10500c1084001c103401e1041d4002e00812000794240040b401c0f444021002c8643e5401c0c2440c2c00c01551034942d555100c0024182c00c90f00003c150b0356166403610113a03800141c09010403805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 633666843 1250 633665593 633665603
    0xb0a05030616090f0e011203050c06010611010b18160207091104090506060f030a05060f060d0207060629070f050a0b0f091203010605090d0605190b090c0a050d18 71
    0x21524159800815001e032036440540000d0b2000c13400c0c441c900d49401002d04440c1004810050500b003464151068095120a12aa80901c800000704c281e0442d08d4a17a50124040c0200f046032091010050f0b8025501e00342107111140c507000541381c0401030b809256208560048a01c0c55541d0016923040d5031002d00c044031883d40108041000070083e00130360b0340025003101d09505007a03c105896040d0701000f424400f4440c0c03104c000c00c009032144000c0e107841c0440a403090340d891089a540700040d40c080b01c2c08807011442d2820000c4d2070201d8915094175003130381400c5880312204107101d814140d0441101038500d03c0a281d420400500104541d0002034415982003803149049103000030210002007a41d969a000005c582c60a0b480350740849040d14882d0402d5512413a448022440801121600400071403070b2506105407620792014201b0070810480c42441a461500c06028810f00b05a6488002050903c61080424000c102400002054241c0000c00c0c0547c02d040d41641d001846060340e07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 633668093 1250 633666843 633666871
    0x160803010f030b060a050f060310030b010609080c19120201020709050406150b09060a0f0e120102030613150902030403110d0f1106040b010509070504030501062301110606040b0a050306 81
    0x400002d4005151311040c00c130380e2003e170b461400e0042841803224003403640c8039030310000001c3c22040b031490b543c20203141c00040300d60440d030f11103101800d07101d0b5600034451a840340c110740100c00e282900b20b03081030300d900e00030102601d494507502a13900c400d8074404038158001c5c0070002c50821414130669115501801c8003082607524110a03c400c2012504640242c2d4400c0000000585610341240c403c604940303452074003110501e5040380e8400c8002c00d1a940500c00c1e40e221901480150041c5008060858444400da1441a00300049440307803500e00d10084441a81044096800d40c05164014068140045400384c00c4003440e081200c0b0300e4003e00810703c40428020340540c0b1900444140c40148010905030809884000b4505014402c26200388a000c0005500c1441541a50010f5500c032000707000e1075486100307544102e400c2c02e0311a80b880180342c1c6840744542c40b40b8041c542c103400c11009003410303840700c1e01448098480b01200d10f4221040800c006002d45040124a02c13070605013010701 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 633669343 1250 633668093 633668099
    0xb0f091b012a0f030e0a0308090f060f0d060f080c01120f0b1002030406031a131109060a0c120f0f08040c0312050a0305060405160c02030a02041104090e120708160803010f 75
    0x140107562001180c46c040c000d00081440042c0365801103801220007113840300c4258034014000342280c401e10041c40c5000e20301240542111078107411005c1600c003201c0c00398100700c0d114482c0940e00d0a1000c401d078000380380d060b088201808180d01010741c28601030b40100700342c41081d0106a80390754030101040140d0001400b0040da6516100c0c04a00314094409002c410441c1800103410317000c40d14600f94265950818080c114401c0801c540220f1405002c9a494501034200030300001e827044000d6070070ba9940a206002c2d14031401004400000c10384803404041c2000e00c0c221001070004100f1500900d04160101c04600c0f49a00c04c10a031005951b0556130b00050a001000e0b9807010704064003c90604040c8400b4280d54507400504a0261403d0700f031036944e41c00080d04d001000503020303400c14036110389070b07142c80369580081081e120100800e102000008848558030104285401600ca00078440c580c00a417803440104200d1001090741414001107455501481c3e01c2a400640c0c0040c0c800010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 633670593 1250 633669343 633669347
    0xb01021e0a0f1506080c13020c010f11040e090a020d0f0f0206120a18050322031502030105150903060105090c0d0501151d0a060813050304030b0f091b012a0f03 70
    0x1300c0c0030f08007000244c02e0000c2c010011a40b01a10303949104059030300443c1d400f4000c1d009500480490004d05170500800e104a2241245c80d4028003801c2d14030306008000440689000441d61400f55002e0134001070b03810a41c13101280c0500009049450f40320340c40c0030802580d80c840140c00c601640103100c01441c1003d80e10001262440140201300c0350904d802ca4010a5011040c3e41440200850520503c612244c9124604a09800c018641e030307081280500a0481c0703034050b5050b00c40a403800c00d0014010303291301105015600e0782c10f6040d8800c40c01400681400070107aa00008003060f07180c00d251205001a080e20703400d803ca0049a45c18003000c040c180d44c0450880902c0200c444025141c808600200b03001154502450041c40012404a2500c59858a800c11910b81000a5a0f110780c1c41c1d251561425200b9101d004031148000c0128030981d6011030a502ca08602a05644410784110010f444010b22419109074a022061046000c078800c00c2d03003024081d200b400002d446d810b1034600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 633671843 1250 633670593 633670601
    0x606093001020a1e090603050601051b070510080906070c021305150a06140301090b1206070e1302091e0a09090b10170a060906060f0306051501030b01021e0a0f15 71
    0x95041e8103030581c00c00e070311a5500080c0a2007506e045140103e0555144030042e201d510941c0107031402410086c03148075142c40301094030070940e0306c1102d4446012281050460741100c080c1c80c83c1c000350300304401040ca068000c40160580c0f41c030140514850310420340140c0100c4000310f030340c410058243e0640ca441c51410405800103400741e410007150039060f400100415000500802203c01d81c0e172504271845903182c0b003c0612501244003112070521308440002e0190140f03281d518012600c400400d011a04540255190100d010f400d074554400c050741c00080c488030300401c50780c1020382038401041032501401944081402036281882d41d0810601041818040b64841c0074069101201903502c80e8003c01c2220b001070b000300001c241c000c15401e00c0300c01000c650f4004130501c040c9520001c1082016049141b10305840c005010400743d0440c01501551a89050309006030802c4c00010300c0c3d1103400202d0b041e4423500208032510b0200f9961202184101c1c3c1e8001e80d01100d20410080c051507840c09 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 633673093 1250 633671843 633671867
    0x330041503050603190f050c030607050d0501080a0f080a1404060201020430030503071e03090614070e010c170c01240308070b070e09041212050606093001020a 70
    0x4010101d00d101d80480c9004104017403402000080692460b45c14001c1c00c01140800050060588806003040f40f40030300580d1225000d501024100400022401e0011401c5140e958010105210780d03a00ca694030403040c2c1c42810f280050082d07a52804141d583c080b005400903083d0b940005955500346912000e00d0344054544044090f00b1030800c801c9450052008d0496607814280980c5035201d0103c00d40da0040042000d69407000c00019039480c041d4182c10070304103d4003510302005910415480108089021a05800401e00c040c0c81d6446075403180c020700450a01421058003100038032060f1103d41d83c403041000c0c0840e9150001d008038600d400300c0401c1d40c8000320070040d106500c0c41e0b407410501e0056a8000c0c000d61924800654014003821984000050003000f984082ca0940340c1038410550100101c0c1c00126402c44400125259104450041c100104a10f0801c451901000030542d800350344030f000c00e2203403030400400610b201c0311030200e41d54420000d030319510481c100500313128601c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 633674343 1250 633673093 633673099
    0x1e030f2406051b06100f080a1a0603010f02070803010303030e03070506060d080c0625030b0a050d02041107080301031e1a150a030503040e01080303010503300415030506 74
    0x520a18080032440303000c00225000c03400d00c69203a101000c0700820000541c1d408465500a600800c802d6042a02c0480182c41d400c881440d00e941c1c941c0d84680d692a41100010710412031102400b003a548140b014580c442030050000c030305600c110340d03d07405a812103501150341c01804001802096013502400b00b10780303400f90013503080218a403034080da00c40016106a000c0d01115190f10309220f0038100300c901d285595401c03500c4500b00384460041c0440701003a00c420038003005515043c024444c0c0149560b40700010071120301e0030300740410084070078000c8608a0340140e540156a1343c0c41c371118084c100c41406410f015803250b242d42450000030f41c80d040c25003250b8039031111040000c1d142900d01c2d500c16122140d040c10681c2c8614111400b070804450703090380201b210100100b007141c000024825107081c0caa106c0e02c1a6a40c403689a40c0b0700003030003400e03070582081035035541445500040130010f07181000e40b600345240302100d80586511a0300400007040d4070510303e01265802d4010b07142c10203404c1d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 633675593 1250 633674343 633674381
    0x307180e010e010b15130b0c0604020f0402090307140415060819050103021806150d0b0315040b16030b15120906390c0c010215090a11011e030f 63
    0xa50005800307080020007104003039004100c011004100148240141150080c3e2a40d00d08d002c240840e42c0d0702c8215000c902c560060b034000f44450500c0e0081c1c503444400074008014041c280100000d007088410861504a55030f407176400f880758047d9217010300034410364685603914102aa2460990042516450724103401e0500420042c0c0301c0480b00c01c118002c0e030303510300320319180d41c3c1c0080e5032611245800c15070020041040e075956220f079440300d00081c400300c01b03c4841c214950a00c400302070b8220f8000d0507200803980019860943c1a01c0480e05000c980340008503400b10400150709010390b181e5440f207c0c2e101080c012000003010404903000f81f01d0701c0090602d072a04500300c0282d031511080c900b807003640b10310003560100e4404070407840028150200f96122148801210f03034407540081d41d640144150610480e00b8026080c10360b01441d03410700500311100551700c80c0c0c0340f080844ea134020b040250a0302e00400070450040341070740c9407105583c041030240c680761000381030700e0701d0301c801110b64106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 633676843 1250 633675593 633675611
    0x90611010212010603020309010212240d0803040b040c15090302040f051506180402160605010501050a0e210f0109060f0b0105070b280e011404030c110307180e010e01 73
    0x2000b800981110382d1441c0150307480c0d07603200d42d16019004804001001c880800140051040c50b10344c040d06400c5d42c40c50100380041800300b002510740c0300c0e42c000350140004001141c04109400101e9038068020000454100d0362031006010a8020402c1d4400140c14101d041c0b00310714280c0a1f103d500015100d050105080030551309107a10031842403284904000034070768138020540026403410200080c001c5448212400d00e908024082c02c408562584c504400400e40c0d602480640390f040190795220300c03031030b8049070a000400305120350240d000c0030704c100e500c69119020004040e12000c100008145c042c40d6203001001e80b007000280805850402c01102c2140c1d0340401941c0d14181c01c5002d40311240c8418201c01200c00f9030510500c601e244042d80008806015000f00482901800003000b9040b00024801d100400c2134070000e00152044041c0804110800100c946440005080c0c601c26552003100400c50107040c0099050540c071000710980b49503003031260100320880c0400074081c0401d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 633678093 1250 633676843 633676867
    0x821160219171507080f18030c030913022b0605040c020c030c0405070507030c0602040e0c1306030903080a090501060b03090114010f0e07110c0d0606030209180d0f05070c060906110102 81
    0x4401444070341d503c0e50940000307c3c00341c810300700c10007038041003000c0c0c0740d449030951400b03601c0b40e214a600034003032260500c43d5111000c0610844846501440d2500e907200c00310103610b0300354104201400c200b19151000401c050341c9030b110352190702040c0c0c1c004180c10820501410f003482c4c442d03403403584541e10304410000c0c031940203c100c2d4605581884c15444180c098030f400e20090140e070300310700c405425030000c02c014a54480c0050020220003800408046e5a8860850654441060007000180c245012a0f0a84410381182d00218492000800c450f515900b40110681003200c43c01c40d169112801c0c01c210108610845001d415000003900c1c190b410012018142c2c00082d01d89010001c1c009414650f0503000c0c42942010722000f402c20513060100d0625001406490105920480480000c60400384940320800900c2501d00b0103002c1c00d1300c44103030a44003c601181e446003400010080880055901180308001d01495203400c440c26003807020060100440712100704140c0c1c810084260150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 633679343 1250 633678093 633678107
    0x105040f14161e0504030203150c0702040218042a0207082d070b031006080403020d03050601051c15051005090409140d02070821160219171507 63
    0x20504501014181c032490754111040528000c500e12045103c10651000a13400b4008008a900890883d2540240214200312006d01a1086c1c40b0700c403005c00c139284c01800e041d0064030080e5280d00c4071a2346050140b01181c155084405161300740320206a9451101c5807494205449844c0c910041220034249415265207508054000c060076400320740e0a449400c9000c54441c00d000c04800703607440e56a4a0034500010740040c4c07460b400d400f41840d00403a840d4030070001c1e80c0c419501940140304480510307106a0081c040540903d040240070441030700c84840f0002075641601020b14009002c1d172200b4200e10101184d42c0019103c3c1c0c3c2c402100040c80c0f54803009449440d41c1c1200c3c0000e14041501d0300541a54880b41c20f46403600460b4200451180c000c01c5440490baa4001a0745540d01e80008000841d0740d901200b40c14000c041c0070806400c2c0b00d0301c222a011031300c00340c2050103628000c101688003401d5503201004603a04040f50300e48043c42880f643c0038490244080f44011300b07021002070048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 633680593 1250 633679343 633679351
    0xa0c030f260603190501020a03060501080903030708070324080f2e06030b070c03110f03040303031104050a0f080d08130803060103110301090903020f0601060f0c0c08150105040f14 79
    0x20808000402e00941e01805041c24103200000300c00c0c0c0c020101d00c1c005010350809402c00c0c02203882d0000015080d40111401c4d4810421200a10302d140d0310800d066800c914060025010903580300445110000070f044c224609101340058021030600e4601c65500d050702042030103509030403c8121610500c0eea002d003981d80da5040c910081188050000900200704990018061040b0b100500c4040c1d500f040001e440e01f03000b56228179490010540243c2c0d07c559a0a00c0d5209900030801040402d10951002564550000919152964840c00200800f826403ca040d02c140c1e014420801c2aa0030410010403803681e05100c020b6180140311041110f030910001f5004140c000001502a07210364048034078121030303020341516035840e030240d04000e0404060071005489480441400050005440b504907000c0f55514181c91250704021520306a0020b0300300c1d04040700d000c000c6403140080c04680341e41040003520005642c0340000300b0083c2c54202c0607800d0550700c0c00c00c00c4000c04038a04a81544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 633681843 1250 633680593 633680657
    0x411b0628020c030a0f03140a320a0f060f0b0324011403090a060504050f0c0d111203360d05060406020a05070b010e150319110d06020a0c030f 62
    0x240300c5c43c40c20680252581845d5010b40740050810001d41ca000799002c01909404140044d0101071401c054030980c14969110000c60a050800100426440d4111550301c0003058004541241d89440403a2422180d40282403035020220030000640b107081d8107900744031040c040581c044501c40c1c002030900c4c1102d013542d591041c00003001070304c0b80c0820400d000fa215480360b0104410f1a0a04000c0e071544d06900b4050068000d40c61129810700d00743c0941c80885400510001c2801d80e1502001034041c1081000e94440c0018006c0d044040300c1e10b503081d4080201070708540007034400020811640310014400078450a6040b60340710100d50002005a40240d010500513600c907411141a80d19018078100141828403c0001103801201c441c0514040c0c01d80d00c0802d684c0c0c04005080640b605210294040804c00c102000c0b0045010000f080c80940809000c0c961040c401e034840710140da104041c000c002c0346c4080510005c265101d80028502d40c41403504482181d6001203c0708003081031010111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 633683093 1250 633681843 633681857
    0x50f06010e0a12060c03110a0306080c01021b06090a08120904053d05060c010608060c1e0f0d06060c0210080903040e100902040303411b0628020c030a 66
    0x40054000c2d40002e810840e501c02c080d423200d404650040190040c1e00905150340100040c407102940000340c0324070096000307110800540300c1d000622509400049285030b200700c82c5080000c400809001201d0a4920004456901c03042c0006100c1503804c0074100985c004020750740c80c00c401c2d0b0180c10074201e42840c2c054509139000484c03452040c4190681205a000400240e000300c1d03440158002c00071610250309a880b50360300e10f02000120700a11880c60b03074070292010b46c051031030080001003140b032841903da54106030b1411400021141c1640040002c10a10615603040d440c0990079010700b12454034204e0190324182100c5a160301643c41075411790747d02035020481c5203003d00d00d498060940d8500454959a403807d008052001c907002000a40c1c810b28544a80c81b8810164079401038405100c1d094000040c540c01002540402c1da10741046111180c3c1a1000e02d0500c407040c00b64820800b0020148040c100b0401c00004824003410b00c1c0c0c2c07042210050349800031040e642101c11508284c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 633684343 1250 633683093 633683111
    0xf061229180c1c0c050306010311061c0203130b181b06040e100e13020603040201050d0906090b0a0c0518010c03140a0f1b03080402130f050f06010e0a1206 68
    0x2e1405050754400381e4048601003180a800b8125607a014056014651030304c01e4958038018551104001c2c0400360801c03070a030b10505002d08015004020b0700c40030100506070384043c01c0c0400200d030000d071010800002910000740c184078030030b0051904243e4440d00c13a15000b0414064075034030314102c0c12074408070290030315002c0036a0701c40302501c0040001c03402e070151038034000443c4841c5122902a101040400c000031416158404100c0c0624650143c00c45145441b41d03001921660004501c0089254030398041000241c007034011141003911440c2d10a0381424980c2001e000c0e10741d9031040300d0400109021040078121140080701c5149001e080c02c030443d020900b812241c0912000864440342000909882d009078000403281544840b1398859a1602d00d400100c0300c41030003004081c0c006503000000c54003516184082795015100c0780b1002520500181c6600280d40d0119028078040000004121803560023180900b070381d8004030388240c5075508014021088112071400a41850354a88042d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 633685593 1250 633684343 633684391
    0x60f09090f0a110102160b041404110a1101180203060f0a18050604020a0f0602101104050a06091a030f04080c0102071e0c0e011a0d0f061229 62
    0x100380600e480d4400d03114405103d0034140c1441d03241c03450b91401032192001d8800c5000f10007a01a00707460444c614540360078500001d0540b040c90700c2034900d901680e60403510399032001035030050800541c0d986402c680c00e07294150703060854501a007035040b03a884201e03040300103a86c04251039038041903103803034110142c885080000042c4004c0da0350440c440402d013002c005100001814030b02c502d108998980c0c1d4551200e603204182022445100701680c015090000c40300304a07007204040d0900c0c01c50b000e00301581c5100040a504a980c40791011800160003406407840e4480900c0c0e50000141c6190703d5420f04000c04010711300c0040c000380c1180004102004145402c1d012180e0598011b140c101c0700403801c0c80c00301445002d401e400c94450802940000321070380010741a0381240c40c04003115182514052450845512108907415096604c110b10b4204604a00c103810140011074010510032400c1e1401c021070144085400c90303210941c1c0b04180308406582c1c50781c0d510600c0708004420302420310442e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 633686843 1250 633685593 633685603
    0x100804060b0d0f0b13081b0a120f0e030304060e061305040906020d0b010305220609080c01090203100608060a0f091703070e0a05060a03051f080307021503060f0909 72
    0x1035648031242c510a0000d211812010b0302c085400746140030b500303448940501481c60203a0600415044040c04101d0f440c100500880250b11014002c0e25111041c03641c1d502c001c5502c41c0c08900c0400c000a0310f00d204940d00009000c56102e080d001545410700b09200030b0040c80c4008001880f41400007071089284d0b0310040800020302000e00305000921603403519802a4100300a072070115803030a48402110740c428005c0c40d000d9005030180035503120034255150b0080c0c913940341c1600c5140d03d580c890300000350b4400082002030351407400000d10520601c1014140814489490a12810300d41d060000300c002040c215000340704036400040c500080400ca0010f0825507801800c800b0312050140340420903140154820301c0117a0310302c41c51004c02020042c00c40f2050003950341150062103490b02403070090348001d40201140007001452a45031405da038600c1101d801a8031660130110b40c500450914203184407020745410a00d600754503140c004900180c556170003141c07103513840e2800b2408503041405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 633688093 1250 633686843 633686861
    0x90307080f070312081905070e09180606011103040501081e1003032304030609020d020319051c02060a09020112141501050717090319230c10080406 65
    0x141d418400000400d9515804188010b84000000c80070800650380b0a800365031040d6001401000520244825480203100040c40c803810310441c2e10866030386a880040c900d11034401040c62006114034464032500b0f02c04003070481414030600000346030381d19002205440948200f0300e40f240391a941c90400209a0619882510286251106000700042e0500d03140c41a01d009403203d6140c812620704405c3d038140d071120700c211480414007043c000a0312507004041c43c603000810000d5011201c2c3c0000f8200044010311882416082c0140f00812a0922140031340e504038003140c0c071201d24840e4019403500d800034040b00301c00355107410728801c41e03000d0004003003c1400c0c2c55040011407000c0300d50240ca8003081d00e2800030401002c04a9034150f120b03108940c401640240f20b81c00c6e61303049510620306a0080e414240d4140141300310790300e4018883c220700342d0b030500982e807000c404640c245a440d4010001e02050055801409401200e5100c858452528030f541c0c0c0380034400c1d55210b090020080c1000a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 633689343 1250 633688093 633688109
    0x18070203041a0d061805100b04030303050a1409060a0e0d0e12010e030c010b01020106080f151e07050a120c050f07031814101b0213021c15080705030a08090307 70
    0x90000300d640040c88179010511400c0001c1044241c468091420100c0c41a100c0c44440023001c00c42400024426045117400c03c00101010800c9419041071000384101140c51221175400798040006503001c9000e0b8142c0003410001030480010366010041402240c203074810b000b04a550000c0840c99002d51003507008284003004e03a919400d95265103406004022842401507080400c0800e00507004640b491540300c4407001004d110002040020555034010300d003084280003030082240032141400720381c0c4a034804e6a0342c01e90701e0035a00d2000e4550b528619030703541d9143c0303490b41a00816400204442c00d41c035190907080d865010a1404541b003c00c0d040844900e8007880d000001c40d49500740920710058401c8408440340703c9006021a4440361040102409145510b80d0038090b080640a1040c120b030610005841c100512030b40e03400b000c0914402c0900280da0743d007050031000540724100040c3c002480540341040c40c0c400007903914040550003030b0020f000040c0e110002d0fa002c0141070002c203010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 633690593 1250 633689343 633689351
    0xc030d0c030b010e060c0601141f030f0f0207030804030503060d23011407051e0903162105060c13151d010c02100807021014040218070203041a0d 64
    0x800040242c030000119034080b41c111140001c0030b2812030142c911110101e401014180c1c604460614001c0e00408820b4101d40c500400a1500079400c0d542d034866442510b011407042c1201c075042e0100c4041010440300c5500c140103003400298004410b81c3c1003a0035140090f100d4a0b1a000030f1074500d83d043c002010f00c5444030400084c1681e4122407550790060b10003c0007040742e4411140403100d01111440c0c0058010001c151001610f4441401d20110100f445800c080700540071a15080c52084d40400d0b10710180010000703c0c1c1080c183c00b20268000860603000f034140d950b41660762401900d100809040400c0315640150182d10110083c050300019007103c2d403048071302501c6041840c10407088840d424150780c500b54000c1c1410b400082e4040c00010000d42ca1100c11504000c1c0a4869800c40c090300031865000000e5000b60702c20340f002c4d602c500085d41072602c10001c9091200031464103210050b401c00c0491600802614200d414104074070000020320704440050740b15441000c0899854 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 633691843 1250 633690593 633690611
    0x309170d0504120903050a030c030210060e10050301110a0c15091407090b060a05030403200708071e0b03040507080a0623090d0e040204051302030403021605150c030d 73
    0x55040700d030140303000e144840b4402c0d16880d0225100501030201420b550b00803118000024410325101c0141400f80c4107492000c55100040700a0311443d92101c5000c2c4070003414071821420851043d03004140480007040407121060401019000744001c04050007641189542400b901026040c8040508442048a00c0031071401c000290103060352003210f48189a40810010384070303c1071a80000c4024242410040c4100003115a42c0c80140114200600030101501d4610b0107031808118002c5c58029042c06420400d50624141c119130040400c009400c002d9090749d0100020342003502c0c1c0b26a8500d036a903403a42401454030f00580c2c0001102c4c8551100f02c428041070340c0c4400301c005510903182e00c1c42d906403000000d81d041d0a8510300b1041e0040218100700324000c000411040038060405820141d485000400243d45000107040c429000802c01081640c14803072441500ad100c0301c40d120950905012658407c90004a02c0c0c2c4c440700014200481c0d03c08000395501007032080024840704403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 633693093 1250 633691843 633691867
    0xe0c120102211e0105090103120309020a080601090c03060b1605070b0307080a05010e0417031b0309010c080c030403020a15021b010b030c01140904150e070e0f040c050901030917 78
    0x2204640204030b5140106054141c00c2103000f07904e04a8100074040b040590854441815882c05d4201d807205059450313566500507142d18840c000206844c6002d072034158901840d450540e140341c804c4004051810300c2c01d000c20041c440030380e4903a103140140562402120b1500d14600616900810701d41400030003003042b05940000c85030310518103048284444d17640d03081040c07030340740301594000d28044c800384e600c10a0090240140d544045d01c072483c01070084010850351b60316441a2400c08050351a0703501c6e80c0405030003848482d0011a00b0790224614502601c0007525440f4220000f00145507004101c80c1d040202d4041d51002d0201214041c46208401085070003007034012110343c024002d42d00d0529442d8014401810341c280c0024203140b800211000700320080040f00c054101c5a118501c0114000100301002d40c4101d24a441c1e80f68241c031420100120308600c0d0315109c0c821030802a41c040c4045d401030544400e80c400703081c08202c0403450301d4502c80c804080313045140e440a0124502c19100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 633694343 1250 633693093 633693157
    0x10906090b12150a0609110d0c0e0a0b0304051f0207050636031902030304030311041a0306030703151a0a0e07050304080904050406060602060601030e0c120102 70
    0xc0c9844a082104400c0e030820b00c40800202c45080000b60042e85a640c056018600d942c2d034030500c81d400c00201da60300c82c22503404807288041040c004280108a03041c84544900c2201300f8540e6905090080441150018117022b0342070081002904000c40810304212040060b40010031013101031011416401c0100b02c000c0d0003100c4240c0d4103100c1c00d0085103010004241d041005a03421202d0002c803c80d080c41d040c2000401010b681c00b030722042080c69840c116500300100d4012031940959603d05103410001c2c165081c84520b900d070700108020412001410040d014030041d818862151a0790b0b5410000c0e0800700b8690010344488241c10b1010503000721035002e060044500c61400460025140500c80c02400740d01034150000044000f040761540503170061a0f1292240740420b203410040b8020034140c4900740d400322100c0303848100c2841003079018000d903a400102841c0800111000031200c550ba851480349680c0122000104851148029011189580040c00c00851250702c00d43c0009e1800c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 633695593 1250 633694343 633694349
    0x7060804060c0f021903020a0b1f1a0a032c060702070801050915092e0608151b040806100807150503160c020d230c1c05011103010906 59
    0xc64a000201e10ba05801000181d181140982c02461070b0624680c8458070785402540680a40c03103070100c541c000880030103201740b298a41d092281040303000800a503000d040144c00c100c21003858080f100c1079071440c0100b5503906400d28034011684203001d1207030b100039210420401f48050216071500305c2c4013500007401401243c0c241e0888403110341e2a014242242d1045d105055540c020840b40002e881c89009205e0b0042c00d81c40035503100c49840400b4101a03444690411030580d05810400103451562040c58001c00c240d0016102529132039480c800720803002002d6030740344e1940d46000d00e080e01d0183c0646003d04400000c99001382088540104051110b00c1a0799840c8910340b0003142010b14858040070000141d125030303046840740100307009001d039006400010000d005c0c003410050396030702c203820b400a4080c20701112441071703803000c2160001907036030340705490307441025010719940740d00c1c4848a000f04031080b070080000c0300340360560140000742c1e058951a900800040364045d0315611117412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 633696843 1250 633695593 633695603
    0xc10091112160f0e06121c1d09062409040e03070b0105010c0b01031218061101050c030105030304180912110c010306030c09090303061a040914010503071208040807060804 75
    0x2c03641e4510401605a00d1401581e5001031418007180710350601c0203001c207031400202c1c00d8443d02040c040241405103e88400c1c480041c011001c0d405124600d4000103020607009d803400c002d00c1c60443c0101d00c1b0420009e03201040308103003940c16201c0c084420300b507400f200f400500c00d1015031051009036946c0e4118140a48010428400001e510341c007818004601e5a0310030010031481c1c1c81c43c1c942ca1a013603400d0741408140039401022084100c3c1405103500541581e03190300c0c0011140e038880c603084420003407400d0b5040200b08018080c0d0b40d800030903902110004200d079060f00d850742e21110302614582c1c100501c4208200d408550840e04140243d04140034402241c00480c003901c0110240d50803440040c1c01012008400e001401c00303600007034880c500038100030860a60b1408003a01c500f21001c01e00242c0e2001190900c44c850142c0500641c0d40202656203c0650500300000d49401d014401c3e180d41d061021003920400114200755001000310100350340640e562002c0c0a08107000490302111303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 633698093 1250 633696843 633696883
    0x70306050a150e010c0303060b0d090308150310090302010b0a0b07121806110a0f060507180b0a051612030603030e03060f0f09030c160504110c10091112 67
    0x2c4441c00c0b58881040300b21940d450031250302608006585020144000750b00f00350b2140030100e0645501c0000705031000f810240011300074130905008029200150400940040080451031a944d0000c0c01a4809080b400b0002d6619840d00d01070b80100341d4074034419007220015070002490020700d000f4001c098000d810f404880d50440400726040900b011013041a032020f8041400264491400c00b031210903028112039492100f0f031182c051a036086901110055120020007241c59885442c0070001c0400c4500e10081a0910300340806500030540c50108210010075601c2c0e081c24801d0304505a95049030194010b8511140014040e1030940810790108107040040f42e0b0780d040c006001ca2144850104800294030341e45150701c210030f80608002000c0c0700900c030018a000d0700348404a54400d281c504050b00300e15000c240030a89018088826690005110440c49076070042860030080003d584005801070b503615050701003110055070750782c0005c600c2c1c0309075104641c00940c0380200342c0082c000c0c1c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 633699343 1250 633698093 633698099
    0x90c030201020d050a05160609061d16050310053d21030f1101060f08060108010207080301090c052818050f040e03040510090f0803030c03040f1109070306050a 70
    0x14403240704030403481d030009900b084116031f010f1450118070500c0d0b204031000310f00c28125840d0030050b52074424000b0141904203101f143c1c0c10004110200005030b640c220402c0c41441c0100003038440e010300301c5078580961140001580d5059003071300c00c111903129031503003040c00380c092002101b480d10b03d400142d1403054403640841c4546450460f0300c07050042c51092500110141d508407121800300d4400e00520002d42100e180b0880d007800b8002c0904950b031881c804513860410050314118040e0300134811a40b041044001103011601120b05440c85140089203003101c0d450f04840d0792042120407444400c1480d02c0e000040540c00744441209110303038880c008156200511002c0650301c1c0308142d03103e01c0301d4200024906041d0010a180144a8192400d00e80d41e400442c0b0089001c44d61400019424201070062040804800c2c000e0064440214294035100d0b9407400c05105c05000642a403409144c0e80080050103104a030700014003800c0c0d1003113402c0c101c2014000d042140a82481000038a0001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 633700593 1250 633699343 633699347
    0xf160c150e011b020f04060b1602030606120a030f090305060f060f03070f091109060304050106181415190e1806040803010e040519151a09190f090c030201020d 70
    0x10f11030000d00186040c1540e50800003141d02c25244103400a88038400080d07650105009080021000959a1404d80d09441050f082120007070410384176080b00050201d4000c0c1c005046214140d05050000301da440c2044103541e071070b405600040003889028200018100c1c3c0b25040c0707004402c261500b1035003c11003010581c40e110103000301000484101c2c010880101d0300d422400c00d4201c010b8101d498844c01d0fa0128841da4000c8605440c0d9a441e00f07800c22400c41c001780d4540c0c0c000e003c1c032801c200c0340741d810100321354049000d0003015a40141000c441d800d543c03594009a000361a0000b1511490784c0c4801c4400b4002023207801c412300c0e1064804034074007204003081007482103070322610052850382021244603100402030415a010311407274115011150341c1d00c0a6508507401034a940f0358000d1040905802c0e02c00c0c0004c44070303e45814450342c2c08282c0b02c2d44c07940303034205070f060780c2c80300001c80b0741580d2100910310380c58812075450501440380140a8800341502c280e80c001e80c00d03902003090842c1e003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 633701843 1250 633700593 633700607
    0x304021239010215070306030c090c0801060503040f080a120507080f07090f05040e030415020a020f0618010f23031902090108010b0706020f0406030e0705040608030f160c150e01 78
    0x1d14090b070403102e0319003881d00c18081c60a1340301c00c0314180000c00d07075101d4580030302518454103c2100d040e99440000ba0403500301034038034014022071416074518503299070b80c86071440017500014440807000c10019182c0780180f507001e00b103284800301004207181001000344402c1043d1038843c01d12092038041340c01039114229980907180c00003918000c0e45e103401c01344001020303410036401641c001840301248850807028070b035079000510303401019004424010000f40c0040e6010b441e01c1307071004008181410107019541035100400f403c101c48580b00751041900e03840b484039200e4000d00191816500200610405140a020206800440c541540c00725204038466002030034041034420004000d00b10042c8000c0490a22440d070260a0040c00c0030030100640181d00620b022035100c0b0710541c41000c013001001d0042c007080b00c0520009140000c81ca0f100e01c2022039146102c44009440208040898080590309074000c00c40801c1d20fa03a0480c100d07010a09400300000140d14500e034650941c40b03458 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 633703093 1250 633701843 633701953
    0x2010203070903110604030c06020d0e06090f2202041701051602060c0705030d181401090321060e18070e0603070608180a080d0606210203040212 64
    0x48035011641151241014100c0301000139174050001c00011000456034080d500003482c46400412400c500c01501600000c407070f404841c05030406000707002e01c036613640000702284001a544003070001c02203c2900b5411540c800040442400090300007901c020f2940c51900d10380f0400300802654076500003901781034aa03542c8050041c0d1001001c0703a0040240e4005210700c0b8070400c100ea1a0000044484080da402d5010030ba100496404003d03060086044802c1030361404c0900800c98048070341d5003d04156402e0145441a034030602404440190b0365014038042c100a0b6000105441c207a00311800107920790446000c980613080d00002c0d03d0000305003141c020319000f00540340301410f140c011101443c000740983c6402c8019040c5035480081840003c2c6228080c00ba42c50351150f58502042c1984d01950042d81000a079a4036900c0c1042400d01903066010400c001580d2503d0300c3c00041c558022452100000c0d0040c144c0300303a42843c0b1020703400c0760351007008000403824101441d94007500c490b0135 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 633704343 1250 633703093 633703097
    0xc09010b0703110a0c0603051504050709060e0301180c050415060f0f030609090c0f08120409020708040503031803010b09010b160c0b0f041d04031b0213020705030306100201020307 79
    0x200c6900000b0b40941c40075010a19000c00700c2e85550321035114000e410304180c0c0480c5c04a6581c80c1030201100310361400340907260094600744003504080c43c00500ca0700700e40c401c0c101002344064101c03060340d8003074110403034508180b07900b9401084141046c5d80d0b115031510400d0700c0b851514020b1039000c0d4960f940d413001c4600503141c0d821001d1040c1b00c00e5840c1400541a5000c03d40c0d1170b0404030707004140740b1802c0191402100d0f21016903041c0040481c2c074001c0358103c0b212035032010081700c0d801d6424800311410766051683c050f8882c5010700d080d480c14003c41d004550300d0f010102d80e12a180c03403944549083c0900850007480030074404014400c20240a0003103005d004d104116076803206100805105840c1d114030f0712600d8a41c0c2d141020f0020f03821105901c151441c0003d01000b101610300a405095444150314008a043c60756026054294001c40d074441601f1a400c10429035032000d495142c0504044419580e0b01c609140881d241e920803200b00d849100c901d0a1400c04030310501c01d4922440d403036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 633705593 1250 633704343 633704347
    0x30601050a0f0e0408070204051e0702030313080702120f0d09060509010e120a020301110d0615020705270115023f0f0f030103020a0e07050703081302041d0c09010b 72
    0x4440c42c0b1042400003001900e17052401c02c14100184c640388035142c0308000000310300070740c1544c24481c2045100094080c0d0219401071085c070854048200040034050780c045c40c0203030b8883c0070f480410741100071100d0f000b882707000b40020090100c0c0040b600c1c41c041da107990b8035a01c005448800649083c0100b200341070000b91080c2d511002400c02c40c42940001200404850303004500b980000d0944003080c071586400307100171800400c4020240240005000c841d5540b40701081e616500030b41d555180e204840c8100d9440514104400501482d02240c007881c0010a00c0ea6840e1026900d0700050011113000502c100c8204c1400f1b03010304050b500648802001c583c02c3c1810707000360105024981030320404440e10401140130310078880030003040c0d00c0d9401002c49441c1d40c554010004030703200a0b4030808640307403030b8010030292030361105c01c40d40517503498104010350703858900140100084c00140250050b01d0095005110001c1c1d0418800200e100c004aa0500c0c0340744091282c101d00c04e110314000c000c0c007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 633706843 1250 633705593 633705599
    0x20601060c030215070f090801060803030a180b090c0111011b050a0228050c011b0b04031b30090510021f0903230318030c010c02010b030601050a0f 65
    0x215401c690701c034a0003031049401000c840038240d0302801041e5102d02c0400d011000000c16160030150410041c000f001c001c02c82c007842c00c1403c030b450b4030008003042e2800b0b0b0b03104061002000d0314031640040a40080a0075a207141c400c0c0801e503510034241949000c158001c00f000d203002c605010360078040d00b04140c0c0e5030307002642217030031b5480c0d402041034402940503004a101844c15031120707105901a011245e4092900340b4107010b42400c3c0c0c0c440c030440c104504481c13403c251950901e030103c1d00307580c0a40300360300d180d81d18101212201c4260400800b00000d8403428824010001f00c421140c90002e064800f08034030781240d82c101d00e54030000c4080415243c010030051441d11210081c1310400740c1c0151100411200c210140320003601c2d94044846d603803402600e09041e0f00032006010320040b0003031010440728115144025000c020003481d03001c04c0e030300406c0c01011800c1c0709072081c9224010007845011180c1101074003030140101200e000e0b1003514000a007a24044803c0d0013100c02c030a14418801303003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 633708093 1250 633706843 633706847
    0x1518151f120b06031c090512010207050604030e030c0406091406120c0d080910020f0c0604050603060909010e0d03230105152212110a0305070521030c0601050109060203040602060106 80
    0x400c83c0382d141c02a03030801030110b1644403403000074040d507a0702c1d05402ca0404082104107800040100102d80c0b05020480000701c00050540c0c005405050000990349060002454449041c50054000d0b00342040040c41202d560000c440b0700480c0400035050341d440105100403002040c242c946954000a020815410602c0700c0c203412074000c2c256680f407d552080401c40120101c20400010307030284010b0b00d1074010a00190041440c2190001c4ca01031030040018058000a07280f50700c5800c50a0220321008001d60100c5d0020300710030241c84a08014403c09030040021400000f0008800f044406e00c082d8409001030590328010629191030300c80c0c104c168005d40025900b24800040d05e108a843c0c200f0071001000280f44d44407030245260541d1800c88803420321591500c1c001c000182090000900100300001500d40030f5a030804c50000074201a410180c9111816500e4000001c40b40244030002c11454180d603001c1e2515291550703102001c0365079229503c2030320010380041e40140607082c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 633709343 1250 633708093 633708113
    0xf10050d05030c0f03070c0f0807060f170c09270a020a0c0b010810140402030a0314071502030a050f2a0d0f1d0d021518151f12 56
    0x6000703008481c207044100110500e426000036182c03500ea40040741c50001c01c43e1201f03402c000350058810450410b072a016242e130303a400940c020403061088080b8400d114510500801d05642c500026032211400c0444e00e01d205503000038150347c09810041c403405051542c14044041c040d0465605480b130b41e035a10480350094000d4001941042001851803000c0b42010580c00c0c00b03442c400000c0e051901c8440c0c5103c0455001c4500481d031026044101310150740c1c00305501e02e031290982064984035080038802d101c18414244014101d050086543c0e803030500719800b451090f00444001c120300e440f8902c800740d445400300d0342c6884040c001000788404801c0d0784900c0e0030700e21444158905003070f000c10041c801e95007405d1101c02540e6842d0764000040e40d10305404000b802d68113000c3c2c0740120b10740c4002034a40c4000508140c40c0403107400414101c40c04076104c00c0380004044207030f4070074440e89600e98441541c2910040800d842c074400d54181641840110000ca8000810700d403081941f9030764640e198 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 633710593 1250 633709343 633709369
    0x50303030a0e160603050f0a0605030d110106170a0c050904020a09020f040e04110103150b040b0f04120c09060501051218010f0f09020a0e040c0506181c0b0f1005 71
    0x15010340804659503405006000b0041d04c45514003041c2c034602801e90800401000f040200540d00341001007000340c4010600c17208022651401d02c0b90138143e4041d182c090840e0340d008805500d0010200f2a02c250080f03109030000c2d1280d140007000503601d00401c603000c3c5003554043e61202da0194100a00c0c1030341c3d0300a04e007407000741d902641840e40c2c80145012100d0202d9041e40e0b02c0b03203d21041606503a02d4495500300428040718911118184002c0300100d008600031035102100003e90800c00d0620202034038018a80c425140110f04240e01d4842c0c11080a4030607040542d041c00008145503000b5001d50f04466507001901d18141ea60501c0c0c1034070001e41e1240c421641d50ba030010043c01440c14050040070b01c22111011500b00042c1c818070454100c258403400008038001c040c0f0002443d501180c1c000c940003207030055100c24400003824035500700d035442264081c01d60821000b0740034041103003e050500503a1494000e07610020b84401c0140104e802c0d0180140380c2c0340500452601e0040e182103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 633711843 1250 633710593 633710621
    0x118080a061406011b14070306020301090b03120901030207020d1b17120706090f0f0b07020d051c0e070e0906010905070302160813030c3003080c030601140d15050a050303030a 77
    0x46e02c0d055800a4100b00098005a5920340c0000042c031400d06640a00c0c00c050b501640102004075012200240500900d460740d07041540003d00c2d002591703030340b030304a82c0e43e03d41114052401c039a52001301c98604509100313940d05920540c128441c21100030a52854204000580710314082650340c0c2c1d100200b14114048640410880c2d0030408142040c0c01d108615109001c42c61040c1003101000e8541000300059104000301040800c800d11611081c0d0b841d80900f81ea4007161181540d60306505143c0d441d0400340189280c2020003600000c0002c040f41280c21000c010841510345040881c16441145403072408040307041d910750009800c0344014a2414513440f0124900c544079034480b240800c2c16072208800c511200f00d1140b41c0c4801d042c0503070214002e403650a28008041d0307009001d2001c002c1c400070900300e011002400302e0740035803820b2640b4a0070340390b003d94418528104070001e0844000d50016138500b2407001c5428100312080b0b80603204000c0046003159590a00721015084907507120384 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 633713093 1250 633711843 633711863
    0x807210906110c0a03030608032d07020904030507112706041b0507050d17070302180d03020a0506070807140313050109150509060709050f0118080a061406011b 70
    0x20440352098040d04680c0c2c83c6001600324a60307142070040a440c2941c1000c0a50340082010b40c1d100c1032040040c20860401074403c2c260390144004002450140400194115248804000405038030600800c21035205200041881c10701d6800d00100340404461140702144104e0b4802200d154904078a90150000744085808001c4820704d6111009070016800031804c017061401c1045800e001d6041040700626084040100d841014403500a02400d600145540000e40d400d50191081d130000068030043d09204440d409403900946e510064070741070307419015010200b440746125440041c003502d030036516180701038040e56034204141c3c8080e1510381c001c5054101280050005c0c050100498050000510041346413881103041d200024150340c001e402010800c1100307034004510a054400941c1c00841d1500c440300147c0d00c5c0a01300c1262501e8610840f000140a02c000820804440c0718000c20710000d41340d4410135804907030580c2d10701c1c0400c044141c007029844040d14400d081a010740c0d6102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 633714343 1250 633713093 633713111
    0x80c061c1b0215160504050108040303093804051b0f03010e0c0a1401051c0f06260601030b1317120103140319030506040e01050114010807210906 64
    0x5054980c0c0c0c1e841c201c0240c1c00c010a00c0149000d855100c81d400344525900900314111a40020102e01c51402403e05100400d8081424144268043c0002a40c0480758413020f580c1c860030106081c3c10a40f82e001c604451030078243d010020900014010f5a0100c01031900c160000c401403050101016078036080001200640041d0b9001d01808000d400540058a090320b49007051000856154202c019100b001070b50301203041c1da1220480c1c00d60911500f0202c3c82071203000c911400307400c2021403040100e040c098040b45210104030b40440d40141c0c605100421203c005005489402c2440050709081d5840c0025240006c0b650000c07000d603116000785600031405460003a0326401103c400506c1120001c01070080050580070803050041080c0203500b800c48148008100304017017000b401c2011307201c4000c00c0e407686840c4c00c265a0749407a1070091129603161215051b0120850030042e0004851201061000c0c1c0240c100400882c14000250200b4049501000280418440c1115400d90b0341c4206 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 633715593 1250 633714343 633714371
    0x20d1103040b2d0a020d1803080105091b03040b0c0c0d0c02010e0402071e081b01270209010303050c0c09010e04030311040b071b0f0618080c061c 64
    0x451256100345a00c26071410f02d0030540c4061a54000c1c800040240c203034880398080c031002100340d4001c00720740026a03035948807141789001d82401500203690000f0800f07140201074024904d28103a4000b914100c41c141d45e142c03c2004a64032881ca084070407401000402c021136280c090031940004030a0103146403e4030380c0c40c11440c0ca100e20846900050f450702d00315045691115501c0880c0d8401c48040d8101480764840000000802c181443c00f0702119515208125050050304c090552040c2d10071340810301035040c5400b820800103c5a0104020581d0400b001540c0ca0f45407090360300608510300307070780c203540e410350303260307108464029061056134000c00c2d04d540d440302c1e414043d08101c900701d211400c140c0780140541d01da021808021540c103100602c0414440ba0645484640111070302044003205001c01c8030203402600703d441c41410075040400c83c283c100c200e082d80500d207440107004047c1e913442002d40710520354008550000b030405c00c00700d15280c42d0306070524034549040000381d00000c1200c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 633716843 1250 633715593 633715597
    0x9011202130b0c030a0906031e0c0207050a170c0a080a03080406020f1b0d08010e070c020406180b0a080111040311060903070311100810050103051008030703120b06070312020d11 78
    0x20f4000c42e807002a40c4001154400070f03000040041d0b04040c800074002d00c100b41c4520140c1c2c0f28088005603150045490503200704100c40003417202416410a441d11a1088545128500d540012030301c1071112556103804c0c4001d010040340c1000300544071002c155036044601d500050016980e880d02441441d8044110000170402c24410304141007860302e09641c081e0428680340804d40912141c1c800400c031204143d0f40307850b401906407401c1803c5400034800900108440d400c8000c04c40c01c0da21201a80c4490f40d400503485100403101015465680c5610509965400424512450090008100245041030044050040208994240034415022a183c050154001d40f00112403c030b0612040c1004510303c90044094a0000000e1401c040c6401c004800d034031400c8c1c10141d813100000c5201e2005005c003000743c0030020950340d492005040081251411050030320010b40381c8072030140b8629021046603801fa80c181c50b69082a441e01152200a4002070034102080742c07204c582c2921140f030940 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 633718093 1250 633716843 633716857
    0xe0a08030103081b031306081f03110607050105040606030219031113020403060911120c0f100c0b0403110709180f061b0504030c0911031614030106050d050601030209011202130b 78
    0x4011b0829440c00c070008100900151481140c01c20f81400c0d0480400c085114005881d00841040142001e907004608c8a100e0f0300c0014006503e40350500c01004103580001c0100ca0003180c04201030b504040e060809020248001015a9841440002c03282001c18012034000b000001c01800c01e582d80d00d072030080c1c1c2c940103000c480c80b24075100300c000300b4900f80a214040c00c41c0c0c1c0004011070944200844c0c60b4880340d00344548503198403e08605801d101e40b01c802c40c502e511100e40c1c0f034a420a894080c1c941c0700400b0304a111801503030000705024040d8031480d0845101d80c0074280e0001c03190348500c00c4c0441c207280c0580c1c08544490250114194040e020003010710540d4500742e40340e01e54103210303080110302e070402303c0000d00313200001803445026416690000b021100c90b40c0c00410a040030355030030341042c01110400e2404000010b20940010180c07090b0844100c0910141e600c00004604a01c240200103000c90800c05140f8507000003640546040c7c08951005140315407650624075451300454 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 633719343 1250 633718093 633718117
    0x1012080307030501090204080a0303051918030305130f0f0201110d050d0b03030703080619260c030609030406030213081009050f010504021509060d0504060f0e0a08030103081b03 78
    0x1448a02503040c49024014144041700314203141c2099104d58454051440240030152102c020a03182c00107840800c03480601404100082c000d4419803084210303c540b001c2d408070f490180010030b00743e40000f0184046030302c4001c0c0682c1045686d41c20f00213850381d083c103030b0400c00480c47d2451485400c010010307082d10329803900c40e103030030450240d002a6105244007070b01035002030120b13100081e0070003c251f401803411107000202c0c0c45a151400c0e080c0d40160b04c182604038240301c40c4181c2500d4400d17039804940e0400280c901c9520002c2c18940c1e1100b041e034644100b03034410041040842e10a038040c09844403d4200c0008503a502d0310f0b0345180506103801c0508081d40e84d0030300020024200068a0b551107004003d1105140640024156410640075141648000036100714a5940c180031980b500d2204bd1003040315007000d060400003000b200c0340d42c007240791600460448118000505d41c100e01da012840c01e00d10783c21a0358405298210800d2800c044c4900c40300c5445000b030a20281a40c07030300720 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633720593 1250 633719343 633719347
    0x307050703200c03160b18060d0203040b06090901021201060f0302222405090411040e070e030c01030e06180a02100f090501091206050718121a061305101208 69
    0x40c1d0101405d0801003050080740c0c080002c4204040709241082d980121200c00c00c0001c0011030102040c00340c495a404811007520010070041007007507d841e518058002621840e0742955085606402c034800c0c81c1c2c0300c181c8200710100401c00d061081000c0b20484000346005410314108801282e0a8500c401d000c140407221060140000150b002c0c03101c03101903c800304010303141c90452000e40b9912464018501036500c0e1400d8181840e015001c4400800b103881c0600010320300824000d04640340550001c0c42070044200f944c2c019071284c005c440010181c40301a01c9103448480d45aa0b00b481d603000c0340c2407140a08030890025070b07140d851884001c0d0207522180300c0d845150303100400700085500202d05110901e541801220303114440790346007079486480029107485408095400041144a000d01c00c0620358002c2504c2d00c805070ba0920f194410705548246140050741d2140003401100c005410000c600480c40d020a03181e082160001070f044c1580301030a489840000d2488100003046d0303078003800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633721843 1250 633720593 633720613
    0x19080307060b04060f061206150e0f0f0a1701090b010605031519052403010602010b0103050a140f190912080609040203060a1a12071a090303030705070320 68
    0x340b40035040b5040b208441c10010329040414000b54140580181d0042200c5280c081040440c250701120140552203045c40b1100c244920013805103080e00501c80c001da14101903918103052008502240e034100070102085c40d820320102404155210070628810f40d00d4244050129040d2411540070b0003856803403658034609403074000e0581c0e6181c1d6040b4051120700410440803c0741c680c000c2c05079041100c0c0c4001d0701d00348022514102150740c22607010340b04000000104160154009500700000f82c80c01c0c0010354822015604982c40706034148110b0101c00005010b01e46100b00550740221200e105c000c251010f001d100c0c1c12100000c0e0119200c04280d201d15082580103040554845c00031035524189151070b5000c01e80710030024191002141d2104a0301c080c090030790207a0792012101500e400c2e0003020119a9585d1424244201c80c04401e010700c01c49140140c0004940b85030f140600110714649541d90100d940341d1040380705504010741c1c80c071003094540100b414802104007443c0200306441d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633723093 1250 633721843 633721853
    0xf14040c060809160308090d1b050301110c0a080f040e0109150819030f0c05120a08130c03261b06010909051506061209030316050c06040b040219080307 67
    0x1002500f4403456502c000c10203580107070300e411800260781e48030100c00c1c2c0b81d115004c0402c0090b445150001c105c1e20700507104c3c0203005030098003034048450480003030000c0740350421a507020b48a240d01e49580ca0300286d19050100d48042c0c0240700f00200807003114a0300da03844400d80124003080e08802207890700e981070344c1d005100217031a100180001602805002406d0324000700d2501d419a002402c2c040c2420901d80d0050103100c4403c0d140381c05c44141d8184001403940340880b68002c4458034081403c440100c0d4402007900c000b0400590b1100c2c50b003c44600b1511169440201451212010412042825071191103000034004060760085071564003c4d0088001e81410b50580062901501c0c002c42c0c0804140002640810810340c850324100e03d444610108821b4850350600440801804003030182c401c400000540c802c03952031031b5108201c00c8510b4112050300c00e000c0941c0c1264403013000309002c1001030808540281c8000c00d50f00e11400d000c11080350b40c42d9a5070010155400c086102420b1103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633724343 1250 633723093 633723107
    0x1b0303030606140912010204050d08070605010e012607180b011101020a120f02070803090a170a050d0c030b030f0c011403010806071115040c150f080a0f14040c06 71
    0x40b600782050015007541c400500d0f61401038a080340d104a40d510741640d00c8080c00e5049401400700176101040c500c0d001c0c00d1074029540000400c488451405000003506201c856603181a100031814503401c1c0c46010100302540540e0340a407035024001d000d0001a070b01400000100a840440b4001c0742d55400480090008000d142d00000203034010482c0c201095841400f40950100c40c110024821200c3d05401c0000d00950034010110341e400414000d40b4030001560842c51441608451078002c2071408032a4140925410b1501044042c40040b494080640118408e13175454980090600c9003040024a801e0084201c0c01103900400b10607411964400de5803d030340740c0310301845859545458983c03035071100b0060606080009002e8080000302d02030180c01e6054001d0030010743c25003000c0c200503030f8003c000d210700340042140e400c150504034016510b0040341d90b003a41f2201103550f51070303108002900e03500d103d8107005981c46044900c005841d0084030701590064030b00300e00f814103020f0081c200c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633725593 1250 633724343 633724349
    0x90708060c13050409230c1c0804090f020702120c0d03030203180a081306030b0604050108041b14090f04150c0504080609010c0f1403060616020402211003110607020d1b03030306 78
    0x641000300e240360252200b019123544017030941c00c0d42200d2809420130001d18055a00148150b9040010f1018a85580e401902d1400d000f118418444484500020b035203c2013004c5031a0411100c00419000c68000da000e103a0240040411819044a40c000542043c0f00312b0401c9070030080c0880c00c6800584420890b20240c0b81e2400c04001e100707640c00004401d030103144a901d04221600b0700040801003841c42007040301c040c00001e44403045c0c0725102414484070035a07010303001d1212000001c2d041800044424043c641010003030000545030380c0c03030001400c40041c50708140842000300003080d81041008a110b904a03000010b425503400c50002c01460b0a6940c0001b00300500000750307048424001101d800c0b410480303429954100100403d241d000700b501d0080c1d4051703c0420309070b02c0180040106508600c81c5850b00c40550fa50a03c4150103180301c3c00091320307442909810704410704044006104240c0020805a2055420350f034940c800c000c2e0881c44103986865030030070420990035001e04070107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633726843 1250 633725593 633725663
    0x60f050703060609120c0e0a0902011407020d060e0f1f0e060403021213050d05100c1b020108130b09070806010e0705160c0b0d090b090708060c13050409 67
    0xa07103800802824403034140500050501d1080901082003101b28110f00113101200c1c1c40c2c06149801c1384201c0003003081030b100741c2c0840d042800300f40701c40003584100c50001d80c0c0240a100d145400b6140c090051600c0030141840f4820f5540000c480c010030400c034200c0400c1003400b50030074892082e12505690190001e0710159100704184800aa000b02d05868aa440a034106417910103144c0c1038180008241c0c4101d0308600d000e2550b0007030007404100c01d400c801e544039003030040d00c3d00c106c0308840000300110a98180506d0821200041d80700b1fa070003980100309031900b40c54040a5485a055000c0262841070899004190401c1120401e01c1007038014080c0701030840480c5860900a003480c0308090135038210071041c01e00041000440070918003c1d00030102401e031a2400000c521004043c4080f00799001d021f81c20004141800008901c0e0a94000c0b0010344175544403001e0351010742d045415800071440006101260303d44451048040242c00b0300075021120f20460707442100e505444260840c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633728093 1250 633726843 633726851
    0xf02160c0b0307141806040905090d02340e0c0a200a0b090a0501060801052e0303200303070309060b0d0c0312030e0111090f06030f0c07020a12060f050703 68
    0x403240c01c0722420864404c00780e0240d9903400010040050a840c948003d68031a00100d008500001158441031103404510125242d9001c0760740140c2e03403071100445008825081c0c50315003018140704070704100b5072410050320b4018107071100701001240744102c4400406070004074080700c400ea4016032007015070356046101c85103245027244c03103074031800d0f20400944613403088800310300b02a904004203400d80341c010380200400c90701c807140f66000e0300003599501c90f921040494038a4148490b040c5014554880079240c4201d40f86560581e220106202840141c1e0840c1c454640f401006000944c410011540c0000f2a050140360400c202c42484903d1800f50b200b440c003250004a5400141058036005035001c06100d07034485040340a07080411101c0031035401d04c81c10b40151841200034004560084414503107a4440c141404242e0004481419a04a80101090308000340038020604180060499010b250319140c040400a1014600700e4a0540d201c1460903c80c040e8441c03550801034510b001c0c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633729343 1250 633728093 633728101
    0x1e2c21120c03060604030221060903040f03060f09020a141014090424090b1c050d080603030d05090303061311070201080606090a0f06091e030f0203010f02160c0b03 72
    0x224403000024041405180d0000100f4aa9521402602c0003075a0003440d103103040703400208005150310710303802d5441940314000105500c984003200383c40c156040203260003001751464503100d010305266203007180340555500f80b81c80540c40b8004088081c140c1c0e803000420f400c5521051040c802500358102d010024030450b02d48100d41e0f02c2c021142c401104a42c003140c010b000500070f80c4241000204004201002c4800041041c4240c0005c0d940c10300c1142e036903190851901e184802c1c0d6012800040c040d40114203514251070003008030b9078002c41c002c0d00b180d0500180c445a04100d52040d2a0084541d0001c400c00c40300380345c001c03808900380c055504144500045014198030501690100074144600c4e00e000494039140c0c0c5c0e0985c4d000450090501090303581e18201001e101c600c42c042c40c80003640a1101181103000d54800450345d0310300c0e400e8200c040786113850302180790700e1074401240c2c59500d80c400c1e00f0f07040744540042c1c80c41042d07c551480b00c0e115285031000c241003a42d0700c40002008280204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633730593 1250 633729343 633729367
    0x91e0603120a0309030909021908010e070c17040b0a2a05031602040f0c0306052d12012301080c190902070503130603021209011e2c21 59
    0x1e80d80e600b03114100440d043c031403890f080c0ca1030b01154100d09649880490005083c00b600302400d4541030345030f25008126600c0780c8020805140407200807000c640c426a4800014203074549610b281c3c01034040c11030406032125107a055a1f880900c070000040d0b07103207110078172112402100400505800d620744800000b01da030303510344901400702c4441c1140c0e4034000c0a010364a07560040c0c1c1100001440800ca0b06c00803000203002804280580743c050010324000c640400858104048805024001c1c5403d0003071803000c21407000001004280c241d52211140d81e03075405e41c07480c3d01002e4041a13044c840b4640c10511418505a20212440d1040c10003d00804d1240303240f000b00b070156110840c0241c0d4a44c0300c3e007800341c40c6d886807001c1f0100c00c01d860000011aa03078141c0c0503240110904072070f450740352a80c140341c40c00c3e40e4021aa400c034144c0842c9000c4030b40001540b02c2004461143c003046d4120383c005840c003a820b13941c6241500a50002c000360541d12400300341000c0c6010000c1c01981c1400030400b4a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633731843 1250 633730593 633730597
    0x60914061c0f06062d08130f0602180604030b190b0402030f0402010e030111040b0703030912050a0905040504120309151103040605070809070b16170c0d05030717060d02091e060312 79
    0x42001b8030403180082001c0440ba105c800301801d81061040344000b003240b802100070f5010000e501885d5003012100031403441c1c20400ca0301240c4c1c00c025605c1d86501e440d840303031800070000305001c2012969000d00012a44a0340080c510450f251420b01d40c0a18040c000508005103048600c0e20a134903201080700591060002d540c15501c0c14001d1544a155900c1e05034020442040060014101d0306803007204c059100380106100c50045c0e40e503501041d540c1043c04151001690020103550305000c92504041c4030394041038146008a1309100318410203841d4200b20303241d0758044801c580000003044144a42c2e4003400d501710489150a10300d900e01314024588500301d234001c03a410044002810708803505d91090625445400c0680e00fa02415041000d107801c0c2e0080000c10308038001c4e40c0b140c2420700c0c09902501e00c90000c3e40c440f800210410f000409095900812050703202100030509000340c0c448500040c8503a0385c0c0f0200c0a1002105202460b0584009003450700c03d03888019605008031200b02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633733093 1250 633731843 633731927
    0xe0a140607120b122a1c020d110901060203040602010e03090d0b130b0708010612060501080c0c10020a08190603110603180a0318060914061c0f0606 65
    0x400040040c01800000c1340c9043e182c440d0741c5680b00300388400403042c0c1c5a81d482e406003040300c2488440302100405000c001c1e003130502e0000d980c607141c00c004405410404460110284104108050884070f88002034800ca000c0c1c10240041c1d0022400b804100c0d0240300b07180e8000720f144c0095040c18603600000700d050030b0140c0700600103080300c1e01146508044a84c0b400965070301030186d40f01440c5c03050000b081ca5009206c6c00307002424040782015000e0081c4901002d45106075140b004550314820039000301c2e40070001c0e02107203106400003015070800c1071000d010203020380d544200a60510b000846e01500e42c4641d140d403480e24001003000040d2103120100b140e060250f50882d2240c0d11700060b4050030b03415000c501aa0300030800c0303a0301015402504c2460074140c020080326000c0d1140c104441401ca03c0c010307090081d2141e0100e401610b031034400386c9034001c042001902c006031003010807015658080c01000c5d1554035101c0a00c41e82783c2000101c1c0100150300c0e05500040d940001000b8002c000071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633734343 1250 633733093 633733127
    0xe01061710030204270b160c0c05090c04081002090103051008070905060103060e1009061a030a090516030b1501050a0c03030f150e01080f0a0c170109060e0a140607 72
    0x4944019000001c0b0345190b8900b984a200d40c2c5d1465050919842640c821240d4018035103d90703c1c0e01c0d044500500010640e5900030052000060030300003800408103010313000748041d80040c4800201c0003010811820a001010341c003507181c050071000502500e5025040b008261072219041c040e0381c0000071012f0848440320f00128050b12068016401810700c4d0b00180c420302d0703c6008001101c1c020424100455880450800030190340303008409089070380000341c0c18055810804159503e01c1d0b90405240d650042c41510440482c010f003031810741d0542d40c421281980c041080000509840d0301440403141b0a00300245032901c0c02e140101106c14880009061555402500070b152507103a01015004101c1202150007946501c00041c043c00309200e0009180714025940b881802c000c1090304410354095000e0151900b00942e5074990003503507808000039917880c1111008240b160040310b406001140c0a84803584e11030400c40301c1481d47c4050202154030901c203105220394841e904104c030f07c03013076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633735593 1250 633734343 633734351
    0x1050a080a0b0601090e0103052a010215420a0609090513140a11030c0619030e0d0e0102060a050105130c0e031212100b04031211070e01061710030204 66
    0x8a0045e1150701d80c9402016610a0140010003000b900290380003070040404203103104030450300025511034214400e4540142c00c0491031000403861844250380000740d0041004140000c4403da24a82d01421200d90019410300201c04802c1c41010480513201000e450041d0701c0c40c00d010300901645080e04c0345e040c04643c1c2d20000b503486035402501030f80c20b6503c6682ca80c5000a407043e6a6500c0b00b6100c015201010013400143c0744d403a000070301324181000a825241891055040c11412090746401c54090507144c070600c2c40c01d0f0105010f00c0a121140d5181c14110840c41c0340024a410002071145d840240307441c0060041da640d4201050112400d00000319544079800c40449a80c00210fa509d501886078140090310102418041c00b41c2032070f4110ac803001a61421001404c4183c07601c9448100710007044180007040d200c80c00205240ca403810a1842c040100703034480d1800d41c86501002151103164014850f065000c000031085a640d004001000d08280c03030311054407800752000a214641e2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633736843 1250 633735593 633735601
    0x3200c15030106090506182d19050108040f0515010303080708090606060a050717030115091203180b03090f0c01110c060903150406090b0a090308060f0a090c03021201050a080a0b 78
    0x943c1f0310301783d0716502610318020f40b402030701481c01000004040c0c0c607600d400c80440c924203051003000312844590010132242c88074070b041e0040d03600300405441540d8030420b091182c404180d04000824040303078000026545c56142d418014400c4002038015020425410288410744c640003c01a402c1081200d6069541d200c98405030740611410200403c80c4002d007402c0d04441c000c1c040558105c0740c0d60710506e01e00340d13041c00d0210384074800c900810600d2021140c0d000c012a1280100b141c90300300e0744054105e070b95210180d4101c1c1e50422250040c0c0da43c00401143c0d644081400b4500c0000b00a0800d0000400400440c0380ca45090320313182405805c01142409044d0f500304031420300100e00380343c000c032641407a081200281403000c5c1c0a440d949801c50119050100b507229003000c0b141c0650307036401c040d10f9100030042c2c072034031494085600c441001004542ea0000d80f048045084141e24010303550500038034041005d540582c1700c18811805a50108604100450407200240d03010b4221801075503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633738093 1250 633736843 633736867
    0x100b10021f1d0307060e0109080307120b0603091c021b040e15010308070b10050d0b0a0605060a03090302120306030a0b090313090902190b090d03200c15030106090506 73
    0x10441d205482d450000002d40c06041d1000c00101600c90042805201282c10101150f090703035014000280011010800203420720300c121003650420741d444001045031146540003800940050303840f413000d5001081d204403501c12201c041c141500a0f400942040702d2180b40140d4000b201c01d10690060362151114001c411052000c3c0c01d061a412413186000e50b16410070350301c241c0001004450700c8240344080350700c801408900c902201d80c02400800000641d0b03032240000b01c1c02501c000074480d10341c0000b0401d030740d85d07802801c502c107115034000880c0816800c00a24041c2c161016000d416410814845a030300c010031607204880c2c10040e0860183c880c000014a141b01d1560026000003035581c001c900c540203600f1110f19107000b190700360390106032010080b40c16095032098015501c1d04105a560504102103640704803030290808902450000e00301e40300d0f804090300340420641268150200ca445c01011185803200c42200c040d0541d810102e01924035041402020700ca440082407061400c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633739343 1250 633738093 633738101
    0x605090c0d0e0a03020a0c061704080a03020c060711150f2703040603020a080f090715050403170409060b0a0f0804230f0106050d0b0a0b041805100b10021f 68
    0x5540307030741240c00c44000c0e13040081d1079010a0b038080b2210350a917070001a819100b81801c00c001088802c910f9002d0b1900d50f100b0689070f02003041c80c000d0607000d104100780c000303007403065a00c1500c503034859006941c402d82e40d4a040c80414060540261865402d000f1000288082950f0221940e01c50f500b5020711122450700400c40f0340f410b03081d01d200000e004a11542d1640103016141e00d80c1d10303107003482d860f19603200d05480003c0740c845501d81d21850701004007100080344a40241494100141303010b882c0c0d12074a44403411040c45503844000001c0c1005903081a100350300c000d203c5c00d0001400c246000e40000c014012507000901004810b00c0440c042c44040088448481d664002080640203164641c0e0b488409210b030f1143d443d40f0b460000100313810b040b50b220059a51000148000e684d448410400410740f084500d904169900c0c20401c1c1c01446004001019000308010181510f41070468015980d01025050181d440c00240020040c0c001410f215800c2604080c0d5401c0400c50501500030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633740593 1250 633739343 633739361
    0x100218060f0c031801091706071d04060915082b1b0308090c0108190213050a380f2b150f0b0406140c0d030c0e040605090c0d 55
    0x140000941061383d00d01c0c0400180d501442070300c3d07803040d150b51b41285941e012400511034180d90170603000948028898005546549090441e9020045140011504541741508403a0b039203580c03040c5070444501011441d00092411400070101003120b2184c3d00c0b84101c1e4010b2030003051800f40040402c1c50b005000d0199205a03079500c011110300d0609000340f040c0c42c01d44d814480c502624151450b15481000c10364401ca4040510b900011309a0305900300940c81403112412140c009140800c050f0340d0807030804d004011840c07402c1d0f02e400c0c0040300b034608081c04012400246004030149100018584140c841340b0080061003612049092041e00100c42c50311101e44d040101400948040c441582c08413a2160700e0140b0b01032011780724100c0086582c0780d40650000f440c803c0c00100300c0c1c5407281c00c03544100c225145030036040c800c40c03c2d901e504d0311548000130320119031900c004600c03a036448252441135072802c507000c1c405039143c4800300b94010b40103020002e10080000300b48030b180c0302a402203542 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633741843 1250 633740593 633740617
    0xe120703051e0d0507020a0201020c010c02041409061e0103020a03060908211605030606030a18060501060504090c02010b1f03090507031208060618190e10050102100218060f 76
    0x4203011404032129034003003075100a041c0e01d44004241170600c006690040258113800602c00c0300340d0700006641d040781c2202c00702d81c03160b00d460100c1032500b050b00701e00b0b0080c0314280c010559410004140d9006024002017860039904032801003016030340d0f5100040844c0d070000000682c2080c0c5051200e214850b1001390030780b50030055044141c0c5030200582034401c0d501c0149004695030140812a17142c4030540f2003560041c8180040340180c0c440d0750060192885a902200314a149541c40005680c026030141010070300c0410b04100103c3c0c280a40d03185156140700800800d1040030000b59a25002100300c096090004d2a401d020f600a51080445030380000032900256641d10304064444051250030b40003c1880c00802c069060440a03a0f9642014207040400d1070000703402c1c001c1800a02132518640d08012500050324112680c641e80600f440b50032280340300c2d00306000a0b250031000a0003070441841004500490325003410708501d9640100d50190f628040007501802c28081c0c40740f2040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633743093 1250 633741843 633741877
    0x3060c0909020a090303120c0815012f1504031205100911030109060905041703282309030405270108060106110105150904060e0d050c060a0e12070305 66
    0x2c0001d4021100c10220b910030b0356409101e00d16103007d034064031894000760012500c1400402c0c0b0b50259191090588001858400c075005030300c1c014101c0d002d003524000b1091044c0b10400c0840c140c000d020050a0712110346540f0320300d042a81c1c00404014540b1406119a95104003154451a05140e41b80003000a4401800008400004c01005600c21b2064003d0949400c00000d02480315010b80352203240c000040221607640216121541e5100401d000a08001c601ca10281c108141c08504001c3d55071000c0040c0e01509400001c607811580710480c0303600032020307007000711043c000800c94050b990181c5030b19000d00c80e141d8003004104c1003801902c0d400c504450002c1030340440000e07243c2c1215015500c403a040883d01c40340500725141520010025a42032400300c016007001611190024826080012100050700b1f465051240610b00c202c001400003c2c01d0010203020050150030810800e0104441b10020384d001d90780c1c6031544001910a20003184071010700d0700410580d42907000b2907c80c58 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633744343 1250 633743093 633743107
    0x4080c0114101806030c0e0c0f03010e0402040e06091e030c07271e2406030222080606010e060c06070302040512060928060f0c20030403060c090902 65
    0x90070902d41d0740901c440018071100b2040d40011207004100843c2d030040940e0b00a9402c1c9401403c003a00014a0115002001c2000d00240140f0310300a43c0280155414a8000d081520411055825070560246a54003c0050000c5201b011802c03640c80980c0300036018110201c500c115045001f00070b40c1d41640d014264000650071600120310300c3c00a1a46a51509098044400c0d400c070380f0307905584c10044420650b14020008682d00c0a681410602c010030304100010802c040e40c4d0045401c01c6000076000304442e2420301c00c40500829002084021000c8035050020480d03a0302002885c50741042030030b02d110b0f0045d8a0303003011243c10685540a5603410720344070101901a50040c8165400382005070360004610700302042950041803400064150445c2031070000b4000e1b0000480300013400c1060320400f0000300644100001b02c0410700012902407201c1d18058050518510170480c2c0750007070052a0a420004000c0720150703540040c0028501003850f04c210b0760f444881d0000700450348001401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633745593 1250 633744343 633744361
    0x512011e1a030901050106020d1e0516050114070309050a0206091f091a030403020309041e0c090f05060408030301150504150e0301050109020c0709020f07081218060f04080c0114 78
    0x158880c032643c3c00240a20390340d85504a07a5001c2d441c113a040090303003201600320981428046020b02c0d00603442c10720304100c1c0d034649101035101d501000711580c2e0341d5412200c08554240012a5120160b400c0c200800c01c000c2e1a042e03242c540e1000028403442c0002000c20841e620084030000c006100c44100f21081c50804002d0209103250003000840da4603850440c481d1607003113003242d00c900d6040d0b0146040c035400005000c0a4241e5445149004030004a42500021244201a80d850543ea64407200d03034504190b160184e94036405c001c0c00741c0030412060120b0cc4000003124110b0b8200012942c0552003040105c0c1c6c117004a402c00c1628181c0e40722540c1c906a484660030310100005c5001b0040e83c0d0340c40c10076100300e00c10304401101d20780002c0f0040115a015034090501c28640420141c075222456484015513400001444118185901031010f803101d1032100c0d60041d10010020242820b081c0c5116410403030083c001801180300040224860000390000c840e2100c2949140d100307805c2245107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633746843 1250 633745593 633745597
    0x131706070e04051009090c0f0806220c061809020f1b01060602030f13081005060301180c050d03051e19020d08040f020d020a0e0603010c170a11040807030c150512011e1a 74
    0x3000e0910640c0c503140302c6021381c2f01d0800d0300f4229404000b05011a18208041c2c0d41c0403941c1841c07241c51003c0400c0020404106e00042101d02082035000c1c2e66540b00d48580d10410090700c10381102c81e85040c2c410301800390000102d40202802c0c55407682c580c580118111605d00d211740004c2002d000c2c0c540c038201540c8890308100c0c003c4004400902c10010001c40c4495140050240035000c2800300e4400c000600b0801d10700d106a078081c1c5481ca2030f086c1d041842c03035800044040e400d4543d104c0080c0a4201001d20740c80c0a0b401d07080e91000e011030f084003080003081d200740504050407820f0300501001c1159201516001c80982c080d01a0044c50360b185c3d034403210b4403401c42d1194065401c112804500074854464100d14480c14240101d964a1704031441303000b0203c011503502131440400c400b0404041c101b01d020010351184003007051175400e1484072094400104000001e101003032050481068007640c1d083e041d84e094505a1032015807840055110110a03030100c9c01c0400c020030038000540007500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633748093 1250 633746843 633746851
    0x20f12042d1d0105010c0f081b0105040c170d120c0512040515130309120f0c0f18050601050d0c020c0607060905011d030f131706070e04051009090c0f0806 68
    0x100c4002d682e030350070040d250010700481c014040503810000c1300006504a02418001c00180aa60810b070ba044540a0840d01c05450580e141c0031055820003c040914480070012641a00980400c4c00202000340240c0004012018142c1c9c0341c00e0340e039414038426020b44d40785402d00c440b500064113144c188a51541d0030302c2c4950006200c20700010742d40d03502c4c2483c8805039075070558a2000d100d18001080124940c1d040b411900c0c42d400344107038008682c01803050805440018180c03404103180240280088107800240c003103c1d03003840d0130003045030703080420b6800c0113440e99400b150881d0401c80072410030b08040315865000c44003081c0380b000e0040039488151118440e1000300318151400c10802d6a18403400c1ca01d01c000d03401040300080e200c0c0003074064003540c1c0503541c9801c16030341c036012200f049144041020007507034464020090400e0303220180e5070b40c400042d94200100d0808001d60f040c424824010f640e002c80e19001520204042c602f00e001c0181004c0829011468842c58441c0d110702c420790b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633749343 1250 633748093 633748139
    0x40c0e030705030f03040b071529010201050f0f0402041509020703120e0a03050f09220b0a030c06031a060a0905181e0903091201020901020f12042d 65
    0xa0020846080002d120981050003034015401c2911f04800409a948500b000315040b40b40104594031f41d0045001e8000101442a000164517840184c84260305800d546441c5c110783c1004c0034000490448002a50000c07013044048180b5901c0740007150140060303100c0301c50302c4560304500040147c290b5015011030f6110380c0d2004000344041395400150303003d0f00307a00151504009003e000180c0100010b2034a642451191410320300c038480014031040c44482c0002c22010203802d03001c1006044e1040a24000044610160032815620b81c1419501c060065205155491448370076254480c00d4101420b00014280d9542e07401c0b803500146140714a100300c90240080d82d8034080d0030401460b0540c842e01030884800d1030b4040e44070b600e5400081c0500781c01c070380340402c10020403541c489140100c0401142e03400580d80304501c6000a180102188522030650000541100e441d006041103030111781100f030742c5200f1800c240d14142c802020b5980c2400945040d52000030b140000041940c1a0b25548 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633750593 1250 633749343 633749353
    0xc06151201060b040b0325080103020a12051c021515010809120304030c03030605100e090a091a090106121406100815040309050d11100302070f060911040c0e03 70
    0x34040e020300b0380340540070b01c4128000c24042803281c02460310240d0303489040700d1030f110940b03144886002c40c20000c1c20482c100103500e1030014030540c01c00d60004401841d2104540c04c079083d69840701a103407801c14540c0711404c0b40c8003140d80c0c10b0610030420b807441800358000c00c06140c10b00c100d14118501d000341103d4086600c00c4006070000c20045510400c52030f10140ca02e1031592241c0e8104c0d00034154440480504d40d40c1c180c04106038940071903a000304110740c1c950620b0048010200003206d030b4003c040020450801c1c4040d400181000050700f100800c1004c42c0009899240c02e6070b015052a4128032000640303008500c00b0b01c9011f101642219185200360707001c1da1201c0b140403140364500e000e15085640100943da54401c1c1103448594002d0083c0b400c4003481c2d80710750007d440c000e107007401614400050151038140c3d14150143d0329a44030b850804500d040075035500c18524000050018111701d40d5500500b05103e0752940341540d586005004000d04403405c0005400c0b07233040c0400c14007030b200b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633751843 1250 633750593 633750619
    0x200415061d01030615052818080609070302131b1806020105060d031115070c03030b09010e0103080f0c19062d020a180803091305010e060405060102030c0615 69
    0xd205071303401d40c0c0200343d8102040100260603141c0380c0c04802c0074601200403421141442000018000c0741e42c01d2540c948030f9130301d800f200141101e07007250090003040d000310050040c65030f4002003900c201d81d41542d03a00c0c036501100095100400c59942d102548a1540c020b40080d583d122003644004c603070514400110542f6480100d00b01d8508950362904041f9803c3c0d4000443d01601c05900c4880380c850864190300d00b081056416143d058542c0000314540c40c85400803d5014050184d9002c030a5a1480d0103601d81481644002010b10010780382c507000058520341d8074608002c0b9815805d10408541c524070850380c401d000c1ca0311100b0140c502d2454000c1401c28181c50301074000d060440c2ca14503041c142c0500b99420000d500100300d03032082c0a072030b40380d403088070071004042c00c0109160b20145842d60341e070006000c1c203045c95609400966103002e0040c04521854000039800c03070340588001809076203100c010303451481541640700e000d22400081012044180c0c103a0003002c2d0301690040380c8184 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633753093 1250 633751843 633751847
    0x206161b0c051e1e0913020f0a06020d0f0e0f0d0f082a06040f0206090102150c03100807080d03020901030f150303141321020d030203030907050a03200415061d01 71
    0x1c84513440552140709000866200da5460003c8041b81e800102860141e01c10300b40014116800740e8010005604000711645015421110a10300340ea003604000d0305103000003000487c1407081340702551180b2040f01c41082480f544044000e42140d018103030076580e503c142d10385c0502d03551625001009101c40d4031010411400811075500a42d40661803502c03412540d420403070f00760030140c01c0a045100c4c0c2840c0300c0d020f4044046d224050141c1c3c800259881c2425141c48443c980a44c00c009050360050408108404001680410308800d034500140c40e903980f080104c0c050001c004056008c2410078040c48060503141134041c04492003610b07034800031240308506030f801d03000e4030094000c80301c21042c0401610280d8907080d1045100c0300a5204607e020303900148280700f0304030050b00180d0002c010840307036903020040403000c1c05088584400035451507079100d035141a81f80c0034000c48400e0202644031611650850513080c0c4035015000011910340e41d008104120b83c484226001e00100030f1249254 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633754343 1250 633753093 633753139
    0x30301081011030a0b0619031d01090201020703060f0209040c03020901020d0e150f04091104031b0b1903060f18141e070c12030b010206161b0c051e 65
    0xd072010b03882070030343da1400c5800b4002d0002c41d540ea604000200501200000607090130103a881203a100010604500c0e1742e60b0022800200b408912a1302d800444c40250780c000808104580e84510003084588a002c1e410000e4000c00c100c40303402500340107070714202a030150050a00c207103080c0c0c02c0360591890000220b83d050b028542c0b071a04096010000380702d5001d0b850050003049540d00c4680c0c034143c1d9998043c03007144c4900403045001da60105050003080380000342d60511640541403107020318103001e03040e200c512801c000c40d0301000c0034084503c0600c1c065005000100400445224102d1f40e03880d0402ea0646280c8121000b0361414403c0380c421b208441800340a00f5159071990b20b0700c006800c8080d40100040c0a80c0b041c014010080400141c080114001201880e9008100681044006841e1810241240c06100d824041003a40d03030307500c1560a0101480110b86161180c900d0030071019510080e04241c1c1c2201c1140103000c81c00342d1050528280790780550788041f21404040645902c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633755593 1250 633754343 633754361
    0x90b01090e16170a1502070c090605060f07050a05060f0901111c0c09030c180c020d3006030503030601080601021506270f01050442080d020303010810 66
    0x781044550a100c103003000c0300e4034142048010308907a0318010507160074010080b10ba0800e03110603000030700c1c2e87c02c020000221000400d403020041c40724a0810b000a0b40300e018540c600c8142030008290241440010098000116080b10640340103050904481c800c5d210111541c02596007003a100300d00d810301ca24125800720701c2d10700d01048080c82c0071407c4400b9000b802c42000c10440c50b00c5011000c1440c4e030344450010700350080301c00e0042c0d058625400c182c1b08030000703800564200358024202140c00c00328601100c2ea0907810f044a100c03c400004558404496070129401e10f440d90210030400c000000b140604400d8a6a401d6542d6000049a03209080c40c119180d600218011414604082105c00380c4001018111300179030b40ea4440790303900b20008445900c210900d140040115013068800c6010443c1003120642038002000711003030345403904172005104444a1403091000601010856010340002d00540340082d90843d002580d0360401e004200840c064007240711800f1006104002d94 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633756843 1250 633755593 633755623
    0x9021f02010c092313060509160221090d0206040b130906050a0302031203090a0206070803041101080c0f070501110c1c080118020904060503100911030c030a14010609090b01090e 78
    0x940b00500740700706514070174000c40002c0d40758800420959200e41a4a1040d180a00030510180783c402000345403002d03082101520019030041c0d81c1d000000b1004483c250101511801c0e0761680f907201081d400d00c22548006c0c100000481c08580794400700300740008440e1010b0050210980b22401c20003a50001d101c0203506900402d5000b220000142c00703543d00060714000d44094003c6130700880c10a92200800700d0340e4640000400c000c02840b40d018002d00213003841e081c100303442e055240d060244a0011220f1074844003180310002c22000750001c4903104000340b0502c0d00d40e001042c006a40e000f0311001d900602c9803003d20086650710905201e4100c42c011094040030210594030100254060161a0381040d00c1e070030003240a84003000700c00261070f040140002d00140d2030a102c812100d03108409886a00488074811071650005426688141c00440c03246900500300d82580c0100b141d40e010414440c01c1409550600406400141c12030b2000102031040812070040705460305041c8242c085 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633758093 1250 633756843 633756899
    0xf032709060d0b2d090114070f0e060d06080102030f07050712080c0706050705090310090807170c07080606010f17072001060807030c050d120309021f02010c09 70
    0x404100481242600106245003821030300a82c030130416640344042e800c0c07079104014001480b954480912444a48051942c030620480c20104c00041c01a144202ca00040121f5401310f55200e41d50603048070020f024950080015aaa91b691a0b010750021074403074401d80b003e40006445640a401100c0005610000c071400301d03190340c4000d555545000d42041d80c100f4041c003103140000c0716440341034003c00898481d00d40745c4078400200b6250000e800e028640c094181038140303001420440659051a41c0030341c0494a10b541c1e031140c03007814080d00718507803000e1240501c002021a40454064050f607400c5c1d13a03800700384941a1058404159000c0c14518818040d000200511310800b0500c0005030982c0c0c03030303041c030344a03040c17019094681c503400000342c1d50031003102081045200d25074040203110030703a8800941101500d0f606c50043c1c03080b08070401e140c3c507010480c0441d582c0010308039281100c594844007185140400038002c111204080011500490b80841c0e02014074059422900c0b501502d84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633759343 1250 633758093 633758119
    0x632040504141608061b04140418080702030c0a050d060b03010e0a230d090909170706051e0c0f0711040e2a0f010c0201020f03270906 59
    0x1000302001801602d050341c540c00181c00d9004103000007000038415080c0340001d107061000842c101100070b00300703030584002484018031088030714050b43d00f210708100c40c4c0d010001e500000704000e00301900304400c84210b01c09008003000542070162420301c0c007d40446201e46107500501004404a000d070a034020309040c1c0c4040022003542160000d40b40180c00881c0941c10503a01a01d800302ea002c0c12100b011030b214040750030304216500340301c0016160b8018000e40341c0030000604a41000c2c0200300b107080d1650380043c203000d0030090300c4204201022450b03035035002070304008000705410384038070312502c1c0620100312110700002130860040c1c80a04060340341001c10400480c0d15030050100f02c400c8080ca07441c42d482942c840c810f0741a220040c0b00a0107075143c0c241070b260441c003030081c013680d01c000e18004400e03110349a2100e042d80400c003e00b0a554030508500050b8030303124858001c45082d120008110018010320156042103003020140150300250140800841c280e08070b40803508002003085613 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633760593 1250 633759343 633759349
    0xf010b0d02070203100e0102040503101b0813080301030303141305030f07021804052407090e191e0c0e0d0618061118010806010e010f0203120a0632 65
    0x24036000f880202103c1d110800009190180e071061054803290b654003003410071290505200c810000b90250008024070341c00710f81e0480d501005c0c218034001700900740000480d2040d151540b6040a600030150750746035a56840c0c0240503241980c4210304c0c540301d00b00803a114510341c00f51002c4040c2d100f0b01543c10009580040821a04160020b80e803007103c0002c0d540703c69405521050080b401038015050110400c41116140b46c00e0740750780e40d0220340040400060a5101d80b580050b03070042902801c040d00c0300120b4440f00089070b1482407001b4a0700008030b061318003440550000c405080303824001c41508810540300c1080b00358525401045945401e00059000e9110202d001901304954040c2002921004102e6212410f000301701d007000150f5204a0008945d500140e40091030210780178945080000c0021030140d6441e4144841400c00a59044c004c0c01500c4585010f07007031280c00ea2074080c0c4180054a0b180c400e146a01e5007500240382110390560b984078001c0200300b100e403c075031000c20034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633761843 1250 633760593 633760597
    0xf0a0311070b0c18041509180b2202041b0801081204050d03170a0c17070e0d02130e03041806050109060e0105121e090f0a0303151a0d050f010b0d02 65
    0x907031803d982035a000260306030307510b00c2054406d114105410302102c0c2400c2044003220840c0d005a00808421000d000004503000b03005984081c110210031128000c070805a24013036000c1400a40c840e040c8146841c1c4c42500300454115200c45941d110b1090341da428202d03459110700300322800e96440c1000144098101404d4081c0100d12074501840c0ca01010034215078010300a40b0000403060301d03220115012a40809000e90b400901082c0b034030607041c02d6002500a10801c542c150155815080d50310030b660310364103240405041688180034092640d04181c2d1681d0081c02400e8054060071140d20310302e1028030503c42a40c42c10b0712048800c1e030402906580c640034040800d030402000700450f00c0400c0c40c1c0c00e21b10f8010200d00c0320907007620140000c4000c5100300100403124560142050031440d41c400030f00c0c2d08115406081c0004d21810000000c1c01809060b0004110410168041d43d8005e00107801010f904500900400064955810903004090300b88a0b0140f4000188041d0b0003d420b01e41c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633763093 1250 633761843 633761857
    0x10e0f10110f070f08010605040b01050904150308193510030503040f05030d030c1407080405120a0302060109090f061a090403030c020c06031009020906040b0f0a0311070b0c 76
    0x8121540b14010b100700034500b900a401c070f01006012414108404c075030174062000a000704076070a2099000c04c0b0002800d41c040e10004a00c6a80c85031030710211020021106405103400450482c1d4810741c40b15003840040040401100142182c0c003c02420f55050903039440c40f5910b20b403429691090103c6207400504044e10a00600c150f920001000590400c0100010002d8400c0350250601c0c10b003c144c1006881c40e1b840703041c107081041c0c2c000000ea101c01c817034031014004c003000d644030006030070510304074055a0416608801041801207950100041542140c1d109a085a10503a01d0380d00b114248c92940e13400804410035100c07004000f030819040442010030180700398804d0030900300000d9200d0f6050b074040d400f0980c2c5030040e80c211a4180324003030b1a140b007940c0440c59400e08101b401c48888a034400c03079034600da022070701d040140d4a140c101c4004011482c1199115400f011110001d640312408172808286048400b8440c00f00c283c0a650049801c403056900613070360302000c1c2c445540410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633764343 1250 633763093 633763127
    0xc010c020d030e1f0201151d1b0405030106090203180d090e060409050613021201180f02010e0303070602130e04020105090d05010b150301080c150a0f09050618010e0f10 74
    0x1d45030103005121040c04d002680c00944c0040f81030b08481080c00241d43e807942144091000300c90184000c50017401246800010300120000e504000901307911642c01180c02082c3c0c03550a0a400048036039850b0003a40c0151001c040da40c0307c2140010300a41e80d94901641000414001c06003040b07014000441e00f544407102034400305080c0c100b940e88500346802200d2080c0880301401907501036041c65000ba00c0f42001000003048020b5440010402002040030020082d5210b440503208591003464410102100075089985070200c0d45405400381d04050101043c9008100000641203001d0700903074043c43d01070319001c1c640201e40091007101c0a1040703041c3c03060340d00c45145008544600300c03031100003010480309039120350516200c5410100340c00e072511f02c145060ae4a400c0c0c90255402160505201c500303111100d40c0400c407054421964a501c03160303002c880411a1007a6072034031300109402c80800d0783d035003c520032000c0c10003014441e00a2a9034000f0f80e40c0c1e9140c0003580c051041d10345010200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633765593 1250 633764343 633764359
    0xe04110d111c0507030b0a0602100c09050f060903030d020f041404060308040501030f0e031602090a090309170f0105040c0e102d0b0313030906051e030c0c07090b030c010c020d030e 79
    0x46c0d0046140c41040341d01400060344465007406804440b881000c0c450f104501e032405803203152500095024212001c1d8500c18580090303240d00640e400c03c2243c1000307000c400e00b55101c0030b6a0402001940191140d4100c00c0e40f007075481c82251815204010a699001c01c120f03081c50b00f4000118000d1465600c0f2036107080d40c8030f001409203501000601010381048038159002103961042c006400c0001e0044c9000310f080154460000c0d80101111094035900c9010480f00c0c00720a0040f4500200ca07092100c19528043c18030040c01102c604000a4a0404500700910f4644a03a95030074250f043c400c10f20240703150259a00503075445004116525480082031518548681c5100d080780d0081d00e8109044c410341444400305500810b446000380240e041c41c608203680300440494100300c510015480e130000000040002c065002603806282d10081150401d0b911200848010810400c107140300340b01d80056885c6035807003240d680d0059a80a403a008401d00382d81c0c2c00f615005040c0042540c40909 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633766843 1250 633765593 633765611
    0x60f09010e0a050c0a1413150905190c0f02060a1a0310051b19050702210a171e1303020d0b340804030e04110d111c050703 54
    0x30050010b00e180603401420030114030808000c01109160b01c1500207014a6081382115910f01443c1c2182043c10300303010441c0c156a01210301050075039044102c2080c600424008100590305841000c615200410400280354402c2034550740d60b0f030306d07020005134814400200800c49035003008248075206910003040ca5140f1300000d003020405444c0f00b01043c0d80d001080b00341c0e1030a100c223444000d60f0381c89844c035029441e1260802081c92080120900c0000a400c0e011510703007188e69858452040781c8580c04030601d00549489144051080c0e440480900292504840460032545401007000552504c00c04480d0750410035008a906112102d1a0190010150326001010000d051048113078012900d0b00c40055401c8625415042c51125000ba188080350300300710715074950484141c14001c8540c1d6840c5421540c440e818900d0380d80142c20300d01c03048200000c0c180601240d0f282e400c000d001c004e00f4049101f055024001501d000d952000303944405480c0d030782d401076800c0000c914020801ca40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633768093 1250 633766843 633766871
    0x906121b040e0d0507050c1507060e0a0206040603050f0a06060c02090405150c1201120209040b06040615020c210616030609020a0e041529130e01050111070305060f0901 74
    0x2035034407140e00890070003c5c0c1c1c0f00c01c10109001109040d8401c0b503507611180310188a890b524040c2d01001001584da9190304290700508001c0c07652055802800682d80361740703c0c0340080107040140d6000c005440400042201c181c014000c080c20782c0d120396500c0801244a07020466500c001820982d441d004100d1541006251940d01612420101e507400344c0e80c803100c2101941c19a4140d22020038051070b0501e400c010790b118180682c1058004440f0352484c0c85034000180140a00c5d44522468640b0900c80c100640d008202070070b0701402100d4001111126a256070080c03400890b01d0381c1035801410000b0080c0c5d400c0c3c641d01002e01c25514000400f2a101c801840807a8440c0903500081414100c00b02e61524050080003003400c1d00803031a20074185040e2013000100100520351600d061544a013a6620100c8010b0350700c16214220031219042d52030b40502c144e00300078042c150015041500c59505d03c3d00000f51703002100c0c3e001d07005050682d1645102855420090040308440d5204c14000d00064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633769343 1250 633768093 633768103
    0x903080c0d02071b0f450501060306050307050307051c03110609101113060f0201023906040b011406070b09010605030118080306130b0a0f050906121b040e 68
    0x407003c0c40c403c5151350300f0031008101c0740031240c5c0a140140c42035899001c1c5200380a00d803010354800790f1a0301d01d140c80851240440440031041d8004000d1030000001503240c1d050f04118100c80080e000e80b40c0494451003031545460040c068660088104089549401c01145103d89a580070385021803084109101306e07801c0001c03d5130101425448420803001c40c986603c10310010124012809240080718121228148502c4c4503074000d209201d11204140c6000390101c46031040442003151404056202010103001e01e14101c05e0121000080c0507440c5000050703d5000d20b070400c84450307241c1e10f4001040d03005800c0d50300040c0c01080030711003000080c160007007080c0100348040010030170600304414542120202d012203003078158034502c202b000c00c0c0e0b8130342242c1c0c00c8003055501350400d08074114004064040c050b045604228281c0d00050408000c1c6038400c1a602d084403203030300c1d98803403104100201c400fa841c40e032529000b1300310444d111501c490041e40a070703c0251000c111075406241130b60030301d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633770593 1250 633769343 633769373
    0x906040b0a02010f0e0a030305100803070602040905010503030f0d020913021b010c021c080c09060f0703021501031212090503040f083003090a120e040b040903080c0d0207 75
    0x34100840c0c0941629020700600400b16102c01c4100030300c0b072040030407941c0c0310703564500079090564540128155002c42c00300c00d40600709440840b0b030345549a01c0c04400941c020310403a00c0b011310380b400124940c40c011044900c0702501c03508107810b000005038003000030750050705a10341c0103900c100800101c540a0000d05880902080902c0d0700c14007040000d401e41d644401041c0454009121000d03078610307601454552030b802c602d01811183c0e00c40355008002d1041801e10381e400b039004200783c030014203031000805a403031185d400d50741c0d48105000b2340c44000c2000e002c010a21400103c41a2515124009030004442d81c12070101d031811103603d8032800c640c01504841c00820320b0741000d22096a0400c4842001035a05071220640c60081090400c0000188038480800c1e00000110355841e00401035805229046991148036500e040070141c0080c070b40d011028011030400000b0340c0c0910340361068040e442d4060725091030541da0980305070b041d42d1050402820a41d401e100807000f06d6003c003100150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633771843 1250 633770593 633770609
    0x4060501090506030d02031801020a050712030f0816030b031f0516080903031501020f0111042102090f06131b030e0304030c030803192406030902012102090604 70
    0x15506185101d01903480040680d8040d9202012141c4007550010841d200c1c003240c078803041d4942a4000040303050021400c0d018205120f283d6010801c25040300b06440058801e0320307001042d480552090f02e0030907086130f1a11541d88013a1110015070b000f074110800d611001000d0300d0741c0324588041d280360214400c074500401075450013003000704401c4080e5101001c4980c2815442c0f85440c8400f641d03240f20051482001e14650f02a1002c640d008200100c02c8107403601c000d20010030b5010403101d182d0001d00c40e22061100380b00344042882081c0910441458020b452a00b85540d04170090361403010140c00140c0182404c5a9000c030b420b030700c0c81603519000c1c86040f0002401210000101a59011a11852190401c1104000140a0714a0032003103a0384040c415450f175a426890805c422445005a0403050400d816046100190411a800142000303180980b65407100c90441c2120300010000340454641c10340c00b400c1d40035402101c04050741e0f001c009490000d465006c1105600305500c9109 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633773093 1250 633771843 633771851
    0x1020d0801060210051005060c0c0a05190302100c020603071e0e061b120c01020702040b0901051804060f02030a0b090f19090503091801090e0105040b01140f3c0109031e0b0406 77
    0x10761441e0021130bc0c070042c0411181c80e42490f40b8042c48802407801440002d2140e200d01c0003e01025001d20071251107103400400d110340ba0b1902e480042c090b001181c070340e05400e400e07203540351110300e000302603541e00810041c01c1c80c0d00742000850402c000688803540800513104030040718039245c1c5608024405030601d080003588420a07072040c0020741c3c0986092604c1b030f081c1ea00c012b008648840b582c0521103e4a01341e8403035a51518140700e002040001c5403030303422500010411900c03400640145407100d80c1622140e0b080e0303440042841c9428000c4c1c81c1c24030b00c407101c9500782041c100345400c54480300b130092050740c1c07400302c2600024420120b000012074125000c20300400040d5500c0c4245100041d84800a11451802c0ea03290403440302d050040d1440107042c00c442402d942c42c0e01902008802c0c01600707030500c080c5c040a51000c2c4e651040c451201c01c0c0490781c40000078040344c0d00f103000178010603124040020304558451590101c0d03888407001d0000702c10554004500c41c041c540d03014a0103508001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633774343 1250 633773093 633773113
    0x1103040f03060b031209011809050f15010f0509101103042601150504090807020310050a0f36200a0506130311040204080105090c01020d0801060210051005060c 70
    0x80c2c00e0303c2c107034600d8074440c0c1c002d241001a0f04107507408607400c5400c24a00400c8008206540080707450f410303041100a286040c040000394800c5416450250700400ea40420200051004450907041a42c001c80059400d1254901504022082d0240542c050070b00c80d8140c9003504420740355170066403100e5440014002c40c03603004100c84007001c002080d00c2009220030560015100514985072103118020396481080c041840746030340c19079020507030080959200c40940c890b070314098a001e81d003400f025450710b010b107500800b05205040d03c814001caa42c1d4048900a0320754140d83c2c044005e8042200721303100e15040051410800e07040300d28026201080c4c048205001c1c8010b0b0000d5400050040d03a04000420303044840c0b03038102044990003800950b03030b0020b502c0454042d00480c1d0060180d98201401c3c80340e1090f010800b02e501c910280c2c00c40d0302a5503044400c82ea4207900f8850344016070094030354400201c100303400c8240c0c0b1180f8a980015030a5460b00810b0007680000507181140e04242146 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633775593 1250 633774343 633774353
    0x5060a02070302040f2a0f121805060403121404080901110a03030624080a090c091104031b0302150307050712080603100605010f0507150c1e0305041703071103040f03 73
    0x1b103101c80303c22003901c1407a4142c00004c0c19071f418506140080c04560006c010103107209400c20501405c0b002000c54401425160440e541c1d0000c1d0b40c1180030402c10042e4485402680c4540d40340030b0790003402e12925495580b01c0000603884261400d0401000206002204c08100200c3c10110312079038002030080e2034940142d84c1c440e00c100058202e19503180403054041c0c0d1240c8255008902c9510001d4403407030610b0041d803081e01540c01406100d05200c9404017510400020300105d9000c0e210649050f0003980701021558260b01000394410710603034080400007030100c05103500020381e04205151400340d484800005040391500000207810808110f25420140013240d0303003202c0d8000610100341484006400e00380041c414104118011860b41c00744a605d010341d2070010b4182e002080420302030b40c0c2c01022089050044c0f0000d401d40d042c20542a031180c41410300c100d4010030544c0228050b8016000540d00203014607042040c0c501c3c00004034a0140000c1004259500344040700520b1403500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633776843 1250 633775593 633775631
    0x919050108033402030f07230d030503131a0414070321031e0b18070917100609050603160b07060e03220302090906040c05060a02070302040f 62
    0x100c031072600240490020040340c6002c3d02c01a45001440004801c5601640118442d0018010f989485a0500030058840c0441c2c0c020503100d581c240007255244550002c0341e03410040c82441d8102446202c0318010901c101e01a542240c0062030340402450b46480300440c3d413040e440c0361030811051600b031108019195480e1481d10200c10042c0c041d451a43c1c4404070007050701610701d05800c117841807460180e44030303500000b5480180e4282c10015400b030615031000780500d000c0240102c62282c2c241030762038000c81c00786125803401d41d18496003a0900610001d24408545048180c1c4658000e000c81d050706030068001034144801d0010780b900c2e040080510385000d065a6104511001c1800d00c030a11154084aa10541200d07001c0761164031081440d10758414000084070b43d80c0013588100c802c0c0d6511540d081200d00889d03044926444c1d100f030203501c44005441c01014180d81c241d081005041110142030107506500658407895526000329041c0c0d401040f00c00030141ea540346450030000103a20f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633778093 1250 633776843 633776849
    0xa080c1c020c040b01170c09010e030f0a03110a0b060427150506150904050405030c070e040201090b040b070201030902060405030d050c060106020c063a020a08010605091003051509190501 82
    0x10304000011b613041110001c0d03400141c1002e80c190710018804486174010440c1803034020000e41201c644038030002040741ca54124480c00c40c0080d0380e00d103029140320030000d604000280c00c89508101601d940c0e0800c030041000074001d900411071040711105a40c1c005c000911103a00641c44580c021903170001c40d00466070005c001510403d00c4084c6207800001c11070903603404603000da900040329126414003031320398058113088017858451000d01080c501c0b1403003400c030300841c403c0e00c91841050711409100c403180a580240000d16405001403000740d03100303402204105001a11061601b5280e43c0401e0900da02101c01d403000c41c00025a180314028100280c40c0103001c140b018100c031010b00c1c0700086041c440c05549494071411062a02c00007190300884480304801c80c103602440d640810300c40406500035a81610100b1190300001480754059000c854501d4002402d80f940084c0040c0e00b0b800801002d420301c0c0902031000c090700680c1d2118402c1c14001e03a00308a103040c180081c82d11913419510160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633779343 1250 633778093 633778097
    0x92b1b1113150b090a12140115030308040803060a0b041401090b070302031c0f020d050f0601020106030b010506070302071a0702030706051303330f1107050a080c1c020c040b01 77
    0x250040b114251441416402d55030400d0300583e40e59042400039081607550342103030035601d0440300764004000c0d03c407000071500340c420070007030246c8015040300102e100401d01c4090b0200300300c0b500140004000e03900550744444c1c0203000e40552905c0d800044003a8105070045000003c0d1044440059078012580400030300401361460f280040c1550300135260300034040301c80018415150f030305e0301c008000d41007140f0580c00108115110005820170002038401600d070700c50703101003420110b092948107004110a4a40101030a1643c0c0d1824083c002c0d503500264083e003c60203856000f10b6030340c07a011403003400003c40002840d1100100e00400d418040e06600580500104014010541700115400f000300c03034019403000b541030983d403141c646e510000388401090120350181912a00c0030b641c004403010029007010032070403601581018151060300c0703001d0b1540d406904564001680c0070010500c07001c0c0842950704c5a44165082609107122140e00c1000d80c0000411080c94141807155031007d210034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633780593 1250 633779343 633779351
    0x403110c040522230709050a0e1e19051e030a020726010c03050a060609050112020903070b0712031503110d02190e010e092b1b1113 58
    0x101d401414100340c2007100000628038075604600380542013410301200741401079141d11140c0c09a6500791102031a0281111842c40c10303001c214100c99138810006c920340018010008003031a0380055100c08000401c40c0e540b403044032011824000c0140a140c40310380b29000070070011074002903011442304030103103181032688240041c010343c6d9400200c80d41260b0844581410302c83e003540a0307941c8120082031304d0b9419801d02c02c02501155165000034810414000d0410035151641e50841e44420144952800216000c403080f4200c000e9038010640c6840040072100006d990b6045040f040c1c204901c1580c01e4145a220180389035050300421140320340c041500710002e81140d42350b07480134030b0224100e400392000311642411034440c1c600100001c507907000d03901e802c582e0356010000703404001d0240c00c1104501c2c3c0d01040300440002a94481c12091084001c602c0440c80380760403904100c544003008000e800d181000700300c8240710200041a000d8030701506c0310216141403101e0000801c3c0c8802c0b400b80341c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633781843 1250 633780593 633780601
    0x30c0c02010e062a1506010c2919060801020a05040b1b0a030f090509040b0f0a0b12070512062206060306150501030b09070f140f04080d200d260403110c0405 69
    0xf015200c0d2300002d80c004118090010781c0941503d2881b65a0007046484d00502c0902a128860140f104405401c440f41402110f8031046614240d000b207940b0392012813405d00060010010106c09481f44a05001d0b00c8003085110010785450000c8000082d40402c0b20220310851040d8800c0e4200080d1109641e1489542003a540b4200c07400e400804001e101d4a1034400700e40e043c030081c0c100004064000b400c0081c1944409040750b15401148075142c4100400440200042d6020825070b1282501c0450a043e601c0e0340703500210b81405416084801e565a000084000303242c911500303c05e51544540400603500705000502120450f5610742e1060181c11300b003101c0c00350310250404c03c1306200d24203030510501109248000d40119000030884001c086404201542c0004a180b904206503407030f51201c1100d00c0d42411804001c401c10200f5820014110a12038040c5460912030a51014600180c0b10b5102406204441c1614120005030340058280303842d107402c111025000320116020405410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633783093 1250 633781843 633781847
    0x1b0b0306010c020103020c01140115090e040f0302070305011104051305090a020415030c0312080117070e070c200906100806040c110f030409050106030c0c02010e062a150601 76
    0xe05035030410141112007411a4825010f0b40c01100f0000c000348090081e400d41810b4a075403d00411311600b5905002c0d240c0a449a843c0b0710855003070108442003070311507032103d1f06031402800c015015403080b0000000062400d2091a55240a038180d050320ad906020400540c1d1050041c002d60135820101070059424012030180205503048034005020302c04180880904402984041d140ca00b008000105010726124149d45104595903070000c07580c1c03600c2044020030303200e60700d0314201d0344104418050319800405864005101d4101110810b0f00c503550b89441707002c0f48052080c00c6180712007884181c00c1c81c6620700d4000008861400c400c03050754100401c10107008018522239034a41d445030305807a0113544103400d071000c40015162800410b440c4543e5980c0140b10b48807007a03280400014080344030340f250701d9400d6201d5a0314600200c558004680394031410f02000e90004007085030350408109484000302d400c400c0c102c60b800c9043d5051409003040004484980700ca403844d020448a60307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633784343 1250 633783093 633783097
    0x90105030c0f030c04090b10050d0503070b0a020d051e0702031e090f030307030815030a020607030e0406091506080f0c0a08181605030c010f0807050c0a050115031b0b 73
    0xe4060342e8100088249100183c588081540d0154100b0714005400c42441494400f0a1045807850410a85247c0d0780050000e868107400c00a0000e800c20300c0b18600040c1041c4200c1d410840c0d100001d0705000340007a20b48203c48040c5ca201c0c2406e03400f43c100a0f1420b00d500c4000b81c0c0040d01d40042d605050f81f0404160f42468441045881080005610f0106590701040b515901501a00b200d4480149140242900c202550fa0349145080741c20a4401881c001800071940380d8060001d5090150355078098410070b0a41030301740d0384592141400303e006903048c40b80d165140f13054080103143c01d2a142d005400d4a10181c904184644038034204050700454408803805450744e4900400199600701050884220303284003110940140b00790011401d40409403c010b8a104805944441511000544056140380c0d80b071004505403000060f401070103040a8401c803444a01580c01070a001c1c0d07602421100c507101c1c9034003007840100c13003803090160004254845141c00c04c484c40d001c0d41000a805668 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633785593 1250 633784343 633784363
    0x5060709060f0302070203070906061709010b06070b0405010b03060f070f082406070819090503030703020d0311091504091808030c0a0302160606030201030506010c020901120501090803010602030a030b09010503 92
    0x3044c0c0028441c0e08548041040c0300040a44000410200da10b42c0c0e130003400e28080011800c001d005282c00314903e401d0601c2941e20b02240205690f241003002c0c0e0b110010054014020707103455507124280740c0c0d41c0d1814030020b8030864001c860310b1024a04920090301c3c0094843e43c07041080044400c1142e000c1c50610713408003c80c803020040c80300003201d8001135083d20402d00010a40000400c002e0b0020944421000c400441603e807003485540f00e4040c15034034040d800c405001030344115101042240a58856100103c404040924203009540880c15103940c030640007440500000c0d0400a00c2d42e640328041070786290343d10111f00c1c0c4000f51201c43c403601001d00380c0b40325a6400580381030154026811034604801040c00015100c446050032001030082d4407040e4007090a0100203500303507200b4040403a5281e402406003007983d007400301c241d030b0070307103650000b294150768400003880030442010184d8020900f80c0c0c0210b42d00c85002c5001020b498182c090a801101c0c00070042c0800c1e5408680141c40e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633786843 1250 633785593 633785597
    0xb060904060b0a0f060314060f0d081608090a05090106021b030a060e010c121104090b030102090a080a15020a0504211e02091803090d03022805060709060f 68
    0x610344440c240702004103104640076500802030303180091a009482e2041045800030f4608010108a401440d20b20300030450310320b9846030a0400088440c83d0000f4040540703401050b4042c1018074003c41c1e4481486c0b0002c3c02e40b00c010000c41c2c0c80d8400d11f8000d10303900c084d00e001e40307403842ca9515084000c0d6035292206c2c1e995072641d000510b03e80454800f04034121100c0d8018905101420a4001d40c078001e120f81c3c2d801074001510824400300801c42ca003d00c00e0600d1906545901e0a0310b04031460f070080280d04a2103070325540030000c484d520f40c0c645088070090030041026001603116403070030700b821106141c202c964003801809105151030304401030358200c0b00d170140e2032164604203401400702c41521400060181040d4410542900084e8003110303442131082c1e6203043c0c1d64a40c50020051900d0081047c841d0354800c01a02c40c0e14108100388014083c40790040381c00c81050903500b40032101042410555200385122140c05001007045000d400800300d041c8507982c10b04043e0020800210040c003081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633788093 1250 633786843 633786859
    0x510021207140d0c050105061207170316060c020618060402090402120d020f0c0612070302091807030b1503060d08130b03150a05060c07050904061103090a031b0b06 72
    0xc0c0031601074806000b00c816402d86900a0710403030041e0402000d10002c2d0354030b62138800010401c2c1000804080401200c00043c202e0038503240652044d0705445000074a140414081c20101d44600d10b060340e80d541c4501d0000c00c0500038004000e207040c400403d846030404120315582c0c031860b404591950840d4050742d2490b07040c1d40e64000716400360701d040d6083c0424401c3c200d15a0505a0200303210b102c19991000741c0f28120311100c01c0100074003c407004103000270f1114001c114014040e074020041340a001e0300e1050f4246071040807945d038800417242000070a0b194121180d80c1d15100300e15203820080798415034254141900030070902249072100400c280c1c8001800c200b20300c4d04070720b960b0040060700c0485d6a0ba103046410700b05000701d0b104401703008801d4940d0100c2d051030490181ca00700d1044500900d0510328000400580300d8001d0b009852007591011455015048440114451401c50004040c031020600d00104044540340500c9849040c84840d080041d00d4060100d410150031a0848 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633789343 1250 633788093 633788107
    0x2061306050c090d060e120406080a0f1e0209150c0c0909100204061806080702060c07030e100815060f1c02040e070c051006060503060618190f05100212 67
    0x1560603c40c116585502642c806150000c0204a8101d64900102e20f0203442d5242d1290141203518000d50190070045034980700042c0350301c13040ba40700040051041c0404140c46003c0012030407051241012509400e030000f03001d40041c01c1100401d00081000c03180149070400b004800c0b0703243d00d01521104d10600c4402c000c50960300c0304100c8000440643c00e411556540e944101502c012401ca2610340882c042c0c1d4000503d0754040c10072903210b4040307600070300310a646507001c00016920160f01242400b4115000383d01c6a212180100c20b04800754556004a041040c0c2d40c100707002c50000c0d4a88600c06c01c00109103039080c41c80c03c1d501c203041c10f11100700d134138008414410042d0043e5004224200702880c10841c034a0761200501c000c1d2409001551100580c601550060303070914011b40002c240d0070004140c2c030b81028401484181806030708400c6c12507001d0009180704860b403807900c4404510440c14008804141e50010040004460300c110001c0b40c00700c069203a204280c4540400c03a40881d0b54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633790593 1250 633789343 633789361
    0x160c0f020103140117070510090e091006032f15090111030c0105010620060114130e030301090e01051512070905040501090303050a1a042403060902010f0206130605 72
    0x545595106115040740c560715905c030741c035103012440602c100900c0b450030001103c1c2400d95908407445050f54441c0451030411625042d500c0c0040c0c941035552003154003c00146040d803141c00d0146104030103184000801e803105501603030789003a0794004680c03008035030042070f42e0314109000b07080302801c003140c0c0710a40c210041c0d5030704035411440c4400d8000000d1100b03401806502c86810303111039480b03104222000f02e41007000e110582003004050340c07040006000c444000d44522380b4980c001004848a00c41107054441600c2e0910f0580800364808801030010b80c1150251104c06c41501008100380c2c0303000304d131648424039018a400d0041003000c1070b400c04440248000400f9040f010410b02042c02c06107061802892a01800d0b00003078034000c003051083d8034a01400d4a0309400036007215185c407005040100500203e41307410142d000c2000804440102c4c0322442d80118050480010140303110f000140002030101d40034400c6400010802800d58400340c90340d803040ea00510b00181643d948849 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633791843 1250 633790593 633790601
    0xc03062b061803081807060516050312010614071e02010c0b07121505030c2e020a060507080603100b0d0c03150b030f15100b07030f08160c0f020103 65
    0xa0041420004400e41080941030100d100501c680d0740c8480f2035503814095544017004110400c01a000814100a80e41c8940007070003500003100d595440306034140e41c40c1c910f141e1061035040d904c00c130130000420016401c850030b004400c07230984c00c403031031f10745260303203203040c0c0706c00001551108071030342034030b00c0c00d40e44900143c514003588a001d510b21030a0810000d080400011440c021141c2030083d00d024041c0d48100000032100080c004144100e855010401303c000c20710821441080c45074200305101c420b098103c040304009030068241701c003850030008203440c40205014140252a8140000c80d1800140d5001c80044070b00c0000e20441b5480c0000c941c11800356001c0e244009a410110901100b2030308400010300c075a204100031840e00050589801e6903050541245d00b0412080c1710030f940d10240c5039400290300c0b040c00b0215844501001c09034011100503000100b02007007030400190004202c41e001010500e8005c00d0341c1c030b59000208034100c031503801410301c0201f0381e0200071a40030b604 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633793093 1250 633791843 633791929
    0x9040513080a091401020d0801060e1305100e1e041202160f0510080606040b0705010f06080f10060e13030e12100b0402030c040b0a110102030411090c0306 68
    0x200e800e5944600380c03001081c6180c58001c0e00d00340108590180d13029800020080c40401d500e441d00f10590307103040f00545800c401e50084039041044040c401884050610540744a40b0404442d5102e0500700641581b07040002020256820190142c11081c80b65003408190b015500155102d1403100c5440308a08205080f00c403900704024a040c0415a2900960b064003039030419101280036045c1400c0440d00c0800a990540e08902c0410040c4080e80c0030400400101e80100c001140e03200d04492070000300d882a500c0a031413a00f05400550740c036202031220350300e1100001c40030711030703207040c000440e00f00701000c2c022080020003007040384c0c205801040d10324010440149018102001e80410035200c2c0d12a040314001507180203500354030742ca484d2082c0c034000d0340d800229500703142c2040c410310241e501c14204101400a0203501c540300d18001d000443c4210310a48070010b409200f2824001c0c003400203400e0251921b0305104210450300c8800501c41d02c5401c0420b032a500c55100c0010005aa01e204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633794343 1250 633793093 633793103
    0x90e15070c0503130e0c19050a020f03040f0906150f050a1b050a0b0a1401030204020904110409020403060b0d03081501112b0503070f080603010f0504050c10020c0609040513 76
    0x3080c604c070403140505030391040300e41802d448400c90b42c85110b40c0960b4440c0100282d2480b40d44040301009502c0360000c0d0031000d5082c01251503502d0003005262560b04564803001285004140502c98011240201001000280d040303503010310042d50080e140c402016455810848003142c01401907201e50f1b41005d02006440b0420240b800600345203840b51143c0c0010750340d18010f18041504d80c2c042e4071605d00c00304000200d400b034590842c1d00300006580440c41075a407107919210955201501c4800400c014244100c00594661030752404c82c1c01c0d101041d071201d101d070b140e18900384046034105081942c0801b018000c400384000ca040169120414644900d07100d2144076500581d401402001c0c03440c001e40300c0b165030b214503030285040b1201d101c215010300020f100c0f07054007420746004070700c103d404c840300a0010400c00c058081030390444404440607982c507408041c03540503500703161807a00403405441c030140248481a00100d101480790b071076114001da0b918800100640f8496101d944519801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633795593 1250 633794343 633794347
    0x160c0b0106020d080f06180606040906080a200d060b120d2a020a170106090911040f050103020f0d050708010903050417030c0607031a0a1e090e15070c0503 68
    0x2071030009540d40081001c543c04252020041134184865241141c4500c0c0d0090021b401540840000d00b5401c0024141c140c2110742413002080e51036041c09458003511900e0020801c4000fa4201042035042011901e4006600260368810350b4645480c6034952640000380450340c1407145022030140c00c40007413214814000c9140c0d007408950300500c0c0403000c140400c0390710321944c0707001c1444c070511a44c03050095001e120010300704841e000315440005da254441000203202950380c0310030000c8e1401d007a404c503150046003241b0060303458036120740907070600050010410b03581907034003044c480500600a45d00c1514661030030800c0003030806c1610301420103180240503811183c40c01511542086c0500d030314940ba0004500c4c0c01c50340000a4440c00300d0000000d08243e25400c42c2a8000d2040d0802c291024840c90701c010703440e80300c2c1e102600080c00300070810b0300070700340034003c07591039480300e4020003052424440342884e6540c001034900c900001100a0308600c1d1110002034841c500c00d804001e00c2e034000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633796843 1250 633795593 633795599
    0x90103030315050301020f090418140c01092702090a05030129100e1903021f080a09050c0f030a1e0c05041e1d0307050714060c06160c0b01 61
    0x4942c200881d05030409580d11165920356007010709074010140d039208440c009010001e0149040e4116009084440721000a0341c06180c60740c05540050301e6981680d82d00030016600d095034003261017001006a950042c4490652401c01005406059004600b00d42c01081194941c1d0315a4000c20041c40010001c0001c481c10858500000750181103a40a4a14030310000c042402d01e0390740c0305a02c7c40f469550b049400390b044108988a54110b14100020044200100c010f80f620894601c0200b200003003085140040200104003c40082007805028140174403280081c0001941c039400c010106d8a404240301c4460100740b40517861030024068041800c503c501c0d040070050808407060041d401001125254810b00c42544c03d445007582280100c0302001c1a0b10b1160b6116004200d566003040c024101000955031840c1c200c4030064400e90051101005181800c8100140c440e0301035070140e062615184c800794860030000d081244411502410740d485074800c6000e1b08003682c0c0030702c0c030068950b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633798093 1250 633796843 633796847
    0x11121009020a0909030c06090c031203050a0501060905100302030a020c07030f200a09050403021f0f0515060f0c0c0a090c0807110712050c1201090213090b071b0209010303 75
    0xc4032000507030082c001200302107a290518058014500d0305611400c080c005c55665441c0103060007001a500c204d01108044000b510204203260600c031a640c0120b00c03401c0c00c0414000310786042c0d00481c10700100050810891304d41c0c0f0141211642c1c241401a12a911800f00300064400d880e21a1518000c01c0000700030045601400d08400d4000c92a51848007078103500c503e240d011184003107030301c09030007407080058103d030780c2003d0341c083e02c648141d8060264401980b1203008080c10b08110f05525203010003500c401c02e02c50700341c1c4002901301c0e214620203a02d000c1800c620489003008820840000c02070350319281081a0303401071102504e02c8441d180d8030001e03131004150075440c42c00010b81210209407028440d100001c2d4103002e08014106462a000700d142200715800d1041b900b9001d520200301942e50742d40c2044c002e4400b0b50002040d000c4032481044214000b900040003a14038050846000c1600303c1102588a01c2c2400d0421010452954a54219468441c02035101419000200c1055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633799343 1250 633798093 633798101
    0x50d0f03090e010b0d0207033011070b0408070f0f0f030908210a030605120102030f0c030403081b04030210031b0323130213020403030212030601020a111210 69
    0x180c040c0d610400d03070315128454120769080c2840344002d09902880300001700940d0b503008004041c4030f405c0c270021251185050756014a010044409a03403484042003400088078014840141c1c00318102915040c034a6490035080d9002074006410b280300418600b08116100f15990704098008500380b0050741c10f450401c00d12a10350200701c0024015240002d04401d0000b0864070b280000310141c0d050000700180080190001c000c6c0d1003c1580b40d5000060303d8851b100c1030103241000300009070742d13490040540c030403800e0080c20810641404104020103c4c1d8403c1d0283e400c02c2c2c00414121461003481101000c030301035600041c3d800081982c83d61340d182e826038450403054049055240c180031041800f50704440304444480c855562003003030306251988011031242d001c2095100c1140c080010340205010042b00240204207560010b414000d05404001308448030a0740302c4200d2442c6040b200003500c400b43d01a0003402c5d01c89002044400da9100090b2078508007c010440d008040c0c0354006402038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633800593 1250 633799343 633799373
    0x60103062706020711011b03120209150403050609070b0f0d1407020312010806130305090a170304091121070c0b07020c011e1b06090206030a0221010602120d06050d 72
    0x205c3e400300501c0300c2a50007546d060b031004550a09250742100175482c161031048034800700c142c8180e402c22560107150788410810b0032010200780e5140c3c845c0e0441c034000703181203409001440e1640c0012020081c01c840030b01101c0c40710700000c4243d522410b0031441c1201a100e21480303010754035441c20070405075640c0000900400d4041410344001a40d03034032289500c07403c055514401d142140c503c01c40200340503200030311540b100904004203481c0d035030b4402d14003131080f505103192075003001408100540d0203005401090850070402c51510824400864500c184040322190344d02282e00040d800b54000e01c2024900b581210407103c43c0c0c504420000d48490180302810301141e5150b800c01c070487c0b0181582c217241030103070300e403040c290074001141901d010040000b21042603c842101c3d00685503040910700410b9100320244e1079103410440c4852458000754944e201d01c03205401009819400100c05070314000604205a4442400c0d0f1510090612900403030340144840303070140300304442c114400e521 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633801843 1250 633800593 633800603
    0x330d03030905160b1603020a0c0801050702061605040603180b18070b0708040501110f0f0c2803060b0609030a05070303020c0910180e1b040612050601030627060207 72
    0x300003151030510f94181c0c582c0681480c0308000e05c1181d0380003403072000000b5068040e00440d04803002c0d6a640300740d80c10154010000594485050060b9103404002c080d41154001d1006810041c1c8414014030501542c4120000c050300c501501c0304885580c20f00d05600342c0c0000039010f40b4176001803047d4002c0c885916107130181c0320384540041d0f805c14100588503035580c07011503a4602450580112584134102034400c280d4003442c0c03c03280640c0b4040000340b4074880c0300800b400103038125004001c4004140d0b4103000c4030032401400a4400c1d500b4525800549520810000d140500c0002203007603409241203540d014030488402c44184000011400e04030b82c0b01c0d600b16415102c4050911818941c01d0381c0701c200003100c40e41c0c00c1c80310400d43c0302082e000c415017443c00150308850200c00362034210245280000c1d03401100841c00b1038106030144801409580c50210100c10f115620741f940c030001444042c200e00d50300c5116034002843c80e601243c0015811003624640e00c0a41071440003544a8002211 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633803093 1250 633801843 633801853
    0x200306091e1503070506040b1225090603110a120e070f03031106070c0b07031e050f040c0501051c090212070605030709080d0905010e030f1906050f330d03030905 71
    0xd190328100e002c8500b03448e400d2459030f04041500449001c0000c000d031003000003e81016400441c0c0c07121408005800c07140f5039840c9081450030b0070241c00c65210300c03900c5543d030300100039041c4c802d40c001c00c01a164041b040400650180032000c054100000b680182c04200040c100010a1660085101c45810a01e2041c0d580c0c1e502d4250f002d4400c5003220000030300040e11a00040c0495010f40c0c441c44410040407124550495511007680c00c4940840e55507249a05140c00e200c1403049190604020342403e003010f44c030306075020584800740700000b810301c26030030b4480b40010110345034001c1110604200b001150a5180c0328100038099401c12220000010302c01080051800c1d4000380c0404900103940b2031a020038208001100e0340303021040540c0e018410300315011401b0b01c0800c42d00d20b0b011090310300400443d400385005002d981001c0c140c2d8641c000d0540034017003441010001140c00104032034002c1c2c2807402c400521402c404e4601c5206500501d0704012030f080c16010307000000414400c4c016a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633804343 1250 633803093 633803099
    0xa141e0106141005041a030108010b0d08090f0d0b040605180111040302100c0b270f070506090a0f060203181207030b060406050a0b0904200306091e150307 68
    0x5003220300c0c41c030a454070340034090703515440303030509420b0864003e08503c2c040703140640350700130720b01d4100c4040040841d44000000401038640c0030702c03c01c02070702c000b1030b10b64032a034845489410440c007894112910481c80310308403000c25511150900107403a07202c0010861883d090a0400041c41c040740c0d642184080400d00880c40320040c82482103030120078407047d041c142540c00380300d86408a891120700707100411408101003542071030540d2190129551509400040780560b40e1404c80380c90500c0f0304c55010031001c615011011603c48141c03141070701c255488150b94400070344810342c607038040f5800c5400d61501260a82d4040b0003005c00f030b42101850161070080c4010300910403c42c081c0d104007504005000d00c000b40c00008003a0300030000420101d261600c940c001070005030580d2003028a40c00c001841c2d101030529000c0e0040d04151908298801d811044210b0114070000700b4483c4a58134601c0010342e1090381c07011104030100283e11003052881c01000080c1c580743c54a204502c00c0c8035004c400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633805593 1250 633804343 633804403
    0x1a0d1415010903050d0509010507020d1b1d0a050c0f040e160c0b06010e030319030209090112020307120515011d010f050102070b0c010207050312150307031a090a14 72
    0x9a0450744e0000051100a90074582195981c0041e1000c0e41001020010000566a400001000140140d000c0c80c0610703a102c280c1000c910403503009080d0b2003803071444c401403600c0d01c1d04000d622180300400802d107980d9121200210344148c603e02100c0140c0443c004c1410080b40d215180308900e801000c2e000349052000aa40c0040c000340000c2c50400600c2c001511944504080b080045024044900340310107003643c2168041001e40050020303601281c050110700e00b0900d1140103007058a24040c1d500c1058021079114150340c02641100d01109000c1c6041110400c4408030f0b20000e070032000d03e50758454841c0c5054640076500d140c000c17040c410021a1043d11482c90b1400c07140160020040f1034a130818400d150307040800d842800795030910440010410502c01071000095040006c0360724074010300302c00c00c80780e21482c036140a584445802e100084011044420700300c000146804580d0303d0b04a130501c5e20019003801800c600d00039038200c454510024429082075142c49030000804080a10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633806843 1250 633805593 633805607
    0x161e0b090a12031110140121080a0e0603194a01020c0c011b050c0d1b090b0f01030b090402060a051e311a0d141501 51
    0x10007a4800e00390032081003400d140c0042c8a500900c40c0c10300380425a980c40c942828400380c2d4403031600c990784850456180c1c00320f289029001d4007006495000386203150040c0310051032842e80c020004100001c040039600e00036516032026400c020452556454011403050420300100e1942c079185040611084240070300c00d1341d90303032009110008141a014801321004032102d0940700070328900d81480d22425000c00070b00040034040e1007c0c0060245031003400c001031185d5030300c4000f4500b00714901c103000000360f404220303078404400849001100400741e052103c0001940d585050200100c40744c0080c2e101d12503081a1080041154500d103841c034800010f405941021850942c0100840f00007001403038014083d16643e02c151a100b8102038080d9150410509440c4400d0548600840c00090b0304080c00745065030325a040b12018800c0b25602900d4400c40654014149018080c201c0c405030041c2c03600c140c61150b90420701c1800300d2b200b20000680000000d6400440314080448504859401405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633808093 1250 633806843 633806857
    0x80d0b040504170a0c060213030c0b0a0203040618090507021b0307030b041e020a03050303040506150105030711100f0e1005010b030f27030c060a11120405161e0b 71
    0x1400d15064200340c0d50215866020042c0202480301c0b0b980170001080451028181c6c000c0b0b03004040c0c0002d0300f1428407841090a0380c2c0840030102007041600035039607011046c0c0342110000c1c205000841808032004800000c203401c0900341c00d240c002080000e40d40001c0209111444580c00c104100b210410701d611820a40070181c1740401160104000401500e00740d1840480100701e00c83c4810f01d64009030b01c2143d00d41c42507030b1992000c001c0c4414004103001268100c8100d0099181040420f00043c1c810f0100070100c0082c0001d44154094460042c01420a00705150504021514502d500d142c0100160000d1807800e10404c080b6400b501e144d8410f03607042c3c80c0032001c860304603681c82c518945111401009014030701c2070100b10100c44010045028591042400a10b4440c24103800301d030705d007900050400045908105c1c0d80924109420216003103610381000714a500c0c0e9440c03c0c100e18041040d2440b03840d0b410036040014402203c80403081c0c0840d0300c200b042210540d51a4400068002e0707407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633809343 1250 633808093 633808103
    0x1020901090e04020d050d080115020106030c0608060a030b09070602070506030919170a0806010f020622110a0b0405010909020f040b1c110a09120f03030c0c0609080d0b040504 77
    0x69000d006104000c462035a0092000f020701094550b60340e94281440c7d00112144040303034800c40140225040403031205003c6250b0b200800400d403645d11140d80f800c0461042002703100d11440481c0320760f111448141c000d180c0218448100d41000340150389e0740c03803441c803070607006004070440401c203840d11350122409050403200807c841c05008045000102c41c0010442e90b02040160341a82d105400002c1d0050f001180c9030101c1604e00140050041c662920304801150000c80c10400600d00031448241542c480b298041170410b114030b0841c00c502041c100055109124610014080490f08010030039127800381d030742172000d0b580d9050301c6082c1d002c0d4842c1d60750f000401380410300001125201070802c8080392a01c1e5104110411001000c44980c80200c10003520005800320f006604000308000814220210302da00615035103a864056902c40030040800d900d616440401d58403560710078443c0c5030080002c000818039841d0960340c5606c880d00300c414070350500d0500e020514040c4030341c40c807440d040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633810593 1250 633809343 633809357
    0x204090b090d030e0d140c01050a020a0306080c0d080a090f03141203070e0d0618030806040b150910030615021c05030c070b061311030103060f15140307240305060301020901 76
    0x4c103c1c10303907081b0040c25224180700c0341403200080188090140c0b50007101a010010780d2a0743c2840002c0a030780b000d4004120a0f40301d14a540155264a801c600301c40b50484072294541004003012a1220b0041e48000d0700184041004000c0c00f6058501c0b08003100203004071030003608000c003000700502046a0b41c4000c03079009a1071204a00f0401c001621292040d440050b0030140c0c5c4181c1d501d44480c0d4001900085d00a90030001d55007405c0c4500c03010740408460103100c50500e01c1000c0360ba40b00c0c0004882c042c9903d0512101414040c0d0054800b0b4401349120380d0600300300840095590050545070300c42010241a205c0d215030180084900034610010641d19203902600c504120000291181c2c0c0c0006440507190a140e980307100b0082e41c9503031100f01565a5145080220550701141c5100d1640c900e440c00c2c034541c130110690360b04111603521854088080152001904081a1340d0120038a404110746041c200100304403031075035060494504000540ba410285400c0380034803015140405c8030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633811843 1250 633810593 633810613
    0x60e0105041407210f0c0206060102010b06032a07050d08090706170103081c1b02330406090b04080403060507110601061101110f1215060706090204090204090b090d030e 74
    0x14008440307800d00351341c0750b02141000c90b0460000840e80e0303400403080140c01000a0101d55030342800b070805081c400701c4865081d410826103461710700d00107400400280e401c00075180520315500040e150515000000d81c0c42e2803c011202074003810382141c4001b524040e5000114125001d0f4610084844d20710304e910741680c1c255681c00c0c3e0a45c0c40009610034044486030348800c0c0d07480c0d9000b4804603a09d40d85502c4104000005c01034a800c3c07a031500302020300e108542001844030020300c000c0c1e14000d10884c40300c2584840c00d00100800c91100c002c2c007802940d108120611400030b00900c01c0b00c0c4140000c1101ba40c030400102c4014964a6032001290080d000402125204a200b0000000c0038800020b107410911202d007501e40c00f004c1c0c0d0440c0840041030b01118894140c0d0129808811226038104d80d014101c0021298403400000038107161707a400e43e010554440c0c0d40500700301540600100038003c2c3c14180000301038002c40d61034005105c2c08110740750082c0302e400323012200c0b48100300802c59159 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633812949 1106 633811843 633811877
    0x907090f0e0f06150c0d0315060302031312180909030e0109150f0e090a06030b1e0411030c1f120c050a0e0604050301060e0105041407 59
    0x1c8041081408440d000e81c00e07501180481e100000f0389050100114a802010521202d600c25199100d0030786d03400d5840088021714400b6003c0002e07a40d100114140e2004580da500034401d4140601c0c00518100f151284410003070400c11020700070b01912141d140c0c1c81e584070310100c60b1541d5002090582011003e1103010081c6880441103042c071850b0000d800031400f80d003003003050044008400300c1c03044000b51880d040044c440f080c03605020311100c01810366404252038010a100200c2c12b10448120f440a4288a10b004004113555035100d4a0001006961858040c0154441500d4036599000c0c86409031071284000b444030a002d040041240c00100c5600c0d2145190050040c925034011055500007509440d0456501c00c8a034040b82160113036622039a0950308003030001c0b41600f51045c441e410795000b554100811603501040e00e03c6031a060340c000010521110840303030041 = true := by decide +kernel

theorem cover : BRFrame.Cov 633633093 633812949 := by
  have h0 := BRFrame.cov_init 633633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633633093 ≤ n) (h2 : n < 633812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
