-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:16:20.859021+00:00
-- url     : https://prove2.me/submissions/728949a0-7e3f-451a-9fd7-199e1f5f6ea9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594244604 ≤ n < 594424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594245854 1250 594244604 594244619
    0x1b0406260c010201020a0e010804020f0901090b0406292817090705220b10020c120d05030f0c1b0606100320073f0c0c06030b01020a0507 60
    0x140354141036000391046400a403041d5105100f128800040b50303440100428030b0600464908030050000d903402880303034281880650b07aa6068a00034024030700002400301c451000e0005540c1954812401ba1060000581e210503803a035250580c00106031a49913160004e0030002b0b540c121044100988000e0440134004198029042d42d080c131a001148107015554810349503502d00403801420707088100030b42d810b05000064051031000c0d2402d580c0100d00008040b0115100ea91510b003980300680c00300240521038108200c03e07001c00c48035403000d402c0340e8242c4d102c081c103144805003408104040407400100c0f4010000196024000011200071100071003228540c0d07940426a049489441818132009441d802031080e129007405818807030700c0c64210b046074440385070019003060b120000d0140320711180c9200206100300302c951841403854000310340c40c03c20012456240c50101805080840b00d404200164094421280c0a02c1c0c08900c04c540500100e04100400c2030003403443c0300359000071030b104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594247104 1250 594245854 594245909
    0x50301030b22030f090504050a0506040c0903030f0518030d030e0d0504050a030b09250923180f0a060204050907050f03010308031b040611010e0f1b0406 67
    0xaa025104041940d00d4142c030441203404124220b480b0b040e4108100000a0f0282e0740610302e1101c64181036441541ea0000b0a06946c3c04a452103c0c4942e950200400d42c5003920800105180514207010024110380c1d0150001c10629283c100384603010807400004070f24012050700c032040180c00e5900d100c81c146405400b40c25150361402060080032101e00c00d240c412026501100c1c0020140b03c8040d103141c072040601e2002030a0340301140140000072603a4030084d08400e01d404200c81c03024045c00d1410640d24116181c04000141c3c00c2640141f441d8565055034110307402031900711200b0f01820407101c2041ca0008007141c04501030050f480c1c8082800516400703041290400d40301100c2681e0b035100111603500c030300c0160b012801c40620042c00840c070403801855010003001041e030600d030000300f881e81103030700154400800119072a9404003158400c3c0501e0710380c0f800c0180100b680042004040342c41e8652058826915502c0000801484d565900440001c10500c0504419800400500e5500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594248354 1250 594247104 594247109
    0x20a030504110f10140d021b0d08010e0a050702150915100602031905040f0b04150c0b180a080d05101a030f0a09020a08030d14010b03220b0403050301 66
    0x100103821107001a041c4440848003c4400501c400742e00c000421054035074004200103407a14140034000c2da201c00c2810f10050859040c40100c0385005440300fa02c052403c03901d04034910420a03005c0040101d60450542030390040c0e2160004500c0742e80d071990880c60900c43c620140e5506100c0c8080c004e018070041000c01451001c4111a0056030300e480b03003407401008a01c159401030b402001492038030700c000c1d1024642e041e001d141ca0f07880e065641c40d400c808106140c11030f5000010000302040301064044a4041406407820a0342e440006a10b9117900300385d008004203403500d1450300d040d03030020050100d4141968482c051984038187c440b9900000c0c00100d4080d85e060441900210303001c0d03042d02c3c16241c206900b071800d601c7e55981000000030b0754006040304100c03070b4031030414200694612030000d01034003d082c001d41d140c0c02c000c00c03a4001e8034624106568034000d40700041c448002c8400c2100c0c1d00c035602503040c048240382d01d4116510348550400c090154a1544184010140d1010041d0304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594249604 1250 594248354 594248363
    0x1801030303050a0c03020f070605090a080f0d06140a09020d06120c090506060c0c0d020105090303030a0507021606080406021308101e0608060708090f0f030702030f120a030b060409020a030504 84
    0x442e8004c03038016401c91050b03010744120a002440030b080090841e80040b503020780104160303203190300981d54012080d04200c0a0110752701e0085030000760020b2503c20787c0c0050214003c20035503202d580700071902c011202d0040c01602d60300040c43e4804584c458000c50000d240c402c0c124204146141807110004407a40180f007211800c040c041445032600300165284086428083c02c440a00c0204118810040b018124180101885a40110b40d028400b0750321032556a90040f610703240034040203080060310380c400b15842c910000113025840d4068403540c1d001e0b074090b01c01a5901d2a072190031032035482a901c1000f5505c01c004106d521403407641c00c413458131454000ca05884210014190055805500801d03007198801c10018130054810b080854204a558086c4c410043e0b68116650614440b00e001001c10b900024400046080800c000810450342c00084d0411106a0072031464910907000c01c1d108064454035019459620f50f4110360007442c3c4d044086544144440024001e481c045034141c071b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594250854 1250 594249604 594249611
    0x612110441060301090c1403042303030106020d11010f18030e01090b190c0209070201140c030423071d04060506120c1003060302032d01020c0a030c021801030303050a 73
    0x10070340748420103458800c2100401080c20b6a08140101c0020800071808008221805c0d6045014803c0b8034001c500646c0202c5502049682d10745015181d000da2200c035000a40c000c2004200150740070407801400300180c504280c0700045a002c030f60140044000030190940751130f0380c0502810340320501400707162198a030031211441410055520008901c81e00024800401c0907004005110351032400f0000642018080195540c01003030580300c00b1a00c40015030342d2080d07102c042c055100b122950020104200500d54649a80c43c0c400d0b207003448199030400340ca6003688921080c1c090102c0006045041c00500995144140150340380409642c2629803d1400011640034145101c10441600c00d64006124000403031090107030b44076031510845e04050b40c0343ca0200c01070b90144a0725000b2528088a4540310700c1d1130000d00c02030b10042902602c268810000000d540902240e1f00300714540600b40b1590806090010036546200001c850200e038015070f00100804d6007561110b800380e10548001c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594252104 1250 594250854 594250949
    0x51e070806070801180b030a0c0e06040f0209100f050c0d0e0a051206010302011b140615090103170306370b0a052203020612160906121104 61
    0x41e074000d00f081c0620106041c0b2144402c2880c502900501d8400034080c0403a00324400a485040107a41c40f074005140c0d4074402404d005891034079024050740301440000c114500f4000c04d0000d15031030f001441c0300003071013a00b104803d00e4034080c109440340c003142034041d0b505039402d21a0003011085041181445505000310100d080d080218800c8034400307102c002045e507030f402c540054500340010f965504841c4100e201d00c42c00901c02c40a40491181004000d180c141040410440ca52220098250144d4006001000441c840c281c0c0c11340d00304c80e1491690742d0380d16440e02082c06003c101ca485006100c004d80d8111010030f031107000c942150001c002c0a0300035503d035000075060388140d141410004009000c01c20090064040802c80740341f05a600e002c5441da01ea01144083d0808601008103030448020040c00c18241014290308411624140b6011400c040d0064109903480c0e00d0b82c402031756140c0040340a43e407002d0849000c0e25140350400e00e40c03000f00c5074080780184c0c0b041204041c440300c0d02d0903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594253354 1250 594252104 594252107
    0x90f020910090501240e04180507080706050306090c03150915030607030221180a083001120f06060b07020a0902040b0405010f0e060d02040819050c0409051e07080607 73
    0x61070596040c1a1890b04141c3c1c014904a500000c0b42a1081d0b0203542c500505948d14624141d07903603802c0c4200040c00c0c080389040740313150803c080f039070201091000803c104001070b5a81d04036294410481c0003210b440b6180c02c2c1b0007800240c00302c4e030084d41120001003071100ca8072a0004d10861400200d088131a01d55480100b2070680c000c1c00004002c4002901c001003604080c1500c00c0c0d80407040b00c00500c207200081c540310b807034070002c2e000540303a1810024181c0101c607002440c603400500904030400101400a0303901c00d40c2c2c101489451002820081e40c14100b00002098410054100a0601030f40e42c981c02c4110b0300b82d010400481c4984645840042c2d8403050340251811550460304840c2080d00d0701c0300554079150a14060800c000303c000420702c0c0356842802a09072081d20300c44c0141c80c2c0b8280702c049803910354006800c0d01540b026160090001d040002c140d003d0380303002d50300400d0441c0c0c645402c0c1d140810328815408942549400c0c842c8918000426004668030700003256600e840e410780 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594254604 1250 594253354 594253379
    0x206070f1412030112032f1c08070507031101090308010519032109030501150501140313060e1e030c01140114010f120c170903120a090f020910090501 66
    0x1031820340ba50050004014443c01074803c1c01015000e0f007400c42034924000580540480c103042c00c08090100c4104043d0360b08020803403440320702681c1c1c2180c40003510b592001341c00304030010b081e00700304440064890105486140c0074926051030340024001c07040d4524002c0d20f01542409024000c800d0301c126003580c5124083c05108494010b8010032802c1e043d01e0303a820b08584044950381c240410307464008000750f000d21404010842800c009803440e410711000400b51107221a8980c8070117014024800783c12660b41461540c0c41c3d100c00c002500d4070701c05103010305066800340643c800642c0212040a003d2000c8014282d050007040200658205402c010a60010a00440715011042c40e9211699406501401889c1d40c1e00e080c40300410340701c4a620800e841c02c0d4149000021382c1800c4a1b2400c00b030170389041ea0017480c1d4101035400c280c4945414004508010200c11302c42c0e40355101b002c148840b220812205980207003210206107005a0303608815022403055031304075440c1400000e2030b00140710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594255854 1250 594254604 594254623
    0xf0b010f0314160c0b010603090b06010503041e051c03090b0603120f0a020312070c0212061326121009180210090b031611010c0f05070f0206070f14 65
    0x328034020b1600c640b140000da030300b9080001c001380001d031442180400c82d4224030500802c590b940100320001246080003078694098a107a042c001c2c1442444009010341c00c00c015108960503100001c09081d050052400440c0010303140034900c11780d92250702c2e41c0c0c1a04007590703040c0a6119421039131900c0d01455a035000c1800721010b0050288110a204c040784401812203010724030480b402c000005501c1c81c0c1d04001541c2120108000a03201c100b1170900d40c0303903144000812000303003071503140030707801d1280d0a40c009500030061107030007440400301804034880e54158a10340d0380045d25810800051035a5900503680340f942568009000141c52a41e4080c0001500310882180d1000075a5030034001e901c0d05103d0340f08140318070001d01080c11120302001e540301c1c881411001400ba0145440688441c80c680c001c01826414908034138219a04200c00040345109407400d0350b80d4245d82d090000b114601720900039030045002610109110b503622103030003281d01401d20099180ca41e44c4283c0e45c1c4070040d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594257104 1250 594255854 594255881
    0x2031f1703030112060b100c14010615121401080106081902010918291905060702150417011d06040308151201020705012403031e0c060f0b010f03 64
    0x104010b004411140144d00c070107620422000c2209001440050351410071070f00c041d0009110305c0c07150018440601180585200b0140c020002982010b00310561030b0f8104229100707000c0700d02c4000c3c0f0b80c030901e940b25003400c0d07148028582d15035031910a111301070f101600c1550143d100320902280000188850780b804107034161143c40d41c103440d1070802c0126030b0300e44142002d5141d0365900318084406080c81200d0b000311307a041d407000540d061070400140403039040220007054504001031003103860f4002168517864040702c400d0941484000c0703000b01c2c2c1c40344c0d400280144401d0358411000810540040d03441190f0045c409414126400b11241c1d90501200d0280004140c3c43c08909040240c0380700411518003e0001d03001a65000a59401c1e41d020f1442182c2681d503800034031801d000000b800000c9001c559503200003603461610010000654800d1002c2c3c14000b40300594441130140b800070100700d80c800703424880c2d0105059003500404054051502003141d460320420750360b100f03200e200c6000540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594258354 1250 594257104 594257107
    0xb011509080304141201020a080f01120309090504081e0a02010f0b030309040c030f021b120901170601031416120507021908070c0f1a122802031f1703 66
    0x2d100480740d02142042c0c41030741283c3c0c544100c0ca92174500780014004030f042074440c80d8640c00d2441e9600b1141005074004d400c4500b103040d203040041d034012100004c40b040c0341000304107601c403410300080d03520400b0907010144101c1e51325179102400041c0a8140e4810980081003032400102809080c0d511500906505400c20020109a03240a03882045550410301d000070341d6811406002080b688a00c00c00c414040302150603000150041020700c000d81469001e107400d1501150010781048019091030311141c90711800140710364440c0d8032410700b401410400300450309120318a44414a901e00c0e0510000d0706106060209030400c0c01014007584503030380142002c0b4944202030035031030030460088400882c01c10030b51000c5410300c4500701c0036200700483c0d191101c0c503005c101c0c0138102c0e0780d0640140054045c4108401014511100d03a800500001440001e503461058942d5800e00c00c2500e5a03101d2000c02413005c542e4040d108800740310321031060000b1458031464001c001c401d8003440413000760300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594259604 1250 594258354 594258359
    0x21b0d020601081002031b130f0603020d060504090503031b091005120a0c0f14040519051003090305040b0d020c010e07170c03071e0b0a0c0c120b04020105030615070b011509080304 79
    0x40c03c03001b0700341c200c001700e4508c00554681c079440c101c404207580b211002075004100001d50030f405104040007400e04650170490285156120398485c04014200d0340c0e1b81645007a888114070f01082201c19600300104051004002d902002d003150300180840e882e02400c001c0050104000382c032403070f00c000809455041c501600e070241110b00016610b25498a00b600340400a0301e030b01c0c0c4582c241c10052100070b10411050802c000d01440300c040254030000c050821519002080c0c0200c01c4900351883c0b1031600c2c1c1d64000f00741c0c4400103440340154003049c540c0380002c1123803650b00103d1503000b81e07150740f940700185025020209980d00b1700e54030300741d42c5034000316410440958400180294074074180132043c0520741d00d03050b0881c1504100d040c0c80209812a030041d0070000c14606407000750030034140c141070400c00e5480780c070303c41840144000c0c1400b81c000b0116103280d0700c0c0e06805150700ca042803503036a580c000380303401c240800b27080c402c118007026001c4401c12481c0c000d100d02c6d0b082d10306c4030000754201171 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594260854 1250 594259604 594259651
    0x30c081309060816140a0e190c050f0a05070201050412060e0609010c1b020102070b0318060105040203090d1d04111c0e0a1119030b07080606160303021b0d02060108100203 75
    0x134050300d04d56404581840c0002c4c91300040c070b120762322842d000940020090103541400c4140c954541d9100100001001200510030410060b600080b055140107500e485192005032414411a000f10001c1b40310140d8030410820310707400c002d100c803500a05803141038440c6004c0340d0980b110034111101040d0040100224150345955580c4040d005104640a5551b1600d0000e03003980181ca9080f040080540381c03201501040000314014001030740e00714a18a0304d507034003503225402520b95900b0070105081c040043c40307044030082031510004004000c00b0107840e910408683c010010855031a03415050603648000900c25655080b8004000d03001d880c00e5652a800308001c6000800e90100b0f41c1c90401200303000f1804408007035403040144140a080400c00030f00110b5000380b407144100b030100080c660f00d018422904850980c181005a20381014520030300360485189584a12132084032012440c4681c0004c40a040b81c1091082d181600d962028500503440116181c0044220928202e807100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594262104 1250 594260854 594260879
    0x2d1104080307030528050a02010e0a030c02100207082406040504030c08031308030f0601020114010b220b18011403042003100501080d0906030911010c030c081309060816 74
    0x12212030780c05e0b4590014a0015440114081030840090400315000807801d070244070320a02080241c0041c4008003160342d004183e213800c610020302030140071800441c1c1d1402002060041c247d0701090b204a42005060340800315180d00d04020420044404a049414144242d1b0301440c1c260f0364540c0111541d0315003081740e900240c03007011000580715481020400140180d070040303000511030f03026402d00d10002402e481c02280e03c189044940801005030401d8001210700007060000c0ea000c070302c05850007551140e51103500c0b0054110300040c8a4255030034805260100348826246d41e1003242d02800c2c0c041c00381c0030454000340300c40b403140c180d00307000300250710090451000142142c00c0012880805426500c1c02c1e402008242d101040603c003146d00281004050041403400b00121a81070315041c1a1a000108542c14407500f40100e50505204500e40c08010b41c101c1e003038680e030740c0d5804105d800c54051445182012450150b0205908002003501f03684420b2540712006d00d141081502d0501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594263354 1250 594262104 594262117
    0x272d15030c1e05040905010e0f07080709031a041a0103050a020f0f120a02040e0309090103022803030504091505060307031d1e0d0809120d2d11040803070305 69
    0xc0c803159000703080a1101584000d554580541d0b1520348445c5009100030039140181c000c18066a168401c2113904049045010380c48055071500c00020740710b1070030070f58441d0600d400242120103280d01c07190808000000130380c016440340c031102949a1500e80d40401c3d020b02804000d20300d41080c00610301500d89610310107080308005090002c001d808030006010700c11b41c86050811a000101e075842545410b108a90b0642c4101008d186010301003400180861414000244103503040c2c1100c001d9881588940503441c0d5402c50541ca501c0e0316400d0207019a001880341c1020217051106200361010101c00074002c80c0e1014003081d0454541c84811703006842074519440314202d03c92400c04038003004011008a0302080118901d0500f050404d541c00d2150700070f2f001c0e09101da00c10921140b0000000c080144104503517206444252291101c8042c1810400040b00f414036261080f90b1403034401350740b120740c0005150400091a0a0042c0400c500461040101d07540050001c0c002090040b40200309 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594264604 1250 594263354 594263357
    0x102160209070905010807030e010f0f0c020c030d0e1512040b0117070e010e0a0905030a03090204051f0317220501110a030801050409050312011202120105010b070201272d15030c 78
    0x9071002168110000c80c0c5828200002c03440d2a200c04ca03c537140c0500481005104c00d402400d244038142d207000e800fa801c0150103a0280e8500042d114103508508103450002e20465441c2c0c003d41058142418011800c2c01408a44401010102210400012000c007202c1030401c44004907803826011116902000780030500e0b080c0c8880c086070000d0300a000605040340c140c4c500041c403050728018031003103a00040a107400040351005d0126440c02c2c0c811108101c0b43e01c03c0d00c150240d070b46201d112140340120040000c1040648103400508108c0700845019a442a42c80390782c15070220780b40c1d035030310041000054040307a00100140070506241d0040c4c3c2d9840d024400300d0f89003064030340702080d95a409038414240051f60319514021844c08900703e02c1c2c1100f14000900c0706506005000e4054031908000070b040c00341d04c0541d0b0b804a0702d90032070410750302c0d421a501500f07a40c3d10b03682c120b11403040b0b10a1165601980620300241603480c510f1700161001c101440103020503644080e030041116020110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594265854 1250 594264604 594264611
    0x706050714010903123b011413080304030203070c0b0301051203091008060f0604080f0601051e0f0f03010513030f032f041703070501060b0301080d1206080102160209070905010807030e01 82
    0x601010184d406118407803d0386d40740070f480c0011000c40b03400c6840207039020040c440098103202d4000b9219028419032500605019038070307200c91a041c3d01c0c5104440008200d01142440040d203204680082d60482d5000e58070300041d9040f5250050700c9100d0140c2907035000c01d60140071381c04648203c00e0141d01c24400342401003200300c0c2d2400102c0507002a445580300740d002a0000b418a08140845401000e066624001d40d0344010b411074a01d10301009494095100408a210b035559520401c60042c0c5019000300b15504042c1c020407410f10130b05906030041780c010181d104416209100d8200c28444412280400344402d190340d00072a9104a036072844860b050001050840e100303c5c00e08003c040c40301c000d65807094645041c80c25222540d000e038400c108140300400c95001c0104000301c0b009100d141c030ac40c00281d0826008010011500158195803010800d001100200328146440ca4004c482900c00f03981c420b2001c1366a00c0300c5004450000304400003080681e8080d8000b1007511100c2e40020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594267104 1250 594265854 594265901
    0x80405030a0602030103060c052704020d09060f0b060405060a0c02031e06040302060601020a0c092f09040e0606011b0507030f080d150807050f060408070605071401090312 75
    0xd00d041d05014003929103681c000700400410081b0f03c1041c0e2080d0782801d095040c6070740281f61f24800c181d04110301000500c001242c451554680d811030700c482d0b80c1040704114141e001d080c503034005c00c2180000f07062203280685440701841d0050507a000c803074006142c0c51034221820381c100d9007005644d600f00e8041c8502d01070742414040300350b5910004200e06008003501e14007400c0081c98100090101c6040d500041000ca0100c1e09264040b81a80c40032000480d02d44038070184075030070f07480b1015922102102540c0c00307012200380600070300e02c1800440b003d22903402c14045a5031280c10903107070280800c28070380309156900800818a050075000d1020b5800e4103540c1d4035502c00d080070154003261200310010300040c200555108101089960034194092141072810159680c0701c3c0303000c0d1a00c44c024140c02e80481d0f5a0b0001228090548441554401555a94060010307008020200c0d07124941019803032071503005205800f9040d070103039108100071060b010200e008003861605110301c00c000c61b510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594268354 1250 594267104 594267109
    0x140904110405041b09090209100c0510060801022d04030b04020111060f160507020d080c010905030d0914030f0a230a08180109020d0605070302220602070609031e080405 74
    0x200326000c0105050040e130030b19a020024083d540c0381e000170001c203206010b0044503480385a1916004e483c542807900c08198681400c070714000010951103105c5051600108541c074041d000f6052224142c40111491061412400c100c10b02c5002d8007603041340284800c1001c078262080068000c2d0060510903200c004814045040c030004560840da40d0003031806202424080074003000242c0114074007103080c034003039034000340c5c0341c00ba50300d03000e8218140401c0303020303d602c401e51080050707030307404000c40c1c1e59103030048014800782c16210010707074244181c20440280e1400100c215902c003040c6501d03440c07400c0c04514050328500304240052140414039500310542c0b0800300003c1c400c059003522020414a404881c0104c030401c840c044030250f0f410500c52800503241d002110413135940c494800708841e540d0f81d90450085c05607051440c27242844050743c65200c0410b50f0b010040c1e540c26030964040c0340d2210411784806446110040c110104a03d030013030382154560040702040d2044205905d400daa4000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594269604 1250 594268354 594268361
    0x20a030216080c1006030206030f0411030a03020f0c0d12030e1009241a0913050703030f02070b0906090f040f29030c180702010b09180d14090411040504 67
    0x300c07000b040000300c01e4054842040318000c0c0c042d0b683c4003440701605583c0881c125001c0a0700c000b44e8004054042001c000c6040e450680c41382000d422603401900d1420000d658803c6124400b55500800c04940c03010f04249656500617500400d14104c48200352508500610560001d490b40d80103031001d810800506004030700c01d20340105407641c0301d80b090104956a070700003181070030400c034901041203404c094010b101c1c0300c0421085544c0b1010b940c600960901007030b11900001c0440c0944c1c100841010f402648458000031107608850f682500c8a03060040d510607040b105500000034041c4120a2601596001104d0400f80c804aa0b0255448041d41564913103c01d0400c000398002c511980144075812030341c0ca5240403001030905030034090200e0562040c02040050005e12000020203e5000b50411600824064551071032403500200c2030b18140010303118840c91780107200d1429030545c0b040083e00c651f04824134541d031030314040100b003200501400502c2400c4140600c40010a40d03541d11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594270854 1250 594269604 594269647
    0x4230307120816110d18080304080a050f0a02030c0f030307050f0304090e1b0d2d03090510020706051b0a201507080d1b110c0307060c06020a0302 64
    0x458201582c20031410183c4000d4072000e000d010440300c1c404005164000140c070200e14080c83c20034182d000310380c00b5240414001a040200c7c1403100103030008141e540000c0d0410154090310545564103064000203854050480c0040e5040d4402200307080c861401d0034807540c01e018020f0840e0b1928855503502410403041c03070494001c9402c0854200440a1039015141600703881502800c402c0c62801c8101402c000c50890141c090310a603001d12040003052200031050840c180183d9540d011881c0352440c4015503603d00700c2c002404840300140380d040001c2059006511038024002d82400d012085130701c0d400134804a0301804640c489041e4000f028496404118003c80440104c0000c0040428080c0e0b042c080007400340b01c001880c007030070208010a903180540d1200740340e642c5000350626800944030b080c1c18400f4000c3c2c1c11800310600c03a00700000c2c1e91a140210103442075029040300701070300c44102d8460440840d01d1003a0260000b0407a6006040c2d02510b400c0050405403a070306410100f50920 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594272104 1250 594270854 594270857
    0x1090507060f0f0815010e0303070f0218090604300207030506011706182107020315060f01030f09080c0a06050f0c0a0e0a0512011509050423030712 65
    0x8090140a5000e0301d100e40b14000c82c10b0100740b5030740030f034802040041c00910103000c030000c114544250f68428103803003007280d000030210fa0300e600c3e2600303050004484009080b44940b6280220a1450101f508514413801610024100642d1b49494030b402c84000241d088605a40c2c5d0612202650183e502540d045a499030042c017419055181c10351421006801c91103040c4081d24001302d25000c000340d46a8000718030030681d400c10800c1000c0c0351819035072076810054200c0d08d1444580c11140503000e0640d190089040300c400078a070b92003542860900341e4482c1d1300085046004d0b8450750081e00302c44480d100962001810190f80c0d19081c04580240c003144000c1d80100c2140700a11445008981d0400c0040d40000050f041400e400140c62181c00310003070a01403000c0006a559640c400c81d80020440a0040d21620f044504e43c84e0007030444004a04014000142c00306842401d40315007449194400d02d08011a1380c0500750b40a030f0300602004c48000d11041044400013100c940c148d500c5074946 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594273354 1250 594272104 594272113
    0x3080f0403020316030c15020120030411010e0303220b07050a0c090501050907030e011d0d09140f120709110a09051c0803130807080a26010b030c0c010905 68
    0x5610405007044c80c04011012a40c00000c814408074001c0e44400003221802e40d044013415000e0101a409003200c103000414200c0328069155003c00000000c5116610880300a001520b00000640b6401c2c0010b81880d0190300501019400300c0e5001c105c8000c108407100c1c40c4650769a90b0300606950390041d8402c036080d030021030700c00040140e81c12400014000c20103080c080c541c1003001107086014024800010140c4a1041029044080d0b0040e20354115484510055a0003091011b9030386240340e038600006000c3c20310020785400c840c1c1d441321110200030210074846042c44100b1810b8101e4a038200e0003409a042c0001c1d40340c140b0312603134010180c000b00e8162921000c0d01e001c0c14505041d407119000c2c20802c1e18007210400490321090050713500628a684988440090303460b00310843c100140081c600040c0a4140b0480c00054100304100c2c0e51040c509410600061a10400800c03c403429042c00038010f01000744540701031948404404407907410402c81c1c580319829036600c03800a5aa5421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594274604 1250 594273354 594273359
    0x203040e040614060328062a020f0106050607121103030a06030501050f0609060405041e0b010807050d02180402040f0204140a1517090a0b0720010c0507110a03080f04 73
    0x5043c240d0660100049024013200308408141c210f0344101501c041ca001c404000c5074008206103a0322900300280404518a407140094421403281c0501c0c491640140c41190241410160140605019207101501d01400c0044564899038243c2e2003105a4061004220041c80202810005144902212000440e07128514104503003142d81c09032012142d880701000b00000c640719444442d0708250140c1e000581e40d9124200641e203807040d082c88644400e8055200c5040c8441c11018038180c540034410754007420faa500402c052000d5041000350441c035422892410b95481030f000326440343c0060030200c0e068140c090240100e80c01038101c640c008001e43c01011803804d150074034001500509450040c04040e81901514009070540c10441d04c1100c8000944002c2e024003603417100b154042140c4040c0d0414110180040d044000d03000b030340044104220080e4501401070358070a00340c549030681b80018544503183c0a4045140c001c1e00010400b45c00000250070300002c007081c0c3d9428015546690 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594275854 1250 594274604 594274631
    0xf06140c031608072c1c15141801020d020d0f05060102060c1c110307020609251428050a05090c09101808011e020c1c0203040e0406 58
    0x5034070040800070014208203103c3e4100002205903400c600940c1360a102081400000d144c1d030701d103946d8201d030030b001404240d407400b980b170210410710070b03568600c01c50070310380b5003400311400020036040501080000c2044407426011205c43c0500c014009450300003400100e00c10390b400b01d0b0541c0001c95495004401e03510303d034070400e43c000c0d00903c09000c0d02c1c2480b51803480d4601a101401d070070302c180983c0b0b1815400c00ba50010900c003c000d41508e49a1a0200c03010b511200111810849802903035201803401c2002c0700c0303808460030038051042031981464050721256000080e8140c00207085140036429034903080c45400b19002d002c1406405d03a040c0310600c81020000e13800540105900414419030318581c1d010f80d0740503e010344500748949140c0e00d08480c041064100c1d0200c1416020011440b174406411510842c00e1862480c0e901c0007094691030102d00c07440c0c1c403a14040e08101c0f4140004510000c009110003072034811a03050546a1a034140c05d08003d0b03c084480d290348200d00c04a48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594277104 1250 594275854 594275881
    0x8070305100c110a110607020d0b0406050c0a020604060209010c0b040c06090f05060412020301090c080f0616120e0304050301020d060510020a080a050724020c06090105060d0f06140c03 81
    0x38402c034a4105080001c0d560320659030f00fa0804001c0c441d00c0740102c032601945920040c0c070a2550010301103050403010341070800d0610001da805542c1242003800042085070084110303403003070711113034020b101c99a5140c880100940054204904002c0354224050225021200da940241e0095001c0c600c203d00d00440a05466016880004043c109150401007980c4101c1503504039541c101c26051550954800030340101084c0c0002000844200008120040005204494441d102c0100c3e111030311000303d43d80050807485050703000100d029440703401524454000740715250a100860342429190400a400c0e41c0000c820701340e466649140403c1607261115101c2440803050014044421240d1100c1400f84103d580b00b60902c81c2c001a018200109080c1480581b4902883c1184018102d45024069403008034820240c3c807070200820166803040c40b0f864011580144145415100ea0750f4503ea45140000f0903940c80760740328410345600d180030107418401c80360729415540d41d18011126500302e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594278354 1250 594277104 594277121
    0x9070c061b051809090316050c031f050f062b0611130510050f03070e060f0c0d0e101b050a060c081b04060e06130803090a17030702040b01090807030510 67
    0x1c01140c000c5c014152408400c50f10b409580d1406c450580a680c24010b20380404081290b8040c46901c9800401107000254121941a07001303007401641c13200c060780c41c3c01c9030341a144981d1111111500d82514032401100e01050240700807050030307008540c0c031100201d60071080c1003800360302d00042c009244c0e600d985090001d803504a4141c0e41780002140020001c0c0035800c446244d4000000c00720318a640994919007026000801369641e803281404070340d070141c00c8064011130303134401c00401c5ea6005002e0020b8040080018004583e40700c1d0480084070103135401840c102d00c2003581202c0380040340c001d00080d50740a004010219000c0c1120300018035817400184001900f000c5240f40300ca5124040d01120100c0e805440c0c54078201c084a000140c00740315940b02040d0741d28445000150340352000c005001c50540449200ca22241d41d5802c0c03078511000f1202e01030094208110540c0146003036403104048880600d813500c003450320384030b1036440e102054005031055444001030501c00c000c4d50140846 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594279604 1250 594278354 594278359
    0xa150209190b0f0306011e05281413031b050a0b070803040b040206120f010f05040c0212180316150c0506070c02040f1103010f0503070509070c061b0518 67
    0x340e05150040790b03038590203061908202c0c001c00102044043c2e200782000d114100310480c50000180882602600319484085800448048400f514079280b01e29101c90300c2000041d02d1340740003001640b20500c1aa4000003180d413001061744004000b1802c00740400040c41404040e5000e4941031008008508210740d0003000035000c10840380c000603240a080d42c1e00654020a5002662100e00c000785490040211544d98401d40004000c09019002031690403603020714a10403600d0703201c2080c8001d45440d4814100980c4c0088083c04d040ca0095008014842c100c0380081020689100000c1c01c01a0f043d07011060301d50150b00605ca8080000340251107600c05003040c5d01e400d40155903c54030342d40300500ca94140804011802c055481d0b0380c100802c00540c41c0c1e0204078046400c09416a0f42e042030007041d490b40c401c61008140303410006040c4007a203c0080c022201c0b55100c0300c0c101d41801c1c50b408100ca1041c0c403120182d00002461181107105085070310744a40b0f506500036103901480700240341e02e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 594280854 1250 594279604 594279649
    0x4060f111c0603080f0c0c040513020f0a06090e1909151812050913020406020a0318031106070804050306010603290901090f140c12010b0405030712050a150209 70
    0x5982c40101c0f201710300c00d81d00403611540b10380702150030800030040241d040303402c107401c00105484401c070714011148212054080403c42d1000e12201c10381c0e030f024500126081c4601846512036410030740b81e00003d46d00301e600c1c2181d044121542921000c02d0708a503442120200c2000e1100503014070503d003030305601c0c0c0c40c2000150f92910a005415821040140500002c1410440c2c0720003000f81c3c41d281c0307295410340d0b6032aa00c0b000250303a0b5104580503400164500604030020041212007030880c4d810842520640e81c03004200400390b400303141c04550740700701000002080c1e03e007803200c0750003442035887c0003035180101800640300d50340242d108008800000c01c20304603035994030242e80c190b072040e800000f130558102030070800402a460710860002d0005041280304081400245010b081c50038405860380da072500040200c0c0124000c06034190840c240030701c4121030f0010200030340750007030089626025250300d840a034031481c1c0c00d00340c00281d0000340d0720000d82010501068600c07501701500e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 594282104 1250 594280854 594280859
    0x2070f0201050a030921020c01020606130c0c0f0302100b06070507030318030c0b033909130e06090f03040e0109020d020c0708010b012a0b04060f111c06 67
    0x4040154090100034188080841d040c489644079030f200320022039114941c042c1385106141e48640207941d804540005106400400030254400b00e40d07580210006403500400350708654011015014402011b410094521055408541004000000f080c0603401800c0e02540e0b6103651001d6480e4400f0050282c00104032034000528001010012030790507181032a1302e241c402d1003108403132400758006401014500303008588500b04200031402041d020312190406c0c444a04503042a110202440f1100c606c1000c0500882840c00010702c055400207009014182d5008184030444000001d0071070160701500801605050400c0030607603403440d00000354217141c500b4441030300200c01400f6078403045402259280c00400c10b5010785120f0a03030340040c0c9141c41c0c0c0741c0c8141402050660507850008902450100720f1400103501d10b0080c0344110a5880545610f885214903103001400403540b4a645415501c90b410581c800d001c010120042415a07030380c1c1d020020302050800c4007040380210300e000c204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 594283354 1250 594282104 594282113
    0x90f01090612120e1903140105061203030f0403120c2001060f06050c0c0a150305060a0b0706090f05060903040f0b0a08040f050109020316030501150e072a240207 71
    0x3d280c003010161070315005030305442e40410005910000e001a00c03005800c404001c0122040a030292400608000c02455560000308032550401c1400c032900f680003007011664400e008a203c691041c041e0070901280e0320a5800a4111501440d9100000f0700400e07201140c200d80120344404600380000a201d10f500741b24080202991604c1120103110000500c403601c031070309000e101c15400c0002d0809046550707030904c9002507401018407a001920700b10014070b103444c0484080c4250350b074090b41e0504010041e034490300180981c0744142c80c524202e00c41c0c2800a00100402e9100e1045080596111890421800c02a030019013100c401401c040c050320142640c05545590b100b5040300707041140d02c0e03071400d0680c0102f013261406909400340e219500b040309060a48602100d01c10002000442c840000041100480d40101c80d0700010305404101c41c03501c5002c0860b4001040024010b11000713100c1b050305c0d001c112000841c0d900c0d0a0780d03400307000c41c00c51a600c146001c080b00c03c25460f0690300e954 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 594284604 1250 594283354 594283373
    0xe060f09070e120f0c1504030f1e02030d02070812070506042622171b1512041b08060403120204050603100e0a020405060405060f09090f01090612 64
    0x400e0100820708140210954444011441d90040f003030075184100300c1301d0b103245d48035400703090118024104040364900044156044504580d04580d5800f012806559000d09448441a42c83c00c030204d640502005a903041c030520340240340e180c009049180c900b030380040c10301d4a00000c0c2140d0701403e00c03102010030404100742e40d2003030f400b8011030103681030010800786100211111340e018041c081120300c030311f000c0c15004414036000b03c0004580315590b400800200d000c5460703018429004a64100780c040065805e00b403101c0001044d1900414040d208100280c200d43d060304201d61a000038441400403024a00c1d140120007a010f515060074001030658802020740010308014041c40f082c2410703811039055801804008011541d40c4c140030031b480f4000c0c0300d140203003074441030040302150003c82184211030468034050902030509141400b000b00720b80021840c00c41c0844100445441540c8040c0c009d44680700194050800d9410b0140324002c8540f150080645501c0300500440071451141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 594285854 1250 594284604 594284611
    0xc09080309100302300c0c0c010309020a090906060314010c020a080c070f12060f020903120918071d030c010e0f0a05060406030e011103071e1404030c0e060f09 70
    0x2200b03102c841c1007000044000b8800c031700d001c0a207940384450001945804001c1c0380343d1100400700861586d03e034500824100c0c03040000b0400c0d640d01c40805940315500940000300d0043c0000d0626041c5542e0394082c40c00c0c2c0b07042ca10115039266494406004002c00d860340080e4078044400200f100204082000e0358500e101203011b0104400410030400761081004800003a18842181c0301005558102c03400e000200d0071001c569050818005c1d03407a204c03062080e940080001801005204010708091a042e804501c5158000c03800780182c529146c817500c1401d0044480b03a40b10380c2d440b48030440c0d000c0340c0c1b0700b00d030221b41c426040100201c00a030b034810f43c07460340e20b1800c40c0c40c400011401000103d1907070b100e602681e044200428001072442d0154410314030110000d00a20541280f0001d0100b103110407283c0d0008144c082c003130085019000b4031040344080190810f40090b06005000825640040c0d00c00c03126003a00b101c0c1441003d480b45411034105400b510758058485030000004c503540c2005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 594287104 1250 594285854 594285859
    0x70f06141303060f020d0c0c12050c0a080406020604050d0302030402150904090501090303050a1a0a060c0c081f1a010e0405090a0209251106011401111f0c09080309 72
    0x1040007a00780080c40192001190710160030451803596038851000707900210400c080b02132038034056040b4103004402005900342e0140c40e844505c59a00390643c1c070390700180c0f4186440e1140d031501b0800200f10703400400c042c2400e81c00609007842d0516041e03280c00108101c88007010b005000348801030700e03070015100b0b0090b01c500c2041e4a610b102c201041c02886080d9010b0490340c01d02c0014828143c060384403e01070044598248062050004510380708610080c203640c01502814042141501c2810160080c620800303001da411980c1e00c030f060386003200b000c4499103801d4a00340c0542680041d41700d81c01441c0030410303503860881032090020f03081141000c40e031406562104005240e582d401e00402071019802000040350303042086c0445100da4022144403030000c464101c0164190050080d01c407400c03031550084c2103581c20941c14410a02201104a044c00706000714200f03100400c0c40305c0140c80743c40c2c0200351600d094000b050030a84101003441c80c2404403068052000b881c0220460f03050120a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 594288354 1250 594287104 594287107
    0xa152a120b2d180c030612340b070803040c081b0a1d0714090301090b041104110714070b0c01020a0f050f0f0903070e28050c0307081003081803070f0614 67
    0x1c4802003055100300040d0340b0b180d40901e5415a41c21051a8601403a00c00003141c5070383c0805623041040400e0300d1360b0040d8461228248000c0d00041e1005004652161092000e810b415541f4a0300510740000f07148030945030390003518800c0e0203050804031000106800031147c0c160341c03400170801d52840b001403c120f00b009124981c103818805107500300c40d84d2100243c02007095a9003400c1415800c80203031000c840000c5102004c01c290301d054020a056940444002c501c2c00003a540d5141c2c910361821248106030046142c001030310649100600902c101d40d038005030b1b0358803161400908002d0001980000c0c07190a10810700a07100200c00c0e51441c016440c4c1c69580c5d4a00c2c440060716018403a8404030304425071100704000840c10b200600f0260721403100c40003070aa000700b00403054410881792101c1c10703403052002845141c4248400c68002a203024214001d940b40d450700782d600c1d0710103000e503001800c61303842e40ba820342010021300004200c645881a1040d041000082c4242d95030244680000310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 594289604 1250 594288354 594288361
    0x1d0f01050d05162601050705030f090f060c031807080303070302070303060f0f15021908030a0e100608071403150c04080a152a120b2d180c03 62
    0x10041910351500c4080099002580d07410380f0180581d0440381908082080780700220003002c1401b880b030040e001074843d46d04590b04d10340f101981c0c2d00000d2910507140700703100200542600034047c2034018003070b02d50301d40e80d0f03854400300103a8041403016601d041c5034460582081400070120035244c001c141c900d0007580d10751560130b084001d0310094002484052142900150020400301d96078202d0300c8401c64014035041008041ea2543c0c61012112000c0d80101d03000400900714000942d800040c031640014100600003000e45080383e01011052595620344042c000080300b0091100200031030680082c1c00107217000880d41f250841440e450300d5520590120722010308103410b0f01c02070720040044030800b8110307041c0780019078400a00300207001d19000120300c46d120a0359040c80f5031207885208203191041020100c4030700800c0c2c03a0303100901d42d50310007500e0207580d030500751015142551403c0407803452a0030309040118000c40200d1044a40c9410090020b1707580360404c0d030003112001000d80701d58 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 594290854 1250 594289604 594289613
    0x21181e0323040f0e0406051f0504090606090c170c09010e06030403110a0302010f0b04050705120720031306050307230f03011508102117070b011d0f01050d 68
    0xe43c2c0c002e0140c15252140c0400c609134103451281c03080c2e0040d0014801d98503142c080d140349103864101d00c10b0f1080f40b01c40c148030505160b0480e190240c4210000103c090703580e518a801c503140b600017080000c0c8500e20700702504c011030b032a69801041d19400c486c074145140001a040c1682182e4a41c02520301100007400d241c014080c00c1740d00070380f1070151204000180340090003080245594510ba40c40c140c1a001607090030b205051207140395841301c62510003079004803214840700626480400c40c01c4007013a14612306220a402c0d0040f4050000c607111000d1000d800e028203059000b01c0108203003401040145940300725110140d440307148190000301c06a00300c0181078810b2a0302c000100e01c0000000a00700310880000307800090a9a03030a5560711043c60b41e4048445600c100c0544910f001082d008003210848138807001803190314100e0132082040140c2d14182c1241106889404001004015022000007445141c0c94404a0050300740b40003480d40c2202a8103000b482c2c0141d0800f50142c0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 594292104 1250 594290854 594290857
    0x417030c0708030703110712061d01020a0507060f020711060706020f0a05030601031410060509010207030c060c02091506030a0209040b1806030f0f0d21181e0323 71
    0x116030010a858506032128149075880c0e010300030880020701280302030200140081007202c26504107444401401500751660303005070000c96038500b4001501900c0e113890b101e091008102901054890b95203481c02401c2000498940282d02c0b08203a0041100800040040c0680e5040d0350040350615217600950a0000c002d004407049040039004c005207601105070840702440c42980241d0b01806030002c1c21000490048003541c4400202207540402d00000d030094019000e010810320444854660380d0f00c400395003941c00d602c0500070030540580d07081542802c02001e80d1000010500115800262004c0f41d041d11004000841460740414403171b46035540c07900040c085d04030007403044500d07401445000d501600b060b01d45070300c00c0c03007000e0394000d10344004103a25460030b0100020b04202e0700030304016128601510900040c005901c2240340c14041c41e8820310180e07950b414040140b1040d20b24222158110701c03154002403107c0c40ca0100002607114441d4181c440c00031003008030401c1c45180d00041d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 594293354 1250 594292104 594292117
    0x2d050f042402041202040609410a020403050f1b011b02040f050612010e030909092a010e06430b090c0d021f02120a031506020c0303041703 61
    0x11140005000210300d0492203060381064000c1b80d041191590b00d02d005403c41e4065541a551581c00e0b80107011030395015a2150100d001d548050207040081d0050380903281000c0361301c900312683c045018020f01400300142c900e0803400000818105960071505807003814420308090400c2071f4030207101d54128903000032489660b4060028000c0d44c030806809006014112501409016021900c641c1441d0501410f13000078003080c083e41c0351600c1d1005022110f030000344800c0003803089034a202c41d682900146140310485a854007500f030803d541c00101200075400c001c6218150030b00070080401010809103550040386c0641030550f1610742101d0128441c030005080344c070402c201000c8140030705480b0141c030404240042c1d446a46103078081040b825500940650440352a80703a000900c0e01240d0f1010044045004480020400d1804c44407150301c046400c400290700c882d050303810050f40c0311105010b07050171300190005a140b440400c0d940e000d01e100d2954104e034260710030b8218182c28012640e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 594294604 1250 594293354 594293423
    0x10c091a030a11031608070207060c170702120f070b0910111f0c08010906080304030b130b0106170a05010303050d1a03030a0e1c0b070f050d2d050f04 66
    0x403070703181c01c54030f1203102c0017620713500c202080b8920000380403c0d03c0407036100d0940c2c00540316a501c13986a51a100c4413070020f0607a0f0f087d0000200804000f40c0d4511000c2ea45800d131010041070840300740c0110340e007080c07c1303648409003a0790180b05001441d540c0303110210600e88145840804442c1c42e450b090303d08445991000c41242c04603c409c150180c15400c41034115117540c071003820342d0340d0740d51081d0205c41c81c038481e641c2c0d00d40050105000084110b03030140d8100c0800c03000701001d00c030140c64078031002200b03a0019001c544041c202c1d40703040c58201a26540080c074050200310b90b40c07658030301500d64420400301c21202540c2c0c241d004c1c009000c010f0031000400307003c0c080b2500c2c0c46040502600c0541c108000728443c000c00e854000305260565441010a03034498492030036600d8038001500d4940045003001e061010902921303103403004a100b0300c076680041c0c07203210840398080000e0070200400403103001142800e150030444408003030f59036990401e51000d8641104600840c5503105400f08482c00b02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 594295854 1250 594294604 594294607
    0xf0d0501150905160206010b09040207051509071a07050703060c2003090a0f03031b030c2405070c0b010e060d05060c03090c01050414010305100f0303030e010c091a030a11 75
    0x24002039268001403141034454120443c00c2c132068401e82e0f42c1c0c04248580c6c07901500c10080d4031960304064020308160b44c4950201c8011500740e091384d8145610441c1c004420340d104800c1040240c128015103040d5141c40f13441e4a03d00b40c4c5c1c58172010b44410180c00068092501c03041f02600381d51090760305146809c18094410711840c90324120580f25440100070a00c03039803007082c002c1080d06204201c0c004583d8140c441d20304c0302c95505142d0502003684030b020341c01e0090185690021a03007001e800d1203400c524581a80020f162a0484012100c1c00351540042000d00d5601400041541e0b0380305040d12900c03e002221139444c00300266010301c843c04024141d016400c01d001000d0750034000385001e43c1030303801502d0380505030a0045441d40241c0c410b122159141d4a40360703915500950041703400c40d80b45010500d00585030054200c2c045255031085001035030364407101500b05000e209850300d5007440d103030524410b8500710312805501381c1c014512200308030000108001c1e2416500252400c8030200785107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 594297104 1250 594295854 594295859
    0x10903170609070c1101030207060e0a2003070303030b032407080a090b06090a0605030613060608011103010302011d03071205100b100302070f0c03140d08060f0d050115 74
    0xc280300488580000908625004140d541c0b4144900c54411403955480040954007510f6001406201d03035205410b0582c200012800708005000d0203056104140040507408483c0c0303480c01c40c04600a5a80c10920594900514559400300d1a403046a40614002c52000010703c0001c4c240803800c51501035030900301d98900341480020341031510400083e19603184a03a6100801e100b55612101c004244850080009113030345810540180c01400c0d401e40026203030346400101c1e00d0a1416505000c01c0c604008800b410416540034907000780011000070300548500031350905141c04103020090600c040a110a00d036003480240500c0418402004c0714400d9503603007a8403410303003000c401c10b40701c030700840c11100007031981406030801e030b104040d080508840000300c045000f50003500c8201c911083c400c0c2c000c13000c641000d0b0004095070044400d6005c41c03d00c000a185000c41202e052014428000c04100040d540c150710342d10940070a407096211010640790890040048594686d05500881e80c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 594298354 1250 594297104 594297107
    0x420040f06021e06010e0720070f060e0a1203050f0708070b07080405210705070b0c011506080c031008032101080a2f031b03070b030c030610020c03010903 68
    0x1002100c41540a541a0400c0514199111003482e5043e80d8a40d02283c01004848001380400f80e06c4401480d003515980444908801034003062040900c0395030000905006e001c00c4000d405005001d00c1c18080e86107125074003c241030441600c02d2030080e03500819501c05141c05441282c400c402296a42543c415092510200075000b42500351444602031000400722030080d01424001c030782010040c0009a50b1080d40c03460829680700700441440f05202d0840094000c000b480054007007613078a50b445100c1d010f440307800c40740c0342c0e08264400131280d8020002150494a41ea0700303e03801801e003ea60360344c0d680e01500002c0490380710601500c40001d4a062140d10100004000c4c4807420380e22143da44c0e21048280c1d507807000c2c0e03400b90010b2000e010040c800700345444ca184008501e0485174111140c0c86c030000341045d258100070f02d1030540c4130014603050701c1c040c40404080c000300501c0e02d0031810051640c1c507060000900e814003a8601256011009000700422a0b022a004000780995070031441c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594299604 1250 594298354 594298379
    0x2040510030e120f0306090a1b080114150a08040201030b090103050a230705060c0a05070303020609010e0d120b030c04020a0309021207060f0f0e0a060804030e0108010f05042004 78
    0x1032503071660140c14459000428040f046503032080204040c50b045855000800040ea000a440f003842e595660380c203a4010f1801d0b4080c6c2c086900d4940326000c166262070f20901e003d01c4580710003442400b803a41175040c0811000191000c103172261809480c02da40c2d0b0700c010b800074880d5810031030307100302820000000c001c000070318186200c1c0b08602e0421081c04031034000c181c4d40540341002943e50032403a4203000c0b41c10203401810030019207030304441009050752101410301007260003d5005030003460400100710000d00030680140d0b592070043c00200c10840d4020160194a0446242c96444604006040c2c1d810010200381c4407005108540e5809444009001060503070012030040512207200e840c4000e010031030034115480340d180c9804140356400121660880b01404c1c1c4d05205e010401c915441d142d101c00c1a028149a4803080302c6410241030182208030910801410407000c02c00500c0340c596481d00b4041292000d69020076621512514440001d0600c01c095410b50404071380060b01c28803054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 594300854 1250 594299604 594299621
    0x10609020415021606030c0917250302150309011514040c0207050607030c020d06050106080f09190204051515070b010f0e010312050705060405011d1504080d0204051003 74
    0x203080703928054050340981c0c940203208600b0b00384c540d0482003007000d50f000750849030049010345880c00031651228442080c1240a4042ca02d2135031080c416480008200d0362180d00061585040107d02e82c40c50740003130071070740c0074036060400181c012004c100303001d000350000451407440711181c0012a0b12425104580d02400880314442c42c102110440610300110700c160948001030440c43c0b4005003074030203035000c40303028000f240c000721900c0d1064003090140c428a8060400360342d883d040340c14030556a011120000d46510b8140d003100d84504a80c501035103203122202d505950119003543c3d002c1c0c2103a21011003a44070790b0030400d00d914034089042644000c01707503e80f242e42d0070aa1640c035954106822016400760700e0a81030086d00500c045010b11030f03141c1041400f4a1b0a03482c2002c580c0e40c40741048400e54044485a44078040c00b4486610814401018402c503001000802c2176401c40c00781e8241c015201400301d03070001a0416610b51280c0454002e041c01520401440c03070312120090040c600007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 594302104 1250 594300854 594300869
    0x2210a14060604090503161e0b010509220b0703150b131706071215060c0204050105060306300703050303191107142107061a0306010e0c0c0106090204 66
    0x40050800d10f0f00303209043c10150440c0040d41407081010342540400400300c4180c601c100b02010458652000d05d1070001c281e1311859040c03c040d4941000d1121071030700917240d20307190724078105d51601d040c81c0c1100108071503410402030501902d46100580040c600444078030360114800d00d000c640c08a90400902030104c03e400400c00703140e034032001030b030080b80c000c00d000c50190400408240020b118203045030104400740b000003403840303440c1d007070b842424510390080780460b507201e0055066161910444c1d00510040ea001442c502d0400000bc101c009040221607013061300344e88440e00c50f5410b664540201091200700c40710103882e810302660f2500111703400350740c10b0243e812800701024070340145140c4d036424903101401e0003903c0d40e868100c8a02503888101d6445800300d800f10218503a2000342c8400ba506142954400c0c1500b842e10980c1d01495192841082d052000b11480e1000036600341181c280272402c8080c1c0c1c035155110b100c5803007540f455070a50340c02c00202080207441c0790700800458025 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 594303354 1250 594302104 594302113
    0x30a0207080f06010602250b0307030501090f050c091c0204020a0305220215211006020c06091f02030712030609141308030a0e03070506090d051602210a14 68
    0x80344807143d59078000d0050400503040500a8400d6100b00c12988408904c034141054040351140d442c401960402c403459400030f6100d0740100300c06895880f5135807200700785550501503440d0030005148248544000c65014000078010720609000304441c404086500030819035445001d150010003809003941e02046104600700281e24412001c04105407142d4084c00c010f108020740c01844409801001091040782114070840003d041c80e030510b41e104e400180301a4000b03504000c0c0003440e00001440240c06040204202001c1ea80c4030318104028501c080ea003681c141e55106412421401080b2005019801808604072a5505a0803032401c1d141c550b8010800107150030001c030603030401980c0701800c09039014444000305040100850b4004030028011807121045400d01e80f440e0700c115025143c40d0804800d1196442c014400d0418010481c40c002c0c0c1085003e11801d4402803002100900c1103403040601400141c6108a80381c1d4100d582c1c0680f1544005802c1600e8509102c2c00e019030305018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 594304604 1250 594303354 594303373
    0xa08060d0c0b0f0c010c0c0c090c0e060c07030b18060a0507080708041e230319030b0d02061204030909050c0a18270e01060b1c0e030a020708 62
    0x51000c802102560080d40d84030a89140034140412544541151240c0d603208001d0740c0d01c814004d010700e0300250b403c0d03521100e04a0305400c3c004641605500080449030070400364889403580002d0b1500c40d6001160119034070900c044906140c0032282e0300045c0070b03180750002c0001c04509058102c441a84100c00c0d80d295644502c05e001c200c3e0021a6643c002c1356551021689440c8100300c2640d01a103e20f4110319085920b15019000f440c03613003811104005002e564041030406905500c03502c04044005506244108200f005102001c2c1808010107646611311009a80e40c5020508516000b400340b0f551002c1c041744030305c0160760440b4180c01042a106000030100b5443c840d091090600404003800c00d07540349400c41d009580000704090b00b000802003c00c0480c603c1d460b40e8003500f0740035800224400002a08010b44160355404080c41c1d02d886420084a01450101c50032080641403441d0a2650003501e0307070060452800d404014403000c2000d4018540000300c04058070403090860b41c84c1c44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 594305854 1250 594304604 594304609
    0x5070e0702010b090f010b0c0a170a02100c0c0807050c0604181a012a08120402010810032102212d0405060912010c032a0905100c060609020a0806 64
    0xc01c05d031840707444400c1440042091240c00c10241280710400b0301aa080d545c201d0319691078403e1944169420b404000944054440d01048035441d89402c200041c0310106603c50046c0150b1019280504540000104c00f02009414480c110f82c15100074006510340340c645581e00c00c00c0d07000c07001036114503142548403030401c8200104171201080c165104940300c601c100010701d010026142041001c01401211000112040c0180901c0f0060000884451a103130000400c400f801400d0745401081d0703048140b01090094407001501d9244d0f0b6519865a055413100301d00c0c191408a102007460501001c0c2c0503101d10150041c14021032554004c04400d0400030352203240001e0722100590400b00300010451428880c02510065000400202c0300e0042e0f00400307404c0d12032003480c050000e50b0343d040c8040c0703c00da4a45183d28100b010046101c540e03540c59000340500d074040c014148140d003e80743c0d07006841e10942036a80225802041407010540d201e0000d4003a40141c1800000310706070400107107150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 594307104 1250 594305854 594305869
    0x606060d0506030a1e122d090807120215030106020a08090f0306090106060e030c0109030b0903120a060e070c0302030d090510150f0602033a020304080904050a0506150f040305070e0702010b 83
    0x2404481c3c5001c1e45810001c0c003a0901f00f0348002841c02d019001c000040c01c04414020b01c0024034420031402c82442e8103204120203110b0140c82c40da1001d1080c0018400030b07038000b5892400740e40c024599691599010300050323640c0740070854107a061080404206095406402980032103d80f034440309400920759081548400d150b02400b800a40c40c0002000800d0783c000f200c03a003240321401030303929009214850749203400007243d488048980b03800081140900e40f403401c80c2d21040600c3c1c410018074156800a4480c0316520441090f42d40324021030042c802d082c420b40407040c024900800132020310100c183c840100c50b205038240c0318000d280c0010f450f400842200c3c0545113510500c0e2103041c2c402600000d026501d042c8181e426100c15600f0140c00962006501980c0034035107442d02d940581041000752174004260000f003508020500c503290b00c0d1a52079000c1c0e04600207036103407503450681c18410345014550000d05644205040040c05c010005513850007441a40d0092207074038415030900130031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 594308354 1250 594307104 594307127
    0x106020106051020190b130327090f0605030c031c0f0e04090c0e10080d030e030c070e04030f020714060702040219020d030e0606060d0506030a1e12 65
    0xc0080005003040b040c2c0300e20f0513188108010b01150b00c9000c2400308152400000040c9400c60b10079006200c8184848100728940c440c0605d0352180b501d014607500140180d51b00070350101204100c03a42c1d034641c260203850600180002c04000c1180d120310308000f4000d421103108185c041d0160140c0e0740002c0c1000f044000f40318035100c0c4403540d00b016075041161240c18403840c000802080808090f00350f42c03240070760702500b402642503070005410203815206c03940000c0e00320f101016920301c04103c0b22a0101e00c56902800c103060000d450101610240c1c110b100340000e039141801500f0012501041e0507402c2c0e80190300950707504140b01d201c0703241030f03070f550b0b0580c055400a10038070082081103252000080000510261015003000c070985008910440c14040070800f6070410410228415130520a031039207202ca031401019a41050380c0400c10a220390111648403984400c00131b069070b142001007c1e89d03213910884000922442d10203c4014500b510340031940c00040480351203210f03100f400d010031b1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 594309604 1250 594308354 594308359
    0x30d0513080c0d1b1a0a030605010519030203090a020d0c0905090303150411040b0703030c020c0415090b1c080c06070c0218040309081501152316150b0306010602010605 74
    0xc11403551908050014084c0200d03140e124407030700105003032080c40740c0040312440344c040881e01d44800d1000070342614084c2d04850304115040c00070341d400d04032140c9082c140681604006036070341c030b801e0801801e2141d20b40b0040d4201c4d520810345401c101e80c20003007004907000040104510303240c2509541e181d10054503041080c0d548540c3c69010351816070300c080e000340400d4411501e005e40c1c1781d01440861b00031b180706401081d070320320319071001c290103218002e40c134001100e04028841c50123100c1c078041c9445005171020107036903100c41e08042e210f124903802c100c0780700d280201d014903251401d002d03564405110583c85010301c0c40804c220074010790749c1c003402907401440104404808604e01e11565402041034040242068000401000a002040c1040c401403507440e01b56050080b4004080040c50015080014501100743c2800c800700c0391420300051104403540d01e0344000403411850352040303000b614494140181c200c10600c15400b89822510540c1a60400da80c1e0302000da0803111a07119464 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 594310854 1250 594309604 594309619
    0x10608010216150212070305040209090c03030d0e12070c030501111608031b0406020a03020f1605011b05010f061424072102030901090f08120901030209030d0513080c 73
    0x90424071012014540f42c460060a00300300304103904003800c2c280d80000119984405010550610306034217540710342c200b4001c14030030340c40d98042503603485100b0306c0c000b903140c0c0d44074566114041403000c6203000e4030320b00180340c44018504003401502441c2c4011035642d0b2030136403070b0704c0d4401c3c4d14002d96107401c2e06641498130b4105180c95041d280d5000502d40601001004441d49030900c01c400504094003c1e40c1c000c01e6104c009203000380c41d00ca0300d14400e841d1544590355603044114845007032029120207191418070702130048503520241806401c001c0c00307035082c0070300801e003500c03540e002d4400c403480c0c1c25004c00040340d181c09014400c1c0910310141c03402c0c19200c5000e4020310a070401003c10700d1141410a10010340d01a0b07021884250351041001a00000f500015540c0d00c001444080c202c01400080c032a85010080c3c0d6a40c98800b0215600071408101e135443e030382c007943c140c0b00c0b401d4026003910300610100b035000344541e104000b4154400c00c0c8e0040880d80d0f580000e0030368900c030320280284 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 594312104 1250 594310854 594310897
    0x80124030c0e0402040b310e0a11030f010203040b07030b01030e06010312050405090f010911032e030813090c09030506132405060a12240b030f0a050106080102 70
    0x2410682c2000740141d03042900c89010a082e81c075285545280340000c007440300c0380d01451601c030010080303602401e1140c3c01c6c140300b203500c80900d010807446400c45e800501e14070140c9564000c80c0c1810b4a56030385c3c03070903548040200800d001030030121520820f81a641000100c6030040107508035110f00c3c0d4040300d240d1103940107100050030901209400b2007541056414203036510005800500115155114529481c004201500d034601401d020150046621410361074000380150b510040c00090214500c503400300b2140c06120300c090300000d160440c0700b080d9281ca4140107082440014800c0600440c504116800c3c0c091007004000140e0b40c5c07080c045c1003030b6141c05540c2600a024079401b601e40146a005031100c1c0144501d05211300100110041174500d0503c080100e0b16015038041e5030800c0784c2142d0040081c00202c07a1601030264040024189174804400400a0a0054503545c151103052019856a80000344080c44903220b00020f0000f55120400c903401d078011900e401e101c205000040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 594313354 1250 594312104 594312119
    0x305010501110a120e030f100624031a0a060c021f050a03090c090e07090e030403020904030503310506010b34060903080906060a05060a0e041104080124030c 69
    0xd50404c22440c000c0c24401e002800282816803503043e0749016400000382d40e00702a89030142800506081085060b1407080d001d050540d29030b00e0103c00205540c0e51144080780c0c0e0036607088840f04401034102e05900d80c030ba40016105212164090f03204810900301c0d400d13030050441022490a10b10765a09042030007904066000c3c140b01e80341192140c07140c040100f80788880d0320403d10324400700d0780144440b43c90300345410704543c1c1c000001e4105402c100002e00150b15104e0344c41e034000794186041c6030340340d0360140b00a0344486548200702559002d8194110b40c007403040000c000340d5000b401618410399a440c0c810030f83d0312950703145d40089802058194402c030780e00c250503000c0d1981980701c070110f4411952200b0858041d100c0c1100492000414041209800c22007190702103025107d01c1324550402d00007a125002d2300c02131000b0004100f840401940302c40d00050550000e0306003503511144c80303007405400b90040d040f0150342125500141080d03e4910355181044980080025010030f003890035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 594314604 1250 594313354 594313373
    0xf062a051909081c0f020304050108061e03060702030c0c04050f130c410a0315180f030305090d1403042120070f0510030b10050702010305010501110a 66
    0x41c01010310a00303000015a8050034048804850f904030701c6280301d103c0064014000340140b074002c2085500502052040b642c000c008250000b03002c560061038520810b03142c1107100c15102040343c00d80120024050400d40000c0503195144d400f178140c914201c1c0500621007220350441d1400720805101021030544810382c0c20107074840c5d00507084211001d4458a00480804011914001c3d2100705410440d0f00e4052031403a040003400d20f07449199000c0e0701c80000380e0917a143e01001d4044190307462500c000d080c80d0f5200c50074a0348800f00820044e46142801d4020001c0c000e429004203051600041c102d0f0b00210300c1003040e01003030b1281000300e040c903800d20402c0d400050089030401200c85040c829410f251480c100c00e07a00c1c07070340c070540f00700c4e21003440100810321940302909652143e0030600c41e841c1009600340a9540580c5c607492148001d0300224054900242081c4c0c1111108102e5042c855204004080880c000e03201409240d99800045918001809110190f900410001e4000421454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 594315854 1250 594314604 594314647
    0xb070e0f1c08040609052409041119090504150e010b09030114090d0f0806061611040203040807050d2f0f03030106110118050c0114070f062a05 63
    0x14610801d40c4096031a40c1003580703d0f40000b804030341178007030401c203500d80241e00512540c075140c6c100840b05501101d52510340268018544550740b0384041e0781e0381c03580c0c09055580d400726004103203c8140814101601e100150700070180114202404c07800804d80342141d180858074800d44c01025680b03081b2880d402a00314074443c1d50306540350070910b60f041d080344030594082c140100c0904004a8441c1c0301a02d0850350b1001c400502540c90104400c075500c640c01d84402d4084c5000d0901c4070755071407800c0740c60a440b110314079a12600c0401840203005103000507080d160310404c102c44080d1007422042d120414540c03d00e908102c0c110f103002001d60030124030300c001c41e80280201d541c2c03002d003e0900c07070464009810120001e0415606148525400d005a480407801c00c00c944450314015240c442d1501000c022507030500688039624102c80c00e1500c100c13481c860b0420300d250f011114515111015040340c0d09011200c803060800c40c00e44200b0200c40100b000c9258845616000786401c0c00c0d00950b0070030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 594317104 1250 594315854 594315889
    0x120903070201051912140603060601020a021e01110d050901090b180d1103071e0f030c0e0403020f0609030702040b01051305190302040e010e210418020d0c0207030b070e0f 75
    0x9003a441d80c040c005c4c4c05005484009482d0302c440320f00c0c0000900d440c00400900701b034115403080d204003003d130303c03210701c01101503001c45803603442940040011f80c1c0d020281c1c00802c68a101d0103e02410441c0d00c90050440e0302000da8514460642d00d0305165a98018088800305410041c1440034251602841c1c0f4100b642c441c102c403261000c00200000d0a0580581c440c1034140d0303a0640c1600414480d0740684013405180340c0701c100042c119110786603100c050303005601c1420302200102e0107150080100e01e80382d8400300300311101480c10112854a0341c000312012130150342001412007081d13006034103682c1c01c84d80101095440350b251104210080c8241d00305404c00300b00e400c2001c00540c581d0700841407001011800460840d40b040251803912100c0e0344800d0502d6800d804400150380b206040300c0496050302d1011800c9a41051000001c2c82940d038169851403800309d8807190150041100c80c2201d00442c03100d5540d0780c2c0d1900c140e925582d1032341d11640c004c0d5141007800c0f052a003651b078120012a030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 594318354 1250 594317104 594317117
    0x14090f150409021e040b030d021c020f0d170a0606122013080c09011a07170a11070509071407050a2411090a0e04050c040f021209030702010519 63
    0x6a004140c07144c218840c2544903400141d400905030800740200081e03039205400a0043d00105100251aa00110039040d1081001c211400c1c089200f0446ca4500b00d007040701b61090f103040241c001c3c10600b070520f0b490140030074400c0003d448001d1817081004441ea00e8488825958020b03080030002e010b03a4200da8014803910601c420200d01c0e01020303245020b030000000311040d0030b00300b0a03490f00381103803a0301c0e20410136100140309000c3c001060140c500070741c50080ba1203000c1e500e40036441d5840f046101e6499000841c03201d1301e050b4804203038101680c0721029228001d4840060126940c01201c108000c6400321508072100c40d8100020f2281a0140058a00c6080d103643d0310b90700445e81c0810003002c24015466198400803d02c02c580071301f030070f0311611071402d5080404500742d8480361092a014028520000b0b0038004180030121612400500c1048141e8900403064000c0d0805040421025003090005414450000441d50403540584481c0d0400540d00138030780b40d81c0c0b0f103400700030104400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 594319604 1250 594318354 594318371
    0x6121b0b0408010e0c091303050d0902030d0305151522050405010807050a0e130b060102010e01240806010320060f0a0906170609160201150e0114090f1504 68
    0x34010060806056420000306083ea00b840c44903141104c151003151082003a0014040d82581407032001840c1941800c1c43c80c4c0b40ca00e5803030b425000301945800650540181c4842c080c6456045d84007510442d00304101c104509080420f02001a00398451381d0521001007081d031030a900b0004064200c001006000608a5114804a420b607842030f4804459a1302401e0140000d04d800610b120140c170f600440355840345007020100c00c00449000c0d02030501c0d202200030071402d0340f00b034210780350b1610010000e0120030900d000d15030341c08581c9035140c032a10800300c1002c901101c0c0803034414122604550f0000c01c12028521100880c690980042c0d44800300700f007150040806503020302000350207510f074088801d1178004007400d0300c06150b10100b18901c502d8108135890342c1f211080e80d04841d030401900b2041c0402c803410f0b80104100703da00c0f900480550800036500308511026030686929003a2811030900e2402844540d200a45060503c55803000c00030700c0002051902d03a5203103034001c101203180700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 594320854 1250 594319604 594319619
    0x310050108130614010602010e120901031d0123060303040515031e0f07080f0705120408210402030c0303250807170a030e070503030a0305060f04050108100f06121b 72
    0x2c0020700021384001d40640100000b907028440d5044074040b8030050a0030b5200c0c0b03004440148182581e01c1d040c15a0341502c0341d01c0b54049070106030241c00a038020403114540019921085044a0741c08950029040015103281004403c0c3d0302150030140c20303e140f060304811040b040317030001004420300c00b0009180320741401c1840c031058001d41d1350601450482c1000d10000f41b882e04010184080c140c0c40700180840c0950150440e168550018000070702a10b0b646011940c507c00c00204841c1c922108140c2034150504454840c000e51084088448400307001051503101c2c001d40303501551b041ca0100520601c101c00034980b80602c2c0c0310309030582c41c01d04165a0414042c85410b030070001c112000c603102c54800e40500c00c0e8000070040e58014000540381c07500103540c0384216090300c0105a1170760082107281d00c404070203206590005109005c150f0312040d14a507a02144540000c01a007080003a01e07000185100360340550b03450031508201d0a81035110304c08410700c41140a020101c40d0301d400900c9a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 594322104 1250 594320854 594320861
    0x90b0315032a0114030a020a031514010318170c010e030d020a110601030b1f0b070605040b01090e190317100f1e1505160506040b0c03100501081306 65
    0x300808080c0c21a82000c0800100d402c42080c0b50081c14000d1200050218446240036290301100180340541d59032500a0101c0103080803403620140098051004509980c8008481c20b03656400e0340c00b0412000780c4c05101080341081d400c09000c5a03002c1c005d05640755011801409031450420003c5148180602c0e0f0381d2550f40b103915060101c59000c80c41a901300c1d0310602074082c0d2130700300e03005065a50541e110072503034040291540900070006001c040c401100005040c6c0101101300403540c80e070781a4180407000e400304650444070502d84400106084056101c0ca4100c013400341c009041d1424500072681001940c04000c1e01880004d40d03a405684191715819481190301c125880d1240b45403641c00108005690080800b0304d0200c10b04403010210800d01200301d8002d803000206199403458140d07118444c0e00c3d400700480e03c400b49200e0500400151350360085104440340800307903039a0340058106000503280d059a6001715102040303590300c9210400d0308040c2c42c114101180110b0b0340c90343c2c200c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 594323354 1250 594322104 594322123
    0x23011a0d080f250b01081b0103270f030206010f03051506060f1606060512030d050c040509070e0910060503361516081f0e1321090b031503 61
    0x406190f800441c0801801240c82401014050002c048040351100d070320217a04110001e490415507500198111242e8095200036014013070301d0042d0755980c0784d007410400d081c49281c4c29000740c89811b00014045061907214402c40381c010001e080c419600354901241036038007a000551001303082c08289003413121107004050946c0a2180100d002c196883c06c41d0607030301190300071071240101517540e520130107000c012500205000440094a83ea80ca402c1d58018012501b02301c0e04a100c500030428042d4215080f031141b0001220090311542c0c8800000310b0300300507405980d00040c402d101042c0c080107841042a01751034034480c0b203c20b002040d4541001c3c1c002080c5143c40702c1d40100d00c244013106070843c0d20380d0001808070300005900c04003034001d44020800350640c40d00f032035040c1c140c110b4001401400009003a08001211075420000c100c40b802007501181510504510b16004810710120700c1c03c00d0b12501c15440300a02985400280080c1d5000104a4526501100540d040c181c0e8180810702d038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 594324604 1250 594323354 594323407
    0x60b0909010b040b100909050a06120b040b010f0308070b0a0e030d151d0105011101090b18101419020904020703020105010e09030f040308030403020a23011a0d080f 72
    0x511020240400c811340b401025210702403aa100300c441003003607100300913109658404a01003402d0301c5501100300189251703400340d001544c48004013001c00400408007400380b8002c2c0c409032502d907228034105410001500c4010f0402d8010043c81000401c5162519030190b104040001c2075406a550903056611194045240079582c80600e11458228001e09019041c00040c0302c2252800010210302c55106000701c40c14441d111041501a01094004400140c0d1004000410b400d00c44140e01c00001000e54812540c040e100d140f01d0399004c54850002080d985049038940c81c1c44600c1c4500301c10f0b20031800131060300e4080182c80740030f80340c5000030026188a540006050362510904842c4030601801d16181c641007007190f801ea00026038140c03020707241c10013051592522945006da1030051a020028441c851840d000c0046001c03243c2c0c5400403442401c024040c1c2c4410200000602803e2402c195001a038074449401050071100a882c15094044a0b1450100d5000840c01500011044001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 594325854 1250 594324604 594324611
    0x70f080d030501031a0c0d06030b0709171518060f060f030d0c0303020a0504030b130506060406080703260d020c070e0405030304020409150207031e02120307030504060b090901 77
    0x1008400411150110240c1031604000e41c1d415a035580201310036a02d41e012a10006902080343d45800d8000c4404846048400b00304042d52482c00d4040c250085a10030049441c804001407401c2c03805c5900500d400d8003002524801d04010002d40c0317684405812031443c5240c0c241064808001080600d0107040c112030011000d1410000704014100e5102c0c409002e03030480c440085249400c4003403540055032600703000d45c0b5600800c904460b40d015680c0043c007030760250350610416940d109052103105004009550080c3d65040c103010507900144580c030035a90055100708041202c0f103503169454154406411254180040c102929802c0903030803800c071700d070300046404c0c2d002c3c1c3c100903000c0101184119580140742c562030300d94403030000400203802382d5150382c10001041901e1041d40c0340707422400e600319240d41090600030800040001c140c401602c1e031019840300c2c07500004403140005004070781b441ca10765680342e0881c003505018008685554503804585080d6491402040c40b8090590001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 594327104 1250 594325854 594325859
    0x10e0a051009141b070308040305090619032405060a030f09050102030f190501061e030915150f050607030f0903020406060824150a02070b07080910090b0306040914070f 74
    0x64a8001c400a440c0c0130348008000003000a904030302426441609400d281c0e071901e00c0c0e400841c2540c0300d040458400104482402809c079030301584824280d40ca0080c00c003c1d9005043d1001104400038020280e008000703210240403d44242c0080320351918000c8007090780325095450600b0380e001582d00c0c0c40ca4180520401140082400c08405a900700722400d00c1194900303c400b0701400368804d03070010481d11020039040a64003903001590303065405055040c0e101500304020f0018240c0c502a10382902500f180090300d40d08825002d17081e074000070009441d01d03075159003d4500c440396040620030700c050102c2c0080541e6a82c42854001c201e507071501c4a03145420030440c0e180462044060984e00c0c13421380c0460075a1540f0360304442110540e8011a55032414178000d0f850300e071281c0c3c030010144500007200820880d00c0c00143c450480c1c1a94901501c00d60300e0001c0d5010590340c0500149140c083c030020ba0285020b070803090525001e421207007450901c42148a013045c45581042c200084070001c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 594328354 1250 594327104 594327121
    0x60e1203341415130b07050c0a0b160c48050f030109050a0222020c070f0f030510050a140a0e0606040b060f07060b0a0618050405010e0a05100914 64
    0x203205103626442e100107002c0c80d001307a82440d0603c001401602510301c0000040845000301c0465540e11030400c100e41140c402d5251551100d0000c5810541c80d40c1d41310704e22001540200132080d042d51b0f2104508074200100b0700e44c040d0500c1c258803084c1d150311550b9440c036080d80f50100f800c030003c0e94180000d0342d46800c2c902485018086016400d00aa02d040d201001062000c540c0f8000145e04841a443c01d10307810024603500080189c103000c1151000500c01841400090400c0842c0d4850700051181a40c80d40328130783c94201e80c40080e2070b6400503641940c600c143d40d403089a00160f071100005000c200850113044030007003101c1d5854600d17903412401d1001d10041245a0340820101d5080c0180e540e02400326070700d40558041d4040f0703003601084280421031290012420b40030050a007409240d40c5030030003000100d00000d442d102c1000404d004c2545d00303050266605842c00880e0341d52598903091681070081000030684085011550408541c0340160302a007014110002c18070080c1d03040c070202 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 594329604 1250 594328354 594328363
    0x206070302060f0c18210d030b130905060703051e090a1506120f02040204090908070b011d0c07031205270102030402010c142104060e12033414 63
    0x112a2401061090700182154010b85d100700307a80640e406924280d0841a55803614001c0c540c010580c0038100d210542d20b545603004500b1100c0481d104220300c1c2c0d26442220840b802d030716004e041e40c1c100d200002c207d80c1c065082243c00c01d014a0f03c40d64040c0c0003903049003407194140c0703500d0900c0d08400402000c0c400e0b04070300551500030304141044040d107840000301100340c100000034415000c2040d031500755911070381070f6030091554010500401c02c05241c01c02039944071400481e18900404004614503031b02c200d40200d104108051080161180c541507101504110812002c200044c96080c5100c4498041e076402080c0c80d03c490b90304901805003400000c0b01c008003105003688140108070150307030301c81740c1d0084c115044000d59290004505c40383c0c0c1003404401010342d04428500780358001d030380c0c000000c00c00c07100e050341e900188a60035010030019003803500014100c0c0e072060100c114540441011441c0e00f04100c50b503080042ca00d601e01c030721840c040b810306440c410b075a5910b40404c00c10170321 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 594330854 1250 594329604 594329611
    0x90e0c040c09210b0a0903140c0d120915021806190809070815190b0a05040518060406020430080f070b0f07031b02280206070302060f 59
    0xd03014040019504801007814520f032042c140c03400001004541c414840300e4500e03a425402c034205484600e481c1d28000040c0011940c11030000301641040911065800b042d61b0070205900c003d00711041141ca42115043c0403045803041040c0c4e252034400009009101012070b40c0401c0c1030258030f4a1038044000c0b50303155130912050041408000a03c0e140321203d006104050782402e12092030340301da80d485490108950081c80c1684500d1480800000030020380900c6440d107030b4a00c29a5001c509088002c0da92034088032604201c030300d00180000d281c143c01c102c2d400444032050000c10705580540c20705e401000e031010b8504a0340002d0600c118640410b2a82c0b024402103003443c2e2041c036481702d03076a40781c100708000b51071210701040300182c4400223001c03205066003042d080b4469050640086d200f148098030194003182c2b4020940c6401f0340c0522500003900e04680107002000c02111001c4001171000b4040800640480c0c2201d0060f40c4010107401e020340a503000340094540070141149850025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 594332104 1250 594330854 594330859
    0x9010611030d020d020f0309151005060a080402010225051002030903030301031e0f061a010207050d0602210c0711010c0f0809010e04060b0a020105061e150702030106090e0c 76
    0x40d0040e412140000844000c9075002c00016034608080e89500028080d220092105880010a0180858000940701075a054000c610011501d03030810400d034090403485031940006050140003103981c0140d001551081c018015070b4014002804403a81900000307514010b442000c210a0055007840035100340550014001145851090700000e6924003051000034444921403901030380941030509a541155804149581c03841040c0c40c050b4060302400617100b444c02000b0a042180750f10001e001804c0340c0c000380c2421003615a03512480c1c080d512000506203c2d444d4103889800140340c0410162251b6110300d0019103400c080e1a107040f07950450340d5101d0400010307075286400714400d4070b500030043c0d0380080c01c5a9100000401a600602400c4c55640d009244c604005002e2042500038003d0040c0b590082103a07640da401004500101d0304107441c0000200d40e110384141c2484012400004e05252045040000503400242521103a4100d40340042d20b80400c0036000404121100002604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 594333354 1250 594332104 594332117
    0x10905060d1106072a06180f0e07090914070e180a02070206040f06020a030f02060402060406081f060504090606030908030604090f0807080a030606172707090911011704170903100506090106 83
    0x8108003011008014007800501d07840480208604c9400342f1044002000d441c9000d100380c84002c140104425000c0f964100450781401d506011840c00f0180078403a00305c1d03443d501c001c07900c3d104840c000075006000d040340c020808010101e407610864914000405040d0300034860341c605441c00526801c0c2c0c1c000c2e40000c0d50300180078840140d503080c05541c19103540d89481e5203a0398403000007080c2c18403078110b4101c02d0034102c030001c5202503120005009071206101c080c05a50303901c001c11000c9488022000d0100344051012a0840c03420b03811902e030303c5008898144a08441e030300c0d40c01c0b490b07000c040119880c580005580c0f4491382c1500884c80245942c0c102501d00d0b00b40c80080030808000201541564801c103840003550076025130b4802454680d8070700b01e91219480d58901c1c00201404a82074410246980200b03034298401c51080c02e90030542e80310340c50307031b0b072100c0d0b0b5000c04150840250b9030454138140070040c03154908106118400d40c0002c03004c14642441414005880e0040c0c01540030800d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 594334604 1250 594333354 594333359
    0x3151b050703050306280602160f0b220b04090c0f020309010c05011b05220302010207060809010f05130c0915140a09090803010905060d1106072a0618 66
    0x4001080c1d80c10315801d82002c650300d0b51400000360140582c100c061441c204010010000c20350040340500c1550340725000c0780c1400039005180c1c803040100f4030501c00c40221003c0d043c04409110307030151000d05a40c1c030340380e894040e04040e0a4107401040e04000c09016020070100b105481c0360050382404141400c20801010318040c00035181d00c261003a040c18410300c40b40c100704000007548580c4c4e1282404010703101d1482c812400034281c2c1c2c0121480c0303003110007043c920840d400305524030104495058000300b07030031481c00005482002000b0003d2041e55654410742c56451814000c2a01c214039070300d800030a42031589272480703280c2e2040e04103460729807400d100c440324400f18a626105490000e900040c0800031100041e0358585660020a80d4030b00306020b513820403645201560680d4401c03842800a961114188240e51301c00d0706014044035841001114141014002001c42c01e00900d44820179034004030358001e01030280c0c6a0f041240d2405541017140c1948400a61f01001ea01500240c0061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 594335854 1250 594334604 594334607
    0x7110d030b01201c030b01030e06061f020705030a03030b011706060301090b04110c0c010801080c030a1401020d0c08060112020310030311100614090606030907180f02030103151b 78
    0x6181c41c40c9043c000702024400d95207810003c220703011070f40f9040c40394a0311403464020b01400d0350485c054040b82c200015000800400f245e681e21400340607140080c55a24038500382c0d246400340c2003030420740c040e00e1004262074905001e1141c10a000346c501046c2d00c124030700010072403d12000c20740b004400300800c0c003c96035551000c903411118814000f003072102100d4009002441c08040104500000141000074031001284518424009880e680d00c43e0380d076900c80035101c20b6400d4500b9459000400107a00148040700d030700007404200c000040c103040c018a02d0700c04841850508501081d000820401c1940c2d000002c5041c850b0182d0056040d03041c0a108000b0090440c000203040c08000c0d628085095403c20500003020702e040001c1c0305440c0d68014074000d517845405200e0158900348001841810440212801122040c000344060351030040c00c1180300c4048400b070115107440b4100164110810300241d8082c0d4090100391244403130401c07a0390f046400d0b1310380c9038070359911414094102e04e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 594337104 1250 594335854 594335867
    0x70b03040c1409072003180405010e07080402010804060612061d0d020c0d0f0b0408070507090207021f0e030d0509040f06030b0403080703060b0d0209100504080c12120307110d030b01 80
    0x1130341442c020b00c0c4411001c0c003919103040c4504070303110700c80800d0281003200d80582500000006480400c482d980b47c51410314400411105000803d0038403002c20700551141030003c0d409809007000042d09510340c800c1d004040d0405005641c1d040d1580c034109000c2c81c0303002d42078a100e0102c1c402016032910000c03010703498008519155102c0c03007444003c00240076803034040c150203940c040110300c424641860b000d41d60b90000707681a0391034032030a02c010030a2801442200c0c41e054006200c440d0320180d0400020305101c03a000c002e42005940c43c3c0c0c0d481039440c2000124841d8246448032515180100f044c0011951802c0b075041a80742000801c10100f024030840681143d054030304101203a541403020342c00750009901c0a0b4201c0e03c000b4030700881e001207901034000d0b0039040300e1900102629010848450041e8000d58503250801002180700d0320b8803403800200401d65170180ca65141403480251241d410131034804d8042001c0d10480400d441041c81042c803011024142003000d00003410009001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 594338354 1250 594337104 594337111
    0xa0f0806090f0706090b0f091207081b010504030f0c090c030e0606060406050a1416030905090604060b160501151e120312020d090c06031e0501030b07050912070b03040c1409 76
    0x1006c0000b4091110361444000c07580c82d80c00140180140c92031101c02e0325a42c1c0d03154800d1040742c0c020328101d4000348002c3c1104075203611050303441074105401d5498064200012010890b81030348042d00000c0d00e003100b402950900c1010741c8000803481d544020b04e42c05c0c1035000740464403501c2d00f0070003842883e0f0000151180d13200ca42c90304100c420342900c41210544160b2225070050505c0d14007040c109030b0703c00446070541d101900d400d6540d440780414881a20258001c0505051007444000490088080c0001883c0e01400011411000c800c0e8411314280c103e4100076011100c02800801d09800064458024018451030f201034480c6030701e0050400f03a04480350307100990001210145902c0341c2e0070415240d5000422600a0f5039203403c050002d000108808207540704440362140820900e21074681200d070011040c44c0340f81d403007800c226181d030300c4045c0159014042c13840410203034070104110740142c541d12620703550700d08242c102072920311219800305900040d1030760005090b4940b0f00c40b9941 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 594339604 1250 594338354 594338369
    0x1d060703180b0a0903030b03030316030e010609050903070c0617070e010c08030703150515041802041203020708011a0d23150412020105010602070e04020a0f0806090f070609 76
    0x88a500e6809904038561100070050041289202484158280780d40403130340c82071013034504110075030044082c1512804208c56881c0025501142e2000250007074000030342c14144074000088035034407001c0090803a00141c0780c802c0503500104041040080c041d00c2400907101074101486201c144800305203c1c0d100c001c0000003040400c5e070110b03001364000c0180c7c51a01d907000d4000c40e200d16112070000c0040c0000f15038982040308850300080c1d00e04284100038455600081800e00e000e081c01d8483c01619a0390344d1038643d8580c02c00c4006000301c44580d08440440c0310350701521b4001d00d41006942900c07541d0840704403003c0d60f684d46001554504c02c00f1040ca6911202d00c40ac0720f10030201400070402409403414035070203500c6081c0d07800c04045a030540b01d00c3c86841060304542c4c20a200324200c1d0801d0091301c000d03038070048091014000d840d6105902a1005120900c0d9031f40701c2c41d13040c10040003039218000c26440503080c0100310f241400314802250708403006140307140c54654024510155445840b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 594340854 1250 594339604 594339611
    0x9010902090402040e0c09030715050a080c0405060c03030a0533030109020301180b0f040b010513020403080403060b1e01120e030909130203060903091f170c0d1d060703 74
    0x104545a60b01500d00405d00011540c0040c82c0c4445050701e1079100e2150301e0302c01e000e402c0020810032801c001a0888c24099503440b410243c20f08000ea615100261131181413500c180b00c0004e480c4d45400041407905800d0014544900340f515030303601a580d000e0205071103602d800f07000c00c0464108044070090429914100d20403000540c010900420740c2140203505035081c0a4040100245080c04091013442103006c1500c2c1d69852140c0310846c682940c00400750614080104214604820410010a841200189070035581d6440c0e034030756030150388211040c54648240c0e41d40da10f042668464159101c660450301442c000000810f00d082040c0e007803154503543c0e00401882c20040007600c4034010098039200d02c0303091010035075954002054040748030b80700d40b80000d0506240442590826100039141a42040c0d121584807003c00c0c03181c5a0b03100304544a4400300e003184040c0c20090240c1c0701c00c5101550761003010884010390b0391031000c61890007003440c00f2250300c401c00107450760300c0031a1340f0313002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 594342104 1250 594340854 594340867
    0x506070602180405101a130302010c080f07050c01110114010302060f090315060306100f03020906131b02010b03010b13050c1b030307090f0311010f02120a09031401090209010902 78
    0x9020328001014031a0818680f50030031400030fa450a03040c00303813404403044002a051000000c41c06d8810102e480303901e0101400100019402814101c803520f114160103410155400b42090454115500554042e407028151003440d580091400c8170310707501c0704000d1003609568000d12414041c180300003401000f00141549a03052150251b451901000f002e4982e07205110340c0c080d00d14a800d40d1018440d000f50004500b07000440f1035070700c0458042480400007030b4655020000030220007003440e40c000250340c01840803000d2600c1000e6058001040d9450000d15150000382180e407880103c40c0a43c0c5400d2600303080e03039500340c408155901c1e520400701d4a5640c0c00209801c40c0110801c4050320160014130130364560010000d50b04c612419034805114560352582c40344c0092440c0300c0a4624138061081426a504c80e00301100407000b280100c50780042142c03400c030007030750210b01d0300d40c0002c01c0000e041c0104031080260a1480e01228000d0200011540000350030740810311600201c1d030f6000840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 594343354 1250 594342104 594342127
    0x5070503190306080f010b040501090501080a0602090d060f1b0504270b041509050a02090f01030b01032c06101a1e0a1d0d05061602010b0306042108010506070602 71
    0x2480038200700310075558485e10392a0207074060800740041354440c9003800c0003c600d45059118450403590490010f002001054649000a501854420b50401c494501060115086001d0890421440305000562100000c2c5581101007800080000c01c070701000100007a40380418096183d03c01c1c0745844000314440c1e4009002080090000354025081c118282c088000081d1510200c48040c042030100381e6441035000101d100e50101243e101d41ea0b4400030641f548a41d214500044c070604000404160403407844040e0b440c4900c014804140060b07040141c100305000c42a0807080060800f04003a04041e4184810385800042c0c9031f545001180c003015034884042401011945252080e5840a407420010814035003564001c5100c2030f510030022081c1130008000c2c4c0b0064010740076000940b1002942000d600b952440c9404640d21140b000104d982c0a01200d0b000341e00c40d48055200308107800c1903518000c03060409400707000d540d4004000c242c90700c404070360302154880740040c1c0d00e45503c0c00b1f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 594344604 1250 594343354 594343361
    0x601050f0307090912090602010c05040b0703050c060405010506130b0d080304080d0507020303160206040c0e2a09040b0907021c1202070c050114040f0510090e04031e050705031903 79
    0x468883d8900346001c21062144000da204442c03c0a42d80707001200352031746401ea007620064100000090f40810082240e03100d007501800c00c0d5803003482c0861400d0f00702c03028075150140c01c1d101901c080c0d54a901b0b00a46203050203117803403001078494003403040d14150700003d000741c207400001031b200c1000000001d007041591001c03120290b0b40684204050300306140c00035541d0b08200c40c80b030640e203080e6064203001c0b800007554600c1240e001e1001c1c0c0020303080540b49200351001500c50765100880c0d0b41c4111000b1420b04420317a40c205c680b8205a122042a02000142c2d9082d843e50307801140c9007410300ca00e595002c51000b0024001d6642c200c0305840d460340854103c5100090500c80c58408910801003200c1c804203541295003d0340d03901101141c051a5145911a07032241100c4080d00320b00401603814219842442c940f001d040c20301a655581c1919a42004100c5045001801d200a074202c90401d280301c1500101061600c603092411950700d6540e64814000020b000c61008400b140c0e001f0710940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 594345854 1250 594344604 594344609
    0x2010203130f080606010c0818060c0d0509091302030d032403080304020312250203121209071d0601030e0c0a08100509010515010c06020f03040809010f020a03020601050f0307 77
    0xc48500090769205142d85651150150340d00038002c0c400861200e41c4104502508203402c4205103150035408140c0ca21645000d0002c542c0000b8148445142c1c04410700c545081840162900c5660346141400c0042c3c0d1341e0010074151500607030340540400358400003081b0349401401c0c140000c0d00c00485640b50340000d07802046100540f44180040f04000c81500594021482601122040039a40a007913996010701c20040c1200c000840e08059003652030b45e010342010b4000b03810740d00d448800e50440141c99200d020310110044528080c00880d00303042050304000e00c515a000c07110042c000c2c502c030170090000740c105c0d81055158a03040203002c030240001d074880180209220030362a40c0703000711038031501e840245480031494103001500c03428040c051180300710300c2c010b1000b01d2070086c4001940c00311607115042d0780b043da0902c4151501441040198012802100722640b0368296800040c00c4c0f0701e01c07015040440d00300b109000c00203030300014882c0c1502c5040b00c110f840b02d105a00407926140321035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 594347104 1250 594345854 594345877
    0x1009082706190206100602120a210203011811040302060c1c0f0219050c04050c04150c141b0907050702060f070c1e330305010f17060c0702010203 64
    0xc0c0303480080e0002d0a86034038606890b0240c40d043e40e01d50822040c3c40c12240716010158100c401c813940c1080c1080007d0060840d58104480c504802050701801e040c3d40382c1c0f0351311443d80e0000061084501c41c4ca60b02031075a528440c1800910181c20100710b980c01035102c0280900d101245065800340b041c070443d080c030014503001c0c0041c60302c403850090001503086903900140c011078410100c860031071011143c2a030341000081c200702c0c1104040c0b0005000c01000d40407401030500c00401c0407059580f0001c040080da0761844803402480c10080e88595840c4020281c0394880c1c00c010340d54880410050004900807900311600b42c2d69000700355075070b03ca030388002980080005561080ca101d05000743c201e950080401a03d0b82e40c0b6490598100d403c200703008104804a400700308010341501480c6004803d1141c1d00700600783d10100c0c3d200946041e181d104000c80d4071000188810a01140c9917401442d4110340c1c80c005414800860307442e034001900650a5050000c1c3c00001e59008104544981429 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 594348354 1250 594347104 594347107
    0x2040312020607030f0204030f0828020606030d08060f0d11040f1b0c0f0b04061e1d030301140603090118051b01051309050612010501080705031009082706 68
    0x5003100944481c42101c204000ca480c01c075500d0551a610700c02d480c1682d0303000ba50713003d80b00c40a89581e401c42d0489000c8860700380ba0100240c581100c0c14000d07041440c0c4a8000b00032034140719042504020f03e03540003000304110501085815580d402c076848121109a07850341d68802d050915107200070b41c40e00e130990000e00707000c0b134000741800c0c55102403d003400c0c001610040aaa81e002201e400303244c190003401c00243d01ca140004244414801070f08103104540020303030414050344094400410400c00f481080d0390303080140c03403420002d00e00712840c0503c401a602d198140301650145c80c3d0f440400601400021000440981013540080880301d00020001c4100d202c5d45001562070380703040ca816950102c1c4c0c48010f0941c0d4002c03c2580c011440319603183c10414140380c1c0102c001d040c000c00d034540c0000814044640c0002c213100d194007a010000180002c1401c10007414a811290080d240d140d52403c00c1010104007100107441d8168000e81e02600e80901450a04401001d4851103940c080030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 594349604 1250 594348354 594348383
    0x207030c060917010903080c160b010e090607031116110604030501091407050f0d11100305070e0303090a030305030601050d020c150a091703060310090b060f060427020403 75
    0x1088080b820840b442034141429448010060354281c070000c2d48020003003482c58021400705034582e800b4141c03510840c4807402250703a890b1601e0314030350310a17800b802c6e83d00042414081070b100b081c4046a400292810148503013500094040040c0c0300d03642402d04001d546191100801100c000300030031280c0000e2019840c0c0ba22401e043d130090003465030840c2c40c2c03071003800c803454060303000700340e41e01200e1005009082c6070103650b043c012445a00c110448140080801110055484da00c442480d0340c2d45941c000740318034007620007800d81222561524403a070300c2071120400c2c540e40c02c019041680d0380351038181d0712901c0d203070016182d0303001d4130804031042da00210384508280000214240203c005210943c00c1c1d8888040d000210307400404060450000c10340d503a101407041c1001960854006000c50340041002c030b56050803100804030480d84610850700b03000b070038641190f4045951004444003171400380b6042c114082049202c8298507288013501f1030903410189a41500c0081d03400000c0c1c0ea05404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 594350854 1250 594349604 594349607
    0xb190b090c0409060806070f120e03030411030f0316060e070e1306140402030d1413090f0c050c06160207091d011d1b120a0c0e070e01090b09010207030c06 68
    0x2003080c010f4180c2d29142c40300001d8504c800048150085400c1c0d1512040d40400050855203401c1401d946221507071944076001d41a801040110b12590140500103942c4580743c003054280301564546d1002d0781e00a012180c814250700300c2000d06190300c10350000f507203410840002c0c10492203921100c802c46008080024203002d030400c141500d840f0b06010020440201603034002d040c015140a074256000020080846000d80c7e4054142c161030301a00e030503e005003e110101c106950895210300741c585070f440c40e03a210a80101d0442c560039041040c1071807698071901d07a441a00905500c0020500c960145055000b4080b003806000680300a21158601941d800d96400c00214044210b6180850301c484109001e140900b204541d40050a5883e13241e560320b03241d030346010109a234807614010b840710300104200421200c00744a0340442400c10301d000e5443d5503107203000f032944060160b101651074690f03900c490000c05403009400b01c2ca464130110340040380b4105a0ba00300400700d1500d00303c04907840b07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 594352104 1250 594350854 594350857
    0x3060112050c011403010501180f081609090201051c090f110f0102160603020a030b060c06060a090e0601030f0809040608060108100608030f03130c03030c110303070b190b090c 77
    0x214007510072180c00300b0042c001103a120716042c004002410003480180000d40c0303c2d5008000c400b00c01e03544001c5442e00c840c1080d4080c0140d501000d8154808601e000c0704101902501000740050308040020004640010340741d48074143c0b43c00d60769a000f24003103000980303d42c00701c0c0030543c000c040b458901c1003500e0b0000941080c41c5015116601041d0448420361000030324009c040c0156402c243c02c030345040000d8019400076a411410f0603143e01303840d80f0319141c50780030b0b0010144034401004541010801d1262864154011034020340c2001c00030a02410300080e03282c11a58000d00c1122400c200d414005a0b85c040c5006199000b42014000101a4400100c05060301d85183c195845c110703005105004440700c510400245820604c2a0f40010752200040c640c002100c0c2c4100360340030b0301c9589140d03149031250012400b080c100710442042c081460211151081c00b47c004500d080250303200c00c800300600400003644400e15801b68480e10784141c000c40c06c08007014000032044d040442007805107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 594353354 1250 594352104 594352139
    0x2040e01080f0a11030a02130501060e06070c1a12040c0501090503010c12050403172e030201020a0b0a1d06060909010c0f0507060219030b150a050a050c0a02030601 72
    0xa106420010418007004101541d0103002c0c000245601c800542d520003020b0301d600805035041c081e42071400d000d40c854462060081d04005400034146d8100180a080605040541b0340210b4050200784009410140792200340ca064142e100c0e440c5100700d1a03000d0620810103001c5071a1000c0b400d110800c21110490004d980d803d80360100c94036141c07824542229140c2d0089400100301150000000940f07500280c1c01c24000e02c1c2c0070310240e0344c024441b060a181501d0300e212001441070601c03c0282e120880c004881070180b511006030b441c540000390340303440c2d400c0d003e8a03821580005c9008003546500242107142110907541c1910f020900c0d950715010126030a80c003400410001400d1001c062041d06c0c0e400740e0729100c146c100c09080d0021243c2e0781011204035a01a0f08116600700022a1810001440c000d03903000301d12294104d041c001ca845000074506100b007414003070300380d1154201007910031102051402948920750080309500d40011008040e4050080c1e02c0040782516540140054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 594354604 1250 594353354 594353369
    0x62209090303140606090607020603060a0302041e060f15050c07090e0a0c14090c0c2b170f0604020a0507080307051b0c1f0201020c0d081605040e0c0a021207060204 72
    0x440c0d1354442030080b103100c0c0c00a8541d01c030400700018001450140040d40d0050300140408030419140d6021408440204014400c1c020021711801d040200d58003924014202d4104181703861464a901840008580c1d4440700034401c011980d007007284000c0124100030030034202d0902107a23050008051300c0e14844582910340810410f40480c4844005011150741003002c2c1c020400340d903e4910015061f04500080e00850280248030041800e40320040950301d00815013044403031032006809441211103100101d22040104c04214840c10302101096104e001640c0c013503610b01510908489920071110b00401001c00401070200d846d61100140c1908071140c07143d81c0700901102724036555200c01610403507112039102a500003500c0700c0642921240200d0002505120721415038506000000e40078100082000c000c118105024403014014100d6500f00303e0714150800301c038540c00402c0201070f10001c0c00e0024004144a00c05c1003071800c0301100e07003a001e40341c6080d4a4003034040d42c46071042d645c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 594355854 1250 594354604 594354641
    0x609080c060408030a080c120901020d0507020d020c15070c0f140d0b06010e01050f03074b05120702010506040c110607080a0b040603030e03061005062209090303 71
    0x1103260400e10308641c1030b00d8402c0020f600703041e4a5841194030380802891190800b506119680e24405404051030080e4501000945c80f03402036401202203800080c200c4c07085600017840440416000f1411001001c0d0684244440c402c0060b0080305130b21030510000c0410001c45800140080340c04441000d83c0c8510140e04006071034102009902031000c00090401444580030810b158040c0004808402c0181482030a02c0ca80603400c1d200ca0b001220660701240401c1d04401d40c4140b1441c0350014600c03441c52201e60207804110518200e00040700094403021544510b00c01603000e00242c1e0f207406040340d450303441841c041c2c02c024040c1c581030351864021800d048260a205e8007a401c014452400300d801403215940305d001c2100c2007200070300090701c40780da1540700344002d031618041c60014600980311032a52001c201d090501c0c10400030014182400d180d40240f02c1a0b0350070381141c045205d405240740c5441503d258501445e00640c2c0300302400c03454900d81400b05601034201001466106c550503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 594357104 1250 594355854 594355873
    0x1b080705010b03073c06110c0603160c060b06030717010b07110d111c1416230d0b040506070801060f0309060906021303020a08010c05030c0904090c060908 68
    0x103a8030b000340c1c000c800604424175101d0000610b843e00d08014094001c109090b0900c00030380402804c81c0ca5085500010381e011060130582c4410001c8140383d120503036500785180f40580d9022400d207c0038880800b001900007251050000b40d41090091002c018100c5680e4280300c0009003802040250403100b1394010700c00020b00074041e105480d1100d4010742c810421108a02c10420b14094503079044803010b1b0707028074840c21a2529151885240300070f10701281e4200c005d04180780c8850200198400650000d08594485508002803904071380880d4564001c0d5441c8410081146d204071035240e4001040605e90000d01641c00d41b980d006d06e008201350b40068445400448141409001c0c12000c034110555045070944aa40410b41503405814001140d0714580e860200342c1c2c4c40320105020312403404405009600e4503114200081601324020044d051604002404901008012000030480898017407890340700c5030852519244d000380782540b01034480b9005440141140141d24043c840c80254 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 594358354 1250 594357104 594357109
    0x307150917072301020a020d1a07020f102003040314030f04060b510405030f0303010e04020913051f050112030c061505090a02041805010302130506011b080705010b 72
    0x741042400180c0c01b41000c090307981c00340701a6444007a070031145151110300390640221814203060182c43c856015000a0300044451450b01c41c0500c09001402d16200502c0c2245000d04044035001e1741c0642d107241c5960b980d0034240c0d09081640004036000400004005a280100d48414826441030340c2c1004004082d500340951200105159040e443d4690a03100e0003541213454900451120303625040f80102000781b010006004442000e0764000110301404207150900c0110440743d030a070011030440d0301d880c4146060394000791002c2d0050100c0d00224103411503003000c4031010790b0804100c031b40130314911010b44001041c11410f00704c003510300317030011581e840103403030061000d074042e07455800c00152611000d0007006a40c0301a41d0300c2e90045000540c0703840e0000ea503849840340380c00c01a15145004145107007203100030019548180342c500140016a903001e90383c03c100b6807001001030a0758808005a600481e0f001041140e40c44001c3c030f480c2001030340d8008000841c450780080c401c8843c1e446c01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 594359604 1250 594358354 594358409
    0x71e18181515050d2d14070e090304090216021503040209091207061e0c020604050f0102121503010f060f1806050d020105031e0106080103120806030715091707 70
    0x3d071542c040494241c0c10040341c11550b4500446150b0600041d03a112503402c12400c0c0d1213203513400c5882c4103005080001050062020000038400c40b42c040351240b9201481a489101c0c900400c16950790106100e500030340101c580342c00d416030183c10119090305101242c0c142c0d80084030120301c901c1c8888000741c50160007255101905408805250400c5803030307950350018103003c1c806420181040412190502c82c14001c106010710302c1c1d009030059082c542030a500341040390001d03c1f216070040003604c0c4c9240b88580300c02e5100040500d0441c2100c2082c0020b805401001c0b400d81d07420382088004a000e42409550008071000c4820840802411038180400e48000d8403540750310201000b00305000d5400b60b00110f5100c50403a500d231070303800401c04001107070303000a800c050300050550b030042c0204180030b00b0785808a609802c204415241c0b10300083e0b610b880c1e50080c07190140c00304030444105d0b4058078900f406000c0c00303031000c0e810422221201d950ba081301d1040c2240302112005014a400c1c0201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594360854 1250 594359604 594359609
    0x905180f0319030b0603040c0e0906060a140102011d01020912010e0607030e0a050d08040309091407050c030d05040807020a0f03080d02130b0d0e071e18181515 70
    0x1440c2400c039680b407041c1c0819140c0d01e650040c1600c4042c00e0502d0394600000b18801c3d485044046d000b50705040344028505c4004102e118103030300078414801c20742d0b81c0d00354860444090b80d5002010400180040f805009480f510003e48843c0c0c006a004a003019006014090029102044482c1c2000e50541c00d950402c40588001d0300140042500c0d1803081d04154034020300c0804032000700c0300954510b403818002481c4040021340c150305200030541c1c45050040205500303079023400181054164030b02c8a50f0040d00a905110300000c880c40c1d1700b04103005849103282044000c1009160070700740410f5641c0111401c9100742c504000c08207031020300c08110320950780c00c03002c4c0500701252115028025400420043c1011151300c0000610064a00c01080c0c0c58820101c04a0f4880304020020f240400540141c0400c40c0c0c400c005511004c1d46101c0d020854100301c100880c5444d0303d401f0300c0014411032100115240c0c20034040b209001e1074440201003000c088104202032501040090120020750 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594362104 1250 594360854 594360883
    0x30e0c06130902031503060901020a090f0501020c120106080d08040501060b2706040b0d1d01020307170a180c03051501061202090a170d031a010c2003030301090518 72
    0x907003050110900070380c0510350007100303822200441d10001c40001c2c948941290501211b039000605640b5035503202c842e14000704248101c4801c51414400040d48400c4048151402540704401ca500110710035003090004282600a1340c0300307442503c2005002c10022a41958590b08050000a041005200b201e184050050a000e52101203102101000b03008201190380064148404600c1b0100c0d0b0009280c498440000041c0384031484034014041c001403220149264410700412a480d0b801c03c0300501c094a486503800640d594007902715000305007810140c0605540501e09104104010450344c0640b03000301d04413070031010344410320002c0d00024000da17000189030b020556201c1a1079000750020200c0102460038450300d441c290010181000f450140c03c0d4003480e00c10b1000c80c2c2511403580388a100c00b03c4a001e0300490000601203009030b903c0107000048000d540d0324980480000543c1404004095981d0b9503550910718010303041c240c642c0c000202c000b40082ca1401000640b02e150406803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594363354 1250 594362104 594362137
    0x27160e0d0f14010f020a0903021f0f050c1603030c030207091107030c031b060b191a090a17011b020d17100f1509061b1502070203010c030e0c06 63
    0x1181d49501c081c019441c2d040b801c07036484e030000d0320149446001421010600c1c0c1d503a44481451401080040303414200c545010b1a4400001c442556100c440c00b1919031040c28541e540e107503060341d8240743c0480429040f65003010007a001c0700309940f112150710510b009600b01c0398100c0e202d50a00341110700c60501030091420401042000034000c0152594490090a000d12103190241700000242c006100c2110b8855951703a10401620340512010141c1002600c4411900d05242c045042182c00e4443d00384c0892020904880036035034250048040d10044070f83c01c203200f2a210506001c0c040c0d01c6903050182e4210034020310001d2000038103e241c80e07520b60b20000a03d180c0a4000f11140f40030b001201c2c00315100002058901c41a9000d40090103684005c0c000c00c0c01d000001044a0080c0d0844020008001c070f4048840d034070302c01701c00d9480f07803c090a83c1e40c1103920380b80c1400a110b07501000b034255080078070b000e090030340550282800c0c01c0804c0039210b800500c0020880c542c480e9927965404d6980 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594364604 1250 594363354 594363383
    0x1202040306051f1809020d020306091005011e170a23070e040b18161e06020c0a14042901020c010e031009080d020f0a03060501140927160e0d 62
    0x4c0e84d08a500941c1c0042c0c00950340e28069004a42400d07011219141c540c2d10820301d20110140c50700c20701f8010f105556400c02c0d401000b241d020005901480f41c420f03800904040700348600707420b200340349030b003507205030004200c0410140c060310b48003804240701e480d0302034504000b400381001c0e08954802c603802101c041f0303180d48003822003080c0d0f00f000c0c000301241c1c4180801048042900341d030071409010508848000c030b1900c1030320440b001c20305030010b008640119580740055111008004141e03590b0221031600301c6005004200249605610140c0c07a100900e0750a81d40e10603141a20601030082e800e941e005414a0300560382203002004141d0545e00c60700c0402c040c1002079002e2100248980000e91030180380c6d41c4143c050740c11280170420001400a02120302c02c1e01741c400e07080141000c0c08d02a030540090034049055004103101a8018005118050a803520081100b41080c00042c0c070425181041104124141c2c186200d010228400e00c0c00c1480a00d001c003611982030b98000d003065000c80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594365854 1250 594364604 594364649
    0x3010303050d06080111120105040c0806060a02030c0d090503010e012a120507080618010f0b25030801061205090d0302250302060415051509071202040306051f 70
    0x80c840c0c018110403d98802010075034150078094080002e030408215034640d45410850301c03a609041e885548074900d88540038122580199170345d070740400e0480d83d1603150203103020103034258410000e210100740120141603039002e0304114581c050b07900030b074002c02031003030207403081401c8400700104440480c08404094a548682680804807202e161400c420907072901c131862400d840065501e40e020074200c200f0044c080c1803a44440c80803043d041c80e0000903503d055100c404405030350041c031080b5a400100781d210910b80000103c09200c510320b45002c0c00d002810000c0945900380204d40001c0e1880059031106005c03402403c2c001c894120103001052001d001c141c009502031104002d035a003503010310300100e40c854a000030707841d8000d03006885141341034981040f00c108507080150350507260505010214460300800e05124105a030707115000d4482d503a0603910350340b003000e640340d40c00d00010b004401c000d0650000d502a0100100c0c003031070b031758296030090450b4206006a00c07000c0c20701c0c4404a00d89 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594367104 1250 594365854 594365857
    0x5010f092711010314010f1a0307140d180507180204051e0a1e180515013e0c06040b0304030e04021903050402030f1b01050c1005070c20060301030305 66
    0x102c141070000f500041c9880322400c840d0700740d01c030902085010b0010848120110903000c0d1900090304920328502d485c0ca4050035440e08840c10344000480825130074000c848680c80928010402c492400619016203007480c0d03112040d004101503480c00c81200844c5180e079000b603c1c240d9900a00300c1070300410300380342e14007000b005050550303016480d820009500d0741c81200b605103400c208032a10b81c8180c1040c01c8103041c85081c401c1024458500401c0002042040c62020312042003440c4c13950b95029540341d0041e030300e41c0c05041d024851441c8000c8e0b141c010f000324000103840c036600c000e40d620741400c80100f0207039004510030303013100708410400500040d10030304c0e030034034481002403005080c9500006140084a618000791000c0b030703961024030040d0328082100124101c1010018001074190004001010740031110741814080302142d0000c4c0c0340e200384890f031144015220108098034000300c006200d030a40c1e00d000d4441c403650f25408091100801418001d40c0c00c080e01052441e486d41da0101e602d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594368354 1250 594367104 594367133
    0x20a05100f050d021605030d0c0903021e040b0603091b0609010f081008010f09020306061f0c2301060312090e130614190e010902090408070309080105010f0927 70
    0x1882c0d08200710f121020240740909560340c01b0b03030011501c03280d101c403819040b161880041014008100c1c0e0420050785c6611000710042035a103034420420320782c2c3d8041005402c0b10030b40c041c0e002c0d40200421030907603400106001401c8440707640c118031480100600c0050b1055a195500140340c46203414101e50054081a402840c540c8018001980e203a50940c01c540303128940000d029101c0000105510b4200012030700a80c04513000e050000c000704149401c2c1e50504040300c18451080102400d00000d0a519030000950136802005928201d44050003000e41d80030803a1003e00803041500c10900c1003044c442518100c40c00c010040d00c61180041c07401e0305003041111256181c509245400c54400c1d1518095008552146000b00c104d11126003034a80c42411020b9030b03890403480f0b10144c0e40b0114a60b40041e048460144d86d9011400c007202c8181240e04440c1c1d0303641c2004e000244000c54558824101c410320001040072425941c5c05d0351035041034601035881c0d0b2008904440c081104408880f00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594369604 1250 594368354 594368377
    0x114041433180708070608250e0105040b030a05060301110f0307080421020601180c050301031506080706051e12060906041e021308010203010b1209150112020a05100f05 74
    0x480b050242c0c1a91902c1d5054120030101c0e0010f00d01000110f0f006018150003001044450b00c0b220f0305180c0c010310304040c1040340700800c42005171407601030340a44100d42c042c0c0308080c4603e5523840c1034852500034000548910b0300039071030900300d0403245031410143c444c14410703a400d280c03440d00c45d0481100c9503100903105456502d4641c41c2c100000c00580c2034181e01c1c0c2e45503000350210f98940500c04800e564031020709901c8504000300c2101e03295209049905580e800b41102c41c440207065400402071080b600000524420a90041340b41d940003005024840c01ca01019030f0031401540b40d540c00c5008052410643d03500403c0440d1241c605100f825910003c054030001d40c8060142444449c0018002c0160103030364005034a400100ba80d91800d005001c0580007540b940d458040c4000301d901c80d88000309108113458010494140050000c0341d5105480d041031031030f03541c40e00800c0d20203480c8404100c0c490106a640052141051548180501c0d00c50f100d01704449100a07095801d54400c009144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594370854 1250 594369604 594369631
    0xf06040305071b090c260105030a060e07080f06011e0e04020105070609061508070e100b030703020405040908031e150402070c120c15031a060702030114041433 70
    0x130790300c41611660444203040d0791000300102c401902c0c404400425043c1942d070002c5a07005024645002401d42241e60348900300280262078070140600f445e0041d005162240914100c04400d402c00113481c9050f1155890301324250305100e001440d03040014402c4a00d6184004001401756000b40d024004003401000c000c1600340d01d03547c41008035030b4514081052130b8109003080c0100c4100300181030140403018200341007400e100780c65004008040c07241c610040e50000c006000c091098041d20020080500281701004240c50300005035042258040b01103102d030a441d5455a00312890039001e10710500d40c0842291a0b0820300c0040c0d8420310007940d0f00b030505d1a0028080484484ca60303541c03806414500c0c5000d0800500c000c0400240144004141c201854000f000e40d078103214043d001d800701c0340c8503550702003440802c0c05840c002c10190b01c0414403408100c180030040040081040042d0b054bd00e0007214401848944c0000c007128401e1f10001c101d00c6184405c2030015150001c08807503048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594372104 1250 594370854 594370859
    0x705033408131403130e06131d010207080d05090109030c060b060903070803040e090a2114190e010c081c02040b0c010c0806010305060d0f03050f040f05030f06040305071b 75
    0x302c910100c00d501c583c0760348009200556092402036078005824000514041414804000b844800c280344074044c0c000e40d00c0341c0c60043d1f044095940c040c90710b0a14000c0d9203c2459081160307154020503202c0c0c80c0a07040000217101eaa4041c4240300e5802c1c0d140c0c8070300c40399607a075480d000002c0c124441c100e90410020054100a658100034410092150000556483c0d05105103c0d0000f08041c010707c0d525800100228000340c071152030344030700040300b507684c4100c508081d00c01c80e03090b1010031403001c00a900066448402041003100c1c815198251229800e1100700c10044954600c0010b0241c9010014860300888098042d002801c00030201c03005801e0a0f1900b00381d49003603000d212802130340c0e0365450703000000b1a006411554888000d080401c220302d4810080381c81c24000f000020403610740b1400800800d070141e03084d610602c010100f080d45503901c0e014010041c0c005030249038401c4c401c4032000368814800085851140d5410f68559003042c4030b40c0d44500058405801c2244c1903600260007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594373354 1250 594372104 594372113
    0x50a03180203062e030b1006180e1905160915140705010e07300b06370603060e06060412030c0b150907020c011b06090b070503340813 59
    0x300d406180600580c90090421003490b1800340c7c2250312170018882c0040860311001000e6640d102264a80c914801c019034035010070340b03841052405010151841d100900052000010a28802a2058840c19612a1154000c180e41c580c1414103a0004500200e051a1400003402070f280b103a1064002050910760f405e0f0140c20542c503500700e1080101e0403d54035030242003080d00440011a41c0507510010003080e00c0e4004450001002d15008440d209071805410207018244c90412403032040f02c01d4144211010f291001c60603110b40030011b410b1031030218a00c8020076010f4028000100554541460400815400a6407240942c11b0000c1548a0f1021568001c41e2602ca8141e06032070032030414251041203007044002d80003000315408201c021031a030b600240c201c4134052140b100081d2404207868a0005480d0006000300448001c00c18400b2498029010f0b60251f980d012114000803000300307410410740444240021002c20940320400c40034013607100f00340c00070368550b03996600044a40b01c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594374604 1250 594373354 594373441
    0x606041406040f15120207030212070219150e0613050d02270406110a0e04050a09200901150503010e0c0409020c07030c0b0708030c0a021903050a0318020306 69
    0x8618405200c4d00700706605076030f0099031070040d00c10010013103040600d82c1e2802540e038041060151754490300052800c0940da01c10164000104c84030300a002101d80701c1d0180c81d25031130b0007841c0c10041112101880b00c6403908501741c40d011510808a02c6060b40341c0001c2004101c140c09041e40c00802440c2c4a1115a16400d030610a0420065442416051614000c41220406800d50bc4004000d011081c0e40340d91100c01c1c90802d0504031004901170f240c05a0071300084c08242c1c002042032000410740e9038442d12403842d101c4410030840344280d160383c2e07030110306404044004102d00050130420043c44501c1039444500e82003054030300c1c61410300d91188070030822a071215a074001c066015410030000c0000c0c9160f01c00140032141c50041c02c0a042d07035104001c60001404c081c5540f500407407000c203404e100f0803008072454002c0c4040005100c46060240075948100d814100190514041c215051007203540407000c1075000e0014141c075507034509000765011880c41030341203a000c0c5101c0e003c80c8103010301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594375854 1250 594374604 594374609
    0x40b03031303020310060602030a0809190c0f0510050a050a0309020a0e041407080a2415080601090912030504030309080a020f0609060c0901050309070315020909070201050606041406040f 82
    0x1461064250f0040500e80380b0920504821141052002e0180580c040141c07074803070344241014259030312207581e441d007001e4050308206080700d0b030081020103015150041b40100e5040c08492011940c40300d007031256402100c6010b0000c141d0402103903003080d100307000800c60200b0514000800204950004440101540c010402001944240030a12140c0c0380528440a2100001c0000502c0c01221907292500300300064107002445400903a07580d8401ca40b500b42000c54401001280e8009540300002d45e528000c2d00c4491003840004154040180300d40c1a650380c00452014045203c100201c5c00307848010002c40c08c141d110308a4000092001002d041e00c0d0b1140d8014180c0860480445850084001e0164600354460420b0200000c05c0504440800b5000e203020b560701d0752011b4a091403c5995030000300016150f88015420320b04a03409402441ca04641d10703120341d11608801c03030a8071020380e903ca0740080c0c01c2104200303d41007a8540001c1c100041c180d2410950364044540441030f582c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594377104 1250 594375854 594375877
    0x1050106030609050a06050a1202060d0f02070c1203020307062706021b1501170312010f030213021e0901030b04110a08130f03120b040903030903080c1e030402040b0303 74
    0x80400f03021042c2c1a0081c03590003880c1d40020402c0c14a00000941d0040c91445126110100404284c0564555000300d980e4800580c42c180500c0c0310b00c84201c0f00a6020460a6400d1280d503540803492034984034403001c0d000c0c1c15038011410684d040e141d4a00504c50710050080b0306030105801d401c01c82c0540080c00d10280140c20058450001c040103260300b406689a01c18240c101c261140d01c100d004c4207100e0706503281d5110103042e03400381100c10b614501c980182d42008031089000002e131204c0451041c1d080d640300b13440da50351520851940304103074007a0031409448107050b060100006d4a90030050105480145401b291a070780c403c0200b0b007110814800300e240340000040400000d80c210b05a141c000ca00072036954600311540d290700110a1280d8401400c010610000c8504807a180d08810500f150040c02000560760a180107001440c0a00084000c961000300084030b258810040e40c03070509021f44107030008a4614000822907100034801c0b68000c1e41c0781c0b003084c080d0301c00b00060241c01016 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594378354 1250 594377104 594377111
    0x120a0504180c0306051c080307110609060105310b01030605100302270d0b0702120406020319020c0f0d020607061d01110703122d151502060f0709080105010603 70
    0x10b4800101641c81c07940045000300104518644042400b01128004e1074021416a8680d190500e00303c07a060a10200700000313100e040244036050744003041c028100c80044488800c042c4081d088902d4940000c1103c201d04c0c00032240b1441411201e400a400d005814900001d445403201c0c0001c2a03444108801070000303070302203413072a607805c1030041056180c1c1c0c2d42c2c3c0030b003040c2c514a040000c0420210b030a00510404c001c1c0d0102d82860700800494800c4944109560344645e00c0d40b40c02540c0b504880390f21043e14a44004651015002141500c03d4100140101d143c00b4000000d1150951002000300e030440f00030007442005c2840d074802c108011000e80c2c0070320240071108442c50f003503542108030329104c4841005810000b94101c14182c2c00c443d0345490104a418401990204550307480c507007280407803811509103104000301c0c0d000f91840c1300e19a5646501a8443c10b5854652900c0c5914a016034002c10100f928038007250116030348040c07140340880120b500d0304a40d5094440a03070244010988 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594379604 1250 594378354 594378371
    0xa020a03090e10260709020712030e0c010c0312061502160e15061b010209010f020f0a260d0f060b0304050703030807270303020d020708120a050418 65
    0x5010420200410b41e0507810122400d264181d59080d0041d4401e11002400e60340c681034078440800a4101c00c14061340980794425540c440840103948000c1d0301319280082c2040318461603020380320300364008201000416802c1280c8005492480d6410003e40920034000d1010344010014010780700a000b8650740204400c0102002038a0301d0740c002000740c480d4100c2003091001101c0c0345a12940b00c42c42020100c0d071880148003040d9548110340180d0b0a040d1002e440c0d00040c14150000c180041017039036112104001c00710f00700d0b00ca201c90750701c1031426081141214049010841e03882840750700d1101706491452041c005000741d42c04584400b5090391100380c40c15401c582445080001c0511800d014036601e09a910b05844071864003000301803001101c04220945d100b00c078400d201e908140081c0c0c58403201d14041540980c00e0784000ca0040c800d4000c141d502074400b0a41008940101c80240000000d01d45a06030782d81041c0f203c0800c108040c8000580c115400410b50301000c4d1f13802c0700059060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594380854 1250 594379604 594379607
    0x30c1b01030c02060c1909150309050d020c060306240403151107331d0c030a0804030b0417030106050903060a150e06060408010231030209010e06150a020a03 69
    0x2e0b032508018080d50018010804801121422507264009031007004902c040d040105458505080d040a01d403030803680c1d03d120320160564440090720340200c4c21102c1c1500c140404a9840f06001803c1d60000c0d0288082540c60900d80c003040c014800b6a0294011304030074001104264009038025101c440d8480c0300d04a014126225a0039040300c0403002d80d260070034946407400303101450344034000070b9526403290045960028854102030165290701b41700166002c601c0d45200681d0103400c601e10700a0058048a5213000102c900510b03601080490415240d03440d944016200208261030420f0b21065155480b1640390040d8040c1c0340584400b51601c4c001c006040c50848000c0103049039a14000071801c40c030482c060680c4c22540c203202c500c4060742da138102060300350207564003100c829800821114805058148403000c2070701c501c2c41000c8a541000c102e018a00703100c1c031010750003000c0d45006210413041503034000e62280b80905221403c258070100044141c2c001c205100c016080381140c0030030103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594382104 1250 594380854 594380861
    0x1914100c0819150b07060b030f0a030e19211b03050607020c03071a070203030406080f07030207110127031b080303010e2d070305060f061204060c02030c1b0103 70
    0xc054070b110401004403e0045940c40c0344003406068220a000700b00d44040208580003d00300140107804d0310f01c00c00c4410011a5500d034610300441c08201042032040507410190425641400791042c0881c50500d40040b03200040550001c80010000001c55100454100d6000007003540042e816000c50030b180d818014104607001d0481c0c000c540112400f0480c982e40020000103a40903c3c101c4032500705541c40d501e09034031450340c1c003e400d808040340024070203401c004c003948140f101d000c600e1466074499078120100d110f030340e0004119442ea4444d080d1075500c00c49a0808002c0d1222561042c1d038400b45440300d04040a910450b401c10f00c101080300000c031400700100050140000450543d414990440c14403d4000c203022003008680401c08442200c1b001c400081c0d00c014160613045041002008011340000c175940d0380a141840c0304030825080800845031403024050305010142c4540d5038003c0078103174000298086101c00d0240112100c4188a4130300041c84d032540c0310b03000d42452000541903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594383354 1250 594382104 594382141
    0xa06080303090c1315081b0102070825170601140d0320070e0702060105040513050d140903010e150a0905060112080f03090d111914100c08 61
    0x1190028070038011032a000294609040d00211503c650070404c044202004004000302202000d031050030010382c0c0c940129014448141c0c002001000043d505e005a0740c40f00d11707118015440c0c0c03100028280440d02168007040c10300d400060040c07560383d5100e900c0300052508015034a0350704580010000101446551610a00e095138040c1c114078142d18080c084001e00c1c1c201000e66550f072a40c0c40d400c11000c0c820400a01101c0c990007031130f0b007844200295213400034001d403802540ba00022814080d860002c4074000740d8040010b0220100380102100d01041035808040900700a001c0204596028050942000030090040039043c180c0381d6107452114010f818500c03c2d80c5000089404980c01040355070540740c1e01c1894407a6070300e40d89001806481143c1321a240780030040f0605c102d40d400131448110b0107016564140f00b1140005000e0307201d42102417482034268510100c42d00040d04080c103000703400065003d0718119442242030200361000d41020b480002d00f48010013085242e1074000241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594384604 1250 594383354 594383369
    0xe0102010f0b011d060405040207050703260f18120a1106040e01030212120403030309050f010c1d06130f0509090a050604230a03180611030306060a020f12030a06 71
    0xb803a500c4600180000d20345940400c0340c01031502c0401500d0301c5070821600142405441103540300704509007591a90854081112942c42d0700c0403400035a0000229440040003134900c0c1031600f4601d16400555600c2402c4022a030703c022003190007169a0300d4107244108148102170308100510f4640f441c0b24048520a030341c030502d4203200c14001c100d44c0c401e140b41500c0d81a10f044a110200c49426440d1080b400402c3c80d9240780041c2c0401055070540103286020711540c1101c0300d02411070b601d01d098640b00c000c21000500e0290310940e0200c060b801e113020617000a00440d180c030100914207100341c0e405404c10000500d201500300004c0c2060a40c0c7c6902c00031540191a070003150b550340c40e80b40c2201600241c1252442c401c00000520441d00d40c1403403c401c10121070034440141f6028001604c141c0140c2c215142040001800c1801981440300c85034091b4003451855442c2403c0003080d40200d810750b03046100d1480850b101d90004c02000303414a90381500c075601c0380f81c80b401c0902640d205400115 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594385854 1250 594384604 594384611
    0x90c030109110c03090409081213060509030c1b0604032306061f0309021f0f110a050a0f0507030b10050f0f01021e0c04141012020a0605031f060e0102010f 68
    0x483c1c02000c01580c0400508640c041020350344ca040c2922103000f030b04501c1c0300c80100d05051003001086d081e401192030740304400501c102c0e6074001000c0e441e801840d0b40384841c0d400c028400c5400c1a982c04920522103001401c00b4180768032601c0c1e03420710040720006d00e0102d402900e0242d001c03c00400c40294812000c80302c0310605400b00c01e01006800d0401c03c03030020305071035034500c0d001c5585800320321100c2056111100c030b070b06c058030340010980b6003145c030080c0104400600402d150780c0d0204d00d640c0d940b900880242141c803126514000110703004081170301c42e03000d8040c003c00001c9200c1c803050b0103220960160030702c0034101001c01004440d42d8000034402c00030f0f50001c008070390300410300c00034038a500d0220140700da002001690a019694044a40c02403a01032402c00c80c1e84d500100d64064104814440da0707050f1240300c6203005c01d40b4180c01950201000310b08100d1180300302c00070740d4440c41c000382040d2400700003020322b5011200c07504403401140c0800c080d5070310303564244581d489486101e403050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594387104 1250 594385854 594385867
    0x5030c0d030f050306010302070602070503090a0b0310051e04050f0405060a02040f0e1b0c1e0d0915090e0709060305090c011209110a090203041a070813030e090c03010911 75
    0x25005030b200d24008418001c0100000d038240e8001e50540341910f4000c4000d540c4c840d800d2500030385a5216401240c81152008804610740e6400030036031307203d48030469840901504180821031041264004024001014194006141c95500580d4003900c00c40e40c007030846003040e242c07042c200540104410781075481448100700001c00c1e103070040222600100344038070503250700406940b801e412004004c8400b60000d054210f5207030011382181011413400c052049403c01c9200c940c1c4901c1c42007201e40c0001d1405609214558041160034110383c503509001301d0040d941d0142c0100700380101e4008000c00c4003808100110703909070180329030200c034a002610702c10500e0000a0644130a0800300d9185d640d40369061804c20824080352441c03110018100ca121503a00c2841c00080d520442d4100c451002c84a05094000c5a200d10240034412a8032510382c165515083c402e10000c031050141c081102c0c030350348000151242d440c028010081280c47c11303038940c1810b19803400d40e0000c01c00308500c40b170708000e072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594388354 1250 594387104 594387107
    0x150703110a0c15020a0209010e10051e01031e0e1b1f051b01050a1b02030703021b0f040203070201050412020a2109080714010e0405151002010e0f0705030c0d03 70
    0x10f07200300705285040c000c1c501e20100e00d440302803a402500000d50000110b025016007105911800048407800b05035174544052000300d158050032070760070038454150b210b6558003a403c18064440940901400c2c940700040d031354142d96011141030a03c2d0044040d800d281180300035581100a0705440001034082020040c26040403021407600400c40301289600d4541c1c0c0400c41560148607003c020300143c10640d814000a010f01c01c890743c3c500041c4da40b0810f91f5400031095900e9240c06801400e0589504080725515001a58005a10a200e028910319690752440a107000b01c0c00c59000045519242c17614100c200034030324151042d58030100841001501d40c1155440030800c0c0700400c14a8000402e003521802c106c0c0d00501884c1c055000d010442c8181071403108038445003640c1e803941000e880c1c0140011a0002d40c2c1c4826010502500001c00d0304010300400e20b580554400040d800406c42000b034145820000c08040301d4000c40420001d51804101c60303103000008884110074503405650 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594389604 1250 594388354 594388373
    0x8010b03041401020d0c021c08071d010203071e0201120e070311030f06160801090c050706151509240503040b0406060b0a170a0c050414040b150703110a 67
    0x818181c590111140c0700ba0007901625594143d0400034000c11a01c404040e403a050b1040d103000c2e130314500007800004140303e013407000e00840e6503071101d140c0c07052a00314850421941842003410b510041000e500080c00300760035201800d2159a07010520740843c40010403426041740c00c1119141800c2c070085500c4400301d1508103c1c0d41c00f0090070500c1e02d40d131010a0420005007101241401084100002000800110f50207007144d49d9071401d40340c4e01c445540d0101c8060171580340c00103100344001e40020b195644103000042650221402c0d081d555840c00c0a02d000084840c00042e0000c442009130844030005400302200b44400059500684103008006000061010b401c450510000c10f007400419440b6034081d00d00da6100b5956070704050f0000d044480c03912400e0064401300c3c000500001003030b12802880180c540c0c0c8552806240c2004000301d402402c50700355000b079841c030110b14641d44001e0302da00e0200903941886d44801040c00c01420203090050f1244041e0441001c40d13000414450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594390854 1250 594389604 594389611
    0xf050403081b1c0225150c05120309120903010f060602010e0f01050105090c071b080a03080601110705060315120d020d140f0a0903060e0709060f050603040602030916030c03020103050708010b03 85
    0x6217042400d8804000d41d50620f401640a8805020754500c015541540009502d10082c050303000c95000902401d03031460140700031140410340303400c44941e41c407416250070003d2692540060020a120091007940740c03c80342e6079404040542c0d51030f0751040c281d080030309c028154090321400811844d03150002048400000a1205000910000d407400400c60f801c2c00c41f0490800e149030a03034280d0744a010807580c4103032a010940110700d220001900941c4552001c0700c3ca10f0480002d413024510303003024015642c0002d07000e0143c05984460030700060b1a21180c0b000c0002d0700c44018442403003086400307420a061140c06104002c000e00320395541600f0074044419581c08100b40c15600c501005045402c1c00140d04020101410000b102000500000f80d0006540403004100151a07803072280404110302c500c20b080d00400d00b80001800b04196038080c50380414640d00387c0b044041d040ac0140d0421025404c102e0390f2500000d001c0c429543c0c50721805234002c503d800c0c005810b5042000140345800000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594392104 1250 594390854 594390883
    0x902030d112a04050408040f0605031b0301061d0f0d030c02121507111006060c060b0301181b08060c04090e060c0403060504020d060e030406021c050a0f050403081b1c02 74
    0x49020a00704006e4600f100d0041c02d940454070b944030b440701c0d002042c0703501c00d540b91100340e01d06003135031003a450150046038100c0d40c0540b21010707000108207646e60b95002d110b00d0301d80c0c01610864840c03034070f403110311149038158401d80e96019484031030320410101d481c29a03015034250744034800c0b681c00228969042038003c0050704141c0d1003110340c6034190340341030442030100c0403407030800304000b078030300d8111560090062185800340708881c800c0c814507088411003c0384604141c100382d816404285d5003400c00f0100b04001c42891031080d00c0b04d080030300e01071003941d80c4011543c0c0013030708100b14461881062804061000600060700300300c035601b003441c0101d00000d44116941e1011a0440d40e610b20981c00c51540644180a1214004221911b81d001442144007600810b1441000c40c3c400c00843c07081020152940e604082030f0110403110594041000002d01004000100c04910903a02801d0b40d03a9052068a076101c00c502d81541c10040b80641c0701a0101c0000703032900d0480d4000ca803242550862 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594393354 1250 594392104 594392111
    0x30e1009061403060f01211802120a08040b0f090634020102100e0c131a040b1807090902070609290c0d060f030605090105070c0b13060902030d112a04 66
    0x6030604000b00488134447d82c0000c0b803414030900d41c0861130500607011180201c492410035000e5003030080c0c4400200e00001c4c00014100000d11045400c1000342c80116080e512032400c182c01c0b080800d405901480303400d40c8403035074400e01c0c080c4038043d0000d41840d566440c3e951030f40b070f142c40c3c0d0003c0e40d01e080c0344803170140554903900c0b0a0408003003009a1310b203040300180541d0103400a035514030002c14100381203100001c6441d90301035450409008205400c1d401030004007901003c11180d6007021f00182a02c81000221100010007040038005130007064000c00380012402e18610305020b4401c1c1e440690309582804e65900c440f0104080142c0f6840380d2020400c03503507552201000030003030203603070030400080440c8000070007801540d9101a04c6000d4610080007030745c444290a035062161105d0052000c0e01960002e04190b81070180303070a0b110722030b0a010413400101c2d80080d04040030440b1540014801d88600c0c0d8112030100041e866085154206d001e000d507a02801d24540d140c10050180650349 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594394604 1250 594393354 594393377
    0x60906031d060f07021b0f0f060c1e19030c0605040212070303080115110304031e06180c060503070207031b08010c091707140d030e1009061403060f01 66
    0x714050300919010780c20a0710b08038903009078965a0f0b060151103000051164009401038030701b40c401c00b052000c00c020074081e85140b50174104000300310031607040d035007150050080c880118005c0001c02c01603c10311002207d0700c00b00060603450015555890000f64141204244c00709070007141d20301e07102d03412810100f00355035a40003280d10302880d40c64090141c4141c68000003030661100c49181600c000307028140d05002d4404c1c0464120845003000705440e0401c002c01c100199060134006c940e0141220039001485654407228110f507a201500405035220310b80d15001c200c65101ca001c0038101a040c880e01314100392000a5a842c2c0c00c1c00700904d0742c1d404102607074902420b844107070020500d50000f40810b10343c0b80c0700280384045600c10321091070a10041c621500002081d41429074980b00308444014030108100a03051100480c20f070b081c800038408a0010343c940c40f0710214003449039282c4142e0030349032170700080c114001026031240c00c00d8140305219403951514103d84412000b407030640c03003922 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594395854 1250 594394604 594394631
    0x603060108060a030503030c07020109050306271204060302090405070819020c030c10090b1510030c05211905010806070309230a0b0603030c06061c06091b05060406090603 75
    0x3d07925000544213101c003004120150b5801001401614401e82c0c807007100710303954014140e6502050319519100c20050b88000c1807000048084122110060100d0f004260103002420740c903481074010000007500043d030780c241420580601038100d20185454000c130700d848282a08500b400d410100300c1541c00142c00d001c40b400800c10303100c1d01c031002010788012481e229802801004104412280a085c40000500300000b188070030901282c0501402e41760b0070801021401818004808000c1c8041403000c44280110742d480036250b00da1101000c41141440d181d2074071054242e5100c0210642841d0050010350000304580c1e42019940c10003042d030204900d04550b00c0070000741c0b81c903a8413908024052201100041e8456041c2c01502041915120002419128815801082c0941c1c5c030050100c1d1150405082c40b05452032180140f100201056030b84500f40c0304005016030748001840042d00c02d90003154910380017000129240c91601e490303c0c1c8040d14200a6210345024503655401485004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594397104 1250 594395854 594395869
    0x80910020c0c090f041b120206070c18060311030d050708070201030908030a05100b0304020904140c0409050601050307060302040510180e070f11010c170a02040b0c06160e060306010806 81
    0x42c000c02d40156841c0c000c0010840d07407400c035000d45000400d08040c402552840341c00c00192444460001400c2d1441d4090101a91018400f01c80c0400c207a040040e02202511007551801c24081c00800c0852960422400a002d0070103c01d210b03802c592407003094142c109045459050340f102840b500c4016a00041c0c0c010301e042100a0952030b0f00004124802c1d4040c0d12991007042d42c01d4004088907101c0000038100c3c00b0494009401010500c041000320b4a68040c048248a9407422240032044410208050710102d403000c5659520200051040f480d080c40364002404542c6002c604140c40d003400114100315110b4504140148041d2909070100e2204031080070302003d8000c0003850034452402002c840f03601c4184400500180d00002c40510103000342d051600d125503469491540f20001c0ca0080074010303110211487e0b003000005a444070345009090192842d0b4060000d40c9003505205042007004103c8a04201d1702103070342c2d68680c0e101380076a5005402841c00c0c160a9460102140c00c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594398354 1250 594397104 594397123
    0xd0509011407110d021b09090109080c0a020307170a031d0409030509030c0a0308040512030c01060806180a0317070c060905100b04020c0a0b070c0f03081006080910020c 74
    0x1030401e00c0100003165800028441100c0161404c440f10b81c01c0c0c4910403a20b1b030741081c00256030740d10980039250652400c00f124603003010301070300006041d0b42940e0350984154000704405020f80c104034191429482e0911070900140700c0c5050251409021811058540781a800020280130710303030502441b02142d1981c19854464082c0c0100a151070908000c4c0007508620304484c445d109101c822103060501300b5540080340e41c00340c103049c02e20f42080108002656a0261080244000d11007801c12071400d0044200801d1050090720150409583c0701d52804003100f0390301c4040e804000d10100180c0c0c00a486d44a2003072241500c03c82e80c60f040000c4071420031290014103d9030800521505202c400b00c1e0f20740c0c0d0504482e40401912030b00005003c268012940065840c6d0003480080c00031800044401d0b40c0b009240c078060000005035928002240700b0088150b0005407104200951a041e02d1030542c0640b4441c140700e40140345c44040c00341c0e100da45407640c0b040940c004c520000301d94400c0010208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594399604 1250 594398354 594398381
    0x3030a051806250203070c030201270306060302030f34080f010c02060702240a180302060a0b091317041a030a0c2316020d0605040303051b0d050901 65
    0xc41c14030304082c80f0400da008043c0310380b0030702d20607488107828000001c407403d607540000443c00680c90761300195155040242959440741c00c0c0c20124020a43c0118181702070b41c0304000c001622425401410700c1d101c1070b140b00c5080c075445034800b181032614a00740114082c030b000b410b07500c0c00c20f0388204040704407034035a00102181c800d10052444516040d0060700125000b0750840e81c550b516100102d03034a802005840c00407032100007414003d8510b41390803550007940035101041003504440c1011040c07250351000c0d80103030840000d200d031080e618040c0030103c41c1c0841c1d15005d0740c02c02103031120a102c10044e00500843c1c614001c0604c3c006408243c03401007401c031900c40d82a028110640356a648105e079080180d86c075240381d1203056806040f0f84c04901c051081e5030001e4060420398402c00707500c00040750110302c51140f00e0f440140c1e1540c50b414245481035601044a003001c4c07038040d050b540e001e080d041d4030901d03440254101144282c2a00e0b041603083c01c0c00f0665031950601203006040d40143c601d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594400854 1250 594399604 594399613
    0x1090803150a0b16030f0f050d021b0d050301030308150f0f130203130b0603010e19032a0b060f100e040b0904050f2407030e0c04090c150206010803030a0518 69
    0x1501d0303000078032080859000b501c6d12072803d900310704102c800344402c0190364007045040c090300001c030400f94081c02d001401e040010107400080100c06e49002d43c100300342400120004014010143d000e200e40d078009409044200e0421090f00001e080c01001921700340c0201094841000960345040c245001018404021035490414480441c04203424120680d00b4a01c0b200205030340e42014071034040003031401c40c0580285214103160800b1809040c006a007080207180e008807078044c04034044020b03140b003018031460001d00340c58802808040103000c28400c1c0c00d9a41c0301e0866403034494001c10200014501151001c0511300000c0052003900b4299400c48441c1d010001017000010ba01081d10780d02c40c0855041c1c010407010540d41c0c01da5101e2000f141c024101c08540c00e10300a070080c10340c1c0110203090b5220300c2d00c1440840c00b1a008803070181c81c034403805d08041041d111010054900b049292000c1d1411f507050031800e03542c0307100141002c8001c0c1e81c1c0340d00007a0652980748441030640c0b51041601c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594402104 1250 594400854 594400867
    0xb040501060503010c0215011205070306021206040b101d010516051e1603082a0c040b2b0203010204050d0812180d2304080312060301090803150a0b 65
    0x6900814160080e40c1c0298a0400701d078205600008010082c1202032140b040503a003440c0044040d140b000f081212070784101580400055100c1c006401c40b464100b44450b0546024400c00054942d9201800d00503219400040c810a600500040c1caa10840c0c00380b40c102d030034050040715113101c0d507400c441c48001548101b030f003007003c00700b003038200c008500644001c501400d89002c3d86235581c03445002e42101d202c1408100081c4c0802c041c020300c0740300040754862186003040203e00c2000300f010b640340580002000e0070961a01e80f1a8842000d01503689100c04160f282024160050f0507400c00900e004121a00007195400d40444018000140c08400801903503e001205034001080c0f0f8210500d00c80c002902500c440c3d014558550704142c02840c0c0c10300c0e51541513440c0c03c60300b405220010580c200d0400c1d81c64442c4007c00090540c000150364400312141c1c081c1c01d0341d0000d00390350300c26410003a440c00410b00000680380c0140c80c01004036010500c880004d0380419603136016903460100800c54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594403354 1250 594402104 594402113
    0x80304060e0c1026090a0b0406090b090606100807021207080918070801120c0e1527090601080a0201050c010f060303081f050108070f11120705071a04120f0b04 70
    0x850480d040e2003078803044c0c1c0d482c56072070a5440010031a42040c0300c1d8800050711002c90100407660f50401d000b1340300017600b2022910b5040040344103d41c800c0c1c1e1684402e00740845070030000014420142285011041820b100c0300c001e440360074042180003603c0001c02c0c40c00510000c1d5048501e0144002c003124030596240c0c1022540850481e03540d40481e15031400012000d40c00116100d060740d000506040090400481494408000d412035140542d0040351900303d80b180c00c40c24108180c40101840d2107011050304a2004500520109064114800400192000207001031440f40e090038210380b618061941640182038200380c9450003801e00100005050300030700340502803c21569140c010307a941c080d030604908014856640014188000250034511aa86042418400c2d00d807502c443c640134a2083d01d401c082d0178030035003807060004200041190801001000f0200d121741841d40505840d03140d001800b40c0e1088500d1405007a0800c0200700080c850002c210b5841000900c907403c0c176080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594404604 1250 594403354 594403367
    0xf160c230d09080705182805011e1a030c0d060b0a0f080432030d2a0203030606130905190b0402040f0918080309010c0801050d080304060e0c10 63
    0x1c81101003084014089001000403c1e040107039000a0103030319000112005420381c01300000c0805000c1c00220b02c400351a8200c45080c1d032511460320b8404225075051080b0f2a8403090034074410080b680d200c0404100000c00c1d480c1300032031301e000765900c0b648a40c0c0311102e1075124800c5809043c03809141c400701040c0800500040c0c00f44015558800944030600c1d141510346007010745001e00b181540d50030009011500d1075021038443c401c03100141c00020b9001c240ca01c0c0d038100b081200100785e25221240180741194600d00c1804001080182c1c00201c0140040d4407840060201c83c01201d0014254140519080c2c2e00f03001464125810000307131500c0001c8481d10844400315551207824070702c041030207142038000d541c03c1d100c14951038450703030740303007194110050401c0494003403401094002e82000c01c002ca00076512036501c0c41d0011410075041600200f407450160082e80c46001e100d110500401e01c418243c1c1ea20a900c41e80010380d012400006c0c07483c000f411182c40b43c0c450174045600349815440b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594405854 1250 594404604 594404623
    0xb0a1b030603050d05040e061009150e090c0a170a0b0d05060f100f051207034b03050c0f06071205060609010507080706020904060b0903060f160c23 65
    0x509680e04e0380000a4220781c00d114034031440d04500d10003004203180745030010300c1c00220351550500d44030b0349640d440c0000d0581101000030000c00d507400c542c0f4826041170b1628a0307001c1c000c42e404a180103041c001c0a8203103104040794080c100140030014007061203a03803221072501d03401006480401c0741c0c0c0c58041d90721a021180f901c202802a800b095030704044c11614820740d00c440008290160801c0207201c079020665141405602c1a9440000801d1000241940c3c0d02c040400c00003451521701500c11420458800c2035550b00d070800103400c0e4370301c4881c0001c0021545854195943e140b40c1c003d480c949450700c600d020036070041c042801410785d0010f00315a0700000301c0c2d0080c0030550b281810850f480c041c2c049910b021500811107100025080c50080203480d201e0740005043c001204003240c21101d943d00000c2e420038000488050614080012540c48581c0c00401c031450b140420070b00b0320340350400340c4000c18080e40b0042c1c0790802048243d101c070380d00d920030040b1800460300c0340044e0b070312101c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594407104 1250 594405854 594405863
    0x90a050a0e0604110114070c06020a0212070807171c1e0e03030403140f0106030c09050c03151002010e0f160b040f0308032511070b04120b0a1b030603 66
    0x6003111401401c04140c0c14031440c0c20160303101c101a00740006458060400c10141e028140070080c5d2000210b07150810009400f00b0390047c0510800751040c0622044180340703040c02035004e09810415540c0001c2c0140954014507852058aa9aa07158601d007504c000d072545840c1840035000c030015540304080ca001040a02004500045050b0301598060039001c0002c0c1c1503082008103102044081c8080c9a03108003400880e410303c00000c2185085414680040711494040401040803005a0085540001c5854100c500d1420a0102810301c4800310440d14042d42c203140c0a04400b600070342c07050413401403503002d442c03d0078150a803080e02d42e051215604100d030345009000c141a00700c282520241c50001c1d00b4240154255141c503082d81c3c000070101c2c0700d981c0d629044200800746003180d8440074419a111030304e8281104003030b03d041c00c1c140c1e04a42d440801c00e0008004881c001c0000700c3d0b52030f40003140351150741c0b2500010b0010f8060300c0400a1608422202014460740c13542c405001c4a008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594408354 1250 594407104 594407111
    0x10507060219091502071203020f060405100501140d02190b0708090a09020a050d15030c03080d0f02090f0909010b040203040c09050f131b050a091d01060305071a09090a050a 76
    0x201c41004004c8003007590a0700c01684400f80c1030250140e000e014240303040c02801111030200f650300340f4501d040421201250983c01000e40c0ca4108001402100c0c090315515030344d644880e801d9804500c0d01038401d10301900c40c2000c0ba80000c0c0003651002c0c02d202404140070f48940d100b07111304129084d81d110b149114054000494001860142403080c1c1d110f5540715500c1900e40b1800a02d0100070300920b0310310b801c0f04c14600c2e03c00000164401103c0c2d004500c108840b0707131030f14003006200040f40c0780308443c5040e590040005240583e50004101d554030b1084880c890705444180e516801090729a071030a410520000601003032001d203281910403981343c40c8081c48951758804e407501c008074003030b01d4114066070b10041d620300092a9040f8484003070760041010076055980c1c4001001c00307000e03500c0047e00640d50141c0925040940104805130b60b800d4000340700310351942c3d64803552400184206a84411196140851555010201d900c0048010f0805c103880c01c0c1601d605000300000d88644240918 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594409604 1250 594408354 594408359
    0x1020705030c062b0903030b010825030e100f0204150203070312110d0504110103061d041103071a120105010314071b020a030c030c1a0904020901050706021909 70
    0x200007030507100d642c001070241410441c81c0036480052519682d48600c0c0300c242d40c08004104076841c03003240f41050082d60085005800e074400900000c0000c1c0c03100c07142c0e107003914034000b0b0210608a10080d000080c80d0024229110402181c24003425810302c201c003034141452407207140c000c0e8000c2c00507140070322402080b00305014001d0342d0342c1c810070200030040b446000075100301c004142d21880300d511050120a1521400d0706003082255411a4111188080c0f480350742c5195901d84100c03406882452a0700725900603480710384075109401840204618450220070245880600090380184a103c1c09411850340a141c140403d402110300c04030800c0c1000700018996109015100a00c1c80507a002c08041d120603600b00d40c03810044100013400010041d2001c010380b25508100000c5008904802005045140c5100c0b8000f0f03e900c8021040041d1420302c17007024880d0b00b21031071140700b1600142c0c2c654a0b540180d4460040c0c10f40600103a1000c1070040c148985070207146d030000c64580e40c0c0000b454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594410854 1250 594409604 594409609
    0x2404090e0604032703030f090e04031d220b01020705100201060305120f0a0f270f050306160c0f06060b09031236040504032604021c06090c0f030201020705 68
    0xc4c0d1100c07005190755183c000400101e8003407501404086041e1400300c0926407154810120072206490403800035281481c403035081801c107000c2d8840690219680840290300d101c4811100410200b0b1f0701c040c03695a58003001b00ea000304080d900400c0060301010803100c81c40d401900a100d11300c02591580134810960700001c0d1400101c450540400c023601741080c00a0034100e8100c02c0c03e20803801807020091a55010f00c18058000c429820f08002c580b01d06400c10340320006407811a4400d501a52017241400b82003401c68426010780b000e1481c0c084201c260724200b01c200000c1407800581660314025004c10f4804401c002005406000c2d4200e9119110720071005400d84036500e0582291405500e014182e18541d2464050b0403003805001480e01140400042c00c684003507500700e01017031450b20104503007103041807514005101d41c50448101c0c43c05030081807079405031070b1481184c0f00c96141d6200c10004a6809425000c1d080104100e40c1a01c60542c0420720b14240410382c0584500d88c00010b451 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594412104 1250 594410854 594410897
    0x501061202060d020309010b03030d0c26060913061e20180d1203021905120a1d0708160b18010807120e0106030209090c2404090e060403 60
    0x29540586400d20f09400c0744031010003500041c1c2410030035504c6800300d01c580e40d01040a040035050f400400a0140c6120350013402c0c807448800c408000308440d242c0500c0c0b01400d0102998011010303950030015036201055490802414240100380754034180d220b40030380a09581c08800c114103450b0400c07503071292079441c11541480343c454030100710080101481c00741c08403800351841080940520f04110b15603581e40704c50b616907141ca4000076804540b0241c2c02c4001041554296000c0c20300c1483d06003050101041482d00415141485071175070501e20403441451114007a035001482906d4a041d150b044403a254414500d0500d80d0410028004c155940390000315070709290720303080032012000170500540b42c5078002011002030148403411ba03207a074070844c0a003c0309000f50900005c0c11505610401c490300350050840c211b184e0000c5607e4150340c4401d6856542c5a140010480e001401800f80f110103104030f0b0452900607003030091041c65090005000350285200b5140c03110400420708040e0142c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594413354 1250 594412104 594412139
    0xa12230a020f041808071a0c04030c0b0f07020402070c0e0603150115020312010305150a02091c061808070204050a0903020a0803070210110304110f15030a060306050f04050106 77
    0x142a041c1140310324940f80d4403480007030700241135000050b1101e0305c44030f449410081046c2d80f11002d20540d51501116a0035069211001040d1142440e0030f54890300e0101c9050b0050f070082c248005900e640801d240c40c2610740c010342c018000d541e6110107140028406100c1e05c41d40640182e0320b804108185000300301e20a580d0207400380319141d60700c0c00440c0d51b00c80e060246001c00b580800c01c441c1040440546103240614003c00007400e02036044a0100c210540080100000620610514201e81d0314502c240d4a0000e4801c460000c000041c07c041004002034184550011010200381c010006120050705083c0d0007120204881e42c0c6c0c581408045c0c42d0307038450043c0160401200b000006c1d1850002d1500840c0c1407040b24901c2e8a42c010400848001c56201901408040200010483c02d01150004e5007816588081c50064207800b0031034600310708100041e01c4030048000b6a010205038400c00040d074100009004905100038051100c0a068406803040e500b440c0d004600716080400c3c0000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594414604 1250 594413354 594413359
    0x105030c0609040b060c0102160314091e12030c010f1a1c080904022b061a0c120a080f0f06030304090902011209030e01120e0304050607020a12230a02 66
    0x20b0122680100001442061000e03030f8000c1041c003954000d10024800781c4090126000440c2c6080514240a030526500203001444402d082205005940f1680a000850844801c0c1c0c100d449010000203940d0079032203200003109101c0819020040d410541020b014071a09502c204480000b00c190960007143d00b14504d50000d590010311114031558202c4401d4003401041100e0601c408800014266030020701d81d5801d20f11141d1070820300709211880c002d00c0d2080c0040800810346003404040c9400c682904000b0045008190b02c604030343c05000102c40c3c0c00f040c1d1401907564076000030250000e4001d817000e10710320b101000010400300c111036242e8001c0c00028019400c00b45401c551401800301c03150220704200d409052801c400c2040c0c001c0242c10744c07090f00e95203403c1ca100000106204009041405480c0c10891010090500801240c042d10307810f40d1465a101a20f0011805c00030059004420468000c4003a00500c44a51100c00322504501c81100c541c400301004544d031075101980c06035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594415854 1250 594414604 594414607
    0xe0f040e250f1d0402060f03010906030b0606030712110c0609012a080402190e090109020102010b01030213260f0d02070905070206190f0e0307020a05090112031116080102120105030c06 81
    0x41600c00c10f10042e944a0710007480140341807441c40c640c0805410030790000d0f800d03d072503400500820004c60003503a0301c0350302070707811500f5454284001858580300b40c5807070038036aa541d00302500f4080b42c0f0089480e0301d04003800322200c038101112001e008021354521101405618130701d5061500c6588082007402e00740e9a2150713001c0d282c9400b00845c9620703091030703140c605904443c0001d502445200300c3d4450005040002541c01c4940006801c1d9003c0048035070405104000f40c40001c0b07106d001440039170755424038055860302c560f812030011403049122441c1a100d40d50801e56031010015211261104540c02e950010342e40d800c4610a03150141c2e198000b50b0440400912444050000c1c0d813080000c040d40401d50041e9950000206c0300c03180764440302d40d08000350304006d6050001e400d5000300425501d9a0156140507940030028110400080401200c11b00030f9025070000c011442c4400c03407640000c000140d13141c00e854000e610000d28449201d00b21000028070303260204e4100d1580c04d0140600c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594417104 1250 594415854 594415889
    0x1031103121909050a0b0a090b03160509030138031204060e010e04020406090302120f03091c0227100e070c050109060f09050f030a0e0f040e250f 64
    0x2000440300c65031030b80801910660015650340d503991004004c02140c41a1036a54424400c018651003068128110200007003007400b10b001c00c00910a002030030140342c165154404580041d000d031124041100e548565201c140ca804000c141c104031582001d883c0b81400c420b5800103161319031480c03900b058080c0741c00740010820207000f030700804001a0140350066095201d900018220303003182d00624000f4074401d905000710b0030898422240c2610110082c0300b501400c4105503524403610301d005000c2c45103c12145141c1144011002c5030560061800c0e52900354441080326104a02c4540301d2550540f0000c10850744121400b001030b610a201d01c030200351b445240603900c000d207030340c0c08136070f81d42d82c1d082400045070032842107145c0030f0690740d03001c282c1c681903040c0340d46402d1441c030108600360410400a20099040715003241c00301d03c25201c2042510000740090000e00110413040458040c0301f41200d03052110140000c1004040c844100d0125103a4803070780c80c000711a00544e60000100e2005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594418354 1250 594417104 594417127
    0xa0b03150c070204050115030b0105070c050f06040306110d0c0302030f0433090201030c08012304060305030307021c030b0108040f080c070929090f060f15030103110312 74
    0x60390080200079400d1800340c166010600b2602c0990091003681c24900956503140d03891702956410341e400340383c03450914503180c0303c50390a400e95100d0948103e10503400880251544010385000f10f030049030410011082c43c44684240d130080d4042e82c040ca250903e1041c1560003442501c1c0a10811418240d09950310758405150344419074044881d2101071101074070711102d14203030700403840040002181910301c0348000b4040e03a91035000c002c00e1080d09401440340444000452112038080401e01d651907107500049801024607800c06022030000000700100c90303030009400b1640400c3c1c0781c1c3c3ca81220b003203103200b14202c1d00381c4503c05000450b07150100380840c00d80212010001d00034404c135460011000c6622b45449070710341c0a01005925101144804010380b5220074409801c90320b1000076540b050001640341000814000140d46158040340e402d441d007020001034840003420112241014400c82150764000344400c6400c240c1094442d40f19040100e11100741c512043c007081e04000711b81a5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594419604 1250 594418354 594418393
    0x1140c031209011b03141015030f150b070b0a110702010e0f090f010906230d0323091f0c02060a0c052a010e01090b1c150e0a0b03 57
    0xb03000c84542d2182019580c01c2c0700e640100d0f40d49252034900203400da00d1888880c120400c003c1c0301d01004403c09400704140d60007002001d0714880107140008110300420841c4008064048003002d99040320100071405c440104003c00354030303020303a0300e41405030b0f951a036030b1050755000240042410814069580154022a100488100010181221034802c4800710300c00b0b440407201c8080307104e403c100400c5100250721462028007489002d06c0c1240000d01408a43d0020004606002d59444c009510505209501c29515110003840215111040540c003520344d0300241d070100c2c403e5103002210245010700707410b801e2080350541c48082c02c100d084c0d003c01101c0d820a8080d1028410050f50810014009004048442118407803118540a62508440800081e88030302814000c01060402e40d41e0380007903004080718400e085243d0b5070703200740c00481d540040d41d15145004508058041c806d007a0f0307000e1004107491800880d80016542c81460100383e558021400390190044001040c601c001c409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594420854 1250 594419604 594419611
    0x9152c030d0f0909111903150b0901260901230103111c0602250b060918010615031107080d02090a170a1101020f06010b0c070f080c01140c0312 63
    0x1049035101d6500e030302000a4802c165450031801c5c0d0001444a0400c01c50f00c00411a982035260400c14120b01c8180a51544c2d054001c9241e21440400c640e6202da11034002481050005852b11440c0c03d01da03a07424101c9102034901e00d250354204254049010951032380300f00031625110b44c00003e0f9103551075480440d044d0a034030315040407401c64038a408405170544011a07070b1103508016507440b00301c208143c07481c1421751405143c1000f1045440803905002d000c90308840120780ca850f15460303107650401c1d001204504403842e5400e080b40010351205c000f4030180d80710301c141c8052021843c0003201c003e2500c42c03284020040c3e2010f001081489003294041c1030728443c0075040c2c8a40e9616101c050008510f86400400b850780445d40d08420400c030300d00c0341c400c103410030f00051600f00c011203086525840c05001e8030b0170020020964503403511007042040000e1200070800c07a149916403480a07110b401038428a404201c030341c80b810720030f00342500483e0201d20a48001d141404800358a00c0c1408a001c1e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594422104 1250 594420854 594420857
    0xf0b07031b11090114010e0a0b03071d1504090f18060f06030803190c02190609020406120506011406090a03033b04050a180b0709152c030d0f 62
    0x4940c440b000351a0076401c54041d0502c90b4003008485502e60005080c2588281020300810183d2410880440038000782c07500300c425820420000b50301010020441201262059403000342e60388a00f2110081400420079a10300d100180030300a000700c205400d94514130242a144100c000c2d00b08003140b4254040602100700e0000811101e039240c4030003503250001d443c0c10040e5411101c0007208600f0a1003840d603420302c54001740090303000803500702d1412084600090704580c0c49000020441d81c0707aa01c0300028004400c00f000350418076040166448109001d203071090128a21060031514095043d0f03049900c0c0200810452410750394204e5000c00c542e0032400e8211040c9a00d4140b54814551880600100113a0090518400c508104c1601c4000d0180c1c01d001c0d24140f1900c401e40310707101440780b02c2600560320f001280c50b01e0340b0440c0e0320401a40420703c24501c1000200d04640e0050b00c075030448580c20071413107182040180d0440c20090850f8603d0341740d8007940301d9840e440c0c0180d51071012481c1d03d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594423354 1250 594422104 594422123
    0x141e03061f0b0307080106030e0c062b0e060f011a070204020c0c04060627030b0103120908010f0f0c0f0c140109140d0206070507050a080306060f0a0201060f0b07031b 73
    0x1148110030700303030f0401e4a544000c501c0c02c00062000c00d070700d84102c98422007a54001d0555544007000310f580303445a2911000c5800310b00d200d1104030300048040c0310342e07441514001c001c07001041a0703a684852043d039400250720448000090300070788210000154050307a02115140100503030070000254080c29400110740106d21b9518070355a40c3e403007040c0c000e08003a11090303091000d540d003150740751000303041c0141e0300c1da011031003800410186454541540d038090321165445440f400c040d2110303134481c1d010f00050b60a101e10f411105040d03401c40f00c0c107403418030000d00010703100071015585000201040c030006a0324070101401b06810340070040c0b501c00e85400024091941d0384071a541041c1e104842e803000e41c0101c5000389000c0d81044240d41c0141507107452420406507540e6641c645d02001000f03803c02d0400300100341180c2e5100110b51507d1940244c090b40d81c02140c0e40030703000c2d000610425008142c805400145c44082c0301c11103420a038903030740d18020001c50117015981108201d0081e0365144a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594424460 1106 594423354 594423359
    0x40c030302060c0a1d0102030c03030c0c070b0f092806020f0606030a12030c030f02031509090318011d0312040f050a060504030209071701141e03061f 66
    0x400d0009100c1403002c170004074954000c1d040b480c0603d0000100b4040c000320120000c1100d40e0302c0030155108c156468150a007180039080c050025058204280c1c4045d1030a400007404054400c40040c015074400030b1064009602e90300064050380c0101c291000e1244100002035000104400030b00741c184056944a02e0005400f03240701c10325444a00c4144054081e402c0650101e80c031038821900c4c4e01d8540e6024401408942074580150026004200309110100440d004c0c000300c0c2d4800c0002182e040700460740c80d01c1d40c00702203203030f0500c9440d03d0384c00c0d80d414041030b20018641950152a00d08040d5402060302050380154498a000c10b01007141039004000d8504407030301101d003c02c09545235401903070030040c46040740040010960011074104140c1000000448040d250a02078401034424054812000015568583d0180000840321052000000d485d03c400017a0701c1042607 = true := by decide +kernel

theorem cover : BRFrame.Cov 594244604 594424460 := by
  have h0 := BRFrame.cov_init 594244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594244604 ≤ n) (h2 : n < 594424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
