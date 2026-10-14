-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:22:35.467665+00:00
-- url     : https://prove2.me/submissions/c783f9bc-49b7-475e-8efe-849f49629a93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600899280 ≤ n < 601079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600900530 1250 600899280 600899317
    0x7030e01020f01050403080a0915020a030c0801080106030f0308060f040e0c041109150c1507030b04050a0b0f040b190308040305060610020a110a03021f080c070203210f 74
    0x69590401c00340224105410080000d8102074601506840700101000c0f8010780760b0000d8010401c0e9600e0701c90307410f00380302c100395102c001ca410045d0192440750740e00c000141e40400001200d08050007803001303e82e002521920040d246403422241040014080b54008428140581c116111803244003a448400c0019006c826030540070041a107400d00741c00303c182e51090040300d0311540d40d07030320030060818621050b5030f03101600c42015007000d9200d00200800a80d0700c1c1045000340d0117400a803483c0c2d07004ca070104600c0e55004401c1c02220f080d143d04035001a01c03403500c02d845003400c1d0b000c0840c2241c000c0008051007050355514020744a140c200b103905400102c0c04000b04401000308603005002181c07401040c036007040000b5035070441b111024100301d45000c040003c0e91120110100a5a0040d0002904d044130300318500f8900c200c4180e1a0001740c030040090244601d038401d82c0c0030b89600a002d044030b00d41308a0400841e81010007141c0c40349104104100345030481e40f0042030f0f1003144940060f07a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600901780 1250 600900530 600900557
    0x30b060a0e0f0910150e040606080f0313050d05030d0b0415030809041404080d151701022205180613090f050f061308220f03020306251d060703 63
    0x4c003502c0301c00600403d0704000002e00e2803d0108140303001d4421801d5406a299154140403020300901c0c1d0200401c0d0060b640781c60342000340400141100c240c12010181d0039a5107005201c1540c50541000d85550400e0240c940840580c0c3c00c4a00d40e8600180086480300f440144401844007a500c11594413000140e0083e040c01c0500440014104071180c4514516080e2940d00480c414400242601580c0d0400000c0412403901060301410001092504141040d82514001e40c00600d00540e12090307801c0e05104501142c501206540018140059444c5491901c04c0200c8001e4211070b4003c0080150b000c070900e46100348108a40100c1981001540304c3c00c01509210903460680f00941200003004440b8150494102c41c640c3c2c45031400d43c4e070740030200141c04210b141d0b030f100d4514403500c190002440400109074000381c80c001c4040d21050340300c41543c028401e08010a0010b50300c000109071000500031100500600081c0d4080701d441c090a0340007039015071040004a0104e80310420085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600903030 1250 600901780 600901783
    0x32409100603050906060906060706150b030403120b01050a03022b020918090c060703030b090403031b030207050d0e15030f160206060f100c02030609030a030e070f030b060a0e0f09 79
    0x350400301000262100e0b01b03004000c5003021900600c02e5004a00c0091814100402c40e4080a4501c682000901c81d80e0f0704d038514400c440d4000e40302903000580e40030040c030070404284500c9000ea10140c64081c0340125404003034000e07400c001e40f06c22400405408000c4e80c40844911442031030420000165907013610802c00848480155280e41d0303410340c96081041034080002c00741030010302103541d5520b80e10985001c8001d00308024905410801c010140820143c16811058034100d00381c41911050101c07420407412800f8a002c0a4580d5000c510748034101800783c951800019000740203503450007059060203030160b109580101c0000002c0d000c2165004213040d081040c0d0005c0c2c400703001d0a080840000e1a65004904a140b09485045444030028010020b03400c15980c080c0a5860618040405540302e8019000c20004030f400c100042076051800304113003007619141c00d480d154183c1940c5170b0103958030008003841d030440700311074001c41d203203a100c0c01040c400c015001070b160031840e0014509 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600904280 1250 600903030 600903041
    0x32a040317190819050c0c19060c03090b0606180904110f040606050711061c020c151e09120c010b0a0b09061605010f06080715080705032409100603 65
    0x1c2d000c0105940074000703061100c0d03a0207004141035a4011440b80c4604001c01c3c680c2c42582d400020602c1401c20301003036000100d201c803160b0350003030408001190321020300350203803801c0001c014400496903001555034905080035204130442c400d00300280059180110b0b841c150161001e50760341039030b0001581c252400e00450000d0000940c0c09025980c603049010340b03103000c0c844008000b005900b150414980300d12094a42441d82c0002d009000410203501d14000d40c0041d04403000fa001d1294030121030080043e00f0350007140740c4404607009643c10301f900b0b00c0e0100c0140841801740654074008000c90103000152000d00800d0b400007070b24091850800040e81d0043d4411180305205002c281115910681034951086500c180b0b0103c2d0002480c09034010304a03403c403201c44500c0c00c8004540310500040080c2598554226480c0e128038003001a559500225400b00000d030041000503113120200f9000a1030000d441183c03003e0b0382c41d1000080d02100c044a11401d00b07881100c08100e0303a503060084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600905530 1250 600904280 600904327
    0x109050a05030c011b053c09041406010e09070c0f0c1509181a0d11180907061116170c0d0203100915020307020c090a02032a040317 58
    0x3c0c0c1d21700f500700c2c10080c106010712030084100b0840f2000c040d0a50b06440029605c1d0000414040359519010680d200c0d69007049180b00d00461400210003081c4c03581ca00c210f40507400586410040701e900c0002c121000f030000340304c0c0d01040a181891000244800c01000085200c0e00280001e24282240c14a050041e592200200440c0c5c40e02009546000c00c1021b40700510811f0204e076508920100d40580e120302c001c41d540080100c1d82310001c0c08259417401104180482c1c50112005d1070517200c0400820503903815000303411038102000303803d00400c1030b040741e03c40361010380e10074180c44410303400d40c030000b940084420301c5201c201d29030b019010f10651004200842d4180700400603600802d50394040345181040203695094a030b428040855214400030b10300030b0040d541e902d88010000d46400041c0c2c0707030074082d61981c3c1c0402d600792183d0080c0c03445130012548840c1c0e0031a0340c03d03150f48040104000040e20280c02c100110220f0b515903030701c40030000e0410201d0b0791180021500485a07541200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600906780 1250 600905530 600905561
    0x6180201110a1a071704050106080607080714070606090905010e06060109060c12020721050d1706010c15061205070605030403090b0a030609020d0f0f060f0509090109050a05030c01 79
    0x250008107200503581c1d02160a00000701113076140d4900740e9417811703502d410540c82e2808004000400c40c0c150498015607040900f41c449a403140e0005543c0c0440c183c2da498007090207030804020150b089000340c5030290140e100411901d42d1030318804115403c010041c0d4042c0d44903801e40d0403009040003400e41010b420300c0d000811916041008001640e00d0400070005c1480b1111802d005200700581e00103030070840892010381042810889440294503021503050107450280c041181c001c0d1030500e224103403203444400c00d5903141d0044540b03200a0f04101c520300703102c084400c50300f10f03c1d20825000e04807106400c40301c40d03500d007000c5150041c3c641c40300041002c20420800000e50210f0184205c03401846110f0322001040c03000d4014004607000700300312601c08100190000050b400c0302070040604a810001400b1a2501c48251001c80c020000030103961501089541414164158000c42100001942d0724142d07031200e040980c3c00350141c0c1c1c59400840c24070380703220303085c4070b1503030a40c01540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600908030 1250 600906780 600906793
    0x2107020a061e030b03010902030609160605091302031f15120507090e040c05030a080d0b0103060b0a0e041d1c18050d03021e010509010e010203130b060d0618020111 72
    0x2c903100600d4918080d542c10035440d000000102d8509410250314150f00505076013103481c003145200d07517410903400c10501189a002000138014060022a41030300405030000017140040784c2468065400940014400460315440f43c40031181e04032110040c1c90a8203c7c82c03080c11124034014880342ca1110500304062600c02801500e80c0c00c0b24002044a0090380c11401c6590b8504113440d90240ca82c0c41141c15010f004000010068154010091495200c004000e0501540c004408a40e4540614219410108030f03400506001d0080310081ca0f10041c0040365902c0d0050fa0004652484081098176900407804900100480040b5924641c3d16181000110503902c00007040000c0520455010311005031010b01070504c00d006501e50341c042c49128102d410905500da500130102162010815481c10711701002244040c0212030141e181010a0314920b0655200e0758a00304000d0300311a809440520140c000401d640180082801c80c2e48109058010381d00000d8041c0b0141c0c21610207642003403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600909280 1250 600908030 600908057
    0x70501020d0905091503120c030a1e08010e0604090507030c03032607030515031510120302061906080f07291c0f060b071202010204050901030f052107020a06 69
    0x220603500c00c178509424008009150042400c0002610098a01d0000010f8808400000000a0800520b981c1c5c07407200c0e001440701d0542644c06219a0000052801001046508200d407a4540c228400400004800400740d0307985e860004142e108442c00ca802c00020018541c00c00c600040031150140c6541d4443c0b5544041e003000540144070342c05040d030f5080407425124443c050b540701c0d080003038112502409080c130101300a0504446c3c030400040030031004113040010034046040964190001e00c51a21034061003500816040500801c2c90340e110030006043e007080081c540000e03100f601500f00ba6062210b9500046c42c100403c19405001450b00882d0038801811240071408040c211400100781000703500103000400e0b41100458100500441c140a46800820210f0310030031100c0004c0855200980c02c1c0e0089201f000c0e0b116803100010000303c0d411030a41580b092203130080e6183d2881060071500c0d41c0c0649445004a564007040d00030031402e204a80300b0107030420b42803000e8214580c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600910530 1250 600909280 600909289
    0x90f0b0613060503100b040e0f01090216170903150108061f050415170708010b0d050604021002070815010303020c01020f070501031a030a05010b100306120303020a1b05070501020d0905 81
    0x10341c410b45040241c00000070b282c406107800c10502405c0c01d614510b640315170714000403007448410350300003048420810000800364254402c680080c1c0303901c41714141000c51a01ca240b420382c040e0390301c00c00c24a400c001d140107a94043c0300c928003020319403108043c95414600703254903003d4010401a5080f2003130080420050310070303030800f0403600100e50125442040034002c060111a0303500240180c130505808070080301011801000351240d00c0001c100b041404410400414201080a030064001e1030102e405400c01c88101c0a80002c070340110307078810345d613a00500e25042011003c01c0300c1580040c010700405606100c0c1911314030092004048084e135044da01c94944145120741e038180743d9035034250b09a207003a0310b104010b11000202a1382542e5480e081050291100c0c845061107800c1558100d544035000e031084100707030b800560f600c1c030f600c4050340c1d426002580803001c504184054006a600749038404410000704500ca0005010043d240c00c0c00685030200850451040c0711040340c040c0100c0d10b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600911780 1250 600910530 600910567
    0x9070f051806010302070609031d0a0317030c0c06070207030c15021b01020a0b1003020916020a0f1419021003020f1c060b030705091804020d020d0219090f0b06 70
    0x340c81e00301800c6900e4240041c0c0091260f690001e11042c245000303030040c190000d0720b80000804101000142943d000d0820505101c00c2c00b009020320181c508250350005500d01843e8019119041245480942031207585403902c1240ca1000581c803403d010b10400214100100003404200507030009800d460034069107135075101d0799110782c4e1900350200382000c0e0710070040354101a030008040c140b642482103074841c01000c1070000781c1c016104440851825881003d4020b0b0300b0500f54090010b401c0d90341d480c80460550f100c4c003612410b8285551200f5014141311540000f50508006140c45e2050300c1400502103103213030f1202c00e1520500506c0500030301401200c200c20a483c03041c41c02c2c0c0901e511807900610b440e0304080748560000c01080329850b0400001c10002004031901041644204202001003408850080d08030b03c50034034040050602c0868141c501c3d00c0100512412985804942d0340502d296000700c1100d03454002c0c9444030403d41c81881c1c0b1480b415203100f4903102c003110601013504d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600913030 1250 600911780 600911809
    0x50603010603201f0804120905220518030304032102030f0a0509063c07080709090209100c060902040c0c0209010f1409090f07090f0c02010c080a020a02010212070809070f05 76
    0x147e80ca2055845c1ea44182c4010010b450300503c2c0b000c9660454a01d24020b4280d075440b00065886d040204072810910380f498501d11506000540c42c5036103aa81c219007500b0040b0007400a00703a407030107801c1c59110034005507100718118902e18840349070800c2d074030307040d18800380c48070101e5005130b01070083c000242c8014011440e40d050182e80e221204450f60041401a03098106214100005101440390300003212409000d5a540303140b0040c2e1100300c000c04030f2017805040e035401420101d03105506d0740510b801300c074818044d070380000d0310f071016401003810750310040034a60002d031402050368110f01c1d00c09040380c050124000300f64025070411a00356555001010034910030840080002c0d5142000c2040040e089008810398038030030b0740d448885014243d00580308a0241c10101d5200c11144144107880103100b03141c0e1101c03144c4c0c0707070b81c44400000c0d4812400c0508554082050070b00c1d41070400c0c101ca0246140396102c28861500c002c2d9a401c145203038003c030000740c02e0000100100da4400021481c2003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600914280 1250 600913030 600913043
    0x120b090124120213030201110114070804080c0709021e0c030a140c01090c091b0c08160605041b0f060c080918070908070501030b030a06050603010603201f0804 70
    0x14410300705490750140042c2c100b00b454000503240c072903070f000d81d82c409007281e20130b889503074040c0f200038159802c0c0ca1117141464506100c0030000307184644a8070002c0c0d00302d401a1009454241c0101c0b400e803c203080c64211070f0b03116400240204400000c44130030003900407521150340c1041000c0c0b81e40c036100d2040f5108003003000000c07236202105088100032100803000b490001c01030204a403400c8040f1103064402c5007041071034284503260000c402180910b185200b0f80d1203001c14146950303038103140d402500e4082c10740c140ba038401c80c00003100d0344030b440e02907801072a14512415249400007021345481e0444c9201318900001040311541101903403e40342d0303200b0801a100d29041c404103841c1c62003129440c1c14582c1150a01101e540c1040300c05c016208110141c440c8070752100015001d49400b054500c0d0158459001440400c10070791203203800c110028000b0a0503035032a1200c07054141e00c81500c0ba08082e041c0790302c1c0400d00c2c20909800485101c565985401c1d2051000035145480060014044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600915530 1250 600914280 600914339
    0x10b07080909090109030807050c0c010c05030d020d09140703021003050a090213020903070f050a09051503071502060106020a02010e0907030f020d06030b06060705120d0b030706120b0901 82
    0x400404400351030500c1c6001d0482807141c500000e040d03001c1c0008a0f0250040341140c03010408451290040300c0804c044e0f040200004910400115491290300e00241d40d41e000c00d011000090401d4002041d80c0d402641001c1681c43c00c50616001c1000209a05440766110a1040006845189281c00720070807600340000c0030b60b03c100f0703a6806049120f80c0294800b03040114001d94041550203000340c280c013982100d00c1581c42d1461362004d04001d01802d0360260300c04004116585164212951003000e00000700071550fa2540820301d403500d180c000c003807030441340104c510700654100655130050041e40300405901031a50000381035264085243c41c011005600000d1946000703030040007001f03d0303856003103640d6100c0d0300d038040051101e80400c451892031200821014680641a10403194100010b055003002480344c08035654000301d81c40750003d80b00e8001c03802540d0140006c900502490300e03803820600802480104544064900c01d110301c0603800113100c2070b0300714400181d80c00103c6616201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600916780 1250 600915530 600915533
    0x2403020f1813142a0904051b010302090909150703110301060c1b03140d020c0609040b0d0503040906151d1002071a090f0102030a0503060f010c0501092004090803010b07 74
    0x2600000c3c2c10070324103482000c404240741d540280003080a400804491840c5191220810481300300540e0040c01aa000c038182044175000407d4200281c05d05040052410740003a001c1610340c88122007016094014070f43c9010024180c8450320342c032440c075103403c0244c036a4610b507540701400f044c010707242004103000303d10341007041100c0070080c2c0b000340c88805000d250392454001511700030219044505d0103100c02051280e80000b1b411040c2c403c00404d0681884540014880180729081800f60b0028084403c81c000c201c05000800c0601419200031a40c0350424042c0910308480c100b1180401030a4090130041030104100c4421a060446040956100910b0308910f400f509410580381000c2603020310380d0011115006001d00c4100792617001c02031520800690312801031344100c00c045002000090168645401e0750070760380340f05040140d8803906c1074442a08641c1032000803540340b06140b4030190102c810509010101404540030300281c502c0e60f0328403400b40418800c400441c000850710a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600918030 1250 600916780 600916793
    0x2070e06010504090513050c011b170f03010b030a0b0a180504030e15070c06080c0d0216120e0909030309071e1e0f0617070807032403020f1813 63
    0x30002e004c001d0060103a4140810000322211740e09030225007500c20f614005201d9400750045181c800f01004100450080a032252216071a6403e20401020010065140803413005409103028000441c1e015480385028a54001103034000c0707101c00d21682042008000d003040d029500c03601a907804401145130384a03403400740d8032407160010890384007401a01c2e2020340320000021384030340d038040d82c1074a080990740d00c2c2c1a51054404d5034a60a03041c400c0104081000303494004150000541c338075000400199151280c030b1600720510440007400014604201d442c1c11080550407140c200c0180d8510304100200c1551426144203d800445403003160504854848078080c00130440300f000304c07aa145da9a46807048802e6980100050701e00781200126400c2d10801d00c0548410000d044d5680c651200e15081e0342003540140044c04150300c426411080c8448204169004a812a5940e1a0b80e040d881004403850a0868450049034900e00b4804205041036000b41c100d890343e0008511703c501820041e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600919280 1250 600918030 600918037
    0x3030e1e01110c040e212a0c0603010b03090c0a05030d1d06030a0504120903120c0813031506300206040f0f050f031b01031503050601030c0509090a0302070e060105 72
    0x30340d40300b45805e0710401035403804900e81c80802c212508140d03110244807416203ea006a0110140415003c0e1305204605010003400404103803080880d940442c8280000b0340a5001b42c000d424003060103c140302c24080100315900740610b0499014092501340ba010036502c643d0001514104006c00c1d4025000e407885501c0c00060f01c2c4064013059a84c80c0c5107440f94040d04094070122441c2039030900041055200d4a101000e4980c440e411603403192159074200c45062446900392200c24041012090342d43c1c6000001c4000c500c122403203440100101202c00440701c03a540041400200c83d014dd03034124201d0812030005108044070019200e0050022600d24010341d0080158880d00030008940094144c0744032088030b508482040741ca45d01501030580794071030922016010074440d892801c3c0c540c000c0e08070034600141148829001da81da526101d19041003130340f040d20311141805092007107040050702039038004211001010510101d070760003903507a00c09100b03940c00d500f00c4602141d11a8400c0b0f088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600920530 1250 600919280 600919303
    0x1803010903020a060b060c2b020d0c0b0c0c03030406060302040c1d0d03020307051002120c0906032e2d0317090f06180102070e0c1c0f02031003030e1e0111 68
    0x12240f0b280b02321a00c4170105621900c0b080b10f11039900d08440020b40c0300141c00f001d1240e25546d41000b10065070b842c82c1d0b4030310001d070152844000038806508101c50070005184228000c1c00007140e614614014001221080d0078800100055504418080b02071606a6035580d00b040c3c4000d66082e00d1803d0403415800703613140c003c10380c2c010184d508960000e0740d0090910303800b1000861620b80c0f2036641d02107991044c00740d4903030004c00c14000100304030034942c00c45003d500c0d5410402a0711420b0854000c8103009500f1540c1d00d2410954002d0102d1100813a005030304007003030700c0d240d001405c60300c4540744485c4502110510386000201458185c84180c0c0d03a04640c0005042252034112051150a0a5a40d04445401486440d9000848500800d03200340295642c03035000789080d000c076001e00c03d034140c11081d1540c800d445010500d041c1000788011482040d50100d044091421860001e04901e12207002520500032000403c900b40f190401000341d4500c05d007400b90103810510a400d0034046401c51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600921780 1250 600920530 600920533
    0x4080304060503102103030e0f1204030c0e1506030a230403080901140a0905120406030b03240705090d0606060306090b0d261b031803010903020a060b060c 68
    0x24002841030b04040954014001074101c8030745203441d030301d150b10400c840448000d10b2000c13100061010a00035031007402e81da5004000e0b180070000490701036281403000d8080c110010400203042043c000d0503081d40b009846428008591801c018110768003155005134840c2c820000040403580b00d2207a50b009441d140c0c90981010003444010060040a11003140d040d0040f490500014031202b006204001c102c00c908640702c8040c1e20f802c0c2e980001460091030850b000e10a40991465109007030014100600031360390040307500130800313060608101d604842e170f1200c4103c440202c0c0c448001c0240407a4002d00700c2c540107844407091400240f0722004d103c4007030040ea10b480000328035582d00d500200142d5000c1a02806552818005d005040360700038409850300569040040d4100340c180c04203a262100080740790300b08180008071510f0204446105000e43d44001140c1c488562102e440c41e03c2548200c3c02001040b000c2d44019441d00e200b2140280b000703039036020b0301d1840c0c0d56a4050300e0581c5a03000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600923030 1250 600921780 600921787
    0xf0506210709051008250504030218061c0b070f050714060412051315020a0503030f0f0a020f0a080c0409020a123204020607020d0b0a06080309030703030c0503040803 73
    0x240042c0c01d544a07409401d015452514243c83d01c03500422015000701c0c00d046031180a16070100b091a0320181c00e807244010000104000009030b42c0d5081044444540c140c400c4915040c02002c0201c81001e00310b42003408180e0b03803401000720715000a0241e0144803410074120b031980706003084a0394829140c0041c4801d0810850707600c1d2542c0040c072544224821100340e0076100180c00e0a442d1402a40d001c1ea02e42510b03c0d006006140c410459289218032500403950030301708a9450908580084030003040b100d4052003040802070a04658640003110400d00b1842c040c210381c0c2d180300c54070543d00041d05001d940740110320070245000445005041d10001107445410b44000203100003248500704c032005050541c508a6507202401503012940c2d0b8900203940c80124030b6440116410040c810303684036609110380c001503120390301c071071414a1054038040300901c0e09034034001c21aa1503400004150748203118084035a20005003030001e036501030800700ea4214152501e9840d520458002c071801d0702011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600924280 1250 600923030 600923041
    0x16180f06080708181e19050d080610080105010806010e030f151b040e0406140703020306090a060303020c0d050106080d02010b15070201020a020d02271905010f050621 73
    0x20781003400780c0680d9036900315603160201c1103104a2460074100c1d1880d00300003580d280c910342014000c6965220700c01a50003407503583d5048080c4404084096800d07410420940b1000d5921290895103e041260741d1104400c2148000b0719540c014001c0350305001e1101c000c25810b0380147c400010207000102140c1211a0205034640c90f45041d503c0d407416002403102040001da40201e0307140509101914460a2501e000302100820078041c1c0f080d40c8190389c482c44584030002c0a100036109901c40c3e2805030b500c1c00d044c020310050301c100621401040346801c45c00e200283c0e0100b28400041401c90303011580c0340e05414941e00401c00c943c007905251050f0055402569010740020040c45402c07524651042e110b81c002c401c040c400c40e58001d005821403e1901c1c0140b40a4500c2501070b0b001074005440300380e01c1c41b080c24100c0381d01081030291078802c0042060030018166000806405094280a1940350202e41d51000090303015052040704040f131542d620701850420f4a0300f08103800328103141030418 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600925530 1250 600924280 600924287
    0xe0a1e1404240f0605030c03220503040303090e060603041a0a0b0d060b01020706080f0112080906030403030902190e040825080702030111040e15240d0e010516180f06 73
    0x80d80f1403908104504103001a100c2e0061060781e104085202c000c40c40c41da109121708070004441040c0810023950b8141680110f4420006000a03521944a0951440c2481038000d90b484005110030701c034170020801c200020760415003076000c030300130520310170078030b843d550f0002c8040e0101001c40381d0007001c0b03058075005010740c41d00301c698030a00c2a025559010344808045071614001c5840100200518004000180307195841d410b040b0700611040d400c0c110041c00150381c42d401030700c1c180d000076202c100034419881c0c50315904141ca0540041c10410303c0c0b4112940b44100f0006001400088001c600c3c0d903411014007866000325212020400c0c00c0707106c5850014000e400449087c3d000c1c0d80707084036a48904113024215000c0e00c0c111040800259200b01501039960301030003c25400543c400c224440024400c1e400500c0340c040030034240e4503040301004400c101c4401e41c456240c281e04180030721104528450303405400c1d440d1450f200d551181d141855001c030102c2d40c1e1241c030307814490002c00a0465407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600926780 1250 600925530 600925601
    0x103080720040f0b040608120a0c050c100e030709020a020c0d061107050717030703140c1e01060602011134050d0507030825111504030e0a1e1404 64
    0x1c17107040003003c1d16480525522010303500050304e600c00811000a000d0301502003502c0e400e220f5002ca405030034884022680b140742d81d00e200c1020032240d2074501810702d4288000710107803507200070444c1055454030000f50740310481c105444c051202002103030306001304c03500155205008103242c11b5551040e45005507407002c43d1311078064140e00c05900303500004004021507002c241c0513035a00401609400525080d40e000741d4900215108141c4114045480c031003800c1c140c1041c0b00d000042c06441c0030006400c0d03619801c02030750b4260301008030310b00519105c4e040e00740d043c518448260b804502150310072140754101001070f0041c072600d4180c0040561100041200510a035141e40d0503171200b4050040040c0345014981403000c2d41024403c2492103030104080c04101041103517844602c510180e011100c040d601036002601d2040301ca10b450070482d401800801209082809210400105e00442011030213454034400b00845d102d070442d9140d07041744504050f00f616010700459043e0b84008003c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600928030 1250 600926780 600926801
    0x50406030c08100902030c040b0609090103060c0906091d0c0c120a12090c060809010204120503071a1603091401020a0909060f03020306041518030f03060b030103080720040f 76
    0x10883c0785201d08030405010b2201c1c6640e000d001411211220010080906000e021042d08090b041c05103c40c25540c40404600071800b41b000081c207030710049801060090981c002d9001d10824000400200308059020102c10943c40e104d10314513112070600900a2180641301c02c090310501ca121000e540c80c01008000348000382d140d00c2880142d0112580540e0080310010303281c4901e0b141c1c03c0000c103009031422070b0b012500c40001031410751950325020302100414025540c03031740040f401d00304020040c1400b0810f83c0c603c039285031003482d18103488000d01610404034010141c50301c4294040005a103032480161024600039034660801480080214104c0d205120b442030030070100052446900c240d103429a03401401a0210b40d8803a20340302d1450a5007141344014079551750541f41c0b602c4480100c00305642c07181c1d64550403500901c02c01800d441c0c140c2c00038040a2400c000400028040004454406074803c40031020950010424000e991171404c41c5038009081c0802c10000b01707915400903c144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600929280 1250 600928030 600928033
    0x90c090f1c0507180501050406180506010e0607140c0405060901150507080a1d061c1d01050c0a030b0a050108071214010b120f040209010b0d020408010903032a1e0504050406030c08 79
    0x21ba07078840030401a40d02a1090200610080c2c2c030302c0201d1150b41d00690791203a01030400104401198001c505aa07026075803c1d0b40360840ca80302803008400a0040d43e0125004480520440c00c00500180e600310061062041844400059201c113500500c1514000c6800035113840c0c480707080007406801103501c0c40710300d942500e0032842204c540c600352055408180c00d00807215070704548078408100400d21120705195844600381132a0700c0c82803d0182d180b043c646200b041e40c449401e5030014094410700c03000701d842008142030900071a64440000350340300c03480d0f00e002c140780d02c200d02c003220003011440c04050140d487c61001090b03003065500100000510b10044607040da80d80940003500590940300258003aa15200420071185131001920860510a5005241ca540e561005085503040c02e03044010035103e07010760b100c6010004004500f021406948045500c10000061040c801c01003e080030703141a41c005107003644560203403000f40030090820483c20343c690801a01c2c2c8070440c40343c1042c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600930530 1250 600929280 600929291
    0x9080a0f031b1d030f0304230a0f03020a090504082a01050f0106120b030c040903090b0d090b07050c0a060e01060317030411100e040902010e060d0506090c090f1c050718 74
    0x2401c001580e840141e01d00005503041500703040304889041d100032303200f0a0329982c080d0186203039070b02d00301c00740000c03ca07040180014a203140306000380e6003165440b07110010b24110410001c0303080d050490b0b84111010943c1110b00b0b80c07075845480380c203951044040c0c0a40c40d08007000003946400103180e0680d01c6a84074240c0e1344500402c02030036640200c102507010b41000c0c1e0510301e0340c241500407a001600c20709000722800d071568400c940c590085070541059985842201c424000f043d502c403030b0001018a05140b07401911802190342d444404002403015a843e40306160111003075015502941c1c1c0140840b8501c401480b2400454200355005d442c0c3d40c204034844403241c580141141d80031851521118141c62481003040010701d0030384011707418004400000411903031640000c1c6070960070010001542d0406a0a000200500607c3c1c0c40300d00303008100c4154640e460420310b85c40c0b17050131103c0c0d80001105540c0120ba03c400c0503401055407142d104042051449012241c086245101e0704121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600931780 1250 600930530 600930587
    0x20d060f0c030b0a060c020f0d0b070e011202071a09011b0215010807053604060207151a0d0f080c03120f13060f09140f0105010909080a0f031b 63
    0x19101148103c60101b00780944020040c101070b003c590266200601d462071141c0107071601030060f6011070f200c40c002080d40c4115840c1e581c1102542802490020046081400710360302c0d034800d004003c0b03400100c0103000700007a51404094000421503150200700c04802203e11a019641306c240c5680d007580982c101001003000503000882c04c04039038002308803003840c11001c400c8220256078403190a403034400f503030f60b80817150001c00802401980300e00c8c2d00603603038603007800c1c221800c2036503161080e4150f041042c0c40b00c81c0c0808006d20202c01104540a05500c00310f498403041c00c0503a020001c10b11580480d180012140110140224114001c0454200d550b1352040e074403282d03011104144c0303503003014001d4404200243c0c441c1d2407404681100242c118100d07240c1401c0125900590960340c0e11071642d4070710000081c040e443c0100103401c814402c2e00010b907510005030103000c0c640f07000c0104522560803040d200740c100f0703d08841200c0c038000c07441d0f82030407009104c040303024991008008100a00c48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600933030 1250 600931780 600931789
    0x2105180f0a0b03040c030c03032006070801090209011e030603020a09020901020a12210f1109100e06041d010303031409060a1a09010b09010e0625020d060f0c030b 71
    0x2165400105911a01c900700400c1c0c0c5050f030006401542d2111140c0d138080002800f400400c0b0155000b03441e04080440d2441e04100c18000c041a500c015822a01c14080c80310340169096055516052b005601c420742c43c401221402c1c440d0103140c01c58130748c0f003815403c01601a4424803c0d0780c0242d0345005142d40326100c4009910464a0140c0107034040180d14011076035a851140e9061031610b0300c0e400500741801150640400075022480c801e40c1c5480703110081549120782e01d041c8100314a558148800d41001400e010107080814052261041d1009100d64070344081320080e00c1900d104042c4403e4441c41d55510903400d000440110b0b2514030800e00c1c2070b103890340044c458444000141541d5449106d058040c00081007081e0600955191040b035565528410034040c041105010b61180e403068001840301e07040017402802201d01704184580e0850401c02008104d0f2a4140d5090035402e610100b803220403a5503000c0c1c8000e1508100f1219044260000e240b10000c079901446850a04c40030170 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600934280 1250 600933030 600933049
    0xe160317030a110a0f0201051012150b0d05160b07111917030904061a0706050907170a150204140f0301020f0c0f0607020d0516210518 59
    0x68804088a5291580615040c0c025a481840c529000c100640e08503965083c80c0c000c0c18610000c00c802030a860001d40d424440c1d5580080d818400071318042c5000541c2807554885000038000113480f0f03055903805101034005040700240501132040b007800c00d0800689a0244000c6e001c00100c4404002900440d000c003a2401540c001e80248140030701030042000c40601c2400700c040b0352840d4103000504104200c42c4602c845e41042c081c6035114484000c000c12102c8a801110311001c060450107090481e20061b103560651000c000030b01502c442d0b01c2c00d490303c402940084050038800c008600f08500204243c408107104140030007540240c111200c0a81c003c50003444200210100401407034a041014021760000c0a40014500380c01400c2c28119944013100200c207030f130720010307105c1c0c0c40e424101304a940c005502e1010b00ba07000c00301380780140301c1d12400c00c401d02c0640d0074000c0201400307415001194603001180000c8180428144007804c0c640004110054400c080c1c100d070f070311609080460f13 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600935530 1250 600934280 600934283
    0x1509181c0810050a0b0d0e010c0302120901020c030307110c030a1a06040905120f04031a070f03140105010806120d0906021612032a0501050114120a02060c010e100e1603 74
    0x188425402e100325844c05800c0040e4006030b0755159480c10102030009e11442049250998002d60b550301e800c0403200c2044000791481d42540c1c41081030340b4280e40044152600082e2900c0c02d114002c80d000340681c0f42c4002c003061203606014584600e4200b000e520b9903041441182045400d0703a0740c445080004031050004064001d4100d000140041f146000c02440070b0306084000a041075140d484003805041c41e034610040c88442201401030082d008694013820401c10702d018400800c000042c0e0312091018454181031040040101d81d581d65a0100344001c410050210749108510f104010b220a2a0f81b10b1400540255070852054848014841044e96505103180508a40541d001c841c410220814140d0141124511000305010070a01032807403809680040796550402c0c03a8008040700601c03105200c0c4120700401d0300e103948003145140311107404aa5050311002d605c21090b014040800195000380160080c1000051803580012075580c1e085044540e00341c1c040d505100c2c1840607010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600936780 1250 600935530 600935539
    0x70c060509010e060a051008011a0f1903061d01020d0b0906060901050403110111070905010e2811160c1403160e040321090b06091509181c081005 64
    0x80000c0d42a0304095044042547c1246170f0540da0072840b4210b942c50440c5841d01c0100724030600d01c6107044030f204041d8850846502c0131208040010325070220880c40010941c82c1c9504a12481061100405440500200080d580c50002081a0004041d04c040701e5118030b41d45800314600b030800009551500034180c4803140b50a046851310071305442d00c52045030400c000804850010030302488510002c1000d05804903055051202e00c3e203440c00000c041c00381c6040000001441d00802d2076881e20031ba1000080001c401c003010303191035150310440701d03090501c14002403d0010007a80b174002100b114682c056140c111111072003003640310201d52404005400051000f0302c6008904040320f0380052003818080b5451454180d481d180300304443d510b09101d65120026800e000e450341029a0045003240c29095a103090340e0895000780d0348548181c082c201c0000000c042034100240c400c0200b81400c1210f4070040c820a40c41081c0c2414800000040d01c2c2a001c2a00c0c4c9035501e6074041543ca0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600938030 1250 600936780 600936793
    0x6110f0a050c010b060424050906040e0405071a09031509280203060709091a0603160c0b0112050d05030103390b030a060503030915130b03070c060509010e 68
    0x54201c03215044640e080055540e94540d5a00030368840000f040140541840c8000480503100c0500414041c0700d840d0061040c20842181950f43d400110307420b4800118440355940c445040c4549044a40d4004e1640c444e005008102003061040142c903a1320011002c5403d160050031500c81b0303050096480392404e5010400d142030302c1d0601c56448010f00010710840500c540240c0001c0d140520070350310040841c054803014041022940109031075010320301c0710729802d11403100102d0781c0d900c0010012030703000e951442c0508006205001400005400403820b01c0d4958550082c9414000d01143c116490700c1070001802503127010300180ea0490381c01c40c103800305c1c00310300680c04240c4508440d0341803100d042725805044041d15074000c001c00341c05403641c045d0300e914140d20040c04031000f50b04201d02c20350052008082681e125025146805072040c00703d501c0e44025240c141511040750417104031031704007100308810260702070040b0540034016002031265031a00510315003280c9078205c011240340c100300e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600939280 1250 600938030 600938047
    0xd03030e0f15040b090f01090c0501030612030c03050a03020714071d091c050909090a03021608030f09030a0f03050d150b030601180f0e06100201060b07030f0e0405011206110f 77
    0x811130307944001c200f82074030f104102c0402014211800c02c1c0302140d40706001a41407029591520425000d000d440e2842c0c8605001c83d100904000560780009040050011364100403920940540d002a644024190624008204c846845003180c1c000d00c0c4128041c594400240da1241030050700030a800c0c1d001e8240059048211288074a8400700c01c0705026041000ca00b10752101c04030580306040c82d001070310341c620143c40d0007420b14110f800390303500c0c521580303074144180d5502200300c034004142403521039a0303462410040781c14140c0e940c1c0302a010718a03000d0300b9004e140d0000001c1141c190100c10800050704101601c1b8000c801074020926000402d00001d0590f50060140c00c1d1044400719208841550350740c041c07400034805402c000300c0010981d06204803420044500080b0202c0c40c00240255030401c001d01d0054012464041d04120014184041c001c6c01170b15248003400300684140165a114142c03611201444a01243e44619200c029141040118155841030b1004a449442c3c81c005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600940530 1250 600939280 600939293
    0x70b06030f03302514190f0e010f0c020a090c02061603110406030914030c1e03091f0c0b2508100501030b1201060608040b09010608030a1202090d03030e0f1504 70
    0x40c0307541c130034001003009000f06443c40201411107001c200f10440c07400465450028510090700d4004810302c962811010300c240e030491149a080c502c18501030b01c044c000b900000f54600c4156015011003441d058280000c00e5010851034414404c0f030035440c07450210080c0c120200c3d010708681840030b00b4144001c0c8802d512a42003009407038088c404ca080580244840c0c02e045602900d141d030600d92003404148001480c581c00b445805003004007941c1401c0648011580000c840001c406400301d041c18a04440c50113214445070007904410308200798544640d81d00110076010f06201d0381300000b841901000b5104810f100c1c42151420b8841320010320385001540504411240a0351005000710901281c540900c41c1c200241f10781d560303500142c24182000400108050680003003a410400180402d420003c102c486504503807419204040c401032005000b40901c042060b4400d4003400341009050b03064004130103c070030003c169090300e102e02d6015596005002605000c07401440c0000307010a50703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600941780 1250 600940530 600940591
    0x60a0b0301150801020301140f090601110a1401060617100b0a030603051b12030c03031f091b1808060a09110612040512070206070b06030f0330 63
    0x2010340046036940b00b20004015140240d04206466035003c001009501b15645d2041c06000082d10b01c81d1040c007d0703202040780208003e128506000c1d00c0038908000746010007420b14500d070840082c28180718401c19180c041c000c244103046c002901c04507240c17041086109003900443d00c01c00080f40341450103000c1c8116810101103581495500c400c0000860f005000414030083c9402085103400407290421200f0902e80d1010301c200d80c8140000103510900004503a003096601c040c3e0000da800b0001c0d030041141003500700d40e01460802213000385280340b0340030010642c8040d4a03803a80540c20990058640c06640c4901c24007940043c011a00703d85080c3d104a405501441603980e44e82d0482c0c010461980c0800049040f540d08035003000103000c82031048803401003000c80c01c185041029000250180120f81c000b4140e00c030414046611540d04020035030000d005807056a80710340e1117000f10b100034441c10f0324040c8584840101c245980a0f5501c11074801c0c107080d104074241e101040c401d00a00700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600943030 1250 600941780 600941801
    0x90e0d0c0c0b0a08060301230a050a091709030615010f0507050304030c0f081005100509091f020c06100803070b0a0b130f0c2c041d070e090f060a 64
    0x86010001080c0c05030b20000420307400c450fa032103543d02070514105160845044000f03184034070444510503070b034031a2a41c20298001000603004074594030750442c090000c1c80d907550010052404190301a051a044802410840200720140d900550703a2081540c070306484034070b109000880e4104140300c0d043c054006004100c0c01081101e0601f1380700e0b40c810305403801a8000c1440d103000d40a040206080420101842441a5034188450305102c000003003562600d00580b48680050b40c00501e040c0000c02185002e080303410240d42d0000c2c031a655000c001d502c1103045d11518000e07440000c9901440f075084408070351803d0700661a040c52034596044001003d04881c0b00c09850f0345040700aa0758500c9080e041000803000003624030b071311b240607501300c941840f840000e01c00d180e13941281c10054609080400400320003015021006c003800940103040c141c0c8004c9800e03070340e1500506585000101401603c0c07880d41c516890742c03a840e00c0d02d541d84045d2030900d05a54041e0b800a0b0b07070214690800000310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600944280 1250 600943030 600943043
    0x9050a1a04020a0c06150f08010e1b120715091e1a04030f29061e0102010902040504140601050102120315040b120d122f070c030803040c090e0d0c 64
    0x9100345c1da10005e4601c83c040714000b1100642d802d2240d0b901da079103080020040000200b00d000c9594541c203456805d04506068000d09120781000310f0703183c1018100b140788400b0165221261240d10b00036501d07568990080014040c2140454807014a0070000c00c045140707884200c105d0328202c4400910402018510700c114000d00c0300000003642c0c0014406d01c60300c51040344030b007103c44229800303551480a03a04a2021010010f0060540b43d0842c07a2944004066182e024180d01c040141d0241c03c7c0c050000303400c98a01010001888017686d1586429100001590456669031004990310928031900703103041032003000800c2c1c0c20403407109603019040002d8804140000c40c1c00000f00030003c4000c9050781034000c2000c0441859005c50320002c0d8012150081100c3c082c07440701d03400f042030f90306104091081c1078107500e08181000c10aa4681c0796108014800e4607450b031130030300501d4106680440d0100040840424074040d0341c050720904005000060030752110304602110200840001603884 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600945530 1250 600944280 600944297
    0x110103060b13030203160e040f030306080304060c020a050109030b1503010f0609020306130c0c0305030415050c07110103050c030f040f0605090f1903020706050d18030909050a1a04020a 81
    0x18400c1210260070790348445281002d4461950052500b000203018103401c4101d030001003404001a20a40340d0b0300309400c100c00d00c40d44040c618040e001440d05420110003440040303000501c040d4400c200e282c110340300b511402c3da560340d1140151152103160000400d08440c04000501001e408407004000c0500100003051800041861504640362074008400342c0e034000007003000720b00380b19214100d402c444020400c203071000500014210388015030300804000001000c6030500c000c1c3d40c6001007100c4048410000c905280141c80b4940c0d01032030040301d10204401244440d580a44103071031003a11148c481c9407a40d510f00c10400301c0e40310000c008549500700005524003250031803262521a600581c014008500d0f0f001c2014a00030000b034038451400703110505040001e60102e2001e045410b2418899185c1a1200344a0080c00c02c0b410f000c9001c07041101e6400a2540c84981d403003c64660001c204090b88a015401d4155000003a075410003034209489580c1608141d4010a810070b030707a2506012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600946780 1250 600945530 600945539
    0x313030e06031509040321061403060108030912030915040807060207150509040f06061206050a2d080f0607110a03090308030702030909010308042409030f170309010507031d0a11010306 81
    0x785083c11f035003001e45540c4182c14403058035041c46c40800d0b03120880090405600d041016540ca2140c00035040c0686400300211150f00c0342041550103411004100515220301c03444c225409030058451409903206140000658900100d206402c1d43c4000304481808034500405481613401491000d4006171f6940009003104024811000581013513943e8030241340341071111005480c00760300100e200d071072910b5081000403000d10140c1c243c080000c1403200c520f0000207a10014001079072100380b06016480503c1040300010031000d11a000da0307201c185511503100c0c1d40e1039955009078002408034039024403d2010844c00d102841e0b0211607031040303e20303000481000c16032140742030384121860f0b4004282808a00d0012264078000d05156140500074408800010071b1240c4a00c80600341024503440402401841c941e48a40102c000e00e4807036032801c0c42c40006000703150455074403000919000950320192001907110744040450320003480814503540311451505035150480d414195900c10015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600948030 1250 600946780 600946817
    0x160810121716030f030e1005040606050a0b0901031b2025030b0901050c0d0b040b06031501030501170714061917010906050a0303080403140313030e060315090403 71
    0x440254103800040d6042d0030315014008a0042d00110141070400b001079580034030000b120040005180004100c545480c140780000306025001507800c40c0d070382007000c551011032800a100c1c0d03017000e076400c201c40280b103070f001c2000c00c001da10000c001600b070504071800b480d01c803800d0742d400314192026120001d00200880304401c454808900a029180300100203008640c40441e5114524400a1005140440c020915881040a690881540c81c4120a030646544d4041180400c01822a55407800c00c00d40000c07801101951003030009062000100700089201ba0900c242d5051400401c2c15600f0310080d01054141010300c01d4110105020812440c1201c64000b5240f021980b10500440c510600290801c0c41c140c0000401606081003005191500030406040300d426240c11600c9407a1403400f1205808401c45980d0316030004000d102d0742e010422401e0441602c07e071586620b044040d01804480e0004940c801602105592188124100101040d40c068428035065101c01a09407601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600949280 1250 600948030 600948037
    0xb060402040506390f100204050904150207080711090a0614010f02010905030301030605040c060507020a09020c0c0d06050a0608011a12070807090f0609020c0703020f060c07030b1608101217 83
    0x2210998481d8108040d4014240306d95828840c040c01c0941c41d09040c100860404031018000170403412070b0030205080802d4641c19152610340c048a0b0300e642e500b007810201305814442d00c3d018820350b0104003049404a4510624048035054558104403246140064401e001010b03908000c0d9500c6045090004009000840c0030314456400050982882e0030509201c007648d41000003488020423001d00541e40301c85c040e80440d00c0854015964000f281102810840c06048091300700417541c040000700306117600074600c2071211090400c40543d0720450b06013654507020403110300780070342443c55416061a1444c01c40d601c480b282110f071401d81d10340d140e610388400c0e030340200f0909556442c52181c0039500d0081c04014403c000f810b40c2020a42c0015585405040c40028411090101d075410180c54101c2501d050031048419100641c3e83c9003029403001408991900000b1031840c0964005400b41007090300410107a00c1340c0503507904140c00038043c0ca1682c441619a00e080f4800c2a80da40c240710000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600950530 1250 600949280 600949387
    0x10e13270b0f06030a0f0b180a0c081002040f0b090402090607050d0e0d0b150f040906050a150b030a09030212070f1208070e010e0a090510030b060402040506 69
    0x550345500d09007142e0040440040c00091180d0440702446001c103952007100c0e044075400010040550702e900192515013801c8003580d928a00803041400240300d41d0340a00760444061100341c403001180010b001003240300d01d000c1c9014000c200c441c00c0c020f041070000a043c1101001e400140f0781400f9000048250b000420f00f00c0d0f1035805122210441548008281d000030400c0d20006101c0f0826907c100c034264000305182c00005400b2080d5540740e640010409080d0380241040060880758100000035160480d08074600f1420041442001c04081030031100702c821400e00e6500f583c0f20b0080c000c019200040c1c0540c00c5105030301e010500c80106000070704040384505100c0032500c109107010304804440300d99034414000d60004110340740d604590340303d000c54802d10b04030b20403001282c00580403c41540121810600e40030403c980e00d084007240800703807402191003c010380d030303003034100002d901c80d070301a594220030240407080381010032602007842d03036062079150300e00305920b001d80c4a0302c2d0300030305003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600951780 1250 600950530 600950543
    0x2030f2205150d0c0302120f040507050a06020a1112030901080a0b1302120f0705030a240816270903050702100f0f0201062303030c03030123010e1327 66
    0x985100803c45403007910340741900c6050030750030a228a0b0402c0703842c0300003e2408208408160002c2c0c04c001050026030050000100421038040d16514001d645080b410700c2180c03c082c00030b0505c00c5038604503048800301c1e503880c00150b10300f00c4003500450740901d026016840e5030fa2503c203408016074849003191880d00040c04011f80303803062080340f0010030340c000d481075141401c0c0d00305012410350b104089076440380501c100442c8070340c150602d00e89145c0c055508400055442000490841c00c013050301082c174080c803c0100c2c51240c0340c18110b04010742150a400c001c0941c0244c0365041c41494102e48080c2e40241046030800b8101e402164141550b1040c000c0090300741445081e008c3d4002250118008503840200500790411032014280040906807003400c68101c41c031400d8a590030022100c06a800300140c9440e941d40e65810b81c2038194124012283c00261100e01419510401003103030b000c00010700d02520700b10089a12070013001007030108070038007000620500c0c1c1c1086486c01c09118511944 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600953030 1250 600951780 600951787
    0x5031f15091b0e0609010c02040e0304180207030315060203180a0b220f050312072118120519060f02070b18030a090605090103141501090602030f220515 67
    0x24801401c110240c4240b41c410131050040402d6a40c4c01002134003a10740c141e40004d20303089011180b40c95400307554007003e0903486161034100a444290040d0140c41d200e40c90070300c61000c1c41c040600881605009007401603100303110454000c0d51042e422001c10030081d2580c01480d40716421100030754003014000e0302880300841c40710000e4001142100c0145940b441d5042201e05040c006030715082c204440406072100480d118090019000c89040300210790001215103e80111000d07244804840340080004804040000c0b40310b0050211070101d607000002d031000880d8210000205041d260045e10029a2400c10418400300c4d40b00a0132900d004035242411407070414411b2140500c6044080e000b90030610030208041e4011140006941060030b1050700c4032540310040b4006c048558110399569656010700c0345e0700c1c841140c0001308920030f03031300d5541c000d8035000306a0b500c3c4640c030011500d064041040c1002148809920b0b50f4442c5040800b54095039200009030364101c130000340c1c00d40c20a001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600954280 1250 600953030 600953081
    0x1e0a0e131d120706050c090a080f0d0c021f0e2805102c061303120e0901060f0c080307021f090210050f130b090a05031f1509 55
    0x806015074510006001001581144211086140070701040100b400b5103074004507a130010f03c1c4058841e0384034040c0c01440e803599540156990341e095125520303000e01901080503001742c4984c50394003466401a03e403049244c12008e20303424180c500c45100040016880001c0030591b120081040002c50780d1b013800210020b10581886161042c1e800b9900c111452501c080001e0b400400b81c40c10b142484c9050f40200980c10b22031200b0100d1151043c0c0e003d1303000500b040300b80e41860252811b807400f9400d505030b440c0e0060700540304075200107010355010441c41d004000742c40c802d096090b002c2245180c4501e00c1c84160b0766503642900f056881c0000340c1c0000030155826921041002d80d90158140c051011483d680c0200b4660781c0102001004c225000030401c68040704d5208440c3d80e000c0e00d20030803c4240e81c1f00075030392403900310b00c1240d8462211000b00144620b00041d034020f4034410b0304889007002140c0e08001c001000301e019000500e902c02d031f800043d19242c0340f050042c41d08825800d424040d420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600955530 1250 600954280 600954311
    0xa060c030e070b070506220609050703200306160e092a04060806060a1106040b06040f14060d0c05031f060e070813030203160305071401021e0a0e13 65
    0x303070080c00035000181304040204e0b80000300d0035084284d0140c0181603009800700302075900020380740945014144039030768040120020f102401c0760b00806015218140302189501e01002d40407071664903a01c00c40c00301d0600101040c1050ba004002d04003070700c81c83c24003000b03d24404821511892000c564a02010403407010000796102080c8404550f4986400c00d01c001e0803a44029003010702131040031409031100c2c3d000c0d00303019401c100710301c0481c0e01c540741500d024002c0f080d0031101c45004908200061010540c00c3c0121065900701502503140c0b07980c0d0905214551036804000c0d140c40e4015a4009501d407414031038040580d017001d45004c20a11460012400e9404590100d03400200403010441c01c07a40c000c1c10550405003a10503401d0980903402c08130310b54041d84040602d1103207040000f104050b041002030070168481e08414142c6030784a21107500f00c0c014428100425029001c2c10041c0c001600300628603a800760600003442120b11002ca03692100b51640000e0385e541c0c600840c075060702c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600956780 1250 600955530 600955543
    0x30606051915020a0f050c01180602031c02041a270a0b0a090306060807061107050303070b0a06031e021905011b150911100203090607020f030a060c030e 67
    0x101a151400c000e01035440140408400e071082e440200d52881011080c00d10a0054022003078000c000c140b0308141d5424100c1d11340050800701404078031201c8803c404900c9105200e0119642500518109054602c01d8070005c112032141e180e4440c2d0800004c1030480740e1640400448146102281d10344c019883c06a00c0302852080700d41d042c0b104802905007036542c94410005840c0102c0700203846407010701d01503803040b40d203400084c01c1d1401c7c070101188007400060101e00301c074003d603a911400c10000e0b41039900d03014035001d0b66801d0307003040203d00c010520b1181119003110210f01c00107403040d600d4881585600040d000021030510f0050f06200391724100c81d1007480751520504100c49540340030000780104c00c581c0d15451141c0c039483c100e2414040c0605011100b01100d88040c040c140ca18a0b02c1020313036001c00420740c40b070380d1515103140c9918400000e44a080701c01400721841c008458003086031060311440e40702c3e4035109808980780054064081c0001500150701d011502408403003140e4140cc0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600958030 1250 600956780 600956789
    0x3050d0903020603010b09040b0901350601060e150c01060906090c0c2301050408030109111603051b0a0b040203190308060609010e0a08030c07050607031205090102160804030606 78
    0x40300014800369480c4000c49044589244849a49078440808100500b43e2540b41541c4801001c1c00014405840c11170404140c61107012921808080f41107004000110b4000300c142c0e40c814401800a2405100c0840c2c40040081080014074075090301100b407540800702044850b51940b9080003080310300c0c0607440140080400500208650820080804156a10280c0600c01d038550000d168000304d407010200e030510b00c0c0240900c1c0b07881e042c000c2c146c0d4000e00c1084410341c079001c1e416501301e00c090194cca45114454041071501d030b00b900e08540e01c0d00800b5100c2004140c0140112014808200788101a0b100d40c003003034214a440d0040605142056050240c010400c08074000080e50010320107034402411904552a07a41c0700c00121307940c0215448191f0800031586000c9110000000600b040c00724400454001d540c5070000c1c801d07540209040140481d406403001c00c0c17000c20540149030f003d080030000606000d6050307144641b10258a400f91500000040c00b4828400c1d980034080c05070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600959280 1250 600958030 600958037
    0x7030606060810061b060f060b120a0504020306040f06021201081f0501080c0103022d0c0607090e04082b0f0e030703050412080f0f12090a0818040207051603050d 71
    0x140d1a088005e8940c1c8401c0201c0402e19540c07615400c10071055900124030318202e008200411900c0d6041c54085d94082c81a510b02920858001040d1561a0240320b2061340c0c043d01074005902c1d1513030350b0348140740e04907000c40b0041d40901c0070a0117a00e82012860080100d00b008140810030300c60040d401d00302c12809440303c0c0c0d08220040c4480840040e080256842c01c1c81c0041c2c6d200441d0720600101004000307100c2c2c40ca03d40110316400b1200c4540503180d80c100e180161421500d61550a44010109105040304c002c1090002004a240c000240900c0c6480341c24a00d203105001264500d00d4600700b20fa034450741c1d03480c0203500c404440c500c00c2420381d9661038003c0d4900301d02c40c2c60281c441c0c0101d101d130190825410488000f080b22071815207c0200f80b149440340c03100d0714441c0504450300400c0d101070403c0d80303042c0000c0d0703100d800082800000c0e42201c0c42c9480e1001c0c40304907110b503121000070306404c41d800b00100e0700094000c029100c16083c0400e410f010341070940c03400e10b041005900050080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600960530 1250 600959280 600959311
    0x9050f03160501050a0912030c0215030411060714060702060711150a09020d0f080301141f05130e01150809070308120604091a190903020c04091103070306060608 71
    0x4481d40d010800660701c007400d20741d40b0307003101c044100d800d07041e03c2e0403456850201880c080101608141589001842160f0490f20420b20000e4080700f400220b401402408401c008030100f42481e05c000c20702c081c041c08101e0400074199004134907002065803040010380c00001000010b0368805c028048852001014090f042e1071414a880d0140002d40b503801c2d035640d03445a00c01103548a0b90100d20307256016021051040b00c40c02e208545030024800e0704d50402d0290ba0f00c04c95403402403030050b1140450040f2415400c0600c034112050380080c00b10385085d140b00742c000f00701d4407108800b560003091803084100c1c0841404074020180e040180401c4180c1d1b02401c010720005050200b03841c00860898110821aa5140005406130842100c042c01e011040c80108425081c542c1a0310b11415000545031100009500050112044c81d400500142c200c00030321a0b851500d1782040c1506809400707002c0a80441900007401e20303805a000300c130b0b425038030401080019080700c0901e511544103c05000d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600961780 1250 600960530 600960553
    0x3041e0803192606100504031a0103060c0306050319050c031b100f0804030f03110301080c09090d051602040b04020a05030a0c180608071101060f0306060b21090f0d09050f03 76
    0x10a001c050413152003455280d00301181c284c0310300c0544004581107080300d240314003030021030201c158003800141d40c018109840c4030903142c024020310080300c0b00940100030301c040c081c4031048401d0f4682c01c2280e090245c00c0748a030066808202c6c884150302000d104560f003410420420107117090845605062242840801a10b55001a00c00340d00640605040c210b040c680d0b03408600928081c3c2d840d42da440008800030401400010380d0074540d030401e403146035042d168540015510311800301c1c1e41001550400c008402006281c801d0030b125480508003003150100c51001405071b03000107001000103800402002044c80590080032501c04c89410302d000c040000300388003004c0f541c05004034814041e86402007070445118441c030b4140da01c4503100030490661129103030700c00c4c2c1c0c95510042c0c4946042c2003000c14400048000c40d03c040340a1007540c40f082c00c2c04204202c4485000b4800c1c0f1245c0505045040d0f13220042c408100d80c0307205659035282c10b0382842c0400c840e01c203030448098000d070300c007040681 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600963030 1250 600961780 600961847
    0x114030319020114070905040e010e0c0f0310140610030b031207021c0506190501290d0e031c02071a06030703020301390203041e080319 60
    0x410840381c24081e41600841c01d4401e81c050240c4181c000c404054200400c44081d6010500c0020781c0c004070b40c28490456180e4849081c1d03041c3c030001031450341111100c20306526000c070f9042800c26028044c0d4000801d80010b400440c3e03201a00c61010510308400c0010504c1c0c00840c0c0107016640c0e040400201030300b0b40206e03545034411380300c3d9001c6080014121003135503682000818004e1030030b401c41003012001c1c6091519903900b51200d048051811141501a44003030003043e042c1c44601d0043c0c1107030001070401e01c03c046000b802d41d0011034070801c50007550080342e00400012540d5074006583d0762220400030401c1d0301c50500100da0780342c4103112010000701c4c01d064141001c2c1c0848800c00842c1c943e94006800d09503140c0c0025403640c45d01403100b50440e5508402021500020000e40d600f441803038072100a80c24441020300140c10070401400041c582201c55040c100c1401c680c00c0689440300c90152031036112803c80e44240541b40006040164010445080008020343c00210011f01c0c24109 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600964280 1250 600963030 600963037
    0x7080103080f0c060a0b010206090d122c01020c0c2b081b1506031c0315050a14030c010e03030a210c170f0c0d180501020307050d0501140303 62
    0x410220000804002c400d05030741c203454000400308199200c0741400880c000c001c211014032075016001b0300d00059484400031a900a5508440c0c6810388034000c04c2d122000101a02c820392209160420b880090b0304030714503507004858220400040e0b039141c42c109210716180c4502450380c49000c2d5042c101d10700240300540c03122400d4030601c0741c100020240c60a44003500078000d10701080f00300001c508500c0403001035051102c803e0035800414a07202ca0701455120b9174605c44c164810080d051180f001c0d60310a6100b1003c80c2d45141058000648903800160032000c254440031701303100c0c022290042c07482c2c01d00c180c8003a002c003400c1214048070782c0c00c0031030344030700881c084003042c40000f171318940010b403100300402400400160100042103a203a000703048800140003800d1111018000900301d140e90308003003030040380c045030030030306003081c05a194000d0700c1301981220103411410310140000d02c0034000745005a00719101e00d038481215680136000c45105a1043d60b442001c9458110b241e00d012044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600965530 1250 600964280 600964283
    0xf0f151802120124031104062607150801060305280e0c062208030a090905071704030305010918080708130e0f4c08060108030405120607080103 63
    0x2c1c0075280740300c55409004004070100c0d010384903c00082c10310340204191041040d40d2164414030034402034a02880116065806003400680c00307003c060f66050300b0683c4007804880340c581196401622040b03503182c1c64180712030240c08902154014008542c260140e540d100d00e20100360754008100c00d142900e86e60a0152404c06542e40791108110603405201c51001d4000c05021140e54000d039510071448400e80c0c02114281d08108400070401d807c000c811104014926230394a192a82040024030041802400d91801c0c8280300841602e1450a01480b83c0b04901903140081c0d0341d0700d4807007a04155040302062680000522030160001244041680c031400e40040303071240c0b1062160815200122140c100045091041c1d08004581c101608447e01c251041c5101b04102030003c0200d042ca2000d008608000151021035035401c40d41485881c0300160020303c0a42c82196100c040700d081c01c0003030b045102207401c002424040b81c100b6a100c4202c03010084010089441c102d1401002400d06020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600966780 1250 600965530 600965539
    0x7090501030b09011505040906080709061a030c090607060903120507020726120c1006050901180b0402090a08060411060301081906140106020d090510140c0a0f0f151802 74
    0xf21000010301c06e00940b0701400c4c80c2c050030808030b0b8039402480d50302c2c40c0311b04c07419600c01d0800d50003140b1003250b8a0080a1f246c40307005041c1c11515401c10703603c40c50b0401c0120308e8102d1401d009060220b4494042c0e240b01500944954042194900c0040c041e41d200410201c10345d03118140810101038000c15982c496001003000c0c0c00003c0303042d4082410b01544200350309181c200829491255800802d40254110207000100070090341c5038203112026200f48a10540f03e58081440454413030181c015002e1184020300041c50a031190001a811140b95080071240b9400502044100b01014a03401c8402c44126513040c00d41d0314240d030b441e65450002d02050510b2024401510800c41940c01100a000c130b0003056035020743c0c407400004d607544051a40c0d0400202c01d01000109070501c1c0280403401c3d02c182e5104951890ba0340910105607010050f074114078410075a04c0b07400701e42000010310f41c3c10b120741c481c1241e03c074142c00d00b10407044503581c811b80c01900d0070700301d100c07400c040c6420302c0c00003039064070b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600968030 1250 600966780 600966809
    0x50106021906060f0e0916030c05130f05090c03060f0c09100912060e0d1404120807150209010f020706090e0c070c060302031b09030d11030418020307090501030b0901 73
    0xc2d045026000950045140b00d000b010041482c140c4244c496114030001d00440748840e0f0300d1701d13100300041103034072000c2c1c020150850140705038100141d0068400b03040b00804200c0400c0c81d0f0780c00301141e1003102c020265411084a1040c0e62030203000c00c94012008200780800c0d410031a040b03c0f01e03481049403440c419031450014001e09030091100c88010000a034a903600302c052410002c010301480401e000b1a030141d01e0103d84800d005403100b24000040030716682c101030074083c289220040a2400342d0718502c060004070000b40700792010741e40307484d40c0580260b01c60304948009031400355003800d40300940d00300010521049070b22441150480f0081070451b4400e0b00c0b405541021442840c0c0e001e80718201e078041c041031441d0036800650145408e0094243e450705102c078107003014041c00d00d03031940c1074102030050700405100f03520700a800c01181040d0b9107059a102c10709910300c003d01406159107a000b10030485010382001112004203401e007001e00030807495200240400c1c4050188100024004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600969280 1250 600968030 600968033
    0x60a172e0e060409030c05061003111c0809041d100b09150103050406090f060603170f0f0304080405031605040b09160c0606050a0f091b050a051623100501060219 71
    0x107452a1b403102c2d0700601500c80c1401d280e1003003507080056000c1a54108006041c0903481e09120000368681441c10780b00062032600c03681d686040307a02809007654070a84851404048684104400c0440444900140704410155201900750380d482d81c03506100e03141d10380420000d1140440c1c18100e403142482d00040c3d540d42d03880d08400a0101103005090f01004070551810414aa4491004d0782d004401d00108225005001489803064102400042c201804400e5488283c64017660b04144600c04090a003901c0d500801d1501c5a2a4848880d03407104040c200514100f61140c1d01e0b800c2700640b8052042d290601e40c1c000d107401402035500400210001c100c0500c02c1d181d00c03c001800009050030020f590380c081000383c16480340500d403800c61910f040071600b11030101007040017001c161161410100740d090b082e81c854008014002d44924160030150020300845041c000101c00b0405038005211100607040c50581d0010007803050030325007030050010680016203180010500c115404e101c1c0d020b07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600970530 1250 600969280 600969287
    0x1903030b0310050a0504030e033c030f0301090f0b01140306120f0c03010f090209010e09011b050c0d140405040f110309010b01110c0105030105060a172e0e06040903 72
    0x2562010060500c3c2000740f024552607600b009019501940e180607080007030204158a42c0001000100c1e5140340c4183e42c90801c8801d07038002c05000d240c010700d0101038000c0c00710a0079540594420300e01410b00100500146019100d80f0049008640e803c00c85401c00b100040c211400c4488001c460700e41c0440015150740d40c0031204040c2a8140c01a600030213007003100281d80e44001c009980c03003942440716120006400e0b1060000080c5c00800340e07440c59180050f02c0d65645c40c0900310820039521081300d403014501030f08940400064aa1b42d1a60f911410944542803800d000301c0b030010020b004110002041d03004090703e05175501120001500c640e550030700700c010104424004c0203800040100010303480706504c86003902100384c9444001481c24070400d500c90500041c1280803034010310062219080010161039090950f061201c0c102c0c517903440c907001d1240200c0758120701030192801d240c440305841c01e50007450490544c42d00b0050b424050249141580140254003a550b1140000b0030f0510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600971780 1250 600970530 600970543
    0x703020304211718010305040206040909080d0e070e0c0a080105010305060f1c03030b180f0414012417061f0302090a0203011a0f03040312060510020106030c081903030b03 75
    0xe11441d6002c3c0e40c400620b030340c94180c020079030442a409101201e43d40740c1d40280282032045600a1040d807416040110b4a0000c0c44ca071030095400d500706000ca807e00c0907145c461401e000847c9402040300c035240c03080100d0040801040b001c020402403094a80180d0010800e03410368400742008105503461760701085d42c08020321f8940345e0050102000300b840c0010903c00d9174a40c0d000c0d0b0703018004582c0c0c400c1030082e003050902d001c4000a0b243d400155401052110300f40d00244100001d1341402001c03000c440c20341d5588010042030b121421461141d9421250010004066650040d440145214041a140c0da1300800000c03250343e001504010030810500142c0103181c0c02000f03240c450402050340d00094000340600020210001c0c0c01100e14500c060070b60310070804071020685180e60300c0c0e0303003240c02c2c4001800c003591107506d5001c00314003540e6400142c100781d90b4950000480b545181840402040607034001c095581210002e84810000603071100121900f5050110f543d00c0d082012915211 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600973030 1250 600971780 600971783
    0xc130923030f041805010906030b0a11040b0d0b280b3108010b0603060f01030b03071a0a0824190f0b0405090a1518140f04050d05070302030421 63
    0xc80000d0b010860ba14104585291303059100010089a0b80742e101c00001c49010f070101410080441c40001c5116200d0341081f0100d50b20001c140781043d90742c8201022036080103d0700c603581611400078800f00d00344448014651000300e080da0400c55188000c000e50040c1d240203019104030005001e0104030b4484840004004154081003c0c0c41c0e40e4024030741e01e1202a0148444035400d02010341054500041a02e008040060051107251100340042d8028500303907480d40c1d09400b81c1ca00006091015000120f026224190070710b40d038411408d001050400d0040c10501d440381400d46c0e8200481440d0302041009200703030b0305810300401d00b1100d61901d040300d0323110000038401f1907004101c0c140400082c004072842039901c081c2603110303440207805440c0328240303410040c482c1020400c450004a5007215001030300060008070144014030640400c1401c840340c91f41c03100d5041c1840100b0404100d49006941c440c9099820000180d0700291644124490404040f441028407200050040750001800e03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600974280 1250 600973030 600973057
    0xe0c07051e161215020c0f0f06011d01080318011e091d060d080d020409050414280f021203120703200403020d08070803090c13092303 59
    0x840c900d4680360b5942d0400804150b094246100082c4800c07400c04122016038090f400b0b03140c140c15244404000c0d0082e211146492003002810710902005104c020b1a042540c00034008070341c10710308582d0021078030310362071060a00c90350010803140402005540441150514584410114000403a0036021a118061010f01080c0518403c0740c4c104103242c003113500c2603042544070060014400b8602400b01e80f000d820099041031080041c10003c010499086003500040c28907448a103960221032080b242200c8544680f00c01600040d010084000303a148864540400010704400c11501c5010f454170041c10030941540303038003c41d51024a02071505441c00c08581c2c403141c03804403550100d04181c54402c0071a280421400c2006100c46d118035081c2241d0044918151840d824461407400020041c3d54680c414000d150026001000550081c2d403014000c0c007051418404204050420300c5075a205035180160446c00110b032000006800c64810360a0503807115403088070381c21132241a0007070560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600975530 1250 600974280 600974323
    0x80901090315060e0c070f03080406020c0106060c052503060e010b040903030b042703080405010b120a0b0c040f090c090b0a031406180c030705090a03080d150e0c0705 73
    0xc000c180d5200c80304607007504d402c2403843d85a5417140000d5100341c000141c2041c84000340200840d0003001c110346c00c0391050750f00602d040441c00c80d05003100e42030341280d00020510150300b81070180401801504800701400402c07030070300d8000b5116070842070748002441652564050b80c210340c4203600034118800301400920081d4964900100207050500000748140e02e840b296695200c070482160040450b8540c00c0c0c01425800c0d1000d44802c10002c1080311199240c46841c501f58a800301c50f806e228491100030143c4014038640020900c00080c403a010049041c001008071030f260050b504100c440e281000203801840c0c1d0310894004815070007000d84040002900200b5982c16401074188150804c00e20626403658401c02500e080b1106022039004500d03400b103010009004000e41e00003803981070061070a4488401f04101121070303403043c1d4103604007041c2c21031404400d0103950303c001d8801603049a810708000f81928400c4010702141d10008022400c1000c211080010f0304001c0950884440d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600976780 1250 600975530 600975563
    0x31809020304060e0a05031e04030f08070201080109020306100c02010201020d14011a0702060a0f170a09062406030c0201110c03131d13020a0306090515070f0503040809010903 77
    0x41c0d4020341d0110340d41860b2810301c00300c81a000c660014540e038018091450640d18900808401c9a64a0b01d9403420310708010010016003080c0c44402c00901ca656131944030f000c140005400e10b50140c0c410540340340100100315017a907864611b41c15841042c1400e030600f0681c0c2c00100e009015503060350300040c0c0303080300320340e044681c1e147c3d820304880c1d0506020801d0200300940c41c1d003500586000942001e810710680c680903000358022845117565162200000034001c1c2c60351006d105c151a5155016502da85c0070050003030340c1c006d4072111810091052800f005a1062880b2600390340700d003104151351070480d1201c2900c07e40181050111064085448402682c0c059071a9800030b04440c442c115584c100051f00501144c98000030340c02e12a0705000b580d20108511098200c0744d5040f039211010310030100010300c10b8418048058042c0004180258040f04040307103c01c005000d80f4140315a4504542c00c950b48501200d5002d0380c800c01f81c40d22217004900513035050f40d1640008001c1c4241060041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600978030 1250 600976780 600976799
    0xc020a11061b0607080114030a0818040209060a080403030606141e041502010e0d17040f021503180706091a09030a05073b22050d0e0906030106140d0318 67
    0x2e050b40d41201c0c80322171f8944080c042580c0c0304c80f090710040c20b407082400340c3d402011049050160030500500051314100a060000d100e503480810310707002084ca0f102c00d0100b8140c1c14410000600511304200c1400c0c0d072401041c40741c5d0300550a400d101094031070707160701c2240070b0721040d58003d000b20400000d607041803080103130207003003041c004403c0b80c400d040b002d860040c0300340c41001d0b80820501b0502002e80b40e5031070b0340c8035110348400240d801810741d46c2e095980303c0800009600c10800d1580501d005208003080a0500040e9484030007008000d240c14484420742d046141e002c802a40352403035a0b40150340210781044542403015200307005640c0001a94001704892005407850740d0010440501800c09814040f04500c0003285804d07600000541c01c07a510541402840300034600c90605103100c1e9580b00d282107460146400010b0700340e0071070710807814200b04558110340100c000f400840d007007110f40d020340c10000000500c02e8a840c01d00b0b906240c0a800b141c00040340c500e42000605840e0710010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600979280 1250 600978030 600978047
    0x301050c0901122c0c0d0308061e13021e130602060a02041202011413170c091306051902030412080a1b0e1c0b0a0c020a11061b0607 58
    0x10b80440c1c2c035080785114505181c401c940c0b50403160101030107152010142e50042c3d00701d001058584c0d11800d503000c2044d681c1d42c1100c1c03c04074070969802101f481c101050240111200082c1058103a2640392522155031f451418200e20328a040c005803102c5000b0b420b40303e102c020307146061040c03400140401c15050903155020a56a00e50211115900c400f58514128480d0348100f006403180260040010740c402c06401e115480b041001d1804e00d4204d1115410807145907110499403040c3c075010449040c1c0601c50300030000f070200c40c40200c903d82101840070408002c20024000d945e2000040c0b4048001440082a21040c0704210f459151510708107103000070100c07040001c11404000204c450304540203140d00c1c14480780e00c0200004100900780d80c07000c0503c14040d404000d106401190000004c01020258061141e514280c18070904a004070780303000c0101c0c002c5401a98410000c1a20301c2c4421000c0c0c00c040c0e802d02c1e61004914400b04c59222640c40340022400b5030390600c210f456004100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600980530 1250 600979280 600979297
    0xa05070305010509010e01090c03020909100303090b0a05040b07030c0b040f020a0e01080a140304050409060902040606050f030705070302030d14100509160c05191b09060e240301050c 80
    0x800ca640d80b5402013140100d401d1207415415020f000c01444107c82130b4204500a9496040150600212000085615004035058960b550750f04008205041d4089540b0000b0034030886650300c4c000b02203500500510882c050a0702403000040c81c2001c05200f070203090141500040d020b4001e09003880e002400c0125208240c0c8100344811002c28070f400b02a6442d8100d801c03400003486242c00d03a03034800769081800204c130820f50009100005040e01d880c00b8003000d4920800c0001a0082079104000440d42e00781c2150042180521007040088041d408036501305140c4d0401d00d40f40c46c82450100e14610890702d118075071070b081000514651489918141c010035203020b0210160780c0324414400c840004481203c003070311002c0f41188d6642c1c09141100042402041600c025203803d12141000110420307044078080110f00401100200d15100280a480b0b2188244011032800122105902002c1d100030000445100b124034200c1301c8146199540c01c01500a0049152054400320355800c00c031030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600981780 1250 600980530 600980537
    0xc02190503121b06011401200706050c0f01021e030a060504020d06210203070911190906090603060302010804061802040c11010b06190804080705060c03180a05121c050a0507 76
    0x2012031803960046401c0d4180e40d0390306e000c3c1c450300414000444600c4840c4c425900502c04c2585030030008101030228102401c0561140c50b074881408a10303610f4000c4061080c589a4414403203814090b000c2c80951003031680c0c40d09078039125140c040f0f80078020442540603960051002440c02001122600090101d8814400100f10200e030450808004000c44400a5254004c02c000b80102c641580c07001b6903204107102594240407940c8440c213182180140d000010641c8600c04100340c40c0c2c00340c150340242c41d03240b406104842c90365001901c48040500300404460315140150b000c0c034866602e00e0f01540d0020001d0210592908000d011840000034140c100c4d401c0c041e84291509218044886942440c1007500c842c008059041340c403458050300841d001d40c01040760030040358042000c18042e00201c0b080c1c5a40b81001c070005000900389100c810f0190300500c0c40780c8007140010602031a11000c100600703a07580110240f04800703109603041c1085691a1405200d40c480b082d0340020702c124210380f0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600983030 1250 600981780 600981817
    0x90306060801090b0f181006090608070b0a030b220c0f1d0405060117040b01151d0d0302070902070501230103020d080a1b050d120209010c0219050312 66
    0x40306400d0f0390084601600b81e890b95004030301e25100500c4502d903c0242100190042590f42c0a05070810300d110640c010b08a844143c28400d1407020300c10840107220079030041402c10315200e1258800d0044840038428540d0328102e142154543c02c45001c0d01d1802b03d14003444140e03005032504000d0100c20500000240b0400c0800c0c20680101041025103246040110080484404000181000501440c1089990030f400e8822402446645019500c540c02001d62036040c60607003d0502141e142e001c042000d007441e5402c02d40d16801200000d01d10584003424440f032141016898100d0580c008000107100080740001d00006520074030952041c4002d001985031000c1c071551864a0a000282d030200c01c041c00c4c2d400240410000f8010aa4203040100700c8a150405076840c8824401003621250030021820803e2917100e66200c101c9450044218140390040c00000d26000c42500d0080c055682910001c01015043e80c681c0010b1400400715156235807444606109600440300c80f00c529000d80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600984280 1250 600983030 600983039
    0x40501150801051308180a1205100504020a0510090b0c0309150a0e19030203010c0c0501050906071e03060305061501090918020d080d06081c140429030709030606 71
    0x1806954060303101e4400c1e0304106141034880250030386c0b00c0314401d1100c413031029501070503840302d9004100030302c0c01b48001000c00d2040d003040ea003040104440240b40030714000c10400180c1d10303c03a820080e1101940c08007450003061400751011415900481c030350040208425000074000801040f9445081c0e0301100040200c540004250041325400000302c0d2020841c0600c504048507a50441184001d82c00121a13698010a0841c0e0790b1100810000b40307000304040512a0074002d040d0004021001400c0d07610306060b0040100b6100d0141031394246409502d420114842c0e00804003a60704403060354400d05008e1030140d5101c406072880b070f000c00d034000c00014030f642180c03060f00a1011103000411703168011390b00301321031920040070480f10840c0600c004201990b4071312800c0b02400b1124003c244c481443c005c4882e00d0f9031801020000c00c8500c600c584104041c41c01070320200c40805e04c0c2504003c0240d03070022100325007160400b00040001c030805c541e40b03501148640c100e0340141000c20086449 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600985530 1250 600984280 600984283
    0x3070b040b18010915090501081807030803180105100e0f0c040902090406090e07050f030c0a03060c09080604080306241e0c010903050702181b0a03060e0405011508 72
    0x6612030700101040c24030142c419141038042c003600781e420515108642c0d5490780d69560f00d04446045400000c3da2890041c1700ca540c0180b00e040c0c012840c683c40d1300c0e850304840c1c4100d030343c0c2c000c900004280040c00701c00f0402104130f010841d10700e00c4440b4000d00861401c3c004510a090303e07031181d6520707182540045825440780c084800e0080400d075254130300c0d003800d01d16090060741c000900140c010740d40b00c0c0c0009903403d281c425120320000380c1000c2c0004900c5c010030001e04a0140200d944643c0040d1495021942d4a010400c02c51380c0c00b1001103040130041000b40c1e110007860344000c2d44d600400041008101001d00158443d8804a550542c0a151110818584c42949082c201d14850800060004101034443c1c55000212114040d183c10440304a4509503030060030200e010400224801d0118900081d207074441c81d007000c1000c0190302d4803404035403078907000b0140102841000100075514a11035009080a0458010f0f403003201d0a0610b0024001c081031101905140c1c40d44501003040d080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600986780 1250 600985530 600985537
    0xf04090e060c09030316020303071a07080121350d150f03030806040905100e011406060f1303021c0204140c04090218030a0303090309080c090a1d01090602030603070b 73
    0x113401541000085102c42c4503042a05a060303034540701c18400400060001d8921940064580800704100d0400c210701516118040e004042400b0340780b905500200c00c0324401080035600a50b8080400c2100c1d42688031141d40d07080709021040e4004000408102c0c8075000303205041c0300b20801c002c15038908413030b405403080b1f90003007011009070880200301083c4601225a044040200001a001656030f80c50745020001c0502071041501c454903115408400c1c400c1100042820404000c45d182c01000501e092003055400d0244010218002c0340c40200d40c4031030006160302800504010190b0300e0134250144042c10b08038465400d018086585000748080180184018a00320b42010f00b0201d418019402410b00c07051081045201d41c515980c0402007050190701944001404c2d40d1a8100203010b00342c1600403101c2a404400c0380d481c0307510380700405940001650b4002135912440440540c840c4210520540b066013484400b006028440c1e0045002e00c80c01c504684403980d4235001c40e2070900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600988030 1250 600986780 600986797
    0x603030d0e010e0105090d020f1204060c1448060d200327030307121b120b0a05060d0c110a0c0f0501030504050d0f050f04090e060c 58
    0x40003844010314500d400d07000480514805000800c08020300e400c0315084039411203610f480c0f9401301d41c05498842c0c060048045070f413500c3d4094080b04000500c0800148140e01c5020100320249030320348144050012403100100e07203071042c1e49488e000061540c80c580348204030303c1c80b83c0383d00c24406086107000401540c0705100b0300d00700c9241040070070100489a00580038400c68943c40d29101c2000e40741c003417412448489903180c442d03100d06000016540f2410b003000e03241c505400d0303e91070410100c40041982d40c8102507140c034407240b442c1c200303808001d4401c09841030382e040c0341003030701075184c58010340021040788425408100705c21342c3c40d0410044040c10b210b0740e0b41001c820410309840c1600c2c0c0e0804640044207080ca81e01c214580c0c040c0f146424440881a83c00d18407001003800b4407549450146c000b000700346828072450030a900c8641e161401c2c0200002880452164005c0d000d0050040e40c01e81e8810022070350b11569075004100141070305080c2c240b01f40c010040040e1581c452041074a240344d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600989280 1250 600988030 600988033
    0x1f1b0c02030c090615070507030b061c1e061406010f02013303020d031707020a03081816120203190308011a043b06092214070503070603050603 63
    0x100682c2080c03020200000d8181078010a200031281e5100030904000c05644d8803800c003c0407082c8c03550800450400000d01164070030501d07110071900e4140221709003400f185d00070500300c0c8016464101481d02100801000f0301c800c1c00c01d07200000100191a101740300344000e81340c4a03010405500c04908032003c1104010b2075240010381d002c07034a200c01d003816404421214800d000071361a5000038150142d01d180c03c50009054002102c000c0c0c4200b040700d074005140e80000c0015440d1981c000d40514801443d03840040500b080d4125008020019006511009444850541d8485912000c2e581010f081a8083c1c41007016025040400d518600109034243c0d4661900fa4241101d0000c1900070354900b0440b003a0911000c2100c13824690392001c0e00e40840082e44d03090101c3e00460000c071702da0380800302d0458200030802150380c456034420350340201c0001c410075801c00745541608c0c03000100000900241031301d007440d5512480005442c07055400403400c42c3c0720345541e244220300f078580845840707130907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600990530 1250 600989280 600989293
    0xa0509120702010314010b03041b060507020d0602121f06020303190c12020301060917010e060403030e190b0f010806040c05040b131a010905120312091f1b0c0203 71
    0x10110300000e4460648140f401180b005a08410041c2845c820b0f004810039100000521082200e000219251908030308080c0f01c16518140f4050800e00503d2006809420500c40c164200a800c1d41180c101c14003c411040141c00c01c400082d020f9042c40a0140d9442605000071603094000025a4450107100ca4203040d66032140d036101021303101710340306001888010700404036458030500145020f05100d9031414007041c5801c481c0c0c214152480d0320300742035034900050380d001c503607011a640382d000f0340500780030034440b0313040d409140741c40300801e11840c58109009a03d020000280580f07400b9600c0383c20000c1c0b050f600d401803603450303510943d0007e1501c80c05030010070075810a034014009100c00100508060f00132040c000381603515404e00321441042c0c40218260030343e0065a440068030040e20480170010301c12041540e60301c03c25902c0d00443c1d8941000440200f402c1200107005580c01180000444108030317400082d201d0001b0fa000b011450103200c0c00d65038400d168245030307a600207000341035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600991780 1250 600990530 600990553
    0x71401020c09011a0705070b030a1a060304030806030304051203030906070201181b0f03030c0b090106180b04020f16140606060d0c140406050901031103040f2406120b0a0509 76
    0x44d01e090184603422140818450a0b0208000307001d084010400f10360b070181c3c2c0746030402982c8200e0f0381e0030b01d1f5000340c8111401c00010a454202c00c1e2644554942071a400940f51080043d00d980201c0e0710083d40030001c040461300142c0048090b60017000d03000f00329419603c1e031940031f07420f88181506000300410400c0b400d0000c1528043c900000c41680c1041003400c588501641558596542064010a0000700060100a002d01815502c860700030000c014071428030721106040c05034543c414000341e07240e090030342141d40c40743d044548000c01c0e10100e03540c509284e942402106503007a41500e2014003002208170008021545034821500240020310340780c2d40d060702c58003d2940941c244104903c02d0703540040a0441e0b0000c3c405071646466a6440e4540e0b50300040649034100c04999802c141131050000046280e010502c5440d4081c0030801202203011104804206489a41d800345003400740010340b845140c0c0000301000c0c080c1104220503615801c0314016100150340b580c00360f9121071205107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600993030 1250 600991780 600991799
    0x6060e06180a0b0a03080a08181b060f040905100801021606020304050c0310020d0f090f060207081201030f03034203154805040b0c071401020c0901 65
    0x540c84115100c000078050040e43c04035694100e183c0088808503400503c2100d242c2e042800d091f0700030b2080480c0344050301100d02c0780751168ac950107650954804180501d8455a4110035903114981030481fa41d252582c400c1400054070041e42d0709940e1008501010070a960107000f203480c8610321000c200080f18803603951000a600c010810303201402030244e808860f90701400031048015403440050b840b017201e0102c030000c48241c00100c1c901a8582100400058010841000300c140c10010050f06c032411818140c0c0640302e00b0501e0040841c6000000c8200304202035004034090007a40d0401105450740301c0c9500300c5502d03000e1504803c4486c807000e188501c1d042500d0f0f150b08049810040b14070354a85c2c03000340c40d100aa144041036a2075110030028110020607034100e182c0c1c2c00d0b130040b44147c0406203000402510881140c1c0c1c0000c10080d4614142c01042101c1c018012150080c0d5a8084203206c82e03214030090144003040c0ca02c62061030410740c030009010301500401481c0408036441e1684c030f075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600994280 1250 600993030 600993079
    0x108060402041205060f0106021f0c030b0a1706072c0103110c0105010806060117070e060f0a0201021e0316030f0e0d09060f0503280e061306060e06 65
    0x100c0e031054003000003160b19098080045030b4a84075800a0a8031b0070009010901140160062405c540c003590030580b40402c81921401c8148407604001820303402028102c014200280e00350b50085030b0441d0000b5003108607004000ba1051800030788049496040085a42910407000e942c65500802d40c5010301c0311415001c1c2120740780c14100051030364412600c00c8003c1d0009003001115940d49c4004021903c000c0c0106580b0500074601034803d280c00013202c12a101e00584104204405407208442e41c1c2c9500c41282c00c0d2426501003070b5100c0e10042c034000e02179484980d16a003030341610100d800c0e03003001140c1505e0040301040f0701441c2c805a880c0049004010100170920b81c40d0322501c1511400350180a070040d0031030b480c0d5800d03007501e0403c0c9010300742101d001488806c01100b042002000c7e400c0c081d104010b4031142d1480e24070340c1c44021080018017204c541c40003c0340200c6090105a0980b05034580840f44210030038010141d440c00e60984440c030840d041b0750001c4e5896500a44d030701101d10300c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600995530 1250 600994280 600994291
    0x4032706050415090806010902040f0e01030203030f030a11040b0711011d0d03030b09090601051c080702010c050a05120a022109040c0c0c14040e010903020d0f2c0109050307060e0108 80
    0x5084d003d03a01c803400381c41c005003070f8081c001c0f0341c0e070000b010f10403c1d0000e039028026044841182c00d0551455001c00d540f40311b55005042c40c0f10b030100100780704107256009203c2860030504d60540340d54441c858152130350300810084075041042102901030794003420108050b4480e600022584450f04010300c400001812800c9003015550074034103030b85607541e090450081c01d030030004020942c10035041c8074545540c0881c08000c0d800402ea01c5001514180403200d10650a2800120b44851440d1103461f00425500060040c0120310340305010040050140c90031120940c2181d00042c0c0588080003c410a5911003c0c0c408042225840a0501350031001560400e4035248072805016201c8141c084041e4000c171031014500b001c01044c40c40d00d8000d6401e00e8012400812a004d4180c1e006075a07803071804018000c0c0141035100a401c180644803242c81500c0190b800d83e41c41d00307110b20081081002c440c0031804901100c00203d624140014050f059400341c1c0c0351454008194001550441d070010903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600996780 1250 600995530 600995537
    0x40e030405060304060608070602280c0b030f1f06020703082b0905121801120b030a0b0f071707110304180b01031d0d050c01020702040504032706050415 67
    0x3002806480b04001540300d180600070002d117043c10038010741d0401651b903001804642c00001c49084102d65800c484860242c116221200b408051400c40da40c2c413407070780c0076400d02e200100030802007007024044c1c6407203000712000125182c402d00040a50100490140e071300164040b03102800046c10000007464641c001a40c0c07000c2102400700101e4455280001c0c0e00002911000d69500304441082600a8204c080e20540c0c20080340c401d41d89040d0114070803040c100a100c042c06d0000f0f8402d580a01040b0340c000d01690f500134440e003030440c5040b04c103a800c050340c500781400151145201d1120750240300550744010310a074407854421202c00800300603580240c0000c22001586803860007101000070040e070f601190841540001400300c0c2c146100101c0c115407011020280741d0408590517140b41d000c6e041050f1100d24440081d4024001d08038029000f03840c0409002c1419080200304114442148410030042c3c5c440340ca001c99011544100c9011810a11003030055001c1d40d0398010002201b4075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600998030 1250 600996780 600996787
    0x618060d09020d0309080f0109080f03040c0302040203091b03030711120f0303180c0f0102060105010f0905040203280212060d06020d15050102010f05010f1415040608070e040c0e040e03 81
    0x4001030003e1960040c100c0c0416111042005469024450340b10021131420080000c40032586500e07419200f1388000b404040750000c0010b0422416610740c0c1b001d1500a8021500c0e03240c148000b55035071030711000688001d000c2002214003490700200b00d0b00c2c031a5100c029103080560110501c01c4441900c200c10901780607800c0340143d10034080024610401c030011040b601c01010700078503410655190f6010303009030341e0f00c44008030b45d0340c0015940341150803e20740b00403134440203141115009070320340040781e100b400002030161146010020000d82040d03611030f00a5201c50070700070b1007207100700003000382c030f160401c000580145460b20000010b140a0000545404a4000503400310f13102c00100036003c4d05680428455035038240700d60400030700e1541d400c021a50400541d450800c0440c850400f1244001c20450481c0d241c800700462418000d4900b641c5994a4541c05080c1c008219860700c00076416490045040c5010300660105003201c0c0c68420403840050184405040c0b0800f8240c864803080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600999280 1250 600998030 600998033
    0x1050c040b0f0d05070207030308130f0308130f060203060910150f0c0b041b0f0305060f0402010201020c33130f05012903070603020f03010b1c1404020406050618060d09 74
    0x7801141c5c82480742ea0f02900c0020b0440c60042c100c01005400c40b030b03400362003803503040000f07441c1030440c0182c980600b4028803a98a42510700d000c000e03da5001051614850f001e0b80c20880560007035401000f08131400303505503940c0d2a0785810721086100b45008c900b0034080c4181c102c0d001d0715850010207000d29051070038503602c0d11114200c480030303181101c842c2251081c00c03014200f002e5088025060303d6071000100e41c91516056901e030406840070000c05030304401304046a0007503045942d000049004e0702c69079546044610240e90082c2407114000c01c0d00007541480d0030204c980c5a2080d039040480ca000212503403100e200900b50400111580e640c2c51210348000784954190700c942003240207031110703c503440105049c1001569800082414010700c58452035500220560341034031500b8681640392081d210248070070f9980601d800b011649400f0b95506915416161144998001c0d0382c2401310941d58000d000d5240f18005020388001104589002c1c3c2d0301c0c0000003403050341403030440410b910105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601000530 1250 600999280 600999307
    0x602010b0d08090126040606090b06071407080d051e0a210e0609070303110a020a27140105040b0a0f0b0708040314030901020d020d0503010302040903050c101d01050c040b0f 76
    0x22203041281080d0220100706c1003103e94040c82010744600b480500c030310680040800c5190080705401480310009412013428030a04214210003409010304982c0490010350f005002d9170300889034411821a80f05135113401c0220341080720502c900a81e0790001079250003461030f83e4000c203107070001a442d40f00c800b00300040f0000c00400703000f401a10003802d0541d2039132802400890348d07000109a48c0d00004a10700142c0d45001c502c2045551800c1d1285403110600384043c0940840014044050700d131103004070020545d0071761241030310001c1c1c1d400c111003803991080000d07102c07041c4900c158410303c00030240300c02043c00005c0e240e440d02ca04201d9040a40300d80d00c804070040a0322008076254000f08505209680c100210b03000e1034418005080300000c10780c40100580310502020703004a4940310040201413040d005ca074410400541a0b9407203080c00d000d102c0213010000a40312961807240380c0b4400160040c0320f0103000e55078801c07032140b50a02d80121214a500301044001d980c40080c446079410529 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601001780 1250 601000530 601000577
    0x50a030803071e090609061d060309030f07030c0c060305191503150207110603091002160b091c050a0509040e0316060e070e0105090f04170f0408070602010b0d080901 73
    0x100d910b81c04007850170004014110500e5034003040030801443d49001a6980e900c6a03d1710001007640c1e166a42ea0b43d05020307528610440e0340d41030f01c0c3c80f07000500308145548000341a410900c241800d4403450f03640d035011400c1d5441036607603201c0b0304010286a403400c1e00316488a032400f44d0503d029040035a403a1255074020031040300c0740d191144c0026000c02004051030b015048820220345c11421400c2c101020b0b6038a01d00f03040c1411001c0d030700151510b403400c01030020601043c0e01c920550181d151161106880e000c0b022124034500081e80a02c01110b409481a1042c0019940e103ca00b44400701041001400d041a0f4815490004100c00341d61089070385640058140200c50108d00c0d100e42006051402d00b2035032046801c01d01d90401400310b07569503d02103800c410a413411503090303112800c2c007100c00102e019400c03984110020302c0a44000c103150103013040358128001d40c0e58641d51040c0507401d03a17500910b02d55202c141c26600303500244150020b00079404061414419071101040403019894 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601003030 1250 601001780 601001837
    0x705190807200105061c0f0f0f080a030b0f1c0219030812040c0801060b030a0b03070e0a0f0b0405012405090a14040f0b0618180a091b050a03080307 65
    0xb51134008009841c180b444128150401511108401114980f1504802d90741008010400c0c0c4200084030180544000d80b002401d0300020a565140b003c1540540100b0343c0003a514040c41c00413421660320b04d0325440c030244840c0301c1c170712580c402c20707655007080071000e22507412003d01d003001e40300400885c020314041d03c003070000521002d2850a060510b82c41c50b590b1a803010741c260781010300a200001c8000c0990382c1008201c076010a040d4103c1002908188564100500340400101009001441900302d10600d003c1c4020030481500c3d84000d10054403001d016070400c4a610b103d4650350070952501072015203940380381c01ca041482c00c80011780c0c9108582d2103103d0b08003031341c0780c0e5841a203403a10076500c5040058108110200140c004a07825000304102122050742400709010709407517480b81300030400c0443c180500149030403071401009120485c0240e81130031010440301c11203581c240690040d24401403000c04414503594404098ad48001d03c40c60402040c0e164801c030644680242c0345190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601004280 1250 601003030 601003033
    0x1a01052503020f0f0102030c0f1809040606090f0b0d03140d090b0f010b181207260c0913020913020306100311030115120204060b041706070519080720 66
    0x340d030b2503c0020329102600c2c10014082c0d10400c00d01c650780c2c0c880d40031104a01d91002145e902c4200d20002c0200013102d03091510341141c4800200030030454190b1080080c0c60507404200300c0d5150404c7e03010102c2e0b04000701a80c2150203452841e010a00031400d130800140141e00403803034128010307241e2303007910222002141d5030000c1c00c0a2007140c500e00d80c049070242054190b081e0418810680801003048503a40290180704d100304a800c00c01c2040c00840050641c040d6501108121050420125410130801d100640600b075100903051a200c0200c502540c0d400c942c5250070709151302000322980d0041c02400d03031040800c031903500584090050a1262100181040c48949103090410340c10742240c05182c401e9140c601c000e1000a0503002c1c001c04e80d060f903100300024411610104001780100d07000740803070002c00b140004044084004600c0122000000d40d01c05c0e03103410f90107940700d000e01c8002950185105041425940c45220201d52041640c640044032101c200b0500c1969409100c010106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601005530 1250 601004280 601004293
    0x2070e06120a050a0303140f042414150f010f030f060306050103081c0c02120d02040503070803180103061a090d06050a0f060b040b0a0f2a0b0a1a0105250302 69
    0xd1607054410400c0d5803481444c020b00030f10302003a44d50b920320130080008040b040c1c10040f802592100415002b04102000380c20040348911a4161200110843d1890030192200c20506550300707190304a00c2180d141031b19422084441c03020f055000d0b010301d20303101c1d40040c0e81b01000408201280200b6001b18001d000296540d0b04003107062a60035204410604078900307124050410701c1d800100d1603c1842c0e0202d81c0da0321245600f000030041d01c5075038403499062161243c0820005000b01c02000c10035064401656a40340f0b000042d804d4072180e10600d2043c0c4602450340d411008602c0c0140811100104080160082543c0305c0301210700946212207036a58030000c82c048a144c500c6150080c10803408151b080601c0c00450000512400485004020446103401c6001703009010f4205140c0c207038001a01d240316000c0a01c7d400c0800c800043c0c030301c004000b0104e0444006031255002001c09140c9040410128000540e816800142c1078007401c14071b26000e0400b40d03103030b104144a02d0305c030354041c1c0030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601006780 1250 601005530 601005533
    0x612040b090703051902030c0a08030c0d030e0303280c120e030c0309120a0b01030302030304121e0e03030d050a0e010507140301030f0809090a05070306080c0102070e06120a050a 78
    0x4580350040c04010720342d010200c20b0021500014044c1c254020003180740b046a5078038400300e4144403007006081d810002c01c000c00328140001001811290003484101c50004001d00022001c2c1c9900c0301c505006a0030030000b09241400c075141e422019504405490090180d180800007101d43c4516500700084881450b000380c0040d50244081144051005500308000b482100d5100e00c210302015200f0540203459400790300e000e0003404800c0b90002c103d90303080d6035a418040c1d2607900881d03007220117045110040800b1070180b9440c0d00d4200110300c0c42d0214034480d04064807a1052000c030140e00d8481400502c0024415010703051080b141c42c000443d4825000408500b50340c00a00100d080c0980c1c0524030403003000400c1501c0c11641c20509502294207607050108541c4500c040f010782280c1b000003009590304442c0c020900600740c03560101320305c1d942ca144181c0c40d80c2904500314016003180b5020004040384070000c94000600a00b00c88a81201780615460300e1a120011031b03064002146050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601008030 1250 601006780 601006793
    0x14030703150b180d05010e03160b06040c02031b010204080706180b07081e042c070806060a120225030206100509010608150907020a11030d090b03070509061204 70
    0x81c51a141c1290070140044040c40c40e07410b00f498518090549990300f50b040c081d0035041240b51100c40e100362907881410400c01080d8030120b0b4410703103d6000b400040788640c10140b00d60300200029a019505142c0e180014800c501611310b9007528540d001d11001c82c01d0305081c00b44500806030768171240504101d1000f0400007220316808a5600c500c1480031001085401c4d007122884c06c0e04000ca001c00c813450301ca0024180c0515040500d00c01051701040350380c4404000141c00d0f80c200220030341c070140d0f695401190005000c81d02140c100d042403040c5000d40d800391640303550301c3e40034050150809003400b01c250742d5030038941540a0400c0c2c104285000345901405180d40005d18480100d00c2d99080c00c020951400061150904018241c80001c2c10013400d9500001c0c1104000d1150b11213041210000b555a80c00b114180c50f80d001f5001d01c414146000144e601c811541925031034a0f80f4580100d061150300002c1032141806010000e0000c10b9540d07a0040264210482c10911541440d040c080c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601009280 1250 601008030 601008071
    0x40b10150c06050709090e0c0a0e16120e0a0807021804050c130605030d0519030b0a150302090d0b0a0c030902033705010225150b0406080102190f08040c120314030703 73
    0x800caa00c00d49800d03c0b264114bc200d5521113092641404034507822188004d100520100039000224000c5042400803c4a07000041c00c0b00c6008079410500900d92800f40750071003405450040166100c0e4500f45458140b41b01110108081c4910001e80c4650f20000710b400c1003696400b04000a100003242c8240016600640a02d101c09140c10884a0118000b142e4801c11900400c0c0c803d005034401080103501c00d4044910240c1c018203045224402c9140445000c034044e24402141410101050b030100e1013441900b4000c5e800500418051000b11242006402841e0b40600280c800102402c542c0b01a01b080552080c411000182e4800d80d08600541043d4112900315000000b00c00500c003040300c500340c0101b84151040c00094058011000500601555100c08000d500215071041c1207076a081220b05441c40c60340380d101d1090b00b110070440d0300c000c086900410060101105101014945840d401e200e8070034101010700321042c180da5055034000312441000a0b1b10350301c03403860108036103294 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601010530 1250 601009280 601009289
    0xf0a060f060507080304080912010e0709090b0103200913050118030c0b060f0414190b03120d0906020706150501180b031003060203040b10150c06050709090e0c0a 71
    0xd00310150820714010503a20a003000079280c508040045000c1c8407145d011548040310080c40c507110201104003007806014418260510b42c050588009402d00c8540030300d509041d44282d00720344581c219540c90700c5040c100b01d030380c4180c0035010b10b0034a00c07030321417050150058402001013000062541342849c01e4564164420310f109401c0005000000d812200300c00c40c9540c418442d580340e0381e80074042141004150300c081c1d070240c108100c4411441141d02018024660a0800c9180d011410461000c0d1102d80481c40d402d44d01c00d025a00e000c00001000d0000404040c00104509036503132a5002039811110094581341c1c1c3d66809094080348820000008017400c3c01c00d88100d0000c1e0303500320182c81c0b0034030546032070f00c0d00040090217510402561002441e0b000c102191682000d00340302280d0030045980816080c001320011550420a80ca00544410943c0d40e110f4008003a41d2140c01400300078240704140301c503a0f1404100c0071020b015000b5080610707001452481f1030709080000440d400d520 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601011780 1250 601010530 601010549
    0x4090c031a010f080721032a06150b0f0c010605090406021215091302060c030703030e0f010207050a030e0f040906050601140301050f01050318060a0912050c0c0120060f0a06 76
    0x800301b0800c0d50500710840000482840c010b04d1501d107003011703501c01d44888062110480c007030561112030004201313886c6005015a00030804c2080d035950200000c0014001c80301d0340c107c103100b00038000c00400014540040c3e01c4c1c00114401c0d60b02c401080f0000803d450495038541c0200b200080d03003001501c81c41e0301091a50710b1078800c0c034002c1c020030510500a80019030314881e0100754401e5403078520881d2040c103036000450380d60f140d0710f060090040040002000003801400210945a17805000303030f5482c103800c5005800700560694040d03c8400b01c030140a504041c007012040001e41d00ca1140c40d400d5070103028040741074a402c200044c51101184901011201d003070006000d903440354582c100c071099003801d080741e0b65100e91203e07075011a000d8030492110300c526002c00200110940103101118480d00441c101841e880347c05490900408209050b81d901c541a03a00680d0303c50289108081e00154818045541031150b0b282059811108010941988070500508a1983c80b482c402002c10743c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601013030 1250 601011780 601011793
    0xa09152d0203131e08131d09060c03220308060405010906350304080a170a0807180837051005190e1006150e04090c031a010f08 56
    0x101c0d15624810755600c041c003200c10701c403002c0309000304e14082095115081070500e074030b841741c8030036600c1c030132029000d03030f500b4458186000300c2c00c40110042240222401405442c0d15034500b070700b440d09030708000d01e0b03d8a030500068290504004044484000754000d075500703c0c6a16054090205560041e2300c036420f00c41c5010700400c5500704565940d2802607115914001d2031150501e0b0000c00400f00d019402580000100007074100d000095009446d44a6121403d0794500b850512000d4005e40c0b016402180617400043c2c0039901c1144c001241c812094000c9000d143c039101110715003005021401d007264000754585851211142004d05c92003d003a012a4401c100fa6480c40d41ba03440c444443c00105880d030020039a2071a5199410030310440b0300c1c0c0104000898200420380d100078401c403083c0c10b54600003000c070300946c20010800b8008950341320aa80661214140001841c1c21003060b1040e0907000800f0000078210790121800030100307400c08009505040f802d1941c0c5406907c0802c0236400fa0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601014280 1250 601013030 601013041
    0x100c11010f090324110c010e03070c091806061403120a0f050708070b0c0403120905030d181802030702070b16030302031e091c080f0a09152d0203 64
    0x20586000b80d0381e10a10042e000900b0f40c1d015500a0700f0413620f0030702c182c20030310340329240c0a010b400340c209044140020b10442e04061055500e0b4072034240d024007241c1070301c0414050307540160005648034860079050788520080342c46210031034886400a0f0210014084003100b6450304000002c0d49040045c00300746025409680500040e481908642c248400803584070144030440c0c0544440b6501b1502000b01480c1018550000b60706c280070442d81440010404009588505450f40940b8000340040c0791101c0c0c428015141c03510940301c6035242900214001c60740a00c2509005022a0040005a00d03810b041c10040d0030801c05400030308256005101218001c0c0c6914071443d103580d00350600590b030f5104c0c5001c4580c101c8134645012960800d0001707101b14140006540c1d011204040d03444c096410130082c0840c0c1c42d0606032640350b02080f0070004100d80b80c14540c07110345890321512600e090030b009034070803500340c8681030f10002802c3c0c00a64181c1000d030440740c4048403c8001c1c2811403440c0b61a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601015530 1250 601014280 601014287
    0x9040513170a0e1903141204090204060909020903070311040207051009021203031e0c0702031926030c0309070e0108060f071707030f02130909050c0909100b040b100c11010f 76
    0x5500c00503103800d00a4003290f4070000300f80301307500c40410301002d6a5a144d8032781e442d1030040d5005200d039000155144400003081d40c0d0510a5400c50100200035052452445d184c46d4401070a0003011903110307a0800103600025420040366442c4009604040790802040c010000018402412107415030000c0040180c9001b4410124043e0000300c4502c500319150010f1089143c000d400c0c000b50103102d02c0402044864003d500400f24922806000001130000e82031016122410f010f00c820001051010411243d40e6902441d4400c110384c0c1214055980c2d05c450a043c0c480a901841d0305401c04014001c0700c01d02075250fa40d1001060400d04440a0312031440340410780b0003090302c401c040c1e43e4554000b030558540c04a9007105030070090300000945503805a0700034018110112070074818840e000c489400c00c003d0141c80b401c00c0c03e024028090741103158001400c49500b882c0c0d07001d130f62041140c03074654408180c110203080710b40d02c0c0100c4c500e1364600018011800b003600390500030716044292582d9403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601016780 1250 601015530 601015579
    0x153308040308041704030605070e10030c09030b0c090a2601060f15030608030a02030d0f05040803011a040b0d0902130605090c0c070e13022409040513170a0e 69
    0x2d010030804c004d8100011600c2d114016904002e00103401e103010700059551145005a402400f100c501035984e1580400342c088801450201010a0302884c0030070100d840d052402e50b000030160041c52900d041400021202e0019401c044410354001d50001e00050000d104900b0a2010070000c00c40c55050041006014180b4400c0210024a5900d4a000c907442030300480c0c020005041141d440c0c107200c04d80a5101c0d00121203242342145850b003031501c5001075024060081da0801c3c0403508d96403c1888203003162815010007150090104000500520b80200400d8040b01c0323400000f4000000744100300010700c0ca44412184035040071018800bd580d8908515001100315915596460103280d62905000c05035000c000085d0060701007008001080d14015101c80c8203c4803103aaa040442d42561381030b207200c0601610000502c40c1c807001d41042d0384080e4019604c9850313080104070b20303500d0314010b200d00c0002d6403000c40046080b002e1550841c416621b448022501c0b580c0704008072100780183c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601018030 1250 601016780 601016783
    0x7021e0a0c2904081509031207020601050f06130b0901020a0c06030914061005010e0102010920012003030112020d1203060305100605030a08160b0c0a0e0402040605070615330804030804 81
    0xe180004a6132406c0c0c20070440303003c00c403289104011442c111201949956003403060130701580051940300da4a103882404c450803110004a030500301c50034540000c11a400c00c1d13031514154890644c112010981403049800100426500842d00d01c44514041034503000303070f104213070740d907400401402100940c0300907403010b43e0405c0c60165100d452950040380075014440f0003170401c5404400b24107502c2d00340301011125030000e0b21981400c0d84010180040002007540d88401500188010300c1000b444412009417a8001402d0b5129403d40740ca505403120850748a07000440d9030f9407420010044280315841030341c619034500b0011103142c11302194030740f00f1540b40284900400902508502c0c058101598000d0304120754540038505000c1e02c28503036128004178804600c0c00d0021a0307552400d07000710782c1a00d5041e0380d51802c02101765552405450501504c6560542c2c2160109000742206c6212041100040006d2031001420002001c0515038110b21300401c0003a00030040860340100910b40c029 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601019280 1250 601018030 601018063
    0x804080c06040501361d06030601150c0201030f110a09090204141203120c03070801080616030905070801020a051315050f0304050a08070308010e070807021e0a0c290408 74
    0x14510000300d07007922100d041081d0101e4004400400c01542e031101c46404940c0c8076100c0c6406d51500c1c4205551207109104c3d01c0d02c0c4184084100d80c0043c41400d0981c515881070401089540141641c01e05655403408800c1180c07201103400054180d000c1030f0b0304001e04482904500c0c0034200100c069081458480141c017850110000c05000042001181c0144425444951030742c02c240005880c10341c015116440014680000406c180e079000c01c5260040521150041e50104d000c0390a0303001e4250014255401d0040c0c1e40300080f1520f003800100900c0d9225910320741e4800e490b43d141c0e6140001c3da0008411701c3e44646220a00f950050102c5a80c20300072040d040d101ea8503803812505c0c1102006004104180101d0007404068114040e18142c404c0d001d07107020159141d680840d83c00701f04983e10b40040c0d2142da58155121100c106141c9100800c1c0107489131341100d500c1d03540c0d8480c1d09070300c50340d0884c4400078403840c20811300302d540419030304002e07869181038038240115a030380b4401000314041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601020530 1250 601019280 601019327
    0x3080702101119090e010806240109120813030b0a11130302010e1f05030f0c190813051504060606020f21090d0501050405010f091e030e030a0804080c06040501 70
    0x780c1c065882030005018180401105d503841d80001529401d00396075289800e89484080b0108144600100c210070750306035a61901c091401b0b250325281207a41100f03458608003084081e024840918a5101940c01a03121001c81d050612000c42205d00c440303e401e82452042c0401001a010b2804240490b502442c0261001d03d030800050160f42c22441c007500c040c68180340c000b0b1256006005140f24140e00000715959586029441c4030504c92500740315142d51410001d04042c0e4054080d0706e03040309080510704060006591014a03011481104619005c5114204003c00c001030040801502292010740110321200c08115551043c8181d10030b40109540c0045150982d10170582d8102440182820382240041c10824000d00b000d486c04e4900d9420b2801c0425542060300803240c1160b8403409001500301d46060040c0c2000001c030040b000c0106104a03035440740d40030081018464010306555a030380b0b240c40010f6181c0700c03166000501801060204000c0c682e041030651003c0390130741800090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601021780 1250 601020530 601020577
    0x90305030a0201201614032203050d0f021e19030e0a060207050913151109150a1d03100207120e1816020a021201061d040f030507050109060504030807021011 69
    0x31f60143c030302c60002c003000c2425030f46040c4101d07042807000c8038041e205030f902800300e503002200c2003401a20305402603401800d000d080401a403170a00c2c003002c0541700391500e83c140c5418092403501019800e800003100341c00c4581d21031900c004100000c00d00340c00108901880c1c0030104402050003030481c0c1217036001354607103801d1190010041c17558940b000c004100c0007402d0500600d480d0881500d25014103400715003404003201500480e0030140316900c4052142e00900083c1c0c4a8000000525815016445041401411b41d00280100d84e115603524001c0c10011500180b09400c2000520310500c02d2006944c540c280c030141c1d00e40c000504040b61031081c1c00c01201a45007841c000c000a4000b01001003841d0044010b41c08001900e4103054003d80d00c41617184010710f007810688000c0c0c4440030f100350120000740590003c000031031107000041520303c090b442c1e00084a0b002c41c1d042c3c002c02e504c003003003100c0d2560620014540240c41d0000b0418000c06a8001d0241c2c0516020702d14040c9406201c00d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601023030 1250 601021780 601021783
    0x305060f09010b04090c090e010b03100e01021210051002010504080901050c0a0b010816080106080c2202030a020304020906010809070312140714010b030d020a0b07090305030a0201201614 82
    0x1543d0100640203005401081ca01014038081611a8900042c039100340c0360400340040c0954034080310010010a8171081e110340f01070003060f40c00000640c96608000d102c60890006d80740a2051941a034039034041c52a01043c858820060f109540440e45407404110001c1d840c1d80a99495140030320700a501e40100050b818549000043c020781030f800c802d0000206404006030341e07030108811281c4054025603403040ba5003611518054541950800400c0c86001d0034111043d9240320441c04504200364460714412089900659044020680003c100300a5043c207243e0300342c010200780f03030424061401074401a02c50f455400f004107000c0041c03038003804080c800c002400e800340c58a4255a650f00803460705c1103010a40168003080f0b0350030844c4c0c9403031a00e4081400316400300c094001d4a2071541541e10310a510301d0061155052010103040803010403010000b40c0044031044d000000d07641c055000e403400040991801e18801e080c1084101c00c00f078429114200400d0740114001da05090884496 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601024280 1250 601023030 601023041
    0xf0204030614102907060902031009030206011505041a0c0712020d0b07120e010e0606060405060a052503020102121b070222050405060709080d14030a060906080123010305060f0901 79
    0x11100d000030802005101442d44010a500d200309e040701c101d20039002c2c81c14107a4079880b80207000b68000000401094204654440b0805001d10384107182946030760040c03400d440180110b248440001c2407003100030b0804c000c0403010b08495800d6080c1703040b513680026810010488000c0078403c030326001c1070035140500c00080307010782c01e018140710315003042201074001e240304115840148118008542c080c200001150140e9070090040e61811500b800190f5440d40040d20416412500c0d890140002d403205590030141c41c820b84c005690b0b500303074040910600d40050105030424040c1801e980c103000c0b6550403036181c03950543d1310040034050000050043d10610400354043c60420080104201c0c0120b80301d88103043c00e4036916422a1500c1020780c0d140c10410318a40800d024102140c0e40000c0d41000d141c0c0716444c40c502003005504c40e06c8030400e81d26660712481e2a6910383c9441c52405001c040e288070404200c004c003034100d600d1619a60b0340c80348042c16071183c0307828110100b50301031020b400c030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601025530 1250 601024280 601024349
    0x105090a020a0c051b040f0b100807090e0f0708161211040b030f040203070b0a09030b04050f100e0c031c0c020d0602040b04060e01050307020d051303060f020403061410 74
    0xb500c0c41205007080301da40d41e050301789006104501e030920b0b40002c0002c2e4429030b000701c00007404103040086040d03000e40703c4400141c10002400228040099405131441d19188a40404150786c83d10741000740000d0b18040c2c0c007070508440103a56023a00c2003015801014500149840080441c21150081964400e132159411001d120b400020401c00007041d041d41e06c42c002c1d4825400c990b15160f40d111041c0701d42c0524080d040c005480c106c03081000c182180041c0750828080c0054440e4980656009458503100c500e11440d040e07101e28161700000d10034405403a003000c040d000740540440721000c150088200c14081c0060142d0301c0a00c00c00e41d142d01c102400d0b86903000d002195602d49408503a43c06030014483c041c00908400d810719100d51089050300e010326103a070020400c41405030400e6842d038001b44000403c820510000101181a600405c0c1049804007001650744c1e0841c14164141c1d400c13100748440c1002c81a003032080c0c14025a50321001c981007881c40c040000060504410a000d070f40d0b00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601026780 1250 601025530 601025533
    0x7020606061e0d150803120a0c14030f01030606290f041e0f0609030b13021f090e0109020f040608090109080703171503030a0e063903030105090a020a0c05 68
    0x3c07011112810ba84c4483c4405080c0b40211031910b41c1e402460343e8a10032114011407107070f05180480c0300c1d030040e50001c0d014861542000524001054008a019041125001e42c1292500010028031216100322009820b50142d64a0484070044904100c1d6281c40d00f00d6001070000079501c03801c86107120903035000e04070348020051a41c80e55121704402100a0003509070b00410450000f9210780a440d51004807a400380300a5441c2d60b60001041c4d0380c440303808059030410907581c0203180c90a54090803e42d543d1060300c2c2c3c1404a1305051022106620580142140c00e04c1005480d8605113640140d804461407807030a2000b6541e0590200c0c0905003400c0300400800003c40d600c410540c108802c0c0e40c503080c19006c1502d8603603032109090043c040034042c1540507001004070000a03881000025011031010b01440c6c0b501075055041401c07140310392018001042c00b001448035840da030000020555106100070350a65040c50005070001001030301d8074070309640c00107400c5981406080f1210000f90480c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601028030 1250 601026780 601026787
    0x8060a030f151118040905070504050112030818031e070f060c0e0a06080a0c050405120304080d0804030935070611070b0301051c0506090d03050f07020606061e 70
    0x9842d14101d5000c0b00e01c168050b05004500d8002032034401910300c18901d400c4400341070404c003014000180500b440c141c0b41d42c095280080740b2510f41e400340900034001410303240d08601042c14010f050400107440016006440d400c00550070f0400025105003080d070400383c2c0342402b00030003d8042440b0782e43c8014181c400d50100807083c41040d42c004d0007100300d95111500c100013400c00300701d144081ea0050f180403924060128200800542c0804040c0c180b40c00e00700d2600b1380f10400140210004c19040e4039036880020306006d011000c0c0010301c1d100300942810200303070600355405030030708003e0b0240708102446110b1800580304015608060f1081c02060030032140c030000b10094071202c0751b006900220707007a04071180150000103a10740440382c0e0042c00c02d04507401d0004005541955003a441122981ea10310000440c01c240000ea01501d250f50050441784150140501035800c0201a1501c003464601000501500890500d601010413210159035080c0b032f4000e89804a2030912142c0d0010010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601029280 1250 601028030 601028033
    0x1020a0b04030306090c05091e0102010627180b31060e0f1b090a06050907081f0806040b250503040b1b0f0901030f1113150e0108060a030f 61
    0x1940204e041e1030420600f4400c0856203d01940c507482210304142d0008030300000d0051f407000e0303141911280c0070140b0011810b244e48101c40d80c07100c0c3c0c03415100340124803401200f03d80d4229078070500c85c0c0c0c481441540410946203440d00724002100428036031480f0031180c010500d03145000c0030032003c00307031560800084194034100380005110b00200240c80d4400d840703424052000001d00300090300d860240410b00441c41c40280b001c003080182c14101c04a48401002c00c955a82107019445400b070340c0d40b0300201c0e00e442001d0100f080c4109880708044a02000c06101c1500c000c2045603000c1d420095140d1140c0300c110010b00365007103000103001403541121244040b03942c03100c0190f0289004105942054880d06911450150a1003000d40e00c1001000f1b80d040814045001d0300903034005040006140003904940c50640c2d85401c000061054000ba13a10346288800945038044c00e156840203d121540e030401402601513810118103112603000050303165910760450801a59100e040101d83c101d15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601030530 1250 601029280 601029287
    0x2030a020304120e0303070f020a050a0611100903080c0a09090c0e09150d02010f02010213121203050c0a0c020d05070e0403020d080c03070804110409030917010204050604031101020a0b0403 83
    0xd54040b83d5045900107004180ea00ca0304400c54100e4004000d1894400c066640a04145140e1b100700d8014049404c005890356511420400500040d20340ba141c0e401040c0c403e80c1091000350300c02d002c40c1e182100390b001103640001d080b6400444001c105503140325041055420041e154010b02d5814140040941c160342d10101034044004151103480e0203031030342c0700c84410a6502d00c041a4101040030000c20240d8860076915002c20620b000041c60480842c10001640b0b000380c1190110440d403000078001c201c42c207030140b418a040c903e020401400c05018824161091032081ca0070001c03010540310641d81c1c0c03030102c040c829901030304840d281e50f601c01c0c800004100494081c3c02500803100103004060060b0440c40c8a0071040d04200d00d1070307903003d20a80b860701c4058426100390082404201c00740c3c031640304085c5618080c1c0ca030701e0545440e046203004178074031300344130821a0707401800b04012588800042d034040c1c079031294010040400c0200101d10700100e003540a40f08042c2c1030300b40320a1681 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601031780 1250 601030530 601030537
    0x6010c140f010c091811070501050901090b0606130509060f0d0605040201111203060103110c0105090c1e031c050c060a090b0c040503031c11040e010e010807120f02040f02030a02 78
    0x548200034843e581895a06030b0724060f062244800c41c02c0701d02d20200d601552a072124590803040302ca41420600f050b01c0306800c66604461380800c070b030f548203030000034002c84500580c3d00c24000c80b031840c07601c003019080f5084d0707225920405005107613100100b83d00740d84040119059500181214111190303d0504402a00342601c090b404684101c01a5802200100d40618141c2c2070124103451503c449004600420030303400b5012101c14284503481d00d8210a008050007403038104010035107404040100061004c81c0c1c024010900c51801d00400103460210342444903042c0d060b00941c84415012064600f03102d15061101a030191104200c040a269440174078228040c0d11044a1640c4451300c00509105034002e55134950300c1030015030000c2e58141c00d41c0d80c200c488460013180b4090381240c0603c541d00103400840e41e5a00e18801800008000c4c2c81c0b0900501059004005081c900304070180c00712400100078185485100c41c075010364895411480130b50132644002c55803458000a40c000075003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601033030 1250 601031780 601031803
    0x1e030f07020a0c030f0807020409030e011403070f0509040603050d180b090d1b0f0605070b0f07140d1401060c060b1905040f2304031e0f0806010c14 65
    0x16405004030358010710000c0c0c4007800c607910107148800d80c0c0c2142c0301e080410064200131105014104541030041e01c56000309410036120303407125011058180005040d52505820000b00400140b08101e01503901c4510a0804504d5051a5a07104c0c802704c04180501490b8202500070b2090885903580c140d407201d00818045038400e50050312644401810350315114101c01e007a803108031460041e001c83d2500405015400b00303922054034160707948030b000344048200e030300c244003180e804912a01070060346a109070f445511000c00e010f0070310b0802c01c00f400820203111450310305000856a001d40c0200c981c41081502c1c01800030648540c0e440da0700810310500c1c0c1c403040700c00030b08182c104002d0742003264502204082d5207a0024116042c802880001d004038082c80c0015031303c42507402c030f00d130440b1810360400403002d64040300b0034981410003800d0008025000c00c642101d52190310383c00c07580140c0c4212011810f01c1c00d061652120340c01281d6410150b00042c01010b50203001121a000000d03902c107412 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601034280 1250 601033030 601033051
    0x1f1112060109060f17190e01050a060e0408040b090a122306090c120a0804030803090610140103020a03061d04150b0d081e220e040201120c051e03 64
    0xd80c2c0f00d010480388400d0600c00c2402045a51010181e00301c11500b075581c2c021079441659425400250030b040544200800c0c80c14940d54807000c0c04458105805164080c00340894100c0d5503042994604615120307c2c4030703440802401241e00111640c4000442c0014204d40385400081500c1e0304241c81030b420240a85544460650950300d64145e000c145180b10b52a00c0c0301078840038080c1001d0000742a44298890311500072903510200058100000d0b00141d40201209605ca1808038502c03450600082c00e13032804d01426000400404032480c2214001a40030f20f40562100a1000b0940c058085c6802c144855000c44c0100030b011400c0c00c107103600c00c9016018102c120903096110104440d0480d200c180c01104030303106400401d1100000301000d89070307860b0030721403a500001807200b2a00700860105ca4070941010000b14401c0b0b8030010340240241c4410391519003415800684000a40c80540f500940c40352102c801c00d0380181c0c1500d0180b540e10381404440c1820022641c40c580c4100c075001d521 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601035530 1250 601034280 601034297
    0xc0a11010305100608151201110903070f080a0609020f040c020d030b0406060909110d05040f03230715091707020306130b013807021c051f11120601 65
    0xc3c160111000c01260701c0381c1c45608940d190321008040e502c1540001580000c00f032241198410320074031800b405410b1259400d0b4550300e251007098208503a42e0b0184620800202c42400552000710314500c185070700c20030014001c100c03440807400c03c448a1000700d40c001c0c42c085940f9000d0b5008103034099443d1407948c0800c8688ca925003040101c6043c1c1c0580f40000d40150002d1001000c41c0c1d00c508158821100c5590501d514801440159002213401300c8109081500f9041055000200030f8408602940851130403014a42030500c18001d009001e4540080c0310302001086105070b2008411030340140d0700341c0b2040c2094021410030340c00940101c0c080d100781c20025281c840003000c4490a113501c0115558980d2820610a54103040110615100c2e0b89002c039041c254254000309880c45010226003a0b110340f054010456100c1066025552950441c500240001c0000c510f0340c03880c913081d102c03d0003503403400c12020008110010640f111204001804290010003446a9116800c04d0b81c0b010780 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601036780 1250 601035530 601035541
    0x7030b0d0b01050118210209070503061c1103070f0f0512060a0b0a0b0d0504060b06090f13020f180306090a050a030f0e031c140a0e060904020c0a11010305 68
    0x25020300c000001e4091800c8600603c07503907201e07a81e104001701c2203c40c401d50b125259540c068040380395032000107215032544000011070918041041e0b0020303541c20500c0c00c0d45444000300c1e440645040582e00c00c0140030800da4100441100c4203040048090300725125183c0b41c0301c00002a600d21f00840341c099504040000d6130340b808150220711000384a024120710b48581c148100034240c40d0384942c0d4000001c25010030301000c08006440e4444060300e0209090500e41016000c07591185100b90041e00c041180f9040340c0ca410881c0307842c1c01d8050b681180b0440507200000028040e400a41040810003d02d20140c1c50038240d644401a008600760340b500c1d100c0c01071103a43d40e06c0702a0018606d401c041c0814000c42d02460700c1e5920f40c1220b007050003100c24068000303804c200340c116241040300303030041000e1901603000110303603085125141e00a01e01008000c0c040c00300842e0b20b8032507210310400200000561a6901910301414105003180c401c90402c0c50301c0500e446100d04070a001901d000c00160 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601038030 1250 601036780 601036789
    0x31803060509071a0f070206090f030604060b1008040503070b09120d1a01020d230f0f0c0d0906200705150408100207020607080334230412060905030f0307030b 70
    0x10501205e000b01185004025800d02c00f840e04403807100c0303902c141e1184031000151070900030303107100f2803049000140e00c040410801c0740e404607000c201002c216602d010000014000000c0b9618140c04c486602c20541d03691666600d04251000041c0005202091810716100c4a410002c007001d5000e40c00007544841000480c1d8855001100400081822501c2c2d030b031041440c0000c078078006064056070700d00f04141a01444660007643d140650740d00004003840f00b50003d0016030080c2031076142c203c18140c80e248009150300700849040c420071100d142c0342e06602004110003002050003a02c40201107a20580d460429046481a08074901415511101d40030091084642042d4000c02c2d05080503080d45441d00c0503080100310303030850200c0b000c4070f01c800c10207c1c0300729800460301810407802e0b04545074018110226412150306c2d401401c0c0b04d450200d207604040d00c00341c2d001c0002c4881602d01c3c40c00c06201030550f443e0090954080043d60310140c422410040d8880d00c030340e49040c811020740400b40b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601039280 1250 601038030 601038037
    0xc0203040e0117060c0f0f030106260f07121b090e01080f031b0c311503030c052a0a140d0201030b13020301080f0c120a031803060509071a 61
    0x104003500f2010021301c040c1c17001400b031b040c128001203901d81450100310840e807040d4030a8010310301041071750040204d600b0f00c0e03c8418040c1d400b090130314006c1d414030f05800356a41c0c10141000e000c0c043d002e1450040c3e110198450011001c1c100303803945440843c428094052001409080c007002c840d400041111100055024140f0a88400451030b24181d14440c0110340e1040c06c0c66402c034000d403070071507405989420040b401030404481d14001010008030500c0c2e07443e10348426080290500486e1107440c043e035040e1000b12901030030561201815840c109080111600e5030704000c810380c0030100d41c460030341c40903081510b205441d90101c0c81d445c0e00c202d00b20407188440c40c0d64003000d08940d51006510a4002480b0408064807403200000c8040014069070401d801a441031340c4845864050300c8400c000c26a51800c3c166031696114004082c5a0f40303c00b9010800f4043c440341c06485121806203140c4000215000302d81000141440000300391209a548548509605d8110400d50031b248000d080303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601040530 1250 601039280 601039319
    0x121202190f03050f0c010c020c0a0e13111905010e011b12050f040b07020312090604090b0d0c080c1003020c0c040905010f05010b0304031b0c06120e010c0203040e01 72
    0x200425034255601e0604284030940102c040000134810544600b038802d014026055030341e030000c218000e6400009140c8104201301e280304c4c2d9081402080140c04030360920340c01c0300800c1c0c40307000c14002034180085940c000350001c03500030900031609080461031669280035605d09a854400e20900390004684620f001001d00c420804017000460004e60821144c06c0d01c0042410305d030f0b0078818a02c1b607000c0b0a410036446400c03544800074400d8218a400d1042c00c8064581320381c0142000c0544010803014052030044842203030765045002130700da940341c0b401c515465109441002150f12030b6a070a45445490002c64081c3c0b0107010400c60180c0030303000f9103002041003130044c0600c0244070200005041d00000a44065586068551030303600301e80101406401500441566410540340c000d000003c1007800028803003001d02a040040d0002681c5d004440c2146007134082405004024001040c5100f000301080d813a2100500c0490340200150040360825161b6800316a0303611903065012568221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601041780 1250 601040530 601040563
    0x31204030903050c0907051801030e03030c0d0b0a0807030b0406090b1005100e011e1e0302031909030e040b01110a050c132304030909020a050d0b0d0b07030f02090604121202 76
    0x232150307605201404d64074032600515001c41c0100709540110b065a00070340b00c0c480788400004110194003014082d103c40c085040d103d10341400d240515035901d4070250300008000344480c0011400f0700503160001c075091608243c1c0315489007003040c502203003a0824400d1a002e003000d08507102620340621014904000180c41f4500354a6420040070803840e12141000305010003043c42006045407001502a40c3c6502c3c0c800503030b04d0409480303e40200700c002001400c200e0400c8070800001e41d014030031901b5080140c43c04a4a02e18060042c5c07015407809420b00d43c0d600ca0790519205101d000941561018800e6540c02c50220b01070340c4110540d51074441c000d481c10b42d20003406200e9000c0480517135101e4000e2800300c0c02d0380c0d16450318800fa17038840c80c150800100003107030a08060b0002d10488141c0031040750b0303200b00d54149940c0c090410b00300821401c14160354062111504440341c040359030400004146076a50b940300c4000c1d40203146201c0c000c1d2801c940403414010703254000a404204001c4130349 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601043030 1250 601041780 601041787
    0x50a0e040f020f03011d1005061f120e03160c0518061507021e030d111b0f13020414030303100b07020d06111c060b04090e031204030903050c090705 65
    0x1002d1050307543c95041826003540d071ba50b2803a12000708a00c8036001540c54080981941044200071506803074010b4030003031003411840e00032403000c10120320003850b190b080d091034000000e00d806d01c05c000700001100780d2074070700000841c6091158000d000252580c0703d9102a2001d40e203900070700400440951074500800c00300070202d0828580000712520034003424002c1031030080300d0b40c007080d85048084201c5400c817580701603028861034284020302a1351070070301d428100e00c42d10f074031305581d0f6880300c030020702115201c140318003041d44400c4e501808081001c0c1c0b0b2150031000d640741c403d0080d48140b0900741d0780b440b8010010501d1801100700d03402a400c5501c804000b5042071500b06003603201c00c00c2264005030301c2d5581c0b40010707414012414901c50b000700b0b240d201c654032403d52a4194079829084200f81c030b080c0d004e2126907469000e4609440c18a400001c104098941840c035512582800700d21940781a001c000400da804509941541e00c114152a485d00c0147e007844107011040c3c0f42072011410a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601044280 1250 601043030 601043033
    0x50f01150c050309060c070f0b030f04030f0903060606050c060109020c0c013608060901060e01060c0c030605011202190b0a05070f020a03050609190f080f0c0115050a0e040f 76
    0x881031141800d000340140c80c50800300900050741740e808600c000c0943c0e0014030040103001242c000b01c2006008140c00e0034550f10f0402d02088101000510040500c00c025100e82c41651180e404080030f564000e41c1048265220100500b181d000b402c0e05c40410310420001060010090090310001d0380543e0040c200100020700540301005081070404000d88500e170036040c2c00101c1043c648211010319425500d082c1030130f48180c01e02d0001807181c8400d0381401e0081044240901100f0304581a51801c5e0580341c04070f103880e9124190991000e44510b007480300109030400c44800c1100a14401c8514071440464200000b003903240602c544216844103210b00c0a526004100030503c103440713409000060b01055002419000180e002074070541d010344208a2800300c200075003c0c5c1c1081c400307074904980e8002e94490f0a500c1c0440402420f00f50003180901010000006469a510200009104904e6001d5450904510358441c2a12502c800d0b01c00158002d48030000c0c90081d0b030044412611410503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601045530 1250 601044280 601044287
    0x70c03030e0102030c030a1d09061f020a200906090c0a030f0e0a030806130204080616030603170a031b120c210912021f0c180b0706050f0115 62
    0x7040c92034103500041140000c10b2009100500e0f90919540b1121524041d000310b010a0384603500700307076000706804401d0101555402845010a81810349500700032120310100324201001641e00401c403000440410f58203844219145d02003850540740310b00140d5422041064045095900d04e000020400661000521981180003034806481c0f011840c2e82003144c15a1801401c0d000c241d001800101c20712880d440d10030308071000400c0c154030560078603040121541c1c0b85c06025100201400c20300140c00f82c0385000c0e8005200071500011440192840d414040c030032075006107440e030006460440d000030440099540030030380780c01c1c42d503884030030803860440440204414498030042c00361000200c119200ca0880d528600c1c20400030100360079030700303140c0a241e0f050755640000964000b1007203580b02a8924292402c2070a2108000c200d020143e84213130f61031101010b001303091132942c60011601c1400c4074010720a00d44201001c21159580000c414031201c030a00481c00424080750910035510310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601046780 1250 601045530 601045547
    0x3060c070b2203050a270506130503011107050f210d110a0c17030f0708150604090b0319030909480806091308070f210203070c0303 58
    0x4214900440042c4070039250202c003080ca55085000407400107140c07480b9540300001154410800b4840426810301059000c1c0848443c02114042d50000c140032004010a00681e4010a8050000c10100310300d803c07070b0301155008220a075081d20803040182d00742a0700081401c0701c03848844184034605010fa50506540d0701080708858150780381d031441c0000300401802401080d601c1e4030b0701c5200d03c1151501d45000d08444528114100080c4200031801403681e8402d540003003245401d611564a0490071202c0440d22110740b17801403001704c0c010444107142c1d404450240340071001c40701c1c80da44605558011004a0300300400092803402d041120f0200c58012984d0041d60a006008240300d074400700c00010b034000ca5a0300e04130120782c144c030940e241042d120050320b0f0091030a41c480b4603000700800c140b102c002d4013140041c00c40e030b29004107200701070007520602544900c0151000f051410907110041c508800c1d064a0341160440e03c1d9844c0c000002c95028aa014501c4541d052954805555045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601048030 1250 601046780 601046791
    0xe0c030f0a0b0405151003060b0a0c0f15020304020f060724020d11030a1103071e0e10180602070e06040e0a14070810020901020a0b06010e0a030c03060b03060c070b 72
    0x1030302ca5601000303a03540c0303000b0103101d4501d950b242400d42581c0010407100c00c9a1201000038146050418800c8401c1e00341210290700850030640a050340500d030a01c4950140b460250441206904281d000c0985400960060b8001c42c1c49a8005130324800700b248901c02c11200400407840010980c010002a002810000d0018075005003010f0341c071030408003554085111860321842c0081040070328140c078800c10a080c40035039400b07400e40c0b9003a82c02400b200c0d4942900000314081021000b41c043c400c00710545a148082c2490000c84c02481003c0d002e00701030360b03811480740c464100c04a0030341d100050000446100749401544c90300c4000622000b4405001004810b00400e1100700108014000c100385404221004040d01031800981d00c1c2481c113082043c08850340104014a0350341e071300051042100c5e803c0000d59141c3e85070741006070b6100c20040c43d0a074200420304400400d020020400d101203e0081d5018015030480a0801d621008100e03152020302900340640004526074950155104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601049280 1250 601048030 601048051
    0x230403031e0e0721020d0b091002040b312930130321050109020d060f0b030c030414010f1d0d020303160e0d14070e0c030f 54
    0x7205050700d800341c031032403000452507902980c1c0400040c902c000c91070701100b030340000080c0704400c55800240d01c80822540580307200a56004540102001d01500c102510300420841d91299203408001c12900049554840740d4401e08110a00a1603060340410100b1682c950000b02410030701d422041d00c500c8010006503a1008036240d056074040f000034400003001244118090b03004440c5109040b044012151100c484202400300704002c0090344100e00d0b41c9402d01e00c203007802c804610107441100708511403425041100028076041203500030040891109014050039481e540d1414691442d441403400a01c8100b0010b0080300041d0003442d0030a1281c5070003220001c00c043c0c0d250a46032070b01348041c2400d641c0e407126840240e0b0078000c00711401c80c02010300400300c01100003a440e404001c103010341c0260600c42d03500c0a1351050080d01c200641c01081c68500340c2d07450038400e16480000000044a04c2840c1e00072480d949510042442218600101c0d42b56640c3e2400714a01d003040031304111600b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601050530 1250 601049280 601049321
    0x1c12060e07020a2006070b0705090919060e010b04330509120d0c060b0f0604080a03080903040308070f0303020403021315120305070f0201020f0a0501020d23040303 72
    0xd404403a03511400390040e68000d141c07080b6a82403610152441c1d040402000f0410b450b00c0001d502c501c426030740305c40d402403107a407200d80c0c8286055846200700000307258040169420000c401031071905040104651007800c11070180c48130240d05811000380aa40c143d0300d02400104400c140d030740200ca000c8020f207050140e80f420003e2040c1d104c9502440300e00c0c007165000c14400824184a00040e50070a5020020808480076110203030854031102806000c0d6919003200410a46030304403400a40c20020b02695034559481ca002c2e51900b2030f00500310005190300011610002c00042a20140c1350460b0420b4a404419a40c0b080c1d90404282c0840500d6028000000580e880c00400003c0d1500d504020510303401201071600e41d00620341183c0700400d03c0100c1007011941c000c056a040c43d90240d040c2c91000a20700040c0d00d4a11600c4141507a8440c1c14600c00c104107042d0090449640700d41000c0c003c0c00d040010042c0504044035802001c04001d400040119202e500041908a0010a201031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601051780 1250 601050530 601050539
    0x7030c0b010906080d03020405060d091e0f060b01141b120c010207021008190e03070b070906022b031812050726030c0705030903030315030c031c1206 66
    0xd0304100741d00c001020390741c0d20070401c0000000c0c4200c0e001585549000c40c58641030000142160042c680d0b140740f140e03075452440d801c20503510140b06010141d81285801302c8490301c0c10304003107070080c10f00f102c2460420400c51815406914181001054080e1a0703052485607514844204006500034003c4e118104080c950507518800a0400000c1c200001d40d5401480c01800010482e4000071070070080080d040045249100f1a040100e40c2c00e0000482e40703d6401c40220b1560161010140102c104c1409003c0c0c01500911802d04541d0540c0949881c200c40c100c00200ca00c0c800701600003070120725504025514480e5205e0359840a10100030074400c0055110410000c80b001c89d0107000c42c40018021050103807040c0c0040020380284002079203440075550b02503560001404d1b12001e500c2c00300c2c10300c08011003070081e0b42070104080e0440307881e460302c0103c003c085603240303d1143c002c0c050320400711a68100800c408a030300c50078000f000210506040200c64075848410a62044d80d0355181c00f08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601053030 1250 601051780 601051793
    0x15150d061206050f10180221010e101203030b0d0b041407080c130207030504030f0b010504110a0807140f030c0a39020a0305240705040602060c07030c 66
    0x4010300320611a07a03240c1440d03468541d08907040a40f110010021000410810000130401e84040d2512402c1480710f0040e4142401c000c2d000c2c0800641c002c030900480c05440180803507445040301c40d600001e000c03613103800940c8150600140100d03940c00514984080200e03019030400c0c6804800908a02240d4459850342e154041307060f0342c02c03104051240031240e40c2d008100203403009805d03450090a8005462030010703003c1007036080c0d10354209401180107001d25019200b6540255042100d0b003240c0c1d2510b28040064000902845d0711540c070380000441000c402c1c3d8140c43d50b5190b1600c81490b291142030065520801240d07103c003050380100002d0100540d0780c005580104d00e50b8883d1910798001d62405009032605010320b01030041452070306a9100078030046e822002030f843c1c026855482c0103002280502c80c25410140540c403c80300e00040004649043c20030303080408449034620744622208480910980c03140000580c8400c0214101d800035900420241780700381840700300d0891550710304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601054280 1250 601053030 601053041
    0x3060f12110607120e271602070e0a0605031c0c02040b0a0b0a0804060b0616060c0504150f0305060915060904020918070e03062202010c0206180f04020315150d 70
    0x481c00030314106190421806e00035544880c80f18940161014817095080700b4084400050000e0b54400704e0b0301011030303101e00030b204d03d00141011031052111340c0307441d05418019241030b2040d14003030700c6886408680c1800ac084103580501c120342d1102c1c0c00c1c000b25001c00c001341001203100c41d03015050103000a010b2048200400c840e28050715204040d284c942002c1e0b044071400030101d0701403d020052a41040c034951280001c079580a000010102e502c241d00701c0e001d02a640020420003103005203100041d03005001196942482d650520491382d507503041c8005000d007610b481c02d81158920410340c651803c18083c0000c03c1000d0801801c00c0c802d50001102801641c10002e60070503440b081c4401543c0c4024001f0142006030001c0481d420032408460000d0703040d00310740f00d044a4200b061801c5a05c2400360080c1c440d001802c954072460800d048d4025950b01c030580e54400d109400441205003054029284030310407800c0d4410100c07031800e051041e841c8005002c407011041c01c00590018891a1060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601055530 1250 601054280 601054313
    0x1d010e22051f1a0304080d0e061008100b010516050102071707020901080c06030601030c11101a0a0513200c060f0705030f150d0611070303060f12110607 67
    0x1902c9448941c0c155860120030250443c02480c01e0242c0d0144007110300c0c5045a4005a102c51010344c1e85024404c0381c0000c201070102e555890040c0380c1402003a4201522503014ac950110a0b600e030341e105405640c0480c2d4000c10011b001c64001c0c010340c034100c14441c0311126100d02a40015242ca82c40b0742c0d1300b111420b00000002c880050103d000020760070054a400d000d400942c000340000b01c00d000008a050000408442c1090f4992107619946442082c1c0540501d00290172110410309482c4264060002c800c03550b1112034400d034060f0b100c0c0c60620704100889a024003a000050744000303040300a0b09008030310080d5600c00414a0440c41c0c5004000c00e0b124610030003070702c2d070340c10300c0c000c0c0d2000308101402c00c1c020003109009200c03c030120807904030380060706000111540d500e010080744044103d520080c1c41c8900d400c241410602c0c0c080000c002d40ca1007960704100711030b05c038075090040b4062401080203140e41071904400161607244c410501d500014002814001076030340e203805020703100f8103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601056780 1250 601055530 601055551
    0x10606020606030a031403074808030a0b0d1505010603050a060509151f030b03062508060406050405070507062009010c060e0105090d1d010e2205 64
    0x4102459050040e503070400c108070040c4c103c080503520014800540500c03e5030418800101140e101030058440ca40541840311503102ca001088940010b510b900d00c0741c1c800841d940036202c24900610400c1050510741c040081403c41c0c03907500078100106000030442d60001060540000811480068095865408100070034158102903008090b5807014121214003030031324400303200302d82d04c181c0c410f6806108011030344114000f500010b0480c041203100103e9464225a8071100d06615401541040304207400b00c580c40c0e107a160108481d90580031400c0861a041149508800d1050380102e400010007040030038003035120070000d412100261024004138400066042c1007003818081c01201901d02981e40748140580070020f0100c0c424030b50b0040c100301c0c1c4c110708501000300c164451545a20b1903c020081c52500051099441c5449046035022640108110101c6000304c48200070103034041e0356200020b9000420b2001d9003c0d40b00100c452001c40000c4080901130302e12450b88260038148 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601058030 1250 601056780 601056791
    0x512030a06060825031103090c01110c100c05070506030a0501090b10050d1d0a06061d091209042904060e090c09190203010e06120c0108041b05060c01 66
    0x300a2046034266400441801490002c01a040704844849885481042c0314690009041c0350220018900000300c0c900c0041e010042c4101e16100082030303480845c0a888003401940360a100c3d60303880e40f140f5103007079022004940701840c2c41d10501c0382090480c41181200e0150388ca03000010b189800464800090580d02d6004011021050045846564054940600001d080d0500500b40d20910660314099a1551030804034000303c45034042140c2048015101808014a00540a03048034460580d101c240103003402141a40e01c42d500d0300602400c0014100d88000140640581e04030001081e40f041d641c1d440700081c2d00080c1410b10081d007960040e084031030300c10f00070001103c03207070741000f240c00c0518420051508000100041c0f10032045440c1910350781c0d2408944d21003001941181021400400009a0201031901540c0900b2085030845622002c0b8040d080d078a0b445018110700240c0207401080119200c1000013038880d10400c400c14000f91a07901140d0264450448240603a64a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601059280 1250 601058030 601058041
    0x160503030901150b03070906050c1603050f0c06120415020d090308041412030a112b050c07080706090507050301060b0306091e040303110d0c0c050c0301020301060c0b060409051203 79
    0x2281c828084d2411040c1a0b09605180c0c0006100200d5800b4070405e0000004110424030001c010301100640410b1403c030811361a1b250103503c59580d40708096007072182c00220010380c5400410740d085482d4099540c1a90b6985403a80102d00042c5008040c521fa402c20000404140314001d00c0b0340175000341c484641604003441e050420b00b4801e02c442c0f80075041101540986ca000c44101c980140243c0c2d400301d116602c440c0c5859007803240485142180d28140c00003010941162040000100104000c02060f43d611005000320f200710b801c01003241800300000c1c0002900c2c0d5000e10b2810703000da421600096110350100f42120032603080316034200e1005c401c002051500020050340810201c0c6a13442910114601c80c0d02e2a01c064070040070b050325544000160b10305070043d0381d5031110042040c0000140e0010141c400f042000058901d070007907900407410703402e05000b124101c40843c0d4980110249644440c40288006041c40b50b01a0316204081c001c100c0030850f0103c604980040f25a990420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601060530 1250 601059280 601059311
    0x20406090e061f12050c060403030207141801030303091a011415070b0103171909051c0b0106050c0a0501050a050f0702010c0906120b092a03010f0b160503030901 71
    0x81c1408101d003804040807216880f0503021400720b55600d8081e82c4107210390318005050040c0703245600d0f00030300081000404c3c190b0010f03108044403141082d0841da818040e0a100700d00c4138010380002d0350307001440101b001903c26804070800340d00440702003200d041e442c2001003001c0020390299540c20807034664039942c0d141109800c030720030103e100e4452800c4040d558200c110501403001074802814680103a40e041c2c0300c1c5080320411300c11100030041000c0c01c00c01c00340001c1140e000e0715019a05184030540920102d200e14480c00d500319032460000d80c680801180c03150300051150506010300d4032400f00241c4240182c0d405114005004140e92034402c20b00400391600070905001c6a04101e00c011400c3c1d08820420141d400c0303840c04040c09000b91000f0ba029140203400f0701d8001c044681000004140000c0049426220080131070700495066440710003400280240f006480d82d20700104800c01450b070081591041844040e038030514181c03140c0b82190822280803c80b40d450f001101410001b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601061780 1250 601060530 601060543
    0x140a0c081f0b0a060e01170a14010e04050705091e01030503041a1207030510170607030516020606120f0a0f06051012020d021203040305030c0607050705100216020406090e 75
    0x80e481410002c0d15550000101d5080f0316202e00c00500015181c01d0307049900c1200e8034007001009480105540c1000400c080041150030785040e400c3c10000004103001821441c0b25001e142c0000040000b03d05210400c001030201070030130400c801981ea580c2c2204204450786500a50055002d03545444c5807403601a03500a08030210608001c0401a1a01c17010300348003261b410071140c0c50009516543c6003042030b26481a80c201d81c0d911341403012807800030000040d503180316198903074052055494181380520380090b000705410150300103400056090800d906010714164014048038402c40040301c00c4c0c0e0510103610741c103450341081022030000f4007109004403034000c000900c072105030500c0c0403100c152180078103500030f1241c2d005401440655139880d1540c0c1040701c141c0c0c00d40b96180c2d52403410b1503803035004107001c1c8590b00030400058a094041c01c151109550000d0207082c026040710b0a107030013580491101c51901008404150142c0c1780e502c01c00700500407984c80002c103000028003442c035040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601063030 1250 601061780 601061833
    0x170706050a082a0c0c01120c0905012f030310050105091804021201020a0c06320c0d0213030201021515120a080309030909090613140a0c08 61
    0x80100c0c2105a620030840741e4082d1105030078004058072100f50400040c0f1240a15450107000300f4035020308000803464210741202600c0f0000311303824030581344056841c0b1180c400041106003108103c00d500501280c400c94165000300149031031607641899011b4007054103611240e0010003000601000414507401810090800506144000b40005c000c0685002003501189070040403904540b2003c08600c56245048001d5485000010f8024401902508180e6030701d410412030440103241c1014003012560107500103010a034030190340c0b9040d140c1c013404090b0101010804508150400d1014120f0103654515491905141d800024035103075100d5402748030140c04000780100380340044205c511440080d282c0e80d20000604e410203060401a0102603e141800002c02c207090304084003c061901e004c54002c085520744076041303551440c04032106006000340341e030100c01040c0301d42d10b8851070b0b5030760904440c8041c002c0c0c1c2d280d41000310194000f0075543e021105a14210701c0900c014035444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601064280 1250 601063030 601063037
    0x1211130905071205070b0702120609030904060e1909020607061802010f081005040c09080109140f1209060306040612060c080105030309131517030a0e040c050915040f170706 76
    0x50f501038071156216000340c400c031902d0410001f804011034481d8080902803000c41c009490107032074002800c2c3e449511850b40d00e032189182150115034482c610090302d000b400c0580010800040151001d802084101001c2c0c1c3d101c081400300100045480c09100c00c840c2e009500340c4041040381c8005403800100401d00420f005001c5d04005542841c8040d8404803082294042402c00408274151041c2c9140d412402c815400e290403c0d061140c080140d11140c0c040c042155070600c4801c00b004c1c1c035408120050590700c1820001104103140400245810020003400020b48690351a031195050a5007001282c1550711107101180e0b498100e8000c5005083c103801070b51501d21501c2c00500010302201400c5c114942cac401c08540200310981100010f480d4200c3d250707002d80300e08801684e403900160305060004000454000d55800d00c0d00620405d1f103016140d180c1030412100c20480308900300e072100861000e040c000003841d00e071340c070302000d004080b499000522a0f1161200c0342c140000c940041040c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601065530 1250 601064280 601064309
    0x12051b0313030e010507052e0f060f1403030a120b0409150b0901050a050105030a061a0408120405060318010b031c0219030f081504060b090405070305010807121113090507 75
    0x205a02250007400500e0183e40801c000e50b4858807030850505d42c410f0023840700d02e000881d03d040000c640c0140241d0307201100348981181c1c0d500e00e02811000308800c482e0150028845a02681d02800b400c1c03a0b101ca154501003001e0112001180480d5800a003d0300c92800d25108602520b1440c0b00301902c9000580d44186158181404030350362503080e10a0794100100040000c800c00481e40c421009040044001c4040044142900096030000d01031000240140b8061350700f0481c1400841d011150003400041c15950707000310f075561302180d445c8845e0455403100f100f034503565418802d2641001010001c0050b20500c1c500003864240c89456a12100c4400568280441d4210301101d2007101c0c0e604c0c240324103696800292003c05860946a50003908040340440e0641200001c4e0081003c259020030a690b5040d8080b003c1d920288100c10381500a214284014040c1c14a284011806441c61042c5409600b0124041040d002d840c030346d001d0b03650f4109600700a030030f108000081c10354100701c80c079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601066780 1250 601065530 601065533
    0xb041109040c061107031e02030601061e050d020c1e010f05010806060f0a030b0f15061806030c270a0e0403020304060f090e04030f1e12051b0313030e010507 69
    0x50b0049140074a0050100d242d010743c0b41000100100f0010315446684014a9202d528208885403800c4004a11a026100000ca1009c0c03083c0c4182ca5907442c160080d13031107001d035600c00355065400b038a4000c0d00c02c1d40070031030440c16040800100c21150b01d2441c544015280814250b03084446102e040486181008010002944005200394020900302d40c00c440700c18480b070004600f0045980000c001403a91800c1041402862901c68411080441c0c1880c9000302d64080000c203118101a1080504c4103814096072424000d015592000f11400101d142c0360050062400c1c600001c070341561b03c1c1c1c1c0c1d2600d0741d0a0b02e0030075a21441c01040c10000c3c00e0103d081586e4040d459004900825007041501a0054846c0703200d1945000105104040d080701400d0509005008510508440001c150036031210140502200d01101c001c2000e41c0c1d645c07003011003200404003d000040e11070400502c002c61400620780c5100c0c0218020071000038103880209540c0780c082d2013840b4116810b414407809112040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601068030 1250 601066780 601066793
    0x12020d14100b090102070e0a0212072c100c081605030903071a0d1104050409030f08071b060e0f0706020d0e01090308040501051c0e070f1a1b03070b040b04110904 71
    0x1582d18540c412011236483d500c4540081c010341001e00c05002c43d41e01030140c03081e04881e10545404101e42c404400008101c034442c2d451811085c000c2d0845902c011041b40c0ca803003908042071081c4600012480c0450030216144400c040e407070140c0c0e02e07400010301070f44c880ca0300b00007050052807003142101040703010385401c81560155000d190003154480f119a020b900b1100219005014024070422003d013150400820400b6404190008120500c004c100100d00481d040c3c0329010004006000300b0340c6139070742d21002d4158080480b019200705004420001001d010460107072100780e00130103c001c0c007050001c012000b2001c045041c80540c0c1001c1c80450300e000101c8068075401c0c2091940c4004180d00000b9411030b4050000303240340342101200b1000300205d0818115400c62000a0038541c1720090f2407081130307242c0803140400b00104040140c07015490b148028030540745050304d05180d000e0311180c46000c0304881c00c4450003900c10410082021040900e03c00c446c09031285115441c02d95108c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601069280 1250 601068030 601068043
    0x9030408010e0105220f0204020f070b0a0b09070c0201180e16030204080a170702041406210c010c0c15050415020d080a0218120706020118050d12020d14100b090102 72
    0x5c0c058643c2c0300081d01403003205850305d18401e80c0548115520307198a00420129003211798102c550040b17000100d00318cc50300c2d00645070f101c4402421a0304585070044107644107088108100d0603c0041d00901400c1d4034051001001040b1800e1f12140714a810301d102c0e01c0da04230101c2c11106043c410b01c014814035a0005114401c2640321410040c4e81c2111011090f00d03016840000354061308004100360204031003404a400342205540707625440c0031014841c100004d45001496142c1e0041d800381c2c5183d031140507211602409005046a52a240c80741c0d031050700b40d44640c2c40041000002c04214000d44000c400a1130401031014014500144100800c07601020b4140c4204c3c0d500450601c440400e83c00c0d1108e101a8000d080c0440c0500c980784c00d0b80c440c2c1b034500c580c4015501c0d240f4069640740c540300005212540c86000352907070207880082a9942c00e260041501c16130307402d10000c11101f0b0188151110182c07818402650383c90102821051000950000d03d5041c0c03062254920a90300041d06 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601070530 1250 601069280 601069321
    0x17010306021c05070306050f010e09060d08040b0706020301080d090e181f1b05130312031407021b03071d0402150a091415031305011409030408010e0105 67
    0x25903180d541110080b8409580350001a600b458842441851605940808102d070750641b81042000300c10001076075442d910031000c0b60005094000a4030b02c1c900281d54100c0c284c401c60002e410142c90300740d44031071a00629402c4410f40c0d400001403026440401c82004000647d00e450704070103081c010b00a03c030300005801c41c5454404a846c158580006000c1c5501c12400d02402d224541088010000a0b09540114841514609030300b074001610074402c5811807210340c07805070000b0b80b5681d155030b2201c6c0c1106030903003010340d989041000e130040c0c0102d06000b040c0c103600a0642d0300c1c041020118440d01e12844a22940c8508810032690700c4e448500b400242210f401c01d1442c2d41d803400032403881c080d00c2d4402540c5890000d11120f0071600001070109851011084100400040007441401941124040300d40e003401e00003c1c0e45401508600c4201c2803241c80085100011580034401600056030128581c2e0401301c0c041c42510360074400d00e8290602d0b88002d103e00e0138150608240c0d030f250b4421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601071780 1250 601070530 601070543
    0x9020105090f0d08030a0603030e0f06090d0602091c030f0c03091211040f021c06141507200111010501030f021c05100209130b10050d060509010305011a01170103 71
    0x5619000b0303600c00b20003280303e58110350601e43d02c0c80c00f1a0908000d020f580812130218a41d1108040c8504051500c44c0300c111010302034501c0c0c90150420445010000c207002c445450f0208184035072a120800c03000c42300e0034100d08908000141c2d14018040d900140d03111010006580181c401280c1c1c01020030003165150349070710051480600b003104a0094003814990000d041908400030a0340650060044110807182c40a104814104440941e50688030b12240078130b207501025102e162030030714400342d400c00c0421030749010207139990310712400464003040015000c10b40c102105940c2154a0703444003542a4001c010301d41c15030740d070a92030014040c8040c2c0102c40401e403941d45480d911000300180f0341c001003118031410749045100d0181d4020768140713000f0061a843c0c0143c0c840c590081c0c200100e402403d030351081e0b50294044a80da00b0841c0c81079034060321040c000802c0c4e2984000030303010314050350020801c0b40c2820030610100655409450420058040311420015074881d0365041d03031707400a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601073030 1250 601071780 601071799
    0x10b0307021002210601080903072003010e06010609093b101a010306030506070c0c150c140f060115031d0d0207080309030d0c0615060809100902010509 67
    0x140100c0c60400503440580b0402d10001d03158030304040c6001c0c03000802001954044d2503948104c011a032000d0180e07403801643c4e009002038800a240c6d074400340514800c0c0341407840b03403540c40e80019094802101c1c148a03150040001804501d030301020401c0071f00f0396002c040c00b12203200d6084466444040102950182c41c0c04803009141542d401c280130003204c020225038811603400c2c601c20007800d4003043d444c1c649210160041040d4028000d4100b00ca400c8009040140c2d03a058041c3d8009141000484403076944071008500d02c140c03609141c40c01c0550360f031051021811454000c0d119509940c4030003695014000709021350b0380004190781552450b02000b0103001210304260050a0b000c00440030880a07141880e00c02400000c0701c3d01116196801c94500d02d9031106a40d8883c42080c624079095000190300046850060b41c81c021000c0c1703d090f00107441d400345080460000c00a8004400040707054091155102c0d0030080e0019038508a581008425090b90029007548205000140a0003840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601074280 1250 601073030 601073041
    0x203040c051f02060105030d09140112020a020148050c07120b130c140a08070603290102030313060905010c0201020a03060806010503030405061b3909010b03 69
    0x21050900401000e001c807241c00b418030900c014803801c5a6460070052080d2800020140b400090110581d0560f403101130300e49040441905a070130380d291a50381407080800c00104601c1451004055129007903000155000040c0c060708004580e0740d03032101704d410390004000303c043c00441e20340d215004441c880c1d03424584900f02c25a40c0d8014406001110700492000007418001154261101d51050740883c070340e81d40c4c401c0703030f904007408589000d004040c0000742802100320703560b04004030440041000c15040e682c2d00720140340111715004100025142c0d50710705000009032400441091140c860700c43e40c548034400013590b13408028041071041800407174070024802d042c3e04c0444120b403c00001e005074950720f80040d0203036004400041c0041d1a000b00001c47c464086281c40c141c0700d00801071450701c2d2404003080f00c15000300c2115040d0b50319029907079200c0c0c4410004014481180c81400c60420b1915441c07038089420b00114100b0381180210300c0c0e0f91541c4a80e41d9a040d41d8a00a0580d12921132 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601075530 1250 601074280 601074293
    0x703022203030210050106170604050c09040906060e01172e02030a09031b03090e091c0e04051b1b01020f0d090605010b0708300f090f1c03020304 64
    0x15a0440c5009000184048181036000c0f840c989410202c403000d2245990355032040311400d41d00700003e01c000c1c022402103041031800c0e400c8560800c1c0d03450100c0b8200b40707900c0300040c110745106604a8070365a88190410008001041d11ba005007005000c0e40c014030700c4103c00d07a44a0030344004d01400911040d480c0c403440014001e4070154042e03001011074aa1510b030115200412200750241c2c042404219a41e06003401a8921542d695041e51100ca804d071501e501c01e10840c0b0301070b0460002d402000c1c1c8d00c0000c00c00144116a507185641d030f41c03900c0c0ca403900303085c0001c95070094418660002078503441c031400610321080700c2d08010441c00b01c40c0b0061400c005a030080c0a070b486031a512101c0058041d652030042e401280d040c5000740c00400c00c50341da401d80c100103071086000c000c203011002c4c0b201412044500304180292400d9500c910380400f1041101c0300180380403102c001880208800707004010308100982a00c0800380340041c111140456040c040440346042284209600003001a0400c0705 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601076780 1250 601075530 601075567
    0xe04030507060e010c020f07140607110d080304061b080c0307090b13090b030102090a0506070c180509060702010e03040504230a020405090f04020a030f050327041112070302 76
    0x10008003c2100d00040c050160207440103403980d00042c400c2c51000341040901107118411070700610400c1c03d0a4000c00300b03026854004003801d680c44040b08150780041c0c0c8800300300641c810f111b400d41079624500385c6000342c1100c100d401c2d001c0d40452203030700408180e50002c20040c2c01c10a0100003c0e2207560700c2c1c1045518803102e4000100c00030004ca0039440100b010010301043d210801014000600e403003003070500301d00601c2c04050b80a14080d40400207410301c10000e002c40d0b402429143c1c0180d464005403c400c1c551076800c0031110340e031881003091500d014003a80c1e4200c80d152000344804805040c00700c0e41c2e80680d0103203078425a03035160355100d440e0307014030354041248200741e4003003080c980307084002c1c000e400901c40d55008001c031000240020709915400c622031030303000f05481d00c01c9d030443d159500f082e0584a0120340c907103c20441c17602c0c50000440c80d1100d940c028a4461001c141c5481030005540407030040c0c039080304042c0440801c512100344001c2e8880160710740113864588c490b0000301d0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601078030 1250 601076780 601076783
    0x612150320101133090a0b090c0f030118080310120b16020d0207060e0109031b030c0506040e0f09010605090a050a1503020f0d031404171903090e04030507 68
    0x11030714058aa168020b202c0510302030411081e103030030304a00248003c500901c00405601c05000781e501121044919981c117421a20303503001c445c00902242d0340c413100c030703c400c0ea030b0035840c1e511445015407a03280c0007891000c02c04c1c082c0c0017031107000001030a104141e6040310008041c0b19001c000100c501c0c1c1000c44440052108145101482240b400c00116900c005d03201d1201c4d4080608000d0119800010040100079550f4024400546803080c00c46000e42032074181410001c01d0364000001c0b84146120804800410449090803403440ca02240c6941055000d64080c000a002c1004050070f07140340140e00003031403000d1000a68610707414034014030f03141d00040e07404140e20044c0445010150300c030b00d1190300e5096017000704490042c0610740f0000c2a200c000e48c0700802d40201c1515003006c1d009014414401c0c140344102c1c12030294102402c0e00950010303081a00d50003202004454100314204054402c480035801020140e10001c000300d685018050b09880e9103000700b42018410f00898540c3c0307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601079136 1106 601078030 601078039
    0x609070e0408070803150406060201051e15060f180a140d05010b03252315071502030603010b030601150e0a0b040308040612150320 58
    0x50024000c50310801e05110701c02c0024004c60280d40140c10003001007410240704000d1104540c25a44900e085a040000744032886a6191034100103a100405005455640000507000c610000c8043d50700940001140d00301d0b1016000a418510070a4025104c0309031064100f242c0c1c1d030a1406150510650740541d01c946203803000c0034907810f51103080007040c0c82840707000080c1481c1078204062840f0540201d507449826641d0792010107015810007280c506005000d0007420254980c07401c40c05030300308805940c9102054400c2c0c0c0c41c51580003901c65070100030070082602940003070f22120b00945c02d100010b0900d03d03020900a058070b0360003d040070085a60b04040303480314104001d150300590840c40200d111b62040008001a60064414a9a0310b00e032400040031640b100881c2d100d0b0310300d000b4409401c44078260140003180c0d000002c007446406901d0490f20b40c02d011600d4141c1c031 = true := by decide +kernel

theorem cover : BRFrame.Cov 600899280 601079136 := by
  have h0 := BRFrame.cov_init 600899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600899280 ≤ n) (h2 : n < 601079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
