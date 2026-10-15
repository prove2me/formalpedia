-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:58.092452+00:00
-- url     : https://prove2.me/submissions/c96270eb-3395-46e4-89c0-b8f0335bd332

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 772122302 ≤ n < 772302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 772123552 1250 772122302 772122317
    0x2060d05041b0e0c250302060601082409040312090302030904051501091202190e0708012301050d06050a0b03090c01020a17030406112706070c0e0c16080901030507 72
    0x10003140c00c4041c04c86200044d001658140265400b00074840d0b01c00f2240070158200c070785003000707915480103c60803800034a01e000002c122800d03402c1d804942081c00c5080300e1050000f1418040b0700c400150040d01070102d0211681a020900d0080030020fa101e540910717111403d500a000907588007901e090203450010024005a0340d201d105181100c2070382d04a940070500c540046819400078074500b500420f400c0c136002c50035041010103a0302880d01d90750f42130b4060380d031100c1c204124840d4a0042c40040101c1413400d20541c0300b00b0180142c0c1180718400039070341d903884c000103441d1131113640810108040442042007005007480869112042800500442c0310190b484080140240c4850302031984007001150a2001a40c03000c4003401ca424a000c2d901c4c02c520f4928207000c01c814182c110340030b00700c1e0442101420704c082034840c10f41d408017488c1412400c1c90241304400e00d0083c00380c00024000e000c84400f03070801c1d074068640140500c03180c0c0d9070307044803600040035580c0041102d814851030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 772124802 1250 772123552 772123559
    0x2010c090506120402100302040e0f041119142b0c060c02130e0109050106081e01111605030c010c050a091e050913050111033702030606040302060d05041b 68
    0x16003c0c5644558111400010790798521002d030024003030b68001801080c505000c00418120113001d5900503401040340e40038111108080149080d024803081d90368140e01e03402045840d040300c8000c3e5408000038001c0094a00c140110418683d0300a0740100c0e645403080c40400b41700c2c0c010a0a0003403d00c0c0d140c440c898210b0b640104000234000b40604c04a50358030645950140300a40c060f50101d6400002404001d03502d4441070f5407001881411004612681d9111186140502c9000d0319401c200626a0408010108001610160071000d82f186d010800840484a000f0b2049000800031a181c080c0c50310300702e1900422150b200e400043c01001088501c9594402504060040350011200884155120160707048112002440201598240041a400c0903900006141b1030060004201d40b000c2440080340030b819910210845038155011907070800c0045900155031016028120915042d6254040741403540700050035500c1d641d541d000d000800111b58484008105d100e424604031908 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 772126052 1250 772124802 772124827
    0x10515030c22080610051507020d020f0a0f08030a03050109050c03190b100c06050f04200f0d15060b130611160f0303020d051606091a010602010c090506 67
    0x1505114440b16500c11805001884003104100281c18140c0540700a810300b1803003000b1010322806642e00c12400c2c2000001784030080e07801d49a03490b400a203e10031055560b024002506006903205801c840701c00008541030311907502e08001412810001c683c0c46030b0300301c0010221541030b048070b86581d0030f11007481045000001a65003101440e00800d02604600741a54000c0070250002d5801510340802002010f40104c40c00c403266020301001d104540d60908405130100781243d004100d06e007550302d011034403001401c01c081034480192050b400c030002d00b40060080108038000721200354642034040341213170f40750041d200200134602c1c101d42000c10300744000c240d0781c1181c0110300401074007110b2210001c008000d1062075100300e112650b0b14984443c00401154111b002c160054401c8074150a0580e2280e0200c1c0c1c1a071603402c420380c1000101d42e407000082c010f41041607400c3c2004078002e1400108400c00b82e4028007036174000142201540710003800c11035141d8801c9200d110b017445110800312 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 772127302 1250 772126052 772126057
    0xa0e0c100513210201200604080c10050103060515030c01020c040c0e040c0302090a1d0f0402131a01171e090712081201140a03110d1a010515030c 64
    0x215040c20780d154010074480740102c4071150310a40c0b0242038180300ca0240660346880c2c0c0d00d10350003aa501d4120380d90a40501d00d45038924803007152164040c800141c0411500d50240044801e96010f0360052401d200b8518240ea000380c006580e0580e1310028000c00101a00146081d070901b80c019000034521071001135101c0900700340507405540c5404040c01060710a42100110030030007801008100d0f49550020300a400000c4800d0203007024a20105808058002c20001c4040103a080f2172349640d07201e43c2a201080190081780c0010640da061103813040103004440030301c41c410119a0361004d600b00010003140359a806107640c2c41200c03083c4240a0b820410b04d0100d07406804008d101a250040d01a2034155507034040c00e07190003002444c104010b0b881c001001e030400d41a000c083c4598884082886400d114480b42e6072102500e0000c100080b682c2d40c001d0b08280e4020048081c490703040d00ca0b1032962000d221005c071144404801407100d0310300b19a0882c0420110600c403421072034080b0480b4103e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 772128552 1250 772127302 772127329
    0x512010506090a0f090f0c060306060813030e0109030b04140c0123090a080d050c011103091011130b0306090a0c0f0c020609180a0608030a0912080d060303080a0e0c 72
    0xc648030081803040d03140c590083d241c5d46920040071036081d002801c02d0a1804014011100040e003040c40c001740c440e11a01c8054050008070302c10756004d540c83d580540b54401100b10b090f0620900c0d0b0000030100b45d90383e0f503051081d4040c940845515044d481c81c68208214011740f1410711a400160000c0c030240007031030b00710008118200d43d994030b54540018540c031040c0c0d0702202461003120359640d400d6078481d02505002440c200240020a24980002100e00045529000581c0505000f030300d01c0c40c5a40007101c1c0d1a104603c02460803100d94a031010342d96580c0c001a4080c080002846080e048c8001e0060b40880d074440d042007031045039513005160080e5101040e00308945e0030801025559040c0480f1256500204103030071f50041c6460010b070040c8101d87d8859010301c0c05e04005100200441192002c90305947c8210a4504010782c0c0c40e400420240c059440080c14024096203400500c0303040042c6000703440b6400c441c0342c044084410344800040807039894000d95032103215600c5803002c50011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 772129802 1250 772128552 772128571
    0xe0c1507020d0f02060c0a03030e070b0f1809070f0e030304030308041b080a2a03050d1b14011b110606010e01050909040b0108120c03030106030e03071209051201050609 74
    0xa02c1041c1041c44543c11050030107948200f000070100c202c4000003c030860207500c01e0f1014016048414502610b4403003030300c00d2010452003003003e5695064a84010b1210392406040c00b0f280a802c6404511409c20440709100410940a80090f400c0d41083c220004a20110000c0d4500b504650b00140b41100251005100e03d98880a4440f0100c030310030200702402d8000115044121141403c101a4195030800190000400c94a03040222000700046c2542d820000a041b450408031003203500681c1504605051412608060006040c10038207959045055001086002841d54040d6414441c0180d00c400e01c000a0310500380e000000c2807565005900f428188185801d810050310a840f4142c68103500c04100c01c200420840d0301090036040c0c0d58184116440000904000c4000d449035005654203a4428001044100d1007908175000c5010a030f0203070380c241611560b9604c41460201707403650224441040a000da8201400183e2600380c21000a00203401e081c804944c1c1040e025110240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 772131052 1250 772129802 772129819
    0x115051809070605090d200f0102390a0314060601050a0915031e0e1b01020a02040e07050603070201060503241306021b0c0414070f0c21030e0c150702 66
    0x5903844e0084180f2094105511704180720b425a1787d42c01650300c1402c6c13a0300c15018685080000d510016021409603d000316680403c810280d0f402c070694440051003140c8500c07010768902a840740300c2404021403061740c6481c0705120a82c5000d04145008180038100300f400d000140d0b0082e40f1231410811141d401c080969140640d000490180c205000108552812030031140d51090b4640d11441a1102a0381524545407a05000ea050f20b0008003116006910950105001d0328007175000da0502c000a5080315409582c0342d001c141c0942040b241c001c05070b55154004c00c1541400d0008000c0382411101d04c0040241082c1641200341d0042c0803050440000000c20f41000020342c103c90b0590b900003803525155040d00b16075540c0310b18183d0520300850030683c02003124001c40350740b40d01030351403a00e43d6080d8201c040c6045401c0c250403070082d600c074450303440e85540c00061120070402e040702341e036004108829043d104510f849140328016004408111006c40e14211034015640310903411502030300d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 772132302 1250 772131052 772131067
    0x307060c090e0411040b060a0c08030903091207080c010c0c0e060a091b180305030a08070e09010909140a03020d03110d0203010b03071b0b01060516050115051809070605 74
    0x1e0750000309801800c2204540b10030b01040c005005940554150115018071006a004082c0003650007030170b4201010448880c5210b0018880c038024560046601d011203040c4410300002860b4181610750b840070300d4000b60b000b80b203034400074455900713100d80c203003802a10503105a441d600c06c665140b0a5148226650380422110b544412558004010566003400400c11491150083c0701754514940003003881c1d000b03003002d00e84502c00c0a80460340c00101030b50401074540415103a1100061014040040304001c0c0881032b901c41d246180030303040006002980303c405103400c0b1080450103088a006a1107800301a00080c0d0000b80030704a01041d1402203202d14034105003103d94081c03649e6281907540040300100311022038202552040c9201d51307500e814041d200100315100d00403840080c28280b6050014040140510000e060b00500b401c5003141480c02500c40b98211494440c0765140015401c004101e00c2c41d01d520030024038210294403141e1410885201e65481d032480c8120301c2881804076821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 772133552 1250 772132302 772132307
    0x170601080c0907020a140d0906030624090e0c072f19090203010305060a18030c08130e040b040b0603070e041509170c0123060d0213020708190e030307060c 68
    0x14108540e01c0707140d00fa03031140607449647d2a040c01074031140c00100b0b03402c0001030a5100f4003030f040454003c0d00301d404a158848540720b422500b02c201c3c40c000e2202e0342c0d10028401c0c0c0d14040c00c6118122001c02c0c651581514940808901c5140c0b80c22400504400c050000b03038460191050300040b0304481c0c0145e10200e2001d4241039120950084680901c080000010f212010818621806c0200740800440e0b40868070410041616a8090006902c02c401d42000818080040107007015484003810203590321075542c248818216000c0b160440c2420501080011a01902c1d4004a003140038002e15410015031112050300140301030038501c1020800003400791182d2140400503001014000c1d820702645446100340e00c54000c500c26907217481820030403052858041d16084150400c0b4038200e450310800c000f003040d0307001c00a0b03900400c00b0551030508002d52005005d40ca2143e10801d8070354071003000015007460030b00c1100c0300f030001320503a42c0481d50300403013140c800540c8140300107002c80001c4000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 772134802 1250 772133552 772133563
    0xb0a1a040f0618050406180b0f06061606090210081e061f021b01030219260a090309050906060301030f0f050601030b1f180902150a09170601080c090702 67
    0x100380190480c030340c0f401c0c05496900018801c2e1b01546050204410140041c8070401c403412010b4640041c08000c070b84a031103e0081c3c2600100c00030303c81c50610810754403805241c0c03c5014200c03450355860020804508010320132189002c05804c060b045450143c0d0700c80481c0740c01034682c18142c4070907000641ca80d03a820200390600189906400c0c0e00c0600f46101941d80c05001c0c078141c0140b940500045042d40c840d0080300c889140940f52000c107250502c0050b1138007030300038005044c10b064891044c03a1020031043e20324440d00f010340d00400d8003140c41c00c010303054003815007020b80524526010001182c83d09170860b411654428403012614104d0305012180340084017004000703020718000001885082080795015085404040782c00c1344d103844000144d4500b0340306d00d036400e071445c0300000358040380f41d841000c015002500704031440029031310803000e07039200710f60140100b422205d00344598a80c100640b48880905401481c1d00e5042c11b40d01e41c2d1354000000003600c0b940b000703030025101034800d100c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 772136052 1250 772134802 772134809
    0x9161701020d020711090a0213050d05030d050c0417010b0307032319110909061501090902130602010605060705070306051905040f2901050d0302120f070b0a1a040f06 73
    0x4640b04c0c402454204183c1c10301488403032007594404045941405184215450303a01007a08a000c454989024000e4151809106407503901090103103c0e6590045d000b40352007802c005003069500c1c1e04100d180d03484041e450303440b03810580c941100003034107480c005445001d07241c004002d8501100c5959445c1050902c84e0140c04c614090891003442d48800070300e0014000d8403501600c4007050100041c0002108101d580d02200c0c1e21210108048080c2442074854802e41071500044441d1100c41c04416688120843c210540c510b180c200041907081c4200b501420f0101c0b04140382803051f0310744039956690b5000103880956200082030150700046500010407050100074001441d244c10040750320503a1050a440c0e000e40340340f05c0e40101107820142d9003810744951000c0c2d0346908140610015500029003141907200b00b490101488240c500039107800800c20400079076555240c9841a6810000341100d103520f0705010500c3d02c2d120407003105881c0f011040c3ca000402c15042460400685125030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 772137302 1250 772136052 772136077
    0x61927090c0303030e010612021021020403260319020a09030204090327180509070e0c0a17060105030a0c0e1909200702130608070e0109050916170102 66
    0x20000070144c03d504400303501c00550000304151366440312000300740f03108c01c50000c0d444240c1055055010f0f0141c0f01603101155100300e4101c18841d4008403800700e9009030070580da07809405810343c0381e800c0c42001000340a80321100650a50500d66030b012814801e0341e9980c0e440580104500001610034a0420015500100240810401030601601c04c480b400a02224040081070804186e5580d485440c00c8600c0310340b4841911081ca5840002484040e044d54054042c1807000038a403420302c03200c18040c41240c20f245e9594400300501a140c00084000500906588c00401c480f9030f03040420380f60300031a40800410000d00b5a9001c0b43d100c52045c06040e4004080c1150b10189580800e003401501c0304000c04116440b0203880003284079501c07503d6002291420801800103082c08070107c003100c40d01170000721703071280c96911480c140026031700802001c207042001005460641d0003410f80144a010160098460550280b51b0200e22130055881b402d404c294409080102541103a800c0301452 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 772138552 1250 772137302 772137323
    0x904080d0606030501051927020f0711031e151e16170907060c1b06020a02040b010c0b040605090f16140319020d0f020603040b06192709 60
    0xb0360000d00100703000c0c0140360054100000211500841e00030b0b0070151210002010524008400c0e000c10014003001c59400f910f409002c407505402003080600281c0384038414403401c0255072018146040001e01e00001d4038080e040f0a9110030401107000401290701d40f684000e15541d100401c000b055200c0c09138404031905400b0024001c0b0005040d82d1401c40b19a078285242d80d20290952900c8801c0c0d840712600d8000c00801c00650b406005040045e9100d207201a2290380c0b5110100407142e942ea210001581100300328008624151140410880d02400c10703070710b800344c0e0747ca07002035020000b00010302d25075440d408116004401c0207a01d807100d014504541496070100000c00f1483c1040c03045240341800407030b0303115030b51901003420301110040154007a60f0310140d40800c01420f50b20a410342e0304c0c00c910650b40300580c0301c0385c0c01140705900a8505503514200f2406001e510740c122000c00c0d103921150700e0280403c410340d9080e600c11b00341e018040c0d48013801031030560004084000e002044074513107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 772139802 1250 772138552 772138559
    0x1603090b13050c03070f1211030312040b0a050f1501050d0905031309020f0a0f09050a1d090d0c02061803150a0501060507020a050d0318140a0503030a09050904080d06 73
    0x4100140001c42c861000d072608072502105055a8201da40544003501c014504140400e66080115a0069000b07040b400c0d40d0b0341040c000b190030b503400008a40e001072000350800c400e1201c0c0c1445c1940081c1781c90310410207444c151300340c00038000020340f43c40700e012071540c0c081c6d800703a100344250380501c0d1000d201003051050324a022a665400400803120385402c911000641c240b0703500c269001c1e6144011040e1411001c4a001c8502d10030142c040414000d0007800458141c452610003809070044c1c0e0b1003c0c10741c8650301000350f4025002403800e85294440d580c140b0002d54804030040c203499056488645900030042d021700403014400d8000c0c2c051107824924080000d500d20f42c6806515003440402059880e854111103900c03981601940003a101ca00030421800e2441c17201100c14002c0ca003003842040c2c0e14446048000159005043c038110b000107026062038610030720002810101c0c000c51601d010a83d0140c0080040c0c0304461080355010700042c20b2180c41000c17100c071713851849000c1000544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 772141052 1250 772139802 772139821
    0x50601081f050702060408030705040905270601060905010e03010e1b0a060f02070324090c08010f1505091e0907030605010e070210021e07061b0c0b1603090b 69
    0x100004800403249031007848507207491840c41010b0090304658050724807a590754032840c0450b030024082a0030407e0820001551100ca0f02c5000d00550b403d0a903102c01d011009103030344005086007502c0758960011401000480c0d0440d030f46400312642802c1580c1c04050741c038002801400c041d20b86030018094000c442302c110800c00718001030003c0845640080303588400c422038a8071003403007100e0050b074030003181880825002d241e06078a50001403045440d1842861003072003a602050411144924401c000340540707102030290b07803000c403942c90081102810404140381020303c04d10889024a0403c4042441c11011459041c0c20181800d40b0540c14141a444c0c140d452540e0701c001d0341c1052030040046541d550f001c4003240510100d5000700442d13502c2c54080d0300207501800a11074450022034102d21068030101c0600300290041d440080d180d024249043d00600704514007804009600200e04001040d09080d02e4000610400146182e000402c055009203041ca2002d0154070014007004210300c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 772142302 1250 772141052 772141063
    0x1e040501060603060b03101a070f0b390a03060f1205010510120b090f15010e070e0102190602040f090906060503190b130602040b030f07020c0a0303080a060305060108 73
    0x540c580d800308013040e919400d040c03041c00140c440d103146040704001002031041c440f80909880d030a00c41d00614000d8140e8454002c900c080c04121081e0f4010b10400060410114080341038a036101580c09404003a03100b55201c1714400d6080f07091003040494840c0f1040d20980c040c0028055146d1b50600c0d054954840b00010306050400f12290340c20007000603543c81000645404450204d0300c0d0b4410800183d0352610340b4074000301911118850740028190001d01040000c456105180c02c1e9441035041101014802e4001003407902444031482e142c801381d90340018a414208040310b04200c1b1420f0030314000b80071344a40e0340104101c928a0b080030030075410030303848800d03500c1c42090108281a0745106058803007000c03144501149212f4130800000c200b040391000d070b000c84120540605c4980340e076038a40c2240c0164009030500c0d100441000920b803044d0034040d8101119000070003c0c041c618001031090b07101070000904011203d030101300c0c01c45050700014081c55014054031a80c0d038603011525500c1c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 772143552 1250 772142302 772142309
    0x30c070f120809060c0c0303340209190605060d020405181018060305011a01091403030316020109150c020d080402090a050601052701080a1a0103051e04050106 70
    0x1402a0306002035504011884140c4865110a005060404003810040304e40c008255081c2c45002c0c554190070b06590034802840b410b26815260000c21001081215100388a020058000412038003618096551944e8990340400c80486544000300540c00e480050040ea52000da046140400c1c2491103080ea070300a40b081c1ca000f41c401180d800402c003009a4408002c1e11a00404e400c02d040900404a0191410849000b0b03610302084a170307665a9124210b9024280c0d20b90280840e0700c00c0c5440d9a400804080241920706000b51064501d10000b0780b070b488050704026408582505114049000303400802044d6000205600e142441001050252940091000050282c0201e02c8c1c42207020384180e9000b90380103004950183d0b00e00c0303220f1000f020084e026074140001880307880a00100c19814504030042c031100c12203030026000025100e0729018041103096400d001d1004a0510880c481251000342480d000ca140d881d05410101b029904191200400d880700c0e0420090141c1500300000302d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 772144802 1250 772143552 772143569
    0x30910200d2c01031d0a060207020a0b0309030d050402010c080a0f020d0513150207170c0f0f1c02060d0921030e071a04050a1d0c0301060f0c050a05030c07 68
    0x865030b244039001c4a20015081c0003110b45079200d0034401c55129500c0034030303405464040c103e550304e241400c4a2404203c030b1021185107800246c2141141810200003004061400e1013a00394108003928903241c2c041c00c83c101c0440c5030303650001030640e0300c070340748101d1601e4011035400e6544000340001460854000441400742c400c0c201c910110b14402d40484246010100b035010180b0309010001342c8509507070040500314800c2d4007000c00c8411802d00c24008105c515801450440a238106016801c5104001d081c0700d2820301c965207042d40c840081d80200380600800741c0422000b00e1001400a008074001a01c04a2508070000100009610341c0c124180034000c5e2982e1011008600714241c900b80c5540c0001030b04420020058010400a030301440340740d1070704c1c0e01e0500c1e44400110342940b0013a444141d07285502c1403406260201d540102e5003015013000030f5807079907040ca039015215140800c0040d0801c400c151300c08080c04000e04c110520294041c060320703030791030380c5d90b064554481c22800344400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 772146052 1250 772144802 772144817
    0x60a230106080f0115020703080c1507091406070c05060304060e060907050306090a0f0818044205060a020f010e07080d02010204080d140d1b140c030910200d 69
    0xe1034462420200100c2031607034028103003075040d5518181e1580080a099016100d020701e040c401c00c1f642f64545125140507528040303a20f1a0000800c3d0a024284d29140a481d040000300302081060010405986c020740310705585e91114a01200146110994008240038100074001c10950205544007283da00700e08441c1551a20060291205003400300200611002045000045c86100c00f40003411005504030282c5105200480c0a1f2120352802a06061044204146500e45070320400308030444041c481c07402d45484001d8943e06030080c0513040c441c06001c203245101d644200a031003401041d030b90082c0907000410440c9a0b9806d028051000d0030300401d10044040d030300c1442a1000c031041072008000d4840500416101c9580d01c07194802a4107081240c004401d11307502403130f1038030104607a280180119403d80104070000c100002e01c41280100081040854004162100d1040c1201c00a1215211810540b20318500711030000d0120403491482252400100b03865401c1d409a4480c8603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 772147302 1250 772146052 772146059
    0x301090b15010e030604030305071103040806041416061d0a0e0103060c0c080406140c2a040908030a0b0121061a04051e0a080304090f0b060c060a230106080f01 70
    0x124002014542036815178498000100402e10a4012580041040c101003203516040100c0c0b03421a40141c004c040542e0100301400100a07040c00c5641002440b0400780c089c2d100480c0000e80407030a94480d080c00c100d076540490104440008410781d480c107005101c2100c139550b03840c0c00644000b0904c001d59001d49003013001c2180d14010020f0342800356100b08024a01410301d44141e49034001182070b484030601c1440001e110540400150134070841d00c11390a4608841220036125103408100c000d0f003c0ca00f0101c0100002e0218400d40c4c1c1c208070200000b040356915100101c44d5a8401e04100b182e051034072a8030040101d259001006546200019008011403080c035030b0441c0c4a24851b00f9009074280203016410106000390711240107000b0104002143d0301d24450b40b55800941104040590307039007143d907000400d44120283c0540c1640c806080c002022101911500011b0561001c661102e600301c0780003500c0b40781101181030140042c0c51a503110a001002c18000b11b5401030702030859400030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 772148552 1250 772147302 772147307
    0x120e0c0a06030b040f0c0c140106170307024e0a0311070f0f09020c1015080624010f1103040b0a03050612030412020f1509131401050607110301090b1501 67
    0x1c442041d095290007104a01f0307659264403500b8402141149550b03510702c00b1070240c1c0315443c180f0700d2002080c01152514850300401101841c40003803102c0000e480c40c00003401c031003041112101c0c0c181e0a003030600c003c6e08083c02009548401030307810740180184020b6070101500402c0d01001e1240a01c101c4100c2920b90000070000384140c0240c28085400d180c080090303040a4006141c0190014196080d02020969080c01e6505030078010381c2c00b408c00c0c4401d08c240d02c810041264800e015420f404000d400b001c1441940b40d488500c1071303040004c14108413000d9030040059a203043e0844044030f03515603586401c950180c020f045901c00107424070020030007500d050b0000e0302030011000c001d14501480c01e124120b94090381c10080360441c00c00403202c3c4265a80c01001002c40d814004c0c0299a82a5030f000c1081114010b580c210405151188511910b80048085410354034241c0c0d585956903203d0809032110b0812406003076241d030910141c10304001c0306400c3c01c2e005030742d01d00a5482650032407005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 772149802 1250 772148552 772148561
    0x1080a12020109021809031210050f010806330c101d0706120b061b15150f0604080f0c011209050a060908040f080102030f060f01120e0c0a06030b040f 66
    0x45e5011107189030100b81d8001c4c1050340f41c3c1240c6c00004991400b2a40310020454000450760381010b040c1e087d5007003009050040e124501c290007460182e0f0249002c000180003600f0244000f2207034411105418039800604120003499038004d400c0c541c55a02c420405540c810441200d403140c0340c00c001356041070304000c0d0f03842a841e42c03c11000c2c007546801c0003c100d990851000e00c10342d0841c1c0f20400348009495582c0104520714035028a451907290141da01494a40005900781c0203003400400c003c0580241e21803121340200480c0c01342c042c664250001035940c0102c3d0880c45071406010b0b141302d605640000c60603100542a00d070700600744411903020046035110000a00550064003080000820070351007440e0781031003104541d04050700e514901c50000300c180c001da040c0780e600000340120030480000680e0700850881d232441c400003c54000801c0c8143d1900320401840d199203103202195011b101c1c9022481001d0301480d070440e135841005018190048209003d1890100003100ba6a858041d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 772151052 1250 772149802 772149821
    0xf1314160b0702090a150504240b090603150105120a090b24040b040906020301060c030801081911030a0b09030418050108030910210207140106260c0901080a120201 72
    0x184841d517882070442c03005440040705040500f0030445011139244da41d0b00c0b901740c21240010030f0002c070350403842c0d1011140c80560800c0d00c1e00d55080c010a54a540c81c1011203034444640f541140c0000c1400005980030300540c001c0cbc1010458400801c042440e0f603a1020b08524000c115611030703911401900d510603464069281c8142420a0090450341000c1e0000c0814503800740c0001a00c09203074544c002260400c1e00403000180f41140b0716018035074081d404602401104014000d0b0207085003440e0034034014030000400d104107030501d440450f942804003400700c03074000c20040300030b1a00807001600c0341d0080c01a054a0345007a444410528100d100d801d0682c0e506800841c0740c0700581c410020618010503228042110a2a925440f8812050307800e0341070030303e0000903883e8140351030102c014480503520000030780e01d000d03820072290071111030700d00700d490404600704668203044910714146a00140f000d500403402d4400015240000220281c909000c0d40b20140c542001e81c0049003a0b610121 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 772152302 1250 772151052 772151059
    0x204290d020625080304080a08070207052407060c20011404030c080d020d06090c0302070c061d091509011d0613141303080a020a080f1314160b0702 65
    0x42180d0380f819982030550254002c14820100015403681c0d441c10507442281c4c101c1e1311800218080140c26001088150480304034000f0308407107401c2c0000304004c0515103507034a184180d4040040444010b074401c0310041034005009205038200324001915540c407183c10b407040c500000e400d04e02c0d142010300c64088201c45151a03100075440c0d50b01c044070a4441c80c2d40035103c8060400a00c0250402440104036103000420042103141c508581101100d68400074031084c14010800e0784000380c0206008400e0310114103284207003e00c1d4455181c2030382c21620070070f038010030000c0c180f11241540d0766100030704420880b48080b40d03030303211245071041c0302c040280503640f10b07580c0021600d140340c4418454040031302100d0001d0b03c142c007000464180c1c0829103000641101401048080c10340c04010280c1c810803182c4150716003114007800510103c40107110505400301940410f402c0103401800055458100c8856041d0580b00200d10f516204040480608440307005400a45212500e081d941c040350000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 772153552 1250 772152302 772152307
    0x9110d050a0b060c0606100c08030711120703030b1c0c09020a12051303140c0d030f09060c0504080c09010b4006020c04020f070206070c030204290d0206 67
    0x14414101500000d094241e050380c036000c004142da118107000e0b024448a0320018000c500300042800390304408642184104102c500c0004045440d550440c3e402c14400d1030191203a030751184d4842c1c104916142c041240c09000520a0107142d49900b248650080456003039407204000b400407440c030f81c41c1a90041168160680030442c011a560182176928028140100030241d040c2101007201d100711408468050604808001e165004000c0c0c0381600c07141542c50b01d0850307204000c0d6540c3c185d2070959001c254460040c00c2c0250090741011400c280e00803418820020750b02c10207001c54120380500d050310f210320181003030103180a0600d2812100101c62140c5800c004460303100d400301c64092080c00340030a16480301802507001180102d603c5501c4400c200c02030910740002e08206601540c1c0b84110b005200c3c0c0049681c807042142c0c00b19a0490382950760310a41d1518001100a130741c40654024036040e44110382c1c5500320a01c2ca01d04001d450540c10090001c0e04205850391038850184d0098420b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 772154802 1250 772153552 772153567
    0xb1b0705091b0712050a0e0d1e0804031a160c020603060f0409022805030c0609010c1401060803120a0c1709030408100b01090b030f160e0415030b010911 67
    0x240c580260b052078410784051a01005444045030344000c425000c1c000340c0001041e0450540c4107080c800784101c11200821448000d8440010900303494000c1140091500131040c1040318041c11180255880452750702840e10201e0440400b113000c40300c03821081d4100b084560b00034401e0f20f4070000650300800903030942c1c545505010511054400190f0442ea9032030910000d13a8916100e1040d0b54202c840c15400600121140c0e1000c01c541c0c0d01083c0268010340948040e6980d40f07007650070028003843c0a41d227103281c03406c015030240f0028802445035445d0880100f0100c0e00400103000b050402c1d0428040c54461040c00011200308009103030005801215241c801d104246900f604200020708072800c01e41c46110460600c24103c62541c12a035680c5106026560070a00007801012041c04460540c0b83c003d01c2c41c50008401410711888100390301620203010b01030791030210b6941c0041c100f042000d4100038004188561030000780e60700d0a0b820000992200c0600541e8080381c900d41e05503051489 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 772156052 1250 772154802 772154821
    0x906030a15021b0f0105060111150c2805090102011506080a0b01050d020f04080f0604030503070c0c210507050402130302010c08091f090603020909040b0915010b1b070509 75
    0x30855544010f003c2c0b072408041031800400c0700005000000d000091039040000026143c000d08074240c00701600115104138661004c0d183c51035200d90b8a4500540d0303030348890203e5002c0003124622004084d600c041e40c1a0042d0f011028015008081c1c008000d41c0c00092641d00d000121481214001004800011020b90325500a04000c0d001810010304180c404030b645000da807c00114003124100c08901005031400401501c0002c49542010f40322074101a10001c0491000411003414000180e03018030420000e00c035060020080c00c0303000e490104452050000740710380000c0a50711841840c1c0c000c19140781c90b01c00c840d0880508012843c00c9851a801502d014208200030b0b500340390244100e020948641c22000c4400c1c0803403e4400e010600440064007c8100c0d4001404040c41445041c1141e00d0307041d070440d0041d405c5a84907007599982004280386c90203600d50a07020420385d00001610b4001d060282680282044002c2c0d10351a62070031050365480b00b032285c940d11207a00800b0440618 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 772157302 1250 772156052 772156057
    0x606040e150d050f01020d06090e071a040f060e011106060a15091e031b0308070b04150c05090f120604060203131a0105090a0b0d0602030a090c0806060906030a1502 72
    0x3a0042c01c809100811070310790500340141c0001c030103a80c1c4d400084401c902e806600c90305015041e01c035401c00140081e00e9072036941e00308501412440c2c0f075101000200f21a480b41c2a40c00403e40e580300b6500058850f80b000305424945c0700b4150114440700b036602d2841c04082420b5108031800b501400c0000d15014080700c40100c1406140c05002c00000040744076a0501e08116402001c0380c5c000c02e140d49540fa00c40c00320b409141ca2428030700b450030340900010310320a0441e0303c001d4000c1454101c50303c9509001e5548101000b128142c10700e00014003003c1600075024100044c02207074a20a0280d42c0407e101e01802803005c0755681d600580005800105071754090360300b103d1048010f0780a4291950f41c0d0001100507600c40080f0030701d8000400c601d1400840e103543c020310006c2d00b4030a464824020905e1401c4c5034000510854001c000241d0503582a40185803160f00043d045c40140c2d0b0314000e1584a1006403501d40c0152030386000140b8504001950541e181d074803100c401c901d04540d1065200a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 772158552 1250 772157302 772157341
    0x70b060f0f04051302190b040b0f040e070e1002070b09210312150a0501051e0f1c050106080f160203070b0a0c120e0d08100504090503030108060606040e 67
    0x4406a1007005a41d2610b1040500c90880d6030301c1828091624010404860681e180c07698603510385040a0044a120005540c100e442c0b04503055241c03c035041c03480c1c8450280360000600061202c04002816601021549261105842c0c06007600c800344012030f2140c02601904182c10030412483d01c090404040206840b003000c10080007003500360741003900b16800f42ca9040b10078080c5d402480f2401d1503005407408001001c48035143c07071070b19000029046c0c0c001d9082c0c2005003d04616142d20700e2403c6001c0f214000c10090119075906010f00c08070600e0200030506048aa18001c004aa990700525256000e000c62403040e10b8582d65050011050201652007081140020b0003100001040d0b003010902801d84080041080c504000c8020000c540ea08003d585c00750504040c1701c0c03120404170380c90400080e0b40c542109103650ba16060030340c600725540402d403c07034030301500c10b02448000f0001d98142e45e040c1098804a0310f54000b0404603010702c1c041e4040c140c06a2010842081c07242c101c8010301d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 772159802 1250 772158552 772158559
    0x4050703050106180b03010525020705030607020709180809060c0c040213090c17011802072102070e1b07020d0c0807050f0d050d0c050a0f0620070b060f 67
    0xa5a140e95480d429100706070300c40c800c60390494015209100131401170030300c0c0010540003089546400c1d100c8007400441d081301c00c01c1c944164041440769910900c10000070344000b13401c689a90900300c000075904c000610031b410000d4075003a00311801c0048959030650b0170307400030241414440c40008002240d484040c03034014030f00c180e001641742520745001914000c292400149102850400c9a0055440c011403c000f008000d0307201f810681146010141519490890402c6c49680c10f91031b940240308585000e4491030501c41f0034801d5078011605401b4450303d603425145a2582e0368886803002d042a40c140d416401030351601c003038000c0c009028041d00303800100b03180801d05940e141c00c004100280c011004580010303005101c141402034400c3d058503419942ea90150121b80c5402c1d869010b0078192400704000d003008902804002c11101492940060035000207016a217051401030400840440b4000b52540342c0c0050707410302c081520401038000302052090307900c000401502446c56543e0550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 772161052 1250 772159802 772159813
    0xf090e03090f0d05190b070201020306091f0b0706020706111e07060209130501050a051e1014030c0c06160c030f031512140601060c081c0c030506041103100308030405 73
    0x1040e0100981c1020717050150b0041c900c0305190070001c003180c000600310001e680c01003050000b10749601149036808214070b00c0000840fa29484162000039a079800096202c00101e962001d2100d903900502c070503840343c002041003c030b10b0f1403a40018040d855501d00100c030440005862207040130005d080051003035500628000180c0c1c00240c2010110b42c0c1e250015540c2c100503c420705140900c5005464101c40c20140c405c81080c1c1c0098003150402840c5c040e413003c0391103000c00303401650081d0207010308d44021602c91402c0d0004000e142c1140c4c040a105100d128007050102d400d0002c42d18608841c5e96585e0846420360320190b4042c0060b0019000301507580d014186040100a50103000d002101d003103e09160305800c03c44011412403000100c1508600010890030750884500c04500ba8004036030760b02d400801c4403c5a4141c581c00f200f40140c0c4c02c114004600c10b40c554451072007010120f40801042140c4040e1100d540806c43c0d154608a0180a007480801c1490015550151184c802c454 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 772162302 1250 772161052 772161079
    0x30305030a060b07050f0115050a03110409121d060a090b13050604080a03090e0c03060d050124031a1504020c0c040e06040209090a0302060106050901020c18010f090e03090f 76
    0x3142503001c0c50f0b0903202c942140b0300324806c450080c00b450a11101b850242c486a0b410000060301c20a81031200800f401000300d40c440c1030343c0f180d80290b0070752038100140306900312038014003404241d612a00c00c6042034000549034002c0c5840c40a42e400c101d03459031050380d10360030b11040640c90342c04500d1000f03140443c4003001489a0b1040e0040010340001000343c05800d07410b1070090b2545105400809180801104008094080030705503944201c6c211030841c014001411700701d00601030f0b180002036512000343c4160441140a43e200d0440f442070740b1080300c01e103400002c503e00381c02c1615080d1889800e5814080c1ca031a26401511040c01808150b50070f440c42403000030125003100d000c050050304090100804c0d0301e084444598841c0361100a481c08100c00c1d074009403a000140105020301c5400719903003c2503403081110080440000d13056020202912090380d561510034071034050491030a1001140c030280300d0007007003240f0030301c0c5009504118030f0800300704003032504506143d00f05803000040c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 772163552 1250 772162302 772162319
    0xc120f0e0a08030a0e0904020f0d020a1802030709080a03020a03260103150c0c0b0121020612220308060f010203120a0516030b011224031410090507030305030a06 71
    0x5100820384031008541e18022010050070200017400c24500c40c1c3c61060400000da04c401c2c58484981c00c1c110b44075030320310915100144405d4510340005c1c001030348441050100c00c60039030045004581d19200c5031412030f075400c0010b547e0901038070010016000502c0642c0041d0040c440101d210600b042511506d000c041c84084500000b6030040da03056406850400f0890424801c1e14038040b410300d461241e0041c1364a46010600041c49422500c42d005a14103007070060b07068888020325401480b15a4915001e1000e441c070400540307070154104c0d28800ca8903201c03a4109014809190305480341009076464904100e90f0103980030a42d41580810007501d42c540c2036581e4070b00d102d910103a20010751760600c00d5200e6640c62075480d091041c145003000a4a281c0e030000c20030b840003009090b012880d060041514070405002c4070b6020708001c0724400108c100f01c07000361008440451641201c950f260140c5154050f922021009002d81d00444000d1010a2250380110f500184510000c0760f02c90b070352640f2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 772164802 1250 772163552 772163569
    0x2040219020307060c020708060f150d030203030601021204530c01090b0313020109030b070230070b09030c070f051905030c0d0c120c030507060c120f0e 67
    0x405005030400030f4030f03c0420045108003840c40c09148020901d8609040c120750f0307910409400c10789c0c841c010b200060384098005010003100309000d00300b62000210782c90003a5494000380c5406015010f0700100c494411810012b54046444401c10b88203191039042044074106854442018a102c6082040c2c083c080300840c4280203201840041c9200411025054145202c0c60030300f504100c9021400c010445410741940d82018030700ca45440c51401c50300c010390360402c0580c4014201c1c0d942c0c1c01000107158020442a9810061108a80303c0149003250500c01c1003d100713402c19071602c14400036012407100d5000340d078001e03c40c1e003c40385411205044689007540c80e41c80002c809140d03000a002a090482016285028184610645508090000e40c45042c400c076118010b04000c1c3c1e03c2c006000d000e000820080c05e000b0420580701c2038a040100c5d80d03824501056030188541000001c0e42d9201c1c0180307058003504000101c2c3c1004d50ba1508a8040c0041044c4da03080000102c940702403036861204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 772166052 1250 772164802 772164847
    0xa12030b060f031302211e0c0a030302010b01022104060e0d060501090504020f030c1806010311120103170c031c0f020313020405060307050102030706021e16030e101b020402 76
    0x4c010b00b00403002e20412a0700c40300e0f03140031580f074103008202c44d003198400620391004101d25032141080300005030a05d482d20056200196105690074800804c5c10b8041d031060010200030307425a51400207141d200704c0f50403103184003140c4114003000b04000312031090b403101c07040003c001e10312484140541c1b075150170344000b03030013100701155520180b00071403502c03811903c1581420f8016008554140b0001074074150040039010300740001c280042c58a82c03003a84003031156a0490044c40e121007072200c10342c00e00c107001d02080b1044003c01c040c4c0c68000400d10107a40c4054400d40080d481c0c2600711800300444448094188482d64541d0344e44000f0441a0000d988144150105070354954001d004000c1914400f0340f406002c3e0308001000d0009980c0801210800b0340c0040340565906038140c0380303050401c1011010042c8000114240c0607102c10807030324465040c013031390768011a1001e22003084807003818038031401e0220b100c500f40c0080c012103440c3c0491109000070001802c0c242000d814a0800e650140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 772167302 1250 772166052 772166071
    0xc0203220603050105011b02040902011e0c0510050c040614131211060f16021f1e031e09020f040f0b0307083412080a0f020a12030b060f03 61
    0x8100780100760349480750500401e42407800304008560161600103520a210340603000301d40740c241020644e40180e6035002640074820305440c0b10041c03450000c0c421541c500782100c43d07008080781040800c47d24040e1354020380b80080500e203020726001e42518900d900c4d01140f55002c100340180ca0700c803e1518035a400504450440c0507034140c1501c1c10019841c019014144120740034813003281d442064000781d500545203588078134401c1d000d50001801da6500004040405a414800c640b090b0b070f4400700f03004410504c0e1018a0301c200b16100107405581e0300c044000102030100c01c400d01c044000e5000700650340e002400302c800441140001c80c042e114003410207290141c4031200210f9500701001000c0041000b080580b0132a031207010201e80c259200035401f84000d00c2d0f46051440303040c0d9004045d00a0007848407480c6110f8261620354055000036000c40c010641048489501d103001050b00c0d0040d80c0d111088110045c1c060070190300503c00c00d81c1c904d4112501740040b800c0c03a144c0400035400b4551a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 772168552 1250 772167302 772167367
    0x206070c0519210f0203041e05120d020d0f080402300d09090501080c121c02011b1815031503060e0f160b070201050c100f1107150c0203 60
    0x540418018070b522400d01d0080081c101980250130b6404805e07903041d60514042203481241d5003480b14007448507074020305d901004004443c400d29100003009042c89481e602a528503240d9010151100000c062204010a440d807000400520701314109041140241407414030fa680a819910041c1c0701d84803401055500406000030016040081c40f801440c60000610840d030411000c07230307111046003c5003405442c1c0170010f00b04600c2d09000b42940c641176601428180c1c0e0100500070f02a0002a016002c141c4d94102e201c00e00c02c0c4140c002450700100a051491601d152195003c5940c00100c050301c10960f840c84400d0444101d070414400460007188085250342d001483e190900d034800c1004801580002554040448182c4001c01103a400e503200303039180c00140c00107a4880c81410701d500c40030b00980c00030040000f16940038130312201e0242000c02443c00609410f2140c2d2040755405003990190350781c0780203590034981111000060343d20569013040031601815074100406003c00c1e6000044c2d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 772169802 1250 772168552 772168583
    0xa1113050a0f080705121510050406050a1202010806040209101205090304060c0807020312040603050f100501140310150c030e0306010303050d0e01060314150f06010206070c0519 78
    0x802100c005001d00c200502c0303442e0b00d0079280342e55514403072051901651450200444ca58014090722100c06441840011680303405a0a06c6a407401c90041c40d00c601e00e0034a020846003041c810030b90036100001840500213206400548103004001c101c0303a805902000105a00d85074081c515180700c03c951138003c0c10751900004c44069400003060303258207900c1031004001807030b4004449403200703402406050340d8200c01e0000c242031903a0586c802500440000f000901e0b103505a0019114000710404441079403500003c0802d0380020f0b21552780043d81b034500000c20804400e00442d08982a02a4074814540c3c83c903145208074030409800021900c800c01c0c001c20305130009944481514100e001e0042c941c159079000e803180c0070300c61a00400b00c1e501ca051540c103100950060002c3e5802c10840004400ea455034a03039144010801e280354601101f010642010b50b5a004c54007502d0140c0123003119541b003000c1110400014082681d8903c1121001c90810b068408443d203040d009401e0b60650100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 772171052 1250 772169802 772169809
    0x906050c070201020a03180e16180e15120d0512090109080703140903120919030c0b0c0a0f030306031703040201080420041401060e1f080a111305 64
    0x909050100e0400c0000c140142c1c0c0c0454400262503140c201a10b03109011004407844034050f400c800b01e08a4000b040c01996058501c19181c3c180720751b5a03800c3da5040c40701c0390405c0720600703100e43c64000d800340c40444c2c0700060300c0d040034000070000b90074400c02c3d040300440743e4607209400000340c000c01d01c0041c011500ca00690441540178405100a020184059440c00614460550301404000003108952140301c14402144c0c3c2800009040301c02c40c5490108001080d0300c4400c85510135221415600c0c400034410240c0c104594101035060042e91802c00002d031190700c254840401c1380104404840014004240303002518000d80d4005410303411890003880c0001905101200000c0601c04c020041c7c1e482141641c0c07140c3d100c004003400d805181c103046880120650401d0b8000d080019410210580f40d03802c2d0304880c0f0aa1310485500080000c0c000b00700511101403103404180d90b001ca4501d4040c0c44415001010038030300041c040b403900008802034000c5405000f030302c003074084100072514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 772172302 1250 772171052 772171061
    0x80403020a0e090307030302070204140405100509010606080105060a0507080a05040807050901050306070c05011b0815010905031b061204140c150706110415230712052b0906 76
    0xb00c6288040d0070f410300d451400d55a000301c0b2001810190009003140454665030021001c010b000d012101040c00e05162540e00c40c41184621301c0080e26040002e40740325014001d80b012a01d00c0e0b02d03840500e03409d210903c1040c0e8060074107082480004c20000c4000340f100d20042c56455115584e1540322800d01084606154050744101c1c41811120300620a960b40400c08640150301c509020712009450700d001c0d401740c281022010a046800b445003032050b41c00064a61182c1c5043c540900002c030070b03074019100003442d07000752501540603801a0400e102c00e000304031a15100105000d041069180c02c0340660b0400301e808590703115861359043c6500c0340400406645942c21540a0f10328100c20b55400c80c64010500c0250520b521039541c0311035524a030b81102c015000e00b000084038040441805005e13681d58002070b150019202058540d414041c40c1510192548032a5603052800488011600ca82250007901d01d00001780a00c060045030410b403000c000c0000300b00120b80800c0b1400e0040449 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 772173552 1250 772172302 772172309
    0xb0c13060207050f040b0a0b03150f0a0308030712023010051f09080a050c1905012c120607020d0c0f02040c0c050d030b0f041a040203150607080403020a 67
    0x15404010b00380519a20b524043d4060502134400007810000d1900103155012240e0040f9188030b00041404078144206610200005040e2106450140702005010341500305110107450a1403d0011410b200d200c1c0c2c1c168010400d00a50250505500d501010031a0386114001d040b190308403554524422640c0103490380c0030500030300304d100703035483c1c0f9011500c640c00000c2405200440c60009045160288520ac0043c3c181c54003110712146881c40d14517911503070600c0d8948030301031180c0c0c42c0d1403042d01405140160b81060703543c170007901c41001080f0003022031000a0141004012000611f0341c40311440c007107141705850300400c590705142d54060b0400601903510010413221420300303004180120210000203038103803400140310119050499041c43e92002c01062405105c0b414818903a140e003115695200c21204028403107201c0c01088100e4007080b15400309843c0422882e041441c2c00d038003035a401403e0324070820521010744000f848641c88024200c0e03845402150600c2541424182d64018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 772174802 1250 772173552 772173557
    0xf080c040c0302090f100201060f0b0318031602010c030912061d07060e12010917040513050717041e0c09050a1103220b0f0901050f130206090301090b0c1306 69
    0x41c84d4054020510f0311140c1d9502070b0148200380d04401c4490f100354000740c020091208410103464444101c0f015075070040e5a500c043c40c03080c0660300c600d804080110f0301c841c820701401c400201c02686c01981d010746858400c0e010b1241180000074000030305c41950b881035106450008040407c1c2c40000c0c0c0038a00320511030f51560126405011040d0456004940018100d494100d500c80410401d405040007900003002010700040c00702881042c00c01401c10344404903205484498010800030172210112902c200007054ad40e400c0c0403040c00c903203040d43c1090042070654114402034508040c0c040141104484152203030700c040011043c1072003a02d410420320a0180016240c44600420030301000d4103804113007410380e00c0e10681c0c41d900c81d001d10003035600032542e11306442e050b0b0b0450103011007118186625424040004c4040a074008102d115200d10b581c04940e0030455000c1c41480c1d0014031845425650301c04c0d04a01040b100c1804511500b840c0300307801d59654407512070001c170100581c840b809 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 772176052 1250 772174802 772174807
    0x7110a0602070609180b0a03150f02090d0b09010f05100e1b0a0f05190309061a060412020301020903011802120f060a1e0f0b0123030a02070305040f080c040c0302 71
    0x1a0344122014120fa0811744034180d11082c500002d0000c0450000c4658400c1e100b00e4000200b00746204c58070f43d010640001040000c402110071b0781680700e12028613038010f02e160320160004c0c8400c04d42a400801070400041e0381520050303140b00300c9800307441d42c4041c6c541034281041a00c06490546900400490150507011070b114112729480c0a011480300600003000c0f0300015440c40f640a030707003402040a0f51b942074500150000707001442440826a905410b0512040e1595082110180c0c12100a0109490300d07180c10b4848142400703041080b0303490354080100711180d940900030074414500008041d0300c180302c2d510400c40142800c5248504076000891040322410300840c51a501a00285c00850603400f48600d14007501400d040c000040b0313203041e00b42c5404074580d5000704070910087c0c0303890b90000c2c00780c4002100e80841455181180e02c0800000d0034000568019011151003410614101a100e01900da80500241c224161591200e410000140f4150050700180c0700c043c1011403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 772177302 1250 772176052 772176059
    0x50a0c0311091212030c120108031c0b03191a060111030409110f0d050f0c0408030301030f0611030412021c021e070b0c032208150408070807110a060207 67
    0x41c45001c0e20005a209807154540b441c0c010100b44002c20300d00c4070718514030f43e0b6031800100c429050f410402a10001403403000004c100a0b5000040f11900000d40703c14000038501c078402c0c0e80c06070400d1405180c040c0250809080b020308041203900c4418412010031160410444142a4801c4014412410401ea20a07480c802800110031075056441161001c6611240340b80c01403541d10500c4c504800116000078000d841d0b0009078440760140440044128140d01d9901107480341d8040c602a6403c25007080004100241e1994508945940b0610020641129049070410550011207055513411443c80080140603814803c00c0b0122100c41141c440000300410002d58901c241e40d03040c20011001d001c1c024150300304000c0540103100071000c07190f58100180034141c03640c0000d40495100c11a000701e0207100303044000c00d0b0003074607840002008500c07481c040068490750040c2c815607a4034010065100850002c00050180f90700030a05007820299103001d0010011065003c4801c43d04141800e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 772178552 1250 772177302 772177331
    0x10203010f09050406091e12020d05220801090312050109020f0405040e0f0f1615021504030e030d0504031b0b090d08040807060e0907030612030c0f0b0a050a0c03 71
    0xc000c0c1d0344802e00c000b40300d03030741c91401c10010048102c02030000040200c0788040c0080c80d0041c0445d2901c0344200d4050215198030583e03071109071503012000719a06020071041e55210b48290200420001000a0055600c10409e8210b0f0782040e01600003442c03803200c0692841090141c1401000c540034110f00c1e10810440800b0540070714010710348125142c14251130f0322503003040361717a61039013440c0d007543d5000c511411460b942d00c20140800041c2c1c1e11144000501e002032012030744042c0c0716a0050300825010051503110310100070400c5090000e00d4101e00c00c0c9807401c0103180c000c0d0341540c882c03556481c20f500f41081a05100d01404521002040050000d0000340055850b407910959500321680c0440c41c140c04c81d4055a00110214492a200014a00c0d48104003440040c0261401d02042d280e041d0100c0030340326a4007860b040004038000e118002441020032140ca43d0086840303049400b01ea6a40f00c0740802d0a5070b5820b0610b84480034010514403a02c0388082c89506420308000c42c50800703142 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 772179802 1250 772178552 772178579
    0x1202061e070921021509030111190305070203070f0506070e0d020d240509060103030e09160509010c08030f090d02030903210c030d050a0c2105040507050d111201020301 74
    0x103103145540c0d0038940001d820f8200641c42c420315401030402c402c00c134482520b0001a00a480388034480d40c202101004451030180440341d29211107800400c00d04004c81d03003500074080c05007100085100402c100400700d2200040044d20341d200300301424a41c181000f00070b0032007410407841803040310200442001680e0b440300202403d076006a40120201c1c00c40701c14070a802c0d07010f920f11502410213040094200c800f10307045068074441d49840600b50748001c02d00200c000110744103402c003103080705221300c25400780c40079000c1c182d0705150045101d02d141c2d4035921190400d444940e13100c100744040c005492424003040d0b0781e441241c40154108414180066a0b42e1501da118032440c6002800100b41e418016080351520024001141c0d5a02e0038049201c00500b0101e03114409145031078a9030100603c100b180a411001e512400d10044d050f031782e1600014400640708a40c54805d40400061a8880c60a545005402403048007940d200402c28041042d012103000c0e20580d10400040c0032118501c0030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772181052 1250 772179802 772179809
    0x2040510290d06030f300507060f18030e0312040e0a060b07051f14040605060a080d09030c150206010303140403051209041a01021f091202061e0709 65
    0x54011001c12090034004a1050158600c001c5003004030100501c11100c000030300301e5204c0c2044100e040c0c1c07402d0b00c13506c120700014113400824100041c4280007500ca0400340080c6801008000386014404817000202c9940c0c2130080081407061944d07500341500900300000112058001d0445110b40710480b070b03014415402215041c3d800c00002c1071a8100d550301400c0681016401181d40d9842c07810807030355078281c1714401070b50440d41074030125240d046070060303240700e41800802400c2a251552900b0241c000109520703000140200d000a0800c41005540f4801c0e00d542c5034100348d1030441c18986410f070070f5900043c0a00300a07603840c07148650b00040480c11a5054640111840d40c244003104151069900140040c810030400b1031400181c0c00081002e4042103c042040d10908210514200120040180540c215080140c0c941200d000c40d008001d900c40f40010f002403147e035442c60391070f4854440c800140e100c4ad0070441d5030044101d4108070300c00001c6240e80380b8641007100030040b280601 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772182302 1250 772181052 772181099
    0xd080606031308090306010603150602010204080d080402010c0b0403031d03180603041b0e0610110c01030e1002030f090613050a080f09060c10050c120619180902040510 74
    0x2e0403a41400b400c441a10344044000342507424559440f24010301400007881089151840c842000803168014802c94007114010005851070078003140301601c0e80c0e10014016030520041e020700d07200040c04604594031480c82528001000b1800c5134203195030b01840c03002110a07900c05c00281e021a125078800c8210080c1c02c65102c1d681e039450f450700f0840000c8240c40e81414800b00c02000c68020381840200d40306c0e03001911200001c2caa0500101c860000080410501d9041054011b80c154801d802880081002c41c0468848445c0381e001c06040340d00171514515281200c9082c4940b9590601c0303015044401680c40140802c00d42e11415142e01d0140001800010001101009400c21100b50b81a6000007405982c440c0146111175480c0c00c20001002d801520b45400500c164851744162a00c0d40500500c0502903511179007441202f24040d511502e0004c000305000076480c506100d001020a0721a001084600c0e203072043c0000c0c1c8001400d4003003402d00400040c400c90100002ea0913a105090703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772183552 1250 772182302 772182331
    0xe06181c0c02030d080603060a02042103031b03061809031b0c031403070b0132060408030f13051518040b101d151903230403020d08060603 61
    0x400203640091070030038020b401d8000c84011000880e000003610b4413610055081d1100741c2c1d1125058000c92103103004114105040300a40d61501581c402524a80c501c0303800d00003030341c80050341201c5000d202c408103100082d0311402d062005d149000303c0180000c900d8141840350380078966000d8a55180c1800041c48000800b030500d0038880712050050040d40c210960a50420548115644aa001d00000e4409440344400001d09201164504c08012401c1604071101c024400840696550441449901090600c4045864102480104221000c2a20003543c504c240035088581c02001c2e17000f1032003100302149035041540180c084603048100600c100704040c1440300000c1c001d0030b00300001a008104206156500c0d0b42180e680750010340300224901224a016040081c880f03a21802d810044005200c40080e8100707100c41840030805504001c03850041d08038a035101499a020500080d500320810b200c05e05070140300d8011103088c6171400c0b000a18040380810424400a010780b404e55181c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772184802 1250 772183552 772183603
    0x1090b13090b040f150216050c10090b0901090e090601080d1713150c031e091101440106082502010f020c010203010e06101707031e0e0618 61
    0x18552584a031160301701e0841d1220b6486c03c0700850207451b4030045942e441800b180940f140340c14919000c803c0c0c0107980700210b943c10080d034000c0a800840c900c0b4140085100c000c200c50004641d103610400016000b0807035580352284462801e1009440b16040c804000100700c42c4c0c440e00c040c0700746d001c4441c589418444803039280c406d26030382c0300c0940302d601c2c00c1c50022003000c01c50707050708139820860300d40b000f6890f0009100d104034100c80c560500201905030310b80c0c2c80c01683d406202c41d900101d901c00313032241110024002d0240102c3e041610207000b000f190034803902d80001050f071680500070038a800314651800500303400192400d0900031003c5072988202e07410f801c3c400d42206900700b031665000d6498034004542c00c1d003c1d400a008911451380030701e0020750355040142d520406510300b03030b5404a840501041c00e005000000d00680700309034440001c400b103184442d8015034041c3c2440030000d807501018007603d0030403001500c01509840b132064010030b80c68000851a1a007200d0070503091070002c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772186052 1250 772184802 772184813
    0x191701030b24060304051f1104091d1f06090506091503032106040f0b030d11150c030403020105010501051809060301020409060308130509072a0b01090b13090b040f 72
    0x5421842c5a40b00e4400000c000401601280c00c1030128a8540b450a442c0809122101612841e1040c1a040b010921040240070403641092602c4031003071860b0500284401186820209a0380d048000e001a241013084040d035644142d000910384c1d800c0401c003600305040060a180350107030840c5640540581041d51599003030088031903e020941c1031001540c255800e400c841e1400f21805407140340350540c14211100319001d4203030210402000307403002800d52070050301c0214100301e0f80700241c460f8245124824080300c281178011418034001944074605454002d003503036016040241000414007249003049181745100e04488000c540b0048640c0e00c40003c42d00a010780e42c8281c0803141050000024002008010544001e03660303941c12a44d82c98505000d071b03010080e40c401e000070751804005010250340603030840b1404a41c50905a8a40d41c1e42c0381e81016120a80086040980d20b040c030940c54030749030ac0c6903003160146071030030f02445800307031207610324044000c0c4003078407142003000c42208208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772187302 1250 772186052 772186111
    0xd03020f030315010306080303041109130c0b03090d090f05130209041b020d090b0904090302032106010f0e060f0309030f040801090c1e03110d0206191701030b 70
    0xd4148049a4591410702043d5420601c1c40ca21140424a4894045000c2101000f200e10468105441d4903250300040e0500c41c07201001441d01020702d05036000980015000d07804c101c003e240100e522a200d00780441c11504211038440544140721201c04c040042c1919102c80d00700315101195030051601c0c2600e000c41c0a4400c039204d01d580310b0700d400314080060032902840014007500d81e084402c44802c000042c3c1d041106405410500d41081c4000702e100d1070150000b81d4a0703072191041c0e07400c0c8001c4e20382c4200e1003100d200001c071412800034200a06964801a403480032440c615114012450700b8000c9182480745c0c00c00360300d0582000002807150070040088038844200f4115803591243d550900a008003e001021550070195041c000350a401910034070701000c4004052a01722031840e5960102c1140ba5895950005148400080984e44280251105002c918030351600080d200c2e10040440742098602840c1a03150700040c4045401ca100150303000a510011549002120a00f02c0019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772188552 1250 772187302 772187323
    0x30605061c020a0c050a0c0303020106080706080115030603050d030b150a17060a17030d050c030c0d150f080c0406080118120513090c0207080c0d0f0f02120f1b09060d0302 75
    0x18440c0b12803200402c9140307c04d180499009500810115407203910580d100d0400f8415980005c21038070051061010360941d942000c520343c01c0c0062129501d680c1c450805419162110201e0350b50305417141582080c418551880003900180d61500c80225030280201207c018285441c0003640000381d0302c0d0325005c0c550030103400005001401d86000318600b03540da6000c4040d40c1a4503007030801103044080c00340140c07401040d019151900b01403070503040c039005000281413007011800420f0b00045400c022034510b0040c15190700600300840d00030040c0800e59280d54842046607240035110000c1000000320403010a600100c1e1044d0340b07004030000c0352540034000311070f8070050440c00005008003040c5d100d0340c1c0b0302526800341c0e61120342d10f030810b545440e083c011407074000700701c1042d513400070303443c7c0303002c006640d100703000c005401041038011400c1c1008c100010f031911382c0801201c010344c81041000ea601820003c00340b454039a100070100e0305002014114034081d03600f041d80d60381018000d01514246 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772189802 1250 772188552 772188563
    0xa0b030c0310230f040c051927020a0203220b0316050d23100b0a140c07081f051006080721051b0304320706050a030605061c020a0c 58
    0x503800c4c1540d980e01542c005981c216144032145c1c20001d8681020440d4010284483c0c0c0382c2d49030645005903410710b84000d94540402c2400208807040e10040c14400785c00f07480c0556000707540b6003440710149440c4500c1c0c240a6080000e41d41803c02988075a1811250b011480803100c032a04c41104200351071034011601c207180c1070303424146c140c00364086c802c00d4142056144040c844154660440580f0020b0b040e00070707444480f804000c0720944d2801492070300500c0c00311800d220314060848070964208040c85e0000c00440d04580e0003400d0307044000500c40e04541c0c41241c02c01c01c504020340001d0b080d120504c034003801d006c01100003804007400344503468000c21244101c3c10708031603402c00503001003104031500322046002461031180146c035181664031455004002c07210302c10f50300c80c00c1220b005070100c1c09a0001074805e484c880012007805000c00501464a415880e1140d46c0030140561718140c10580c00703004144180c101a21040c03511010b0f8201040740142d80300c00c1a80c040381c242c071300010040c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772191052 1250 772189802 772189871
    0xa050d0906050a0f05041a06150d0c02061006050a0c150905010b0a06030207020f0d08040b220b090303120a0b06040602030403021c05061501180803030a0b030c0310 72
    0x1d01c441504260700c12104210300308a1032100548034800c603030b000c0e00c1c05481e43d02d0035021013400c000d1100d80150050702c014003145e6000da412040c08980d80c0002c48855125481c0d00c0d0450768030b1f80400141d40c00502c852a204080c0b4101440141640158200381c410046140450707000c0c840f900303450100c1103000c00000c1c80007024604086000c3c02c10301d80c007940603000d5180e00040c268070910a0b2804070f076005145c0800c501d101c104001c1c106180e1760094401807010040000d542d60703403c005004403400c190707987d0444100000e13200b0580600d5071112003074603410014621155404021141c01305041c0c0c241c0035039a02c070b00300c0d540300803d8003032000760f0464400030740400c07a60340010140040341d10031910031407002c95410f154145142840700c000c265a0000020401c00691001a00340290040c54210240540022680b190305101d52040c4640d8200005108806c2c17000e010300c50002c203040e4010b00c92940d00f2004259180e21440d08a40e00701c2d5611103050f03802e800350910f502e400402200c13411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772192302 1250 772191052 772191071
    0x1315030903020c1905091b03040b150d020d0816081b28030507050f0d08010e0a05040b011707090204091509060b0306100215070e010f030515060a050d 66
    0x400034401040190090710803200307810f8451410b82550403002102d00640c01900b45842d003404801400640b40780c2070340d00b00040040070800310001039441640212464245030502ca2802c2c180b00c0d0b4600e05c030b035014244000e0b190000d82c81d0100c2da41c0c10f07560f22001142e901c4206820201e1613105400e0004c00207600003c41000000e07003042003a070201401c9059030302c4118045099a154003011604c0000c0380d042c00355003030100e8096000342189074000d40a8580c1c81c0f00081101d4140780000040c00c0200c1c96440050040e111f102030556423100300ca0104200e103042c01d4a40c80c400d054140301d1601240d4501d00c0707a415010003484204002c15001c41d0654507581c8a80c010405825102030300c0c80c454440c11000141c29105010b054201d40510221514548a403420302c00c240080c90420015407062081c8500d403214400d034000e2094031f19640d10241068250001030540020040a03000c0504110600c6950810311041001c408000c07666a030f550100070f00284d40500455042c080018039100862 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772193552 1250 772192302 772192307
    0x7120e06090f010e181005091303050702010210050f10050d0c1509080a0605160518130b1309020301050a02280207030c090504031704030f030b03030c1009061a0d081315 74
    0x507400340e9100f184446ca1562240d0170b00c0740e9a041110501030944c480721040c40840d0140d07004192040c01031041e918003800d071a01c50000d035581503504180290f2510b0400c1003003031080e100b24020300700448031070380c00c108240ca8484c80703168180502503448640b00c20000055000d000f403034004013001819664500c000b81800c40090100304c1d8405541c4590348007014680344034500b150101e01c28401130010481c10301d42801000340c5066580c1d09032568034015070341d083c0d69100c140c003458103c140703000c100f40501e032041c10709542c030240ca2041058010f0040c116092006260000b010f0000d0915191001240d00c08070b03c0d184150340082c01c81d650118020403541125003045209502a41f6a0f2131104165040c1402162084802400080101030000c10580c401d401250b030f12000101200e0070414a01c148600300502c003100c10b0122940e504840007007113800d0007591011007045d40d10072114031000c00803943c0b2070360524009010a0001500c094031804501402001e817010489070040f558450001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772194802 1250 772193552 772193599
    0x31506040915050906011e081017060901060f05060702040218041d06070f0e0d1a0703091401020903191a13060e0c01020c01030c020a05060c07120e06090f010e 70
    0x305800f131022400020600c1d4020300c0b19040384083c0010300049210315080071a45038038041c00054031219036010004041d00c4010740c3c90800148200070308450706140304003e0840f810b5600250300522003070303c00c100b581c0e250002d40f40108c0d010b403400341c0c0d12010400c00c0c0880e80180440c1c10360061511401c03d0300408075000e61914400c07005c0c101c03181600c03140c1060719104286445540002c0d100d0b60500080d040c01c02c03288100d580f10b41d40410f140100e03590b0b850052042110404002a651404001440101800c106003100040000c510340320341000880c0d20340e801c0880040c450106800403600f04400c000f541d8000031039031510545942032a01404104401d0413005030392043c20036011003a40040422656401d0303805800405803125284015406071004514010079401001449000700701d05108091041006003441e5686080615090b0310190b050b00d000c074104400c08400e0718045c0c90700c1046a00302801168015142003645c80101c40000c046403540d90051b00c17148800354850801d01e138 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772196052 1250 772194802 772194809
    0xf0807020a06110316030e10030e191703042a03020909030a08011406070507080321040f1121100f0b030a0f0602040b0714120a05031506040915 63
    0x20300c501c85a0352500c0c00c60380c604000354050000c1d0010010306030030071180340510310003034442c0c01c040c0209a00c81c00018481c18a601d0680c02003519070401000c007c20501400900e500d14000c03529082140f512200c1050705c40703007900307110504000089010301141035880c29401d54010b107185034450042c1c01003c0c002030188422806103101e0030110300c0c444000b000b6140c0c001d035241d0b1510703101c0e840d26800f81c10140e211982e6603041101000f039070000c510180045000b81003410300555079900b400715140a01e02c515046903140540a10610002440c8054a20f009a8106c020f0f2170003545240c000601084032114244500217564040441c03e120202d503030342044040042c00c01c072040900c00d203032007a0388040c044694036410603250100005d805e2078010b840c10303005000040c1081d4845035807904580c001d00d0181d07100c1e1a60b0421724000c0b9001c206104140e0103c41d0705608202942c2c0c0094058000a00000d5159490402102003922000700b0b40d80140002c50302448130540520b00030050200500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772197302 1250 772196052 772196059
    0xc24111308120c0613140a200405010f1707090513201c0c1a0717090d030507110405130204110309030a080a110a21110a0f0c0f080702 59
    0x841140b02e00d50440b0503188040c1184000d0600ca5648034200100030404a004450f003516212481d070758a6020040d200c10540720354032051310781001c03001c0c084a049014458901c40c81c1000300500815200d0306c201d104458040211503000440310150354100009030300080d040604d010100b200250301300d0312551129000d00d0318003501181415655510080c00c01c0110340146004600000000d00903040952050254000c0c083c0e294075081132406145940744001050400458184c0501070810624050100d425109600e040c107102c0104442d800507002c0a0140304011408030148618200c0c4c078207a49000070030030425894810004440405030040903800b0310329000c03c0d44006041c1c0421603010b003045000a42c00c1c5a10f04204561a10000308111403c1ba143c41400380e444250402a000b10402901c402d00000f245040208000d01d500f90800702d250300b8060741071400c924030740403200b4040040c5041c000070a001c81d030644414481c8580140200c1051041009104901001d825124401c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772198552 1250 772197302 772197313
    0x4050d0312200306190801180302060703140c030901150612060b1303141005010e061c1113180f02190e0c0d060305060a0c020106060c24111308 63
    0x190400740d0701c2e11206080300d60082c01040030859514200c401400c1824a81c8103182c0781d80c2e00c0f40019802c2d06e80b0410b0811010007000d441c5c0c41090340600445a010015290400050302514000d00b00e0183c0a00380c00f0400d003000001c1582d0705006c0d0402904099241c65a40d40f0540d00c0d07000602c4c0d8a4407030010340c100d0785001d034003090807000700c0c0440f000041c0c1c01410f80301031800c0d07403500202040a00b82c0c80c80584600702c0303c814046040e0085500078007580d040c2d003150f40f8000e414411840c00f600318201d0040311108450b000110540124124084256450b500781e44104035400c004042c0014051001d49844880d041009000c00a100040e44242c440040c000360140a0802c0440180980805040d8001c00a9503101c3c410002d071002c44081640455896904c3d02e400d82800c00c190358912401d91580d50689034150240a4800103224504d0042d4940003162540d143d42041546001c00402c0003801888041d42650809410075104c10380aa6482400c44440c200a14140c03194100c2030160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772199802 1250 772198552 772198571
    0x1090f02311203020601090f090c09150504020301060f270b07050f15011206140c090a05240706060f0602030a080f01030f290a0b01020c031b01080c04050d0312 70
    0x201c118961455044d0000c048503400e08455201400383c548600034000d945090820110b4850b02c512002071400074000240c21318030700c02d00480f00c04960451070003240101300400136594004c0c2d01360051586071400c154612190403e000000359085144481c09111150110700700882c60010118244954101e0b461100402c40d80d649980c40802100907001d480c0004005844040710514007117441021300003044a02301c0d20242160f035098800c0d0545004c041200748080c00c00e448844003a0034110390803d000f440c0c07101003420000300d6011a40c00c1c20401305420040003415009403003d0301c020f00000c240507440d900c0080d5240c21030703e5108002004030001c10300d507080c95560030b41a25000340290060b450a078481450000c1c0d1070500f501d0360603010105900d01317010f00055030b0042c4400400800c00d001410002860200341c1c4a90600c02c0c0c00810180800301c2d980302602c00f030766400f828849002d40c0e524400c4401801240d200c9030700182100c000d03104042d8044014111540044000c0141c0b564 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772201052 1250 772199802 772199819
    0xf15050a1a0f0a06050c01090b0f090115030209130606080604080a1707021914060a0606020c0a050d0b0403021002070c06080c090918010207140a050106050105030f01090f0231 77
    0xc0250b451500030110300d0060090b00d2190000b000301218220010840c010340c1ea5415003610300468400c102082c200040c4592008280036410b044290803c8c140c0c402400d64001401165010380820524104003062008000303080d000180140750603801d41e45107184c14108901103521000c2000000382e261000301d11010400c1081c64068080d07030f802403506203102d80d0541c8030310310010f07000d507a4007a14502b2205e0b85002000030501c140c070010808280c252511401034500b40400700304078428100168140f0054442010740010b103074108440040c0b1307455a04059003081828100c0d1540c02d400094034200b40250050b04c0c004680282d0b8568a29503228402c500040c00b414100951144e03011000c600044004840702220f002c07841d000620706a941e1303607005186400100c0000c03198100000c90f5045c0310b03080c850440189420b007001881c620703103410984c1c231000d01402140801a038440710004030844548c1691640c548822407501c00c40451044207081c0415802c03e03410030741104074003003403010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772202302 1250 772201052 772201069
    0x30e090405100504021c210f0e040b011e03060302101110090302120c060109050a02070807030302030702030d390e01080919080a02010b0a060c0f15050a1a 68
    0x541140240c40320400b0072225101404000d08240d81c404071040031051300c2d10300044054503051040c00040c2e0202243c0084540c4000c1c0c82c01008207110305444c3c0e00041c19044000c0e101c54400c00c450010325001c1410040e2010612807100200150300c0804101d0300c1c0d82c2560155069a000f100c22803c000d00302c1b039080714050403c2c40b03030018a4010080261103860950800014940300e801550b1058504094160080d00070300e0340c28a2030b5108800410a6460911070170b5002420301109510b484d001d5152034066210307140c0010b00705580000000d200070301c03c0c0151034109035043c6003401500d0441c01d60780c60724201d64200810215200c1060050920308405184042800361200b123580d2802e07000540380b68500401213500c038040c8070105e4100c6400d41449648061045125a0300e80e410130100900310b808020300140104541c54083c1725180c1c1280306d04d240341c0d51103d550030352031025140401c080e01d04160b051440c5401d00d000c0c41921340c000d030009007007a40c0201c8140c22810100d003c01107601d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772203552 1250 772202302 772202311
    0x20c2503060203010f1e050d031d060a0e130506010f0c060e0307080c06062209110d0501050f160909050a021b0606041a06090f01110f15060904031d0d02130207030e09 73
    0x1523040b04540f800640503000035400d40620144013080182100003086042d406520884005591540d00b803107140f8040c07500002d81401d1020412844c9040c20000e080108258856024403543e07800c0039040009a8012441c21590301e41a60740302c00251600715000e8011120f050018041c1000042d0b0078141010190715008400030755107950005145010010300900c802542c04141103030260000d6101c070320b2140d0070f15124100029041c079204010580c40f00e00034103066035521028141c80010f40d40b0236080800d40e078001d0390009141d211401602c00034414200c40d0304400516015800d61403001045840c13250720191070501035150580188011902015141c5a00c040d0078800e020b410704240410810551040c109200f1501100302c009c0d14162015001e0941e40e0301c4070004104041c00d40c15020341000045d0f400550a003400c0c5c0d000b4000d202002c1380c1410902881006400ca039460300c030343c0c040140d00900000303f25034041c0c42c000065480100d0a4000c61200030702103640d410302483e1644107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772204802 1250 772203552 772203559
    0x40b09010c08010b0a090e19062705100302120601061d01320c160e27250e10030c030f03030605100f080a020c2503060203010f1e05 58
    0x20b076070038109410301c01e8201c180d4003000c0100403140800c10b803007030302036aa0080c40423a64040142c40701c1e00100e8280c503010f03080b2000e0440017082a100f8260440610750140c110307980d010425540744107078556410400c1d48065030206110244421801d030110f072583c180c0f213859623010103801c2004130041c180d110715a45140014014905201d180250070404010003aa0308450143d9120000368600141c02484500c01190400000b010504441c5600360f0010045a0404202c910301b480007011007080032a0104812007400c0400000c9000c14412550720012141101c0c1c0c154060102c00c00c00c0c04514042e108501c50401c01082004000343d4990781200e52101c148101541107654002540751000b800318103054556902041907507c100081440740b14980c0c07104050480f10200402c1d4030000b901e8a107845e13104004402c80485d002c245054040b142240c0d104141040440b464031a2106920103000c9030304c04400401c0c1e4912914a030382c11101d0720044004500344168545410b45014403c0650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772206052 1250 772204802 772204817
    0xc01090803090d110d030f030c091a181e030115050603070513030618020f04060506030606210f09070f06020309120a05070308040512030304111c0614040b09010c 71
    0x2500d802004814080e04c02c8507a0744d00031034100089100c1d060250400c0b00400c40c006a403c0c80250300d8450102040300328582415890700d444c006078814042254180140d080018420400c962210720f000c45204d009041281440030f00d8030845010440903942c40d21039404c0c100700b42c50b03403160f8000c031100387c45004151a1035900c0c0c0700420b48043d13000340b0803841d8255180700000086915440382d204200b01003404040a90b001d841004404100703491082d100d06d19002e81480300e034541d4015250301041c01e50b480380d5501c06e11032150700102132841d482e45001c580d0030104070749031559140090040340c0c07601c222402c0701d4507907101100d07143e100e00030341c0c0050f407041c003510f0700c03600e00300c08000c0700b002602c010764000c0145c80d1a01418021141c1050395800c0000808201c1c034105042440d02e2003011101031421402c0542d5250300326490103108070b02c142600600c80805170746640311004041d82c008010814106007a100c41400c40046605680e0703000b0355800206d4066044c06640c00f01980d607a5842c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772207302 1250 772206052 772206067
    0x906050909190c0f030309090b03190b060406170106060201050717041b090203041103072907241a0609221b05180d0b0406020d02070f0809030c01090803 67
    0x21118910b0010a4030080d20880b000140301203031050300350146002c0c0c0c4c1c403a055141011200c80c191442481c541c3d0280d405451440c52551001c8404010744ea848602e00c1c60075140d01d4005005020542c01840d00c10466200b164001141540400120381c1240c000f0b005943d40d1031016152448544c28040310301860070000340c00200c074695074443da100c1c43d00080101380d0b00c41340c01c10201d0300120f8080741c441d001010068458a403c0200308003c1c0300b44420003642204500c0d0307052960300c40703081780005a180824440100070482c03895074031a0501a4a101c0300c079a000c81c40101602a00740b40320b6061151001c554040c0c10309078111850760f00e000d007a1031103c0400341402e02c40c80e0142059614415039505003101600c4464003406500d01c25a528540c070384c2c21a500f1008001c500369223041c458a112080078000520010350389501c560407050040c1c40f8000042003001906c10014001d10366291a58485c0800c5804c00251450354001e50440e01d441d8285801541c0901c031354010310646610601403007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772208552 1250 772207302 772207333
    0x60c02010c14071206020a180f0e19020f040306180c0506030910020406020a020310091a090f100501090e01140105120102070203010c050a1701060c061d060406060906050909 76
    0x1554442c8428110740c3c8555888880001c03009055500310b441507000969504081e500c00d1082c151101d40200e011045072410080c44041d910510941c20900b8400000130046150350103080c0c3c0c0700751007000541d07540345d18920082d5203500078002105c8807031414259100071307400065516000e40c2c0c404031480042d4205010016a0b0704010b04c0000903200b0415204000030aa0020740700510389900240710340c2043d441014241400103055000583c07908000c032010500000b100900c2c00c0303006403164984d8484141550500400c007858001901c1000110705441441d03a102d00d0403078210381c804000803880301d0030840c240d9600d4406d180540c110940144038514140801000304511000014a42511580402c0c03c2d00c422042541c046400131580d006080d800c000031180b2040750349000307240c6604209024008a44484001c7c00d5242c2c0e0317164030014003030141602c070300258101c0c040b24800d02c0e0501e4200007520180c0100d402c0c05081500001d080e0034004001d5028810001c0a4000c49000f4100c0c13 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772209802 1250 772208552 772208573
    0x2010309050316050106060306060512180a0b0c0a030b03010905060403050918091b030f070e1b2b090c14060405090f091e1c0210020a0201060906060c02010c 69
    0xe54482c0802c200d1801c5100c80200c00c1081d880c0300e42e0003c52194504003002d0708441c1e80e9030203401480002c00c400c2a2850035403e84560115407007000c420218040c3d50003524080c980c1d040104000c45020070b0048a10203c805070854a489031703810b22510400d4018182a80c03820300005050f5446040400c00282c040c0000c0c1261603005441280f030680780d05030013031080005441040c045d400121000c0c1c2249a81351005100c1c56069004004104004451315a240305038440c0000c0301c480c42011404c48040121081034003150f52807415100c01c0f2902e0340c0302c0c0050030741080803551000001044042c200702d0045403000c682007420031009500c3e091042c001880c0340054a940408100000308256841008103802429940c05001c107038649080301c1460000452128501c41e00b408081c03c0241d480003a0040c594804132580c1000350003030407000ea2a004103000003818003800401c51003a850747c1503004000310761114000740b240303d5031414246c43c0150b11480103400a8001820000404c043e0400e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772211052 1250 772209802 772209821
    0x70b061c030e04020904090311061b070b040201021207050c0a0504060f090b030304030506130b06040209090601030b010e030706171b0405211e16061d03010b061306090905040f020103 80
    0x351908016178002403c441802e9801c80100e909030791903807900079040041305d900540d801441c0d0120000030080304005d0044543c010070418448001a086920030711901040d0310402d5600c6440702d0680c40e0258407690002c44c842c0c00f850343d10f41e0010301864540109000c0300c1c0c48500c0620060b052800c100301401c2d05410782c1d901403108000000014408100c030074801d003440e0800240484051038424400c82001d00030300d01c698014055084aa40d60513110b682003002400c0c00110f0018031401641c000c040c3c816620351502179090002a81c030740040b00480103005903081c01181c0d0f03030b80501c0c0b080c0090400d0603400c0300c5d80042c4401d01031030421032401c41505002e1039080c12040c0340420f095140c0204d1406603020181c80c00d01180d54140c0c20010001c4110829101c84070b0107041100051861070801c900b49a4a20b035031800c18030303d4400b075105100c0315402400702903070b400c16078410709985030304c5114174000a40302c0e07035001400348103510442f4080e41e07004003592a80a126001103000d4001000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772212302 1250 772211052 772211059
    0xc011a1018150801180204052239020313050906060d0c050d0606032f0409060e10060c081e0d2c010c08060607140303070203070b061c030e 61
    0x59010035070266401d800c15100d02c03599984841c2e58148800d03144030f00a01c5c000b5424144c0144001d00050ba00d40300062824041c481709400c01944100c62200904070101a0248410f43c0e42100001d00d0303401c00c161460200c1040400109042c24138049a0301d100745007450365000300702d10083c0064540000f525402c008000c2aa5040c054008010705c02c0f124000e10410219900180e40100c40000740500030090141d402c007080004000000c030030004100c0c480c4081c6840c10b100708800380c40c00140684d0302402d10001c04009007504c0d241d0300200d03140c083e1581c5040c1007050320002034140c4102040e04030650302488181c20451048440040e0621904102200d190107100b0803502149510400410010761890b81054070480da819445002c210701545800da41496403c0360416080b0406641045040c0d5032903035260001c0c1040c040c9081d810b011304c00d4600000041c0010550b000000d8444a40a07111510b43d5031583c07420462240312500701d110490651501c9507020038007070280880c8180014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772213552 1250 772212302 772212347
    0x7050702090106080601020601050a060e01141b060103021525050c1203030a1508031e04150801031e03080718031202070e090703080906030a150b0c011a10 68
    0x1035000444100d402d8200c040040d400b00304101c801c0da4100f2020f40140000d90307529900c2800c0000c002c06114450b010700381403164684c84410800000350486003085295201c400180b0040001d85850b43d600b8801070788940081a240b5400c0340c1a9001c41d502c2107503900500140c40711251a41500c03950359402a03d16010310001b1800fa500c0f054201800c0c07483d402d000d150b881ca45100300100f1945c01c200003803050785084106003c3e1190000803142a00003900050300140c040040c101998851a004084190202c01d001c2100503007010b0210705803032244071405004002219601c04070000c500000d030000f41c054011400041c09a03241101050507560403280a03601c0b074460444081e800904500140c0c8091020454000c0c0801030640103040d44010b0706c4d140b440c503212010717030b409250f00e102c0c440c03403000002c5403201c603040d48649590440740303803480c11940e5103008681c1d40d5080049411495400e040116201010307100140c404403030000c0a040c60020380c001d040312200ca14009624051900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772214802 1250 772213552 772213567
    0x50d0f03031526070e070c02040905010c030b0a1a0306010302030a09141b01090b030109020f1303060609050f07090306050a0915060303110d020d08071b32060f0705 72
    0x3400c0b4480103000160034601001c418140e110303100d20800a0308106075003004101307228407540206840d4200e030346460910003406c030a0001400403c004036004110b9803a00444000311601901b100a20340380c100c0b001c1c6102503442804403590183c0601807e40c51400f003000405540c02035002c1d6400116215002990114030b54441142c40036280740b801d2540c0c02918a264160320034030681003d4003007031a0041c8543d18003681aaa80d000600a0f482041c1c1c000c140c62a908101c1c40c1134070642512800c02c4810690b40b4100080203191500070f0b28030407401d1800103010248180e8600b40180700e071b642c84080759451622440014100540748041041d01d6503011030108850700d002c040b0ba403c400320005120b901d10300d00178042c08620240c0030030603007040d00c860b401c580d008509102c2c1c00803a41001001036841040444403640e045002602c0c0e2000303564000c0901551590380f00c40c458890f6049a02c21003440407012850081200c4000c00ba0b01040006550a800c0e800598000441d41440340c1402c80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772216052 1250 772214802 772214831
    0x501181a0f07032a0203071a1e030a06060908061611150603060106030b090a1a0904030206150a050604052206030f0314030f060405131425050d0f0303 66
    0x20002c8281d001442444001c03404004a6110750081d00c0c031105000004078242d408217417a002c0c98412048005045489640d035403040500b00c0d0001081c1d00d80c0c0801003603901c1ca440344540c2003500d10441d903918002d00030520038040c809041c19128010000e01c1e4a07a074400140d40c2c6442c05000341010828880f1140d52003007401c10903180380b43c09441c070640c4075140102c1490300d40301d0140d11200c10182841c10a18564a940018030b8204141440100342682180c2600d1508183d2070701d960341100e1783c4030804c0280b640c0443d58601034002410b0b404140d41c046410442c2d1a0001d000722603104c0c800300810442850a048900911019100c9400c8820807080c20681203c903e60b2098425034140070361001099800b03400b00c000c08826682c69419410080d9000402e518000d001a009950311000311307141c07420340c1c03000b0b0503407550211265240e07003a04044280c442c202d840500c05010721840c55a40881c070054949810381c0d5010381042d0b100001034840f03840381aa980010f405050351004100f23100790 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772217302 1250 772216052 772216057
    0x30207090213061116030f0807020306040605042109151407060c0f2a020609120708011109280906090911060c0a081b010207060c090501181a0f 63
    0x621001c21108030740c94190041c4c5800c00504c401200e54004c8855944007001d01c5034200c003600c0e002001c864003d541c5117800081440f4170b00020b0350501c40d101c2000100300703041c1c03c80c521851003245c0507000e02c0c0050123000825150382d40da06011400786281403000100082c01c0c5a840301d140e00d07191414100300d02280c61103030700a4074195034040e181c00850035030b40e400c00c1d0b00100001d071b1407400e0701100c0784240b5084445030801500c15005080020400d0940d912a0151981c2c40c070010440c010380803554006a44d181e490741f00e44d0315554205030800300c810000b0b8094401050020784415a01480001c811003250808000203400020490780415591207900c60341c0c0c040d01100d1400030380c050940c1007040c815518600c60600c1550204880a050304000c2413080495910000c0c198669440b40450305055011a401407103940c80400c803c403d000198203c1030030b64041c1c0d11405503490b164801103804d541001000c0504c2d40840c1000c2054000a0403062a094601c240550500803412107a6031941d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772218552 1250 772217302 772217317
    0x405090f060a080601294b090f0301060e13150605180c1e04090c0f0504170703020a03060b0306060f030a060504020a03080a17090105220302070902 65
    0x4050401c001c064100440341e4405052a10000c102640c5041d1054219140c2c1010b1055204028041403081510010a8440d8a03101003014030707540d55509800368000503100301c11510200701d10104400941619003803441c446003d106a440e081e0301c0411b101d40d001d04111211f400d1340d0f80d40300c0010030382d00080106e80906401007140d4000c4040b4202043c2d0810b04a40383c04003245080403c00940d03071034903104544415030b283d1194450f0b465a6003601c01e4001c05211a41024004607114500f00703800004005540590004100310040140210b5104134007214000204608210901034203071040c3e21101900d80c86011640110b40303030760101c2c0c10400690710888140341c540e41e0070a26440c0c2030150340c1d40100c0684410002c40740d9800041c0e902c20044001803d00c0d59108081001c0d9190000424050750300f040502e81e48950419005140062540b020681c2c03841c5007011546841c0c0600810f802130200211000d15943c400b01c0060050302041000c600750f00c503843c000140c0b4842400941440b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772219802 1250 772218552 772218571
    0x9050a0e06242107120e210403051b06070b100302100e01112a01020c040c0509010807031503080d021b21040b1603050c0f0a0c09090317090102040509 66
    0x202c0c42030548088801050301e29800d401424001041403040d4001d0786800514170341140820410b813600300782414010b08415900742c0036104000c070420304500c00014002c0302c4c81503040310070441d104c2800c088401c54078001c00350f01100400c0141e01140b4070440564001281d07030000c0203d039650b980000c40da03d40d820308600104600c0e6203034070b03040e40c3c002100400b210482409001a410000d00300c82c4501440107001c01442d04452420300564401c01100810300d001810410501440307280184c180d0b00308644060010360035200052080d403283c01115050411110744030000703402c41d80d49890581201440214442d400d009a09544048080009102e5000d002401c101c5a505841000d0601881282ea0500c1c0c010001004103090f450204e03004010325401402d8100c099140860751885210103008591184495a41c0203403001300c0c4c500c0c071003480b61941400150b910292a4252100710310080c02080400d5901c4182140c1e103291254400d4080c0c00041c039058a84001900d50b62341610807114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772221052 1250 772219802 772219807
    0x80601090501180506030d050322060614012303040213020d05090f0d05091014070b01140a0e04110f030a11330c1006060c05010c09050a0e0624 63
    0x3100f009007080604044070103100340828134020700460340d181607130300f00038040110000c0040c4a121481d0074080c5159500b21618030405118282180a410b0a00561a81ca18044038403042507029401c590061015800c030722803e40c400101854554100810581c0c00462801030354404080c2440140000f0555020000c0d150914941040c075010103500503500740e5120610050440e0f0300f147c01e40360301e03100856590404014241013110b010703008240c2c7d1688071002281d9031041200070550a41a94128103016901a041404100c07501201d88981181d080141c00820042002c04401d24803c01c0050b000310200c524140c0030905d04030700c19005071802840511514000d00c1e00603c0300c5042d440c1030070300009000ca03204030a030031003508000c680c104a0340002c21030100c6034284080380042d0410f810800a00b41d1b01c030030280c01400c8152007100e0039440d21480620441c02410003000741d500183c06003606034203102019030307070000c040e04c0c0562143c0d2401c6005400c0131300c103203003210880b02007010f41d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772222302 1250 772221052 772221059
    0x40e040f1101030501060e04090206040b1c0b0d02060711040912031401050603090c100e030607110609013e0c070608090c0315060f090906010f080613030513080601090501 75
    0x10000d001d498003604250408004004441d0b00004100407400212400900c501881c80012030360b1203540d20801d103c00c03010420070201071034070704100914004184240183c4505208020b114400300c10000c1d880a000d114040100b03140801c1c8018181000d8070018800031141c4131442c108801404a400180e00c50707942d140410382501195004010a503030341d906608100402a4580c180d21041a005902c05501e03044800c0c40b60001c644100d8024054414501385500e008107942510101c0c0300c80307803141c0000b181010a0510410072000b0105620b00407003040400781e80e0000c40240040c2000109007480c83d25001c00c40c1008107141c031600e00081c41420701e403103005006400002c0c9a070419400609880c03c07241c80c0030030000c85058035404040e0080e510300e400640c0d4000010400340d0030031225020003050210004101c1d044c0c5087d14a6020700320343d00c071103096517540304480c401803640f1880e0200340024002d001400060a502100b070500036118601c0c2d5103882000da0150300010f440c4c07030041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772223552 1250 772222302 772222313
    0x51525021c120f110a260301030501020a110d020d1d090a020405040c11120a030207050f060a0524061e0c100b010302070503090d0c0f090b0a0504270602040e040f 71
    0x5011401403c00c164040e05035500c580d1101581100648036211000b00c0c6c40c14101c0d1445840c48588200150640742e586a040550007900003c211101150340396000e42d1072284002a5900c0c0f503a00d030303801081c4030345a507a8203c5140240d5001d104005041c00041035440c0d0390160b43c2d070b200e000f4110700142c41d01d1400040000fa9006500c0311001c3c090000e4164002c1100840c1031022400220500395480d503403810700318004c0c810690090494051954008290349020a500340038240d0500c0034811520745d90224143c409580380600c0801c01614804082820b103034001e0444841a58a184c10f4290400481815030b40041c121a60306d4000740d012000300c3c9154428400401e501f86011802e0090603941c1550764800c143c201440342c03403862040810030500300c00210203840b05200c0d1240d0030399620700b80000fa0820145d850300c54003503000c0104031070400d1310070344200915840c2e0a00c1140003076450032840c1440c406069514903000c00004c225410002c5a40d4040c40c441c1804041040d41030610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772224802 1250 772223552 772223567
    0x903030d052d0c0a0c150f0605060301080c0d1a01030b040302120301060e06030405100f09030306140a030201050f0d11030723090f0a09060b04051525021c12 69
    0x800541180a151141030b074a9410310a5a200140440503907848a078004140c1d07107100c2081c80103009100e03014080400b52016040f04030f4040034220184500703a22142004a10b007c2401001d00e143d02111b2846800e142c101c200d202c0142c020356085c0218111000c104005510980050355411f4000c002e0100300742d4104840498440c13400040c030f00759410194028100b02108465a103d60f402101180030320500b0b000f0388400c140c9188d001c21410744100d04480c013030a680320094000c01e181490005d04240c4260210f50881c41c001d02e01000300d400c581c01524190081600000031070f80501604048100500c1015000c0e41030010058a85c13600c408001e1401e11100c5241c80c1c0101d50044240c2501100015030b41941c0b0203c85100d01c3ca0229400316a58281d40d0340118011030034410b0014400486100800645100740c0d00e800c0a0714181408005030320800311402c500950030460b400310756a08a00e0541c000f40700404184100c285602003080c19180c0600075150500c074540340c4d4603542d422244 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772226052 1250 772224802 772224841
    0x3050d0201050c09090405030d06060906030608030711040c0c0c18180c03020609060f191707120504020a1728080f030717040602070c050a0506071103030903030d05 72
    0x2d11141c0303010b08502105004024026000f10b09010108040060500503a000b00310080000c01500d40d841c5c0f0b000301408554820440401d00c0e00401140800000c011500916008001d9424007841303031003800000c01049402108200008802c400001d0007440c03903100070300d2684121840480d58020003800c5441540610022070020b0140c030000865a42043c400c4940440750340e922043cada44042401032080c070110780813241000809880f0300c01e4139030b55400e100c829541d03001c00901c00f14001d02e1070444203079080340101d58000072420410503240c01103039101d40b01500d005101591498000819102c00301c0584468200c00740004002034481425100d80754a1416190742228541714104503102d02001c19001c0100007002911071805008090b60340100d10070041124600307410440d002790002e10003102d40d2400850001038609d40140090180e48005001d14175049003991502c0019003020b00258040c041400b041d982680d040c8041c01c1100d00840c004aa0351611030500090314030240b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772227302 1250 772226052 772226057
    0x130222030b24040603051c050c1c032a1101050c070807050f120301082a01050919090b0306090a210c0803040303091103060108122101080703050d 64
    0x101000840e6152481540000100302c5a01e51501241c0442d140c000034900c0c140e80240c10b1940000c104040095840c540850320303485040c4203525603000b161140310b504000b60065001392210142a01c001508d80100344450800084e0b103254441c1080282e02015202c40d40326240d464044030356900000b00780341d0b489035072000300810b152200403465140141140030f05043c001080d20300030000c0801107042282280012940c5042e100c1c00300e0300e0742d43d00900600c613881c000c400f0485c244075481c03212520091210100d0181a046403401116184c102003501d40d48440b40840c101d82d4001d450844c1005000448404a441c1d8040c50600d890444041e010f07001d1070303120350960300104441d040224413000b80c0f1883c0111004140104452903481101c01130072010f0000284420543c00d5480442590b1080c41d1403e09507810340101360701c07408240701d400d00035084400c06030040b6070310030001c01110604038103036034007200004014640180300360081d0b00d45070300005041c000e1020400140f0050340c3c2a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772228552 1250 772227302 772227367
    0xf06030b030c010503130206040f170d0806014407031a0d230106060216080c010206010b030705130b0d0b030a0f02040c030209041803030b0307030c0e090703021302 72
    0x2c000070841e1000800610320501001c640e40110b5980008503001850804400191680c0f11a140d001555440001217450b100300400d119803d400343d08013902c00c10050711000311000d41040c07118250804032103a0b601031f040c3c48071a184a240318078030742c0400034071007150549149428580641200c848102a41400e09031003010000c940d01da9410062a40c0d0007000128006400c05076101c2c0100e0310703054244103500700180490303a240e00154084825205180742c1071020340d1003181d03d40b40c000d03502d0418010303000314004bc410706a0078401540c10540703030700d420343c607020558941d2081e01410ba0050600800c0014060820072401d014046003410110060100c6010700c1e81c0d0742000283c1c45030000c0c05140c0380d00040c40464001c0c2c1c107627180c1d014003800920052a806a0010680302d15040480200c0c4c034000f80c20040b414005004015203030310800396009507013810b4000000940007003194400d445162404401616114064089005412005622101c0f40401d9240d503d2041e03859a10b0b81c00384 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772229802 1250 772228552 772228573
    0x406141b09061315051c060b0307110304050406080303010806070813120201060902030421030c05180a030206210601080c071b03140a060e0102120f0705040305070f06030b03 76
    0x140c0044a8421800b00c40341c6a95030111004107030700004980c410668140e003c120b00c0105a0004000d10804403901100e00304500c40a4607002160400e000352022410203000180d03800d13000340303411500202c0500c1100d04007a03640c030003c1c003507c80c2030304251020b40010004019200301040071a0f0030284030309091442d80781840c00c040240004407400b801c102803191039038020707170b00030741c04000a05100101950341e490301d42854146034904000c5440c8190708032061071005403081c13040040441140c1d80f181c1ca021301d20320540140e25a00c80c1890746c0000c110f0300000060755400000c2c0981d1076074a41020006036044411031221100800385410300201108002d00d90880c0802c440303425600898800745000c140554007a4403280350402008001c2d01019042000760010718410900d100340c006000800f00301506a00740d00070700302c060402c0c3d002c1c107000c500794582400300386038040c0303203442d1050030181c2d2070312003515050302e0b68490008001000d10034401180d050144102d07600c020340040c6408400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772231052 1250 772229802 772229851
    0x3020114160c0c0905100312090803030c090604050d0614011d010b0c01140a02090f03010b0a0902030603120a2a052d0a06020c070f0e070e18040614 65
    0x85425250741080301c0d540104007004941e0b0410009070100310f4040040d840d014010381003040b1a07000984040c04c06401c0d0508042c0302d0440c00b001e8074048000341d8207581b01c6031091042e0350070217591580c0c070020600000c04d00c1e4940303040c07080000d40107007030201d11a80031800d526000c2e1070681005541030f1800c1d03408100706001403d41030450781c3c4992100e41d02c21202000a0040c844480309908040a0b103080c081c0d14041a0003510040c00100d03078084650120800301403c9554550b0b40f01d81100c40d07080200722282095000d07540c007903409000d44034940c1203070398902250350255120300041a1070a019800041c0894811018840440c24030210000c0c0c0ea06ca1541c0c2d4047d9050001c81c46408102031488404507030446120f90002200311030501c0010315105003e03400105a40b11548a0140300080d1280c03c101d60000b207800c1070346440340c7ca455480080703a800b0742000d13206400074103080702008045003200050f440303a070041a0015040001c0d41c48040301c0c076000341040c0081a40244010036416 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772232302 1250 772231052 772231081
    0x6040e150606070609051c090f08100902011106240625140d1e0f1b030504050d0f02091f09051b1b010b040c05030c0703030e10060303020114 62
    0x20084910b107890b80e00078500b220260070086401005805500d40030f1101e00d49520404001046503125200f8540e00e801054070300d40c40a2140d4407030781e1300c0055400020b000d154009490340c1c0c0185030010300140c0c010042172070400259041d0041da9906080602056441c001e85044400b04031340f12890112501c136090301001003890080030034006007100108100c0c0d0742c1d0783c1000d60030000043d20200b1102400103071801c150b18100c1041000c642c051030440300c3c0300e03c5902d4122070b1141c940d00d8500700300c40706c04211305540a01c1101801410040800c456551500ea0032203948610f40c03440d1282c0e0984144103014201421100c056404011101d448004568800303040e00c090f400009101c1d80c404540d241b80304600000c42501c18000a550a4640b0201400b43d4142d00c51000034041803c101c0306110031240100b03081c10004000303001103401120614000c100c224042c0c80c022400e07045c03041103641440c1c21824040065550341604108241d028065842c82000c51140d5051500c0c00c010550900d0303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772233552 1250 772232302 772232311
    0x1050d031101140c0c0c0d020603040f06110f07030f080f0118020d021b07121212090203011506030b010903112103030907140d12030c0c02060f0306040e15 68
    0x4484551a0709800400354020800d200b01c0300c03500d40181c201030120710300030382c0180120b40660041c03103554996400e11081040000e40d0180c607242c950b0b5581e840300c45034030318a51022a58607488a0800071603002030f1000d40500c0103081d500da56100510702d005898141d111090102f0b1101c40820491510303a0907000504640d000755509411914500392000284582d98100d03030403610103c0c1075800200396000440510451004584185480d81c010940080c03035008000c1c10550022661305e00ca5100c0c1c0d030a0340d00280d182201041c0d81e25650300003800c0d00c1c0328200700848101e4000e810010981c1c1030069030010002800c2500b0017a086407250840444580003203401400c0c240a103c002e201442070101040030b40c101500d840b410018031082d00e81e10a8071445080b540c105640140c1413078400e040e94816a400580c0844045c2c0e024015006400140300c0c00301845203610102c405030b00e4103030003440300d1084c903503038a40d40b80360480030001211544504108107511061320f4060718031405000039000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772234802 1250 772233552 772233557
    0x60309150c120614130c020a02061605010608120307030209120f060406050a021303080f04032009010510050702010e13020a0207080601090608070306050a110d020324033a02030c1501050d03 83
    0x40005128240c2c501082c2020081d042b02000070b51410700d0101102105419101e80700134044155901887c1340d6400048180e1421104c0c1040481c0e041340c041d9009100c040d501a281e042414280c02d0580e00b05600c1050f003500d00d8011600b00070400445204040c0e210800010460074a000080c04201d0601c0380e00000b030541000003404030b401107900c2c050b036004503071180500380307032501c0d01d5820b0b4014800d00740850301941c02040045020f207407641c242500d804840c0c0d640c90900360303d9001110700300007000c0e91580010a003045055103140c0c5d40018010b29403e034000b081400c3c079180b005460060305034401c2c41c50300c0c680001405444004919042100e80203070004c51540c4030801804020a4072441d685042000040d003400d8000064014510621800d0001401e00200e205182080041c0702026030f0b242c3c100015285907a090030390b00038060307902c3c40c812184440041c0300c1d840d10707002e440348640b0241c1d0020511800322030301007101ca64102c03c005c1024540b54034243c0800c40244030b01c88001d05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772236052 1250 772234802 772234811
    0x5070306140d05190312060503191e06020a020c010822080f0f0403030804060b19060c080f0a0305101208040b07060b0d0803060f0303090307060309150c12061413 71
    0x2840400c01201c550100251041d00c1e511811780f4003e08001d01e40080c15030f209081840016a07454046401d5002d101e04001017811504640e81d51240c0203001c4507004000c24900c040700c07003c111544081d00c00805560000c007045480900003401c9560010080c0c0c84600392642e0448105842090000941d0350050480752500000c0340141c83c13034041c520003480424008a800000c4c5070740410030fa801940074000802900c80140b0901c00f070101c2500a207894480846010070000d8800c43e505491a8010f118070350410104082e010711a0703000d05050800a600c0d5028424040c611403980c80043c2400d40e0388414641b4070750b9950328140600c2c4a000c0510001040b80014080b80384c1101d9403400e4002d00e0010301214502e8800400c0c3c0082e600c09010b4020441114401d040010444642c3e40000b40202030592406800310098007810904560b21503580740e200000c6491070068010410b0380d40c844200071001010b044048810707982c00100c0e5016070007400100360b00c071040ca00074182d641400114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772237302 1250 772236052 772236079
    0xc03020d14190203062215080307050703141f0510051e0f0f12010c200705060d090b04032c0d0b06010504080f010510060f08011202030c120607030507030614 69
    0x6d13019520440005650f00051044940b0100c4552100a0035220325200b40941c6481e582d040c1e03600d00032a607000b00158040707001400801d250b8600c00310811042401c681030210b002c0c0b00c18806028000c191801d8940707840c144120301c41c2c05c1101002500f0180c90710111032440c070f02000123803460300c55400d005002401c1d41500d1522154a010345c0c021010f030811030000c40780540d0500806948642c1d000150b4241c0d0aa40001800c810078605440001c0007008881d08100c100002540007103107048007540d4804211000954045266100314025295240428611192040c1024640703840d0038000f4190030407160155511480c1c0c0d070007550800d03aaa00c16540d03440050b03e0760310840c0c00403141486490200c01c50401d054100343d128401060241c060b8a0396810255080e07000500c42c400465003510040c418a001a85d250b201d1a00040455844107811404680d0080369003949890a0704200e041103907668050003180e070040c500d45410006589041040c054910b84400c078103104906041215 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772238552 1250 772237302 772237309
    0x307060b030a02210c1e040e070b0f1b0706020303040b10030c060e130608071406030720210304030809070e0106030f0204030c080706120506060708070201020a05010c03020d1419020306 81
    0x1c4e0075441c010f0303c0f000e21044a500c041405400b86c01119105608207069034590380c41c04140300c000c980000307000a0910078000c0c61082039412454a07995000214107041d0910441000017400901c0343d60080c1d95070781001e0401561800b8000d00301d406400b501001000001c0c204d2403d1401c407102490a0001080700c200010420707a007036030750b44a02a0520001240010004c644c100031582c80e070080c1040da958400501519002c00c0300d440c000706000100006145a401c0051070715021400156500c2da042c410052100603031095020343c891202004100030143c00c800116009050700c0000c02240e03282202c41c82d45110140145000c050310780d03124500310159601610051980600e41d551156191090300355500094850340d40000ca1480c104581c2c0740c114810f01e40980300140605152070ba041e00d4000706980021405c0341140708a85015010035020300c2410404030300d030391300580d40b5840040c8000aa481415000c07074401c48810521242e80c000d580c6040348002654030142e22551102c001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772239802 1250 772238552 772238563
    0x5191a070e121f1b1704060519051006110102360a08030702031615200627010b1305060a03020303040b070302010501150e01030e0106170307060b030a0221 68
    0x1041d04030301100c8a515510f0b05400100c03489984070341840c240c0f00342d10011512400116040c3c0d420000c60400315011601350341040d07510410003600701c03c94070304001030b40b8220340045481120354010350300c040c040310307511407040311090070218000e6062003541442040e4506002d08032900090100130105401d0348100b84181c2607100081240303601c50343c4c2d60b05143d1281d002d00390881c8240542255042615903109013201541c0080444101d07000c281841a1503944600f00d5291004d54510900001c400d01000700b148520550701c21100790540882c0c0340c1d130610b02c100c0d0070345103642d05280c080340722034480011940b464001010049816140c6c4008a20000c51540000c4d406010014000c42c45c01046801040c200d4840d900030489a0f80e9002541c03015507000f102d0000003001e40d01440703841d62203500070003000e050308000000c4140d0345c1d840351014212911150f04498101051907000e0103058441c070340103030100b076001d0004520580c0c00070f0201c00c500399000c801880c07603810003001d02008104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772241052 1250 772239802 772239823
    0x30f060307050a0b03010e010603150905070201020708030403031d030c030a18030605041a010b071104020315041d010f060e06010c0606090c090918020609100c05191a070e12 76
    0x100f0762003034581e202070010740d2090040c01c0e07016601200001d103841c8a03104280580c119400e1060b800c500b07242c890400707440701400150440d07400b40001004505030000440c0501c2c441e4800286080d0105540c00802c55103c0c1d0b41c42c015001400f009603c1040441191540841450060440900b21104001c0c10003076030400340003140360808000403c000543c81b0000b8092030020045260b03030b5058150224402e800008214200480610b001400e158000d56001007546c40f1514403040208042003c0b1a16101c104281d017180603580348803090284200d0f1040b1505100070310469081802400c032a0b080a0034850400032044030b18400c2c172865a1002d00034265182041c01100301c0c2280040190109004569220780b6010210710111480000b01042c503074007030b00f00c3d030503d10340d039040200c4c10001040c04002d0114400b810f0002450900c40c443c0d03000e10b404018010303e0245e041003045016188550601104c0300c0091004064012a104645010417603c554005011548450a103410140c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772242302 1250 772241052 772241059
    0x1020f0703050c0a0b130308033301030e0c0904170d0608030910050a09091104030f080c0607092115051503010f0b0d060506010302160c060e1203030f06030705 70
    0x1101104000380496805a101d40444143c00c51a40f1081d0621107445000601d80b21241c00302c204100123050070b07000d59403100e80007051092004a00321024045150a4056000c034140d44443c01115a01440380c11101d020643c003c1400311031440114107080310141000d4080f007142d140c545541c01c4801d048802c400d590820500c16969140d50496803600b040741005d201e0030b2404064522140b140301620040c66141d5200d030a26881e002040004144042e9071549842e000c02000c0045020520f80303410143c0320302111543c2d01400d100940c1417050103403800d4200052000308000c4039075030582950111000c103002c03407215031040c030b0701c0c0d0100c140034844100c0c16820030040121070908800c100780b202e08141d00901609200000d00c2c4225480c1c861123903408030b14a100180441c1d080d07480720b5030166042c107005161071040e904244801c64060000c50b02c021034410306209181d0700100410500c1c070705030340e0038540c0318000c803c0685900009001d84160b00e110800245070741e5040200c03000400e4083c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772243552 1250 772242302 772242313
    0xa06032003032808060904080313140f0a1a01030f03030c12050403020c0a06030e0307031202040504020708071704150503130b10030606050d0809100201150e09060a0c0e010c0201020f 80
    0x446240f49a0205001e85001113030050340054154100302c1c81081c4181d074441d120901d03640c4c41c0b80d030711465a0050801a07582c60200b4101c2662050200a040842c1d42060b00419500191745032000542030303801e241d01c80743c2211030010000a07802031032648055525007000700c1d40074910340045844014550038030500320f04007804e100074140c004c030f43c1940d01d100580c1c140d00c107942c5070072041e001d40c4c001040d616003640c000c000d4030f404a84582240000030b405170f41d000d40381c650f45000140907608840815103d1800004900c0d04000000070122480e0352540034072810280b0f484501d50354030107185407103410301070000b00192421040300c0e81110016031000d800c080070b0500d00a943c140c0500c034082183e4003440c10401141138604050b030f8007016940b02c00940e28220850f002d02409655102d440301c10740d9280d451610f980310a14410401814075a00b00c42294503040180a18242e0003410444280e440c19440180d020307840f84480180440a0030002d400881030701c0100e03d0003040d800d8410160069 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772244802 1250 772243552 772243597
    0x2040f0b0d0e0d03061e1a0a0c0512040f0e070912080702090a05100e0609063109020a05091504021c1a031608102a0806090a0603200303 60
    0x1d94042c0c0700b42c40c040004100d0448858102880c251418061180800d00300070100101f140030900a1000c060b507898885c0c8900032603030b1213900d0400042c2c181d502c0090085414028440791a034441c0040110f811124407a081051004c0d0140b0101d0180316080310f15004c0d00000c1c8154042160115540900700850500c1d00c000010020b0038199504291840e005c000002c1d41390381004000e0182500419003507058a4110411109004404c40060651800b8400c6d001451031031510400c105600c0c0004214401107204210a0000b170360004c6208082c0801404103a0310480740c090031422003176400607074416203030421404040e07541101d41c0c2e40702d0904030148181507548801c541441c5095003141c0320301201c14940100d40311280942180d581c46a01ea04c5803503580c80c1c00c91198501d89441107110b03038400038503d550030200705802401140d04217050241c0c80c04c110344082da0052080b0010880141903a81e40c820707950180511403401d0360081c450101c95901070048600c602c03007040c0040ca52400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772246052 1250 772244802 772244807
    0x90515090a0b130204180515030609060601080f0f181609090c1a0a032412030215010614093015101211100e09010902040f0b0d0e0d 58
    0x11840505003e00c1c402451400044150b00946060b640800329480a0700c0b0506c4903d03008103c01807854069221540021310161014480170b801050a40060b1003140380c007000140045e00081d081c1070880d401030003040601d41da01a24590003070b40000c00d2443c0820344d4529640707000b100c10001c10702c1780030700d610010b0120070740e5210b49103091103052600440f0b96102c006454526095542c411400c0003085594240e038429400400881c01004052200c188020026551102070342c016a00808242c032b6410705041c0c04120300024101c18540c254400d41c107200005050001c0940e542440103004504441995141d4040c0560302048419020070701064003030181040c000c0c3e0000074924001d80c00362042035030285100e80c0c400d00c44002010b003400d1130142128141c10a0500030b40d02c0c0c0d1501c800e00c414a03034800700b46054841d4695144108881160b04210b807c0e40180d00001080388108030801003009142c031840100d9040049485d25650100c40903c068051806040382600a40c9441c0c60302c0c94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772247302 1250 772246052 772246061
    0xc12040f0311030a0f02130e19060e0a020a0506130513060e0901090f020f061e0a03060b040e0f0903040812071203141605070206030f0403110d09090515090a 69
    0x24003400207000003000b0b0380241510707010751440240c04428048401d10140c00d01d4030f00c00c1e0450040900018400300c442e044242481840e003027002c440d0780062145820300c5424007030701d1001107400d00074002000b29507000540003015445010300601000c50300341d200701c4044200400503c0c003d0401c160048107552420300504040c0a003804074500c40c404211200014440d20342c1040e4003d001031001c0496808226440300c0154a0503031145040080000c040070b00242603030190301200d41251201c1c541d850250654041d6000320316045e10520003040703042160310700c290f0400c080c5014207900d03440303800c030160661059400407070791032050034200204c0311540e00092040c1070003800810402079070544114140c90441410a05401000d8045174500303400c4480c4a10728030351828958a2701001e980407038031a41007211041030600c98002000141604111106130031140c00f00500703842400400040d01e84101341c09030540c141d503900c001408802d01500c8841c600d103401040d4040602e00b1201e900040c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772248552 1250 772247302 772247309
    0xa060e011707062309060706020a0801030507140904020904020a03050a0305030108150103050c090730050703050601091413020c0f010f0b030c131104030807031b0308010b0c12040f 79
    0x30b00c554040000c4070f510581101d4015645042c0d18040b550340080803014a0b000b82054981c0800108941c80014819100a0500b01660b0700c03441382c15071560410310b04000e0f0030352000c000b8072110000c02d07640d0303035401c0740541d40f10358101d03841c61064450f80082040c0e00002c0c3c10003425481850030341d030b00f85138100000d1130482c0c5440b011518000990660308075100428400101380c0d0b0301c4902c4166582c50844030240c1c1c4000309180003800d000c0c0401d8081c0f139881009180c0000c02440668030107980b0b0300d43c000d440e80000c16003000d0000c1d0802ea8002000c609141c490814028100741000d003884c1c1da00640e5112508a00d0415034581c9004981c072a1118030542005085601c0c000701e5461065180c01180300c00c034802005480500700035000c1c800700c924820315003102c5503652142c1c21070200310080584080d602440c080c03511000c4034903010b00780b07020080300080300c01081c1c240f8200203175111b0006815207203a5030900d9110340042154900e40007841c2d0008503151004a404a80c00c100e40300f00304102d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772249802 1250 772248552 772248599
    0x81b030f180a0c0306020c0f03030c040f050319020d0311010f0e0f0703120e130606020c2404060516060903031a1f050307170103030e120606180a060e01 67
    0x961881901140c1d035075000303190007000351036001c43c2080032805a07400b070140601294140d400b50100c0318030003800c55008942c282765a103800700b002d20403560a50b000101401c1d0a078000c140311001d00f0b080201c54607600e08024401d2103000d0560f801c2510400054121510030030007030080d08444001e400150088140814844c42443d1103210502c00000340034080740c0d040610294001ca080d5000c54400340c641c250a40c201c10009511407854216200f404010999075006e8000c4d2403000e0100300e101e40700c200c0c20858280f6082c80040074540c0c1803084404407907081c01c02c640d40e01082c070444204060800c40140c0168030706040002415090307003116114050744402400824485d030100602e21501c484032849004010b03546907085030042c8001e40e001007031414680000145109c40e51035000090700201d001805841e100c2d81182860815100310120244c003400e1076160020214400b140d0401c01041c6540481c0040b0301a40d040b40d00100140c070310444c1c010300542e1a01140103040a9041031800c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772251052 1250 772249802 772249831
    0x60507140a1101030203130c08030403060507081b0310180510050d0b1605070b01090e0d030209010507110609040c1d180f04051501083406081b030f 65
    0x200c0500481c003041003079409840c2200912112004400070f410090141ca038940903690b120f00842e44041d8070300000e00600c00210396450540c5008020b940014101005001c42c890501c04100c3c410240c034007400c03c040030a11341380e0b954487c1801960385141d200c3c25105e00f41c05905040c0d500c582d0400c5109420840d5002d0b0160354500a000a2900385a0b000e45280401001b24040030420704840c1000601441c180381842c8a58035002401e490a0784128a0a40da42020803031500d0706015654540f0700c182000c6089c10b4070100041c0040c030446c980240180300605000040b5502d01e4141c2d00c5da420040c0c41002926410390000d0003820782c000541032440c1c01c4201c40d040902e400d0008240d213003c15035482c0e0990710341c080750051850001d80100c59501504100c00076412002d09028024070070000140784810b0402d034541d10407a00044024211881c80920001c0740030188000001c56540e0310b02000584e542c1400c0caa00f07401d0703040d41e40d0f0304003100200384103a0500840016010b00d240d11925603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772252302 1250 772251052 772251083
    0xf020d05090612091c020624090703020d06150e0315060a1205010e010c0324060e010e03070503010221093c01241703032707060507 58
    0x2262401200c524035406102006403c00503030a03024200c1d0450020401c0758034107a82c0790810390043e0601e040400041c0c0c0000d0810509011081a603001d8150b4aa291a12404800c0c0411155000104200141900001c1520400d21503501480c001c040e00f4148503103042110100a040d5903801120610030300ca294080c40c0001d10444075603003c0e01004113140d954510303040140c030cd2110f101c83c0c1543c89550350801c62086507001c0c09a00810907a0341c0d0300040d21402e999a01840c1c98004400c1c0130445628142400085e410504003002482c0900300f050b01c0024000001349041401c0e00002c0d09540040b8950038000b131041d944410b041e01003002c1c807041d43d0f2614400c81d990081340724031002c1800303018144400c034032088038580d19040c8000c0100403c034001504850944100d03548604240b030b0030030490003100c82c51a0368400070300b4000c45849810704404001640c0c80c0400380080d00004e44031074050824100381c1903541030844030705083e210515600c8a002c1d050760801042511010420031104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772253552 1250 772252302 772252307
    0xa0303150e090d0f050f120106080702060f0a150f0308090312070321020904020c0604140307110f040e061003060f0204030b040b0a020c01180c061103160804050d030f020d 75
    0x92180c811a401861051a560000c4903044c20034010782c801e101e82081507195401c4a100100300c52032414291580c19490110002d1020310010b10640854000c803080c08110350003800310380c0d00040b00b61804580c9101c2041c0344041000c296218028140250354000104010031001d410f441c0004c805650811850509120891195a0f40200001c11100b00c406020000e48688034031001605401818001c1042c0803400300d80c40b580d10014203a1101080100700b1804802da6400407603400065814441c041c0c2c4c5d0005409400d9100d40c1c42415401140419a110b590005405c04c1000302111840d08041a61a1003048280003e41c0c0441c20a60051003030320950086400712507000141104c1581c03252500d0b50b450601605080038283c0070003040030070220034003451203025a2110340444228203440c0c100c26000e040e500020a0090b444100e5101c40c20100170780700740c0c10644030b4041c00c010b95880c4c03c14041c829500025442480030060400745588a8002c030404101d58003102e2030a10148010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772254802 1250 772253552 772253579
    0x6020c030709050a021303080d0c031a0909010b0a030b040b0603070b0a08090a0204050a02041404061223070f060215010e0a11070501020708031e04020f0405070e030a030315 76
    0x40981580c040701041102250941c0302d1903008108403070050500c01042d01e04440d000495005480b440d00104400124400324440c00035980c03542d040420103000c6051a03c960f405498138014032445550000480d90102900b194020300703801001092040d4907442c0003842020166010b5954800030000901c0505000943d1030907644041d00003810100da02c00c7c1250007030030060880c01140103c611880050302d56015071801000201000b5071a6400e003e81d4401c4c0c8004141903500c00c500701802002000030b01e0b103003400c1141c0c015075141c2c00e1103140c00340d00e03030a20303058484903195101d00003000511400e101d50701800c0d10300d2a400d54140c61543c40002030710010a000d05001718009a010900303884056010200ba040c00d0240340d414030486403601070172600a0002a5040c00d0008108030494404510824422102070500c4a850410341c000c5036911154415950242d691034020a080030700600c088802c40c40020308a4220180619004006c0d182260b00c25110310308900c1d0105002080652 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772256052 1250 772254802 772254823
    0x105070801090e06161209080901030b15040905061c032309090f070311030a0203041a09120f070b0a0906060911032a13080d030207210909020a0210060602 68
    0x14412900c84014100c040c0c5c520f210608140701c2d00d01c043c1d00102c1450f001d0703000030794040c4810075111019100094103551424540b00d2180c9130900c0303a61140040c06003602c003500c1140c00001610f545800104070000e40d000c08404048200030388500805921007401428510241891a41e5042c3c644503a2414050545119404410480040c06582010f040d003031744000e0514002c50449a003600a40e6942d200f0340e41c0d14440c0341c00004210900c0001d9203029001c1507102c40d1840c00c0c1c40d001242c503880d42003503008524005400180b0780c650300d080300f0548881c3d6070030101c603c44034100f46011100070075011000700e804600b04000014119000c1c0b06901c0600e6180f007000340f9542d64000c8500c03003100281c00491165100d011520080b0054501800501500b6800d040c80d0500b014400391401404a8511080600411035540000e0050303aa540080041e80d2080030300d446140d40a4901c11441d400c940c0d80c40d44003168040102d80c0c002060700c4c001e1500d041c10004192103400c2242c90711003058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772257302 1250 772256052 772256081
    0x20f01030b060304030819090c05101103030c210a091406091b0a09050f0a150b04030f0c150c0c051804080a030e03031914100501030b0f12010507080109 67
    0x1801086c02206040c4e404240c82860491008a0703e103058111440d0403070a4802d84002a414006414184051f0703007034001505041070128003e0b00210b03940d1000401800c1c00700402300d6045a002105120010161071401000505281501d11540140700414040e601040a1400b08100441c0816014001c4100c1d0001d41400c0d40644007441e000742d848900d09402c0340d481c1000013100082e03881400d0003108101e1a1400508010000038240d4008410700c841e40080d605e010407040c107600040340e0450758400303010310030a812801e1420040402d80d203e291464081081b032440035078005e8401c4840b40c41400b8200155480344107010b40b07545642c03e180b21500b80d0b04081070102c2d040e080034000000042c5008281c04070b800d0310107411904196455031804610104200800501d0f00650880d04000e51101c0d46500c3c0480c40448050340c144111410300d42c1d00c02c01c00c4aa0348801944259126000d418211288002c599440c000c2008442c2c142c0011002070001c203100156000300c000703820100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772258552 1250 772257302 772257307
    0x318020307060f090e0423030405010915050c01050a02090310060e06040504150e0c0a080a1a070201020c0106080a0308070503070804150627060b1c0c050912030304020f01030b06 78
    0x34030241d901580402055060005078840000c60005c00000c043c440d5106068480c4860030200241844405506020b0044d4005000038491642d00090483c11a0889034140416204008054440b4410075425519550900040040c0f48a058009111800c0d041d021511520a0340a081d0201e891382d0140b41403801c40c00002c80c5080c0b9042d0040c41d0003c0c0280c0c41d4000000d01105e01d141103500c40100ca400b250414480c00b549803038580c140034001c200340005850a12495510501190401c1007046640d104d06004216001d100f541650340c9525558000c002ca10389031400b80395106107003081140015292030020355074920034000c0d00e0045034180c03602403a0b074550b561084403400107802d5001495680300c0c000203c68040d5295103500c0d040c40102c80c2000c000c90380080c01911540c2c4c111406c2c13a482045000360207100601444030245d440180040c1009400c0c00840d81403250005003035005524864180902c800072000b1405644200c1d0514043d0381001c00640c142c44605000c550300038410b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772259802 1250 772258552 772258559
    0x9010911040f06080714130e0c040e0705030a112418061201090e07170c011107080d0801060206070c030f05070320030705102a020c040212070318020307 67
    0x82e0005038415014041c0800c0107900c1d41800c914045480e4040002482c61003926005810648070310b0404070005001480708038001c0ba16540e4909079040404d010b80e0743d07800c401600d0340090050f20b0250000409503403149105045c484115001c081005105070603810281c0e058041d244040c25003114800d108508210400b5071040440113150354050300300500300100a188105114894040d104107600060a18071701c1150510300351642d00081d2816071100481d101503140020480001c400900e4400145840400b4180c100020703944108158451503031985036441e04180b206060310019802c4448695440c0400c580c0b6841c00b49014022508140e1340c0d4862038880c000521205009040048900710f0450a0003210410120176240c3c9070408141d1004002090010100544076048140103503264180030b0071001620f8004076400c4a000c81c00d036440d50780248404442d19030700500441d142c15140e061100560801c031b6548000901d007180b0000d00d650072032094a495500907009180c0d0608 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772261052 1250 772259802 772259809
    0x3031812020111070b0a09140d0c050f060702130e0f0106050607152c0d0203031e04170a09090c020f0a060b0a091a01022a0103020306010507080c06040b09010911 71
    0x1a803143c9200c1900841002083d03080103c0000e140b00141c607520249050300d09808641c0e051200094180700e42180c24011003c103401301441c50542d101141c1040074504004006400e40c854050025004a04d0070303003004903072005612080200b110380003036882d851030000e0424200c840718051254002001e00024010607800d00c5002c590f400c150200040c000014041c980000903044581c02400340c4c0981d901d000014240002d02c2c841030140010341c2903003020120101c8100711000a00e1006000500250500072140d18a200d030141d04001c07c0d649001a0a0080c412000c50044030841c90a0050300c244403480010b0494256188038094003141259035134680c054080ea0007a15801883c60401180400c130f40e100c0c1480100a2180c0100c83e014243d00182c1048000c0c5140d607108000170741c0399441840b0b0600c540300031358806d00c2e0040e6207940b108010f07034441c0200d2001403d0003301041c00b4030324000c002500750143d400b0328001244e69943d52119400d0311340304d40e0000e004000350a2429903508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772262302 1250 772261052 772261067
    0x609030f0f0b0f0106090f0b0f0904112205090903070f060b0303040b041401020105060a0b030405010603080c0a0213020306030a061d0f1507030c0e0d06140709030318120201 76
    0x344104005100e034209611440b031018410307100819058405001000402d811148040040c50001c241d644000d140c82491402e601640c42e858920030f100241d41c1c481c983d6641d0000307841d10986a0400c0d02c4190501303461703c800021101803064000b072182c000c644c0d46000900c15100308a42d800075441c040c0260350740350b041c66256000316121519503200b11802e55051001d4805004000d000e02d858a16080c440d254540b10606200c0c10b41e458002480310507150b214410701038410203042c0790750382c0d1160324081e801422241d00150640c1004181c0389070114003c500714045a008483d29028640d040314031504910050b1031199056001245c40c01c0000d50542101150a807100c12005002132450006410b28006443c00b1045401040e59507161011481c84680c1103001c80c5801c1000041002014045580d038502d0288510a4803103042c0c00c000941d0094555144915144501030400400c00303812041e4a002c120046103107031101d0f14441d08039110800441d2144216000f000590790015103405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772263552 1250 772262302 772262333
    0xa0f090e0a0e0c1302121024050409060303030903080604050708011203020712120807020a050a0303051306110408071a0304020f0102030d020c1b0409030807030c020c0307080102091504060903 84
    0x601402d01d441d02c8565484000c00000e2214100246c2d039000c0c40844043c0024004108440b98580b42e442030201e6a0345100040c5c1d00c00c01201d000002110140f0f00b940c26025075808540740311b00b07024010081540c5600320b521003502c00e0325107240ba0307200e1740c00304426074030304580000029034900e0040101e44002c1c0200481c00c0c0c004d0040d103850b6900d80c0b455520407001d2050a0701c0f545081c2020b12a103d60202c4d046a11450750310150920205c84da403201c0d2510403000d0081d040684941c0494080059400c42030241640008200044514000800215009413141c4080c0b0300510800007040000c4900400501d141079081e5442e564880d42001030010051280e581180f0040c400e0313105e040c00d03900c001c2c0039503003031100288900003640200c50302e505890218170f80102d007030090201c0000e40000019401c0002c504011610105000c030403440c0a00300c0b03040a03410702c104007000811440640c018103c1d0030b820341c3c09880303520081000d8050780c4100e10500001540c942070400120304040d800300d604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772264802 1250 772263552 772263581
    0x3100c030b03061003050c120d0e0a12050a0302070f0308091e1903020a150c062a090509070302120a0903050708040303050a0e0108062103041a0a0f090e0a 68
    0x2103481070350200346002c100f103912440a00c0100c0c01030092010820050313041010031510b51035841505a992030f21440c45d085401d051244414203491183d9071000190702502005954481c00040b505100f80d407000002429000741c0180d09000c202c0400d44140304054035080f00d6868a4814441e09000300041044620302c01e074030056048c5016a03580e03080104681034079280e1000c9280c210700400c0844c0c6916489110107400080ba0184c000c0d401c50501f6501710303000750002840c1c10220441e1400c84980203204d0500c10149103524101da030b0080382c5081900d4043d61201510360b9203a10550480c0f03e0800403100c01010751001481811007a080b003030b00c8520034904039090000b030741e44100c0325030441d4000300c0c041000400c1e0f00124070fa21140f0300d0719010302440d000540e420300c140031505191002001c0100180b01030600da168810410483d001001081c15290807042d400c8089141a0040007248001a111032400c0c40c0c00da06c1040c04200761403180c04414800d8640b040300d00b0060003205a000d18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772266052 1250 772264802 772264811
    0x6020d051305120f060a0504020a170f030309030a030e06090a0b0709030c140f1e04110909160207080703050c040c032310080111090d0c1e0e1503100c03 67
    0xd00f038940c91490401005244010940e80e03203003080060070408000c2100c1c2e015407401c401c000c056950010044102e45a503c1d1068804000480d140d060800c84501c00c54203100020520600d5000007004205a034126030701003060b16442c0b220741e034484d03005445141c910740c004070000740070400704030384160440002e0038014011903803030351a240d01c010f103544111031440c041c2080030403904040038038508050003111020fa04c030242c4103858104000c1c6c043da080c001d44da9280442041c100303602c105d5801200c01041000c1a01d0f159100c5034030140070021000040c003800b500041d40c130100060407000d5a074004041d00103a003510007880300030482e803001c9508054884403081800c00858044038180c01d003640f5100744e5450300ad54506210302035540001c9030b5a15000c100300e010100d100991703000e21402c65084a001c0a0f41c00c09024a040d982c00025400141403540c4400c1c0c0e09082c0311804031800da01d0311203800c0c0c1c2c5900c0000c42c00032000b000da07601500521031003520070810340e0000045003510b080007c4d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772267302 1250 772266052 772266059
    0x180803091507020d03050c07020a0b220f090e0d090915050d15050112081206010c0203060906010305061302240d060b03040510200f0f0307030203150a06020d0513 71
    0x39241e481c15a04200075821009a01900e140e05010b00c5a0002070801503514150540c0e0100e01e40760260300c5144100000031955408400e40020032801c0d54001003100c10b04107841d1040e00204500c184695407a0b5480e00544d0f0605880105a1940c02d120230740f108040185071800c0d01c0c02030031540041d0b40c07154800c40000300d05651240402c051641c002c8104095403030644150300111107060708408a02036424084c5800107484030122082d880081000682c0381e252040140d61002250000950500410701005222440022140d0407203001d0801c860840d2102c2540102c50280309070080e4000418600c05c03004070b0302c0f070801000b1946801d0b20070707803508401c00380c0c00b800c56505d50000f40c2030001c00814030091040c101300400c0caa601c00c3d80104034460500850030041c039074480034082900703004a48802c500c1500810344004000800205940f4505400300070025070040790004101c1744075202c47c1000382094500e06080d40d0154005113088908242d09490301e40003821041601c005003074020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772268552 1250 772267302 772267333
    0x1d0d0218090a1509060e191103010603020406150f050f0d0902010c0503031e0612190813030c05122e0b030a050601150813031214011707050418080309 66
    0xc0491410f00712000a010b121031074820b06480b5003030911803e0354401c0e2103200302c07800400103442e8895400581111030302c141c00c01107800740c0707401e0348061340c001d1070000009260500b440c40241305102c0c5035518a01e070101d0001c2035515000c1c0b1130449a0300c00050240e80d2010300568401305016005040a44011005030342c0c0c0c9156500c100c0d0300c0c540303046103505000c0c1440030702c61407203421480884900b642e0b403003468403180c1c2d59184072044a02d0140b030900c0160500c440c0800f01c0d42e10790400b400c440c0358181c9078240041080c80c548125801024002a038003c452004a030003c00e03003a1100b00c001c40240074400703c0320032901009101c03041580d61144103086503010003800180c984590040c21307541d0302d44003080c50300c09174141a4100f030008250401c41c411002d12500f146041d407505010b00854400d00031100100b10480052901031810400422210180350650320b0000041007120030040d101c006001c1510b13000c1900c8040042d00000590000d09020051a1f0050200e405c5800340c4c252100030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772269802 1250 772268552 772268573
    0x5040e01091b230936060f011413050a0f06091d0714060a0c061a0a1203050906030a110d051006080c0d050a0b040c1d0d0218090a 57
    0x1518040400d0700307802c005803680400c484442d0f02550310402c05141000d008134004040c002c0c4800d0300303501d0b032074001910110303640466520070300e810440501075840500348a03982e0505907101e20002c96024000601e50140869807800d0340c2d00505024690444200e001c8054074019103002d292649072a03518602c03420620800c001885000c20100e458242204c80031700070b0848005032503503030f0401c42e421700190500c015076070095201590410f5844c3c50a03002210303503029241e0024003090900843c4820f00d40034000006901c0d5048405084c0750340d031130b454a49a40e031141d50080100d0828404426903180c0000a16441038800a011603204282e60741500168865843c0e027030315039568014001d030341e0a5601d500c0060025410b112105040540d81b07502180500c1e0740424000e41c40c1d900060400f01300f07800c011b482c5140600288000403017680081c000e8280800b12148004034840910040d01d040b400080e80250054091a0655504000030b02501d4008100003114410448240300080c1c2d0b0085 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772271052 1250 772269802 772269833
    0x1312020c031f060603090507030b07140309060709061e03020702030312090d14120a050907081902190e0c130f030b1501030c0806040b0301090f05030403260405040e0109 74
    0x1050704400110308050342c1241c070182c001c80105440c20451000040001407120181c0740c00403005816a50b8106003110140154407440f00d81400100034481c418030002035090080702d850300c032203009da510380ca8221101105085800241412007007003085042c0254000c0036400c1c00501601d240c40d40c1441c0080b42450240d50500701c580c00181c0c00044198004c000e030071021080410180fa04e520084400461a03014050780011981c60300801c1000380c04010482c000c22a400940d0b80c500015050002c010600034000da000c4d1600e00383d07801c04080d00e9050740042d01e03201d10417544551200c0602c030710583c00c44666559440400c80022402e01c0350303051a1401148a004c5080303503442c1c0520407400f0340c00a4a11a4141401c14107444e829a03008008554024010784000030281c14030030020b409407134030b0840540a444030320450001c1c420007100400580b4000d01c14401a107180050340000500307008504148000b0901080c06180707496080f8602c031031980b50011900c0510340d11065401d9030001e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772272302 1250 772271052 772271083
    0x3030c030601020d0504050d15090515070e01230c070924050f090109181403121f030318080d0306090b0a050123070f0b010504050f1312020c03 63
    0x700611503904204607844644a40b90490030546080003185100003100d200030843d07058181c284140c1c400c4d6500c80b010007078024003259030b031613601c58800c0000007054407040d00080d409000e400007035015905421001a415150200000160101d12083d40245221807140e000d412000a40410280110001032442c28a02400785601c41070703000c92800b0540c4168051214061080c80c1603892110a90440c6c0a110700403a0f8540c090810286c04060500024114000c0094043c401c800000107014000800b401d5410303243c0f01e160400c040381341c1c081c0c0010359100440c00207000003882201014070a16603005621300503900ca070105814141c08400f9a40026a15a0308020701c250764040c0c890721000c10b5418a00e254107040000306848014501c520400b640b45840141c02a01c0608507030304a40c002d8140070f90703040380345450b44060000703104403032095003054007040403103402c0da4a6900454140c1d11003e010801c170b50301c2010040311480d1842c150300a005081100d80c83c20b2100b0718130002821b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772273552 1250 772272302 772272307
    0x1107020a0905160311032a0a02070e090a050316030504052e050a0e010c0203030403060c080f0c0a1e020106151110061d19060e010617060604210503030c 67
    0x1150022190710f20b580c101410141407200c2445500403c4040326000241040c52501c1c40d00f020001541030b044010403001e03000400034281c5078017540031504109035691988a0341150725800c080650b140760100c0080c1c503079002017180080d140303184648101c005100741003a41c1000c0d83c4000080010301d17042c81c200b1180d010302d101642002c0300c01200c104020580d003491410808540001403169007402c90040c18484184201070641d5010000d0f18002d585c031820500182c2c000480080c00124151071350700d19400c1840100f1801140301c2d00391030740c0980c281da54001c0844441845074050840d0880b042c1503560302e10010941d170f440316180b124045d6103601c2c3c0014100c0f40c80c007130520f41300340c0500c0c0e414414030b80242440440b01001908150041140c00c281183c0c94040005945582d5081d0610a80346042400160702c10914000c5040f0781d4161030b41703284064000965003507a0011038200da48890208014031107003c155182c121200c0058034103030003c96440d0360382841e40d4000d455032203144902 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772274802 1250 772273552 772273561
    0x2826031801021905281506180603110906190603021b1c0309080c011506080105040903090e091e0f0f030703050717070210080411010302090f041107020a0905 69
    0x4219200740c0403d14148010015030300d4480300d84074405001c0d00d1503060500540100310782c0203034000c0c26000f500034034080e584a000c040a1b0000700a01d109024050302c1021408041108070b00c50902144c0d0000414101c0c140c004c0100540e040c40101003d034020a044c4501c1c220701e9405200c0409803406840069442c008810401901300d400082c903440e543c09800401c5c1012084900d5664400c01402c0c013145682e01444d0400140c06001c1e03080780340f907283c100109203a07540710805030b048614580760040580d803280240006d0340d50344c03803001c0c02044118508100d08025140b00a0b4417070180d03c16520500030b0071000415480c501116040680c3c815983c49111400610500c0110402c90005610b0500e16580c058298000d00d070b8050408100420442802001c0008903540d07503074028140d0520341003070080502041410f480c19030300c4000001d52526954002c1c0b080f80c1c08070307400814803045d4241090407c0080d02c105e0a00700b020a50074011100142c4900301c100000d4140035002240c603140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772276052 1250 772274802 772274807
    0x2061303032315061e030709030b0f01030312052a04080a0b0a0f0203011503090318090c080703290f120a05120f04031209150e2826031801 61
    0x3c440c0c500d0310400040081000c0c007200c0c0c6550f030b00c0b4610003442640c0c60b5034520b0000d440199140c4d1011f4944c14003601001661580c40744880e05076446130304d032949070145149001c0211b5a04669142d006075122074078080710000c0c1c0826240c08001120154600354a80c0303c804d00f01601100111002d490010511031459424081c2c1d013500d0940305000c5040d0f600d4051500081802c1c12014010325990f0310b994010301d403091514203880309061510314819652038880400034114a01d038440012101301c0440e8a0a20a0158030301d88142c038009040c039a0b00e003003c01c03e03c01e030401e48102d5005d02c9007488840d09407121115aa0100c0c41040540603041c2d003402c029040104644160a00440400c2004155000201a5800d80e9005241e00744e1038100c0010941e000c603442e81141c4042d43c006006c5031456680003075904002c85082d80c03824100808911501004451841e0b2204c21039842001408902034020030310840401e003030614500c112807a040b95055610044403c80d000c0480c2d42004000d58 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772277302 1250 772276052 772276081
    0x1605010e1008130510020301120302010b010f0915120608070513060b04090b04020d0e012003011a030910020409020a0f0815130f0612021f020613030323 67
    0x200c25100945850742100c0c00400101c0300030580704003155000011418040e0800010074030000b0800c0442d901d503101d07070100c2840c5003100300480040d800e185035401d05500c942004140008179443c0d0040d00c50411680300d507400101212041000840300036110b44810358003894000304524030251996504190a101c0c1c0006588112414036050120400420b24800b040306c0441e440141d00180032402c1000043c0644103420210640030708080c0e170742c50b00c802c040d803001c00e00d0301068114840102032034030103016600003440381c0b8030850004c181e1066028084030086a01c02c07614019107180340d00c4001d030744040341c000d0b80149800c2c60b400720320403a10a4121a148004c603806051800c0389280070b0141d440c2210040700c1c0c0c103001c0e0340c480800200c1080107410010f1900860307601804081e84404000700070380180c9400340e128040501c00700c0c210b0322401c50540000a01a40030346011340e1030440010820b600f03100b04a013095503030465452200703044d401d409407010003011641c6040c203103038542983c0d52 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772278552 1250 772277302 772277327
    0x3032e0b031e16140f04142709010e012702040b060d05240f0f03070b0f370e0319030f030b06040506070204050a021b030304050610030b0106110f160501 67
    0x103031010041c1c3c05c030100400c0251801c59450018a40f40707030a442c000b0901010b500b00202502082c00d8440c2030101c01307003540740c910070310f02c07980204841208000141e0a907201c51008041c00701c462055207007401c5140b1707000c1700700d44d002a00101b0441c01c1107003c21501c1c0d0100850081107580c0d00203100c1ca01031a00c04202c5003041c011049031350f0b8100b04001901e0280701c0040c4921038110f20400009507107040c040400102412750344a41c580b0007605205400381d1014010b002010580103120312800341c0300c0b407410b040909140c0001c00d910702e220303015030f42c803980800721a0785482a0701301e1200349a2420b180b075074014802e0f601c0907882c40607044064269030708108464441e6038140300900940d2100000e807400b00d0f40403500840d0980720111400001d102d0840c0c403d01d0700144a80300c6e2001c10002005500540c861400c60311107544003403010410845a0000030b00e4244540c00401c4098130a4005160741d041545c19207140a98a0a10380d10301100c0ca504010900700d403800801c000c1d0303000104120718 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772279802 1250 772278552 772278587
    0x5030a0c06180b161107080c0f2b060605040912170402060d02131a0918060604050103111308161703030f13120203032e0b031e16 57
    0x4900c466480f0000300d50010800d2901299101e00000007900c40d800c0c1d008510b15020035985511303285d00600b0703142d0a8640c42d1a020765902c000104003420a004003000b1030f414481d2200c41075034a4406810341c248000802c3c0d800311b0703c1d100080794603a603a00c10034407660f128147c4c1203103902000c00041c103c0761440806840c118402d10400025850b203104540d0b1030540d40000603a40c0245541e0b004000c00d042c0c004402e2840e003c50742d01c0c00142c5d0700004100030711044600c1c0208824071805174640e0341040f5400b0360091024042000554001e40054520780302401130181400d42040030382405400c640d000340c500f075104141c5c1c503011516201101025111385448000010401c1244079580c1c80b014003801d00d090f4480000550507414200d460b55581d070b1140c50640345500e10f80d4004c1d80c03500b0030303140080b140065008000e840114156144018250609215102450174900200c584c00003000c0d0a1140c04003051564490314102165104400108840d0020100c160004200b010740c020440300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 772281052 1250 772279802 772279841
    0xf060901141219411905060a080a03080c0904090c03020907050a020304030b09070e01080601151b060903030221011a0a09030b060310050906090d1b0b06040905030a0c06 74
    0x89015085102d44c0480d0035400c1c0c9012405101c05000e4040e0910f05034400c0e074a400c000d00520540d2011003001c07140f211081484280c5070300c03042145400f4a482442c0c041d51204246000083c0540202035020701da4030842c1342000071200109042d1032020904a45e4910b8110042c0110318190454642001c0185001400e0000c640000307542c0e8400d0b800081e05003200400000d102200030401e60014000718181041c29581d0342a201c0d44d01c0000b0301034034103810804103100c41640e00c503c003020070080c21240e40c0140c40c0ca254032004000d1012400035001c064003003002c001d03d0b480e413030380d0981f07a000d05005803450342d032401d00300d1403042e001040071140c080010003541d18089e611a00710b8041d00e4101e004640662900000289000d0031031541d005c032103040404000743e140700887c40a10880980041c0c3d0606140c00208031104030080c51030702150400413050300049080040f500da4024809800041c41c0300d059291680ba582144440364005036200c0c420008000850082c80e0101124855466 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 772282302 1250 772281052 772281071
    0x1c050306060d090507050312040e06010e010f030b0301111c061e180f0603060c080703060b1605030405060723060105130b0f0915120c0f060901141219 66
    0x4481e441410002a4081c0d1551064024050b0510401c001450300400706d40d02c1e40d0448024102903003092007080c0710045d01c500051241e5000340e10558103100165600b002c4a162002c040d00140710508016030959a82c0e14507040d00104d2600a00d0340f510350303002c0e0b502607600d46440942a100c0c980c12038142d8801e400f0814600b400b040010505036050031254082d0700c81e020484400a08100c034441d0300703440c204030001044c401954003101001c4500e5855000555078000c00340c0580d1800c0c030a00381d40c00700401400e44c0083c44101c081001300e2144007620b19290703449000440e00e420041083d02c528400b020083c0a15001c5a00c0c2c803002a10030300a48421b6160000045000d5150b0101c010a0b585420340c044c40c50f560030032240b10740440203191440b28185a03644990034542da640c41401503074005503600882c41c0002d4031503900c00c002840342d94502c0340c941c144010783d004500e1640c10f101d000d03c0d007500444104030160400826294031403200345000790016082d80c101e1050300490b40d2400d075544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 772283552 1250 772282302 772282309
    0x50f0609070f211b090b0109060f020a170c0708010213290d060909050703110f091621020d0f0902030307262109010c050a030e1e1c050306 61
    0x60f070000c107510702c103004018440c00c1140c01c40701c031040d120020b4511040c01040002d455808085041020398070361800740c0d10303034505a07080000c8412160240c0c1c015100d060000704608030100c54211154542d9084c15180c403031081c40c0040e2500080e0081c0d40226980a440580d1350300d0740000d080c0d4001801c00b08103041d80801c182e02e4034400800c4240c50000e0400c00012858100f41c00400e4411f1040194000f641012030b10b03010140000c0342c4420850117a921185448000c1c40903429004204021a8494035008810080c034034510780d041c41003418182640c0040034002003034281e04104050f98034041014040e003165110804c0c9101c1c5480c2c031380040c026850000664005079032090061200314101581d040305141900302d00480d0940000d40d4400c039801050b80e090080b40d14440c0c1c41e21a48442018600340c403401b1000302c00241003880480802440303600503413030810007441035450303442d51980460301803000c0003d0482d25030f1014290034601c60004102e501226943d02d03004e4154103205000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 772284802 1250 772283552 772283579
    0x80111040510052506050a050a0e03041413230601050f03010b03042a09150503030703051c18021816050901030204080d18090203040206071e050f0609070f 68
    0x7a40401c000450b40700e201520801d04042e40c04d0340800c250382c654840c2c1c5841c8014103012144c0c400d0171800c0034085142480e180c003a55180c404014051424241410b00d1911140c10000b0700d03e5206030310414490744203c05129848400060041c205148da154003913100180401400c01810031008202030702c0192140810f4074150744026031745a40d00d88850a103d229140e2030341062409440d07085030400b0400307181c4030b140b00302c0d04420810f1010208813030000740c00101c0c620595805400421070040000d12942c0141040941c42c1c074009180391114a02c4001c071581b428948060031000e10912055103800c0086140b48203c00b14500020314008510310b0401035024102c00c00d02002280d1692268002c0e010ba4015000303e0303044402c4d51110300340003004819411070711b00355004411004108a0101d001b120321032900640280d07e0240e0550303554203401c0b080741c0d035018503a004000c14000940180315020030604c14034000c00107418080a01ca081014980c4440c00c200320241d410014400b00190 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 772286052 1250 772284802 772284829
    0x7050c030904050c0c100b0301110408071512020703020709320709170c0f06120402060310030b0a0f0e07080c040e1219020d090e0f0711010c020102040801110405 71
    0x50204958a603000700c44079034010640403402c41d01510081d81d032a1025076000d940c406804030000d0180ac01071000d10740d0036202d03034042c0400a4001510a0000815910b0380f0304c201551441c00084500c0043c000d4812600b022004a006803c44030041100140c00d0181c031301d0103041c8c0d92202c000980c0e0000001d84d220310901141c1400144407002030005400b130340740d200040c5407d1601d1100322840144450300d03165612403030b5224400c40e52090070310303080503810783e540c0e0002d030451401991656001c00c08a80c01c01024009650007002c008000200e6000c60180112207080010415824280c054400d41e10000c80fa400607a00003a002c0200d080c00082110313004805a4000454064400707145091104000355000c200d1000108d030043c00d140c041c040d10701d0324103035403d03200c030b202030042d085454110074450312005588000225140052680c107060300122942814044000c0104059094031141041000940d40c04201080030000c280100a00b10007a0b100044c034150400000414480c90810b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 772287302 1250 772286052 772286059
    0x12140d0614120a11060c01090302071806030c14040f020c030304030305010509070e0402090d0b010618290c070302030712021e1c03030902090c0d2409020d0f050a0c020607050c0309 79
    0x1c0c0e13540c01c986614080315a0701100d80002d02050b045030a000c3d40d140788903c81c482c1da000d0030210f0240c3c08238003480f40c0002e40350700400c4856604d15046e0100c0c90040e10001e050780c441d6480c644c00703100d540648018009402680003a54403480d00341009011598141d200303074041d40500081200d65a40040850301c181411540140c0300e44e1b000c40030940083d803c2c0b5005040c44800030021808039040450f28009105c1e201140394680e4544014a10020149182e25283e000308480c0b10400c803103440103040e9a41030030044501c00ea980341c000034501062a0b10502c0124809203e00c2d05504000300c8581903000030400b5006148a20130110350845036040002549c0d40302409840e081510a0700600d10050b001042985103081c55061201039900c07007510481510301e1f190800c808421101106480346a09131070f107800507403502007540040e6001d801042540d540d1031340d80c94420805846094000d58104800058988650101a16012001c0e107038606200d81881b0600d040b040003c12604c0400040c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 772288552 1250 772287302 772287323
    0x4061a010f02330a0e06131101080a0e010f02090f04050f070c0f0611030f07030b09010302012f0307060c020a11040b040603060911010915080412140d0614120a 70
    0x949480084144005101016500c1024407034126100c0d007058440c01070300c0c0140e0b0310a44441f4501b20301e00102d00760051041c8009400d466040d0701660689600c440b49200100d40240e0340d905583c00c46662000310740e111540410340f0b043c182410740d050f5148080c151000c000c1400c000108034000d16005240b038040121540710b0780304000b480e07101b00d01e481d68820780074003008100c0c840410064004035070201800c440400024502d6209015003584040003070071041d82039082da0011039052070b040a50b4050411651380340c061072440c078400080985900c501541d20b6010600d0083c041d1505411000c0c210750040900e2004207108801d44007442c1011540006c4458880000c00d019004e02c0c0e0014000314544071000003400700301a511002d0107001d0740c6415005031034207004c00848154081c40d100040c4400000740010b50103084424052035075080044000000c034030103000b11b50000c3c810710b04881c0c0f604010404503000e000039103006202165012001c9007104004e603664a0356000c00381405004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 772289802 1250 772288552 772288603
    0x80703081606110d050a0f0c05120c09030d08190b1c060b0a090e0c0306130b04020d0209070f0e090c0702090613020f07050705030a0302030415090e04061a010f02 71
    0x4681c0f1401000b0811501c142c1c0341c2c070280380b40200400b001ca684410040c00e080c460880070380c56202c3c40c81075003440d03110181484952482c0d11103400000703014064020081100188907078007008241c0798a03c0c5c0c2d5685845a1a00e144604003600265202c1d11209060201750219542d4400d403042c203224108440030605540781c20100054000c006070140c01c00e0040001180c01036981d000009240087c1040b40c41544114041c16980c80307007110a80b29001c140704150001511100081d80c00600090040e5002011500040c2003050180d80c8440811481c0d031701d0050b000d0b000307418440b562504407150340b00c9182051084442d482400b1b0300034499903000001417a00d0341c441018010008202030210740752180105007041c1680301003019200341c0f2440400003220701d00002c80751091030781075024506091510620900390008404070358280240345030081a912544a01d01e0310540c003034800802d1900c2d4084c55094100c0d05504c1d91810801d400d000300c200d20340c002994000c09540e40c02454541245c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 772291052 1250 772289802 772289813
    0x303050703021002040e06040b010c03050313110a0b0306030708162709060b03070923040f1202011d061b0d0603080c0f070e010e040f11091e010807030816 68
    0x103560b20341c90f09900c00325010400c20110b1400504c201c81c1034800b08804840380c401913900c10340c502c07030041c00101c0401c00505188034040c8100181481b42d6001d200e18160300000079091131154200d100300c010048200041481d04200c40402001380c42d0241805404805001004c0308041c040c030f0003900e0041e041000300000a62004d80d003c1c0790843c04000d031490078a8020042c003c080d0040384270f07118900d80804c0d0303400c141c406d07440610ba4403a00c02c014104c2c11820700d50074080003403041e5810718903108000e002c107220701c401401e41c0500c0d9000046400003a424032080107203002042c1002c0d0b04c401c040014017008000c01e201002a00c040250300d44291032802e0300642a00e0300010702002c03000c0b0b4010712030320300040c5400c0c003542402c0580b0031040d15802d0f4203004800c24031035040100c0d43c0d4008200803810b43c94a1810f82da00035410991b0305404040031440405050324011b03c2e8544003000d07c0c04450601020501400048018040c0320f803640d01e51041e5401034052a0100906220b080c000700300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 772292302 1250 772291052 772291063
    0xa08060607120c02010e0306150118060905100c080f030405011b0807121506110609031e390c030118140c0d0b07031b0504090c0c170c10090c030305070302 68
    0x4134010300f1240c0c076290400c503420111446d2490349d40400d0000d01c40c030110361100c084020548016540e00c1040905c0d200400c105804540c6070746080c030644130040d02c086042c180040c01004100d480203a56410306141403400c440d049086640800505402e20441aa118904d180c000d40649030501c903415580c1038400040850a000e0104000200c0000400a800050382c5580e07440e10001d4035800d903a4201010340b039100304446004040c200e0180c00d8080c10603200074099012011503034086011810000341c0041f04018040d12986020422540700b61030104007000b640c0300c0c01c1d002400700c00120b415610040c525080001e101910031243c2c4107481000300040b451111004000d9841074196051200c2001c2c07041d0f0b0090002400c00780000005d00101e60744000720b10760b82c4e650514042c913140305540104000849007040018800380700010032032150340c840e6000e00c000d1010381e031488200b001528000800d00800e001c141044d14050200d140d05d2290412207815060041d6a003146140c100e0408 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 772293552 1250 772292302 772292327
    0xc0f060e24030a0c110a050a0305181c05010b0a030803190f0c030510082a06090a0b190e0307151b06090b0c2b0612080a08060607120c0201 61
    0x38008400c000f1142015041803144e00455200c168040e0180b40c041c985964040381d02501a9000300d55030000070388280c0013402d0520401d545025980c4500340091400d444090680300300d040d8080c02c90044c01800c3c42119002ea601311180b00300c2e03600d141d172008035501000380b40984e1a01d0b00c0100700e45c1a0355179041030b0030b6154420320800c5443c044003c041d0081038155040918221005070105445100040c0c88042c02054800d01c0e804201d00000640002e4004c401a504054207002c15070498843c0c80311480a0400a00d48544421285002d0082031180d0021081080b058003050903440d1800309082d41603c1c8240c0d080804e04640310015114400e1640641d070010109403c0b48041c0001507104403e068811140040c81c0d40b601481d500c114042c52861190f04212204a811030040c440b000500c1903075a40d1000ca43c0580d80d03c04032102014035001030380d100e8000901b00019591203c0100c0c1e0100040780c40d01c0c1080030503124840410042c044050500c1801000807040d07a0003000340d80d200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 772294802 1250 772293552 772293619
    0x5070f090c0c03121e0905070611060606090d080324010f091205010207150219050a170402030708071e060302040602030409091a010303020a12020615090c0c0d08040c0f060e 76
    0x81c045c3c42c40340c00380106400501a80c5034042c3c0304000c01d42ca44070300302e0101025128401062107456810030882164030038025180d100c20144410000500404c024501c6030492100c807607030112030901000010440f0301c0045040101c8480120709480c0c10418080c140d8007510310864040c030852608500921031110003511a080c00d140d007882400c2160010305a0f041e6480c40c03810320b4400880c05880c0c40c056440c68501113620110007410002030b0744890769100740000c003150f254590b00d00d682400e04801d60030000700280d01080d0820304001c03800b01c01d4001c0c103152804501d001d2400c2030003501c9000f41d0203200d100945610302c040a0181c0403102034410812014100c2d96940e481c40c1c003942ea208080d804032a8064004070a240c00350010402c94032451001c0e070701c00309102c812001c11052503002042d1000902e02070262041012041080078020b0300151955202401d2500b031044541e1115402940341e04100b040a110442c1d2028070710721490700070b4450b91400098801e2400d0000140d003044002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 772296052 1250 772294802 772294841
    0x70b0a060803032a0f0d050405070e0916050604030c0b0c030d0c030b0102150f0c1b0703030f090b071205070201020307020d030f180e011208041205070f090c0c0312 72
    0x105000d8682108031802d10364500e01c5451409009215441d0151a6000c8050700e41441052a0f006c0c0b25005940d006100d402515121911445204c00903c0d00740ea2613074031030384041844030040c00c0c0321410101070300081755920b003028036655581c5d18420090240c40b004840206801100c68410010b03118200704842c3c0a202922079401e00070000d010007001140148210250029418141c80200c1e001c1c008100095000b9030720740a10b05069072111500800991006031101c0f007802050002501039482a501e03114614888880206600000e401082d8247d00c104100b000007031380c1541140705140d00b82803103500c07103801f80010307800d502a80e0340c069000344100561504143d800151401300c0112500c070400401d1560001440c40141402801c1704400040018000390810300100c1c401c061062444034581600c0d5203068140c42c440f103204075110ba205c0e182c1884158440c018190180c0003ca008100b0a42840d10042901d900500050180326810f80080c2c03a0500c0c81c0c000385400288842070360b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 772297302 1250 772296052 772296061
    0xe060f130807060513090e1e0309040603050303040201080708150d11220c0e221107051b010e0d02011817031803060105030304090506030304050a060c0203070812070b0a06080303 78
    0x80855102044100199500031001b10700700b00b40b842901000c900d00002407004001c010036400d82d0340041c841d0b164482c4428052502241e9440c000c1401a51048000c0c41d00c90409100150490304007810398001e00591004201c0c0740000d45104040d521400ca03004100c410705420b2805064841e00115500054000c00300ca0f403481507210340c0c9000d110703105020048400301c4841101e0003540985800d40c4200c00500d242104a40141c6040c1c08001120000032400b121a08100304e0781d010074021142e03504000006411940241c80c0f0105c10078003802d01030305000008000500140b80308a001f418840e121554010400c8002c0d0484054610041d403041c0310000620040d41d80e8115009c0304500502d0f02180461a0070081150344c1250340c041c00442c102820120828060000145031036014031007032100140650f140702081004018507210700d0201e050600525090200541003c0f01c298800303020b200b800d1801c40301b1624001c0d001992800651100342c00d01c000360405900c03900541c1320210030311 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 772298552 1250 772297302 772297307
    0x40f080d0b0114040602070905090712030807090608040c031e02060c07050316030305091201020909040c05041a0108070e030a14240c0f070602090d0804090c0e060f13080706 76
    0x80407600402d0700d514849421076101d5103000c1c42680544401a004140100045410758016170b4200749501e003541c0c1c0c2561104036080c2e8400310303420150300091404052100440d04550544088e0045182c807112600e4251262907821407603110081c243e03500c015450207031210b43c4200035003040c0d00818990b5079080b4030400e2581da66160046500c28000c0511540c0001200440d035001ca03a85030321061300b88010041000480c001e5035a11003c555001c00406050b552103c64162103a8842c4400b0380106003030506110450340c544d1342c1a0503040b80c440c1c40a41c81d80c0c01030a5103500460504c2c02144884030200030030308114072080c0c0149541e410368680c002c41c22001c01c182511031000b60f16000300f000d501002c205051300c1920b445103011020040140e00d4440c02c0014500d06015035070140c41c142c0c01c8800305d80001842102669000c0010030b060040b40800d014a0482e41968500301b11080c0d58000058028424092020701c403034070000c2e440100b500d104550400034180c80d0103484c03905035100da02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 772299802 1250 772298552 772298561
    0x3070c15030c03020c0601090b010903170301230d0204020912010203040c030611211b03100501090b1305040e01110c0319081504110c1f140403050304060203040f080d 73
    0x40380080390418a03480c0c4064801d200755210000030038020042a460030700b10710f00410403079031450304201c583d07080400070882d0422400c1c03210a1618009030b5030341c580084410301d01483c00b09070352031803103103e0b0f000400d503550086e40c40d84035011240140d441c036540c40014201400e40c407290005500110400050100f00b0044104490080009000e80d0b00c844011641a00c19044210300007c001507800c1e0080050b00c2025a01030001d40c9a00310340c8810840c080e116070030442c0d181210b402021828009075a1284246c4000c00c0b410540a080644c603201d152201045e074080c2078081c0d82c1e2a41c92020004e001d420900c040c02d0144111341d0354031202d18499440e41e000015281c0c148004403045120b9030700c109551841803003541e00310380d407803503440d003c110223010802c1c1c04485202c002c0c081441e07000b0040c03000050200311262001c0e51004010448000d481c0145000c4505100e01ccc1c04000119030040d01b2030b54420741c8808010303501e6541e40f034a99601181404081c11a40303000c40c8140d81828158070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 772301052 1250 772299802 772299839
    0x2d0501091703040c06050309030702281a0f0d060f031505060906091f090608160f05010906200318040e01052818030203121503120c03070c 61
    0x80e446416110002074003480c0c0b2003524001c00413080700e141007003440e220360051030304011a07000b82c0307140202036000a0010100c240c2c203046c0320015001d00000c185210204140203000409864003607c101911507103190017222417171044c00d400007404031103402d190303030014000e030020f44021110f41c3c0e100d080500002428099000c0f1240c40c0c04085056450f140c400c03036200d00342c020034003802c0b0ba03540303e41c441c5848142d200498020400044c003003221901030007481c01a00107200180040c2100c0c50721070840750b0f42940020300e5108401000c2c03241c0d90780505c0d6503096442504101c01d45119088050404207100080c1c4015070001140d1200030b2a02049665a0400704460a10811940c3d00c241400c0301c034140d8842410112603120714501045001c0b40486081441300700184224984004090715446541d0460058200060420741002c503902003940041e501401d100e9020b600c0c0c4082aa1b4403038410040c00b00041c0494059000e0004104686000c1e5000708802070030b1395590192000400c44a6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 772302158 1106 772301052 772301063
    0x708061246082703060402060c0a080412020a051917010f0216020901060804080901120e030c010606090902070b131115030609011a072d050109 63
    0x2051850080b102d0300c0e95203003007100303180864400300010544040750000707618039a14000b5503580c1c416410746280f40c0e03c000c032100c0ca80c034115150000a09110002401003940c030074040308040703c240f003551a251015200c40c100b0070501c402104001503d01c7c1840304004290ba84031202804003080c500004103d03800c03001001c180d0b44029058052203d07511100c1c400c60a01e65045030040c0010324001c817060900740d4804003e48a0500f060303041051107885080d4800d455403000b0340141804044942e00c01c104c4c04128060031300c0f031288201262a9600c0054035148500803108501c0d840038408010340e440a4180c00c015000e84030541d800c01c04000d100c40d4a4461b84508030980d100c0102c5641c59152040400c40b05002c141c005256285651104070340e150201020349203050307400b181c40961651002107903290f08030051400c1905007e4000a00207002c410341c090010a070244 = true := by decide +kernel

theorem cover : BRFrame.Cov 772122302 772302158 := by
  have h0 := BRFrame.cov_init 772122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 772122302 ≤ n) (h2 : n < 772302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
