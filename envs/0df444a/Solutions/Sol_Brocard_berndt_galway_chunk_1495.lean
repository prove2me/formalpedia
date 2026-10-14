-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:15:21.092225+00:00
-- url     : https://prove2.me/submissions/065e7a6f-463e-4b38-9f31-6927f14335f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 268705035 ≤ n < 268884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 268706285 1250 268705035 268705069
    0x50c01020c130b0d0204110a020d051305041d01090c060210051b07030516081803030702090103060b03030403060615090e0c0d090c0503100f180209060d03032d0605 72
    0x1074810782010a0000f041203005958020400340c82940040c0c5851203060711002c50b5514294607040301e00d40c0203181ca510f00386041e041240038426400c5501c0c10110520540b08101c0c0c020404000080803070f84014861300382d09030b01d0b608007038500c0b052052198408050721103641c20364085110640c80c0038103440040c0e81030401034200c80c44505103c0340840c01390081b5482440c1003480c0503885c04088004580d0004e0555000c840056212461140c82500d03120f50402600a141402c0c03079500003034001981448080d0003681c455a20105d1a0350a004a8000c0c540c014410030074a0f172200b40d040004030100e85400042240010003003400740c0d04000b014420390703c80000b00d280c803668051520242102c8141180c08400104011a0030790702800722019a14014000084100c103080101041c1c030109680305400c810200c0c207000150312110500f582c0b00d80d00395801e40c00d4580340d207412401402140308028281501c1902088100b074026289610703148108418000c40c0e85501c00c204042a408050352 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 268707535 1250 268706285 268706299
    0x11040909050705150415030905030711060904020c06061302040f170a0c0e04110f0f0f030a0b0108150a0b060306010f02010e0f0f07081b09190216050c01020c 69
    0x405085401400034035220740156240c1650300d5003c14203500c3c101c08108096440480e00380303c0e008400d45155802655490180b0003803c90340c58070f9442c0e2003860000780c50a0f545540c107107856180d1504a40400d10050001c654401002d0801521103505849035803083c5002c0c02c0340050410140203071000d645692111641e450304e442c4540c2e10241c400340c4507d03c0d500a50b01c19002091640031000300a103403800108105140503d04200200802c00301f40e40f007012454084502601ca41c404091b0300c03842911009606043e46001900d0b03c50341e158000c0c8240106400454000300120302d240e903d50100c0360401445e01d13164000d2007900d912031182c42c0c100c6d2041c00042d61941c421551050f04081e54000080c0c801340c0408c8150810031400c80180250b4402c072195000c44800300084002010050082c0518803030202c094445501d1101b0380b5482124400f000c80c80e040500c0910300c449540c05902150b0750100024900004948018140d072240504c1e14800059400810404071602004000c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 268708785 1250 268707535 268707539
    0x31903080109200a0c0804030606051002070614090d050d031d010b010c02010c03030216230303090a03270609140306060d03080a0908030a020403170a230918010807091104 75
    0x84072103030400710000c1300300014a14802d01144240e001400603502412020402600b40024000286130f6040c0c09002c5500c426010400550304c0440043c803610454545070751101801d002540b550910003010b030481c0681c48003040100d805034402c4008682c0e40c5ca40c2c41682400d50b440500b01c40580003814041480242907000541c407c6400040e42442400c0050070f150080c0c00034240a602c00c001203801682c06904070050907001074108800100c00002586986028588951075154001c0010184258000d5080e140800e90055801c00c0760b00901001d9110b99402004044951034414585900d0025881c40e1446c04d022407075510a00000e4000d81c0000065038003168a40d00041400040e1541e842009001400c002e0046000300003000e0056111402c50405800002e1401403010100780100510135107140c106102d00d6841c02c40c0400d0210040c850300103c2003c1c451806010b9103c3c200c0c426644001e03201115050588503540102c2d40c46980b6010210120352a4000800c8082c80c00d02003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 268710035 1250 268708785 268708841
    0x40e0c07051c030f05040f021905010e0603060402190e010314040b07180b040b13050a1d0c13090f0b1c0609050c030d0c1e03090303030b010905031903080109 69
    0x4241e03501d4400d15000902074456a400c90448134143e6085420720a07c000460540ca85042c645903151548120504003603d04400a01030142040a0500a020100000d202640e666068a82d0382c5500c8141c2010480c040b04010103402442d05c80901007032a004007611104656000203210f82c2c4e00501d449420f880300401a40c010010101e07100c40c02c4108200800e040c19550f01510040c030070300325642d407107000c81e1005031603001203a00924051100513000700081d00c940c04a00c06841c01015030743c0d000782c444070004240c80c858100400c4100c131a05200158080866000c009032400074401041466596010062200b0380702c24203040500c03030458200040341543d8040300c03c05102e481141c030300031248800b284c1450031a6010802241091045034140b207402c00400140d8564507940780940f40031a600501110f00c603000c0641015a941d071100700702d900030307420309000c2c01004049403d450822080c0d0303078030503006040880010b401d0100000e401c11040c00382055110101548140b43c2541d084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 268711285 1250 268710035 268710073
    0xb0d060e0d231b01060f060207050a0b0a0503060105030712050f01050907090f0506090325030b09010b130b032103071107030c0302060a09031406010504140610030b12010e0102040e0c0705 82
    0x200d03c00c10b55513140000101820020304c028002d040e190080c20303c0c50301c2c0008001e960340c0140c1c40003201c0c2800b000306007403c41d40101201c0c0d1046003400d08944079110b40a0880724004da00e00c0d0b45c448a85450240070b16084c60011541c1210780840325030344a641d812500b00d070302c22450300c20b412040394000d400f8412854424003070f0800c9070001c0c08a5544440b0114000b01082a10050000150030f01d102403080c40106199950710680300030003031085e0006540441c007400131403c41100790f159038904640c1c02e07550520803d540c0307035507050f40f815843e030004140d80c0e6130f98001e540f20b1020444002c0b50314411680403034018201c0f5001003010241516540a00c0300e03541c000b111240c100502900044002040c0310b41c49a401000f000060000d0742c1084140000c89403882001134444036000700300321182c0d5800000e83c004c95254a0b0200c4d03602c1c1c0c540d020450040086421003440d50030300218005121056010f013040318040303445101c45440740d1503402c09510078004094065000a80030b00c0c10304507900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 268712535 1250 268711285 268711327
    0xb0f042010110325060e0a0804060c0f020301051e161710080a0c0603050705070b181f020909101203030203090c060a080f0c13090b0d060e0d23 63
    0x20b0309076841c0000580c0702c50104500da0540b2802c0181c0505214240681031041c26403e801c40c000030114242c00b601c2d07081450003070b846681c041080080c0d002081103900303000c460b0181c0d40540207115030f003030201006505030700b604541844080f140340060702000c05400c1d140a03130740c2c01d91903000c894203c00120412000700106004a5a00480400038030402c08020303900b10303a13004003003010300d250412100405568026103500d08102082c80800f020074100c0c0d00c25034011642e03c40d00e100c0e29400000a504112004152002400c030b90310400f01d14103001e4000309100c1070112a03203c059680c0e03107848401c11100d40540c1c3d0346401c580b0300c40d100103400395000b140c00241d118115081444103d00242c220390103466020f00040034482800b040c507202d40850b40d08100103c95050500b1203000c1403030034445035071203504e9006884001d0900d058075601c00142c2034581240c0c00b408408410b10502c1cbd41c07a0002c00d051000a14524020300c41a100314110790781c840751010b011031401c4041c3c1620299400c0107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 268713785 1250 268712535 268712567
    0x9090307020a0303020741010c020a060c1106071e0c0803040314010b030c0310231024080708180106030b101a041a070b0f042010 57
    0x402200d005665003016581c02944681d000b4007a4608004400d00c1c4416141e590521055a0700007003000c80003985003205481c40843c90b002416054680100d440e8804084080d4100c001d1400c04034941c3e902401c0540581c1c082c0312201044039a0005000407441202005131590042d00002d11400e0720704c0340e020f410b160140703411044068661702c6660640d80950310803034549450010f4146018001e009a0489540c118081c03e40c4100903000b107a141c402a002c01208260380c1c54942c040484605494650743c009400208114900b05000d40c54101144c09002080c10b00312005d03001081d80c06405180101c80b50380ca041da140c130b40b2441500d0324400a0600c11002c40e010504c1e59140c0780074803540c0004d40c000c8800350034a0424030380034825100c050308048c035458120324480c00ba6100341300032141150070881903c0c0301c440111016100074024071500420b50361500c0d052001004d101c82c0940c3c041c0d03015604560328a5039103002c81500201003100c041d0000f034486a203002884c0038900a00505d008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 268715035 1250 268713785 268713787
    0x50c0c0d0807050105070305190b0d020402130801020403060f0e06041e0305072f0102030a02070b0c19030201020301140406080a020f030f0316330509150705032a09090903 75
    0x429070f80c26082d101c1c2159041e0020b03a4800402007034000c58804e00d9041454004100250721140c004600e0b030000302c6002a0143d6000611412000742c4095100c2c002d00e6404000c54a854a82c036199010749080d00510b00181c0c1000203003003500d60f0100d052406241d10140d08144c0648104145030394403445a4142c00b400400d00c00f25010504c0b10300d889905004402070078441d16002c0554100314619050840e04550080c49a00d4219800040030300917140c58038102e689a11400e4051842c1210011098204900c0d0540090400d03030150017a505071103420040300c80c18180070050000b00e07040b40c4200c080c15413116108402500b81348104450240014003511401400a041030749594003031607100003804d40074074401080c426401008664901c49010b0b4100403404c8d200c2e210011003c40e001901c189a13104041101c0701000c01058101c4050700350084094688820b0280440d0030481d2420401c0900303040140c1a00d600c1d194941d102e41c00b1000450805410300207201003082c00505000a601c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 268716285 1250 268715035 268715047
    0x20a0204050a0509060a1b0305060301092a09051003120311130303030614010206070f0c020d06050f060411030129040b0a0f030c140702060d0e030903070501050c0c0d08 74
    0x165030041d00e2080440301d8022500b030030145a141d281c07100040203006043c1c50a0303100e065030168404011104c03911840c003c145a03c03950002401000e809100905020039143d05049a00564501a5010380c24245072880c4640d40d00e81441901c0044803e220b40851407841440011895541540c80128618001420844040448140d60b0105d00140c150310300301c1e4410020142d06001c0c500150148558460300c01c9001c900103551038602a01d00c0090211580120308a00d03c41e00c031080c40d0a80061002c001c2210608020740103007010754520031721915041c005000c90a10b80500710b0490304400f0381502d560301e0203002c4580f202c400581c0b0200c0c6030174402e400e502482001301074400f41144001050b92040801070180100b00841412010316080141101840703410071000c421030801c91000d140d551080d480001c0480c86240019031055103410186c1381c00c0b18002001e0104214150212580710b91203a0040d6181d0052210208030355010b0010202ca40c00d10103441218a449400e910341041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 268717535 1250 268716285 268716289
    0x115090f0e0109080919050922050a0b01090e03160818031005062407020409060902030604050c030706020102040b030c0a050702030f0a0c120b07140c01060e250903060b01020a02 78
    0x85286505680c80c84c2c012801c1e12862503c100591002141142206c14880c540380201d014050006c0c168140500ca941d5032100210403113407450600d5a004050b07443c0880e4074a4842855102801507480380c604c3e00092002e070400c00000c07145540c0c40407404400d05a0f00d981c80c0941503000110388040000b0340d8500c0749a0703440c20040362460280400d0086254a008418400400c0b4810b500c1260712440265001e9200c1149007240c08458050b036000c5026981d904220024040c1c030980290148180010003092200200f0005526142101a50b425a43d0b40404a090b0b008501913140102000c00208941d0300d1f61400404045045060250608125030006410820034800394401034000c00c0124007007000014130740000d0000080901a003030500d071517043c040d100050400090000c4911580c48800684050328040d49015000744522a200c03101142c0340c1c801a981002c040301c0c000c030042d081d2a00004a10280f0780240d07507410000f4170f10348484024008016002c0c0c150301070004210090303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 268718785 1250 268717535 268717541
    0x7060e0f0d0801080f030301061403271e03030c0405120705040608030a0f1b06050402010e1c020301050a0608121c020412120c08031807150807080106020115090f0e01 73
    0x8900e0710381c00002d40c0f4010055042171070b8402c9403140e50300204010300c05660081015000e44090880071500c0759521024414000162103600307140900020200c06090300010380b206282c0c180704c1c05004280c1c11813507015640d00090718910107038101031109000b00d0600f50310008008662008484c0b18a40d2000072404540040d04039840c59000061208106900407000450011143c90402c0303070303210404030b00c0d000741d0380c01c1e03030000c0107503807148013040c19a80b24603110400c410300203101d024420304084806c0300c4109004001ca0295080200040c24140c051050600b1503c1c000c025100b030700035070201c040c4c0ca544002c11003450038003a031080404004161000c0c3c0042c24600744410504802130902c0c00c1c5d0191480c21900130400d8801d014400550740000f41e0f07030019003011042065000070a10b6608021440c0c103c880c10910100c40090301d2a480380010380030b000303140c40f0b0100e61b0342ca0300ca04a0995031003260340e62030f409200300104a566000e90025074039950102c000280140388162a60039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268720035 1250 268718785 268718803
    0xc0d020702060d091703010e01061d030106180b0d050705011115160e06031005040b030a0b09011406090106020a0807020402071410050705181302070203030318100606020307060e0f 79
    0x3c080e0741c4400d4802001081e885040f051008140d455045601d02240c03802a42c3e014054103007044042c440e02e14266841034905458444010000d005541d2200000d0342c481e08111042180705080a94101580c100300d00700000050b00400506019424500151800082e00342001a01d1056803901e081c00d110751082c03240501418542454144c12401d8020035211002c4200c40c0304103070400500c200001440d00c0807048541c103940202e203a20030440000d0916400d5203024141400d8001084561181980040b6800349004490505902c540d070a21002c1b4000f4001d00e40541e014141c0400072540003000f030603005100500152909265556000120740d40c05490807182d0301c11840e03851094123a009160380140141350290070001e030b41d50740400074140811018055891800c001070303158034035011284201c2e00074003203e42c0d90421040c0c0342c0034074440544048003406981d810f580404810301a80307040300c0d8660300a41c1440c103540c070784a00038405200307500801e00c40c2502c7d850f417455040c00a094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268721285 1250 268720035 268720057
    0x1415040306090b060f011b02130c030501051c120e0d06110d05090606011b0507090236131a040509030c010b04060b0a05030406060b032503140c0d02070206 68
    0x100c0a00503d020a0482000b0380814450518243d03480034599000e42546000d2419100409840250740045410401440c60128101d41000200300c3c800c3e4040d003105048942c151291b164421030100d4410782010064401003c0e03514000c0100d03109481032000c04c0c2d4000c0010a0750b05003020658a15080340e070315418000002c04c1c082002c1807601c2861141540c00000080034101614000380004d0035036000180144810140102c82c0052041c10070420002c3c1c10104002c42d9684103280c9100b00c41300d8400300000407000c1400405d00078070300c034003a281c1d001c81e0003400c0300303850f103c1c03100d41d0201404c02003020039158805050340050f01e40d06c9000e4140034a040c07a01075561b40c195040b03540c2c00d66000c003845038000d500b440c1e400c000140090b000c4492502036890890f460b921140341c480082d080550281040510100c00c6c8481038800c011988490078074518000c3d02c3c0780f070105050b010f1303c09900c003419642d030705000043d661821080040000b010f151000510300041d590015041d500f18040c076103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268722535 1250 268721285 268721291
    0x4050301020a26010f0902071a0702011d030a02190303090501050c090a120c090908190207050907021b0f03031e04050414041203090f2102010506010908071415040306 73
    0x81804200f044004101040740a80341038198100b4482203440521882440081e5500140c0c520070b102c50020703950340700075002c5c6001050f8102000028060320070360040c0b82081040740d0b280b8496a01c0001140c400c088150060201e070400840b07507030a1101801000e405040c3c603244030b180040c2c2d081c0315084c89101c2c9010010f40b61007042c014001020f410760091503240c0c0c081c00081010400d00d0f4481c0d030407940e48040106001300300345445007090151001c50f200714004900c2c00c2c441d642d00400d0803000d46406230313901d60792540d034410201c1e0307a6840310782600103c116980120140382401d01c20200d4055000d01140d182404006804100c502e000a040305030f0b4001240500851070325014617003080c0382c1c50409601c241015225071001c105030f844003000f456524000c03041080601e5030340c3d0b08002c3e0170a00da003c21500c0c0c101030300d58210078440a00015440d05002460542c02a0408825110010001c10b4643d003024550300e80c8210203401c00e603111414284442d04120181d0041010f14401c803004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268723785 1250 268722535 268722557
    0xf041e15050709081002070c0b0403050303061c021f050c030f0c070e0f07080402030c090702010903030c02070807050d06150b041406030c0f0d06051f110303040201020706080a0204050301020a 84
    0xc28111900601a1820030402c0002007104000c0020070106900d282d1100507130700c1055140c5503034048015070001441c41c0c4045000014850040040c0d48125000d43d01c000051642040c5d400c0c0743e0790300c0c6030000c3d80400010000040d9101120b1309805858181c1007003440c0144581c00c142c40d5801c08801c501e040c0c10000380640b0800018808000204030b1681d03001c2a41c140310600d502d11640c024800c60400140000090a40d40c00b007141c90f1010303c01a10b105014107051100034068040c84d582a00803908120700d041006200242210841e0500d00c0a4003083e4240b00c100000e003c80d1001c00d480080d150b622800001c3e02e01100000140382c8403c0c10380c0e64034944900f18000506003800b0911500d400d00c01c01a00d13401000885041c00b40c40e0740c8103a9500944801e00c07000341025004250055411146102c1c14071344100d4041000c8615196071a040044481e100d0b50303807004880080c01a0041c01080003001d0085281e60f810540408000d400c00b034961011900726041030707a14000141c11170040f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268725035 1250 268723785 268723823
    0x30b04061a130606120c020303061302071a0402190602031803010605090f010e10050603011205190303020306120606100806031e061902070f02060f09150406030b180f041e 75
    0xc0c000703200e580600c01c6c441440c070303401d004e900c03030100a115900540903035011310340310b090a40c1225003056114580c05000741d9040050610703c0d030100c071b04a005440740610041c41c02075020000301182c05e507138000d52814140030000c0e4100d0228030f14254141d03407107140c045425070750104440e00c1080103000c0034020350701d010068030580d540601440d2901a1211042c081900c03120200c0707044d2070687c09900101070551800300d18240c0c81d9a240078104107418880010150300d5002540251812110080070300c42109501da103581c0255000f641c401903000c80300790094003a00381c00c0c0d8841c030010141c804014807400381c01c0040c04000b121550070780100d4100b12900300704a503041d119401c12441141800e04035914001d0040005101a105110114020360441c00420442c0d02031740300a0452040d043c00c88042600a4009006403c04030341014459042c1d4100781e03121501901c0e440300102c2c11901d0b1940b1965803080081c1043d117034812880400b1004100c440ca41140c118800d182c40708181101c241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268726285 1250 268725035 268725047
    0xf02031e0601030f0201170708012402031b03040b040b07061d1f021b2803120b0a21020a080706020a031d040905030c010b0604030b04061a130606 64
    0x9200d4000d42564001991012800144181500d078003c00c03e4160049900058480c12545040710030402c400c641085007540c2d105240381d04a400c6801c50038100030b500c600010803814002c80e0030005a1080c4608a0b0303690640184414442940741a0781c90107032111080c0c50700354000e0b0000e40c03c00000081d94000c00205126a00d60382c07007182640449000e50101701c607101c0841d03054001981c640394164103e0319009034100c0b50260802408143c54900201d402511407078040c00381c1400c3c0f5140c90007186003d580000e50521250b05603900c482189071801504014146200d2090300002c8044000c10f005034445950b1a5500c0b5000300c103800b40d4000d1040000f03d60f42c5030481d1003a608201801c101d42a00000c1e10341c00258141040b4010018140b00c0c14012503a0801c52a03000d4100314246c2c040c01000b000404581450360000d00c074101100080c040c40d44290b05c8020300083c844800100800c4680c1d0289600c41e004581400314040c0d44000201030010203040ca50b5140e03511401082081d40200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268727535 1250 268726285 268726303
    0x5061219060e0c07050115270b030d11030904021c0e0f1c020f10051f08330906010503150903040e130501020720011b0615050306040f0203 61
    0x303001408100e003480d80c0c5414088010700821148003001c0361000c20003a0a400c105820144544145410765031340314104c8800340c005400d000c500482c0c0040803120b550038021400c009030058010900c40280f610110b40e501c810303120140c154082804000f8155030313070380028141e000704004001890080c924440048910045078820507034060503000c5084100428600700300b0f6840750414409883d860000d0313007840442c0f03549404034010f890740301e00c2da910646d02490207407032803481507450030325004910030001c3d071240202000d80d841020805a1100041c1b03c428440c0b01a00c2610450700c41024054841c00c03081cac401c0703149034211030018045800c08106811561910003800c103501e00b0903125143c1c03030703210380d0081d0103a0004620004110485010b00607400e254854003c540d40c8006060445103908101c212201a11502070b140101758420361a14445080c000e0240c01d41d50600c2d078850000300398181d4010081407a601c0000749540e000d11095100e1805400300d0810504140304160400c00d0784 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268728785 1250 268727535 268727581
    0xd05011512090213020f040504050108060405061e0f1905090c0f180103020405040807081303050c01090501050a080a1e0e070f08030315030c1201090201080604051b03040606050612 79
    0xc90b01000f50340c1d91480000061112080141c1e506040180031201c1d1085401481e0414103240000490300743c0094a5842680076400380c0307025403120030b1103400d0707500c082a6036101c0d02095400300381e44684600320303250001c240402d0301401e000600d088005580040340d0800040e00000400c1c50107003030001c1c00341000070301150320b0b03000855415081100604180006401950380d4400501000b00201c01c035038140303130000c51700c50311400d000081e60082c84480c01f08030381034058489e00e0b0b081540145860300076500161030b8503040442e8100111114040105500c2d041078a42054076a086160031610341607000902020070390110404c419403500025a2101451614001c0c0c1084480408001e5039044401e004030b00340d4201e04180080d251540d190a01c41d8042000041c0c143d004005511440d0360354070030b894034000d6a4071142003004403a001c03506007400c624100d84000764000c071500110f50180c803c3d80000740e450340f5140070602c0e07a00000e8000d00d00355046428040d051001c4034400070140c0341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268730035 1250 268728785 268728791
    0x509041104050102100f02071a0411030a0209060603040302070302190614190f0201150b121807120807050708010213080a0210121b031e15050d03050d05011512 70
    0x20b8080001e44e10001c980d800801d0715580c00880400e0200c0d501200d401d9900300103450380d5040d024076880c2d803090007541c3c111212021607000c0015424007040141c20650000d111051076950903041c080c013036000600450850040c1d2038080010303610b4803500305865014461110300380c2d05208026128450854606c001031000b481585032012a40302020300300700c0d040c83c220a403c19031310001e90161000c074070301040c1fa448058010650306181c0c0050211030000004401190300c0d00000d0418402904c080c0c44400d03081040140801441402e4401c803162164952034070702225621901e0500000d0b8105181c66500019003040303038900e41000c040940f00060280502c81c41c10750026a41814444046083c04090b60540e003940180f41e01050a030b54440540c00c509200540004000b0481401d8a00b03940c0c2c0100e11101c0e002c0707001d100703031844d503000e062550201b0390600741005a0071602d02411010480e08101c02c1500c4502401014000c055201164204291100003d441ca10840c0003101e8141d03d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268731285 1250 268730035 268730039
    0xb150a090e010b07082b15120c27021305030f07061d0111010207050d030515030303061c05030c0a1205120708101706040c140d030323070509041104 65
    0xc1910480d80044d902203045031b9100300c0001c24030300c004c1e000180c00516102d00c00444807001500e03004440c40001c100d1590340c10a44400006d0010f140e0b8580203080d800d105036080c070059403000380402c55a42c44031900c1c0c0c82000601510410b99002d46d02460303a5075402d5000700000d04080210581010b940800303490b680342015002002000e0540d1040b040071440f021640b5540d010300281d56101c4110f100035950f40380f20b820070517070301c0080340d0b100c0001034504000694040c03158480e940d1070b03050040c003662a41d1154401c1040e011480100c4001c5038485002140004104000a04942164401500c100007150801000c40d0600004480038882e0400c01d07003440c409c1e01d044641c0d0110540c2842c490075115140203502000d1150000040024a180b0604178504002105403145204800e01c110590721040b00381452204104917541086810074000c0010b40603070000780443c203840082d014031100a402c5510030041c107650358000301d80c0000303e0803581e0070705003e01c041080d1102c03800c3d0b1800f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268732535 1250 268731285 268731299
    0x8070b09040b101b0c0312020a050f070515070204060b2a0c0d02040e0a060c051b07050307060804030c05030403030302090f040b0937020415020a050a0b09010b150a090e01 75
    0x9503000500c000304131004038075010006003942d0301c400f850700b02c545502031541001029689113aa00003d40d02c92044444842249500261000540754007900d141313481603407418403880c42c5d005460304a0740a902e880c808100da0300b0607001385c0350303000c500350045858012020741c14001e01a10f0002e042d0325000895050b415031260034015502c0341d0305503400038541c0e003403200700e6040c581700d403500800781800c000c001c4000c03a61140240c80d61151240d1004e03850b01042d04002e9842070a4480d1a4142e00500c80403c10103010f10081c41e0f000d8013174103007103540044a507a02400c2d82d100f5081180400d078040f0f500000e905003490302c900702107806d54040050380000780004a40040c01402c401146118490503c10380000d505546181d02d081e002400e130001c000c50701d401c003a4001d4000c401031062421103900a052002803254003554021002e0000e401c2280c903118100d210040450100e903486040d03090031510740ca02d010031050031000d24181c130350486080081c40c80742113a0103040001c07010001030100f8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268733785 1250 268732535 268732547
    0x7030f080c0c030a0804081b180601050f0d150501050c1002090d0204050a0501081501061b030509100309060509030a0e062206090e0a051312020708070b09040b10 71
    0x45904500060740310720321107007402d01e050181e11565030103000b0344c0081020029000c000d0710070340b0040c1e4156040640401c0100c14682013401c40503510007410300c0c0c224010b10040d562990002d506241c454503040c8008400001c0e03621107625103243c5540c58503100c80c01c1d070001261102a00c024038001c0d1038504103d482c60b0740e545000c000440610f5000524040301d545038032140c0070075903020b081840980340c496502030042c0070920032582e0070b005680e82c44043e19034a00070103041e6901c0e525100d00403030004104c5680300480040840038030504000c08526079442e01002c0c0120402c660300072907480010b103058811303503101410110280d4030034004243c00c0742c1c0003403030300ca081070b01903a889440e00c030146484002410305543e4003443c1000324402150301c6520002200980c3c0703c0304000500d6858070080001168021194000040040c0c9100000100900054030030380300c05104659904d5298840da03810000c40f0b601400b013402c00040e03000745504050062080020084034445204043e0348006014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268735035 1250 268733785 268733813
    0x8070e0906132306091003110109050604090509010f0e030f1e07140607050315010c0c0e0c0a030b0405010e0105010c0c031a19090804121a0903040312020703 69
    0x8962000d80008a03940c44102120080c402c0b905024001034846a50301062003440d440d40210540901000402c0340c100741507440d0150841207140d0382c07007500c2d58682507050f0035040c03003003410810355a000041559032003001d0b01c00350001e10000911414035145070390845120905422a0b107080001c20f00a01802105907040c0c0c03019505c070315503070b40b244100701020300880000d018144900030a4110a0000030205403600d40d440c1c004840c516111745800307031114002291101e10b50200c0480300c00d10307548a800c1c40806a44560b000106190300c491014202d18000c0350511520500441d6100d191a458007861a40e010292402c100650411103280e842080502820381441980c00110040061224540c40110b8004c4030803035811070f202c43c9040c10094252510407400428a0072501811110300c11484900d03480a030552526185c0542c0c040c40f80d10b008000e481c0506248404040b90340002115486140d142c0301031513035182989050802003001c0b00350302045521801d428000224424442d141d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268736285 1250 268735035 268735039
    0x10b0705030c150702010e3004050a030c080d0519051804060303030b191401111c020a02090c0a020a060c111212090f0601060c111801080601120503031515030403090603060608070e 79
    0x42c900b200f4982d05448d511030b90b071200f43c018445020000510040da401c010943c2c00c498192140c890804208807800c0c02400d00070340084040101c0c01c502e80c0c3c090300007083c2070905243c02c060500e211400290441300f03030750310075804261aa000c000c090315080d010f180f501c09190300090101e0307050519400d54040340c0c2e82c0003410b005070109081c4016004019106000c4505d910180c1340d080d824000945400080404078000d20640c0049800341d8940420b40302092419801011011056152500680030b080c600c0713001d000500c103c000181409108210003107050075070290361402041e11104103402d004051001030f820410749401524004906241111140d1a04d0b0720500603504280c15a01c2801c040194080502101150031880c8a40300904031002c441c2a2191a030780c4080304040d03824100b1000340103401c108001242c03800070031f010005202c00980704a1030308280c141074a8580e84142c43c160041026440b04010040d13143c05280b0241600e1315003001c1900340240007615000343d0b81507581c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268737535 1250 268736285 268736353
    0x606070f0b0c07020d1101030b1f030b0a05131d0c011e031d010b1002120a080a020906041d09010911010305040515010902070b060f09010b0705030c150702010e 70
    0x82c50742c000860a803807000d500200005c803048800c0c0381c204515409414502d02103400d080c44980030346844800700d01e60200a0f8000308120025140440c0104100d5a255a1082040e40c001c59507131102c1244a02d0000300c2507000802c03080324400028001680d401e82c0311745501c84400380000f640d00510044541040c0720040e041c01500010a40c090000651660301040114001281c0710a054200d9000304200355142c08035203e6a40040341c03110410405a100031004200486075a071060038015841606030900608280e000c900041440d03006901004036550024890694075101c6542e1f540c1140055000700186d00b81341d5200d862504511144905066a540c0010180241403014104101c1c2561101c0842d68441c0c3d41c1100a403c40344082d107802d01310b000004c03400e0602000103503441034010b000c100b45070b10704002c98200740e026031422641408184040c400c914420002c807040c502241c11000b00380d241059000342142d182252001c015401100000d0002648241c0100e5078602c0881c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268738785 1250 268737535 268737541
    0x906040302010f1106070801050118030507150e030307030206040b090601050a050603130b0702030a030e0c090604020c0a0807080409050a0b01120e070e19061a04091802180a050606070f0b 82
    0x2504c5a2521004088080c015081004400c2c2d90040c40307541a82c80c00d884400c0120400da481c481004902c0c000100a64094242440600070314803080703070400c58038a003070f4604105280109042d50010001103000d0f80c0040240320800800208032980311751084028862585002c00280d0011100e20446000d0680080850b0744c03071840420482155030000039040d214240003030300960b03075801809008006441c104585a69140115040c4400c44004001e050251603910400c4020f52100c60959a60f00c6013000e144001690341c0d0140414900445c1002c0e16035107002c0e20f840540b000189000003007460800d4600b4960381042400c000b450400900095010100c66014070b48403280e0410000d118491041000b41c004981250302c4030a0002403c2c41080d030350f0000c100003a031152081c0285080140010300003800954480018007103c803000c911441a603401051209108011401180c800b10080041180c01c81c000c00760050415a0030380d20b00340c0c0c02e4407003207038400742e1010003002c1c5045003002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268740035 1250 268738785 268738787
    0x50717151315150e060319140f0f01020414040501060c031103090a1403010b01031806110f04060c0b161d180708090c0108010f0e06121207060f020906040302010f 71
    0x45104071502c1c0c1c5010000400c0191104485224500c41d241c00304440030001307019401e0101da00c81d9a4500c88510110113001580c03983c031303043c0386641201498460410651040401004807031410741141000680d218204003080006044003503099000d1800c0c080100400d41d4048004103c0c65014038007038407201036140c00d890440c4601d211541d803203d801403011410080205d04003003a00310032802000a50940700040d81554040c2e5008928851148042804107586801c283c0c14140041c0c2c605281601844028000740c006810020003c0da900c6100401c01c0481d0581581000d82c1c002c44d2144801079050041c00b40012155107845041c2108200c403d680700c0030304101ca40704038480068141c1c50200402002d0304000c9501240d02e01c1041d0502d086540180000c0381a0350a242102001c1400c15584584101001c3d082d1764001c410301540103c422800c0c490f801c011640351608941d07038003403814240207590550003103100c424410004031078250303142c0d8201c0b01120f41c21300340180d122074102c2c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268741285 1250 268740035 268740053
    0x13030807050c0c0a0b040906050904030507030f120c0809010e06060f04020a030603050106060509130c0210020702010c021305070f0509060d0b03150a050601090b0711120f0a0507171513 81
    0x601c950801c00b0380c4c60219001c0e0f103080150050720302e04201000a035550381c0070010361000607240600403401c100301e00320202e4400d41d40e40e515044e8506068a00c00c880c2040304007201e1081104d040061740031014406401d42c00c1c02011078100481000700094140b07100011046050a0381461055a0026001622a01940000c0021074024001304852552048041c142c2d41c0852942d500c00d400c81c000408443c07c40b4420200c4c000340c0c0d40d00801b441600c0346500002584540400e905200c00e0301d42d001d0040e5101d461459042500e5a00400c031030804101c0940044211482c4009010301400250306907161030055600c0040707c00b0003c113603030541001181c200420740007a003456640a0040001404503a0401d82c01602e007079a41100031652602444e44038055130500500d5844140001542468094451a04141101d0540d44080e900c0e12040d403501d4980d05c4111055049541c04102488503002209281907400c0301410b0b0300c2611514044142c0e4004090b5450104410700600521511700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268742535 1250 268741285 268741303
    0x1170a051203040c1203050a26280c02151b0a020d02120906070f06060801021b24011505070c0b090906040614091902040f0e13030807050c 61
    0x2405840703103040926140e14140d44100e0741075441000610300028850800884030340d5040d0140c0d546c43c1403001300c0380121103008004040c846107400002a031840020006500c600481c40801c0a0b038034400b2058080310040000c15200300311a14069144080f1030300890303803c030b106404130382d81075403566500d601141c0d01c900030b45c0c1503401c0f46000c600100c0f843d4001555240b602030035021606803180303e000c108258818944d0045e0000014080c000005040da003028010030300c2004040394040d1541c8503607089030000c1860107070707007100101c510105a40c14000e80c003e00641d08000d111201c070002c4400040c020612a00c95045505504150424072030b0050b0381c0380e10392044100f550250383d100492081d4108104143c0700b0045000421190304d03051103070008a40c410080d0140c0030340b14000304880348400421410a401c1410350300c0c03203101c91910040010780304e20744076000d150723080000349203441c0c900401d0b2881c1a40400c2da02004240c00c00e0079a5404046454060f40d0740340342c040b800b41884051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268743785 1250 268742535 268742543
    0x1b0207030f081b030d15320603100929010507062a020610290d140106020f030a17040809090c04090c1d0f0117070c031101090b01170a 59
    0xc4403c040d41a84044024010740515560074002c800c00038034254800d481a01ca103c046020241d1400381c0d4510041620350880c141d0503944e000c190100e4003103030060340300701c41c0410f023940480014840d2808030f114061110b9411000002e0081c0c10034181d003800d12103242064140400413a0007401c2108580040b449a1026407a81d101805101180041d400f1400c81030009030080340c001032042da4002201c802260345c460824094240d0010080313044003445102c00035218000c106a484041c4a40a001c066040e2070501c02d1309589002c01c02070070503440d1416000e40b60801c200b044211580300400742c022480312240a0b80549031850000239a11810154503080b0900408009520300c4183c05001207424000080c0401c8800000403648100d0300c0c0f60014040050320500d103c00d041100415001d114107040c440400c110181000011500c00c03070703a200014034242c1103001016400703540f1740e01e01c2e4000e0000340218041e41e41c81c18000c001c140a4102000c01240700c5081402d010000f0700380507500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268745035 1250 268743785 268743817
    0x807060c0908210d24150801060305070c080d0e07180528050604020d0e060708010f030209010b13050d0f02040b010305190905030906043005061306020403021509041b0207030f08 78
    0x16488400030800291002c0c031b404030341d2a100000718103000b4010729100300e13103076580c0100901c2140d0380d00d0313901c0d000940c2c40211107079115004408a101040b41e24064000c030301c0114100c200e101d900105480c2c008003100503000e203909500102c00e04130340142c2c0010852007808030b0386030344400101e0024002c1c00b40340b030300c840e007040811256600c0c003107001d60007613902e503988a600f40c1e02c808a448800c00c00f40b0000f0340291031079004000840c01400078220820030701d400419201e03500c03000100d40345809001902d44035092203400c4e0852900b4422180485028201845907190000741201400b04d070181d9500800d4035186003c0c2001010700c1120304a580c010b0480d5112502c0d03554410151058840c2c001220341c541510848003180100900b52180d0f00000429441c1e8407110a02405400c1200442f5010f03024400480140e03121510036a0b03041803502c003540c079040300703004210a03a41c0000032007001070020b80210200382c5c0d02103114002d594000d00e80c0e840c0312160f8540a421407091107045484412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268746285 1250 268745035 268745039
    0xb0f0318030f161208090c010c0c0510050309010605010309110108040c0b04180e062e080111182b080d09060b18070206130807060c0908210d24 63
    0x2030f10280440d0060191241102503020342c102601c840405031400d42c0c69600c07002c08480550301c0307003403142c02140c0302c3c0c0713001001190341d1000f0807550004030501c10302281c408010041000f10034441c82c8014802481c05000d00d0301541c0f60042c1840482d000395040040c404001400d00981135001e40c010002d822003941d0f52951462410700c0b9001c0f05103489070243c2085100303450f03440c001980c030b402807070200003e00c11b200420700e400416449030728000040070008440024090001e215040303154800f051407a5446d0360003100c440710941940c10f1280f240d00144d24104416050603a240000308000b110f100d4019402d007840e505502902032882041810300d0225000c100094020703d8800c5011340c0c41509001e043d5414a80c14076044640000581c80940040d00703a228012a03040d401e80214006850700480b519203405503698101e481003c240748540400c4107007070130400e071000c00000084031009010003410303a103139030f00c80c2032103100416440b9072a02c4a00c3c1c12a0302c0002c401414903441c540419 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268747535 1250 268746285 268746307
    0x5070c060f330504060b040905041502030a06051c0f03050d152c010308070b07030b03101509020403050319050c0a1109060625050304090c02030705070b0f0318030f 72
    0x3042041c0b0702c0da0b4011541d00014079401c01c3d0007660107480365075084500301f90400308110001c0c88020404d41e6034000d40201101e07241000c1c0300450088607416400714049090006221075806d8040d80007a803060040400c10101d01010044016941e241c070b001c039510803140303102c075015050541d644802c0ca20f01500000d10191600c0f9080c069141840072009100c440403a17015000d1000d20014000100800030400000c010150041e0300074060b0500248040c450390110b40361200001e00601d000d40e032840c224080e5400042c9201c01084600c03000c0d0701c0c1c40c0c119903c698582c001e2890b000305035945c03880c040540500400070b0300c8000c0800d0b07080f20640742d654108030000480c484412070195904c01c01140312803c2100840d50210160588404c260008807641601d02101c800142e03a1800300707000124004000b4020130550081940c011620354185003007040c10b200c00b59001c50207001e0100303c811904540c0c002038950240c60003450424204070340c010340381188a180013040104800080d07010b101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268748785 1250 268747535 268747601
    0xf010804061b09150305010b0f03070c060608030a09080c0109140a081c0305100e07120f020a050a021504020d0212120319150506040909020409050607030b100305070c060f 75
    0x180c00184e0138249000c515002641200c0c4207000b03985095204101a00c0c4180342d140055400c800140b030281048400d80d152241101e280d03401c0610380f80c00000e02085034540c0711070312902a0120700c02a01c1d24a1208001170520041403050280d410700040c2c682032700d9500e0f00c5940005104c43c2e0282d4150041c0b000d11811903503030b800701c0c400110380f406022544003c1071425081c160b5180120344003540d191980f0070380e403009894203171000d060707125030540c480c40d016400500910b05483e25510344540354110301074142041d4020441d5200e450b0010440540d07140c08a1700040e50301580e481c1ea5541d0501d03031050074081c94192006108070000305001c15081c0f500314001c118516aa801c001128401030020948500d80c81050b80c000300a002c14060b0b00d145600c4416a80d1005000150902c490380c6d0b42ca080490481d801d00220b80e031040d0710186400c0002000081c0d5071689020041458031a20152400c03081c001c1c0505031666034961100c98401c00e51209070a144403c03c6882007801d42d06200c101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268750035 1250 268748785 268748789
    0xb0901091e021209070b16032012130e04020904060203060102100204081605040e07090b010201061d220b22050a1b080312061005040e0106051809060f010804061b09 72
    0x9100f4200002410240301040c5c8000c03000314074210b40d2071071f44c503141101c1c61000101d00325061007054500d060b981e0000c2190002c008040034259448810b98a80c0e01126101c81d0f000c1a20450b03034404000059480500c8076600c60f6004000503120303211070380100d1402c40400710310b81080b440010082000d210009140d8020342100c0c50703040545891310309100070b40c0c00010700505180d010203000d020b9411141c1003ca450031040c4000950745aa0b42503011100710803455a15200800b4018484039190101001504030040302c501e4001c90f4990ba0b5903118600b0007441d0941030810484c000d0800802c0c4003001807a107420004680e5800440e00780012007088191252111071002100001c3c540710120030f40300510703034244c40c01036076a403100d0500250348c04078a11102041001c01000c204842140100742c00307880c1d103641e496156509085a00605110104814030444080c4200030b060707562200003019028003031074401c0558803986081710140040c0b00c0074808400c103000034428425809004082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268751285 1250 268750035 268750051
    0x1e0c0c091e070f050318100609020309070603061a030c04050402040603050a0509061e090a0b01080601090e072d051521070207030f08090a0902040501030c030b0901091e0212 76
    0x4071a480e548000e071500f141070000140421401c1c400500c02e00c4645803008000c5180303a060350095050000c000b0211403150b086480201e5022003072012910040160b10702620032800c0130442c56013018520f020041c0c140041041a070030000004400d185401e0075140180005002907484070b4036110040d001d00422149616001d2421000908012001030b0b1a80200c0b085130703800c9000b890201088610078001021050740707119038041140005c00c868005030003414072001a0a90f94108603080058400d180d410026551010f0000e002040607030040a0b1502450704103004400000380c1d0b04070607180e542c3d009a91002040c1000884010040010420000e00c650b01e0140d86400421380841501c0c207850480c01680198411300c00030b4800c030768900c0058040d208050038a00380f08000342d0702c04840c7d041700390400d40210741040380b540c260040d050a15110708090101c2c441c841b02054201d14141b266104290300c03518004c0410a088440041e610100c030010741d91081c241c0740c0a01100c44c2919416 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268752535 1250 268751285 268751341
    0x42319050d03090c060f0c0507081501080604080f09030a0b01030501061809170c0a06111207020f061b070512070c0f0b0307081e100f0501051e0c0c09 66
    0x41690300c01d10854805644c000c004804981c01e2510450754071400508070b4080c80420380040c03000c00ca04008000080001100030701d200a6200116505200180e04c5032140b584400c040c0700c009071600007507508507036070101400d4640d09540300080c034010344048060464810400040240403040d08074600b65445943d08a0107006003044003012038002ca04081c2c03004080c0043c000d00c8130f440300002c025004102e0304a581580d07040d12004210380301ca00c198103852100040c1c041d070743c02084040790340c0941c5500290017034032101094192901d0b001400e001061040344000072454405c001510300080d005011070704e605005010355986544940c2064030001c00d218000540c84400ba6604003e8a10802220713081d5203034820252801c2d90083c206031404241c0101040c212010460f88070701c0780c101078121031041c500d0a9045800800c054114034100081080195070840065016130321400400c00190303900e58606109504102c800c03d0079507481841001070085101001c002d01000c0d64900e601b003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268753785 1250 268752535 268752553
    0x7050d09051b060c030d050406110d0b0907030606020a0209061201021305031507020a0f1109070203090a15090302130b04110a0207120b1909050303161b0b04231905 72
    0x70003e409400c42130b0355954020810a54440b8003900301d1500f10707204400115000d0000c03030f07610079203030412540a84490b40c2c450285101c0d10748001d6250704030103030f030800304821820b020000351112294280640290110004524582c46080360140c06150b844000c6484400840648100c80d600b0f01c1420b1091003810010484034688403102802084107400400e09146940d96011122810400a07183d85080181d50b4000d5101c80d42c40da03200b84070340c1d405140d41e149030303808100f00ca80721900010800c0700701494000441b600b2980800c1a82d40441e0846048a004040c16001e4580001c0c2280c000d801d10580315030340d004400141043d502d60b90241c49030b65841e0111001d40055002000d4004100f01001c5050b030400003201c985039074025080481c045c0d002d910303494038591090b40d40307180391201c40c00039060465110210103d084928407035141d0300003040c0c03601001c04c0c0020340702900c4110400b0b040c94603802c0509008624115010a0354940ba07910f5036900e814a10a400c20f44240c0502006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268755035 1250 268753785 268753789
    0x121805060a0801150c020910170105070f030e010204031a010302030d0e1e0609030d0801090b09040210111c030f0b041e0b0321090301060e1e07050d09051b 68
    0x1611610685a034a0316503c0e86011129441d03084125008801d0019a00c440c0000d44c481100180c82010703015030504459140002180083c03e00080f81d10590349024140111a41d010504680380d20b801d1402080c03600050707440344d00a225950009045000b904500150384000c0c1503440d041768021030a0f00c0a101e250b000690320b0242245450b03a10098160718100d0b2844078841200045501400307450611080c0c0d17020900d00428503010300301040100f00100000040f5018900d075841e01929612244d0400c1d0740441d040c00c52458421040c03107184480340362494010808101c040300000304a42202c83e540c80701800070415050684107107411320035540700c0c900341030080d00c0750310070103600d81585c00000316083c0001b08004280540c0c1030042034120103000010104002d50102c045424507511140f20081508440e00d9922595a0b01014401c010004c245409071a2003116410312002c0141d4801c0411149842050540d05400f481e140e0404180200022107052602d12000800200700620003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268756285 1250 268755035 268755037
    0x30b0303070c12083105030c0f0607060e0307140c010f08060909030903030c340306322a04140604050418150615030203070c12180506 59
    0x78002d862100310541c20072003540040e41c89000140143c1c642030030624002d18500c1103045041101c60040320030a0742c0c803d0301036004280402000704400400b250201d0700082144284075200032442080c0202d010800d00c0843d07000654882c0012068076515031417450984804800b0f200c0c0751280307100e1000107200350f50040460030001055501c4445c07540e603842c801c00c5400b8000a01d1602140001c2c8072440c041d4508001400b0441d1070040504a0340c01ea00c00d44c07038102d4800044600140c0561103031810003140c1d900240058030741025011868a1105e20925110801c6210312a00f110124060b560022402039406000307540c00030b43e02046011514200c03491100c3c0a0340e201161004002c1003158401e0620000c0725294050711590801d950b03400090102e50401c540c2440b0401402c0c24441002400c00703040340c1c001c0c00380000300241418130320742c00001c8001c103903460241940080070a803000c0c001c1045001c0c40e03502807008010461840d07002000d00302c20030280d101071040d050020941c0d2034170300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268757535 1250 268756285 268756297
    0x90207030e0f0d0605011202011403010f0b160c0906031b0803030606090a080a03020303071e0903060203070c060e0106081b0619090803041e1d010509100e01030b07030b0303 76
    0x1e038468070385400503801c001140000000a9a011491074100e00014034240a254001c0509510070407480d82c2500003d0548115100c400001c920104010300c032603604004c03010185c9649140c61030319000504000046410f4045024180408907203000030700800030703002541074a1140314000b41d41c169954500c610170205010342c0c0000d420500012711513007040c0c000340c001d0820090601803410750b511485410607003900000ea0050b0400001c006095401096400c64540c5c5501d400c0742d409280d940040404041d804003d00d081d8000002c602d28502c00c6000c000382c070b80c00c00f0f400c0208000d01c0d50518020b10301845007252074011b24402c984280f046ca0690102c031a00a82040d280141424102c0a0480401140c5060011000380444c4030750f4108042c0000e0030040c00c411403841101d1201c040106860b500c01c1402440240d9004412442c40e0101411a1000c1d98034030280e44030380381800c01001040d00401d0000640800000610816901c9580100c00d40d850030485040b4503030038540c03248981 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268758785 1250 268757535 268757537
    0x30717091309020a1707350d05040e0403270306180807020906010314040803060315091e071a070605130210050c0a0602070f02010e0307141216081609020703 69
    0x740030304000310241040e0100400f00c4800030b850721b4a4a540100d00c040c0a0181a09400b124900d242e280301c15002c00640a01800640100103c014600004009214600070203001c4481000414209401aa52441c1200000c4400201c11211002c0c0340803490062005844030f505040c04406429944003900080e1500090000c0c6414104c0c0c0a010802d60098401810580e98260300451107031407002c02409244078014450b030740c4c1020410135103024511a24ad074041b51590042c030080c2c0d400061144a2966003207241070039000c40c02801030610f09145e214480c10b02010910000d01605040105511840744408010b00d80303c3c503020440301049903600035049452800b941c2e07115401135024006524401d01100c0080e40141ea5a40a982042e48220350081c8d040800104540e0070460418907200d042d070007801c101e860040c080344242541d034801c9014041c4001038549003003040c0481d400d140b00543c0049c0040b0750b01d0341255030320201745280f20418050410b0204600f000d0b40211180c0a0701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268760035 1250 268758785 268758799
    0x4092a0b031506070f020a030f1205030c03060f010e06130f0b09060f0f160c06020607031406010c050f160e1e04021e09010f090b042304030203071709130902 69
    0x40b060010540c480c09003500e445410317100340001030b5100d041000140d071082100500321102882d014042543c11852102403081c02d1080010700d00ca00c9043d40e40c00079086850071a601003800068684445510b8038580040c00021481c094003149400e030ba048480c06d90140580c965070f00c40301a0035004203d845613000f0410001106000c100402030004040c1c18108a4a401b11103404010040c080b583e0444449280950801956405000c030380c0d4013606a043c28400440c2c0080340b6074000c3e000411860520401000e140280102044007112450146080310101c21280c04040b41400e224400c03211a801c10600051444900a48010305405040c03529103060701c9d41e41c00c0003039410103510014281039007194035100b581c0d01c18800500910f09141442c0c0e041c1d0510b602c98040c2c55400040c130740242c1c184060380f10440c01000c41c0c0561210610b081c1207880d12245000c0341940f0410300050040869504144a051408030052001e51402c42e076075068403400c225804203a070312207403002c2d5211038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268761285 1250 268760035 268760071
    0x6030406020304230a0201080901090c05150c120405030c0d0f03050d09060212090106061409120f0a0605161403070c0201030f060603140105060708071104092a0b03 72
    0x80036802454205110b034600c620304640036003040600e00c400e90040714281d0b03c00078041c025541c10041c42030700020000d0081c03080d120f4544900c8010400c510802c0d005400f03510501d2a0441c496041da10082e081d1416503123100c0c280c00c0d09032007982282c0120b9100c1c0c01022702000781480e03d07210b1601c0d2145d0001900e69001d0254030159995084034012440341d6440d0940c010000e4000e00c0104003913150141a2001c50401c140007038211084c03078220600344501640c1c0c4010800c04441501e01b01030003240c215030101d422002c0c5506252b05081c07c0c0c1014441c0d402d902c4100700d015040140b180000102c00702110651a104580c0c00c0c051f0340d1135031582142000890800b6208dc03001120041c018100480e000c0c280c80400421602907500c0f1000290f603600e801e0040d6008184030a00400013202c002c2c0c24644691540059413040e048024050001941d41015985881d0046071455810585030a10301110185400c1c82900c0044029882805004082852644101568001c1500305901c55000d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268762535 1250 268761285 268761293
    0x30102070201020d0e2101020309060105010908070b030901090605040807050f010b090103030f0c1b05030106051e060714060c07150501081b01050417010c1b0201020a060209120106171605060304 85
    0x410705c07201c64124180e92802035498840c8021a820802418001a0b41707250036a0418100b8606030820381c10420110001c01c25251300203070700e9042d51841029690b8a4944070345280c010110248018643c0b800d000030070092212160182409038001c4043c0c48100801003080d07401c9504604510341d0050742d0800510109207d00d030101a49580e07403c0c1440206000c1d100e200a02c030689000d048458a8100240304504007070203488002c00c3c0035125040502d1188040c03002c804460311025000e0440415254280000c07a42c0386072580c00c10710162040d83c18500c540e214a9400b42d20700780c0383c0062a50490407a18401c0c1325aa0480380103001425888944c42404405650301c020003904020302840089400c1c1440e5440241c51512000001940030407400040c060020032002500c44d200702c00e00400151360085013940e509580a480169030b1182000001c9802d0800c5110001641ca4450080f4110a80111100d00c224000d4100d5840caa0102920483c224043c00340a800c8030007400828002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268763785 1250 268762535 268762547
    0x9020f0d090f02041410060203070807082206080402100804051f020d020d050105010f0807020d12060e0412120207080912150408130e011214010e031215030102070201020d 75
    0x11845900941040002d0b6000981650b5040c040c0c101c0e00f220120a02c64800e1106001200502c1140040c60a251032074940759101c1c065014080c00300100050780284012013052640c8004c801111031201c2c80f0b0b1258402881d0f40d00460301240110100c00d1443d400c0c0f1300440310f42c0d100300d61041c004e1810301c940c010301d0389500c801c8032544490703e40c0910410052528078000f9042004041d10002615803420000603c507524558a072001c0c44100018030190075404180900c0405540c00c0c03038482a807422121900900880c0d20680c200f030700600c00d00c010050700034a01c207511140c59942220b0f95000c00c50f000200d2041000c0180604820080f94280b400c0c280301100240039650706413161071075104104041400203c0e400c440503c400180d80b007000044502e90005000400301809070380d070500c00011100e20380040f014080003030340340e0359644900007504582100303009001076035210300312804180c2000c041500c000b02101c8030847c0e02e841034201403007038440d82ca405134001c040c0840d41000c141c0382 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268765035 1250 268763785 268763801
    0x10e070b2517040803090906041107060b0a03060c0206061212180a120f12020d09060509041b18140a0e0901020408030307050c06090a02060417010f05071809020f0d 72
    0x503089003640c02407120850b501401c0101070a00107035543d9040d01c030130404200c200601a910031440c00000c014a40a28404e49901075440000043c0344403050b000a0200e040030b03880105090304050380d4002090740480c2d964095001601c00c0c20300c03003800305880303500c03413208100401452409100c0c01860041030520340700261400b41c0f90a0a80342c840303200a4000403080c0301581c221000700581781c20881e03200c40c0f010103010700b44003a100314001a0700040058800f07106090800001145008241e0313540c0c0c0c003103145c50300100050003081850050242142c0f810702455170f82d10340480700010f48003021000348600c1d100300a2000041c1c0c0d040c0444030041d210b000e010110159424480401c0c560f90070402580550031a0701c07400d441d00c1c100e0788140d00d481c02c000c114440c0c0350000300d5110016250382d0183d80c140c1c1e07852141610007a0400d84054018030601c00d02026881c02d08080c041d040d50425541018411401c0f40420740f16100c15410041e445480701c5c989101004200d40507584645601c48a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268766285 1250 268765035 268765043
    0xb2e081b161209060f08060a0611150411030c010309080a0c0c08030f072003120a05070f0c05040507020d02071e0513060807060c020303070b040318030302010e070b25 73
    0x41807407150b071500810310200100400124503150018440c1c55041200402034241d00d10304505d8030300d48400840c034a07005603c545010b1041c40d126543c00b8900c2442080c85000c0349118200c0b85d441c0034284180c01c0c0040d81c1c01d56002e4007841291205c594800e0140e19071031604045007a1800510040c1154182c0c0d01000640b0079000c040743c0801d16110a10042110b65000030b642620b5036650f083c04241e4014110342041000328500c503601e4181c5000c14102e0f86001507101070380c1c480d0040703841038500d0b1091800060444540b40d8184c1c0030802218103260030b4030701c20b0b5001c20503941ca800e0305983d15000c00300010096404a041041501258801240381d030503000b07410300d80140c0d00e2010911154034144050900c0c3d444910501c0b0641080205200500711460503c0c00b24215030007082d160f2203865005017030301d101500060181401104030007c1600c2007048054815035a00300207009100201c048a07082c0681007000811aa030341050b502211100408030400119200402c008010040c40c201c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268767535 1250 268766285 268766317
    0xa0b01170a05030a0e040b040603020d12110106060809011a0306040b04030909020c06041b0b070b060a1a0309071212030c0311040f180c1e02010b2e081b 67
    0x1c40011020301c043d04104d10540c581030b80404103c4108420b840a00074010300562520904001517030b100070002c0c28594201d0404104807207001c2d000c403060024008000e4056080401c00580c56503c01c12151247c1c1c95100200516038011034480d02c1e031450180b00e250305910040109001c81c4980789500e8005109092010000341d480d500030b0140e8000d1000858a5041801044113200c000c0491005101c100314810b840b540c1400c84e08901d40c058558003400c00a070201c0080c416468514150002c0c007a04a910044054031694108850f130045401c0b01c0180a80600018507644d500455100a40d000c50300400c2000708441c2100188500700350a001c064030380340301c101c002d44824020005071a00385080c21859041a205402040c045034104640301d15001d02000010b50110391443e0303c03062038001048d41c1c40c004000301d002d040219540e0742c4c0700d24160745403040030268208a004000d031100c107100e02d468103c071096800c150211a451450040060b4030a02d40c0e0010004120070088001e0728 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268768785 1250 268767535 268767553
    0x10b0f15030a0e0706030c08090f070b0702060c0601120c080307120507020616080d0c02030f07060e030408010f02090928051003080f04030b06060a050a1407080d09140a0b0117 77
    0xa0384c9445060f0344201c4c007195403401c00d94407269200800603402009a03000f4482020002c10090f40c440e210311031320810b030b40c01142000440da00c150031515081003038000ca40310b6507142c24603500034519503001202d07440d007910000211a400441501c80c2c1c6038000c10500d00c1c9034100c0c4001d445540c0199002c0380d01940422040f41485c0032402450100c6014500340da0b240ca1500041d0b20845811300308040c1958014401e00a149903028120b030380701079004001040c290300b00150585180295003050039554241540c0c8000102075a01a00c0003502c100c900100580f01c0c0207070280c802505208040c501c0e0b0714102c4520129216420050700010340840484038142d403501c0300445034101000b1540b001000041c02c000b440059100359800c604100d80d9240740800309000500b0314480d035145078003131062203074554034201d408500350344c90141c001c400c566491450380c400b1001444071103804c580c044040844441c41c0040003d0007400194401f0380c0b68070607401c101505a102c06041102505841404c1300c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268770035 1250 268768785 268768811
    0x5031207030f0318060903030b06042303120408030315010306060e04050405030f180301060801140a200a030903020d020102160b04020d021207091109130c270602010b0f15030a 77
    0x3013000b00d180075981c005000c000310700c0e004040c0c03421403030160721411080c0014080f88011048608034042c02d040d02441040c40d50001c2818801c0d060501d01c0f0704e01000c980040c003a00c01100a5100310100303a0f40e080b2515401c00150119555405041d0010f030449410b1203480c201a40080c2c2c005024108481c1450019080b0280e1359001c0020b45211110f00b01c00c4035441d003001d000f20070241074150020322003a034001a681e082e4090003070840f80791075114400c10404c40c8003001681410700051007855510861100081c014280c0d111040f0014441d4040100c40a8410f00c251500c041d4030040800300d0f40601c1e180c8030803081010b081640c2c80000b0031030a0b0010380d1105134600d2801c003414043e045251410305550100c80d8002d610005140c01000500501d6030740e8511344403c40325040340091401e84501044503501a03020400c0514100c2c44203001d4542c4030368050340b00300c810503030083c00300401c03000a0104142c61010000d030041e204000c05c800d0f0b421000040c540c02514440300051003650084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268771285 1250 268770035 268770071
    0x103090c080a020901080f0a0b071803080408150c0a050f120a05061503090c010f1707030f0c020307020f0f1c080a090501020604020a05240304110a05031207030f03 72
    0x884000c042c1d00c40b200450441c104104954014044070010380f04065a4180c055220158510010036950240380014407290007841d840c080d8002c00c1034082501500e07490024416032090050103014407800e4603c400c1c4440560082d8410881844205c5c01c000302070070140c420f80c1002801c41191007060240c0303894540340c0d82c6200d115104048000c503284c188181807140146000b00380b102d81c02006c2003042840e031400107804c02520428640b40d000400440d104840084607004a100c4040201041c0501c495040d008000303102c0890104118110990805980d24030543c1c00003900200c20001454680c41c0c03084200510700380c090074036440018880342c03c11241c0700b619421501174501045124005a00c01300310302c080d04081c001841903040c035800180c1003030b00600c100c40c41241d0798103c80b803100a5200100300540d004890342500c134101460854103000d50002c07018019a0261000106031500286584102c80c0311080980f07418001c0e101121034240b115001000d02d42c49114240d22548800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268772535 1250 268771285 268771289
    0x1a07030e150a0e03070305040b0304020a09051306180b0105060304050f03041e150507240e0703060c02030304150c020a0f05010f110309150a14040c1e0b090402090103090c 75
    0x90002e18040105408440394242c440049074070500940e000207801c0003c60b030070794480c0034505849698510000305824050b0b040441114203150900c4801100c505204450500c40c0c181070004600c0390750381401c00450700c05c0c040e04ca06154070040040d428140000c43e042030040c0f040d9130016441c55003c07403543d40294021030820321608840301c81e44141c0c04000c809400d00d44001c4007040040754005040f40600200500b58007004d88201c1b803031006110301290102040803040c007d6201d5030f849117440710420302c000e6407050b0070161f4880b91f55101108813072156602070107510112518001d514024000c6190400c154801c141034072000c180c2000c298186544030714000f051080380354000c8000c0d1035440100540f408018414031140c2980803038031300070748042c14051000070303556401740c0000f40041100217246034801100744000d10112040302000c1e105602c0c40e1202c1c100c111403401801c0ac40c180310326074004105002000c0240b510390020000900149400300d03000300300352940c103810111a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268773785 1250 268772535 268772563
    0xc0f01090b07090b09010e060a0c0204060b040e010f05030d050703030e030316030f05010302011e09050411041715060d150509070513020c0601140105221a071a07030e 73
    0x10741c100455a544200f41c080a4100d1480345402c0440140000c0c0c1b901441f42c641c944a03d0000c00d450401d10b00c50070031041d01980040081c403500343d07a040c000070310782e0250003940900c001c0d040010540007400070341e48044400180041c8803075403031110308030b49036004008101c04054980114003000c8004202442c000d0151981c40313140400114800350444500d45011624039041000410260ba0441209840386801203a07a62040045600898080c101c039081140d00514010302c10030a041c9042c060700035201c054080c1d02c403080b01e000c54550307901085100c2c0ca0349202c0d0300d40003c1c03039401e0080c05000300c9441401504184280000c001d0143c810441d203180840e481034104002610300610f0010040c4094502145040d203403804154803100c0c1401f900d5501040e1806041881c0d2140b01128900b10700b1219aa081554501003444038003180d201b949402410140c4d6101884448000c4900255204000c01c230311441c1051381091000000b44820141641c6080d0102c400c0400e02040d1814811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268775035 1250 268773785 268773803
    0x2060714072301080711060105090a061206060e0601140702240a1707051224060a0503070f08090a030c050c100201050412030621170f2706040b0c0f0109 67
    0xc90300044c6101d0700100395804220b4003856a0651610100c0c98606681d8169116009a6a0300002c1030181402d07034000292001c8900c25441884403036440002135441e0120214101d85030600111341170108080350b01c2c02c03030504110304001407411000320f0040d24002c80c80140460001000000d00340c0061421102040c0481042c812640c041012554000041e00b80a030622a00d00718290391700c900105851080074081c7c0030107500d00940b402072144950000c00c00ba950300e0b11004004e200d45c105030f814402103000300d803101644500825500380718452040080c550300203142c80032121180daa120581b181d029031442880107172214220800610003940002c100780c2020710700f10202103040068501010710b0800240a203031040100c1d505c100c0e400320102240e19503182800115071190500c040a43c1e88000b5405840b100d15001030649200750b0090342179080700b03017001407481c1d5114180e181d610050410082c049445000d01a0034090b00309011240c00c4208410010300316058008161004d040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268776285 1250 268775035 268775099
    0x90e1c080603010b01020303070507020405180703080c07080109020f0607260c061e0103030f12092a05220219021c180b03060d05070e090d020105040206071407 70
    0x2e0902841c4c1c00c90340e0a200840c51031410680003421800703000b000900c269141c0000c60390074008240d010080c805074509076075103281d584c50411900c0e40001e4400b011405540400030729290107218040c5400e40191180f401c0004c1e00d4200700e00f950101130101c40c80b160f8050780642c0c80244e0481c4450343d150045080d0741d60f203440c00603540707407901c01844200200c0800c40c01ca40b01c031100300c0800d41100d030305051822182060311015030b55000c420240382051440d05042d02c091080b0340081081d14000d10003d4002c210b9011240162200940203440d009071101e01c01d43c3c0903500b00700d159211040f280320014104038104140841c03100400b58104d0040c0d0201000d4404400f02052040031004242820061607140c2a030341c40b210001072103020b40c418400700000b151515400c9414042560100584001688a03112071000c2c0303809503045c40715882003074500102c0d10f00500c83c06004079002003009051010300e9941035441e1810031190030581c0601c00d40014100070280c0b1205a00e882c070506211191 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268777535 1250 268776285 268776289
    0x12050405100c111e121e210c130b0a0f080c040302060c060609010b03010e0a09080d020a020601170a08160206070803040b1b0909060f0a050a030c1505090901090e1c0806 74
    0x340d44804c58029007000700b00d02600650b0785221102102402240161603034103c00880b8181124504110a1107d00200300088101c0c070710020070302c2c1d0110541d00d81c003058031414409024040e01c00407201061081c2a07a01015000f2100d859000c0109094546815180c2d4007242c090b410603444180154041c20500c129890b241001c02c1c05454656107480c00d540c034058001036800c2d0098196040740c1c1e510074100050100320002c0b908513134103201040d5502d07170082100a41d40c1800344156914000030356000c030361741d1030041881d101241d0840b00c01810681541c560441000c10b00a049034031000c100101c0c800a9180800b031446503019084441c450320306007554400902c018044207581c40f00400c5000c1f040e589140200d5084402030706d11409a0001c8004600d01440f1504059072107d0120800000c0043d1001801c059840100384c064030720616003000d8401d4016280004e81c001010700040c001c0c40c4082e07105150003541101120444084100030500304a0300508900020380480e040152138 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268778785 1250 268777535 268777543
    0x80319060303200c1005070b16091a091e01140903030a080613050c0406090501020d080a02070311010e030d110406020a02010507060603150b03150609190f020f0a12050405100c111e 79
    0x5803501d51041c460703a0320020000d184401500528036951407101c2c0700c40740c20080d2401d59031514000b0749400c03070840451500d51411024548514000780d1941f4fe0300c040e80c001030056899440c0c010b0011070400380082d030282c0d40058001c01e0550006400e4202882c146032500510b80158542e00315595074505040c0000c00e010b070f164200c1819544910380d0445800c0d441101141c0c000c0340c29000588500351481c1c110760101c003402c0e040f4425802c0c1104107208a4000c4028801c1c419940f904210035105c280c00d41e101c5001c2c611442001d03812000c440c10155000300020a885445000000785c11500c0307507210380c0308040c44058058060b44d03441c041421410104406000c1d9018200103254901e0b206001464201000f080044480700340c140f100d140210b1500507a0210150100a5445003c540268492070f04141c01d445d0001e602c080c841ca40c2e1344c07600d115040c001e540000243c81c1484103202c4000c0030b030041000c0c4e4010004510000344500100b40840c045000030325000603080c805440100703180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268780035 1250 268778785 268778791
    0xc0c0314030105010203040b031807090c2601053105100611100c0306050303040b07031b050a021005071208180c0f040b03010612080319060303200c1005070b 69
    0x1035410400042c40a80e8001007070714121060f0044269480e905c0d5010f6080d5559060030f0704080740309000010507105042c0d00040c0882e04c1d5a03440c0c01440c1d000c04c1121034003010106200345100608c0006014508101221464288080940c40c000f202052031001e040b039080b03000240595541c00501449035124007600004298134a400344049000d10040782e21142826501c0c40364a6030783e50f002d034145000750800d5004050003401d480d2600da0361056404254002c1d0421000200c83c0c4503807074042e0080368500300340190404001d1611300590340c00c1c0620304110004500500209000030320002e80300954070054281e2641d1900c010b07040c00d08080c0040d880900d108040d81e04045a44d0b00b0a89651084401000c0304035008600550b540c40440e006029a400444501c62105400c01c24440403000450040d40800c00040e03800c0380c3d2000303030001c80d42d49002c000c2c00aa10242003001d900e298070f42c0341440507050300648600fa0380d40c1e400111504106195400400d201280036400e202c80300300c0c0198 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268781285 1250 268780035 268780067
    0xe011202011b32010e0f100603080406030c1418040c230f0f13061211030105010c0c0902031e130302030301060c050f1902030c031f020f0d0c0c03 64
    0x100300581e0741c40e440221035545200f04040c220000c03882c420720115a440001c225510300800014403020202d94030396400c249540c0c00b078840c0c40e0071542c0290191141c03100726504a408681040e0030540110090101a1480c1c020015210b0300c400101200b0b00080846001c903417000340030352800700c2c02d01c000c3d0b88490f07580c0d8050002c0364000e000c2c20f108510b80210f9505c505c0707105d65600c1c00c0d82c6200f5502e5014001d011580d180010030f803c000040d20750310354010b880c010b8441e0091012259103080590300c0004014100c01c03c284010003003540640e240d0841d040c815100b14003c40e44400c9284200c0e002103a1140d200f03948070748250004195104400c0c4c000e550700362510160582a24042c0d560710061140e074040051406622040c40360034080070100303081010503074081e0b140c0104590295034506000b80e00c2402803142036040c619000406410208061015110941c070000212000b0740180170501e480110401940c500300701a0f109800e0300ca82d075a00e410b200344091f81001082d46081625240c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268782535 1250 268781285 268781327
    0x212c09060a03170f0c06040c0e090f0709051e0406020a031119210c17160206070f05070506040b010905100e040b040215070c091a0d080702010201060e01120201 70
    0x2202140c0222a40d481003d40ca01d00c003559040c1d00511000e0078410040e03200c1d0503011718024017040045200001c005c8800003e03401105480e00780d82141c0320a0b1460b48050b06a000310400c02030004141c03c00780d440802e0400386070ba400c444502c0300b00481d0f0200e400b02e900d1640000c0d02d0780c01d5609849101240b04070250b901b420320242e90400380c0751003c4032032070703106008041011401c01a40d821610080190201c41403100b03a1003442e0150036400340d030700c00412481030301000603a8003080c0e0798540c245840607401042c00381c0f14403001740c9000b40507500340e104002e81040900c020807010010180a1403040320741344080c4d8076101c103043c100e0b0000380505107882e440c0e19003040080101280183c0090300700c1c08070617440d00e440c400a0241014a040e2590680020402205100408000c1c0e411200c10101c00e01102d0030482d21021620451200a680525102800000f203031000024180359407043c000010303a40d03182d01d907603041c103c4240e012121448911030002e0031035038071054441407200c030310b2042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268783785 1250 268782535 268782539
    0x807020307020a052e050a0807261f080703060e01020304050a031209020901090509010b030705060a03020315040e0307060e060106080606070501090602030703140112212c09060a 78
    0xc042e4100c0b03104451041034000d2800700d4080c807032900d1010700283c1c0c00b1407070544170a41c10041c0064100e880d0004c00f0030f049000003000e65000303080b0030140c9000162181030500140d112045441006025001c86a5061114800703d0741e03400094009070080c14002c0c040c451031b40c50450700b5501e14490b1400182d0051042c0030001d0000605ea000131f540c103090500031a281c102c81c0c40014074060070080c0d03100311500c0000400801c80c0d0700042c020103180c0005d02220883c2c5007411340d142000c2c8500c5800150412850b80b031144254007554000e106442001c0c200a1402c00150540d42d42507184059a0400264502000300602c10072210b88907050251600358501000500581d00042c5428000c1400040c3c46c803c021083d4400d01e4001e911000464507420150030003001030400103207611051031004004107421409403a440041580b050044440044924103114560300c5482d02c0801d10900b00303248058035030140c001c001e031154640c0e0f050040400010030031112880150811b80140d03520f18007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268785035 1250 268783785 268783789
    0x80c03100e0c010c0312090807060f0c020c040b0d05011508070602150105010f020a0b04081305011d010c1406010305030d0f0c0905041e0e0a03090b130302091312030606080702030702 80
    0x80b0148118090030b250445000604080e40c4495001403c940150b01e440a21000c0104550141400d5401480204807004070445070741c085542e000038510150340728894600d098641070b00310030034112024050041c07243c3d036695140d00f541c01d03a09090202049104040c00581c2c01000b41c2002480301c1e200038200c0c010240a01007500e1810b025041c10080c881d10101c00081c02041480c0d06558408100101032900b4200140315070081031140481942901002407558400d000500c5070030314104401d0200301d403400055a200e140074100b118001c4280e0340c1444812000d008840c021070003100556651071004c4c94a1085502a1030b01c030480924100700140a194440303001801e0706d005540000300607c0303c2c44003d1005000c002285031244c00d0802c559018032002c2101e1075810b02c07035190300225540f0783c0392040381805100c0400300c11031a400820005450525001d58001101c41c041169503c09919680c90a1003074a500318003003600c4d0304c810410a070340081ca1550104a5101035400c0c0712450b80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268786285 1250 268785035 268785043
    0xc0e060a0801120f1b050a05060a0909021602030a051b0a08032d0a0507060c0504030206030411010311070305031005011b030e1203040f150801050a121407080c03100e 73
    0xd003c1c10180380014100801900c03d03511a200d941212240d000c69003482c5640d000b1981a016407801a0381030a4005490f0030170405940b04110309461b1a5201da05284100f00250010890880440d800d281203202684040c002007440901860143c0760b000100311b02560508000c3e28003501580b4409410031218102100750303803602a00c8031544001c011541c05109441441c5403409002d10000107581c56015001002010160b1144d402031007101494070b0305a0302401a1b202c041d400c00c42c1000013400244640240000000050600041c9000070f003c40d0681500b000c482100455000800d102451401e9112000200000d207006a14010000740c1303e00c15980040c3c3c01010b1100745407641d24070342d40740d1800154040040381265220f0f40d4856140e0b001d6803070382c85050300b0f50992416020106200303408075070581c1e1000e0b2182411070b20300100d8407440c64908105417000e80001605224404050080030003c04141006041001c0c2c0703c0105401c0042c12109181e24602c1d1103500e6440c204086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268787535 1250 268786285 268786289
    0x60509070801062d0c020310060b04170a120c060f0522020d12081602010908180303130b040807060804320102030f0114031b130b030703060c0e060a0801 67
    0x22600c0d00740030000e0b1486022000c20040c80c04d20311211000300c8a109607000e4141814036000300c0403241400c9842d480c031400c80c0d4940c007507003059500c1000709201c1e40d25182030164108070041c04942c841f007910303102c0c00c140707405550b240c0c1c0005d0451300692050101c1800343c83c6041c0700010080202d402c0c129402280002002c01400742540100130340320079569079200e0b295407146c0019610a205c805900c004100900131604e882004006402e51040d887c8140710f045051070740074083c00c0c549000c90410415404910400c26454070040000030880301c04444110014204640800c0d11141070140c05818a4a1070300a081000b10300410000420032480d60155004080c1c03e002d1b1b009902c02d40c5442d0f010982d49000a80c940c000030502541c2e0280d51001c504a6808e5454003000031420402c254407801d090ad4a180202585282d0489038540615003541000542100260b0400180c000c20700b403216035032007901c00382c2d5241a4a041c0507005203209a00410031103100d490b100102c01c000c0c217059018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268788785 1250 268787535 268787537
    0xf060f0e09151e011119030c111c15090816020f092406091305070203160b01080c09040203190213050a09020f030609100905030d1e06050907080106 65
    0x844045001d5502c0e24115200180010b41840d42102c40701c20201448940c281d4500c0c00034a00b280030700103960001c00c0020004110100402948440382c03800c0b1005002100c0070f485001c14159481829511801e4209096030340f090341404200307250804586201a2a2080013054141003960b000030301007108688040928044c2110045658004150b1045001005641103402482440303000444855005113120708501c09101219209040c40100d001d20505650070078141d00302141d00b07160342c0d001070364445942c0c03040b2410074005250b020307090703089010140c8a0851020040c031102e00c09121f120302c05d02c02582c9224840c10198040b07135540b00400d002e1020803000e203042e0411951031f0528610780d041151f80c14000b03030805991101c028508030700124882c2c0c0305409040501d050200385544a02590409850900e121030011b0024040c0e1804c04c441da0700040001c02050700c4240b0030210860360070310740b03000312075110301106045070502d4225074810032441041100066002d654141500d0007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268790035 1250 268788785 268788799
    0x90504020c0f01110403150c0f03050718120c090c050403080304260405041802131112040b010807080c0607030f05120a2702090103020123040f0f060f0e 67
    0x82800c0841c1030018070780307032020603500b80713a041c4601401890181082d60f0041d60307410701d180c0302404600c04940300078a4000101e00413075040950341c1e0182d400341d0340c04450390403e06107041031311840880c41526038004c13031100541c5102a4003402456040d8101074207041408001480403494098010700541c40000c1c4403500020006003000505104824001d80e04008003104000e000295041078029024240c0a145003101c00742d40428500480b5094540107442c130f60420040e1540c03500030780021320801e40c208508000b852410700c0b0b5880c807503100f01d000c4c4500010550511081c1da09110403030303106072855444503115000d145d46241c1211035482e4503081c8082d482c07902076020307a0540200045842d01003d40d00c2088414802a0010510500041ca810f034800002440b100000318034000080c1d001802071005000550061444007102d01c080c00300c40701200c0c0a48a03c0d031040c0c4c410b0300b110b598007016110400000e22200208006046541020118003d0301c2c18000c0c040100083c0b2117216000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268791285 1250 268790035 268790047
    0x602252102030f0c2a010c021020030403051e060f0604180c05030111040f15030e030412020319120f030f0207030306140607030f0e180702160803030709050402 70
    0x30003041103c0c4100414242c0e140c841090950f916262440004100d000d10b0300e058007400d80c0b079038041c1c0d44248440140c40784c1c0a03d0002c2d400348804074607840100004c0c0608501c2001a0440000c41440340c860740c907000b995100e0840c45d00c181040d441d40701e02c079641900c41003805000f0402013000c4d6807001041d0b44d13460dca5a5030100003800f605000d080c256003c1f08181c1c44c3c1042c4903030a0786c1101a5032080d4000c0c0b00a420406446501c1c3c810740c880e0000e246603ea10a1082030344000c440803051000745000f25011000c0103085003564465400006025502c666250031402c003030003c15003546012101400c03091041d2a98001c5c8813400300c000040080e5051140517142c040d62208805044208017107480d180306241c050014917984c042d2080e4083e0341580c40c00b061030500c049403d96603240d62035143c2180c078128155a4019130204150f480305049612580c00c074580f555040c8942100d9008200810700c0408000340c040301c58000782c010b60030800c2000555500f1000d410210340e800d54005903540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268792535 1250 268791285 268791287
    0x6031009060b0a12120e01020c0d05030723012009010e011206090e100204030507031709040f020d1a03061303020a1e14061303030518060406022521 65
    0x10b08248402d078040075007100403400c594015040c0c16001c0c8034020841d202c0c075110070241d81c0b01c0351240c10310340181c1c481540705e0118202003030560315003889241140c0c02e02a80b03640f0482160381440720180c0480018501141c0920240030f001c21140030a14013080711003801c1d00000003842008959414814001071240240e4031440c4040035106a800d800c000280c0c0702c07200f003400ba00034907080d81d07114820300c0c404425880a40c400c0303404690340900100011072856848500640548510000496048c0080729041c1c175207000b031000000d0b09181c0182c0d90101403100204803515200d0000030b01da02d1400802e21a1400541075400030131000081041a040346070803072a01985039801800c88020040360b040901c201b4203500b1000b4400c0d4070510003c0142c0f41104c0e0384440454901e100c0107603640c0c6a1003c24040c2e48295007100d50708520040400d006d410343c0b4509801501e044400c1a4002400c448800700680000d04131904451001411412a203482105c820450502100b1013a4040c080c0d01079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268793785 1250 268792535 268792541
    0x10f2606031504030207080c09061e030f070b21040c09020c03090315040302070e0f070c0201050403050f15060307060903060b04150305030304020102060a0e030a1206090204090207020a0e0603100906 87
    0x245002200911140b803e440e00030348072603052040e55040e20031060103500903c4c190780954402c032001b0b400041d0003202d40e5900b44a60b8001142140c05014514281c12104020b0012001920a407074009903281c0d085040c2001030603801901e01d021000c0a020301000504060740481140c822131301c00b58542110351201070852003081c1c521a41481042a1032030100b1040500500c82ea0294007a9540c9a030748191a41c42d4840c100e426030614100030300094841400340c01888006801850607a09040c0c0320380e1100e00c0e001023001840c003d0b91060058840b4039201c0740011303502100035405400706c9854481c1c01f4180b9031240c0001825143c503202030324071980700e41e03011001440100603042c01d10350380c9040031070300c95000750f40590040c05881e00050041610780074000540030400c008624200c3d0100b4216000092405207000301900d03058006880101800540050304035040d0050b60b500851040083ca200c0b95400751010300030007410054140d60100b01d0204039a024003000c41c0160440c5050001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268795035 1250 268793785 268793803
    0x201020c0a0e0a0509010207030807140f0a05031803040807211e030f020606090103030806030a14012a020303040b0a0e0d0e030d0305100909050f0318010f260603 71
    0x1c9070000445100c54151240034194040742005070343ca4030180c8509034420660081c000c1401980810070b02ca00c030380c86a02c1d00202328624681000240004442141e20203a5031500041c0003205100c9803031240d110300070786a401d42c0006c1d440c282c98001c030f4075150100c604c03c5072401c00c5010191510004491009265194000030881c003c44403511140c6047d080d89000354001020f4442c186002800010942d00900005000b00c2060f03107180d400310744009e0003d0089802d070143c1100d203000220345001d00941c03940702070008205084031139010a41d44443c0310585408140a007001c031511034002c0308498000d038100d0076800c402d550b400501e0b00500542814242c1c00d115131002598410391014001c01c0c130460031801d90303410901d40304003101070710404c4d5003403144803455507810071545c138042c1e000c0700b4554891002d8801441f0241c101e1400c0d50414082c5d02c1e900c2445801c1c0d1152980c1c490003003103e00005003003058071000c0b002d4406c81d8090b00d640309045002e014101080b00c40c0d40030071404803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268796285 1250 268795035 268795039
    0x170f2208060712062409060305060a0b0a03021306031e05010312050c0f0f0d03050906040c0501080a0b18040c08030307120903050910090f05040b151305120610091a09040201020c 78
    0x144216100c4c00c9101c1c1c501700c04201d500061541802050441c403038007504d0302503c002024100018200f59240038154007000340c600505600f005451082440c152400c4001c24894400044021008120380d07030882c045040410213500d03000052001640c80200b0040d41d06181c80d217a41c6601390340d90005d1401e00b41c00d000e503110340720340000c48015580009000e1410052550284031913102d40d130701d8070342d25031080d40c006122a60890090100b94868648076a019070120000700d940e2000c6070208002850000d00700300c0c001c4140301004107011410324550b00a02d0341800951a528219100500040c3c062004422864a9020104c1031520074400d403001494010150200f6960068024208482511440804c6c442032203000440340780900c41c03d000e8143c0034040360792495415181120075440700d1446890009442070101d0b00c6e031210514a00c1c002c4c028801801e242c1810080c43c0c16080303607580020040386c200002c07100c2030040c050000510321425901501c807a1500c0c8010b0b0b00b0100d020207419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268797535 1250 268796285 268796309
    0x11203111b031b0d03030c091211120c1f02031b010e07141507060f020705030310081f020a0905090a06060305090606090f04170f220806071206 63
    0x1081000e04141028001d4404900300c40c100d141080c1d4954007040342c4104950300903030300b00860b00846d000f60005c948105c040d00d0310300e22007a20b45e01e0800c0303803044030301c400c2d2020106622600f0342810301c615001214030f00312001300740c500c2a00e80040c94058140c06070ba58070414540c100440b0390700800c1543d04480100304840d014295101419000740548040d0b0303641c0b4170411000296040310740202c622040c2c40a40b40b88030f42051241400c00344d61011008441c0c042d03951607104100202840a032581c1d51140c400b450340da042c000f22050541c44203030800030707264002c2c4c03403006c664840324012000b564003540310150b01c0f409203481c1a503403000c195001a400000345400c00c090b074441a030204060740d6a5813000c2100740c42c0c0f416480e40c0e5940444000f90803000800110f094004892240c2e580144265101001c0e0220301104060540101e44015070030440030444c01310b085c50700d6100c0070301984c0d0315030708200080c50050340c5580d030403002d0030100c180403104034040781e03070400350b00058003411083c8440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268798785 1250 268797535 268797553
    0x507050d080f060108071d0a0806010e0103210c0f02180702101a0a052101020d050406060602030c25050d12140309030f0906121501030e011401120311 66
    0x1d030a400003261508103044494000540640c0a0800c0c107004050540d04e00c4004403044260859184a816079180e012080b010000750f4510100308035030107015002c50310b14070307940b41d440c001500040501c40c01d94050303081060350091039806a503d08249800036500d038040c841078004030b240c40049222050501202d04100605903400040000c80c00c2200e0004020104e0030814010801800e14081d030f6205442c0c820410a034a051100e400303c008190b46102d07021968028000d003280e00000c06008843d0b1248200000d004140c4207071700040c145070002e10724040805690f0f64880001c1100d07540c0c030001d403080881e204030303081d0113580c013a11000e0130448020b240790414182c00405050f18800040c907200c11110840c1124041c5c0e4094420200110306000300740703000c00f043d90848000160411000d000080400156600340c03401852943c5c0350600d42d2041c00c0004090340c2d03000d03400920983c10010500c007081e0440e101c1904403180d041d240070001e4803600d01180d40305503114070241d140c411a050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268800035 1250 268798785 268798787
    0x130906051501030b010c080309070e15010207090b0d03080c0c07090b0910211b1502010501080c0a120c2c07080c030a1a0433030816030507050d 63
    0x110034011440200031500401d41c0500440903240d5120915001600110700c500014000101a6400061703e81c151540b827a01e036401251008011110700b850240004c1404099580500014014004454041c0074511220002c15045801c00500a08104108002a00381e08141c81652030078801030045e00e96581e0760b0700b411405007481104541c461030701a00401c03034401e402c10b5038104446c9803a0042e81079004082d211021360f18003980903201c0b03100700503070301180b012505803c60184c9041c50000c4504100751800070300b140c43c16040800240d009a59101c020740d156030341e03c0203c0302e0012544c4d181c000b40e45440c0c95115180e90204402d190603038129920640c0042401d000c80502d00b07846640c664900d03000f116046410f982603000c004080000c07410040d0640c002e40c85501c41800f102c041d00e541c610201d0304071858507444201608862000b10340707000b0b0b500b02c18441e20f004208250815811601d41c41001d20580d540300e1517502c500d004803810580a03d095408440c0c00c401030343c00b40841a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268801285 1250 268800035 268800041
    0x73513180e06071d0904020d08070c120c0816061d040605090c071208040b04060203180616180f0b130b12040308011707060e01021006031115120c030402130906 70
    0x43c00003094030403d00c03840d84c03420001302007403280c1d40045c184d0b0348180c03850304c920307549a020b6941681c5542c10940081001400350180c000c6840c81840ea103410b139441c0ca08c1881c140842e070a446c0c40100301801c03082080c281d20411400d0a410011141482101c95070300180040c203141d4803031074100840c1c2040050a04195000d4401c00f40215944400c1d42207011085920141c2110010304000d0740d0008200841e040e80d0103142d004488803404c0b0203404102c01c0c1945001c4084a500d030108880c8054440c5041c4d000468a1011000104201142c0e09041002030340e14003034000c0c10b0780490085441d01c45c180c05074102c1401010f90b00c2449613900b40c22551495161011281600800c03040000001c1c810348111081c044c800c0c1100103414501d0130540200e56805498850904500c21001f101c0c030080100e200301c400541c03107103208682c810561800c1c0441c07022031200348400f4030001e003d542052405600d040303601c0305000600c40e40c1c075511440083c030044401e54821403da480d010315207040000b598 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268802535 1250 268801285 268801307
    0x90c0905010305010c090803303408060d0320070302010306050a0b030411040e0d020f0d0f020715050403060c050309070902090a0b0d02073513180e0607 67
    0xf000a120034285080240c400d0480362181d400f051b4020401810040140c00301c075281d00240c00c04034954064442220741e504001a40d11002a1a5503200b180e034000840905413840928140f1104089200c5100549480c600030405030140c03c1403520b000c03c061007040d003100850320100d034184030080710400a0350b8981303250100328042842c0110109452403d0307941803040f640750b01a030310b240d40c1d0386940314204010750100054100307490326900782d00c0c1c10090002c1b100c03002d40d07540140050096841102e2401256058003001e00c58003141544015a000c51b13540169001c44c40e40c2c484290040f0700460b0984215480540028a040c88013802e40c2e60020040d40201800c00c100c2c0c030b8140d1140d0581c0c00b24030410300ca050b4000c8035018104070400b480e4015004d4101c03c3c250040c10701020345c94103861001a1241e4500f88401c0e0010310f000c22924903462114026003412140c10486000600c40013200c003030042c0400c1130380030208412501c05680042e04092500720941e111820b150101500c008902 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268803785 1250 268802535 268802543
    0x609090103080a260103020d0203010b04060902090f1f05160c090507120608031b10020315270402040b06070c0b040501320304020a0b1c140417090103090c09050103 72
    0x4100328500281140e1300410300d0403889144142da0b440c0d90b0810440c1c488900e0704030703015521103d205816645030720408004102a0384056610714500d030821550f0342c01d9003180c1d40714000c42c0d42010302400e110580310006203001d090641d500e29542e004e00709890381c0154001c1c0320b1048c900000c250410513230050340c012815600d8028000d40d640c144001038a446001301e5180d0740c0203104103190500c0e0720030f5910040c0c000b03c0684840703002d41c2101406981c070880300007040c0e135000c125220355420503081039000d00c244a510003038180360841e00100e2040e400b41010b403145468100030340090350380c607088800042d800605008015500c2011139919042441080e0200d15036050140c0384e10041400c0c0072410707000d4002d04245001d6182c1c03507082c42d040580181e8005200090110f045051364008008868010074980c4210500b03407a00e074141d40d4210f1100f0f021102c142e050100240510f42d00d006014003560074240c0759080400100e00030201190301400f440304d0303581c0002d84d016550380210705803402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268805035 1250 268803785 268803797
    0xb0a030f06080f1002180d05070f05062d0f0d0c020d050715020d020c03161106120a0507020c030717150403080c09010c1205031008010507020a03050304020609090103080a 75
    0x240703501143e2140140c802002e1190040c0c07545541440003580101180e5101c3c003d040c010b9440b4a02103103046951074001c44a5900961040c8044000000540c006000c119001841e20310480b4015070760001101960140c05440c1d00d900704280210070a460507481050030b00c41d2100c0070f0001290151102c20380d800c01500600c10700303101e218425402c0343c1040d608004666680c10185500034002d42c0b042800c006050f0f82440f030095403050510060030301800440c520900e5a4050401000800010180d144540380400002003039020381e400a5910502c107000019060303403080000d0303082c08a859429941409204004900501ba180b5081002202c41040300d00300c40a000000e40480b00076540a0b0100c0c08000000382c8102c0d40310000d2801c1d007410703d008064100c0f5599001035032005400040041000442000100240f0707010110060059400a104500307000a000c0e40b18039011801904006e0004002019034413501d04690601c0c0018045c3c1c20303603603583d04201c07060707030044e154000000d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268806285 1250 268805035 268805039
    0x30a0b0306060607080711030a0b07030b0f150a090e090f0106090b010507140703060603080a0e032e1e060602060709030c26060a020316020109050a0803100b0a030f06 73
    0x1000500284565400b41007a49000d0950b102c80013140c1050740c0c200d40c7d54010002e4944562014406065200d2161a20403000e0602401c090300342e81c91001e42034010016000d2807240e80c3d403100380d412044120195130964a00d200ca8040301c0e8010140c0140e8030300c001d4030003805545400040c0c0c40000480c2c05008106c1d15858254900c2031b60017104c452030003d01c060000300c002c06d01d044d04034220040c003581203d226650369918502070b0340c600c2d8030603120500c001c039403101c8040c3c00030308a201000f812801b03810340c02d00d1442522980350901a00da110301c030304180c0381c40003580c26030702044401380c00811880781102c00c0010800a00321074041e41005026600c080350040c0d002d441803805882d4030040d0955194101240c10851108041c2d81d02c80d101049484d0010a1100b44421070148964040c09139607880c0070f42d0110514041c0754007441c1103a00d001e0104010071808120500002e9110302c0c141d40d41d480e1180052902c800315001804603410005e030b103140385901503000e901051410035003840719035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268807535 1250 268806285 268806289
    0x11040c05031005150c060406021e1908100f14210606011b2a05010c05120a020c150301090b0a15141306080a0f110417070e040602030a0b 60
    0x1000680d45442940309010b000e000030300d01140004104a440140141080401c08032640380000c2910195070f055400600076034020311090751410031040c5200324901c0e01d2108126846070401480c10481005000701c0820b5205541031500e000034210a0803a00707002c2c2d01d032040b00720301c42e900032100c0384a21210416040319600314800041c07200c9143d4050076448d80c0710030056a41c2803580d4100c0c0542c44a0000090020b00b6034007407a1100034641541a101d0328880c80702d000480c0c00b40d00300c107041c40b4503c18124005000044c00d00b203030f003500d142d84540f00ca060740d0043e8a45004186c100380d004101d042a21002c40014016504031542a130050244107480300c14824624028092800031410a0f51b00c1c11407140a0b9507020347c80540344040034580b0700f560543d602c41402d17540003000018240c1003480618900ca0040b51003189003d8400c002d020203480315410b080c13180740b2403003030f9040140f035003140c43c00700034041c210080001000c2c0c5580d0b071a040c234203500254130858241001501d00b0404103058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268808785 1250 268807535 268807537
    0x6050a060812070f0809040203090c1011191106031e13030e0603060f03070b0a11011b081801060b040312020601030314160f050109031101090f1709040911040c05 71
    0x300c1a603118a00481c5403500500f080c00504c0c1603402050421144115840d603200451040c1c402801406d4507000d400c0401c40b0403400050580208040d80c01c60401c002c902042c2d4103000785222140e100740d4a40742c60304031403000380b1a14443d406a0080204a2141c1e002911425075032655511503007581d81d000201110501111000390010f40c075000e00c07104a050950056070400002040c03c003c0e4008100000d24000d0140c0003850208000308000d000950080203c0710b0404989009201d000051018045801704105981b07080141703020110380c010304200e010240180c40c04000b0f00a19441c0ca40380c00c0c540d0302074031045074006114600c3c800713024800b084050590b58140c1e91340948401c03005001507544c00070000c200700700d545020058009004a810044490301c51000850300d850241005400800300c031701e551006905001c03070880000c2144810402d02d0764810480d200d0b810340502c03001154020340e284030b03412900d460190014092034081045070050108e500f400300d00d100740c00132581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268810035 1250 268808785 268808803
    0x6050a020307111c050102090102011805060a051f06080601090602061b0f040503071517040b160e030105130b0a020a0207030809010e10111006050918071206050a0608 73
    0x40e001031001d000080c40400a01c509418001c041110411251131041e1984464036001c440c0b40e94000345841c0b8030358083c00ba2400c0001c1e4183e0790b011038802da032070300e41c2ca90600030b00c200d00e03580d52400010580003084000c2d10f5402030342c0c00400e000d07d4449001030440354064441038046112020001080e920000c1e502d4403c00962048108810304e8103150034031038004040400060301e00b40800305154400b04605401001000b04800c0c0d0f0040c050740c0070300b40002c500d1984250000200c2040046688072400c6034110443c50501c00307142e54401012554403141442440d415424035017403115481100c01c405246030b005604001043c0c440340507813812480740381200790268100040c20008503d85201400b030400c010305144000050600010300c0e0486492000804500c642c0851102c0d00e01c104103042c02c100496004202c2242024000b404541e4000c0200240745524803040442580500400300106040c64036064852858035094018103822600114521310348100098920340c00075017030341d0f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268811285 1250 268810035 268810037
    0x605010905010504051509040c081b04050a060b0a1b120f021c021b1302030f09010c03060f0504020903070320131103040b0403050405032b09030c0915090507020705030706050a 77
    0x4061044207091251300c0d01d00500603030310724564040020b400e40d018410f007511264bc1000040314171444d0020001282e8003e00f11110079803618105001c83e110440441d8044403070b506100b050120200c03641c0f00c902c40140300c014000c007075900d02465881d8004181d074a00404e160240c600c0f409030321814540c8121907454010050f0b008404002c8880c00c10640a904010007900706010312918685440070f981c03056030040072081c2e0403010010302003400c0c8541e10228169103010b1002c82d02d400f6000014240034000d01344075583c0001d114620b5a41000880c009503480030092070511290320030418001d600d40d0746070307000e012007146071410f24149111b00d042c3d114414826506644840c2c40710140c0703403070060080307041c000200700100780c1d6901000312202c0c801846444260b681d20100c61003c7c03e0300003a540034148450500c0900001d2079030f0403070ba0700703480341400005100c0340c400807504005141544244003451500050141c1958041480011750383d0660440d50f001d590303031004948610807418204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268812535 1250 268811285 268811311
    0x50d0e0609150c0307050a050708031c050702190321060b041401020703050a0506270a0201030e070308030a1407021c082e090516170405011107060501090501050405 72
    0x19007481c00c490085860424803912509214803d400c00d490740d4000641034075217500001026041100030442c281c0540110704c061130400709904800040c805420301c4c45843c581d1103100160a60b4402c21044100544030400e8200c0301d401c0e410040d000a262a221201c0d1858009405404241c640a11001c64040310307201881c00b40760882280380303030401440d41030444c090814000003013130341040810300481c0104040c0c003580c2000d1918844024120407620400d200c9002018031500012400915860302802c0c04180c0a501450f09400e0403002d40000782500e00200c14400407031030950002001d1000540b05024548600f4000d907507800804032060b03070300040840704205051090b00c040790810064038445081c0506044905c543c80d402c0614001413501440c8200700000c210b001700c60f003007004540700c0020100a440c005000508500225102200000c0810200002580126800f0407801c09841d20741c0d0300c91a01d40082d01c8284542e15885080030001318882c81c140c4140c50240074008412 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268813785 1250 268812535 268812547
    0x90c050403110d051b090a0e150603011d060a060609180f060f030327050a0e040503130b0c060609010b0304020d050c09090703020414040b04080f04050418050d0e06 72
    0x501d002c800c0800283c110070401041000210100414000801c2c818105a100071001052001c900002440503076044e00300003240d60702000100d0000c10360701000c4400d10540e0b60b0040864090502800d0805092483c12091480b4104c080740d460300450079148184030b450380e640c0003210028424043d40d0b0410313100048900b520a51a071140800c1d50003000c0200d1102d5407001200c0000101d070b407007900070950319031030344d8507038a280e480b1203401040c2d43c4030905000e4203000106000030f0751401081e40071068140801c1c18070004000b9101c20b0440400390f42c1049440341880103898200c0c13001e01e00030340300d0301c00407900c203141000300c00e416200e00804103415951a03400700900d84d241224151694091540c040c82c10f81c031030342b01281c46101c84000070000f151440c4140000c44160145200b4440420000d010004807901d440e1074100703400550003a203e00814009000902c107990100d58040e2509444a104040000e420403802e40a0307401c0d2100c1d4000404142c41d10340400003469401107040243c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268815035 1250 268813785 268813793
    0x3060906040302340303050301030b1f0605130320190b19050c070603051603060b0d020304170c07060f020a020307050415120b090f120703210f050a06090c050403 71
    0x2000844040d4201c04c101c0030f0102c41101005030005c0c2c00a03000120004014018402d06074a5641c0080f031134100c206480c5a62481d8a145c0d8a00d40034040c100a000a2098001c061441401010315040b070340c01071501c020740c00e03994460003400a4650041d4954824525007500d00784070030040303c00c00b000e03191421216820019660300e4008100051000c01e000c040d43c42c0d581005040003614203501c2c0080c00c0d0070102d800d81c0205640610308800c15090450070701520b0085803d5480b0403503404005622601e9503c2c0c44400c00050b050250714440d00456a04038035000000c000c07088403080c0e141d20700b254001e198101d03164601c5600194166200c1c3c1e8041140b41459400001840460401c3c05009a11201140070780655800140e919040000078080359000c18080160040400001400800080d43e015041401085000703401e015203031070042c00c2d07080b40c0c64040c40002c1c90300d042044000340b110440340003406d064805010681c600b09010440e01081e1250014060154540c1403e052660342e0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268816285 1250 268815035 268815073
    0x200a110307030f050a0c061d07090204050f0f120a0308150a030b070c080405100c02030606030c1309081b0105240a09050a02161202010b0a12080304230106030203060906040302 77
    0x9299006c00c1001d02842d00400c2961103a18896014004144600501c810101d0b140c44115000a01c46904c1004200031660740c0500000e01d981095440c1604101c090f07000030b602502c07644404441d80184e0340b441c0c0404d40d00110441c0705003035540d80e80303803614044418400c03a95541d00006268810080106103014041d424031140c0c9072144108601c0c0ca0344803804200e00c0c105010b5070002040f02c00c1d1400c403c5240c24080306501c0340058005100c00c48941000414001c4051440b514580d1354038403103428860740380101d07140c1816104c801840e001509408a000b84030480d80c9203142407500441214041000d019500c0c100c4000704440d192074241005d150081001030900c00ca0745c0c1e8200b250a140a1001200c001c200303028074100000150b50b694080d00f52490070700c00341e100e140c801c002403000e4140f0070f400c918116041702e0349030b803640d42d03620702000303512000100c907010508a04900718400348150041019203100303800756001c0352661412142d40d4201681c004015070850240c000ca40440700d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268817535 1250 268816285 268816297
    0x60306030f1b150901090314071508010e070206040b0c0918010b030f161409060d050108031b030903072d080705040515030d080703200a110307030f05 66
    0xd040d6410050400041440c00d0035880a07182420000b40000425251820140e40c4030030104074002d1800e0000c10000744881c000d4040100381000071000003400c0380c01000a000903140701c4509219413104180050007018092150190b80c20020300082c020920104041d400750340c0c412541c1c26552605c4404400d1a002440c0c0160417010303240e03101403440d1601c4034441c02440002c0000382d62f41010720b200031541c10000c041c030b001c01146107400140c665004050f00c00e2071141400312038039401d80c02d00107017041c80f411020b04442404c140010a41420100040c000c100c4460140c0341c0415441115a80300d000320110541d05401c294010429181c512040350200c030504c4040041141c00a0720001c40c43c40c0c44d4000380c0c0140e118103020f115a040c1881069045006008090b40345000440000e9540700b40303400070000c02250b000030619050180d00603860140f6000440742044017178100004154100b1029080083c4c0c00242d20250b11602001300c8400035015a41c00d1081844034609aa595110b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268818785 1250 268817535 268817539
    0x5131211010540060f170a11030403110609070302130c0c050a0312060b0f03150a1a09040b0a0803030f04020d02060c010903080714091c0f050303040b0f04030905060306 74
    0x16800401c0002240070000c0c0752004042d0094182a5a040a140485019006881403002c078174100307400c0a40001c041c0281e00c40e414526a030320744d26594054050a008524890b030f0300804010f03c010903411400a0640f8686130741100c440d5910791346601e42d50710300e501c8041d4110b00000710185540059800841e4954854185840d203a03003076030b569919040c942c0c682600014030b1550403028840d400c0c000c0500829142000c1810240758000400c142e02c40a0030000441d0b5400b0300c1021292200e40240000740348001420311200146400d4504541c82403410512a91038002c005245162885000094070003803c02181940e13100703600f600e041000940160b0b4802d05040040c1d0050703a17450000c0244428220021540f086c1e18600a00108170281591080c0542e4508015030241c14000f51100340100b1288005020780c07401910002ca08100800b504140038a000ca0003401400070066008a100e2150b58140d6560582c00000701d0078280c500030300180c030440c420041c900d4400c02a6410900c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268820035 1250 268818785 268818817
    0x512060a0f0203070f23160b01140108070c0501110a12110313020d050307020d0807030e040b1003090c03080c1c020304050913020118090608010b041b0c080706020a051312110105 78
    0x60045800507074201c0000301070414547e00322075080010b0304207060700400300d0707065070588408220000382c0000802403002d0308202002e1008420710201b50410300041544040466a9240794840102807075504c0e401c0710a03050800809110099202045078842d120b41a004d0352031100d564200f18080b8820f400580d50381c0700c00d000e1040982e0310b003202d0700f1801c1c0c070038101690f903074000340b0740640652119020903100f01d107030103000d45054503001c840d429a040c1900d40001c1c000741e00e18001071450b03a20f400140100d040419103041d0038200182e91802180041c041606000c010b10003240e036403040740505500316100c43d011039221000d050510304400c0c8141001106a00351030440c4c0204171882d4400306100361218003c2020795402c2c8690b441c001e005440c140084a8105a030f04c12855440440004004e2010045414012040f00345c2c1d2240b50b00280543d598056480c004016812200e07100c0a01240305100094040b041c0760f0043c941e035884040251026101070064a842d0000304e810320039a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 268821285 1250 268820035 268820087
    0x120c0910080712120314041103100504080705060c0a0212090109120c0e0109020c1c0c0c090902011403090606043c06050f01021011040512060a0f0203070f 68
    0x14107110850150580201c0d03003c95500e00e08014084185080c50a8107040c680b03030303000c50708000e404005a403040e005404040103641000200740f078030b40ea84a4803055685424184010400c5e07000090503410b0041c01207484a80703031050217880324860a003081c80941c0c00380c030040304000c502074003078a8204014140007282940e5844069845070380c3c00700c02c4915142c43c3c0d10074030210400004503070251102010450820a00d102d080d55110b400500d1024151199034a081d4218442c450f02020307507512040701840d8603911101c00b405852044030890110b110300c0c02d070a0450742580d058034401c03010b80c1d00505c05511610144001440721800c0d1030500300c0c07060350041e0354041d000400d00d008a45402607080e503050104d00102103c003da00010f110302c440040c0824143c0c2c2c00101002d03190210240080e6543d641c54641d00c040c0b140380d00c4642c124a04600c02c0312046408102c091144669060034046e203c41c0000d114103d220403110b10001c15102c0c0020881688501c0c0394131901c07080d10030b603040610 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 268822535 1250 268821285 268821299
    0x14010c0b06011403010914150a03020103050a02090402130602010506030307031b020d0501060f060e030d05031f030f03030b090a0606083603040501020d050406090509040602191805120c0910 83
    0x50b109806c072a102c0c0e52207040d40103c0368280200240e2000d4201e0528000c1e2400000041803103055100103810161210046500c0b011180d0480b180030300c000340115070780c0d50201c41403641d10909110b00d5025500e440000340203402e01204031480181d056075a440c0210f5880400400031a2864050360452007070007a590008209102e8035006c2e2134140b040a046900d8403500415a81d4489070b0740340240c01400201c0d6010f0341010980382c2054041880c501c00481d0380c5480855590190310140a02aa1500400c01d042c0c00d60720005000701c0680c0e00042c280d0300d0804000c243c4107948036481c000b4066100003000c00d488003003441140071392203c2400d0480000725a5007000080400d910b4150b400004040200d9a0100001861380000d800d215041601d00803001d0152000c501c5002e00885010780014200980b0f80d046036280164079800a405110b0420001c0c03000126204030f200c044610140401c0520f00000e0700b0480c0341400000b443d14604c04014443d24810180c200300b4901c2c4581000310b101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 268823785 1250 268822535 268822537
    0x405041e030e120c03030703030c02210403060f0b090106051b030301080f07050108040506010909060b030d0f0e121b01021e03090405070807080411010908240114010c0b060114 77
    0x50780a5030303900700b03000c240c40204400104203900040040d031081d07500c0c004603140802a01c0115400d4240014682c4035090300760b0414033249098448030301c41c6030880d01a6000c00002e0000d82e030040d1006c0111030003080e0f07005c00720b924070450315621003084c2004014091040c002010080d11002110b40404100c070401444c68000380c01c115000d401c03200911410904c104a19001050300340303451030403824180c90715522458103018178040f0f16141d182800600410b0741040d45040300c06000c80300f6540400c14010805003d034000040000c9228030a40302610b000030608005441001c050103103440c9851b03441114031191a1500d055004510804034645030040144e03000201e1304000e50382d80d44002c0100800c685004114400f401f0380982070100302d076400034005510a6106200209607080c000c01650070b98031030b0703000e5011032245400d019800d4104514010100544080254190744c031074056101040101c0301c3c0301e0025880002400c04a03004814075a08180103040014140f116852080341c0d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 268825035 1250 268823785 268823843
    0x91509190b040203120a050406030c171807050f0a0b180301090f120512070e0310060b0d0609020702010e090a0e060109020c0c0414190608030406111911040504 70
    0xa2008840704010950909105a03512604a807035071520317188074094007404078044c50041804141d954400301c5452070080303882418503240624143d45900d08100b03041c82506107016660a42c1c0241f500005190508420031450717240300074050a05503040410360080f9810401c030744030f40d00403180d820101a407000c0c811044070038000d000301c1681c00f4060500c0c145186403c3d1140041100030015440188144000140c102c49240341c181140080c00c40042d1030201c031118180d54007842c0250024040e4030365001041c080e01c2d04a17043c4003c50341c400e4600200d001d00c41010b8003040c00c3c04104031b00791800c002a00d41c450040e40e00003e8040c4010015807034203100345c10061221307500058480d0910800c000240c44518111810302c480c94400c54150a040c60140c0303d01007210800f40d065806003860b400c607501414051003103030340303c0395aa8001030409170404480d04150107561480c541c0001010742c641c2520340c120001101c0d00800c4010b200040ca00240300741ca41c140c0d084005580020a091071000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 268826285 1250 268825035 268825043
    0x10e151c0b07090b070f0204020306010e04061509080601080318130504110a0e07020a080a030e010509071d0709030f020a05031605030f010c0804020603070e0d12020c060309150919 79
    0x9450b10340802c000e001d603400780e003001215050a114400000d05010f445c1b228140d8190707005038890b220140147da01d00e4084000507803080c2403c0e0041049065044008054101030740c800b14a290f80382c5545489440070f0007500c046070002c21112618440740800c0c0300030400b02600482120682354500c6084501c10780d030840c1c10703645080e401c02ea20725154940c80007230000a0b901c10594200694040c0d0f41e289a4200100080008100500c200307000307504c44180713030303a49600a00c400d04d480b000032600d85015024440d204040700c01340c0c5060001c100d4006220301401d4444903c007a0850300c0742d40040003900d0089a21002010000c24180c409000c150100031f07100691002160803e0109801c002e1201320880103685030111120380300b0750208141e44c21a4064404550b00d40b1030764030032580b52000003070040c4c00622110f441410000b04500c81440b8120a07407d94021f01c01b91070030040e1911041d10500c090341d00851103c0c62200c5030b104066041084081150641c202d03800ad450014607550700140c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 268827535 1250 268826285 268826303
    0x20d1b0306060906060306180504030e190e0711120304050709020d0c110c0d110604030215120108070605040312030f050a0b0301050c030103081b030d02031602010c0206010e151c 78
    0x70850750f1500a040c080c208900b0207000b050305040d42c10310400420324450140c541c4940c0810140f60054103a29681d0001038603070301d1079a082a9160405080500c00d81d8501d1a1400010703142030301c541310422496801c1030141000c6120407079100955080540306690318002c0c80c0c000600349500748024016680301082c045008c1613240c001410b650001c42100c01280c004020600b01707030f901c00c030689006552260102c0c02080c62800401c0b82406030707410003500064868200001c0c100d40001800d020f0300021511100d40c1c0e20b41829a4a8a03030610170f00e004102d09020501c001965204e1510300c0a803185000100c03400840c6000081d28030540304091029900d62810540e41402c1c082d42c0c1c1d004011b001181e2855245507600314442c80303840844007156825000c5a068040b0500c00c413601c282000400359141d003003603104034000300e840580c024003644c03800c05161941400803134220b0485109804040c965650b0300d01040c00ca070489041550b022450380d606000215a850005861070301500c104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 268828785 1250 268827535 268827539
    0x11060106080402010f08070906140f0f07140c01090303030b030a0c0e19060509070c0c08010504061406010e010f1808030301030803070228150b1e09011a07020d1b030606 74
    0x3405c400c0581812008120b24502000030b510f411542c41c908a03a1203282c00602883d414005104600071221546241c407000500d000040b00c5440181034468020b0580c0400d8500192400390307503405900c3d0880c0810390403801000070034002e5004040c00040501a140c28182d07565500360050404c0d0420b091941c440811b0241024000d104005100c60312101008800e0600b00015420000206000c0c1000f404502a20030080484011070050003c1d6000b03116604180c503160000d01204030f5450810301c000c0001030007130b622512100541047c103031180071080c034481604407441d2603c1456890031070f0101030002001c440030401503000b507018021070740d00d909107118003d04246009074840b05c80051a0622000003400303106003021540d100318105503c1c03c903104858050b00d005505141e02c01c0c801c480d6040d01c4d02a2118914400c81d08950248a13684c8980b40c0416003d824600301655900601600d801418040d500211290092442c0c05550b040b0100051400c207054000301c0c2c1950320360b142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 268830035 1250 268828785 268828787
    0x9060203090708281b0e15040c1706010e030106080d05030610030b0102031215060c030c01052a0c0102090d0c080105011406030406020912010e1609050411101106010608040201 77
    0xb001818040c8150701140908504200111445041038094280405d21104060718000c00303105800425030000b20011500d0006894041e039001c9000003800355080110301041c00384a010014055000d9400000d1181c1300c03080111100700803d0010ba8040d035036441c021a101c5030800810321045101e1740c034240d0313038900329081c44010f60fa581a440249820325192a0b12aa004410b0311041c2a144030a00084d645d41054a004000f50194481c1c0040c4005003200342403038080020040c0e001400001c1c4440c0d141c22005581090003140d040c100c0345c000310410020100850010101025440005401c000d500c030700083d00349454204c11101070000450070401d10b8400c1c020f05005020005101410740000c202060483c400200004e2130580d001400c1c1d8180e80d1200b010360b07020300d0310000801c0003003021000d040d43e45682c00104181001c1c50000000c6030706190298070301c40e80c5d001c40c400400c1c000074003c3c0f010300181400d4034018002140e0100144103000c000140c002e2000d0b640da14164141400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 268831285 1250 268830035 268830043
    0x11b11070506030c180604030c0b07082205190b0306011409090c030f070309051902030a150203010906050306060d060b010507080310060807020307051b010c050a1401060501051303020103090609060203090708 91
    0x707606d000d800240410008140400404421034442c8032000340d940200d071074854950301c1000b02001c249508102502540451900804190340050303460320f18101e49011102201038152041c90b81412042000482d15481150000810310b0350440bc03904015003075001855555040799020341040c80801000521042c1008258010440c1d050030440380540f1745441d5120303030b40c050740042e68000c0440c40c202103403010042c40c003105400501b5882c09022258040300694000c7c4144200181080c80110385860701080d2140203031070040c00c082c10b141150355003030060040c4035815414000144416008141540011441800040031034046981491400341c28080080e10030021541300f40140000103900144c11600840d0711003051420201a10040342c070b918454078020000e016285242040210601c0c0ea81ca00c040c4280080c0032464481c00110307080d0203084103070340c08088000000c20140d40203901c40d203080e500075000807400c22019258141031b80d0003030310076a00540c4400c0040001510130702c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 268832535 1250 268831285 268831327
    0x10e010615020c06030c070f1112010e03121e160305010902040e190204080102120f0108060903030a051b0c0a0516140f0d32011b11070506030c 63
    0x10300710401c02041071400942d921101d98006002e02000004075940400718001d903030f104e582c03010711050140d045103007410b10b0000c003e0200d402410381190108502006020b90601d200981004500b00040344c5010903a031000541803a0403109000031802000303298801c0213208072081d1030203030140c03003000c24000c048600503840058020b2050200340040c2c8180808a900602c1c0e8800b0312100078070303100c85100288120b03801142158400201501c4195038a0682031040405a03031b0902c85a0780c3d28100e503111f120443d07480e041740d04104006107102d0b8103544125086690351003100310100e44551410819445451034480c0d560051400b08208002003009218240b0904c0384002114502010940c00c60189160f540c4100c0b003002da4250551105451240c1494001000106441d801c40c44c1c048103000740c21945074100205007101403070140501038003d4682d180f400c482c6041c1c80d14001190b4045103044c0c0440d847c01a0040000c05a40e400059806075401c2d4010300d40c0d03100ca40c0c5003030005103c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 268833785 1250 268832535 268832549
    0x303090605040b0307030902010210060f0914011a0a02191401050a0c021207020d02041a0108251d03060c0414120607030207080c060106080103200d080a140c010e0106 73
    0x104000e110f412030b0401a40d4000c0d0441c00d020407440107601c0141c0c00c042400d00541c04c060f2800d00005030300c40e114025001207642e45001003010503495070030401005800d0040441c0c1c0c46001c0301f10801d04032894002e0241011030301c15140064011000c3c8802203418110903510450360700d0100c00c849200703100c1d80b40c0005110030200712000141002a46038904079030b42d200300403000304898055440e890081c5a41d690f0040c0104440206000d0f8154101c20b01810a80011540000160071103809003034005002d101610000440c0c120304000c07207146104107002410711080904580850300c00b0000c0f54042c181014900e0f840b0f600f03041c500600110740400320744c480c440303040030f06a131824080303401364024406203405039035a105820202401d10070b407034040415114247c0005281c03548240c2603410b8a11070032002d08200400701c1e00381c10302c00d8941c2116074400d01c04040c10340000c08510040003034501a050000382c0c0540c519542c40c0c60341100c0503a8046035121200300c3c11800081c846c42001c0c21310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 268835035 1250 268833785 268833787
    0x90105060d02060d0b0604230a0308030103021c020301020c101b090b0a02010209030d0f02100504150c02100207061508030f04061101090206031609090203161805190303090605 77
    0x89200040c1c2000786511001c0d00807040041e502d0440e030503a8000905603a0050080b555465450700c1c0501c00b8a400c1c0300d628600140100c1c3d44020b0704e844100081280e8220b0b1445086900b0f68080181c800e00b083c0140045080344400200162000e0024164000c03664010340800b000a583c130400381d583d008e8068058803040c1c40b1402d500c907003200aaa0640d115145e42540312040440189c2c0284240417500e5894420141c14031040341e4050034440c083c2203da400d80d01c0303445c50000f0b10026034409440c01090703280041681103c500c8181d111010707003c014030490300d4074020244a0000c0741e21007401a520070361034490148100000804400007003500e08011840d048080d04980c00c04e0107180110070401c003840c50101585a400d4200c3c10011750000c2c00c40303540b070a10341024040440d03000d40e60004602104000621020580300ba68410340b03080c0f04078408030421605c120351100361091030702138490400a000c1499200e4103480162007204240d0f03525080c3c1581005003203c034203a4808010000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 268836285 1250 268835035 268835041
    0x103200909330d020d050a12020a0807020108060d1e02030c0907020601030215040506032e36060303020606090901090c18092a0909051b030a05010f14090105 69
    0x40140402a150000000075940b072140d81000220030154180c80658800c84070708a08061200c0442c01c40b10385449641001140e54902074141d858600100014000007000e100c11005540140017043d80b0020040411309401025034528405940306104d101d51050324206d202c00f1030074100002c07055400221402070085c5407128009583d40302c1408028040c80d0000740c604103150701c8105842c05054020802522460420405180f80046507200007030109024003082d24500c140003040141c40341c1c05515814602c80300b0f941803c603555440c5580060f02c0003010090200824400c03200034621a41c040d1503a418010100101402e02411011160349084080070004074030f8000d0000300c0e88002e00788480d2100c01188a0002d00714040c000d0442410401031450800407036030540c6000f00c401180342d03440c41e01da40c825800c48840030002003580e841002000740646040d881180c02c2c0070000c0444105c072007965201030a4501200e03136209465254410010080140360301150300504c840020040c0345 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 268837535 1250 268836285 268836331
    0x6010302060f0d2a020610170a081903050f160807051c0906050f0c030103060507110a03030b090a0e070528030c0302180c090d1b030308040606060e0901140103200909 73
    0x20141e02c14074070b40740d1a48c0b240148050b0148a80d401d80c0360003544032a100c41e000030384c0342880c01c0e65a10703180000e840c100002d90786100b101c0003a0f0096031203030400310f04410b0860080da0409400381a403014400b0070300220710f101c813000001c0240110103100110710030005280450584902410500d031064120040008000d900002c0d41d0449030080070100c0c0c60340b41c2920a940c01c1090b01914000c0e406040115010306425400c40c2140c20001c0d1130300d01007562002c48100c1220040c003120140d44e04240710400183c50141c2010580c0c0c1480d001c40d041111201141466190b410f82c0116030803072a1540400642c1382c00b100f91301d11111020300049e0030b40390a202daa01280b2954030303010320400c01c4001940500c2210035055100448003900400300503240d0801400c4801c0807076007210218100407021510034864002c2d8001d41d14003030407101c2141d0030184190f1441c18502c9480d41015520076100790014401041d00c2048400c0043d6966142c44000a0010b0000010050000445040d070036580715 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 268838785 1250 268837535 268837561
    0x10302040308070305030403031d1c03020f040e100806072703020f040213030803070c140309031e010e030315030d0201110a0e04201306030e06010302060f0d2a0206 72
    0x1644c14906295203a440d49010b6008150380c00c890713190030400300c40e040d1000c1c0000410071807519031251496005e55042104405034401c80300c5407480c150b424041080654808507103260041601134400107815100c01c41c4900d041d0341150f2540006040703902101e41074259078130204424810300980e03a4681d0542c6c001c100c64002c3c07101c1c1d25000f50307400074240c003196030101201c0d4007840c0d00150450342da05000000800912048a0035500c3c1c0005e110205120a40001103403a00e100c09006892150030750900300d02c131296003080b50344480d500c482803024450814002144034251030000e00074404111024546048009145002035a1424000c140c0515956060750714685071441c2813501202c0700404903001d896031481c06550207a490001540040b80c0102528001002c8007645030a00d6032881d04030191050140040c40d1500000014400741c1042001408108000118185001c00d10901002290805440b2201d0380202041c410800810080741c4408041b140c401070081d030900210070021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 268840035 1250 268838785 268838797
    0x90b0703080c0a020109051c1404030b010306050414030a0315080609060609060f030106080307170307050d18140606010f0203040f140a0b0d09020f090112020f0a17030d0605010302040308 82
    0x440100440c000341c200e40b01b5084288031503800340640f03102020a0511a050111581da07800105420202c144e21683c07008090300c0440303402009601485c1d02e5038031018010040134005894000a1600340190310310108002c00c2d5022190b81c00140d140040409042907000c02d401941c6103070000d500703028003200300045441c0c010800300c9a8070219240c2d440001c2284240490480c1c2650800e00001040740002c40034000f0207020720205ca0700e00e014403e60349001d01c0200d44071408501c062104080301a1a5408061902e01850790b100c40b0152039194407482d5414110501c010780e005404102c42560b011910b02c5012605000441c01c0a0034581c11074071800c628000d9000c0341c415000422610ba58030040d58002740501d048165480f06d181c4c0032180a004d041006074041d1941c1e111850690800c0072034103048815030100b41c09881d031a0350070020030307503010060f04e640b0481c101d001003640041c03074034080c0c440340d103c0d40255903401852452000760354040e480f06e03061510620040012803109030866103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 268841285 1250 268840035 268840051
    0x102060615041e091505090f0705041d04060b041503022202030c0403110f01081f03080c0d030e01050606090112020d020706060611120415020c030a080a090b070308 72
    0x600104100640365140101c0d8031003112658001031484001c03240c840358200313a0f04450f40a0205c48040e0f80000200103091107080d4020f48503400046007461195800354000c000d038030300245001c1d41c030081040640c0340f0303000b00220700840b5001d000402c00c1912400100d01010383d01400082035690a03600d0800c0a03100207809030000348000e04442280b031420b03224265544408540380e00301851721000c0c0da005070008664003802e00d5007020251410601c000c00720807050351244195602c2c02032148218481c046018500b1b0035803500400020169405010030142030070041469900404000701501c0041a036415264942000e015103910391104444c05a1402c0c2050301c201c03055010101b00901c00c13040405c8149102245d030300200401500540c0c111011681d400e1010b180311860300352601004c1400502e0024104001c110700000c0151114900702c50b4016116184602c1e00400e06050050070210b4080500140010300b603034010b40120060700c40308412a0425205640c0034200d503201a10b450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 268842535 1250 268841285 268841299
    0x6030809150f040603060e0a0e030901050a02031201090c0314060312160f0b07110115050f0d02180a1103072106150c120c0503090405060402090d110f09040201020606 73
    0x1501c40054508a40040c860340c60001d0b5103c0d641c0c200100180704c1401240320380c5284c1801310b0306050860103848140f0010070081c6140003007082c0156450344c032542401e819800b0520090301450b4144004a00034200c41d2804144155618001000c8400940e0325a1100283c030043c00625240001c400741700c00307054aa110303503803000c1150107455190301450050078035104500160030807a41303150305030241c0140d0b02c41b1210001c044034a00d098594403859000041d01e140310821191406400c0c4111141c80904014081941900415501500c01840a191004500510552540500c2113a0044c003039451494214204114000d0410703c840003400021282c1c0401e803c642c1034194860340080c1000360a90701e550400880c081c080807100302e0141c0340308245214215410f07015150f0404241e41c40300c06146068021010040140405444250040d509214a202c16100c076014516a54008e004001b41d5620703100070000c0307038030700d083c1e0460180900030700f4000181d0b0001141034008204403082c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 268843785 1250 268842535 268842559
    0xc0302030303070e011416170c030a030603050607050304030e2413050a05090609070c06060b0703020a0c050114040303110f0f0f0f0106061d0f090c0405010905030703230703061103090c0406030809 86
    0x6a08c501841c0011000c9010020f6000680c2d17826038400b0f01120301c500250b0b4a15503890009441d21300040b40d000d400b14903484011125442e12941401c081c1100c1c0c2d118140342010344011060a4014041c018185c1100c41424006454408035060082604440303c10b0740e85043e0000c00c40c0703518041d003071209202048180c0741c20400f068200001400808000c50748640c42400c0095880c00041020307941d41513000c1004c1070030b502c101a4010765440c1c410361603240502d0b641d0100c60b5901c1c1c1c0000c0420f14007900314180b41e00c031360038091910a201e0080007440b5a803101c140850801d80d040345411503aa150090420020780c100d044e080b018080240c103c0080512400401c041030a00103186a00144460800800885020140061320020380e61180516122014140d442e8014080540020f980144c10081013a442880c0714614002070113807580c440d1390f99030b50410748070350f141c0714203256001004104042c14100301c10202e40c107040310140302e202e2440e190505148134900030f460183d80c0040c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 268845035 1250 268843785 268843823
    0x30705090301021207030f0e07050f0f09090a05060702010e0c011b0506040b0a2d021308030715050a1b11031204110306010b250c0302030303070e011416 67
    0x5a400008019000355560202800c042d01c0c144d0040350450b0100b460310026480174031403446008080e0316400002c00745207082c07400b001503202401640348e50001540010b0411910354400300c40c001c1d400382c8020301a4001924000d802d00500401410441e0716224030170305869800a5190100b00c020300b00744841130034070703085c850f420b201201c00030b072440c4103441c01d110030860340d0280ea0748503408142c4204400c010f43c000190581841003000007403004d01d010503605410307507a4010322101e0020303030216035120799800641c0d040d60040c140036140030b01070f00e081c1038034803081d0301030070303502803081903040020241c0349480320340700c0040f00a4030701040030b92408102034940401c100c98103080540c40b101d60510f003a00e800c0351522036501c1c07524024018000002200220003040c0c40d180d1055580d0503e550800140b80c00c140901c400c0143c400303200c1c4a00020250700e0500080d4012545035440c064100320001c00501840003a080c01e0110701c00c10441400924559005d88103501d03408481186a60600d0f44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 268846285 1250 268845035 268845037
    0xd020307030e0f120105070c11010215010b030c130905041a0702100e100905030c150103170304030207030f050d02010b0901060207140d0503130603111c05071107060c020330030705 79
    0x883c013909600c0e25081c0000541c1050a0007511032080411a81c6d200828004a840341e05155811351041e81c42e00050003031502d4072000d0340c2e0207080d1250050402140c46d001c074554810607801040c1c01ca940742d05002c10301c0107468080c1d041d540702d0b142e820224201000000e40d6403c500d112840045d59841c40358083d08810f100c1007001b900c1010b004e20400d449800c0c035984130340c800c14094949208265050a0000b00c1d2860181243d801440c08481e42d101c1a00312803281e40010022011230203802000b200007008046030850300342c000c4008200112194001a003180e0a00c0c004034441c1c80703898010803040e40e000400800740d0340c1140400740d4416800001c1a89165a400002d00600010800030b0791740c1d40c0d8914403011a540341e07134107000862010203090080c0c030a02c00040c902c3c01c000e03d0000e17903503075240e00155082203003490808a4001e4203d00326090100b0b607007001c40000e0701c00b01c0e8081540380400011680d0400d0300c43c0051440460f40016449126515100001070004400190740c680608 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 268847535 1250 268846285 268846309
    0x9020a060305040218100f090b01020c060a0212070305070219080c0103020d0b100809211b0a0609050303010f0b0c0309010f09090c08061002030903120310030609140d020307030e0f 79
    0x8014217071401c0038401c002c400c4d05140034020189015040000e4104018001c0381d900c0281a005819020350402c140203060b4445413601d000d5105040b2007500044480c00284044ea019907543e0343c580d5036078810400c44075200c00100701f0608884000340500c06020500710380c0c900d000d080041c0e646601045001c050401d211445611003041c0b1400d1600c0d9400c10215482944554140d45a00105040816025444414151400307a05114408126001c1051034402c0440c40c0211005506256100803ea0301403070011502d036003000c0010170540180740805405420241d840606150710358100b0b42d501d008407641c0d40c0c1002690200c00301068019441e540107000b03002030510034220303424000340810000f9602c441c0601c0c81c2041015202c0e00c0071080d01c83d81d00c4010050044000045d51041d041d400241009000c0380d12100004001361151080d4a80588a01c00c2140e421810508050903c910785445800b55002084420300003940040c0305010000308489040c1280c15510109082080c16 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 268848785 1250 268847535 268847569
    0x303070b04021f05030604020a030f0906060e01080304180b01050c03190834050d0c0e0906010306030213020a0c0b041a0a111e07050a0c030b01050409020a0603050402 73
    0x90900038003481003051403145000341c45030444261801080e90240c01c150540302c0000e18248003184051038107030014140c6459502c1c000c92924100891401202c2c09403400300d4100341e5621040103e05210940303180149031a401850a040c50b0a0880d0001302099110044450399040690301e60781c01345083d42c08688404085a48945200e0096841142c4203944000440c11020000c1c001c10040f0155015000d4400039880d0820500114225084400c90f01c1d00140300e030500080020600506ca0440ca0306c2d61070380d0b84090403400200788445004003900203410541015400c2c000360b10340440011001510800c0169240b103c403a00b10f51400240c1d1000300300b10202d006100c113200c5040c8400a21885e811240c55264695000c40c2d0100c0d07241101c4042200018000752810441e584080c5112569031034000c5c0c54464580c1d44c0707a040101c84031007140c294410035070a1042c0986540340c0303030240c6025282004a214281c0000d24404c1203480b44004040c0c403140024215200c12200d0032070f209607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 268850035 1250 268848785 268848787
    0x306050c0403060b03030a050f03090109080307090e0f07090303080901060e18011a03281b1707030f1509210f0306050a0b0a1716030f020307121a0303 66
    0x2245000c803080d07101c0d1206440d81410701c0010091490003108451045960391a81440d1050f41400000190030040c503c1005541c1c40c00e4001c0460344090041d4484c000694445603140e041052142440501610340161a0007402c1000a541d0300528034500392505401c0450b2207035070347e185003809007015070403114070030b01c80a040c48038108120054911900c03204009000001c2c60391503400071803040003442c1d64142d1214008600d141e00c9081e03d8904001c031241c1f11182d4525a440b51200d50034140c0e40701c02c1d2840380190400a184411030382210074a1590003604140e440c41e107842485810191010b81031a000200f80b001441d00c681c0300c40407107940f00d8004c2c16500c6000203081c0001900304d0501011603189a84221007a1081c820b001c1510801031220171040d041c02c260f48215000b69180209100c2840c8039411246188440584a01c00c00d480700b41000003010401015a0018013191b20704a00610038054010340003203400c0785040030400d0014113022102d90603904034014000b901d8140c08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 268851285 1250 268850035 268850041
    0x30f0706060311090f04060c020109080f07020a06020a030f050921210c06010312030b091008101b03050a0b060d0911060301060903110d06060b0a02061b070303020c0304030605 77
    0x1400c0d00070744200c0b070045400054007001d000501c0000c010454400c00c0310340b80e640000300043c107640e01041c2240042d00c000035414025030b42d5000290301c0480c500d4800500070800008500e07010048001600c2140301915081115070350181c94000e07440d0b0042c040c050013103135054007a100c1c0e41d0364080350141c0703441380c5811141c000803140e2600149102c00003240100c0300040b03c4185440300f00c400d0504850010304490780303141c4501c01c00e25000901c58040684035184c4905940d40d9600d0240030342c416442400040b4900006507181401c03442d000d0590604002c110b0741140c0150318070351402402414003003104d40c0c442082e98014450310801d603600400c0858001343e01142c9500802005104031420120400345a007008000e020911680703001070038011003440000c40980318100c4487c0d001e440115080216982c0c44103607601604807003400b030000303d5243e24043d410000c440d00401540c0600b081c603852840007900e18441c0c0207001e020316400141c0f41e50500b004004980c02541c204074100b005003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 268852535 1250 268851285 268851293
    0x110f1e0d022703033108151308090907110f010b090a14010b0703180b03070e090142031e06050609040b0301091202162114030f07 57
    0x5081809201519141ca00030000400d051808040b91800010000c60509020311591003101040c0d4404102c1001c81003a0340002064454a15019124040141c00c41c40c1c114900c000060100030503500070000f4801003400442c01510032105104001d0f2000c0c0c9850390f07491000e90b411490804407040d5841519880f0345003590640c0a19024002101c0104031520394204000a4a5482c07403e41d00e14a0350071700411580380e607000103001303080c1319090010940110081c0354240d42800e40c0321500d0301d200002004980c075031010706861600411035107035042c0d505201d1100c211400c120210f8290405158041d1400b0440101d43d08400300d54070781203440c00c00d0001c80103000d00076510100311030000c00718500c42c101c4058001c40d4156080a0171481c105610201000064545110302c42d030155230f00d43e043d50106203025061501403002d500201041c4020601d0b0b00b120131619445403070311281d0398034510b2141c0c654000d0695059046100d00ca99603101c44211400c61080d44e840560040c00015044104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 268853785 1250 268852535 268852537
    0x40216170a021b03100b0d060612020a171c050708041e060206010e0604150503010903170105060c031b030408060405150a0e0c10031b050c0d03110f1e0d02 68
    0x31907090b425200030510001018030b054203a100425030640045000300d501102a901c405903040d4018201003400189403100c3e001c503500c9400c030440c1c240e042c092a01c1941401a60b90f0b0050000381c10050f05290b0f440602078803422094803040351905200e030000305492250003511007054004401301e994554404540c1c8000300d0070611040c0c02c8e08481c1d000603010f8004502c184c120385071b02142131496924642000b00800c0025044481d00c44203120101d80e0340c42c01d1082110041c0310740c0364068064a800d06d05101150140e006610030001004284001d89011042d2039001d402d0000c0d0a9541c0c0d000b422450440c00340c0d4010f1421885600d0400c410320800140c4000030120302c140c004444e0700c6450116043d0b400e50003620307203035900c1500185502d00304a103021400d00c1c030f207281c0092894086240302454000810446001400124031154550343c1480503207244651800c04104022108104a0540c0601403011506c0103010034514080c0004200c403c2d0542d8402429a644a0391002c4100003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 268855035 1250 268853785 268853797
    0x702130b010216140a090c0c0314130312140a0221040803070b180318060901031b0e0102120403021c060905011d15060a1712190f02030a0e04021617 65
    0x3140c0c03c0d1703400004c2d00070740d58443c414900b04941c2d02d49015031280d407003d07106c3c40e221420301c40c0403100c108142c5034000c0814a02c03002a522032404411400b0100f8001020346002c1c00c040c1002c40b1041108000300d6800240307460340094000c0f01c0107155054030300d0024140c015607110718824000060340300300b0410044d06044c494000120107101d00c40303002c4800c1d6035030301941c440c0c2c4803000000d1a4001c40d078500180942003903641494082280d1602d1040d40608460f410158808560801c030078001c0c545e010b0200c0490214104802c9007407920359000681170030241240f1040d680418002442800219088198411f800c400244100c508030006903d240c1c403072040c0b8942d5030240d04503080104250404040c0980001800900c8850504030810156664070350802500d104240458400d00403040103031a14468040c46c030650086407442c0a0070100c294602c000454200300315600009400a04c1c0f50f041c200c05a5005840d5900352207107600d0401818000f80201c01c01e0300e8110f91a000400c01409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 268856285 1250 268855035 268855039
    0x106091d06010f081005061f030b0307080a0c0506030c0d020a020a02010908030a0228020406080304050a08060108031c020d051f0506070f120c021807030c050702130b01021614 77
    0x3181e0340c40e050b54020860500512215405c850003140000107140c11403500488014248103004198000c1c001101c007600010001090700c1b410ba0301c02602e002d2020b14010140000a412074164983c1c414013070792440d01a1501c62007000c0b0100e1155000841960380d02039007511b0455542000e4900030b5601c0d156071004900107103644001058002003c0183c40391400c0980080c452500860203038036404032030540c0c01d5124044010960702580cad079402030200501c610f1002d5684c40d402c01301400171643c001c0e000382045900c644010004590004122008150214401441000403141d01070284c4124107040501a0400c82400300700501e800f45100410084030001a0155440d001c0c010a40587c540c0035140c2070314054900082140c88080540300610f51510850210703040c0d000444188001a240002034241e601308810f00703815220754050840e213030a2443c280790095000603100b46e2503085542255031180600e0030386034001c003c00102d100c80b203020449000e80b168250950710155250141c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 268857535 1250 268856285 268856293
    0x60207050a05060f0304021e0411040e09030c0604032304060f09062f030d02030916051806130e25120317100305010c0306080616020319020106091d 65
    0x34061030080201c1e40194007003104982550361b1038003080f010400c48029246a44408000c010340c2d03a8444c4606441c2180640d003c07074540d814040900a01c000c01449204e00c0d030b101700081d80d052600081e00300d50066141c5000922403e442c0c078030030001843c13106c1442c00b0300000700b008640130350071803201c0003041d13401d03a281c20100d40d6606044400c0c140c0c40b40c60202c4d80050b02034824910b02c1c40f40d0f07508200080e0004492034204410000c0040782d00482e428a25500b1015064140c05001d0300007400610f42182c0315000301908411000301e41030003900b070610801e0700c0e0b5080340401d44950441401c3c2c2c120102a10000c901c095081400d440c2a1b0141c249039171641400070882032800c0301800e2120b505903035010b8181e11200c030b40c07040742d000103006400b240d4403100002001a0782401600d640100594011440c0e07450410003511705071001d480c1d10005000002101519980041510006560b1860340001c0d01c800000a90042445800038001d490070101f80748000b80f076904015828540f040202c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 268858785 1250 268857535 268857539
    0x5040201020d0207030b070509010903020604090b090109050910050a0b090103140f150402100203040f030606090e0309030d031a0a0b040609050901140405151201051b1309050403021204060207050a 86
    0x4a84030805400001d1001e086e490114a000707110340f0260030303640e1060401d010a0394690b000160700d41c005507c011112a140c0f000e00d1801d05020ba80580100306c64002030045040c0f4100203611015250700e0f00702907582d681e0004820700c40a070000491001c0142c0503090b0303961a030a09800014004000890600c01c0c40001c0000c90b000003100c50301114074501a2031203840f03036401c00c150780c0030548201045210901010402c3d039000c0c520b40d4001c610400723000446914102002c415551654040d1541c3d800511010086460224149482e80540c1c0b80002c0c4255881c15040e414444a425064110380c00000200700d4020610050046c2e071341ca62101e40d04103554074204050304000f4000d4000d00c0c2c61200a556480c207094210581092042d505400303146110340202c2d03c000d19000e0240d005139160b0b0188052034180c01c110740d41d07001c1c8080c0e1040c6012150031100c0c0c00c00080b407143e54005d91b503990008080c03520074403040b001101c10948556646545030030007541c0f00c02c1d0340039503403003100c0d40400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 268860035 1250 268858785 268858787
    0x60a0b0418030324061403040203070b030108012009090a050c040801020406030906061502070611010212040f03110c011704050a05030f0a1403100b0d0f02040906080601090506090f070e06030a05040201020d 90
    0x500201e8001c0c3da42c54900f803103015003124090704023600c00c90b003500c6032200c0441c0c0382c220340b0061406041004000601c0840750030303801c035203202e2050342713a02410b400b003061401c141c403962000c513404401031902003444e89070444030311018800d07584403030481e510109002c115294560411052a4000c48061006075118036080e5041cbe080700460710301503803041008201c0c2030b018055116090034948001810165088085850f40d0004c490803143c01c3d801520110403d9040688080760941c03d000814981c0c080c000080d0898150400740d407018500c407030001701085400c110b40000c03079601405883e00c5850002603040c00b508501909000704d42440621400d241001c42600e00c41e6021a0701c0c621283d14040c8803904941c403001203895680d0711420200c400e82420b000800040889200000d407051608000a041210680210084500340010b1003503903501c0000d12500002580304600e0252035000313043d50711100c01400141c000801108100500c040d80d449a885039000b030702980d1a030039507000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 268861285 1250 268860035 268860101
    0x7060e01110c0f01120f0606080405010507020f030301090218030a030305091002030906130618210201020c0714010903140106030312090309090b0a0504020d05060a17060a0b04180303 80
    0x50f80c000d01c030003c0c102150344c800c2004280101d00c1000015107030300800c803802e05840080d0001c0001c01c0007041400104282489419417010383c6102411400641001c01600e83c4018415402da40e500864003800000d505050051910001800c403407000002d450040d0107020300302da11064500075424030302e15034131060084920076925000070306007664510ba000020b0825141003941c14a1b581c000305207502c41c108126050442c09201942c031848001c01c000c20400d000c6c0e40c4a0007c690040c0101505171704002224400e0b2000044017006406011740121081c80340750b807028000c544004c00d101040d0906501000c10381c0d00039030b540100402c80c202004185c03180100c00400062491508003c100c2081d4044550f0901c0144aa043c407a91400020103076045001d1032081180c1da2000c0c420704c4d10b409e03074005004140542400605071105042180c0301e0360020102c0e04500d481e480c041e070141c0d5541c0d101203000306c01460280e0400461341401001805050f104d4030130004107604d00501e45012207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 268862535 1250 268861285 268861303
    0x705090106050a030f020903030a200c0a0e091207030906031a180c1c061401020f0601030803100504020708030405060c03090a06020f0f03040b070806010507030e0907020a0507060e0111 81
    0xb441c0d1502c0c207820550f00300d00501c01c54024200c69a801c0c40041c1c00c1c0e54081c80109118090f0741e580d12041720500d00b90807014a1032460015107540714004000c401c0c0c1700d00140d0340469081402c41c40c0f140c1d5580c0d40346814043d000419443c0b0040c002481420150005c440134191340d0203640400041380d900750380110140f0405103003680142d01d80301d5a05044100f05046610014429505060561b11003448440c02040700f81061496252a13091004140082074140c01b02c5091006000300340008260640380c0c030041c000680031200c00000191760100c5170621200404024000315a00d0425051103019504296000c803103c1c018000814030440381841a00e0051084501501841c00d440e95200e009610024504030980418000f10041c104e4030400385104600841407202c0c50720301a00d006190141c01071440381845801c0c000040880e52191211840707903420346901c007040d116010f09030315007080248010301b1031180c0b00c008204680c0c4030b290140314030800c0c0c0b20141d01029019a007901c0e54544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 268863785 1250 268862535 268862537
    0x110304051506011407020f0a0603140f07051b010e060403050d0b0a03080f0717030c04050a06080c0a030c1215050a05012d09030f21080411100504081005090705090106 73
    0x1300485401944590014103600b4802080c20760f003401d444022607600031041d0300070030200340c2d9800880407071240785619540c011080c021400d4030b841c019901900a0242d10b40240850441950b0011000030950014500c100848100c03030003450180f4004103203603c1203101082c1a814000b002c44a418003040d0f13841540d40c02150107041c01d2070300545100301c0d0810764050b11810307048038000b181074448000a41c001c10350300d5861940ca900b0a410f01a0b91681d650083d0104051790041001070286c1c00103990101d00c3c146004504a0824203040300d0801c11104444200f5240095052141d0059040380003150400d507141c8030b400c0c0d82d03400151110f000c221000c01d2500e400501e0310904c03000007414810080f03001e041000581d40c80e03403181c940c106c280420469142c4450b0450381078034032110710800208442442e046445240c02d698410400d0240c04045000707100c1281c400d2b88090188040d41c1c060407914044031852802c03840c0d40000303070101307507601c6a41d8020b280c40440c51381440c2c00d6640c1030701d0007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 268865035 1250 268863785 268863797
    0x6010303030e1906020a14120c0f0c160504060515071e0c0611060f010b090d020418050106050a08150f06010315030b0402012a02010e031011030405150601 68
    0x2940d20154058084040c03035140a01a08058039030181e00180100301c9607004450050302c406205201034a01d01568940444032803090001d00f0400405501a581c44801a03401c1d90700c40c850a041a145406050391654407801806c101c0c40418000c0410941160300488051214a07558014000080030249001e80c045808010120108641140319010881115190840c00c2c2c15900d4074902d00940e41c01440020b40c650781000c0862404110003904584607414a0f2440c0d454009a282a80720b0030084601403507154280c2010b540d1140c3c80711120046401050f0312050b030342c0c50402d00a04180c0211032050924502c0071074105000514203c19001401e5a03a0442c2c40e49450420480e40003005241016150f1610030074524412007442c1c000c5206542d0343c1c4450400d0710000d80241180c440701014140d0800440741d81c80418415a03d1168080c2411120b5901400c08a41401d004507868500035040010840b0340c01d0300030004500ca54019000d841e00b02850500400f0081d009852150000d51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 268866285 1250 268865035 268865039
    0x5060f040207020312040605070c0f0b070312060e090106030203010f05060a05011803020d030e030c191e0305060f0105120114010b0a0302071211070e130b0622150806090601 76
    0x1001da00814107030380028111121414504150246680550030010000301c004c91000700b000031001d050006030a03c1601a0210b40c00d18003409070600684001804100002c021000050800d61000c4054958084100350524084860398040d02542c030040307020b586800c486e040031104034455603005000003080780e10340616150044907540304220000c50081e1801e00d0000060340c0b0500f4a2080705c0c825142c0d80d0010300e8070f10400d414034801e01101ca001741042038500000d8680303e8100030655514080490a861402c3d960000842d660781006205104120a024045084003540ca04071942100c0c40800b011800c6a03050a132fa0516058101c5038032000b006200c0000602e01030045803c140c0380041c1400c49070b86031788240605154220001c071303004103985a1008801c1c001c100140044800050a03402c0200b00710f000c03e5608900a480152004003054003a0f030381e20545070405456043c5288440c4170f5604990060070700101c50304055030000800a000d400204901d0310030f40e500d60180550381c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 268867535 1250 268866285 268866289
    0x1020c041512050f010221060f03070603020c0106050a0806010e070504030b0c0a1103160308091b060708120901020d0f0e0c0904060f0c02030304050607030b060d0e2e0b0405060f 78
    0xe0349284040703d81c1c1c0192a001442c0c03080034030183c100c40540f6a1204a0f101d485000d024a2620243c0740600541d0000755075404c945001403d0021a0383c0c0c1d00e001a603d24038250250700404442c0c002950006003032000140e070402c001501410381365840201034460325000e030b091307485105a100050495a0b8000040e0495080030040c200f46000e9003001d421103040480420700f10351201072270310031010b1003020703080c241a03011070542d0b4401c1e0400b0003050380d90b051403469007164043c0040c00303104020000c3c159082005031015111300b801c1c000b000181c42c0c1000d209c15030103900103800c5403841348d1410381e16820740d83c40c1780107809540c114003000d40510f0781c60710180440c0c0d170802042500c600341c4682c00e5543c10b403420711501011700b840e03034065030700c030304080c9880c6041c410302800c03040c00c150800c1030607001079903010111285680c2d14200002c51100303042d6854140440d00d49a07103440c014a21052841d11203484002c6407190003158204680c0c842c4401b00300841e07070103a41064019400c541c0805440c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 268868785 1250 268867535 268867559
    0xe0916060c0c05060309010213050324041401020c0d1103040b030105090a0b0316030213061a0c07081504060c02070b03130804030609030f08090114062e05040501020c0415 75
    0xc1d402100c01e0000c450311100460116401556a01e96681d0700080d1100c518074001c3d60311000d0903007107001c1d10100005030940303107001d0004c41d10f08080c034240c070740400c00f040180300c0a01c1c20107103001c00075900e801c5580341c401d860b009131240348004036000805040c803c0301e0100481e01a201d4802c003050540e400c0000344080c004005040c2400c0a40d42c60382c00105a8040000004840049400b00b03500d0382944140000c44138840c1d044a000d6013044001d0051444448084040c05011505284c1762252207000e24540042e036480380e0b8040c09a940d23825460303401e0321600f41c0714a004110038880c5480c02c031030890340d414140c4940c0003114400d001052034030014082c00203016000d01d4950303041a03100d44a90040340c0302201d044000c0f9202810840301282c2060216a11007190002000b0501110035203003c03901c0d00610b01d920031411185103c40e2203001c00d8096003411030003198080a80c4c403800000d000d81c0d00c0750003140e0141c4a00b44110045207414085c0204180d06000d0050030a0b252901c46800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 268870035 1250 268868785 268868807
    0x61a0304140d080c0913090b01060e040615050c1c091406030906160306090509101d060c0307033201080c030a060902120d030902090609060d0f03110a0c0e091606 71
    0x100040e04100d0340920400c84c021941c80c54088c803a24541c4d549444005004078480b1070071613006904041c01003240d0541c184404030543c80504002d82c1d01c0301c3c0120458100010000350701454100c2804040310340368000b81d00001c0d03400186044007000071440410540340000c403280170855120301c0c0020f60310286541e00840158a90601080701c80e01c3d04101800e42d04d044540703c0d400e600051040e9044600d9004816288034064803110b034101124215607101c4c50000c00441001a002021906941c4241e1040007404000100750300021038490f48105180014040c00c0c5641c03a2010011810050104201d0348c2c0307881c01030045c00000d51171303660040035051161050364000303079103881e1694502081c0070101c030300400c0b90740001d508402c0344100488680003500c4c05020b0f00106003000000d0300d940c2d03412106540c2005625901459a142c215103a1965058048090188100710000c02415000071000e0f00c4203007000042640e20052442c0d614034150110704007081b0560000c10801e0f01489440325 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 268871285 1250 268870035 268870039
    0x30f0c050c10050c0a05010e07050103061206051e0703020918060d020d08130602030316050a0507020f030f012c0a020a0b0a030b09130201120501030b010b0a0201061a0304140d080c09 80
    0x418132070084280e42c10584c100c50705440907519085050300e200710500c844405441d0034241088458106211404440c411080c0142156580c0021411102414890070a90344c203084040d9980d00d080f400080203034016072240c0d03015001c003a94001102d440a50060f1081c2c501903c42c04100c1c0700d94007048001d104050003070f10101c1c03042000000303805001d00b101d030141c11150015652400d20300f0003e140d040c800000441080018810842c400b81e0020850310481d404540140400310003000080c00d1010030750340c28207150710b040e002841601b04010800c00d07040000340e5802048a40700c48554403014031f070400a40c445190481441055003a43c080c083d141d08500e80000c0c0d01c140350002c5883c82c44161802c00107030798001203000856074405440c080700100c4074428002c6c2e5155a40b04c90312004180141100d00f2404a040d045252007548200d008040790f1280d210056404c600d0005503900c1524180c0d682401e6180c03041e074a16000030701e10000202c0f44c2e40c8840c03544c0e0b0b8500c05000742e009020b0707003a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 268872535 1250 268871285 268871287
    0x2150a0c0507030303050601120908040e07030b0a090b0a0b04050901060c050a0507080c040e01200a14040b03160215061c02030a1202010b030705012114010e04030f0c050c1005 77
    0x1010074420000840590f02c80d440000e074a0600100141c10030313a02c805441c1845007003007580d000043c0740c0c8099800700d40c005074190b58540c0300c003007045d4040c00500300101c1d0084401c4200249206040e00705000c1c408041e224000c41584034808620302e072055002d245e81080085004108287c41211185c9165000384240d40c003213149a40c60a04003042d40d0700440c035507030081d0204442e80c07038548150206204c03408000c10011410040300c1d869144840c42d61100c90070041400c1076a0703402600d011882c1c2c00040c20f0030383d4564403410031004a810544071070380e1a4410f20320081e17105000152480c00900ca48120000355640c020030071285200211490380312215509003000180c80406c203042c20a440f542d0114120308200c1c6000b400c440096800038400d5006036001c00040c0d80014a80880300281300c9440b000c1c0202c13540041c040e02103509094017100c01903000207442c0541c08251801184290388007089007104d00b00840c1ea0151491002e00b0390b82041d6000b4406242c032001410000c11941485 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 268873785 1250 268872535 268872557
    0x10f020f030f032d1605270103110f071401140415150e15030705010c230a210201021e07020102070e0c0403030e0603090a120318060906140402150a 65
    0x24268040d21800304e071409202410901c411110070f1988a01c80254500d05a0305050380c84114281e034102044400c0071058210880300810f9120343c10003080300e0340390403940d680c56a0300c28861549a20029003510f180445440c079101c3c0c0441805803480034040315203002d04c0c0d0345454403001038040740142200800b41d034541c01841030707018040041008060f02012002c2e103180040314411048070301c00e1068484d0304a44414009681c11408610360b481e0080100070090400d220314800c24103407005003a07410300c101d40f40c4608200d08030b40495103500120050070303060000c81406901780e000c0e40d50040261001c00c240e021003014100041d045071401481158016a030f0754405002e00c000548410100ca20005014410705030000d07540142e4032000e0b02c902d46945070138160302c0e84612070b140005200d00d030401502c030b1020b40b180e007140711103141c40c034803000c44900d15203011001003092007401c031120b07800c00c8800c440d40142c425085225640241105045844131404280554042c0c1a9603080c004441c1c12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 268875035 1250 268873785 268873831
    0xa05011d09010b09072703120e010306090e03030916080601140d0f0b15060c0309010f020f0625050702031b0a030c03050f0c0d110f0105070f11010f020f030f03 70
    0x500e034066015a200d81c035a5503040511a42d008180f86e402d605404c0d0703111070410002e010031607291118034080c0f0f458078030b500813000101c01401255001052090a200044009840c0800114010a0712404552008400e20800c03070800e82148202c8040b030b040900104034840c070510300140b10b40c90040480d4203505269039004c0d8001c0c0384850541358001e82408118a040800404881d10f56040710b180e400d101c4c03a840c20a60328440e00700c14030304000c81200000c00980c02000104407a41001058602e0b500d0704082da4a01a0500c003a14a00d0108407800495103500a008449103030b078016018100e05c07040203c018a001e0101c2d191681c01c00c602080010214070000c19080c0910300c140080e2004c04010011146804140780529214020f038904000000301c3e041d8018529480956852400800c4240107075000c0c0110f00001c0c104071614001002044058006205d002000b40c075900d201216a40040b6510307052040300304899842084126a078103554809150300280c18000480da500ca030b024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 268876285 1250 268875035 268875049
    0x2060c030d090213020f0f07060902130219141611030102211029121504150b0a12020f0f31030b07022d060a05011d09010b 54
    0x540140c0c1c540e6452a031000c525040d000b401c10312004d24802d60a20f4025007814180b803051300e01e144000000010340c0320401800f500214141600103111409011508801101a52020315250459020800c14090590080105942900381d00503402d04003070410446080010801600742c1d4070a056105101480d80e09000400074807940c084031000c40c01d000c516038149101c0182405c4c2d80c41c0c403044018000034441c01240f00b00743c0603400c4000c00800140305400007030301c64a11252412010a410800d501280303500301f50748100255402c1000e11141c010901c2e500074076024801101c0400c12055810a00c80c03046800155181400189002c4e407000d05520207030b00001700e103120a10013003540c030461500d245a0000350403101890803061403119450f40e14003030207400002e2407041c443c404107400700e108120002c250b03c08600c004040d2100408002d55136940409400070f20304c0354a0014400c1c17003a0b409000c1c12143c1c0c032000001d20912420b40503021200040480006640e500748564582d90b0381a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 268877535 1250 268876285 268876297
    0x60406080d0903020a170c060f0706090c14010207080c120c1f09090b150f0702040e010e010605040b0d020d14120310060201021306030f090c1805100f0b0702060c03 72
    0x529450201891071041c003171034500581c86002103c41e06001d13142d500401180040d0342c0c20080380c019560701c2e201d0050760700750b00070040e0181030b282c81c1036095410045000c503c03000703031135804c41212541d4089500480e502c50311400707000115080220b8000b5103040070303c0200300041c10b900c01c0d01e82007510341300800e240c20603500a10f4541e00741d031070660714000e410580d010301504c0030410038407800345018082440c07030032050852000340100050882c1d041c4c006006035076125600405c18070143d03500b1500117000c2c14082c03108400c04e503c2c0074400100d034074044c894909540806000304d40c01c0300c12602000031600d6140c900b980c0c01001148141d0b0340840a004015554544912145c2c81c1e06100b00ea20900d503080d41c2000c019603104001c20171079681c0d611402e108480c018900414000b0b1800d94443c00351061000080c8424000100030400e14609400c0b02c000e012070303c10800c041da031112445070241407a40b04104e9a8205007a050050074105030040103080d001a280c00e00d41010580607601c0d60f4426 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 268878785 1250 268877535 268877537
    0xf0d11070b0601020d020a030810050616021912060209030312040308010e130b0f061302070605090c090610052101081f051611240a050f1905060406080d 67
    0x140030082120180140e50410b9080c4001c0ca014002110080c1d55002d9501e009400c0c070207120006604a542d14880c0d601814001d0310781900c4e20341d840c140802c2c007184d10004a1003004890500d6581017032504040080f00c0c401180c00320b1501d101c0d101d05000b5400380110f5601800704100071421040c0304203000780118400da8514a8661401c9111220729a01414003072081400b503041d9008182c40c00051500418610644a200c3d2190030000d5070203188031501c0f2141600104090060002550102d031040d00e0040036244c0c2c100c4d04004200d0340c2d503422035800e07034003c01544260402e20310642c041c14039100c5160420300c001e11030103855601800264030040303441c0d110a003010300c6814041c1d900b6408804240090000f402c000820355080650041600c0030481c001c0c8408032010003c000c2c0400076071101c658000c000195984074801d03c2e204803084002581814040f0307106010740e40c10140705d9441d041400000811110f0075070f02421340545281d52094850794041103405051210b00f0101c401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 268880035 1250 268878785 268878787
    0x1e040510050706050a02090d0303050a0b0a0801090507051215100302060d0c110c0604090c1e080f100e04020105070812071112040311102303042d06020f0d11 69
    0x91520b0802e0744e400a1803031203038500600c45003c0c42d07200c40d1145814030354541008030310340d601c4c00c00440040c2105072441d0380c080918070700007503c15010352000006900400c2600c10744d60b00e810a102c4042c518603000c110030351003e111041120800303c00c16400ca060001c402d00d405559400042c2d0580000b40004002c51b030b181203080c0320542280c0e00080f0000007501a0500d0407030707030000420500852042e441402e490344003401e94a072140c40b503144912103500d1030f040d0801c0809001440c130607044071000b24414201010403103810035036846a00301c420410410915544e581d00444090b0403500c8215a9900180181020b224030300001300d114005d9070755039071124906038a00c1c501e00b000355604d116021000b00070600100b148554603544200c0f05075030369521600000f2003107602c040f0404a0141c00b0310300710a401d246e0b21600b8015406079025043d440c02488940c081c04084040f819501220905500b507440300103000354000d8031200d030207505c0c1a803d12003c1c1807541d0945002c3e807403010048034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 268881285 1250 268880035 268880047
    0x20403060c110604030c0209060a0302030118140703080301060f0c06090302060a0b040b0d06020c1207050714060c03160201110d032c0a0311010216051c03020f1e04051005 75
    0x251258842142c1681c0c14000c00340307400e054134090320080704c1c104064015203110000900913203408155200461340a8001c0190b00c68500b49144c5004800400320b4044405880c8121200c80003d03040c400d0725000024245182d04e40442904e417890707034540704014014035203490310106403181b0803026030500a4003e08403614211410b002180c40381541c6600c107529044801d1410f803160498205025070000b0b0043c5e83c0d65402c846180f81c044c0c0a0141034241c500011071004004003c80c45401721100d03102003030789040300441005540d0045941ea45001c1c0e1041c050202008079200d8072803c4a8018103180002d4103159002504291402c54004042a16102030342404041c401c94050f80c1d58a4144007004034070b82001c03c80e121b20162601800f004141d16118650381c03002c7d41140c400600100c00d80405414a11340551503080040214000d02c01100650100078040d0081301c60090301c580c0b203540b421014018503140e04201000384900030405005c04249a2129184003a6241c0a40c583d00d031654 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 268882535 1250 268881285 268881287
    0x30c08160501050f070e040b03030d05040f120c030f180b04170f03040f0302010807032c0d0e0906010f030e061026100203060607060501260a050303010522020403060c 73
    0x3d00250026058030b0b200c01c1000800f90380708a010449160444011510b0380b102000a49540107449500c0900c030300d000103110801008a20304131500b0300c54000c007900c41070620010f072452444d255000d80801d0520904c074124034810071014405042058441030056144c008280060300302d50011600e412140c03403c00001c4000300207060910b02000700a5103060b0404c500c68502050030b1000070706121220340030424150183d0440e1001308040b10300c8600114141c80c1e020541381d0a040c80c00c0d078030b028070034200711300611840070002c40d0032018000006680b1a800116503241d082c5e94482d08040e40c1c0e10708280140c00510509019244940030b88200c1c9050049149030307102a41900e049040058803041041600803d850413a001440130041c6c0300d54510005c94818460454001c4c00540f500b070011441c0340494034950241c8480c10400100d8904070118130ba519031841902805581c801c0c401007019142208402c43c502d0b40c03c24000b03010041c802540020b82e045900125445a00c1c0c1a581400e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 268883785 1250 268882535 268882541
    0x503070b0403050d200a0309050a0605090307140f03031204120206090c10092d05041e05040615143a020103110403030302030114040504031b030c08160501 68
    0x64640d8264851500b45140e481a0344d031035a0403d104180400301c0c080081e1104c0c40c403146400c0c40000c00035512035003080d1a0080000215002e000d1140301d2855020440d10b1065040e00c6d40c41308050010003181d82071440c0002d0b90003e64100765844007040a10f00841d803420b10192034240c158000f03a094a080900c0c00c01400c000c24103c10086501000801407640380024640074480015501c0130f04085403004111002852a04285828026014130700e0566600140c03000001c0003241021400383d80711010001942c0050308a401481c011030380d00100400c090340441d811070b104600009a26000a09400b1001e401da4000004124031440c1082603045c04400c0c18030f640e444130f580074415011404030251441c00748800c104031881902c291030459000b5400018500c00e42c107001601c030b658030700c0c00902950090103490130360404010840341d1410540600e5020742e505884c0c800130100d400d0340703020451040316815401c0082c086ca0807004500180000c2031449901c55800c020740c1100c0c1000c60079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 268884892 1107 268883785 268883789
    0x20303060a14011b03110f161a1e0a11282303130e0106050901051e03010909120e0109050d050106080f030703021002032404091209050307 61
    0x915801c0f00d841c6e10081c0300d1500701d5a0b005000038a842c0c460f112040c10311002450000c0511620b440d05802000040000010a0130282c0030b030500ba80c90395003080307114100e0000040030b1203400c0c0c0c445184d440c802c1001008000d446080d00c000403c100140121050603862000c2400c00c025441e441c1c0a140c204641d031659081c2d05012420362246d000d22101003503080c881d140010241606a0541c0c125829a101c03a800c14280d07200544990303204817103280e418441d036010034080d0120840034601a10a01d1000101c040c2e1a1400c407a401d138170601d01806002c104d1140c080da613a40030041034280c84068074556030305071032481e000b8003600c0c0350b82100382c007801500b802400e00d1800101030020240603908480301c5c40c074004044030883c8401c3d100c4040804002500424505141c80d0b007030040580580300003501106070300c6007410261114911030006400e14810000c5207410000000 = true := by decide +kernel

theorem cover : BRFrame.Cov 268705035 268884892 := by
  have h0 := BRFrame.cov_init 268705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 268705035 ≤ n) (h2 : n < 268884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
