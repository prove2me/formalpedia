-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1896
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:04:13.658798+00:00
-- url     : https://prove2.me/submissions/32f4bc0a-e58a-41d9-b94c-49d5a0393061

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 340827338 ≤ n < 341007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 340828588 1250 340827338 340827359
    0x307080a0c0212120d0b060a020d050913050103060c030c1e0e04090602031f0801060b0d0902150408011401050409020906040908370206010501050f0a09050909010507020f0304050a1e 80
    0xb09043e072105181d4441d6485c28000485d0060010940714680c2401240c40d80c1ea400281403030501254201541c2c0c92040d040081c1c6000c0030301402c20304603410f040010003000f105401c0300981144944060003a083d400d4815500d842280401113074000c20610007501c1c41d07208000007001c4080c05480003610244a459503020b90348115a4902c031103104400c02c407800c0c440b01d0000d00003041d010008001460074100d049580e846045c00181c1c1c91600c402c1141e0655854507085ca0038400e0a030305050707030382c0c2e61505400c0c084c00402d0144204000320000015550820707010b603021007940200b00c480e256451400f080010118050113484044081c400350744085400b000324088a1481803206451003041c17049000c5800c0080c01e40d400315000701c40104400c0c0d0700082031b95003410902c0c82081d151070941c2e4044554044c1c0b80e001c40e40c0103102105004d400d00040d80290301510050b42034491b203c00c00c0e0032082e41c0b44507a01c126900403078030344006c200005a001c80c1040405820f104c1e0011159501c10b40f04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 340829838 1250 340828588 340828603
    0x61a090d08031e0c13120c0b03010e0114030d05030c0c0a05010c0903022b03050d0e0109152d0207020d0c090203010e0a050709030b04030c061d0d020307080a0c0212 72
    0x14903d00c04030f0404007402e00e000326295000d6180c04e401481d01c560580740240c5003603248922a050b482c510155402c02200c01e0f1503802400c0c2c1400165102d40e074400b81441454420302c01c00854074000d4141071641d090220b1030010910440e201c141c5140c452200081c0c040c0e0000c0c201c1c040e980104194000045c2c4203002d0651400700c259920300c6a2402c500400040c40c02084510102c00d01415074245020701c000c1c980c02100740c1504041d07403920441c10100c0c01525a03541c100c2090751030b226600e010480c50b0900c017215054480c80c20020a402ca11410741111118903418020710304c4402542c00e00050798000b032141520190924040000c0d07035071600701c40902e681211400c6030300400144802101084950742c042c0361f5030b90600580c1018000903200740c0f224040a0048800300e80001c051601550442c2034003580600b0070042d881c850703a890440134000d485415810f00411994000041c030000c161656541c02030000703440c14511200075600c4000703030354003283c0294510000c054140740500001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 340831088 1250 340829838 340829851
    0x4060b01030b0102160302061e0c0303010f0b090901170106080304080a120219030f201b031b0f0a050306181603080a0e040219170a061a090d0803 64
    0x1250044004001405458007100c0703550466024444401190030408945000c80c1d4050b0b601580c0d881c0c07420002081007610503100c03a41c04900146d0507840f5480080250b040702d0700d4040034006181c60b0350084800344034822480e40d10909250050100c100700340030700f4652050b81000040c08aa8981c525410340d0407507440441160061064502071180d01c0c8840c5446505a10140440800c0881000305461003948050304002c0d1004203250500d002c1c4030692040c11800e82000300c43d058200c0c190740c0d01c0b41600301a401080b401c0704210264200040da842103103800c0e40d0030010444c248405d20841c0075210300032076404030642c2000902500d040c00424090b1015441c1064640700080c01c9515000b4280900049074890803000c0000c070710000f0590380038107494942118520440300018000c0c2c010003070b5280c0c682c07001d0088105100d411007440814800107140d4590690354040c0f41400301c505c513220360701481c11a0202d00c074132220760000070700821070000d140748000a41901e400c105a0012201c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 340832338 1250 340831088 340831091
    0x605010302090f0c0406051303020a080606012703140709050c0c0613080f0307090e090a150501031101051c0216021809070501180e04050d0815031b0d020301050406 72
    0x40c019800c000604a501006403c0b0100580c00d180b20302d07520a2040c0d104200c10400c1c041f4011080d9142400d40d60002d40d00201007400a5440d5045a5260740e4140d800e01d000c9589205a03409401c108626184900d442b4101c030940d0500d10380b10240184607140d0800058080d815004c03803050b82c14401c25000c2c80004026684070640748850310324041c405014900e610207940c1d00c10740081d2000c030032100030300002c0c0b00c4e01e5182e884058013590824a1b40d0031003074407904020704100a83e2000550031004500075000c1144800348844404102c0d6400c0c0400303041c10340e054203040565401400100a01314a450745101c0c05100060a04100d170069160001e219500d00010029803510710900d4900d80800e1a0b010206d08001c0a07030f60b07869030280301d214140100e001d07920307046030b202d914a200100320408082c0e040c0d140c02d14015131140c40104e1000d001c2000b040100d080305010098070304070211b01400801071000080a01550054420a1964428500e582c01801038800703016060280b80b04800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 340833588 1250 340832338 340832341
    0x408031603110102031303050d0f110901033614060103051e1902120c030a061b02030408120f09180406064109161202120a0e030d06030605 61
    0x60081900b010034401101c203030f006200b07004d0310030b642103d2203400d40da240c2081680c0700f906030640e001030528914420583d62030309020b0901c0c4071416004000140302607904004002c45807402c42c4545049d08c1c02e0036941c40c541039508044a40a0344485d02090064802600402c0b020490700c2c9402800d070011a07950b00840a410030200018941e900c1801d50b91002d4554641034262807807206a103414040c0c40362040103c010b00106090003000c01015028043c0c3c0d44002c0350741003d0000d031501c80c8103d002c0742c0c40c0035184000700d403001c416a41503c80510207040b049001c03940140f22a0440817030454040c000308070f6080b481d030340c0000d55400c004200405407480e240904003201201d16030f80c80300402c180c1410314090034000c0f030328140f440c500300c408502e607102c1d00005001c400030018440e0250410000424404000d030075803040c06107102d5503030300e101945101d22600026801010000350500b004140072400c290100c0d005810065590001c4a040406200d00041500e0080d8016200c081d076440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 340834838 1250 340833588 340833593
    0x702070512030903480310091b031703041a09010e010f0614191e03050f24090c0924040204050a0b0d0b030d050a020c01020f0c0d05010204080316 64
    0x482800c154000311a02d61041741c803030403400d041c50085401d0b09640740c001d400340241026502980d8684000c06400c4408010a8984000c02840e030050b00392983c07404000031881d0803441541540503a81d00161075922141c200114a02c9500003400454088400c800402d100c882c48000851289034107400110300c91140c50302c86400c4920000c2041440d90070100140002c88840e1409410004240c6224010f0034060b480000102c40c2504850111144151000c5c28a950194040c0540b4060302c25aa414100c0360511075803210710040e80307950642d0401c1b6407a0080402540b240d8020100020344407034005e824000384044004032000e0f1080d0303841c0130340b550580d11800158a02c00c101650118074160400001844548040c0f041071419071001a00c0b006602c01600941c24004016080702d2026102241c0600a6040526844018450710704040307403540c030000e0301d40c0c000700405000e01018500f41c0140008088641d90942e2559000c0000261a80b0104001c1062031031041c4180780b01c00d07061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 340836088 1250 340834838 340834843
    0x209190f09021c030e060c0f07030606030203060106170a020306031009140c01080606070605060d0f051506010c0b0a020c0a0b040516120c050103050a091209033302030702070512030903 81
    0xb0f01c0180d0303210307101d031108000640c0141c1000034541e800c803005030700c9140c00645c0398a88042030607010103a020703603c0300100b00410354011205803842101036075902c2e038032070604031440b92101c0c6c2c2010350304283d58081040080c0b19401541c00400c0901900e03448020410b01105440010380120745c000110340c1d195440b510140030050510400f440d0491706402d15000103003140c007820b00040e04030350781c58000c2525940c0d068038010040d0f5202e10f820a6440d120709005444e02c180c0810070460b68401c400091207176108101c1044180d80c082c60058142e02c0b4894920000d401842e2425030700c0c07246460a0000c10495240d4900c5503110350000e0250110400c0d0002d24080554442c02c1e13040c07005181200026448644081030310030a20307000503650f40e0403001501400300304c3d5000d8541c491000e5203032111030b030282d00301090b41c0c0210360f80070502e80000910100102e0701d10f1807028070041607a0205200b5016002503400550034812640c8654030385002445440f025455443c160f07000140f20758280c2000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 340837338 1250 340836088 340836109
    0x5070f120810090b0904230a031d041e0902040209150d060504020a0909050903160b18030c2107080f040806060409030c02221109030106080303130209190f0902 70
    0x31010f05205003a0620049001301401800040c403040303c070200302c0d90303e14030101464040c1c82c05104840d0301c03590a0501919801810300398100e81d00f642c06205070a82010300500140072a1aa10b002c0d035140c00e104a00c00a143d904012a8001c1d002c011002c02d903510480c030035a28032040b211465030f071100d03240804100c0d039003a403000e030049005000d03080180c0c1d000314503030007102c20444003c242941c2e00400d582c25840f41c0c4604081000c4048501400e121b80441510311032030200003160004409100c9a60340c9008200541351359521a50580c6030858005002103207580e4003801080c109107869680214039000300705448940440400c04100f404002c126254111000b61f03020000c0c8044d07500d00402014080d0006801023641d483c5040082c0d0503854002030100070403004209044203400d80301001d601c0310b1455482503080400100e000b000c0801181d010303004005045da20583c240e424804846402040044059508a44400654424020800e03894402080000d44914901c104545940c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 340838588 1250 340837338 340837349
    0x9040501050f01140f040b0f030f181f0e010903020c180903040509130209010311181e092506080f0609040204020c16031101031112010605070f120810 66
    0x700205088241c1d13000b401c0d03c0500c4000c43c660513520074451040c1aa140701d6503000914545002450180d00017800000d035001d01e01b0038110001e65101d0f80c0b00050300380c0c0003100c084255007011203e01c501d9450443d04184210603d6004030390b04e05482d03900f80c210350210b0f0701500503070403031020400c4c0c40c6031805c180d0b28600c04841c520003060500c2d0000503643d008034000c440c060f2020801103100715200b6100e8911441d0b00500c2c80e5000e42e101e140940c10510304141241c024801108460311f43d803d03c1c0045031088121040d40100080052800a82003070058900e2105019140c064100403078403405034900740300d0202000269a1800318028401140100203151400078281403050710382c2d80003d842c0c1c0150f01107c01603102e60302d442c03100341032040c600e52000108128a400004000460700624403a0310300762820400301e28070882c840b40078404e100c20020301c1d011860052001c42d0003031001d01441d5002c0e40c2e10503080082c6030f50f07840350500201410307008201140100b2102d6070541040401904 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 340839838 1250 340838588 340838599
    0x908030720010f0f030939051c020d0f15051f0b0919050a0914090601080706141312020a05040219050d1404032106050a0e0910050703020904050105 65
    0x3c00c2910000c0003089500d400380308064540d8810010b201c00041084081c01c5c00c8810341080000c01d00c0d60140400c080304980300095a890340004451401c80011411441c2e800102e01c002c150650801c1844c04440000710b500e0b046038442880464464081d00031b9a070b844400001d12420540300d002c10208110388103041449680200784001c02e030b803100740c50b5014070588601124817060710305c82845150300d800440c0c0240d250400012200136035008035022401401e01a4010b0300e80d29111500d5031424042c2c5085544022002c00905120304600d00d07014042410603820140300c0443c245042c1700e1584000026205078503460309601d040141000100700c1102d046142c486c04032444d00201e01c0c0324000d40b0070701c0004551640d814041e9080b02c13804908042c1420500c4c40d01d450058810408004150900c002d80e8001200c1c0c084c0c07910507c425501d000741401e0f140340c642402501c8030314005002030700c01e02858050000c0f0b804103028040c00380c2010307100561216041000d03c4100c0358140d00039031080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 340841088 1250 340839838 340839857
    0x605060304030915090504110a0314010e13051f1d1f020c0a05010504080a080109020301050604031203021303050d03110f0a031503080f0316032a090803072001 70
    0x83e0044484000c840320040c82d141c41c1034502030181e0b0782c02d000340c0c01582c2007410b00c0113407172281280c40c005044010305500c3c108004025000998100042405203411080c1c000c80801d2040010304801e203980b621400840e9034207500f80301c0da00018001d44080083d455107072820154041158154415000030315001000c200d102601303c404010002540c00c4034460340000e00341c0f0442d034244181d61850360000024015410700e468202d40301d40c008101c4100041140c0d0000c0368000071402281e04039107004040034101411600c88400034070140c0d002206050f8200401d00400d850340e000d41004600a01c090101001d007108090709403005491080101042008001c11205001c000d0722200741240c54001800346c0121441c0c0d050513941d400140c041107003ca000150401135400031440342084603880301c81c43c0100c035000da0a49140880f03500e100c3c0d51080b45c469010300d1b20824401040880d20741030400990f200096401c1d6400f00f44265580004030302950f03551810020200780f40082813800ca000e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 340842338 1250 340841088 340841093
    0x18090317041a070203040302060c060906101406030c040e040c06080c07020901030f061d0f0d0806060904050c2110060f0215092d0c0a0605093a060605060304 69
    0x110304614503000b40d030245040101e10101d100b0400c0c0d40145501400b0b0a41e10a4541c5e41c3d0759a801d012202000c09204540000380c24095214814040324490103180720342c002840b04001031900010b12611950b80148000503180010241d407600aa00171401c16010500b040070080c40b60b90010242101104100907000058850424141c11a03410200e410403914480c90601c015040f10394482d400621021018101182c001c1414108858107004607030b134100c1c01d030790140c4151034112083c1c1d50225082c008407810341000e400c07041d0710002c148011440e2186041120384040356002d19096005030f4001040000c007c4100b150000d01200c0c00d010a0120700e1410095403440e80f04000d40c0141749440100355141000c000e4101c10034084690030024031301004150011000001203a0340c680f081c20b1903d0000e040c0790b28a00156142550390b02e2508170510240070668010000c880048410b03400780010185030203458005405001b20b2000003001c4a0034458103454582c1c102c140310320000c0003400300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 340843588 1250 340842338 340842353
    0x19030b031005191d030a0f09060810120f05010c020a1704030f031103070c031203140f010b1b100603120e060306090a0b0909011e0b150c03041809031704 67
    0x540105401001c14851113145000000380110142c5002510010a502d0b035010307002030b00d00b02d004005960b2200321075a5280102d4646070241d5801c170a03030040341c50502c02050881c001c84442e600444180b406200541d9078282120b140101344001a00210504020400b9194120f10166495104c1d0b50810303065403520011158454802000c0c003c0200381034514020601c01d884d40305030445a081121542d07030503d0f1003103850120110300041d14208400c1d40645455858030301440721604d00c138480d6802c0070b4451026500ca00e1a02c031100c000d44040d45c2c11500100b0802d8884100010041540c0c1e01d0340c40d000c0200c612003000f070000c0c025a454810903540340c440959600c40380031114201c040d287c0b0115000103001070100c03a90000c01003000c0148007401500180b0182c4440d031071f070b0710680181c081c04504640700760140a9021506080e06920711400d00702800c01c8a54101c1504e142554a0b40702d04900c04200c41c4600c02503889604d00c50074550480c54042181c0d43c0602d00c00480e203815070301d200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 340844838 1250 340843588 340843621
    0xf02071205090112050c07020108060102151f0b0c030703090b04080c240d050f130f080717070309030203070905190c030e031204020f0f0306010902030a0219030b031005 74
    0x108200300450071082d80d82c071070018540034a1810904001d5420030740c1d61483c9544c0000d000380d000c1000d400200b645035100107610025590000d07040748041c1c85a0f081c0d03001c20b04942d00d02e540984d44034807002c00d16884010042034a42c03441d50040d0355580c194500035001e001190b12241d94110f00788410480303403201151251005038222501c90010310151541d1001e0801c41880d8649a03a021950707824245a80e84018040d94154101c0745107561f82c04090400c008146a00400301400c00099100142c40000500003140c41068044050640b4070303892038840d000b5150641c00240403101c01c10560030180200f00c054454030800344034034070b0700840000d030001040c0362510700995507403000b0711003038400e911103181c543d1040e040c0c0c1d0785c1b0b40216144005012003940c081e4400c11030707500c210101303140c030281c45ca80341c10340540030b4a01e9030701e0410103070000d4000034010400d09400300009581321204651120511545407000601e0351108001c1c5440c08644421140200f4905818002240844d283c1d82 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 340846088 1250 340844838 340844873
    0x50a080109050319030f0216030e0a2303010608300910120b060426071412011e0203091e030d240b07032c100507050f0d02010f0207 58
    0x4240e644c13644001280204154040e8140312440455001c1184001d200b030704000354003e6031501c0080e10454200519010780c1e100d50144034400c0f5090041c1d10300c0211600c00c50510003400052900c0d518050a8100181c3e00983c1c0c0c50b5003000000d03040c0102d4905280e800317407011000858149803001d00402d00c0c2c91a410282e80912040b18581c00b0800c0007904070f0801b0781c0000e000661a00e03525503821440690040002c0451412014211000380001130b0200845828030040d0301c00c6e502400610800c501c0124001034076548480b80300f50100c50201c4034032004080715030010395030302d404003a80d4284081c580526032041c039102004500004000305460409104810000d009103903280e800414054160050082c0b0352900d400282c41d0030744070041c000290207511100d09248250241c0c00141505020b0506412044402d4071a41d04025807690300301001820641d02d4000d180c1c0304d003407803c105809801c2c11984052912141141c1c20700924841d601380c6281075007815001d5985450307000035080c15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 340847338 1250 340846088 340846117
    0x6030c0603040f0c06031a09040f060504020303130b03060a05030c090403110114010b0903060c040e01030f030509040f0f0b0a080a2a030309052403280c020601050a0801090503 77
    0x41000c0c05400343c07200200d540e12205004104d0754420024014140d1408649004600d001006070641440030748284182d51040b4103407030b18419540d40d0780040030090802c1c1c0c1c1600c0184031b200340050a250900b0040c000381500141caa29100d0100040c8941a41121340260002100c90520741c03103c214884d04203505041103010180740f4180180180b030101c19804082030140300018183c2406070081094402c181c0a0310160380d103002c032085107840b0b540f0441c86078031030001c0100b0114802c0c0d500301d400c1901c01c1c5002880c054840d80050165450404c03d0310301c5650700d001003001e6046e14400c0d420301c00030580340c44141d1441c1403c803a4585011500c05808581001034500d4540700410b44d00b8562610481203401258880c20014040341c10b90207900e0050009038405c07035030600c20302c0d50b00b8484607036440c042d850f43d07403003d818040706106a02220003000200c0b10b654a144000d014040d8501c4e00c0c0cbc0d000300981e41c5400e04008010801c2d510a0b00c050340f610041c0d01c0400d40110451300c2ca500300000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 340848588 1250 340847338 340847341
    0x9051509030d11031e0301090509072d050904060b0f1e01180521070e060a0504090515090a05060112050712050703150c030e07060906200d0c12020606030c0603 70
    0x43d1581540300f085040c6600c6480b00c0502402881c007000a14141c9030006010080f42d80d5081d14241d42e94114041c000000c14040b042440d480700441e1003401c040f25064140b24900d603a9404207501810a680c203c580d03640f00c0d0214040f41c140b00c1025071502030b00320380e40442c0300c1c40081107807596024021943c0c1041032030054a00110101c1600c4001410080c08110a054903900703014074000e810903c1e507030b250180303000c001b031010000c5c0c89550140000030401d9966903d46400c010040c50300e402c0440d081e01454081c0ba0018041c00e141503c01c84548028203c07070211880c0c50317820054143c102400820302040d8280105000007002d605981076100a0404080039052091420746c00341d10080c031000729101401250350a45d000f490285096403414061100e0941c1c156403075080c40e0040303c00250050300c007001038500c1018003014551080d0080d01c002040e1a25041c20710040340028000710311119207040401c04e900e80800302818880c4081d0031182810800aa180c820700040188036090220 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 340849838 1250 340848588 340848617
    0x1203060605090d021c140d02210307020f070303030606170c0d0b01020a051603021c02150306060f2107050c06011512090303051501030c02120f040f0609051509030d 72
    0x400000341c40c440102005c50000d440e140612450783c0030780342c207526401016a030641e82c07400058450f011480580020f0101403a41d10040c0160300003d100c01c08602c238000000d070401c1401e0207200e01031030281c2d8011941c14203040028140000c0c9207805068180c9410420141c482e1003402e68207001c0c600c80c030100f401202180100d04d42281014040d00b5801551560700f082c203403401caa5021a0710035900d5180d081c9000001c042d003154070302e1000c0d4100c40004080f002c011040e10066030b020324000e091300e040000c0c802c4615400d80000500088030080300c0c01d81d1180c2c10300d0010591388100e1034a059842d10021070303090f44c1c40c1c49040c4180e0a080e4008420848058064040d080105104035401c2000e0346071814000e010b400e09075400f0a45155045d40448030354030038000c498000180b41c00070850350320550304102d469844059106040c503000d00c4080340d00302c810000360004120f5030f40d400f40054102002c200c81e039204030405d809200c808005503001902c0110303a0000d42945030420b244480d8448 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 340851088 1250 340849838 340849849
    0xc020d180f260d0e0f010507020612041403070606170c03100506060f0f0a030506030d0c0b060d02060301060918091106030402011101021c1b090b03101d041203060605090d02 76
    0x144156141c00303400151000e441e8020740e6009120000c403917408101e8403000040d200d5225031400130b508110200240c03078000a07201301080d0000d00c503001c4032a220810a000c01d0454002150031181c00707485180130051400004421581d4030020785c0605009016100003e03610115204c0d800d283c06d4a4070002921a031340c0c6003d07640f54500c1910b00a503114003508006043e5802010b505000c640b405011038194200001c92244407640d940312408914484d40340c070780c00c5040081c0b00d00d40c0075070000c88640040e140c10300514001c140d60344071928240d041080c00540c0344801440c980e04503182c14440004601c11444071186202c0036030314555a07440d00e0004841d40120550a40300640c000190202d00c0340042d059002c12903854070080040081e050540704404030242d100c0c0d4006582c230042400304110907001940c1001d100c801d4021540da031801980110030341c150512980c0d84481081000303102e101c040a501003003403071404000090410801501c540500e501c00390090300c5082c400e00441d03c45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 340852338 1250 340851088 340851149
    0x6160905030a030e120606011b0c0503010c0503061e0306070e0609040e0c10031407302003040b0106030f0209030f010504021216030803190c020d180f 66
    0x5001c2d200c0e001d0320b03801d018041e844030041d118001c110705009150990070224039a8045c3c80142d41e40003a80c1c01c0351404050b41a19240c055a154003560300025280d50f0074032880010010329121282c881c035091040041c0c44540220203480c40ca8003080b100c0142d47c001c10026031201c0c0380c0c00d100c0703040034141d80803900303c3c0105410380350002d00d480c42c948981030001400f101c007480308407801c04031880305070402c4003a207014400812207400c1420120341c50324010654056001c0c0c10403000c01c001644140c4034007119030f1410024122036921040c425900480002d00d613040404010a50b282d410590785541104d001442040101070350740d481b00c00d64020715012510607880c0141218104050700d178419008080954080b40300d089142c0c0c007041c0440c4082109002c00107500303000346130f541c13845d11840c2c1c590b0b00040c40444141362441080c0702c501d506105048007201260300800050401c4030001d042010140c0034110443c0c0113035000c100354614040a10151110702803001c18a05030480054031540d43c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 340853588 1250 340852338 340852349
    0x30b1b0c1515090906011a04080a0212150c03090d03090b0601451d04061823010b0402180111150708160906050a1b051902040e070602061609 62
    0x20380d05000980c400028414103031031134510100d1202c40c051f0700a00c8103100c2c0f486082c2d210b801c5100d07001d0262400c5080400c20758844000d0700c0f0905003141d01c0c441c442c441141c0c6103468510200502111a40410000700020744508081148804649614441c840d009142c60304102040d044014204601422840140c00c10312a112040000b08082d0451040d003481c8110500803441e0001502445001801e5907003090403c0220740303480350b03100ca6018210aca0f4042c0d00d003518201005002440c46510004800001020303c040700792414959402c0d90380a4152a1007140140050350b035000c00ca00346284c4440007424000211480190754505018044031f54020012580c020031800d81e400502c220b126496403110f01466054802099900f0091030243d0000600c003400581112402110000606030000518400d07c04480c0e076001e18203100c000030081603c0d0003222603030460a140c041c0c58040092803001c1c0000d1414910020b45c0c4000050884c0c000c01203802c000b0751554050a00a400b508 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 340854838 1250 340853588 340853599
    0x14030c0916200307031403010b0f0c030403050706110606011d0f010e040603060903121119030b040e07051905030c04020307050c0607020a20090a0e030c0106030b1b0c1515 75
    0x7411416240d8104e407034183c3c081070000403900c59000c1080110780c1650441c0c601207040c00c0100c01da80102e07803c40800a0664402000301002003081000a84020401c81c0c2d1007181ca07100103c01e15003003100240c0094180003101c134080341664018469040038035002c0e18101c0d00c140b00440100e42345030460320360642091505001200f40110743c0c0240040d54082d807031b419003030000000e0301c2c1d00706d82c2c400030038000100f418005215451040c0407042042036080c0b0300400d1051007040045c0817550320640d40c02e1103a0121404000c1800c041041581001e40401c49118052900010984688000d002c1500c240d41c0040002e071803a0046064a128400390790450740c1c28945020040d43d41d0b1113a1030107490300060904c042030415160f41c0c0743c04a404000d0305d115120b460712038901c405003015411072481800281715003201242c09108400045004000300e10040c2003441d13018000b10054142c1035092242040703004180c5100017a58504202441000c1585030755991300382c1c3d0720b044144186e07507000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 340856088 1250 340854838 340854887
    0x1020c01050a0e150d05090d02060a11090303131701090302030d020a03020c0f0604060f0902010c0311010e010213051e0306071107090204060518090610110102160c14030c0916 77
    0x74540d038000d1701d100203c0510800c01074441184403550f400c59140b4920042e400940064819400ca81210b524419854401401c10000c440085d0440d044060134912280c0d002800b0000035140c3e00b200c004d40c80021008000c0c030764072520000d4891003600c1a1582c2d4135000101281c245220394101c0d000c000e820b5040d50700c100040c04c201a29403c0a031000c0d40c1a0b410101c210341c98031341501c111010035a05840311a0340c00e0460f1350a4400c02c0300894071588a541c0e5003140101c03508207000030841c481558014441c21410034080000f00320750740002e07108800041407004485d0b01c000820315044030060508072810310107004110f241c07200310781065881c28008030f0b00041c2d036600600a0300030802c0b0024202400c0c0c03015801c0c009550801c440d400e0388202c1c4c01d1424030f580c1d030007090380903017601454002601d425605403400c6c0d010304143c0300456112030301c0c0b03170104645d80120240e00d00800c000c4010f0010030100c2c80c001804007070040c14505054818070400f00019000340300010009215000d4032011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 340857338 1250 340856088 340856119
    0x7030203010c0c110402120114011e02070e180303011a0708190e19051017070801032109091a0409030e03120405030d0f02070b0f030109060905040201020c01050a0e 72
    0x2203c524804130754030074100b40200220300d4240250b948400842c071070340d04a60320f41240c1e49600d4071407039003007814005007d9021081540c1c0d0a05c05072035841e01d40080140f43e281900403490901e004142c198031055860307030180351072401300480e4111000d505009100e07800c48241c4038610321031480001d02c10303d070020713180407800c2140010022000040e101e04900541303050074041071541c00a00c92070040c1c42c6000601191404910140340b0306a01e281005443c208812501400e0384251441c10110f18580010400c020070302d65a03500f0303180d0072001c41000590b54280134010203440d0203541c0d90141c4907518000c0c0c0100510a103108407400401c03d10459906003006810844268040c0340240946004040c0c0308a20344200c030704484000c0d00406c4410300e00c0e9801c03104a1140c80710b4104501620000048078510709020f0305c09145004070240e940d5141500c0c7d20210307a81940805010750030441080050307078011480d481e5190007803c22a40d29000b4240c2112842480d031710702c651010800131407904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 340858588 1250 340857338 340857347
    0x1201020d060e18151e040812090d020703030c0212030a09050307050f03031804180b090c010e0d14100603030201150b070b0c160212010506030c0a060f0503060307030203010c 76
    0x448084928001c2e40703843c0c81022540c2c3d00402140c0e01d1250b401218a1901030050140d0154850004440c4003801000741d40e0001d80c0c04000d8906443c0b82e2804100d806000c40038129154000b8400350042840d211030410194540815120150a1060031a0300b00e040d134543c0491240c62a001d60103980d81c0b43d4152101408a00b06405014001e1150714400700d141d040c40c0022025441c4000c00440c00c01280300c4540030000b0300b40c40360581168480300720048400c11454074150061040c00114124601018464585510501000e0401010011124240d1500c4a21007501c0e9000350341000d1881c030070010b50345000340d408040c803403091900d03200205040c0e041d400482411904015000459564180401580100030001d8079520040b000705034070440741401002e4504004009019403001c94001900c4250340018903040c50b51910100549882d00b0b01017609c007603a040300c0143c81142441001400700420040c1c1030248200003001c6a11503500300308501c011507005000348808401883c00a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 340859838 1250 340858588 340858601
    0x909011703090a1d07091d130501050c0d05090d08040f020a05030f0309121b011803081303060c080f0a0f09080325110c01050708120108010c0906030216020f1201020d 73
    0x130441c0c402100400c1880380308082d62030071520500001500764841d03a22202840401800c200304903103031166010005403080c024a031003142441103c90701d03008139003952819a0b90003003200010313801c800c1114501c00d810011082c0c2048c0c000714603042607070251004c10303251405078219641c184590140308500081c0000103029040090f5203041240100c030030a03d581d5002e040080b030366a25503030b02c811019445034912943c625000f00302c011a290303a035141c000903a81300c041020a40c0003000c8085c000d0160780d004500392005585441240c618100b5180000d044001e8144a201d644510301d294011185401001e0781c01c1d01319641710341d030782400c0d440002c2c003446241143c000f444c6c400f07010140c2940a410610712041444001c1c0c84284d02c0d07080115219407040d401100c400c1810301041c0651003070131498034083c000d040c0000428265002c0058840d410325400541018010032980c5920844030010301c44031039041d80d1890740711007107600143d80701d005009040742962001c5043c1e4441a102d40003003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 340861088 1250 340859838 340859879
    0x3020a1701030525051806011e020105060406060219080c0703020306010b0a020607020a030503013606030b01050a050a03020f04020c0a0f0308070804031706120d05030115050909011703090a 83
    0x9142003078001500444075152449116407000c950202c1c01b07a8000300140312a4410300501d0901d41c90062101c2031581c0700644845080140c7d0740c3d9003081080c0c2464411100580701d6800100480348009107c0c009008100500400750440401e00d51001c0e80200054005035900506503681c940c1c40758440d5400d500f001c41d0070b000604c101d8010840301800405e0303d05d00c0302e070160340c1c2c1e41c41c6a09040a60303d4280803143d105029080e000c580300b5410850600340241d500a64001080e800d24504000100c042c060b00403510462140300d0401ca2565084a00c004a070340c1600c100010b2000c0900080007801860700641c8240a0000d0660811101201051240340300c1d03119031440381c48a4800311b85007030046034001c0203c2e07204141413000201c0c5c0401c45500450080000800710f05c120106400c04c20810010390103e54080014800d4489400580b14413625601c0d2a034104203003000094509007040c810071714070f84049201964012418021582d00c0180640040f02a40d40c80030414500c2e50b94070280c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 340862338 1250 340861088 340861123
    0x2303130914010e0717070504030209041506080105010b090f0a0f030c08011a06031f05220e0303040302030a1407061b020d032c210c060106050a0f03020a17010305 71
    0x20441e00c3e891144107002c1c070b60959803541c03251aa0514461007400182002080c090148800001130303840045451280344140350121451144421400c01d0b50340729001140d603039040000500c855480481998107078141200c1000e00000032401142150040723400c0141071000c810408424001c2988a401c12070340b081000b0405d012080c0760488217107003803648a5503c8041040440c445e840d01c0914003489190010b0007020080e40d890000b6014200151103103c0113081d5881c4c00c1c144003c520840d041c440d255005135156103003e0b1340094683c804e403000401400100701c03601c08614111800c0d1900a035000c035040200942c0032070180c84812070441114018803c9403007100c1d500e03100e070145083c18000300c5c0c4a1100c0300f00e400500122402c0b1542e0011252042c6414030707c071030000c1d030f120711004511400600d40d1411003020041c10031030160018014007404004c10b94200d640600d0380c2c07010b4100da180050701c611011004551b561441c1c001000c1d088111400407050000204500246e011321620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 340863588 1250 340862338 340862341
    0x70801020c120316120f0f0b101403012d06031e02070f2003030708190c0b0109050a1d070602010b151b010b0604080a1a042303130914 59
    0x110200944030494070903c4180202005020042c00780d00d101c4803901c445d0401146040c0d60a143d44101c401002080c5069511880280082e04000c010007d43c9a00d034030b0481c0020807035500038200c9110601c2448a000101450051900750010f00c0c3d03194942216415118140e0b9482c0c02001752101c0503a40802d030725141824109822513208560041d60b0045441041c845d940d01c5904402100c07019405042030100c3d12a0482c2d176052004007042072144c3d030060b4660012000c8910501120f074003007001e0200c500b007140302140070284090f0442d0b4240c0c40106160b40e9040070000603000c0342000c81840300082e075048030342050201e00f01044c0c8416600800c080b0302460704000c0303042943c0e42246d280807401c102c0700003045a45003983e101d680d030110002c40c20708411000702e40306a019500041c11608000340c1d4504004004c0461003d0740f03012640800d640c02c1a8540ca05070078a00c114540e48415901081380700d008080c41903a01006ea05505400c10540e105011380c060040091002d062568190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 340864838 1250 340863588 340863613
    0x6030601060e01121d03040b0705060606270f060a0807030e190201030e0717030301061202130509060d1209092901080a060b07080403050d0914010c03090305070801020c 74
    0x203050803103000d0594500c0c1004c968490a400100b800781c90b010090781c100041c942c60b403402040240000c00500d800c440d0369456034202207040541c00303000c04d441480200820a1948024243e44a0a031060064081c88442a1002030325141e042c0b0603068010340c02040d010f680541081a451003200551414407a450f02200030f941c480c01c1c1010701c8400300c09102280c00140d40310303074800007880003210f04075981252205034021124408030600131080d840040140a0303241d00c690f20420051140c001981006c980082074101040c590040a0160b04001c000405940d1303003082804905410005070144807030440c000074001d8055025000c0443e0131320307441c0301c41c00804240341d071100c4030036010320000d0003511401141c0300d40000c0c0000a004d44c80b0074010950305843d4005061407440380c010030341d803245545030030b40c1044d90150202d424051100010019640d4400f50b89002c0780c000d02c0c10700301102c400e1a0a54241300319801c0640140310310100842c0d0036005500401030103d4030b1044400c0020481d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 340866088 1250 340864838 340864847
    0x1a0405070c0507060f020c12071a03060a300605070201060e06030a0b100902040b040513020c100b1206090105041115090d17210105040207020d080a05041d0603060106 73
    0x41c501d9121080070001070b407295000040c800c220b8810380b941c011500001410003000c003a123081c25504201d404101c0c01ca8803091010300d41a49204150540c41c00c48005070a9455510030748054613802d88030515084845000c1004034500002c4182c248d8100d800d04000a084c11140d4102540c42c0ca0004545101d600c004a07111782030041c01070101c2051551541c00c0c420018050030340340064020302280c0e18040e40054000f8060b40080e1076102c0d450202000f0800c0d803e1081d851066104014011500d1300109000c000403d210b00f020030413107440c0010a9a030703059510906906d0140e9000d000c00752006401c95030240c0c0c0201740342e02c1da4200040800c03840d64030b0f03a001c1c0c40c1089001c000512550410031211032401d400380b00d80e000614601d50111103681d00c41040001d090b580e0070100103044608403003007805440c007070350704500302419070f030200b190508082d0026020381e901160f00e000340c512840032500505824020080090485442d2417400c2d101605e100d8428006c00002041e8140704 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 340867338 1250 340866088 340866107
    0x12040b0a09020d060b041d0109060c0c0201170606090a2702160f0c0b07080a02010606050f07110d1707140123130b010b130e04230708011a040507 64
    0x41802c0410303d0103039039203030040c036000001c00d400c241c4409a80400d2440d9000481050548000100b069501443c0550403210003850540038050070504083c0542da1007000c0035055102d40125001c02c1d16600c0000c0c129001c2c2c10b140d00c1e401030a003103022400200e46d12040b41c072188150b8151030b18981c4080300300d00782d0060180d214054038000f0300100114642c0110700c00924002c12200e5441502c5241141242d8031500042e19a000700192800c9000d609208072402002240b41c81750a01101d40b003181507030701c503025001d012070341d00b220804d9003550303480116914180c0c03100840c0042e1181000000f0707150060401a0750800c00d0111100112006000e44820100d05200c2c64181030400910000041000361814400101c11002c25001980e01c0d200f0314007809201c0c0d02d0740c1d100c4201c07182400d0843d01701c0d08100d99802d240c50a110001e01424a89440e10000c140d040d400c6042c00e80c00c0c0d43c581540755019101035820803e10103070202014480d800b003800160b400b40519641c010050300c82e001d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 340868588 1250 340867338 340867343
    0x90112021201021e13090207030c1a16050d110403050106030201140315041d0a05010501080f070f060309031205010905040212010b09010513020922051e150d0812040b0a09 75
    0x10b480c01d103207804600480003000040e40401c5d4030110a9101c840b40d03c103d03085180708802081080040c1c0d030a21143c05001019607000701a014541d02d402c01444000c44202c200704400d22401094801507041030340c001c01011400c4c40c031221303107469603414041d01a01c1c4c0c9201c1a404120300b000300340001405030007102d110398003000300c90300e1041581782848000c01500003c0200c00701c046101041c4001c05211801d009802000007003155410324901c24180405461324503031943c03105004010654003090310200700c0f2200e00b00040c0308c0b0528242030b1401c0010b03240c0044905c2c900f800208070003100d0391000d40568001c2d0344010106a00e000f2540c200d800309000c1c0b5600c048004010080703882c04907116a03001c20381d200094106502503021412094100384202035490f40107200d0346020549101c1c42d54403c060703414290710083c034400c8402000c400a040058126003103400c0c081951584078030100700c2c2d0362100003180d40d2514124200c841c0181900e049609408000104140030454026074074039a8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 340869838 1250 340868588 340868617
    0x2030c030f0f070602030406050a0b0303070f020409020105040e07081506090904020d02120a050102030412030b180402010513140a08070b180d0c15030c0f09050405100509011202120102 81
    0xc61001801c1c16070801d44402c090341200700301010006110380080e6001d82c1c800d04000c40d0508041140308140c0f40080480c82c0664010700030b00c00440d80146242940341d40503900010484414001284c0c45d104039008440c00b0840703442408020f9a0004440d440f524044126182c0c0e2194201001050300c10240c2003640801640089409881e20601d0043c0a510003022140034001180009003026034240c03094880384d6000c8100710901032a84031104c9100c25034070b81042100d01d07a4001800c8402c0380e120611469404d1400141164021808c03145912502c4514400c0b42d0b5451840845403030b80808002e000b440740f600001100c2070000ba20f9800d0712290b000c1c141c14411401111103988000d444010b50001450a01101103048402c524000e00380340e0140c8004900b903948042c0540741c44800c410208203407040d41420382d5501241c17010a039441114040340341d460780f0361740103030304030b01c0d5000745038010608070001410040d030340d481d401c802d4400e640000b8144c0900c0c40c0c036801c034024122103a4284 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 340871088 1250 340869838 340869847
    0x206010b1c2a0203090118030203030a0804060b0607060506030c0a0e1b04051801051c030507080a02010b1531051c050105040c05040608012310050d05071502030c03 72
    0x4802070b004040c00010b02c51010501c40d1a5050090407401e0b0400e48030050303000045d241e0515684505142d0350010700340300900284e80b466002c26624802c0c1a081010010b201d00850708204403a000100c03400c0300103180c103848130900e0030044020402503d0003807003486109512003190825111803000c40b80c286211004554030754116483c0d41e09414804034811100b00400f00e010341e500707440811300141d54140444158140002e1005401c1802e00040d40c0010b001031440c0042d81c800100c843c5540c1c4848402c6d101c8d403810b2001e2b400740000000c8194440549845c2c0c40c04801d0441c0a001d2040c5e988d4881b408115000307030b90880c3c042c80d80c02500715210300c0c0041403143d030402c40214080b01401043c0c8031020103150320359508403042074070104c40d0f208088408009070b14140c0940005418410000c006040400000340030f180c0034101044100303001a40055021107c0c008203d000305806407088094014910b0078a0b00c81c4030b10700480c0c00812a521450002c0c51000040d01c5c0781b1880d000045240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 340872338 1250 340871088 340871137
    0xf18051609230d06060e061212130512010516170606070f05030408010e071401050a120e010e060910050f18073203010209060f031b030c07030206010b 66
    0x4445400080040c0e001c100100010282c4541d098080480d0080d00f000405e181041240942c46030040c01c00c41c4602c5007406030300307141c10300403658078106400384807103039601d10f403010100803900300355808142e0010240070303001c0d5154411740245201e03602c4898032031140301e40d9801c140d89203032882015000c0391070050005502801e0440040001034000d00c5420303682082030352564075660080d0854411a51034241d88400c0c64020810900903064401c40411201c081000003042e502a40c0d01c44400c0003d4028031000c0d003042d56202e100c080e207140e4005d0162803000c80042d40e0302d510680ba076040394450030360b03c1000d6000038030a1a004099031002d88000d511054800d4440c114602e4403408140505280000e802c00001c04110541002c00c10024554504810030350b010301760a5521801790740100300c901001da84183c2103800e00710300b0b540c07016141d80301c1801b11801102c60340719040d06120004140508016400c02070302d001d6210340d08a40450381c0741c43c00c01d0200d00940085501e000c6448000925 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 340873588 1250 340872338 340872359
    0x10309060f0203071e03061d0a060e160912170f0c07060f0f0e210705060a0509030d0c050a0213091704080f0c18040c0f18051609 57
    0x51450003500040380c12080d0311181002c0340c0c41604c018010032880084070a8901c400c0c85092080965400c0421041e0b103400f01c1c1074100030000d000c0ca0003100881d000984001c5855000802074801500301101520340059078560234054880000d000c0ba00da07070340000700017403100c409400c0c2940c00906110100003184001d01c003074000010f40400d5440c02e03c44005070750001c20000700140381c5540d90142000c8006406410104540764502c100b040b0142e000826845800300c140070744205440d0162030034410700d030003420442183c112660040001039507c100f15407000240082160450907900654501e1030180c0704242800e4008210b43c10603150200940340888450a2440445002003841e06d102d9031820702c080d0300c680d0601c0c1c0c1c651010409100d410020094009440b00c0d0348000c0050340002c00000e802c84403030300003000d1009500300006003003040c450b00c458014124800110103580d11448981d8404824039003c0191520f09000500461001c940346198507286803900c08540d42083e41005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 340874838 1250 340873588 340873601
    0x204180501055b0b0c07170115030201051605061f061112070602041706040b0109060303050f0f09030708070519032003010e0d030b04180b010b090f06070501020c0114090c0103 77
    0x8140120f684000881404003001441d804403580050440e030790414480104c4407086000c4215580c1c0742401c1c68600c2c1104902803015070703409007070442d00c41846101d0041003000341070380240540266428014207078034054141d26400003540a10b211541c480d642200d0f101c440c440d242016034040d01c000c5640100c0c500051989074041e040241c40c2580307510f81101291080c0c10b0701c842c241d00104c1040180104485d54a0143c40342080030b2003441e16640740140140500d46005000340c0c0002126000d07103111400b180c20180001c2d00f518001541c13080d04548071f14860cc44c0e20f001d1200e50050100d9294680303000401d4a41c05030b128010092414080020000c54080e0550107668407000742a01d01402c21805807811415600407503903200000c184025607400214034420b00d40f40c100b0400010780d0a2040307605580d0002d280d5a2182640c00c0080c0c2d450b60104481030301304800040200a010040d00145820100345000b40190000340142c80d50ba6003080b10101010b41040c0802c081c1503110b5003045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 340876088 1250 340874838 340875001
    0x3070f050a05090a120c0e06130e01020903011e1b051b0c042c0304030b071112030703020406110a0c234504020418050105 54
    0xb0741002c0300b076000b1403416207403600038107120070f12412110304000003119484042c0240c6030002c102410000045141c400c8608a02c3d1031480d1101c503080c10402003503041d684a000c00030002e021400713100403028500c012000054590a082100c0aa00100322071a003000c0e1a55a5a0b8903103092443c41e56000c40c0035800001d0401b034003440b43c0d00000341da5580030310215440340c14440c0c0e07800400410340010310401018640c1482e002070000300046142c80c041c1c25444441c0741000301c82c5440d010f1005040280a800d8601500710103c1803216180e410fa0181040d1546070316821250103032803007125600d4034488001000c800c5d6040040c89035040c800b021507a6910341c2c00c02508020610000151f140442d04170f11880c004000354040040c8000003040b00c44800105485c0e541981c1e00322021042c404028800b0b80900d0301e44190100c14200c3e80900c940054009008215905284111804041001d00c841c0c03412920380104903091f8030100c0c540001e0900303003814120b8039000312441080d04012068503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 340877338 1250 340876088 340876097
    0x4050307030809180c0a030c0305010803030a02070c080a0f02040b010804020906061c0204030510050f071d0d020301150806160c1b05030d030603020307091e0e0f01020a031505040203070f050a 84
    0xc60503c90b0403190b00600204170a15110621480700401f00d900c404108010141040c0c01084500d0b400700849400a01075500580d8410150900540b4140c0c00c0d03004010900c03c808521040c0402140340d10340c494800c41d400d03c6908080e00c01180c85078404d40b0041c4d444404040825107a05c1c0c100000d00c0008000d07a6003480c40c040c4910b0480c201d8005620948003a00a035031190301ca07950502c0707200d03840b4000801e22411400c2c8440014020020b8140542c000079121002c80015914490000d914950050081c481c8038951904072984615501c980d52940c440c8401003490035214007100c011982d0143d0b41e80e11144001e444202c585820969840e52000440ea4042595282846041c0340c241490314082034061462042c503103012003070340c07240d2007007450120b03110100c03050584000c21b103013240003010030602c00c5042940e0900c030b20180b2141c8258800105403134000d4254105110f203289000c820180360390b030b0b001800309034401101c40d00000b500d1060120300c020302480140041c61824500f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 340878588 1250 340877338 340877359
    0xc120411030111091002010501080d0c06060b1602120d02030f03062107080708120d02031512070806150622030812092a0f0d060c110f0304050307030809 67
    0x10038210f6400f01c0800b54450781c0010103052508000d00304c6210004148000c03c003540c980120310340c46141c6400d41e041003102c0c4442da942848030366041800a818055941592440e1544030841c00d540041002c074003135440d140aa401a03a230105442200b0300103070b0003544c9040d405812802c100d9000814107507100322800d18241070404408041c3c91010340f104018180ea078184000d05103400035562001c80150700c040341002d07065a01c50151181c1c1e550044001d6242d48038000094940049014403540180f0381c91500501070b100001d04204960102003590515203032804902131803031038202c4007130b00305d00c00304000e07409154406006405c1041401d09021155202da54200c0c0320380c40380900e0f2402454160130320a8a5400b4081e9101016600c01034011035803c0900f8000c03138031048020301b441600c0708050303d0311942324004081c2859a01c100100040307203d49202500c4c500c6140c40c170071401d21880c01d01464010000088405a90000b0b000f000c07401e140d40da4084140e802a240300d134204130440c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 340879838 1250 340878588 340878623
    0x5011e0c0c11010309080d1b0207080718050a021209102007020906010909230105060306100e04021c02130b030f04060f0e0105090c130903092306041d0a050c1204 71
    0x23040c5442c0340c1d5010340c1c03001220b040901c024600005e54000e081d05400960040050844000c40c8800041d40701801140d07556503012200020702540240312544280c0804102c00041c000c10540ca40180342da20421102900c44041001030a1014002c0442c2d8800c1040074094646140a1039116005141c120004c5031600c4031102a6401440d65126070040409070f84400d21401112601408040d00e00500b03500c0d04200046141441d84034090511203e10309481c0c85807a1034040714000c99128440881c2d00800080a000071f5001100090a040c0302c0c1ca000304400700c0d24030071240911076540084030720342c4541d2101c1d0010064041d000007038590318900092003076420b002e00c40c17050000700c01400500d0107400a0207500c0c810321082c282080d103400703264000213070081407020642d200300c84c01d0704141a184012112079101840341d25030100f4045400201501c485001c10f010444102001c01c080d200c11a0001c1074800a0b00d48002d107103010310041941c42401160507030302902034a41c0245050250f03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 340881088 1250 340879838 340879841
    0xb0412020a1518060f120518030f03090c122817070203010605120a0b040c0e041b0f061d040b191406030f0613060305011e0c0c11010309080d 62
    0x4071040200d40000350704040c241c0c600000200628117030410300241010420018002d1a40010b0104480d6840000c1000404560b080450031141c1004890317a442988003403030313801c0e0021103021401d84914002036109003082a0421503001000005100e4040401ca04141c460281c00c0c204c0c1d02010b41d51041404a200358114040b10a11914547c1e6075880c180181420348225030080c174007a0844102cbc0f0698401c0c00a10744000582114400700c058075503180c01082015194404849480954240000e2001c0314205052101240c00c2e40d80b0300d190740e901c01446519291150300c02042c0e22000d07102f60200598070041c1c180c85c008000040048074900001c480d000e9211008804581c424001c0c0400d075111f40c0c6124048108450003070031890f00340704030a002c4800420260003191140c0c6600c0c500140c1d0b421200c0655440340082c80121145111f54040d0501d84040001f02030030520b00908150003083c481441c1a0803400300380347c2d010300344015006012280350032242c01408211421032540035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 340882338 1250 340881088 340881119
    0x3051c06050112050106090b090d0f0302010501150e0a030627030806030d090305030403170c07090c0e180c0901090308040807140a08060112140a15050705040b0412020a 74
    0x808100084150070800010300784802078000c0e040f00c2d40744c1001401044c0e00002400210341014400554031a08203010840c003004000005001c2420504410105a019000703281038641080c910000c029000e00100c65003002000226041102681c0030710104a9039041024031140d80401405645018403645807c400c640b4000c0d800280c1200c140f103450724046c01003440341501450208513080c02d503210307a42c49114500c0000c01100b0b40907642240100e607002580c5215040c0d40940c0c0b4010707600c041010290003202c4036030000a4000030314aa4a1400c0d030341982584120b038082c48420790b201a920f031020f81c400329209050001242c030002c00911000014406441c401e0040e02c41c25282c0b00d4030300082500f1805083c40307100d46220a0084560010b40b89045030200000e418400a690030480f00d8600c4902c05461300d03016804580c001c0c00340030f040c05480318030f4614042001e0b0390380a030220748600603405855a00603081104001900c1c04001d003030502400108400c94080d600c3d0401c418002c00d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 340883588 1250 340882338 340882387
    0x9010e030403110405181f0f060302060f071109040804030210030e1e1c030b090601052803020d0c200705180a020415021b0a120303051e0705070203011505100c0305 72
    0xe60407c00342800c0303028020080030010f0070805111072811a4009a0240a1100200d0081c1030204110040c0901c5650407103401c00007270a00841d9044c0303810701544030b82c001d0000764003400e201030b15410001d10a1080014103190200608400942003c19895510340349504000c5803048a410740310118960030740b052403a1241d10006001e841c290207211000100903d070740d05102c001c1c4006000450605160880066100e180001403a102c400c142c0090090035900040289010f000020560300010300c100e2080e141d444009145070050f40d040c1d91194030340950b03608101100050200a580d07560f1240d000310f5144401340c106500c850125108464042c0300200580c449140e50081103103426001582030f10aa4804121a00b020066030a80b00d0b10400101055560800180703141c056450f04400901c001c5202885030801d41030040c16900034040c262303c00d500c0d10b030b0008500e08100600d50102c4001070201c24401121034000d4801d1700c08014185d060010801801c68495541906c078a031f860f5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 340884838 1250 340883588 340883623
    0x3030c07050307080c09041e051e100e070b07080d02070303051e04080307050c010f06080d1b1205090d0f0b01060f02030307080a0b01030f02040b0309010e03040311040518 75
    0x149000201498400160701168803500a2003402450b912040324455100e5080141c941400002840c0c0c0b08d521a140c1c80c001e4000d0003139000c00b295480c010003041000c41711401c111107074001070000070421a00c403005055041c4d8000304080114194120203845c01a005000b000d09143c601101c0c68180c3c0d1201c074040340042da4960400c20603450702024030ba0828284481c110540c0b40071782d0f80c03404074070019045405100c0041450784c0c908801350041d56010f400100d09108180d52508099500c68101707413182d0126802e903109002d2403c1e00000b40c440e0907003081c081d05040507042d030f0550381c41d4410040590040103105401002c18406899107501620a10081c1010741c5811402001c541d2040200d004541082042c840310560010300c0d1078000000100014601102c400113800604450350510a041d00116000030320707600c480040c501ca003800798024454a0400c454143e2030744074600004150400b408031074a03e40c185544510b5112861180009a207806000a280b0300841c0f0034000c083c5a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 340886088 1250 340884838 340884853
    0x90a060509102a031107150506041b08010504090206130803041508040b0f0a1b081503160303030b0310023105060f07060f021612141206010201090203030c 68
    0x8440e034030441c680407000f1600070b004150a010019840c40c400b810501c2056210140b64a15803400800c48100ca035005661130344d003615007050b50010304012a001e5108038608051035918030505200307451081c003942c0e262401c60707084c001000010104040144e07003007041800940c00d81c44d4004130201c06090300000941d121403074502e030920281d00b100e24020801860310280f000241c940ca80158004900060140c85543c410517088010300d80c0a0544014184c480c0d81d068032039400c250080e003e442c2d43e08011140351040d50074540c1d90071002d17800350060200104100007003446907000e07401d103002c0101628a0110020344100aa0704034007448201442031850001031405654180c44482d00307901010b40c070307103864407000402074020180c0c048010480000e22204101407a4030032001c05c660010215210b030619050310851540505046486664610404c110381d801698400c94010700c07144050300e4104034442d1004001c00c085c201505564071600c4c154016a13047c0301030024135945000030000c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 340887338 1250 340886088 340886113
    0x10504031407050622050105040b0304110d120e010e0306160f02010207020301060320040c050f07030c020315071101140c18030d0518010c080d050603071805040b0c0307020c09090a060509 82
    0x401154006c6050250411080040c00092000c0d242d025030442e044822800c1d86401050410201003030080c40c1c42d40b25844030a0040c0c009240e41058282a030f20b8800180c410000e240c4d481e0b50036501d0541940c1c4d8488101d8440e4403d00b000045290710348000342c20801c1c140d01190a55206410440c6e5540008060440a624462946040903001ca07814020031750f41000161aa2281d0013140c40c00990000b5000e01749405034480f03508a0358090b041310141c0100c000c40885240703090b150140000c0600b10b01105c048014000c4c3c80740f69504868200c21900d6103a00c650305544585404207251105c03d040d0465907405121500c1003807072544440340e03100080c544810954100c800d080d81030210b90400e00011400c3c1ca81681c910342c1e4140b0f0005015141d140c0041c1c40c00c54103030b20620200c0610000b4141907241c071742020b80034034802d1222402c10703240c544200c0e401e800101c2c1c3c0c42005a21803000c003d61807a0036070070642c00071a10703000e440550810340c64450642c0c07001c81d0107032000c1d4030050041c401e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 340888588 1250 340887338 340887397
    0xa0501050f1008070503070c020a0f0e0f0106021207020406090f05160203131206141f1a030f07090906080f06070302040501120506030c041e050105010203090105040314070506 77
    0x4070a504850000b20301d02c9816025181d0603014040d82d041000200c00605900d008d000c00c002401d0300240b0310800c0715074404400d100030515000d624503000d41003000c950402205c82002c0d040c4c650f603030041c007030b04d9441c200c2e4124560060101aa44540c0701c10300000c440b0017520600612440c4940041468038000c141c5150381d00442150000b158010482002a50710b0b003104001514102c0445a6420041e070811034081c1102da82e100340003081e4102800401c03002c40c01a0044d61190b86108180180d5420040300505036030310034650781c0d45040000981000b03440e820154004007034108608810303220542402102c6c005e8106c86543c6d4020b2540000c00c0b0700400090341d00034072910f0254985820400000c041030810820701c031070039850304013061069030107000511480074007070001c02004041c40000a102803c01c0b003100c110f07074540320022900e54408000c0720044101030712014a0301c0e1450381c400021400c8403480c0c0d012402260320200c1d2a80c0d403100100300032a03601030068401d1006541001c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 340889838 1250 340888588 340888609
    0x325031121010e0609031c0b03030d18060e03070b01210c1206060e070504030305070507030b0c0d14040b060f1503040b0f010902070c09050a1e06060e0103050910180602030a050105 79
    0x8a581e2080c0030b1f0082c210342103024901c1c42d454800004c112241c658000c05c0c50743c020158260b5007541460500800ca2881c000c1d40381c56940581801d118100c15100c03415101d01c134614014200c1d6541c6c00040c0003484401701c0700d1034100f2400203203152100442d00e903c2c80006803034004001e800016442d803002d00071180903040151402c170011742e01604101001900714840c910006050010220b8074806003c028010705000b56003000414800d8075003001900318030b6100b010045226032030200c1020040305444901c1d8810b603071020414101e61225002c1140090302040800da0155507403c854944403440d40c051400f4038407850700c0c0906030815007440d528034003058100d6030000d071042c49214003081d40740c00309004032282c07070394000703295190180e101c409804400c0f204140364400078001030724554594461421618603956040d41008184011001c0d5201a5070001d040e0348011080c09400e003043c1c0c400c141c42c1c2c124001d0000025140d660381e20990300b048400003005aa40c00c010095820300a0101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 340891088 1250 340889838 340889851
    0x19140c010f1a040e060105010e010c14030307090618030308091908031812092e0e0f030d080c030c1603020115060c0b0f06130f050103020325031121010e06 68
    0x5000c86102c08080c640d4070401442030f14100450b020301d15031a640180300c0d000c4065000320243300038024200003070ba0b880e48141c0d860400141d42c140f001545622450190701145c490a0b01c0348111850360b00c0c11140c2c00d8000e070103c06180551030781404400d04ea140d40c0c0481034031884042e03071686000740301081050503011a1045c030b90801040307d09a04400b404458040c103017201c0c80c01180d10380940f00c0760701001030140d80102510034600300980030b13000a943c4100c40340c210f078094180c101c80d009060303c41360b4421002d00072804040116040710390010203142d00c04502d01000d400c0c680114454100034a10744010740c0580d6540491201916000b01c900f0042c211a0911b00c0c1840c803940d80c1c078041010700a180f000081c3d02540842d03e2541c503e401e0b0652103120750801c3c025445443ea5000040c2001c1c032040b44244608000300c3c500d1540c0d07021451740c4a220003d030300e800c1899903e40c100c040914901580e4013240881401181c000383c01e140d14220303690680006125210103001034502000030309030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 340892338 1250 340891088 340891091
    0x6020a140c100c03090504050106020303091b01020726010203010609080601060201020a080f1522051b0910030b0d060c110604020f01030c1209080a120219140c010f1a04 74
    0x54150740c5401948260109103440d149000c143d203414103c6601c01c0540003290b005061070000640e0b56400405507004107403d00a0f40c9900112207022000c104c056041c41e030141e0030000d41084180910300110a82d40003810180c8821b81320b1080890890344240c100101260340701c141800b504008020751780c05000c07640001c5103032015901d00074110f00001482c0080d14042c500024030f80503900c034000d1201900c0030380428298800070340d0701d003452100d000c801c0f40e6141c503100015600c000034010804450b0583c010041c50311100906200308528000c1c45070b414076407140c3d15440c0c0382c3c03500b840d032a8100780104000200021300d983e00804400c0c0c1c0d03919056480c0d1000701070001580d110850344150f040309090005103200140c006035552819038102d5104946044044401d011120004240045507a03070307021401309403107000c50224003d61550310707010300a4250b0072260714043c800400070402a0b000e07450400449410803425543c00310302864030300f03032140c0d200da003543e90756030911304400002c490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 340893588 1250 340892338 340892353
    0x301081209030714060c07090e280204020c15070903030e100806131814010b06030415020901091203030b04180510020708120103030c021003022d040b0406020a14 71
    0x40d40e01d20380c0f801070030700761500d201c5130008558407001100c03080e0b11a071041da8403441c0c1c0c07280c1e61001043c041e41c4401050049200c01010ba03901c0313403043c25a031800d0101e4495072800c107800f40f100035002101509003d1181541c2942c80c5982018a2440b030f15041d6524440d1904610f0010070381c124542145000301d070608003051002e40c100140326840b00c8152541819036042c03c0034607014003140c988040300c0544451901c0d081c01103130000c280309480c07070344002d014064039130f0300740501440116005019520406d000000089030740d0002c148410052404070750560b25451802ca82512100003200440d640c1d1242e030b440c5050a010b0400349001c00a2900402c18498441c1503c0700e08922024020303590000c1c11804000e0182d09441d0301c010b20b059210019a145e01d80500761a5090030b090b88520292401c5524a134400d008072110100c1e54001c045241089038110f01e82c60024103c0201c04507018800803642d81605c0000d80020715146d8010305407000541018100c50050210b995020313048407d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 340894838 1250 340893588 340893607
    0xf0c15090102191e0b04060e060105030616021203190c02060106050a0804060f09120e062107140c01020912030f041a040b18040b10091401020102040f090203010812 72
    0x40c108400e5000c0c44644180950940f40c400d22084c1340e5030503111024141da14404c2400108110300d807041c0d10403901040002040c406c2903650b000c00b442960b51503808600021014400511081126142401150540551404071350303200c0d00110b461400400c04460f020b04401060b000320078030228240080c01e032550420000400318451011400284001d810104007084110b5220360b072204000c07507080211852600d8000291103195000078000b036440c20300350740c441c5131050403900f03504420b800f5103001403182c1d01da0110290008102105100c11355400c410540710940c01407000801900005a861001004120f410340e20504c04000641c0203200079819014000c00b101c041c1c1340720391410001e4000305640c208591156411010340c0760070125075a95205120b100704000c451040f0780038410043d0325002d11005400325584580050200c1d1410082e0103030702c03418610801d2040c4005440d158840c0b80300903c2030b450b03034080d41c1020b500100401c10301e5410b01145400b1a4065505440c05c85982c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 340896088 1250 340894838 340894843
    0x6060e01020105180c040c120203070903051c0801050409050f150604150803030109053d0e040f1104290a08030304110603150d030f031a0306010e0a020c0f0c15090102 73
    0x300717046002d01d94036207407060814010018038400c5940a0019992841c2c4500d00a251440c2c078401100d00388203039a500825003821400c0c0344449141d40c0e17030340c03950f9030328000c2000b000d055103c0303098a01c3d000e05141e250f50b590b001d02880a400d0350212490010713040c03103400d01040761041d110400041000389014080e41c0008001c403811154550004503032521182207421103201801980702d14180c1c0405030145a1880400c00508404200300074800c01d0b40d2141a1601d042003194000c00c183ca0348150030001076000003005682d8180078100281404440d0068016009058220b800d0043c0c0340a421071030b45050003018010709020b4002e141141030a5860b02c0308040d02c504214820000400081c0000c0d0b009500555400c0009044000c01c0e2803a0a01030800004107401400181c00c2c240103480703020065906200318138014005089980c80d04c0720014001c0c0f4003a0980100136000c02044080c2c00c0c04200c0d0036421590303140a00541c144010800c03800204541076007898900a004044d40750785c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 340897338 1250 340896088 340896103
    0x1d060a15140a020118060e0d0815041e0e030711030a2001020c06040306020a1116031112031c050708010e070804030207090609020702030f030304050a0201180906060e0102010518 78
    0xc595202c0d154940c2480036405000002e080503021440c904003c1d0603c480c0380c0000c00d030061034609a40c0501601d59003101d030408100c802c40e4a0b245100420f54907401d29138040b400046980b200c15403502d6050200300181c0b542c40803910310036840441d01e9400d101d101c1400c0c16120008500808050305a5581c04800210750840322444050703040b040c0360564001c2c030040d503420b44014a0580c2d40c43d100d140c094000e4200d01d6408000a110405003d1203940000e6030070400546c03221894000703451641d40b61018502d842e042a08680407070540c0140e86c2041000d0311880001305402c5144000c0c03c180c81d002c407540100710b60104044180100680320410300c40c00c0c0c01c1050b624241e1905d98035070070305070315000c52a070100f002145032000018242d07103681d014045580c4201c094682c1240c100059640d0307408140e0f0301501030b410482181f0300543c05403e590b40000c01e0f5800c403540441e511031082d000c0b10642c5d4420b034003194050710420500d42c0e081c03003041c0e841000c004040c0181030030358188aa45022 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 340898588 1250 340897338 340897367
    0x2160506041a07150c12050708010303360306090308071409010c0f02030d090f05010305150f0a030803040b0a11031005010e010507020405100e09030a0c1b1d060a15 72
    0x1800034103101070004c081c00052840e280008140804829003000400742c45190403500780407481c0c80041051284039441c5a812030b03402d80e07520005c00c0e0000c0c103141720014018a0355140c40e01614002101c01c0c4800140400560003000002100d41690402404000c80180082c00308200c070540d0f2140009544284e4403858070a103001d01250380207140105000c0441040a0b40c1072040c0d900c1484510341c007001403019039000c0c101c4504903994503401501503030410380d0301c0844002c22565804060420322400303181c41500500e5202e007560399845103900740d442900c00b9107a0080c9001003142c0e103d0140151a02180080707445443c529040088682407182402298100000c3c041038401681c802c5040d17401e081e4000707008010504000b00070384220b076032500c9400c2c0086a048002824250f0120554035410b40c0380d1580c20004003599118900410800720700c1040020840000c12443da43c022803c40c1403001240b0b0748080e050643c01c1140b6919103521086480e6000070b03d002803107074460b140341421031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340899838 1250 340898588 340898639
    0x703030f18050415050307090207030e28060807020c0109030209040b0c0d02040e151009140a03060516120501080a110d0506091605010c08070f03030e0601060216050604 74
    0x1428070344161000e03910380c4082e521030b013003050076109044041d0003d8103d5604608440707040d13584103c2c1d1000c1e40216035024000c030b01d40410854040c00c04540b40304104148040d04c0c0c04285405040d03c01e40e9807140c001500040808040100f0360780c040050082503902420200013491442e40010f850030001000100032150312804200480e19803410b492180503c06015501c0343e40350110540b9240044800f41008522040050002e0070050031045c17458056684000c20710b0700b0000000f2520346550f142507000000d07202c000010804902c1424000c065214504045c07083e02100100b10202d0328800c95095850100100311000c8001102d9100d00d038041c042d685c210f011900010910307a40240080c0050181c1ca0030004e40c07150100300409490103089503006520740f2040115070880181d10000c05481d030030001000428a20407610580b0740c80703890003041040c1340700b804508002d401c2e803104025070b0081c08075110110113588078070081d003020f4461608103890702a281c0040c48000c0d03844900d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340901088 1250 340899838 340899857
    0x60a0f09032306011e03080a050d1a030c10020705121603060b0a0806040b040b090a0c0305030301050112180609082710020a050c06030709080604060e010e0703030f 72
    0x5402000c9510045801c0320350030045070100050884204814281444940a08400480e80e0f400c2000340d03180302d02615503003000c1c00782540e480c000c45500664201051001c00d02c8038062507041409107202c4c1e50311074a0004203442688041c90328229284039a035114048030410041540c1d4001503900403548105e42c4514094180001d80307080040c512810300322403001813008820f102e03050b007000744030310420380301000c14070b83e01c44145841d40e5060380e0083c4a9072601c0007150110b074403a00c1080c0c120035103000f6991104000d54490116020036801240e0741d402c04001044a9078002d451004040350801d0180b01c3c280400120764039034076400b0300080417a030350303102c10700e040c040841300b6100b1191141c1140390f0508a0f8640701406401d103807080c1880341a0103400452003c0c4040382141c00c0701e5205000b07080d42c40300c010400004d41c000401000801040c03a000050220b801c00007280100c0c01500001a101456030005007074070b03000041d00281c0d0380250010030000c2d50095420006182d2440c0c00c40c80c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340902338 1250 340901088 340901117
    0x1020d020606102f0d02161509080105071205091b10051c1e111e0d0c0507110901030206070b07120e0c03010609060f05040504020d02060f12060f060a 66
    0x4440030341d104042522a0074529005513080700880305804030700f10403a420001503c00803130b81d502811180da50b00c0e005141d4108411546106038440301100c0e820300c1030086403a8081d0908440e4103c070544001400c05041c000d40e0f50040c400c954100390520301a140041c580085170717280e13182000b5141e001350110390001c550350f84640180c1381c4021380f0714030354014031081110f4840540154030601c45aa80b00ca0030a41e80c9a000348a601c01c0c10412034449420b2070f110026103000d075820a07040d410115410070140690480c9445840f00f0300d080341d00c50700e031594035504050451201042055000c0c0320300034010710240c1d4610045c1e400c00b56000e02207501c41e41d40c0342c000700c414880c4101001c02507801e010034030924020114070341c030102d80103600820029545002407015603040d03120315a020034482c4400c0c881410240c00c040e50050000e013608034400095800300e40903030320418448080c0d240100724014449038600d00b00b500850700305da00b004220b0005002400501c81d600701c03c01401012002c07640c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340903588 1250 340902338 340902347
    0x60f1a120f0d0c0b090d35010603090308010914010302210706090e0703050c0a0c020f06181507030e04050a0b0d2103050c0415090906090207020f01020d02060610 71
    0x10341c80c105069035101111610060b240c0c4084220031200d00d0542000110818030018000700d542e02203980381200303541046440c0c0001c1380780000030300168051510740000707018095910f070300030000355600207250122410003d01c4400182c1003180c9c040c1c10840081200005820b9080c15240c04642c2000030b1300388424400c448829072541d140780c601a02d07100064040e01301010304121204c040411b60b00d5035400c2012403c4507011540c1e0001c1910501c80824140c1c400c420a428480c400b8021380c00c0002c08200050301c0740c1010002030fa111550301c3d010411703410708c145014201d40890003080d090031001c0e94043c0c01d032a0040403a60060baa034a00181c1c400b2150b07007180000d20800307880741004200c581001e1201c0070f130008010105903142150850036610070705c03031b89102c0d44500e0081750500e42003000c1020080840c0b00341400700003030400c011880300c10a110341c000030f0144982c0140d440481d48140014414a10440c0d41550040ca500781220b0740c000c110640d00400440e5120f00c41441c1c20019039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340904838 1250 340903588 340903603
    0x9111206060c0a03091401110a03200303130302071a030705071502120703051807090207030509130e0105061c0b0606190207030b150a151407050307060f1a12 69
    0x2061150400f401c042c1900049194103852a041c40b20754200300c0180150368441103821315803c10707070100c4401c0012a10449042c00c3c4104182030340240c0d0400d038203c141ca940c1054656210b40c110542c104c004041e0104611030080858001001c030206290741d480310207003c014880c3c4144100001c2c842d013080320054605446900c0e5500c00c548403885d0b10241c0510040c11245400070034070708000b007041029070203100fa042e00d40c81d00041c80b040e41842c01103000f07500901d00440600a091295400c15900c200d80c20070070f406035600001e802400140c506094840250809010340a028071148110400017105602c15801c4000c4081c40c0e25064046440c40c03294807502d0745003208810201c0c0c2841c0e4003084c520201c900411400003284c50f640c1d0b400115485900d6003580c0302480b040100800c0d002080120707507203141424540d1181d219813006800b2a0f00c4003404844e550400100102001441c1c0f049200c3d90401c0b80d410802d45890440000d01d40c0070440b0b4480c45000303030b6884105907200400122 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340906088 1250 340904838 340904857
    0x1061d0409060207060b06040b180612010e1e0105060f07030c0501050709080610050319030c0506040803160207050312090f13020a0f050702011209020112091401060911120606 77
    0x80015985a00b0320070029000301404461280c1042c004c041c640ca0080252819a035140e6120703403a00d41c4031000748000c008a91483c0d900100c3c10b00c500d04010384c0141c000c50003010304000e2080c0924220451161000d0344001c3c14044c2e0501000503c4a0749400c8143c655524180405558030901400c080d11207a41182000f4055800d1a003004105607010380907a0480700d40c0c0007200c52507150903207072404070011b41c010160907a000c41c400d103c280c03240300035861030300e4041c1c1404440d44244d80c6404e401d004003103074180c03800f00000040c0449004904c24a10307000c000c903c05001035604140009894162400e8070104644000c00e1584a583c1c448041d19413901000302545244284214014040d410813006800460481c1c040e509489010344100c0e80601c0d03050391031110004c41d4104c048000c01d07107104180e04105091542c45031132800c0340f0680d9003c0d8054480d0205032032080001c0c40c20348a06401801d074040c02c0200046001d9208026a00d0b0281c640314250300d80e079a1200451540d000f400c090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340907338 1250 340906088 340906091
    0x509060c10020c0c03120307081f030305120a0e070504050a0209040207050c01030b0102070308030a050c040b0304030e0f0118142403060307061e0819150509070201050108030301061d04 81
    0x1c80028080a40c000d10302c15100e6000e4075026200d0340f04158451304e1607511440750940810000d038400e071180e4541c0743d000201d09210030880980d680340e4603d80503d5001100810030028150450240c1a130307800da8000c0c0030103814005802d1000c00680c50302d00600c01c01e40166100d40214090f60902d4041c1d80300b110f00900210344480c0c29003049990307a000e800300c05002c02c1ca0000004425403009c80d5410607680c01c54400703407030b6448001c183c400500004142c200c0d1540240b001240100c100b40055003d18029a1100c2040011008100420800980d000c3c107021300200d441e940110034101c00d40c120350402c80000d140318182c4020609a161918882451440100460511041e45005507020740303401c3d000c456180781c88100581d400b1b01c851030358010140001c83c01d026582c0c810b41e0b10561110460000817089000428448281d030360385000044000c10640c0244454202044c0c4194013a01d43e10080c005540350a20082d10383c4010b00a0340c1c2009030481c858602c00c00082d40d05001c0e000c01500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340908588 1250 340907338 340907353
    0x506011b0309090f0509071403070302040606030f060f06020a080705010e0f1608120702040c03150b0403060e01020901170403050f070c240e0f010c050d020606031015060509060c 78
    0x20300078001c5030b040c000c00c041c1c245007841c04000880399100b070b03500c01c81d00e00c001801c0d802e00b071941c0c80760307140f600c1d002182d0f04d4495044c02000503117450040c4002000c864801040b04050780d142c0340c06036070064001d40441040520104070440c1e0000e5424400ca401032441d55a8102c5400c255001d000d0122080720503210300d070b080194851001460403090040310203800c840a0f1120585602d88807404113910a200060103e4800740c5010707440541d40e02114140013440740d4400e03905480c501c48075484185910804101001800001d0048000700d03103030200214a000204000a402140d00c40032804216004c003000038101406141115a20644a00699101c0000b40307006100c0c80241c3c040d0030007003840512041003800054000d0003d5542e5600d901c038100c440350f01072054442c0300030300c818108041e007889540859410301004070500c0e92680a8201440c0450038585400c503c614440042480d0026011840c0031005c07200c81660f1040c548140d5030105032001400d0390103401d1104030f45010b00718 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340909838 1250 340908588 340908593
    0x3150f03210804030503180c0a060f0905090129070609060207061103060a1512020705030a02060f13020d0201111903080a0c0e10020102210a060e090d030506011b 71
    0xc240794075041600040140c00058410112524107041d540280071a8007880030440f0449a04440c1d16901503280468a0745c01c030400000b44d010050358406000b203415401600c01141d40051050003404d41a030380c1107440d52515100f4160a501090548909890900051811400b190881c0c000c3c54120106006041300340c00c0c0040203600400d000c60b0324610342180b41c100f0200c41000c0e00d11070003004100781c544602d403402201c0240d0703035489034204101c4c002525a500d40681d102800105001e080155140c0d038400794044e207410000f4018080d4201044e08110842c008401030002c06641a50801c80b518003510040c0d0b290780b20041e80748000c2c01455800f00c10010991840c004141c0699115043c6071580200081181e505101c4000002d4205082c24a9400c0c000c80044041d9540d01c0018580680080c4411030ba0b104681d4400c1e003405c50800740000e544480c010f11015000d0690704071883d0030030b039180340d030340d0a45084000f05240d114000102246c0c00b415401104104030f5840f01d1817501d80d407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340911088 1250 340909838 340909853
    0x90b0103061e05270c0d030c060b0603010f03060213030b012c090c0d0c090e06070806030d050307030b0d080d14130c170321040501140405070603150f03 67
    0x410707000003002e0103080319000305074000d1501810681c1c0300000d03510300a85444540403000c1c00620180c1c4580a07510340a034860389410340b44030380a17030348556801941f0301e0103070192170302100964490341007030006102c0c40244c5185902105d41c0004010f995441403101c4003120383c415400584482c802070000142520f007484820340d180328141108840c01d8220302070a8480905582c142c98550098100207158100700c3c2c203044180d8055a1540d103565075400440094514801c20302a09800c03050078440241e411900c1d20760411002c902920070721043c20700003002c40c00010030520802d87c854081d01e101d901d8014903180728a41000085035a018598445000380c02070708000d4506004080029290b103000507001406560700000308140c50340b5105a184a601540005c5c2c03229000802a0600507a0046610099140001008001490181401c0d821101c420750302070500c042000c2000f000540c007194030829554103040002e880c191020103d00481190303005410321040e1808003000b402841d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340912338 1250 340911088 340911101
    0x615190e04110a030e07030804140406080a05210c10050a09050d030c021002190804021203040e070906050a080c030703061a070b010510050906210f01060216120f06090b010306 77
    0x242c1c5041c40740d030f04030101403590b946c180c3c4406070001e030050106010b0f60441074190495440300410100f09a5118808c8500340651560f040728075030b00c0200c0d07181451540462a003442401116424100600105a99140d191040300029090b41d20304c00101200584d40c0282c4409070400d044039862070340084050014100742c03400c8805440342000076142051113000301ea040100d4984070884c0a095101309031107107007001c0c2040340d1269250100c02c2c01c0d20380c100b000d0002840d1000744a101420704801c003602da1f4a00c0e03000503082220400010740340581102c480b5404c0b2080300c40c0507959642d560411030007005650001c0c24400e894080001e000800d51024003400c034064104286140da0b0f80c1c1c200921111604c040c50049031081c401100b4038503180f8007031301020025950341e2101940401200110483c111360315180000d5100050003006e03810810940215881c1c4907601c1c0f468186043d0322059074151000801c0da03914041130404201440d00304001507584030250240c5547c407458090050802d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340913588 1250 340912338 340912357
    0xa02071a0f1515192003041802091f0e0d0b0603061303120506061603080403020c01021b1c120906110309091503070302060f0a080615190e0411 63
    0xc014046001a103003c01403c041c50b0036100c07031980f40035802081089600001900c0341d09103c1d440e402c4031407800d40d02c81e00d01c0043e01c1120107543d8407403e244840d10709501400c2e034540d10038418895a651a100e411030103519803100c0c1105554482c854404440180b14580b8564002240310b041c6010032003113a450364000c2000310180c8441d55a513a01d04215207070060809000940d082c10104e1495406501440d007003140a031400d840c00504803040c003107010706080c00b1000103100e501000103041e8180420f80c2401801d201030000e00b4010000140703402c0d10500c6403803107644003001c82ea400c5115002e210f04840c0d4410400d184404a038030000c0c0ca001c5052080780f000c03076180203120310380006c084100c5a10100062211255485604800240c41c960040e8660107101e840000310140c0d4415018110003c210304409507039884158006000c52000340c009401908418400039440c034050040d01e10200e81007168000c90202040110340c0c281c00300c01d1311508a480d2614460480d16507170300810780ba42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340914838 1250 340913588 340913611
    0xe0a020d060e1c0314010803091f03152c0c18040e0708010b0a0f0602100e0a060e0c0f2403040c03060c08010e01150e060a0c051e0d020a0305030a02071a0f 68
    0x30790b02c1c480ea5441340b00361001968070002030304402b0300d09071f0602d000d44004600d43c600010301e03420301c803420359514019422480c010320003070421480c00003a1001c3c03d0304862000f0352018050604000955407030048089540c1c0140103440e11500541300c07a4002441400c8190448050590390300205001702551403c05001d182c9440c0c1c04a510503a401801084884a600600303001ea135555000c00103109030400d11640740580f251550104116008800017000344801804507840d000c810419581894075416024403040a549044030442410050b076400052010f59540d64a038074024109040640000700298a4451031901455000d010241601c10008d8048100d076200c41d494103041c11611000c03000213480200c0d440c103e041410183c034101050b81881090300aa555070141890540020364242998145100c41c001343d04200b03100c050007841c00074040500035034400414030722004201c0030103941c0029422080020601c50b00d00544562055290f0600704503103022965241038a5826008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340916088 1250 340914838 340914841
    0x9051e0c1804060b0612060d020d02040f0606020d020c0102030720030604080c01051302030d120f0e030903070e010509040b10030c03030804050607020105070504030b040804090603080703030e0a020d060e1c0314 92
    0x2e0400f00106c503681c4003c005888015521501001020010b004c802c0360844000c21000005860720b001d48040d02e04856400f04019040840091030004a543d6501c2103500194004046d40d8011044514440d040070000504001e248440d5510000112000f605882424204018842004050720250003140000d000d5078803202030701a400e40c031206010754141c2026800c1e00c0c4190050726801c4021034591f5010400c912020403980464244490441c440c2e00001100c1902d441c05100c90b0019003007202103076400d0350411000c21808003009100030652a00c51011400100340303120144015a4056800204540c40b4600100040310a441c121100e00ca44004220524010f0181324818036241d034901d8109480c40c3c85a40d045603000d07009803502d5004210100e69500d0a0007103202541c000c002d015590101442c001b400c49800c00042c1d040b80d008124450016034442c40405107158001401141418941810506218288104916110901e240300441075010341029080941c05038101c05039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340917338 1250 340916088 340916111
    0x120e03041d19200a03113103050304061419090617010803090d0609170306010801060302030702120d0f0c1805040b06030c0705150c120a09051e0c180406 67
    0x103403146410f0b243e000071050365a2052489001d0054480c4100718600800e40102c440c0e04918030782c0c04050544900b2000c507005030407240858040207074400014070307210031580c65a140c403516030265000d4002001300002002042541030780544040101280e145010242d01c00381c09400f81035075210f000d0101d02070035100b0280d0100c240006040340d60442c082c502d00342c408402c000c0c0d074000790705046a61071764540302480030406c8085941c00100c0d050b000c043d601e041c180b001601124050b4491010075004104018105601151b2240312274507440d840743d04d03860b1030344064021704514110f204141b46807010b5001030340e0348600150503c045181e140a0740e1600c0300240000d481710000d2180d0019010001b26084d0602c41c0018583c4a0282c416100b40c0c20410400100c0301e50291100b4084c2900400c8161401402440701c40d086610100100711a110542d500d5031501e018822401c0074000781c0096001094040c40340c00c182200060034604021031200401c00c1d501010744003960142d24017800031a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340918588 1250 340917338 340917341
    0xf060108010605162a0e06030f07031212091505070e19031506050319020916171f03030314070201050106080f06031903020303160f120e03041d19 64
    0x18503440040304d0020304155512025031302d001081c038a4509003290130a140000c00500591005440c55070300780c910500f4903004051610403c00d50041a40e0490a010400181d0910040728440900d0501c0030f800016040071000a2010703400c05021038291345205000340b00c0726400030f44504034a4940e100b20801d101c0c140b094811401032603c3c01000d0300303c0d0500c080b40345015466200c400702000803c100c3c0d22100880d0034503803501204800410400b00010842c0b41040020b54020440400200400c010100080040c034040704000c5041014002051103411215000c4c0d80c108200100f09680c5503903890700600410b40d0011039070366005488086802d5620600659040314480d9075426030790307200c54040350743c9034602500701c59052107003005500500940200748044a0300a8004e15140d00d07158220503403040a00e010101008114103210820b0b64015200c01030102c079100f400910002c13544038282c41d61085803c12030b034824083c0404214149030034403e48c03240f03050701c101070b105183e400ca0050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340919838 1250 340918588 340918597
    0x103141e03090d0503071a010303080937020907020307060536030702040c03140603010905030a03021605030309011b020105010b0a08070c0c140a0b070f02010f05120f060108010605 79
    0x36081c0c00c01c00c040340c600d01d00786080300030340d07406039007a40c0c500200395443c1120380900349503810101c1302c0400104181600162815440101080a8900600ca41810144d0000c441e00319808146d01d14900c40d04180300c0d500003502450b400780c401c1426042400b07010b90f9907007018408a4549081200241d602e05103a0010b0308804c890028860219603000222907040d82c210446441070311007885210f01590f21402001400400790314000b88242c0050408040400010f10072401307a8101407048001400003c1164203400451400581310f0019003205115100040d8010b031051102209005540130706601500c40141d05505405c140c01c407a01c27042e820b0311001d111b0343d42503a1061140a2415029034149503228080385020303118011965101c2400f446240c21100c4190392480d415205424080421009042120b00c1d943c1407404076a030b000706449000c40c0c024108094008a11203640c000c5003503070412200c1c10010341d010700c0e10700350301c03a22203408a1b01c05000506880c00000c440d4041c00c01c45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340921088 1250 340919838 340919893
    0x31b0903070e18070e06180603060f1005030f0c0a0e0405120714010222290703020c0303070f1a04082209060902030a060501030209060d09080909010314 67
    0x601000e0301c0c00a140462081c01802c050702c0a200b103400f105214400d01250001c0d012108001000d420310805000941c0c5500074000d9400400406100c0d080d0740014206621969070f5070f284017503581d840c285030054441580714603058818140307501d45400e00401d0000d000c2809407030035810541d903600280794001c1c05440252032508445403a50842c175140001b0300380c040c0540d081090001c0195030a42c22a0300040556600311485450103000030600b204440c02040d498055032003507100d0b07401d403442002c09058440007031400015000200b60082c080145202da004040d20348030a41400c01c102101030031082260b003605482c02550000b0030006140c1e024680080440d8106201030510030102c0100000c0c01406114800e4001a0007440d0b0044a0141c49a164096268200f079030701c200541da0913800803410300d401841450300ca5141c95058a040b40341071040482c111205003085401482110003a6800c100120008400d010038003100401d5051031508a030506540070310200c80c03031600c84820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340922338 1250 340921088 340921093
    0x204050609041509020a05150a201b030c030303011206050108060112060507030e070602070915060c0b070c0f3002030a0e03030c0d0306180b0a090f140a02031b0903 72
    0x61003c040c20b503110641d014070141510100503106d80c0000c0c20281c4646200c102000000f84401500c4c4e440942c1000c0d41d46040c450300d11841d403884000b03840d40d050410300500c402012002124644d007c00c04a50304010203001c0e02e030350396100c092401c00110a10420390b00f01d810480000380050000800328121111550411314003031043d46d550001e080083d10003800c043c0c40303141c0760a41001c00d01c0420028140c41c0c00400804d45003010000c262101d1007280c0c1031146c010281040219000041e60340300307031b500a0181e81319980340344007641c01400480c00a0140c000013407800c0100072411107403241d0308040450700800b941c0880d07140e00c0a1f641c1d07101c4140042e0010300084c1030880c00703186850751862009041e01d0410758142992407400e140f007440c0d0000a611800304000003c20803400d4120707024505801e110081c600d002040710403840d8490140003e603900c013003040040155000f40000424a003058402d4106561040081d400540c1da1203c00303d94202c800030307c4042c04085903040c1c071001c1c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340923588 1250 340922338 340922363
    0x611030a0806060c0c0a2402120a110f06130c050d022409030303090703030305011508070815060d0501031101030204030b0a11070803040309060f052506110d0504020405060904 77
    0x784100358200c44c802452921070142e001c04250707500c1c0c60140181c03d180184400c116461048402200115116032081d5001810304559244040003120754882e800e0420180074513000e02107034600a6401c070200c4860003950148482151038410b42c2c003a043c000c0c0210685151188204030b40041c550301c00a500980c1140014046901603c40c2c0c0705902080c0c140700d081194550100c0d0540c0c1c400c48003450325400c10b603002c0c000c264051003442c0c003421903401e015243d1030035410003030400d40300584608148401140000c41c0888540014030010a0207031085845107402101030000d0030080c00101c803c01500340d1840465482882650b085070341200c0f203001a6261503803d90020300c0c503ca159404820704000d64400310300304d040294040e6120b9aa00001c031840d20380c0041c0074542418140041101c200010344c043c08840712403d45042c01075681c1703101300140e441c11000802c01c12407454410351000c80c4204405103c1d41c00144180e0080c1d800f0702842d9a00c00820142d804201d60040c4000030410303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340924838 1250 340923588 340923601
    0xc03030c02180c1611040c030f0f0204080604080c010603210801080c06040311030c0904050a0b0610050a0315080609161202090c07030e04110703120b0f060d02040b0f040611030a08 79
    0x10b1001c1e204c3e80103c3d900d002c110780900c041070a84000841007000300741c4903041110300c1038051080c507600c8941c18030114140380c10704c0704103919007001400141c0600008145807402c60790070b520610081d030340075044c503107074035601c0c0464207060b0300302d200030400f20709044000140f407000403900035200700000b007840d071500d1306594a0004448032032081c56098482c0c10f10301c1046031a100d15041c0100d01400051060000700c0c030302402d090100400840c003c0e51614803542044d6003000c2a1400000c06040c0802e441130358011510030700142340d200d182e4a120b540c0c240714282c00b0105041910750556010810b00b00c0e22040002c0b00f450f42c1c40b000175080010300d00095211914040901480340c824500300002d60b56101c00141a0768040c108e1003001e00c4001071107070030103401088401102810510501c1001c5c01200010308480702d03441e07901c1c0603920001d0010f485111301d9048401820034001819111040c0e40c00ca40700b550040d00582d03003c1902c0e1007136582e074060700000b903070000519a80c030703141141e4590 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340926088 1250 340924838 340924867
    0x108061f050f0c030a090f060f0509040e100518011802150319020d02040e2503050603190615050922030318030c0c050a0315090f0c03030c02180c 64
    0x81c1110b1540d282c0a0080c42100348003800289600000d40d59165012403d128441a4641c525070010042c0700c0801c24018045402c02c0650b0802141140c0025400040c4650740781025004004a00400d2604040004071b41c0070903c409c010102044c001c22100180c140c500100e0f11131200042d6101b50001d140780509030500b001185d01014125241c1146401903207a042a40c0200070f80d4940550042400d0000c025055010750744502d030f840c0b880340e10800500044140c2899082210200f50f01ca034009951510100840c20b101800c50300082d071001c0c0f1a04001005008a803014295035a64a0001401d490000f4407103000300f01c0340d484084911442074885940041e03900d42102850b0703c8400074060796144404820155000c0c0d287d07541042614038000904008c690000c0740705880c070300e00500201e001c00702c010030300d4185031000003141442e0741440a114601c4420003001d000c0d0b00351022040640c4a10460101c6100350b0769a4058441c0d0b900c402c405142c200c032040302d200024815a9420b8a60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340927338 1250 340926088 340926097
    0x302090c130b0c0d1701150309080f07150c02010207030f0c0f060f330504150302060c0d0e0d0210080a110d0603110306090a02060c030f0a0e0108061f05 67
    0x8240c1954101a60b80c01a4050380d042041c1c900580c0e008401c00c060004d0b048800c03008800c009440e40102e66040c210320169200800c0e18003001c15543c0c07154a01041581c83c111040059403c00c101d89504051400385015582240c580010270b041c0102d00e2101b9005000f654a0f00f035240d204c1401c02014000225103841e80c1c00400d4071421a40040400490024421041c032036020500108032040c0241c2c2d07010141a2101d04152661181300c8500024198a03500105030342d801c417008980789580c6082e20103d60f903943c002a41c1302034001001401030341c000543e44d0404c1001d07140c040d4002c006204000310101801c5000c0e40241542404481d0703188602a6240d10009111000500c00ca02e4200340703480707400121412284a81d03481c02841481410a13040f038004000320300401c4146404480070352a100321550003805900c0224030b001c9070401c10310942d0054408030036040c0d141c0200c6031004203500305000202e80418240401314483e03092080d07010715034040c10040c82c442440030500c121100d502 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340928588 1250 340927338 340927357
    0x180b090f13080d1b020c010e0102061506071a010305060109200f3117031206010504120c1d1302100c050105010b0415050c060601200a0605090d0302040302090c 70
    0x7410044000912910b21564295940c04001000801400c4e5406850710b65007034071050501c004900f00195580e4001072841d8400c0b0640c24030800c504030325010698500840c9002000c02a06020000c1603001840340541200e004000b224803a17640c585030002107a81d034501e0350481c0d0307007035000e40c2814119420080858240d1100c409180001144107c24050407158109101d207118045054030388260300300b680003620302c0340d000042940c1800c40c1c0313559134420480041e10503086080002c555030b0046050b83c008180c080320500c0811030900c0d000d590310429024106600c21a1001540103031441e0014a108044410420180b094a42c08000350a891014a42e04101c03140e842c21000510078081c0600820043c0000383c0c486080942c6030f6698401d403060442009010f105000d44100001446a00040203003400900f29120300c1c07905c8161446a180c0401e41c1c41100c0c0c0e510108584e0b540050311540035241a40d034074011042040f0140d104911010b540306151002044058005d58000c24442c1c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340929838 1250 340928588 340928603
    0x616060c120510060f020c0604140f030303160f050703050901120b03030a0305040221071e0e07120b060310050112090b01060f02010608070f0b030a06080106180b090f13 74
    0x101c80c82103405440301240c0541114003103e10400140d81c00007100e210622a074005000e4041d002404100c050085115005418000c807e4201e00d50b1505099100d4038140541529528540050741c070302074058421b5020000b4001620b04102944070320181d4584540c50303030300d81d45000020001180c0410000414004807580c511088103599020801000344880b02d4801003018545401017040e100030003e44d0601c0d0707403440b80102c0c0702c5103000300e0904107a581e00412a0100440c811905132070107000d07085918424020f1052103121074008941103940210765400340100480f01003840b407140001e07900c0c005000030403201885130350302888181007000080e41e00001e4054141d258a0b100117400e82c400c00101b070400c51048400340c0d0a00031600030308001c00080c1251481e1100001d50314109201700700070410701001060100b0a83d40001c0c2c0100f450390000d0000980300d08103440881d00e007800080025280075482c0404d400c0071540640f0500c05200011110707a9601065507039030926503000c50315071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340931088 1250 340929838 340929857
    0x108010e0a060504020c010c02060f040f20091003021309050309120307171308030702060f09010203070605010806061201061a0a12060b040306060b07050618150c13050616060c 77
    0x182c944e48098081810360000109010100100c060b04161000e0440040d1120300070030003001c14a1500c202d41510f0380180000c14095502112459280341607240642c8041c0c2e041c24041c5001159000307030180ca000b11180017500b1400710441044401910004003103800621481c50140f4040a181c420940c3c50303800e50b458140742c0c0e070351b4813101c2d8000980d14004280126804000307500c402c0e407a002030660440110310344492600051701600640300068607026001400e071039940d10a01c00e442c0c0f515402602070005503100e003500b541350f0204441c1c2c903000340b04258101410b0081401920201e5a803d0405180045070031070700030066202015000a0094036440c6400301110740c443c0800601c9948800d0352101d0851400c1003e0725819841041d8901090081201003007021038440c0e00034445450f48022403503403180311420072640802200e9040211401c02504243c018003d00102d0034240c0c050480310b86407410803071640640442c02030100c032444140000140c0c00d600801e40d800c01c3d810040200c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340932338 1250 340931088 340931099
    0x405041104080c0a0b180609130903080603150c0304020402040e01120c14060a032c1b0a0803030c031e010321030513080304020d06020a0207080f030304020108010e0a06 74
    0x180c41041645012180002900700b2444000380016074486008880e40c640480c980040c5007024020030300707210350500440c40402095900d41c421100a0b85000d850850740010442d00d4000805c0060010b401080b03166001412a00c0e001c1000c081c80907000e4406141601c800c0e000303c0320380d0401481260429400c1101113191244c481903030b8000d16540c4540800c00c41346281800148909034405c01d20301c10b4514a265813aa1640c060b9030024002c2e150024903103440c8110160380d00b050400903aa600300140760402c00a01c00700d0201d19000e000c10705022148900d006000300c2488038400c043c1903803c244041069814280003c60708108010740c0300c43c00c0d40c007d1095000108003a0f004580034072440f0b1862503405242c0c10300800e110205e0070200005c1c1381c0729001c00010005248020b0a090b00080010115500c5c483c0c800451500481c7c115240d001050010f56103441c503000b4504503129505500d0303030f01c04000048a01c07881d410f0f9074a03031080c4d10b4aa607900c01f90b0005040150039a4855001103407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340933588 1250 340932338 340932341
    0xa030b0f0414070f020a11041806061511030c1c0e1e100f0e0103020706020f041706100b09040b0301180507090c020601031a07050d0603060b040e03070b0a0b06040504 73
    0x412150b014001c01540c1808000034040c140150940015900a02010f201246010654844071002070310080340c0751814030454034417050b5882c00107141510b00f803004290094074000a1010b00420744401c8043c07180075a803595640519140301400f94040c02c5038000454513072484204903800e0341003044460183c1400100c4c4101c0000c24440044494030358a070340c0b498503400d0f6400e402c1013414a411001d119040041104d034506800d103041c5600003d1510820407590304803007188110740891502c440d215210204111705104520700301c1c3c403489020a001c3e01d0390746d21440803940d480c02d0b5240741507541d40c180400f038001c0e4a0f589a16550b5090320502c013180340600c1c0c1e43e0740d900c1000902165810a03080000701c07001c03400710701c04640c8440018030014150301c1a0041003802d800c525002503855034000c8403144905504072640030300300b000002c02c00100780c01c83d40322150115401d0204124640e2926900e015001003d03210300d03802808a40d0001441d486005a0310010708400d10306a140e00c0400d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340934838 1250 340933588 340933601
    0x305031615020c03030a050c13030221120702010f2a060212070e030d03090201021515190303030605060307080f0a0204081203040c1514090103060315050a051b0a030b0f04 75
    0xa0f81d4100104100c150800c501c641e640c0441048185800c100030018120158280d6000c001d000b106001c070000c110105003502c84622000b44001c0390250701c2c0141e9514401e1304140402c0340460420352044180754007607123020381c02c1d8041c01660300101c10081c0600304a40c0e03030300354180d407a40d40c01c01041c0400e104448002c1e02c0356540d9100c1d6a03040b00400305052a20844a180104061030b1805000050782d010074030880e0f00c80802d120440c0d80d21201d541c003030f104002400c8a6400a0205420034550300030150403000c0302d009480801201c0d544005108052008031541800156007130002070741c2c144044900d0340c1101c1c500343c0040c14984c584182500d050005480700d55170707100100c200000c102d992503009020f07280204c2040d0381016490809000c4004521100302c0044d008500104140d00c00da03c004025a040070451110b21b0450b1820310051000f0340e040c2c902e0300d04000c00100c2c1e40141c054480e00c50440c05003e1442c00009210840003010707075940503035210507008002c4c000c03507480f8061007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340936088 1250 340934838 340934857
    0x90206120403031a040506060d09080409061e0905010f030303020c0a0213020705060a020405010246060b190504020c0102120a02040e0708090606010e031e030405030106060504030503161502 83
    0x242d1070211307000d9a400c0d00c45000030740703200d10b00f80420060180c4449081d02c80c400104100403034010b040d8035240007240199001103400310324000001444070042d8101840d0805200d01845005441d01c07041e03010340d0f0090203130718400003410200704000b034400d40c01800303030400d07140035603580103d168005203050700d00c088506485034000c2011f2080c84414055240c0180130020114981454a000130303450f030f04041c85070840500358440c003422201e000302d41d011002c01c03c00104000d92826450401c0703114403440c000d40300319280c210304030038905048108551540790000404503c62038082040069840001e82041554090220303580052003401c00c680911111a030240c0c80e0790a000c0302c2050800014500c40800481c0001e124280c00c0108166800840a20b8000510301d80140800e10b0882c03810000c1061507641d03149031070214800300242040c1c40c4218001d0194617601c0340100c601e03000e5400007801a800030008803414a0600342025041441544250229215418604101c0e001001030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340937338 1250 340936088 340936091
    0xc02120105090f0115051818060703050412171f0b07080910020313090207060204081014091f020313290105040207081b0c04060305010e0f0601081009020612040303 72
    0x181255180c3c2030080380344242032182858192468240050484000414203401d000b14440105c0d44040715260071451442c3d01004441d55403c1030ba4000b401400100c0301030f204481d8001c85840071610802640803a80f10100308642c0c5501d8040301008032480400d10040b04840c09100010450311840160102c103000b408040c0cac4910821050040c0c0b500c0d5500c501d000c41d0005c102001c40d0030320802d001403d80b0481e140c0161580120b2620100070b01c501c1d08049001e12451050103440e40841d000700610022044900c482900c8114000e95250311189044031801055501000410003a9000e55030042803000030b94003240b4a07881c0c6880001304003a0850030380000c40a461840ca108010300e90041500752001c501d0100301d0f44500803203001d4602c101400c1c86003011040826001045914144c64000308100840390381c0385082402804070b039035031203850b0199045400f000704001c41e21a04035661500600301d03a22810301000c1c02880c10980481e80003105110301d99a1100741d0f8031042c031491080d1030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340938588 1250 340937338 340937353
    0x2030910020609070b120103030e01021002041e21030e03190f0b06060703050909190e010f1b050406140c010212010501110d0f0f0c05100204061e08070c0212010509 72
    0x64242000459041403c540ca001c0081080380c420041b0b4490441750145030002403110690300403404d01c1029201400a14004100884c500c0480480c51029041d06104035414640d10841e100035440a000804403518001e07480b41d01181c0201034514000d000141510034002e060032500407845040e00d030980b425404000203000300010b9408042d00300c542100d00d030b804c21382c8540d402040e610500c0b45040c0030319021004551003401e41500c000d410111540c06025400b070402105008016940e1400c4500b4206040c1c2d80000e02c01040c03015170055140e07182e62a15003002c1e003d82e9001141010100c0b100710400c0507004ca00000c3c0f0282c03840a580350034003c4a0b514080004010300e0b0441600c8c515504480c1a84802c1d5400a00004004800d81000000c4800528040d5000508007101070300c0c500515805482c074140030b0b4001e0040e24950b0b00c3c0c0e0312620300d0208080719201044c603031810202e0300750f04c0401d0603d130040818418543c401044400428940400e01d42034400640c0d090146612122 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340939838 1250 340938588 340938601
    0x30703020a051509070302010f050d0905014805040306090614070f170709170307021801030b0a0906021b0106060207091505040507020a05060103080711090405030a0807020309100206 80
    0x140f031021090000d0040c3d402c100b0380c0d41d9282c41c003e2200a0500c001501515900d5005000b0744100e01d0f201c800400204915050040c003074240400030a002105a50310917418031604a000744001c03280103607815000030040e0340c0d854003417600140b40082c07103010f0000000241450041c0c0400501c680c1011032200700c081180c8503000e40240c007450900152541595a255001900114614108032482d40e41d440f902429100540d607234104000100d01c1e8200010400307000001004070718404e5404114040700c01d01034454881b402e0000510315020304012030388403001c170f03000050814000c0400620f440c0e211071440c01c40c4e8080c251120070594456004003d40b0750180840c41c001c00b000c04d418006858401c400b00101e09450152611450303a980114498034400c2103104901030f0321204075015540c4a050600300754001d0101198501ca0380850481c0314240022401c6c012a80311008604180316004256103180009117104110300c002c1c080703440d140d514880500e8060340355802403c2c1d513081c00c0d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340941088 1250 340939838 340939843
    0xc03060b0604050108061003060f0b0c0f01020f04032d060509070602030313030305220c080d05040e0a0203071812110616080a050408010c08010501200d031a03030703020a05 76
    0x303240389114200030300081003580d07000400c503540410708860340091116402070a80080010b41c00506840c44890800300301c000c0990300401c210000001198500c495480042d4240d11440d030030321a0340341082c401000001c0440050a103132003041c40602290442031000703034800c901a09025500f480e103807010f01c45030210a0001802920703091014500c0c624104c0200c0c18081007045c2c0c01404c0503507480c0050720040200622001010003108501035042840c1004903002c401400390001d28000e07a40702161450040c0304580c1100c2d202d110754040c40d0f48481c0e030503000b50001000d0000788061124900e100304410007001028164001403800070304524280000d204c0c05003d0250b014030030401075140e8226610b8110380b410ba80c0000e01d04d517504190b1100302c3d20b5000304d0b40170200540c00c1402d40503440e500012001d060312800c0c0d845040d00007652031888041e040b039030304500b0301d5001180d00306a1203100350442400e06814013860001400b41c000882e1550707001c0c10007a801a00301c56410410400c06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340942338 1250 340941088 340941101
    0x803040314070e100e0a050f1810050a02090a0611071403011805342112020a0312150e0703060e0901020d0b19060f09080f0c0a080f190611070c0306 65
    0x2d1007c112528140c0b952205003040a040381d0864101d031801d0030442c060801080501507041e800c20300140c18a511900040e41140340618850229100041900340c4070b601041c000e0145071006214107454001410007050011100903015500c440d007405140701ba45100a406600c14030060071100c18080300c403d030513020481e402c003080d02c01d111010414030311000d244d0b05582c04510700200e05107807031500705814008404000c1c6084001041d01103d11b402080c410340850081d11405a00001c81d4079403402c40d0000151740f0f03c5403000c0c4005111180c40d00341060b0307120312213050010340d01d40c0300c1c20b4080261900320303034034002070b03400195039201404280241035440209644912441f40c40c000c1200c868186800b8810410800c400c5440074588200055030081c4031403010b030342d40c01e403010074401d40316026020400d00400340d010001514003400500c1580302c42d00c000141541c04540c0108007001010740b4001e80d051f035140e48c2c00b60705000c10f903c018441e41c0c1c800c1e440401c01501d14a404419a070b80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340943588 1250 340942338 340942351
    0x190b07080618102105100f140406020d061d0a09171201050f0f01090b16020a030501020901020f0601210f140a030e0409080703230a03020a11070803040314070e100e 72
    0x64421880c0001a00003501c0940c851b60b450380841e40c58841d040080c01040a8516404000000402d000500070290b0003005240c0c0c0503101803217004d0f1210045040c1260907000c1051141d1000006004440c0d10350106003c0791007002070800c1c1042c20703541000c29410404201040c1119940100001e20701140c44000d9140c0c03c0d50080301030a81c40b800601802d0700c51090910580c0001a0340c00d0140d95041201da0f107940c01440715034030985a0034194001e400c51034081e0701611031508c6142075001e0004105040b50052208144030802d200184041e110380c007030046038254800b0101e4800159130240c82102c0c40507800c0100006142c0e402c00510070455071300d01d540154130f84040c05000c6414002112076440c1c150820b641120b10909106400e43c01e140308480c0405408100810640c1e0f05800a0001c041130f41c1d203d0b00c000c0f0061248640740c071000e00c03d02030544c0c0100010070000d4281040300c8080700c00c0100752007100365141d100c40f1312400b0840b00005207a000304d000340030100c40340c1d06a60f04400e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340944838 1250 340943588 340943639
    0x10b0a0305030f0313020a0f051c05070b0901210c09090603031e050715060612020405060301091d0a0f0303140f1f0506040f0503190b0708061810 64
    0x500d151911074070307482020b40e0345502c041c0010003e4816842e02108603100c07039000d800c0888896551101030380c140040e000781c0380b0906071008401ea41111030004040c944da00400902051454040030302c05550001c04260306100c1420042c601d058050502141ca01904034004100806a003100810f085055041003070100d2910f401440803a0303028100781410960005414081c440b07444064841c1c2c014030100410040c00350f803e481c81c0108580011044170100e407184560121414034910a0b4021801010340024090004112103e001c1e04100c0748606a0002020030640c114003e44c1010040c01042e81c11a070605100170405034188180760711815690903c0c590fa041c49403418100c0b40300a0010349894000120204610003110170020080c94000c0c2035130fa41d9030343d41c17618074003510080c4a1144a03004030070901d030220310641260242ca41e84468230302d01c25079035003209035580d14000e0302980d0000002c81c00501d041982078206409148540c0407140041e00c1c20211081041c2d0841d080103144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340946088 1250 340944838 340944859
    0x3312010f0605161211160e07020106030f060c09030209070e03060a020304020d030c02012007090c090608040b0912040801050402030705030c0f06030a0e12040f060e130510080d11010b 80
    0x101e08840e00c9104180d0310041481d024013103d2000c0351014101c8031011114002d00c14039003560740410b02c0040c101c500035402248140da03158010303422542c16200c00f6045000640e070141c0014096400034500d42c0b00d0382000844c541c0c82c1d8020803582001180c0fa000860b2200d04242c607a458100420355020700e02c0c0005628500c0c2c181c1c080b901c0d55100040040900040610040071a0b02a0412440c400f40c8844001e140803410141103a8a400601c180c40720249000c4590006500c45c0700104240e0740241c41c0c3c03e1711174883c2c4d502c804075004000d28492540c051115040c84102024008200030440c40001140605040c01018102009648007034401d900190718044582c40d81d20194098080c1102c29684983d5400c1c100300c083c06032500100c03050301541d00079200c0d80340d46001070425110407a01c00640d103503c510041e0303010384061084c10b0344030702d5580007440454095040307103600815140d444110a40d4a50074a0328100910047c4c0c408101c1184904001b40000d200307030184d00c00c0442e00c03601031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340947338 1250 340946088 340946107
    0x8090102210f3102031f09030905040606020c011404050d0804030221060a0b03010b090f040308011d06060a05071a0105100903170306031c080103030807020c3312010f0605 75
    0x200c1e84190050082025212003203021342d602030007885c1e2140c1c1752840400500c401440980c0041440e000c00301e000c110510320110380c5003800c1c4103040a9400c540c00800407031a1550041d41e00c1442000d4403115860200800f0845031035920b003801d05944201c0000740c80d14110310410500100440c03400145c034484089001d0081c80008840b03400c90000c00740000d40074034040201e40502040d4481c3c9801881140901251300062140ea07071080e03000e607a8480c405c3c0d0301c80c108851030200748074a0345c0c000800c41000c900c2a2030f0140c010002c00348603007006841c102559484040a0308003800c140d0041e14031100400083c1400c01c3c40c20b4110413107140213003c55041d680e41034401061012180300b00c00b004000034001c2c2c1c604000040260044200011041c0c502680090950303600340000c4001070f81e501d000c224414000590b5000395400140080940018030710000010261090700560b0b003c0150b80080100503508014400203600b0500c00c980b560401c1440400f580c107903403101e82006810000c00c440f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340948588 1250 340947338 340947391
    0x150605070224040b040b04060e100804081c050a0b0f1002060a090221010c090509060d031202040b07080909090a020d122a030f020d0f08090102210f 65
    0xa1401d050680141d00b04a0841d038034500c1c0c01180c114000c0020b0024010940c52580130151080780d00d81d660320164015030000b40041440460814400305a44001040014031114041d101b9080c50a4015101700803e013122015200280c4441e42d02c80e940d5903c080c010b040a12080c02c0f000750607107070200c0300c10f072000c0025650300000740743c180026580d1507801e045659201802c06e44602201041200000329803566000380350005580c800720382020000595402c0c42c1c440030344118401004481140043c2d2020b855008850844044865003000003003a0000c412000d0100c040c0185100c544850284081c07000e5904c01420890a43e0f0103c0d410b080143e642c480703a00002035205074090003c00304540103940c2501804000b0b2841c01d141e10700081c0c04c103607500001e8a100d000750b550031a114000c10060340c0302c0561461800c001905210240c1c05c1600900107240c01601600005180170010740310b01040082c1010000583c0d41141d042c0045d0b00c02220300c031904aa1404e840801e2011030051448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340949838 1250 340948588 340948609
    0xb06060a020d031a060403230109030507060f06030b0c1308070806041203060504050f090d080708060609010e1f17010b0405100314090d1103070b010e190e011506050702 74
    0x10142c84042d104130412142002c0f0f614070401501d02c40e1580d0300c07407816481e444d480c809a5008420528060425828140688c0842c69019201c80d0701c3c0c031100c0d480d030038050700e084207121a030940ca846000002550804545125411429500e5100c111489551581b0b0a0541c040c010303a9000e514240403070003001c604190001e0303022005091620038800183c02034001540f11561180c5020204100791210004944c442c1040c9025618144a908401d5460038801e030303003540009071000005103203814100010080180c0c14109601c04001020005603070029a0040d001d070f0408100508000d59040b15002803d048035109070fa07400d6040c5241e0b0500d03030180344221441031844401090f11b2501942c0040c81903503c1d086800e13900e182107420f590b40d1307021025142d00000c0b049800f1081c110804401d0743c20480d84002480802d918144200000079800760900c5036550340114810001d003a00d200700340e110308100f00040f940104445242d040400582e00510502c541001020010b030b80b0300c40d410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340951088 1250 340949838 340949863
    0x2c0f0c100507050a0519020a080307031706060f03390723030d0b09010605041a0703020f06070c03031b2309150d1d15060d020406030605040b06060a02 66
    0x1d0312840301d41040f602d052003404028055000359070302a40d10301100a0a81c40080c000c2e99203010007599a03042c295207100b890000340024040c4040b075000340e51900080fa42015006101e1030401c084450003d42d10340c01541d04045c010080c440340c0e0034080c05204001c07408040c1d0705907006d140400204216040c4680c084c0201200548008000224003d681c0c541e01d000d02d4000300d0341c0325a01c800c0180001d011004120303200300130100000544a00c84d2046034280c07131185814025640c51030b820300d030180d088200120b0950080d036404405a18040150754880c41503562028800b800d1418045d003143e85010002810b030071245035030f088054000314100b000c111404c115003200d280c40074188140c1d000c0d10b0301c001d2f07110b510088088428a074050241c2100b4422400c01c0241c910749110024949070b080c0c08070715068000d0050303500c49005034100301350b00c160007901c1554000c150b68006421a44160800c945196840d41030005115100c5445940981d0a0790041c0c80d1118030301029550301d20040e001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340952338 1250 340951088 340951097
    0xb090108061b04030c081015050f0411091918020a0c0b0a0603080c01090308150a0b0a0e04021207020f0a020a05040921170c09100c062c0f0c10 63
    0xb0600070109407400c4030b00464020302c80405058a030a0220f071100c101001440040c5e0030042c804000704202642e1104544004110b041c0c00c040d0760040c8005040c02051301c00326042d043c40502680d0b1204171810140e000781c0300002032103506104000480382010200c800d5400d10511660201e0b81e041038000d00043c0d00104500709568480701f1050141025030030081101c0e0000c00e200c501c82d08150040100382e4403a8588054580c5c1f01c3c1210614204c0c01c01903598021180c08040000c410300c81d00a0500c1e29452074403000d000f0303002d40420241d034800c0855040c0202480100104580d06015014900d05040b0192a6030141500050420f002c83c0c01554800c0e66101d1905041102218401200d849000400e030b0450b00408000350104104000456100103000002024019510200e982000000b400700b203289035400c1007110740f08841e0f041250381c1590382c0008a0040344012003c001c8039420200117400e10010382842d8103201d00e030000e0001581c000c900d4021141d035030304104004d03100380c0d140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340953588 1250 340952338 340952371
    0x9030905090c09180a1a06070f050312010807090c031401090f1e141f1a0403060905071a040305060105100311040608060a0f030519030e0a12060b09010806 68
    0x1103038031103100f20114240c0c403042c0c10070310140c40501e00036043c2c8199000d09007000071100c1403000840c00103202c1c0300650321031420844040012a01c4400d01401402101224100710092a4083c5050300a1b080260294008542046450307041d0140500104141c0340a1250007072840031054003000600646239513503100c0b4110911540c41d03600019452510541c4d1100045400e88608001c004800702c0350708403000310000507401a50100c104041000c0b600000454601c2c0a83c07041c00c480c002403c1c1c002d060010000000030541e6400744010290181000c0c0022618142100981025040c4203251584043c07000f040410804209a41190015294884a0800000120000c0ca803d41c40081348200c04503021404540c010794061140c4e10580755101c00c035468030341d100c14000d5035200c0240745a2041ca45070f00c03640e240000c0d08003400e110f410050520100240000c240164a80041800e00013404561043c0065400360301808407003039401000a50604900383e032108002461030004215002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340954838 1250 340953588 340953601
    0x17040b1603050f2802030915030702010b06070302010c020d0201050c04030f0503040b13090c02010b0f04150b0301080c090c13050d08070b010b030609240f150c07060f030903090509 79
    0x4003101d00500c283c05249a032014030403144071407200325100e0390f1404101d04000c5109140000304580702031b90020041c0d001c4059461a0705426800148000b0441d522000c001d0060307100c203005840001e1080d000800d50383c032000002803030510950502000c5a041000740294000901c0448040d2900107050700c1c1d096686041c020320354480d90381f01ca03200600000e80100c110840c84a00307810344404c100c0034003500b902c2d0003049080e951003007501d59203c9007152403134a0700d2526900885400700100d10302240e40344c0d5151442041d8009a0240c1e01c0e0390050201e44100e40351101c0c3d2243c0c8002c41203822400c0180b100c50142800940b4000d40f4060006003081c4414090030200760344186903c500c1c6511030750303103400d17000307446800c1603820340d0144000d400440c8240d00e503401d15858494242a003415444000004c120488008186031038100c20381041c0b0055424100d0020040c50200e000200b40b0140307016401400b43e4116108001094a400c456038006a84a10031108a440444948081c0e45522 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340956088 1250 340954838 340954847
    0x6010c063b01050709091a040905030901090e04051018050a0510060518070815030a1a0705040605041202150a020a2604050d050a050d050717040b1603 66
    0x204a041d4856200c01601201c9903038070159070715841002807644100480c00c007009801d0b00e40a81d034010100300001c40520542d0340301d501941c00e91300002414a800c000140100d800c940c1072000a071210b0f000000d0701401540c00483c0c881c000c203c0780c0f04032004c2c2e240c1a290180c0381c1003980d8000c480c80340c03030300da031040701c1d51401e511640c6c081d07040420394605c84440c2c42c2003a5142c0e2402519020642040000202407400c50104020f0750204240142c1582d200c0f0700444603220018a0786441000708a440407082c3c40800c40b200036184900000074079038522160a1394840b4000785004104007007084280003c43d404826281225218020341c207818110744001002001810206501703450042800c01d505580096072a40780c0f4040c2e583c3d14803012000c03d050304d0501d00e141d5000000c1504205c00c112500b80810803541241c01031040d070b0011440d981c3c40e40e08003c0003405080c000b81c0c1c0810713682c1c18010941c030201510121400b10a14081c581104060301c3c0c0141001404002210700015080c10b014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340957338 1250 340956088 340956101
    0x71a040c150203040f05041107030309050712080403060b09040201050a031112041505100605120a0e0f031c05011406030a0e03040f140f0306040f080403020a03080901020f06040b06010c06 82
    0x21801100003003001c0c00c0000c0d929049441903215028862400107000d050510911800301c1c2515090342ca8890b0948007600a0301e040f07001100e8510403000d000801c046444040780003070b445012255901d500c0c1d410078000391071440824520400c1c08005100040c3e0300441118a859011309002c01c0852602440b03003500c1c001d01566000070f501c0300d003c100400440c0200c404d03104001c4c40701002951110400110303aa0f54070300407800400c80c00c0200101c11581c40c0720059020326195400b2501000590010b42130041510304840700c2d0f8408140e040a6003030b030102c83c14484009810070845503151540c04e06070000c44592042c01442d000012650441d90340d0884841070705400200c0f07a94541e10407500c80c00310010710840c0c020115503410350115203002ca50b4500b000c48000c00070711182e1902d4980325244c200380d59080790ac400c000c110000041c1c0740d000b25140214002c6610381d44845090001a0411640c41e803501400c0d040f6004000014801c4022290810020b180032094039240f4a00304005008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340958588 1250 340957338 340957349
    0x120106050d080a110a0209010611010912020a03120506030d08060d0b040b01170318091008070603140f1608191406120601080a03050706021c140606071a040c 69
    0x900240741404801d00091407055015070760310700d00c4030b420507080d80c5600000c00000d600c020004010040c4900c180000c0e040421040c0000520000c036175525058040c21910b0303d40540c11020340302041c1604030001391581c0019090600c00d52404030006910303080800c00c1d01d01403055071800728920703403030b56800c864440d5401902070009090608207400c03100c000f44035400c41d0b16000020306840c20b41c0803055544103070070086412202d0100300c0c00c200070303800d0081104403c04c0051500080c5200200060b40042c11140c13400240c0030307450200031280b140001c261102100c2800d0900180407180c5008419003031580c50024041c1e200e000781c07081000310440c001a0f0301401c0104003440030302d0200300741d8002c0004a8006d42d5440a0b4030700c245d2502c0d4240304209440c7c014a00341c0c0701280c050001884814400d24005141c14840b44c0e8009000c0801c09417074031401e5440c1c01c10022030b0031440300c440d00a1400c40c3c01a0a240d825501e100760000400c002c91481e00070903011504129840318090050036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340959838 1250 340958588 340958599
    0x3180111250f0b04110a080a050303010e071701090b041505090f0612010f0f0e0a0210052a030c0c010302030c09120106053a0b010302041d070807030b0f100512010605 73
    0x10a810105c207404400700c041441400d10400019520b4400122802035580c40b1000d1401c0da0310344080c14000000080c4420248541070300c8240321480780003a104e0107802c0e0701100003201240d840c03c1c002180c0b004120224040741c110010701080d551000607a03400464120062201c2e030b6840041030349920f140d00c000702c0d1507007464100714140107030340c00051048266039001c020f01c2520805a66543ca074607031019400c1241c40450780c1195102d60001c14400386036084040c0620041441e56066041b0507203048d50b0764202141c250303071031101441480c1c00b8001c240307815800c50800b2030003119140b01c0e41840520400160005181c088020341040004010090560107024001545088854511b080d6010004500c00583e8001c2200c0b204490f001a00038919454503801c540c244001400b070351010301e001d80385881c0d039180d5003c010402400a4a4440b0103400c48a14520700075081080181c02d10582004040420004801c4c020b502d9045900803607031080920303070500d051130040005410854101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340961088 1250 340959838 340959841
    0x10b1903050111041202010c0602070816050d0207030c090207020f03070f05010816020a020f0d02041a0103200f160b010b2a0a080c0f0303180111250f0b 67
    0x480268501046038015002407106400c48841141c1e60700c20360085803000d003140326880016501c918000340361350b40b051000600c1c00040e034948080c0d0f40c010b0b07400242d080c05202c15500030420113000e004145001400244102d60840d074503520128280d000700b4142c143c2c085640c01c195580ca0b402c204040390054151044603171503d04070580071005000e4031740411160741c08070320540724100300458130b034915901a15114080e507080010705403010074685d03400480344d040080542c0d12481200c0c4403900410b04c1a4680c092140054290b51903921140c819041d00a04455800d508400300c0365aa08201c0700e503942d5050800881d40d041000c040007410300a000000481c1c02d20202c402071807201d14540c02410701c440c3c00a448108038914035040324403908400700d4040040c0011010381002c0750b600d001d0302c0b0f48036004003c452454004031401007200101000010b00c2c000300b0321540c050403002c81111440c0204204100300701400075106600c1100d440880441030040c480c2280c0b036965400a10750100703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340962338 1250 340961088 340961119
    0x90f080303010905071b030e0f09180115030c17011b09080c27180328031b0507050c0a060f030b010203090f06070602090909030403032a14010b 63
    0x3680c1090040d03412062410010a80403402074048606a890607075214001c0384c1c3e00c0d501101e8030004e868005401c2a0081c00c0c6415075902c0303030001441540030f032030380300c14501c0d010121900b95484202d05925041012105001003200e903014170040c1d500343c6884400c4a071640101d07030300402420300300603280b090066102040e41d5000c4001f100311b440748811076200310156002c01c03041c2038003079043d820503500140030100c01c440d029001d9540710070907680780c05411810400c0c40f0308642c0030b020f003d0b01c00343c03901202140d15604801112a001500d00c1c0c1042003180500e8489136010300c00c0882424024049410410440208100240441c01618844155542da44003501b02901d90480c81d000c81d0030113083d440d265200000f540c2040380014040550400d58100380040c0303034403401c016951581c08001c401c5981e15882c6001c0d0041c1c0d2028011a6518694180204403e840940703442d40020b405151031551200c000c001c00707807141c0150f4000000144c0c414030328010070184d510140c200d1443d84941c0c62 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340963588 1250 340962338 340962343
    0x819091e0c0806010914010509091e01140a060302090402060c0f0703030c03020d230706021215100504060e040f1b091e05150703050f04030c170a150c090f08 69
    0x110b4441408440d4183d80f224043d8044e03031000760a150442c10300000421480c94507100550300054800103030351006c0078900c00da4480c8a0240142c140513074555080d950540f441a24903a404098040308111607421540051844140500003030300c6030f01d0110b28061401e40510038000e000342c80500300d0701c9c1280e8a140241489841c0720707054015008804400990130700a40485100c03ca0300103494814241241d03804103543c00420b4280c0340c0f2a0f00380900455140010740c0580140e0240118428012130b40e000c0008400c070415440b02008001d000c20031400350803401c0c0600c1c0031000c031400314603e4034010500b002000c01401c10305245840401070314a05420032542c405980c4c861032404042100e10461100700c410301d119994211104900101290303583c90054080d20307203e85400b0b80341030112698030750703190020f802c00e56090340061001c10510069010340d1400150301c00280c10b4461076602c640c0907a100084e00d00780c0043e250644040124865030a82025046040c41040f8041d2190041076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340964838 1250 340963588 340963613
    0xc040c110303091516140c030c340f0308030c07050307030e0a150516141209040f05070c020f0a05060f070c0503030708180105040f090902100819091e 66
    0x8001e43e1100100b00502d041d4010080405c03102d441e10100c2e8504c00003618690313440700080a409000c1070080505000c030500805c0f5002200d082440d242c80440c0e14880d52104100c070f040146e01c85540410820011804403017411203800c8241582c403030f510412070740541e109a5600030154000020041e040680003018600700000c240c0e84882031985a0182c141480e0701d403c40040070404c10302c440c903901c0300f02d43c041110385842481103000f624070980350180f50694120382e00c60f05003808244a041800d1a1159a18006a03048184024281010050320b54948400081c0c003031200d1086004035a126180c0c44801018007612035a9600d280800961041d0400d030000c0700c010005110000b07040c60000152076020703410855982c50008000da12200300718036049090305004044c071001481c080c6684124004008200d00800c41c1c00135881001603241e4040700e0700703003804191400d108044480040603003844d00a100300186001840c01d00c04410300c1031a6126031086100c0d00360404100201c074003003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340966088 1250 340964838 340964863
    0x1505180a080607140a09050d050f071212031803121113140904120c060b03060c07120801180902040213080706020f0d0e1e0904080c070504020405030c040c11030309 72
    0x810080c0c01c207500c4c6800788511588240080c0100c0c8081c01145171000348e0744145d40c82003040380c41180d18a540035090000c0c03540b00301e0101d5152402d00062041000074214550201e150401c0480c0f107048040c625500403d00c050b081110300000c41d0000c05190f4003800d401a55041540e44a9031003080d0540f0045190041080045041d52030708502d0070b100524030b0040740d212034040c0110344030000c22111564826001d40d0344d55200c1c40c5003071660b2400d11105000d4070f40c003d400f582d6120f0506102c24070300c10013610907041005139001001613800010b4500c3c0e02c5505080c001c24000401d0002034003034069095900c501d82c50542e00001c10003400a0524115480303602620302c88102d04101e035480e035021103002c0000c03c412000405452070301c48004e901982c0240c4e510031820000c000407604500c0100c0301100d680d03c001512600800c0700f0800030000303000403181035240c03d00b0400482d456040000c80c42d4000ea1b1200601c00c2198050071449104e0b8000c0030407a0f8407890050301c50340d91403640c484003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340967338 1250 340966088 340966097
    0xc071406090c0108040809010311040905010e042010272607030c0302220905010c0e03030703020a0611040b160204060f030206120a0e011410060206011505180a080607 73
    0xb08025540141c140a220765000707540035080228110055014294120440410110400020072003116500c070301406080e842c800f0311002d01c0c0c0361a006400030001502000820403082d81c0d40e010395190300e0705c200d80c440c4a01d002c0c010480b072124051030b119180781980400c4c012444010070950318142e442e03082d01840e0441e04420070750b41810203894440a00004c0e000700f158080500241c10f0013101c00083d080e034014000302d907502c1c40303415808650740d0010403241070751a1250020007940c0f1060000d00ca1100310044e41c580340803550080d50741c0389501d0008040c00e03110800c030295129a08280c400074102d00ca4680c4d501e11128010002c0c19002a100301c2c0308a2420340301003196084885200c0507260b014200d245020b0030380d81d2500082b20001c00e00d880c00c07a01ca04d0310b040700607028080c00411030780c00d0580460f1402c080046070821a400c0c1c004030119803201e0010490400001d501120b00206414541c1c0c0e1003403402c00d092050a113000c08607400000034000000c200000040007885000c240ea134 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340968588 1250 340967338 340967353
    0x4080910020f010c05120109050105030703080a0e0406060c050106050a181d12130e01030c140a05040222050409030806010f0c060504030f0f0c0b012309010f0303080702010b1005030c07140609 84
    0x4009c40c3c40a01499405a0090005000041c41c40b4014051a032302410460400000c020008080d80c4498003c20002086803ea020811900340240405010121902118030342401e00300c88004c032f000d002d1038092a482d402210140705040070b01d48000340c458011b40d04290380c0c410161540e60b115514000080406500c009014804c110703500341aa03600808800031189480920580d41100781110b0354404401940003550303aa43e032000f0300c04100c03415450200344a0301803a1030707000e800f2940a1340c0500d0074001c0c44130001e40c1c0800134507881702090814001c0000011404c813004403a103280205164a09401c0c0410316410103995505c2e40000c0e81c84910070000d46004480c1080d00e26002000c0c4078145c001400030b000d0600c43e0900c00f0805480d0500707000e00010014000c070000f80d0010380b0341d8803140d02c18402d050b405034500303501c04030358002845051591808581140c0b1340c07014580c10400c1c0803000c40c0c0c01000171421581040d03040403040c1702c041703554041079840f0003054406000c1c0c0e129109 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340969838 1250 340968588 340968599
    0x90c0c0f060c0912010b04050109230408160c0815010f08150109050714070605060103110c03090402031302041d061e0a020703181503050a0504080910020f010c051201 73
    0x5400c80c0b007850040726050400d211503040c4101d0800704074460f41c07203540396034034a281034031a4820321f40289070309000407462100803200c1c030105042551940c0050030800c0200004103c201d4100c0304c0c0d0a104100750340903284941458105a00740f5006840d2278010740100141d600400201207041e50280f000285005a4480019582c0d40c0c40044e80340c1c241c0d2074480100992070312940304a5208a1604005090880001008690703a020440c102d651075034490070b00c14156810300c40d500507c40c14034816844c044014000b1581c038044c0500541c4625000070004880d6005002502180355000e0824400b00010180e010510f000c280180070061103050002100c0c1c4819103900d6103554140307451550306440f0225500c0181d402400c0070f8052184d6942c0308090600e202c0d8044000380004072a103004050b1181009017500d5001d008a1520b41c00e040502002c1451a421115000d2003102c0160148444810603400d0040712107011240354030704800540110b4008006041048120076a00c10316a200e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340971088 1250 340969838 340969843
    0x30804230d11120a030908061005241c020331021c0507060f03050c070b0f04020a03050102030703020c0c0a0806040f1a010f03030f0c080306061305090c0c0f 69
    0x1802919402146031a0071804074074103154030300712520003a0001146112110200e46443d0600008900103140c03000c0800041c14140600ca0b00121040c6081601c245070a000800c00850b01440c0716214501c3c00c101c0b04449007040450b80c4d8001014805201801d1014001d402034100311101d90b684640b10001c03903d2140843c15850007100240d02d010700c94005602441024030401c41c0000c038051400c0310716008900c04101d54002071401366182e0b00b04001000000b02514005452194882c409110000009550809071a801040b00c0e0f8080c2c0e031680c0760700000d11590b60b1540702800a5200109000310240e0680043c000500364008440340104000e082c0a03051001e0311071140a50418004540000c00c0701088104e114001c15035449000c00c030b0650041c0c000340a80c0038010a14040700100105904592404400c556508180d1403036440da49a51001d848001d1019118240c0020b40301c4504600c02c5950000e04070140403907006290040b4035a07460b512483c0406940e22807801c900e410031000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340972338 1250 340971088 340971149
    0x201050a0507121805030d0203071103070f080a02210409061403060105041d10060302090a140a0b04060f03060b010e030d0509100c05010e060402090a0c0801210c030804 74
    0x8640d200620f5512800501000700b0404010341400d098000c902004544100090440a10756050050b9039040c41400a44840c2010030703547d941c1d400a100f5180480d02c04040664965042090035030b80f90180d6504a08010700f0540114190400c2c010b228038076403429020704151504d40ca4200b180179190403402c17085c0c210030605158154041e10060000b420940c00107055074010742300d6442e900700d100c0e0510b42481d4042d90540000b42d0307920b10030425450104040c941146000404004101e04031000202401d0020000e207074040d1620700d01010794540f40d001500615403032000f401da064580c584a0043c1c041020032900044070f036a020821490081044204003c040d250389140c8540326040c007420459441c1c003001803000704801d0f45c3c04600c0a01500b02c0310310310a00500001d24080c030401071081000380c40c0d088064030340350404894980000c8160305641190b42d814070408100e90100f0f50b00c040e0400000c281e0100c4d00710020030040e807480030700142c0d4031114400401c010200e4040140380d85 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340973588 1250 340972338 340972351
    0x1101030605032a060301031b06141b0c0613150306080a031d060a02010509060a06120f020402040317040609060201050c040504020313060c0f0206010503070602120d061e060201050a05 80
    0x85240c3d200160b0010b49458060b0800811200d4241d104250001301329801c260310039600001024000760078030b00c0c44104807024291604020103005240f450143e200d018000d507543c0f8000c40810400d14100d0104000801c12000422455891907058038801519003144501003901e44859100c005050013070007084152001d900040c052034015803802c9031050b0b20302c082c100704800d4048818925483e014001d00c0900680d8001080508100f00d0386c1d85061030007000b030b01185240001c01d102e0400c08090071010241c02c01c508089112007800010028850351340f0052a00306891000e405890f00a03000d041140c1880c1c44141d000b90f0b959006900740c070001c070388005211204004c18005031a1660155400582444c0a0800c00fa225940c0b00101c9881d001e10101080c00b001e58040455070400c4400d000d4a01a0007405201c8d26084019640e01001011007143c00008911003806c50726551000004182e16004c4034424848880c03551202d00083c081d0741c0c019420080011708841e158021680980f8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340974838 1250 340973588 340973593
    0x10200d02062e0f140103110a0f180303090e0106030905030415030e0106140a12020603072601030317160804030e04060806040803150108070c0209070c0b04030c110103060503 76
    0x1d80381803000750b2071a18041d9084041c1c078500328564035500c050305900040c0072101030100c0c84a00b0000c0039480c40004e10728190400d414114148020800e0200b5102c0b00841428a8040300712450300c00c0c0c502d50b8103600120900034615900009140d48507040d03c00f1545110500022641c9402088040d00d0300c040010b0003a074000c04c020840065048900010b648040c07a0004484251a00990940b0225403010a41e51900e02c0c40f03818500d0054001e00007005256120382c030790142a030119449020082c00c98040c41100c0c002802c141c001e1a4441840d49440100c210b00c80d0784a140103481d942d01050350342243d03c1c0c07660004104002102032484a14800d8444c2d0880d40d8440e0340c1118111303040c2d02c4840d0021340b541c10008034a81c0c10042d43e801984140c0c41c03103890307142c0410103441072401039100c14100529502172040141d003002c0d02c0b04072079030141c4100d81c140d0f94182c4181c400b903221000c003c0c03803039000d80204414181d1000c0c82c1040d007442099000000e400c41001181078030140d004056054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340976088 1250 340974838 340974841
    0x504020c0c24160201050f070501050a06081506090604020408060406020c1612021002071a090f0105040303080a09020d020a0b03040c0e0106050405040f18050a050c030d090e04020f10200d0206 84
    0x2100840b60f40301052051411529180001800c10416001403104841030f07910355050003002c4460b030181501803e0320720000c00143c205920610128035010f40590f00440b441e2001c0303500c2d41c496404580180c040391085802c5810309240c240025400740500c0402c9014689a41704030000445201c0d00300e0f44c048072100561a40c030f408020050742e0a4410f070f4154421000c0003e007090294021200158450206548a040035001d0003240d020528030241003080802062002030b810802c2250000e954510000f01c44400c1e2001c80e101340b901a5000e5408000240000780400c0c0c8035000b14483c80c41307244070f00781031645c80040b10001a804e014441c0414810310082c0002d0401d0b5000301101302c81d259021940302314640d0b416179405074040064a070340d040f5140e48401d014040003c10b000d040300754010800f9901404004200c2d100e0b502500c44803150140100d015540c699125400311203004260085081441c800038060810804000032565600340c0c000001903008034070362848003641c3d00542040e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340977338 1250 340976088 340976107
    0xe100311010c0203070f0f09021e0c010e0a0f03031d03160302150108061006020d0503150310060f081902090a050601210c200d030b0a0504020c0c24 65
    0xe8145003001074100540c01c405038016a038100820402424035040d03101d001404c11045c071078606410341240c240d0038010030060544100d81308411013a44207100213161075401d41c0007458003400f019010b05189120b00c10030301090010441d841990644039071030030855012002e0080c9010440b00101c4c9010b0b400c203001c071621050401c007a00e40540c0c0f192041c0c500346003440801c5611080c003a0011000395100504111903503426501031005001c00317000400784c0390a034001c0100301d4030006103050307074100f2600180c1070291010408810301c0c2080100c18080991180c10400c4903600900c070b00240352141d80748155403103951400d803103d20394001d4049a815640e052000380940009444141001a01070b1046106140ca0800d00042205101c010444801000004007101b614030702b414031048494034042c0b02c0c01e1000031030312241d003220f080102e451a82e0f100085c07e07100b9580c3c44160014000904101508030204201c0c661900c100d501241c0f1024100b0401d440a2084a1240c551001004469031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340978588 1250 340977338 340977353
    0x3160f14160e090f0601090c0c05060114031203010e04151e09030f030b01200316080702030709061d0709080f030d0f0506011709010609090311011a0a06110a02030114070305010e1003 80
    0x652302d145003465540d950301903a82902e401c4090f030203480d042004803841101d91078141700440c2482d04101c0d21504550501d11741c040c1d01304019000600c0c2c05030080c02462b034240960419210321110784840e40001c84581c01e10006045503140072000604500c03901111640644a65070610354181d6171a02c015215410392101904c10140c003101c0ca200070f0140b02030202160380d41c0540b146c41000e18a445001600c141031510307049805c40907006050040911061400040010303054943c01801c00d084e40340d510094503040f81715000841d20307000f280e011101c003100000c000c20584d2142c9008001d80c003401800c0c481214015981036000415a07000d0000c4441944c1295402c0803541c00001489603540c2000d500700c40e0000011404120000c451940001081c070807900b00042c99180d802c540500b510000380d079103480c1e01940060081c1d502c0141e0100350104120405264050000c21101440c100d82200d1080308582c4900001c0c104400403500381a43d00f0212702a40c00003011900b00750942c0d60700321 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340979838 1250 340978588 340978601
    0x2030f06090d120f05070909060b040b030415090c14031b09010519121a06010e1c170c0a1e0309030305030402030a060908091203160f14160e090f060109 67
    0x54071562a001040c1044c50b6a1107864010041c603210007000c246040b09004c1514003c0d803140764042070500c03040010300c0e66201140d500586c03180c1c504100c02155001c2d400105908900a840004040408211514812300c1c104482d01c08800b19000b4898049035040c0e0050070102c5507400a101c480100010704118002081150f140c514a80002c0e4441031014151180400e0659041039102d51210242000054480c0c00060a1800d001c40c90b250001084441c442c00c801900856800c0541d402804060506200d11031600000107544143c01b0884599a074015001500d003c0715002c030030484a680b109400024076130640b83c0341c21003460f41e201600c035038000800c140c0c0c250040d0000d1000044c02031292181c2d882c420480161506a04d006000103000e90a0303100701030360720801407001e1a241600c01401d030700342e10502c083c966804d503290a01d500814404500014440c0c011024202c1104607180d4080d629815801d01c084c0e941c4000041e540e83c000344151790640c12807001801103510603000b62 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340981088 1250 340979838 340979867
    0x20c0301110408070e1b120610050a0905060f0f04080a03030b0315010902030a06150207060906050a0c0f030507080706020403061a130c0509121f0e190519030c02030f06090d 76
    0x36a9541154400d035046c1c1d4801401102034840c404100142440c064400840755801032800905004410340060201004c6004243c80348a002c100041c290820724111013860f6400d405980d1034070f94900b4100e689081c0d0741c00c2100424108490a07036a0300b030000b14030025a144a0114076103901c0c1040610007540b02614154240780c4484000ca5048042100704510940c6907005144072032030b000f00101111111b03000340042040800c4004010360348401904101c90300100d505c04801c00d08d15084d03d1a02c504038004101c080082084400e0243e079501070300c02c50f0f0003554140046a180c6238180c1c242c003c1c1c075031269406880312220040a00c416407018003070103018104a4a4104090001500c071141c046000d2059070010001c00000a9400c03200c00080c9440102841942d950500c0c454548070f01c0e000e0300b02007580c40140c1c0810321100300706114404a840494082980160a00034541611a0000c0e40a0b202d00510100c208100003142845aa410700c0030b440b000106903000c951501d1901002d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340982338 1250 340981088 340981111
    0x30d021605040b090a050901020712020a03020609340905100e090a031407060b06031017010e0307080a02030d0f050105091503060a0b0a0806010f26060705070f050706020c0301110408070e 82
    0x502b8001394010449000520a40e001800d0951881c500286480c0008007a599540c000a0800c0004080180d0461004220454005038512005206131288001c1e0f030181d10300500308801c1c04100040c4484020940e0080c132074a095590380d0002c466130b5600c2c060700083c00201c01100580c002941c05018201081c858580413a014072610300240703d40d002900c40b00c20307010034420104109469901d6003014290124001d0000d41124032816449018000000c0c02d00032001031400c034074520078011210140441b40c000c1086981080a01c002841d09008050040300d004012030346000881c5165200c07060020f00403d0709550b90b003045001ba0010302c43c1d0075001081004d010900d99010b0040750b01800300369540c410018a02184e1355070a00302000d084508410740c01c0548026200450381c01c1d4004810b04015540d1800d600d003030307201200d0071207020340240500d44011440c0c80d80880d012500c11703003c074001d110b030b40400148110188500e2142c07580300d030300c200002c000c0c1c2c2001003c0242c1c8107441025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340983588 1250 340982338 340982347
    0x5160320030309090a0e0106090b03100e0718020a090e060d060e010204050d1a0c07030c060506060d150807051c020f0f031501030201170f24030d021605040b090a05090102 75
    0x101310a0281a101194101e459810480380701000744151002019889803d02941c45a000402d8880f01c4c010724005640703403907042103c0110410070541c402460b00344084419800c5240041c0000d4200d160f070280014002c2c40005100240c3e00401801010700a04018000c0703802e235900f400401809602d845555024000001c81f5a9082c03101542c01d40101c8222566801401035080081c1d0300800420300d0700c2e0180401e00105e47c1c0444800c2d9001c0d403000000503103884a10000300a8000c955440c3d034000d06154004500358100b0b040380049429810860b0031990300c80e001c010212404038a001450000000c03840050301d00f0607420801d851002c0c00501d085200e810109003403c1421007168038103100b0a00401c03c43d640816505190007420a00a0150a00c100c1403442500c0203031030a40c440600300c1c10103011103101c0001301c1d01320400404450140a0446019495540011855042030441540080c0a081c18001d13904000c2000341194201c0e5203c525100050501802c03a29840d0760921 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340984838 1250 340983588 340983607
    0xc0a0e011413090609090f080705120c0f060106110a0609060b0603040c14010c02010512090f0f0d030506120a030c0314030103210e0102060601050f0c010f09051603200303 75
    0x1c008882c1d40e403030307a550b2250515020b0016154940e100345842072900f00c905002c44d40e0091001c2115078444461959044507040441c5850610650100c6105002460142c1d009000030720701c43c07410350310058850031b070380e5140161040a0b41d20b16041442d0484480303000021840d6201400491103514005031102c41b850101e44240c008a500300e0f01501c1c00034051200304212804444014424600a503541c90301d940000c11a01458003c107044000d140d0102e140c5503001d05c05030407800344070411169855036101030b0585c2e80402d5001100403914000c040b9205040942603d680d004105000700a20411a9000c44507542601030583c10080840c03103013002c0caa01c4d00019402140a94201c003420520303122165401002d0b090420240070a1581d07078903080c2d80100d02c2e2540b00100b400d0892b2220800c8400d4811071044900034040303035184c5000d881c8904007039403113004031030302950440f0b14042041c51351190210f0719002c05071400da0050200c10203400d9070701c0003a01c4403401809803424100d901d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340986088 1250 340984838 340984877
    0x711030f070602040f1a07020d031b0303060f080f281a01060f08040209040204050901090f0b0108160b0d0f090f061a190302040c02150f0901060902030c0a0e01 70
    0x441c0407900c10b82c0000d400c0080c0071050369680090301c0c419414103030780c05c0c000024942c54030400f90024001c049000c10102814041c0c104c990650440c000403400c141c00501d070042c000d112500400100380ca842001140c3c03500c00084101e0004d080704003e003a0f0301d00e142c544840006002c0006043d20580c40001710004090b02808060740a400d007400b0159418600050b160441c400e020f0010010756400b00005a82c4003010283c01039010b0394001481d89400c180d890240583c0400a8542c6403004142d13800c0101400c1918101c50b51407094904020144004803090512f0b4840d0302030010342400042245403166102540d0b00c0d403040170006605100d90b44001c2c407580b008006840703155843d00000103c1c107008191007411801202d000c240c290005130001744210042c040640075035911500d0030801d42c003c10100351819489649070b00e04d441d00300c0446400e0b00080760b00e9000c0e9424072000140c01c503214020b0b680a000a2903c1504040040100b01c40c035030f0035800114100118403021200480302c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340987338 1250 340986088 340986097
    0x203071502031c05160c06021b06090f0604021011100c1106061005120408070f05100e010504030c0b250f090e0105060a08090f10020a110607080711030f 67
    0x11a0051521034042c404002a0f80502c0e61424291908010401000311080b00081d030341d1015500f0071039202c0b0794500300030009005403017a0401d1450103e00301d40c142c520004200b8030030103001d011189150f12800e8803540b111710541d0003d4201494042c40755100e4010081001d9440340c0c0400c440725603050410000a42d0311303901c1d0345404104070148200c10b9a10034007003d544960242c40d40310446580c1d00d4010118070458041008041c650804601007020351002c446129401c4a1a500d080c03625003003103a19480f0460b4a10041464020f8501010b201802018811901902c440d944003205440300514104003d00c0e6000c02c3d50342e0421291000d0903000f11459000c00755444071107120700c0306000340050116800242c8100641801041a0390311501243e260802c1480c1084003078441b291154a020003030400160180540d903000c40302038045034040e2403034200960325880160840600c183d16214140c51000000300c072000028103540c0140056210300b40901d003181c0c0307070846203005400070750031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340988588 1250 340987338 340987379
    0x9060a120f110d0c140a0501020706030f0e0d03061805102102040509011508030705060105040902181f090c09061b020a0e041a150d031101052707140607020307 70
    0x41e1003009015007280c00d888005c172540242c5d4640e110380c0c288030010b0f5988015100308810540c03a403201104200003900255414542c5400304c6800103003440c0094041c080a00503240c140030140000d2403809024021103018188074a9115007103402c01c803035402080160ba0b512618481350401d86c00041e03d940c45014407915002c4000503d42c181c08144c000c1c490b03499842030200d0380c014170802c4041840800c03064115501141d000695082520116000c21035091400300c5205c260010404911850750060070011074000203d5000c5440700c403890111804003540c4400681d1403c1c00741f120078009d040080e40c02880a9108041c80400d0780001c60141450b003200344025000c40c180010800b02c0444403454900d113540f14041481c041e0003544c203854400304680d10075464030350000c0515009200000c03440c0050030081c85286818410010b8050488248855002e0791070641c04008030049844000d80d6941070f0b00c001150602002c01c449904140c10599041c0035800c0f0000314400c0701241080c20301e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340989838 1250 340988588 340988603
    0x504030f02150c0705100c02010207090b01020a0206040e070e0607030813080d02040303051207081b09010c0c080307051e03090121020a0f030c14030612010608061509060a120f110d 79
    0x1405d16040c4144d240340c0c0540340b003e000c00c545131000140e03004998102501d4400b840041c8018900c00100e00d0000e0025000c0e4016500080119a40181001240c0301c0c030101d4942440c903006070310030b00c1040c1c8248031380500080c01520210340501c2d2048041c014940c011402c1c0c03410403000e4080310f4201e900962046000c9100014042c90800303002940982c0b0800e541040c0380305281c4400010b400721114600c1603401d04002604100f141c0c011002c1c00c42c4590807044102102d611005841d94952100c0016036492080050314890f1039000058403411408178005182420305c0c11005594014241c0c00c0e110a041b804404c03001040c16510141618060b03658440032000c400c40d40290844444a48400c100040206540301a0700708c1421686c1121044d1180c0940103181c003242c5004041c1d5400051081c05400d0500c12411429034002541040495102d0000d444e10f03820000702ca00342e489041c00004c0c0503105c490200e145202a4102507001d0300c411020a00540005164048188012079691 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340991088 1250 340989838 340989853
    0x2001110f03180d0c03031b060507031a0901031110140a03290603070804141b010314160e0307030506011d060d020f04020d090c03080307030507020307030504030f02150c 74
    0x402c105962049900b1060352248810400398448905805003800301409000307800e1401041c600720071210b052a80d0b00300e01c08014a01308403d0090143c208409a0b900d8a41c41081185052400c000043d040300d174402c6000308880200b009212100ea402007211080c42009140d00b00644540001010300c40d00d10b540000303044040d200c0c22070ae2103413451030741000342c8031104603003041d611103908607a0808207906100e0b070103503158608000030844660195030503010710601c09107040391507054000032a800f600d040c86a05002400354041ba0b100f1520074409601c0e251003194024024140001140009405c0e500e04585a440340307407070401700b131340700f08901c070412041068604068500c698019000311145d12148944e83c002504200e455001305201d2036002445054504e000c0e80240c600640c42141c0b401c3d4a0b507281021b401d160400c41e0b9040210f4102400602c8080c400b00444903580d41c1516160309060075615500711210140100702e81106100000c103968034107881c0035248a047e9840203001e103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340992338 1250 340991088 340991107
    0x3040c0608100f140616030c02031e06060d081b0c011d030a02130b15030f1503060417040e0408090a0b040501090e04060603021c060b0303072001110f03 67
    0x204603005105145480c8102003e00050029585600460301611120707040f10020301d0014150340302c0c04c10780c4510a030b8144c100c6001c15800044c007088042c02101520501c40da00c10914580b1640c290043c034580c1c00c244002070b0a03250140e079820380580130700d101c10304042c00c00034410324100303141c1c0001e041c0e580004009289583c1c0401c40e202c0a55502c0c407600081c401c2d00002c40d1351f50203100d000902c50040c821014201d0480795010403480d9500030a0005d0f1103411048503483d40d4419605907211000c04400110b0380c0121310280e540000c4084e0080070680c1c2ca41c2c40e50224403409034450000040304010018490601003c014000d82c010000b11381e64641120421520a140d940600014117080c002005540c3e00304070100b0403a004404051400c0d641c80c034092000f00142e0308001e5000b9a0488010180850500011002c2e81728800410200b0280010955640034000000304881599900c0141e07115100040c45072116060500071083d880382882c0b2401d0103009100c0d11441c0c0e1003c40e00781031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340993588 1250 340992338 340992347
    0x30109200604061e110303070512010803070f0305031504050f0a0e0d0f230a1707090311010f0c050a05250b0d0209060d0608010507030e03090307090e07080303040c06 73
    0x104488120340c9280b9082c68000081c00c4000050b41c019402c2c1c800603e0030706100e01494a20224040d030b031042e81c0d070b81e151280d4090400d402c02d4a9440fa00f900000c00861090b800004a5400c0d03504441c1d00e10000e1f4240d9011652a4802051f0345c40c613451004440c10a40c540c4c1c02070502490441d41140d8842c1307402c26103481250400c1c1074540d00c540c480545440d089400c00360200b5681481d203880e01e1703030490506050174541d1480f0400000c212001404083c07142d8008008080110042280304051319001c10440d803640050201600c1c088000708445010340c050b1000c0150840382341403411034a01980c80e92410694090710035140d541202c80d64107072024010081c16001d214042d0f520a049041081800840c05001c147c401065070000f1300103003e40d600401d03104003200e10030090100d261110a0070b400703400d040d01c00300007003170505501c54100c00c008400d4810907500980141041880c0c5400c01c400344c40e907064580c0841c080c2e1700022540784824401984600c0c051101c1c44c54192600d04020b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340994838 1250 340993588 340993643
    0x403020c09091515030a08120109060503030403030203041211030d020f190b0118020906130302010801091107020906060d0207061401081504030503060316141813031d030109 76
    0x1100c98002524480034000c020581135000800308140010480c60a80070a2030001200c0002d0004c110200320a80c1c08085d44420303074141c41080700c2c05c0c00b040b82d8032804d051707990145000080c00b6810611080c4960b40e407102c02016054000c500100d00c0240321310209041c4400c0e0729000006801c60314841107450401c22912148042c0c1080c80e840c24035060301c640c8010103060042240f0600300240741d0780250005e0701070b50b0b00304800400b1690388a44983d4000b0300603a00c0d00c8206d0105030003100000b50417840344250140359110300714191820380c0c40d9003040010500200b40c00e5102ea03052003400103849280c4090055244240300004800520240c20304c3d03001d105070f10180b005e50101700a895002c82c00124250855418286280c0301d40310280043e0078441d005080e044150528880010808040354121804a2043e11554552036090349100c40e040070803145000220354000703219000a10481d40040b10300301c0c2e03c400342d401c44407000010b420750700020006d4540100c000c080c1d1002090715004203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340996088 1250 340994838 340994851
    0xb06090604060f180f03110604080f0f10050c030703090c0f09090606090209210c0d0804061e020705010c020a0306050f07120b1c0201170106030c0e04060503030405040203130b0403020c09 82
    0x442503840c244003c0303105d010b0760000505401068400341303415220138068034080c120107002e94407140c40d48801d607940c40b0300c507a4010195200e03514400c0407030f024500c80c05001d00e01402c070113450755039a40000e4000e4040c00400f00c81c14030b29000000785c41d001c1460740c00040c0c4850880402e4000940c1400410baa2564102122841c410040c2541c19611000840748c00710f5206425584c01c00c00201480c1807611244410f80c00c0100044000308102c0c0d404000c10a545072500c0f00400250120b42c0c007125200081505000760303010f480148060746c051090b80381c01610050160481c1e945a6451005594050720510962034556090000043d0000301c440421519280108080c0d0148000107603480b1101321211031001c1707140000c0056921a944140d14580031981d03038803855a6845c402802030001201420000e24441c0c03141c2030f20b140034010301701141d00040c015800c090a00003004001d5101510101d907511658070860300040552001504ca41d01a070040c028000e1102d0030300c85000801040c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340997338 1250 340996088 340996127
    0x60f07022109010c02030f0109210e0a0303300e010b011d060702040f1503020a0b04060504030602090316240305011206050702031309050105030c0a06020d030b06090604060f 76
    0xa20007400600d030548101d5402440d04284008880c000b190500c070001d01281c10a5080404d94418090302c2c424440c0c01900c0f1142009407803031203640032100038080b000710561242100c2820408248115140c002c02e03910501144420503140040b8442d210710590300d5228961034075880c1901110030301c00ca1041c19000e080c5105819840702d14499640c0d80130018900ca10000320700a000e640301c6038080c0300d00d450004401c1006800c00c1c01320382502a0140300c12441822100e0001c698081280241c8085807207a8460a003040e04542d03909003c2e4002100e841d0b010701c00c0700d4a0f44104c101300740d0400014019070031510800e1080c580751901310b20f10b1480302001c1c90b06160041046c5100d5822010329a500280700151a4135142c03003c0742140b18480103030920002d030110200e00201c0a50080f4100c0b40308a088a500210307140500a55000328031404004d60000440c444025000741c00404031044000c101360319150b600070000e000ca8020340c00000016008092181e0500d0308140490003d8158118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340998588 1250 340997338 340997383
    0x2040614090c07060603170d05240402030405012a0905090606092413060201061211010804030903080a08370c03020403050604030c02130221060111060f0702 69
    0x414041c180103800d404400a00040e42010300034503a12100186502882130307261a040881e00c00b00c02d0f0000c01c1d1411159252001103849240500780790810482702c580c0b0101c11404407820000250001070042d0340380d548030f8000004007400c10b03a86d0341401e00d1406c50203440702e005e10001001064981c120070700914600052004035903400050341c160307590880706400442d00706111541481c0c400080020040c2020480054041e58418400d050740c01300d44c000c1201c1d654071041840c61901c0650081c0284840005603207282d40300d094030700d600c00c1c02030804a015580d01d0b6a851995031040031b1090000350a002482142d01c203800002100401c090000c0f1020340d107c501c140070004135101120320441c0e4030311030b8002c1203005c1e4040e81c00968020b070669800b840c29040160001d50310300070403445800c0b00c0e900c0400c40d203160708c2960350810100680c07540f003c20b200082030010402a1101d030521019a5408a14603000c11080b8800e10f41c0512117003050500c041c019103003280c800b503a148030441031318 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340999838 1250 340998588 340998629
    0x41203050609061e0a0609060f0507020d020f06040806090307020a12032a0212010e0c15040b03180105040c08060a0606021b120703050a17090102030315040b0a080703020406 76
    0x200706600450102e888003000d24840051100d02c45058a013590080386000c3e0001d21650006200401c80c0d80540b40d840c020101c000085801e4480c0950083d0720003103080a040143c10444e50185050304060000351074a512010341c68602001110400e0041d44000b0302c210440c240390754088001d190002d60407071a400e8a580c040d00910416910300486d03070001407850307079940034801080080d5801a281181c0e40103044e00b80e0340681004034190b007180c8100c11845070603041550401c81001400566a402e203400c003001280310380d01c05444048400008000440c4046007031080e50301641c07240e10458266860f080c1207608010005041000381e070320f02142013200725008503440044c280d072000700c403683c03211240002d0042d00f07500407140d08901c54070101104122002a62110050046480740d8544943c4003a10f21503100f401d9900380140c1050010520403407960300c0b44568400028404140b00c080c400100324140c0269028002030b5000000400540c203061107603d024080303d10201401c0b00080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341001088 1250 340999838 340999849
    0xd17280807030b030705060c01090606051c06020d021e07050c040b1c050304091407090506070201090909060f1505120604020136260a050d031e060e0412030506 70
    0x20101c0003495210141c2c0c001c07130b0780d0a00882000c0d1100502030b03901c072447c0c001c4060007080b24003001c46081e031602d6404105d525203038a5240c5c001100c207860003007171a00da41d10000070707400a4440301c600c16024400b01d0500345441d211200812901226903443e0b4109061261902c0002c039a4140039514101c842002a2142901c1d1105103a610343c080350300c03008500d03140c1d1440c8900d0340080946450100030015048006051602844055a42800782a107c00400c02507200762040240071640e00308041010390072030341156030b91501031403000843d030803e0001c407000d403240b80d1600c4c1e419141712002408240780580e00f00b01420b03040070007004103180c5980044e00c0f4140041c0201c10455110b27158102c0c0080c0b241c0003900150402d018034a000b6503c3d010510704030614804082d07010307c4510510550300c40040c1b110102d9410200810200340700000540050005100f01440c8034144960101011014001c0f2401000c611303001c240300349000c0c2882000b40d00061881d90401d41801c0c10300c07000b070307444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341002338 1250 341001088 341001091
    0xa23120a090c0b09010c1e12140a030f090c0f060207091b080c071509021c051c0201020f0c060403080f0112150b09100801061d01090b0d172808 63
    0x43c16405941d1a140d41c0141d501c41c800100007001614400c51915a09410b0041c01c00303958070582106010081301181610000d00c41107032048601024000c50006d10302c02c1c1c0010300f4603083d2080000c0d410705285c0f5105010071239504031009210312100200542603041003190010411180200088805420b08100e111030403002d1000b08040360000c6032642c4044800c864400b54403031440405034000c4803801002d40013154091f4807612142d61030030051400740301c0500e80340e0b0f4403501528034840343c11080012400b1441c110021994207001030420344100b100203000600003000102018905803800410342d21004110302d5a0008440041000ca000094040c4280d903000000300c18951658210f0b0000301501d120ba95130103100a001d015002c85504200010350341e41d44000e0042c5c6454803c03108200c06c0c683d00580444003403500401109205030b116040310003006196801219681e114404001d40c040340007121518000b81100905e459410148500d0f05013200c211041554045c000d00f04c40390 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341003588 1250 341002338 341002349
    0x4140307080910210903020d0c02010f032406021005061c0803070c060203010e0601080f070e0f04060b03091b090c0d0b040906050106030b090901050c040b0a23120a090c 74
    0xc15211071041034050b0342c0003078040f0007089100340481c0c01c5901002c080c10740070001b0740160243c94600c049991203508207910168040c0c480c02e8403450300400840060034100311030280c2c0305507021403040b0703074402c0c5000c400202600c1c0d005140c0100030a8800381110000f41000744520112060f06102c000fa480980d01d4403504005402d840b40d070303a95010340344c1c44604c280003070142c0c0c40000041041e40300c0e100785900075070080e80e0304002d960b40d1804c14a0b03c9202030f240f0201103540b184150240785000c800c044034488014002140c010f0f6540840200e0f038006403640c83d219000707054071400444068014451451046484400c40d0600309401055481041d003c03500c1d1581711081020251202c2c1c100070138107503201c00c08201c3c940c1d440074000c00501c42c0031030080c80382d0304a2012840c0e82c40c050003054090038800c201c407440e1070300c0e11444404540c0048003902c1840b04103001039601709504464042040d80000d840c42e550080d0b80350002d04810010035141d5050300d0040000c0200e0642d071076076800d581 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341004838 1250 341003588 341003599
    0xd0515030a080d0e0d050a031505031009060b1206010e07020d0f05070f1703010f0b090a0b07021f020c1f0206010b0d150902040905011a03070315080a0b041403070809 73
    0x2614005824060b020107a4031041e244640306103e845d40c0c0d4807030001d111585046d6010441e03054690064880400c1c5486900e42c50361000c0c4801d02003103203e41c0500c6415204800c001079604a20f00440c0309180c8403002e141302d44c1c115000400c410034032151460b030300c10310a201403c1c601c9142c030005080e100400c0b55000410402144e03180820503241c07440445540c00010840c0100c2d080c504c8203200d07034400d0140940b00c4880803400036114003070b442598450a0b00503c81656103041400c000c07056041100c2c00c4c4d900c400207420003200c070300054107007400c14541540944946c000000901c405140d101c45440c0c8a401c0c40b03d5805070056000c05c1003410b4400d26910143d844041b0181c01016040004601d0740a0110010005000300903071b004104031669107806000a0780e0341e001081100031004003101614400300009042c043c400d0b40851034151000f403421207120b0300e40380507a142c8205400d00312850350b41202404241300c040d2200c1203118408030019031810012f039445000901801e0140360280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341006088 1250 341004838 341004847
    0x2190305030f1b0d0e0d02030c0a0b13080d0902030c420a0908010e06070503040b0405031b0303040303060e0705090411090301020310090b06120112020103061a0d0515030a08 76
    0x29243e03080a160f030305031210071042d11031034451103540c002c120809002507144180000e004200303001109032128000300ba0701074103a0340115110324028034802080e50341d0198103a6412000039211740094142d01e0036400700018903150324410706140c070162940c480c0c0700f10602d8240c030340c1d21441418241610300355400e2a20340180080d0307520340103203409903e0021b001c40118402040710382c0702c000b101c1100c3d1614028070031210560052600c5160590f01c01d400100100000b03030128141918098100e0b11070000c17280b1308490040c400b9010f010201c40320090b07403c0003041c0020705505004480190003115900301c0c1d03d080041c1d0140c800d02c90400603500403500c4240ca440c21204940a0714901b400180095540385000c4408002e0070100b130203222926841d1858141081c24084151044040700484948060b400c4c480900c000c50072140c02241090b03100c05000c0341004c50491000750301070140d46600c0c1c842d03001c0d694400644900a000c12600000c0c40140041030b0b0700005c15901c0079801140751a9074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341007194 1106 341006088 341006101
    0x150801050613050108130512030613050705090d05070f080309030d030b01090501030e0a1502040510030b09180f07030528020d06151d01050102190305030f 68
    0xc845030b81d0140415405645144d4100c0c0c414481885d500540f41d45007450132102e1121548003903404010f01a50b414040c1c000041545113450a2000e031074004c000810358084c40300e41034841c86040a011003806018048240a0607070b5020b45c0740c03429140e01105680f98000003800340079204150030b482e07200d44684038156450f04140c1d0781d054190325040044000e400d6200c540d00c2c01e802041c00c040c001a0f03d07440c1415104030b401002503101d031f1a080403c01030b00720380808642854141a00c106240c0d440e404280d92000a2420801d82903013150541840c00061849981082c440d481000c020b100002684400c5240ea100000034141e41d503032a400c82c860000c2d80029040030319020404001001c0f500580c40242d070803000c00a03c584d8809601d0f0716450f110440300350031442c0000611407540d0510401e000420440c001c0004026142d6004000f4407008001100c48000807020891 = true := by decide +kernel

theorem cover : BRFrame.Cov 340827338 341007194 := by
  have h0 := BRFrame.cov_init 340827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 340827338 ≤ n) (h2 : n < 341007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
