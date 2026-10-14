-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:13:15.751431+00:00
-- url     : https://prove2.me/submissions/0d89dca5-ec22-4af8-9870-2408dd597e26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58453240 ≤ n < 58633096 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58454490 1250 58453240 58453243
    0x3040e0a020705010912090819020d030302130b0c0703030905030303150f030106090f020304060c050a02030a0e12030d0605090709050906060304080708040308070308060909060f04030216060c021809 87
    0x15000c5154198000303101c1d02005002d5000c408200c4d0700412201c00c200c692100640120003a100301c9104d0700408440505482c010120100b070700b9401404014000b106441c1200290030110366220f40591070031001c40e01c0ca9040014050f003106540040210030305619006000b2085684102c0c003991007481031200c80c00005022002c0568142c0704031040e01e40000c0040d025010a520103440c0707d01d000556102005190000c0d440f0b00d020340c1091004501c075060848007440748040900042e08144420141c141c031883d89600c41c40002800449100050700507a82554000c90040c0c1a15030703241c20420613030400013040d0380d10500300e040074500c1034039040106543c21002040c451044100000040401a82d41e05650a86811040d40354656440e8540b50303065500c481c01c2030f80032034000b00c001100b619105032024400c0e00d80e5070140a90f600c03031194000b10140c010f04106c055001e207100340300210100d402154020f00050b614542900c41c00e0040c06440020340100c01000e414800400810440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58455740 1250 58454490 58454519
    0x2d1203041209050303070b04080f0f070b061504090b0d12030b0906010e01120213090212040510050c0d050405010b030102030a060512030f031303020c0402030a0b040e06010509160516030206090d020304 88
    0x401c0104192155903900d000c0127248550503825001050102d403c544446500b0083e010340c40c8100c60361642c40d00c3d61000c001d0031524280322050619010402402280110b030001d1500200c0500034149828030f030303034403c6041d60002e100000000e5465034240b40d10310304202045d0b04140c082c00d010108480c00f0000030610b02c000404200c19503000200c164001c803540500300000c2980103002c6442d0000200b00c5000c080c01540c0546491103905010000b40b103d0344a618000c808070491a403a1801c0c290b4014081e00300100103440079541d5082d85400d9807001c2c0002d51003000c030710200041d990f0600c0c0070480c1c1d00d00c030007951281ca40c0c02402011011140a030441f0707002401c00041100001d0a4a4102c1c40e03c42d41000b510b42150010041c030041d808141c01105980008540510560145540c1c81e0b46e2402c0034445e2551254065012070101d0703c0071100001030f149180b400c103251000320b0409403040b0108070300c01c5006910100c00c200d0003000c18000744481040c1031000d5441d091506c80051303004031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58456990 1250 58455740 58455743
    0x140c120a0b0618011704050d0908060c04051201150902130603020304020d0f0203030f0d06050a060203090108010e06060702091003050f031306052a0a06060503030c2d120304120905030307 82
    0x1400380c585024241c1c0100260178a070010b44114044a10741440c00507111407018200401003444140007080c1194082403c1e40f03e055080181820280b504041041048090312450307195580c0702503101251400708240c40c05000d107084c01607958070340440c8221105940394084020140f062003030000603500c950301d40300c1141e000070303004074000c5c49800040c0c15440307000384c7d002c00075000003403030600541d49800c40b4080784e804403000c982c242c2e030f6804181c0c2c0320720460148030300044c2d4030b10041c00103818040c0c5280d00320601500b541c2c1480e03920743c003050300e1140641c0d00c0c10300c40d5500380040041000c2049841c2444c2800006142040751071880414199124055001403000129848201c0191098409058514088080c0141901007045074440241c040240d850307906180c00800d41e400c2c0001110542c5400d44010002059440654150381d0701d48234903510715858100d800964060f0801c000c40100d2300064103941d90b424075142c6030342c60b4a60860404240035225804006655010094a1005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58458240 1250 58456990 58457017
    0x903020f0607080415030905070e010602060711010e0d0c1b08030f0306060708370e01030e030c1c11060c040504050703061502030a11010b09060d0501140c120a0b06 72
    0x2e407403d00d82615a0f01480c4c2000c401c01a5092a031100c1d2681608951001c80c05001981c0480f03480342c11208141500f401017001503884040410345042c0304000c402d48604001000042c02c0d03140180d200e04010101d41d0090001d003401c4540d101748400c1c1d45049213600205046481c0c000d180c0040340703449001b680469016100040006a10354407184101c0d50400e030300100440e41d50f44140084181076003200e00c00c0e0070b1281e000d0722010140b8102200d0210480060f1280f01d18010071900440141c03d030110015071074003050040c800440720400194074100031178401c101d8000311205009154450400e820b0007039900c01170911a90391002011101a25419200810030303940300e00c0d054014083c6940b081e140d11025140d04e58a490740400548008041646e486440791608210315081c0c5600d0590180e00428134400329180e890000c50302d0002c1071294002180242466500c40030b0050111010090860005140d1410030111828650f00a42d0000d003042650421004210036004000c03135039051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58459490 1250 58458240 58458247
    0x204081c0c0f140105090d05040909021302041401180f0612090b0403050a110c0f100c05030f09040605060304030206010612020705060108010f0630150e1c0903020f06 73
    0x4501c58401d18110a400001e036a02040c00e515052120080210916a295181070b011820111000c00c548442401c5551a2410541040300300700007003c150800b00d91080c025052419440035a001500080080d07050000310700503e040090500348040200701c00610b035102c010701041c0c0c0701d280d1401c1174811a28150040700d0703035043c0d450001c0940040c080d0200c002001040100340d405001060040115941d000481d95050849a540c82040400d40c0d4020140c854950207801c240c11001d024500034a00760f01c6041950700c0c0c0e9801c650140031204480d00000a40822504241c01200b0060200791409440d40c81c060310020344030030303041c0200c200f0050382c8a04500107171421b0b015528041e030004140d075038650b50740c894540200088014500038a0070903c000580c0d0524500c420000b04564040c600c440c0000d0a4210342003611010403900c80c4030b002030f8405c2c2c441842c402c030514008450010898110a0440982c518407081b5460003003040400d02400188c841180015007884141d81a584 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 58460740 1250 58459490 58459543
    0x9120b010915230102011d0613020312130501020c0d080a030b030709020a03091707020303070f08040e090604020a230105070f0503160606150e0609010201330801020408 74
    0x71451416444920b031840000c0b01890f001c3c03840c203440b481c105026002040390305010903038030411040c008445401317908603800045100f510300b814a112144000c080c8c5071030500b00b000d8012a070700514000b40340b800700280140065601005442920102110400040f89550759150520301c03505024404068850404558640782040300b0009841401e20554a8000c0040010010880f031441030302e06c52040040b40102420401c221041590041d0146d0300c4d00c4160b4880c001c2c03070f0500500491341e8420402c00010320603040c3c10000c0c0180702c002c001e0a194102401084110101038000e1409842040c29840d840c07525200c0303c40441c0002e081c265204c101d1810403102352000d110016020740000154180c401458070b00c05150680311307400c01c02000d03480c0c83d0201c3c20050100a040041021003c40898a107044800382c400030505100220381d64852b829002058a103084108101c00c4030094525000300440203503002400355070780210708103480c0c40c0d60300d070380d42070950200490710001c100d403c003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 58461990 1250 58460740 58460771
    0x206040e0f0906131103120a110601050d080403021909020a0309030f020c010f110a08030f0702070e09030a0503041118060f030c09061009150203070b070804030c0212070e09030301030309120b0109 86
    0x1e04011203070381f42c507171181202c0002400d401c240b25001e0095000d45400420360303140001d00350851a400a812a0600d0300715401d001c4403071820b2950b44005c2041a800103211802400101174429043d50042844c207894030f4007412450610128506541191111566a0340d005050541400480c541100c0b0304d0b810850441c18a69840d03005440307a00000108100e054400d003805003e28840e60858804136a070b240c609200e000b0a80b05401c0e25042040800c0300d461140014541040c011381c0039140682c20071000903085440300388200390301492441040050300c0d01403c0450f2194003076026029022842001841c3d041000f00f030380303105142c00d8040301038040c0f05405a202610308803210310390110032600043d551f6044100110b0340c0050311000038190510842c1103030301842e0306440f0000c150f422a800c0203186000b2011181d101d100309080042c5804032000f00501030340b030180c061660383d41107050041c68040a60882c038203142c10840c90100040e038880c22181100e480300000580b0003c05503003c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 58463240 1250 58461990 58462003
    0x16050a050c1507020d142a160e090c0607060f09170306090c04120311010e120c191703150604080313060f1407060204030206040e0f0906131103 63
    0x1204603108803000190760b03a91440300580034011a4003280c000c4004218111011000000725a4041100f4868104038203c9011420f4070010700e103d03000030317841e8881c014928007903e05804020001070510704000245641404a03042000791014119406494011907141d200300c560060100e80d903410700408412090744080030345c540c404d01d11111002c13005044661600107454040c41250400003054951043e103084900b140e0b011066041a440340752020390720303604407200e804c801d95240c94003242d407070301c081c0031549022200c08109a100d4041d21115031602100c5030444960f0154101c800011480900c94104000f616020325a0740741c2e1401c4540011040004896401c076002041c0420700e0740012020341907200b0030850008409950310301c111082aa0b0003102c0d008504449015042484020300a0075410702405015150546c0c0354081461a4816840405030000c080103010070081c802078000d81080700e420003041c6901780381b40380794202003807250000c105040540d180d602a88051040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 58464490 1250 58463240 58463257
    0xc030b030c091504090c08060709150f0903080307020106081e0303011208040506120603060601020109080406030f060e0406060302011106010612020315040504060e010608030c280507030503071a16050a05 89
    0x140000c3c001850f064040407814000d004181c0501000589d55074481c68080b000c4403100800005d040a0043e02580e82c1884c6550507420050b40e642d0100220f40a0b200550081c01039500000c0e000e0314002029003040c0b1040c1170400300301412000d100244c0000819a81510300610380f56040d200c16250100d118425544490380181000c54159440c820032007000d48604800e074103880b51a40e030000124200d5101e28402010303550140014030803d403003a40856854020707403000180f10740c0c9804003505604c408507000c98000d6154030040c0119607011090540c403040c40340050096505103c0090071801070640c1c0481115404800902c0b805419003500314401d4010304100094101410020081d04448400d056030350308000c00060340c124000202d0f00310010003000790540c46401205560400d41085a0415800c085070581c00030130000d0251100440c411001580e45014a03c0c080c64184da40d0091149a4103541c0104400001c0000c0c201801d1203051900c40d955401700d4200740c9490095400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 58465740 1250 58464490 58464499
    0x40204080d0e12010e0c1503040c140102010e1203071106190b0103110706060f05030c031c02010b21010507030603020105070204090201032003060a080309010516052e0c030b030c0915 80
    0x2804138040e01c0800c0c280d0300000706407030401000c2d1f8145d2160301c6074031041d1402041e20001d08010030010a4483c410000034905200203d0f01040001c070191520701d6180c8003400101c4000103106081360030007000c07805041d0340c0c070141c5103a1500c03078160320700150841060350310141c4400d07200103240e10075404122210401d07c019038540da1341c0e08100b40142054015503200d01d03205980483d5518000420303410f1400300400801b11006910301442c21100c020f1400c600355901e807584914280c2e641c2264181050200c62030300c401e0348500341300f41e0959501030b11840500d40b600b0070030700140c0d0380305046604c007680558000c62210b01c0c1e880100e0050881450407080c000d2408a079242001409e0001c5005010440309000f030140c41c1e0419075128442d6203040c0d408140c1c10410410108003038034501e80d8140c00b82c000d85490214441088499904440001d1900b42c455021482040010b10462200115a281c01c1010303a0440010903511001e06401350320030010300d000180308400c0103030710a207221000341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 58466990 1250 58465740 58465751
    0x910050903070510022502040e07030b041101030c0801030b270d08060402030f040b040f02090a0608010c0c02030d030e16030c05130e0304030b1305070608090c040204080d0e1201 78
    0x18429460780c000b02012034a500422620710181d101c030b80259200700307000a0b22070b043c039200a00c0500030f0389200c407402c0b608280c440c0f0641c00480d0007400755400940c000c40c441442482c203071824940341c0c501160844d0500d840c011040e2013459000807000c2c103580c0c0c0224030003402d40b91581615200903d4109154451070b151140d0910904042001490103070349803155a0641c940104200603400100d48941c1418130703810019010520059001744c02600903070140405512540103d01e0081c0200c0341264016100c0b03100b000040024403030310362914440e00d02518181400e0b800651910703d9a081c40042644a00c0719940e0b90f6428083c0e550502881c2c1d0494034490ba0f6840c010948031400d100f090320a49070080491101c501c0d0340a480c0c60242c83d800a0352a01c0d0840d900d00311040c0018040074504508600d0b108001542009003401a02d0242c44180711441c1001101e46440004001701d030103240103200800400c440014401403c041c03608003019112a0080421014441020329800c0340d030030f08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 58468240 1250 58466990 58467001
    0xc03080c0f12040f140f010f090b0703051309020903060402041d06090a0c21080307050918100506091c11090f0f10050112090201030e0a03030506120601030b0708091005 74
    0x15000f84200c0c0e0030b012102d00007640d03540764400c0040d1540c804039000b10b0099120300581d841840d81a60a00e854200113160940300d048144a070f80003100c08601213000001d140b0105803442c0b5003c8010411072030f05619041d42100800c0d111000908000e0080b074030303010310071481c581400c600b018012828044031981d2070100c0c8002c0d5903420410041d18041016140402c083c90010030348d00c014070450843c0130384141c2c1540e07051560791000b04100b0400200340b02c0006555130329852200e00d00703000d4180e5001803c2c1800d81c0e6850000e01d40c42140710b071004101e841d0464888860b9080244140b03000c0c0d0b038096840d400d144403000b810b0003025070301ca9030100c10401d0401040002500544404100100c10340d1203a410380d40c03040044c05007902189141140e00c68003000c41c0c00405402e031040c50089041e0700305100300d5140c00494001180800d0f06d0710100020350400009600d0240c051100070800c55145881c3c2c0341c42c14402030078802c204041200002c005003000c101c0410303d40c0ac1c00300108201d1504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 58469490 1250 58468240 58468273
    0x608030a0302030f01050108010506040303111903030e010c02010203060a03080c070510050c010c08061305060109030516050f0405040218130c0303081504330b070602030708090a0c03080c0f 83
    0x1118204d0303010f040b45001080c40c0d44607005240c161440a00646d1419065450030b840f06c81200c5c42c50b1949105941180351001c40d00307000b01d502140b082c0c070041240008482c805080d40c0030700565038210f80c810f20400500c0d9445183c0681200c0d040100c4981e92813070204500c0c140f8445070450b503000003401c840303681d0703d03a48007009250f0350740720740c000704001d0103a0709040343e1840c41905c107550311500c9a440c6914104003544500d8014070141028641c0c0c942e20b0340c0d83c0e0f081142c030281d0460b503c4440303481000903051111041825100468080081d450643e00190b240c6001d084424540003101c3c000038003642c01c0512106500d900843c1e0b0103091030341c0c1d240040401a088820b8010044201886c4015081c0380c040e41422043c0442480584d01c0000700b4506602031000401c1c1600030302102c0040c140c115100100003680c020500540e0700d1a11002c050000240a041c08c041030303000190210100b090320000005482c0d0141c0c88503681c010705080103140000280c0c2520190040a62048000e001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 58470740 1250 58469490 58469497
    0x501030f0e061e010815040818090103080c070509100303110703211205090d030c09050406030614060d0308040209060a0506031005090601020a0218070216090e100504020607060f0608030a0302 84
    0x14240d83c500c1d680c83d003450546500150810080c02520600800e00041000c006031002100c41b40c003c0c02200321450004800340d20030783c01a54022000a550070544500380f1220000d0030060b1001d803440d04040680c081c0c1405188405020401e5510980310100c206110090055800110040007170038901d20310b580115005220902041142540481c000814040c0e1403082401d42e001d0409402401d50a501070705041040e03800b04100e0140102e42c0d50340c0d500c0380901a6005000c002420034640741e6409005101030b203c0e501c1010f04440c1800040ea1060400307501542c15a10405503031200400304a001106070003140d030064011040007104205009000121002101c007450540c4401006903103130f029040011350001b0f08414440c0d9000510064030780c11000754412610f5a44450501404290300b6070081d42800c0d03101c0000689500381000486800d0410000420444c03d09600117031140c4900c69000305182d850f00507142d200c0c0c20300d61100000304901030980382e03a10f0425500500952 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 58471990 1250 58470740 58470781
    0x2090303030c0901034b0c09030512120a0e0a021f0306060e0312090f0a06021b030706080f04020109080607092c010302060c0f1608100b0a0501030f0e06 67
    0x2d18000c0c0342c0406d10b10040110303103824545480807898000c034081070500c842203840025100280e440284070909020700c507601c2581c0d03056881d554010b04600e4540d00303200500d400007246034028040901991428043c0c40d81040d0309407000203d040510321a03038102140c1c00790281d485080c5841c64102192400b8181524280d50340d0b08001c0b442d25214280e80d440401c0c3d001c2505503101011525a07101110000c1554074001005c03803c0900c54400051500075540d002800140c002509945a903c154011280c1c21902180a000d5260900d540180300b010010290490701c0181000719055901855000014040c0d410503985d01d4602128042c0181c01f42c0e12031041000801d05002c01c00711199a42e0171411060103010422591841d020040b55410820410304980100300351b40c0360302e45040240891030320050301e641d801d1918100456007050307820f5840414403410302e5100402030351a281c040e41030354400d0030001000c000009482000700346041407000c841c1300d41030501c50103111501da40030589 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 58473240 1250 58471990 58471997
    0x60f030605150118050f03070902031008060c030906040f140105040c0612020c070b1c0c210507080f130605010f03210503010605031b0a0c0203010b04061202040e0102090303030c0901 80
    0x2e60b4102c00444240ca00180704841081034080140030b0f500e02813103052100a4010200d416154807103103030310226030090b1403055105010500130080a8024044182d200340703220f030964103501d031820340680c4854004100503c101e1f401b2100d40100721440415a1074074500c8002001149400e00d480c0300d4001c100d01516001c00d42092107010b5207030041c002c8600f8100c604002d001c00c146010400004c58000005c5a00030150340302007922240e40500c951150f0b00803a070f5070014103900c040c00c006016551444940c20450500c010488803d80040c4415081a1102e44540280c4d5030403040400c080c0410304010031b000c0c01c22000142d031506d410300190a690080750614141c0b101100038501c120990a4180003060341440104802070082d009103a11030480748841c0e900402c00c48400509602c902c51540208130040d01d08410b5090912400704814415901040b945042030f00002000300c01900007032080c2d84440641240c86000e4040d200701307020180459440c0e0400d411100d0041e000948a140003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 58474490 1250 58473240 58473271
    0x50d0c060506222d0903032a0c03050f0a0206090709020a08160207120317060306010b09040b03250602010e01060e0703150b0a030f060503030f1c060f030605 69
    0xa41c60011050078860b01d8500c5055254807003002c02c3e43c00b821080f11104950b40c0b10540441840e00c184e5015040b00340c607030380006039200107031401404850064240002d107442403810240e08412100052401d007105081010481509240460b0203105400c0c219121590109000c00352039000508603002d24a94010303560303950380700d4506e4012409020001e000050910000c66034200841024524417801481036602030354440788210000c079007001d001c50000d00151004124070545089154101504802905180d49402c0200c08240030741000b680c2306580e1000700010b943e6080002410074035a66079462003500c401d040d024003202c0c07644680405542000014842281d040c810217040c1c8241c01000d2400c0e4071440011001821403a080c41c5072540e05600204144050710060300c2c80401c00e41d004540300c03211281d05070a860496001500980c0140800c404500700d2030161002c03548010400c0310141d041440d2440a0b1140d43d0101c8c0042d62800400f000740899a0010303481401c155800c3c805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 58475740 1250 58474490 58474501
    0x1b061505031504050a020d0c080102030103080910090608061e180403080907030c03030807030f0f0501060e0405010f0e0408120903071208060306190b0604080706090503030a0e091003050d0c0605 85
    0x407203000f12001041500010072090041c03808107001580c848c055804174244a895160980c221380c42030304203070b861240115580c07616181c280c50800300c41d0743c0d07448e00c4c2850500d0300d4405031047e08040d10440c840e0003005140c0b000010300c09281c440403200200040400d00c0d0003211130740300c03c1e41580c060340000c280e100002c6811500244100480390b000c041c24800503d103407000c40d4256006443c82c0c0806866256241340140d03980100c06042c02115070000b80c0303515004020b84040c24000c42c1c2070155040100420a0301590080901110810008424a83e54900c0d20b81c0d4940f0a100305450042e2586061142014000005e002040e00c940c00350300480e008400c0c103680100b411140c0b1645a0b111100280c4502c05a418800c2c05000b0b400340442c80c1e641650000d043c40d0040e0700441c0141d1b00514003080300710ba00042c07200040c481a0091450204850303c010300b481500c03003056000389458008162040300c010400790085400a00ba5090b1401e0b01c040183b1346440003005481c03880c148001b01700d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 58476990 1250 58475740 58475773
    0xd0b01030c170417120f010f0602070602070e130804030602040f2301030903180b0309011103070519020a060504060f0e01020c0a0f02190314071401050a1b06150503 72
    0x900b16900d03542486099a2141e680c2e484800110702c82c20b00c10074040c400480c200000009142c05501c1050b204807156040c08212000b9400b42e900410842d8415482042800c2d008183d1a05071505200ca81c1d00981c0c0d40354031140c030104491001071140c1e00000c0c000041c0301f641e60103081a02c0c0c0e00501c090409545c0d08035030b0b070650003d18502603003403544d004010b010342c0a540070102e020300c2810607100502c500150070100400b650300140280000004120b0b0240083c41203228071514500050300710b00f49003100401b135019010481e800e2501c1001c8a00c0041d00030440c2803a80342d40134006001600e09807a0040c0038041101100b14035908081d01030551807410f00a0b40c0715a9040d50040c800e007070303081e119040d42004404003645c11400d05420509041148030b510340185024810f00e0719446203000c016840d0400f40c1e0710881c0c018441402c1d0500c641e078000222008230500c2c3c0390511190a070050000814442500020202d40c504070608000d442e2142c500d104440e001c034152000b0104615a06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 58478240 1250 58476990 58477007
    0x16080903070206280c0b0a050a060302041a030f010513020607030203190c021002060108102c010e060f0f06010309080d0c0906110610030b04080705121b0c0a030305031b0d0b01030c 79
    0x24150706c0440001104080c0031b5000350b900c909100b10210b1083c0e43c0741c002c41c045490080c401c40100802c1e804800042c2010400310314a42907101c0200118a40342007130420404003400000c1c8900c00002d254000e252080051302d40d4a00880f4511062180640c40601009914281203000d0582c0d1200090914000b186450407070ba07442014000401842c20741c00300400000e00f4a2180c8400c08202111045000101200150307150307000044031414130220364900314008010a9110740514100205100341020440d040700d82070030046045003030361900080900440c0601c00328107140400c604040d952007018403080380c120b41c03111047d0440d0300c449191a0801122002c2c07e100c05e0840c1000000c1c0d050701e003258043d0245551b1030614641c1e60300c040c00c00b200400041070b032000205490307500c40d02501c60072841e009000c0c02050001c088001180a40d4810700c406802d000d00400024080c111850310f202850040c4441956a100b031408000000d0a40c0420540000c0c50004808145400398460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 58479490 1250 58478240 58478243
    0x609050d1203050702030706111323010302030c090d0b10150518030f0d050705060106050a02101d1f060b09061902070f030807020102060c0316080903070206280c 71
    0x30350080300703200c4030980c0507010280008086110030402d4201242d044d00c10a4000c41e60001c2050380c0302d80f081b42d00c000e50900e82e048121710142e00110301241ca4211030030060002028200541c4030760314140d440d03003a40514441c2c140c10015a80e21103080040c1d242d0300c184100700c1c460f2450041901e1710042c2c2c11000d0720a03494804181d0410880c00d11400a070306648101c4002011142044403001c000c604004c440954400440c1780444c5820800105202c0103016000d5803500034200124a80025515a402101c41c11501d40c0e4281c4005591502107410034541c541204a945841000c2081d1140c019000c2d05403019610f8058085004503600088600882d4020002030420210843c1c1c2103680c6843c2d05018103610411200190102c4011111401980a00341007a141c1d803190001a040000080290003410000c1040060503482203128014280d014035000100d95115004185544580740000c0d5001e0804140784100c009203000072a80c0e01c18540250040421a41081d01c118211000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 58480740 1250 58479490 58479503
    0x6030705090402030109060204170d021504060b030f0712030e030c0306070f0908010c120b0d0c18061205030301061b051b040f060902030702010612082b05100609050d 73
    0x4200140d16240e192103401c01c2c002070000a018402d565808126403042c2d20010040548141101d2b00c414240115001d484050000d0000009105003a05003140001c00081110341e480c003c843d02901c0c20815196180c9031013044403485600c0d28668840300074840012000551400c100300040d0030702194005407a800640101016110b040382500c906070311103104401c01003900400500040300b4010302c548100c06031a0340f01c0c0b01a4034500700064420741c404190003004d15401201c000307031184041d241103906550001078040003180211010f45440e60052038910301540c010b8041c002d000c00150304035501c0c2e440348001c0c811184d01a00c0100603d0740007501c2600000c14500940d40700c1001801e0310b5200510000d036004851030004111780e80741c0c0145850550200401592940901c01c0340003404110402120100190b80c50345402c0c441c210810411158121231800c941029071401080481032142c2800140b80c8200101d12921152068000003242400c0014042c20500c4842110540146 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 58481990 1250 58480740 58480753
    0x8030c0d05030903070506010e040204050a020a090b0a020a0515010503010509060705070f0c0e040f030305070905030a080f0f070602090414060105070627030305010e06010f0207090902130c21050603 87
    0x11098070142c10007061002030f80010020394000500c24070038180a0486507155256505150043c40100d070001002c0c2d0040300d104000301a80907070801048030480c0d888100e8a90350b0080c8641c12800c111002100031300318032402c40c06a4a0004009c84141079403c19030080200f660756050b01680c2d00c02c1942c2c000c0c041482000640081182c03c030f1444e04c4035015221035203016548004100916404950594071007601030400820180d02d4000d56030042114603001c40302908140c0003e07143e00402e40e00034221800000d90f0304898101d0b00644402c040c64640451f01c030300943c01d001e0040d5002080c4035114a2034010b01c4421156035011860103550180e6030a800d01c071a0380d40e80e00040039014074a0000300e900e10001d544403103940c150401236034420341c2c0100c0c807940341800c1441188805045a41404449442c00081e5980050868102c492486c004550b1402d9030012802c2444505104034011b818400d14200c00764126a40c1c40c0c0740c81c040d564200740d85001403c0c980444000740c40c816410707000003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 58483240 1250 58481990 58482013
    0xe0601210809090403020a02010207050f010905041a0904050a060506010807200109060f060f0e0f19020c070b040305160506030601030c030b040507020c0102070603140a02180a091508030c 82
    0x1003040004180319015140c90041d0590015103008000c0760114016408000c41a045590501c42000100010394800410b6022240040d05426541c01681d0007142d894600078801c10700c0811a2140d120042e00c0a14513007080d090054840c500c80300f040d9101c50900d00483c00d2940f00304c000c188220800d60310181c0002c494036a625041d10361500380000ca648a0b89108003003511885082074002c46040c00180c0c85280a00c1c00013443c143d0f9018080e5050840200101c01445201c0300781e0000310080c10b8011a1103074030301c510007402031101d10340d4244122540802c1318500c180083c8103490288040781d2a1a02d011911040c024007406142d42002c1c003480425010b50081d00305005090f05405c0c00b00c3c07084400300208044400817240c0100503231290b01a4101540c0511251014103004d10342882050031100b00c00018540c040c040c60354166000400040e10250b464040c84088002024040c80a0750340201d80080c001d44c40c0549901990710900080d0044000b0484040da4207050140c81007100c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 58484490 1250 58483240 58483289
    0x80103020f0303070204050f15010908060a0b0d0b010915140d02060d020d090507260601140105040312022805060402060a110a060507030f0903080f10080706120e0601 73
    0x1c03121054052005118003c016a030398020640706149501800c1c0c030f10f25009031154040c40e4000251414491001804c1c003035035401199840e84500c2c009004200c004448000c0b4041e180c21800148c1402d54100001c140d50f01c0c00d4000e2108075142d07540000320386803925910361541c5040150550700c10030302c03403c070001410420301800103081030308001814190441c91700001e45c1d540040c202d60076003045d5070612107106103000c104032f5291603103103c0f6001c02800b800b00790b5814060040d01e26048041c400c66a142c0e00c150200c5014680c49102541c0e500209040a590713921801d5500c8402c3c0062100d0720301200640300031500091304103000748103d80319074080c030410b80d00c01079020040050748a03a801d041401000551003035442450300040c1480c0252005049410b1011382d1728007581888031040210398410b0015800c10032060201070385460313241070703900c0c420a582e2000406004850700094480c0d000344c1d500c603074031402641c18088074040b0880c20351904000d0261a5014201e003132000c131080b81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 58485740 1250 58484490 58484509
    0x20c0705040b18070e0a030501090b0c0310120c1203020f0f0c0123040305070b0307090b03130212010b03100b0306010e040302070612020c01021207031b080a0b04060306141006090608010302 83
    0x1079080171080d0b250020041038071140160402e48440c0c0d120101c0398200030002d07081940c0500c0c00f41c1003900b1810122740c5984584201e00c224011303403410b07041010078818410302d41c0c001048189480c40d040040c031310303002c0d440d04980900d61007a80102d504221031500003041040d01d0b580143d40e083c4001441a015204241d02001a80c000725014040070001400c200500e401811410450381d8403454002e0004000d64500c0d08003040d140c0c8244144446070b207011444155103a8102c40c0302c90f01c0d8100c5001c5500510075410220b6041c420118030020342111640821040081038007a60401c2c2e8a600c8011b680c00c901341d900500582c40140108681032151980d0400b4407081f0038050b16022012600c182660001000501c0020b003030414030a0b4980c05116070107500b49841049007910030550b01c09056890002c0c0451003e5440d458141b80c0c41d41c45500080103594030071400c0082c0b10056058080141d8112401c5174110060403010400a004042c1401240c0c080d507a0418580c0c25542404031000c5d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 58486990 1250 58485740 58485751
    0x303031d0601030308071101110f1b0109050c040b2206090b01030e030301091d0d02060106090815060f0402070206040803210412050a05071509060b1207030b220501020c0705040b18 79
    0x56940e140c02071008078400080c0404d4100910946e1100b40d12400e004034a2f1071440030710300c03c0e0300d00340807800010f10118144040000c00c03540080c1c180c000300c0100e42580c421a41103a41c9005107071040040d1002c50303001500b80d5580c42010492164120010750465404100c43e0f20150710034001000100c0d055002040300c048004800b00f20b40d01c0041d0031620306140c6040500250300980014040d080d4413003000402015040010800720309580c0421072a000c0180a185c02101d41c030b005101c41c4e44a580446400503400340110b0345d29035881003150707182d400c200c008204200700152003007031a2036000c5070a030107140c000038401000d0081c010140c5007517002c10003000500105015010225190104800e00c0480c40e1002165118880c60f0040442d514805010b106111100c61604003490000b6a0015a9441aa8410291281c24091000702c0d11101c00414802e00c43f03011804100064001d04910600841102c806984520400040d182e0700c14409400442c100c0c9119403801140500c190400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 58488240 1250 58486990 58486993
    0x7030b15060405030f0703060516201606050c01050708060a0b07060f06080f10060602030a05030c0708040305150a060612051003020907052d070f030e06040303031d06010303080711 79
    0x83e81e00d03c003290824040782c1548403245c20000040091003094000d9545c000d03840d0804160900032654068142c40d50100b4460030300c2c44440c400c034030054040040301c208028120103020403558904004025a0005084d44019401c10011481607401141201c0c0188802003840d907465081203208015600080c50544119468042d21855a6001c0c45140d0142c80c01c07801511515242606441c80c10a070740c1c3c4107200d031915180c0e08200c09a4040140c9851802d03a1911076640d0f02d800356001032034024800098507103600010008200200002c030980a0402c01c040c49815644444010044030900d00c80d03880410161001003074003000b95070000e98410b0742040603040651310381d00844e940e00c400f242c90034041900010440d100c10800d1118030181d403082551180d028800810700440f07405440402004000c044000e0010540200240c00c44004007070401600d1f0b50340c900300200509a8030701004210203041c00d058400701c00102d1030605030781c0c00d0b03110b03a06562100107080b10860079017070508005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 58489490 1250 58488240 58488247
    0x19030b04050106120605070e2b08042607080708030d05070318060c200712030903061103010504060801020702150d0209040e01020901020f0a11010f1e0c03030b0307030b1506 76
    0x80c40e1043d41110344d250040100140a20300044090a9401940f1105104101004900a0300111418a05519681c0c044d60304104007651078003100c14007940d00510380c02e462880300400300c192804d040174840c0665108491155031394400c16601c07030165000d4054541c20802201c54401d01680100b0780140a41c41c0001d000c009002d0b88241c0000c0c8480112000c07601e030b860f0841d403294401c8291540441e50911000c91007035881d2440d0b80e4925602c140410000040000400c0c10300964155000f140c21484c10701c007030301455042c0fa129038005d00070702d80719518001011994810501c280d502e03171035016140184c1034046003168104c070b42020b002040a640c0800c03041d105902d0328096120300241840015071200056000a41481c0d14000d0003280d03540100c0c4018081410700c40b100c0c03591802800c000302d0b00c603c1da10f8100c07070800c00400c800f841e080904c01d0201609034401a5881410301a903406c100001d9200e00b015110400303444007504510110740814180029001c112206410052030580f9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 58490740 1250 58489490 58489499
    0x3030e010c02190e011a0712020c0612061c110906060405060408010510050d03021207030201090209090f01050a05090d0e0604051c060506030712061d06010807090b19030b04050106 79
    0x34928a80781084032001d0f4005000c015a41004020394050900c001d500d42d8070304180c1e000c20000340200b0902900c040054240385203d18002e0102104050000c0d005582e41c101d00a100303640c0300c07401c0d2203540c000c03e0074044c9800d801a4201159000e40e50120075030108440079410095001c1002d41a0b0b07602420402c1b0018483c0e403204003d00041c110a03001040a15004000c40c0c1448040e0317000728091344548400100182c0d000c1142c00e90b6184107005542c1380e503554101280142902000290071281c2e043c2170242910700001c41c3c90b000b101ca5802404155141d4120005588090702c1100360b0764090500c00c82014041c00f0349000080c0082c06140c10155a807001541044030a180030030740f90b89940c032120910410703009040c0e00ca007080d4000d101c41841c050b50000104001c0c0c002405140e0354480620314019080048a440c0703052008484440d610382e040d079503d4045500c0340c01d072140e1601c4042030300d0b070520255224101c0c40080c410344075245507842d19401d00000a204650300d540e88c010226 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 58491990 1250 58490740 58490749
    0x101d01021509070f1a120a06120309080105180613080d05010e010315200309030d0e0f010c0306050901031211010203130c0909020a1404020714010b04050609010303050403030e010c02 80
    0x9200340303110702c003c02040b86018100440140d941c0c00c005012a031501c59010903003410303000c50f03022445032500c001c032595444048000502d203a0f0040d80301021281d03282c0b0207140d8002401c02c16100c544000300802d03220140c103a000051030900d149100d070410300004890700f10b17031191540e105000716842490002400d9584044517401d030131401d103083c42c2e200140b091015820440e800e403801d010303080101d2075804100c6280c4072010880068020400400618100000d0054503820101d006060103050307008890661200900031030007080750303e808600c034030203803290203003104498000c3c02d1501a41d00355104e451034081501602024040020013503514100c0910046208a400c00164070002c1d5007450305012280c425404143c4042c02d04404a01507071b04c1e02c04150460f9440c02c0006c583c4103282000ca0040c0c048d07013002800d0a00c015551100d500019000091081d80c111400c00040d0748410070000144400c0c00003800040c414402800000e00400344040e030b02105042c14542c1803119400207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 58493240 1250 58491990 58492033
    0xa020a0b090703110909070909060b03030a02060103020f180a02030603010615021c03022a010b0a03060506030f0303190c090f060c15020901050706020702060d1107030e101d0102 78
    0x798a0781c412401001800303c6008204500c20080f11a00313183e0030b0146556607501e545008110b94290f544000c00d0422071b103a4421024000060140d0b40c540c0c4240001949492003403006038002e0b2242c1842ea0081c1c40d00a417103000e4142c8071207074410240c4076950b10700000d400041159030150740c3c500c00421001090302c1d011421490700c0d0f000700a105444a102d03034075040321140c40c2d0145401809a040251034014841c1000e071400c0400082611b02404003501528020340b840c0e820001000d404024004990080340c4640026000c55402520700304049a42c1d220840b0220210303211500c103440c031008950001c0001c81070510340700007c00c0c0c444090810256295100c50041030020028400304040342628030a98094030400714202070341000042c01b80d105680e0004d10b001d03030008441c4210f5440c201030b1805903198510800c070701800380d03108a00c5a8811002640407a000c052200043d2414140008051280d65140444e0088403011130407070807150181c1c00d0650041241c030011444c0501c9c0344 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 58494490 1250 58493240 58493251
    0x5070620030103050307050d030b091603060b03070906020708060105011b11090a0c1107060509060708040b0a020304031b0b0d0509010b0405040507140904082a0102160b0106080906010b0a020a0b 85
    0x5191b5601031443e12514240442060006050805d41c3c1da400660700c01c11460f03803046440280c5040151401c00c2100188400c1d0400b03c1403020100c20321060340d034420103050075580d03d81c0032129803075190b24100c0d940c1d0009104490010701c1e00304000b400d90400c150900ca5403817182210341701c0d4202c41c500158046c81e04031105030320310342d9070300090210692040416080f80c0e0090043d00303010f420074000a0540c400c140b003040c010078000880038201b0400350202c030004c010902c0c5050302e40e44101c0c00251258041e1200741d55003820030140d00188484207124104552035502e0a52508a150924001410300180000304a5503116220740f2143c542d80552842135201e500030f40043c9042000c035140b900070b40c411090284180c07034100000500c03080c00321505034400d00f1081e501d084400380d01000c10840360f400c030070317141d4008141607032080080e203044042a44111f20f40907541e030300c130fa2045030202003ca0306850150301000c01040072421740d100626010f5101d1054819070110390300d070701d044050107441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 58495740 1250 58494490 58494493
    0x31e02220b0706050112020a06110f01090c090615050301090f0b041d0f0703080904090203070503070305010504120804050c090c0f040f030c08010212010e07170403020105070f02010c0507062003010305 88
    0x800c60b003000360342d104450140c000c0c00b4110010300c40540100389603055601416050081b10803d103007100d94200034003200d4500031002445200e0719864a40e8410a107403107021086403c20b040420b5040d911000031006041c1a03580300c0c1183c6c41d01020001504c10605060001942c4400c154482c2d00c5d10302070585860354440040c00d200d45004c06080c6490a190442032198018102c1800022094022200e0301c500460707000c546c268041c00060704100031a03000030750510949100004001c41900600e20450040c00c050340ba4aa480703209640d14081114020083d0300318482214080c54003043c0c83e82c02250054125050111a58040c1100e920580000070690041c6404104001c40428000003900360380c0020340c00c1000e051514068000d060003060414210f01000a030349600c45c0650318000c00020200000c24205401c029000b00001c3d40c02c3c100081c0b03c0b4401c0c10080d4014000e101300687d595442503d4440d0075110000141604140356104021400342d080d13a15010001650203140141c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 58496990 1250 58495740 58495747
    0x1d070c140a11010e0a060e0a090606020f06150a090f060b0f130801021602060309030c06190b0a0f15050702030a141e0303070c0503090a090501050f01031e02220b 71
    0x140054048003000b041c0d410024003007091202900c5245100089849a05001d20449050300c0000e910341c440e500706c0100c031441d0400000c0c00650024101400502040c16500151160040a00c41c1664900702c2c6030002c45400f01080503442c1175100d10003040e528000010f283e031700e0f5150807031150300c034400d40c10080b00049600048100b00340210300c0140011402103182c60041035140200c5e0309030708006886454044005803680c00305008480e8800c00d04010358000b860041d0061a5181c440c0f03801e00c0e24a40b41002c004020b06000c07a00b0320a8a03c420020b441c400d1400a56500b05503d407580304003009024040301c00182c07070410581081e103104e00b00903100c81ea1981c150924003502c0c1c00c4211a040030f00040d0a1a0100100c03c5a410400c94a0905400102070404528601c108180e058100400a43c0001c040e00305600540c107860b01100d003c13844041500045060711040034031840c603840701c0000a1440105c0350b00500755030b0b281600355181c841c0070410300341000c0b00d0307940507944000001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 58498240 1250 58496990 58496993
    0x411061909080f071202120709060b03011503020711060a020c062805032415031501120209090a090f08030c030129030703090c15020a02040b0103061d070c140a 70
    0xb8840e801c00f4071400c0b0010100079141c418070742003d142c0c41c00003030b001d5101035a200701095018417580c005051020700a04c0410342d03a0302d102100d60300074481c41c3d59948105610000c01171103402107501054024040620410000c0200205070344162480300943c494083e103016241c5620001d0480c2140a12021040441000e0141207542410500f68100101042000b040c458038003400c0306071811000000d24213001c0b81e404036078034448a01007207208000220421804e0001005039600c180030a9880c0e54035600064100c030282d0103120381c0c180d07102d00600b00203505601caa0340300408a5028402c0000440c4680e1640746260340155060850f0803c000018004400c0f030360701c490201001205650303200c0126482d0302030320740005002d00040640391130554084c07101c1098218007608940303100320480d031000d034006592401c00f2070041340294100805081250700901c0751134201c1d541034000c484500c1d07140f00c40f144a41c10043c000b50500200c1c286d0080412281c20f04400c42d217030b6a000900d00d04005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 58499490 1250 58498240 58498243
    0x10f1b030903050406050c03130801020703030614010e0603130b090a0b0105030307030503011e031401060f0506070b070c03020f150103020f10020d0c0c03081204020a0902070b041106190908 83
    0x4051100616081c980c08000090740701c012541140e543d440c0c566115150a84000c0c10340c0318001484070020b40911020540032819030080a4840c0319403420048555101201d01d10380142d0003425001c00c0c0721000e521268180140159841902c031550700c0c5a160300c5542d014000b42c0d003603480d9002640448941d008110058080b00e0142208400560501c400c070341c2c0c0140a0311050140345032491540080304003095000c40a2030141d540b021400041c080209c1035035000706074910078203000c0c50842030001814107140d4200c1d94055000035040200e50754503a02602d1010702100210118481c102150908900071f0010401600035111101c650f54074500400450412401c0301c0c1e8410707020342d4001c40110b5000110300d2032200f11810460048523180c2489440419541d0024040d4400000d0040c901541c3e55034140c07085e4400c544404030140c40d8a0600b080f07000741d0100400301c2d003601011a000c541c2c6030909608841008081600c0c204600402d030640c5240c0c011114041a401501407194110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 58500740 1250 58499490 58499531
    0xf07050a080715050402030615030c030f030d150f03080703020a06060f09050c03090a03030c02070b07080301080609030c1009020406090f0605040b01020c09150103020705030a080405100b01210b03010f 88
    0xf1240340c28006402d00d80c000039114000980b8946140e1406071038203506444c180b007000c60b042c40c02020f940d24a20001010343c2c80e40c1c01200e212500ca03103000b150724070510001200c24141d480f400c00300d950141c2140d585104075441709a043d01507228014809000070114000e2001514031201038000c80e0f0700c0c02207203030141c030300c05081120050001e10030003035172510005010515540620300445c59011150083c2d06041c0305400600196000050000c10304c001440214102c8590004544896503080600ea0700ca0080c4410701c00c10760406909104180031680100340d41c03600041c00000c03850750301d841ca5000c0300c0d10340074183da02c6501c8000421072072600e44030313100300d04000b8000751100f20718150006044841c0100400c084844c04038a60b141d036480f0b40d044d42d013281d6000382181c0c0c1d9201214006010910111021260f40c4208142000395080a0203422000101a1150a442440f00110b006400104410200c415a41e03000190103990240680b09080320b40c000c00050178040202800503254 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 58501990 1250 58500740 58500773
    0x91908090306060612060f041d07051912030f0306051e100302031611010b04020a081602030a050406050318031603090b0a080c03070909050c0405041508030901050f07050a0807 77
    0x4100303000d0030350349085d45d00840e1340c40300c0c3c06c40780d120b9014411070005004000003090380f4088851000e020800403400103201d01910400c80b00001c490808028000362800140942c82924985171240d1000031f006501c1d0b04c085249500340804c0294885012074495004003030a480b0400c1c1d92850200c040c284118003180e4810030349802e40c0f440c40c0c09000c0710807440c501e094150403c00c14a41034a8000c400b0b40c010b00034044003c10655039178086020040000f28156065918000d0070340b1940c030024000021540301c0c042c05d40303403142018544503054a0359000184207040e41f11003031346079030200c40c03045c0010425251280e60b030a4503003506080c01040c40e04e0641000c449500100480c0c1603194100c02c0b0643c0c4144106040e9a8075914000c0c01c03078400c0c036558400d1880604000c00e1102c450382d0000608141d50094030204144940c0b00070443c1052142c4c8205013151704208050030195100303d0040c618080c12100741ca00e01920359451601d070155441c8241e0320708034007055a40421801401c1018180d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 58503240 1250 58501990 58501999
    0x1f0f0902011b030513091407110c0909190804090605010c050a0204051305060f01030b090a030903030503070908100507020f070b09040203060d021c0308060103091a09190809030606 79
    0x1a241a40041d0005005a058111441558202e14101480340c011504a8003000d100030f620941e0b60480700c00034101202c0c0d12601e40c0c000c80001007a00380324442600100044000820840c102001031210900000d0031415082c001d62504004522085051146092155910540c0e40b860694810200c41c030a0300a2410030204c10742030b6003c90f0000035100051034040710001140e40300c80c0e0212402c00c0368003200802c1405500204011006290302d400e040368020078024000d55107070081c064403502c0307800c00200401c908034005e1001ca8860009181d000d50755060a0b505141c0f503420b040c0c6091809400d00002c2a2200b0030052103d505110006103809004003c00c070090070000440807601404094034041c031b90200001c1c07040e0360b4201056100c1c1d6005001022900d190b040d1003020403505a6058003c00c3d403c602040c200c5d4424828a2002604298444046100801007603032201014102c00081c0c070404030420002d01c5080c2d4880c8003144150302595807111070790141428180010900340c8903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 58504490 1250 58503240 58503251
    0x5030d0c0213020c0f0706050a1205061305180307050106050a09110d02130506040b07060605060a090909060905160f0603020301050609010c060608071706160f110f1f0f 74
    0x16100c1c0c0440d980c00d0408004096100c24070f541d01246803001e40e602c044410301c51014005101900300b8002c0c260560643cad1580c0b807440c0907038040c50540300d0942c1e00b140c1225200b02405000c5106a00060304851007841d24004245401d070040e1464010000a032800c3c0d540d280e04001c1441c045100c07a0007410341840a014900b00301c1e03508004c0e4021258000348264002a02e500c403640800c008601500e00280201e4644d5110708140c1c106410102c02199070925103107011802d46040001d64891800940d6a5a031141c1440340078405004041c0381190000d0700e4a280c440020030070b002c8540d03814001c045840b052486e0006080040324540d0014091610400c01440151114012108004030a08054212104502c2c044009169aa101403214007030030340c010a20031041c09125004a114900300ca0550b21104008910404000da981c00072480042a142c02c050007905100303101101c1d0401e44000352417a5100c58108040171640940045c10603050b108071a0403072088180601001c40200907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 58505740 1250 58504490 58504493
    0x1807020a02010809032703010b04060807050103020a11060112120e090402060705160b030105040c0305060a06110f0d180e0403090302010513170a03080c070b01090f02040b120105030d0c 81
    0x440300d44010001e410840100700007880f60303a042085543d6880c2042044e00101062490704088101a00609110794204040382006107014080c060a4070418000752004a01d008015002580b040300301606006031152200c040c2c480a02c12103008105090038404150003c0c50501101502c40466005104541d4a4800e0310f032141e0011503030081d410f5907403a5035001c180c01c00500d00615005029000aa008000705441034000c01840c100c820a8409200300000c407101581540c40071605180c1100340c524042165900c1070040e13800d001e007084107a81c0140d1308240a1408c04206400081c0400d6400c4d0841c0315960220003482d0040481a13440040c50600d07a50040c241e000c0f13440b029040140106811404941d09440760005158185820310404400b007019503d60701d1107401036000c54402c600084c51409a03000722402e07039500c104000341aa0915041400510300d11104030300840e401e000129802c00f90400a15002d881c003403040345a98900704c2018540840440444100091900b4000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 58506990 1250 58505740 58505743
    0x190219020607080c0d0f1e090507080307030210091a04030302090f0d0807031d0a0f080706020c0d0602070302100203070818190605041e0b010807080115030f0c030c090605180702 78
    0x410701c1c0c1c429140861b04480920324000135011291070215501203e6041e00c00c240303910ba00c0000424810300030790340119541d5001603102d01076010040c0141e00420000352201350141d03c400c0c10301e4810884030001501120aa0075181000ca03011000300381e0005a044541ca422140424012011141d01e05d550b8159900c4442a000d0050000c051103034000303160086500080502c0d041c1c0802800040e81245e0b90041c2e844002900d11a802c80c0b4080c015000c0f52813440818400e5142d48041c12802011a03075071b44400c02075004207425021809841c0d82110802c105000540c020031807540c1d0310440782000c490805d1007600d00024111241d00820821001418203030300740c41140d4000e172000030680c3d624204441022003807142001c5000080024030b0400c00b4051515042e40c081000301c0d48126110031500c0c0c2250401501c0f00c0b015103030010104006140c408404908601c00c00c03000d0700182d0b895440d6041c0d4200390b04445803c5841c1c1209001d6400d003405c001441c03812001803c0304074203010342c019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 58508240 1250 58506990 58506997
    0x81303120203060d0501050a1d030307020d0c060f0c050702040b03010c081311060d02210402060910050c01050a0e010b010e0616050f0a05160626190219020607080c 72
    0x42440a4011002981d590307161328040d50810f4100000303124524080b41c0c8140104a0400f001d03a0140718104802c0e06660b001003584e103c0c8590750020410056911015590040300900803160700d41c5400840314098502e00442c1d0702d5446680700c0e030381ca8549510422080d1819401c44901a80c5800200d5031103660203050f10740c20003070b908903650f00c108150908403206c140074180a50800e80c00a212500302265900520949189402c00c40f06048411000901c02600343c0b0007950000c0c06000280ba24039000e281e0382c5081855040146c034200008201509540b400c550704040240e482c800f00903601802c1c09a00c11100e07092070804220b0329134000291043c003a880710800001e18814051080000c1005040d0340312510304100d610122945c60421f69803802c040e10020f61440d85540018401d020f204840d920b0402c8411039503001d056940d00e10f440c3d01e40180000000c0307d090031901c0c0d0714250340c40141188410349a22040000540c40c000c0d1400401030490010032000d034080240702d43d91041078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 58509490 1250 58508240 58508267
    0x21011060601050f040806040c06080f040c0b090d020d1103010606020f030403060b1c0b0105031603030203030604050901060b040f30060203040302100615031103102105010606050a081303 82
    0x503a04c803101c4c0a612200c0d8011038100075468881c0200307000031b1051580ca41c604656181d60340c1910f65450148001b0095010384e0000c0514103192001c0c440024180040c2012031400b805200c1090440d400140c0403102402007641c90034070602c0201d0319401c003070080a014202600043c90011040c50003140d40b8404d62101410550741d40248000e00c0c0c0e00c2441d20b100b13041e000c2181214001e000d0034440c001d5403080c82002c2c800d01c41c1c000310040e04a40415480100c0390160003a60460317035160207110190900801c0798009550710a00031813a00d40d50b0f00644060801408c0182d40c0710300785046008002e0040343c024403202c540344a07003c641110f03881482460f41c0d0115000d61207481d04d1409038030300070000d41907501803400c280010605118280402c08540101d540900030315980e002e1144003484284c40f04451040819024840da0307408031b14024003842106182c07402811261030300f60844403140c0118000820015081d40c10b0340d8000070441c2c0000e1140020851013855540180c50109416903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 58510740 1250 58509490 58509497
    0x60903070311040e030301060f17010f030605040f050607030c0908010504020a030201120b040c12050f010b0d020c0304150302030105031e07030b090c0409060204080712080a110f03040305010504021011060601 91
    0x240d0381c40b40e20703150026141c00841c00112901ea5841d48400f610080c2e908040c1d500240038160143c80281c40308802e80e040b5013007401450703081421611040081c00b8010400d07240c005550300700400107034007042400e12800181c0e90029404604100003454803003154040d8070b15038142428040035903151011181201d90900300540041d40c0444124003810500882c668064500551a80001d80110031184410b038440420010fa0303484140003107a1007000e00a0088501c1d0910a5007900c001c50f81c000c0101408070030841341401d0341c980404a0f400e9074040c449001940100040020781010018901c0000d001d2002c10f040c10103841c41c0d03a540b40d0103407101425810754400402c0420b6001c1c081c550034024041c2090292403c0c1c1d0030040d02075401403288070100d200d45070000880645000a644589501412482c60041c062004942a03400c118265540b80a0388a0032134400600700020401184030310008902460f0600411500d2410b183d176a00521218910310100c100000c20003076409003090a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58511990 1250 58510740 58510763
    0x501091d0106050c0708060103050c01200703020f06040305060117010e071d1008060f040c0504090203030f030a0b1e09010b070206031602030405040c170114130906090b04030309030e0609030703 85
    0x141319140c008150711002003030049400104c1070100200c2c410244c1002038a41916005002d0a61100064200901042a0090700c0284014030b095040302a0b440d00040c034007810907880ea111141414001c1c1c0c0140e04038a80081d0100d047c0c07a080c0a8070304c1d0780805074064102c035454500c40d5140000b0050000340c046140c1d00014000c1c1d50810103c6000e804203100700c8046107840707441c662110505035401c2d20008203805001540780b4081c01900e203090741c05009103003403602410074943c00303030406030a0030901c1e030b00d81d601c11807103807958108810400441841d41340928100d0082c0400c41030180c0080c040401d08019050141c2c40d00ca00706c81e08140e000c000d00c08114003640c02242035000d80d03004241c2c07090070306501b007600513445007160110f031a240d00840c0c01c03a60b0302c0c016540d641c820080d04580001207140900e0101c0040c3e030000800500612003c00c00d65007540d0b0343d20020000b02d408402291b41c2c0c594401c00e1691080120181103000c2d1002031600c03150b000007030380c0d0300c8861000610418408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 58513240 1250 58511990 58512007
    0x10140a0b0604030807030c0c0b040909030e041104171903120c050702010503060d0609080f0a081501080414030d0606050301060206060103060806060f061606050603161a0307051c060501091d010605 86
    0x40200c2c00924001d03124075110bd0711000030001610400ba4160700140c40c040a0b241360b480c2a12500318119512000545458604076920030803d1116001e4803450150402401e9005850082e8010180c400c4d690310401043e120081800c40e254441c1e04d81c1000b01c11f000302c10051b41c001003169004032040307610707110545035481c1400280010f43c400500e0000701141003280701c0e019a02a05090142e03071202007107a65100340821002a41010060000700079101241c0402e0030f0402c180700342100102680d103007081d500071840a503000341d8014000074200000400c0311680c1408001c0c1c1090091130103202d050310b081001590350202604203449401d4404901078143d1f80c08044038010114440f0803205c80200d42800401132208490050190044083c07901c03014012aa0000a03900114010130f1a103603003c003601c106801c018010300c00e01004100019540e5224841d03005c42c10a51400420070300c2c101b9000401030307400c0c0e80c03010111020005040e02190b2132105183e042d200a49800c507260b00c0907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 58514490 1250 58513240 58513253
    0x11150105150c0d18140607030e0315090a120e0d0308060a030209090a03020c090717072606030c0301020403020310050717071d0a060206040f020310140a0b0604030807030c 75
    0x41c0082c524152042415100e040b03038208101d1814040f043c440c50304502d40d82c80b120020300600c1380300180d21010402404000074010b588082e1140406801c40c0e0ba180d900066404000c0c0e015501102190f00c150174450030001d170f02005c0240243c20b032522403111f00c420000301d0944001900000d0620a11000250046d11803400031001990020a22036003810649400c54480c824001c3c1a0014041c00c2100d0900381401015640203886035a21840031000443e04200114000f50010b002c111250304c641d01010400751180c16582d98200020080e03040220805161080551000c2d001c0d0340180010009650003150001d0890700503500807a042c0c1d14550200c2c1c080d455030440c030520003000c1082c041c1032a403101f19906801c914201505005811004111410815214a0005a112800103000240046c90a140051002d0100c40111700c8800c0c050080e81c1003aa09045049000030070042190f00314061034140c6030043d00c03003a14082c290344464605114000028090018000705001040384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 58515740 1250 58514490 58514497
    0x403050d0603060b03060901090201170403120e01050601090512030d020306040209040608030304030306050d02090105040207030e0a140913030813110301060902040e0f0106081603090c0b0a1115010515 88
    0x1806882007020585034074245009005040e0131a00a208510000e60701d11814030540c02180d4050b120b0640080e038103e110720000d0340c0240120100503001c80c2110311480c0d07900465501030403038000407480d40f41038000104034100c070b94045481003041c012011072590001c000c0391003ca000c18405a600c2c0d44100c0454040e108540085810500d8020700080f0702e44044040c500480c40b1b035a040c080c640d560703010021080e0b1901000b070b43c0080d03210010001460264010884184203042c11840500030a0004d82040010f17404000e50b1310102e07846032030b00d00e815100954031078501d1109140d02041524018640c0c240203050030760140528000d802807003d031094041c03070002c0040082c002103480d04070400180d0014490704c2010b0107400049a0514030400055041c5c2ea050ba403180202c1ea03400c05800c500000c80507042003450340d128100004520000e130543d000d01404c0c0c20701d6558400d5160000d16210255407181d42e035400020b40c0d14291009550118111003088942c0030032130503005c141030707614030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 58516990 1250 58515740 58515757
    0x13020d0b0a051e1006110a0c0311031005090304090c0504030c150e030f0a02060d060302060d0506030f0a030c0b1801021201080c0a0b0706110903030a08090615010f08040305 76
    0x944420841c1d2036449810061142070080105200000341c00180d000c8a001560501001c142002080c00014411071340c100382c0300902c0080301e201003066200c0c0c108000040c0c0052300e91000300e090051040c03c0c204824a0140c0150404100c14a41048503644a0150b4018860780c1e0b91941c0c1d0400181780b08a0580300a10741102070814084c1ea00c2200d2480d00d1036210840e4041203074031201c602c00b443c000c03980214454262010307160141c0c90b6820050103622030007106002075621000480940c0798600a803030314120308440090385080c000700b01032034030204104246a60b880803010700c0c00a41c0c07020040690350f0303000b03070b00c107500d0f071100c2840314044288a40c583c0f544d9840031446d114001031709450302d4100d076401d40940d400030040e442800100000e50250407040e00f000c02007000041c4184d4400104641500382c618101155034000a0550340000348100002c3d4500050104200c400d000483e0052103000ca41c80a6207034040001e499086a10a0182440300c003000180c20f144c003c07030403502d040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 58518240 1250 58516990 58517003
    0x1002030708030a14061002060a0b0a0b0a0908010f0509070605030a020f0a020c09010602060108030a14040302030303070801170d14211303030501080304050f060f0d05040305030402031b0913020d 85
    0x340f402e0015180141204082812140740700d0001c42e5a80c20480500c000c2a502e66003e40103c1c0e82c0c040150014000e02200a900416081800110b00e1903210241401060350b6071920386040c40c0101840c01d54139000c80c1240124542010b010310a800022250101c40207800e1107910f0356200503815000740141158440416800180400110390105041c80c41e40c00445854141e66201e00301260354610074029a04070741c0c8208070051001e40561411400114404d100764901516580400d0968000f55120790101d22240014062092081c00c004403c0164000802801e001c84070700404920700c0482c0b9540300e000014413010002040f20400071407118640c24440310307050420304245544004c0c0c43c160002881c03d800442c411030044211002c64000a1002d01203021400801c6442d50004100c404100341c2008401002402c43c02004c0c803450082d01c520f5180c0c0351a00505091449030408210140c0c0d0f0300c0c03420502640c0e0341c00000e801c4012509650401d034918808288030b881c0d10035024104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 58519490 1250 58518240 58518247
    0x70b0d0905011d0318130f0b03060a1505100e0a0e070f0203040311060906040801060b0703030609090b0118090503040e04060b010c0503070308150d150b010203070c03021002030708 79
    0x5040594001500a0740304034001c209612200315002c100003105181e5840c150010450003151112000c09404c0c500c0d0002c10204420120a05030804c40c0c5d206420300202c541c40b0854964140f5090100d41c1d40911410000d000022021006403001d210b54000c6a10405d04019807007040c600c01e05450544c100040e090040340c9480d5500c00910510803100d82c00003840e80070070361b689584080705580451b42d0100c01c80341070710b0b0142d0030041c0a4104a4006410580600c800103684409000b0035000304440900559a5852802c2c02000d59000e90031903507101d4200002440061a10300703c05046501011046082022080b40c3c5006800086009082884082808622200c81c284040c0c0900d00c604401c202c1d01800b20010744a580070480090110340003400311002080c0540758251b48003003000d216046814000000036003800c445401034850840022104e6030302e40003403003079000440c4240000c60401d41c01c0c0d0f690060700301403800000e000c0c0d4107007820031503d20300810545806640c0407011584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 58520740 1250 58519490 58519507
    0x6031d160e06061809040f15061409040b07120605040627060b071b090e1e06190b0303120f09011109010e060a0c080307020d02100612030809070b 64
    0x150116a001e14424140010041045441c2c640122840303d9100300303042c681e0003807003804c00c80b1040d002002510303083d4070342000b000006d120382c0410b640400c0407840082c09a04000d84000100200c03050030b4020a81801444081226000010b50100c2c0c1c0d407415449191003243c2040241c90702d644010f0700b250400e6004204488064034140c2c00c5602120f811541003a6460030105071070b8180b00d00302c46004100f150002040c42c28203802a104010507c4004c165920040d071000c44d012a000d00c140c541000605800c9400c0c1c01d9840008421000000c2213282441d0400101d00030000c0072100e00140d8510729510242c070240152200000d212503000010300c3c08901510b01c941c0c08440b10161540b03016803580c0615549425118030642c1a07503802805c086003002c0c403010340d01110040c1f081c48410b0b00010002100031000394490340d041d502810180342d1500c000f0385400142c19951038440c0c2441001c0c002c0d0300b00345001c2040f090b01880c2070001c1d0b440d81c0d5010303410060290080300307403100e00044801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 58521990 1250 58520740 58520773
    0xb0310060906051906091802090303040902030f070c020307140114030f090d0c050c010c061e0c0f0908030f031008030c0d0e030d0e0405060a0503030d050402030105070507050706031d 80
    0x1040f508140c4a8a02032488042c0702c1c1d801280c00d01814000c103a0101003405150740c0000c240d0007080d240b9400615000c41d120000340f9580195104500464000041040002800a8154106905061031041d01465900003500c0300483e0140c2003441c10042da000741d09a101d080c10001c0b052901d151176a0340e0810762000085000b080700c4074002c4d840390062a0a007948160703840d504180d0004041c2c030f0700300e4050b07004441c680302d5450107450742ca0303c0341c21040048008400d060400e092201f400509505000c4020346075940115508051100403142008128008070881c0c16102c0564130302039896844410001014010740c210000a00c80031580d10414500040e0b000c2008680740c8944034000741074810540d440b0f905016030700c0051030003680782c140382c101900040d401170030090031125001d40f00c502080c99a00303c44413040d0365903103d03c240b20a60500303204a41d0001c00700e01d051480d01c60141c403002e50343c115602c60001015500d200740100322030804404c42c0210b01050982c0d284820a16150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 58523240 1250 58521990 58522001
    0x6051302010e090c09010c020f120604020f040b0906060f0c06040305040509010e07050a1d03031c060e09030f0a09120b0403030b120c010305090a02060f030406050a090f02040b03100609 81
    0x40340402c0c06000501198500010150302c141c003521816403500c0301c07040c0111a49050f00d10120303003100d45050701380101c1c0d0b0b50501c550390f5071101c00300810441c64240100302c0040089980380d0702441c5400c00c450055126940340c00c0d840b038801c0c0c4600d41c2c4c51300002c4011000348500030715001607000780030a000406500c00018011910200c1c4c01982a0762a0400341d45100c100755403603004070303404100466090380590f010044204d031600340140c0121102020a042d0b521600394600381c01802c0d00890003000305446400050103289240700e00514106580541c1c0c0e00c5600117881500c200400e050300032510504040e000341c513154468001001d480d21b01042c1c10b50090f10200c0c0820f00304154690581407408004140c1c5c88400014040c4030659401580140005005001c8502802200c100941c071800001e08040c80c940c40c4d201c3d0384c0c3c9401d05003030007201d2001d061880717814149100180800c018150402c1d641d50104d030700282038400c0700300007440d02076070f070781c0d800d41040c1085e10009184800c3d5100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 58524490 1250 58523240 58523243
    0x503010e06040621060f020412022701030b090c0310050f0a09020109060f12021603090801200a0e18060111070509010306150b07060605010e0f1302030c07060513 71
    0x206442500c80074104401da42c4180a601c1161800c0d210110b4802d10152201103681d004000001c1d201d201010140180e9005810802c007484003058410118144401002c40c0815098841900c80351070b2140e105600006200280200000b00040703041c460b814001420a1080102140c4818410300740300700261000300c451400e88590350000a00d04040c03800307503400160381651031051460500d00c0950b4008180c03291542044003002d201d02030001c251009164503025146035000c44981c1d450000c02e0307011a60031511403070341000382d402c045e4500c49880b1840303486490a016111480780f101116400c41b1111810362011074104010360801100d00742500400b42a07071506034400b82d0900f455540c41840c8075180c0c10604001c010404500f550b4001c1096141c8130144041c060750b10311461495805c8040f0580346c99596440c20001580c002051503010f40e01541c03c0782d9092041d40003d0760b03604903001001c2119400000141104080740112000c03580e10050410940c10001e04540c900c4207400d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 58525740 1250 58524490 58524509
    0x8060405071701020c0a031d0a030f0b0711030306063a0605010504080307150b061c0c0905030309040903020c040905010f050a1e0b0316031a1f03170415050301 70
    0x308501c0b2042c1802118286881d690041200c01c019580c01c8070800240700c000c1030380600303501d0b2148040e550b20030044015030044a525002c01c0d00c0b41000f4031502c10180c1040244594107188000250002c0b064944c06901281c0d0f140c3c85911689585105d168075000e91805001c40043d00f81181d5403d041100040843c1441000b0b526180d00042d900d510603402454059802807080500042094008200a0131709140100f641903001011034581d0f00136074100041000742900c180058922072184002c001150320f80b4684140c03500003c25168858103541c540216112010b0105142c02040104d01610300036100f007003121211b051050007800303080c5030200035030704180205030546450700aa414840c1c54000c505416101056294002c0c441004040c0e00350045d5048507100545804900c00214040d011081100c0e4082189860101d002003600701c51028044551031100c00484924007660352040c201c8898205084000c00c95000e545d220700750404070800001c2040b80d200c4041c5048880340301c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 58526990 1250 58525740 58525769
    0xe090c03010c090b03060d050712200d030f021203090114010905010b040e0901061d07021e0d05090a03021005070c09060803070f030c060501030302010605120304030b070c05070806040507 82
    0x20503090310519800000081c07080c003c107000c100000e000454020b40020f06103c031080640e620b03103003408201d030b06c2040c0c451001c50b1048144840c82e0035814003548800c0c01041d40700c02c21400031f4140c1d5551000501005aa01c2510a00328000c105000c459218a40d00b15200e10b0110a0a0b01070310990401c0d40040c9216000040d1100303660003514107139285818801d0a15040c11002111590006c004444641d21513100003038080c083c018021007140f4100e405004c034646110060b1070174001c2480e0ba1148005610b84092900700400c04180241c014604140c5d81c0e201d2000051604004d0340000e948200c2c0c00c12005038440e0440c0080c82618442c000d0841960350380c1500c1e80496200e03110f40f1015070000c04c8514000f802c040c403c40c0507240301e41440b51000c4216190079040390320907042240940c0d550201401240307060a42075400a04820086207003d0965482d90401384000e00a1814031240a9122003040070521400c8050400b48044440b28505070800d0359458006100b48004100c411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 58528240 1250 58526990 58527013
    0x2010c1a07170f01031101020a0f0b041a04030c030509190915060815040b060d0f090605090118060c0504080f010b0405010f080d0827100e0304050108150312040e09 72
    0x5010140f1510341840c54801503803079911040d140d80d005007682c2e81103000e0702d01a103001900f090a02d00400f80510442c1c00c0340e103024a01580c040c5003200e03900c016082404104000a0360011000f8046076140c603007507854070291004901d80220825110252100c0c20a02050360f840e21740c4050f0201d00000c0000b034400d551030724180c4004030245c0d002d900880300c1090600c01c038240754000c4081d103035000d05180c5c500584803088008075100c01441740c99050f00d850b01d0b030b428060710b1b005441d004130040c002040701e40d0031150b240d851488040c0c0e0003440c0b103444400c440341c0d050185003603a0080484000351641c41d0006681d1038000c04011758020710a0340f82400105201c3c201a0f10b1740c06903100300004194902543d0015036445500400c540740c03010301200d003000c101c008203500080c8555a030004080c456000e0f0071300421b861080c90340ba003140d0f10a01c0100300d5a07900c1101241c102000000f44078080410b40c000c04d0414002c0120184032001c0000c0004e082c0d240d518405e03100d0b101c510281c0b820509803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 58529490 1250 58528240 58528277
    0x60e3a210804030206010e0717041a010501020303190e010e01050906070f0203030f01170703050d09080c06090306070f03020712110c03150c0d0204080a05071d01050102120702010c1a07 81
    0x90702c0140c0140d10080050002140c08540c05801c603107107091428030074001d8144408030800890b0111003e007403c00070706002c501c4031140030703014050034001740d0b085241511841d0b8190707070750b507007544403054a0b0300210041e480d0a51010384800341c59802488503180101010f0f586010548080000910380355418800074070100c252800741039028a050101c2e441d2034019821102401007180711801080400000150108950741c0146500d444014109181505140c2000d50b10544503004100400005007207940108480d0b40c0088c8504205669001e4182c00301c1c000c4c000d0020051920b814021403607070190300003e1348010710140c82c0440c1d10b4410041c0c14507454050901000419110070b00114071216803510203403180400003140107007402e40e2044201d10701122001c054031030b900324010500040071041806441c01c2c8118440550030752400b00002e5403a900c02003202e1642c3d002044003c11a88142100102e05404c01c0c04440940006803071001503a100b5140707031000c5406a400c1142d035000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 58530740 1250 58529490 58529507
    0x21503070203030a051e040c090f06030503040308030c0f030c090a060e0f01030c020a050106140319210905180613090f0213090b0f040c060e3a21 64
    0xc40d4080c0d030844e1a2021580060301e400b4041103941915030f10b030700160380411554184aa40910207408400345400c1514040310100c9a01e100c5984c244034041c404100c000080340c084039809180c0d103589949000102030140606c4652140e4a0780c00400d216040c46c406001e411681c0c400c54203200183d5a03104117440304442800510780002080c0304103212503009030b000c811401c41c01c2c010389058014135a601c4d400c40d80311740c12441200d020240080303c9803c00700400c00c1007000d04010354000e405180c0711107a0660b507a80d14400952107214400c0c00181c030071904c0b80d0041901400f40100c0d0f501e4411038441c0d500049400c035000e0103000924036210181401a090b00f80c0c0c1200c000350809225400380501c0c10450103d4088240c1c50741160b10020705108540f6208540403031b011005410586000303049241298890303020003c0e280114034bca0368810f14503c2000c2645420008a454551209583e000c00d41c01d44501500c1181c003420288184c05117801c0410317101c1c0d07240d5030002101450a50300b208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 58531990 1250 58530740 58530751
    0x705040b0403080903162105010605060a03050108011107050303040b07090f060e040f0204140d02040b210601050621070e04230903210406020c07031a0702011e021810050403021503 79
    0x444c00b40c00c0a6000032159200c5c80462302841c004280c40c1c0d00c1d8004110b4641c0f1403c1400002541da02c01000a148203201d9061180e8001e4005c03881c1c4030440d1180d80d03580c0000f60000c1e000b5405007001c5aa041c0c0245481c2c8020241c1460866603e550780b54060900310114050303078003d6003810709980c0d900a042c400c0b50309980c074889481440d03928150a010410a0103201203800942d5492941c201d59120b0003004500510300c03010118401c020400c007030805c10187e001c2d1740034880610001d007400d46504c90040a012040038101015034650004031000790750b400070f540d0407615250701036032a104041110884e00307180f55030a035810340300c441e045541c0317100740004444034030000c040e01440741c0507607001260460b025500250800c03030b16020301030600380e440e03208407481e10010840048070b14000c8078459102800d40000c21041d408244001000030030072a0160305183d0000304c41007401000c800f08524888060030311065800c0030b2034040c210b5802800280d2082c5100d00a031800d40303014004803031240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 58533240 1250 58531990 58532009
    0xd03050d14070527040f02030907060203030c03012c0f1506040308090405040317130b060301090507050f0307181505090411010e040f051303080603070506070b0705040b040308090316 80
    0x4894404d000c07075410413240801e011614910410200c4e540c1d0350107464400c80c2c050000503641d0031702ea0100c81c0360000f1944010155001401001010403021043c2c0341101d03407100707080c0c0381c60800b5212128204941108248115500d9085c04080041200b10310b00c5681c80c01b10840114100c0410484180518800240f80c8141000b11450301c2c1825001b4a82040c800d090800030400d40d1003003000d0070b003811141c01c0030101e00c0c401c2403024811201c160307541001d4154000c1100d000140c84003500c80c0030314055140980c00882c0c082c25540c50400c241d5008040585001d1800c5a1054803400913200c003041c1710054074014100810702e0700c0c180c04020301980d8003200c20b642d01000800190742210826011550003507560001c13442c2a4514010203201700391400700007890307004a10b0040d0503000017409042c06130b80800000d00482c0c82e182d0407640c245801406450140e900c4820403070b030910442e04124601c1d98041000402c10115402824403050300314151990039500700d0748001200e6582c130800b0005c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 58534490 1250 58533240 58533247
    0x108030403081b16060503060301110f0a030506060d0c08060901060918180c0b03100e0903040611010b0a0b0d062301112a040e06010501050f0a0c020d03050d140705 72
    0x40181c1c2143d0072002c034540420341e022038000450303001004280ba030090300454400020002245028804c0d01440101014001d08000184e028900280141159001859510b401040d007a13038070f00064402041d0307c1350301440400d80035040203012003025680030b4003076051100080303900d600030346a040a440c0c21107200b10302d8803000c04100024014007018000b202e0343e40608100442d0200c4c42c0303180506500004180d903400c000c003681a0000086d4029040700c82c0103801e20400450201c102c4084920900d4000318480703010b1042d0313005000100c1126030066a0441c00120101750001416000b010403008103d03036580c608600714101b41d2060400b54130b03a01c9644c820317140d6002c0d404d800f4005201004903800d6945601400e10003801c220201c1c101818013400e40e102914050142c0503841040c074010f0101c070351514001030007a0203003d101e8000301c07a01040414805202e0841e0382a81c1d50000d0800f03e881600382405090703503122031120040c9030304091400c0f69a9034000340b0240150300c0356440528 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 58535740 1250 58534490 58534507
    0x1501120b0d0308100b040f0611150703150803030a05010e07030e120c010906050c0c0c010306140411121e01060e01020c060315131a0306040b011a070503160605010803040308 76
    0xe01080c004c0c2408060300074000f011074142e90f40b50140c0042c0ca400250b5030449030400e880601020160f00a0020a03480002c000042148031a2030b5074004800d4100846d08950080186039082401d821026842c030000c001c014103208640c01560485504000c000341d01c0d101d00300b044040c0c40d4084c0070b1040907400000e14499418028000780360301e0380c2040c0001080142a80c409040d1941580c0c910003011002c1a4200f2581040c081c00788070000c2401c0801a0354604004d000d5a1400030707465920460b0ba410421207181c04410454064060f150041912441c01510f9244421200069107404810940000c07481da4002c050061104005030024001130078014204076075035200410000c103400c0100e240b080070380c8450015481000e00c0030030201300620480c8011200c0305507005103038802c1c1e02007418400401c00820181d4195804c000400b000c60a907040300900301c0c41042d000400070f1000107071103070b030b40b030300329000005100d2240a00b4041c90341e1700e018a44d03480c0211b02026000f01404c002e08403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 58536990 1250 58535740 58535747
    0xb0406062a031218030806060a17060105040305060c0406090f030203100c050c0a0b0a0515090a0902040204030b0a0b090603030306060a0c020d0c0b0301031104051003020d02010e091501120b0d03 85
    0x1000c10340b2910301a201d182c10504140b05850004501c101072000c404c00c0041016000042103a02c60415680039050000c1e24400400c0303408001003040c0c9100d0f146020031540c0e40b00310200c40c095038001089401901f0161004912075015104010000c0c0100c64007164407850310420300112600100201645501014488014400c001642d403e0042c00c2241c0c4440f81006e105440780c050042110341158505250940c1c20f6510040103403c1c4810002c82e521441d98132400140e40000300a00b0014442c1389500c0404d0092084e501b01404403d1007a0820003000c5207604051074103030040e1101c3c402e0b40c603050141662400182e0700c0fa680001d003844030415091041c05104110340c0010075406080d00705444040784403440c0e8004882c00c1900100500034440340c801400344500081d1820002031900c80070f0f2445008050000070b00c2042c050025009681c41500f8405032403d0060200840b1309204180d44040402025078902042d054440040302175850b21034111341d030310058043d003820f140c140c2c0c084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 58538240 1250 58536990 58537067
    0x180b070b1f080f0c0102011b020d080c1c090201020c0103140619050604032109050a17030d05010f1d0c04050603040f060905060a050c09130c0302090409060b040606 72
    0x200071100071140060380c18400c00180c02c0702d42c0044040e0482100c840d0009081d6000c801c0880420b070140711495605550008120040600c0e61400d0003071611804080c501500c0b6540f0303d03940c491550420b622600d0500d40c491541d0610036022205d198481800543c2078504048120b04036116a100045a40c18143c1c0c482c4290440034250080f80c5440c0c800049103600585c2056039204007024015140900f5020b10300659056410010121460440003c03400809802440f41c0740d000e080c0710350848502002903a6008030301420600856844007811100c40c86540300c0c02076071081480084080c020050201b41c0611a43d038619860b09040406011031540040c20440d803d003200316161000c940b1920030030240381c3c4100c016007803608102d48040142c500182030a00d458608003c0d912150f640c0340910140807042c51008549003051a1081d4001e0245007001034105003030150010803c2801d9124151040c0101c400b00301a64888200310b8814580c0c4c0c01e54061102d8a1615818100c08000d81 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 58539490 1250 58538240 58538281
    0x6030c02070305120403030908070305031606020d1d100212010306020c0708060f090c0f01082a07030306030b01080604051009050102160609031403070c1e0f03180b070b 74
    0x466001c503960350703202031901c54804038107103420801280c1801019800905c0000500d0070100501c2000e083d03481d01c50b10b900c240c8521003481c4a0f00101d0904200c075a0f0161028103200c90340030040824070009d0903000e0aa105118601401840030904010b841803007030301c40e13103000000704541603030840e52401d00940c0120000c0341c2610070040001208001001618421500310551410310b00300804a54541121620f00611a4824260304030169901c206400ea05c81080c0d1001d041094542142a404104440100068440001c1c41d42d05254043c0c100000310780c0f00310792140d40347c0e90340c90409407105020f8030002c043c1c2c0c0103900034804420190b0812214140181c0c001442d100c0081000d03424211850021503545403a038450009268020488a01c040b120325000c40c80c41c038215030002e1180151400040c6000110700b00500d00b8001400030030341c11603019085444e003207031a04002c0e20640c94500984a4103408a4000c502c0d0f07104402540c103581d0780150941200d4644060800c1a01184c03c40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58540740 1250 58539490 58539493
    0xa02031314010933050f13260c070e0103030215071806031a01080103020112020a0203040504180c1403030f090609150a0f14030403030c05070c0617011e06030c02 71
    0x80d8039002c14201c00381e81e10544d0f4541d2034a032201060b40c1911500c01360031084040401c1c506001c101115440807001035105c20781e01081407034070201d89442114180114142c0e1441b003581505238203082100c2008040c0045070384100c4810a550b480c85906800090200400603040040380005d92242c2860098024146060111209031000c40058503040c19074883d100082c0c40345602031251808030b00c0588c080d802881c00000940c1503800107042e244481c60426001d81d0300280d04103221780b084c4141c0c1c003d0b0500034824042a0301c4554803039003540c4400c00030380d0340181103980040d01d890801400020790388050003075810130003030400d161050f4201100203600074008004000072903441810012042c40034058250f02d400f150740b03000300445d0030480c1c0e0380c091202c480001052002c2400981c0c0c0d0040d414500414881d0070840101c803035005206008240d03031460040800c0144e0407212148246441d8ad4024006a0382c0c1c1c0140c40c0d001440b451410354001400d08144a114801c0d0021039500d5510300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58541990 1250 58540740 58540751
    0x30f0b090a12020d03050108030a08010b18060424052809180c02010b0301020705120c010605060c010e0d1d0909070b13082506050702010c0222050a0203131401 70
    0x440b0200c0303403000140c2840c01078101c015010702040d0184501c9003d03040c400019410441c01400107420715a046c061202e03a448085009200410b080b032800060b0074000c2c050315100d607078642c42480100f0851000c0b0303a80162501e140c4000520800981766140884141c5225042d12220b0f0b49468a8545502004000820b00046540b6801002201544541da01c1c0042c840310344410007400c55410f1220035100342d00400951003c104000ad0b040600c4e100311441503555450185420300500a40d403100390000c0b00491414000030041d03000c0314080c036403101540d20354424800200ca9451036952410104072450002c04050308010b01895808029103040396052910f0b558414100e82154182031501c0e80704080611003580288072006440000040c1d030000340140d840707803428825050107514208107011542d0800d42e88200340c02e146154001c0c000750301015688100c060036461006800e01c5060030403011803060541072080f24841d00c42031542c0c2d904440107598041050358030fa10095095902c44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58543240 1250 58541990 58541993
    0x20906090406180606140d0f060e0915010801020304080f07050a021903030201060803040501200a080a0807031a10050d0207021906121a010f050c010e07050f0901030f0b090a 76
    0x30b01c03850b0050802c485142110425080e1a4010346006800c00410003040111340c5243c103980c582542e0f0b046201500c0170030407000302c00f41000240f515600c001101043c600c140600c041011840c0f54a031003c0c2480304070b07582c2c0c03140181400e13488107036002000908104800641500303c0806850018170403001d807441c120603074001864001805800700b0350003075032406c20003c140d0244503000081c080d080c0518103045ca8103001030b040e0070381d45c1807100400311291166007070584244003076480903a0048140340c9800e1440c40042c40c0104c100d500b0400702e40782c0303140f07040140320350160800d5901004200d40c00e40c058420342158150008a400c0d041c0710340034410742c401a615400c04103140325400624481d41403500c880140300f6075400082c40ca0052600501c081444403469010500400a080002105202500488039442210481502941303884a40c080d0288086010300c2190400caa141070003480340303003c0050004007071100a01c0c0300322200741500010305910101d80e000c1801e000b5680e9107180c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58544490 1250 58543240 58543249
    0x90d0609030e0406050d0210230a03050709080604020d0305090109090203090307170c0c0d08040b0a020d0e0423070306050a0602030405011404030f0b0405010e03040801020d0b06070b01060302090609 87
    0x1141180407405000100b881401c203403141d0002401d00316070440119040d50081081000214081c0b03080000d2070b5a445a03c411540c0f05070781078480b4019440e03888101d904014000c1c80c0039605280040e84001000441c007400058040c09150010446140e8802503541912298040c1081605010448800082c0b40b54144041d503ca51680d00141da0341d0001440c0081100074408a0340c1c9488406000c501d005080000c2c8004c103d0744161412510b1000a0500440340c0c040c50780148403003600021350308581c0f6030204420104140540380c851031480058204400d13241460200e12414040c400c00c4100811a031442d590840d8aa0400044007601c1d0404150950441d42025000d41c1c000641000319517808810440d41c001900410f508160450341c68041c1441c50b0741e0050001072003940440c09100082d40003105004652007160765840d0748003000d0b8040d40040c01c40000070751610141e680c640c1400400c5841c455440407121150b80e003008416002500803400240d0810418070084031203407034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58545740 1250 58544490 58544501
    0x5030928060201020417070303090b0901020a08030a0f050603060705180d0f0506100605040315050411030106090c020c03010203090d080a0f0507090504050604060e06010e03010213172a06090d06 85
    0x22075a0004d40ea41d030a0000320a9103601c000041c040550082004102107980514040c058504440c68190703103800c082e00403840e2080318040504070320400030500224101592002142841804052001e90703a02c00401d03441e604103e07004004076904004006001240421101c0801001820040c1003c1d05845070800c841400000b103410341d2120092145001c83e400b180e10040419150040c641b5086a0781c150b41c03a441111400d20103a00c3d500410204102c0001084605c500540204001c079a5192003101501140e0141c20260003100013641e030500301802185d1142c1d2000b0010302c1d8040c50311170308569070310000707103004400c55540b0302d400083d15850003010f004048999803500f115044c04204400c803040a404207102e140b41550030090401e00035081d0782c1c050b0302400c2c000d441c0034420f00460b02a01c2441e500c0b52088c0c000440100b8002101e5454980c00741003001200c404100c440000760074025405012820003180f140082c2036450490010b213a0160b0150002c0c0c241c10030f5568580c01e851 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58546990 1250 58545740 58545749
    0x120209030f06010806190501080a06020d023109050c0306010e0d0602030f010504050717041e050703061a0102190f0303020418060302040c140304020f06090d0305030f100305030928 79
    0x2c003c0801e120200d03c1000b144034907451031445c2040203500d009e1010b60384850400005042903000f20305910b016085a0640324206002c0c420700e120030011001590015180e040d005a00e00e1140e2400b0814402034446c80c0d00c80c05950f071000340f0315203650300152583d07101044055840085840c09400080d5140060740c0286803c28460043e54100420001510001045002004034000074101c190706c921a031160444e07080000c2080e55050203031001c1e050f401003003025269119580c0d0000070000142c0c402c40c450084000e84480490681b40120386864210004a003101000c2c24090081062030841c2e54146201e412b0040c60580e48400c40d41d250306110000d2107445a60304010019418940586010206c0d1841c1442400414101d884503a01001d403000e07005885604820819407103000441c2c09104004001501c0d00c0210300d4000d21681c01110000b007012802c401086603404080b9061003500d60010165003055401001d2100b801d481a440340002c400000c484140824000392200117407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58548240 1250 58546990 58546993
    0x20717042103050a030b030f0f060604060b07051e0c090405160603020f0406050304021c0f17090a03061a0406080a0c0f050901050d0302010204080111030405060f0601120209030f060108 81
    0x56151100780c090a01c1d81c0015018408440d07200100001c0d8020110ba01229031400c0000d91101c00002007031a08503140c1d9101064806c1c450200020b1100155052098804960a009403a124400b141c814000d20340000c2c400d522282e0000c4015049820554112800c402141c100c00c10f05e0001440920b010744065800703070001286100e0b07818584080c00c01901942c00c044d441c05240781c0104131940b145104044c200f18012011a04564400311960004100041143c15010b014109202003200c500340888040f1440c0311148404d801070001e0390741d0100c0c02132600146c1e602e540c403610080d018400182c490100901030b003060329519841082d001d0b000356801041caa59841c0f44c2511410b103550424aa51b43d071b0544204400d54522409a06603801a10b07140c1c044015803070241e02a008941018165508240100c000c1c80211000745115a0282c0c0885000d51105603090500d1030040e80d45600150300b00d150750000c4203041e0028190000c015080301c07075402e0310b40c002d14100b8800380c100b14440e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58549490 1250 58548240 58548247
    0x4030b010510020a0309090c1106070f0f090509010b0f09030d02030405040b061303020616080d020a032702040e0304031a07030b1210200d0b0102010507090f0306020d020717 76
    0x59050003403440030b000226000500d4050040d450142110310580f00c1c40303007900e499080d41602244203a008002c00c1c105d500440b24241410180a40107101040b40000052030b01c4d416004000d00c2983d440c422100b0240c800c0805900706450901654007500c941000b4603c01c015020350760f04d00b02701382c0b211882c03075502079505c441c280000c100a803522203041c01e10500050028102034451001400200c0c0d9040310003550307885042112594100e103451300905503007070200e1006e0300c0500b503400620f8114106e503810041b20592091310710100e40e071745c00c0500c2800201055980182040e500400c9a040000201e030f040650b00c2d52a5031542007090590076008014a0510428039010700862550150458411101414024042ba070392900c0c4090201c4550315443d00740c40e01c03040c0380c401510038000348452603035614407a52501c000d0080d20304c035a801036103020b0000b8101d900c21200300341500c26041c0c901503881d01d15210300002e500064620030f410341d402c20079240050070800155491310815009181c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58550740 1250 58549490 58549499
    0x5041a1603090302090a02040b033705040b0606040803270a060203040f09050103020306150619020303041202010501051e030102090a0f0806070503070f0f140d0617010e03040314030d0204030b01 85
    0x410005c094105900c4500501050001c000400140ca0b40b0000d603070034180c4510301484d80422004001484c01e03480207294032000c2e040580765082140b069002d0340d18401d44d03031105014411a40720360b00c520840ea070401d00c1582400d01034030b0884100001d844410701c0d18003000e00700180c6280003551150000d68000503003000081840c14030034004000b4480304121940c0b541d000709407200710040044040d1003511140001d142e45620a41d426401c4c50040015083c07248080a5580d500543d8241d800d04074810b003003040700348140502c9040c2c0d600030b0405220750000c1c0303001c0c0c085400c00d01e410907030554091210103169190329210500420b00300340c060409501d01b0b89080c0c14044060482000c10004200704008a50000490217400e40079240070080044018400c403004500b01c0344025561034001040704050405801c440140c801d02c28402801e6440500d4039030889096554000450300140810804202c690300300c048205000c07015a0320f1b11804820300002c03079000e60030032541e16241d01b00501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58551990 1250 58550740 58550749
    0x4020f0a02060603070e0601180b120105030f0a05190611030705030103020a1203050304030806030f0a06020c0106120c121a09100c020d08042004050c040302030d0c0305041a1603090302 81
    0x160010004d80282903101e061103001030386400001c00850600ca015865034401c0070180d03155100500d01a400580c0300e00566002401540b001c0c81018842e108807100e90324200000b007038003c4c50303982c400000c2c15811110201d01d074803108084801d94000380c0d240c0442c240d4080980040d4820800f6561349596581544104433400d80c2d29000480d20b1a00c0160020000c1e03003140803a40c0150700343c100802541d90310000245000e13036107000068540500402d850801019402410030017001c14000c4c0522515010218440040054068180041d00701e00700541c03104850003c0b101400341528420000101d002404207103801d0f6441c440c2503010303005c0e58440840c0c610071810307a9276491000d069600d246210040c989000508054031035826412910f9944e9020440c800341104040c1c800d121a141400d044103036500503210a9019010759103401c008144651b503100091a0b240e190740d42403905204004444d5145907201e52403004007003000d00040f000c41200140d1031403081d0388070b401681c11031041c070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58553240 1250 58551990 58552003
    0xf07050610060c080306040504020607050a03080103060f0b01090e090c09040305040f1d04060c0522090506090601081302012001021c060f030605090309150307110a02010903030c020f04020f0a02 85
    0x400030425003c40d02d42c0001c1d600700451390840400c540100c1c2039115800020914070840c10000c185207d191415001c040e00014501d040b64011801000301e07190108484054039054074146001178401c641c1441020120041e45410619600443e070031420300354003098143c1000c1d40c094021030f0003c10100044980b86200c04041c107600703201900040c1c0720728008058018080e000500031503e580c04c408216118400341c0d404142d8082401d03a1081c00d00c5802190030500e401848151810003001980380d0a140103520300902060303481c101c05545030b0115114407035116070103c1c10402d0321380d00498139001401480043c200e90000059490080300c04010100090312110f00c403041c1448402c11400c105440b00c082100c0d0840da010030281c3d20000c10604600c40c0410f450740c000c076051091a8060142c00285101d41c0064440e445000318001e40e241c1c5d40c081404009000942e000301c1400064458445510300360304c003412900f5212482e00000b0160303081240d4000306510041440101c25a040001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58554490 1250 58553240 58553249
    0x2060c030d0c05040515070501091b030c050901080a0206070503040f0e0a1505090a022b060602060106080408091012141006180303030c021f0603021305061e0102030f07050610 77
    0x11031625140c8000324800034586c035003400010a0100340310701400029000000c506511640d201048150100c1c009880420b03070000740c1e81401c1c0d814010405091542445040c0c88030b100003028640001e81c20001d071782e4081041250f0f107010501000568080c406487c1000e17289144001480d4500b035020074040b181a141400c8104e0b00020f0b00300017a44552281541101120501607610190400c03d0100070940c00d140c1070707039044500c403040745070780c01940580261540e9030700b69941641e80303440854001000b624040d00a200400c10300e080c91805503000c41001d21641418503c1c0c0400c890070740101c0741201c0420b20500300110800c00a2000038035080003130100c904003480c5d08074203400200034000786404000c0c18980c0c0d40d14800039150081140c412030030380301c95500b001d50092610010140c103007440120701826802000f005a1503190040354451030024041d1241144100014202000380690700d60542c0001c100800c03a03051948000c6c003145018100801c0b0b24140700d5021214086079901 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58555740 1250 58554490 58554497
    0x507080a02031303050d021e0301050102120f0405040f140f061009030b3603130e06010c020108060a0f0b0c0f0d090e3301030e010204060203121302060c030d0c 70
    0x300410312074181e0300601011381602e801034031403510a0b1100000d1180c120740e180001100206101c4207070961380194103840f02030703080c0d0744000309a400000e221300940c0f40c100ca0500040c4418407030303800c0640c4a0601034007110b0020038075104c2c500042c19054010b5461145007030b41003041000c01d003801c1041c1c41c1c0c1c6120300d18106540e06e01e1611510351740c00014040c40c0e044101005510158800040800d060328904401d0050f00501e40030100e5480e44107a01130001c41d1103107030000074200030710701449118210685844450086942c0111000c4800078002c3d0f82c4a1040640070484c5202e0000c254041d015245859a60b02504ca4103a0702d410602d13040c111090380300041000c01c6a501000074411182c9611a25445454a0404c2c40c0c081d000111001c561001144040701240504804801940c2c8280c804029401c8942c0a0500b0303881280030341000b581c02003001c0f0541450bc520301a40c0300783c0b40c00007a031040c4141e900080c0258400d520b8100241d0000c5022441c1928074401c60141d84420306 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58556990 1250 58555740 58555747
    0x20d1b050901020a0b0a06050913030305010509071e03140705040501020c0405010f0b07140109080301050f0306040c0b090103020702060d09020310180602030411030106030302010c090504090803061002100c030507080a02 96
    0x180000c2d07a80c0540440100f01703a80d050007040700ca05484e00070a001d440002e140041c2d40c03070b00e42c4040510000800303050740001d007400f00000340c038104444402d0184000c1d950303a080007409285510488000b001c03044041696402006a251603090f000303a00940ca1907407040d03611490000020700d00030500310083e2069242400402201030500d0381380040710402c40480e42c54150904102ca60f00c1044000034600f07500702451282008507060055060350821a100c0004403441000c0c035980f81c1c0c0c1103074004c02072004101d040c06840c81460261103200d205250261600481d64003084040c0c1052030404407485e1034540040c01c602e42480100300c1b200084000b04200a44101045503640040c0c00140a859002000c11b0601101100030010444068003e112655a914000f40200710792440c1400046030038401143d076142c580200140c80b50484122410742d141e0f801003114a40d4036503800d10552107103001096801c1c0d410f016002c86966540c400046626060700302505482004200151151040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58558240 1250 58556990 58557007
    0x30f0d03060e0c07121202030a09060608010c020c12160b0307020c2e120203040b010312050c0c040c09030c09060e071b060f0b0310021806072d06020d1b05 68
    0x21400d465609400480e43d441e400c45c0440309032140020041e40000b070070300003c100300c845a6903820005d400380c440c1d0410806c1c11317529400c0300c2c2202c01c5291110016040520001d5943c90205000107044883d0b006685031070480c060980103240f07440d44420310414011041007003064042c03200345c0c5194803c0e6200a00680901000c685130042d0104006c03541d03403140c0c102d540840c8039100035581103c2c840011583c1e0304003410510300304a4244011641c0000c00c0242142061281050b180301c007603001c00400c00300610008100291500c1d01900302001441800040410410901a00101889400081c1d402d003000071030180a200100600b09220b0100c01d03a004014440302c0c046540f035084800000c800032019910009030107501d5507644e042c4142c3c082d031600c68440b58018039042c076117803000c14240a003d100b400120301940c4006418440500e54407413001c9403802c0c404100021a203400948428a691100100d0304920301008106685051505094080e9000100d600e01d0605049040c400c61 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58559490 1250 58558240 58558261
    0x3050607030905070905090307060c0f050d050415140a06050303090907050a09080706030605030c15030609040503090603010314060601080c160f020301060303030b150310060518030f0d03060e 84
    0x40d00020070150390b040b107034050140038407044018220400c0300344468100301c0b030b030a90707a500450340549515150200c0044500d0150040e55031485045c0c075810b00f80074404044000030500100b05503042102440c01d41902c40e035500c20300c4040c140d420b010300c0203130610100342400c903542a08103a0107680304000011891b51025202c0b54040301600d070190f610a10b1000c220749c04003256210300e540c0e118a41c800304400f909904000184c0f003040d800c4840080c030000410012500314400318184400070404a01c0302c0c00d1880c50103510601800c12245006900e001051603035001340d0043d1500f42e07144800702c0f10132109014250704501c092030100424100b0268031031280c4522401850402c0309440c0401c100142c001d0100000c60b0020020030005549003009800f51039035503075051040e025414800c18901d00c4000383c81c050440080703065101801c082c02981c041d4028442c408146200c100e138804035079020015a800881080090700d4610140b26014095440907000010902c1c9903400b0031541c600d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58560740 1250 58559490 58559503
    0xc080a08101a091c0c0303091707120b060d0f05010501060e0103090302060f07140315090603030403051504020a05040c09030201020c0d0b13060213060c020a091404030c140304090b030706090305 85
    0x108a03144030042c91801599944c0b0980403a0081c50100300303400000c203040d0080081004c68401d581c4084e004020103280c10740720041d034003e86980c0900c4501403000304000e508080d034000c0c8054410410032285840b281e801750041d80d0708035003580d190310043c004150312405a1080301400e0038140440152943e000c0c0d12120f005100c1c0c181c40d202d2000150b6001d101d514403505920081443c20f55070301303101401c814180040481280141404c0c004540d03e810008119011260001f01078015014107907024503010b54054400c0e603010941135400b14855079144540154019180c80b2007072103614520029091040320310300d0500c5901101c203500041280d0082d03080d1700c01c0900c901c2d201c481040b4a401402030060004664211001400204000e0380080030058154001c0b00c101207003130365440307280341a2980608c0501c807042d241404900040e018070325031500ca5224440d40341040030110074507071a54005901162899850313101c6008541001c2c054000a0a0a490b003c250340d400e68881c1d96a500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58561990 1250 58560740 58560757
    0xf0b010c020d03091701020d0e1501030b0703110d0506030d03050c040e0a0908160b24010e01030608011104090e0a17070311010c050403051506010806040c0c080a08101a 74
    0x54408107090b0070540700700380e440064a41c80000901e506080900c0034000e400c00141340440920300100c14008200004e00b1200c107100c129500c2c2000d80c203560304d402140d80003500350000c0c0350710395104051544680002d054490b095960000c3c192801004041c0741503402d110304002d05103400c003802480090303c0c0483d41a2042000003010390f407146942c010007010039450140c0700c01000300703540344a030b04400070b212a0180a0b02c2070f6200d54494440c0d42c1c00307030007140030040c800e032440304a00a01d55000b44485003c4500504002901aa50303018003420f58801e0255140300160002c0c0c14022810300d403003802110a0001c00502603420180c2d20100000510a1003545c0c1c040040b6a1604040c0710f01c40101500607103030005d10010001e0a0060803e0300140012507280c01150009000440650b103090f1285905035500d080c2512149c041c040180b00c060341c001c041000d80807480c1c3c0420741c1000104034a00146e901d0100310700d402480070801c1186a04043c0c00f850070400c2000390314481c0e000391000740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58563240 1250 58561990 58561999
    0xc06060a05010509100c020d061d01020a1b030c06060906061b1a06061b010207150207030914010309060509071d07020705061b0d020c03100605130f1e0f0f0b010c02 72
    0xa00170103c1600c00720500301000798803050b9669481c0c100304c15a000100c0c09907044440f08600809014690b09034018940d420300040d4060b032102245103600005000c02e030b4041c0c2400b168049070b9849032025240a9000010010b4440c001000250751042c07804810305107002418604540703035918100d4000125040010b42c000640c041002503680e101107a0043c119a905884c000021042c51f41c041c1d00008800c0c0c82401100d2080f8801691600854689035896900e0540325400c0c200110414841c601410741050359402e586800a507042c8140c5004201240c01005000d103400300c10306501000c2101014940b01c0c01c000d100c40c0540004019040c1c500072104107072543c6e4944a0007d03035042071081d10501d44122030a0094464000c10b03070203088071043d025500f108000070382071400c0d120f0724454140c03c000c0c84056140c0c4a9003c0e071041803100c01c4018040390000c85201541010b0102800740409140e880414000c034030514441c40400ba03101c25002d100401c1c00c080044c1c031400400901034004c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58564490 1250 58563240 58563259
    0x9030506090a0b01090b040209061c05070c050c0909010e1009020307050a0602100b030c060409150b0f040902070c09090c0602010501080c010509010e040e061515180d0f020303030c0c06060a05010509 87
    0x30347d40e141c0580f11640720190841761101920b0b0b400071a540e00e011000d890841c600b0010410071445040c024141d10340000048c8503544281b010b110138120700a1901417155030b25003403000030100034042813001409490000c034030500030740101130030b080c0c0300d61006114540014040010326004a04851260340c041c0000640c0c2c141c26002c42e09000e044103445d6440b0b41c0024004c1000181c5920040641903019001c0404585138075036005d0794802c000c0c404402c07a805010400900e200c1b50001d000d402e1080e030103d00b06503640e417806010b07110039a408840d00d24009505200700ca509100301401404a04010030080b2540c1c8006002403013110724103810440b040344154000e4881d40c20160141c404001281d88502d800d41008075942407a1864510031043c01a40081100080060b10410503045404008107200c100c108954022895000c580203d08990207001503a42800034510072051460025aa500c00360300550605a00401107441202481c1c1d040c0510f0343c1c030400b070b166240320030765000d50b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58565740 1250 58564490 58564511
    0x111009030602070303020c060a06060e190b070b060315060a050f0105120702030307090501020304180213030b0705070201030b0907021002180909030d050609042012030a09030506090a0b0109 83
    0x1202216600081c24181c0009204010075516600500d0032403528420b40340d840d1194224601641d0071445400c00103100d1410a10041c40c04012807584a03c43c01a01031400b0f580b00344201040c0c2000ac0240c45001d9010108103035802c041c002920b0055560b0132004541c60148002000d143c40c9000c0d0b06d00581e01030a41c1401ca901070740403141c1c1c20012140c245468600000000e50700e9204541d9140040c0c0308082c0003d0315400081610b0544d51171203404010500194842d10081d00700c5192002e001714a40030000104e400600500d00444481d51103503900c000c1030001606440707110402c203000d120003404211055a000c501800d001810340c00150762404500c0055002801618820b54807403181e03000e018010600000070285003d200d141800240d4034002009034141c000c0300c02501514052200c4044141104e00301d0703e40050081c00c0c2203840740b0304e1141504d0b64101504070000314910080074000e00004000e41548020030400400580030140d4600f01d02c05018450711034496241d40302a507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58566990 1250 58565740 58565747
    0xf0909020402210103020f0604060504090504020301060321080606190e060c120702090a0c0203040902210106030213081207020402090a0314060f0109050103120c02031f020913091110 80
    0x14503c803032044000c211002e081080032403010013884202e01c540c2c03180c0c4400b00c0302d013494001d0702d00f190420b071511070500d0303d414601d0000d44002041244d240d540c8500100001d89d1440204122030740302c8040510030010908054034a280c0601068894407082c884000303005840450140303440714038030b0103c50360000c079008030360903008981c82c0c0c200902800c0003645403124004050807585000701c545243c41d880d54000c110880380400c44041c01a0000c00081c043d0110703c2d0020a858018115140343c4040c1741180b0402005081c0c00080010b500061041c444894182013040549444800b41001c864102c84101d0544114180280110b03004500c0a51070755604009900940d0003210038100e0071100c6800740c2c1c842030100d9040900c000f05100100b400801442001d058030f42c080803080f401d00a1110503512078003076170800c0360b141c4070303142c14010300c034074440c0c0700c1100c0d0001001c3c00f50320703201d61800b049608801400700f0203005240400240c0440c45240078104040800d9070581c62403180c0500c101e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58568240 1250 58566990 58566997
    0x140909040f031202030a0c020c0612010e07020304030b0709090f06140d050f0a08121f0b0714100b03010e03071a070203041a070c050d0510020903100603060506040b09010f0909020402 80
    0x440f154400700402201102c50342255601640f240d003503e5001c3d00100410460380245d0017011141c003805030041c0f060f8a01c54200340d0700603140340126401d060b580e507100c81003803078202c41034400614000c2003040704403d1170103000401c0d0040d12050204c1400c091440701007059140d0840d1046000041103000c1c060103100810350651920290ba841241c9800c200d0b10b260320100c07003015040b6489000030100b0608100d40c0060490402044810718034080104070181c010302400e50341080a0040840c94507002c02c41d8020782c011140780868032000010402d42120501896603640d40c2081100f24000b88035115007070500600010050740d82d89810104074514041da400100003905056983c0540040b0b00000e40041842140429001600c0300113001e24107049400081065101010001c2002400c1e00070300001e0030007500300d0710f85010b911100010386e1015172042d00c400c0d9641c0140711050816018031005a0400c0c2e0700c8030420352501410800c81426440356100b1140d8410301c200855a4a404a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58569490 1250 58568240 58568267
    0x30906020d0501050916020a0209070509030a14240126061302040605010e010203070f140d0809010b09040c09020c03130308030601020d14070209150301020c03030106140909040f03 79
    0x119101e5015a5070303400101028040d640c800c10701c1c00005618484a40b135480c10a0203075a01034074507070340d03154240541c2c080090600400e028040c0902d032155201000002e0465010740090800554154074140c10088100b414144405070075845030000c4000b0076072030381151000c1c0710301075144207007482c0c2d0a090700c40704841440d0343c010f500900c01c400395039030503182c140d900865081000341c0d07403078005541996001c03c2c66400341e0020700075a0701041b031420303902580ea8018240c50688588101c101407d02040c148600b010450800c18068190024880e2031140081580c052030a800c00e81c4070080d01c4004d07031103420802d035000500703202c10038024001c1d00d60307040c0014015010252a403800c001a5001119038500501c6801031494070075208449200000c0c3c010420f40c0c0c036241c104c0d02070045403000208143c00700742b000d006500450324244010242c020b0008061a207950600000802c0d50200c2500b0000641d02031110038010340e940c0c010160003a520281074014400b070340c5404d403550410084d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58570740 1250 58569490 58569503
    0x6030d270b0a180f030212010f020c1006122a05060a0e042004140303040305120918010501050a05031504060303050406180308092101090303090c0e04030e0603070309 73
    0x100054140e58100540060005a141e40510607904061003200500c24411104204e05000c010009800d254140801244800c8008141898004c0c04507040c0d034081c0200005a42c0405103862078a601da10400d0050310150a00b114002e12507180e0f584040085540030100401c06503d6a00a0049100072001031a02518040d2940c010000240c220708030071426a0103542000780c401000d02604000c0303150641c0c0350280a04290510f94120b1090300d0301d50980750544004c00000c0f021500401040041c0b00c1a04a12561a0400d20902503401105c058200381840f0f002c0060100e03a03001400c0c0c60b107200d914641503880e9528050b4103c89640d00d03c4485410920f4090040700f8035034400001c009448240d210348114503800038050703405aa2510000d4907410050100d401d207464075601e100e102840c48210700c140091030981160846645220031030202c0e5455200c0020032840b01d10030402000b40e014402d500e49440d49015107a00555059580b00e04400800038040e940a540300e6001d0941008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58571990 1250 58570740 58570817
    0x3050604050607110606030a0303020906091302030115020d021f0b06030f04051621030c0213020a02070501030b1f090f060305100909080703030f0204030f0f030e01050306030d 77
    0x3001d40d02c680c0d0a440c181c1c0010080b8442c1e0b00d84c00c0740061007034020744001d00189400e8440f914102c000750824610140d01c001d040258019941d0343e43c540101e030050b072210042e0703294904052030801015545880c015900a24220000316802041900b5601c40d04810f080c041e403500c41740800242403034045280d1150002c014402c3d60803885009034811072049007180c0210380d0800c0000180880c601ca4074002c0400c0a481c206c08804151800c50340c41d100c1c1c28642032190441c0e0018640541454124072a958085812490140d0420541000b01000e080c100003500300b0320040b60040d43d2200304203d108118072050b1552921522441f0000c060708404070300071030380314480100a004180c0f001c101c0440000d101080e01c1070f1f0752180307120542d031020380540b908106950540180c460f1107000440c42d6800d0100001064202000c4203105214080b0425420401c1c0707006841001d8044e0f50750304001040c0100042510b001401d1800d030340060610f402148038030810b00760f1030074501101030484079031903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58573240 1250 58571990 58571993
    0xc030c092e060804030206310501020d1118040b09010e1b0c01020406140a050403030f09030503070b040303050a150b18030714130504030807030e03070f0b0106230d0c050403050604 79
    0x840000e011340d10035425920300e0345401c100c0101c0021a00005142130040c0d01c4059072001c8511254481e00d0720620026040214200c2c0c00b90803103088211030408031800140d54448001848050440c1081c00c0f1001c1190b18141000703d02070380014011202e00b00754404c081980c4d400880c0340d941404070303c1c07804540c0d10845223003005d010350421300c24040410258015009104003240569006131940d649642c1481d1442d1411620744141d521406d090003140e200200c007007a07080c401091400d0240003a070704542001e180080445030b0050582c824685030100f4649810442110582110007190702541c6030510b03800460000403901d511994988074400c0001401d1618110340042c0b150103c030011551601c01440c0307426505c08480040008068400080e0013034007070b43c400030a81c0300c6d0750105c0c0e0600d13015071b4502c4440c2c1560386040c1c4608203d04010801c561388141c111062213158503500d5082a0500d10b201d10318000d1100302c00750262201810003a282c8518191002107070032000301c405c541402d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58574490 1250 58573240 58573247
    0x7030c050f121305010504050d03050a140a09030c060e0a1a0904020301080c0a080604080a080c040504090b15180115110a15050c0703020c09090304170f0c030c092e06 73
    0x40d014006450403284030009896000304160b4023181c102a10040290701079540840d4070340d0110120b0b00512410a0b200c03400300001c003014000c1180c4d03c2d200d00181030308606005074210030326448581006102e184268031501d80c000c01b54215600607007180d455a03a1441e030041107005100e816500244040000201a170001451001d40c030303420340741f12165580756074043d62203160488005d400d13602c1c10410b0303001841c411090a9488040b031810181800e468000040580d11141c4060f54035650301c2c020f2001c20780402c900312680140c01c441141d0301d55082d55a00c00c21303040500c03030000c001250380d10210405018124000d0060302220035a07850a5803460a2120b19880348190550645000002401c120002040381c03e0281c00d900103290720a0072108219014900428030941404140800503a2140c171048020750426460701402810713440d03280c104d10b0545140070080c801c1c0c0c010900070a01d80c40380c0c074145801103c5d900b042c034117042000071601a0700c00c840728030b0307210b58110b1300300001d480d9031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58575740 1250 58574490 58574497
    0x190c0209010e0408120c04170a021206010f090b12030415020c0a0b04120201120c0314101a030c1306050406120b030607120e0a12080a1107030c050f12 66
    0x4200d8580c0c8407039889120081e04140c040707400500f103010400c07960164243c04481d45074071908144090340380a4441d810a481e20340c05500d0155940d001d04501c030210716003901d10380d140c0304082c402000e04d980f520001c59114a601e1203501c800c02d80d505800080382d22603244004139001400c04032640c899454074040300b4001044e50100044c000d4000c0d0800c64605000b110045800388051242058281069000c800e2400300e002c90600c04071940301034464160380215240002030b5100092b005c6124600801140e100911f095940c904040b0188180f607512009200c505004542464695440e4600d0509a101e2020b041002002440000603502e03030080c002c005841c1e40385c0d1110070200c0401510000c0d1400701d0a07003075150300510009401c0074030a0340b084000412002000c503011b0450581c0d181002c81c0d60f60146c592417010941d0310009904004400d40003c0d020008100e50030302c080d404c100a015403178000341004a040b1401c02031200800852580c48010b005541e9412084110310b24941d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58576990 1250 58575740 58575743
    0x90807050d1d0a090e1f050105030709181407030807050c10051303020402030a1d03030612030705190f051e0d0203040503030f160b0403080402030705120319020102190c 74
    0x2241c0781e12860048218101100c050b85001d0107000c011400c10003480040c09001c549180b440c403c050381e8074500405001160b090f26540100010ba035410501494100071582d081604154100b402c0c018200d14030f81840002140c00501d09040c2404048946041c4075580c0d0016120990100d2220144200807030251010340c030842c0c41c02482c10410780155260f0050304034200260b43c84840c00c00141c205500159400743c035021000400c0c0960611101d0b500040704a40700d00e0b0f45c0040200540c0f41010100402400701c1c80d0000c42c144000307a5506a83c0303c01e0315604a90b540300030f03100c5408002510b40301c4001c1c1c80c1d100081e2410365540ca80180740c03201c1205160307412032250b04400d60007030303002200722820744d080680658509000503c84000d1070b07004214100c00f8400312442c0303a01054290042038000c81c13280d9901209401c00707004161601040d84c101d40d1044910030450b46541c3c00010840d050444d031103c00304407034211020103900900515034254000012400e0b6100a107500244001425 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58578240 1250 58576990 58576997
    0x5060108060f06030f0702010f020d0501080106170307120201020d051609050910120503090406120b0c04120303050603070f080703150c05031b0d0f050906180606010507020301090807050d 82
    0x2030755050200b00c01076a1190306a50030000c00c0010131031403c2d01003022136201200340004100c100c0410090710803070b8041122109100d40d01c4006111494080c05000c00806034007286000112041440e180c503480b88010040240c0440003034812402e000b9015600a180c950703600300024070780355080c41441c4034040c030b10300009805200080703094075000000c540503003041903590481a040c01c80010b00070598010544e020b10043c8881852a42d43d4060040545400114080b070b40c80d0038603094280d483e014000d00c0c40c01405010600c5005036070f140e400c41c41da030949404980c648814000c03c0c01d164480c1c019069034020704501040000000848404983c030900348118001031900c2290304a40c4c4160122000603010008541482002000250001d0b112002589048481c403001400c075003401c05140c0303001b9195020007803822000d00c2101d80c0903030300194141d02c102068100c16110704009005070305001001c501c0e601551000d51020750200d50040c4410f50380d50050802e155a00010030b08507001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58579490 1250 58578240 58578257
    0x2060414040c030504030206130c1a040807080d0503130f0b0903030618060f010c05070902040906140301020306030a03120b04051302030c01090b030601030f0b03031611100804062706050601 83
    0x1c1486131040500c00e580580c060040350f107820345040c0c8645982603091b2440e045000740890014a0741070791411050812075059550351030078010340d040c8617860b8001105c0b90061404000382300e410900300c035800b001584102049900c540b1744444a40340319007018100000040c00c01c0381c0c0100010085005100803140c0440040504001500e00482207074002d0304015440c1c1803205950040c0d85103a01c05104905480c4c02a4923900f0140485e04268820070840341c8550080100c65040c101800704202d080d0020b40c030b10316283c030100c0d90f58406490014100704864141c50b4440e02c04e6404011221001030080c000c50401220348000f511080e802a0310234001c607001c05000350701540c0d03040210b80982e80b500c0d04594845005400810408501900c425102c4140301c00540d001d100800f40180b00718914842c3c1041401c0041010301c08120042c050300c004107440f10510b412241c503580c4180d1200780070503150998139420011107410b030700c07107074210030b00111710401c21056400491040d1420303642c0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58580740 1250 58579490 58579511
    0x3050d110111070c0e0a0212070f09060504080c0907030f0f1a12060112021311071b050d1704081509010e1902060d14090a03090902071e06090206041404 67
    0x4043c45107001c01085801038000c100141112041c600d5488901034100500741800e40e69070a542d80000c982100000b4048041010a26040110f0034085c2c585441c009080c5402c0c5a00c055030391020116040c4200210340004180d00e109401120076998010400d01550b41540710443c003802403500528a4081050038440d5142080340c8001c1480c84880c0091903143d1800ca501404602d25400980c6c020203038004116100791140140b1f403440c4540c2c54003a503074903180e060026000100015078445408400010080c42d69a00201803902c0e400c103c0048820008015514082c4203503445102c95004200da620a0075801d001464401c80308500203008900c00700301180d845900c00944041c450344c8045218026042034005021310700301031080014940c4172145035a0b5017007801c0760703d55460342c00701c18000c08042e0300c200b844000b40080d840c154144a4295208487d008841d07401d10820003c1405117018001c5e580c00c00385003160090702d516a5282c4641c141e0404015107d070041c01141410038144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58581990 1250 58580740 58580771
    0x9060603020d0b030d020607080a090b070c050d020a120e030a05070b0403050d080103050d0e030c03060103140c0a050306010905041a010308070303110901170703090203100c0e10080a051003050d1101 87
    0x22008206e80c003404860f80c81040c19203244d00301038003420000d03654040f000009142c0244c0036004180703984078003a0850032445c0c1107140a84e04400300c41190004503962000038140510441c002d107007800d00260080b030030004030b4074285038518080c0480c40b07402800240344110070000d0040e02e025900340d41e03001602c0103044c1d4132400280310041042c1d01140525502c54440c1141000070038001741030310341c001c5100c2c0020703140980a03002030300c00843c40040d000b0620710401068200005c282c5140300560320f8000040c0d01c81c501441041c0c90191508002820005a4106030811000d050601422543c603810942d100f500302c1d0400301c1c0401d240100e041c80c07240400c001ea620f4024169900000030403046010079810070701801010900d611400010300698040c41442d07501407847c0c000040d1450ba642004244c09251404140110441142842c0c0c042e40109419481900140e0106994481c28103503c3c0004003544003400c1ca000e400d100394070040c1d0015030356a90001240091007120407110510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58583240 1250 58581990 58582003
    0xc06200322080d0e0409030306090e011a0406141e03060106020f120301050d020103241d0708010302030d0c110a08160503010218120705120a0302070b0304020a0e06030709060603020d0b03 82
    0x30001c00d1848130b00031094a010b400910039a4803030302d40030402039965100c56058403003803101c40785140d450f0045904061040c078491411010204c800344040c0b4a4600182c907008514010680100b401082d400800c00e0003540070b050b542400b808550a942c1d40d488001e4440000c0124100d00d40100c1412111001a00054038141c0d0f900130070300a0b5409840c1c0c0198003c05a003250030026440503181c150783c450629031820001d00d0b039800318240c0d100d1460b0003000030107002030000092050710b000510150300d0014003030030800021306007440d6006550030110900b031541c000f455841034903113501241000c004500100b00111010122040d60713240e5040609034024400810791a5501d5000080280f43c07410059059080c280e0a0325155511b8102050711078110f1440e01d031207540014604010160f04124030300040488205031415801c1a60000e6100b2084e4880d509145045030041042d5590031700c4100010035000c4400c00a496440b0400f0b40a03403c4009035010312881e020458589040100d1807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58584490 1250 58583240 58583263
    0x3120c061b0815030a050d030617010207030806010809010b09070507061805030a03110409050c0a080f0105011b060e0114060307061103070b07110d031e090c0620032208 74
    0xc0180c903590f85414003c626044190141c1d1500c80e01900001041c400d100540c886002030380c0200d51039051440c01403085031482035130b1055030302c1003051402280d48006a076400410034a0103c40d60f0315030038a0f05001d004810040740d8071048900901c80c146030020000c025861040c0300900c90101c0710404d2004499007500081c02580082095808140c8668803c07000c4480d0500c1c0d10b42041e4640102c18200d44040f65501c0c5000d00028940440541100c0d4480d03110181483c9842d82d50b050070002000100007200401c040c0c119403c21108000a07031b0802c03902010000020041d40950303065650b0652400d6900c0f03401b0b03008841d004281e41e0303c01c400349005c2d003624070001c41c0f4161076070b510b0f502081d0004110200300520082e1900c90014144000c1c0c15004041c1d50200781510201c01c0c010103d186104000395581c500400200000d0203810400129061400c280700320440c030743c4100c03d1040307075410181c406000c0002c00c440c966a8403e400e2a0b41c49409110403ca01e85403000e041e6074420b0b0144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58585740 1250 58584490 58584497
    0x60f1a031504030807020a2a080609070312091d1801020a0507020906010207030b0c0d06050603010501020c0d020310060b1b03091305131208150f1003021303120c061b 73
    0x18003c28052158181c2004031441218104002d42e1070b9510344d00641501460103644c0610400b5036030454103480b42c06424000007800e03250515041040c3d45209030300c00201a03c50f00c40e1588441d034050310481c0006e000411401c403d40c101c0700b0f4094001c06003280c405540385800207038420003c9051007520007800054807282c0c80d040d101d80070040c4160740105400c0c1103104515010002492101011740151007078840583c07140f070108020004c0e18410340005009410900040220f0b03a0300040c1038005031400e0300c801c0035540ca1800400e080c4100700b401d204515080240c0018560300480040c19040008a0200c80001c0541c04d000e45a2050603038807603000b0300c18072244d003400b01d490744081e030041d015061810211165581d946020401d02e43d0801c0441c01c0c8008000150001d03000350000088c0454116155885280008065a0081908100305680480e0280180e001d01014002442d000840000b2100c105403004000f08654401107071903070b0500d1484050803036407000016406071a40c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58586990 1250 58585740 58585783
    0x2a180b210106140706060801020a170601020606090f0a06050603150a3305090d030c021e030d0f020a0c0305060601120501030203070302100203120106021605030a1a0702030403060f1a03 81
    0x9956031801e03004941c1c256401131b42e07110002810b04092004101100050300c0b802891054030b0015259510000d00080c15504210100440e0f60f80703803000507030f00007051100d03190240c50341041c000c000e000541050b504200d00009001d22203905140c184240b220844002d0492500c4200f03820040c0d00d200c0d40d4640030381d0760100640d03c0a19101602c48102600d10f001400e0000c60303800039100c171806130b405502050b01611214103600b040c9203000c5000b0f44034200022074900440c0840d548040c2002443d007001040c5d14500e000c903100b4050511860341000b0541202602c0303040c11900c030442541d41c580403541218508000d140640500303030490380c0090181c200285503800380141038101130006800c42c00108039004021100c5103559002e0221503000b406d20540b06010b14000080e9a04401e00c264052800c2100080c00b00d070f0481d019018030115450640c40d0154180d00c0c40c000d64100900d501d00b80075451417034401d075503c08500010150328061601a03540e0074161600381301e40c941003c1c1894407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58588240 1250 58586990 58587017
    0x70f08070b1201090216050d050702090c030403020d0509190b04090b09040507230603090a0302010501081209040c05070b0c0901020607030903020c010c0305090307030602030105040507032a180b210106 88
    0x50740501070a04080c6c2c802c0041c070003245e0381c4505041c001c43c80200403035400710703510055003001c4107420751104190743c04a140d030078241c0307001e5031f6038495101032000c2050000e0341e403007552a0a04d000c400f005030701048a00c0c3d10344582440030720b038009002c0c600d802c0740782004248082c07070f0100e09a80100e812002600b03501e41090001381c1c1658084000070922240e2500d1400c4607140e03003004510410701d200103044449201e190013400d403401a07001c01b1085d8480a05000c11004070412540e04000403a400600c600302d9101c191110b0088981c041c3c00c40d86544100485000c0c0d030402000007540907070035502c480d92042c1d000d070100e403204a00580160300001d5049200c0d4084e40765500300e1402414014209000100000e00d02a42c0d6041120030b04c0d0044010401030605008058100c00e0a0406114600303010350305041c1d59140320403014a030b0105130360010711140280c9918034a040f020791820b072004d40b40c07805414103078444a184500260242024842d1064092046050712801c1c1e48009401c0300d00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58589490 1250 58588240 58588259
    0x80408070b07033c02041d100503121207050307050d0509010902132306060f0315040207120f090602120c0f01050403170c070f080d020903070f08070b1201 68
    0x406201c02c0c16540c001d00c050210070340ba036081e004082000e2204411014080104400d81c01c82c07013010455006000600200030b01070b40f041d0406030160302804a6a6488000001c507203600d1707103c59058020500900d130781203007107001482d0403c00840d8413402610303100e9080710745120031100c01d800510203108014200903203800280d000f8030041c00204040c030003a000107680d4140c1060040085982d4092664682d580843e8010b100c404203181801c0c614004c0f000c205a03114089032559600310010025032400d04100ca20120090098421511341c40c2c58686014115207852108010405000e40016810700c619010400d840f8a940a006e100c000b5616658a0740c125901140550154070840600420240302d441d100d9070196075401101c403515200086000340107800355030f05030320070002e18010810303040104d207045a100f004281c1c0e1710410f20600340240140983c1951500440c04001802e01981c8007550965001c6800e403202155241d080d4030480c895030710302103003400007800100301d040403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58590740 1250 58589490 58589513
    0x905060702060c010b030706030615050c03090108090a06020408010c030506040207030e19030f0501050105040b01110c1e040203070c21080c03040203160b0301091103070c0213020c0d02010f0b0108040807 89
    0x203c0c00002c03d001a9405c0007a09198071a044400065901d00c401c100c40b505205030045811524100036185ca03c1c4035045079100c0c464244a00c0c10b01001001080c2000000c1040c200041e8125504640315601e601e5058042c1000d5401c50300001e0034440450310518180c82110140303981502d502c5d104081c070030240a22004240301400a08140010000120740c0440c3da50070705511900000a1940c104410002120700c4001214100007008066001d2100002140c44044804540b0320115101c15003170240084031441c1c130760340c01c0350012091140b00c03500f010040031403d110300403030b841d03600d41d5809101003030310841c40c0c08001414031030209000c1d400300b0380110b4000b8009015100780c80d109601c02c0c03151850aa200d012a40c1c0700000400400040d8803491001c1c2c0c0c00d00c0d07c420b1441c00c050314001c00d400d003c200064400c248101c11000e000540d641160f107041c1406040c1c428a03010004064024907050203005e840909201000c2c075250301c1100040e02c0345610175810303800d107030290321407402041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58591990 1250 58590740 58590757
    0x801050108130312090602030402040e0a020d08090613090b09061203040303051804060312021005010b0306040f06030605010f1a0406050f1b121b06100501120f0c0806030d090506070206 81
    0x10342001304150304411805110070050241c0c9000d03940e4102032060004031000508440c045d504090f0786440166103901032840480d40001d4030301d44686440d80012510701c43c940e0b41800564100c20000f6022007c1d070810140401e08450f81c040f00c0c0e0b202c2c8140501510740b80712056040d0001c10003400064000c078090f040d0410b0b04202c3c00c0c81500c0c0340780410101c810070340040e1040c8501c4164803940316410003008102e01c003141001d102e41c0d45800c5500d00a8000a4040742c480d0782c440310b03898481e015550007100150307000711060166503502e65162104244030b0050512070f035502c4d4603106030394481e1000c031003c4482030381e662842c000003000b910500c0e4001003404100c0200000348000076010030050305601400c6040510303075800482c41000d5103000700599100340f40c1c1102c410015800b005061850803220203091950440c2c500c0700d41480140012603048601502d000502c05441d548680d08030302c1000168219074a08640e007a00f645c84411910034ac80c3d0180041111000500b00035014200c5030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58593240 1250 58591990 58591997
    0x206061f0c060222140904061a0d03120b03010b060306040b01090b0715140f01060e041113030203070e09030301030809060403020607030305060306010522020c030903100204051008010501081303 85
    0x6a8255948000b82c1e0320a2042101c02e00c140c00c050041303010032000400c000c0c00356800f20550400d259021400103400200044c180036038600c1028500124a4240540b202c8000d0801080d0b0103075240280144c186546540c0285240402c0321055050500c01c3c034030f0284000b02450b0031031f40c8100801c400760440d40d40700760400c00500c00020b40000704d00007401c0d110f071217040c00c410514040b0034444121881c05000021540410040c0314141c0b40240c203060540c1d844d1b2a14480502d0054085000f034121214006083c523000565448040c6800d030b88181564406c509842c0c003142d44200c1d0383d04043c0156000581900100010400509107800038082444042c25443c140751340c0760000740c02900981c03c00e03800303e926501040101d01c1d0622507107002d40421255007072100d815802c40d550130400e1b0913690024950008040400c0e05003081924025000101111890142040604041e40007440380c18010b4074000560741c20749002e04070f91816035070181d40301e000a59890406841458000200383c052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58594490 1250 58593240 58593257
    0x60a050601021c0918140f04050c060408060610020303090316060b060d0207022b06090809040e030408010e0102190507030c0602040609030b010503030a0f0503090c0a091b0206061f 79
    0xa21504a03212404218a610f038103140600e091845540c0c04d50702e08035005c1c11894090b001103584034500c0541d412070448a43c080c1c0984e07071860b2561074000c03006030b0543d000101180016810000043d400d20858042d07aa4031850b142020090780e480c00300b651482c16540040c04076038001c160064000303018a000b601c020075021a00008207910350b00842082210640001d51071065003040503e00318695104003550000302c820003046000f05416501c01064982c0300c80c500c00030b00c07a1020980d0045400100100030500984070410390300d03405881056065400c00603508090001032003500c10b8181c115a5080300c040701c1c1c90b0203e0312544180f00484c1804010881600401d40c60700c0544042d1403540c45a069050940c10180f0811038140d01240c40f0307a2042002c00e00560307100340e001903416031a0408685940361081c410781040310040e0016085a40307104005048090394114044050750550046450a0188001c9031124030440b049500301c0c0078005034845081e1804415071081c820307031601e04207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58595740 1250 58594490 58594513
    0xb010903020d03120c030f05090a020307140d050f030901110a02090f071215050109120507051203121303111506130b040204030525031a4507030203060a05060102 71
    0x885d024100000002030351010782420a40151003901d400c01c01d000010203140c0c000c0e900199441480f03000345c842c01000c201d4910341989400004440c010707406425900302d407641883e0320755260002c0c1c03412400580005080c081140003c00c050405a030046c260800711766480302100c905082c094000b2003008038005540c0300b0400d40384616290200e180f900c4080c5640f07004001401156141c0089400400c5041e0505c0040e0300080c0f42812108141c414a1002081107005801c50052802039081c1c1c40120003013014522008918940807442070b180c440260407000c0c2e141da5034011940304116a1460302010074150701d03107a180d86074072820754403001c100a8008070102e01a6040b0b94021941c55205144107910008000729031849000b604100f041200d02e113403075a820840c11055201800d00f440004944030910b41105061241a031aa0b400d903016030300b19405965504105107840343c40e0360201003100c51000070446008581e0001d00038840d03600c1d400d11000c01003801034012030552180e02240312 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58596990 1250 58595740 58595777
    0xd0813060509060601090510020613020a0b03070302070c0e0702150a0e0a1103010501060806060f07021507080c0601080319030b12150103050c0103020307090b130905010b0a09090b010903020d03 85
    0x18418a1050b0142440c1c0c02d0182c00503000003103d07041140308842c484221200598000340d81648202c00c1600b01d61041001e0001c920524a1600022411071001040018150b01a0000c1c00381d14452026400100da68540d00820080e0948010300140c02c01410480b035001e0803801c0c180c000300c802d1000034007604400d0b4600d2a002c80d9641c00c880305544401d0000c4a40341c02c1c8156401461907080c203100c0351405e2000070390f1074858000c604048403404a403000c01e540312401060f401149000c507a66951459007040f8626422412402d00c0911807c0300108601902005842d804001d0075925401d203452120240c000c0c06c0c0700c900c016003100560402d5800202c040000403000c0c9100d600380d03415035055040803070410121a15141c1418010404e1100e134a0703021050200300c0e1410138015807200b83c4020722200480580d800360380d450b8180300004c01d0005a400c010080c1c0da1103038444006040e5660348a01c01d0320030142169022600742030741000075080c0045441c080b18424030784070450300d2110f003d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58598240 1250 58596990 58597001
    0x602130b0c0a050c030606090c1b10020c190201080601030902040906020403060c08180601030b090c03010f0e070603090c09110f1801030b010810170309150a030506060c0d081306 78
    0x1181c0390302880c0c003001401800d00c110601004142d018040d180380240c0030035680c031800b400c8801020340002d0f5603505c904081500c5240759501d1020340c0d014071054180380000e0b40105a0300d034141d01505400d9410403050755048280380703074181c40308190f0342d5a520040d4010b08044405907002500c030303082c12000030350520007003002e036220342000202010f40c400d0062009500514000041d811074900411800000620504403580400288101d0303440c0c400316802c003440003100503015828039012554007405500151030f028906000c65071119590a030407010749840c000081d00045100c80e05000303000d220b0300000c00c403252000c4c90b03074502020809614072641c400241244202040000190250b915000301165900246070040c1203091481000101003000d22819940f09014400fa40c1c402d9001e00c161900034800070b20b040c8218031416980040f907440744a034280041e10740720004082d45003a0080c2d411001021008100d03040700254280e500910140841034007040701c1e1418400503100d402007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58599490 1250 58598240 58598257
    0x906050a06090e0d090902030705040504051503061e01091a03060f060f0604060f030506030c1804050d1803110a0905090d03050702010c050a080c090d030810080a08070602130b 77
    0x40c1d0780d03103022010012a111045001590f4002d21882c00015600514020584070340480040e41d94407854400e40e010310650340141c1d00141482e0802508080b507002c109507000e015000d41c0c4107980c4009400f03507a800e90914a007000e0000f030740188100c01460740408604000d041e4010007a034070060001c0e1405404940c142e2481e07140c0810409107003818169500c0510303095904d6070a040c10110701030003044220070b00e2070405940b00e0000c2e90660302000002594840985a41c3d52010070320390b5558040310488081c0e6440c81800c8003604141c0c42442071010354901c81d01240d03002c031f007140e071440c8401c01e413803c0190380b103c2106004035008019100d03403400703007107001d00501c03198070f0507440034060340c0e0020548015a4504a0741800803600a01142c100c0d5405241031425641c1d04003c4030490301402c0f00403138120801e03e902100701504001201c0c010300303030381032601030a80e42c903401c00d50348401e0904000c0140009111803000981d2b46d030042d00c251844524900300c03c3e922154600350342e0b00312941 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58600740 1250 58599490 58599511
    0xf080a0f020c0a030210090b0c03041704080a0b010f05090c07300e0316140102030c010213031b03170a0c15020406090504140705071b0312080f070f12090605 69
    0x2075003055010040700e00038686010b401e07c00d58440c2c1d00c590340401801403c901070040b000000a08002112103104142c44001d10b4040c2c0300c9440d050f1140d80d58082c2c2d0700c11500c2d828004004108207452520101c00c03a0350007022032001395280c0511541c0d45e044101d00f207490400062100c90200e130b101141d00d100c220f961040481c698039401c8010051010681e040c0d0194111050910038500a40c2d03070481512002c203080000e003038040c80100c2c60b52103450120002540701240002d8240400c2c0180002c482c010006100214038803180004c9c1d00c19103110090214200440345880b40e280c00e0050002c0d2403290822151103012601c030924181002920781000e1340d1f0005061201c40e401c04030901c041c1c0750a0314200b000703900031114840041009000d0006001e80410100100408040c442150314403803046025819900d1038141c81034100301900ca00882c0c15240000d0104014125003403003522690b80e8010f14500c0c5100640740007004890b01380c15251244102000b01e00319000e002d002e00b80c0300b034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58601990 1250 58600740 58600753
    0x60c1509060402010f031a040b06160b010e0f090a150b09040506010f090606020c040b030115080d0f0509030a021e0301060e090c0105090a0902030a020d0603080318030301060f080a0f020c 82
    0x10004111703000300c80c04007003810700d0f000c00d507190050602c2c3c483c25603c4090740c00080c4041200300040c40d41c02580304d081d5191100002c007004021819144604036038103150307140d43c5601c58a00038045510110b0f00703a10103500c18003807140420096004a406070000000001d03100702d001c00880c05c031900480d029038165019400400503d8500b44a050013003d07111000c00009041c0500252100c01041c0402d00c181d03180c04030450543c3d000c0d4454941c03203107081c0d148441a60780d1041e0f103481d510400003107404261042e208441090040c1d003241ca06000c001c020f400c11644a900f000386000104c260240307000889007035500c0d00e0b1024070424000e041300d440c07511070034544000881d20b480801045941003280511058070680c907910342d64810b9442c8160003680781d9543d41c811070b00a005401142024a08080001040c45150301c0114020035070b42d5240d1030100c211048059803171000384642000074091200b0500080e00c10884150000c2c0d04410101d140285000c50005a8001d079805281940145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58603240 1250 58601990 58601993
    0xf030405010912140f07081204030f0e0906060403061a060c03071103030702092a0d06090f0603021309030c050a0c0513090302060604180b0106020102030114061602060c15090604 78
    0x10a43d40640d00651802104030b48020401d6910390094002c860012070012604c0010072030044240e90304a10403909112080c030305070400603c6010380c1d48a14000c9443e1320000100b9040c55110140300340c4c0040c1c20149010314503a0b80e035004203108940c803900c14145508581803a59414002c11622030860000c50b219402c600b0711182c10b04000030414441d0f4400c00203440140c4680800d507620405ca01d0340c0001c144040d0195190441710703120ba5807500440000d03010004010340e48540c094400c00a002c01c501c01c91000007400720303841d500000e03600200d81c0140401c00200b580240000305d00c00d181c01050040709544980c0b07054189241142c0eaa101000706002c0303420151aa5174000711381101c20f02c802092514041c0d15484040c00c118021a210f042c51550740400b036840c042c4c010f5100d41962010340e51400024000e4001317004010302c0c40d000e40300f24010b80c41d1603002e4500c590040702086a0740142e5508200142d03011080d03d4145004640e0f14569160028031824858107410000c1c04051926 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58604490 1250 58603240 58603253
    0x5010b040503010b09060f060a3501060305060f040b0409020619030e0a0c03030c0f0b090105190204030309090914030d0603030e040e1b04060b04060201020418050601230f0304050109 80
    0x1113000d41e41c0241c400104120140c0c1d1441d104c0c2d249040309841e8503075500703482002166848501c00c003054880c0702800d8000000021501b490303c1000340300e820070f40d00340d0300c4040c21800d0b600c050740c45a507c0301b00d5074409000d62a00e9448890f204100030000a43c0c00e0055010417115000484404441041003956031405505030284006004440e0080c00e10346000780e40703411005249000280800001941708400c1103a00c2d074020750344a8020585658518204001a02803d001ca451a203400040c104100701c2000354005d030340a981e40342d203a0011603400c0c008401c3c0145003508050f00d400e03515070030421208506000a100001c0740f0040450317801d06604002d005c005800f416240a289000307403150800e00080350081c038280d803008541403050b030030400142c00340c12a6000108070360000140002c000ea015402801120700540503082c09605003010f00c411240700301c1e00540402c41282d1400c440000c1c59090062048840700d403a8202088035030310b02126081190101c0300e50799240f0030b10b0144501d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58605740 1250 58604490 58604501
    0x20f010c0c0308150a0302120102070c1406040308130b07030c200d0b04020f0604092705030313030219230601051c06060801090b070807030203090318011205010b04050301 75
    0x325041c01d03203854541c0c0d640201007810007050701e101400f00038001d4105540e038601c26402182c0082505018000116540703000307502c010300450f0b004210303a20010701c00d03548004105910400900300e0342054a5a140e108459001042c01000841e0104000c164200700740301501c10750740039a8540805103c146000d1202000b1902100100440f085080541d551940454411a5070142c901001601d40e0301c0810034000600b416036601c61000724000c01d20a086a000d107684040303a41c4501c00309031000d0703112038032109a80030180c510b400c1080041c042d60400204201c8046c8648111401c1c08008080e4460700e45c0d005400b1204008040c0044103410002c07110030750034000b05805031200d545046c0010381c078401c00b01d004d2030b1444603560340c1f0414011725a2000340101903030300007403000300d0707091401e008140070882d6010041103090000c00c101a200e8400e5034851400e403002140f40422814865041e50140c16100703041050ba258802c54524550291900030000c01d01059119818542007600350350 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58606990 1250 58605740 58605761
    0xa020c030a050a030228060c021f051009020f0304020f030a060c0909050601050a0e04050a0f020408031209071217071a01032a090b03071706040203010f0903080402010f051603020f01 80
    0x406c1094201750b41e002640591554000d00004450800400580c10005400c4071040011103c00140c1c091061a42140340f081c24007440b4203c0c1280c80309021000c0b0b0288038180150760500788000740050506016607140440b008003258850300c0d180d0350384425503100841d03140002d0065a41000380c5410303070280301c0e0004001d00b00b4500308034110074000c06070007007190341512a58a800104070b14400d29844181c04903003480d015552561107011255580e030001c0c001c18030080d00c0d440010302100001c070342c000681b00c4230018094a401325840c1c1e00440d00c01030303491083c1440c0070401c26001810b40700654442c04284c3c0100d000541c503600b03024201004040c501303c0301d0700054400b0f610002407110640f09880a40000061180c50b20300440d15000c180c2d004201011010b01a00c10a208002209849584220024060001301c07003011400c2e00c0d44120020041074003100460300540c010b5034034004692161418a04222030b60706514107041e81010180d001d60082000d04400700f40078000c4ac030984 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58608240 1250 58606990 58607023
    0x160818091303020a1101030b040204031b06080103020a0621020a02060702064203070b0421080a050a1206060504090f02030105060406140f031014010e090a020a020c030a050a0302 78
    0x92074603180a5214902050000c000191240701c04a0b04c3c0e0180e0f00206010f04054021901c1d151a40f034418039144c0d410152540200390301c000040d149100d8010541030b60381c098203041c1c08030300d07055040d505041c408070410781504032085c61340359072070301071014000c0403005038000d022030304001c103000e0305200c1d010b0130001d210448003900381003122901e900200c00c0322403040d601c808404000601c02c6074008010540741e150040d074400160100c2048007070816641409024a032107072850362144a103c1c9807080080280c042401002505801030003e40040412800c2c2030b1000c07076203030034003500700d501c1c0d504060045540860300b8001c030000c61080b68513201c1c0080c0114a9941030000150741d0f0f00030341c0300c0d03031003041003402c0041400441d44050f20310ba0505008026224200b600380480c2c1d0381e156000c8e156007090601c01d0504150702c2048801d481247c05403e03c40c058442d0307030381c0d04e004c1e5000800e4a0b0a51280f242c9460b000e44040000380607160040b0081d0104505524000303040144082071b90000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58609490 1250 58608240 58608271
    0x702180c04150507020907020c030d020a02010e0607021305010f14030c090c031e07082d010302010305090a050f100510081002032205070503100c05090616081809 71
    0x480c00304004480c1500e0012034041e42000c414442103d01d07129030f880080d0414032107802d100c500c03600098a001d200750210107459481c102e40c08126a40c01c021b14000e40051000e412542d000e042040007441080c0c005040c19520f1548555084c1c1501d40130f0740684424501c81c1e004004105580c0d0592203052011400740c20385800c000001030720b500c0080d0144004030300010100d0380d100c03c041814803160b030041039011414038041c0c4c0d02401c414801c41c3e5008075003002011184158009801100c0b0f1280c81c2c0340080e09990841d0011401000000c00c400e001d481001804404035404000c40c074103106407580200704a00019440c0d100303554002e0072801d5503074080007060205180c0400c60410010302044c1c016202d5540740c001c41c0b090398040040150301c0900800290901202161501c01d130382054088a00040181a20b103007201e0702c03d1111400103c0520030b40744645403020092121482054100300306001c0b607115020244e0010355150448031001e88a03220030b04090801540c814900c00a0416 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58610740 1250 58609490 58609501
    0xf0618010e060f25140c01080705040e1801020f0d09110609091906050a060807030c09080c01180b03010f030c0f03030c020105070203121303030305090304120b0709030611070218 78
    0xf49401610210980502c1085414441075080204594000e80010f188100c03a550804a19211101c0c0320482d800a2240c000145000d80103104503000c80345403003502202e60382da180500e071001e01101c81a42165400b0003d659038592090302400000400550010341200d41e031404441010405680901540c400e1000801076550010250ba1019280a01d8040d0055034621080140419080030750710856200000c928242d1100b07801e4414141034504003c0f0340003424050315030f40c145100d0284c0784d500c0f54564012651103091000c1785022010401c0c8011511800342890307a4000742c00c800c002400e802030402c144070307160703000300d00034001340c1c10a02c14503003151402845800c04080190601100060380c40440d2020818015542c400c14002c4c0d1f29220100d15240d00c0d507c0c1c0c0d01c07068000074244008250546004000c0b00c1c1220205005254141010b41d0b91003901d00004100c14240300303403140c000000c40e6640c0124071040c0503a0400554541c41481002611425001c1010f80e40c00100d08215 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58611990 1250 58610740 58610767
    0x90609150f030f140303010611010b0406030c12020612010905040c09090507050105030c0714030c010608011404060507050f0d0b0103050c090a18061a071a040308010905060f0618010e06 81
    0x10242e9411000410414415084c01a4003042c241d104510b544400800028115400901ca40c140d40360078000340b01d19103007a010041035603038034080940f511100400420800411512a81c00c4a2001d402c641c100f02c141c184240d0f41e06000d900840d100c541b41c00401080003841e42c0d802c0c001e07004490080000c000c258881c581d80703080c9401014148800040801c0180481409032541154481c4032913200c1209a9059600d94000d540501d08a40c01c00750003040d116410b010f10380c20f44c0314400c85030a040e13403181c46140291401a0011040c8217080115500e0400720744000c01059006800202c2d5504c5c4030740c001030443d00c00400c000340080c8144040354050340c40c0b18400c0d0480300100041441c00180a0340701000f4500e5910008000c080c1c0c00c4102e54041048000c3c3c240c0da40540700b0640380001c41d14107103d00751411180180010302110050114914030b0b405141c202030301902d10200d104000c404102c0a42c072440c0656849a00c80d4a4140d5960744103031130708003050003034500301d042414a49100d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58613240 1250 58611990 58612019
    0x3030905060f160c060801080a0503090607140a080a14030c0313020a05130501150e010f0302031f03030206160f02070b0313060204030b0901050105090709060804020f030709060915 79
    0x2148541c60000780426060306038015105182501400610590300d41d18101450308154031403a000b1450740c07000081c56003c0442c0102405801c2806503203441c1c500400c101403903000c804100c40c4020002c000c0c2006410820850700f4103072141030741e55520b001c002d02c0982052048414803014040c100108481041c444050300d820400300c0c190041818510701c00100c91000c80d400080d0808010344007070443c2041504118100e0b542070307141e60410307a01c40400702d990750010714185022407508441c083c2010b01c02d6005503485541250a40c2e9074800c0c0e03c02d142d442000d00d07401a030041c0c5c8900705000c0c0b114528a00c000b082102400c0075044100d50400294490721107200d6008441000b100084850700e00035180200c041d0700c8101107580e00e0f107920f4050b000308803c0d19104402e41c68000081801c1c10100d41e045e00a02580c3c4400c095146410390803503140100810881e08885242203542ea192020819030018103650803002c038480b81002d00700701c112102c80c4040d80f0402d41d25034080202c1884068070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58614490 1250 58613240 58613249
    0x30a030f05042001020f01020a020714040203100b160c060e030607090807060c05010e1015060201140406020d230105030c011b030f02160609052107060e01020a050307060b030610030309 81
    0x20b460703400400c0c00040c5c3c2030446d000d42e40c2240c0d5000050444013140c8c041460401c1d10761480c401c1c44123000398000e01c4105d01048070181c1d25500c50b00b40501140140c0006010010085814a0301c02501e541d107043c00e45106912480111b1030807252440360307140900041e43c0c4003e940c44d06138065071829100380d540c0e904921810f014480b51203200414018290054641e00b407020085658007034101420300000e280505029018180503c2c0c085591803060003001c2c005a20014410310503100c03612894025442902c0c0c00301032680d12815500754403c41042d100c0402d11403206e031702c1a50f24080515083c9039800031340904002c100d04c10324651a58414101340d40e070707815140082c404607020700140c0c90300d03000c000f050542e107058000020759030350300940d4082516420b6a404041c4103200303100311880c04050504100981000c501440329921404501a40c0c680503c1190141d00707a40d01d4032411503100c0c0000b070302c00d980c9a0340b0045160408203e010b81084443d20f201031500d00e03507140204049030b18002c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58615740 1250 58614490 58614533
    0x2070302060906120f2d010605130905040b040b0a111804090f0605010303030b0a08030901030c03021608070209150112050c0f0c0102031008030c0c04230108030a030f0504 75
    0x41c2e502441e11600c05641c5000e90080d000d00c140e003003400700c80800c3e040442e520b0301c200240f582d1030b403c04640036903c2500c64982001c8500c459003055800d4602d40c0000c0200c51145908090000d00c0c508180a503500480c014400c010584c201420702c50b034040002054010341314200a10761004800f010f04890030200e201c0c1c070450041403a013000a018003a940805080c1e2a452080c8205001c0c40344c0c01107040364031a880030003504100c2028006169854810854560014004059254080d0b00303c44820b144c84e140052600206100300018174070114816594240013044043c2107040894201c3e4000161020400345203100c08002007141e1003240e5000005c03a00e031004901415021025600d0610780e071000c45443e80f800641e82e81c000d400403624414002d10601303000410080100440d084480f01ca0003130001c2c0800081880041c00041d251001c0365242e8050700302024840240490281c441d0320080c680e99806040000c007950780035040c4a000c0c0b842e1006000001c0c0c840503040030400744144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58616990 1250 58615740 58615747
    0x207080a02040b12030c060a0e010c0507030f021e010204030303050f15061303060504030e040c0f1d0a03020406090b0a090b030c0f03010e0a21030e0303010e04020a0305010204090b18070207030206 86
    0x85008215650713203d003080d210101c2d14409400c0007113007407072140c0d0240004000a4840407200c41c00d0312007140c4420003080c801c000d10f001003486289a800e003032810f801121000d4450219180440b100c40f41e9115440e58003203000d00401d541805002e03004070601c000d901c91428501ca44800750380d00c000e9202e1042000107056000700340c882c0c9041c8000d41d0001d50800a6103083d050152035040845d80041c030480c9859003540c000b038000c0c2d80640c40c0c280d0f80c0c2d940c0a2901d221701d03054008298100c0e14558400b65030040000141ea560180c10050104601c010440c250503100303011150390b0640003d01c0d41428450300604945001400030700c0803c00b10b50800703403121400007003801048510004100303800303400725140500c01000c0703a1214881d040035080151200c45241201203c1008800b40c1c030a401c10001003103910130881c2c0103a00240001c0135034210654990382c1608aa1080d4008182251907000e401d03550715182402d65031181c50a01c400d800c40c5401c1200a481d42081c0c04020b10518020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58618240 1250 58616990 58617011
    0x16081c030207170a0305040c061707120b060d1505150702060703030b04090c0303260f0402010e191802070210031e09030306081b0307060804050114160306060207080a0204 75
    0x16103e2620061540c2e81d041d0f540e20340110043c09040f0403a0309a5202080c0103000407854407405030241061640d454000c0b1070b0300c0d00307031040315901d016a01204443d5210341c0c0f0800190740d01310040076880c641c0d403c00114401040030140c956030465111510800390080c0ba215050300d0b0b241180c0358076904907002e6a580c03d591a090703009012180b00b02d9001454440d43c1030411100c027030780ea001daa010761105681007503450400001c1100039205604850000780c0030420b590a09141107801500c1418084083e2001038007084070303c00135041910500c08960000c11031a0b501c400041a5030382032810662901019401080c81c00560a80710030805980d0b1001040311008071441d480c07009620007043c0200000341c14000c01905107800b403030810340034814841e44440b000300c40d00d817506103028014003039031450140140c030b90000080c801e40d120754a1303213000d02015106005280c410f00c10210302c400d8900c00000300404403280380d00002c0542d48128410b120203c1d00040721420302c1e0b8115004034881240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58619490 1250 58618240 58618253
    0x905100b0403030201140f010b04050409080d05040b071103041d09010b0a0909060b09060d0f030509030706030c0e01030c0e040f0f0c02250605071202010b03070816081c030207 77
    0xa560280c0509080860040100355040d048010030005a40300400c181c0c6900d03804c46c1404500303106d0190010010002003215060035000f80c124030b030081e101c0e40c0c105664042e845c800e883d82140c2c12110003c451080100043e0005070b91110056210300071800d090170301700000c000b0101c1000c1c1086c9041ca0307100040c62003609400101e03080702c4c00f41101006c0c0b650f84030032002606001d075048421606107142ca408034100103600901c81c07200141b04500f4254141c40707890703042c5a0007209800f0000100000142600c7c20131490004140e580c0e000a000301c05844014050400c8038207460406081c00c18208540d9400354062003881d42c110703400245050b40f00600c0e4000d0070900d1170b241381c8c941442d1102480340c2d004103c80c140c2c03070141000240c81042607a090f04000c919802540081041802404003040c540e201601041005000010321440d04500003890030f20719074802481980007103000b0003201d01030038400c0020013507540102440c01c0130300c0c851400000c040c1c224004040e404074108051040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58620740 1250 58619490 58619521
    0x50402030f0a140c01050c0a020d0201051e04060e06070b06040c020a0501090804090b0d0308070c141509010b01050901090b0906040b030709060201060f030201020a03030e010609020c03030906060f03070905 90
    0x941011a124442c50745012081400c05030300d000c2c243c1c064850003694a5010310101c4480c01c0620303000c0c16101034a51301700040108401c0b0143d04100e01400420030702c40e580b0000e10710511200c102c0130f844529003040284596100c1c4150381c040c08050202c40c0004862500c0f0680010088070080390821203050101e190607240040a402c940c06c210038841031182d010024001e8441ca0f8500f0f0110b40030302820300001503201003000300088e152800103583c007071003680007041092045000b20f40c094444580246060304000494480101110500104982c244281e00319a83c0a0030100c1c1040e80c02e400107003140509101d407507103a120015101c60f49554101c1110094454040783e2900c90400c400010011025405148055840c203903020401d402d0480790403041f05d5050740101000b01307841c0da00b00c0151100ca5141000c1d5921039101044100103800030700030f20b101d01c100454036454048042032806c400909064000c515084a0078481c0d1008211002a1040300d440800c464480000c16090441c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58621990 1250 58620740 58620763
    0xd0b04290f06030d021c0201020d020a170105040e1902040e030a022410051905120a03200303010e040305072111060705090f030307060c08011701020a1205040203 71
    0x8000e03491100c40c0035034840d5114010358a9140c800d0860341da010a1554692a850070000903900c141039812040e0b0880801100c1032815100140c2040c89219440c001d03a08200c040c400402e0b0365070401000565011f0840c0e004000c1100e00f40014200821a20f8a0f02c20030144902c5c03c4a207814007005540721900724851076403240302102c1e503a030500180291500d04540101000c001c4062060580700071600743d1a01a0102d00e02c00c0000d54038000c03c04c8211902c1d200d400c0c0c2042e40b2200300054a56074001200c03000d030b0092000e410218030700e150042c0800d00c01c0e20034011041401500300480c910001c20b40f03041d200300040c86a45600e4a09058940b409a00001810004840080740e4059030840310354071800c5490300d076080b03010808821503403510700c202e03100400103005008118541c0f4100140f810007403400b60546e072030461641c0b175607010b461410400b0800b08070740000400c8900301080025500e000100c0003141440c115038401085075210500c0281c0e52500ca1010030f0540d60140030440000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58623240 1250 58621990 58622033
    0xb060d0c02031b0f0f1501060305041505040b1006030204030f0201050715050a020a080703020306280b18030c0d0308040f11060309010b040605010c0215070302010e0708031c09020d0b04 81
    0x2c800c981e1000d80e613568240b4251829005d05251030030303510301c0043c01164099078219140d01c142c2c24244120003e0900030806d50322910031808811500d5074510410f8003450080106031140d00d0199415010143d00313038015410580304110420100c0c2640c41100c0685609180c42e5a07298a141029038007204204004001e092818081c0082910303640d006080f003c02d00d842d900390710785e00c00c0b030107604a000c03c031041d5400c110404071521100c04142281c0b2454074601c60005443c42e00c6807580400c0c0c0c0c0210f1241145420401c05907507241c50108800071120400b200c03207900011141c0d600038815007029100500050140c03180c002004020b007114116010301030401501d034640040194003800040111a010301e10308500800c80b544030700c2200c40d840c0c3d009020f080c1400304500744a0544e5002d00d005070700715540c80803a2100b40700309021950003030140710002e648901340c400c1001d10301c040718010f106200c0d240c20803482c016140c01d025469840d0304149404456619810070054014812010300f410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58624490 1250 58623240 58623277
    0x9030f180a060305010b0714030f040e011a1c0504030c0f03050d060504020f04030b040f020d030206010305101404020409020111060a020408010506090603060c16021f030f0b060d0c0203 81
    0x90300d9111508540a1104440c1600780503039805007074003150707820b01600009100030804d050105079074114440041e00d404080b2461b0400010403081d041e0401e0704052490348040004200141000d41d8104142001524440c90100e0385560841c1c02d9a2454524001035120740000f01414010012007192a0700803900c81031a03036503491300400540c00308403500c485501e0038030007040c94201b501c280c0f40300c00380d00c2201d10f1600d03003151200110313410028011154180280c0030980181c40e65948011960710940040c90b16504510302181000d072212401142035240071412908a4410a600c542058040d1000a5020114001254034000e040c021907080e1041c40103021441600b94005e00884041200803c419122201081034903801070325269816403000020030035001030440280386414450340d03264159455940800c01540c00d50804541c4240304020614100303815000d1320341c0500d410308041008410000018442c4c0c0207611011a180340c1d42c10382d0300301d15030080080700c81505010103100107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58625740 1250 58624490 58624507
    0x140f28060510170f031e07020301060e010510050310031104390203040302030d0e060c0d1205280e01060b04090b01090609062a0807030305010807061106010e09030f 72
    0xc0944151044100364042c1d210a1940b0f1800464011041080c0001961820004058041d1202c0c51a41984200740b8100b005d00c006a4003441200020940441c07440c03195032401c0104405082e409a00c03130203006c0100b0400524a0640b010300080e660300c0716800d01c00c0642c60f0f0204008080e501c1c1d01601110901d022040e4400d075079103161000c007103a400348034a20984618100d89134003032480000c0d00b44d0300040d034010707545020f0303000d080c0ea0f008007603c3c0f40d0900303000d034400d549440700800c4080c002c29000100d01d909a185806620740c82420b0364281e004a03c2040c0c90315000440c2c3c5000066480c0c3c1c0c0d4941c10450f80d000307410140060440c04071090300d0310340302d04500c0d0052030441c9029001c03a9208900117400d6000300007440884009131100007110848003030000540714210110b03c0ca807045600e110300017551101c0501401030003554000f40d0396041520030780c0707801c00d550011400d00180c010a00030041c000103025040d2a201202c01d502a280c0c40025451806075000c064650400810b90300c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58626990 1250 58625740 58625761
    0x40e1308160b060907030614090c0f0d02030106080114100e030102090312090a06080601020601180b04050c03061e060a110106050d051f02030103020a090c0c0204060801020403140f280605 82
    0x240200f034201d49158540c0c035845010b07070454010384111960b40d588019251180d190122082da407200301c64503101c2c038105148844e01c00640c03280c40b1155409502000610a141d84012090301514061503140d28240c6000005080c421090103144104040403140d03d102d42c40c01e4040d11b0807520007400702c40f61418902d011141035004820107a00031003000400248d600d2080025074040c10040c1c000e8001c0f6400d141303038804160700311000c0a01142e101c0f45010240e440e68030441c1e11135408145c2107902c0b42000410041c40b010070002c00f000800901c10142103581d202c0d4104c50300404141040410704c240314100d2409003603da806580d0203040c02203400c0c1800300208801248410703002400761501000c854480482c0421b000180d0080070320f50041c842c1207070950065210100c6820048005d200c181c0c0080d094076685c0c0c101059994021070f00700100942d000782858042600c03005480a44005940943e4032801141c030811484000d00c04280025041c2032149412500800280264038040300d108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58628240 1250 58626990 58627013
    0x40e040f0c080f0c062d070506010605030601030b09040201141b06160206160903021e040e030d1109060904020304140a0507051c03080403110313030b011a040e130816 73
    0x180058040c01360207070380754074007a01281c0c0f5584110b0000b200341c000040580405404105d031300c00001004218200120303100f00714050003440d0300c0c1d07101c594034542100014160b1303402201450088031100d05110042c0e0300414008003004104012580b184420407114201c1d0000405450003401220180102105281e9881040c480da640864086498090b0540c1400e1502407405c00007581c5827909200500c1c105039541520f04800c5080051200c542c2d0005045468100c08a43c040c2d0002031b80e800c100c1c0e51070081149141d5030340001800c1800c0d0030040381e501d100720014184101c1d030000024042040c1c0d4110545c00700d25410131a0944107242c5491581c1d01d0a03405158858102480300c421901d28a82c9481882503250b5981420f0351500d07581900e41d40d011110340070107400148130300c1c8985040307040381400850003020030100300d515107001c50301038015540c1001680d0700100005e1090594203d43c45812a0f0100c10340c0880c0b2031181800000b0380500240f05180740141e1400b0000d000d1142c2c1171 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58629490 1250 58628240 58628263
    0x14040209150414090108030a080709080114010801150e041e05070f030606050f0d0f030e060d020706060e0c04060804050a0b0a020702090a05130219091d070503070506040e040f0c08 79
    0xf04140c54801c0001c201d03420000b480b4081e510b500070070042200b10f100381c0520350400d0003400e0180c00307541c94045041c01d680001c00e178038280103a4040100322001090143d01d1203142c05801c0100d55500b0000710700d0a8000041c4050440014000b80690300c0c42080c4250000700d4000d01604e8065454007040754080b5030621050325640c0c1001c9007c12039190010205020b0200101286090072103961500d1603805401000d8040c040280104a42602c9031030040c02c06280c554001a0f41c0c0b4064a0410304503003e40d0460340a6a004e0380030051100310b208201c4d0190340c03650501c4007080d960b51920500c2e208001200a00808030442440132420981c2c0150442d03d100700c0e9000a0380d0b545034282d00855a08507001404141d41d070302600f001d070078100701010311001c00403241c50340da40d11400c5e920182e4141c60780300c01c00302c490149104600c07541840706c4009071100314040c1050301c1c0b410b000107c4601a40c041d41921404c8400840c0400040c40c850030081e95100d1501b4018541d1400e081e5129840c2518 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58630740 1250 58629490 58629509
    0x30a05010e1b010503010b040314011103010b0d0608070b0714010f0c05070b07020c0108012c100320090115050702030d0e0102010c0305040503030f1e01031b050301050907140402091504 81
    0x1e04042660061301034a06a62162460a041034034545400e81c00c005a6103210300c45540c0c0e00e841c6c8040b6000000114040c0c0b0300c20b220030341d8500046544504581c0147c0c0600c04603001820180400143c0b035046881d1150000035a00b40c1b5a04c0484150041103c00c80e040000c503c0c3c01940d0840c240c0060141c0260b1b03000741003582150382d42c5542a6182c00070003110500245c6510010310142c2180008949003d00803444086c181581080c2c070700d160507041d00d07a10b00c0c14070f000404004200c85407101e4800d4121034080c5031442030f42040850b4a6001c10700442c100c110303461b811049001e22603001c1d00c0d03509400030229411280b142d440a000444001e912078015402e01c001210000c0c000d01034140200e501000a614594802c0d18480300e0080161820500300d560042642d0001d81201c541406580079011716400441d406240e41c8880d400c540c00a40682d040c14104418440080303598412282160074907003208003a040000d00901c203410005601c2848446034444090f10b800240007910009807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58631990 1250 58630740 58630783
    0x20f01020708010612061a030a1b0b030a05100503120d1d0313080601060309150c031104030b060108150108070e1203071b0807030213020a05040302100509010311041211030a05010e 79
    0x440c41007507c51803082d02c6400d0340c00420a100081c120150790b9510741c10615510b0b20198441c030307502989500584904088507110310134002030f080900c02d8a03004000403801030034001c6000d08a6004d500645201305005a41c4502020040b510312030400301540c2c10405980ea241031070311030000780181c9800358488901c03580300003013203140c024421702c0200d64000b03010710a07500c40c0108240c0a0f0403000f00c40e030101525058450740b65140351340540061442410091b01c2841d003400010916034000703191a0340201d0003a43d101c0aa604064801c3e00310b0414a880081c103142c02c00402ea030101101c4840d030349840000781b494148146140110460622868194801039540c1130540d41d542032400301940c030007150031410b00d144c60907a00400e413100311414094141641d980010310b4994030724410342d000c5000002d0a400a40e40b40c801c64140700c05030940ca80c2458100343c4d030018440040c0700024140240d0443c240d010fa5001c01204040725070100083c0101e5010940c4103884245084c3e0b21113072000e922 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58633096 1106 58631990 58632011
    0x2100207110d03020a1b0e0a0f060510020a03031d120c070302060f0403110901030c0501031e0203010807030b0c040803030f040204020c010f021308030313020f0102070801061206 78
    0x35005090400e200c0e007049000c4603001e05404203100596074040c0000c44030240c0d056080022388000086e800b0000032200f00614041c1c0025500c44c40081036000c0c181d0740059170000b518070a039400e000322140b8250041c80003800d114000690b8018a516542000400c40500001503107442141c0003140c2c1da8000c0b4840b40d20141151070340785030025050050049142010b094850140c07410040c3e91b1654440d000340392814010755041580355600d1610800b400501c2c86070080d0305082c02c660300e50f5100e083c181d8442040c80308a90041140c00051759401a0b4415202266984005145542c0e1404441221041d0060080383e020780d0a100c0d0811a4009108110303d82d4849240181c3c0d6040c4032065064115240c0e0120001e03920820400a80061503078880742141c0d41a00c0d4140d1400041c401070741803d109411000c125031a001e0000b030300c0f400404181071501e004040400040004 = true := by decide +kernel

theorem cover : BRFrame.Cov 58453240 58633096 := by
  have h0 := BRFrame.cov_init 58453240
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58453240 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58453240 ≤ n) (h2 : n < 58633096) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
