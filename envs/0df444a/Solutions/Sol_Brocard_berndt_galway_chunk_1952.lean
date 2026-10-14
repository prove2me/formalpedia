-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1952
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:16:34.774024+00:00
-- url     : https://prove2.me/submissions/a8517268-47a5-4686-95a6-69b4d4b4bfdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350899280 ≤ n < 351079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350900530 1250 350899280 350899309
    0x2030303130c0e0c03060402070f05011a0315010b0f131203030902100503040b04021003140f0a051f05130207081803010e0307111c0210090e070306060c031d060f09 72
    0x143c42d4540f9205408030490b02c0b004004034413441e8001814000c00080d00c50425516810000070050303504a44170300d5403030005003804d04c0d11034418030301e14170b6003c45407124040c162024407412604140d240340304003119400204400780402801d20000c5030301b554810f40215214025540400d2561041c01481006220049040c081110800801c40428080c00d821500640d0545100701e210b50b03130010480081460110380e0a040200005000030348502010f414054400003800700110b0b120325034038001101a0145050811038450740800c4607242800380100c811030651809480c10085070b5a1056545c0400b80c034104480c0340000301c45981c1000d01c01d07910322480e054029071030803c1d561200310f003006207100303110300c150084808410f4000c0300400d08452280d001e01051010120060054000d100d18010000c0f00c048140000b4411842401904115803003902c501040da030740f40d1006c9034140000340d20642c50036140810041030f500c40c44020100c50719101d8415841c0d003582c2040000000c3c10380003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350901780 1250 350900530 350900549
    0x21f02040303020d1103040f080606090a090203060f04060213080a1406010b1c061703030103030f0906090e06040902101106060609181503100b10032a0203040302030303130c 76
    0x80c00001e800080b08445004d480c02e04c41d43e000b03010000310b403540c40f440d08041d407204c52200f000280c078400010014042d03001201d40c6c0c129983d808051504407482c440002e941540891b0200e03101c6044000d10a401030f0151001500d46503149903d01d40c01d8050b5070000751541e0008a10700140504965109059401c090181030903516140203011540125241001d000c6192501c1c0d0786002c005a10002c02041d1444807140c85c03140104a1981301d070005d10055010892001c24452014070403000305d4103982ea40c4d2214881903040c1480b0300b0740d41c100100001c5d040f039510b013603407400b50341e901c081917441214507030f00c0000d000c14000c045420541c0140000f409880d05101603a01503565800f0070100b1070b16032001c0f11580c3d90b034000d0b60004100701c041e0300f0707090301600503080022083c030340082e1074014095a40c1d0550021011701202150051017008200714500c02d800c040c007010307200c0030403000c401d0740c03040741d04294a0b5000a170455009503002c0856003607220100041103010740c00203004141404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350903030 1250 350901780 350901787
    0xc2d0d08090d031505092502010902010c0303230a0606020f07030c05060702060d0608012036060c070f060c050a020105160b09010e0c06092b05030a021f02 68
    0x6072600e6844440c0c0040c182419224a000d050621000b1400d00c0188001803003e4081c2c01c1c44184c42c00001e003031141d007410754000142c0014a41d030050290b0341a0907810ba66001c8600c03040d403806c40080c102c203148503140080d881170508410780300c202442d02480c100000050403e103000f0001c3d1906c82c05078030106a903006000e00304081004c0b9810707981203030019510141d45401e40d100217489441440c000754092442d2030004549464154405100055030b0300d203480c54040141c5c0d1400c0c0c28041c80030b042c60900c01150741c804005e0030b010100d2003241c1105454290701d0390702c2d0001501c107801c8030091440ea51300117034040080b0401d9034130000c02400ca60501c8441c0c2c0b811910f4142d12140152030103410300400140c608001401d900300503100c2a003280280c00142080c03007a00b8041c05140354035060520581c0b0b8107038060301d005c50884021540c0100003490f10380080c2160304142803010491502c40045103001000301c1d00600043c6402081a8080c103441c1c0d0a40b00001068044050008012403050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350904280 1250 350903030 350903041
    0x20c01090506030c2b09020901063e1203090d050a1709120f0306040606051312080903010615080112030504090e0709020a0e13021204080c2d0d08 64
    0x1141103a81241c1da07400882da484e113441d00702c2c0301c103c0f0201034104111000c0c201a117401310310592021002610032624a176103a640d9060840303041c030031140000403411510040b0808040300c201c0d107043c0f104d0350000c902d05c840f90703c0082e82c0c2041022800c4000402c0c0005c01c2007020681130240c0500c144250800c1800c0041c40340004101035004c2040184103480400803400c1d4848c2048a13220b403040840b503180d0f441700d0003a0700c06016081a0b9a590080d4102400401da00d4001c6095603c03000d680003114614914041824901296091081e0384042c0b0400904ca1035442c02e0080d040505424610000c0e901048080142400340580c0144000c48500590320000707503026040f02d040b601540070100c0d6000b14110000d0030001c1d1548440005403000800380c1d50150042a0b803c200b1350101c400b00c0c11aa40e002d2140183d11030300b0040c040b00c04c450000100003c01420180403200d150800321008038002182910408455400780115030700107a9000412440812002038882ca49181101450a14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350905530 1250 350904280 350904289
    0x51b040608072d0338091c0302070c140108090303160807050d15090b01110307031b0804061205070c23150f070e1504030b06120f0d020c010905 63
    0x82400c8200d8580103001d61803c2c07543c103101c0c100186412102201c0312000082e44003c044060000d002c1c42003011041c0c01e4a090240072a0510582003580600b20341600e242002004010300003450060580c00c2c0000e401143c0d00c0b91680e000303400300b610f02082c96806000054840b0200500740030142c2e1040003001000318031040061682025030904154507290f10344142c4081c01154244110640340050184c144002090342e50116400c2c1d800412004039118011601140c3e203149800a0341c6c01001014006407048040b001c0705104e030216510052403a5542c0701c0107500c40c1d4484000a5240400320202078124483c003a0440342c241044094200295a0201680d2075210b00314001252018034006804041c41005a688402c940071981e03480c1001c0786a2a61a051311418005032107044420114103100320348405050b001206241050b2440e0384107824074400400d6030350012610020b00d11340c29400c105d040c91041c00350014200c0c810500d10001d00d080e40c045801810042126020402d13500ea = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350906780 1250 350905530 350905559
    0x7050312070f0b04020a08101a010905180c040f140306060a1d09030d0612050c040519091e08070b06040b0d03110f060403050316050f0307050a0309051b04060807 71
    0x5002900d00072a0384d403800014410801075100b102c1380c1c055202d0740c0c412240e2551214440703152240240c08450904c1004482c02404ca0094a0300044074603811042c0003d0803480d141d0000c3c104a40d2032506803106901c05001e06aa481044003030070440c480501807805203d0f440c0d201070203503032454000c0d19041880c54840f400045d42011090300802240d65040e00f401184c0c840280d1403420b00441e071740c401d003810a80400724425074442c00340e0518041c482c5440d00449000d41001c031408508803d5644080005007a2003a00301c41c01c0c0c100c08186440703c42540500d041c00703405601144c0d00c03643d044c2013020200000a055078400d9103408000c800300d9440d1031003100f9694251401580007184200203a14211b51244908503030710aa001300070405510000a40c0b1944980c3c40344443c00303656607425101406180ea00111041d800e20004407030f41d114601030240d11844e8503000c100e080082d1551400c19401403003c080306002520b00c100107080c980140d00051851600420016280c03c0740c8940482 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350908030 1250 350906780 350906783
    0x506180603100e0c07060e010e0304030b0705040f06080601020625050901050f040909120801080a032f0f0f1f091a0106080406060905070909020d021b07050312070f 72
    0x400800e40119441e94180e0151542c0616600309080980070102d81d07410045c411280c95080c901d2030f074205030040c058854194900d4004604142c107595803642041b10040215080100900000a03110a01c07810200140450b440f880443d090800009060400c02407901c41d0300e1442c000075042c2074400c45007445103c04980750041d21201c946004803594440d1040d00c40700c1120100700441c0e40700b20f079884403000f2881500702c08001c00202005a540b10024810707400030b07810800500703010900510b03a50040401c0d40118000d0700440d160b03144440303c02d00c1d6440800c0e034032503116000061700411005240049400041c40c41d0305140000c0f1400c010003200e107091840d11342c523001082000c0154603003144d1030302102c070880560b1546402046010100d400703031022400d060300011900c06500c81c4c01d0181c0829a1384160351406d018961010750700295044424079400c00c13030800304929080e618168405400050720040c2c1c50441010301d8450484038640422400b0880e80001902d50b400103103869 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350909280 1250 350908030 350908039
    0x1103071d010c030e010216080c0913050303040b04020d140601051c11060a020c060301120614060303070b06010207080708030706050c090901090f1b0305160201021603030b03012d06050618 82
    0x13451204c0101d04126a900a02c0111b138a24000482c4142000c10107a0003440d007940c682c01142d40307001c0c13003529200760800054015002000483d01103080c408d039440c0d206002804102141d80e42d40d465101d03800c0d522a1080c0c0130b40200b8018000c1d032a0140b1070030f80c1e40f25800c0f03409100c0c5044e911901c001481401c5c0b000e00c02e440000b0005042802485056203840300201701c181c0301d69440904580f4002d6202d402c483c00d40c0703465202101d4455245015000b40c1002d0011414100d40340c0d203014000d1006031006042d81b1501c40e0018402900304108800381090381c01035078580125241c900c003030302d5028110305010441801402d0b11512420032042c1112544400030440a07840002c160080940d40180c0c52221528460b2546158045e045540105207001e174903203038410700c244202d080307010344120500e20200700c41c000804648260043e146100d0004d0000440d40c40740544c0303084110740d04618445800c05020394072102d40d0f551091100410003030b1601c40c5131140051950f4140d40707141d40002d126 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350910530 1250 350909280 350909297
    0xb06090f0d02030d0206070e0607080d090311070f1706060325030605010f031e0209070e031504030216060e010206010501050315151c06030f060b131103071d010c03 72
    0x4a95800c80e1a5a031550041c0961380b040d40e01d020001c0d1242c00841e000000329a808800c445241031440844540e550091101c3d0b091a10b410316403005400180016420000c82c68a8492800c105000d04002411444185800c99161403510441c84800c0808a090754110340e08200d65604d000c9659076038107500c003240e04003410702e40700302d43c036044066000900414a41070000c600d4085020040090328000d40b0f6000b008580c0076040c034400080f40300c00941000c49000401c000038015141e5031407100f002030a40d16108002007004039580c00c110740c158010392198240c4080d081d043c80e0718002902c042c2ca0203460020703600c00003035078560043c4143c40c10401c00000040d680018031512402810006202c6010b00c1015403d98055402c42a41400e0340200c103072191118404500c01d400440f039105100b1a00301256445202c020f0651011181c0c009540c860000380403002e601c101001d01600c4101241c40b42400d400041480d000d11004000600c01d0300b00355a0240c4c4c010881c3c80e01c85078503245c590b03407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350911780 1250 350910530 350910559
    0x605090609061c1a011e0b0c03090306040807112b2d03021e06060d020406050a09050a050c071e170409050a1a010c0602180607081305040b0609 63
    0x345403c1d591108030103d0700340c0301c44604204003840d00c42914203100d00134220503601c1e42450007400e0740741204202120f0030340004008881160b409050102d0006098a08044003031022030f080002c101e50440d074200c000910701003040030321b0321204091042074524034018a1f0480f00d40b290301c0e90300ba0450b401800050311010800100218040420501d001c0d04e110706501001c190340442c030001e0045000d4000d001c00b1900300c034280b8a107a410b44503248020f00903519043c045c0300c1010252441640c00584500340452961200c41f0100c0c001c0c4152440041e042c50217107048011190040c100700e4803c0401c000304804100c008407090304030981101c01e100c1d01451454108406020117600c6155a031001c503001401c001694041c9200b050545000e026030041c0c030f0650300c00e10140300001c0e400700d0f090704004d60208101d60301400c441c8001881c101451401700b4001043c0340c00241e82140c0c404400503600b4074860300250321030000e0100792010701100d40840d00140d228090f0008013402058001800740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350913030 1250 350911780 350911789
    0x41404110403140607050c070e0a0e010212150d0807022701090903030e0601050907120f020403122606060c15100509070906140a26090709060509060906 67
    0x20800d480344030100303954594918060080c00c240201c0364003d809440d0008003000e004804450101151002600b480f90030300218183e52030024000c83c0c0c4983c1e403a41c400d00b140d04244014040101d016194060905c0c000e00d80c500f4800800704003a0003002071254800014044900381c44c4400c3e41150f40b45120703403561001000d01114490101947c1045000000340e4005c01d60080d0005400303a40c05201d402041d034141c80c2d48800078464640c100000500050015201c0d50f0030186000389078001041002c216003140382a038005400c2620010320019040d400386030070260740550a0561126000002d801c68844d0104490050203540600d40000340f082055005010001025408500309040307410218074842d5421000d008031805143e0762808100350900030600b06044a01560300e04001202c2c205100300c550f0041081e43e0140001003824030b210307454102d000400b540d844403000803689050148507203000c1e103e5001101c0b0920b0818180710030344407c1c0b4180c0d0301c004162200e2030785803903503000b24 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350914280 1250 350913030 350913041
    0x303020a05240609040318060f090503060105100507050f0a080405040507110c150903010609090b07020703050309060d1b1e1103040b0c0a2901050405090d0807050d0e01020d051b041404 81
    0x2207c1c006075001d000c5001074001c85086c50800f042c2c2c2e1150005510744040c180d40d2070003030081c0396001410b4205401c5a9208030001c0404611803800d4039448500201050700c1c1c11106201112075080220707050041e81010700c101c690100071880c1c1062052030244030203071519072401100d401840010640f61150008404403404910098020041265209244401000344210840310002e20601003600700d8400603800050f260082d010314a030001000c204011948a00c10b081585529140036501d0f80a005521010307489990322000010000f159101000c1350036900c0c400244034921441544400001050b5003c0c0e521611700301e03a0751014112442d140c541c2109004010f80d101060104403805414990442401e44040d00ca010743d89400811054500c112030080e0103500c881074880a05100706829a0003081d0313030400c1890202e21000c0d07a0b0546040329801007103a03400080c2200c0b958028418198041400c2c0c1101800c2c80b4003100d03000d01480380d8030600c006c2484010b022182d5940780d6110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350915530 1250 350914280 350914307
    0x31d030708030a1e0807081f0e0a02030a0b030111090d080d050103050703050606010305060d15091e02011704050a121107180b04271401060303020a052406090403 71
    0x100e0b0380711600c60300010b01e0942e40000041000c44c807900813448442c000d0341310601500c0320f912030782055607401741d44452180c80c88a41c030b034207003142620015502c1003001d42d841c0908600340015a036031401380e400c4425a540012424042c0c0c0c5004641a0400340c50750590315249000c840c0d0003c01d04060400d04034030302403412a00d58680c903101c000000c0060010303120040764440d1003583e02c1ba030b903890015011a0b608480c0300f500058000065000900d1038809113802e6004100c0c0041c2c1604e1613190f131103404506601000344880d03171400340c8046d580c00140106484403102c0d84600c0514050303803203d80744d40f08204010500c010100300303511424000e19003041c80101b03000869000c542c0d40c04d5140c085c24500c4a030f10000518000842e0083d042501800a1000750710f5503c4212041114800c0c1c10038040150035201b800380000720814501d000c2c0a050000c1d8003035401028403c0c0d490400605040280c40c80320a0300041a4061107441c884452541d4031140031200100725070b4440c10306a51080c000b140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350916780 1250 350915530 350915533
    0x504110904170d0621120504060203030105130e0703230f030a18030b040803070f020309010e100c06090605060f061810050409020a0801060e0a18020a1b1a0a09031d030708 75
    0xa40b0740c2040700c010801305d2082c012414415444151070050721240326502030000180c1040006009030300700301e04011540881000000751180c51a0410740c01d140641d001118210480f410b040040984006140303e02c5035824003030290a801e20071091f03a0303840340c0c0040d80c0c140500304d1a5001440040946100110f8000f0010f80c694901751a00364220381c400c850180c00b00e1101d04449805902c00015102c0c0400d060710b074050032314004000c10001420f151910b2040000b20320510340050b849000e1000514411100803425040850400c000046e0450056000c3d000520030003524607a059420305401c0010b460002040070b030701c5d40c21900c40c41290003007034040c1d00004241d11102d60100165040f0b80c81d5641c0d414030f030300c083c0e410402e043c503c0d44114a11404034404252900c2e4555000780f0510840d07003086022a070002078841280180304c80241d6011f802c0c401d51024804000e00610f600080f2480b041000c0718003586e000e000c807042c04c0001d800744d0182c83c0035a00651010048040500312040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350918030 1250 350916780 350916809
    0x507050a08010902091302131109030f16090203100e070905060a050c07050105040815060a0906060801083702030a0204020414012c01140712030504110904170d06 71
    0x108070a0280c801030f441240104443c90000740700c44403116684100680c01001050f40380d10340318540d03016200300800c00904010230040c030030442d07400700300f440c03550305a900c0903001800c900150900e94003d01e0384160092070042007007001c044000880310060f0340c4002c80380b007043d490b490000c40e000c0c0e0158010300e41003500000c00c01c0fa240e0300b01014000a500000c12a184281c5078801155280101e204d1f0381d5142d40502180190840c6e40155140d000700080c140010040d6651505000d582040c1d2100020903c0600107102e0703e4401d001d081c0b03e0304581d81d40c000c2180501c0d004500300102c1010f04028480c03032041000b0456030180030a044d4587c00034070035511107440c0c281d0b941d88445181162804a1000700d542c2c02030041d803524a000000710380342c1c0c0d8000350180d24019915a5180000d4003203d0358100880400103024251070200c11005550010b050700c0c0a140100c40c40c400013131028840c000450411000510824003407004003820394101c1c0d2110440541c51000e4240c54001000c00903681 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350919280 1250 350918030 350918039
    0x909041b08010603150b032109180115140a17060d0605090138010e01181d15100509040b09090114220b07170a09030e0616020d0507050a 60
    0x51700540b000008000800c020310040c41010343d075051030038030901c101800c0c02524194905960141504010141c09228954070020100801c40000d811080b108055007004024103540b011000d40945200c884003407800060135000342c4004001c9194072107412490f000904e03142c0300d100e840300c0c000354403640c00d0005080046410740030b859425041141e0380e01209100030309415042c0301080350160f0010420800a0610045072081c0145a40710b061048000c1307242c080220814a0800a00d140c840100ca440b0305071800c040c41c2d00c0c0150002c01105450702019441e5901e8118100d6601d1950812503030312100c0d0b60105014000301070b01d02d07500c25043c104014103410103401210301400181c003001526514071041200801c2c01d0241040354408400c9004001540c1100d52600402d043c00c01c100c010039941c002601502045880e10321458507001050100f5800c1f06400805510440359181446960303a0425036101103c000a8812800361b03854a040c481e00f40031003009014041e011550b400d454 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350920530 1250 350919280 350919293
    0x20a0503040e310b070f0804020f041b090504110c2508010f02040905010603090b1603090b070215070206070215040f02033301050a0b030403020c0406060f0201110909041b08010603 79
    0x80c2c4505075100c08079280005c1744103200f00c44d0102c01d030101da20390340001d0712181c0a1040e1100300360a4a9001540e1b071841c0c8030061a4242c000c91054201d5940c1510103080c2018081581ca00c2880e40c00d0f198001c0c00105407002c00466039058070012450001c03c00c58000c900c400301601da61b404000d465280114210404540341c0050090b100c501d00c0c140402d076a1003004600f100e54405020300b071034103c01c001c605540711182d645507003211a8a404100c0f00300680b1400c012040c1a5241d00140c0d20a4000302041c1c2c00365003282c0d511420900241c0b00924200340c1c040e40b01d00514800300007100c0650b00080c03c20042e034118507000c94025040305e4481d2060540308907012220071190b000c4816000ba14010320691035074480c16502d000d03244900030340c9005102106508090021010350249404c004201d03161882040d0080610356604d414037401c07100041e0171038404081c0d00c00f80e0102005200c1d981d40701c9809030390f0400d621041c00100b82d0f000c0403503030715001c0c0660066603081d400c0a60020034000c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350921780 1250 350920530 350920621
    0x109081614070b1905091c050c010c021011120c03030f160516063e0301140105070812190e060402030a0b15040501090c02060601020a0503040e 63
    0x414100e07a108240c0604006945011500c61114441c0703041142450440c03080b5103244140c0e00c10f0601c181401070f40c0c00054203a025107075132003480f54480c801c4001800000c00050900c04d40a090085106003030f0b401141000030b05146420a0006d0a8200f002c8400308008030405109003d56194a0703480f0140059117030b40c0300b690b888000454203008110500d212142c4d54034214a9500c03924a08407074078038100d080d507402600c00d54501e6610340414800720781e001030042100c0950300d401014019246090108080b01b82c0d0641c2e5200401c0c0010710402e4400980c1d000d00c2c0301c09003899610348525290a00b03146c4240809101c0580c003040c2800009017810800401c4512030310824000007000010055482d42c00f10380103507150380640b1045012400525449801c02c180ca01c1d0018407072501d1000c20246c820a0b032080c40915500d61200c40f01079414041c807604103c00f4409005121055202c00343d9034011401901c5100400354046000c074449140c1411071741d03c2c41958a03032240c11040c252a40c240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350923030 1250 350921780 350921783
    0x6180105091504112205010612060308090f040e070e161d040b01030b100503040b0c030f0403050901031404031106010609150e3039010201090816 64
    0x40c2030401003400164045001c111160018400401540d502d4070707468143c01d119000c56803c0b03240340c0c10b05841d00c203491154101440d401c0c440400d0651601d90001c2039011542c4803640154a010b1051000804601c01c403078402800b10351140d00c0c01c055500150080410000c004044e2080d14070000c0c240044100744c51254000e00c2d184111055245010b0f0790070031003280b413034120b0701a03444001c0f0b051819034402c494524040c500080c82500c0712000c180110051103108010800c003000304010003191040340d5901000100c1440e0550a1003169041c10540c040c00040900c00e001c40d1428941c0d02c039900807550b0310b034dc80008143c242400d00b0084c155440d4339034485000d002e1100049035141c0201c4a900886800d1a0244104207184000b2908013089050b0503500498181c141849901501c400510a000e10341d0f01118540e00d2402c054580020030010652601e19020102a012030340e2202e040750058a0307981518405a410040b0300605e02408000d100d2440032404000c0032080c6903580c1c0d441c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350924280 1250 350923030 350923033
    0x102120f090f01020f0909270102090901090b09131e0804090c080f0c0f0d0f0209030d091406030604140106030507020d09120813080a0302010f141009020a050c0618 72
    0x14003601030b0031401d0b441421412080744801b000b11501c18144050f843d544404142e0100281011074100c031090440d07100888212a034001c0b1718071040b4035065131024010513403041c1c00c000402c00800890244a4020010001d82040840c15400e12000387c902e0140341c3c4032202191a002d08928102100360071501410302080e203008a0341404500603008140101c007510313500c007000c0d603c528203d20f0a031b0000c11011030303641d4180002c41900c2c030640036241600c5005d510150300ca02014007494506400d251030360080240b04d8004104258601d01c42e1928081c080c2d4100d42d50340d98800c0403801822100503848a20001d10000040311356040d40721078011200365095039808400c0107002c81d0024418091040c900d0f0301220410b0004100c03400500511203c0c500910005030746061076420035500100035800741c1d448040d075400c5110244036030070401d2204005240a81001001c50b41e54404501074810001e900103410040580583e0603584046414400c40d05a40340c0074100130040000d038608101d59 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350925530 1250 350924280 350924293
    0x91d1c09050409020306010306021606061706060a06050d050403090e070e2106010506180d0c03051501150e0a0504022a0d020303040f020a050a0602011a060c03070609050102120f09 79
    0x1882d040c00782c5800980c000300148030366401c60f140d21001b5442441d103c2d480ba0403000d072840006e840e5029070002482200f42c1c9c07400c0c0031024810300d0305000008006d03910800c0320310800e01516822205907407a4840d00100002d095a8614069a510311580c222440c18541c00040241099009007984003d110945590341f66406c4540402c02c028154048007880d500030000500c8a03090040107802d042115604034a240c041d00300c08203510401528007900c5001c4181c030203000384181002582085241d0200d040710303d614120714400b044130942e50744420065881c1018103156210141d51003d07200062003103541d4004040025410b41000040700b0440b0b80020726040c0310500458980c11036295500914a036540f1960b802004040303407401207034064044580464a80c4410440a0161026400020b640041183c02500150030401424480c4004002622503041d0200c1590f04d429404400800d070030080d807800d0b50180c01103050b140d15003002c0c10104503414140303c030864000d00380407082e1800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350926780 1250 350925530 350925539
    0xa020d050c030d0504060b04020c0318011d190e1911070b01030f080426061b04060c05010b060f040e011d010510020f1f0b0102070e01091d1c09 63
    0x29240622101241c481d0800c1c800141c410085401190744548550000130705141154006802c98002c1031203681168000720ba0b100040418528080d05e0715424201240441c8240c9464030520710401c801c103015210303103036030f0f0200079030709241010203080008241a41d610f0400c1c0550712000070b000312002075038240003010102150307800c1121a45608282041c203e030b801d42d00c1d01107104002c1c200848424400b00000181c9244c0401e04145d038a0500b209240000c49102c64185004405800106080d8500c1c2000e181c410455044034205c54450a1086140c1c20508201d4010184003c509410100008100656000d6000204203950701a5150145a600c0e1200b0403807141340c59030f801000120902c014411403400403203032502d040c4e4610480c3d2405074040a030500348107801c0d4031001d0450340e5542040c6515003d000d44032000d103081c8000e003181864032240c0301d1a0481881003c4c0303080d039101c4021656140a4040006451a070012a12405245000b22900f1101c2209150008401020105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350928030 1250 350926780 350926787
    0x170d0e030f3019030b0a0306051e0a0b0108060405060102031b060105180702060705130801090c150302120f10050d0b0108160302011d011206030807140109032c0a03080a020d 76
    0xc038011100c6080c1c1400d02c1c43c44005500074900f01e18444c0e800007402600000142e018080c049c410212800e62408200c040c0300c0c8080c0c0c196014089640700c0f81005400401c1d1390344140d2082d4000c40440340450580c44102c0140e08510410707508001003082034408240c504000603036a4104c6000361201c50f0300401d071854401d2410b6040c0c8042005804c8680400d480d80d2040e0068841c000d0b00214a141c6a0380c0c5a1501d421281c501e0021524140d042004012501c81c007689016416120f003019442c1050070605a281b03010001c14030303000d080c450400b14820042d11000071002e0040945141491074481c10310000e0311100348941d81d0b080c4a42c540c105030168404c0c01c0242100d9041c1c59800c01c0b4140102a0500c07001400c0a040c1005030600c80c0c01c1d003800c00c0c0e0241900460080401c10380e601003508142d43d04a10800160410740c1c18040c0003000660310020051547d5030f10742d0000c8004540e20180000c200180d07403040c0c2c1c40590f6000c0803060002981c0203140d000b08a4080b1041e05913901e1064 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350929280 1250 350928030 350928037
    0x60405064b030a140a050402030c1f0c0501020c2401080d09030b1905011401030b030a0b1803070f06060603051605041712041509170d0e030f30 63
    0x4504120714904a80240740c0810140d504640c91503400301d10110310f030b021442581022111320203900e44032028002541001d02aa4040740025224611032850079940d02520b1000640441c08020070f02501c28188502075040e220f4559124080c1e4490140d041600110780040b030811181c2e0081800000030480ba0000f0119140d0296803101040203240d501c80820007a030082055501985446802010300c3c120710841c3e028203078071340c0c9600300001070000043c00c482c00c010740329010703510002030400441e01c0501b5182d4003c290615003900d441c00c0758601c0d4154094020018800c00c02c001040007000000c0e0007090940d50540c0c1c007080195140e000b0070708207100950045002c43d01c00c010920090039103043c0a1080c86200086038402c69190540c01900d5100e44c0c0079a00511503a001d40d81038541c0800d203440107111740d003120190084501000c90311480c00045020601ca02025103c003151404c0c491001d102c078540050b0b903000711510b001400c1e901080d400c104c952040c2d50700d07162400c04404095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350930530 1250 350929280 350929387
    0x50c0909091f020a050702030601080624060d02070512040b09090a0c0804150915060303090b040803090f0f041803080a1103040609030212030903040806010b090906090606040506 78
    0x1003401c00302d10b281090025484106502c0030400100103180250703d0402015000b01700c900e00401242c43e245000101c0d09030b1008000c40142c440d00900200307641d4002c182c1303e040490040050741d42d5074034544a0315000d090ba10307074030712100c0205002401d441064007508510005566170101035440c600544d04460f15100b074800403403900d030089404224082091404400da1181c0002c50340c41c01e4944c0c6102199901d41c0300961901c0d440c0078030406038070411030002000c0c000003441c201424042c480c0d84034000c0c940050f001c2c1c442d0080c605500d684400c1031640814010f0b00400c000c8075001c0350a911100c0d002030a03400310b2003e60200301440102c0c0700b49905252072101c0d0b142940c8a540d80c40000d000042e1081c1c045100b100c10300d1047c01c072880000d6001d41c4040340190f0b500c0b850800c1d12420850140e101c180542e0003800340201c1511021303680f6600c020101d50f45460b5035581c2d0300065450249400558103c48007155001d40381c010360007407205c061302c02c004a8000300c3c0c002a44400c54400d0383c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350931780 1250 350930530 350930563
    0x10b0a06081503031b0c040b0a030b19020d06030f030e0a0f0b1b0607050c060f0402010801090c0207090e07140405040206040605030c07082a0706140c070306050c090909 74
    0x18610621503500d4042c44540101900d01c0e0041c0082a081c58484400481215401c289800000c0f89010300c20200301200555212081500d9501d40780340e001c800420306c683d5003020441c194a407194030f90444c1c07124484050104a01c94032410643c07400955000210046840140450090310380b480c0741c0011186004640b070911410110301074210380001400200490004041c140305102c284403585c40340c00251756040d107545040300340a1410b10090034690304214880305000240c4d038820512410740da03190b42c022480701803901080b85403140e1a07005c07907080c07450050328959000000c11034a00700c0b074076070503480f903d410700b02e08100c2101c00c2030710001c0d4054070401c02000818004c8001e141d0042c03104908a043c000613480f102d003941d0080c103002c0c4031201c0f604000300c80c40c44039102001035504140000c0c802181002030103054506407549100f082e0b00b01117550154060302f081044040c642c000428007070760400c0d60040c0e070315400039101c06200304040c40c0002e02ca003000148001c007074070081c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350933030 1250 350931780 350931797
    0x1d1005010e010203040b03010303170f0108120a0c020a0303020714040e03040302040b0d17120108032d0408070e10060513062003030f0601270e0619080f010b0a06 71
    0x41d80c8007920500c51038103602040c0070004440400a01840c021406921004102d425a00303510100000050800da1003419030300040c41605400600a000c9142024503141c4e5034101c00c2d003e40d1042d56000b0002e50009108002004169000c103030341c8111858000760b00d07440c130506030800c8203840c402030b24018558070a000c04c102514054000410044014100b8180020a600d68450402068141e40107940c0005803002d480d01030b28071803600404001c0095402c001030071130800d02c2002444400c01d40003100906c1b00301d03403440b00b41c1181c0052613a4411680320503510400b6032042d00c3e00705d516005003504000000340e83c0b40200100c4454607104030342405400c0c100300094443d0a16a0301c00c0020032500d9101c001000c008000540c01015422011030040c03800500040c0104454240c002a81c0003800101d02c0322284101904155802540e03a906031381d4034000421180340040c121200c04984c05500001c1e080c10110340c0e554100c0307014000b070114902d00014028107054510031800010540c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350934280 1250 350933030 350933039
    0x32001030e0d2106170a020a0b03010302010507060515030a140d02030a170c0f07030203030604060f050607140a0b01030b0f01060c08041e05030102030108010c1205040201210b040908041d10 83
    0x80d070324400307061000c0000648a9110101d0741c5179115440300396400c9601c121094025441c041e6101002444400031480c503642c19a03000902c503000301c0b80024902c0340c9480102c1c14071075445480c10b01515018040741d02601c000e00345007111aa1400c3d904009001d42d9100c002144d2010007210350959140c0c890b86508101da000900074a0401412148880030074007228400d401460020f01c4924003950046d43c0340c0c02d09408220071203140f0303070005000925a000401c100e403140800d0b1901550403d6090312130f95000061703281000c03040d91000b801c10300340383d001008204110003504d000d80702080c0b10a03207a80c1c03030382026a00005595030180030302406000410503401ca03114404211881100041e40c469a030300040b03030990b003003078001242c1030751252400030085034008009802e18403030401c00d00c42410320380c001030035010001d01c11001800041d0302103020011107401100b0b4101c0c0103042000742c9196401e0102d1581c01c1405200200c00f40c0d00303000059415001010360041d42008448801ea503c2c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350935530 1250 350934280 350934317
    0x11b05130e012d0302060d0912030c2c040504080a1e0e15120f01060f031401030305130308030423010c09170f030417210a0c0c032001030e0d 62
    0x11040e0000c0c0e10f0003005000700060301d42c1c1c006800c500c4507544001c0f440c040d4a01d03014102039010080001010b190046074038405500455400c00c620744043c04040403c490013185840121500156400906020920040042100040c01120441c0d81c901c0c2e043e90490349040c042c3d030703001813000000404001a001d82c6281c080031203039503100100a01c038034120402c0e80850350300d201124000700c0c211003140100310803508203d91450005503440c0c01c0040414440300709802c010103000107400c0080120b903005400c035032030350402c0245400c280082c2c0c5a150502e0240428040034260081106e100c501d40c401c0391005010b101d02c0d12686071621844603080105070f50126001e078041c0d04052040c1c00715039401c01020300c0200040c0104032010103c02e00a40c0700765150003458074858890112092580c681c1c004000300f1380d030401040f46409090801941403003032138103c071074001501c4011101116004000130031a9440c40510a80f024032115010360200ca40300c0100301c44c0305000c81d05a078200030b11941c0c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350936780 1250 350935530 350935589
    0x15050a0c02090c250203010c14040e22050703060b06030f07080406150e06100512070c05070b03130605150607020105090604150c0308010b16020d0302011b05130e01 72
    0x1040f00d40a040400072070980d28207104c4001c4010813070440c1c00b044400d5040a0041c654180c1e414100a40e024600c0342652006110b070384521348003510203d01203011039001172000c80290039200070002c0540f1a80c100306460783d0482c4421103000380b80080d001d0080c1002000da074403520f50a200381c64680d0f100f50040d1000300c0700520450701c0954a182c07103114000c0c0d944540002e01541007025255290040c14040b415001121035400d01c241440101011a00d001145501204601d00000700156038508540340150703640060303409410100c2004076806221702001405400746200740a19154400b0703d400c5c0d14060000d03140c000008000e454059401278008002600002d40281c0c81c050340d0381072442d002c008a0344070500040202c1c0b642c80038158002e280b0740c09092244049454661181000e00e0f584202e0b100080c062980051341d6400c3c14001c0d801012801403001d001114080c1c68603004100e03511542d0361000b02440c010011549040490707403141070f5507841409044801d180501000c10b846c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350938030 1250 350936780 350936791
    0x130f050a0605030603010f230a0b1c030c020306041109060f0630010905090f2d15010b0a02010c0207080d0e061e0304060f1b050a05090301021315050a0c0209 69
    0x40d2501f8200088108510130401000801c41100181840f522a4001e9841c00a1710310641c0c981080514080b5588510030070610720100c00461802025501d03060700c801c54596006981401980c08010034820b007102040403082044034024072030b60700e840802c0349525285510a8003c4030900602200f0742500507a140390401072480407110011080200c14601003d811440c42292144184480c5c4201001018030241d41d0001402850612451944c5c4c1000b0030310f003200c641c0e079580b030141141c100b0071302010422118401b40814250b85031403145113607078094011500198030745403540e10002d10102d400000d887d2450090038207114103003003c86c2c00d070115450044d40a0404c010b920541c0000c110004409559240d60b240c8138036242c10000e08a40308000c88005a600b001c40181c02c5502e4100c01034600f40840c14095124481d4080842d007a000c0c00105c00d80661000412420340800c08440404403080c0080665801c411030700200c600e070043d612454040f0700761154200051401d5184d40341d010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350939280 1250 350938030 350938033
    0x120209030309030106031203150b070213020c010903080f09030f19091e03150c02060f09012301030606080706020601060e011806080405160b070b060d0203070803130f050a0605030603 80
    0xb1030308000080c2104c0302a441210549038100c1401c00c919010702907210aa44092682809946842ea5140310340c4182c030350084c400c502032600d040f04040140d06462141140704008c201c1e11080c3d180261078107000351440701c3e4a035405400107803403100003c100c83e8200002003015017410702402c000e030801d07140011903006001c061031001c81c00f221a15800c80c412042e03071004584052460030b0264034410b109000050590a242c90240203a4000407802d41003043e20201d074140d9034504000c0383c01010040c1d031030140c01c09462404100009603c22890507640545030400c03003a552482c10700d980b007245e40b0410002d038100340010002c1c0c0303000d6800d03100c00f188181004070354501c00a41440220902e42c114101081441050206002d0304004641031117010482c4624403c3c00c0c2883d100c414010032400600110181d070014803a41c0314540b490b40c50640c054121100782d034984225030340340c1e00451600342d1444106000041c1c2d42182040b644c04841000e40700700b891a040a108407940c0e03200400d0386d60103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350940530 1250 350939280 350939287
    0x41e090c0306050c03240d02010c0201140c070911040f0501080406110a110d03060602060c0d060e0106020a030f03110306092509060906020c13090201210b0901060f1202090303 77
    0x718a0b01e003d0f00348184108000203035689041903411602c4026007941e41c1c2c04c0c241c0d07001c500d007103502d80700c410440c1180c0908000c502c01d410352004079854140e94180701c046000c086000c0a41c0d850000d000c00a03101e0b1000e080c0300141101403054254000d03881640c5940c100504c00f0402940980c0d4401c0e00980100700c0403a8000540181c03005a40c4401d035000002280120810042e010074030640981462611303051054610f001030007941d8200103424402c8030000080c0080c80744c1000e80c08580140800c0d00307088420340c1e485401a4503400c101c1002d901180e92283c007507411620038401e04403446040c1c850b075415619100c0c1407201c2c001c002003942503403922210040384080101c41c1072401c04103003542d0310340d405400d1200040050f036450f4000350039907000c500601031603641d1200200505000d080c00080111031400101da0b00b4400003000504a1040000450402c03102d030065004a0400d590076825666a0001251013540300c1c03030700000041d26100d400c2c85203900c54004050040004049030305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350941780 1250 350940530 350940533
    0x201050c0304140f120c0427060203060117010f1509030203061303020106060212090d08070209010303120605120d1d030f030d1523060d020304050615041e090c03 71
    0x207560302c2a0410148040302d00101d5200b441c01000b5100910700c251000d40d4181403065225685008005805224541b84c50440e00300d001d00c0c030401400224552210311130300c1140d080400007944161140343c0054602080034a813012801c417041d0480f0314854550001e14038000c1603c802d0313001500345000300040840300202680e0104903690160b2074854a0714020a0300b450013030708503080e690200041d5000000c0b00c240c20b11103001595100001070310f024030304040510b0401800d100c2c00300d001b54060118800032062552254200006207600701003042845d4540c2d00b04044000e400e20030b50086c2d8001c00d40082c0c02403107002c0f0307111140703a00d0780b04c150460100b078002402c15010044c16505039101007200c5043c501c0a010740d01041009040940344070742891030400d20300c0c8201e1089030307010f483c01840380e80e0740e190f10741110a1503103858004c6483e0305141c03074819200c01081d54083d441e4014405070110a18140c450900c20203c0031520304100c20400300441c0141030940000d0b103005104800000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350943030 1250 350941780 350941783
    0x213080109021f0315030303051e071409041b021621030516020301020c0115050a0605040608100f090e06090d050d0b1305040b04021507032f1230060d0201050c 70
    0x6010f90b00c42c1d200400e20340340545c030700e50100d041d80c0c0070003000303031014ac040c0000035422520003544c5070100102c1c03945d1030000310301080c0038200410040c11021010b0400201103580420035081e902c10990040c1038166541440b803074000e07404413002d004101d8005030800042d0140b0000d08000d00342c40c201468140c0a034001a089030015044050700d07945541040b0040812940c42c1e40190038100d950901e50382c20320303800600703070300560140c0c40034054150041240900440c0340c040040c105031400000c020745408156010300f101e041e0b00c001a105400100302038810124486403601e08a030b850340d0802e040c03042c8030005845c140401d560021402e407800c00e09201c80d401818400c0d4000c8040e4146400d0610600c4075030070090340741e00e48010042c8500e0000960282c926168905110020340c54448554072200580e13843c3c543c040300a20800b03156000004e52440500500620b0ac01b200c840e2a203041c5944028800841418007105601c0c1c0020790186043c860340b0183d5801803401d07a06180c4102c0c03445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350944280 1250 350943030 350943071
    0x20301060f0501030b060c060c09031507120c05090d02270c090a120b06040b040b060a120608031312050111030414071a03040b041104020d0213080109021f03 69
    0x3030202071441c11091065507014015a5006402650410310f02a03103c80f050791a9000680b4003941c0000c00103194a40c0d0303404016603a40d01d08208101156030600d088051b100c03ca22031000e001d41400d01e2110b20044d400780c4d0581c2c40c4000003a000003d09840b660800c0301440c2c591401d8618000c11500090b1010000c040c0781c0e11916001c0502d5558204000402c190200c1c41d50000303089a0001c86002c00041d0b1100195400c071000342c90214503070000c01d0004019094180c4200d8000002284c1c8030701c900d5014000c0c14081c07881d948100300750b41d04c030425a61248580703582010380f01010700041140c3d01c180310503150500e00503000020f003c007809e00c02d140503034819201600c04004151400b14030500602c4254010300312808204d02a0401440301121800000c0024203603207100c00c006420f01110507072130503a000e40108115520710743c40b81c00340e000b90001007144903800703001e541c045040d40051040d100340c59001440c0d040040540300c68003400e024034607403072000c240c2c071040c0c0c0642e4810501210f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350945530 1250 350944280 350944289
    0x306041218080606030c03011b180924170c06030903040506030405030a0809010207210903080a02251a0a030f0204030b01031e080306100302070c060903050f060408090d050a02030106 80
    0x2800a40c03d00304d040502d08128000400d102e039160400807004040140303003107110380e102c42c140607104100500d41c3d91040001c5910031598113003005d40d0301000c84c940d4078144502d00f4000d10049400c2ea00e50652510540ea00c001d12481d80c1d1008190401610341a0091544407140f00d00705c03071a02d511003020528580003910116102d40c40407903400407081d003001009500090307010085042c0506602d40300b45210052482402082d1300c0c16280040c0c5202d4030340f800c040c41e0403040460340c58100c04c0d00290388074061001c03a000340441004000e400c80c0340c80c840b1400c66584510380d901c02485d141d04140c00344d1003641c2e404145aa940344c40c0c6001e4520380003810056024001143c2d040d813440c10822444215070074400100c140c50900e0100140e0188152600310070203564070000c0340079592054000344201000508801551132002070380701d91280a41042c0c03442441903807a12041d03041200c0e900c080994004100420502006d82d141c00c203055240201c034051421282d01e07a4058001c2401c55003180c01c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350946780 1250 350945530 350945533
    0x303010918020d1103060c03060a0314030d050c03061002210307020f12070b01090506011d06090d08070c050316030201082206141003020303070213021308010902130605030604121808 80
    0x1468044d524050000c40c0d8400050203a840c51490b06000188a01000c4d0000402c603d00c0e220b032070401041c08109481c203071440c080c0100a142007008014185030022201c0a03c07a109440c2000c05040c03010138008440290a90a400d40180a503103000345900000e005e00d0861240c070070741c0242c0c603108000e01c1c4075450364030075625680c000604201c4840541600a03040c12805c1c5801c0c4035549c0d0f8041d40c01c88240c0398445c024030b000051000010b03c1e520134815803ea100000041d82800e0004410042140340e1007a40308015045d1b80708113250312000c017401c1c05000001d280d0300800140d4014014143e118058250800d003100c10b02000510124294200303079000c81e511070001000d100f040c0790b4546c01008071500e082c042443c642c0041d0ba40d00c50140024020300d14028800100e0b10b05030140e43c000c41036543e8042c03903c0d0702d4040c0b00d8020f00000d00241d21980c680b50007444210f5040c4945410741d00041c018201c550b882d030306c6228107000003007000f004000800901c18403007141f00c4440b0016007100c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350948030 1250 350946780 350946803
    0xb0c210901021006050102060f0403030e0a081206040507050f0705070324050c090d20030a0f0515040b0703180507090b0a0518071d03071203030f09050303010918020d 73
    0x10009107043c0c10291111281c618005003030015a0700040c00da54400c00b0040b003451f880c0e46528045001e805008c3e440580c1c4e10030310740c0400400c40600c02500c10802c021105a109030744420800c81038500940c4e040e408a88100300b9100380ca03800388002c00d5203601540443d21010741daa03030384002c6091050380c10202d0318480400b90400c1c5a880c018990042c084145040c00c1c515000c0010707825030381310f00000f4006520910f40c039080c19070400301e11504400050a41c1e8403222907007403100d60341d406040c003190640210162200a8042c42d0141e038040c1e81c11902041040c0c0d2102001d0303005100718a0125506054a654400054010001000030f400007282c0400c071404c090b42440f8280300b06030002ca11400094400540b091000816151300c1342c4146007950443c2000c549130254406c450140b144c040c0205040030940c2c80800b4042100244255800c000c00d071143c80c2105c0440b46100401441c50f00100010841211150170140c14442501c2c5140290007070395000030384000f9605000c69142c0e0180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350949280 1250 350948030 350948047
    0xf081903050420010206070f020a08030f010e0f01080c0607081303060e070501050c030703210f0c080a09020906010e12030d0c080705070c030803100b0a08060f01020d090b0c21 77
    0x420901442080360f100c107000c4011040081e499020050007101080b994605070380034280b08020458829410a0b00c2c0750b501d003082c401201d29a40240a405c254100900100c4c0e6202074030b10741d0784e040380d9101c0040c007441c0a00008100d981d510100065519010030311184c001440900d21943c02180b0400c0300289150300061000d0806034181c2c0880d05100040c030180a44000c003004480005505207445688462400892002107205001c0855114036000312898562543c3d400340541c4c4030241c40712051507a5040804040d2031000e80029088009032000c40c4403540103c5203114224401062111403c007480102ca295400440b201e01a241d02c489002e886160082410340c0c000c5601d1030680d24044080e1911204040e051100a2031814000002901d908451010402070104e00e0100740e038810215000800711441501c903170340b088104500307580c03840d800007a98801d011015181d42c54030901e0582c0610b403540000300030b060107005503c4c200b01c2800e410048040c00300c000e405059100c0c0c100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350950530 1250 350949280 350949293
    0x30b091302030d03270203031e0304020103050105150d111905040e01050a081902060d1d07050301060609050108041502121f0e130c05091005011701050d0f0819030504 73
    0x211046010b140ca04050320410080c04d21780d0003880c4c49031080202c0040c1c1c0600c0481c0c0303540700e810500101c49010742041c0a003060b51100540c0a64000da805110030b91304c1d030040041585050582d140c0c90a400c001c610f15064179500117012105080030600e0a200184901041c28162801c1c4080003610001f0148000d141001c001400740c9030689140100c00d0401204540d6081c0e0700305c07440280c400380c070201c904554480013107980304440804207104c2d02080b5008840300000b481c0c40b20354071f40203000e4085140d08051041a080f0b07046c60340e91220701d604e040011754041002030f0080d0b81c844444010099110f21a0000301219078895845020501d05071a2580b084559400544050080d8401c00c0003417103001740300300ba08105041c000680070282d9140c0b840305d00c1032036405142c11940d40401c0041c6400c0799140e96046030801e803905100a0006034800078000024000d95900803050240400420711509450b100a4444ca500307070329241d181134a0010021038510040d0000b40c4400400040141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350951780 1250 350950530 350950543
    0x414060907031e0c170c1503090d0f0f031806060b04061211030a0209061209010c030b0a0807170321100e0402030d050d180602220b03040b07030b09130203 68
    0xe0a88070601c01e25030b5640816007200307417041c54510080002c00c0305010805010021a485006240b80e031666004000110660411200c400311406801d1012509034000d62000070050459600c41307007807517070030603040d0018001d5008044020000c0360042000542502c0b48078090b0104191464680f45005801003000390340008205002e410043c112000903280c1003505c0c3c100c4002c800168071144020041001c9008140150844007011001d001c5d1041040d032203c1031022030f90f601030105812407400c0c82490b021a200d100307a03c1e88085410013030404252054100e001c11241540d2900e40b4031a400148140c84499910310351801c0340070705c624041a004840001d28020031008110b00d004d400007500c035044060f004044c08400a0112540c240540c01414240da505426140001342410141d000b5001842c0e1424090410701c0000c6112140b201024100d6601600092440d544da548402c490400038100348203158481c584241159140344c0018451001c112924074041d00500406103042c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350953030 1250 350951780 350951813
    0x60e060a0305062206090b0108010f1503020f040212090c011701080c010c03110102040e150a031e08070f050607021614120c0d030815150d05041406090703 68
    0x40048410000524042955548070301c491404c0c135401031402d42413080c02d442e9504000c0050380740c07140d91403c100d5801704150507280240000c0100a0f1031240c0001203482c01c40021070034040c404801c00c014a841d0000e1070711300c0380181000d400c010103105a40f0303540d00c0c2500c1101c0c440d0000030550300a5607000130024220104000d558030b040d45400881911a40806851410001e0b1480000e050500484040e507001d100f9030000c65559540e09242d807094802030b1114240340040b100b05c0d001c0d51500d0000300007540d40084400340f074500504071480c000007943c00101e03031064040c81290082541c1981c4d0450843c0684040c00140c6403092000703040040300c0b002c40c209454402c0d0f00b8002a0521940d0301643e90050b40c418a00c0081c030210913140c10002d400c0d9a50142c088042903080590042c002c50007800c40010319020a55100e0802c808001a2417480003c103400b400180800040b03604219003142c0120302080c41003031032848003801d01d0011100c20f100796000314001c00801000b0346c010310f0180c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350954280 1250 350953030 350953039
    0xc0d050d030e1f05060d05100c09080309010503010b1c020a0509010e01020115060c05031201080a120906020a0602030408090901060e030c031f05040302031c0902120a0f02090c1b01060e06 82
    0x70503403000c101c0e02c507070340c1001c20f00c4070103964100040103600c1d00320302452580e4100081382e4141c220101c00102510000540d5000207103032020007c0e89002c004262803a011050b12030f90300f980c2c01e040e00c031046500304091f1104104441720104407000c515200507c060981076980366900c0700314500240880a818040c0e904580c908001c0c024030b045a80590000d444961a10080342c0041e410424518080c1c013420000c01c60704100000340e401c100003040f40b40700f44250350400711034050030b034203683c05101031040348056041064200b00040c1d8070360045601c144910315250034004210085070001c031b026000200030540465121761103160810014a14600c1103008250b24080c1c1d10b5112801030720115401d440da82c0300c00c0401d08042c003d00c156100c420b0301c911400e11841500f2100c9010340803c40050f8020703420458100301c0d07030b400421050b0a49800903001002c200b031940c24000c01c2c8038003c00c480b50f180c0040c0003101c00c81c550004050955a0440c00100d8850f007886160b400601c03001d4003e500c503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350955530 1250 350954280 350954293
    0x60609020a0815090a0b040f1817040e0c03040f0b070f0306050307050d020d050312041a0a14060d1511030405120c150a110d0c200c060304050c0d050d030e 68
    0x2d555410a04c19070180041c000810030100f403a012601420280c0c43c06180b0b41c3c100f0001303103240001c10100f10381d980c0c010b0700202c10701c0042c088040b00c50b100750b00403200203407480000280301c1c05100c401150020700c40c3c01802e51503609600c8070009a001910101c00080000b201d40d500c0c907915000b01c501501048018000d07031483c080c001a0342001744c801c000d001e030b030440138400240b14040c0240d84e403c20b1400c104121030303c0c25140c0180031403106000d10794007007150004a56520001c5c0b00d050802190a40b90803820b465500400044c56030b054402c481c0c0041d6030400d640d440b503032409403003810b08090341c006440b07041925110b4207142c01c0ca000e4400c1d50005010800e4090b10005585910150001c0090504c1e00d41c0d0012902070060903610318804080025040021501c550000300340da03d055948000b40e0002640e800321901602580300829400b03148600c170b45c1c2c80c00c8401550040d115400300c500501c80ea101080102081160035543c1c1e420070150701d5100394150092101d51400913010341034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350956780 1250 350955530 350955571
    0x130602070b040911040302030f1f1b0813080a0306060201061a0702120a0804060507050f070f061107090905030418060518060d050f0309040608060c04170a060609020a08 74
    0x202d000d1407281c1d201003519032409100f10161001141e000d5134001d0260345000ea4810f03c03040d90b40c08400003240b070f18811680c041c0b070b422890348240c0003418407041c00445650307620740e4100c51006006c1e0481c0c1c4801600302840300005d136120020441d109231782c1c8021421915152019085485c035601200340380d074080c515101178540610444100c10307030484a03000c02d1600301d42e00510303000700a90020b10003e0000350201d541034205000d860024485d000703c51900800c03240307080c0c99081c144118114281140e4050045c940030740801c260003400c503000c0350342d01da9407061143c0948490181c08e803295040002c06120200c42099107000196010310305010a034034081c00b01704110054030f0f1001d403100d003400c041003160792000015120b1540110482d109a081034005a07100c2d40a6922144a03500d405400258500f010440a01c030b00c00450480b4282884c04003440101480c410040c80940958940c1038002075640c03081788003038803810000607181c062898002d8150b8a0141400c60001070007004081d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350958030 1250 350956780 350956799
    0xc17040b01050a0611151e0a1505040e06010306110c0613020a0e1005010f05040806040c1809080904090501110409050f01050904230309120f010501090203040b24130213060207 77
    0x2500c0b084150300c2c6143d40d41702004181c1c0d40203002d00c078481c4450013a048c0420001d80790400c12000110706041c07080c46503620100812603181d40c81e68441c80e040200104003050a46e4030401360781004680d290703d4403070040420350503c1800c54240301c490226620450540c01d04200399000b51081004c1210513052120000340d4144503803140f50304000d410032807030744170724461402c0c6e400800d401d4080350b065003050319105203400a98020745003151102046000001a9402030324426904100d210786410700e040d0a03c409000c0312a0181d64640d2a0600c0420004946000744010044480005000d04007aa240003034400c040e80524401c002e02ca00b844085031103075006002140740d810342d04900740c1200041038214011501050382c00381000382c0c20045054046000c2d40d1421500000f0045aa250000b04082740001e48010300340c2c00a10000411046803400030745101d81506085c001c00342c03915000180d05100c050050304189402243c0d04106132240c00c4003c02030441800a802d40c141001d0224 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350959280 1250 350958030 350958043
    0x30b0a14040215160819031410180e0307030c03090503010b010e0103020a1e090306050a0203010e0606130305011514010c0203120a0c0606080604050d03060b030a0c17040b01050a0611 80
    0x7144030410005003441e00702809069001a9a4400e1740b0f95113401c0d240d80041c1004480e070800402184c10b03c8a00302c8401902c00741c00f80b050103001c0c0481c1c406401c0162500b4400c0441d020149035a54814054554120800c09071049034800e9490b00a034200b1803400403e40030b40350f0301160103603040400c440300316a000f02210214140c00c0c80c0043c1c82e91321030030b8101c1c1d048440c0383c00c208007030b1541d808001d10b00d0f0b402101d11041d207000b07480500840d02d40f0310a1000301d00c802d104001408401d580424010314088000344848001c512150812540386e49501d42100d1070061803003401c1c201080100804200406410380030003090030000c10713070b03102c80d004030752681020308038a03d41150002e8018591401a500a003000307401c8801000550345030642903540e55400e5400f80c46521410241540705c0f4031a0103040155210040c1040c01d5449000d15032018000001003032041c03106020398100d107000070311480d6201724000d20840b249541340009101c0e0005c2c050300094108040319003100701c403690004c3e44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350960530 1250 350959280 350959309
    0x2d020904030e0d06060e1803120c0a090315020301090b060a080604051003081b01050615180a170a0b090c0328020a0b090a1d070e0402090a030b0a140402 67
    0xc08540702c1c80500194850565400003040795140c00004a01003642c80340c500e1103943c0f0a0300202c0c1103400101c50f942e0301c0c0560951741c8004130903d000200906204005440900a00d040c8000b840b80c403540c80d815500c07580810300c000143d0100040002460f507001342003d108058503424500342e145030b070007001d07800000c2406004540380c401003002584c0743da0083e801960001c00c06e60b11042e004071a01c110030000404030169608040114416141000345c519100c5020850303580360100310b600200c0780d44034410105034890419000041e000081d00b034460030301d03484140035200103d01d40c034103e501000050b001c6803079640071603c40c0d260b03601c001500304181c00000500230b50f401009030352909a280c1c8210b0094000542c000c00040d030b8468800a4020400221414180181c41740d020149080c540c0c001c2090400f40140420f40c0d01d4042c0a510368240d13800b034805454403c644001c01e084807000d90048804400840801c600c50310684a0a21107200740c5283c044941080d40002e40c0c3d4940d500507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350961780 1250 350960530 350960537
    0x1a040c050d1a06120a0b0406050d030c0819030b04110306060f0906040510090321140d09120903030e0d113708060f370501032d02090403 60
    0x301546040300b554004282c402c000308942d94034404021491030544007a11503a2030705007003020341182490540100030603030740301a0030b004441507651000c444010007600d064070b22000c100300c0900c03203020b0488080603203629500d0110745107808009020407600f407403c181032940d20900500002e070b5074040480f401119046142c43d2035152f9980029914803da5020560080030f003d0000605900440c010040741d01034503920302c485c4442e84011040c480c480c405000080c0b0010712402442d41008050034031402c10035000941c40c5100d0b07031840b0007407540714103050204070600d008004155100004115110b0140e45056401c1443d940e4900114813450225104101103442001002508134044c240c001006044156603030121a8940e6008014050a02c00b030284d1170000e15a104450905401548440f14209084c072503e8181d5032006200036061486075005c04d205115541e503406094041c5d4043d5442c3d1807a1390000200b2481d4000041082003581c91440700f080140ea00c1c9407600741c2c81070b01402c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350963030 1250 350961780 350961791
    0x603060f100b0a030b040213050a0b4008060a06080f0a0204090201050d0626010b0102060a0507050c240130020607051618060e1b070c06031a040c050d 66
    0x8406a01a2080e0903849800510204408c8040e00602c80180b04031241980c151094139111807001106118905040c0040d4001e494035a1001a14080240ca1501e41715005104140d4000154801044a40c460040e65104e8024030200020610030840101600001800d0240d00220650b444420080d400383c41203a03124080001d6902440448070044004541000340b29242d2590400b84101d03001c0300d4038408000e0b49403070180c0d0030510070040bd001058008103002da07030303541022010b032a0080c0400b0401005101c0d08205000412015411014640c0b01c1003200043c140210080d030016401240c240303442c016640c60201c05400540d0866000c0000c0092054050001c2103280c411404001d0552161800301c01c6500b90f813a549001360303500c0d4005600c1c0d801d203044c050419a8428090b000314a040c40700414159100c100e6140410b0b0540e541c10782c20400141c8500810040701d82c8202c02098480c0c0c0c0c00c02d146207500b1402141c910040750100b080303078040ac0c0000c2a50181c116003102d407980e0f42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350964280 1250 350963030 350963047
    0x5010905041a0a06090609151e02100c03020316080c03040605060a0f15180b0f0306040b120f160608010506030a1104300b040803070c12080603060f100b 67
    0x4014240841502400300c0040b513590b0701c0024000540c9121ba0710005c1c2090001042c482e08a91003200c240000d035072040e0b4507078000d108000320320041c0c1c050038003544076a0600b54485040d9025900b03903070710582c50068403844c000c05142c1015409840c0e14041185000c10011200340740710689410907003094000960795111720109851803441d4001e01030b03800e00260001a0441c00c04041e003044e1116a490541c0c0011480311030b180d402c200c2c007400c514018203020311580641202e000d1584507000610200f80f0312800c1d0081141380110210002458010b480d0700140090304100100843e0184468240c91524081e4001c1443c1410b00070302c0d00c00c200000125000301002e0300710114256885007002c1c0d4a0707030390350107060310f21451100000e10b0701465407185401b244071441301094280c0140c1d5800301c5640b181d0b9a00c0031a0710091210b03040c08003081c03403000480c08103410903280b840c45886286450a00b0b408251620344001d0000240803000400c1140591980380d0300001c80b52180180e50716039011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350965530 1250 350964280 350964311
    0x1603260a1101060e0f0103140c0a120203010f14010501110a020f0103090503070b0108030903071a041a04030515040b0a0209010905120102071e031403041a0a060909030f030b01090501090504 83
    0x11350300c41e1030b10004030810b1060010310b8280050480340b0589403042071030139609283d5251703d5901c100c42e50046820204200c80d41c2a07842d13090314240300800009071456031b00c40040c00c8030501c140281000018074014411540c02c901072102c5581920000e00032064141c0c00220409560a10641019208d803840d008011041040e1460258080701c00074180d038552154a40da504007100092003807144120018003c0107841c854641601c500c0481c81c50306082001000e0075002c103c0c003418070301200700310000110b8424040e402035441d00264440060030319003030429000c4809040c9002852041203a05401d0f07070404002c1013112000d40d00006030890400c0a14024060080d01910090f126011381d030000c241c481340101c42e00e20a07103c0075805070840b800c403032890104642c0107141241404401611142103403a03158401081d800c0481c10366100e80c4082c05846c1648012030200b1020500b404155416000b210b800e19020301e8000b0b1000c0ca0300c00000d11071100c5108035806156106609200e0f2101c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350966780 1250 350965530 350965541
    0x2040b0402040b0a12050c0f030a0b0d141510081b0f210607140f0904090611030415020306030304090216060e0a1202070501210902031603260a1101 65
    0x2900503a41340c0d0010358000d41407800b101e00103c5194508030000c0c20182c40c180545060143c0a0719843c21035543c4d0104174018080064143d44c400c5000b4030141c002030500294980d6184038002610000c402c40c1d0400b01e800c2800382106540c54020030f000d0004080000340011418098110b082132100c0f0003002c80d14400f0280c2d0300d203801c0030100211711500c0d2071341503407403181620050440707150f0307519035104030342c20b0a0284007242501020000d050001088402070980314600070700001c1c049131250f030b034071040320000000780d09150780102c02c100134403507007007003110038150440d4041d407039450800e0000751244218020000455408622a400c4488034000c13070f490b0552081080003803030343d050718003503a81c1d035464401c40d540c4a1410700f86010700c2c80464031000301c500c10707141d015501145245803003020400200b50110242e03206150009650b003041601101161050308403040303403c508082451a81084404010340c155441c88124519001304607000802e40349060119403440f9400c0034050030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350968030 1250 350966780 350966789
    0x41206020904110f040305070506070f0b07020f030712030b0406140415080f010501081c0903020105070203253b04020d060504081206030c28080a0c03050705150702040b040204 77
    0x860101e1048004d0624100070003d6900440450380c00903600d0080000c24402d41a0060403019034044200024064001454000350f02c2e005131a0051061004a0302d0b50b04041e2007900e24204007900b0111807501f40c410485003038400d40b41400f0040c20320b48e202108a1403a0307452801a03a076480c00010010080955501502040e0160b51280e0048051140a8a4203000b4080d03103014021600e03010000c641c142c580b00c01c01075154540c2240c5940c0040d200c81d001280c050b81c041c0100c640b02e801d05140d406009118900080420140034209009130500e426881c0c0e0030803940e4880b02c1a002c1c0c2c0c0840e00300c0014800c1c0c0c04e500c540800e0360380e84086940106816801440c11341024184420814a04007401019400c051611104e070340310400c06958551030312001da044a888800d840340302e030706070344c640350520138111460002c3ca9031106850302d480403807582600c4450202c4414020040107100c0307400140740850350a50b42c00c1402d50311100c2441181c0000344150354404509966031500d805603070050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350969280 1250 350968030 350968061
    0x806030a060e0c040c0912200405100609050d0803130201030902060706020304020f060f0909070905031603020909030a021209152206020303090d0c060b1f0311041206020904 76
    0xc18002e0090b40c482420180610444c102006051454410301c4114220342441584004c003e0302c645800074521070510100810011843c102076158650b030103864000c05015809442e11440c5c1240140b09412036004244150780041d0008082030701e000a9a801502003540407024200910059005000680009421a10110342001801800e5010b184a54020703180c4940d0001c10342d081000380d11a40741c1e41524a0f074203211110160401c408081d500c0112410503158041c3c071000064581201c1c090708401c0c074410140103000710300740a40e0789034001608500442c104464103d001e5210302d44101d10080000c004260b403002c0d551910b40c411205a20384902c141c1e1200c24442c0441500d0880d4078841e000c601501c8005200d9200004581c8103661800103442a105046c400b1151010451000d132402038030b84071013100950f034041704d503811100855051540803004810140c2991840754103042c2103d800d110402940741c110109011a550001c40160740307010311030000300185074906268860 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350970530 1250 350969280 350969291
    0x9031e0d140d1b0810180510180e011401030b0613150902040618030203031b0a051009030f0201090b01050907120e010204050a080102030103170a02070e190b1c030806030a06 76
    0x2c100401082c090410090780d52045640ea540c1656185905d80c0c415070312010f110451841440160742d102d6908070340c10320035583d0f5141c0c7c0e420b00c842071004485412420305079039140b020f60080d000d01c11852a0015a9a0702c1c44541c0b441d2030f00300341c1810080182e40101010055500407882561091207201c048403c000b0b4019190b18600e0000e4215001e92400305a65000696600568a211100300c0e07a000b4011342c0380035085902240346c0c0b03150441c04c003c43d00c103410104000900900000e034900100c903c00044007640360034010300c0300341c1005c0100f0669141c408800082120740b1320690554400380d0b80040c03280c0341c000003210241007454264043d1072030411207051055041d0000e2040341d80c22030b005c0d0846a1600d6030603080344801c2c4002003004111906d4a603560f900e98015100f110050300580324035990b244151001e24504603410070040500c4402e803e140d1310207100b55110100b00351015800404000d641c01c100c02c003a402c0240c1880a01000150140c4e0100207802ea22980070400340071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350971780 1250 350970530 350970551
    0xd020a09050907111f02040b0d020915070f06020313021801030201030516050d1d12130b07030e010c111201050405060702190b060a0b07050309031e0d140d 68
    0x1030219501070540714510a0010521980c820702a80706180f13120409404404072021000e002e0715420341c840000b00c0c3d0203220001318248408040c00c03100d4483c8034050380d10705241080222a40c580140039482d8030080c00083c002c82d034980d241080d000e41c80080184d0783c4c2c441500c030441800100400a50000d00c0420b020302400c902000c09040b240b003a00d062106e80c031219200c00302004201341c00000a501485008026802038006a81341c80c2001c0e4400400e959480d0054109060142c0300f000080c00002c23510b2401e4185203640300104142c0081504050842d580100440003942030a0b0410106003140c10512010080303080c600800141000902c05116a5203030182001300c4041e80d150180e240018022800824901f4281800788804c0484105d03907a0f882080c0800549050f4011000043c0450100d407070000034110f45001d2001982c03556640000c261030700010030102c0c088000a501e20340c038000e100289035080d480e101e0520400c5450404c030045c2a41c0140c55003214583d040414424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350973030 1250 350971780 350971787
    0x90c020c1003051e04020409080301121e0c030201050c0c060a0f02010b0406030b04030f02073507030206030105040e0a060c0c14070602031803010e0a030e03011802030c0d080d020a 79
    0x4200d4050392088129418050150120f9400303c9194070000c090341c15409092002e04075056200d4401480040c0300c0715640c9810095400c00d0704500c0600d041d0780342c05801c0c44607804c02c0400070310481a007107a104e041c940d1102d00a44003031000030305204000c24040708c8424203000302c1c2070195002c1d00103511101075990090081c5500020f00c030144d460541c0c143c0340b9080070b01071002501d4020700700c14280e8640317a608035010b0030a030b0b03888001c6001d8034101095a002440704000b000800201d410041515542d14414541038801702c111940c2c005d001c2003005880341010399044400450700010801c0000c0300c0e16040000c01c240040c60789203014541e60304243c000940c00e103018058898400c600e900030038229600c8000d80180030160748180b001d403959106e030b503035030000f4101c014001180807030f0440c034100d24020025800700d0104441d0355491080d81401d1103030140c11110b000001050419a4020a1701e400a01c9001d42c050300c01c3c4030091050218410803540442014081195034210030784005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350974280 1250 350973030 350973043
    0x10603050c060f19030c1101140c03060a080d090513140103150204050301111809090a0605041a070207061103160219030b09010c02060105040e0c0907120218030d1e0305070306090c02 80
    0xc408648032620b09007580f0014810070958031842e84100004ac1c81d500c07034140745504018401a804444140301203206030b41440402914400c60703e0305a089070030602000103171040041103085403071404120f80b10b90340740c4d81c501c68116038101c040c444003080d903180100c0c040e1081d178001e55010760910720b4512601720100c0c01007052412034007069034841c07c02e03420070214000a4800303010551091441038040340311035106580181c0310702c500c0110003400070409810514100c44900c01750300525020008650000c0c074042c40c201c0814051842c1561110054407182c0d01c0c2d0784040d0007002140c400750443e5400f801003801554200c4912100c034504600ba65001e04002803c00005008a0300002480c0c1428000d03094512600c1c0003a05041c04003200b80408844010b045e44c007042103e604101501240c5d00c01024000c440004035a10011120f05040c03410200142110070403d2200354a0040e888600700a10241450b1501180300d80f6610b0040380a4450380e000000e5051400b00300841694000a50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350975530 1250 350974280 350974301
    0x32d260a1d120a030e060415050705070510020a0b04050f01091506050303090a0311030c1e0306010b070305030103150e07060e0301050f0903030a020903030c061017010603050c060f1903 81
    0x1011181501d00070302480314600741214140d507100c20f24620004c2d001d0b98600c111502c0291019051a60f95820240140102444000400c20008484c0240700c0c1c00d100560140009840c0d100010aa2290082d5126866040030300840e20341400b003000c1000a02440c0c401c1016070b402801401c402c0e04000318041c040320222546c280c82c11200142c142004001c1d103105850080100c070406145489188401400380c8244d03605000c5c071614803c1c2661a44c08165585020150010a030304164083c18030f04601070b04400103081041c0f1004000030b510008482c1541c4e032044400100090075240302d406003400708602c10309409800008581a40d01040c465a0b10200718002c1c030041d150130300f5540c20702d002a45c00c280960010400180684c035650010180c06030050120380c0b4064a09569604012080e20f039030302c008681c004200a03062403203400003a40721849000700309851a42d550580c1c0d07000c11b008414003030030000c42c0804050b0b103003000f40c0f5080d00c0840461040d0580f2840028000e0811101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350976780 1250 350975530 350975567
    0x6040803101403030d0e1518010f050f07030e2404110603040f03030b181003060b01020607020706030c110d030b091308030103020607020604030c080304032d260a 71
    0x200103240c602c040001d424242000d0041d520303003155000300c42c02400b0a106040d00510440c12552800f0080801c0701d403140581240100450185807400ca007503941420798601400d080405011024840d08401c5400005904000402009244540e418080500c12a142907850040c0850380c4a42440542e403140d849415442c820007098000c000c0c86010a5801400c0e01c08166034100000c1c2c081d900c1122080002008001303441804407611081d6207007120341c12405c1414100c01c004000850241181208090001e440140b41c541c230000d503524140d2003210201038445a2000a45000302019003181e036490003990302c2955090b00140c0034220a02d215805000508005000703c90a2505092065480700400d442c0d41d186170208031280c1c0207105c00743d074899020080000002e4074440a60300905030031026540b240c0ca5410443c51200350f0f000e0382600c20507581d41d9040d003020a41e0440764015800380701c1000720395040710801e1709640105480c17109040d00050504c1d9a50b08501b0380e01c0079546050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350978030 1250 350976780 350976811
    0xf0b1804092301020d02040801090204060609030b0f130803070512060f030a14071509030b011e05010c030c06020d0e07090912050d0f0906021213170706090506040803 73
    0x2031208860482502901808084614603484030031042000004900d0000160501c88000ca88400700c2c0e12540c4000c0d003da56a039000011402d19010b0400101428202000034500d50307200c400f05003a0007001800300000210014101075502c01d4040480340e00710418940700c2c506008050246e511040c111a20505c0c0800000c29500d0400c2c4126030045002e00a032040d0011a80c0d541c0e41201d614181c1c071118040c644001c20200c68014259841a002d655958400c9285040c501c1000c44107810008000a020149084410111851100b103400070700c0c02042c680032604089461600c3c1e44d00090106000140508072425540c00483d071070603104041d50302c80780d5150040002c440482c040280910040801d4041540c02000540700c0810200c20105440c881500c550040baa5886801c0720760320b5000c2104a654602c5454040c1d124080003980c45052030b49032a81c07422648a06054a80784000180c0003041000940142000c40d60081c116515414540303002e000540046442f11410388850 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350979280 1250 350978030 350978077
    0x50306060a1505070f0210090f09050424020d050a0e010c030e1b01090e07020607200604081b19020103050c040e0c0703200c0118060806190f0b 63
    0x501c03110708440740c00225051002d60b02c1c80a0703a1035003041006950a40455a00c000540c4540a1400d06911142d440d41c0704170f41414060b0041c151a07400894089260108020014403055a5003d500200388004a03a10b005c0e924003c003c0d1040308041c42082d4207100038881812816000092401c1514009100030a2403060442c12280e60384840c0e0480c0d84081d41c0790704400051600040f01c0744042c540040c100f40c99641c14014840241e4024005901c002d00f08807003603034003000031031000a85017800e500503007191071140e030303034503c09070019103c07500001c1c0c004100600192052481030f01780058a404020520440004041030075007640805d040a00240040038020100c4003920500b40209026403542c822120590b0400d91044050043c40d4002c400c00120414100c82c890b40301c5401010b866a031440010004100d200754100c1c0c0d0320017944140030b01034100c5011a4048029101415040109002217402040380d50190980c410952404250010804010000c130512083d22007204683c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350980530 1250 350979280 350979289
    0x200316120f0c0b07030902150d0b0d0b0a1e06080705150306031903020a0602030a0516030507120b0310151703041202100e03160f0803030108070303110709090c05030606 74
    0x4140340c84000350440e00e80e01c0000b104410303496013021a80c580090010595804109120030f244002d0042c2c1c0f80105040070180e1480c005c1104040e41030b1880c4c641c1980503035480b02c243c03001409400001e81c64007140c1994004c005680880c1e02c0b0b04003018040c0559600ea056103550450040e80d0082c1c485801e9204814650011a40114400340003000b41c05042c0404640e119500b060440450040c00040c002050007800a1409100724540004142c03c0c14643e01e00e40311903580c003090a1604000400000036080703c894145010750f0080803d08400b0310000a04080e40f081c6401d01103490314854444500c509048241594004070b17018030303011200d00b03d580e501e004501c607480e0465006c1e83d6203001400e18404080852410b0708005012070a5070000070b0074070808181003500c05284000802c500012400400f00521040000d18919410406a203490344060f000183c10303c00301c0003507a0903000d81000000c0041040541c1000401282e2408403450720003441680d1291050202082d040d103007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350981780 1250 350980530 350980547
    0x7030909020c0c010f17040b0601390f0f0b010503060a0b0604030312150e0601021e0d0509010504270f020a210605040509010209040509060c070320031612 68
    0xb07020006000c0c01c0d103a03100440380a15007003200001c00c4940c144840c00c8030300f0103003c240035900c541c1c5401d095240003000103051101d24903101da068000e104c44043e100085182c010341d080400419600c82843c0390801c201d8a8482c81c0005140000411501d014820b548030040e041e220100d05032015034580c0d260900c195030440c840c10b540301404103c2040024052051000411002e0b100030614a03901d11561280d1260f95021165180d201420420b0301d6a0512032090030403a2040f240e4035031200229201d035241d10200010782030200000308801d46d40c0c040d00580c0d0041c07003000440115120890081000d203c41188041c45150421801880800480c0203035160554550b550001400740c064259898840351510400440d0f51020301003155144e9008013440b0300c00142c00540d80341c10001c14082101c000a003c00d4440d08940d00f80941050604121506103805103001401c2c0030301114100000400401907a146200000c1c031200b82d400c1c01c5130040200b41c09041e2401032000c4524044e5801c29 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350983030 1250 350981780 350981797
    0x40c0f0312050a031d0a0605071103040e070c0c0f1505120a11300a091509050c1210050124030e010b061204050c030703020f010c0203010905120703090902 68
    0x6507806a1007101d119101034480400e0383d19020030204014800305001860070550364146130000d8540350207003c154040c1c00e8000b900d61508075005217407800403c0d2240154080e0880780361001010580591007040b03100701040c1c000030b4811603946e5aa0b11952080300c2c6100341c4505030110300c03000f03038083c3c007480070f0302e0a805000008885076900c1c9100d03079004200c03c08005010000034800c018100480030340b0032103107192000e5010048100c500d00e6186800004004012447c00d1240d0780000542ca19070302c0d00d0000d45c0c010f01007a0322503903117450340c01d101c0c2d840182da801000664107031740200f00c002208200b11030f41d41030800890b605c034052285035080008001906161400705084c016229a0000d000700d141c640000a646901c28001500f0740d00030100c0742a10004c4c442884144502880a690001c03011001013248502c0c5d50701044800322201099410310405400ca08150748081d04901003a9902a054904a03d46419940f00c103401c82101030340002d80094010a11010038400c569184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350984280 1250 350983030 350983043
    0x60e060405010c031e020f010e01020405010c0b0a090b040f0213090203120d060b0f19090e0a020304020f0a2403140105040903020f01060b0703030e030304021e010c0f0803040c0f03 79
    0x742800010340d20303107035114000c8042184c29095140010f00c40e1041c290148056800703007102c4050f041d030103030955a00320010400d50344104010442030b80c2084905144540c45007480543c5c2d42c2e1080400024054004054000a040b00400041050075403044410324821550540e40c54509440b1b141103c1c80542c0094065000000720301c41c07440c4c003c010b0141c501d0f00031800b09001c0c2e03c4a620214a40114491060881c808954648101c80b1241001c0d8038014501d003100c07404e450200c0902d012400a06102c880f01d03030001c00700f020354488400048400c03101612600180b560b503e000d170020191a104003442c1c440c45040d195000e4841c1c0a480f40d280100d10542c80c10f0b9084c041004001c005075081202503120340b40e080703140540280189401003041030806a112106130801034242c811000798800c5a800420403c030041c0c0e100c4060705c2a416000784044070364800440144c2c1c2515615001030328203105890024104452a07004612480c4524115022265501d0608600306194040140302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350985530 1250 350984280 350984287
    0x120e011b0c0b0309010b1305061c051513140601050103050a0b0904020f0a030b010314060703111902100207060b030c09011a0c1203180d1b0b19060b040f060e06 70
    0x418082c10107180c1000510000140248030710300080c50703510b06580e500580a803240d0030084203240ca000014025065001710b003088440c1a56455128101c12905161260309132000c03900460214185c0070800b80d000d514403603a9600a40400c3d0f03180807d00c615400603045c43c0000d42d446a0500a103c034010001d0054896501c4950800c800300301c20180c80c40d00403094080010102e00700c00342c2903000b140560300c185800c103003e1081f6418943d001340b40300113050510b03600e038040300300c403404a0340010111000d83c1010a6100780032400c0181000006041c81e001041810500c0456844007040807401c90885141108100500c440c00400f44a00d40e01140025801800d01896000a107000c007030710400c1e207420500030404110540c00a403044203188642d150500f2011008002813500450130741000d003d5082403d21801c000145141c00410f099100404142220000000304880c1c0103041e2080c88031a0b15004a02c403180c10900c1a055490b418040004010b4003882d80482f00c006c0c0504207030724 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350986780 1250 350985530 350985539
    0x105270a0204091502030c0703030c03050f01060503090a150e071502060705030c07050a0b0a050609060901091a03010c0f17040201050d0504020609040c030f06170a1707120e011b0c 79
    0xc1100304804d40f21180d003042d01c2610f244140c4001e600c00e00c5400d502546507d85400e0040807144a41c5e070070380515141005105016140c03c4000341114220328203650b403603960b901a6400d20101302802040e42c244040803c0c40c4405a8122a41940100c411a80d0640d0303181424640800a07004082c0903800000114115078800c82c021980001c41241041c40d0143c580c0c0c2e0207141045005055a050150f40b040c001c015225000706600310780d044a000d1500c0c10504006003030203606210380c0348160b64074408034800c03240e441c00b13022a041707006000300515000010040e1032040030070216030004441a0807947c010b1a0200002c1c022501079403090704203090000d002c0005d1001900a82e404042440146e8940c0c0e103e01826003207540c29540414100107902840081e119140c000320303c040c1d0304542c1c9010b02c40000030700300500354002d000903010045402040041d8840c0352000b03271084100340420100035030818020f007400e09080e07032030840c8581b401138000c20300071800f8401000211644000c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350988030 1250 350986780 350986789
    0xb03010e30030601050a170903040e01090e0d2001050915070906020304090c09032307090207051c1e0f1704080a08190204090618090b0417040f080105270a02 69
    0x444d2005c5420f00c69450084121f107424141821600500c9940c80000c0074007200d48011300c40b90051081c000c0902c20b000c0034418080d20303030b003004562200f0000e2925400510300610500b820812400000801030f60910b00c502c03d484602c8020081980d5100ca808141824070a03415203007100e230705501460802c0e007408404000360005500400c204a01e4940110100d030f1400104056034100c058070740c1842303003070b12030007803c06c95594041c04c0350600c14444200030a50110344000740040c101c00d0120040e1260000f5204d4103924203911031806003584403150445d800021450346c00000340c440c2d902e1240340f464a04d480701d60803240141044070502c0907000082c00385400305c0d0080c91039200b00d0b50f00c0110018640898200b94054000c0c00c4d2584410012200c001c10240d840030860802488186020340b61486510300142c00200078180c40b2041d40301d0050103c003a94050440390304150314103a5502c5025010b0b00c0d007503420413200ca06000070303010301d480c01c801c404940b02090005402039800c135030200b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350989280 1250 350988030 350988037
    0x7080909060f0a0605070615082a10050d1b020a051603030507020111070e070302070b0a060501090315060b0304030e0102012d0c051903020703180e011205010b03010e3003060105 78
    0x4443d00c1e611040394103050541410070348090b000d044020800078050810214200c0e1280c4c040c51911000754a0306c0c880d035103510522f0103040280e414442c8c1d50b4540380c0111801420305551440d43c031100007a03484039107680445c0da0700280380100e04941102c01d19070301a10603c1e550784801000300c0c03810000c0000550090103241c124411a4054848840c0d880c0910310040e202101c40f000081c0d8009280b44c100030710340e180143c02140d008000c0064a0401c0c001804004007404050050060311070503002c00002078100e0fa001d0b1010418598883c00c00e0726024050190000342135016500b0302a03415900e03520850405609408400d2244400c2c0741500c0c5440249038401895040001c104041800d43c0100315190000101c6a0b80040e0307104040d0600610030308800141802038410460100a60405170301241d0548481c024110403031241803078000d004091a844c9644c16508050000300b40341c1c0007051040242025200e00c1c10100c00c0d00c0300d10081d110400d1280c1407202424000301e44154890b1019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350990530 1250 350989280 350989283
    0x5040c020a05070e0a0f1b0c15090f021002010b0f01030506040b06031008060f0c040308031e1608130201090918150b0f150a14040b07080909060f0a060507 68
    0x5880c00d10314a0b071515828030705150414554902c140b020b0210780e0045128841a1180d0948208040890072210300703050200034504008014030080040103204100074103140782081c401c002c00060507140740c0b52410540d80b01c0203900c24681182c20040d400d0041c000e4001802e002000b5107008030006005400600c001780c00039400030707030b04d02050500d03845040095005014242c600c02001e85449080340c42d0100041c40200500c81001c284040c046480d0103a82c149c03680b002c000ea84903594100c0541035486510b0140c400916110144206206a000c0707001141c02c66076206441e5a59480c140e0701c0003070b244840280001c1150790108510505a030100c0d0804400803094501e41d9115254000450488208100c14641d18030310320195150408080307110020580700d0f81d980103a400c4040c1c81c503001d49800da02c14026010b06200004075801c00300c601805d4071480450702e8843c00d0410f5802a04120801c030f01890300c40003c1032030351411601d54280d5590060441800d1070800d1821220b50300050700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350991780 1250 350990530 350990533
    0x1b0806030307060f330f0b030c0d0213031a0708010f12060e0d05030f07090e0103061e0c030b0415050a0501050c030d090b070f080c0a0e0a05130204030308180705040c02 74
    0x4401d0000d6005440c4554014040341744040402014180c20075022180c4c3d02055804000c40400c000c0300201a09403903005000d0b0380700a407030726222554070020303100e043c05080c114a11a1030200401c40170404000101c070030752548484a9807140320940d03400f0170038000c218200d0400042000840345281c08405541e1150300c002c43c1415451401303d1038440811780e000d0124001104122a4a16030154564407041524155641d00e1801d40c1c1c000d44030b041800041c020342d40b03131003500b04038184040e90740120311400c0100300600e5080c80c00081c02002c000000500c26424508030744111038004461800f80c83c0000c01400503185040019149544048411003440c007080c030603101a00014412600c005000703e6000c1003134501613400900508500d404041484802400c0c410401002b01c141c5a42c410f041c2811050084050001410589941d0059501544d45a0344211164482d00a0000c4034480c0c0c5851010340c0350342c0100e0804100640301c0301803c0c0c2c40b90700c2c20409494580c002440a500c0da00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350993030 1250 350991780 350991791
    0x90607140a020120030612030403030c3201021308010204180b130603052d07090c0e03011d191203092103050712060e0103020f120607031b0806030307060f 68
    0x120b00d102810181080c01d080d041001c8104501411f00d1180c80324084041806545410705554010305404079001003c3e000c181601070303481d056034009038400140b140c40c0510b0002c3c4014004124041c2d0b10480c400c41505a003140c3c0000c0c0c60340140296016103148421542048950030300300c400600f86800d1056000d00c2012000d50f22100700d20030000510b0080e0301400360194407584c0c0079021010200712460710084500d24404901d0007082c0c007801d85900c0ca9010414440d02c08089900204080c00706a040d4603107a030071810703440035410b4084501b03400f20684140740116010990046412100035200401c90b031428911075210b944610242c1b4450012010541030300c0d01180700c1c00111010002c0400e94410a01007107541001086181c420301c413105000e0719040484020440d003043c40003d005100c81004c0000742d648502041c11111640e004aa0079841c19100007000360094620141ca4450152503002ca41e40c4159101842401c0c040e00171803401c8101d80c1e0710802000b07660090215240d490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350994280 1250 350993030 350993051
    0x105030a15171b0105030606090d05011e090c0b0c030a030e10020c030702040605150a080c0903012909101e0503072c09061602010929090607140a0201 66
    0x4480541001400000900399403c050311245481641800d40c41d0601a00b8420003403595241422146128415950000391200c02e241c10340c01341c034805030000e0704d648a2600402d0080a183c0c04060002d020380c0903040101e689000c4140907118401e0b541115410400039084d00720f0194009d10b010440040480f42c200c0d103400346100072030b0440e42101134281c100050712025407a00c0d0240300050502103500a42a107002c09212040d072007011201c1c4103006107107000540020f08ae000f03440c9064009002804401d6400010606003103101c0c494003003404800d0b8080000c2e0a110500c5c9205080942060b00003034200a03107009045007840600850b00c0150300c0c003251a840501c8103400034000c508420a01d4441c4103514000000f110348107207940c40c4101e00704118082c0011342c0c590030440400307002460803a0342000301d014003510540984801d140620591050b250382460750503032500f01041a03180e0b00c6021000d5141c81050310454001600300058a41740d003944e400501549140e4000018501160b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350995530 1250 350994280 350994299
    0xa081228030c0e030115090c09050406140a06030504050709050903090a0e0106141608130e070206040b0601020114060f2b0302070806161d06280e0105030a15 69
    0x8a500c0080041e8480c05882d00080d000510603040da0811030003440a1b200b0f0f40129030294500380f04800101e910784100d04480d40c007540003100503010141080c040d183c2c803114580003a02002c185203014031003541d0700003485440b030310840f0701a80e44070010f0321300b00745040c2c1420702a01018111721041e000c03c0001001c16555850444000d000500d0400c0d246d41c500100942031481218012445400420045420706010300303803545095409215551a184070718501800c070030083c2c0151982c04801402c2c046999000511280301d0392151940110f50350b115001242610010100c02e80c894100300d000c2000c61420001803568048060300700d1040308500041c0a1400140e00c40803501d00310744038060800c1c9a41031191201800c00500107188500b052850b6800c04611150150704100540103a03c8a6904144055800c004014800c64684540c2c5950300f1800c00c424041101d10710000650700380e994050601c003100054140c49050950b6151100c01c0e000e82840440041c0114103040b0203c0c217281e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350996780 1250 350995530 350995597
    0x20f04090f02210709020a050f21070e030616053c130b090103060f2303061b0702030c030a03020307060c0305060f0103021606060b0705010501050a0812 67
    0x6000081c1428460700602c581da07000341e807a00c40b0080307001103c4801c421001403400100c6003102030041e903850000a00300d62a0285a0747c00202d07100001d00e842d0a2000c164841c03c50401c101d400c1c4266842f4028103503215004524610f802d604440b0020313a0702c0741522800004410740d0300300507180c06102d4241060429030704e01e2040b02c07020481e0f0b84410036840c08403940008a0740100c21490034000c0c4102c00b01072076040c8074041c000440014440c117540d2082c0c01140090080c0032032442c1c03141d100c0415411042d14101d02d40c40403c1850300400303003860009041030040e0108040c3c0d00c0200010850000b160740f040314241d030144141c01800d00702e40c40410100310801d00a0703000d50786843e1a403401905440020342c84404050409041c00155070b0b4480c0e420901040900b0010380d140d80303a1080610080392508050a00343c40c03e0030020300607200710010078281f44990002c2256a07240c50410424503014064420107a2100000e00200c0c0500342c020000f060030b21030500c90341c44003074614032000751 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350998030 1250 350996780 350996783
    0xc05071707030c05040203150d150213210309050d030e0603010602150c12010e04030c14010c0201110f030c03091c020c010915170705040e010906030507051516020f0409 74
    0x500001d410420701c0308080700c4202420007140d05600d1810016840c000c445001101c292148549130078400800c1845c0c1c4024240c0310800c1c005548800c1e902c140d00082d0000b620800d03140d1240c0907400780350b0190304160b0700740f6154075440300d00e8101c2c204401c1c040361a4200c20114240302022000c52030a9940c1d4024500070481d40d0300030a403448040e100001c4403040034000c81d1035850705200e401c0560f081d0700c0e40d072415034545010302c000c6a40d560030200c1e220401c0712400340403045003200e00d40780f041040d04032001c101c6c4a90002e2024044104c505201c45c4039522500d400c08805002107992000c2c401c0081d038105c0c55020403184180100b02252400383c0c000340c1c0d80d0000d40c1c0062100c0c0080c0d60443d001c8802080d844450602402501c4001350291200c410038542869034480000d0910b4010b5064a0280c50341c06548c011035a140d98040004000c5800156442d10030107900150741d00e00303803003a00c02605035109003030709000489039403107a441303e50001264003500c1805d02d05060380307442c4201e00325107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350999280 1250 350998030 350998033
    0x3030b06041a07061d03040e0c0f0a0810050a140f060f03100e011202100305040303020c250f05010c122303271506190b19020309010f0c050717 63
    0xa206030b00d06a4101c5040c59013505101c100240001c07041704004c0251401c4070a0301880100d15991244681c11b40d2140980050343d00b40d0208203030045641c409401c52280c0b00704800c211889490b1000c001c04448d15100c0c01411000004450081d400c11540045144d480542000c2c202012584600c0d2075400c220f8030a80c0840041a040200254092040340100b200c5850f02d440d01c031854003ca181030320401c91180a140e15800030800301440b031380c100c0d80224000303030944004880c5000c1c1041c014808400300e040d1000c1404010170402e401c184008102c0d00140c55414202c070003a0740791242117210284120900c020507009408841803100005a003104580c2190355070310708001940c4102070b0001c1310010500b002c2060b0b02a41c90300007035002d03508880840b90441c583c0c0d07040025032144043c42e400c1c1e000881100000404100060240064002c0e0006176081140040700032a40c0380915070354075000810107000f440f00f00b40a00d1030072030089d00038070503170342c0080d10703a2012002540e8104441195 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351000530 1250 350999280 350999287
    0x40305150901050703091505071701150206060a060c0b09150a0506190509181f09021305040c180219050405010f02150a0b0324061c030c03030b06041a 66
    0x81c2881400d50110340c0d82020030580e0103644401d5140242e03000341446159692020480301401800705c0e01c1c222000c403400d030300e1540e1200403800c400100b01c84900e002d031048101050407860900142026100d903581e8803418065151944941880094101011802441021600315482d481d600348100046100403c0c1c0b41000b009000b0780c100403a4a072080340f4a203d20034845031382c03054070198004d00c0410303d029080309a2070a05040c0611451941322820f6081000400e0b908190003107008540203d90019810054100e40d0058610448000345090315003c4203104c14666a4911182003551050040c14101102c04071240480d5800d500e001003000403070304100365a401210741011b04818030203041d0120a220380300400102c050070070840b15071a424210281c0c2c03010414480904554403200310180103c40e0100c0714120160340041c01181c800da400704000742d40002c0d1100e0305525a55940240409440403401400c03401c615540c01001080b0001e2001c0c403000015050703c1725120003a65 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351001780 1250 351000530 351000541
    0x1906020c0f01030c02150c0c010612031e0806040216050609071703041a0918010f030614090a020409170f0c060105010206011a0c0703020a09090605010501050c031e04030515 76
    0x48203903050300b4105800c044507869940e40c0802e1124264100e15034034030441d1600480ca541501a072601a00a90b01e003100000d28890100c0605140e54040d8554011001e00d46900d203c20060007002e42d030126840001140c250304086e4001d0a04d24401c042da100f1054036a500c950500d00295420718003544100c3c0e05009581d14542d0810440c2c500310020b5140514100c1a80d41c40745802400d40041d1601250310085502d030503520702c0d503000c0c0180003000290384030380000780c1004081c04251880d51800c0c1880c0c8165501400070360180151340010001d028290342000041e108110088990024000c00380364030307040c0c210203041e183d04012907460721003444c2001146400d105a005604551203d00100708442c001013003550315080c0400190358070005a0b455510b0b08485a10003500100300000006500140c3d622495980e48600d209002d0303640e80b82c0c0110740c24042c1303004001e141e402c2040280b141544462400980e00c0b1710081840c103140c0c0d2515400e00b08115500903081c2c1e03c1b0300300b04000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351003030 1250 351001780 351001789
    0x90c02060a111314150f0705070821090a150215150d0201050706020f0d0e19020a05040b040e0f0303060108130c030b15030708010c090b0f030a0504021906020c 70
    0x30901c0d100005501c2c01e00044500350f4a03144802e119084404546030460300480e110000d007071103d203038102d20f4195a0401d83d590032900e0340c86081c083d1214094400301182a030004956880b0203c4c2010384902c00e180c01101c100021792200400c40d900034031545000801070300068000e00074001c00d801800164800885041c0c03d200300400120b00c3c0030107140c4048940e910807078004189902131920548802c1c45140220081c032810b00000021000030a010742401802d03089104a11a8401510700c2480961121884803205100c002e40c8401c0c018814011410158414482d4000040011030482c480024040c18007810160088203030300300004000c0e80c0e580242c503442e00408001442400b05030741d6200d04005001c0c5000003001800c840c004580382c00c40c0762000564030f0000505889003da86d030315500d0b0080080401c56800f08451241c006601c11444c0e05698880d030142107102d10355030740e286a56009040052040741c5c806100003c2800b035040384200740e4080c200d550001c0c980c05151100b0007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351004280 1250 351003030 351003041
    0xa0c240b060918040503041d0106030606021506120703020603040b040611044a0106021e07090f090c080c01031802100f020708010207200103060806070507020109090c02060a 76
    0x1a000782010000c44030140c561002d20145165082d59458454650b07150150841c801c940c1b0032080010f1030015410007010f1840600e04840b003e80b010044c03542c0c0d51005a03140c2a0441541101148100c000740740303420701d0322807032542001c201c0c1075611440d203d0317001a2541e00191400e8440310640d000304000c100e4948150b5204c4038040040700d0174186071103510441004c1000324464001d41452613440c01a0f81d0003205070030001403c4400c19241142c0341d0060307503544241310b058014070510036400841003180055084066161010301415818040c0c03105c094203a00f2140c4020a40d680c1c240da000c1480841c405000d4031241c0040c0c10928400c00005003a00c0c8600e41300c58032400d08075911700050f624258001d01c250307000d05000c240414012000e83c20203449038000311640d400010503804004501d945004001d522070182c100c1da51240d0011011600d242c050b000040d440600407503203076806400540400340c41450401a03540d110110201070ba40088402005030b0311030024031640b0156805034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351005530 1250 351004280 351004301
    0x20118060810080705131109130902040f110405091906170705010e061b121c050c040e04080d0e070e041e2d02030d26040c0b0a0c24 58
    0x4144c202d017003800050382e030305a038180c070a6019035074002ca00004564600392100c190005140315605020041c2180180c560700c0e50032031181d0300c1c042ca807401c440924820b001e40e2110350207100d1b00700381c10700090140b0000d02070100540d1403908060350280060328040c0034040e1600c80e4200c00c03e642d00301030403807502c0455000f180c144981c00c40b03d9012a20b4050544849107404000180c4502c0100f00d02400d2004c2e11981c1e004141d0300040c401d408a41d40e0004040002c0075210030803840d5035103560f2160f94084d50068203d83d10041d4040b901250901d406000211036402000440040300480340745000d0f01980311810f40c402e29000c010501200e41c040703041d4900710f0004201d5051040c1c5e251098602c40111080c041742c066220003540c988038107250981280d000c0c0071104e2030700c096031f00900072803040811700c102c503001c28456003414500440301c40d0046078891180ca201d039003415a40180da4000410040c204047c19480401280d1009200041d00c00f4070801004406007c045407015a11200715 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351006780 1250 351005530 351005533
    0x30405150a0f050f0d05010303031e02040b090904020a0f030f0c120c0603111b1c1b0f080d05040b240f06070f240f0509060f0402011806081008 63
    0x241c1c21045070066422900401e40d071a01c50b41d560008209400c09000f00e000c006142894103002008068042d400000c12910614910801804000b0800e00b81e10482c09200c03590a414041c00712141010049540c000340300900e003031041500c0b01c204401800f0a90700a44104840010340c1c01803041c80d604800180221050354896109191a2107055204602c290003c042c1d0318041d100401c50644e0035200468560400301d070080cac1e2002d11003542d6540c407100002c601113000d490018154051001811205410007803038949180a8450141c1407130f040c641030302c00b49070403ca03141c0c9141281c07040700e2103284900914940c90400d92001903c2c03a01d901c000004440348459851802e03551301d010890018412070b54640d40b80d806251812041b0104400108a02034003090044444008088060729000484c0e0800146403003005410607a48141e5003d4819049000842c0078042c9400c1101e52207030040c10030344617040f55124542c1e031410640d400900040e03c404181b000d0400e408400700000c06a010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351008030 1250 351006780 351006787
    0x9090513080a0806210c120c1005040503071d010e040201031112040605060907050d0b040917040806150a05040c030b031e0618070b070f05010203040b0f0609040803060f060c070803040515 82
    0x31402c9684500c00f4203882d03c11120111f0f402d41c510030070400102ca084002c0c01014500c8021017000c2d01c55001402414444e001c0c0a00104d841c2c014100c40002c0c50340c00c2c09054480d40d181510b510900c00d800360069040503103a209000341d1810310402466024400080180c6500e0107041040032500054121440396003501c00380601e855100d01694003640783e00b20005140490100041c0041092450081c03001c80035007501e0580410010140048840c1d01090318240d5444080c040c540f100104c010650080c100307803081c0f11500f0203a1114900e184181800501181608006840c203140454030301030100504c201d04004050a000701d0790044050205550811800540c05840303245ea401000c00003075003c110041071040401480c92800d410070000c641d40c1c2080d00304001203103130480d0000031504140e0702089050030101d6030300384a02d8006280c00d066440781000c00c241100d04818181c0e10103400c3c03102013036003441404074800a003210300007156242d152000740030103aa010340f0009108042403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351009280 1250 351008030 351008089
    0x1e040308370509041b02031306081e070509090408030a14040503120403091e050f032a04020c010203150108090613120908010c030f061509090513080a0806 68
    0x540701541d04402420308689890000c0003041c01000c075400326008030a0819400481c1c590080000c04100b020b00b10300b01c8586498940a03201e580e0143c4109026040504c48010078200c545511508031a091a00d10325041440780050f0607824180c8080e00c0da041c0c000248043c0c3c80e0a0700c54400291640182009240707002d407140b5484e40906500d41c09a60b91100015040503c2a18440090182c1104940452450411001411446005503805200d01c0000300d005850002140d40c500b00306d40583d4000a2000c0030303d4900010440f2440c2e40040c0c09101850040c4028005140700d0195031400140403112040010400400601500500e4220000b400481e40a00c0d4050403650b40000340140c01519550040759001e640764000e040a5290104503101181c2c1500010030300442a10103000c01500d5205088192034a1343c42da174007140b07100f041084054210f402c903070390001c145002a40785510740d498072200c039440b20044130001030079001044100d01d0503086c0a20a04013607030048100c41e1a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351010530 1250 351009280 351009367
    0x31b0105120405031b01020910090e180f0f010b0f0904020a03060e1006080105040b060406060f111c09030b011406040e0a0e1f2405061e040308 63
    0x9541807410184800000a001e1000030811505015940d41c080d515501442c52840d00079003109010302e1095401c0b80c01643c1c0c60344100d5005054408a0700b400e20b05440e40e0b00d48072a642c201c1039180300c00740100c6040703c80c4a0301c00d111040c075802000f8000f0a5000c030480070002d40f8901424010300c140801824400980c03600d44031071040c1da600800c006540540d200310546428002c111682c08070781040e00c00701e41c292042d0440343c010340c030a4614100e151103210410003510614003a03800000c604440701042c05101e604464180d00400c0156042240b100103845a40c003198204000400d500310b81c00c004000d090518103006200e001008281c51044000044480c840c40c450149100c40d0080481c2d120141c543c46610307848454802c5500305c49060720ba60080310700c0c00030812850b504c0c001a0311220f80310742c2e040f2007505420201c40701140d810042082216000100040040c14038842c04501124080005002030350240100e285c40b6070420018201d1780b900d01810034190000011500e80300303540c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351011780 1250 351010530 351010537
    0x16060801090c0e0108070c0f14060708061e0a03050307031e03021c0b0103020c1b040e0307020d03050a020a0624090209011d0316090509061e04171207020705031b0105 73
    0x302441e0061041e11411422903041421f6000902080e50009000c000c100e08050080f61490864040c0c800350381c0d80707440a0300c0d000c1044840640180c6096a070a035808021200c03100c03c00c0009149802294030b0340c0700c1500c0c58204000840114051020340d651061000009156100503407400f9171501e001c0100c4036000d903107811300008000343c55043c424540e81c069015566110200c0003129807461488001018168482d000b0030f00070b514248a142160b5004011079080700e8001e011056085560395088840b6070120740c2c244114041d00b040e4900007405030080880303052124040361804541042020a01d200070b5100346003482c0304002400300790342c1085075052041641c003825041c0451200c042403c220360050b250151615404000c55400c1c0c5a0788881c0c022100b185c115445603456480135154070500c046000200b80c40d440000700020118122440100240d2142c10304001c9903500e42800c0788001c0c0d0754040036030056401807215060030030a03a103402041c0d640310300758000c2510002e403c074070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351013030 1250 351011780 351011807
    0x705070f2304021b0c090109021206061b0a030309050c010305070e1509030a050601140a0e1306060306050903030405010509120a030b1203040b0d0c02011e0905070816060801090c 78
    0xe0030041d01014540d115030581d200076510f0004c09010391000d0103c0b580322010081e441d403140d0b500e4000031071942c0640c800d4a0404201250109454072001c0402c00715401c49a0200100405030040d0010b81100f4032848010324400d0321302081481d054541203007406c9081d8502410149400100219a0b13070041605010304016500da41100246003660314080c410203070903079010300c25194044100700b00020f8890403181c82d0105103140560060401075001040d1103840756020b0410040f804c00c40303101c000d1011a500c19135000901c682e41c0e40e11803054440840798112603400100401c07040c444280102544000c2020180000d9900883c9060081c02410031210800d40d90f2907414080742c42300c060071890110030600b00c0c1c0d2215501d52501c881c50780300741a0150300070300305007038010301500502441c184140007003540c0c180110801c18201c01040050010b840c64403135a140000c840030107220700c40741c501500d00d450341001d0901d0070140940c1410b030f11031503115181c035031090420303a8446081707500d10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351014280 1250 351013030 351013079
    0x20c010f031d070b09040f0605090103020613030611030402030f06040b1f0306110403031e020d030b041b020c010e12151b040803193608120705070f 65
    0x500444200c49070303402100600000c51080f0080411100035000103003141010464040c400300740d04c0d01144040c0c1d83c65110346a08107950304014401484c240c40600619039082c46502c0321559640c8030481659a00c140040100030000248001d40c2410b1081d507001119580c000c143c03a04255031400c04180000b016080401d0101400c16111a48005900c00650300724400f800540d1800590380c403168841c0c84105e000c5040500c0c910400722040100f92504a031347d030080c100059040c982a0b020384802c03400c141c1c1c030981c2d804544102d02040317140c5080d0200c0030390050045411010024011101c0765a04911030b80060044d04ac042e4000150000031088203e6030400f1500d80d11200390710500040c4103c07522200104002c1000782000000c1c00ca14408050038142c925844401500d80e80d004028204104c41101d043c41c0c02c905c0804000c01517500a00c49000900b6542c0311400c1c14403406403400509003c00060100038000c0400101000e8890041407850943ca0800740341e80c01080980d512450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351015530 1250 351014280 351014291
    0x3080c010b0423181009080c0607030f060b0c06160207080601060c03030501140132040e1518040b0a06030c0e1801050702030703140f1209060601020c010f03 69
    0x50070340140070914000741092141604540c101644000600e01088203400d002000038090f00070403001c02c03412254003010340100613112580d0301c040e0403d0f44c0f00b40d400c900c0030854100f00d050100a6284507a440351350010304540d000c2d04140507503145500c04c90344244280807136003c513040421101c1c1c0044880da00441a905035201c240c3c00c05130070703134402d2102c2d01070356000050540d0802861200c1610030b80c7c0c2085141c1c1c89040c01e48103000403880841c000b410354031104c500004807109208000d03040346224006140c020500300740743d0344540c0003404203080340c00c107011500b100184000045034040340c103005019080399101d1b000303210003440940141100404078040c01880d50144020710740003a40448015200c441062807003000b611010582c09881c1c02005d00c140d070610415004002542c090b5141031581d440442d000e000e01001200030340810407803405560094401082001740010b001c03481d92901d1300d030580c2400d8004280b44e0644d00f22070800b5540d40e0b030260410000150a0600080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351016780 1250 351015530 351015547
    0x219020a03080f0d110712080603010e0105070f021c020606011b0b0a050711060408220909050109050f0102040e01120302240610050721120603080901030c0512010308 73
    0x2103208040d440907010560000b424841c541c440300050462110105083c40302c0400c542e041c920511a03000d001d85902e502c5140c45400301e00c1450031a8001a00800100303080e10b0a00109003120019282540031800342c8103980e20070b81c7c0600460495040844600c00e4804640300069220700340181030604107c07050b440c20384030000c1c99643c2c07003403030390850340c510201d2074103a4886005000c00d49050000c03458503902c51440d6440041c0300d500c41c41d800303615117040007030042a8042414000044a0141f00071290204603441c4a202d4016214020000455052090b0804a003404c80c0760303407415203d034010841031140c0085a5000c40c11a80e0282e201d85c284800c60034220b0401c0108003140c031003102241400d00700048440300140c040c81c011140742c0304055010307106503914892174800900c4020050305841d60000d02041514446000e0705184061182c558055011501e503a0001c440c002d0000c40c0029680d6490b22a00c082100603003440303031900d03881401c02c0b80c4041051200601c0500c00040508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351018030 1250 351016780 351016789
    0x40c0608100f09020909010b0a090b090d050a0804030b1b09010e0f030d03060306110a0219050a15060305060c070203030702040f0b0a080718110a030e0a1505060a0f06021902 76
    0x80c161a4140b42d4aaa11004064060340c05408a1341c81800311000100d94100003404640c41d800c826260195414a805003100c5586c21080c1060f5203c440800080d02244061041410007841001565a030f2401c51800c10b1075414040d22200c54810410b0000301c520b40d806046480c0740d10309080c28001800100005840072280541075078050103644500c0f000560150451002c0e40d110300c80c1030085107601c1852000b03d000388204440103900c0000d0001d000d8103a0048000c42c80d000e1000d482c1c90707024544542e2000c01c02c04617101e074541e40d246030810510030b081c0030b4650440211404685484080d400280d503034080c5d200b002c4c1c400c9a035500710f100383c1c2c2c000d54004581e405016149221495485201c1600da603414482d02e91030910014600d03880481621500101581840a903420600c50100440040003d000c50030f100c0e124070300810001c150410001111200e000c0c00c00300701d070301d007000c18848821015480070403044154402032150030380129903207210014402101d80311562500014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351019280 1250 351018030 351018061
    0x91d220203030d020d09030e061303030e030c0603011203030608060f0412032909090c06070b040c0e102c0a110403020d060605100c050d032406080915040c0608 70
    0x2214151000a440d85d08100305e400c02c0300742d140640c403082c0c0000a2001800380510511040d0320301011034901c1803000a01615a240394035001904540c0c6080d0f56030701050182c2e20a820078a001c50b88101558209035160203920042c107114409801e86013050100c0c0121400e01502c01083e078032100e0b00400c070302c80c0f01c0d500094510005052003060819500030400348210124141e03400742040740000b41c000742001074219142c50001d04118501042905c40f01440000600100d444005044d00000e501021901281c00b4584a404003401139241a19a1070020096203940c01c03181062480499940034151a55a010440c10310210b0641c03090040c50450b4411500000e50140d0808445d00501c40b90354030060550f20306448100c1304403649070b000d1b0707031794001280300600c10ba1000782203180c654403d800c96803080e200318040c0c03035014030114070b01207004100d81c211000041d42041040400c4900b0440071001c0080c090084d640c07802c154403002c003024003500501c011b0107168004a0003454070550718 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351020530 1250 351019280 351019297
    0x10623012123070f09050603060103020a0915120b0d0302060a0f0b060d020307090f0807142d041b02061b041a0307030f0209010806090a021603091d22020303 69
    0x65100e0740a161550844412050701d243c0001590000041c20290140f040d2030180e5800400550540d6141c100450195006c1400c0c2c104002122200090520340324000e02c98007106034454581c624003002c0480c1c202e50801b41c03164810001e00321f80d10040394000c04ca60340c00c02060280031a021481d118100e016148055215800540c00100e0207680145070340954001c40380f550f00d600b03101da940ca041a600000c1402100c00f80e4102c0c5400304110303040750086001c129000b9104004030030304840d00f9885e0032010440904000c07900610003d0500c0d003441541c2401030024500600d090040000030b58441c07000380755091144021250b24034500724071041d6001040300c520b015155130144c04c4120352a41042d100315010034100790201c412441c0034020343e44940011382d180445581d92074100050080048e1403109851b41c02c200c00c00d404030001c0d2414010900a84400700c41510380301010740400c001000d08002d000d021411b000c101d4400e0750303001d42c1e84101c850020078410281e00010742036200d00e184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351021780 1250 351020530 351020561
    0x7150906020c0d110d11031c0f0c0f0f02030a170405030906070302030403050705030613030818191a090c06031e0406060302010e01090f0b0f0d020c0106230121 70
    0x1c1e1040030780c081e84c0a91100780345400e4a102c038032041015600450120074030000f0341c00038042e44181e40b100c0b01c14050040340120010585c15141e0b043c40040b034945c080054002148044034242e401e80018503045006c1c40c41c4019460840640e4000740750514028404031441125008601400410002d0b5108018010441e5544068070b1402a58940c024803045940c3c0c0107103c4009040d10700403071001c1c0701e007076000d911207409103483e9003c80b10088010000139000c6060a8110580002000215503030a08611079400099060415505e00c01c805c1d0100b4102040c442d080040801000c0b0b20110307880c80c1900c5158030f0362941400c00000c80385206041a0180c40d103070410060102a0b00802d04490003a200c8400700d01c861001120203094501400c00032003910041044000c6035800103010382100000c05c42d0a080d01d8220396010b80c1c1c030078500400c0f140e442e10745c14083ca0003580035018114402d145000005010040017070510840c05000445010030305800840b8045c4a0f042050407201902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351023030 1250 351021780 351021793
    0x18050105070903021903050a080a11060405030406090e3c0a02030f090a020f1e031006150215070807030e1e010b030309090103111f030506010e010507150906020c 71
    0x60700a2041c0d507588000e81c420312024400403000c480c90001141940e4104000c1c000700c43e403a88032500716910601064082010101214000082c00c0c041c0078000d5204002a40d600e80c42c1c80e0008004552903040707040040c04800c180981c461800c0390101000c06c4501d0700152000088100700d2800c0740d20a000d0200101c02810812440d18590085105401812140d291511b816411940d00c08071550000c1d00a014940300046601d002950707280402d035007070780072210841c2200100b800c000030b01c00c4040e29a5100c280900409083e0218500d5080c032034802080c2c1050302c44015211140d018200d141400b680c180402c0c040c900c2500000208003d090898416010a4245086150180c0548000d0f540780c01c00c000d10a1602008480c01c1700c1b0020102c4d90564256100d1340c01042c0321039903d681c80340c20342c515405241c1074003c81c1051190700c1d03180040e2501d01100007400c0c8510784000715041240030080c21002801c115858060140d903c4400507244580d807070004001d01c03544010003a18410107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351024280 1250 351023030 351023041
    0x60702042c0a060c0903020d02040b0627030d0e010512100302060703050904050f0c070b130b0708180a03050f030a0906020f0d1401080a08030a021e0c0f06100918050105 74
    0x7601c6040300c0c0f14520811a4450070700c0100d40035003603408004d50284490201074003514064201500601d80103048a1520055840201d0403070780c0c200a4511b62120b01075144650b00c1c041c407080c50200c2ca18181440400300300b9000030a544541441108001324030b8002c51405e96090364400b000e5a0b016104940e14007081c00e0240807500072100303c0748181d081000140d400707002101e10301e001e08007195203a402d0660655603803204141c0144125003c0100c41c0040c00468246c16805000b0f0910362602d580a080c807040b03010100c0552821000d0540c0b0107601e4500080c1e101c011141c211440e64405030f01c1340c0758010b201001e05801000a04454000700341c50000b100e1103401000902e47c0150704120410071003049880021092180e04885c0d0025140a408225120001d680c000044000180340010402021800d0151124110600c65020030b407030031540c800300842c1c114403408400405082c608801d107010344d0b8140d401031a100315105c01d440d06501c1011000202e819a00000900403031808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351025530 1250 351024280 351024283
    0x30c1a0a18080904090512030a060807060203181e0405090304170f06040204050402061b0a0204050a090f1e0606090231050613030b04060c02010e0c060702042c 70
    0x80e24080500c5242120503503010386805021400e40da40800003030700b4070340756008010040c40f007034009a64a0280d03007401c1807c0f107880030007140b290180a400140350b03400c2c0003140d46840301d1500080e041d540100710b40d00c541d0203a44ca4100c0464412101c0703450070050341c0d40140303086444c9081d1a801070b08040074040f1000000c000b50069945150040c820084005000e41d61075542c1c3e0942c0010f030b00000041005400d00c2d4203e41c0e84140042c1c045171800368001884c600500e10155107038059082840c2d05021480c0c607000d40794008401c8402880640c885032240c2400c0301e6002402884a005036504003c01e1000b40300000c40300d81c208c0000c08c205e5981e80443c0000e90711070500800701c0e001506403c1251000081c004c04d001e00a2003540050609140a009159024205e2002d141e44088000000110b180c19994400c0d403264a01003100d41901c44d020303013925000d8000405a800403921030449860302000d0740d11031a01140d020130040915040c94001001c120f011a102d0510613a4040e1080070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351026780 1250 351025530 351025583
    0x50d110303180f01050901090b1305031510060905060306040e0c0d0b06100201020c0303150d15090c0504060b1c021603020607020d140405010e12071211040c080f04030c 74
    0x20907501802e510344a01d00445d02440b801d10401c0c08a000c842051104207035600192001c02c10003285805450303200d0000a00c0c250542040420322028013040181c800300103040480100390350f091041d912801c010020b50315000040810303000326500d480701d00e60303181700304018803825a002e80021104040303410316403007400040b542c0901400e094200108058814800c48070011510302c091801c40e241e400040c1200042c0c0301d11140d01954440720311001ca40110095000f080c181c0d5400100b010301c07464079140d50303c100da1202d44100e14001041000b8085102200c9048039031141d5201402801c904105c020b0007120b0301c02d514680305c2c949070380030140c000034068061103a82c1c08039400070305507601c21105043c100c42140078070310b070a100030400c0d94003032807a05028500c0100f05140c030f10104440903103040229448501c00116002d8028213010505650000c6800140d03018400341c40241c10240c441c801c040c1042c1c840c10903400000302071610420aa00e4496030000403d041000c048008444492 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351028030 1250 351026780 351026827
    0x40c030c09091412070f0f06330f1404020d0507020a1b06170601030e0d0806040b0109120b04080705070306151d010e071209050f0c0a0609050d110303 66
    0x100d030407030000c0543c9800110140c03880c1074541c440e40740410603a5030040c0d114030001c007200c4251010155000141c1140a541c90001c94003e01c44082444030311103c1c01002002c0c00003900c02c1e80e0820610443c1402201d09090700c1901461610004140300450000c0c0312348894842c8240c40c007001d0000c0302e603001c079407401254010907012a4810300b1901543c2900842d10560010170b00350000c2141080e09405d0907940300f60305040c00240c405e805504541081120a22140040c0c558810804189410f1084c40e03c044400e107800d23400b460900d85520400700c03c0540181102c100da800080400217a83c1c01c40c1e01c860f81c41402d84441540d80e281441c043c024a00912800220024000c6408025201090607007109507815454507441c2c490f12104581001c0c008070f0420a0100710351144d05040c3c02204410341c07044c2e0041400410102112b03041144d0006040d1040c0d462610400000d0340c00300b550010b903081140c1c290f5121a03a440c103c0c1c1680b10344090590540004a05e1600346410841c2080100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351029280 1250 351028030 351028043
    0x1204050f0603090607081e0a1b02010e060a0209040204050a09050f0105150a0c060b040c0503061203040f0605160b0406050603010e0303012d08031215010801120803040c030c0909 78
    0x1000d8881005041d00046444640c0c6a000c4000110b03124032404d0100d030400400342591031101d92102000704a01000c80300f0420301510341707a006002200c1280484c1c00c070162480200030741d5106903062600e800740035044210300c3e40c001c901d014541d60780b6070440c0c004180003802e0608bc1903407054078102801c0e0880341c0c075420b501c020000003482e01740360345484500c070481c0708c100c5e190100050045da042e07003003805c1c1540c0c0f2607501c24400049480b03038030482803c3d281e86e0315180d0b1030340382400811000400605010240f40c00900c000c000803c412507142041ea5028106183c458011001c40b03107503a40c96a41c00760440c004c07441030005101980d8010ba0040e030043d030083c000c44114203100e42d640c2c88288241d040c680c11a0010154184036800400c01c00c01461072909100c694600009141d40c024443d641e841c00b00c01c1c000d0029405c08030990000410007801d050b4043e615040d0b005907142c0b240c1130007500095002001a081003801c125020107143d00c8083d4186158403070003030310001c108220086541 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351030530 1250 351029280 351029299
    0x1d0405010815070912150b1e12030a08070f02030c0138090703020d090c2409031115190504150503010320060f0c010b0103061d0a0c0e03120405 63
    0x2c01d101305003400544100d06070f08000744540341d86940c014480030400840c1241e640503811010754810380003070154030089800010101d010010880540507044560780280d200300119014141c21001240c0c0c000300ca82412003250000706026411481402110082c41d441e03c1d040403d40d4825283c00c1649682d0030806034042e02034600107460102e03035404056800340c0f441c00091000f9120340c0040840c0700b58942c1c00320300c41c039080c1e0342d007000b82c41c03103800041c00b0341258002061420f082002041c1043c94030b01d407080c852803440c1c445040300310380d0200741030040784010075144040f000d04080318000d18100d0b012002502c0790481c02000f40e08103005a0140101c41c141c401c0090f03210b602a20305036900114001082007030702801c02c18900e40b41800719040842072110b580280300e094007030011001c2c034800100b00920030100040495601e90401107039084480200d0b140411040242c0f680301c000b0b60781c00680c441d40381009465850300d0443ca44e82c140300d5560300c0005d02021002030701c11031b80f00303942c040c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351031780 1250 351030530 351030541
    0x6040c09020703080f071b0b01030303051605030a0921090f08030a020c0f0d08040f030203070906030803040605071e0201090c0f05010c111503010e0f01090513031d0405010815 77
    0x76072164980c042d00180c0e903070002c191858600c0780490340150ba01e050a5480070021004400740503040c1505903080700300300e4010020300d505805800c0e8415166804060321040c203150150982c0801b6060800031340e1ba07801240100302c1004505584000d482c81a1150203002003c010068802da00514510b602d18680004500d080042540c0110081d5000b4181d046c100b4802c1c02118440b682c4170300d900c6102040f001e40800d0310300c00100b01824800201741042c904500601d441c00840d42d00c150411807804008001007001101075a41140d405000030545407550315086070601602000900f095407400c4415085a030158005240c003813240040e0401ca0b84d0300c101c880304501c814071885010070103044d008000a54001c991150801c0010b2205058412050001c0ea19400907000703100c0100c511000d0081802d80000ba85004181118045c070441c541418840c00d6004180001001d211040741401d4090040032100d400c4800c0c0517004100c950f9642e071405680c1c031038640791611610041000b240c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351033030 1250 351031780 351031799
    0x2b06030812060f0f0d030522170111040b040b091f0c06050112080a2007032d02061b070503010f021917070f0201090507030302031305091b090312070506040c 69
    0xb5a960000d00c010b103510117070b8606980e1035001c2030700c2c02d1110407015100030119030707807540301c0e80504401407040d06c281400d00c11550845807105480080d9900602c1300700101e808280c1158155111841103940f201003490225400c420b180741c20700d102c0a02c4510100003241c0c0300a0341000680922400d01c4140d9880d04064505201ca800c043c01c100400c10542c00c105000710421074a0740340114103c042460300b100d4250900352940c004460304480006098140521240700c401c49011a18010304800f499074006044d038130402c000c0800040d042990001d042c23005001541c0205400b400034060f44080241c0c1c08020340c8400760102a030b25042c00d802e0b84040c0f042c09480740c6038006926000281d01d030302d101940d41e1500010508115074a9280e82d900180b4140302180042d4401c1d001191100c2030000c0b10420740300f2035013025001d01104c0003007003541c154030550903000702880c0c2d492940da0384816010a080a54610368802040000070700303142040320001e0180e100c0e5000b2220000a0303903c03101d604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351034280 1250 351033030 351033049
    0x60302031519050403050d06270c171503070611190c03141b0303071a090c120303074508070b0c01060504022b06030812060f 55
    0x40d40550241c891036421a00d00507801c2e0300b06003550300c15103981034024222010394004a6007200024804034180e0b54148040c01401e0261060665900070303400c4001501070b490b100e11440100f455100c200e140c6501d0701501d80d480458a82e8000d040701c03403900300414440b035500046198000c0c071036101c00064007417140125010000080028069282e00e00d16002070440080a0a42c0c0f10120a80c0000000e02d80e095070307059840c0008041d113410380e51494510390b03010858906d40d0190f0010006000013800b00329110f0604040790b80c003800142c482e040c80c02c1c60026800c04003500300020b001c540180d4400000510f200712480d946400d5000c907032907040100480711020186a51381038250240d10748900302201c122402084140b101c61a90361000035103007a1065221540355200010440c1d4045804e02810018010645095152000400b00980940100c4040d40300900303c44010658844880e044100290781250409440380e0000700b04d074200310402c0e100a48a00c8001001c10341a04240208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351035530 1250 351034280 351034283
    0xc0406030b0411040b040207060c0801060f020c09100801060f0306050a06052d060d02090909033108031b0c0f100c03051204061b03140601031d0f01050709090603 71
    0xc0141c40d111591250a02d140c200381c4160f03c103880d240c0300d60050f145d61014203101400f840340440c915901c0d02c40a411138206800c16410091000c00c0c138549107800082c400e1006000740d031034070103035514504021903da4150f017201100e9401c100c0700040900c0e02c010079405490042074204050344030300c0c030901c003110bc407481000e0300a244d0140c41c4c0020b84010701c003560a01c150b94203030006103e1040000e03456034402294401020390108400b40c02d420800a080d83c005941d9005520384000e5021b1144100d82c1441045801c2034009552812541240c540100402c3c054045a484604110492400403c100b840800c540305a40761701c811443c206c0b440800703a0f0005030440122042010702100c0d80781c060b1a060b81480700c10080294800e1990114a1189008050000d000328007000ba0a041101000030a020507007400d4001d44540000041140c0041c001d09000600c910007080c503031100311414048003000d000b8540e12810498040d00310038800c0c1100da0701d03a01c40e1b0351a102440100c1e6070701d010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351036780 1250 351035530 351035543
    0xd0203030114010e0d0f2102010b130e160906031403090a0605090d080d050403020105010b07031706010c06020304060b040c110a0615050904080403050c0109031e150e0a050c040603 79
    0x115402c103940942240000100041e142d0340301407400f5225900e0907000700798105d6540c422656103481c66440204220000320b0300d03100034408103000c14001611400b0407141109495554400705101c628200a541402c40c1d0f0340c05540b41040e5188003d000034000b521090301d0882071101501c5800002008131091440e0042540c006581001c4046030150000c0c60440d070495001001400410481c5c2c01030303d10743c18508404a650325080c50300a09541c2c06911400c0e0b0242c00303000e0403000a800101201c0049964481402d417a6680c0c40120340010f864117026183c0c601c00401d000600107190016a035a5000b61018419544d408108407918101c582e84418103802000d40c3c2e0f800180c1319041040c04010104040f1025a11040020f80303148040da01151a0301d8002030420400106100402e41d1000c02d00384900c5184c61511140f02040c0001c2c951017112960030748030010007a0919500d444540100420481008a0b20307500390f40780f0341ca0405a50381e214031602a825450280500004e5aa0020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351038030 1250 351036780 351036809
    0x1c0804021f09090908040f0e06010c1e061d150702150a0e0106180609051e1305030a020c091311060318060a0b01110c030c100c0c15020d02030301 64
    0x5410303400c0400700e60103000401800368030005402c0038034018103c045000e40301542d5110b207040c2d900020300c0d80c0e6601941c0700d070110b4400c20010340e03000301a9141c207076041002c1c04c8520b142444200c0d28000c101c1320041865150070104e07445040c2849618160850080c121240320401d4200c103041804202c50344001079000b8080a030742c15502c45500e5400c8400c000000c5907041e500c211950948840c2d4001c91402c1d40305105080000c2c0c270502034070000b015010020086400c0905100d40d600f004002c0c030008441c0e924000c105021050030844000c1c0c1d402106980c1c58400000f402529405c40d00c885a100c0e80042c00442e0720352046d01400b00201c0d5000307942c6400704010009009050b00000c10180080c0c10350540054000f80038401c0d1071283c001c6080001d1101c05400004d45210404054101294041a072109654030001122020070500304e4050090018105046030503130810000109003441ca8140019006210902d01440b60220b40036902c01d0030800c41c04903130300c0c0001d10501b1800c484c80e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351039280 1250 351038030 351038059
    0x60909150a0906150e07090906150503070e0a03050f0f1f0c051b010204050112090201080121140705100507030c02130e06150f01020a0804090203060d02121c080402 72
    0x26403240c9050b911600c40414183d0800c1604951a14280d1004005070b0010041145290303008010b00043c0a40c0501000706034100000384281000d06c041c07090034807070004046049140100ca801c00580c90003000a8001901c0389000350310b403c0c4034041c0d20741c1c5204041c44581500c50200f0341509641c030190020007007a09100044d009001035032400002c1c04130400800751100310003020f00c404e555114002696482c03500c40010006640820686659460115405e005030380c096002070443c0c502d04c5d50100b10400e106034508048003592801410413100450001035580042940811280304450b0104560310600055517140320300100100003410024141d070051a050000c00490401d101c40040c0781e456080c1e496250020075510587d90301000300c6001c07a01d00c0d241d1803c003004002840940f101070401d50798449180281c2c05420034080c0c01000040301d645495181e030102503001002145a002d40f0315500e41c542c441c030900d27200c00400c01d610034820300303009000c1d86008e6540603250044c1c03030203807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351040530 1250 351039280 351039301
    0xf010302160618080d1a010509010804110a05060c0610120203071203050904020301091e2d0e190309150507060e01090b1513050606071218030b06090915 67
    0x1054403105074854040c1c03504011500c948013030321120004250001c0d240107403144200080d1b004d21402410044100000b010a907440480560000e9011220385002540240007494500140d0050394119a01141100031214000ac0160150402607196600540c40711000420342d03042050107500340e48161070411151781142c0c10032240f02c0c042d16150b401d100030507000400340d1f4420f03031003804541c0e1192140b4100c100c0030191800d01c00911801008200d0000040000449501011403600008400352500104e06501300b21101a10001529003a89002c034170386940f0103070750030b068000034088000410450518a141002c0340a01c0e1122400c0c481d407580c030702c4050300841402e00d240e55211404140010501d2031500e00400714421150003556054091101004a0301c140300c2e5141c2c00c0505102c41038030781c4022915215000146e100d0344c01031545042c1c4142204a40c06a61800e0109001084c05203c4801a00500c41180c09031125200c160b5403650b5904003846031450a102d410204024040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351041780 1250 351040530 351040541
    0xd0503090307020a090b030606040c020c0d0201050d0906021905040303020c091f06050307020f011401150507080a0503010302040b040c0807110703060e06090d090e06010f0e03100b0f0103021606 85
    0x151046901e0b1885650100d001501980c1c8404400b54071072181d603089150034090f1a52007032041e0350401400340d604000a50b185c00a03880c041c000c0700340c40701c61401d692003007044403800442c429050040a04c240741500007584203485ca4200e0801003102c6243c0244964201c4007140c0c0c050f4020012220340c1001c006100f000500b214103c1600b241566058041100b8480f000b011551280703a02ca00e020200a03060004900700903400da49407a00f0900f01c1079184503203d055a80c0d500c2c070815141c00440f010b5405110b080005000032034042071001845603c500218180e0b13200f55000e01c403403081e100620099564000d0190042540c5400151300c0b41d03c0b4445540c280c0450400b01d40510741e49898200c200c0300614007100054000008000003c903040000e03d40ca00068982040210310782514044c0654000c0c21580c100310f4520315800006124003442c00100030700400f5241181400b01c0010300910340040c0d82400b90004103132810301580680b0036203080c03110a0700891081c2c42680e60b02c0e0010300c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351043030 1250 351041780 351041791
    0x312030c11012f0909010b090303090306090610090c080604050411040c03050a0629090607060e060601080a020408340e0a0e07030809092526090d0503 66
    0x14a02200c1540a1000d0040070010b603188a80004100e001d00c0320b00501c2c3d103031114054145002081040703242e880d010a154112044204015292071001000a003507129403150960701d40b0a034401e1041d42440442c581307008002c406060380c807441e0344d924400e090341c0340420800d0200380c00c0000110390341042c2d00115446841038440044008440d80050101c0340c451000c5c100203580c803420081c44025500c03a910207001a82502e42441d400c1896952510070451380303004060f00f000c608060143c548800355207109030300502c1440b0100c2c09082c2e4030b5486100301c1c1c083e400160000d0200d01401028400c55007070b40c0f4504080c0c9001c1340345105000700e10b181a1001e5112040c801c08004240c0349085a143c05424152100d40702c41c00c0c140300e24400d441a69907041d4031500418000c00002c1e003800100d68030054159503180c5295030b01c07902e420400b1403052140b2a141203040c1130003422030344001610034140341f050941d440c9044045021511490407208045a41d002e560300c45000d40c0100b0107154080c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351044280 1250 351043030 351043037
    0x15010f0f020a05030f040e0112050c060f07020319030315050f0d0309080d05091005030c04030201030b0402070501091202010e0f10020c030f0a020106090c030903232208010b0a0312030c 81
    0x142c01e40d84403407959001460301c1c02031540c04101808414000700300f581c010310110740100030764821604c40c0764942d150342d40100d120b6080020f44042c581c100c0c000392440e09400609640e00c0e1701e02843d040328200d40f4540d08900080c030309210191100c202c403506005540d009040140c00a580c003040c0003230760300d0485040d814000e04201c0024044c1c401c00c503000501d4a16650b141e01c0d030143c2002d0041441d0b00c28681d0091010500c10003011200ba0303029501242c0d02442d0210b5220700003004074000f4400c008015180c2d50a288141c420b00005c0030a2048020750359000b042140301c26024a82c0700c0d032203155440f200e85c018138060401d441480d000340c05c22028180c2624030380412100d5450580d8040440900981d46a010401138102c5510a8401c2e555542c142800711400035078000f891680d400300c0c05409541ca00410a54404c480c8080e03a400c5a0039803020408030811581d0b031140180103200384500c641c2051286141c0b030070b000004004803948501d01c800300c200c0c218029400380090f01ca0031402c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351045530 1250 351044280 351044293
    0x15091a06010c0605041101080702070303140a20150c12040f03020312010f05010305070806010507031112040b091003110f09010c020a061809020415110a0c08060108010515010f0f02 79
    0x100e90030b84038180c010b61141a1031804406c25000141109800030310714000d64100c18001c0011a030808070401440c0c90607a0060794815584000341c445095520345040c8211050503196500ca90024803c082030f606002002e1f0f4030350360a03100010780e114042c00401101c060001090004610704801ca1803244a401a00d0034400c59040c401107042e03007640f2041c07006070b8110040040356018403505070072404600d0000c18520740100068254490000d0040c10042d500a100c0302c070100600c00605010013503114540d407595515000500c98100300d004078800c0b1440303040e041032180223212303c0b45400c402c0c10040d170816a03481c9103080b4036001032007941e0602c11032503031000040c0d40f9040c1d070360050220340d251445c1030007420a10b00008c030115041050018410401846aa45004030099a02c41c40d40703003901010819155144c10301c0c3c85070310010b00c0c2c000344a5010075608000308000c0d05981103100200f180b0f80d5041c11030b1907030500e421310903030110b00b01d030388000d03c0e240c0300d117205d1230500b21280101c480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351046780 1250 351045530 351045533
    0x503033109050f010614030403140a1206080f12070201090608090a02150315030c150d02161110020703030905060304020f100e01020c0d080d2f040315091a06010c 71
    0x40d640300b100e02c3c05218076118010303c8582d411130380c5044184440085541140b03042d03500034007020039000364030f9a88400403d040d412184a8003100c0b901c07901c0060103019a5a498000b41e40d1801c451510020900600554194400007041542c1030540c050359511420351404605499403603014001d160b46010b03145140000d41c84008109881c0b105c0d60040c00c0e52854650041c45c01c1070300358582d030ba10a030400f170801c0845036100f0014a1000f00307d055025503407030b12900100020b200d0031174004080d4003024242c106000c28000c071348815400a0340c1c98241e031a4130b004c1c12625042c090000601040e4000003d000364100305c0040d640c0720303101410840c03800c5091000180000003046415001aa0700a0340c400c007568144101602c0e4141034462914203a2300b40d46000140c007440e9085040389a403426a01c4011046410b078011005c010f2000b8000c051380c0f8000140151701600064418040b030f01c1d030480120742d07039110b0b9884254000e190000e1421449071512807070140580b41604202a1440800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351048030 1250 351046780 351046799
    0x7020f030309030d1409060c03060a031407090615020a23191104090b040212190302070609050109030f06091104020414130c050307030e120315010905030331 69
    0x50142568100841e11082c82d441c0070070544111745403040c40c0c040c0810074000320703076000100d0355044018903070b045072683d44810214481011591000e0403d0140d914013101040e8003282c4601902e07900b00052140c0c40e00c900686594280d4054282c0059002c901e030400810b4005001c903204802c4076450030740c0c04404183c0c1c185071120705d0310303c07034481c1c100709400d4020003030025000012043c00751403e12040d152515941000718000f4406400b500010000641a540078490843c428505c0c0c5e090a0011041d400c00035540d81d56406100e02003021110003080d1507001e803450204503a48040389160103082959403801400c07051a08680700e00011762254010307605c5001400252801100c2c41c1c038600c3c41201003049000444051003031091500320079064050748041120741c0041c8a05000c2403030038810304150b181001c0c0496001c5407807000301c00d0002c001001d441c191044034091743c0e5078594540f5002099142d10410b01048100749002100040c100700849001341c450b02070b510780440305680da40481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351049280 1250 351048030 351048037
    0x507210203030603010e0f0a060e070306111206030a0816051006080c04050c0703050906031e2d0105210106050414040b0708010b0304020904230d090e09060a0507020f03 74
    0x94000d600702000f008240e007800d1143c240d070003551b600108030301c40300c04201c1a20f401c40d2401c0a406c207911891020110081045094011079004104000e1910001c58821700b54000d82c1e04070001221080c04605103140c00208001401d80240545152451807000c54004040912007241c20b80246c071401480088107100d8000201224005403002c0c500c024100400c90380b0092403441e0250081c040040401c1d0300900390703818100d040c0c0c0c031155241c603091040f402025443c0325009402c400402046203010981c1001008202d0392180b022001032030b4003004680b98024000d0076003082d082c00e51040b80e007101590044283d201c0200000314640c40300081426154200034010181010009020411a0307554403030383c0c00100c0c2d2070049200e50500f018483c40e80700150001c0e1191814201050030f114400c511207003294503a80c019034002100008481c2c84a00360ba02b50000300350020000181040c1c45101d46210700d00b080003400f01556502c203088020a00035040c1c000b18814003a000460a800300002d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351050530 1250 351049280 351049343
    0x703030909060b030c0318030408120910030e4b060906071b06020f16020f0f01080105040504050a0507090f0c09030305070b070e04090b1b070f030507 66
    0x400800c94144030a007070a640d01503211122124081041044440601c0b040d26084185004408804075102c62000c0c0b0f140120340003411640503003041d0036102c04001b002003801031b000b681c0e4144c103003d187c00305804941c80040d10501d50b80112240080c010005401c0390303600c440c00708442c03040c40e420941442101d610325110803c0c14400d61500341da034000400c09036500c64100030060040b882d10440040c08250213100d0800709c031201030b401008100300c58054a19404005894645550603829900d50315021001d0aa000c2e40b507140d0743d2012303414124441c400030070307040c2c45501083c0d203014248001020300a01c252160b00403002c0803400101e0910111000b032080e44004201c0e001c6c0104520205c07407514425609202004404000090f003100544252640110b40c2e0809a91120000d9900c810095102a481450500340404202030300440d540900214198495500100d4208800ca40b04012015000b0300030301c428000004d10620003070190300d00c00c0701d208102002480c217088403a03988401c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351051780 1250 351050530 351050537
    0xb1005180418200d05120a02120f090103050109020906160512130906060207060c0809040603061b020c04090816032106050108060306041509061d03070c090e0318040905070303 77
    0x380101c42c50b440741070505620804480507454814245c1d030b000d0b0b0f0381c8955101600b40b2140811681d04150003404405900021414000d565140002d40040d6a80c0101580f9000c246040004602c2114600c2034580305180a004c1902d00351018000c80030606649034101d8a078490344070280c125007015400740500c450040480b180b40d40c1800f00140645d4011b410000441d44003000810240e42d1105541410941001c0d0f40c0380d5071007a00b000b08024007e00d0300007403c000c1c02c1481100b0101019105034a010200da400e0780e084541c00d00401c8255440d1000251401c01d040c0301c100c0803141c0c0300ca40700a4680c403d0500c170044a0800844040031280d038800004030b19540d5408000c0e0f543c0005045611010440142519181950312208100d0141064482d0349a90b4081002000002e80c444180590030079281d0720034481c54915143d807a44004401c5842d0311407070700009591451801001325080c02d03400a9410400056003540301d04450780040b940c420744484070741c40070509c00e00031507010314001d68 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351053030 1250 351051780 351051803
    0x160c0603051602060912210711190c1406121512010e0a12020c040501090b040b01050c03030c0d1b1205180a0803042103050a0b1005180418 61
    0x2c004002c0c05000031030707040d0341143c82041074161010540c3d50748446148800da403243c0c03503107071100d016040d100e81c440c4181000300b00344140143c224500513001588a0110b8610703510030081502c207605840ba0060801640020500400a6a80c00c05107500d0020b440541010070703055404800500c2901d2203514141082c0d10009581498520fa804101481000340301300300c204529075640e0321840b00301500903040c464064808078420b101c0c144488000034028031170b658540c0e501c0e600400303801c01c0c654031540c5459030054855010380150b0381201803002c080c60039641c070b8800d042c80c80d602001c117062500751b032685400e40315603400900e032000321140c2c0da800c0200b915103031400080b1000584510700c40180180d4600d079401f0005140d03800355034022803e80d02ca881d00c0c0b80030441500b11500c82403038020840d220142a0b949940841c0c415441480c00b4400d01c801d0506021503402c0316660040000c904000c0441c8124502019912140c0c0c068000600f0b288052182c60040407048400c03180750b45c959 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351054280 1250 351053030 351053041
    0x803072a030801061715010201021c0b031516050a0903170a0810050d030309060e0604120e01052820010b04060f0506120c070c0e01030209090f070b160c060305 70
    0x807881805882c1500300000601e240c440c12401000c0c000f0310003032881d4039511b0003800c564400c0d01919600c0d4109008015518054540e40005c1c08a120302c00d07010f4420071112a07500303100600c84c0c6005600800d5010182c0003204001ca52030f600076045d503030901201e03640c000001031044289469030400040d41d591243c002c15802014200c010303145030b0018020740e40c107000d1591404c418102181e81414001001000743c9050800307010400283c5145005120800003031045020302100100e1890f991458100b5140c401074900d8060314501c0155080b42c0c2c1da8020000d551400d05010040c1c15052018a41c0400305102d50030800954010007903035102e04e000c010a0600d030288001514115208034070f881c0c100008281e0074000e202005000040620100302150b047d00d04a600c85c81c2c00200344050583c40701803059500e907081c48124003031445400020901080443c400c000c0c420a0360181c6511854001582c0f00d07500410340e00002040500d200000003440781072003200500d0345440116452404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351055530 1250 351054280 351054287
    0x20708030a080406150b090409020a03021249020c09070f09060e0d03030903090e0a02071a040c060e04021c0501060f020a050309040906020408010c020a0c060207050604030803072a03 80
    0x260103a105ca020074a007040c4070303102e1b040080d68100f00701a500007903504030f03600000e803002140d5480a900841214800090b541021034a9a0303001110100344140003a06554000c0b4814060180d52102c0b03040307088404600342d00c4107a101c180219104403880440000001503903503005542e074601045800908441031600700c5004c00c002c0015040ca401c0b020071103004502500382d000e4000b01010f03503c83c042c004150080c58514041d202020920031103140070040c03400203501240054402c01c2480d01407452030400c00520310b108075400400394292a1503d41e054545201c0c122045074403903000d0044ca100d800401d2641010503903c2000424554500cd902a00c0d0004031402803007190440c0b801c09001c250300004590056800f0f0354006005115130070a04001d001e1900f2803c0b1341d50038106041111a40011000e600501a11039580f28640d0b802c800d13a5121000d104481d0070040511040004c110070714061540032101c1c0c107141e050700d80c642388410041181201d500d003d02011800c4907052550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351056780 1250 351055530 351055541
    0x100305010501141e031f0311040506060903030d110d0c08010e0a1b0e0a030f050d08090606010c03180e0103050313090605010518031f0f1104031110020708030a080406 73
    0x104002118030300071050358480290240451103800804002022400a06460907a401d505190389a41c540c4c00c0e469161400c030b6131505648d0f10703108030300b41070110300249098411904200760041c0203510f0034155160802c0903018840800c08103a40a00c040e00f800d6205000e41e1040400c0c0e5a542d810030341c1030040c18400f85074094190401185880d0200341c500d5400c1c6200601c0107100e040c2419465400301c0015440500d54200070610f5074117441a10401400007680c828121a030303220a070507603448020b400e82c2c0b004100d4000e0b001030034103003000020070300036698817106020b00840e119115491b20300300d000000c020f03482116144c0c00017031491651401030468502a01c2120b0003804520b16103000280140540c80f03510ba15221030800c41121903508101c0d400c0702146a0350300400c840103800140004015128104c3c52035402c01e482403602005590132141607035400b49540214072207000c14403a9140d00038007810150b1058541c007040c242010000780011805030f50f2521304916051402105588 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351058030 1250 351056780 351056807
    0x1090618051c17070b13140115081b01023703091715010e130c0e01060e0102070b0706090812090a03110c030a0b0901020906030108010f140708150f100305010501 71
    0x100344100d60020704800085c0350003505500b803140c80040d107070802082c40b2800d00024000c0350710b44106550b80c0c0b074104601c4d00490b140c0d07100382c03054000103800c03d2101c040441c0c52140144c111428071010704080d1b881901d1480e1010610703580c0c4441c40c2c00c1d1f031110003148280c1540030403100c410803c19403e150f000c1c01401040d1002804d12040b080b010b8150808041c000c0e0812035074203100280011021b00c1d107005503a90400c41c1ca80741c1030b0b52400c440801d440217014010001e410294080540c0d400040c0d003808461244103500d1810700103845d0440140280740f4210f81500d0100500800000c943c0180d500441c0050058040000d083c5006404004130040341c01e40341c0c204210720b201564001c1107800210760454441c48481d40e80c01e10440c0244541e140716035005401000100c0c01c1d0380158080c2d0103041c002101048030003070070020380400400c03c40e00813000500940005100d00e02005121440e6030004e00b41d110203100c40340008201040075411000000e5440300100090b40c1e209a0000500c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351059280 1250 351058030 351058073
    0x30d050108012301210b0403030b030c0a03080f03060a050306040305030a06090c0806130b0a060c060c0318080f130b12010b0405060901030e120f04140f01090618051c 73
    0xa100d100c941c010000f605119440850000704502120302c0341c94001c80e601c456100a240681d4a0a8a13018008164042c0382c0c81c0a403250b1b048143ea01e007804040c580903250008501c03402d0904a03180ec2c1c00b030341c0c80241116000700d402a00003d03039403410000d91b070199129464040d00c80c5480410401102d103240c0c4019240703410144a4500107401140e9950084016911000785007a241b0f28107001d81100500540c11180907100004d842e58400700780c2001c18442d145c10300c04151800b1084094030844800405001a40c0406c4000100218028050304098800741070402031b10101204803640d081d8042858a0400158400d048079840102805805908006030500342810085080c034001e20361518107160740d44002e060082000c0182a07810300c102f4400075134990303510078100c1003600b06c0c1c07040d0390000100e14807a1400f45030048141819800682d5043c1c8040c1c6051422074031002c1c58076001d10108072014002c240c0344c682620450701c1c80d001621040d6180242e140c0602d41311815008044070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351060530 1250 351059280 351059321
    0x3030906161e090f0f0306140702060c070309150309060c020703080313020a030221100b03060f0711060703060f14180601200a11090403140d0608030d05010801 70
    0x12150403102c038450448010341140e40c6910007000a0f00c400915400400068010410000d142c030b41421080c0300f40ca00c992402d00c80400c1c0e210090304110340c10346110000d038110600180402c01150042c00e40d5a01a20b400c1052654644a9400c800d401c89410400a500d03114207000b4000c050080c501005944d1000340041e6241d6115006540070140446200d8110f0f090080190f658101403c406540c00800d10449000c81c02c40010303001c61440103501c202c1c01030f24403c003400c000920495401c0e0102030003030041d95903507910004980c140200100184880d03c045800a40c1d02082854880d41068030001082c40c2000828203200302c0f20340c4030820250b644600c59556864100301e860203120f4400301d107002c548620300161000012104114229101c3c0214440c224000041c1202e055004000080310085000305004c4800310440d00580490088a4445069000c060003404c851601c10343c0060310a0315840242e0030341e40044100b130200ca4031240180304004080c42000301e6101480e407030008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351061780 1250 351060530 351060571
    0x5030a0309090b03030f03091006050d11010e120a030f1e2309090f041208040b06090402030f03040b07050f06270c0a0e0405071721070c060203030906 66
    0xc1d511a50285515882e01d64540303211a40b020000d844403451211040c945a240240407240e5030302e9015954031102d4242400000d0702d0a0000202c03884d2038200c2806215644000019904824141079450b000300540002d40380140c0140043c001c200d200ea42c48560725001624010005034101d401d0716401450f032040e914005030031010304038500407405419040006910702d00b041500945414680202203002001115039502c05610306c40c41c03207008150031680740c00c207040f03515131002c8a00404079600324002c252140307881402d10343e021344000c0486e011000c48103110303415604607900400380306001003000300c104a03040c032002516194401c0189070310b1614810007051b03040851003c0c0e2841d41103c00c0c2402c406c80a000350002040c024004018950b5240c80519460000304c6054889000b2040c0c081a0a0715201110681d10007034002443d1054880d0307002850110802010140c0c0d00d401c100c241c001658425216008102c141c029584a107000c0703102504000e4000d2079503507880d03900481c2c1e90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351063030 1250 351061780 351061787
    0x9090406140f24030a050d09061403040c03020613050604090c030e12030c1803061003050d03091119080f0708070803040501020d0e010309020a030b070306060c0c030f03140d1505030a03 81
    0x340100905141d29401250383c002290a02080007400742c102e004040c15004480e42041c2164115123055480310780818504d01d0740310040c04242d0b401045003003840001c1000d0b01c1e00b00b01612040503034943c00d010b8540e4590019606500c60b500020060b41c94180a44a071601803041d608640310000103090340e00000245444644401480540d1084d0f0120b4121029910b00100c0748401502804503155030800001040040c840c2e448200c400c4c0c0304d68241c1d0b0081740d03c030380a11495207500800c1038050100050802c0743e1407503e80140740e261a01a04005800314041010000070080203015048043c1071641290508800e604800501d0740700708010092643d00042001c2c0e0004586001501d0810303400049003d48a001c4c00650b01c081442004010300041c189031a020300c426480401c115947d0b050142d80241d541c1c6800781c803202e518402000480c545402a2412034405d20300801003550300b0106803034580004181080b01540d0301c55a029900d0750030032020281ca801c8000303000b500043d54004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351064280 1250 351063030 351063061
    0xf230d030305040813030b10081b1002030c01060e2a07030804021804060c0f110c09100f03110a09020f19050f0c012c12090609090406140f 61
    0x2030400d035807800041c0501a0080c00d030f0700003a0800c9001e907007056482c02e09059203130066846044203035120b4030009000d400060b651300c8001c0d8820042845810780e50802c00c0841e40389a082041d40000c02c058000c1c49030a214090240c0264105205c0d1800c1038001981001d200c0040480c003e505115405800d061400aa4200c12f6161030701310041c0e07999201045c1984e5492507100c2d845140b880500082080c0c54205441e014400c0d079400c4000702000c0340c00c6903088881c0e04540c5064126002c1c03807046040454505a014002c0b00c00c028a442d5519010341d01440b040c1e10030f0380c2c44460003500b600c00e8034104441d0402002e60345070a42c20103a0320004031020b88243c90201302c0380280540829203980c01442036403015005407800b80d894501401c00d5038040c0c55090b41c803070b2079401828000c0c00f5007084ca00c3d814440e03010000c024510664041041c40d8203500c02203800754000d030300380711850959581440300c9214a10031070300422294407240c16207985220192022210001a400304085180141800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351065530 1250 351064280 351064283
    0x507050d0f020d0e01021206090709030b100b0a0215010e04020906060306010c0b0a0e1c20010204050d030903030e0409120e0f06040f031a0c040b0c01150f230d 70
    0x480c0d040001c0850000c0c4030700c03840400709500708940c0702002001036010300740c139103161268407885a456000f04500b40c2d5085a07280040f41d101078051022503104140541c1c400d02100c0e10017060341e220308042000750000440000180c0c003000100303010a441050940c010200d08504c11510b040550000d441914010300e518010040440010b000c0c0e8810280001020b13005078500c10769040028001d0007400340318840641c0c40c40f400c032070010b0901a100130950b605d0070316034400145628003171464101914644140102d0341d020702c0701040360303900d400f0082446442511540380c1d662440c5030180101c81034130341040c85146000d250308046000140c0c118600e00d854070f0071100b042c500000155200000c02c21054000b0404200070815080760382a00043c1c9024000c50100c4901d03201550035030045c1210006e5a06405010400802960304080c00150300b04100110382645000007018a003a21a80a0b0021904a61080101440030b6007062070080300403148040e480e074204080307085421038550 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351066780 1250 351065530 351065557
    0x1110d020d0b0406060815060c0d0f111c110c0315060117130c0510170423011a0a1a1803060c190e0108130606170304090b0301050705 59
    0xc81c14001c0405622015898034010010404c4a440e41002415400221151032561210500c0c090301403406c2c10035100d03146441402890b203207000160807500d0f03031206180d11090100d2052006c1c80c0d80d005011101c0080710000910081512140d00105180c0600c0196100c4e82c1000c0700c41d84060300d0101d10700d480090080c0c04c018654450000403904600d45d07500c40400016010180040002c040303000e4620a8000c40d040e5132015141d9040003c0e803001cac2c19074200071841400380c5000300c1010310403459015001e11410740200203085605240f5182e10030800c201e99540c4c07803503421290382e03940109001c0e000642d0b24040c06420511910039031415405000004100800c0c40d5101d006010846022143c018060310042c5c10102a40d6000d50880742a21000e41503d408000b0007a105002900e00103105030346081103515201c03040301004513801000e90f0155200c10020503500f200e5401e05081d540c03000001c6580e1450300c1011001c40e280c1303030200c46c480c0c0d040000b4000c0c0c3c2079122080e074102050212 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351068030 1250 351066780 351066787
    0x90408070209070525060b06040f0306050a1407020a03080f01050105070b0c04091e0b0402071e020f0a1d060301060303140309010b090a021210030c1710060e061201110d02 75
    0xf00251801d028220400d51022400000440407000b01d00d0384d5012076200e0f03101406a4400f90341008618040d0340944000402444010800314540d42c10091300440055000180901e00e405000c2841104464460159004215071804c15500101c1154400807000070001c06504000008159200c0c030302e8041e0a101e4030742c01050040b64170004803070052003803c2c0d007001003030b40074024801100a50700c0321254040c070305078251009041c00e000302e0742c441d94001c4110030710409038401e600e80009600c40a80e0480610401200542c950055002c05400c0300e1500702c8440d008600c41d42d00e8000028489da0107a41051420400a50003e070500100e820b000503054881c0c7c0c40d840498010320b1100600c9500020745c500f40070403203846034001c0c90100c2d00900301a409680e540c1d1001e07540c903c240b02c01000701042c0c0108206500080c001307440c0004c83e04041e1454103800c07545640c16212240c00c064461030100f4240314061500c0c1000d8120f030180392000340011038a0050340c1d070040c050000401c0381c00381c000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351069280 1250 351068030 351068041
    0x108120d0e060906390f090a180f0905031806071218060c11100507020301110408010b011e1b080a0801080d0e0a0902130503060103081305090408070209 67
    0x15000380e8031034400701040340c020f8500210101d540e5070b401d03990901443e54030352a004240740500c411041c900b10000b042d51114158a407003100720360148080000c0c03190148001445c6036181c22142c0020400d034154103011081034141c500c100c50540c8c80d03442082d450202d44000041c004002c2c3c45005511b86100d900145201d03020810340e00c940000200b105e9040c4c9000352540d41c1011002c03101301e038000c513120801600c5040c103440c14120040081c10b240c0800c010040c49140119112071516001e282035818140543d001c2801c0d59500c4208500d9154045414810b485007445441015042444c104250038108085000c101080106034010416058070640d640110125020710899010315030b0790750703030b80880390080c0401c0081c000d20040d40a0341c02e146c1e07410b81c031494801040f40320082860740f0b62803a0200a070300951004c0c44800d002c003080400010710f550140521802103000311615079446180c00201c409403102600b141d840b03001c800b402d000105100e0010358000c40d5050b01c2908281d20390 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351070530 1250 351069280 351069307
    0x3021605060702240403050d05031e010302010519050c0109060207110109031703062205100e0709120f0f0b1009020403030e0409020a21050708010b010519030b03070608060f0405010812 81
    0x101d0700047c0882c4594100b03030250350b60100095105603614030002000c450700c0307400c1e000709203c2131002038001041480b460b9070405100d181d440300050681861071800983e00e00c0c650a560300351106a8103d54003040203428415200c19a00c440182481d11881990965440c0e1464850075294000c0412000c400a0304c10384030324a40e004402200a041c041241760580801c0107454211103103a2004452580011040c0040520304c3c0580c105032207080c130036401c1490750740d0034001d04078081d1141012031800d00c1c0414205e0301c0740c03020240103015400c03c42c030b8502c3c200042c01486900c28041036204100070008203521021442c0112401c440c007080c40700c99030000079403815081d0001c04d40da040006001404510303541301e5243c65071280050368840c40d943c02181e4221002410300902241c410404a80c410001c03082600340c3c100d49040001d5a40c00e0200030a00c1d000498210700c0c04a5001c006200d10382ca40034104075016401201e0522007981444182c0e5116041040480d400501c08140c4a50002c0d9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351071780 1250 351070530 351070537
    0xc040605030a0b090f01051003090206041208040e16090f0503101122090e0303040c0510050d141e07091e08191a0112031404050d0302160506070224 65
    0x400134401c1c0c01d542007003460b1944a03c000c2c0710f0300e0306c62440c11004039003060007406041e00c4550001c080d103052a2906000003149485c410048950000c2000f000c142c21855100403406412f83c4039910742031b034541200180501040b03420245018202001c20081913400103800c00b0381d4172150001081d0450711f1950303001c540c01030032495520480a500b40f03040d01c462102c2d800c0200c8a8050040c041101b4100c481c82e140c0c44143e40107031050601410a0049041042d55580041c1c003500d000e61511940c49121400c58141245c1d10b045c5d5001e00e01801201000900400750340010220060001d040502c405440d003810b512071007040c11f8030b402e01006403800c4001400001c04070003042d100240c080101e08001e010041000311072003400d5480300301d044200301851f18183c400000d5030004101550301d082d0347d40740007901e501142801c20080410035071186070381184007500c6600104414151100409080340d1181c0245006080c18440100541c0c1c414488009201c0d4204244250300c2d02d00c4d4285a0510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351073030 1250 351071780 351071801
    0x3020a0e040e100b12120702012a0c170d0e010e04141807050d0b100302100c06140c18040b030105100305060c04061403071e030905010b090c040605030a 67
    0xd10b84100010b0300c0300c01042c00855001601410000c01d01107908210b49490b494a00c8076003a400b801302119030080800c0181403003801410030360000c07954103c403846011120721041104121001144c0c082005002511f000351819203004810132030065441c1b65120310b00100c103801c00c01140d501c50b007640d0058481413488940900140070000084682e641d6004050b500a104450041441a07501102085200560398000c11040d0440d9041c1c0b03840840c020013038880040218103800020050b91852490b041c41080c1792034030403083d401170038220212401400d032175215440b002c2c2000a000d6000302141d05040918134007410850213800420000c4c18410000da4056180400b4007042c01d4628a8020480b40318008940207a40c40c500301c41c0c410301aa06c180408100c1030034000d101548500051940141e1a103090014401000726030700d01840300c44176040109030780c1c414441c2840b400380a608101c150680e0a404d0758204294400310340e100d54442c400070820088041440d24800d50009003859 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351074280 1250 351073030 351073039
    0x21040b041b0509160207050a05010e2106010e07020606030c01140a03140c0306100c0503071e061a01020706090e040f14010609140906041106030a020705060411040608060108060703020a0e 82
    0x5144c6600741c90700e14040880d002001d0312070113000013000e00e01310b07880318103541c01a55045003890505060003000c0c001080310b44a4074592000c500c0c0146403c0141d18000e107000d074510a007070306003940047d007020700190055010740c0044c2c144000701c3e40c0140c0880750840300070780c0c0d090351154090707000c43c000e2072914a8889521580414406441e14000c091805000203c4071350107c900c03030000c00d407076101c00690014002d80062003000d0204020410000400c0084070b15100c503902c40c0c0d581c000403100201034000c9020107151380d15013996030421480001d020a401c10008050610b5a20301c11664010030041c5410a050144420410602c22207070700140d07244000e20440d034543c020071018081c420b414181024001002401101e4002038036801030303130040410040400e540b010320025500040c00844031a40812010000a00400c6210310541c0034041c1201e0300e050036002c1100b60b9140e5170149001d0303131140006101000006c910650800040e00700140d9035903030a901030b281c82403201c3c0c1d070942c030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351075530 1250 351074280 351074299
    0x41a031c0513081e16050906150a18050f0a0b07030e0904080a030507050405011b02031603030507061803050a050702041d1c031104050d0c1a21040b041b05 68
    0x5142c40010361824410003141941c00072030707501c04c3e2643d0701c403220301c4020012401d0703810410640c2032041e00c2da80c000342d001e07004080d0003102c542e021019a100703081020024814100064401e02e81302c800c0b002412040700d81007880090300c07000070040c00d05800703561400180011000f003010b006440180843c00e0141c50b04145150500f80841c40c2d401002031071011a040c6030004070603500c0341c000c450a80700705840316001c0c00300e0000c40040040b15040200d8147c07040541d03100202c00046940390041d0b201c0d5a40700d0380c41643c2c2c5400b5043e40c512802c0d00345074a000c10010000650448162084805146822a2610340d1800001d000d451a0400210810a050000440c000c0c010600c5800845480c0342800b0b501002c00080f400c0300c0f0000142d00f6040e02c20700c014001450589400309c26280a00d0210030601d4840208083c1100e4002c206c0002c000005881e5445210030400101446079910f155803d51620780c407909800c54008000600050800c220b441484030854080006410003030460480e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351076780 1250 351075530 351075539
    0x20030606090a0e0a0f060f060810030c1806080a0201050f031306060e160f05091002030c071508130b060d0206071b05040b0906130b0d140309041a031c0513 68
    0x21550410342e841c4c0e085a08101c02400c1242e064041c4004491100c1c94071310180e46400e4044804c510050000004980100300005c0896102138104010f009100c40c01c012a00d10300030004103ca00c0b9620015541d00480088005070780c0000688010365450755809941766602c140c080d040b1041309400412940c90040c0108074002405441c41c800c94501c01c09068013800c00342c00b0380d2480118089800024810000d101050030000e5045c0741c41c1002d801240e007082c5800d510582022590780083c00d801c03020a80d181c800c1e9600c418000e03000742c1c80465400f010801d98444000d01d0000911039401500c0d6080a541191240e04c02c840032140c1220208285188142c20500844400e22505102d10b003068184103440c58004840360240c2c0f4001c007819600758412452101070005e008c101503104010001000105015040b00100c6407040740145580e09000002c2100303d6002c21401c00c551200003521049584002405480c80c7d103021100c0900d90b00052001c80759481500c01001a5100c031417000107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351078030 1250 351076780 351076799
    0xa060f020702041107020a060e130501290f0301140a08030310030c0503010c0518010309080307210605030a0b04081e040801140903070308100f1509060320030606090a 73
    0x140c52072080380c0c280038203c0207044c0800d40c4d00a03003101950000100008001e964080c44c1005400032015105600c00e0001300b42c050205d44007640284c1d00320b22180c131184044081c0c4060710300c0182c4410481030800890120080c154001401442d1140e10910b10601b442e548240b201c80042c10341c2d8080360703580d250260903009501414030040300c40c44010706000c2090300d018050000503100d5070f9241d40c200340a04c0342c90562004022901c5040c19590302c0c1c10360110341908000c5201d5103864550380c00000b6071030780d08071a018820301d850070759a141c07990030712031650003040144802d80c0203c521a0365840d24140075a09115140078404000081c0010300000b070489005482141e0000008000f043d4110138500309684044925480c0c0f0742042100348006030050b40001e0300821502008a505504c52090713038a40540c41d0010341441006800880407d54440c1c000b02c0900505e203401c1c0120f140090599070600408241040580800700005515854201c00d0b0f802c4800010b0504d512281c0c4d50044a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351079136 1106 351078030 351078037
    0x80c032b0f061a1e0a0c12020105060105040308072a06080c09010e060711060a050301031110020607030f0b10110613120302090d0c08010606020c150a050703020a060f02 74
    0x903d1000c2c0d016000d005c2070140c0d40c03242c4038441c40c00d081011000400100940c05c680c100010401b007642d001007aa4103c80c0d2120500d9110300240c50030347c954005520703100c2403034070705003030302146558190134000100c038443d803150601d0351178010b0b10160920804900034013042090460040c4c2c0d007807010042c46454051140b080501c40100001001c40e4400459100002d00c04001481800030700443c0020698013207a020421051114002c2e44400d0018014010301da40c0e40c243c01c10313041294204842c0c010b0000e08490070510350000280002c010115444464401d4800003420051869260019a90404d102c0c0d20010030001044019601c04a00f958000c003860a50b2070010f1864580c0300d028110325400070602d2407c08100900c2c100030348034414802c2070040001c00c051002c030400c5401d030f400c0d649071a0390345401071b050036860003144d1003000b04889c0c40c01400701980216980034 = true := by decide +kernel

theorem cover : BRFrame.Cov 350899280 351079136 := by
  have h0 := BRFrame.cov_init 350899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350899280 ≤ n) (h2 : n < 351079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
