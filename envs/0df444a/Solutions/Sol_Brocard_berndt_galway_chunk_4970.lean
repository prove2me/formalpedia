-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4970
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:30.668693+00:00
-- url     : https://prove2.me/submissions/1af82162-fe74-4de5-95de-fd5396cd3cf8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 893705035 ≤ n < 893884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 893706285 1250 893705035 893705041
    0x10f2c04050607080a0c090b0f040e0109021e1c023912071e02060915070c0509070e24040602061009060e01030b041707030f080601030e150a0603050105 67
    0xc070208150384102c95680f101192985e80e140700200b281c400300000303401301c1e5031381209101018007a0080d2220340758000109282c40d0b140c80c40400e00c00e000b6800218026000121005c1c0000f03000f0100206101c000000c50402d1100060040002d64a411ba002030345c3e400300c2e0740c01e82c00380b0034407601800b1900500d10f6502d050540c82c658481c4c8101102c030928502c5003101004030610102c0442c0c070550b80140c09928050422600000b050181315001c1e82d11000600c8039544964902e491400584a200398a1f03030f68252700e00d000903140b0f801d9032005204590010030042c215401032400205e0703c1003240c500d03445240114403402410072191441c0380040b00801c0103c0c040380c00140740d601a0340c0d1518010403660340c80380301806641c1c0b28003801e807410f10b0580040002882950846420074443e00c151b4183d1443e40314081069009458207400203219103c1001d8503e03005120b03107400c55001c0c0307020322810300400251955030107803d000c02d0f5035003614000926007840d5940000080c5038040000e00080c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 893707535 1250 893706285 893706293
    0x12070308060108100602100203040c08070f091103011d060d1b030b1b19020709020d1a091b0a050f0c010e10090507090c0e0a15030e06010f2c04 63
    0x10800701d903036a010900b480085840c0c804611250002c0352501da00601f03204804400c0003029400c0540200c5004200c0700000c0b4003604140240805403914500b0030400368a031241c1d0301c0036500364104c041d000100810050144100340b030980c1c0b0500c084200c1c258455100c1c03001058048681d41400341260780e000007804440300d0340c821140226406180e0000d501d899884901d41c0c1d98801401868080c201048000c281c2c480415201c107000302d6a0040d180115920404a0300341c2c0d003c400315080300b542d24080302c203507a8290410104501002c0d6840318940ca0100b500b103120508461000142100c00b0031000e034514810001c5641003083d0908150b290000a50514080e218003805508213010b40300002d041c680e594814609450b80100092540500d041c135114028105805400104000700313016a0303003a21928040d41c000c0c4502900380c1c00784c2288610050803220744200012141d0880c00041091142c4e031001b580a0341d01840c10341204500c15041246841c8600503040c020000e0001008180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 893708785 1250 893707535 893707547
    0x420010540080c09010b180a0b0d0f0e010b0a06080a021b070602010c050c06010905150303070c0e1302060f181f020132091e0304031106070201120e120703 68
    0x110311035030403204415260f40c1081160142401010300d803003005d000035210909942e001868226015003200c105e035460f41c40c180490350000002540441d2a8040000341c000c071071142c1400c13410f140b4000c210068440c00003401c03402e50b07489603104000d1480081451418594100c0701540c01080305400812a05041c680c0c07110401d205100240d440d0100301504980258212442114410050995603080c40c2281c801060054803000e01c10b9480d03412b03c44540c4080000740241c44c0117000b400c80c03ca1401c98840c0703508100500c5031000c0410b20386840c0060311a0020b942007050702c01c17512503c03907210380700a4620340304c0103484039484400b1010905a0840408907031060702001d40c001d03c00507003070700e8201d600320045050349040c060a26055045020302c031020b81e0b17003111041050300c08660749485040051800f2004190650f000024204100440050644e8140d4415580d0600b000065000a80542c188200760741c0c80c141c48102c080300300c0c02c05000c00080b001040c0101d41d2a01043d0038020f00c0303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 893710035 1250 893708785 893708789
    0x70305150f011208030a0b09041406060f012307050d050706180804120515100e160503070c1a0109290303031603150b030420010540 58
    0x500005503000c5218a154142424140c40c0035080380004901d8595030000da0703034401040944043d41e078040190b505d0341c070050710ba402603000b03402c5e584c101e41c0305040590a00d14060045031080000c0c41c0b4414042e60414811113048002c1c8034018041081070211800b544501800240907002d8007900402c0150014040c04095004030350400401e041e82c4441d034401d01d207105020380b1942c010701003000303680703002c2420444c03180c4a0016540c070741d084880040840c04041e1501820707854a250184260002c10801640c02180700541c01c0c084402660090700b81d102c00781900003001178240c40001803040e032060500e0f80d1606030080d018103683d18031000009201c000c2406e15485070a1610340000a40010b4040e00d014004014510b941ca602c0c812111a0f08828180d02c04c1c941c1b5043e0b5603c4840c100d0043c04010408202c81550300e18080c5030101846e411302c2003001c0010000c074028892a64400c0903540c190105c0d80b2188e9400f0b15640d460181c203520404103148200350240c80c429030034225202841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 893711285 1250 893710035 893710063
    0x115080601120218130c11031314130603080318030f1e07050f0601090f0e060106260f15060703081501051b010b120a15240305010b03100603022808070305 68
    0x11140b254002255207a2083d2040394278440c4000d80d0074480c80c24104074140c040f0741e00802501c40803900007501d00c251109a84151902c010201c100135050030300c101444580c20340440a9498080c6400300c2003103a00903e010300301c03034051565a007503420451340102c807951900031045664a07040400c60a568850034040d0520403411300c4455080c0c60031b280034207043c200c8080058101a8208101124442034544c201070003010008030400d1000308007c40b09000340013864060b0900c0c5010240c0c030303242151720222180035040810251010a40c40381e00950001d0402840d0009001c050004a58500501c00d003032158207040e071640c461007941580228000202550b955403050800b212071529043c07001409010042c1d001441451b0044c0ea5004084000a80c101d03501c4080180c1c0c400350001c54030360001c54507690b4070009640b042c9020440c01126684102060200f14110b50201c1c1400505c0c00c4014104c40350b9402001d41004910044400703000414211810750741d60b0b080441c0c0c0c0e08040e0480c51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 893712535 1250 893711285 893711297
    0x140711030a050f010221071e0522150507080d0506040b120a0515010b1b01020f07150b030c0604060309032a0b0c04140d03260115080601120218130c 65
    0x701003200c81400040c441c0100d510351240c500228440c42c040f40424101c8c0104100d0f00b0008220039044801508407607402003a0740c441c0160415099100c040d0031600c0d95402d02005000c0000011006421110300406101c00032500d519440702060142080e482c240368005c201d03c0c0e00b100341040c0043d00003205c0e401101102e0b6000384142c84101d1481081c00340d01000442003200c03146c80c1010304d8002c15100c01e02c07c0010f190044580c500241c07030b000100112984004181000d500c002d0a014030240040120083d10003214900001030aa1090f4418142403503100c003100801c1c103004100d44054021800c0c1960501c0380b8080e42d10300c504090300000c440490481011501c0c400c020010b0b82c041d116040d030511182c3c2c101130100070001d02914004c4041000b5000f2040c000380784600e00b00342c0042c4481881c5860350500c1c252a482a40350304d0500200701c511001c0100740c2e86d0050031041000c25100340166242d0900c0c41404911040d65040c0f0b03008404441aa030381c450a80d801030419007510760f1a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 893713785 1250 893712535 893712577
    0x90c09031b01020705150d020c210c0318040906050c0912070e22051006032a0506030c13080f210703030f060909060606080601140711030a050f0102 65
    0x307840d10000c580c1d61030041c1d0100d00240954141441108003c054040c03a0b11304210303510001c6c030180c0c0d0001d01c40740d80c1da41101040318a0a0403440e030b1224940800c094242c1400441c10f81c6540d00d000d80300b50702e00d13151403100b440340d000d0b1a964015521a50400030600c030030b10b0300c1c540005260380030307a030954040c3c940d100d8a00800000811540103484113060150000d8403415004000071003011101c043e0501011561400103004010000e00302801d02004104185541020805071680340d000c00580c88003a200b406d0700c60fa8080c050001d40b90206c42c020b8a1351100d480d40b00d02800798205c5607018006100010864410020325000c0742c0c481c1504565090a14120074030309a000e4065610b9056024040540082d001b0307040142d10984c7c0309000034169607589844400d80d02540c1c4180c1c0d9030b80d81c070071b42400483d52200c3c045030b000c0c4007824422022107040b04440740030300c03401001404411410590a00aa400303112a81081c4d400408840380d071020650a01e000358000c0c2d540040b4144d2020345 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 893715035 1250 893713785 893713813
    0x30504050c01050913020f0910020a02090f04120f030b06040305010b04061208030103080f0d050c0714010b011b05010b04141609060e090601232115060d0209090c0903 73
    0x4903284848050b290750f042d00c0b03003178034448080d400c0300182812440c0d06200c5000152104c5a00219900059004006402c01c9005210240c40060040e6083d5001d8604106c0459440400d091032100707a032030030b500c584811000440042c4544480d541d0303c55400600007080c80815000b03608080e400301ca003080301e43e81c0c44c107241000500c0c0c0e0350004c0050906000400100d0f0706900904110241508000d01e40080041d00000b00d40d800c4488490381000841c0c95020b20103030000190807814450001c210302c8501200107410040ca070200c80e078014109460351410013000303401001f09a2400f410500801c0c034010400b480c420300450f8040e81080301d50403680c150340d12410462089405607207812200181040038840c8a4000410b01410320403260f00c0c510b00303003403e400d115214074134800041e520795849124001070b0302ca1441d510150104060244070340090070807001c03044103104603091a03540c06d0300c1400b280a80500aa03465100000108000c44411900001c1060580c102c2c1558466071880711 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 893716285 1250 893715035 893715037
    0x14010e0307080613140114040b10050a050d02040f1109270a0b041b0518041401060807022514030610050405060111011505010e0d15050c1603030504050c0105 69
    0x110300041c1d9880348010564005a040b0f00104e00c9000341c2c030164520381c0601d034850035102c0503100700d0031010344081004244201400895000802e42003071031441c2c0c1c505030006d02c009006000b0b4034840c00311201c05d2007c5540d554042420000003140610035541681c1d1310001c1c51f000428410f029241038941240e400107983e9031b6244129203212103400d1034941c141c02d40e0050004130b0038141c1150799600300ca4600545c0c050103001c1c0328519a250703561201403102e1001000c8125854a00032030034190740c80d00300c581101113181910598644280c2a030755041c0120303d4480400441b81e84862129041e03482c510a4441d640165010b800443c2800c1000000b419070354101160501910311141e18103003c11f00c0d1036080b01c0e400040c1498581402d41c6201b0000b03003196810405000074038100c1204202d50f503044148c03100400001c0b19500300d19044d07600c46441034008540760316811079441b00040d04d41141802550340c000090000e82454a5941c44c02800801c001c2d20103136428403840742520340c40d601c140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 893717535 1250 893716285 893716289
    0xf0e190b1806010e07030908070516050d0201080c370f0503060d02120c030709020c0c010801050d1520030907090203010f05010c0c030f0c09060605180907170114010e0307 75
    0xc00141650b80c03a04504c4108200302410041c20503880d03882c0980030800d108040c0411500680103004841c046a0682c5840c500070f81c0868007a104008070700c40541e030007030036a40e4003614100006a0300c814a4440101c011090040c00c80d40e040204003a040491024494501444440c0c4440d00340440300c400940c2da07400200c1e803a07588100920b100d407005041599299800400d250100c1e1201c9032400c0c006400c00c0e050f504120801d035070106140701d070044c01f00a45a1040c00070300340301c199941403e0105140d500c44400180202410420310358103400c040e0310024245c4081f2801d807005041c0c03c0c004842981c0180c44d0126107104035400885c940d1160300c01c0741c2c105c2d1500d0a107600070f14540700054801442500c03056034000d5041d04000013041585c0c0014290522034205416410f0615440e1070071a80180c1201040010511124401d110041600011204100c0d440c0409540e8590101c894504507041a900c02148000004111108560750240c08900340c8400c0344070004502031503614a0a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 893718785 1250 893717535 893717581
    0xf1b0a0f020f0a1a090102070e0609072d05070b09121e0405030109081315050306040e1920030a2d0c150f051207030f0e190b 55
    0x904a400185400d408518420300e0182c001a08513548460740d05543e08a00c14071408201c0000b2a1690781d03a060040002500400000c2c4800d418031001150f102e20340245444107200300210001450301c0d40420001005103407213002e081450841400600a030450441282c1100e6110f021401e5404081516030b00208030084281c242600903000b0701040b48000350300c588120042202003000d8400303029074040b05004200e901e0392606070100b1400c0800907540310b070300750b0030b80000303655030b401e0344441141d0b0001d00885000c10816030811031181404000810480305480c42c14150f01000003000481000c025201604041402802d00340b41d01c81c4281c10000b454201700d0124a02e5a20941030729107404604940e0031810030030142c0ea544100030345604490410680d6100382d00640707030300080d10900810035140a81c18000a607101828005c4081c00031002c1c5038580d45883e84502581e440002020b84140171280100070348000751090703107009001900d07884090000600e800400200200d010a04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893720035 1250 893718785 893718803
    0x9100207030c03170402030a060507180f05181302060d1e090501061406120405071a0c01060603113a200c071707180b03011b0903030302070c09020f1b0a 67
    0x1940c0c1c9d600c001d220007010982801900420700454894803118074001e051058012a070072410702c0200146c00d04001d0505c0c20030b0f8210300401600708525000c103607a040d8192101512b41c0b1881d6000009400300030321403041680c800143c5050214280c006110948c01382000704100b0b5128204803030121061314541e600440c1c100402c20482e406207800b40d601500402c181c03800ca0343c960314041c86800d50700410701001c1e1804034018031018428031501c0000d1665080400651218145591b00c0e80290001c11141c460901048a40d9002c0411085241c103040c13401d10402c0101990054002d0054a03806404000c001948014042074813003101e83d281860350040500e240b40021008158060084009060185c910000381da44402820a162019181c1020440700690320600d030071114005034204104072450700649216070001940341c25280c051070b0240e9034400c141080050840300340d01c07900d601c3c0d20000304000c004121801526016101d040b103400c6201c2da5220321551880c2c600006045210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893721285 1250 893720035 893720053
    0xf0605040315020c0d11062809330609060e0f070c202707050901030b030d230309280b040302010501211a09100207030c0317040203 58
    0xb0390074040607841c81d001c201615254200e4115802c000300e2192810114286c980c2410003d40140481030707100d882951080354001d00c51100c0001c605482140201581d0b5550100080c40800070304da19900d20700040103020200514102084140e0380003000c584245440800301d10814280a401c003200d98000c0c80302c040d51150714007003201c16400307003c00050101c039020002c0081c44041030080c43c510000d91080200c1701d820140a0b6060056842c40002100340a0202d0344c00016041907821111a1420a441d071210b400140d00030f007083e4a049505201d00040204810f90084004c1c1c0c80360b03000740111500060340010840726001c141c1c0c00c4134079030304041e40050003804a0380320700c01729515080c02c01284003d15200c100a07401c007036906400503510340c0018401c1109000b90004011200340c3c0c0300fa80c8600790348590030069056070508140702003400104403080f40c1000480c8501c1070041d0115502c3c1c90503d006001d40003040e90480100709011030f5000703e01c207905481e91080707030060090a1040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893722535 1250 893721285 893721293
    0x42105090901091112040c0906080a1502030702010b03030424180603020904091a101409010e0408071203050114062d1b01021206040c02151317070303060f06050403 72
    0x11391281030b403541813801d01290305d616090170540c1d800749000742c03000020030b805c002e2000142c500d107800401156014440c10030000d41c40c0c00114007100d1070154016144d882d0f201c000c0f8090082000c1143e0f03d48004a4041403102c1240030b2100300c0b1894000901094480c03035020b886d4001d40c000d0107185079035084d1041085038000d80081101641c0180002842081c41d41c815420710741d01040700001010140401003002681d689000c041d2210945400c500c82da0500010251001401401407003030390100450200724200701640c030120303031203850459000c0032035400400a207024814646c03180b070210f141100710b051030802c031030f1030005060920119040920b8140040348040c1508191507904000501d5088104800c01510800c000700260343d519034a541480120405003281c5c1c8101d1920b080304002640010342c2003010520710a2405450355600944040402140d001800510f11000c2050f0381985110082945d18801d40b02045403079200e505001c4622513034042c0301c02003201008284045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893723785 1250 893722535 893722541
    0x3060c070302010f0504111e1c080c0f030307080f01122003030a030c020705120a150b0402030a09021003050c030106110a020a080a0309150906050f09030604210509090109 75
    0xc14068000400c0d0400003c420208a42013102c0a40d6541e4407260700796028500a503009180c40c60022212841c249424002104a1003101c00c21810708000315201d000c00c2480415a600a2a45070a4441030400d10307180613180d0340111000000204503d00090074840503240481c107032004d00d09084060344955540d034441000400c0100c9215080d03c4e180b80c15554100010281c0074040d40d80450354005842002c0c1c03404c0d0064001621626070030700b443e00a00340020395042c045800a690701e0389160603610720002841070100ca240c00a000004006001c401500144900391003990042c204070b20000041f01100d60030340311080e4000040004005c40c504c01c03948006aa462a0142c5150705d000742e00081c0b4210450748010701c07a4000c004e803d0203158001051070300400740301e005888a4198020000e124014500600003401000308141d030340340c1259801e0b600b0846003d021a40142803604122040c22076a107128400325010040c09082184203005684800201412090341c1c5e9003002001405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893725035 1250 893723785 893723797
    0x90f0f030302032d040f06091203061403300d090507060908010e0d1409060705070f06182303010509060a0c0507020102070e0915010603020c01061703071506050d150b0f03060c 77
    0x2966444013444c07008109c82e1340c01c245624400b520300003403540c60060301c08125500d0080e40c41c0300ba00646205131030f5110030ba0355407003050b4100300d000c040c245201985c00c2050080091500c200c501e8103888208001d800070303000c805c1d103070262101c00006546081d0542621070001780105c01ea081038080903407060142c0140003241c1e142c604014105220389020810a41100c4000d940350380c0254410031915030380c0c80f20000500b05903d41f80c80b083c000b40044801a4880780b10314581200b403220414400110081c111020100080090001d402c142400710760301c04027036400d19019403410304c000350130302c0c0180300f00c41c94140d06801402160786001144103204034010000805801040b0303116029507001c2d0780140c080d0503ea02c0041c4c407509101c000e06e0860313540c0d41003005d40da030401400c003c4495000050300c0304254013500890481510004480180980d0740c03005030040c0102c10a00f00308031104440c03106040c0810003c0001c140060100a203080c078034804d85400d9000300000c958100886802010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893726285 1250 893725035 893725043
    0x1d010902041521110621090f03040e150a030308060102010f05011505070206190c0507050d0b01121b060c0b150612040f0210050a171504090f0f030302032d040f 70
    0x100c0c035602e504c08105203501c03003014105001092107041003540e654114068102e040c110081c01407030f00b03540c00c2507980d22039809421115026000040c10700c960f186515480383d071019048580780c81d038030314001d0180c1d00147d034024099420075072002e150a03074901c46c1a0491f0050f582001c010b142680d010341e4142d2220750240d0b0411000c000b00c00400401d103540d286010754940d200c04000c2c0307447c1402820710005800031449115160b4540b800708011011080c15079405140009407031542d4600300d202984042428620514800030015081d90020003502d010b9009005561390340d036074071941e040c000004401c030550150080c08452002c41c000d4003941d5000d84540e007001c01c081c0164001410207480c0c104460001000000c00d040e0083d4013290004000c441600155800d05003104d18000884c003003150300303009650710040b650512029000084040d60001c1920400c050300d410300070080d5108950950741048603840d1040d400805000c808211100d02d4400c180c80d807110703039038508032641150007a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893727535 1250 893726285 893726303
    0x60533011202070516080a0302100509030903011109150910050f07080324030c100509030307060212090f06015f040e030702040507031d010902041521 66
    0x796070340d26a403000701240d40c00f481c01001c0c50113000c03108103040f0005400203546034004903683c000194000414000d0400c45040108240e0b562091080c6580901c583c0745078190300302481035400091800082941c06000d640418282849400104052043c9402150888454031000f0715451055018060146500190f980382c896103031507030501a0001d4034030880c80c90350843c07107446900200030701c1140c1000c00d802070011008108005400d100c80000c0200038010006483e0240781e40500c00c55103400d030701000c11915100b80d80c40b0070020000488480e4202d01c29500403030905940010b800d8121035000e40321382d134090192002110758132240b880c0c107d411148504c0900c2014170040d003030785001c0220f5044a8070b4007010180309948042c038210482c0107900e0101ea1102d140c00100c101c4611799010b4802190549030610308a0040651b8844680c0100c80804021411101034003d4100316000f2202405003000d008684a40e8030214414507124900602040e000029880c0f040f09501d03028020314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893728785 1250 893727535 893727557
    0x3070e0f0c1b06010e07080f040b0a020919031101020a08180406090f1a04050601050a0c02030f0109080304060c05031519150306180c2c15030406053301 67
    0x220010307031405001e00d0b2500200c005203e0b0142ca803420700d0344100c403864416041d003402003064212540240024090141150024140c002c40390121030300c9a0000e0000104c000314004140d0000c01c0c0c90204807850903241280344510340c400141c00c180301c4e030800341083c03600388203250f841400301d4414a400d4100c0c0d10b0341000601248148504003444020410105030401c0000000b811f0001c03440403148554601410b001c9940d0b8048140c40303e450460426000c0a4000d0000920305000046168080d40c2021004c0c020040344902031030055108000600c4911003028041c1c803603001c1141c00700c00c015102d00300101e4510340515220210300611034001600d9403261036003040e0702d200d000360030b02180d11140c0070031412150703151540900780320140400c4880950b42009111340c0c01d000811800e00d42140304100390100071491075100340c0c0001c20fa1a481c480140301110241c00440b010f0390090314101c0000c01030883c200100d038102020f00350702200304624413544a001e10180d8040e40c10000044c500d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893730035 1250 893728785 893728807
    0x11b0813051c08490b0a21110306011d0c0a0206070c080c2b030605030c2701060e120a03020c10020f0a0501021305060708090d03140d0506030c03070e0f0c 68
    0x54242d80718601c00304200c44d03c0c511404d000554408151590149415030b104201d8810419254800ca02024107882040503460806018401910100342d51600030200001109400c1d80c0b0b09420071103080c401d080faa90340310803402301039006031300a003409a00040e00003030010b4440d410b0207a00130302c11440242001c4070826501c0c90304503c204d880783d0020341c0700200103000d4610204900b0801031850709118003410803000c217480c0c0728400040303401146d44524050f40408601024010184000c4025205603551180100301080c2c01c407071240a07000c04519544012008a014007030b85800d07400030200110034500b8000402c1600010f071045005005166100d42c400740501c0881328000c0d0009a11010350158040c8101000d611440c481c6204000800000d090b41c029229422011210754585404a04040e200d0b0b11142c28484023112000074546500f00d05948031600030308040e0215032050100310289591070081e07000f0017400700c9250000660b4a200d5882c000c0e132028031051824100004450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893731285 1250 893730035 893730127
    0xf03260703230c0705040b010516030f1806022e0606020303010f170d300f0608030a05160c03021903140304060905011b0813051c08 58
    0x101c0c0060720074003603004040300c0b009207a1228100889403501d8490b02e043d40c10b50707540c010300c1440d0003540c41b1100c9106030380c020016501e03a804542e003060003488480c9002403c03d400658020046112108548240e40e1810f604c030068448907002024080b0b0b412008100a40c080c1ca06582e2100c0d0001c2e115050503c24000d90300144166001140c69505101752042c00d080d05421a404034a5a4a0240044100010211300411a03401d10504e010b0010990340102c04407850710a0300d0060410000c14480132960164040000c1e22000704640c0b526560203648030300c9250445800a101440b1285000300c5034030611302d40621400c0e52070565aa40e078081411001000c03101041204943c00c1081444400ca108610282d032841c0554505402c1c800094030b542c1c0c3c2401054100030307140058440e05c0c40d08810181c034003a0030014080e281c807203003149903840d0081401114001d84200c0e88150700340e0340410840403200da005a1132400d04c8551400710110a4a50080c010641c684408135003004034054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893732535 1250 893731285 893731297
    0xa080106120b0a15061115070c060c09030b012d06030c0810080607050c03120c09030c0301110702060901020a12031b0c030801140102030d1d0105100f0326 68
    0xa40155014041c0c0d0078035000c004001040b542d036142c20820031640d1400342c6421001501c541d402d11880b00300c01a10a14600040c404500c64094080014480c06c0c0d80c0001c0503c4406104403c20300031001d0300901203401960314403000342003502240060240f8080d40c0e00c000000f0b1240407000100c4200300c024900e003007409910140c0401e079184a42207243d80d012200c035078407003040444150304511f80808d4559406008144c070003009008220300b21540024070844020007044400d04045050005d21826550701101415100b84070f08a2107022504043c06407507070004851410506020031074007400300e103034003e560700c2c0e04500a52031141c0001e50b01c000308680e040c403903580008030103051684503000320a40c5230b088802e000701c001c01320340040d030f200e8041c84c1552645a0070000700c108200040c0c0c84e40c05134803c103104a60505480c04140460070700503000d01608d200003841245c544010f00752802119024410402c020315174188046100700001c0b198100d40c01d04e0102880b40b01072580da401760070007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893733785 1250 893732535 893732549
    0x2509051c061a0f0a030f0201201e010e010b031c020a050601030b0114060909040204151a03090c040e0a0602031504020408100c08160e0d0f08040603110f12060a080106 73
    0x2c118081410300b82041c1c0c0d01c01100f81d80b100b100d5421074640211440140c000241000082d01680910041c051a11090308101e0402c54855666405107002062032486000d143d961801181605e202c605004a07403241401401402c0c88080920300c401c4203815810b1003109603c40e2100c0c4900103141040341c0b83c001c6001c1c0c0c40702c150550420410844143d0302405036842142d05111301c0c02242d07112080650050360449000803813601e624411050707144698030100d4454586181001d0040c401001140b05500800c151260700320702c88100811a801c68888020540c0f001f08260b0020741158000d5400c9107024000c0f00da80d01000303000600382c0c1c1c40340c0c01c804050b8010700c0118040001c18050b40c0010011800d0400c8030303190240ca00b2000003d80c03071080d010456130781c203413800320740700c503018901a84d40045003858100c1280c2840b42444d07200317114060000f85840303c4138885290310b40170303124080780300c03801c0510b807002044c4005501030003d00510b500004020000a01602c01d00c1514003c1c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893735035 1250 893733785 893733821
    0x291006110304080607050a141921050108030912190f0309050907110f0109021c06090203011d0d090e070e0f0a0e100b040e0c210f2509051c06 62
    0x21f0200000e140e5110208038455000b0248048040181d048040d0a207482d003918100741130381c03c1c981e450340c0040311024031518a1458180085101c3c82c021004040c0f14001f40c0d940c010781c141d002c0917260744107134000300581100707102d1103080300244000103503a1560303003e880c1113559152554005104400d09503403520201e1440fa041da04c002006003c84520b42d002da40080020000341e401240c02c0c504040341c01c6512095507000b030020403080d90700c0b030b078281d0f078010f0001c00000d010995850303e004120a0b62075641d10448650280b4280314544400036925910400f403100d40b500a800e440c0e042030064140d0b8800500030301a1510788654060308010005109040010300703050703580e41d0721117003075400010190030204000d100348800c503400d82d17421a540c01d003400d60300d011003440302c4441995916a00e0814103040244a8140d0240000382d004004c0c12110404104810300c1c65050340040c482d60001182510101700128600081c80100807500c1d05640c001048d03c0f551482c0444091044440c0090f02e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893736285 1250 893735035 893735047
    0x1081b0102160602150f070c0210110304030f0c0e01080a020105210708070e102001060b030c0a0201050703180605060102070f03240c2a080729100611030408060705 72
    0x83c04c0c032807140c006d07108000a0111b802e00709401000d0641108020340a16442e400781c001e03070383c89549880519107484050742d40303907900d0340b40c5101c0540540d482980d20700c1c201c050101d8040c0700c2c03190007030484808c0001480f801c0626070041d64144c002d000c0200312031506460403d4205c801156462003a4041e0307440305101d2901a001410300748010344401d004403080c010526100c0e801c050403c1c030f491000480314810321215080603008d005ca603003102055200100c18842e00290910142614844e903800900040e550800c049045811a1f0021500308090004a0000c40c0e610b0744401d401000c10301c107072042140c580c0038621004113190320403250700740b6000212801040a02d429484841d050b82c0502c0f4601004400a1a000740000d0141050f00019486e610038210300a10307140d19580010041c0e02d5070300a0030502a8888030382140304502d8004000c0408816204c0082c42c41803555070290500743c0c1c2401740440360302034080d9a81e49184810080410401d80410015104001a964107030755a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893737535 1250 893736285 893736313
    0x61f0b0f0d060905090c043909050301020f030c0a0c14100e2d0304050a32060f09030109020904060c0906050408190516090b120601081b0102160602 65
    0x980b56884288090700c4c29040c003030500d20225031701c01940c50485c0c0c0495444c0c0d4040300301012040c20000624103c040900d0420113401c1446c0c141d641d2003031740e1036a03040d0658507001d2600341c0c8540c4e002d2488102c02003000401a801074809000141d000d80b514080045917507441c10a075149101e8004908e600400f0120543e1905020740c0307901101e40009480601d40e40260340030810301ca0030740900345450840c07030042d020808205940060400820000314143c1e01c010806040326002c035003210310480c07801a0240640c64125168083c403000c0e1003645408090500285990840c1417480d03859502c51000c8400b5030b4800e4030032401580143c0c80082c86024000019102417507507404a0180300050000300301c81b240200b00e5207840e02c5954000e01d10041e03c0c2c50800e081422075425050744c0f000e02800030421400c254484842058296400400c018030300c100c080ea80d031424841c10703040c0e074010840880c40003030031909040c0e07600040c012070702d000745154040c80900e4401e400072001079106d045100c1c250 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893738785 1250 893737535 893737541
    0x5180d08010806220614240f010c1703010609090c0f020a11010c0f06020a09080a0f021e04050a0e0c0301060503190807170903010f06060c03080c0408010e06011e08061f0b0f0d 77
    0x601120098401f1410340750010401103840040e405050003140c0844000744507810150301503001c40340003215503c1d038549a007d0030780c200e2400b490b005186004e8000b020b480c002d03c1d24440440c9250018134031490b0f10354611403248013081080703042140b05000500098844100c00d54224401e8a0251300c94480724001000d007000c0f0780c49801c00341d22042d00030020620b409205182250140c50750481c0080107894800c9208450030515046494142045000450b41e4070613a03140003034a0517910302c0444181090b099602d030340121645500304c820708481c0550b0021483c11403c1c41044e6040c184052903c54021040e02201022614100001e201207545401e00c1a01c48038070869800300003050510100a00b030070101c0c24000e082c0020b000c046901a0442070540d8000c2c802c2e08000d11000d90301c20000394a841c070a21814400c02400c038400d08009400c4000d420550f00c542c4010011555441e4200d191013041400a92040c04403c47c0031520000500041036000280b802041d9500c0c1201200021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893740035 1250 893738785 893738821
    0x50409140c0117040f1113050a0b030607050d1a040905070807060c0b010b0309250e0a090503090d08072f0d051b1305180d08010806220614 61
    0x100100d5020014400340ba41100d0b6800503000f2031080020541752030510380318460289000d0b4084482c0d049502410300941200d4496410f005050210508440a02d42c1c1c0380b0058561002140e1b041c4a0f400d150000340d4030082c40c07020480c500f82060700030600803030210703040c40400f62295006034005001b00c003801c01c4524010049c61134003114070300c401d0316240a41c0c1e006010304d102d854000004954481c40c100318482420740c00f81d40e03141052101d44030501c8500c01c20701ca0883e80076400400141c030f40207284540c4240075000805185810008020030500100d0710004440528080c800040815a01810302c1c0384c4a40b5010100028210403004a401c00501055135101d50200014880056408211501c0c5d00c0380103007181c5e40c1000e001b8002028000303022130940c805460036042003120811a25694894809601030b01e95802e18424112500ca0090091a01c41e9200340e010074820070f1403103011501c0780812903e01501400e5030741c1d84d03000d1322403141e104002201c02c0c0d0140174529116501e0444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893741285 1250 893740035 893740037
    0x60503070c020d05241608040b041e150c03050a0b1005030604060905090102040501030b0a0f150915080405010e0a020f09090a02060a0c0515010b090d0507050409140c01 74
    0x1056140c8508010718030a40c0200090080c0903c5808030b08015080100c28160b9500d02c0800c52070000440d8091001c0c101280d555a80ca20710101513480c05001d00c2d1010b003d140c100015008a503216242c0f006420b40c00c80f400d200c101d4210301c0c42804034884408144480303041074030201d40041c0700306006041d13400262079402c50600d020103507500e07690780d40003001c8240c000e0700308143c07030747d94820014000f40300aa08c03c40d40d441c10403042000414065000384140c50090701d0411805101304180400c88a490043c82400d40e41401d0074802203001507014070030648503107400d050301d0ba141c44007401450009031506011994002c01d0200b040700a02a0042018003c0700905051070f49030002403001110a0815000305078120210350241c030103010300702040360090080c4d03075100d141e8800100680b5542c1400e4405001c0e80101d0720003686003e0392207041300c02000a02c0e080418003410800ca2101185085a191062141c0081c2c0d0fa250f03805414070181c020354044844540c44881c82d400c01000c0300f8018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893742535 1250 893741285 893741287
    0x42c06041a1608060103021e04090624030e100e01142412070e0c07060b04050106080610110655090804030f05010b0a060807031a1203070b010605 64
    0x11102841951082c0c0d850a01d00d043c3c1615200c040059000384541300d4003090a00382500613500c100d80c504010000c0f031b04c160104000d0f19035030350b001860300302c910044100070809039460185294447d400c85101070846130241d4461910050f81c01c3c0c00c0350000d05045405035111102d10340c41c8442866400d510440d440d0b00c1d4000da007603440070800b2580300516035034404d0404d1050a07418079010000900070303020420526405052190705810790741c00110741241d940b8144050000c180c1080d0007440d0486142e511001842e8980070100406032011007010000c00041c1089141c15017010084e0781d000d58038000c1a070710300c00c408013624490148242030070b5000c0ea54810310307410100c014400480351510000071880c3c111b160005000c1c0a0b0031514005003e4140209022091000310304440c50b0542c4104020800b416400c0148603c81c900d0344185408110014006551607000e50042d4456a03c0d0101071a0b8800750200050010414182044032036440454502c0400c20040700144c003411007030030b10b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893743785 1250 893742535 893742541
    0x804050c0406121a25110d05031b04030f020d032303240a03020d020a030602040609050f0d050d030509071208070201030c02060415022503020c0406050406060c02042c06041a 76
    0x10b07000790071001e40044030480412200081d5188031b00c0030340c03030709907007503415155800550680103201c0e4000751910b520020705145541100e90401c01250100c9030b01a03844006a40345400300050b0b070401c0c03482601802103400b410b04c01210210008041811030b104815201d040404e1000c04c0b1580c8146004451689800a0b85084c1c0e1001074103011607504403811381e40c071461440401c003200400d501c01001d03035001045c041115034101d01840309490040d03a4005e510045c15003007051f50140e0140150140d040700c80281d2845111b500078640c00000d00d011200d94554406100400d1603100c0015200d280020800c00210b41c0e05003d0f05d410b09031907100902e018102625446600644030a6504445500046a01e00f4513a081d001075403023124419402c0e1140c11034200030303445031000103108c2d200354584100450107140c14803501c01514010759584a0f00501c0340d080c0802010740103c0004c03030180e00110503544082e540010b48090340c441018040504091808002c00440207041d8104101d0032820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893745035 1250 893743785 893743801
    0x1807020d03090206071425051008040b070c0c0f060c0606170d0c21020a0203060a0213090f0906020301030c080c041415010e03190c05060702010e010804050c0406121a 73
    0xb5078030000d0f002060307910b1421000c40f0740d41c90400c40052101114003041f070111203101c0d15007441c20490350140c8000c40281840f19040b110003408840c024100c0103500040352400c0e01c02d20002104501c40e10340c80700c900b500c40119030403c1c0401e50040d000945641e2511041082500640c00100415480301c0304c0a01480c044a0321041c0a03000700c0104440d07121180c0600c0500412004901c5051080c03d458410f02c1100039141c1c4a40e81d81070b4013070b2080d0000300b6075148951089441403000e025850a81c24141000324000e4004004aa564176480741c88141c0852594401540214032802c21070801e14038082030301341000c1030801543d110324549500d17009203410000e01d0390b5015850035039110442ca803180060b180b42445000281d0544500302d4400c4c00c052103a240200400d0085075003265290780d4808000e5640315108000b80098851010b008507940a040d08680041c414000c0d690402045d03004281240c805600106d0b003041c05443d00c00501150344900c418010306a98500c49502d02100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893746285 1250 893745035 893745037
    0x402040b090307080d05031b04030b0a0504120c05120a021c020c130204060806040207020301020c10150906031205130911070201110105040f110d0f080409110309060c03070504051807020d03090206 86
    0x4541c0190f0f10000b23030b19a480c0c052800c950103180e0001e601307816814900003101c01050122012600c400540b10498007007400764041004969120b002020805507868845419401c02d81c1c100003944240003c40e00c8503000150300540c1c0050950042c624690350320108440c910307036105240d415a104100910080d40d000c04607541c000401d94002d40d40d501c961010a0084c45202c10000c90307070141c0e204080c0010300542190a41203812040a9640c5032200900d2040722000c1c4401030110050750b00550b000340c002d030003810422005124170039a040c2c2d20040003090b99a0013000d109410000582a0110368103c01c401c0540b12200c0020002d614140c1e48900f0b07a17070a1982c02810356036808040c02c2c01036032210003e800440c0d000044454805103440c140c403483c0c00a01881404908060750740d8030501c1c0e40c0e0240c9219040180050015032a500d042540c2d507840a031080307003004400c000110f941c1c0c83e580c4200e4004503401c2203805892500302002400d207100c500380700040500b0100c0d02c4004d41d40d288 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893747535 1250 893746285 893746291
    0x51506060f0f0912010221152101060815070822030e0f13050f0108190335180d200709060e160503070f0810050402040b090307080d0503 60
    0xc502581d03d001c1d200000d4110352810b900b03d0300365800001d0320171220310440002200ca1101907042c4034039031a09064054101c12400701c042e04010113410a417803500c07603400c1d00741e000902440001401c684400d00a41403100c20013103541a250404103000b070440c0e2002815174441c100c138030802c1d43c20310814841201c0c56071207a005020071aa00ba00241310b5030340c112213013040b00f100802ca04c01180e1840b074544040c1400301d4170780741040c070444000242c00d50302242c14410319035107648014a4078400ea80965088081803a181003c03800400380c40451640103841100052802c866440586010071f047d003440545616441d02d2034011b00c640808540c1c101c0080c4220049416004100c10282e032181840c0190a0b40585c00c114180b0743d0005013060f500c20418002d010515180521060f1820140c805100940300000054180540b5080a6214660194100304a00200130a40d0340e540c000509076040740c0c0011601040010b460702007890304014a00040448402030041c11446a5025100313000c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893748785 1250 893747535 893747557
    0x60c03071704020907121b020703050705030106060e01080a0204080601030605060f0118090f0f15060f17040609020103090204150f060804050307060203091e0307030e091006030c020109050604051506060f 89
    0x204400c11142081c0c00c07201f40d00b07040402502019508400003551036030300f0300c015201c2c2e00078280f0100c0c1900b4103018007002d84015403241e20800b10f400004450341c24000b4401d000c0203600703200c08140d0901c03e000303d90096010f65800b04d024200481000284110000701a0501108121b0b0207280c00401268038100d4041c004001070903c0b054620a0240280d0003c80050616040e10405500700c8018905d05458155680c0c1036800c0111000b0b60380030103d16401420305004800050004040e41c210b08955441031501003488403d0703038045825103094800c25240303005001800d20060b203021070508000d140c1031400a046042c2034540307035201c0c070500a01070050b940010014001c80030821000d9403004544030f0b003040b84054401c403545c880c0c205143c01c40001e41d00910b02c0c206840c140034010f0240c20440c104000740d514000d01039005241c0c1144038810740d52540f2803100861342c10300045104030b0150014018480071049500b403410002049544145403e01c010001d0b005003600b59800a20781c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893750035 1250 893748785 893748797
    0x51b070201020601140a12050303100605040b0315010504030b100302030c0f011d2110050f01060f0305191a1804080a0f0e0a090f0605010311070f060905060c03071704020907 76
    0x3040001c04c191000c15000b0407c5054540d260301d0401400000652007000b01802c0e00c0445034507a402100d02d8403441c4102d1a12500130700c0803400500d1214415020381e8414140603103416500d40d41c900b601e110844420082c860300714001c0040d420f0030b00155580c2da01c102c2c0c3c00360b204c9140c503001909032403200064600035100030444009540320f00c0c0e0403218103034001164100214a008950381d0b2483c115a024841c0350400c0c000c1800141c8181245058415540750100441211041103000701401000b50401048000905000321054403032a09880c1e08844a054408164001c0c4028294a0701c2c80708240d518110801c404203201d8016902460303441c0c50800c210f520100c0088916040b541b942c943d2103110030314000f501e50b03e280d001000a080f50b40b07042c06081e5442e001074044641044c115910450108008030005081300b600028042c0705100c0040c2010250700c4041c505003003110504003085000050101443c2c01074aa000c011588041042803450140e02046100c0c401410302428801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893751285 1250 893750035 893750069
    0x7062d0203091b03070b070506090f010911131b1815090b130506120a051f062d0905091f030215070f030e0111070b0f0901090f0801051b070201020601 66
    0x1390501c02c450080000b1328001e926040c0c00d05115449800c180c0b928a0b00d4030401c540c2610f00c00d010300410041541190702e162454004006006494034020303659042160f0b030350310002440d5509452021009041d0f520860700f408020380700d00c0007040c590008101e211500381080a001c0e0f00240940560300620710440e11070000304803a0302c00d00002d41000c1da210300d010a900051144d40d0b80309521070746482c0340901480d1100d40388103a109071654145403121100801c1070120364045d4404200007134459000301040405140021191840303521207000140c00d92108100381d1404240d1a504004404c600800921840200d802c035003105100c001d0003005031303541c090f41a01c981c1058610090b0084140311006c5041c0c070303000705840d44a400c0305020a440c2c1d803003006128000603041d02624000c038150303460500c030081c948090b500003c6d01641001075104003c129031441c1041c500003084044000305c8e00703042c00c5040a482d42c084500c13030110b2140c03d021400c0980e0380098001d04441c1c50b6040c01040b94 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893752535 1250 893751285 893751289
    0x6190f030206220308090a05060a140a0912050601091104060507020f01030b060c070e0c0a1b240c030b1f0e010e030f0604060b0405041208060607062d0203091b 70
    0x82c0b44411480c1d01243c0718000200388003100c8018039140c64102d482c8646c058448040191078000e000f1800c000481d203205210fa0801f480004083c1d2655600348241d40542d901903c400b00f85e802d1504039502e800202c010003403001c05026007807d94030380000035403c041c00e11074006d24034083d00070040e118400c8100010811b900aa224040c030105c0030704105d9840c245001150fa882941e0310a100ca40d14041d00001c40d030000b00415a21404d5103a80c071540103c9000c440030342c80c107000840070707920a41642c2002245c2c2110105080d010450a5404240c0f8280801c01504603810052521b014103000708500c0058040f400c20074070501030b01c4c00c04400b114500b40040391128182c1d10341540600c50381120403c0c50741c000aa580c0700c2c5202d06010b104001100c803c0c04141c5005031001009400c0d1911049140ca02035220b81e9480038029005504001030360716814107589420000c48034080c082c2c5070101709480310000d4210401c4103c3c00951440c206a00a00c2d80c842c20035114041c2d05504448051482d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893753785 1250 893752535 893752567
    0x8040303020f0405130903020607050f16110d050a050105011d0430090f1a030601050d15030b090607090806011403030d05010906060813050a02010509030c1002030306190f030206 78
    0x540400340c00302641090800c0e17007000a0800c0c42c2c066015202d01000500c556119008480404160f2860039080c40074840c0d00ca00483c0382c0301c00c200d824040ea441001495218001c8170160a4000c50041030103940c02e003070080c0cc46030181c00035051080742c00c2080c00248080240d26801603031240d02c044c400307441e4028882c40052005180d4a26541c5500d44900303443e441400081514980d007240415175554103d00310f01e6044034024504102d0342031000458660140e4098010b1215401e008030320360301401e074410f1103402c00d5001110b00000720350a01c04402403c005240e07004802d8200b882030b09060100742c540c0c400c0e051240b45481c460084074484c05413018030131b8410740d0400390b000340030341c2d61900c0b590b00c0600982e00980340014007880000e40c03450480f480342ca216070f03013040281c250301c0802d4004485541c014000f458262051020b01141d585800310052030030361a90b400366489040c039808001102d840d4100d0f00302d110b0182d660602c407400c4c000010703000b1260b048a281303651b00c58040c2070b2144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893755035 1250 893753785 893753789
    0xf0432010f170c0a0e0a21051203040b070305010b07050714130f020405040e030a050a050a03020423031e060f06040e0304080d181d15031207050706030c08040303020f04 74
    0x20b030202c20824410000b10301009001490b1041d00d5100d807210300760341407100c02000c078481c0110180780c034911021031411000038003003a075000750107881465003001c0d00d40c12281d01c00e903011606070f01842c1c20040919454450180507010051081340f81c003005885455035105240100e40d42030340c031000c045076aa641d07600c01c04891154070905201d164410217403d4025000380c89118041c500b003440e1005517801c00b10031a5920100c0303455260800070501006c480d01c0d0886902103050650820020400c50409241304280c5802c15031244c0300032132054141410264103000300d92020f045030740d03070610171039020611542c80405c69000242e59134441c00043c024081007034044e900360200203008030b0b803104017007968854002c807034440d001c400c4043c021400000441e4480c5458031003031054230286c1c44090540f03203600085040c1d10301e03920f1280000007900300003c0d55610143c0110004084041007001e01012000303118a0a00300104030402e400600002c00c0100002e04041c0e000404600c4e4040000c00d80f40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893756285 1250 893755035 893755067
    0x201050712110a050105041103030405132007060207171c02160209040318081f1e05092d1f020705120a031a030c0d1104020f0432010f 59
    0x1c2d00c3e0312900302140246070640e4162584581010f500c1000c2c1000811078040ba00060300000320720010000d4200140b00200700010000005060010030782190f00291000320b00410380140d44900ea072a11112000840c42c1e101703048041800282541c1c3e00c051502d6501402d06440075a450b1a40c50552a0040104000952100b12103040c4014194450340025515088107640c0340116150f2025555510140c0c0c54101810300e103050a0168000c1500610104891400005620340d072921b00c41003980c90860f407201007039000c5009140f00ca20410080a861001030840e40c2035001031001d035544644e103440c0c80004000c0140e1090008107080c0d81210383d01c030707004007d40d04058883c8880e10440c1c3d00843c3c1c1a00003e0074599004142c1d41000e819a100e00c6004000300307400f90041d410b010f84240340c041d0540300000812900603840d12940020045401d1076a00d9681d92030a1840d504110314128101200101520440c001401018600319845e201c0909004404020b41d80b41200c0300041c03002e000d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893757535 1250 893756285 893756293
    0x904111c0c090e06010b1303030e010c0c0b090415030203100908041a1b0102160308090f03030a050115020a030203030c03220303050604052208030717010807180603020105071211 78
    0x2442011a41c441c009416601c0180e524a980e80c0c08206e07214066200c0d201e103c0001ca62080000030b00884241191010604200300d500f0b000342c42c0c80100c640f1350b0b881f10645050004904c1c0d4507183c2881850122030356020881c03007150950300420380c0e40d40600000e03400c4907520410001840040c909a40c010b0001c0100d03101e0941102d02d04001c0350f0803141d41c4040e40d8681030580407012106000f56000300b500d02045500f81103454408480d2554060311401c0280a5001c5c00d41c0d5044041c8021807060b883c5120115042d403420254030300c10711800b07111a0464020310318520021354040100c80d0414082e4071010f813039455509804000031401c201c9001000c80700b01d07d4004054046e002240300384011901003090f40e40d41034045002440b043c0307900c040001d0240982000a000c0d00203141c006a01d03203403c4c9012109003040409044007038000e204190300c41340f401c001c0c405ca032590324400c5213003c400600150b8a1a0700107440c0e03000d1118020800c000c0d182c05c40015a01c50204590006040030881e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893758785 1250 893757535 893757539
    0x9180f060b041d06151201060602160602031e03060609100e0a29070602090a0b130f0f1203021518120307390c0806060904111c0c 57
    0x320000c21040c55a54081c03070802203207401c1c8119580c88140034802d0400a4200c907503c0c0401d50303135102c00c920b2003135510030841c20305000001000d00c40d40000c0c1800380c004141100080d42c000c010090b1685c4800c0842d44100584942039404440340c100114001e81c880e5182e4440c000011114000c03480c074103400400c3c512110a032160700c0070f030208100c1d00581c4c07200c001c0340e02c8150004601170302d2001d0f40324010b80b5070f850f5a234858000d00249070190207903d0040c140381041c0005000801c80d9032180f20a444003050550b18122412a0340c001401104019007031245024041d1802c8441403058014280040804000341030003845a035801d0343c0100350f480c84070b103400080c1048500041d203000402e48a0002414402c2c5501d104490140040d9168041e4009142c484554400f9001841086d0400c80321100d900f044805640102414402c012001c1410700701199107140010003000540b044801b4000d11010522521580c00305200582e039030380030b00545076604025032032001d00081652900c1040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893760035 1250 893758785 893758793
    0x10b09040210110705031624050301180605130902100f140306040f0e0d02160b09041104080d0c02010e030a031707140403051e1b0d03030618140c040e0109180f 70
    0x2e25088c0c40104c1a40b072603c041503000c10001c090611054800701c1c1041006004083c42c8001c00d1881020341c03007000c41e01589400116000d410141d0112100e1130f1aa2000c1c0c0451801e0030708084030140074945103d42c6110b507840240030034050401c3c241403610000102d0450348694110b0711346014003800a1101c2d000040d030f09603841d1100402440107001e1147c0e03032280d5131080e00d815000c90721540c40441c00c2046034001c000c01400041585140c40204020000c1c03041400c0c045441c40d071049454080f14203906000160469442c010b81c0740c481d800065040c400250070071a4143c081c00d06181c0442c9942c0ca80209592014640f0f484821061002c540001041000640468544d40540440841400c1007400c2130b9580c3c0704081d0504451810307100e4a04504058220f8441d160280c42d001c03812350b5507060000d54240003600c032240c0300350b02ca004888042070716100c0d25401040400915291501c1c0220700481d00b078043c0030301e4007025114400440d103100b110200b14141604100d610340c80d03207610f00d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893761285 1250 893760035 893760073
    0xf0e0604111905130605100c0201031103040f0f15112206230706021204050d110a02190f06090e0a23070207030602040f0305010b0904021011070503 65
    0x10100c522044442000229003800032481150a107542d1030741404a080c0020052010808a409820039981d02c1e03000516031740e10301858132140345913152004030202900005041d10307498001c485448000304140300000d02c603440015165a08800c0041640c03c151038144003242c42494190780440c200103070b0071900c0048400410712500f0200e00c480b031007030089124805072182ca200b20808561001c0b2400d0204650034a480081c4807203c0d44503190451542e02c0000b207820284400c56885100d00800c42084020080d400200115060003070b0104140c1d000c4960381c0c0b18501c0000d0180b0111841c0001c01080c1d0585000038090090f15030141340d44400c0c0040115405218000a03041001d01207005010701d48520310316164134074100c4001108480c1e1408403440c014002c901148030b402000808940b00d0b00c0600003404a00f8245000e141ca507040050030341d100003400c84e10826030319080c007006958425400a40c03071214281034010381004440305080560a070f101d507801d402101d50000c18581194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893762535 1250 893761285 893761291
    0x402011d030f010e2a130204150302030712060b030c0706090c080d021e0d030225060b0411120a09031e1e0203090a0b0c030c100c020606011d0d03030f0e06 68
    0x8011103144c95401c01c03103120034610340c040817428812040d00410b6a401c000c038580500340314041d0090b01d000e56607000303412946400d010341e100095001c410300480c540d102e440c401c400c8907074800911146040c411034007224403014129100d85d810005005007003007101e0b0040c80c0039076080300500c004260f403002c0302d50b250b940d8442407400600031038120001303c00c43d002e8800079000d940340c0180030160000380c080d002275102c40180d501955032008d0b44861070007105c0780003012600c1840c009c96500d074114103102c00e596007100c5c42e0103400c6050cc581000804000f44a940c00001e144021845c00ca19040c01c1d175100150707848940000944a14903002e49421000e0a1824080102d5600d1305805488089840307000d0307003405a6010611074401c2018842a1000d8903184084030283d03854020001109407409880070124014641c440104000c1181c041c805581c0c8200b0a0034600b2984000c04160003804880c05102842000c240111200f410310a0380440403041118004022178004414402c7d9514411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893763785 1250 893762535 893762561
    0xc070c15020307110a121104111e2d1306050304020d06050601030b100801090c030c12050c04030b040b27151915180908030402011d030f01 61
    0x20100094092604018480200c44a501075810000a40c0e1003110916440b035046600c0240f4000c0818400c3e920006c240106100310310406030150004284815542004101c1038181005e11000800c0261000c03842c00f4400303901c6441e5500c03010f54038441200005641034040882000e5070b041e1200c0b502d84000d20440041020347d42010780c0c1c9610460b4a407000303c5009400c04054100b2000040142e0059a0412014100441c0300896100801d955224030300d001000100c5244c010004600180320354030300300a0303924080c41100e5001c50301611800a00c0000311800f40d0380c0001485490182e002e450243d5807142150f05a4101401c005881e00c100755205201e038401d03c3e182220550314844000148006031018010000e031aa03000390401c0e00041042a070a0030310611142000b8003440754564102044450b05001803d1484006092256007101d40c3c8103464005000045180c010941c0e90040e4246010122070080042a04103030000000140d014400d1100000800314190000307a03441d805 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893765035 1250 893763785 893763803
    0x90303040c210602030402040e0f01090c05090f040201050a0216180b01082401050c0a060212070c0f08090607060f0506010f0302180f010522030c0512060a020913050c07 74
    0x2180d42d0103001a0100d04007041c181d80084220001a03026000356900c5030000780006011444014018209a0005c6400d0b0280e50b42e900c1c0d501c108544045a0f40c0075010079908507178a46040c000042c071408010300081e0502c140807854920462080240f03041c501103500350f12410940d2507001d1400c1081c81260701d00045d04040b50540f25500c03d08a09105080d0002c0034500c0084050020325803004981c095410000d080007449200e4104200c030b001c40511420006940321010340c40040c1e0204040c01d90310030012050100004039581c0311900004980100c03925950300c4400c40010b06a1040341e0009100500b843d56421000b205035102c544280401e032201511681c522000304d00300d1181c0750380c4040c1d8287c1149801000d0811030303502c00704810103040051801900403122451551604807000b580644c8000134070402c1000040080102003d8501c08192041c1050403070319010020510b0303041e690301080200b2555280360001c100400003c0b0200001d04140603a941950310150054a00c044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893766285 1250 893765035 893765039
    0x106030f03031d0d0e06070506011e0605120610110607020607030510030f060902030309060c0703031d0d0b040c15021e0a0201080406230a02091005040807030b1e090303040c 76
    0x103e0a01c07016080c1c114060098604c2c5076806468403013a11700c3c890b400c2039040c48a8000140200642c5010740349410301512010030540c80008804002d400007070800500f0b00c032490701100312030482c0d40c00c840210703903141035080404401c40318889080e185c62041d20680d0309200102d9000701c0c1d000d0145107256028400e5030b43da003c1800011000f88801041080300d141060042a2154010a180da100a0a4900d028800400940241c20418000701d050b00110001c008054110012481c02f0130541c00c0c80d00d0580340100011200d228243c0c01400084418000408001c01c00c9000801380040c0c0e07070703d041d1200684000070340e1208a148100502600302050b41c0c034048001550802003941603450f0344190b0f8803903503110058000a00d555141c001310003402c505203980c1d10701183c4581c050323180c01611001540d082040c042d03e070461348014004204000c2c882c4000c04500082640d070803000d80449512282d64070020301c00c07643c00d060703000c50f203910500541e840040002d5000301d015003d0032086ca9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893767535 1250 893766285 893766311
    0x2031e0403030504020f09060109090f020417030429090607050705060a02100501080616110f01140402040b0111060a1d01060602011d0d0806010c1110050306012604081b0106030f0303 80
    0x1400c1c1d0311240410651030003000807010765003003301c1d100307031070203025003882d80e44c40c070800780c0100307203803084041350000309041c0820b9501c00c0c1c43d030018141c8507071420f010514604451545104940682c0d004000000342501802410000c4030021300015140a41ea0312004c1c0000303403120402c081ea00019803c01d000003901c802d00243c013074010700f4504541102d04003120403d072030140c400403140c5014001c803843c4008290082c890490406030a41c168070702403500d41b0421044500e03250116062003400b000100d002c070300000f203982d07020b204a000001c0354000c000303207030420280d2010b88040c15820880041240d030b5041d0810402c100d4080c2d198444018480c85894881075070082e803200190707000001640540c440e020000840d40a83c0c48401850300840100c1e284869103030340680031843c00001d002c1e455a0147d8120302203840480004075200c000c0403101041c590143c405002840e0100e01484001d804181f003504c2945140c1c020842660340c0d00e040550384440c0d0320705801181c5030a0b84d0407450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893768785 1250 893767535 893767549
    0xf0b0109031208091501081507020d09060e010c080304050307140d1205071b05060106111203162604110a050f150f13030c0b0c0a030302031e0403030504020f 69
    0xa82e40c0b19040c8941e40380a0041119440e500a00104162040110842c100f0a240d0105806806100050248000c011a96605035100905040c00715403004214241c0d1540c4444802e050303520628001c0030a080c1c420040303e120100440107441c04a001007071008101c0000024078500c0c0c8500541010b50448054032030300d501803003985202140c1d420007452144107491f40090f80c48115410034a0764400300c2c010219100c00000ca084856038403039001403000c540c010b00d46401c0b07041244000c251014030040d19010034040a0f0640f0f0302c840b0361a810395452801010161021240d4580c07840c20803440310307c078a1060000b5101555100315841d000809410221410801d4500103055240b61a00c0700e070030300218464080c0c40c4401d58034180201c1041e5940e001c000c204d10b404442c404c405a81c10350904d0703070750b51085a0180d000c581c0b0400a0910540c40818605000e42c2c02d800c00503201d5680c0b00c100d04440c120b060f031f0300603150a0941000201605070380400e000f94000c1e1241d4120001d103800740044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893770035 1250 893768785 893768789
    0x1e1308070b160510090f0204060b04050112020d1b08010e0a060e010e0402030111031f05030102030f010e0a0e0a24113114030f061012060207150f0b0109 67
    0x1d5a400700b00403454114188011542144a40221019542440707800c40841d0030302941205c0352882c60a0003c2545040c2c0255000380c1500b00d07040745450300e808006000b43c2540c0c1c10040144d9008610100c4006141d44000340c43d504504040c445550101c4004020744000d0060124003070300040450800c41d03592080e40e0503200d032500e425000c4d03401c222031901407000080041b40e05640b210070035240003c281d00610b000b0100300071024002c0da040500c4001426040d00300070f01a80c818001c110a5040b070320855030444403e039809a001d40c85001c1104040c2c0214100303100703548605980c100c100440003901d0400b444820102e1307154401c10a01400a07901e01c1d400c1302c038898905001c01c41d440c850062400300d03110104140301c480c80c2c0060348001140c112a52000c4911500740c5070f4901e03142814015104d4400307500000c1c00342d501d00201408460390701402810680903805d14011b0400c25030368101c4540035044503495480090390405d80d40035110280311104000d04010201c11954080c50710340007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893771285 1250 893770035 893770049
    0xf200115121b1a0c0118050d110610030303050c0c0706051218070b03130203070f08060f070807050a12020c0105060406060f05070609020609100206100609050f04050a021e130807 78
    0x141d01070b003d4041c66800105030103283d95a07070f03036503c07590740c08801302c00410501c1800034014100e01c3da00c01520ba001c0941d090501030304400c00b00100c030420b05c12544180c0e5414180029103880d080803280c09400341000700120380c45088808180b15400c80042c040149131010300b10095520108401c2d1595607a00c18104140e104450500580180801441d030107110760800d480305410a8001030700d400295806420402c4c0300c0312061003814030610006900c46546101c07400d590800031001030110310001d1002e010401c0c041120b05400c2e01c56502c80d031a0420704e100a41d142d00202211500800c005d88849210f9407070600001241e6004d03a03800c194801d050f4643c0b505001c003d80310b01c0040c00700c85108991000c01013003203e44039541e0814411003280300b54010700007403400c09181000036445411034424815003080412141d6103e07250b40610020585002c1855129082004040d025031412030400d04454030b005120501d180c8050025030044401c90305039030740e442c1d08240d180c5e0041d000d450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893772535 1250 893771285 893771309
    0xc06070806010201020c01021602040f021606110d0903020d02331302040903020303040c0e0c030408130504111e040f2c0a0b030d0f200115121b 63
    0x40000340124509503000c4018000540386c02c076014803080c00c80e0b120a400721500d916a10008065041900c1408006400e0712011460720907400e10300f06011480c84401011292600da0720304000c04460141c90b41200c000409100384220762501a48418a1825010041c410303000403141c0301041040c40d40c0c08560810900500d01308001400d5403201c00101280d410208040031980103803a10b00c40c0c40c1c6580c0c080e901a42d2030341000c0c0340c10007920046600c03d0540c2d075203040c18044070710004070840b600700350311011959603040081001c041d203820707075404594010301d002071103403035418080000c2c070200c41e41c2d480c9100c003900c01d11000c4507680164004c001c0c1c40840d00b0f0b418841c0992100030f490f1604d10701612038816070581c40305041c54442c00c4840c203800eaa04c42003202c009003000c00090600f604c403400e000c00340441c2810002c205280741c2c5403140007403103c0000703840003107002e60290300000c0c0007141000745103455a142c0038840c0d440740d00445071030151b03140130b03075081983c60384c01d40503a43c2c0b221a034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893773785 1250 893772535 893772541
    0x391b040c0c0506040302031b0d02030904020d09200f01031413030513080102252a1814010e0f060112020c06090c3a1a090604060506060c06 61
    0x4000106003118181090002001080020681c00c000d0305110742c0c404e600644e6982a611140c800e8113560000e820510b074403074103081c2a01074011003034940c001410341e001607c03100c00d450742030040c000c81c0d01c026080c0000308980c003900c407800c10b03a980341c0140d0a441c0c15410220000044089401c14091030f01e170b2488100c0400c204005000640744003a011b49451810315011414030880e0084035402001c082c0e50024030440682c4007270389240d1801194031464001c02c00c02c0d0300c07040301c20765880d41a40d20f0303400a40c070030380a000d000c619020003502c41c008010980340306410208000f0103035186140400455040000780d0319005140092180c0c645041d0f602440d2107030f0300192a01001190320402503a001d01864001391810844544965032940041010b003400a05004441ca4124242c1c00c1405800d0741000258180c0d1a42c00c2c0d05041322500410a20700d20304054942d10b210004900503001e001007441960701c0e0018203580a6400b9800c10005600c40305c0800c42d0314801c10200c0c0032a50441400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893775035 1250 893773785 893773789
    0x5090115050d0206161a0601081e07031508010c2a020a14031c08061e01020706050d0b0d29011a0a021f020c0f070602070b0708391b 58
    0x1401d01e6174411007454040301200c3d0b480700901c030400307440070702841d0150040000075a4081e4000ba0040c5440a2450070204036a100c85000d0100070500c40c10b0503112240307c02d02d08a01c40c1c40e400100030b62402044104203003d8020f045000c0e03081041e004c84801c80f0341861b6900c0c8000007181107a0b00900030180a403500301500c4215511258496241c0907071355100304200541511640d00c0e101d11303076401880d480d0100411a807001c030300700076108a0451028507441039800240240c141c0b41d4509100340c03145210f145640140c5560010283c0089e5255100401c101c084140d0345180418540c401102d0030603a042c1302e03600e2409118458001904d0040050420200e40081c00000310600c1900c020500403102c04003c0c800311500340c003000c0c0e4001000401e03c0350900400b0000c0c640308001e00125498884001e60b94019409400442040080e010042212090844140c0290240b110513502c188040301080300340c81c91181c0d82005d04a19074140002070114421000c4248850821190720904003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893776285 1250 893775035 893775037
    0xa02150d0e03160b070509090429071d0604090f061502030a050a0804321b09181c050904050a09030801140307090207050c040c020609150c0403140105090115050d0206 73
    0x1060207101081240714548c0d2110501144140c3c001c0700d0504500c6107480c0c90b50003031020341c0368400c6165001d000740314125900c80b03035070080d824024040302c00030010480041d54078413030b5a200201461500000380b000d251240c011408940c03081010b6500d10320308980c182e8880c842c0c2c41c5240e000520803c41c255199028400098101d4007440c4a00c0c07281c2165040e0a0840381604090300b83d20b40000322246011404001d42885413028003031212207010100007050140e24050102d484003000c83c05030b100044800c024100f00c100310b41c1000c0c0003080f0490070240c0503a0121841a000382e04180028444295600032b41d603010b50b0641d512040d45e881c11210008152181c200c159040c0a0110002040b00d128005130031140d011302c0181c58140b00c080100000c44030f40002c600195002032082283c107c40205911f101522600c3c031807841580e8442c0381c0c4500380f0980c0c000426540380941012910541503010900c00c10040b0001c01c482002500034a00c40030003803044580c810410700c2c80100605040d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893777535 1250 893776285 893776291
    0x1d03010e060411030d0e04021803011e1113092a21020c030a030f0e1209040501140d03030c03060302150c2a010c08070b09030c0105060402071e02030a02150d0e03160b 73
    0x45509c01ea881500307800603007956003030f010940d40c010b0244000301c0c1d00caa240c0319005240070940300051814940404990000215204541100da681c0c101c01003c0d00728141c0005604ea03c110240d00b03ca6070034000513040c15030740d01c24401c01c6480c3c8101c20120480620880791034950101c0118181500005e04070046d00104181c0811141c44050207546081c0800c009460342c00380c0c50025403904145018002202c005911aa5415080e60401205903c4503c1e00c0424150181303000f00d00c5065061003900940071990000b034118140a000350358282d031a4018145411025040ea4110f03181c10260a428084c0c50012500f82141c2e81102c0c00b06601030070981c0b8446110300d100606001c01b0351504901c4000c1144d4155294000040b8110243ea0038440c0c5540020121f070304509003001e40d151307001d002164407111401c440101c503401040d5541003152251203580102282c41601120f4a1200546c01c03a1040b80c1800382041c90000118178040300384c2c0c0b84503954030902e500d440c0f43c5413542c90047c0b5001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893778785 1250 893777535 893777557
    0x60a030c0f0612140411130507020a030e0406032a0e010e04021c080f1b01020c0304061206030f171b0102041a0f0f0310031a0f070c11011d03010e060411030d0e0402 72
    0x204224401447c0d0b015851292201e034000e00000c0300d1700d0034080c1c5244240001580710b10b151040900c0091210500c000002003641400c20421001041a948031182902b0806c60103555500000d40c00070705005861190780300340c800c20201115036844482440081d54002c15605003841300e4040000d81c1000740c50381032090040d045c1e480540c1e80c4494220f074000e1001704c00b15040098207203d8030f6005034002441000307030320003042403d10315102ea10940601d124010440c00400e04084142e002990035100e6902030085019040c0d040450f0b82c40c001d40c400c2c401d2203c81d6510b0405104501c0012059640010b00140600e2410500301e1034a08640c0c0000d045010201400d0000b0012606c8400079440301d4210400213515030808020021100300700810344000c000d07103c1150000900501c83c00e568003d020300340054080c4008407124051031410304540c0c0c040d840c00d8035001c1420b0300001c1e00380c0581c2c014481018039454420505031030300c11310140329000c50140c0702c0402a90070550b0040c07131a010700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893780035 1250 893778785 893778799
    0x5190e0102160210051209030403051e060c130305100b040e120f0c1f0213050a0602030d09030522051206073f0c0e030304140405060a030c0f0612140411 67
    0x309001140c070001b800c0d80c9144031540b02141c03d104018040042941c001001d10511443e020201240c569070f84c4002c00d10080f00700c020885a10a005081c84200a1580312017510307102055400c0f810000c020010341c1e04d00c114240381110505810105140e170fa0380b003009120341d14140c840034003422103038044a581c1240b403045054169890f00c0b0381d144d1551203030581501503580c005642075480c940c0f944e90040c510400c0861410400660000100c511209109901090010480c142038581e4001c01d844110307116078148944410180b90300d03040080e940105ea404100040940c88555115421100400402c4010305048034050312044071042c000030f0281d010400c0e60780000c02442034409001d8002c1031903100d1b903003080200e42051844c070128206a0017181450318000c6a4000c0b0300d607402d64940541d9075003011982a40380c2d149807001039a0460059220640d44543c2035107400110310401c0d0006940c6624030b0a445080c0c01041c1d0195200100c9540d142c59607207602c5c42a0140021850380b1440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893781285 1250 893780035 893780047
    0xf120b1302100f030605010201060e011203140406120e03040e011205030405040c11010b092a04050406030803060a06110604020618090106110709020403080d050c070605190e010216021005 82
    0x80d9102d0310301401c00381c60756194124100c003000503068801c2c68003c68156410240e0520081d02c05100c420304443d13140560700f66441d560704059070f400901c411004250a030000700440c44507044554254501900c0004000741510104819100c3c0654054a9806c4075800c00410034a07a0300c001034a8098040c500356450660381e440020b0446030b4881403000401d2000310182c00c55007081c840c8500300e0405488007003092500d502e03840b4440301e072002203c5001000b06d4a0007461460b250544015010241c01006101d0b02c0307080a11058100300c581c244a2940e00001240151190900d08001c0108600030807240d1520790070040550040c04081c01e0b001d068200c1c00d0700c9517075400a0140200030030f44540651241c2c8441007401d12920f600170700030180c010401040000c12410840b120004590000034650302d9000a5a60314850544060080782c200424030468086030003e201c1d0f85450308004000c070700c003c02802c42c20307030107150a2582041105185640541081d22500700c41301d05c1e6140461402d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893782535 1250 893781285 893781289
    0x40e0c3a08190305100605070f0b070c020307180509030f0906031504090b01052d21060103030806091308030703091e08040806330d150c090f120b1302 66
    0x1a034004900c0c00180c0caa2082c0300c055481c0440f05d001925003440c11f10310b400b20300d844010408001c1d5000814403d04c4c2e00000369002d10a200c40019a5402420b64060542d2000c034161014400301c1000f0402e403411020458000b400021610480d55402502e030801450004018858100404004500440054001681c1e4480c8035039250350344101005c040c0da5062074240805014000c5051140d8100302000b00540e41c1420041449054201c0d0b48100c07500b2a100a00550701400380ca005862043c60000300405801c1241140300d140c0c2604c440c2c20a945044400c030340741d8525030015000d40c200b000820882403092700a1128140280c0b4003904070040190000d030000c01001044d00c21210101d03090080d1403003803003842d4000016100c1c17801802030b55403104030a4001c0610061500b03901d802e00c82c001b6215074003250704003600f00508255040311941c90390040c08114243c8400603401c0000801e14110000111064030040003180407010425a1500c6900b84083c0c980071080b060102218016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893783785 1250 893782535 893782567
    0x412030b130c0f030b1e040e0f0f0111040e0103030509040e03040f03060f27031806030b030606030d020705010f0e040501120209150d11010e040e0c3a08 67
    0x14507001180056020034140d001080120303155404030815050462680c03a030795078044686114042ca12110206070b85032000500103200ca200121074034054407104003541c10b004503545c44d440601e5002840400100c1c12030024500c6a4022500403101711001400400c0c4240042c103000c1c40082d000082124210a10528507085035000409031071030740310103004000d05402000b03003155031103c044c400d0095000416001e5140e64110a00222141c075110003818462681d04192907a102040e600207501e441c4010050100c0c4509507002c1c1c80380502181c16401c00042d8a00c2c0b144403079018200300343c204401100c00600f0785d03010340100722555000c030001e40d9540c03042e01e0007404403000302034601803107105104181d00c0050024890366000407022090761902c1d56007040c12a400605059101403910041c0c03003c8400d10380b00d0b504140f5000c21001b032004006051220b0020489400d6814000c460b0b9081c010007807100c03502540680ca42d07840b100454a80e41441009105615190030001100441441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893785035 1250 893783785 893783809
    0x5040519080a0201060803030c1602010210052706040b0a0b060405121c0903080405010c0f0602120a050a02091503090a0b0906190203060108040318090608011416080412030b 76
    0x242200000d50100e140e6024445c1c1801450f50101079070031813500c2c0401551034015400703210b02e25400d011100c011a03100340500c40c11510000c03070400c150304110b00e601d4600855040080e05000d049a81004410000079007544515804034004000d82e56046458000d00300b8008040d030020030500c030114407950740200c803d10501507240105460507001ca03140c80394100700d14480d030a2042211080c004200000e040704d0554100782000072050160b4070340300750154034a08025000c44d10110300d2511003214904c17041c0c06120240e2040c01951200550f200c124840d03559030782c2d804580400e91b5030078005e140016541c45a00e007420360f80144440c0e103c491003001e00300d82e8041d50381c001a0800964100003882c0c2c00c0b4017640c5800031030940c900a00081d11555001c1c0000d030a002c401c00220400038080e05002d0054841c04800b800391a43e5101c840340a0030107030030502e090b0740700130b00040c91141c030000c0c801c0051213440d03445c1031450716952202c031381c110b1501041d501059241d148615003034482610b0040c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893786285 1250 893785035 893785043
    0x191d03070f0b15090c0c0307081206030105070306080d0809030d0501060c1403190302070c030804140109090c0509010503180703081b01060e0a0b031c0e090703050f0a05040519 77
    0x22500741c007850101e042d400020101440001c0214000e4201d80341e400340640e0204ca2801c00c2551082d441d0442031450044060003041d03420000303007218404031240351403409080290000d001648400c0800d134107490460040c00b44a600c5010304188051242c49443d0300200c0f820141e0b80340c00a40d5601c902583c200760041000f10b090ba80030782e010080e00f40039011080728070901550814200008511074444001104020140c000c1034600c00d002c61901601c00442e400901c140e541c6a49040c1038120242c00342d40702e40410403844001544501301d0140d14886441586e50f00d00d0151310f8001903801c1e80014200c0d281421080700c0308411001c007002100003840c000d0481c2e82d01c030b104c0300da030f0142e10711044142400b260741404001c0203902d07203403006542c20810403400400c0f11788907100440e240038070541040d000081440040c00245400190200d6000000e480a180f1951040e0b0309800703448040d28040712002e42080060000c0e4980d500c6079170042d218000b0f4031b08110300c605244051440c0d203881a9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893787535 1250 893786285 893786303
    0xe060a39031536090b0f092b0e01090e0424060303030f0509150c0307030e1903021203040b070804020f040f14060411040909060e030d0c090608191d0307 67
    0xd41140900c1c054000316002c203070040c0200c2c4e4030359580c61500c000182100304010302001c0850300155042c0003503a180d044030780104590300340e1548550a081e044091007400328050000a01c1c140d48194070bc40e0940d540c800e610019500e61380d0321501c441e0000f24030840d80e40c40200001c103162199014800c0154040e42c1d0210310b5080d4031030400c08498014040300c0c1c59510148000303544950900482d58000714075200c6507101d40e10a80143c0c06040c003140f80c1e2181d801169948884140035001c82c4c001240030b0350880300c4034411125040d40c217201c2900c01034408035410001440d068450800154001d20280081211800301c8000c9019105400400480030380c59002498801600c014410340c4504201c0d014001c022400352008880d02c40d601030030707140c281c803640b00009001458000050036403c55080303035a1130004450140003050004404c400060751100001401481808094050710385280281c1305103000300c0840700100001004c00d1494041303459080070f804010300180038003034040d6580b6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893788785 1250 893787535 893787599
    0x103120c15090b06040615030908090a240c05031c110c031e0906251a041202010b01090b0a090510200f0607050d0e060a390315 56
    0xc0500c1d030b000802c080c0c001c6180c11020045c480c0503087c00d18000c0503509001a58640b5414000c0c854440c283c070994100440400015403210420145060450303402040180458525070803030b01040c0351000500b0070380c010b102400302005d4403801c0000e0003100703540009458440464511490300041c5191026400c0850869040004400107500b02203070380e0409480c01481900158660046400710810409007200910700400030b070507404c000f1608a0b10074072601c0e11498080c003500c42c040fa0111900801c1042c411001030050091100444050b180e425099003001001c00b104c0d0440b01c901d01c104210101c1c0003a054940c02c00c448109074840d51020002c0d034150607681c11039503819008000d00d0b070040780c58a200d02808145035810a44a19003e030743c07120030038046000740801c003443c0c0310b43e40140c406006c15104280d0001005d026828407118030207001c0e0071905040050440c104040c45c1c41c042051010382d01c03a5001e0030306c002c050044450034a480711144002c0c2c07806125104403900981401c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893790035 1250 893788785 893788793
    0xc0306030105070f0906030c0507171b07050109170a150510061404060809030d0515010e010e0f0919181e0f060203070c08070507031103150103120c1509 67
    0x240c164040514189414184013426008015861030f02c51001010380c0c480c046441c0300e20a000b220740d0141c0106440b03020280720b442aa250391310980c0e000f02c0d01c1c480b03100001d00c4018042000380445205844c0c00d041c1601e00300d620f02c886c000102c4d8940c410701614090303000040c0460f14028100c1d64200300000c80d490041820041009203030005000c0c00307540301c0110a40420001150162541890104125204c40f1a42844c501030000d07100c00c1d4505010420030304001002c400010a80300b43e88422114000c01c00648282800c41039082e0480395124240f9141d04001165903000140411304030318100752904c0c140d08640c040182506a1072501c0b100e00288054150745000307075030341204101030b000040e43d19801c9410000000030401c0390040001182a03007d0125480090b170415411a550040ea1a255440343d00e0b81c00129008a4940d00031781c80c0b810000b99202450f10818001b00d03440e400d64490400000017042c0d090100004c1d005030b40700081d00c0101c4546015020174000c140f125403864 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893791285 1250 893790035 893790041
    0x10801080f03040b0c070807062a1e0c1203080f10050901060f090f060c05060109201b0a15060b16060b0d081602120a0201051209150c03060301 63
    0x100c90003096000010030703040d5a41c048202c5080319401ca400e9541e4505145500c1d0600c01e0310780c44410b2900412400240d0540c110701e0000a403070401310b6112030071100e1115501c41416944001c0c045254202d0401c5180454406040f0411300942550701c5040e42e43d02d01440c04071b11182e08500280c444400e0100c00904102d2007074110f41c1410042c2d1449040a0220f0000755051042004110250a42003141401001c106015000441400180d65180d200240003840500e004440f940b10310350000682c000c4c907208804080320a085020000c448400490300a81c21284848400c104090459410700720104100002144103503403000041080074011402c0f1181c940c0f08246081040040917100d08a4013105c8811503803003100059103142980204480c6072000c1c600800c05000000c03118051084400508545ca2003100d070002d00413052500d940d255940d4400003404110305010503181104000c61440d84091181c048400c440f4101c1c200b0302000d8020f8076030200d003035000030a010850800380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893792535 1250 893791285 893791289
    0x606360306020d0b19121704030b0c04081005012d08030406020c030f010e0a20090129070218070c0602070602030601090e09120c0106050d080a080f010305190206070602070b06010801 80
    0x100011034443ca011b035a1403e814804600030908800c80c0400940c00031908140e030041d54014048848074a0724a90f004a242c0c41030040e030300300313104168150140d0425030090324142c403200303407482c801054000147c003403582ca85032441c8000148510003080e0300740104080e10090485034003c0a405020300e040c175080c0550800c1c0700c511a4140307542c00c0c5080d80c00051604d11607a001d584030854010b18803142c0e443d601c4d00c410151784264007200009400700d8203521142541c20040e4070076004640d8851001451007141702c000e4010600c044005d6500e00c1c0c0c0721100368884030a003400340500e521a40e600c82284d00010003111a43e9020050003c5542c0c05104100170303000d807220b5141c0605055002541e00c40c035040a44881c2100000c0c8240002003c1d001100100006024078040002c5860044072a40006c44041c001076021800070329849030840c5024103e03a0030070060b03c00b07030140b41581a85481c10755001e0742c100724100401d40020f030003407004000e50b50040422004500300040014094201a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893793785 1250 893792535 893792569
    0xf05190b09010b160201030f050f160e012c03240c0a1b0302190f0605060405271e0f2b030509070e090d02010606360306020d0b 56
    0xd81d0041c01400011000c4804a1210a800c1201d10441d071004801402009450154580c03c0030305101c0145840303510103028080440d0209200b280c84142203484612046480b40000d00c102142d039544040000b1020302c0d14501049105460922400b0034a80510070704221078400c0c20030064079a5118244030a900038038200030451810018450003081801d890740d98400d6a08050302c003104242c0200903003020300030840d00c440307901c081c4c6051024a040403001d05603403540c2000300103081450240b16103440b9015022286441d030003107102d41165071401050202180c03041c40308528255551180090003410548010030249655010b40c80c280f0f0f40195668004943c80001d500e44060329092000400780146030019442e500d08460900d00019944000e8656400701c041c1f280b1903101050101c10801550000e01c6443e9a44400719001c0f130355178610400c3c009a00b103c070414444850f803070460040c104d840d5507140588a494000482e4001e0710b02d01500b0380d4400d18480c1c4c3d81410448061070100c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893795035 1250 893793785 893793799
    0x2903070c0b0a201309050405070614090a090606110604150b060f03040302030a020f06060d08090409050d0f0210020f0409050c07050f0c1c031707030f05190b 69
    0x445800035014500d6480014101664000025020403542c0d01c07000d000e06210b80030550380d081c4840501c01a5000e5041200300f112070581c0443c1c034007482c3c0036060280f0f078000e005042280c5010411076911815500704e6407803003c02c020011081d070b18281214083c054030100000d04614205000d804d2800404da41005500990100404a2109030011010300754140022441e814804001042882030003c503000401020007400141540000030b4500c0c02040c1c0c00f11061a02c040d1161655007408a492545c40407182040b8000a8998000b5180c000c1001e000441e8941450f60344505107800c200b41800090540d110480070281d04110703011035240d50070320461510f0400086039025100700d001d800001600d0700b000ca03480c0b0100741c2c22a22440d4002050302e000251403032100d40c55040d541840f42c8640b0301a1501540c200030b00080440d410382c541c90310304c003c030f2000d201000c480328011721280074544d40301c1c1861100ca00a00450b885030032561488507181d4001c5100c02c04884039031070304a000300c2d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893796285 1250 893795035 893795041
    0x509040e01180201110109050601030f020f030f0c1e0907020a11190306020c030f0706020306030d08090a1101020f0d08100b0403030206150a12050604020f0303031b07050a05072903 79
    0x1e000085080b4094081c40c04d002c401c103174014018050900341d8070007841c0b84106800003090048891001c41814822200b25450820700d1040507940c182d4070864078015000103030720840314a8000d0400c0c4044080d01c010040d003c001c403001031074540381200c10401581082d8280403c0000c8045415000e850480d0400c800e4070a0783e02c00d021f11406800024101540016120740700e003010402d5404a41d4084030080e03841e00c013850884040e40003030310014000d00c9004c0c00c1c281d00d9402030344401d10404055005101170041c607207840d54440c480d52007083c1940203105650f1190307441031101d00c10410117621817081c542440c458a07110310040c0d500c11040400284412301c00664080340340c0790042200b4082440d040410380000d4420300e440e900003510707a04044100e208024010444612841c001c0b60040f0303030718080c40185512480204d500031203040c1c078020a50f10f00700701b41d00642400c2d4058000c8844401c003d07505d29250030420f4000d014014a505151141c900300f410203080d240603500369541c1141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893797535 1250 893796285 893796311
    0x1e120111090402130b1306030f0204141012110405010e1801031218030c2d12210e10091805040201170c041805101e03120509040e01 58
    0x4000d41c2001032180d500000d00070345524808999030045c244000312183d40b0031409040300c1c200280b501c41c2c1c0d0042401d050810310b104c4a1407081c0c808a4ac10100741c80c40482c580c01c108000c1450010810f8180a21f082c120b06140784244070720040814000b50195403a800c2900143c03607a101e0030074180c0306000c6070031038a0000c02641c0c0081d04590b40700c5280b070540c842c51401500d10b241d40d80225120210103000000034072030011305000481c0c40d03507010f458143d0340340c411060f054103140c1050a03441c040034008010216128240010080c062030000030b982e5190f40a039a20003400c40142c2001500407481180b07146004006003681e02c4241c203025604526003034412021003881030740828403651b210300040c00d40e40200d182e585423070282d02c04403103140303082c11180d0a1500701c3d006182e401c5010307401e812002c0e245403003418042c01c28058642d800c5440c03c000c141b068000007503041012400d010001000940c0c03000310701c00c09185610b40940b6954698148406c4030801840c01010b40c0c10702001c01956 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893798785 1250 893797535 893797537
    0x605031002072a140f030c0105090f0603010b0315061204020d0804030b071815020c090601031107111005282a020307060e06040b0c010b1e120111 64
    0x4403103518405070700d40b540c908054035500c1d44031032807010441c140c6031600da081080004450950b1080c071040b43c4101c031658140309407070130b0529032280c240d0f20250301e207100c0d58058800380981c55401400354000e1007010001c2107071900207906c0b080c00d24001009101c040784400c10713400e100d5001550854180300400c00507800f0100041c0000e80200580c0d0201018811480104c502564108c40180303210304101400900800f61000c55200792035400601150505440c0340324040242183c2c01480c180300d0020400195010160400d410703d0740e149410000d0340c100740050501c4034017400c001c0a9204113401031141446182c0100001c102040010f100c00f64840d80c0010380d010102c00120401007400c0c03100b0ba514108608085061401140b17002d10000440001d01d020b80d071013a4103550000b0b41c1e412065400d6040c40170b400768415070900050104020001c05041c00d10019000030504550407004204402d4403055209801070074099034a907103060804446110802c100c0c001c00c02c02402500d42541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893800035 1250 893798785 893798803
    0x60703081311090403050c010c180e090a0609030807091406070f060b03060a061415030705031914011d0408040512070906080607020708011e09140d0503100801060503 73
    0xa8480c00308a44000d10030441c050031100e0001030083c010504140c10f01422580103050104900d600b0010154104c80c421180111055007003511140220700b4500042114100101941403d01c1440c042101141250003a2040d49010307445402c16070500c110300400548968114800c0451075502c82074441e1144d004591341d0325000108600c6030455803410501400a104c0002c1d45442088180224800b1991190b0120750940140016103682d000030b0145101c100c001140c040f00080c8000341c55903002d0070095074440c603e5400c1d076000145004e510000c50300d0281e003c022201e5045c0050001c3d040c2e8121408204000e100d01c46030710300e0590351388510b0713100e1809001d0241d080c0c203000000f44802001228081d0185c01c2080c03200703070386590046580d10011145580144190400014541018442c1e41100044075a640c8985090016071001a0210610803118000c0c009800d0000798400e112200c0d40718446d03038582c1c0e0340e0300f0300e80d00c03049210495070048032503030745442d04c1084107a90000340c60342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893801285 1250 893800035 893800051
    0x70e060a030e01090b1f0e1303080c04030b010906210507090b01120203010806060f1c0206070f0b0703091115160501090f06050a0c0804050307022101150302090606070308 75
    0x281810b000740303141c0c0900840100148024903000c00d01c00200000f28008041b140c0f402411103090703585054040348a502514011030304c100110404000c41e100705aa6070784040b140c030700f03103103450360380d640d000c01580c03090f8800300b0840e0b5107400501c400314841540b07014101c01007110a541c1c903041c4d1902516030b00700384242ea083e01e0b5540e4407030f8480c0c0d01a020300c80072140464000c40d243c0d03070741c0c020468540c04202c0b0203600c0b0381461801c0381d6003458440c654000c1d0744d210007a60142aa000d500303000c0303641d000300b50584143c640025100e0006401028051056100d564041580c209500d04484201c8090b00500d200e000c40c194542101d90b102c8040c4e440c10801c000c0c01084001c0d20703017001d90040080310400b819040c103012941d401d2101542085000390004402000000070b40002241c556205a40040013a00200840c1026240181c0154820100240c80520150002c0701082c02c61741c0e04405041414240c0c1005c0041d440d000d0300d200d51189065903020314001c0e09a5009040d1500200266 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893802535 1250 893801285 893801291
    0xe1003020c39130608010e12030f0a3b0f0607020c1e09010f031403040501050910020106171023130305040801152606150312040b040608070e060a03 65
    0xd4083c1d40701d0750860503040c403040b0b0410141d03032202e8109018001c4801004518807592090980c4030013a43e003120310500041c010340c062511604006806420440d42560010059101a1048010211a1440351030724030400d4000074400c100524105000642c007003010350040300412508a80201d25460b07034000459240050041b404064241301043c2c001e02a00700c98410004162494000b12a10a03030b4090485a040d10341c8034000d003681c80c801ca00500d030000c1d0007840500340d181404c08448040c15103900004c107810703480381c40e120454120600c0303031001584080100076010411344070b0040e6500100b4800b103201d0403492040c4000720405402007420340ba0002d071000c14540705605840141c401d2200a2008000e4084c240f2002c0440d405002c507150301d00f1150115064002818101c882c5190019014540d00c00140d00840c14010084542500603207641056041e0b1580003030010300400c82a040c0c40b01e0034044000c0034481c5c000c0100080c020519120000c66075414140d40440b0490704c2c003c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893803785 1250 893802535 893802643
    0x1a300112021f0f1d0a03020405040609020409080915091509010c0c06020c10020604030818030408010906020c010c090e0105060708160c151713030e1003020c 69
    0x20814481ca606141d00700b42c5240d100010415500c0442140d03846204d5035011440c401801d40b100003d0114070741c040e4401c02c6010100014101a0455940540101c030009211074440d00820243d414194040703668030000920800c103407600050b0105020200c1c0c0c03c41341071031540c902143c01c020841010008070340b07000c698880369a1140206254665101854550480e5160b60180d0340703c2d00b8158061140404c0015410302e240f000500c1445990947c2c1c0d042050b450f84110b01412246031101441103000801c00401c0000c400d01410319154030031140180d0394106014983e08561075005141c04104441400304a2680c05035455410350307108881941e40e030b03452445c01031520b12034420a20010144130030400c0a024240ca200c0b0112040201c4518501007902800c440540c1c2a10680c0b00460300c0303c01041c8090410740c041008103210303040c101091801140050101c000041001c40001d4000030f013142000c41c00d0048403012222491084542c608120350a00a071003540c08025008142501d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893805035 1250 893803785 893803789
    0x4050609040207080f04060c0b06040212071103130e0105180603030724050403120e0106260708030f040816060e120c06190e0312120c041a30011202 65
    0x8a4a0305d0b010118001c0d0341c1d03a501d600c040c189803146d01e003d650141e107041c0021450f09050080350354090121907501c2c0165502d45c030640c2c83c074180c2007500b845444140002c4c040da80c0c000701c3d1800509100030401e603141d03141c40c1c1040300300740e1600000c0202003030210a04c9001e84000041c1c4921070741c03041c4d01c41304030188000000c407a20b100708054601981003038140014541c02100e0034040087c0c158062140206e50801231b03080c0c40891252015114585032a00f04000380c0c04e464859503010402a540301542d00c6400d180b568001c40010603000c800054204003060082003000c050441000d5100031031850514090044054800c0086c000c3d11071141c1f40c00c901c0f4080c0001200000c0042001e80c6a04102c3e50704100d60011144010105105020740c010740d01c0d00148120044200628503441c0c00620008905a010043c0131515039600600002c0b0f44080010892940c4500300c0c0d51060711a003030003203e049140601e90140e110761210b5440030003d00c8a1301c02040c10360b1481b5404051600903840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893806285 1250 893805035 893805037
    0x90b090f13060501090b090f060306220b01080601051c021309050c12030309010605010c020f1005131203081e011a04030b0a06030309050a18110702040e0a0204110405060904020708 79
    0x40100403d103400000305010180740e001d4505d14170203172582e542c15542d40c03c4074041804142c4042d03074150310090000780f40024618822842400100380304c507540c40b8a44c0d0320782c6008020303009403c1c0c580080c001440941004152420404007014000b00100002d80102d06565862140c02d011181c9803e07a007030034071604002c1c2c04230082d0050501c0c3c0e01682c070002c40c107407250411303204600c96501f00000080d480d803048080754203030358004060000020311141000000d958408a280034003200340601c0c0c2c00d00b000c1e5482000148950000702003c44134500c0c009100750b100510032800745010801e07104902a5603414070b0b0560f190107180e2529a00c859503600e589008980c4010300e803d4911003000307045032941d00080c044920945614220780c0d2900d0810810541e503000f0510518000041041c00c1040e50700205c08000246c3c3c1c0c1c007880d20002d03401040980301780d03a401c29040e51080a0850850502c3d2244c600800b00b108034040c1041d0030000080c442e0b1055400340c910403a000f04001c3e041c40b000d04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893807535 1250 893806285 893806321
    0xf0605160515010f0f0f0e090a0c0611060717150a05100908060c0403051203060103060b16110301051608091207290402010e011d030f01060807090b090f 67
    0x5011500d100c4002e040c0b150144109000301085241016000a03613600940d01005c01c4e51701151100c11600c3c2800d030360704c045410040030384185125207041c8001140490381190b0150140d070345c8902603a031002c0c0c290341c600b1902034220800c00000072540d00e650182c41e04c1c000c3d007107200c003034008840000840000d441080c1680140b81c1c025060707a14045a15004075660381115803140a40c0c8444d640c0e100606641d014510010380550003162400c086000900011b6600c9101410001082c0d42c82e0140120641c105004a101a010a1600c4402d00241005c504800c0400b1402840301d8a010000001040700803400c940138842d0000214085400c188410408100c1001b034042d181c20044c01c045200509503024240b143c181e91244003540128945c480c2e1041c0d40603180d80300f03001e160b0b03001107460504100403680303600c0d040305840c0035607642800312a001d16541c00001c140c1e0f0b82040705190400c20a0351029024629100d048181c0381c8554414540c0180ca10741040800c0d40c8040800303410320991 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893808785 1250 893807535 893807543
    0x80f1303080a110a02070f0906030f0b09070e0c0a0305180d180b180a12031d030f01151406090a090209031f02130b07050601031203020c06101703040f060516 69
    0x4201304081c103500203079000071160304c600040c20a65880c2030680c101c07207403400003038244641138880d64089040185d90b613030814601c0003102e85183e40d808080c034200f1015501302106010002d100021113615002d0340c1e0b04500081c841d0921b191000704041e940d50601003d8905000814444861100341c0400410003041034100041e5900713140d01001d4244203c50290a10415401c203011940140c0746a000d07101d2941500c0d005062a40300301c100c002801785075000d5505100d07030030680d8020882070141c0d080314815a0000c03070340c080c20110003480300c0742030103070344c5014490034804465103540e0003040303100325140c00c0c4c4d006075070302039a0001c00c0c249650f41e40d107a410f400c00b104c100f8840c1d44507540200350f8042e2010001341525141e1040c4601031041c0300d0040e1555100400600215101d02854403220300d550400501d0490000480c03401c3c00401c40b0418100307003088030100044099210310100405144024501e0241020030b042000c0e00c46014103002c0020108124403150000500c4102003504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893810035 1250 893808785 893808787
    0xe03010501080f07170c2e03090b01080309150d09050a05030705070b0301142b11040b060c0d0c03050d020c0c010e032806110f0a080f1303080a11 64
    0x12014010ba84142990345a1841e00c16400005035000d2110400701d0301d001d01c10060880c441c4582d0070080b544254515840007001c802c44954000344c903c00314047c0c81445a20f020400c512141000501c1d075105902c075000980040010442c959941113141c20907911000040341c45003c4400040010151050000c0040c4516000c0d0401d016000010b0020940b058044440361619400461702601081c420300e026500301350004050340c6031000840c400e0510710415a50850b681c5043c42d02094001c41c000e0700c2081c20000d891069040034020304150400554240b4940140c54040d07650310b03084400b18400b0010b04042c510b04144c42102144c50010803040150345407580c007a0002c1c2c40c0c1c1d000704603a40c00304200105441c41c40c01c0100e003400040e0050710700c9545982c100004810354a6001c0021180141ea0303140da1141031000b04054502400780c03842458031135403003501c05031060901414071520603012804101101c503000d031941500b0355051038103a0311503c0340035203000a04507070305584154000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893811285 1250 893810035 893810039
    0x15010c06020d060b2d030a0507030e07061d0414040f05030405090a0c02011a01050a030209060426062202040f1401090b0f092a07060504030323090c010f0e03010501 72
    0x390251031204c0c82545074400700d104003240c10741d0260001c005c50407013400c2800002c940201c5036004550003500390501280d008a49000c550508215400510200e04000d2405900a00204651000802c1610200600083c0f14170710190f01c00000c00003080b80e503840340094104142481610000c00015220b900d090514031020f00241c00c0c202d120000541c600180e01e561a04011610051210113866241c030700714068104038040d5202d00902900030074100400901c880220f101411100c104003280c0c41a41115001b1034105003020346940329008007081102600e1a80e200b910350500d50443e00024801f020300301c01c001a14240c14031504a01d00a00001801d85040c2c00281181000b1103840e21140340400401081d4201a207210303030b9480c40c0c885640501d2424100141403084031440c8103040012580c6c402043e18170032201100000e4440118117407000b80000320703400b5506503001198451401d02c140560303031a00710851074100524540312100c500d025031030f04950110080c0c02402950b07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893812535 1250 893811285 893811299
    0x130503120c030f0a02161b03050a14060f04080406030b0a05040e01060608062205061f0933030f0b33040609060503040c0b03090c1815010c06020d06 65
    0xc0c108903041e105454240b40000da1302e0015200301d40c901c000040c4041c86202c40c0b511801440c8040c44919810750039240d00101c0810301c100b154108403031207050b103000140c02d0b00802c9401c2100241c00182c8201a1b1000e001c0040c0b5084290b40641d41285000540040944005000c41c900c991115420600d01081000c00d918190000310503108503407121211912480c060040110154005907021a2403004c01000740c5011303040140c021380001e20010a00304020384144028101158000c081402c01c1c2c81048820b05a001d420480d890051000004407070f501c02982404c0c0b4042584020035aa864060100350855408440b6281c001303484400242c00c400e006500540e400d0005c0d43c00c1d1451004421003038a101c10485094036465904e88410b07a20f440c5c400c0d00c040e007002e003040703902c2002007002081c0070340054055403140900c0d20040c540864200140301a0f003032650419481030064004110030f0007103100108100390000e203800341044402d41030120090068003c0c03050a00e0402c0000074002c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893813785 1250 893812535 893812537
    0x1b09030201080109050a020d060603020d06050a05420415052713060902130e0c07020915030d0306050f0306010807061101020c0601270b090406050612120d0c17130503120c 75
    0xb40e458401cdc1081030326200e03000c01c0055802c62065942c00045841440b02c00c40c00f10324035200c402d0541e00c1501010307450f007004030009080c11802d28940540403030b04210362814808400c0c0700003181d040085c07a040d4150700040c0c0047c3c44001c209550088880c0141c05502c1e5142103c015006c01d01e0100030080d151044e16010794052042c80500480e485030124081c0c9011a040b8040c8011065840c5018165803d11001c803400401020281000518141d01504c0070700c2100903212251358006a140d0a0104104000c1c084c0000c0f14040c0e800000140031203000021450107440140c1841045100103070710b514064406c4035001e16060007450300000e4440b105032428024000c20200d1170644400c45105c4108070740c06c2801c0140d0040700c050118002c101c50b64440740c2c2140014200302205a998130440d441e2244003000d030480c2e618000780100d6110b40e42e2098036814900d5180282c0340c0006c0344221031484c540a02500b82d603e40155100041100800440d6042d03030440300014101d240c420040c201c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893815035 1250 893813785 893813797
    0x1216031209052d0102120706201309180827030307050309040b21060720060402190e1302031b0607150608030d1b09030201080109050a020d06060302 65
    0x300320340010119440c640f2224602215000d80f1003d05820b2124091800c4907038805041415030283e0148403031808040001022024000da0000c03400101c901c1ca002c014100c11400c40d0b4038003106105a00b61120340030303580c03800c48120043c0400c4a04044680d03600185203038000034080320000804c1e1102c543d401c21a00d07040c00000340752400c1c0b2800d0600713040d1070780b098a0000785030f034004104480035407134541d000c0100d0355806000030150b21074000164664441c40c0e02010044e41c490401c00500701d81c0400040d03041c074031400d000003940c003610050581e100c00c0a88024803941030300400190180d0300e0700d003001c01040c03a252840414109a83e040c201a03c22103400e902078020480021181005000d4010104101030452840d040c001d44401001218a05071190b10a440700000501c07100200b015201d070442c01c003400918861814040c40d0841408080082440b00500f01040541c0c0c1010046044420010b0301144595840b86001d00038480c030004103004c980350440c0410055899406004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893816285 1250 893815035 893815037
    0xc0d090510050705070203070303050f0708161b150c0f0206210708040b0604090f021e01031a01090e070201091b1d0903030a0b010306080105071e110c12160312 70
    0x1015440c1c50307004031396a00c24000040c0d0564030402017080081d1040e001400110100460a070506000d66200400d69000300200d545030750300780100d0000c1c040007800d122041d001c0652901d1029180c410341110550586030900240702e90f07203081102b41700e003940d0068415a80203041980c1c41d4080d100941c507a56007144a60440b5919100040400b40207800347e5001e60741048418046035610020040a0059000100d03540800d420707150700180c603035001e451038211040a0f01c0c0314503c5031400040444110303416005060981c100c00e10201c1e608000448103840c03096844020960340d0b54816409002040c0c40180560545c455644188030011008015914040055819181140041c0740d5000d02a29416070640040010444a07042944294403000c01030502050065031901030b9421542c00b00c0700c5001242c80d40c18541c03241c0102c0c800009504040c1d0804000c40000034152564418002940c580101c6040d003240c40c003c0c5c002c2205801c1e0074017a031849104143c0320722b0a003009001c88105a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893817535 1250 893816285 893816291
    0x90601060c0b06120c041e0c0c0f0308180a0302062e0608090111030c09010306060c0c0e100b03070c0606080708030910090e010b07020f09130b0c0d090510 68
    0x803603401d200d241040c1d809900b100805401d615908100800b540100b00981c06521401409030140c2d00c0d240144451000300b0030410a1040480d00300100350303050346031030310708200c90707601d81400240c031030884180050340500d4481e4584e0780e41d5065888940d81001d411016104070307c5200304042e40050698814103000c04402034072124401c0c08400d0000c5240340c058404059070007405098800d02c007460780400184004260104440000d0070360742d0041d140000401e10014400407556014025403004201500d002d0311003290030784a0000240d0716020340d125040ea954041101e50000e40c0c2601d000e4501d015190b60380b410460405403203000351000c1140d825041540014002c20045012803c0b80c4421000c4d5241140304000c000004140294600501044000210340010007400b69400b07000c6166201791b5500050040082c5400000001403007040b0503001c001d1041c0840b00042002540250100c1107900c03070000008081c020000c1a802107480d040c0400d003130100001f1400c40c203020f241810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893818785 1250 893817535 893817539
    0xc100207030311091008060f100804050c0a06081302240a14160602030a0e0d0809010e010507050702010c020f1509040b24030406060f031a061e1002010f14090601 71
    0x403140a211078485c0d01c41c14018603424418050215507a01903001040802002c0e00030002501822401940b035001412110410007000070802c0041240e07981100e0018005107040c1c401400c580d4024001e200c06806c07170840c8000c41d00c03100c070b0800200c0c0301d21002d800100d801d00c680001c1130b08024004000200b844480c0c040918a6208841d00072884900e104820000384e11507901950018154102e420b9980d507240015880c113105030407101c035040da68010503042c1041ca0030300b5600030b400e4151040c4d00d02014454015000021100410b0b82800c0001c00c0064038000201c0e50641120150b80001e0303280c0c1a2800d0300e52440083c10500821502001082580c1c8144403030802c1350a1081c0d071540fa8520b01007a030110702006190b0292150381c010035510745810644064a0040e841224505810b85030303803180b0f00030844031036400708090368591269034034040710301045a40181d50b43c1c09203440c0d04003046205d100f9003002c1d1a40c25440d80030300c0786009040529181002c100c4104107a0b015581c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893820035 1250 893818785 893818811
    0x315030d030603030f030902150c06010614042102030a05011b200303010302120a24391b110306090d09150c021201050907060e01170c0c1002070303 65
    0x40c0b801074a030541d852510b0000102016002083c0100050b41e1120721250301c0b01040c80d08070000c03c01e0405000241c4455407400502178078001800c9a9450385034000d00c42800000e1a20a1090000e011601000e1411301b8900204e0308020100d007016081c1c2d403c204d10010ba282d2142d003030001140303942d5501d200460a4900d0f6a4200600e02ca4040c0c00d03030420401000503207000c0f070100c40da4002c014103443c42125a543c03801000799007203012484010500d12042d2841d22389214001d180404424146051040780003c441050040204050081d40d18074000d5205441140c801c05805140c401809000c070b11800c1070b0141c1042c000403c0d00c41d10420000500342480450301084a20030360319699911810420082e40300780c20140c13450200705c07080b440c40000d80c3d1034041322180510207000000b5582840c0034800d013001c40641041c8180524000d400c021071740c0c4661045852142d001c03424900e0340310600800758920880c90b1000c040e01c43e895941c04a07090b983d0083c40c0d620b119450400102d440ea0b4a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 893821285 1250 893820035 893820041
    0x2040903200d1e0203130e0105011805010509100203130602070e07033e030a0e010f1125120807020609060114091f08030903071e1502070b0315030d03 66
    0xe00d40001950340f04088403200c0d2000901c1c9000c20302401540d0411405086100b40e504040e407081c01006a0103004200f10351300007418480b15070754011000e04603410180068444e01c120f40407240a0003505121080e05482801a03e03000304042c08000402c83e03540c10000e5488013580142440c1441c0c404c041803601c1d01038401c1804d002c903011445010a0458920a081400e4a11907003545e1004910401154880c50006600c038204181000640d165415040e074211884800d2000c0b07440d14041001003005140307403d50b02e5240c04200150080b500c3c045000403924000b800050120f010b22071001d45190300240564882c5600da03007110400c0d81d40e402c1c00d542e901828402e40c0600510f0440060f003030300b4916681ca51058000c40555003560300031315031490000940c0d20507500384d000850f42030102c1c503040c00f00c00018070341c060342e203d100442d0382a1259049168860780b031500c40d20081c0e10b21020f000f07008510040c400400455160b140101011106a010420540c07107401030804003603140380284 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 893822535 1250 893821285 893821303
    0x10050702060c0d0f020a0521040302070504110c0a03030c17160f1b0507090b03070b18130e1e030a0815010c0203010603050a030e120a02040207020d0204090320 70
    0x203801821151030300b49a0000e241e200c40703048840d481c0c80c2c109200400032140014a141c03030942e610180d03038548401e814413091040710520031802d001c500911011a90009840c01900c1e021200020301e050500c04404007442072002e08102801010303011428035405521a02e00e240c26500c600505400b2140c03841c8410904580c10542d003241c224120300164461207120744540010302b000201c0b900010b903001c190070b45c0640103d92680c82144207000e0001c080c019521250340039401000301608040d61030381b0a005160003682807640280380e5400c03598030717041002406c404803031082141d241200c0115885400407603c40d40c155607602d8010700082c800108581150105aa805240d904c8100303400301540b2140380d18034100244c0b02c0d406405030b0780c20303c1524029481080103000c5d500a62801420300d10010707000302e1150300c0304148082a00750205104403141d604650059640b801440003442460005034060b40082c0b030301420320101034200700031074001c2035500c07040f90051218030703c003136581e20080d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 893823785 1250 893822535 893822537
    0xd090e101203120e250b030c310e010605120412021e0a060c03020f160c0b0d0e0c19051504050d200a0501050403110d140c03100507 58
    0x8803908000d6404105800c1c0e007898403038a001070741c0118581c1040c0540d1151418a10b0503002800142d00081080908980b1a4900e10212076041d10b049461040307030100504003030990000280d15041e511140d8540e08000307012122440c041203541142c0070360f50190f4066503000760104c00000c1a8503000f001550914001386241c2c40659a0344e036030b9800342265500c1003e05502c2081d084010340b14140113100300c25910f107c02003013140c83c40e08081c0f064030154551601810310400101d50031181e918100c03011410108103026000250340f800d201c008030aa0301020901c0004139005084076003c1d04269055034254044603007800c00c040c01c2000050b0000c51028410b0fa90f41010800c9061044021080850b001c00c3c2e02d00b01607441000c20704104046e9001c64201710f008500f28094500401880c0100109503969100241801c0c00a40f061203280405400300b8144d142258a6649070740038096059400408914450441200b45545414025400e4402c0c05080c240c003240f07e8017440b40328030032045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 893825035 1250 893823785 893823811
    0x1b1b0f130c0f1214041e0c09020c070f0b0901110f0d200d080a090807021207030b180a080f0d140123030a240504050a2901090c0512090d090e 62
    0x1407070752035080f02000b40ca404401281d07001c5901007c50704068052004007014078001d60707141004a19281004002e411010342c070b540c20507050248a0505090744c00c00c01080c2008510400f55019051925110115241c0980b007445440c05015034481c00c0104040001c800000621f40c0041c0e400d03032108a490840c4000400050015001d1007640e00241540c50250000b6441c2208580218038038a4007102c22000a42c00080100f0401088501c610341c81f00c000c4159098980d0074203c0c40c0c0e110040c20b4800341412030007142048640440100f11801076034018801c0200c4503080d6558070500342e09105440c08010001c210500d2006048130b21031100c440107000e0701d841c2c0c14594038200c54000c414090704071056400070800600e0b01c144185806140208020a0410058a465032900442440c4060401000c0b89072251540e04c0f24101419a404694080f80d4065503003000c940c01e0003000501e41c01041c005051001e03441020600c0488041165507102010351140d4030186513150030703a2200c098146c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 893826285 1250 893825035 893825041
    0x403020a0b010e2a040f031109010e040b0a0203060f09191a2416060207020906010c0f1410020f0c070807120605060f0406030302031b1b0f130c0f1214 66
    0x1203504d00450b601e504442c050303040c6a01c0d1900e04404080c0c0390811580c40f044615000498941524107070300502098010303101514241c1d40d28800114060441c019064000c404101d081e9a081c00070f89043d44090070000152900306200401c00b4420000300b104145040e6905180c0241c01c0c4135510b8551000cad055008000300d01c2580d040c41e1000400c2441c480c4414042c5c03404000f01c00d00c007074240c0f501075200580c4550903030041140541024081c0ca05002a01079050700084083d4503002403150080c0c3d0030303c10344040500c0340382880300c00110b0840c464170000d0101752001c1114068800000164215007429845d2201c00e175903071015005104500301c0e45100f1000254682d00032550007103020703101e80414441a0042002e07681c1c0c075001200075801c04161440c50b810980044c00843c100f000040204050007003500020890401c142401040424011100c2d0703222508201d580c288006402c003c5804480c0000700040c0c501400440007646a000201c1142c80500030319190360051202801551 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 893827535 1250 893826285 893826331
    0x7060b040e0a0f150509030a02010f15050d1505090708070b0313080a030b060d020d0b01090321021213080609010204030b0a0c0c050604060203010603060503030408030306041d060403020a0b010e 85
    0x9a4081d013201c82c20064600000d0303071aa94000c20f40150140380055131224060f043c0603003900c030300301c442e05d24480c50000c0528160050304c0842003124400e03252001610000e082c001540141240b0f40070105050601340030741b6210014a0310120350050b02501d26841d11850440c0ea54441640c5031191010105c40d607a01045000d401440c0702d0740c0354200010021103c00c045000b540060703407400003c541c041b50340c9607003075440d0003010f44d6103101340380c00c0140e00c4c15565000c0400702170700d00c805da4400340c181e00003e4844c001c003d00512001c1071070750340c0e4490b01008900b680b28a0f0710b02420301c05014020100304904014003c1d9400e5a901c24500b47c2070755030300e0001a0050084900320800c0090440c4c0785030200d041170112038001c03402020096a2076041910140940c4c0aaa121074040d9100308010401030b07601005036504120104c41c042a5034088550042d11122158400006401040280410150002560305600e4400c02200341d6a81c0d0340c42800364a403004a5914110040c1030022540c81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 893828785 1250 893827535 893827553
    0x18100b0c0a060c210204030303050a2009060f03090601080118030507031803080307030b100207050627061c0b01030501060c03110f01020a02210703170a0902060703020307060b040e0a 80
    0x442964500050040313800360801c8500030b24140390040075540000c05100341989400f400e94001111082400612690744e0310340c0e4030807074016580ba220311000c101c00b055075030b50070111041d2020103065161281082550309890780c0b028030a543e070319860103807540e000308140c0780d120600d00d0b00340e140d05081c06c10945043c0c54039030b03019011101080b26081e0200000d0b02d4100954010303180380e50300044108522040c400d00c031810950280030341d40441000c1002c1d0703490000302da44100e0120303403054210842e032400b00d5503001c1700bc0f10543d1003032010451074101451010f4a920080c000b0f1802e010700c1d00b03040015012aa000c0c00750f00f0016085c030040b5404640524160b80000c2c2004040b81d00e40340032081d0650881e0815080f140050f0000e4408100341048800400710b04d020780c42c4080d00c1d260b2030780c3d805800c070010305008541719064100090a55042c070390203080e4590300640a0b80c0c2c2c4500c940380007500c9500180003124080d10b050844080c9041500c01d401c1c2c04c00d04900201103002035500ca000320 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 893830035 1250 893828785 893828801
    0xb040206040522060632070f0b0709140a03020409030216061d060f160c080601090225120e0303160c0515030c091e18100b0c0a06 57
    0x240c8104800940c90310b8102ca0104038030703d40d00c0c0c3d00c26071010b10800002640c43d294010f000708901064803da24401c500001c03811084010004100ca04130400c40c2c0603180180b51000e04011b142001c0c0d401130201d0500581d100303400382d45c0c030340419944451280e4180880440340b82e40120709d070101403005040590146240c10b0080c01254032084a201c0000710000164200e1710019403404412a00f05045030000300c6e94110890714141401554103008055000780412005c21a6102013a0350600204600810241c40f02c10184c940568480040401a5200c0e090700780e4000e1000c3c00346008060200404800d0f1540a40c0d04190700004480c100d890201540701c07180d05000802054880d45050781e44070741c0f00c6100f80500c144840c6031908115544018000f40303023400e0303020810065452001d400b102e078041b000b142c441c1c0410400340d2842848000b81c00d4481c0e0000043c0e40101045000c1954942c49601d55611007031450340c403480300f51524011341c0300a48103039204a15001c000b50640e00082c5c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 893831285 1250 893830035 893830039
    0x21603110114010b0c0d0305060603041e06020c070609080c18100905040c05090906251115060a0801090201080a022b020c0105180a02191e0503070e010e01030b0402 72
    0x54020400c0300000b0016030280c2c00a04110f5001504425550050003c0329050045040c1044689040c40102e05a03200003000182890403500d5100c9007819400c3d400c8000b80e03040301c1c0464445e00700020f026505e0704d0030f0080c00c1c08074100c1031000907004400600b1980c9400064410800c0560b001000002e08c04043c000046100380c400020031078540307910919101d54010030f820800540382c942072040306003010b005401142c01078407c02200801c881c0c2c050b4414104030ad00000c61500444046500d040440b6841d0500c0c021210250803201c6105180c2d80210821200808900c0da00d000c1c01d400c8440f030107802800304002c14005030f608211a400740c19503c210180d4201c0101411349540d490780c150000318220300b0b90101d5015900b100c248165940600716580da881c000d08059a2282c0c1e580034044020b101e084100c10070040b03013000b251694010118003901c00086041d18801441d02600b40c020720f0f0103071080030400218805907101070b40c101c6c3d85511810130307241d08503280c072030300424006c009030303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 893832535 1250 893831285 893831291
    0x1060f03110d1104210812091501080c150a0f0509040b0a0e0708060a0501080a0e1006060c0b160c03050c07120803150a05090a090f021809100216031101 67
    0x507290000310f0140b281e01101d0800c0d0190703038600748400350201044042a450024440701e282000084512085800b030100c4244406038aa95640c0c400380741622150380d41030007511110000a102c0000900c80002c00011660104c02000d1046044081d0003040704000000d00c8880075206001d004400411040740054804100a20560302050f81f0b9540c661010186071105010840364552005407141c100d032007250354880d090314081c00203204810240a40076a41d0792100c18092188040045802001303650000b44802d5540b0f07100540024800c282c25503000b224500040d40e51803400c03d2203040001c05480d198114150f0313403002c4409402180c100703e40d82c400d82c08003040d0004480202041300c2c1c400c0710021742d64640308164010003801020050b002c0c4400440520150744d0f5001c18951000803500f00013800e00c5203003010204582107a0b000380d0400c519420b00360645030721640c0c46119480400480c0c44817815000d054040303104000c90300142d0050034a040c0f000a100e940b6001e80402754070008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 893833785 1250 893832535 893832547
    0xd0804060c08090301141b12010303030c1806020705010e040b0a120c08060112061109010804110d020402041e051e091810060807050105070209040f050a0b07121401060f0311 76
    0x2203421100c40c10000c0d4045d0080324204002182914a448402c5141c7d0018034207242007024820700310074042c00001c045c0b6403038040c5403200303910515512506c81201075000c0d5800e03940755000794550003c0e0041310b00040c000d40c030354089410140a40003020001030101c4a00c586800d4400442200c1c040303048032103a000e180d00044d2442e003042100d01921542d8085080c0340c05a140001c1120b15030341d52000315507030030300403800141e81000700d1750341c0160856040e640144038640002c000d21100040254018404100480c41c1f0f2051541c4d1307050b206e034000b004c0301c034592104108969840c042141c265604480002c1e030348075052913140c4540110200325800c94031345d01c9000c058100f2a10700d011850711035540b803040050b2142042800c00400c0c080c2003441c40c015054002c60b40c04040100003070502c50b10b240005080000c104107251246800201c5591113080c0a0700041200070f1109051407940d0070010303545404150302c0c582c5412140315441304c2001c84072028003a0701600e080744031000c01c0d103401c3c0700d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 893835035 1250 893833785 893833789
    0x40f09020306011103310e151504060806090a0e030415091d1b0f0405060f120f010e06010212070609020a24080a0501050f010c0c0302150a030b0d0804060c0809 70
    0x86c10384031107161000d080780c907000d00c01c2c640084038080140d1885170f04c01d10104600b203001102c55801c070541c04411070751162010080390002c41042c2c0f52a0002000150004005500c50081d074041c42c0c0466480e0340f01d8803100403400c00e881300002030843c990410081040310314152502e004405003141032541d4840da80d01010320508005020201c90810307840100701d44240c461482d0300e80b00407000781075800c041250210303405030700460050501608001501955040928054802513403444400d00e80914281d500c008405d2020310644c1c0046622001140b81c66002146d04540440901d20343c2e81420030307580342c81026140d141d009903000704030300c040440e07c02c01a03040c04a8481d400150030700320b81c40c45076008200c2c030300003002e041d502c5280000500c6141d45840f00340c10140b50910b80107046440504001400d000151f100a5002c01d00b040410a0b544100000c2e25962055440c1000001c140c0300c18042400c6400f9002850800104428070605000b228180c0403c0d0040020904103d54100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 893836285 1250 893835035 893835037
    0x80c0d03020645010b0d0c06050c030714071502030f0a0e061903020c210a030203091002030703150b09151309050f040b1003050307031b06151802040f09020306011103 73
    0x403103d280350150492142101024000d15000700002c0d50094001107039512290302c91075040c0180810002d00103042c0c10091001c1081e101101d410000c256502140c0d159425070340c2201d4414080b005504a0300002c29500100903200300040310052a0719100288104941c40c2c442045d0780c1c0d920074010700800d01c0e018008212011941c450fa00c005944026000203203203000f52030414034507074140702c03a02d44000c0c032804000e440003155142400b58481d1200c090050030a0312145040b81e0091021041201c3e05501d40c2162060004540e04500c4294584a00d00c006100e1000780c80d03001402c070b08124030030200150041c072003104032245901d1b09513240e1050f8400c0e1001503c0b001c1100d40110180000d1101051136903030896501e460070703504245141d484a031a400f9160002c0c040c003089140c808000c01070623026480c5517a001c501086541c0c0c00c0c0c5440c011180c0c4902420880d0044a0380c1c00035007002505c2110180c50045115404080c9011118000307940000c01d00c03410446c1c40c00c0302d0100304600b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 893837535 1250 893836285 893836381
    0xb0d050d180506040b070f06021215150909150f04060b04050909060727030b0403110c042304020a05060f0d050901051e0907150207080c0d030206 64
    0x298500001d004400244421141a80c00c1a0f1007150200010071a425070740c0102ca4500703521132000180c0c6212410944002d0203800301d07a0051400d607008001e090701007041c4000c2c00100c102c0315071100d0000030b2010809800349015003500908003038003151002511141c8401400c0000b400d036442da4034048041007e072110361b031100600600c003050500141c1b0b408a03035507030b1108000005024914150500a041c80c8400d005041d10751a05e14482d1a00c91240c00404051600050802d00e9401d00d03241c02000d03590b480412603070134007480035100d10381d203014012121340c800308014005ca50081008000700080000d03008981c0a11000c0c800500c0e0703203410000d0415182e900340c25030f40340c1c0c094025060545100601600059140078100403642c0c241c14800c08081500d0003031865640d40300b02c441860b00c01c440e0889001900c0201d06c664899a000400303101391502c44081d80d00300c4200000b440b150940c0d0b41d80c02070140e0003940001d85114400c4501041c641030404584d40014011009101c25101030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 893838785 1250 893837535 893837537
    0x608030a0c050c06090d0b04050a0b0f071e1e09081e07080a020105030408090105090d0804060201180c0e090a080414010e060c0c0f0409150b090108150106030b0d050d 73
    0x4420305110081c429150404030640d0704c6807900c03084900003018604045401010700741c80d0004070b020306c0400c0028444a903440060b107846400d2003480704130100e100312503080000e4a5101d40420f8442483d90110382074169480d511140d54001101450491054500c1c1c000c1041e4118002a145d0301001183c05051040071080a2400384550700750811040d80c00081c2c00c0d901142d03147c00141d034010126544180c0003035041e500c0d0366113240101c1d0144230b0220103a80c4002801012000e100b6083c00500481b001031300200416403610400084001d01c200d07018007140b284203400c2103000d580740c048692000d542401d03502c10307841c02c0d507803800940c005030410742100801444100f0b59507044002104031795000c85100e41010503442482da902e01e0078640090140a06a14440c601d80b110741015000d80d50210102a05000180103000148242c41441e48205054000061370790710110314885046d0320149031414503030818000382d01900c0d22100032a0045c40b03031201da9000c22018401100e41e0486 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 893840035 1250 893838785 893838797
    0x2130e01060f020f06060402070201050705030304031d0d020127080d0503090c2d0a120528021003110d1d070f05010c0215040305070f0602060a0b220608030a 69
    0x10004002d0251481014200c25584803050501c010700c000580554085000c940160350b0780402e00c0100c40b54080c09400030b0280c030011092000309604183c4800e1101022001800840403070003c0000c030314901840030740450302207a464103000d400f00f014007880940d8a2003c0c03c246035601055882d103c0d40d00661000a18044203102e0b120409100b400720f4040219600100d40108001d03d2150302004a40310001e0424400002e440d5258503440c20010186102d44001418440c100349072200c0d00303071580c50440d940d003e0042d20702c050002c0c001102503070003034016511000c46140039001046007111240c1840d40031302c003c1c90491076134028001460034420b00004801042d4100915141d001e4008030982c1047d24010700c0103903070003198000c0064040710312110744509a21954507901c1142c002800c01d00a144000c0b99140300254200e0445500e0b500b10f408580d0b07450151804c441c143c51140d1707844844d596401140d01d800765403941d007a585010001400e01c0c2da440a0500d594400d440110115032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 893841285 1250 893840035 893840039
    0x12020306181e070306030b1305150c040306061a04050d0515070906020d08011a1612090302032803080915070e010909050c1b031204080403060f0e0c090a02130e01 71
    0x10070007504101c0500b410b000e100c1c10741d5108640108010238100e24074940342001d07001d02c0810004100b200703001c902c40e0516403c5c9410500100da102d80010340d0420700309400000d0107112490035048280c000c011841c140340c1044100701141c0c0e401d080554044c403030301e98042c4482d001c400c1d50038002c28054648034034803481c144001e418000c10300c01e071a042c0134840c0d0040081e00311f1183c00000d50044110010b41d01c0300d1500090802c0701c407040000d00101c036246c0044010b0fa0b00500c070388041e68000c034110b59030248500c0c00c041d0303000004c080114054101c1c01c1c0c0c403030000303010f000c1160f04441d03171000340e070108044419151640002103540e5030000d8035440c0c205880b541c10080c0c07140640002a0184428a424018400c0c64414549083c400d50b1420b0810141c02c81f003071040d0761600d0124102407040e414a400c0800c60ba030810b01040e42c419103410255000090340d48900c001e00d00103003000e00080e490a20800c0120300e0700810500a5507000c000c42c01d540c038100c554400161640502e102c0d1994 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 893842535 1250 893841285 893841331
    0x12091201020f1206030f0d050a030e25051504030b0c0d0203040c0905130201081302010c1712060406140d110a0e0a0e0a1e060f02120403020c101202030618 68
    0x104001d0301c13040c02504002d01460f2181c0c1d0100d0150360901046c1007a9948504070300c8203e0050202c0b03c03001c00d0314044c21180e45010000c02000500d80e00d00c11905150741e5031940d0410284c01000f8170b0402013480100000c1000503000700500c2d81c0403100300c8040f03003003131451501c08081e0307807044408840c010098202844410110305c41d450700241241100141d105583d4006003802402070240c03030543c0c50360a4010b00b10b80c0b00d03003000c940156100c1c8010360400100002c0762940d0b0407400856003c0540c0ca000a145820280704020407913406482035100c0380703400c2c0140040100541d00964440542e40100703540c07a02c0e40c0090300014414155100b481d894070360300b034070111881c0110030052504112130300780c04a80315481280c040039280c100121480010302e044001001e0b290484103c032400850030035100e0b44401420740c401c5005e6004d9420141311078003000405891040814042417031400c0082a00c9080d0b0f02440c0d000c0f10241c04401c00e410100b20614924000300e038180118010350700c1c080010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 893843785 1250 893842535 893842567
    0xc05060d150803030c040902090f180a1128020a21020105060a05090439030209060910140f13020306011d032e05010605090406080f12091201020f 64
    0x145410000f035801c42c01c2c00d0511040c28442c0d03210791444250086006180c2c2d039640511559220302c001c0c8408090b6502a0100c05503405c110340540902d49403410348566007200404880380724423882c101700403038544601d080101d03803490583d00c02148140c10030700380083d8640b07120403c00086541c40c4849951054402829203a000704200d01502c01e401d8200000e40b62640c05c641c0065002d0075042c0c02020550103d182a00e034018640710f240c24605001c0312010109104400781e030700130380340000c0a9a0382d0b4284510b00c502030340d02c1c0c0c901003540442004032040d017041e0503103c0c5400400850341000c04e41c00045170780200701c0c43c1203080756001003444180e60300003500004a4501b5075111130032140240018dd183c079034070031a0301c2211881c800a1030b241c0840000180305510300d568108440d50315240c00500c3c1d508a0302c10540211700d40100800d001c0340000d0b80400305c121010017051204452041170391190480015190401001c40021311103c100303001400c4003030717094054952a010031401301c13400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 893845035 1250 893843785 893843789
    0x1c081008010e030f1e030109020301030201030b0303030f0610050d02030108010518241302090f042d08221707141011070f120501050a0b0108130c05060d15 68
    0x280c1e241028031404801d0200c192524090103200617a110300c2c00c03d894110481040f4540c16840c0c000000102d031800e000d50155040e203000307036810004040d840d424943d0380e10003516100c410075000e02c00511289800c040c3c10452540c0e03468500e0616150b05a40341c241d800a80002c0c07001e9441d58100004010692a811102003000000308200f0b2052a08070b020003aa09138200780311807004000801e400b03100030340244800d60141072a8100e01c2c0240c0705100c5084150344c200e400005260000c0e00e882031a46a04d00740c0c2e4030505002001aa641e611800181d005010f001a9592800f0480c40d4092001e420000140054101e000910141c1896203040545d207400280d10484d48407103510483d203900e400d20410700d0031030510150144160182a20700445a07005540400c002400130902c90801026041d41c18402c0d8000c0c40252603000580043d640300c902400e00042c100310000e801190703040e81c5500458000c0d1f40304011652900046041640300c80392251240d07455000c0f0702070401c07088400c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 893846285 1250 893845035 893845049
    0x614040f0b0d080d0b10121808070f0b070305011401030504020f0a030b041218060e01030905010f0c09120f0213090b04111f05090409170a0c05070801020f1b1c0810 72
    0x40c1b49241d201000e0b0040000d144000c00a0750350303c281211610b008950181940c2e0820140c0d034803030000b8a0507140d40f40c200c80d03040f508c100000001ca81c0c2c0d90300074020b2074142c80e01101d041c020303000e851004500901c0300800680e03014810700980c1e960fa0711060002d10182d400740525000504e0a400d0480d0521002200c1c0740030400445a0102a619200301540a81d2864a00801112883c400480140c200018040e01c29440c1680282031081181d111080c110080d4075000b540f0780e600d0901010059103803002400307101d03600c01d80b08014030785103040018121070110000348107980c5807507521131210111400c40c0c0495071031a54112621344400300703c41d1801c501c542030300ea613200c8000c000c007075004035002c1c98052501d811034041000f12102041c1c4140b0050b401940e11448034100050101e400c40b801a1024013a248010a0341c02041c001c550484241c00d0070980b51803403800d218402e603030842e0300f90340d410301a002c0317031040c01c2c460003c40d81550703540790b65801c545040a0404250101f4039502442d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 893847535 1250 893846285 893846299
    0x220b18120d020604020904240c090501030b030304090908041d0109050c031003020f0301020705010e01050a060b03101e030609120305090a150c02150106050c100614040f0b0d080d0b 79
    0x240074541c00520142d0040d41510300c01d0017503ca0746080718a81c1000c2018100e80c0c0c0a940d40c2d8036035040c00c0e600220000200740d0f680904c3e107580c1c20040d801c845844a00c0754054004105c2808104401e0b004051464850380307146182c582e4491042a00007188201c901c440788552004002880d01401204d8005209404003840c40c10050b503207200030555840002d010300800070302005155000e5043c2c940c115008030080c0300c10496002c0060091501302d910500d0b2034600f0300302144030a4007105a0b8420a0080c0c00001c060b400e0144c008400c0c0b0112035001f00c0c520350344001100169690088000e55489074440006c001610701c8085c0603508010201180c945c00f002003d804107912001d07440324800106400074102840304c8040341031000300000c0c241070400240c00041c40c15884402000785981c1801a280d01d03001e40040c030700030717079403984101903040342d004454243d5454180e20403404038042003000590b036001c0c00081006400192010703540e01c4801b2410311040314150140c0269071808903420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 893848785 1250 893847535 893847553
    0x1201150912050a050c0928230921030705091c0b18010c020304060e0427050d051822051008061003080a051630020f03220b1812 56
    0x2c0e03040b08962030341461004401d0741001f444030785510441103078140100c05904040c041e1282c2c1d80b0004c094072030340110f1042c00b070800b414804040c0216001c00300c505c00d0300d145403207a00c0211102d410041c0c009511006c1c48082000303520584081e806540d11441140d05070740f61085482810603013015041c2c050341d05000b540414603601008840c1a6101814914444104d0802180003071141ca030058001e10282034021005e48101040f99207011710810441e618401054411102400b85c614680c25408100d80740c00c43c0c4c0d20701419001404c00e4840040d49150404900080c15900242e0b0818441c0101c07076414480340c03406200c840ea00c40480e504520400d8550755a09090b44541c0401904003e4045040c6000104c02d200400c82c450704150607150003014800030954030500c0303080d4000b0308405008260091400891550ba80035036001c041c6d03052020b0100c0d10b0841d084140711030740d09400c290303001042c000001406002c0705a003900201c01181012810310008085031250000c140d4455404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 893850035 1250 893848785 893848801
    0x1005090d11030d0f0f09060501031e0209010e060102150a0b03150115110a0c0e160f021e1501090c170f13030e0301050412030b061201150912050a050c09 67
    0x1160444070b00280c0000d414a03016131614010b03d880c0c10344c0301d8801d0500b4120b000b400340d56045141a6070040c460858221203c03089802a00303103030040290014000e000400c028443c0c03d030035552000303060060390300c4601d401f15052824081202c60080d6156100081c160307a04080001010040001403509400c3d4104030291611140044041c000c00c800c2100c210f448032014050001c0342c2e94004012080b058650704e280700aa030081314046803092403a0300c00c0c510780e40f25003158410081282c000c0c1210340c910f82c910440c1c000310080101428458100900c3c0e100707620000341030090413110b0f070002d103a40780058010414440c0c41c40d0000d459540d2402e0201d10251070146541201d0000650b00441c00b10340f4090300e0811902c03003500d40c03652910080000b0311a240c01421400c11403960204510301c560001c120a60103180000300e80400002c2c01449285c2c24242003d03019201c0303041084199641e50301c06103040721317a14030840341e40d00174000d0f2004100040046100c0348108440b600d000f4544480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 893851285 1250 893850035 893850037
    0x3070c060828110408070305070e1302090a0525091503020306100f090f0b090906061905030405120301030c1a0f0901051e0415171003231005090d1103 66
    0x801c1c520b15655200380650810641040341d0003000e0900503030303004a680342412a12640e40344134845203050690700080703c0c0019100c15194031035000703112040644130300301c00b8001041c00070840d42d0303460300f02a01060021903108901000415039a12008010b04010114441d01007030840c8809040c01401444015541c10305e0804090441e4542000e100990b81002c5030f01d030996612004039019250790104090341e10300003c1c20b0b6036034191941d00342c1e03032181d0341800818481c0000000030714100035291910140304000443c0c105005408542c2600348112842c2680c2c1d0080c0e104540008118004102c260310b0441e9180b08005001242420704c10204008449480b8446240d1304002001500c040720140e40b05185589030028500713551140c0c3ca40a003850342c0051001d001010491200c3c00e4410750902e00c4102d4400c1c400d501c820161140b440d5030712110740001c0380418421070b4143c4014054403101304200d064220703d4100100345400c0260100c0d0405c41013254170f40400549529103401810004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 893852535 1250 893851285 893851351
    0x50a090618020f1005190f0e0d080f160503180307060807020c01050c0f06090d030f1109300d090b070c170307200a050108010e0a020d090503070c0608 66
    0x141320403809004103d0101c600c1c0c415106000c0490003611080080143c0c06609440c2c00d43c0d99444082e88100c5020810008006030000140748000410107501c0344141d9901400719945208840b485030500356035801d082d5048052040482000684130b8440703441d0800c50080104038508002d012414000e100035100c55607804038a0500000050350981c40c1401c200190600303810030180c80c4242030484541d51200014201400040c0c14070f004610301e0b0910b0b20443d4040c0101e42d040a24000c1650207000360382541102652602d0104490180140e401e100b0146d01d80c6102006003201c1e130900000a881d80b01c554000c00c1641c0b0b020311007400000d42c03241040c8180c0d03039000d8980d810604503900c0b0620398032581d240101021002417100901410701024030000e1841100d0442c981d5482d40f00445100109108180500c500440403406a80042d401002543c01c1c0543c045442031642d10b42c246168490710301212001c919540421410354030022aa8025a08950480e551440b030502050041410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 893853785 1250 893852535 893852539
    0xc0a08070302070f120807031a090a0906110403080903100c0f080916120b060102010b011e200a0c05010305060a05011b0c08100e0a02150904060801050a090618020f 72
    0x5419811302400e4140109450790000804c940000c120380000c0000000791a1745021070308004506490785800d2848986080003d001a549079403507407010005085508401c1d60440d50350091803080026010013400603500540c0400e40c0c1e0b82c1c01030145480c04050302103500c406442c00a2a00400c0d500121240300c0342c4041c03800c0741e40c6803164103d290501060662040b01c00c9070760100040c41e41e080d07d40d103080390360141d01d0084d03141d0b981d0b030010ba00b80c80301a040540052460603d002c0c7c00d42d1840304914600d081b0317260284228509203171025074a03000c110070141d29800741d80c01c0c03401c008000f4410005040300b842c003800241040303000310b0a214034034054039040c401c020400070220307410070f05d0501c400c1d900314007609031a0703a0358000f0740d48803d0f019515502d440d041c0b41c0c01d00404e100002d40d2040c442d601602010034403004031451015a00450351656015440e800f0020b1311274424000c4034001c405459002078013065510b002c0e011200d071100800401150048841c0159940305201d1004c0302c41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 893855035 1250 893853785 893853787
    0x105061503062d03010518060103031206080a0606050301050714040b07030c05060a0902010207080307050a170c010608010b18040c0510140705070513050412030c09090f0c080c0a08070302 82
    0x42c0c40010b0302d904203d801031103d000c030500342c0050281c4002c8041e01c414805800810403516600c00341ea500141800b01c071252644100c00420010707110f0740c5c50110b1400c0f900c10009480e600d4103800c5003030241d00c41d019034905448103801d110340d1500f031180d180c0000040c1030070100c101c002081160325004d644030f001401c0c42d02144030342c1458004e045500c00d0341d902034151082c03807070300c0741010004082400041c0d0062107854000b1481d18400011140c4070368000b03004019801c0c0642c1c580144450300c00d429030b8021402d20121010f91000d002d08005402104004103100304503009018025520742010f2905141180520001c02c00078140242034a000340c4004500310300a01c8141e564200701c90b007031034948600050120900c000411048203070b520031150b541100320140b0f48001950010345029007000101045411001c0c00303039200740d0911031075081940d415903a1f0188101291440c901070f680f004d80f503554028000754445c440c59070007a0f00c500031508001c2c032000c0090140300c0050209082c11741c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 893856285 1250 893855035 893855041
    0x9051906060f0f050a1209060f0506010203040317090406030203060702060106020d1805060c0118080408011b082406220501140f090f090a020a0305060603090c2709061006020105061503 81
    0x206c6440030000a010200c018000c9201d1850b00f40014240650b02006075854507010038910761010084904907074000c0c04244030408440d12540036035216003a8554003640d65280080103032024020b183c452225a000b501c01980341207006401d00c0c1040e00d24070208803000c4a001100700c91103140c0d10a4440507034085071610352812096004280c00300040d1208140e0380ca03150100320000c40100305844060009002d101071184c40035040314503149021000c0b54001001400c84590381d44100a4948031159084440e28488049446a84022211207014010f6180009484071200f1460b0045c40e00b1b1030140360f2540b4000c14901d40d4080c10014866105000501d00300720741d034403615000310a0b0014100103003400c088042c00c00039840704804801090900d40050704501e85001a07a100395055409080c071205c2d10300400231062078014503c90403121b41ea00124024040c0c00545114003211001004a400d1488400c3e1134516194410380441e070400d003c000d142d44a80c0d81c441d420807640200306403241c27 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 893857535 1250 893856285 893856287
    0xe16050c0102040807080f07080a0812100e0c0d0e0705221b0518041104061422030203070801091101081503010e010f1508060c1309051906060f0f050a 66
    0x3c0b040360300c044801d01c5080e5001c00c192001059201490148400711131a040d0380f9a22070f9120300461101400b8690b05100d000c444104101c0b4850748100c45902c00a501070710b610180b00340103030960b5546910074003c0b9074400c0d010010322a14503406400d00040040500d814001815100416040490b21454100030001600c9a4010404460541603038461723000342003a0042c0035401c000311a500016001521140b1030405102e0842e4000c5003989240c0303403a003016001d036002e8404614224200204021031303242100e8242910170310090109404034690702d03500400d8504803503034100d280c0c16403401900d0380c0003070909003081410910070301380074849503102d0b018039110071100d0714142d826508150749032840d42d030103500c525030740a0740364000c001100c0701c400c85803400c0c00e00d40a604e0065206402081c0001c583c2c80240040410352103070010f02e0342d141c0c2e6203201911421740c2ca0080040300543c1301ca030001d43c03a024a2000c0d10440c0741414070700565180003031603c1d03103a1240905200d00054500c40c0c1d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 893858785 1250 893857535 893857537
    0xc0201170703050a0515030d0f0c0209130c0e0702071e0b03040b0603120a2307020a0605030402010f0c0203191713090e0718110d05090c0a0e16050c0102 67
    0x2030402444200840c582414098081c1c001151007071202858500040e4504040300402000c400c0090001c00e410a003207401034488916500c6800e090000046480006036180c1c8411407003222000c240e1512850300385400c4104072001d0704615424500c80003002005c650004001081b10194041401080400f805d21401c2d11595006401c0204000080000344002d200e6800d0140c070040e011526400130b008041c2c04640104002a000906000036034600403584842c2001564411300200e40350621030b0780007850484240d8000300110340c001c410407080d580c206948000091241c2404543c100040d8000f80e00c60007e22840603110304121225014001780e000044502d00107200c40d42e540e42c02ca0544482d01505a04c210741c089030401e52481c0c500503000c21964101e07115146064004e0380d51190510182c4a200e03050704000c1c2060150510401050013502d00441e030301e0b409014070604410170300c00640c0c40e5410550350021600b0a00c2900313401d59542d0056005240b801a469080361313500c0c240a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 893860035 1250 893858785 893858807
    0x30b0402030f1b0c03120a060b2214090133032a09060503071103030408040501080604060509060f040207050a1118091207061b120b0402030105030a030c0201 69
    0x494404010020306281045500c2d02580b16030f01c00082c80e081580201020380b02c0c0d2031402d2042d81050080c1340c001c0100a0003582c10118103000800e407107440d804d0085050300800c8509540c01502811440c4c0f00e4510b224420207041035000c01c910040804010800c0d064040c8142144001000f8200d441d0b880b0004a128960482110b104400300320900000d014013090500e04002c0b100180740ca45e00d08580b8142800b0605885d100c0102580c504101a50749820051801e400c1c04036403240803040340024001144210306c940000c64940b401e1200041109000500c0140101d00d025800e204c540d9900380c40551080b000c0341c90400404500c0007103001ba01170b00384000e00b41d11450007a00104450400801d046040c141c50042d5418210701d0b4041480303000741c448450a82111140742e010440203002451214000d060200d102a1440031180402c0360040d0303505c001071083c0e200400d80c444a4002d0b6250300f08211025419941004006900c82c42011030050600c81c55030200780c110390007000c003021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 893861285 1250 893860035 893860039
    0x3080f090c090402211006120f030e0105071202062205150c0903060915070810211a010303110d050f0309011e050f071719060b0c0a050c0418060c030b 66
    0x80704011100540d0340381030380b415031040c06d8140762012910704030340011280e2940d008000010b51540a4600f40c0b90105020159030400004003e22001b05074150080030303292040750300400761407502291105805240520040403155114020008504005051807003d542042d40c0901038a440c40d5500c501c0c0703d40d02800f50540509001c201e10500003042e2550509070401c85070b1496913032040201c0391214100c0c0c001d003007201c020800740b0842d001c001070006200c82004000c00034031000e481b100c0ca2040c1030800d040e0992000310040c4109688000c0480440e1003000c000d06812807212006000c2d13018544850701080d0020001506811007500b00010f60401600e05200e501100700410740a00411600003100704a00e0340403501162082c14002207286a0115942d000d840e40d8688201c010020b0901040940c0c5550000ca480c0004200400714003000e0001410b0038075440c03805a0411220036480b1344121720f0003111805020028440c00f154030341c00503000800c00c9020304283c0040807103240840d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 893862535 1250 893861285 893861329
    0xf1303051e0903120403060f0b060301030f05031c0504030e0105030c121302060a0906090b0f16020f030609161d062206090b03061b0d0906111603080f090c090402 71
    0x44220140c4d500800a8900803101800410301a541d000c05451903032030429040841040100042480c00300c0560030b20348940c2c282ca01c1c02c0e42441c0403220306071001954000d81685d50f0148401c01da0030051861074100207081c558150f00e401d04400202e8007500c40c444400c25a0540042c40d410024036103c201d84da030081100d6120051003c000344200c40d14010100401d0400002003102400003098481b01c00715211050f181c407100035900000b8450f00142203803c03250f00307044071a00b84c1d01805200c0c4100c910720010216016640c80e171203000040d0741d001d40b034001000784440c031070f030664007010951002050310780710340c2010703030030084807902c1d0103610340100c10391808402040007102a0407100e403a05040b0200d51403a00d460306c0c43c96424002c07001c284000b15080100b28281c090307a812030420180600c00c0010300b503519010540c1c40e540042c1ea005070b0400502089810150001c0d00150003511600804110345042c0c0955a03076503003500603036031107a030f255000681113680d0a0710303441080e09085030386 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 893863785 1250 893862535 893862553
    0xf0112020c0609120909060f0105090d030302220e0f100b030a0516031e150308042c0727050d111c0f060c030e030708030f1303051e0903 60
    0x2542d2954003e075141511805051918102054920156240c90ba0011b1010001352600740c01c020101c092442c009061020501050b40d9559500c4095064580280c03000340c1c0d600c181e00070b11408003586840070100220104030900c01c1c45404441d590b404268140003800039203803191480c4a0500d650720401c0f01d440c000040010030005030300030b64081c0d0440900001c080c1d100302c20903816109041e001c1104400c641056048607c2c080d00520f2561126840011019440b0f0b1141c078019441600a0156450560007a1030741d49034106030703842c1d0440751540c400440c0c1441040100340c442005d21394158198084501000100c101d43c00200070718006000240030b02c087d261841408030f11420007481045140034000e11115100700c06030070291b00c10020050f2950a680e45002400311103144410580e5800100a10180c03c10081c10000c4c0102c160310340780c0c034203c00030392042c2200818400160055031000d400090f001003da81a40d904026180301400100c04a00894006d020078254144250b201c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 893865035 1250 893863785 893863807
    0x2280c03181410021f20040303120f0e121b010b060706020c011d15090105011206021c0c0804050606060f03150d12170a0b060f0c0102070804090b0112090b060f011202 73
    0x81085003110810381401b02c20300b48126100c69003d64400500402c038100c1405111211a034440303444890309110000b0000e03c0562180d1501500755078400d0188c40001e080301c490200d113a83c02c20400344843c000d01c129011000407034000c1c003410500801a43c0c01107401c0c4295002900104002c11080d00d1070b89680d00c0700032a207070b503c802d07030001e00306000920f07170101d140c1c1032040c054141600e60074101e20b55150055503d48009521003685c41e000c0646e8050140e8611041d0b0094000004c1c3c039603944969424103003402402c0075006402140b00d000100048802c20440380c0c26170b9445400410f50300311030082d981c041003070000c40b820003d01441500c5030005003150070002d140e05542100030784140303d0340c41d040d2140465006094150f40448180030702054909100010034241003200005410070304107690310b0600f904117420082d011522600034400d5540e01105811003c42403c905210144203600c1e182c000c41c1e405844280100011607184005900070062030100d079000c0030701150b4444c84410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 893866285 1250 893865035 893865041
    0x702270f06180411010f0311040b0307021504030e010e0f0301240f051f170a020717030f0a0e0a150e060615030a02280c03181410021f 59
    0x28009100c2c0310326816140000441c0e8103880d114552090b030455007803400c000155500e90808090f10101070b29030401c60703003102c2c00070007601c000c007412985c1030380702d0510381c8001e0704103043c0e10404070300008445d080101003940700c6905035030100203081001e52015400046110807c0012942d07402d0360030001100c240c802410341044007040c0251032884910b48030300083c2040c4541e4802d0035401070203022445011003550034191400e0020303041c012803062020308115104070048400c50034041d804103010302403003d0001000464110110303210f1031481c1540340141e2840020701145095540c4410703803402844100913a1300c6c0035030400280385649505551943c007412004018005901032500800c0f0b007030504c1408801c00c580ca002d4034505540e10880440b00a42011242e001c0c0380e03a1880a0302c02160104000c000e02810300d55034550604800c1c1405801c80d42840c0b4640380c4107001510800407060313030301000300030340001300c030203001c118000b82003240f030303c41c404203604015800324110030500c41c0030b54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 893867535 1250 893866285 893866291
    0x3230702070609080d090e1015020709050717041b080a0b06040e120f03040303110a0f02060601090f051905060f0705010b01020111030109240611010b04020705030702270f 75
    0x50381c3d0760882612200901d4079001044102008241d0800c824030118204200f00c035400341c052400320108940d150600045200081103170300145c1c210003410701c504903450144940c000b10600705a240900e1150001441c88070013400078004001481320000041101101d540044c00018115002c194280c00e02486c0000d040c0c0e4081c0c42036107824100c03200d0005c0441c1d00e0321003800c16076003141010800342d0824500e900082c4200c2c01c240d03949100043c0e02c0626806007294103101c0e550110281450a00a454810082c08007418060300002c00c2018450340c1082c0002e03a1025038050381840100c0f0b400003200c1181c2d410441d8460b40c0482d440c0c102481250207803440724003a000038030041ca00e010041e4201c80e0651071442980c18104014800c0009942069401d0103007000012a025240d550030020314002e600712100282026201c01030040090140305002c6100701c1c1c4c1140303001c0b81551075641d640320741400240205044070003540511008070013152a2032811401c11418540360060303002030301c011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 893868785 1250 893867535 893867537
    0x40606030b10180e0a080d060b180f40020a0309151812120e0304050f09010828050132040b180a0204020d0c0816020d032307020706 58
    0x110043c500101d1030b0181942014184014081c11a0300e5120351020b0303071080c10070718442c984441001800700c6124000b8914905607800354a4045030781d004000011a0403040184940b0440c0c000720f0002c188c0010429150040c0d00822034050410f504002c9694025001d07150950b20210311425a207030103820400341c01c0d03c115040c0161144040300c52080b42c400848000c0b1080d041f0846000160400c1004030004185080c20a11030583e0040c4c2c0e030a44050b441c1000b11500041000c00072030418a06003141042c040b144c1d6500d640c180422255990510b038880e90808008074161003e80c1080f41c10458801c4d00140280009070b0344036a200c074030b102c850420b0a94100c6403484055405d01841c5054005c45c2e01031500c000c551682c0501000c2586400780c2d190040c01002091001070341c45200403c2d80800d1603001080e04406224081c2001500920b00c004199171900c0c40103070a42e0101d0764000101c0c15050000da00300c3c40070300d04035284406c07101d0780d042c10400005210704a41c0008006c4121441c17 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 893870035 1250 893868785 893868809
    0x6060103060f081002211e06040c1407020a080715021005010308071401061e1403010b062d210702070605040e0c070227060907080f040606030b10 64
    0x1650329900208003862181e520316401040044d030720b002e040e400815440b00c010a10101e40040140160f5a02d541039aaa030891828007041710f1100d83c58511080d400b60007201c0410041c00011400340030b030f4140e00010404000d0000300781c400c540e1442100300240c40c2c10411602400d17103a01141081c1109041c00001511501d045c503140030415000f842c1c16203034404d03c0182090303125a184071a070546030044402c19501c42001284030303510707044840148400349107c0ca00c040d190195035049960560201806a41410702c4044580c440100321052020140c058200d100c02405078460b1015821540210b544400070320b1014441d01c40004040c030315064036080c1c20030b840701001a680c4003014412480130500501042006540e4422120f03441075007556402d02c0d01c50640d0028400030503030041c194821b080d4049110b401c400c0c500e03089034030650036140d036081424181d50241209400410420b241d542210010381080425009040250713405a8284c500341014040d1000c190000c1c041c503228048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 893871285 1250 893870035 893870039
    0xa140a0b0a0c122c0a1104151707080a03030e010c0f080a0e0309030a0812070c0f140c03101d03030f0a020a05120c040501030b040b010e04020d09050a050606010306 72
    0x30310351154958003505601c40e5040d00055000b110f000d0001d640144680c800445402e4105010345080c8200ca44400340190100c03480902c0d1580500c10a91940c2d03001d58a130481c1c0c400c200c04101002019560340b0008419090040044c00e843e02506400c000c500d030040d00461001c250309038000d1190400448000d020708024080b08a405007580300d610380024201c80e000c11180813565020b0241c2d000c8100170340c0d2074081e003100400c1c541401241c086481d0b03200044c2c101c1013a0000640310790456014540900305074240d848a003100805080c01030400070401c002d025042500304031411007140c002c0c0076074400078085d008c61402410740900420031410101340c0d42c489007001104480c41340d04110070280b025100c2500040c020b411417607440e82400070802c14201c095800c1e46405100d140c00c1e0640c99a40c0d42440001130540302c5254640303010314108460340c0f001da80c10004104a4a0054800589903507544407040301800ba00c03080608907004403d0068188500030503002c1c030540c5e082e01d082c82215 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 893872535 1250 893871285 893871301
    0x150a0804062307050a023307050f09130605120a05010c05070515090313030b07030b0a0308120a0204050d060e0609070e0c0f0d0f0207050c012606030a140a0b 69
    0x41540b94080300c81504140c002840140a24041d1490405500c100c039102100072140f009512100904640c1c810348924400041c45d40c0030815581c03142c0383d0300d0f01d98108080480e018115001d8003188500ca00c00d50304202030b0a079103641c080801004001c040e2200c0c0c114403451142c803804c40c0c0e02e040d5015401c048180c01c0241c01003003180d03210750303102e002032080540c9840c60b451040401340c981d0301d0174001004203103800308503000c01e400a14000d054003481030800880260072148600001402011f14010810210349502c0a81e00744091440740052079540e289030f801b0007881035405c819400b46101d030f8504284501e950102c0260143c080c01c0314134544501ea904c55070380d50036114400040d806030000601101c45100030b09030406100d01c9150402180c6541c410645445400058010764080b43e020107110342000702d60400c80d0300307082030040c00e00c00d40f4000c201084d503050070316260500d00c00841c400d501c3c01c0040f405032b5038101140c5138424200300421503c4103045082507a9000410021503400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 893873785 1250 893872535 893872571
    0xc0b0c0f1911070b2704051e010602190308070306080106090b0f040e0304060507080f1b0c0d03050d09111005040e01090218040509010b120d09080705100509150a080406 74
    0x40c9203d1a480c070b0a010080c100050001300744c4801742c401221940586410791602d00070180200703c4108103e548040c1301c00110203081c070507403100c130841d44104003a0040135440320078400c10541501e001c04082e95140c1041d40038051b568014400e640c41c0204c00603090069900c02856040304a611114401500082200b0740b040050051090741041008200d4940200010101c0300c0c0714504c01c7c0d0030002c03008044000394000d038461020202d595a461600d40704c0a100c1c030700f1082c10403100800c0440c9580c070000d18601030411800140d50755500c2c0365050100c5003802c3c941007180208811400307091040c0092160b0417601c102041008500e0010480e6034541c001d85100c1c50016610f0240e44405100700700c081c2030301400c606800d568460810046449100384039203001984001403070230089001c00104400c140d07622002468100b0241800f4645d281c41d00f24100bc045860311359114100d0200040461600d00301e0240443c030300180300d46c5000d0300282c016110b2400b07500104040c1003200c1c400885 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 893875035 1250 893873785 893873789
    0x308180d02130b0307030602070c05010801060f0f030509031608040f080f030a0c0305043f0b131704060f02120307171f06032a0c0b0c0f191107 63
    0x102400d203040e1030b1003114150788182e5440b6401002c4502c0b155807900c0d4a0200c6e44164804d403002449040103110a50300007101e913004001c58640500d074501c251000901c481c20b541c0c2150304045d10f400c00b184000c1e030100305840311200d1814000000101602d000c0d01c65a01920031700c211802c0c0c000300040c07400710110341c22003203690310000346d45011900d04085501c00f008440840034001e007800b01048101e95500140740d030f0440017405900c08040010798101e02c0740e02e501d2400f0040203601821001038900150707a500709100d9900c4440a03a0545840c01404292600c41240d2000100d000540190700034400c0c0014480c07502980c480040c002640202031100326501d03400f044014041c0095000c0d0040300e036900c00d403007080da44c041c0c487c81290006c0300780241c0e01501c000b80e2034004140044804910100000c006011a065210b0010f070019051200700c400241500c40e005d00020345011450301101c82c015149031101340c0e0b0700444004102d186c0c240c1035070000043e0000f010983c0c049800508070342 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 893876285 1250 893875035 893875039
    0x60305060106050c28080c01090203070e0613021b061311060f0a050304020a050402131706070c08030a0e062d071e020a050114061906050a0809160308180d02 69
    0x10013005d4100380000d122030a40710900318090780796903070340480c07041c8005d0103001c82c80b08004038232001e56004140c54020b16030062401c0c0303403010007809403507610800f2040140f03101060242e207801c0303000102e07007111100c615401071501489040069030030300000e151003443e06c00c288002400c0401002d2042e50b001d1485001c4480c0010045d00300c0c40e50040c0c000e940d00520007406030b42460b480d035012034280d803c4130000c126403501181c07081c1b0001ca01c0e0501c505682c4641d0005080c81d04e45010000c00304010160003814a00001012a030781106603004020041070f6501240c0c8203040165507c03050105282945034881d4000812035aa0380c25466002e000c1c0700036540340350900d0b020400174101031031070309449010351207000e0040c0f00213407080c09144c10040014543d48a1403800c00d05002c810801c101490124103502242071000e81d13000000c0d070350380440b5840c103402c2a40d41c03088120700e80728841c40440c913048035031040002005810b40090050600e048000c0c0c0304192583d05003c07040b214682c00035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 893877535 1250 893876285 893876293
    0x909020108040f24060533130305060702071d061e041e051e01080a150605180a060812030f0a140c040501090f03082b0c03060305060106050c 62
    0xc000c116001039594407140030365580800f826541d0002c14450b640c010840c040c80303494245c2044245886541d501030b8411400c3c40450881c419002c8000c0d54079085e000380d04038000801c09401d1001c2c0602502c01950b400b6007181c0c080d04001002a6551820f80704004150310201442c0390302140c6504030314080e05c3d010f004030a43c8000c0d80031110210712400081ca80107030751803d0914500a80302d500340c4a10041c04800038007030418240c6403100356039080c08180c81c0b0303445030010060300d4000910414416001a0074a4005034901e5102002d81501d6001300d51040e9003c181260b05100c04035260301400da03601041100c29a41c024003900d40c1403c0f0b1004290b8038003400040d00c0b50801910030b07544113500303020000d44400e00380301a00402d9001c1c0d130400b01c500c0340401c00344502e50308030b40108054090000f68401040c078582d62800c0c80d214030031208240c10551807600e0401600d106c4103480392501c1b404103000002e0316000050017030802d84001c1e0303840d1007500700016021b809078040f20b2100c40c006021b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893878785 1250 893877535 893877541
    0xb010314060108090c30030307171f030302010c0e0411071401020c0d18060e060702130f05070302090319050307020d1106070b0a0f110406110a0c120c0909020108 71
    0x196105000241380c5036140c0160490098195030b480e030081440c10a0054040ea03440708803110001c05035070074140c40d0b665402001445a0190007100100340702040f02610f80301d941e10070f01e030410a0b60724024005001310703005001004068040d0007140842c8945d9444490140c240d10400c0242c5561007100f54807000104401408194040380200088100b800058500020182d01500d000028001c1d44000b4164014581c1d049034070401102c020042498424002282c94000507402d1041083c000e1003200d003040ca0b40d0a41c03444d60032a1420304510a020041450300c00b40140282d400041c00d24400d008128014150324a02604c0448841c0c20500a6040c0400d84e401d00002015194040e50741e42010b80800940341d8a48004040c07a5221b030366100d8180c03d11108900558a800007400c1c041390030000080341c00c0d01c606058404560483c5000c10307003c280014020309000414001404c0b141d2600c00218000c2c00050315031004601c1002c6c0c00250315550040700c022a000c0950080c0003506030004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 893880035 1250 893878785 893878787
    0x101b0c0809130204030c06110609010605011e0c05100c030b01140f07080d0c0e0a05030d17070909051003030e10090b032e080c0604271805030903010b0103140601 71
    0x4404202610030b6001441c0076142d0f01c40805640040d404040080e041100350000b0394014020b950f04410308000138003016040c240082d0610f01c0345614658141005d188040280784191210b178000d83e044402d40b11030140141c1940040c09c204211180880d081032071042c0654800c0d5850f517150500c1d640d61354100b00c44003040e440d01c1d80c440c05003501d0312601840703a203031507400c1441200d00060300c1c0d441d6450341014403401d110b20b542403540100d02c40c2c1c20520b01503422036080048003c030704900400054455032849070944551585401000c3d0007031400701080303040a09031a54000f03403802622224404072040c000c01100802d904c507000006240c0d48420014200844007440e00181d0101d030f4088420711040c903188408260208540691449000c10000840d060203c1541900140d032514500750602072410243c3c40056020943c403014010043e1008405a2008c002000b220b40300440400d950f0a1442d070f0b039000380116a100354605001d080c9913602074812a000580a00a0043c4076655100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 893881285 1250 893880035 893880049
    0x3011205070807080312060607081206012003090a0803030c0a1103210a05100503030a0c050a05030c07140307050d021e1f0206090a08030f040c08101b0c0809 69
    0x80129114450075001140e9041d0501c1240003030199600210b1b2180181c00029001120181c52240207100c01c0003a680440c0d860750488101d0040c0e0130904142c1e80b5401c2c012511200700c0ca400185001d041061b40f026500302000030a00b0035421660b5203815911141a01e449100a58410942a8040020103622401202041d03401c0400d401500e0500c4182070310128001605030304684140750440130040d800a40d4881c0c150425101a000740080c3d0030000480d550344103035000c0b541400700d50210201041400c0011507441c90340501929112110807601a554444c640181034000c1f1031015107106504002070241c04940c0004d00c03076604041c06e502071204106020810408200c070700808100152907408a50b01c50700e42d001d010183c0005e0318031009040c814050610314440d000800d0603404107a0035419281c0140e02284014140c0d1a0761400081000d46a80040c1d40f80c0078021325202c685100d0341c002c0e040300c20b020310a8408610300a00c00c550301050000002c04c141c0062100c0401070271300030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 893882535 1250 893881285 893881319
    0x402030106091221080103060f1e020f1306020a1203150605030c091f02010c0e06040509181606110d0807050306060904090521030415231e07050705030301 68
    0x300064100360505014961041816039080c000b00781139000402c00c000103272050308619681c03040108041d1000403101c45401d45410b07040b050721038001ca007001040c1800d00c11120041308110b007900e4030b59580c5c074010f521070b46210380558100c901c03002b6244549000b4001c40c602501820861a001400d042c025541074001420f03440e4018810b005021451b00c5150381c4800151211090860720300242100900399188a1401001c04c0320700c1d01044060307101c5200303a03800e94404807040051a41c1e8491885082400000018414404e901980c040c183e503101c01c101c10b8a2455031007001248003000c460350b450300c09843c0600041c0701e1800289100d0f2040c400b954000314001c08043c540341746a000942a80d8080e04251519003200c02c01201c079862044100c1841b00d81c030010a411850951602200c25101070450201c060325500d0780d5044001100221514070201e80d040d100c02d040000340e008c4d140d403184002c0c10130a40407001080c21035000d842075420762a44140210b107107030309105a0b4942c03d003040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 893883785 1250 893882535 893882543
    0x305040302010f0c02090f0103140f0a12020114040c08010605040b0303071202070512062e06050304050321090601090b0d170f04032a03030c080912060c04030302060604020301060912 80
    0x2095820011307a06d0121060003041c2d8401090129411400c284031140c4200c40c2c0707079155500c40711820750071110210f628031545401580502204a031450f01b40c1c05044845122041ca042020401c010022a00a0303402a41d0780c403402080a6902c80c002e01046602c0c40908503415072041c817800b40018a0b401681e02202068415544026610008541d50070781d5904007200b2500520200640c0c10024500c400880080d000c85502d072980c00c5040b100889820b0107444c5c20040000700040c1400310820480d51080c082401c425520380c41030300c10007a9410301b920304a02d5406405c0c000507400513140110415030030014428404149a5560342d0040f02003955084c82c0c4100500c81d8000b00b1120030050001140100d0408200d20003220415402010100c450307524001c81c0d16051003c01d1384426002e00455102070701a958a21040010b12024810007024609100b6841089400441c4a016000300c900c40d408498958880404200603400b090042030002101300d101005240d800c4501c0404450003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 893884892 1107 893883785 893883797
    0xc090409060e2d1203010501050c1c0e010f02070f051309060f05100807081c03090f050f0c01080f1302061209150106111f02040b030f150a030305040302010f 69
    0x40c01f8007410000042010044a1420000c0d004035143c00101e0b03002c02d51214500900b8a1500ca1060b4005583d2400e42c528043c000602ba81c00d40d54103064249150b801c0c04180801070080040789925a501c41140d40d0110380144601039100c0880c0d880407a03140f40dc8520b4108030802a482014a584180c10403c034144021030402d07003540302455100b1001c05108811005030140942c082c000f10408414241000000601d644294090300161140002108010743e00e40c3c0b400c641e403c0c1302c0109080080c0c16141c10070f00769501e80d48001c04550030010039280c01c58a0000072110b20400c0d6200031103131908464000c08950040145242081c4221854400030341c07140c0d01d4500d089600460081200c151803541c0d0180c802030b00c9902041901c03460a410441f03d03035070060303500ca18000700c4624081d4107400e1a040e40030a581d01912800d1920b4510350044a010075048012020001 = true := by decide +kernel

theorem cover : BRFrame.Cov 893705035 893884892 := by
  have h0 := BRFrame.cov_init 893705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 893705035 ≤ n) (h2 : n < 893884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
