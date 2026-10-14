-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0618
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:45:26.685923+00:00
-- url     : https://prove2.me/submissions/32be4cf8-866f-4b81-bcfd-f572d566822c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110971223 ≤ n < 111151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110972473 1250 110971223 110971247
    0x7051c06090509060105010906050c10020d0b0406180614030601050d030c0803090c090703020c0d0513120503180a0b0708030c04050d0b071e020a080d14040807060c050301051c03 78
    0x14500b0801400181403000c10f0660403030340f003603e0f1000183d5450780260703824080c07138012610303c2d0084801c1c1e8030420300d00d23001821a54407a9400154100c0c981000908540094201c1d00300600300b14281c2d98241d00344c3c4102000f0705120000f030041201404002940da400c14001c1c07034050100c03100800c0406002c1d29841081c81d80c0030080640380d2400c900a16035074105011002d202d0074070703000031451403402803007100c1c5001c0c560006080c542c2009907040e600350784525000710400303c46000001e002841c06034500c01c00303803084000c1c594801400410004c030440c013480c128401c02c00c43c1010040014660110340700b2650002c5115100c6d0384035202c4070294055640180c0c0c10002280b610010001c0c0d45003603c2c401c21240e00da420948540c000400048030080da0404c000d640506a40f2021504000141244840a4a01250b100b0900d03020700c40c071442c00e0f14100d6007001b021070743d5020414240035810340a1114a07091341558504000a84000c207141903119000004003000760038148140510340c55 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110973723 1250 110972473 110972489
    0x91b0a0302131805031914090103090201020f0a06050604050a1413021c030806011101020405031e010e031912050403171302040203131e08030106050a09080105040f030206060907051c06 81
    0xf402c0d6003002034076076004800050311081c1d84200d204280340500c00083d86200d084d0903582c10002ca580040d0011b1032284016030640c07007000b41040c29100304100340c2c40e00602c0759001050360b05041050000395003010703100d0604c0303074181034010660032041130b0041d40c032540701a03031025100342a0022031400c0c0d11400041c8081d04103140c43ea018140c005032100e0244500f07980704a8400c40c2503040c01d080f801035029041c0c0c0358000710842c500340b00e55444060180301c480000001e1000c2580c0003546558005880c2d15009413800d00f203102c0721038011070210001d440d0010188110b142c25030b4000c0c00740c200c402045010300c07003550120b0083d40400c12500e0007580d0260085541c1e0814107010306030109400012074120944440200401d43d09446903040e040c2e1010745207003513900381a0281c0c1e0b580c0200e40e0301001c014008000180028090190900850060012407074140403410020b0038400c009103500e020f14400014081200d03400001c5440c03c064003484405c031003909031502c1c1c0140080c0d07804125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110974973 1250 110973723 110973761
    0x1805030303041a0a241509050a09021c020a03090c170c0603090a06060303020102030a0b04020414090910090c030c06020f0c010f0207050a030c090b1806010c060902060c0105091b0a030213 82
    0x41c00c0d004540205c011b64000480c4001500d611000c200c43c00b500c036000740c64001aa204081182d031000380c01800c002125040d886e902e140807100000d080703800504400d4002900c81d0b00071400c0c0100c01000c9805040d858418030070044000f00019902c0680c441603078050740000001421a41051140000b4540e0003082031140507600c3c2002400b0390000c0e0b5041400314907000100303100340360500c01c4a00302c45541000303103181c6034030360108400300340c0041c06c1c20214012a08a0918021140304454145210700c0c00c41c11100e05606003103c5c0402035812410a543c4000f408050015000030360ba4001e040928000e10303210341184c07089040c00b8840e03000b40d40241c9841d00200401011f88851000c0d545580c408020b4907281e02c04101c241f0005004d090110040c1e0400b180455206a04007103000c0e000306000725005010f80d01160481d84280303031a540c181d55078424880605002c2c031000da500e070a0014181d0b81140c0e820002113a04800b44402440350f4984a5000c03c1d540b169001010240262540c4d08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110976223 1250 110974973 110975021
    0xc140102180108010603091515050603040c1406070201020c19081207060b040603020105040608060a030f030201050f06120d2d050a020d050a0c29071805030303041a0a 73
    0x40e00112428046003c61202d80010890324030900c6944401c5422041031400e47c1100440c4900411041c060340000c1c100300180030490b61202d000a5000d1442041d000443e82e02e040c240d11100340c0314261480c0324000030070001003d81c0e4002185081450102c40c5040105844100300030f29007000d40c007007980c1d4095010541250314542c0080e204440c0540400c7c4800c585220402c012a9181d01000b40400c109103c1804014810581540e20a038003401709001540c076030b100d5602c062003044007100140c0d111010024028a800030352074021009540100070344006540303594540312414220302c200b2200700d801c034004041d601c001107036042800d11036420454410078000d000d07601c044003440251142ca4800f420261081c822105036032590b80d41c0050800e1580d880c100882c500c5410300c500c5040c00610746460780c1a11810901412964440f000c019070141200503a4203000d6020324441d4000f03204010203e40200e54502110080014a040a0362084500d02c000c00d001c0c100042c80307155504c058 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110977473 1250 110976223 110976247
    0x140d0302090901030b060325050108010527073e0115051c060608030301050a1e060c02032a040606020a020d0b100b030a02030403030e032b020d090f02010306050603160c140102 77
    0x34184c44007a03843c000344cea04d6600f44401c4c441407500d000550b1900603044114201031041c1540c02004a00e0a42040c003000e01d10240405e50b4403d9000510903520840c40e03030b00f1049a02c40040c0c0d28003000a01116003e003091354400e030858822903001d60480b0b0884900c84c021441c04800150340101c00f00140c07505ca400b0345942740c0090103660f009640010001c50320071400224080c40a210040300070700319007042411070382035200303001c200d8140c452028542104c0a29500d5051058000d046100040d080e030020071059a1260303002200b950000030201015032242154042c0c16900710b01d042d02da54440b01000401000d5950010361264008410301500a58640080d4052806580c091040003491808140c480c45510003200c0380c2c00d003c3e04409201e5021080e40504078040300c00c0141020342c048607083c166481c80e6001c842030494441d1100443d07800d8803880c000740c003041d10801e0079880d14044d400104622500b03040140003c1d00307101e0040042040200020501100081d503e4007030345124 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110978723 1250 110977473 110977543
    0x30a0905190b0f0f0412120203070e041805030717090901090504020301061413051506040303021e07030314030405010f0c050a171303030e0c040603140d0302090901030b0603 76
    0x400c035402c10710200441c64031100c8075000c500412008220110540310b681e0390f68040490683d104045c0302d0305200e030003012903a5101643c81008181c8442d850042c80e202080202c076202041c0e031054120b01d0080a003c10f800100b61340d441c681c4a002d55600d40d0307100f0a070280707500034035102507440700c10400040f83c4990b00317801242c05244258001d10009441d216142e281c40e50345541603811820b0115030105500664000e1a00070b031402c15190743c0c444503c008605241e100b0b0f002640580c2c48030780c09071488603421f414451601d803081c5c0130300075103421a54000e250440c0c2100c0d8001d250404000700c0c060107000e502c803800b40780000804000b134400380f410145c42034101c4084a00418940960f860a859256514038810f044458003050100b0240e82e0507401094414952041c51081155007103c540700c0e0b1042101030f500500301003000d06c0080704035619245c40610035204140c01840b48003400d4a80301603040c1034980c07060707442d055540e5620119140030107051800308046202c441307103c044a00004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110979973 1250 110978723 110978773
    0x4020d060308031f0803091c030c050607180801110a18090501030606030210020604020f06070c05120102070510090218041a0a0501060318050309010c030207030b0702013608030a0905 80
    0x50fa00681350b560b0480c40d441740106840d80d6008a01e48695503074412000b20a84c1125120341095040b410a41c0c132071519010301112170710302250150140500c0b25900341403000007002e550000303012610700c0b80040343c40c070300034120100709109180c05481412440140294043d045e02d040420180d80d680c203115004c0c02c01880300340d016a501301006000305101149031445280c0203010110010384060070301175540e2200c01e00b40c503031030981d80c0081219070b0750031025a030300882c5400250301d40e0814144a030400d1000800e03640da00c2e180c915842c0040c1c8a5101c85041d8129407054030031103a4507803c0800b807a180c151030ba0701041520000300302d0050b2040e400075050362a6540c0410038211a84006040c200790704a0140040c0c2c03042c0185056584950107071b03517005100b8815604041d580f0b60f10300c130255005544420250b51a2008034010341e17088200070820039500c0400068034000e0480c280302e954146030014007480c00000001d020040250030100b200c550000c202e5504003074100603c40500710080c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110981223 1250 110979973 110980021
    0x705190203031e061e0303090604033c230303040311060105010c021c020607080f071a07120c02070503030408100515030d120908040e060a090e0c04020d06030803 71
    0x51403070f44200ca0b8030103107922031800901070800079a0f2031000020a40711405185901d40f00070403c0c0d111984824000d0b000a500c2415028202452081680381c0c0e40035491401950703820318001e00884041c0140f801c02c58540040c14280e28180983c480942c038400518000c1e1340c0e00c800004d010401d5444011034040d214035005503035560b41c8807401164243d180c00006503118aa0300030007600c220741c02d20811212031000342042d2406019503121034242d0401e1404928000c00402c00006010114680304018603035242603d03060300d4040b0000c0d069005040016a085030365080140e4964001c00c94030300035010040480ba240d550b0b0310311156490801d2200110183d09020104008180c20105882d2050005014100740c0c0060b1004642101b007036245080c2c107503100e003481c4011400c2c0000500150100030540319003840c1010600c19581070a078030501c0003034035259483c03109100c041000d0f403400c40220790148e650200c2d8807030700020b00059040513018020000500c2156920040b060000013405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110982473 1250 110981223 110981251
    0x5040f0b0a0314070504061b0f031707020109030f0f09032f0402030402060406050d060b07120f08040507061412010e07021606050a0302090d05010c0203030702010f0501031109070519020303 83
    0x81043d00032810010782da0b280105000380030900a55004d03107464003000f40d0100c8800c0744002551101582e4141109051300071900000200e03140401188034550302c0f5480c1c0c0001d10000c1e5140c1d60090515189000c030707400b00301c0369003a101b0260b845000700394002e6400203e2420601040d02d074410a90490120910300003c101d0303e94001800c00f80240d911035038005040a040514085003a1074a231702070800f03d1140c690b5044085807a25103e030280501c40d0040c40742c04002919501e01030701111048042d4028011100c0c104000944000ba0242c1914658913240314403030b602031220300550242d101940a1000d5840010400e41d01c188486445810182c0c215000c03c01c84110110085e5028040c00d00094010084026114000d4004000b03c0d000909400e407100c9041e2035160850381c1e46050a40160400400d102030f0a609000c0d03a00300c3ca00c18241000a54955030322449251151640580602a05400601d09900600c01d8449072246400310701d18040f00310300e00940b82d50044410315000c0300c80f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110983723 1250 110982473 110982491
    0xa090e0d02060c0304021917010b0f01030203060a09020d0e0f0a0302060c160b0c0c01091a1b0306040e010207020901060c170c0d08040606090c0309020405060301050906070c0305040f0b0a03 83
    0x2001a5450080002030f650310302c4c589558090060610505c1022070300e000c114040001c2034114820170000002044000045050a64013046028100680c01e5410580144180031603955240c0360030044420b0f6090050351f6006250010014040104024603103018403480030b205407101003441c10005100391300340c0340030341c8c2c6200c0c0c58181d6018100d400700210010250400029806100d86a0041d4001c0103032810100c000c41e04a0030b590134064102d13408503074621984808160000080d4003e8030124245c04600211034183d400d80c00000e00c4544030340d480302290f6646a10a42c100d9100e140c02400c0307030186686410014020340c2c2c5002045401e28080c07240d001461035954281e614a1680740064020403030b40c03050403a81c00030701070004d0b44d00341e640b902c0006088000744a800013031440380c1c8001c28031070803a0042004641004000340e02030b0f4180401c01c0100c0c1404104245d1009541c1001110200c0e503050445050049400c48103203411381045c04981880c2410203411007075082c0d6418410078417 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110984973 1250 110983723 110983727
    0x5040c03020301080d08060a0e0a0c0305070201020915032e0f050d0b0117070f270c0503070507030c0203010507210b030718020d050c0c0f0d09050f0d020a090e0d 71
    0x100134130542e00103402096181001c913200c0ca240d660402c000130254064a511200100c0b01740d0020f0741e00740f950b9651340d80c00d054003d400d401480c1c0e00c90642d000850034107100e2400304580d00384008503800303054000070000c0c01020300303141a0ba810043c4410805c81d0007801008800c209145c1b4056040c3e031a41e0844006214030307006400080899202e2031030401030b403901c45004141103084001c40680c1c0a80e01010031520000c2ca189030003006441842c21030b1302900c0d8040020340000c031a48840d080c1c1070141207540c490304031040320b4100f0031902d0b00c01c1e5542c02c80d0504885d82c0c030441d8070003941542490244101e0302d42c001d12402c43c070113a84a8128441009100000440e14414940c503056003280c501000460118000a0b08920074014090300d090040d6002c030f001c452040312108545480450079042c0b01504100c4c00c0342003c601c4c0000c0944e140c0b09500034160700514407c00e880b460940d0410142d54a50281d84100c0c281d02620310300c03585440f103800c18040d000c00400b03a5154810381c088030100324 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110986223 1250 110984973 110984977
    0x41109090106180209010507060e0d0f0207080615030f0d0c1205070203061512151501020609150709050d0507030b060604030f080a170405061e1909240605040c0302 72
    0x4683e018a84616044405004080c0d000084e210b41440002d110120200c0c0e0b06020b8a07641e021103c0107480d03401101800a04280b9000122404651214000b031012080002d000c5401401404034030210565510001e8a403c00304141803009005516154906d150007141c0786401e58828150f52401c41d05004d000c441501540f20007a606a000d0004981d401c200c00c00703001d07985000600071242c2c06426600d0701d840e045001e010320203146800020040c0360011000306441707008c42440a0010740c00e1525034075907603901d10002a80071020a0001c18030b100d00618003c002048041d000d070008030800c0c200507488501512054a401700b05100261040c41c00d0340440e000d42e0b901c015806025852925590f60b1604401c1818091041c02e40b061100049903030306080c4a03e00c20030003004246800c00d000c8007080141020000c282040d04140041100080040480400b04c2e250001e030390741680c00c0040014124003401501c0c19125003030b658002005070007100941e0402d5400788440d42c0400c2c1e0440c00c074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110987473 1250 110986223 110986229
    0x190506030c010c02131a10030903080a111b0d1e02030f0304110a03050609010f061a03040f0602180f100804030c0501060e010e150a030c12031403041109090106 70
    0x10707085428010300d5580034110f070011042c000b400b86150400051548400c0703401e541c214920769402c1c0105a60b581c42d116181140c0100720f4501402a1042c030b55016020510180c82c800a65446401031401210540140ca140980740d1262801e29038003c420544c40340707644071080c00022555410020312461208040e4042140c0d13600461510000d180c2507a5a030300040c000716810444008200410790b10610781101841c0100c1c0680303c0c900b4821241400c44611407081d00101c0e0501004000f40c5c0452030f41d505101e540060a544c0c1c0c2d40d01c51030050641d080d03000d40205034610100303041800c0341640396020520703d000c0d6543c138030b885024001c00c0000c1038003083d2007001031142000940003034801e00a405d040c6202d90004294191100940d29480c0d200740c0100040680320b200700421303200852180781d032120041e140e400300301d03080d074845a2290281d4020601e20352aa05101010503205582c2000e0750084900c645859041a00d001d607007003405e1025851007a03420313030049051580184242012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110988723 1250 110987473 110987479
    0xb0f010501050316020a050f160e04050604170903010e07080c03030310090b150f070209011e0b0c0a0f050a03020706020d020601060f03060801140615070f0605060f0a03050303190506 80
    0x85613214003464404400c032841a80c2140a101d49180000c0c00404c04420915500310140c880909a800320a12002403070380103850030751001040c000400c4010a0881e04150000380d541d0700b031010035078520198454a0400b940640c80d142071441002d40105408056a103203409592580c0c4100081540d80d0105030748254101112043c2001007005580c0b00502c084c0020b0002c2c19440f40b4031204000c01e40184e103959010380c00c0014050f045151144d001c1d40544111940114000b008107440250300c46903000d03030400300ca40003807425800c80003000f041890079808030203001e41420314600303c0d4442c2c4c03400c20110054890b0890100d125400829006403c0c405640100700d00c2e860400216441d81500102c131050595680300804d880ca1f0a000b1500c08424008408511f03043c030b1400d010a0800400400c003099400f4050390000500106140c00c0b4103810010100c1d5a4845000081c1003210000c14283d2003c0110070020070000e0100c0614414220312142c4000400c60320344480581e082141c1c8564 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110989973 1250 110988723 110988727
    0x5040b0604110301120c030b0403090e070504030807020f13090309050310020c150604060b0a03050402010e0613050d060f09030c031b0309091515021b03030a08010b0c030f0a050301030b0f01050105 86
    0x105a1042c20090703141c46011b8008411000c0d586c6d2110040034100340c50980c00104002001c0c4810095240d03010303040740c040c0c6400c40c54140307580c40c0c1001780e02440384000c0c81000d20160210740740e6200030310100f1804529000b00f1521541d8940074009032144e100b810702901801c1c001c00268502407098034103402c43700d00507141480d007440c0703001c4c000c0000410555105a548001250a0712060050140480692130014090070030b8000544814213030401e80344180b0b0700300400540b50325404110383c01c0761820344070380c2e001c012503145c104003920700070b0720507012545001c03109002d2542c4050000344090094490304040001e51540c0c595018203040d000d40420f440280030440040158407145441c80f546c500e900d411525003c80514940c2d004c3c40c4440180d115514080844000200c8018000d6080340203604e0a41d040700c6c0545035140510071258003520115a00c03c140030b061046400240d180c0303580659031400540064500d0300280410b80f07610400360f000440030109031802c641070b144141c440034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110991223 1250 110989973 110989979
    0x9060f010c0503070b070306180e07150201110304110118050312030c090a06050301150e0f01110a0c030f17070b06061e0f071416030210030b090a05040b0604110301 72
    0xd00c1c8036890000448191104004031808200d24400f641d0241ca070700d940c08070703443d031178280c0c91381c84003490a2098190919110421218401c00640c01c02150703054148000b0520384014164014003628040d2101100c0c00010002044101e50404512900980703e049821140c0301601d9000881c070b0260035091740c040a0b00510b01211a006554440220380402e1f2030321580d880030840f00c0c5080d5101401080010005000c0d0a080c0c800c8445240224074000d0303104d140a02c00075190a00c0e68125038140900c1080c0d50103011000c0c00501556a0000c4a005003140c3c2c0380740004400401c01c00543d040c86c141e085800810311f81e03d0489d560250040c0c072807102031300c82c001005800e50100e00c0c04800001d0313510100304a4000c10018046102240818988400c4a420050081c14581d496564250003002c1100d00740b250b00c507880350680750159821024840300c04015401003603884000c2307900c2090b00040082444040d0802c5d071141e031041500d89a01c4c2c40c0c040510055420802500702040002c0c0018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110992473 1250 110991223 110991227
    0x10f0602070902090f041401082404020904030c0c240503010b1b030c0a0f06150e010902031012200301060501090b030a061a03040b06090705030a0b030a080409140609060f01 76
    0x5048024001440c8509085d00000000c045803c204080060b442d903074001042184030078842110300614030000f08290300301680d04800f09201c0100028826000480410103140c46059802c074001c0e80040340251141e115440700d40d103900c2c4c1c3c520f503561900c5144070b0516102d1080041d02c0c100c03070a101000f0b04160100d001c0744603485000172543c07550f1005000480d81c0c01410000504514045d0f548101000d6580c00c29106542075010300b01d1003101c00b114100821081c0c080981e0440c1c40c1c0c0100140c403600c800c4038101d0000c549910038941540d10721082d0041c44191000c03070702d150300340030217005c41040824141400e0741e44030322030715000c14140d0408001c0a442700008550203480d08800050243d1101d8290348601c00202560b4480703000841004100100f816820b500520110359808040c43c103c1c000902c148402001c400c2d440e030311032403c0f444686040190103610340c1d10100f1640c98940300c5140308000d0950300320b01a054030341000814500d0030b02c0151b041c00b074079015185140103c124001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110993723 1250 110992473 110992477
    0x417040b190e191d0105060901112406100e0f040c02070e15030708010e060a0e0f070806070905010c0f020405090a08070602030105010807020c010c062309010203090105010f0602070902 81
    0x31009010241d11006160354070826800e001030307403e000020720f05041c08070400e854150040004410781c1000c00600a42e52241c0c10703900100c80901c0d0240c1000c911250880c203000030385c0d00030f1790340250005100c0420424041000e00c9041c0c00e90b9034400996440300304845040400ca0941e40003900d007180340405060a4000075071807165401207415140e03540104840483c821980d00724647c243c1c03000060300307207018410781c2d00800c50100280484500b450340749031196000f810b19407005944280c0042110001c1c818215058052010b44e0b070300507500e24505460340d20803a0800001800c8841c080340720360003014100e41075030300050160180601e43c0d09110040402500d40c102c10b10034841003c0000b0461401400c6440c4500300250b00e07940b400002408503100507080f04155000303d00f00c1802c90341d11100d038152040d013083d400701e50b500261482080c904c02c0c0206a0078000c901400300440380b80150000c500411046008002a13a03841074403d4081c100e0340522001a0411030382003001d2495900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110994973 1250 110993723 110993767
    0x80609130503120103020411030103050c09060d080c060a0507030903020307080a1e030f0c050a081b040801090f12050c0709110f04030308070e06030114150c0105040b0417040b 77
    0x5080c0c0c225034031915120b00d9074005000410440b03440100520840c189401150102d001044d40c1e24215411644c4954441e04e41c0b541c40c40c0a40c2840000941540d18031a140802c560021645941e07480000002511440100c4150021504000108119501c02c1c49440c400640540c0035500b408040d5072140e801c1d0340071520b81c034200011010301d9161810b5084600e1000d075415100090004008e00f0303001e069030300d80c2000e102409400e2242c0c200c556009000f0592210320005100300d4030f9407001000b4000c2c001c54000c1c80c095840c00070301d5010800c032420132180480c01005030102250a494080342d1702d10030b200500ad4a600000820803541d08290003500c1a51441100e00b400c207150b88842c0c500d02d030404d0740103030001100a003d015941e9006200703600b50010541c0d48034615070400080d0000200c603080c0c458000c0400820303510348031541c207045d9074030054034600a21142c00d00341081500740c0800d61b000c0e5112210440d0401024541c90101e5046644407205141004885804a818010044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110996223 1250 110994973 110994991
    0xd0e0108060406080d0801060809071406161712010f030201170405190320011b050a021005010b09011205060d0209090a06110a091409150105070f0302060103020f0d0201080609 77
    0x50f8011440c007000788001107800c040c40c1d075010265850702000500280c0090039403074403a0000142403180c10704a001c0c2c50703d055401c0d201e03203a07641d0000d00c081e803400c407030504040d00304040c0d030101030300f402c4105c0001c000c003403e0390007001e01598031800d0300c45412409100007400f0804044250f42c010959000117540540201d0958400d481d0b1000e012601c0c5100c04030840002c1e0380c0310540f40c55000f5540004122070b003040000c1080c02440ea42c5591945044040d40b8140080841c202c046a8802c00c180445040500814441940d440a08803144d030054540e003404a090500322034a007120a10032644201c10091800914514030b400303008103010080c3c20380e40c0714090004503a01155490148031040500c0d880f489545040c99100284070700e0040d0000f1607100d1002001e070125555a015140c2c002c020707a10701015041c02200180d0f41840746442c02808200101540d409068000c40c0003812a0300a0303071103829042c01003041064150400f2030003030200d60105e010420360309004d0009030b40300100b5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110997473 1250 110996223 110996231
    0xe030c0306220b0408031905090604150204260106051009090908040312021005091504110103090c06050405010e010314240a0906050f03010203040b070f020309060307080a0b030d0e01080604 83
    0x80c1d160580d511004640a407402a00041405072511104098540200c64000d0812031411304e000c27400cad103030f450151010b031034a4950440e8454001190b81120028100000c000c403440701c1e0032504c0700305410b04034a03000d915441c2a0000450341080c19005007850003a0b600e0005040c20450484010002c145060350210810300c00031002030303e6142d800306402c00079001490781183c48001c0c482650320040035014903402070380c2c0101e5040070305540180c0042d408900b484803180c2c1d2200403002407104c82c502900c665400000003509540040080050b1003081e40c800c9481001d103401035003030b503402c9000e940c40c0700c4407800019448420504004170708449801034518845c1d4010000342804c907940c0007106000c2c0d41e480204043d240c104204071400fa8142c009500b0b5151035102c140030040010444001d200712803c210348444e10900444051440040040d07407a030401c90802004000111403200345146024a41c6c04245000104c800320383d68187c3d29500071a0300b040045489a602500b030681058503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110998723 1250 110997473 110997541
    0xb0415140409050603071505070308041b030305040305060606180d0201090509010b09040e3702060d0c030b0a0f09020d090606080a030215071421010608070e030c0306 73
    0x1201004000030310b6294070100d603500b818070415082c0041035100750410100903c0841c20250040261642a0b4042c240421655600c5c01c0100d14800b00c015541180c4005c407001104241d0042d0191003600e0207042140c0b032a41d20181808030310711515110b01511184460100114603008070001400791040c0b401d4280950f0784c8002c00c1c0280303030a03080220808004240309005003021b2042103500c0a080000b49034903d1420565a900c5085014640f090220803040710061801000021a51b540c090403c5540c0c0c1c004400d200b00a01084182c40006410400348440310f260500d0060b090f01ca40308459034180b490844044001d6020039007501e078140c3c40d4001000403d00500c140e00050540001034031083c1d466150081c10058902030420008440005000295502904000700e1111503504145da564072048200858200380118000080070300001068071a401041c00c3d01a0315581c842c0c9601c484840c003059113032001408510340580c02440024281d0140c80b0400d441100c81000044401d1a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110999973 1250 110998723 110998757
    0x140f0c09090114041107210203040e040b0a0b0306040210200304080604020108010e10061b0609050c0a0b180906180103080702180702060703050a0209120f070b040b0415 74
    0x1c000d07485030102c03000305588910241002e008080440c0503002d040344c0b81100c659124800240c104c84019885820303c1e0700200903600820480380504002545094203250910340002e18000403a1448001420442054064100010710a000380c0d40240800c81c2d155448000312501101000504103500340f0408071013550f9401e1000348040c1070184c002c1e229a140a00000d09a00c0707040c0e00058401640608111459034900e4180c01658014075000c0603e00b00303140160135101c50420040c001516100102040060018020900304015500908200c1e40c03000385103100e0080c01ca03011000c6102005d030f140c1ba40792405c44244d11920040594075502c0b0181861200441e09800031907139800e00040c0002540b45c0015400c61903840112030210798944440002e465500150404040c10744400200d00520540e40654854a0300175291140705085e01c56259510602000103844a005120780032408204d02d030121000c1c1c50a440640d450540b4145c96046c4950f102c48410040000305103181440003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111001223 1250 110999973 110999989
    0x314040806010e0603070b121f08011401050103290303070501050f0f090d0c24020f04180b0d0201050a03020d0c0903020102011a15070809060c1e01140f0c09 69
    0x112030300c0102441d40c10032040c15014100940550b100f503200000400003900e0b91421509058400c0e18144007584a805441742e45503c602d001651551044001003004481544102c0c0740c60300c40d5240015590b40d8100550440c1d1034558a500001c00d40c140751203d200951310000e1000c0b2010741100d150080d540c4807142141c50941d000c20400010009002c00401c0c2c60071025000018040504000341c014000a80050f401400003030041004e982c1207884543c0052074090121f82010b025540d4414804c15144c40368400d014507117100310000c1d21a0613172040b0388110f0600000241440c020007101c1d800546413500001104c0c1c04050b0204000341d081c00c1e450082e0004198240ca880140030304500c006406d40b03a51407180e441c640e81000310807201d0b5a0b000140c4002c05e000a458503601d0fa1a410180030034481e00003540c1d0005130014901500d040005041c81c0052982d084244542d41c000c0d40490076621032414601c2402c010a02103440d9910040820f82c101407106095860402c01d00045460b032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111002473 1250 111001223 111001229
    0x706020a0807020d050c07030b060103090c090506030d0311040302060f0f18100309150f060e0f0a14070e060306040603140606100f0c0f4e0206070c031404 68
    0xa03140000380180c1d150100a4001d5161160070190b0601d4560006c0c6a900c95007444042c1008040e00c0128501d0307402a403215090a40141010740f00707039114141e10000d081d05446c10313800f034070641d0720004440703100c1d220701e11031602822059072800340f440c4c00b0054180c1110400d41c500d03d4003005a041d046400c0401003aa01d440c2d4450400c03041d0070042040031854100380031800341030038206000c00003501c4000700c0416140a8900003041c403002d402c1c840040409410050100081c1c1c0d080c8460a0103c11031540705100e40030080c000014880d01d03011144d40107544100c0483c110303544041403490040059640a680030340000f03003055480d03c400503482c10505100c02c0a40007001031100034207040c1940428000d1504000c1c2d40d0802008000309840c00489010b00b0070301014405408000d4064034a030018050001d0b0500c0d01303c2c0d8800403181d4100c5d200c454600b9280680c400d0b60b00808156203010b81101e564000e041140d4508405813101d07003000c0011400c01c1261880d07405c0500c01e0703001600c09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111003723 1250 111002473 111002477
    0x90e090c03010501050402090904140709090804080601080c01020d030911040207141203090c090402043308070b0324060c0307050c0a080a0f03120c030212100620030706020a 76
    0x100155000c00c0c9400c680040c5c22550050340100a416110344401c40c9158100c1c2e808542e1011070f401a100c054184006a0411860a403d042c5050288082030b00900191941502628860790b0b8419685a54400c0c80243c0c501503005860200200e134041e604c5070b90058000c12606282800c2d082c0000d040b030740492821164500300500c0c80213201020418a81c2480c2031041480c030758204080385a64409042044900c1031030340c100098110f4503250048074001c451810030083e60901c8800c900700441008075111421001d031034000503c3c48000620b00200d072400418071346503403a0041120b214034075051504003030300c460241c484401c0d1102030082c6464001900a15294412803030100c1c00d184924600c41d10411810409001064000c1904003003280e022486840c05007c5160a640e01c4e2908600c00a0240c90b0580207541c0507019001010311003802d000c01005980c50f4402110303540d55900030240000c10447e030080b424110020419002000e8000300c0382090201c0c0e0352841680e008001c4580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111004973 1250 111003723 111003733
    0x180605150301090b010c0b0a090f022e08070503070507050a0b09010b040b030f06010b07050f0706020d0801090c0e040b010e0d0f0b1305030a0804020103090f050a030207060201060b160201090e09 85
    0x15a602d0384035140340c040007440c0ca146e1481854503803580307800c005442e034500a90345480d00420005102c1580315074942c05080c0691280000300351561499107000781d4035074802c010206030801e1b88184001c91113807040c0e449160640e25800c0040b2807a42001304c00310707000c0c490201420007081842c407000d4400c0c28030301c00120385052100148000d075400d100d03049020364040c08010070311003404183c0e9419a072007800c0709600c43c3d0701c60804c1841c241d45280c110b0b0550085560100765550f010801c1d00701c00407203413143c010b1641d0703501d494000c5070303400b480c0c075000101c0031040c501a80c0b405070050313402e1040516091800d184403030001a0002a2403030200c07014001144078508100e050000d05034003240f018565150f00da04e58680c01d40360311401e60445e00700301d4410001011a03010764010f4504c0b5030007182030401c124040ca4031643d02c503000c06041d405131043c12000075142d84140115410740710750703450041c10440c83c0d51311a10080c03c2101c0c01c074103008480e0703004100040644490307842948104000c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111006223 1250 111004973 111004979
    0x120809090f011502010b0d060f09020607060b0102012712030204150309050f0c100309240209030723040f060e04080d05010603050f0408130b0a050d060f0f180605150301 74
    0x2d00d84030f10031207145041d64100b5002d280c003903440e0380e042d41a80340c2000021588004a04100008088032000203600c400003044030414010542e1241e0902d8600ba00200610800300400e5000f0700712240792080311400b5941c0440c00100418100010250030341005401e140d240e085800d40c1100c1e0f20703121030001c0c1d6103805210601208102000c8020782d00c1020b400d00310f12580228807500e03403100d0140c00b0f040d00c45031030310100903040c41d0801c41da444848400e203116038000030f0b04e030295200807100352081c4940500407401024142000f0b290303000d895014403c1d00603500c1804054a641c892405d24250340b001c0019180c28030306003482c4514440e0b680e083d40d81124200c1d0408850f0183c20490401d85010100503402d00503181d074540141d003000001380c5546a00b80c115442038159003201d0414080820203210080d0003030050010b080c00d034042031000e19214202803e403165280b060340081c542008042040e9800041d40ca00781081c846070118600d0b403036901081403d808100c80c0400030700c0000c010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111007473 1250 111006223 111006239
    0x181e01090f2d03020a12200901051507060501030b0118020c1905190b010f0b03270a0c06021b1012050603100e06010e01050d0309120809090f01 63
    0x4001805200d1145500341d03081a003600003a000402010446504030800728030542c10520022004690007051004c0c1d035600e9071501290b1654080041714240c544407d0101040741c45203482d5100303200a00038145076880c260403c078200c403414001c0703106800c01700310143c042040c07401a00d02860054400f0a495450300046500000b4010040c1c40400d1041c801079540c8500400e4000c24075215105903407640d40c0a080841c1025413a945c48122030701c5095200b000c210700a08010704881e44008804000c3d03a03605030f00d404034413088500070b080c0c1c42d01081101104d80cec07084204e42c16611140881312140e0301036940072101903c0f03412a001690000f5502298603907025012500d5102c180c43c180c000007100c0401500340101e40584107003690700d6000003046501c042100d181d00d501e508400380151049280e107540c48050a001d01d820310440e4100106050410b81c1c1d04030450f56060b07440454a81c0f03042000842c10b12140c02c1100e00840800000126a8804003503030700410041d0f07291034480d45040c0f10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111008723 1250 111007473 111007487
    0x30a091e1109070c0f020a090e0c030106080c061c140415050106031a211009020a09020304021e0103022109160b1803010e010e0a05010507030614010302181e01 70
    0x700c2d214006100801085513480a800f00e44a503100e00742000d214800d03c00500000107903041226880d141600140c03c19a000501103c10340342640200f0489441d082d015444001c03501915030010405c01007100b07110780680c0e41d0355180c080002c00160b10303840440410705180c025a41076865801c4051070341510503c5100e100c0c010b2240c2d0600300400b62a0643c410030002c10115000e2080091426400f4540500b0b0f10a400c02c5c1803d0040c0c405550304580c0c05070080c10401002c1e40641041d88000c80c07105407902c03c42c1d0103a500100303c5004c16602200c0f65042c850650101810143c0030b01042800360141100c824a5040b65031f000349851030030248642c42c180e408103030100f1403624443c0410500b07103018100c50b480120020022032400841001c00d01500340c0e0300b00420f041d07107000e421500f140300209005148620440081c004c40e203c0b0541102528414051689090b8000d40c1d0700d122980240c0c020507204010407030307511074003003803000141000c01d200110f51000704518882858940c0c2c0520 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111009973 1250 111008723 111008753
    0x30e04060f03080306011806090303110609032b1401180605010503070e0103091b060210090305120601121d0d0503040b010e2203030c08010920030a091e 67
    0x6010040146001041d040c071414521010307000f41c00000106503a644101058030040c404005603901c002d41c2da990051041e5501e1005030b0000d000802c5030845010042021030007400e2601c021400e11010310860080d08801401032506e6015045000459409a004040070b55a80714403d040e07542c07500c3c181c4001604103401b02000c00d898104207001d1030384c103d4141c0c0c2d0007403074628103040040035840044e40184240b003409000003004c0850000c0d0b180040c61040c041c2d800d40d41c00e89418400300601c5100342c070744540d80103000c19000d10450b010300860b410702a034444030502d030030a202981030344c180088400f109000d44556030943c030802103140c1e003080100840c1d1098644189545400e4131014011607042c0a550108030800740130443d21ba031040b40f04000250800041c0c02e14174642c1c540580101000b00c0b94bd000304205500004441e44a480707008034206106410140303111008108001c254001480001001e583d0b4004602107121003d948190000c9115030981c0c00a05042140f010700c0069 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111011223 1250 111009973 111009979
    0x41502010c09051807030e0c030f100b1903080307030b060307030903080606070c0306050402060403021c021f12112101090b06070f03080415051f0f0609050105030c04030501090f030e 80
    0x4d070310761140c1e8a140c840903074407440918000a06000118070b0b0743c100414480c0c070b0341d413501c29052002010304000c03c1d03041c000301c90304004220820081083c400100e000c0f014020100c41c0000c42040801d003220002d560001c52498000360f5088103500180440d082034840400103507803100308a08241e0060299a0050740403501c0d642032003213680e905000b140c064003009002a8440010804549030750003a5406141e005141006072007142048034092500100181d1081000510070203640725500b25000030450266a2261400d1304602c400d0b018049030089107041400c02c0068182c44040800f40c02038280d05444200c00a5142100200c241d4041c0e202403440344e0030070400c00001500c0162607543e20703a458202815aa600c5080c0380488010b05074103c9100341c1400200701d00c11400e11024041c81e540d9007140001e440d142c2e0305008040301a030003a01c2c00718104102c00c0c44a980a80040c50344000c50a98039490141c8a0740da080c2983e00c0040308440c0d0b00800d4480b80c3c201508045a0040d0032019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111012473 1250 111011223 111011239
    0x90c100f03060f15050c0106090903050705010b01050901080a0b19290a0f0f021213090f14070c0c0503010f0209011407020604051c0507080601080d03051501080c041502010c0905 78
    0x4d85040e9140850f20034006110300002d01c030f14079070020b402100080c5035041080111a0007400c002d8001d500600e0101c905510300343c0c810065601950a541f00740e54181c0d50b640b000d80c0c0f05403c1f44010301e0010100307640900800c0c0800e55004100b401c5801810485204125030061100742c1c080c00364106111101c5d0070001d115803900907511881e003002d042d03140d01d4640b85001c06440242d0a02d0034220800000e41c10000c0e40340300341c0121000d01400c4a2800b0f1080020184c9003a54508a5040350361403029003107103030049240d03144903604148003640180e00e24044143d07500c000a00310744405d00c500c951141c010a8400180d85c00c40a8004072410b42054545058095070001d10744d44100d014041c410f2024020501304041c01074010300210313a2140c02c03140742c5038036401410f40c2d44a09109103c542d10409007030584441c40380c01501d001c2d114400c680009250303800c0054034003090040c2141e90128090000181d4442c81004401340c00c441da400009070701c80740c0300009003c80440c1e007006000f0245 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111013723 1250 111012473 111012479
    0x1002030a030e0703021c0c0f0305030415080f010504020a020f0a05060a0c05031006030513120905030105060114040e0c0f0403030807090e0403020d0c03020709140f180a030305090c100f03060f 84
    0x28903900d03980c000e41043c10031085068901e409908406503420159002300c1849000c0700300980040140281d4201904250207440510ba0440c2d8a200448240e0901c2640c0d000402490405030060011f003800343c010b64600403000c0308800d1070810801802c1d81c903980880c081c44241c0300b140c4a05259080c017894864610b00c0c1002c0b004a0100b8103108100804da40c90f40004d00015004030440d20040e8040007010800c2039150f00105800785501681c1c0c465480c08000c500158020b103e280b001100141c50309040c00d107420000481c0075002465081c0241c0f0400580207554508801000035501c280c481c090541400d64000708510303040e801c50565000c800003480003080d00007460040c0c44803280340c020b40007107980c44d003242046107981c05490320a080c852101410349001030041c0c881c10340f1440080329592221221001d40f5800100c10885800c04144d0703502092094020941c840c90840848180d201210045610700488000603400070320821283d038000c0383d0600840c0003c1030101c828411142c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111014973 1250 111013723 111013729
    0x51306030b1c0c03080304140606031b090c04170f0c010e06190c02120f06130f0b180d0306030b0702060403140d0e060a2003130201050c03091002030a030e070302 71
    0x2600e070740c0204001a00c2c0340b101c2044110400c0f840503590208556480b0300303251030a641080c4100c3c0343c1c10300a005010006850f801e001640e010884991410100401c49071814007460b0840500b070030300c1c01c003020007001c5500031042d00b82c070a2110707080340101801d590148a0b03604000020300c3c0385042103030030600844181da61000ba50307108088040e101c10880c022078000e4800301701b41e1200075001305100304440c81c031010128102c0075211101e400e50f021940c0b1189285840c504000004000d64001e84a54001c18400c91600d9849113061248008c59514464141e02d019181c5680c0d4000940302c0e1010b104001c030b01c50f10f55801c07000702e0000301100e0600340c0d030261036a288410118000b0601141072621085035400c0f04e9940c0c80c418080e100c003401e03d092301101808420340c000d042c0381c0c40c6c92041050741c1100c03400c82e4401c0646c2a0300b080619115801118564802506000984014000304a19968110505100d64141d40040d95140502d0704080d05035a0400510348058101203010405030b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111016223 1250 111014973 111014989
    0x910080c030c03060d02090403030209040e0712030f0918050a0b0f15031e0405010b0316030b0601032003070804020f0604210203010e071d0a0501060507020d0809060a051306030b 78
    0x2e1a032150b0580c596680d900803800d5081c0ea100c0182d44681c840091000345900341d401000e64480656050100c0d03050441a203130740f50034034070600070300100000300c51020a00c034600d10040200304c0e2502071085036980280c0c802d02c0054003001c4903804c5c0e6034000d100021020748515006000269008600417440200151414480c0d101d00c00510f20008000b170180d1a142042100f804091888a94141041c0c10114001c01103840054061b11038440858260506d40e0146821294419140ca4050743ca040046000d400c0d00400d1700404401030010000031140500958810310309139542c10a94503040c0100290400300001c12402440108014401c038a220b056a8010102c0e10104440d544036a1002c43d00400103c1c80348034250140200109481c00c00b905564a411a512140d00c0305032079050042040350400e01c10040803a0381040101c00500704071350700000d0b00740500c40d40360818010101040285d400b4141c008002080045d005400901d01c0030701402409039490704203d94446034001c18400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111017473 1250 111016223 111016231
    0x6091d100b010e1206040c05090c0d0b01050409110307030f0e0307060b0a03020d031211090d020d260405030708010c170907180c080901050702030409021804050c0910080c03 76
    0xa500d803001201c9030703405039070b20040000f00030308400294001d041c0c220f80c49410a80d130465116103c0080000c1d01d140000041c2d000b445c203809402d103015a4007960300001c207a050001e41c1800010320000512070440e00c83c5a80c41d8903442d040070b58902e80b030304004040f1140d54442014031494840711141c030301d03000020350740000d5101c00000f8200480b5000102c00484903400250311007071a00c105000c15511420030307100f840d40c8034000d00001000240d14840b60203072044040e00a00043c1036440549460307066032201a005030b41b4181d80d417000804007145056049259945004001002c0042d4203040000400402099008100c141940c07040144040d0400308a402910b244801140480784d040c00aa40140841c400244c000e22000006001a02404000d280461000340001c0c03d1000c042c06100e125490310750285103010709086c44d403000ae400c0003c00100740c9000318003c0009845522509001c0c2000c0006c00b0340300e448007410002d000c80958808401c011a201c00e110000c140c2006032504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111018723 1250 111017473 111017503
    0x20f06010b0906070204020c0d020d0c080307030906020904090302010e0d0203120f0612010f090c0e1306050c0c0601030506090f0d020705010e0d1e050c01050a0c020405041a010906091d 81
    0xa140c2c200300000740c940c010808041c4d449440000d1040003298001381e07a500b1030060341c00b50b40c52500c21100c103a5100d40e8803400030b00344410400c0050740b264840e41c00380c0b50b0703588140c01c01410b100c145004601241c031140790450240c4e64400d12608000c1041000410701c4c14948029403515698200316215400090b1102c5a21050040410615a40e0b44404521880340d04003c01c0400c48240061000e000303490710555400d608400003284505200783c20a01c6202c0c000350341c141c00e221544d60031009203030040080a90728000d01001003003003800c3c04000c1c0214018130003804242400d074456400c00520340d840c0e91040e80004c01030340c0e4142d0040780d02c4044400c00d003050500304181c00007040000130441340c01400e0110048080440f00342942c440c109840c00f600c2100e000140500c010340b40340c131403114100c01080c0201041300051405810540d0b10074454456000920008840b044501c1001e03000f91405a07190481408010301603c5140c01d69079066100c800d503420b00c3c80c0416100c0344e600210381c44e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111019973 1250 111018723 111018727
    0xa290d02040c020717061506040b2215110f0601030b0f04050114092b020a06020f04081c11010b01050306012003030907050a0503010b010e10020a02090c09010f020f06010b 75
    0x40ca0f402800400004c2400103c901e0f501d55804a800d03844440440e0f9190310401d0594400f000f50400d441640e0945950410081c5442103505c00030081c03496005542c441050f440c40046046000380f500004403000f65150405050000000e15050081003021008258000750041001c1010784210542003400c031103001e50ba0351030710306006000d403001d1524a2810b107418018444810400110001c03400c0ea0060010301d00c01c2c4004886503000d101259401c0164400180c40c4041100c5034010900d624204210703e203016a1400050b08262180c0a03000d562945d1880c551031440e0003041481c401d60401c0f00802840b40c44134006440c90102600c0c840c1040700315081c8010200c510055142500009021a5142d281c041a000c0da24102030145074014484214000f034242014015645602c10585850014a240c00180143305004466010440c0308100c03190025807503050b4100d000d00c0c04200925641c102c1c1d038002410351060003518000310342c0014081020390703901154090550b60040c040e1a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111021223 1250 111019973 111019991
    0xb1207030212240f1321050705010c05030619050d0b04030e0406030b10061809090201050d091a0c09010c02012715020f0307030509090601030204030b0a290d0204 71
    0x35140c1404401d041c002e1000d18002c840042000141891041492400d1307508941c0d928017101c0c1c104070b01d14000030f00c000c2e410442c6d03100c1260945005c80c070400442c0f4000781800fa0702e0711030301d0075540c070046068082440002486101e0404481011803d5240358008558a15141c0800c80305e5800f0300001d0181d200c40c40128041500c21984004035100003001401a01c0d1a0b084c000708000040e60300080c40500349078000742241c01222881c2821180b542025038161503e079007080501070450080741004400c0220304a545401d2190303801c4207000d4145141c0000382c84e69078000300c1102070052803003001d041c058052241e070300144813a030640d8286440c1d0305262184414880381e1180d001400584e16000401192202c2c82c420010200300702030342228241c050300d0b141e140e2644183c50000d00010400c1019a500e420035841468011070185401450309559807038181241d40140c9505131490b884000b410710b0984401401d00b0060004840300f10345400c035500007a114090034a000380a1900e4074654 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111022473 1250 111021223 111021259
    0xa0803130204020f030a0b1903030804140f0d02030c1011070204110408150a32040302030d110c060601022d0c0d0c090c0e10030209040b04020a0f030b12070302 70
    0x4c2c60440b21200d01c21600c904041c1706035000b400e802e01050b8040c48120000769440541500b4803000c90703805031075042c443c1d191625400d009884190301a05148205d00c124110354408100c1140c1da87c1244d03000d5a00c8420101866007050380c82040c2c04a020301305500c80e006500e0307141c01c42d85100e0b0b040b200091b8211142102130701038003c40c1d10100301409183c0d440c461030355410140c180f059a90a03070410048000689103005032580c2100c50303000020014002c0303070010000c002a500240640120383c24104101c00d44426908c180003806828840400c041550290400034241c000350240081c100c1c0c02c1c00c0820811044035030301c400035410343d0400304086114800b0b016441481c2400303407a50305034042508003035100300700745d11030402c0092401035101c45c91445159150a072150003400d442c84600d451104402075003100b50070320f503ca9562000e600d1107645510091505039040c1d100c101e061160302e10090202c40d210741c096401409020f088040303418020904005499046840961103404441c034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111023723 1250 111022473 111022477
    0x80405091320090a050c07080c0c030105040f15050105030d03240b040f090c080708071803230303040f0803070918090c06050705060711120f03010e06030a080313020402 74
    0xa004003461011203909900d05002e0019140e20070b580c240d145480b41100c40c022290100c5a1504020052054100180d40c401c0200b01c480c40b90011101c0820001c000682103680550307003114021104d00480c0100156000c070914070001032441000151f2418000c2600c5070881d106101c00c2550b07a444c424110813046c8044c0003220304044940020b50b88640941c034403940580034200c1904040500058000690300407110001100d0780d803640d2980b608903040e683c861000d4a0a418801c0b9420f0b02119003506405250080d800780c0610f514600751000e00e13a4194086240711103c90b0810410040410701e80804455515400b0410a0380c03035803120300071154010f142d00009922035010200000c1d8031001d4100d042500d00901071091243c1d83d62000382c40e203204030368000b03040390060300000f180701c0c1c083c65010044a84107400d0310942d0031000d043c28102c0d44481c40c42c0756041008001400100015074a16500020640091181030084e1722800110f000084c02d40c10710703c003000c0c3c00b601107450f1901 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111024973 1250 111023723 111023761
    0x3030d061502010e07031a041707030f08010f0806160203130603020403052811060405060a120506060705060f0606070c060503090607030b0a0611010b0d200102030708040509 76
    0x4011180c1c079141c509030040c1c2401c041d8001982000e0104029410120392182240d1703008003028000d1000c80c1c0c949901047c01401550f0a0000c8492003195002c8100100110341c400d40da84840710040d030324042c10710207040e0005403004040c4002030241c050001510b41d01324801c442c401e400c90541d14802c0b40f8610981d0040e40c525001c40c480090f860350103030040c0c0b05603840750013502d5858510308001c031011000500d0440201c030800c605840810342d070600125002c034002e03102c0c1c0d1409403944003060f06940b04c048440e000074180d4440c402501494810785070040d400300d41c4a40b03810303115210180d0b10f5001a050700102500d031004a44150f071044100c2302c8150b801048000c0c05540c03084054141c0e042203034494210701610000400040c0b0900c921b8031001c1c40240012619420800100c1d400300144041c41e56a641ea0302407245950ba40e03094a101c054415042c100e20b02401c1a0500030a01413540e92034199030040c0400000120100265000d44200b0f40307013a480c0e9522801c50501e1491424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111026223 1250 111024973 111024997
    0x3100f030302070306110a0507080a0210022106041107080c0c09100905072c01140313020a060806090402120a06050705040f140310021612020607120b1e0303 69
    0x120020406070081a00400c5038040c61040000c02070404441e45548034240c2c0e241d000402c05c02908000501100251018000303e104070f884c03038075042ca82401241d11280540c01100b00c001141c0b04100c407602c81d81036000e042a141402086442007080059000f21130005016000106645803002c200708141072280e072009000421a090920a00040030410300500e554603080c2000500381c01e008200709215000071312100c3c00e03d180344546406008010400c60f90410140e6000d0840480400002d90302500071980303440071400c1c80c1d00c1000005035085e4090f1003404003140420100da0b8400d02c1c995809a01aa20b2000a00ca6400d09500304080081c2c001c14851508080c0321000e640710006d0800d60340b0790007034201515158003112500300c0c0c908124030381c1a400441d825007031440e146c016200601c2c01c002d00c01d041c40790540c1d0f500c820307000004c545001a800a802c125610798002e11000b8140c41d2158104010100c3e6001304444128480b44502c11400c1280c51400d140c90800c2198aa84816 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111027473 1250 111026223 111026249
    0x3020d0812161218020909030f030907050f0102060c0403060f0209040f09120e06040312200606150c1515120c0a0501020607021c0c06060603150e0106050f0310 70
    0x1a080480d0602d60700c010060020f000348880341c0307100400303224030364000c0d0100010903810141c41c3d08005100c400206001a94002030080410b003140c075501440c0100e03401340207810a14108030a00100d011050388590441d070004003402180c2c03d810086809032500080086918000001d881000e403080340e039000d030820b24002d4000301c204426841211f80c2071159024003103410b500a021119103c00303250842c0e12480c10402000000c10090420441304450705041c681d00401359032440b4140c0801c0c50015060b0032000410030180380090141c00070424118969042c012018070080d51010441548008400030f14081252030307100421034840c00074010005ca040c0c071140001c0685821001c0600e0b406184000c8000c00c0e2503002251072403040c400e503402803c01c0707a0304010340c040c0c481d6261004010f01c194403c0940100728240503c401828068501084441054041d401c0011035a448154200020f000600c80c4075841000c0b0765141d41c9491a0a40760b4441d454a0225100c3c182e021103280860 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111028723 1250 111027473 111027481
    0x24090c0509090a091103010c0516050a050607050703020616090b070501060504060b0703021b0102062a0d020901021c140702060c0307060b01020d021b06030711060c18041503020d0812 80
    0x69000100b80901c0f0b88017079840a440c8038141401d94182203400c00215070b0900590301e492294034a002c40c5107005000b1520a0134007511090b081207000c0d5856000074030300027a8003042c90f03010000c064004901102e1101072840c6c95100501400396030003500703040c3c80c000130000188042500405c001c0c050040c400c0107044d6031201800b40031360005804070050b00594030303048418620b6440300c81407180e040c0c02a110070350301d460401424126208550200014841b040084c2066070307400b800090001c00401655500f02000184c0ba00000d448100d14041c1042d00b04400079a1020b03040e0040f02d21458035588a12103840014054010035040441501c000f2841c0c000b444050341221524a400382c01740c41c1c0c0110345520032038076a00d460f080200e200b030018280d01c219041a10045074040d074a45802c020490700c04401908161040d1380a43c0d409002150307414078800c6042c140c060041040740c00b00100d01030109558112451880042c0c400e1240502401c00d202d686803c0700c8138658428101d40252030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111029973 1250 111028723 111028741
    0x170703060501021b18090709020c0d080c031303080601050c0109060603110909030304081804020a110706090f12051c02030d05010e04020f0f040b210124090c050909 72
    0x4828820301e401813050300a0310a09401400b4186440c0c3d0000c4c000d0204802c05008100d54403002400700201803081c0580001c200c034040c809011030700c95040107808883c0c9080c1008020043c094044444100108144134220040094151406a150521215603520000180d40324041ca1400000035404e000b8184200017980e400344023924494010186a0800c0d8401e00c41030f4801103495000903403041000c280030608280150003c5040350203543c555a00c400c0108059801115521000c41c8483c003184030b5290302440314070701a04203031900c401c03214600740005044000c11300c21090b0070981400ca10082c042c0c148000d460920140004121290201500a580c0d5100e844681c0295141a00104109120300300060003aa002013a0038410414001009407001c00000010fa0041c4c0d035418460550702d0f041d02c02445c0d008a0344204c613115400c0540e00d800d446070204401088407603d0010110000d00300ca4150039541040400100310209090586107841800344c4c460f0300503020010405149 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111031223 1250 111029973 111029981
    0x21c0303091202030c100b030a14030310140109030b0c0c0303010605120601030b0901090213031203270f0b100b0f1908010605030c0c0a08070302010b09090a050319170703 75
    0x5031181040080c8400302c180203c0c0c0302d005100c0a0112504403003284012844150007844c038010300201660000c12883ea1014114000d07131400320750540001c020080685c10a02c510070041503124400c4110b002c681000900441d01400020007000c450f90114180b400035030180c070a10703841c0c601240d94a584444000d0a25086170b00c442e03951040c4040014040d51180c080c0740078014000e4065000c070390030300030a40e0294008484130004200009000000b00c0d194240401c100100c81d2000030b004440c540015010886c60720f1340c041141c489032045c0c0005540244040317809034100303500c0c0445031181421981e4043d0b00d40e100368521306011503100d0308c050752240109503101c00c0761707404007201c0702e91034003561104000d2141601045d000e0000a001c514200000c06010100805852208815503107203080d40d000f032202500146c0d500d0b801c100e0700d03091016146800500140c010f000400706541d80715940d114081c811415405104840300710b880c000d220004075182d03201c00c620f9940c030340300900030010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111032473 1250 111031223 111031241
    0x1f0c0602181e03100f020c07030b1905090c101103070b011d0702150615041d10030b0c1602100c0b01090204230f0d1a0705040819021c0303 61
    0xc0c8141030340500000710082c41c00b0002800600a8800b492074401e225005080f0703003960f030090070b1302002842c2c0041b60074030500010394440c818103691070401c1141d0a010701817191031680d0452074207091105103080002c010030b80b0002225031075090181c04c0d6084408501700c01200301700d4480800d0401c20000418602c40c1611040700200c10086080c00c2c260f40140f605683c0c42015030000d41c883c03000e900d400302c1400c0e0b1062000d040e0030381d01c3e52420301e540c3d0550f203d58000c041000d081040c0384910650a140580c0080810a80c81c4030681142c80c5c280680a01030405078841c00001000d14102c52840c0f0701e010401e07001010030035a558448405010a82891412169079004c0400440e10310741c0b520990f400da840d0104118100e0070844102d081d280c01055003039a00c0446851411034036a544a07101c174103184266855211035144a0809089960141407802800410310046c44400c0001488040c1c054900d00c000d05201914000314030780030342d02030121003a1042d111031541410f415400070190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111033723 1250 111032473 111032479
    0x8060a1118040b21190305070f110310050603101518060b0a080f1008151f0810060f0e04060f0603060f0c08180c1003020c1b100e1f0c060218 62
    0x2012210340174580400700d0301e0b90300801043c000d0101e0000704a2071300008050a202e0410044180c55000019140500840450b006151074008015041c00c0a02242e08007080031403040c49084022125240380d62100d00030f4104018000403134050403042500900020013403800210759484940c54014059102103034070104203610788001c6403840003001c1040f03046924410141101c100885c605044a01c1d0250400d51046260b0701c00502d01803004201000414030400200100d00d040031381001611510380c020703501d000e440d150800c24108440051380e070003075100f1400030f003260b03c1d002c0003401040c15410103000203161000d800c0079062a45d00c401500041034031f5508981c0c0c1d61000c0e00b100d15003070300e00202c003641120794101654180480807801e540d25600b030140c1440e0300652141d180040441d40c44281c0190401181e810b400c150003401208540c0d80b404100c2c10a82c000424a840c8028080842c400241c10300d403030209118102c1d0400882d0312140942d0f480344031055802801d0103040c00c0c148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111034973 1250 111033723 111033733
    0x9080d02072a0501050703051201090605030d020a050d0305040819050406030b040e030d2304030f090602010507020601051009090204030602030f0f070c060b0109050907080108060a1118040b21 84
    0x41294401112804040c1c02c1e1464220100d00b00f000440349134120440c11414804c0500c404152311090300c0d6854003a1400f0080000c9a9181070205494007a00c0c0c0722200c150740041103110089030001c212184280d142c0c0c240030405031150710301208039100b614070b002c0e060041d4803100c4503550340c80401441200d01e580c6c3c003400b4401c0b030002040220340794600b010b1324583c020405400110b070503410100d0740d40c0b0740c0c40c43d004004094118651003644225000c40000d6410440300313815540240c40c0a0161410f44020411460405e6019548050600400e0320a0088140d00c3c50f038148a03c0d04040a05501d0100b5912290783c2d1410070040d41040c0c0c4d882c214a100800001d844c400c0c4002a284100195070359050b0400b003e0320340e40001c2410341d080d40d04004920001290075103030741d42d80302c5c0102041d54a2070907c1d0314000f1454140000a80704207060360604c2054030b00410300c1004c0c0c4002005450344400419580c90006008080c00c101d00c81d0849844003413210281c8000140c41e14800601080c0c070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111036223 1250 111034973 111035003
    0x6100905030f0f07090e070905041103030711011e170603070f09050105031905031605010f140402010f020106060c020103110c0f1b01050702090c09031e070305010b06030f040b0a09080d0207 83
    0x5c001d55514000c4050664881e0314200901e005075001250840c1c01240784500c0605250042819503000810603140420510410f16503942e00102500401c481c80b8840f001e080c411040c000c0c08080c0c200c3c50300d0320311505440440c8085d0307402d014000c001d0000c0e0003030b1010035569401d02c41c050802441558480d0207984190008240d18460320800c0c15441301c003079840c00e0240301c118100000b000704243c4a540d42c8100b0000c03031a50510820f08261060501e40303c0314a0584001450180001540380459060907001c1110036041510410030560908020400f685444401002405014485503092141901007010714401140190000c01d1440da030604182400c801560a4491aa0002d40110b440c40008000382203500c041c0122100040c1031b40d8045400c80d40440810b810341201d00820303000f441e801c00404c2000d1160350f504217010380300c1d20704500e003ca140700c4030b1400040c4040d00f00070561b00091070110440d8440c104641d070180c8042c1e15031444051050094020020072114060006109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111037473 1250 111036223 111036239
    0x909160b0a05040501050304060e0d0c1509030e04020a050705070605070302070b040e0a0c0225090c080f0c0918041208060d020307090c09050406080a062306100905030f0f07 76
    0x100c00070200368480d503107070514140045402d03a0004000780c41c141d640354442d103034003c4240b102d601544060307034400d201c4040700d080c030486100c0043c02041c0c01910b4024a0000030b60001c01094030008210f4006840382941d0809407141d100d444401440c1e409620000305001d900000986a428000e90880d0700154941070026840c0c03142d40509101030b409040094078100c0305400050404580d817040e075a0101100440c181e020200c042d00c2180403150010921411403188600d080d043c2162030100c0660802c10003040c003220024140c00e016a80004403c0c03000d0711041c5007140f0280b5018001c00700c0745071600b050744c4c0d022241410000040c0c1183d020030203924280d428103184a0700140500b00241c503000412008001e03040259050224039440020f9a682d90710a203802811140050241a01d0510f4031604882404880d80642d259012030b080003420ba851119500c13417402d440c6038080c90707580311007601e0300c004650000d9031511a032070305280c16490200f40f0400c406599011210180c0c0c4514503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111038723 1250 111037473 111037477
    0xf040812030411060f0705160302010201321f0602011e0606081306110c01060305010b1909020901020a06020a2c0d0803060609030703031707050403080306010c060b0909160b 76
    0x800f03040e121590b03203880c440d8548080100902040c181c509403401c04e40360348039400e00c43d50300864844401140c80c104190f58080c065040440200d09407890b5090b0708290001613411400d1041610010020003d000b04d83c07100074005901c1d1102c406011951f698902c002d011f00040c1d000d9000a00d031400361403809040d94000c2800343d45064980710b00a0382c800c070307494290f049030220a0321401c1d02c84040d509050132000040072010310000000c101e01d030450030220309403040ea400c041c2c003405000f04104009425400050183c4800e10400750b1395100600040f1b140c40401503015240620009056a1041e003101c42082043c00496810a007024102c45078682d01c01c400c1049504055404020b50004240c00000d5601050040c0340360b043c08215400700b443c0444540040700440c072101d01e407406030312001200d60740c0075016180513031510703055690b1401680030103086a4140524050510b08100391504801105080030b050950307589071607481513541d0810400d2220188404d84030200d90310744d121003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111039973 1250 111038723 111038731
    0xa0e070506030105040b040f180303060b040506040506130906060c020f01020d0813050a0804030b0f0a0203040c030305180429060f0406080402030f0d0509011b03020a030f030905030f04081203 84
    0x1c020740c00c40e840e100034480a84031071201180c0c0146c0e01c490b207400440203485107101544010950b00c0c00c460161074003900b1111941c2102e0405202400f08008a13600c400448081e10b03829039002e902d802e001c12081c0030f40e1045800a41e46242092804180c0b5075116010800450007121640404507059006a0312890307045001000554020002003070111034101486100744210112514540d107a128880c050300703c2e800403a0507186c210b09010341441744400f5240c100c048400210710318140380d620240f20201520000b07040c8900410000308801200c160b8202510b409030007801602c203442c051001544110054030307a64600080000c0c1c183c01c10000362588521407840061900e0300300071090701c510000400403645846041500c8800c1c410901100e80f1206190b11880c0c0c035450400c00240c20b00341c2c2c0c0c00494242200340101500800c1d800101000701d550142072284014007154012000340c80c075142e015080c0d00c8005403900c20005420010022a010700c0b064410b42c102c0c1c1201c04580d403100791 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111041223 1250 111039973 111039979
    0x5060a0e0909070305030309102007021306080d020d0306150c060908070807030507110d051005070908070303050d0f090206030a0b01210b09010b0a09060c020d02030f03030a0e0705 79
    0x500d481101c0c10031600d4190030940400454607102c1d507035a580c13491036104403030280d101d0300100c0c040706100c04d40d401803081180946682c840c0340038501c40804441c3c00f1320788001e807142e016801520641e008a40c0b000c0064589542559600e40940401940e54034480e1420030010703203003600025070159418142d8a1606213a503501c0000e03c526210301026005444080d507400608010341d40000e2207d81c02054001c1c480c2e00d079103495106074148100070311400c0030154060030006103024005000892002e0100040710400501034444840446540505401c5803142d84100f110200a040d0014040c040b41d09019405010951108169009803010340c20b00071340110b82400415299005500042075400e41807501c481811142c440e111586e41000904000060741d5610051450401208190161a095600f0351a102000030300401840711803294004005840c40e080003103589402004071440e400034111821254488000c03038881c0d000fa102406060302c1c16521070045e8802091003030840f0401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111042473 1250 111041223 111041237
    0x606011e020d030f020d060e011701050c071b080d03021e1603050a0c020d060902030609010b03031602060d0203010825030c18090c0b0c101406010c0203070806150a05060a 75
    0x81002903004c0c0810a16801d900c0e030b020f0103003a500c03964038030441c0c1c02841800c8a129140d403500503043d4218051030710300c0421340d050104000501100d1411584060317444191180300303103000c0f074820006401680190515001d0400300600540e03140c2c000e807150445541c12107030340041401034202c040c0b160300550403034618a400000003084c040c0d0042e2020380040e003480300b04000298000b0358a8000210106c03410703940c641385803041d0b042c10004507034080141b4000300401400e000c0000c1c1e50340185007813940040c41000141d0210b469540075101110141c12081d516540c4441c01390307803142a408210b008180110706200f498001c81c01d108400c0360b1b00070f5410b001140c14002a00b650f09404400b110000d030f2503d80520009224004a000038080c0f154003e480c3c240101da40e50a007040703203005e90400d83c10502500035882d0006410794109000f405d01c02c0c40328a891001c2824403100f5881400203010b14410028043c7c00f08400066a401c11104100010385590800026001c0e000304440002c0315 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111043723 1250 111042473 111042493
    0x280905061b0c06010b0d1103070914040f0207060203010302150304150209060f07050a020306010504061d1506070c060905010507030206180330061c06021c0501080606011e02 76
    0x40d10803098016140c040c9020b142446802d4403d103082c00a070f000c1008202d00144500001c4518441d00485d48000c0000310f1960909040040c0850064003540c090750703120b040300e80c019648580c080032007501c41d803e003552140c4103820010000d400034402680103000c0c0c0800c107c0c281c2541801c07039214513800350040000320241842000207400c51201c3d5a00520100109041c2803c510301604009204d0030090401d1882032050500780101030b8401030089042000c180100302c035250107140b078180e1080c50416940d1303500300811071840356038143c25040000002c8603801c1c0810201400140c408a80b294040c441d6948011552403003840409001030308a400480c048500045840e50340d6655030701240e080056024000da01c9a03450030b907000f030815444e83d500111400c1c00880681c046012104c07030040b0140c464040c84280c2c62240024412940014094582d92089029501091100300100301c3c968641ca0820382e02c420980708280072a503401144002c51040e5008403115645d15405030910540d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111044973 1250 111043723 111043741
    0x10e0a0b060415081b010306050a05010e030703020d0b09010c0203090a140112050705131d27060f0103050c03060402011413031227050d0308150928090506 68
    0x4005011160b1150b02c4000d000402c07082c00c0070303001c0075010400140c024284000c9148803209a481d10385418142801020003090f610b0384c500100301c8000b030803c001801e0712840068145034960b00001e41c481c4081800406201101602c540b1881e0f40400810042200c204240d07502c1c004ea01090b0b41c8141803007002d02481c5c07140380c42c03c0ea8201040c1020b907036002e04810158251241184c4280025801007803d01c401a1003101a000908214058a04860004030b5103041c844004110740d44034040d0110030055412802e025901111b12b03d42940c5032410280c2c40c00541c07003000c0c4801d40312407040381d0360080c1d9403a022400c00d014940c161240785a50200c0e071144400ea40205a40040003468440d0010105401401401c609803907035403003500007151440c0c03648041c404843c003c00360700076581d030602482c0c803888554982c040c0c250909024550300d40c0d246186c07060034803800c1c6800900f203800348104682c490b125a1501d002c080c4a081070b8080900d4550120761000344041c00551080d80840d14001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111046223 1250 111044973 111044993
    0x30f040b0708090405090102220f0306020322030806040b0609090103020f03011806060e0c0406020c06030408160c05010e030111030a0203090a1406060102070b0414191d0603060702010e0a 82
    0x6104003035180c280f44510380090119070084a00c18a1a500040c003c428003141016003010495180031003092030f82040000000d0b100240001002d05030f002001c18415842e40400c410700c6404011040c144a4807441c0c010040d070300070f5030b10a0185041000b038015510388041683c41859001c1d1504002e41c2c03a540800400d02c415040c030725055507845055070720f1002983c0c02c5580b0304d4003510b4040307030181c6803102d038500181c801001c4e1a12403c0a000a01c040c82d40406c11040ca0b52089690b41e0301c94495040c40303030540c892040c1960910044e40084000c110410520004603a02601c5007414003018400341800ea50b6403842a150a000c2080041d44204580d0b001d540c00142410885100b00c040d0b5840f1180e010804004580c150704c00c40230410103690402041001d0200380c00c0c0d070382c20645010304040441000c43c2c49039211341041441c1030400500c8166960081070a8201340083d8010303c850a00104001e640032402805280f000402c11401401110060072024008095003442604d44020320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111047473 1250 111046223 111046237
    0x70e06010f030c1407051b01020a03050a0e130e1006090c0504180207021203070b0702010204030c030312090b0703020a030e03033c150103050603150610030209040501030c0e09030f040b 81
    0x10080f040040c0c44c134110168064015244a500100381130949416404065001003490904651180281c0c8001952000540b2941b06007400d0900d5210300c401d0004601100710a41c0106a030315240183c03d02110000d0310560010355148100305030390315100d480b030a4400e912250b0f0003040f03081100f0441e40744115610300102880f0640142800903680c001448500c01d401580d03050b03803020030481d092215200d45c407900501c060000314545032860f5552007418032580300140c00d00031005a01548001300e40c00c0001190b0f0321901c03010041c500303007402900a40102d01c40d0300009141ca000b10248040020071030780114204424000c0310725030264003d00e1102d101c40c03882c004103a0410000c2041c030455041718050500207600105031010940010300f16100108000e01c41d5010041c0c01d481c912418520769040b600a480d1140c2c000000075060f40644510004140c015280c04000410302100480341c00c103807070748800291055181c1860303440d07a0b03000d4201528140c0c0810401003004126502c000d004c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111048723 1250 111047473 111047477
    0x3240f1e03060204030f0201080a0618110c01050901061d04050c040e1509030301051201150b0d09020d050607020d05040f1401030b03010222060903150c0e03190302070e06010f030c 79
    0x841a1a0355500b01641c00952003110074103049403c9804540e041010350344d00c541c000b44100001480d091101218460507040440c031195694813200c1d4124400040b00ea210b901d420080c00a410400d85560080003d841013a01c0b203d10850518040312507401c0e464015074024004104000aa0080100070440c48030240c64511813044610141ca40e8040d102d0702c5036501e10080e582380c0d0715200520648000b0040601000e034582001c0c0803882c203c0c8400c0d142aa900c0c2c7c0c08042d10351059201c038200a100218020354014050000c10341040740c0083d5583c86004103500352641c810303203088240c90394066800f800800040c800018000403c02c946a00c00c4400145008141611900082822030340658500d10030011542503000c0c03441c841d501180020010303071814140180c44c40c0c0303c040e20000c5221200c07503c1e64039140042c0142d4850b111488540c20024203803000840030040181e0b140a50300720403405070040c044002000c524504202d0b01c03824042e11400c10f44200200200c006040c00d07040001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111049973 1250 111048723 111048779
    0x3040e09070f0603050703050c1903050c041e140306010302030618120406020d03140705070f1103030a0c0606050901120b0403020f0111040602010f0203040215070f0f0303240f 77
    0x2944055040c1c1c0c82d0010103d50b14009424104805d000301039136401452844002c00801c100e5204072820b041d250f54041d09417600048588030608209101d108960100c0300980d400d40e03404082511103001c0004031a032100d203c8040c1d0002805054607240240f00180d4984c0090f80000c51041074000304c1d03079403081840140d80c000c0e811070340206416003290b001000146d10800415541940621030b2000784008018440f82a2615140090040c0309540c00105600743e190900d03030412540180070003843e6001801d681e1900c0f808031004010419801c1c090f079015050010000721400d04001150584065003600f8071110069120720710304c3d09001e0300481c11407242d114001e0384010284603100300c0c14202c214081e0355500d0102d0003801c0d119040071003000b80f0702c10070a01005035188000520700c150180c812039102c02103810000444820b4000140983c40c00c180900c04065260340f0800000c808104016054100b8103400068810343d4040c0002d0202c4209013480701110310000003009400c403180c0b00b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111051223 1250 111049973 111049979
    0x40b0d0e0a12020d020708060612030f040306050403080112050a02040207081216110c06040510090e10090c030b03100e0a020a09090b1f0b0d0b091005040b0f0303040e0907 75
    0x686003800300003080e114401100b2031003400b154148504000b4503020b200804006007492000d03511843e01801c1d0320720404100707403d011825403d006440704808011401521070f50f50781000c0c00178000480303044002896940001c60f60a071442d901825050300b240c01042041c4046d4244002940030007026100e41600703200310381120100e40405232003109000700100f0a031500220140030b035040e035400050941c0020600c00000d45408055070101c2e4800c442010702c88400c00000e8401c20000e40040c60b00142940c1044122801d60210328203d444c5007800304000320206504030120f4002000301507044d040700b0b06000035100c494011080340b04005003600d00010140d0b00182148000e94803580e1031580360701928050207184d184886d4042c000103080c02c003401500079042c0c0e4500950007030000242000c11306040745c41c1107502c0b01c1d00340031001d48482a1401c00c08009641c4170218425207100d1341c10040e40701c81a040440241d020f8150241c015420a42020441c01d003180c0003c1220361b0a1040581c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111052473 1250 111051223 111051251
    0x70b04061a0409050d140c060c0d06180c0219030806012d020609010606030b060a080910020304152906090f0d080307030b0d0c09150810020408071a040b0d 68
    0x82d680c118840d200400317642c0090a000f030b04404811010465000741801201008a004101203500c80c4c440d02100d60341d8120215440000c0032a5001822401030490220b0300e0520030f039028141e152155002c440c032141c0c0d218552070314810b541500400044803a070100c2c101d035010f041c041c00d0996140104100d858001541c030b4862411054410006a0001e028000718420a210301c02c0034145500d0144014640c050201d41c0f10311810b81d86070100201c1d000024200170050003080071014100000703540d0307800c00e4102101008145c0c111210818030b09040c0c40c000d598510382420000d90b94414030400c0740342010070460280c112509650304010b0751010318206030740b40f440b030051591051004680f2410b0074000102101d0141c0350300c902401100c0007100201d0300c0c07520400304603000ca250102c0c910601201c0c2c10780350075107644100c0d9148076090f501d04034000a0340203402550751030030441e18081d03a508110342c1440301c03000e030303d103052901000300b800b10f03140100040940100c2c949010404081600503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111053723 1250 111052473 111052481
    0xa12060b0d060905090c0102030405060706060e011221020c0d03170a090b0c210702010e0f1b15040b03130f15050a02030708060f0f131b0203070b04061a04 68
    0x3084480740d5448000f400303801ea1901c02d0a402103454002030801d1030382d500001c1e50707e108501440b0b10401d808105001004000e400c407901400b40310806071501d50351075194056120811000b182e030700301e0071001c0e8a02450f041e460740813408400c1d40140700c0300d18520284120b01d100c0d40c0081c0c04210340d040359250002e402c0d0356000d0080740300741d5001a03162814109002ca0190113800070429a20401080c0320581003187c1c00c0c00b4501c05141651401d03190300005130b00401c1003181042e854052461001c909000109155105841211640000c0c81e11a0100025045000c603000084981440144416000000919805003400c1225103002d11640c40c0d030541c40b914601d0450307010500030040801c0c60780a000e00ca0700031003420170a6085040c0400003a110342002881e85006021441c90054aa5241c03045401410000303081c5100054949010401404401092416011180e101c8041c0103200100300c1c1c00c0f103038003d480c100083c0c81d2641d40802030562881803054040c0c200d41d0790b2000340d070340c1c1c81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111054973 1250 111053723 111053737
    0x10309021e01171f05010507030203040902030a020c06090604020307060306030510020708040512031c0504021c03030209040c1701060203070317130602161a06060403032601080d120c050a12060b 85
    0x16002803030701c42090420b0404130301500454100481032000200080d00042500c082d18110a40581c4a948503110200240100300c0039890900c110810300420184c00b180183c0200d00039003c2c1c548441e10303a0415400d0380c82c0381c80000e0040d40142a481d080c1e44041e4090414036200d291228940741e071301c2002580c0c4035083381d19031010b43c100003410f60720540e21a1011000400307421050001e0700c2d2a400140740240c05002080003100f00205040c10180300c1d50403609540da004008000e424400da900403d1a8208110014100411000826020300000a03102c034540d06a903034415403641002c0511501d100070740040c2500b00c003d03407800002402400074041039114207075040904181c45c1040344140c0c03240c00c1d000701d0480071801400415180d00b004c41d4107490301030a1081131159411214400000d01520404c9640090800410700c4030740440e04c0e910660703c0b81d50780b01c4030250364000700044451614110001c03035000c015802072a8042e0090300b06640c038a100c00650b03542d0759011100780380d0101c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111056223 1250 111054973 111054991
    0xa0504090302070e07030b090403030f09082a01020f0f0c01060b07120815010e010509010203130801090c140604060f02100905010606120b0906060702151602040506010309021e0117 79
    0x42070a02c0311310901507165520a00b5480c007401072402d140080b410307204c00a0301c00340805071140070740c0048500641020000e00c1c0d00c510810b40e0342018154482403a600b803111040c1012010740e014030301a1050096990082c055030300c40f464040d8410517603480d688050240b804554945400240c29460080034001203406a03c1000c01501940c2d8001c000b08030040c030b0343d0024842d041800300e45982c06500888082002c1c203050766110500303c0180d155001c0e48541034000c0f00066804125848190043c40226201d0148651082d032160f820700b00d03003d40c1c0303608143c0082042c042003282c607104c2c8a001d84080d403103005032141d00b0124080c48068803102601521345030746884041080e5944600ca1214440101d0402c0104100400c0081c00250000e01840c0c400c000100380b28041d0340d500e80c04074100c0c107200d000072aaa4030044807642810b00240d40180e20840c0380c10000780c00d0354024020500405e5000703003503207228a0190020071801c0c0c401d2929a0401024a420081d010a8040b48501030880c1d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111057473 1250 111056223 111056233
    0x8090402031009020a05070c050418080c150a0b090601050a05030a0f09050d080403020705031912090f090e0c1c0b07030e1005041104140a050606091e040b10090303030207020a0504090302 82
    0x9808c00d107445480345d50085001d2761511107107841010244052074074003a481010070356540507503143c0f03900d0001101848200c00c8a031505115454005611002c9004c0040e609025071341d0f079800042d1001c0c0640f0078044042001003001664005460f8007520f11000c1110b070009106d041c80e21410701e411111003440c13000c80c203d030307080c80140b540401500d401820120010940c3d150903443d2043c4030004180010845109090360341038250140302d600700540b0480121021b026641c0d0101000b50049824100803402250a121020700f01101d40882c020060382190043c082184c0e1011213403e4000c6c254020140d41d60041d103401c00c0d05201c02c01c1c0399462400003040d1030916060482d540101012003a2056280c400156900c98050904981c8060f07003007000603c030f0707591001184052107610041380e07101d0031100001c0c0840e001141d90302041c48065070100154190071080c0030070040100c04200204901502c1040001c0c825001041540d10103485a07030210303030782c0700454203541c000c220850250b081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111058723 1250 111057473 111057487
    0x15080732030a0b030f2d031c1407141c1104050306090609061f0b030c042d05060f0706020406020106150509011e0c150606021908090402031009020a05 66
    0xe0b0180c3c8090300d908402070641d044480d01c886989910981042c4039540130605580014107901c83c00400210988041d6a56801c01035000c003055a0611800602149003044204501d2000e0068600c145116128440c043c89400c65011554110b5080d140c1e1300032048070080c45141e070718003858070642102c80c00c1c5500c1c0c0d800c3c10101414914002c2103500907910000420001b10000981c941d040440380e100342100b0300080313801c0141010756401110b60310000009002408007403c0090040741d031041d420206001107000140d8284006052101942c58901828012827030201300900d0f030300e1000510303140b40030322544e43c40050b0f0304a86d0014016035518501041444400e4907145d118881500e88207181290000000e00844000f40c05064080500f000040c05540207043c50034000344c001e0840c20741085002c0594000d8905401000018000c4240713944070020042c290006260340525441d00381011402884000c0d0002044428450101007000500032001d100030031141c40140d581c6a96001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111059973 1250 111058723 111058741
    0x10905150d1103070909080405040b240703110d0207181e0c0206130c210f0b0103020a09060308040b070501090803010801060524090108070201020c0d02070905011508073203 76
    0x42c02d0f03005115542c00d090b1181b0004800c907045900b50b540c1120005030f80b260003404a0000000d200f04603103810307a42c842d98510300071401c02030802c00e44079594984003100c1c05007440762104034107098040582d103c940140012102c419180b1540700551200003134091403403e421f41038449001107110500e0341d501101200d01d41c10f1101542c4608007001c2c00031241c0c03c50303541f8000e0300d005118055a407010002d43d02c4110b90204007a40816410214040c80c101d000d04000c00e0403c020f21040f4494101d14500142c04105801080e0460340c200c0307480d9050500d0078558020503408a03000f202c0a5584400c0c001c0080c070031001840c041c1001c0400000d60900345030910000d420018800e03008002d00b0318481d0500d501c0202120200b800a107001e002d00c0e00c0c1e20030140e0284c0180a6200d24034024809000015076000610b1400c98100c03e80510499a03943c840c154003204940d8032038005112640014541401103e4900c0011310304c0c50301d1490210404075814123880b10010261003d02c1c00014045002c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111061223 1250 111059973 111059983
    0xc12031b08071b0b150607050a030c06090f120906030b0102031e0f0408100b01021b01030207030c02090a090b060d0519080c07060e030f1506010c02120a0503070b0f060108010905150d1103 82
    0x70941d091703450070b456030f01e0f0355640309d5a011004003008034080e2403204201454000c83e4090741d01c240b0881e1207004503d440003602c6040300d0a0000116514400607a040c480d01844450700c8068000e07501d090103c0b080d40550f44c101e0a0700711654501001040e200035010b0380244000c280304c0f4050501884180381c03180503943c803002d07410f0441d44280d510301040d82c04440e01c0a45000242070040e641c251500d0259488201d45074081c1d84901c14204214642c1c0458001c00e54443c41740c141803005540308420050000d641c200041c04691245600c5031100d500700d002a41c4041c06a900d441c108070400c12a0f0317240c0712503500800000755580001c00d0b22421b0400030b0010f0b1202c441c0c0507200007010011812400c0300d0007804141042141703d400300c10340d2910800c0c1201850001c2c1902c01000d61810082d949074030101040354010240d100103074411603440c500d1401200141c2d2803003080d9113400041d2000d080e01512800c901d00310303401c0143c00d0303560713696592000510511a20248500ca0302c1054144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111062473 1250 111061223 111061261
    0x402270316030203032b060e190e070302090601050f0a03201819051206010302010e09040803060d0309080f060f01080f070b1e0a0c12031b08071b0b 65
    0x70014103081800180d601009413500c6428201e201029a0301101041090341514070f080b0f858203107004d80c041400c070041b0792010300c41c81d090003d49041104001c14402144c000801d071000c280c201d07102c18401071405020845e0001c1051520a080090070400750b0403503400101d507040440d40e1034002c202b9419580d10842e40c080c0125100c1400d0061390400e4980c40704040024600c10250403d212045000d9201c4c600050440030b020407540d010403018090b5030700701c280420f9000c2501c000e40300c0725034504910468070540c1d00c5003541b8116203401c418440e141040d03040c11002d01c100c0d248082032255080001444051001c0c00a00389818079208460b941181a0050f81c2caa8202c4507012000580001e5284100d80c0241c0c1e030301b980c98641c00c11a0207511194080f018020300000780c420b82032a8440110441c41e40244a02031103408400410350495960a540000c80803c000309401094010700216500ca0120b0400306100701000c10700702400441030300304440884003101400080703000b10300345405c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111063723 1250 111062473 111062503
    0xd0203060a121a040302030d0608100f060b0a08100905070e0f0a052202120106180602010605010c0b09100204091422080705030f0409230105060d0b04022703 69
    0x155000e0f840e40c42e2003c10214003075580c1448880450109482007049900c40341820a007000420349542c5a1610f410205000440060a14017841d841000703501c59002160310240d070491806203c4002a501b0507001017181c1048003c20000059000c554021941700704015070711112004008410010702c2c0c143c3c510928002c0980413400d03c82c070b480d46500081c018141c507604141e141c41c0400002d02030720a6003628418070f09800000a44140c100e0301c110301c4907007040600d200403602c4034012400c940c46441498001441e244c100008140002500382d0071000841c00c0d20000209103410780f05a910a42c003041582ea603481546c198030040800080d08505e00000e108044503040385c00380c0c01040f483c1c41c0a825048001080c1d410044100308862400300a850425102d0f6555a4102d00030f068210b43e2110f105540070380c810140e50b250b207245040c5c0e82c0081515041c8409140b04200400411010980007542002800000300c840c882c2041008001c0c1031581d14a03283c0d805050170040742000101d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111064973 1250 111063723 111063749
    0x912170703050f012115050f01120b06060a050903061906050303030910020309030c07030c06030f0b03100e010b040504060207051e03120a060e040302011b051809040302030702060d0203060a 83
    0x4840e04002d41c007141145e0403d20320203034014482070881e0501a00e420010f00b0400c020441c1e00ea41c0382650845ea10a000003620b0400710f13039858103014101327400c845e0010420900e2000060703c62628401501c500002450000c1c204011032011038131340030301500d43c180c100001c0c05d00c1e00c0b05500030f07004100281a0941c091819030a1140503185d075510780140d00e6541503004400203011090030015100440c014008650516030340e8107125004414500070300c40060708124044008044500a2440c2c0450103401094025070306100c05004080080c0290708554940800d03142c10364803030207054017075030280b103005030399444600c0c00a10f44168aa2403060b007039110183d4004d8410080151802d0040c0030b2507090f2640d80d40324196008102c150001110030f058803051009065055000203a0107440300c984480522410500740c4840c02528135400c0d005030310103010629418041d030001e81040c481d0040b03d003000c540d81d0003d9072030f8101050304c0b003405901104024036840e00c10f15420003080000d41580e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111066223 1250 111064973 111064981
    0x19050703021e030604020903060c0d050f0402030a260427050403080a02070f0204090f030e01020601081002071104020324010f0c020603040f02030319080f0f010315091217070305 78
    0x140c03611000289051030b18002c800180d0b40e4460b50121400c43e4401016035070280f07040340910807241c0141e07240014003480e00000402174002803500c0fa003e183c008004cc4031816680c2d440c120080a103120200310b1114000f09118103d4910303000c0c00151103465507208002080302c4030501c10640c0b0480b6844400d060000340b1021079009014117810108044015a40b8030007401e10b00d4191440b03030030003500585010213079028049460001860750b44640c0d1014a0355008400484c3d44420138050862141c001c0d86c101201c0021607030040403000e129031600e041602c0c240c0002412600708540d5002203240c2d403501c114a07410300b04120311078540c090030055101c0c15000f8004007003048106000340074900000105003440340b042c0e10092180d03801011a962a2005204041d07a440c840b110380c0e003c203800801043c00003440b0100c05200e0000d05d4045981d0f40e00c3d5845003200034010461100c0f406964841c0140070482d0724018144c0003100c0e031510071070684010074180701d28070020961010149071000344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111067473 1250 111066223 111066247
    0x300130120f02011107030801140910060c050a050109080c0715050711030307060c030204140603010b070204090c1206090c05040e0a0201030c050f040e01080601050108070509040911091905070302 85
    0x34648910091404070980440620240d004181540c0c0c010314424001c907204080552126410703042e64109585050001a00c1b428050b068000396010203650b00109004d0110a114140b610301c0c1900a004a40700ca450a860703ca003181d0700d0607415220204001496a0383c020108014402080e4009000b120f100d500c001c01031060140900041840c1106043c00c1c40c0341d68100242c6481541002c01013044c3e201401c4050000e49c030610901c1c40f40507222840b40264a40102036038101d5664082c01460402c550b820000103111090044513010030000001c81c01d002d1002d00c285407184250b0001907502d50f0303401c2c60b092501e4140d000e03a10407030a0000403051a1000705413803007015030a0070b021880d40e60980e02950940110100b10b480340c1c40101700001c01c83e100c0303d49641260b1446060f25443d0343c86400444000408455106c042201001164840c0c00c0582c00310204501415800700346a280c8800101540d006848580c807198408070100d415224500c217098100707405060441c035103a032603164 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111068723 1250 111067473 111067493
    0x105190e0103020d0804150807020f030903190c12060207050601120221010b060703050d0608010203101202150d090501050708071202131d07140708300130 68
    0x340580b130042d16810403c1540000e44020300782e404c0e0034403039140700306400800d0124212890b40041c49200e10b0b4502c4004080101c2e00d0010020b00034054812044400d1800314429102c102c82d8070070800000034000d01103068515070684141c4001d642e5001c60308025280180c10703003141015904060343d03a40180c0e2403061301c1d603030121031400d851158104000458010083d10f40996041030b80041e000c0c0070954081c00801e10b00f004102c0800620f6115903a003401c0b408215607459840802c0d1500f440000d08529100c40724170300c000d1601d03021070015000c00c0c0c80703034112211420320a40c0f94a0f19208010702801501e904c495036141100c511b241260380248a002140000c020203139000661100c244820110325000d04080c240704002100200400141d100c0c0480c0c51900003108191030440e040301500440342600d4001000d503041c9010200142e9103c2140c0b1007401222400007841c0900c1388950311035a000b81450090805070700420300c2c48810005071059200d0711040081c400394009201580c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111069973 1250 111068723 111068729
    0x160509070512060406030c0626060603180a0204060f092003161403180d090518150910050a060c050303010e0414010203010e010609090e1b0d1403030105190e01 70
    0x1611842c0e4580c04041001458503800203032082c0c210358004200c040d00914041107081e00024a07800c008612000100405415680e6560000c0100702040c03c41007054420181d054a4000340d4032000c00303550002d803c17210715910442001092100800462005124403000c883c00014221040700040340c42100074480288800050310313480950208141c800d02603688400812a9944d83e00e040c8004108049035480200206a100e615200e09030640324004001c200c40f805020035452200000c1a900c6d0000000d103c81401d01800d01e100c00255941038526014080b0000801003840c2880280280f00c0b203203400180600200180b00c4000030701c0081240e046546176251640140c480c0e180918041c540410407502d10741c004400816030907070319020541200c01a845038018666200e08240940d00001c1007d00c1c2c0b82c10800901c3d2a00055608042d50403030018805403c440b00340c2d87d10104007a410200d10b855510210061050782403e80c4800c0381c100c099100b41030200d01d00403e480e45079034140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111071223 1250 111069973 111069997
    0x50705011215030609050c03070806270a03030f060906030305040e070e10030b0126150303091909051003020d140114070c21020d0503060d0b0103051605090705 70
    0x201220035290419071040302041010149146880d0f500d041c80005880c64810564081c040d40d422009030f4600000c14200304c0d0309000140102e07541c1e1f400b0301041c0046003c40d55281c035a043e44101c06c103a00510004103d03070710031b8034000b89000e4031716185821030702c65401c401c43d4a4607040003032010079000b0781903030700700d0701440038003900d40d680c18108071070801c04562001c3d0404034044440ea1074942641100102d58000e9071110401005418925038010081d0740002ca4500d5039400705034041300c1144484286c1034054200c0e440d1208013808940c204030715000714182401e0401c001d010383c803954054150046802e0032943d40d50341c19034001504a50b03419a0061a404c4501340c2840340e03182c20b4003c1c0c110b000740114403258a28100101510401c0c0c4071130b08480c08000d102c460214140d003801c100605151725030003000030101400080d1926031010300b00039031024610035558002a00443d6040c00380d84101c014200b01a00028002100c508075040b8621403105e4500308000150710030301b5280d00c41d001c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111072473 1250 111071223 111071237
    0xa11010b0d0816050a0c03060513030806040c0e131409060c0a390203100e1903091205010b090c040b0f0703030b0307031115070c0e090709050a06051302030405070501 73
    0x1c1407041e02c042c0c5041c2001802c4d8040c1441050500c140b0200e41c0e0100c900840f410b211a40d0741c2c0f80d5030030700c000c06040c0041c0441c2141c00410214145503000341030308456403c00f10324007102d080000e00304280f454185060180c58284284040d0704007099103800030100002041d040c10a00114000d40c0074031540340081041c9502c5039419007106442210944a107103500e80000701d107101e1108030f82d02440070184c0c0240714a00300e20100f031001e1300c100c01034901d484018100e14509040e551044020352031b800d60403c00c03050404501215018400445c0a10980c000213941511800380418614020705134068040705100410010b035100c4102d503203000c04411002c1d03880d005464150700a005081d45240c2610071080c02104000141c40c001e10915011544910300d004540035034265441207104c010302106443d501004901c440b400e6154001e000072040d03d15040c0c4442c41c420480d0012600940f0203034540c08104203506050310f0301440005290419895840c294680e03d5881d1040e1041604000403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111073723 1250 111072473 111072487
    0x1030e031303081206030a0b01090f0902031f060608010608010e0601030f0c0909050c070c030b180a0b040b0109020304051902040209060d0605040e0f10050a200a11010b0d08 76
    0x400d004a91640c940ca501c41c0840989a00341014a07421150b05111800d160401041d400e160001d8400c42c0d865009810f41c03040d03803c0c0b100c0d000280441c40f0441043c3c0340c8480030780d00165024403914040120900d101290380744001402000e6984541c00070044c000381c0001032205680c41001141540e00c1141c441c00540c407903200484c018403254944d1050680b909072180da442d0750150281044449000c403d010f01e841d0144000c04602c0703100c8005101c00900242000041c0040d801c0c04d500c8101d420000ca141c01541e2003280c100307503159004464400003041008200080c07040054050941e04100314118036080e50349540c3c0300c060403a14001c0740d40c140080002c43d0303941e80480d119000003034446c54551929085480c058001030050910407030900540250300d074000140c000790951000001c2034126842c0d000d031350040034007030700748450740c0d8890323009003000c0311000c0c880340d1344030316440741c0c13543c3c1d8030440c1002030000c0344080b0704075040e03414a141c0007515618004070111807600f14201d1030b65204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111074973 1250 111073723 111073751
    0xc0a0b06030a080a03050403090603020a050904240e04031116050d02031e030d0b0301090314070c05100503010501030524010e060712050c120306031522140d0c02060301050103 77
    0x181c0c02d0000b45841e00019a150072140d0503040680154420384440d9921610345000b41c0a9010783d000040c0004c5061180382038034078103500800007940c80c1382030140c48241800010a000c031040d0b08400e00c00b003840e500b40000c05501a10340f00c0b0b4441d2280140c4003106c807150040c420980603100e030300d00c41c0000729914400d555051000d4040c1c2c280318044a42ca24120382c0201c7e450b0340094203e8090545030804911103800c1c180109205140c2c9960f40240410074101c0706000c40c2c215000542c0d00540c8080041102d440d4500c010303041c480c458980503205d6142100040a0301c80090008540d80c003480050040d00c0c035800d0b4042c2921000742062240d42d940035001c1805405200d40140144c0e054031030800045820400820903640c84400303a40c6500c500c142e85202a1005845983e016484072003626600c146075040c0c2500301c4000900129400441060800c00070264034081d2846c000422011144c7c40003081074502d025158109020000c1490300040d426000502c1242d05044d203951072602204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111076223 1250 111074973 111074983
    0x509100203121501090b120c2203050114070302070b180a0203030d090506060102070803030a0b0f0d030e040f060315020c010204031b030203070b09061e0c100905060c0c0a0b0603 78
    0x9000b020141c0b0107803609800c480341c03907081e0501407030105070400408550f10307210710308590700301144140e1540b682d00ca13082d03a40340c40d41c419030491514051044c0ea240044501c40c80340e5000707601403000803400740b03020b04071100c4485001e1306046c2450310420810700084e0500d00031a50020400320202146c81c006200c550a001d40c84000940c0760100040480541d9626070207d01c09d0b6028004a81e1305a031a1001681d44032014000c904180c1d105000244007804203402080401c20040c120202800d10100492959042c0d40d00440224032031031480b000b6410144500710b01200242800d20500f86140c440b0089400b007035000204298000039580d001481c01d4040780c00455105030100070480101881d200d50f030410b400100d10a000e501c0780064200c031f00c60140c400c00c00c80241f00b03d207000080d5184500000c0d1400100d40400c800340b2500c0820300c000c1c4a0300c0c05550b0002c1c3c0c00708003600c3e60326055041800c028443d00d107038a020f000c003411410000884e040d10300d03030248089215403128400a8601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111077473 1250 111076223 111076237
    0x70503071706040b060408031b010b09160c08070302030a020d0e010e04020310030c03050303010315090209010b03040c08070f090608070f030f05010b0310020a02010b0907140a170a020a0216060509100203 89
    0x44240006c000600300d00c00001046c2551f00c1c2c2c4812000402500c080070300340c44440784495481060400810b05c80b16031f5182c0014081224284600714145968600f58a13400c0150140c0160300003083c4d072003000340c041c404c1c084c0c18045c504d02a4a071b84224000030b0901c002c0307003101601695020000881d41040e094200d00515049203400c0180c82d520b01c2d0403a940c0c1d00902084900700e0801c40500d10303c200ba03004020569130b00034000117090b070a10309100f210b138000501c140c5541e8038811001504043c02e020100c0581102c0041c081458100180002a1801940038040306c5d40802c80400803000f00007001c0041d2030b4041c40303034064210300e402c02c9070141510004035641401142200c441401d810750040120702081c1d0001d0140780380380c0c000c000081108840c0e84001c20320340c0c03504001000388035008045a080d40c0c00c0c0403203190f6a600d18550101c0049420146541e800501450a80d40410203800c81d0701840702942090b81c1000740c0200309000f611106030084581000b03818081c0c2c001e10a841207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111078723 1250 111077473 111077479
    0xa0c050f0c010504020a0e1e1513050718031a0403051306050405010806100c020f040e160e090303010f0902130902120610050406080f040218010b03040b070503071706040b 75
    0x484000101076030080c001950f04a12803402810f0001c0e4002c4844401e40c41105104e5103100c003061a401c3d000902d007001000c10483c15040d010203002c40d601c0780b480c1d007120781c0c5c0840c00003036614010f5000b030030310921602d0506815040741c0003080000e03041540010101c54002c0703030307000684407032905540d07034000d450110340400564007001c15030a9210024004640c400d98070002e03c2c1c0c90b88004c1c00f40301c0d02882d400400142c0343c624108058203144406030103461000d00002a540c004040d198241302c901110b400c0201d960440400403981d038a41c0030b68228600c00d02444c60355140c019000107a407001d21440e2a01c0c0d40100341040c500c7c031442e49000042141190a5507540d030041e10321710a4100840710140f084005034281e1a0951240d0251002e81304a0344812100d84c854144031414401c000700100d90102d0b40d0340034980c00c60300f1020245e0080c000c00c103001e0f4aa0500c1c0c40c11980805004000f074080140c24010000001e6000030188442988060f6018940d100e220120300602a00152a50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111079973 1250 111078723 111078727
    0xc0503030f0702011b08060d150216050607020102090306070c230d18050d0f0606050a171902220f02210109060e040b0903090310230601080a0c050f 65
    0x100522020005510801950f0300030001d184a089194145000480410b000900d000340055107038102414185071060107942026010486001988140d07809040c03c0e001d5580d81c01c0c440d0007084400c005050b080303035450000f54104241d80011a565043c010048c0b010405400900024480104c107840c040f0050a1441c484030068148501e5550f0604418000010540d00c40001941e00c21461202a146e00500d0060b440c010360b02d0761440e156580f0429510940d4030300d40000e0a40d01c0780d44081c01441d80031081021910342121440c00e24102c8015040340424802c4804016070701e5040d00c10983e00300000d10000051401421001049041c192000031480040c0090609403010000301140030203420080e40c036030702c500300c06050703404178860900243d2140300410700107050614896408003a400c110f90400303000d180000c1c03138441403503211629a596034010052003406820419510400e110303944429007032010001703240440c0100418034041d52a498203042e540718104481484031002d108607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111081223 1250 111079973 111079981
    0xc060903030509150408030a020c0709020a0801060908030a050712021006060806030f011a0d1a0c0306040f090209162007091b020a030e130911010806030307080306100c050303 77
    0x60014081516032000c00e01c144d86000c00080308001c0c00c1c51207154413034601400c58407441100c00280d00609001c007014041c0541c04103180d0040e10140c010501e44da1750b40d501c95450700340c01038a2043c064010000b141c004210001200d90000d044840c0e20340e0204203456081409982281003050680035120361342d040400001d6555400440580140804c400740c0d101014a01d004c20300b2070b0404480382c000c00103800c3c41354170359150100b91841804d002e1001d0207a010b081c1003001211840480b0046442040032041c00610308140c401c0c4420b042c880b240800644030309400103a81031000406038246046940356140b4614411025107841c2c0c0d840901c2140c2c00c01d002c803402600c80d0301c0d500402001c5032a10005003c4500c240d1001c0d020340180b500036204800241d00c088900540329001d10b50010f00810b60012140c0403846460202400341c5824017850507031800041500001a150134469881030107201c0119000004a81d00420211a00034140d0444a0b081e6110300e4103134006019400080100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111082473 1250 111081223 111081227
    0x904020d0c112b050f0c0105011401030c17040c090c0c0213050c1207030612050f0d050a09090504110904030203030406180305030a20130f05040203010b03160c060903 73
    0x288400c0c005460b850642d100e0311025969842407036860103107540510a8801044810006811511a842c0380581c03502e0858140d0f41c5241d80008000705060790b445004004480003890340c003400440901e000c1c4121400c510f00108018441469141c840da00301012904100017030003401d0040515501c00e005049410748050b0241103600804d9000e02a0700b10170569901c05445840c3c0b00d907550243e0f1a0034040400750700703008044010140c1c02810781c0c0b000e0200d041c540300901d41e440a84182c0040c407181d03c599a20500f415844119007043c880103001c0c0500c8190031068210a07114103540002c1c0a50343d900703001a050402008440d04807423840240018942e0100c02140310758040c8000384002c160f80382040042100e20300000d4001340b02417020850015168000c19039041c0d00d12a0400701c0c10040b210074800e90701c1160030b14004042100104100c00321040c0741c0000f03081c100d81c11400d541c03610565510900c001045030054410015030114070a00581d041c5880c0798000c1402c010425540c41c1c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111083723 1250 111082473 111082481
    0x1050901090c08070803040b0a050c010525081611010906050106180e1501030203060f0a080102130608060d0f0f0b010b0715051303140c06100f0f030503040e06060904020d 75
    0x4142c80400d4418004a04204001000c2c4120f80301e200046141901d0121185880d401000549042000070811500c890801f402000c1c02403d5200000c410404601d4001c524503200c0d884203410307c0700440130032070746004100651100c01c50a0810b0a10410000d015500414120b034000b412140342000101d10f0030b034001c4181401c50041c0d8a00300d5219190841c20300b40f2281119043d00809040c5140c0801354031079005160014006000c0c200360b1b1a5000c000303a50a43c00350041741d0301303a50100341c0f03441080007111000000c0840341080121800c100011440a0420381d01c05890b4090181d914401c119102c40310b070003101e4008005164950f1200d00e258a9540004429511140c2042c62000916503900c5030a020300700d500045400c0c404255001d96881c03003581c1e0100380036001404101d00c10602801102d109240d505a11182d0754180300c1400d062901d03581051001100c19002840000c50000407a0292420030b00c00c43c0d4640d454034001146446100c0e2000e130854004140700342c0c2643c180e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111084973 1250 111083723 111083741
    0xe0403031d0303010504090c090f14060a0302130207051f020c0d050909041704080a050a0c08060702030301181b051e0c07090b1302040617070212040b0a1101050901 72
    0x14080c800d181594244210460041e00540e4094204100400140c98240c0c0700c070310381c0d40c801c607071041105640f01084000c0380e500b0b04ca0f04503500d4450300f04102410307022010030761180080350318002890650b004202d80f5260814450b4500c1e83c00a03019041c480300f080181010203040021044001050364140041d40040603040080c2c410550743e6071446028030161501c0c407102400d502c03110764442c1c032460151480080fa080d07a07000300b0000854400e400b40502ca9840380958020052000c00e8a071003407441519074082080368112909003d041d950100460341111130b404110700c00e04c1d00c84004100205007400e102041040d1801145940c40d4201000e400c01506052588004040c03100302d828040c800c50100d0a1030341c1001c0c0c0d0070300ca2620160300920741c1d03c50240401414580d0002d94074226805900030001103183c0550070301c402001640f005500c61940c2c4060b000f06840000c100503175006a0280340704c9031074045000741d40d441c464142038241c0c03070100700207020381d0a003000c0d0b0a00806101c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111086223 1250 111084973 111084977
    0x2030c010c080c090d11030102040b070203120313150b03030403060501090e012d0b090f1605070305040608090309040c12060803040f051c05010203040503090f0d030e01080601180e0403 81
    0x240304459032034019503040d8843c0d011040b4980c508028902004010340540c007048604801c01400502c1d2500c00b4800742010b04051654030b0f40e80d0480340105440c02c0701c0989807401c1d050040042008503500d043c41e840e10990311040d1500200b8400f20000003906c41c18014a170148004907001041c8805a00090f048818100b000c0002095140c1101c0c2030362118920710b103031001400030008220030f035181c101c10464090300000803800411070018544103410744203142c55078011000d01c40540000724032400f03480120700742a440c0080f13590380501107000354461482441110340000d5484030f4240f048942d10807000f00104248480d8a9026041d00c130031a8810301442c1c41c14101141c01d4100008403420b440c55000140c9525141c038080101c1111074444503c602d512074940400000c00900155000301d1054024580712003030003003400f403014140d00500d4416100f180386100441e4004500340d0042a0a281c201e2996a8040060f180a8503d44481c0d0302d241c0540000555a0004500540124070035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111087473 1250 111086223 111086231
    0x60f0219020a21020709050408090a0501170402060310090903110717030316020f070305070302010810050d02010305090111040305010603021824031c02060a0e01060821120702030c01 80
    0x4804a0b03a403142c0303480003014281081d0300c200b18070603920b51500122020788122500951175010401c01d6034030503039080700d010b840411400c0003440c0c01242d440203420213180c0176031000c4260140074a1102c000c0c001900540001022490030f8801003810405491078034001e00c40c400091800500c0401d01821149941c01241004203012242e60005680d001da2600218110346035504a03102c0c50507900c88140541c070a2414003103003808140001d000441c02480079040c110b15600001d0318512009107030400103011840700340056950416a070f155560207180020301075403101c0344d990061004058040c1313442401700e000000c1040540058040c1e038400c0d902c04901c242c0c0344065180450f001d4030b400e100040c0718100c041c00c500140c4052900c1c1c0400804544a055801c4c0030711610382c940d07800c82c8006820003410405035500382d020f03074081c40c0ca1400080100e64174241e441521140119030000384090b4a0002c0c0031040c5036402515485541006130b0040d81c10701c00c00180d074a62000038881c90550030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111088723 1250 111087473 111087517
    0x70b100503061512012307020c0306190509100f0b0f03010e190c05060403031d030a02030c0123030a06051003050601020703080307020a0b090f070f180e0703060f02 72
    0x410b0290145198103254018039801608100001d0040540c644282d941d03950340e008010004840031240da00340070304442c4541803070203001342880300081480d80690f0041c030a1040c0b00305200101d40340040c900100086030340b905141c250401c005483c203120143d00305010009490201c5d4000d400031001194000d00c5180c11900749802c3c1c961030003010205070130101c0300d01001e42d07101c20f00f100c0303c9118110b924440c680790310004481e50004c1c1c00c20b50004181090f060b10a042d5140b251000311400c9009101c44001171b070000e50383d9803105805904100c507030b402d03044480301c3e98400d01c5a9018020b00d410786914201140714010904d41c13003018480c0800a0a00906a0091140c00e005050607809002c01c01e045883c4c00c0d04c503900260881d0b085100d4400344d4000305060142e40b07400751401e0f00280c1a040b20702c100843c500601138100c3c0d030544113100301c20013490b5081403c41d000120702c0c03400030900d034034072a528a007000d515920150109003000c0200720703c100f10354014002c45420380390550362456 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111089973 1250 111088723 111088729
    0x20309100315080123041a07020f1b09070507200103020915070501060f0e010306020f2503020f0f03090d0204060e100905010906030201050703080c0c0a030503040203060121141002070b1005 83
    0x821b83d0003034101090581c0000101d4201c0321031941c0320525004075581c0c403c0c01c4010301c3c50304410f224050b8102000304840380c800d141200401350000400c0c540035082c0071960300d9200035032402c41e9181d00d41d40c80d00c04c43c550060740070750142d4001e0a00184a0b50340400b01400d00c404560100001f121320b94602403001c02e6223803400041901743e40c1103c0e01c0c4001e50703003560744520017984401c01250b620301c414410304803507042414960004c58003004d5400e44008041c0f030064641254043c08001c983c20480404c4502e04c000004c3c0c0329440002ca0388854800658000301d401400b03142c0002e40002c0b0901e04111042800c01c2c080c008841e041c1404110580e40c60581c07104403210350000078009030003041002c02284c410101c06410074001d04019180048030240e8924041e10b200007140880c101004210a44c038052141e2401898815004208400b00c1034107140c034114a4000180072984482c1c48880c0000e040002810100c0e222030115501c0c10b090920000401e01251005645602010081143d007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111091223 1250 111089973 111090041
    0x507050c010c030c08030c120c0d0c050a0203092704051605030c010503041203060e0a0603060f09021012150f1403070b160615030b060a080d0203091003150801 70
    0x64069544807103c4c1c400f0381ea480050741c030150000000c10018016045030070042000e03a802090403000d40f540ea00100319045040e185150714440034003e060002501c0560007004451415004541c0d203094004036801199400d40c0d527400004000812004001c100600084c4a00141c2c014000440ca001e65500c1095642c0c18104e12840c0041c3c406c0c00071900089044455040e500103a0074040341c110707200c0e80e04075400c62080360300701501d40d1030700340c00c005001c410700c40c00803d10f04103882030100c1181074012400b5945c02d920a02c040007940f400314410019554062240c0c8045080c3c0c102ea11559281090b070004a58000c4400320320702070601420764500001d960303088600d0185120b0400d004070300f40000c0e101d0351741c0c0c017a11001c1e141c2d082d078454040c006a252002d0351043c640e5544509180c0148540c141164000140a40c042d91719270f04465000008d84461040888800c1110640c0c0d8408501401c0a581c1d0310044245100002c00c1d00101074200c940b284940401c0040d02885010040f0500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111092473 1250 111091223 111091247
    0xc08030403020d0b13050a03020d030b040504021c0813030308060a050108100b0f09041103180712060f18120f0e0603060f06040e01030f05060a0b0f011107080d0507050c01 75
    0x7116a8190a00c0010060800036505c400d175200401c0d60221541c44050604111110450041e00002c01d07400d03203d0340504c5207072410581980d08018903d070540c04541540360041c8150000780b6a01c600c41c0800411200b00c55041015420204810f5964900600410f00075121103209020040010546500c03480c0c0540c0305000c61003918000500d80740c4144c40551002c8140411031904201000446c3c8490041500300091010001e56a02c2c1200f07240c0161030b000300c200502600314010404c00205030b0b201892a007500000000741010781c0841f0a0010b050451070312641090303e008403814090001925007810811313854100341c50344046011030311041d01d031000301d030700c0a4184003081940c10400b1200001c0500a4903851a01e40c40d00180e01c0419030991084074041565050141000f40034004943c1240303001c01c003807019212602c0042c0c0840c051400450402804e00c8050080f00001c01c0320b04001c05c07400c0140c030714500305440010481d90127804181d845c3c0c400c1418031441c40d441200a5054 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111093723 1250 111092473 111092479
    0x10e040c0e0d020604081204091805070e0c07020d030509030d0504050a030f060609020c07031a0709120c0f060c0302060f090316080c030d0e010e070609050f0a0806070c0c0803040302 80
    0x840c18001c041120041e032080c070607a0060028000804d021300300b08528104071861840b4141c4a07841d20103d8000d40703076401200800420588041c0d400140e0000b611030540c6c7c820f0009840e50350344d882000c0c50b039000721040a503000505001304d06c20306400100038500b40304281e0903038a504400b00c5003502c1c0e41c45284101c94100140c09010004508070031001c2a060344030b0100419942d940f98600c00c00c1c0c0e04070f01c4081c2d0264210500030000c105a030200c4010000030b200c60070b403107441c103107001803d41641d0b482800310810555942000b000700b10f01e51600035050240b14114043d0711028000c00b1110300290850161003090302056114020011a070300c6410329100861400d000b0b20a103060300318202400f1150a01c0c14400c6820304030061001c1c00800c0002c500008901103240303402801d4444203240b0040075003020700280035517a40082030b4402e4170001e17508580c018840a01048034041158061519030041d14288141e00d680b103018083e000d4003d40740e441241da05c03540400d440b0310461200a40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111094973 1250 111093723 111093737
    0x122009010e150a0e0f0604030321061811070f050601090f05010308030106050c1e060403081509150a030204050f040210020303090319110d02060a1104051509060f07050c010e040c 78
    0x900c440c4136000f0459002c030058481c9041031130036408500903170003a4204602042d00895502c01e1803000d0400c8448650002c40d040c8806458410a0b81034101e07a241080d40322900d626824113404055000c80e07230b00550002c02043d22241e035084c00c0d529428280564443c0606101d002d076440e0680d805003034184d94104031030f1440c50b4a4500240c680d40d21264003080c6074060400843d9241700d20011204000801c034024040350f14291400402d40303480200400c40508841c4103000d03031900d9018043d44d00c00c4504800200082580c40042d0301d00c840c0381d0000717500509050070040c141842d013400c00c1c0101d10075111840310805014060382c4a000031071386416981d006010340103001014043c850130944803800e1140243c110200700904002c007840c41030380503902403828004402d006110b030004038a0958506410b085c1401f00140c3d003500103e0b1030600b4480c022403100303120740d503c0d800c45013912409483c0558610441c54100c0e101d214198035680441c00313040600005049c907008002c60b5420944d6180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111096223 1250 111094973 111094987
    0x60c09010e1e09010308030f06010c0f0b0403050c010e0f1002030f0c071718010e030d120e030c0604120e0405011a0c070e0702070f080c010c03122009010e15 69
    0x11450b881100c0144a000d45202c0c80c0034644072150402d0103540500d0846a84c0c0c940301c81060f0b8441c0303000e00703400c0c10409078102c02804906034800014200790320040c03040e010346481c00c00704ca171801028500030310f5501e42070081c007182c4000200c00d00c03814991300070758120070b003880d01d0705080303010803503d00010b24045000102c01c8420000145801c0e071140980b6081e100c078490010b81d842c0c1240c0302d1405100000c480044240d030b00300341840001c0c0d8003200100fa5246101000500c11505802d03009000d580700c60413080c2c241b40a0056030040c00c1c0f001d0840f5210311f080d08000372400500e40528000c1a452136403040039003003900945068518112010b1705964001441304c0180e440601d55075103038001d010022a80c00240743c00c0b80c0c000c0701d040d4018075246082809c2810308480b1903000d0307980317603111368a00304d02640c122101c4071016816090542c1072240d038901002c003074a00b50007606d15201510584000c0103080701701030710b02030f0001c2e0f0f14030300322103428404e1200e80d000000311240d0710001403005d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111097473 1250 111096223 111096229
    0x21308060c0a0e09091504080711030c03030a0f03090b090a1203020301050306071101090f0c050307050d0b04020603100305070305011e02130b030702070b030109050106110a200a05190602060c09010e 87
    0x1845d0030220100440c5c20401d00c8054454401201340d03022200c0e0b040004680051201c0c00c17024841601045000d0300d0300590000002e43d40f48245903011043c060a4580c8000301400303540081c0440d40c02144020107450107118a42d02c82d015031004032980082c1ca4002c61400d807003071003502d050b0b41c0c0140c000d00e1140c40b50642a6800f010120a10300300d07640f20942c8400007900032822841d0f19206261820541c6c4c06d01c42054102152500298000c1e422503110700045000e8580c401c0d0042c0e010354481d40e07680c0300c5c4200e11006800c141c00281c214450f195002040000550151482c070500c00424450001c034009504203a00c140d07400450800c911081c14000007500400075504141d9900490307580130317076030035190049130426802224407030f6503840100f1689030803036801240540ba01018200e034000c182d641010a076007a103840000008024500c42c3c50341c81d100c50f5031000e404000d05199244c1c1041100c400b04081500031040140294004078040302511030030303980d19810585415160369529414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111098723 1250 111097473 111097489
    0x1110a120813050d030615030e03030606030604020403080c06060307060c0b16020115031104050a090308010b070f02130b0a0512151b040f030303150302130903030f021308060c0a0e 79
    0x2e00050144400403100040d03c03c00c0016980d8255403400700b0401d03e0720f11404402041040340d0818181050302071450304c940841240e501c0b840131998241c41352150808100280500e0300000c00041002400584400c070015480344200421011075841c90b4031030350125007803080c4001c000e000e0850000807030309100b240744109001e000e4510002540090710b81c03001c602401c40e0b40c41135a0360464914041c0c61410b1a00555a0010b804002400300880e695401044183c052103055140c12012501e00100201c00f021501250380041904d005201c01285000045c001030001921901d10901c0000b080d00304142c403080500d82c40005019200c03110504404510002040440d06900300c020005d06000b190007e0b10242101a07000c0384100c2c15450003038100d0310f10b6441416070710a009020001607540116205511981c44008626201c40f03103420f40107080c0c10340c03550320400c0c00400d100e00700a05c45003000d0100e81c407c0007140c1341c9440f03030b200b0540544905038109001450807800051a400c22b881 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111099973 1250 111098723 111098731
    0x110f07020d02090c0702011103090a1701060f170d0c150902120706081819020f01120e0f1e03030114120f07180c020a0204051902040e0601110a1208 65
    0x301c003054420069000410048046910200c2c0c3d100101c0d4407015560701c1034480070100704030402940307441000300000d9a500760074492004c040801202c40d404544c020341200c0000d089002c40c20300c7c046d8407044005e407008030364000811944200002607240c144034901041000341c00000e844a8640d99a4004001c1e10700c416013a44c10106008803112105e1041000b40003c0c4115920640241880880840070b00000700c012845070340302c9a80808441000032101c0c9082c2e50403500d400840c0b8940e00165252852042171107012482c11a00280400c1c0214901900700720000c1030f034014004011a0120f450ba00c0c04100407280e00610040c040074000d186810742104c03000f00310241805140913500d180a00643d100280b0b50050401004400303402c5205080ca4031031443d05204c09509030000940d550040d4101030b10403525100442c56140c20f648500ca06503c1d01c10056640307035101c0d0030020030084140e940710700103a460341581d00c1103200482c1180b21254020541c0850030201c440c01c039030036a13020b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 111101223 1250 111099973 111099979
    0x41103450303040c1a12041a1e0109060e0a0b0406170d03060e010503060a0b0402040b07030314010605030108060c03040206160f020906150f0d060b03091f110f0702 72
    0x410409450345009080614010400259070b24a40384c90407020300902c0394000e151100740360103000d0030600c240d0305543c1500030410f0541c030700e036846080004e110700054003014031100da44414800301803045180c1c0b1080d10b03803079980c50f83c260f6610713400c2808031b0310244581410b200d075090100722035403c2a0482c45800e40000e0002c42d12613101c035030f0841d900c03c0501204009609c0805644806909805460000c180060243c5065850400440d40707441c0000c0002050320368411100c2d2550395694155030240202140c555210056450050010507241c805621803084410001400c284103a04503410f07209420302414050b261203844e00d51941000c4c0049911060610264141c0c48030702629944aa0042e4000380144550740140058041c0240245020383c1001400c1412031360440d089038088032150f11882d9403428500710303010040240350818030f9090f8000003403003c1900700250324000820012403002c0307130040200c490001c40e02e103121030092110b030600c0304c0d150104540001c1c0901500117 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 111102473 1250 111101223 111101311
    0x2a090f030111040611010e07030b0a05100b030703060608090a08040b03130f060b241b07090507020d020d020115050f040921020c012d0903150203010302041103 70
    0x8480c9540c1c943d0090f42040c0c0009070f00305150344040c00240507800e101d080034005000c4050568590b09940c11008000c000c072240c031800402c80384540034070210010302107a040b4545904100358010040c101c05d10a41d0300040e18400440c000c20008510700c0c0300e555011400c2841d00d172505030b00108a40004000c54501c44070034040c003000c00d900301c1ca071103000c901c10800007a0803a01c500400002c072408007007141d100070425460540b00f00300035003103504401c9540c842003100c20500b00c80a2400b4040c3c1c20034020141402c003401035194000554003500c0401d81c00f501c00c00c01e5504001c03404c864a100c412030404501540803c898102100900428400944007059086141e201c0e22044851040100c58000e91744082288003035043c44840e044180c03d290181c00b54000b02c491104119494001c5008850620303040080c850080740810000d603803040087d507207102d5150380c1c10003c2d0024070003a07002d60700341500d540180d58000c04a9214000102c44030700300b641944c150160984101481030b5402c298 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 111103723 1250 111102473 111102491
    0xf05090a06150f1e080307020f060c0a02210106151d011e0206011a04081509160314121c09060f180c0e0103030203030a11130602062a090f0301 63
    0x107a00980c0c0042d14130150b40d0380501500c503403c860100a1507105840ca43c200b8000b420060f52003012204550404452894031001580d40079402c1103803401c0000e6111701030010411280311214103818440c6016030003080342d1943e403042400d6000103240303c0030018040c80500c0724207610741e0110a03622101071414044403054000c0c0d4040c0010306600d07180c0941e000b04010440c3d050004903185000724924031040c00d140ca01a0055980c02d11503c0d064a0b4003125400204ca040d410826810003070b034100070400e605c0b0350303d0402c07500d04078040506490a0040d5009505604941c40c103c400d621054000910491070307000c07403d03009100b043c0045801c180c4500c000c0074940c00300d000d0105140c1e070b8146c0d41e0003800d12529120141d200d0380d078048015030010100400c04a0b4001c41500c0d07100c07400710404035826600d864403042e20701caa0555558800c0005c04081407050b40010090300c030390707500d12040005001c0340c04074010800c1d011506860302c0004000866043c01c00381440701c00c1c140080d0004c104200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 111104973 1250 111103723 111103739
    0x1a0a03180803101403100e03070f120905010e010818120d14011401020601060c0c050307060f080a09021c05011e0209030706180302040203130b0411040f05090a0615 72
    0x46106001d5409190100520400c0c04032558810000c00c52520061810441d0b5400300c0d84640091940c0036201d580c0760140756802800f841195104c0f980a00f51202a140500e410076107089404207a90015804c564046640c3d4014041d0810442c0c05855860950380e9005040c50720000d01e404600f214080d00c444c02040345165009004140001d28022480c40340029500304100303016072200c00c00f402c4a501c0e40300340766004916a0b044d16107500d0704012541680c1400a0040c610f175100d04c0e094881d541c0000bd12581c0942001002d07002a61a03aa00d51921100030041c1c0350f0703100d40a9404002d07100004070b548450003803020720b20700c0780c030000c01d003180c160541000e0502454402445150002001c808500c0c0034003012028009074103081a030f0844006c0d41c02c140700c4580c00000d025a60010201d41d17800d28220b0030707610740b41e07118003030401500d058540652044c040382c000502030750910126902c2d042a6020700d43c0303d030141c40010816000262a2000601221100380c92a05464280441d4242d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 111106223 1250 111104973 111105011
    0x7200d0606080c010503040803070e0a031410051503152205070302030d020601060210090c0308160606121e0c1d01051041161a011a0a03 60
    0x500803400081d00c14905419a0b00708110b00310a02d0401030b04200b00070000705903509a9400c616039241140d01131980f03030080361f041c030300c203030006410000c109118038415180010f0003525150480340078000350711440d948486d405001101203600da0021803e900303510b0b041045280e8420014800344100710004810010100200042505c180c0c215034010300540c14100203070141c2001500c0241543c1d0b14001000b0b4480c6900100b0060540c3c491011105000c481c00345180515008000a5501c00000901101c00c00c0c1d84075085424034107140001541802240418010030b800c60f042c041440360394a000320860300d910000311040086090007084003d9500102496890f10207078580c0f00b94144810050011a81030300c850421949596030808100c0800c10101d00700440d200801c5020b00008110000842c003050300d800b4180c000c134050ba41d0003501d21511600900811181c01542045100d2042080c0d00f40248a50240d12240c10b030724a541c00c000410f640c00b00c0b482c000a5031013450f4000d140032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 111107473 1250 111106223 111106249
    0x30213080309180c0a0305060109030b16090b09010f0c0c080102030403091a07110d020411191806020d1202120a0b01030506041512051c020a0519080720 67
    0xa03900100c0e600149007408038804111194050001091303140c910b140707a006201d0b90f0301500030540c0301d2003c218035901404c0a440130b158044210b00e0b0915111058618500702c1c4075400303000400c0b03c400000c2e02140c000481d1040caa06a40301581c0d0070343d0b103409440904121000301c070001d07020b40000410075001e01c051801103200341e90b00000301e454020a4820122240301c802c500036000c0011400003014a90040c403100300071f0714804003c3ca400c1c000900101910714040c1204800000c500812440311329840e80c0d00c1945840d40002c14071314030316103d148016405140d02503441512026005801051442042c16200c4800362500c81c87e5003103200089800c0d11866807950700ca010000c411741e05406030550006055900b027100a03000c20b07402000141c10b10400140a803403402c042d040c8681070003444001080010b18600c103803200200256542c0010909545034010780d100701c100702041d860201c0d119500642a242041915200c00b803500b0180002202c0150f812502505647c41c0c01a44040c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 111108723 1250 111107473 111107489
    0x2030306090c04050a120201030b040903091502030310210602070302030a08090c09160302090301110d110307022d0d110f0d08040b0406090212030c070906081b01030213 74
    0x200e003060401c0c068a90409001000c41ca54140014046512050480400c591980313609100354081800189c00402030114050f0308241401912418140c00144010890350300b05850402c407001050b00b20380300c0c002611221000c540520003001800410070384c2d10842005052440c004000d15507036101241d000442c2100903030030105d820304034103421204260340081d4801c040c140d48400700000a001d008010680030040203045004041917119a044d0b0b242400050000c10000d200342c001d9401c5504403c1074040301c1c0e400d0030951841ea050410a0f2402202c41760000c1a5101c0aa00303144030707040080d4649040d803580300171002c2156000300032210a1180c1a1110f80c5001011120329040c100040c0071580b040c0d125402c19041d10707501c011030550040d00070660a03101d40300c91610038060441d200010b98482c0c0c03030380c42d00310f080f0102100034a01c90a03080107c82c1c00c507913545055003c2d10014070881c8501d800c214031b1260458000c45810340f20250500d401450b25180a19180e410300d8290000c2e0a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 111109973 1250 111108723 111108727
    0x20f01050910080a060501110a0b0705040503011409010c0c030f0509060f1207030b0f0f090a110304080a020c01090513050403030b03010c020c03061e010b0a0201110f0306014a040c0203 81
    0x24422080c445c0501a01c400c1c80d041460390010300001d50ba0748481d0b41d004040703c0a800c00030781040e00c070b001602c02408004000744003011034105109000d89041d0ba001489511740070401c4540c6000c1d110001099605031514100b06005440c10346940d08007400302500030404205411601007003038010940411001007130806414210130060440301d1040740b05024480c2010380d0a40d542d100d9600060420048400b13180907036880d2481c0020301044d09495100220104c240420400c011024210100c1150300310381c9a94014001141c1105c0c6a100d00794000910602601c803410f250703003020398042d00074240454003414007004642182c2280181b42c0060708035451001c0c007480c0a010254109089403410612014030b92058480a281031149600381e50000804083e514000e4000c00e07012078000e503605440354441c0c00c1c0c401c1c0a0384115200d900140055402955100d034804180702d0029a03040440e0031a02800e81031500b1004032654040d0244034903403107010556a0b4080e456500300a580515 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 111111223 1250 111109973 111109981
    0x70f11010206090c0409020a0b030a0902011805010c060b0d02030d081b120106030e12040b0d0623060c010e06010b1b0a031b031407121119020f0105091008 68
    0x41108415048641190814801d020000c00005500d0080080482e070000e04059076100107410b503c10b80c2c3c040b10310018080100103c25803142e01240b01c0c03a0003070b25820a407640181841c134a00c9103a0003101c5c04a032140702500d0110b54550b00c920b02c0b00201401a29a1000640000385003019100d041d50000d40980100300d000d01401003c54454080203030100e0800c481c144450051100c140610000c0559400c9840704000b0200706401d00d610032450456a182e403941080142a44110850401b01381403030400203007180170034900b10707502003009000c02c3c2114082c01000916031040c00170315069900c030280d41b071790038509012542c02040720301451030303688000380300c503001500c000c1287d00c0c0140c00c20440080441d4000e0345119403143c40d9041c208844195250a95062b240400400742c0880f0100e6510200f111415105c0303400c2043d61500c1d4107400403c42e85954824051500c19960356244c076900005003084681c01741ea0301c105040203800c022101c80841d98034440401c0110018039120144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 111112473 1250 111111223 111111233
    0x2010f0212012c01060507051209060d1e110315010f020712062c0f0c060702090c09041104030303050705120c09030a050d0c05060c030f010e04050a020303070f 70
    0x501094054a881942004080580210740c0c4405204a0403c04600300e050000e60000b110480c060306910a100c0c0392558490b4001007440d04000350403613082c80b0f80c447c0c5200034615002a50017100000300715a16040f0400e200802500e6100c10040307100000f0101a580107196001c0c80c6041391880000c80c0d228640054003c001c03074007022070141800780c03205040000b158081003410507540d502182e80045510343c40d02c980101180c00c1c00b0380701031260000c004c0b009050703003140d0811810340c101141c00d001c24041e8810388440500b130a0a500100411060b0014100142c0c841d901801c1c040c020b0f402d01032007102140c10382e100c41e0b80b58042c1581c005800e03c1003581500c90306400c91160300d401c0b402c00c00c0310f81d04102c502202400042540b500850322907499a410086090800d03030250135510002c1c907a000207480405519401c076004d00412001030301c40c0e00428241c80c03003038001c00800307a400d03481d105903c43d4050000e0015102070040300303210070260b1401c1005100c0a44280715404180b061703400c0c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 111113723 1250 111112473 111112481
    0x40204140f0402090a0302010c05280605070207060219030e0306010308092b030804061d0303090106061112030c040b030405030307090501021506120a14070f05010f1e030f1b0201 78
    0x2611070b43c8103116100380c5072620201002980c0d030a08100e03a0070110b41c14007500e0a00030300384078a10311a00070102000c1401d200400c124981c840c401c00c1c800c648400400380e03182c08060042100681c00010f40050900000b626448810f00a0506107042600301c400300c0d0600000340c1003a501c0c41d000107220f2a6505100000a0b0b0759903544058041016004004030316868031084003804012101d00424240030003548580f010300790903c803003076981343c01c1550325403a41c0007112a070303200c3d52811a0000b0050700680c40410207a40c5600036040c45020504482d0981c1c001400c1da0041c0c01c0c00b8040494028580d9000714040da028130300440c0c40e40b0b00094010400241c0340c021034110341001c40140303400020004030940000d0700310380300e20031810605c0c0c80528200e034600380a0404440702d120f04c8a00c40c0d001c5038080c00d0300c00b51020701c008c0035114001902c0300c14180390203900198255020201d22000030600d1006e60500346404200610306550b000300752a001420f0030812607a80140381c07400da0b0244030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 111114973 1250 111113723 111113749
    0x1219021c0c110d080402011d1c0204050601091a0307050f0a0908010b010e0913030201110d06050a060f0203030a020c03071205030f010905011a09040b04060e0f06010c12050d0b04020414 81
    0x50683c0b0701c41400040400401078402418800ba070010380d10600c400c10b091494a16026180403411038100c80d420019040c20842030f809645000085401c0394403a9640006030f07003141a4001802c601101e1103040e80e4001031085c030820206000034071055003c0002007800340019a40d03074403450308001c0e0b46400c6668100c0000d040c4005949196081d80310344901a6100c00301440e01e10100c00203080c2039001d000100401804040c0c00640000c100001d0741c009010303100259034110f04a0b803075032002c1d43c4000041c0302040240e403040c00011038804458000f07007803010541d42a60b0170014550b54104000c2c61850600700032030000720070401040f9007603407214010000000107001d41d500d0090480031811840c0c603078166108002501402d04c0e121900300700090a800741c81086850390703548506000410030b0f42c510b1500d00d004008075400c0d61003a88452402078210800c1403800d45007610030396050344004184480340b0744a010726200341d42c40e07202800050001c1091480d003040e0007410800b40480e006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 111116223 1250 111114973 111115007
    0x6010b120a1512021f11060a050c1909050901030609060c020c0105041503180c030309060c020315040f060501060509030c03011a04050606070b0a0207030809031219021c0c 75
    0x10b0410707140c0602c48050850f0010001d41550103854000b01e40725412403240840c03102c5545030200c588580c86142029244502400d640c0f458036036050410554030155aa0004550148044da40056241420454200190901c411016540d00100c1c844200c00d078410340e9400e650740302e10801c0c003100c1d000381861103200e03102608100e50480000303091405603008010102801c04440b01c0254041e82c004542081b0f80b000b5010003264510340a18482d00c40d00040b4000b40340303603200050f490300880c0c3d01218141c0c000c0242c030040500700c09608074608001d01c1605c040903021345200105101d84103042c0a03003a01d031b66103a80e814614080c58640402050580e000703038034111400900605114044542e10b01c1114080340c81d403152130000703149000d00d40001e00b66180100038050220002d41c0203003a00f030301c0390300d40c000181d981c3e6000725128050240300e00d074a040c00301c0014038080321345080c0089000708c802c001414444420001107080d0006160340240c56500d001250403a0f4120344500c0c0390207040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 111117473 1250 111116223 111116231
    0x61401080f0a060c05090a090f11040f03020603061302070302010f0506010f0203040b13080708070306050c03010302031504061506021b030d120b0409080f0702010e1504060509030304050306010b120a 87
    0x5058000e549884812014090950700c205a51004d482a0300b06c40c11400b004008440080d26403800c04020241240c65421251401103542c00030f00b8050243e404031807001429848903440c40e000d01c083c2d903000806035580820b44521946800d0340620203080c132a0302030b50001808ae0004c21510044030b00c0035000d603051000d1040d41001d00307a0300008480903210504047c949940a200003d2180412a00500c5c180e02501e03c01045001001500030100c0740079000034829503d074007082d10340c10701c403e01002e5010380101c2c060069190340c1c0d8410a800a102d00c1000644002d00710b01c2c4566200c0d150071040050f0018000c0b68034260781c1034529001140210007030541002d4495019000c58450014402d0700741e02c9846c0000c6a1391260b21200100e5040b4025550b24000c1d200c00088603800020700300d010410f1003015107540d0170b00d2501602c0200300860030901d0142802010346458100c0e000f01e5615110801011415860030b21042e0b0080041c51599500c800e001398030018041001407030000b001c0d1034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 111118723 1250 111117473 111117493
    0x14010503031c0605150309010501050406050a050d0c0302090a15050f0d0210020307021021330b040305010e15060315130606061e0207050310051806010306140108 71
    0x400710894281100e910201038030004041d503118042c0c401944110b071700404048940114049040c02548621582002040543e0301d50040008130366181c010703d9001858400288200d061200c55200b24600550483c0b018503075a500050000104a809224030358075845907203050748008504a02401e003c071411080340502c440460038031694180080c0c4516002030380650b07641d00900440320300c1500600304543c02003440002070700e0704010303002180a0448040d40c120381841a841808000c240c8038200c00c209100041541c4260201c2400b55204110100000910846281c2c014001140703d100041480d4002440680c01c00c01c1380f01c88904121f10300000c0010b02d50b0080364032030200003692411505600c03103500e801c1001064501c0104000d00e4410041100d0742c1000300100c0802c000d181c0308040c0f4501c524200d07140d80042c03080ea601a48855018800d028040d00019841070b450a07005203096800601c483c40e086082e407040d5030055031030804401c82d2081c078106601602c1040c00074030011130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 111119973 1250 111118723 111118729
    0x204080708120f07022133010311030c04060326070b0c0706140403080405121e1b07090b011e050a1d030a03020f1605030a0303090201050706050a0f140105 68
    0x85101e03c0c1070001000015240215500c5000142c54070b007200503a005a0010a448250780b60761020100b4800c46a8281c0c800709440d2003808000d5a081840010340503902e56682e80d039407581d0410340207626000309040303c58281c4562040700011800b44120682d00000c01041d5041c00c8075429040310034110810801002c01d02440c032043d044901981110359860050611a005100c0c040c41140000d40b00b40034402819406107200e4052405181034541c22141014150030503c154000d07450115030f85188503d0703544134030002e0100665202035084080380c801c80f16504001848d086445084c0e075420758841607503448910300f1b881022000b60441d9810170040301602601420388038600f0020301d102441c00c00211890310021001e400380c11903200301c07068940607485260702607104220303120741004409410101403000c01142d40150162101c01d0080c0c80441c050210014168140f08042040301c000449510816100380085440043d46064031102242a03d6586031954071012040c0c0040c40155 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 111121223 1250 111119973 111119977
    0x307080a0813080111040e06130f020a02010606050a0f0c05030f190207080d1d0f030706020c090a06060f05031312050315030703020a0b0c0c040207050105060a09090b0105010f02150901020408070812 87
    0x542c48104440381f690300c1c4d40004607000401c00d07181e0308072420050400e1008a654016011207003294009001494840504079040e00411080200189841c921070703840900541070360503040c2c0510262450b2240b8080800c4540c1d001c0c070361407071aa02010b8800c3d4107107541805204050444003024000d0f480440c0b81c004e000c403810741c0051020500402282c4415920003040d94411040034081c0c8011580d6031201035100c3d01c0007090580a0402d040008401d80014400e440070307510180c850000c075011424040310f280c0c00050142252414050fa150f010460420a2001c100e0340350340c1e015524a02900c0c030ba6802103110001c0b41c0298400f450610051340c4d01038503001079450012400b80c8a000e4041c0c43c9250040c40712940350030070710000c0c801d4180101900142d00c115410380d40c000783c281d81c0720300480480c0e03103814002e80341804c0000103002640c451030042a1072031483c412202d0b103580b0b00001c00702c810426906100c1c5a940024104200d140610180b4020481200604020b1a440921030001c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 111122473 1250 111121223 111121229
    0x1003030801080a020904080d0e070b0a030b1c030f0507060608071508040308010e1302120a0c0b0301121709040c020c01020d170a0209011704030305100b070f060b0307080a081308011104 81
    0x3c7c480c04507130340703418075910b0f400560340d840d85004032041c0990381c140540481e801b11840800213410070780c403a016418242424a81d81d10071021124101101e600c089451521a244c82800c11404108400c0881c207103015000140c074020001d00382d014584454031079249560a055002d1100e030304208000709802c405014112a940c01c80c1c240c0d0795031100c1030160100d01d810070095001c000b81501403005280001c10b0a071140c070a07507820b011743e9107610400da0280000d1040480303943c10340110000040030390200b00d21038290b90782014102070040c0d0018060382c019410b20401030384001d00784942980e0400c00b80801c41c5850a007007003a03800c0c0d9501200c58000c000d00c11440e40f5000a10310285910a406d1103542c040c02c418100c0d414180ba18004001e8003080d140001d400204035004200c22540a084030482a8401024104180e031503403810050042c4c46050b59050051400c0019001d400380025540c103881460707059640d56100505046103001600329090310380c0b410010800140d6000112425 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 111123723 1250 111122473 111122483
    0x190309080304061e020c011e0b03030301060f0912050f0d050415110304081c020d090e04020909010b1201020a110c09041502090d11100314061201060305061003030801080a020904 78
    0x4603800c204144595081e48081d0713094402d20000d0001d07800d84041d8000b11103194282c0d180170010308410122020349807400781c02d40c0e16420800040040ea8024007011043c032101d0f080144296a54154062130003428000c1a61550411150f03194101021300c081076001c203040c05c10700c1c10103042c011851003540a440368035052200d18011080c00c07200800640707008080700001c41d054401d80800000c0170f845141c01d0705004d4800c902e0b04000c86809503103404140e620b000503008065465808003c000345024010342515540c690760141c01d42c858404881207003c070a000581d8943c0317044001003507100c1c1d141c0e801a0503001107143c20a1a030301e84c0805600715800c01d504019030781c003108081000744540b00d41c49512421a41030882088080c6070405c10040c011107000c0c4a680c0c01040640c1911808001c60000b03000c0c0c03900091080c6801a00c002200c0804400020030946a945003494035000f41d0303405c0d0b4403c02d001020820982c1c0100b805014200c0300c0041c0510441075400b040c0508005480108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 111124973 1250 111123723 111123731
    0x71b0b0603010f15141201060f051002030403081804020d060f1d060307030602221404060b1201152105040b1e0403031a100f0816090509040f020d0819030908030406 72
    0xc003035943e1844442c0c141c030401b40200012a503401c0071b004c4122440c030980740685d50307d640c505070060011090390112500500214076101401505020403111900544e034000e500780841c6c0007220b024030844010b029039644644d110703801e02c01009da22900c0d001d0800c41e0030014104100c01c90318040341e4282280e40c84000940c0381d2031602d449a074028000c60002c1411181007030000341b403040c040d40a5440d50030598040003050744440140303015205140340e2200180200c4010440302051031504c0b005035070a40303400c2d8032003991020403001d80320540e010a01c14a03112001d000500010060043e0010f01c00f012201c0c5000c2d0741c2182070f1130024010320180500d47c1d98810303c00f00c014604070199221500074207220706078680c010050502c0301200c0b440070000d030200000079108861160a2244500c0c1500c0b2010031504d0300702001142000100100c5808450150610042e101d81056000442c40b50000a44ac0d03c2000024a0107e41c0b8211130350400d8241402c040c003007030319041121380250b00108041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 111126223 1250 111124973 111125009
    0x90c121802060a0206060f04020301060c030f03020d020c0102070c050402040302130b1305010602011b03180f140109030f2a061820040b030606100503071b0b0603010f15 74
    0x120000400350300294000c10300083c04290158042800d0f0304ca000d0407100300940d08009401c0c081240001d01550f408034000346c12840c00f09020b410b0b881005541d07403070098684001030b002e403016038120070200d0100780c0d004562002000280501b09019000903201181024070b5500080c1c0b80982054405940a944e44070f4900c41b500c0d8146088198500c006050141e940d507000020300a1007101822441020940d0b00010b01e6480b0b4011080d10140350b0000d4000c0b80400c0e21080c841184001c400c58a0226100f4800301043e020300480e0504c501945543d15445400c4070301802d00c14032000c20341c1c0d52303600c0d46216040c980c90003034400210981003000028050003003200a401c2c01c050401c040c1140180c00c0303201c0c0c03000d46406020680c2c900c00359000d00c042607003a000c1c547d488009495a41d4885c01200c0c640380c0341c0d8458000b075a40700c1018940038401007200462880791188031001540c0300c0300418100f0095003024090030600040103103080000120807201031041040c80d000300188612005604 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 111127473 1250 111126223 111126251
    0x10051210051507020909010c0e010e13060e01050306090111030c0c160306022101050906041808120f0c0304030c120c02061209280f03051b0c0a090c12 66
    0x1640900710180541014039150118480345800c0711a04900c580702100000300c5002040c01403880204454403040c92000c030200c0107640410403099000d8121180d050503001c00c807498003403a0024804410442481c0d4103003c241414000024030703003947c80c2e04040310076114560742001c80313503c0952a8106c0740ca801c064400c0b2030524440840c92490008440000301c01c1c4105075008014004920300b4102c6521204c41d10456081824402e05500c0041440080c0540c107107038010b54038144e00c52114022071102640c8280b0b40740c0000300c1d68030b5191103003000c1050a112000c0f0058100d00080041130130f504d007070b83e40107004014180700103249610042c41003040c80d0050302c491082d107034014000e54a600c00c50b500850841c0040303911800c0b078422500f2180c002180599008019200407038800d02c3c80f020b980341c4d0440f651a600c0f08804000003005120b24100d0951802d020b900000c40242040c85400b404100c00010329030070110006d4500f100c44409150000705210001030a4503022036001e19039014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 111128723 1250 111127473 111127501
    0x50a08010b03180d030501050307050102010c020601050d0f0804030305031e012d150c02090606030106120e0c09090105091b0d0318080a03080403080f130b060d02040608010e0c100512 80
    0x9070f0a058440d0f1410350b2074054050b0010f505a4200741e0486810755581c400490a80d10b1075910440543c01040c014480307420f0089041508038040d030782681c00315455075100721465009500a0b80064000703c24443c0140c80322914000225000d1003031081541410b0b03540c03004d19815641488290088000c5142e00e4040800a030020545840100700c48020359001401035901d009040740300c3c060500001d0228907017203040d40d058803107554918410501a00c0c440004082107221240548108400031a441d65040f044a10804c200070003c2842d050468645281641ca40354a024481c03071040c0c9034506859104108405a4052030400e0000010801d48130b810a0550090350300340c003a40d4540d0050640105641d401703644203a1b40d5140640d00c0c070308000340c0745200750340d41c0c00c040724024482030104002c0003482d508000028200c0803042d02030350004040711403580c0300d144aa5140c0b03107903d0740110b00b48010407642e2405d80796060441745c5588000c02c203115091081201e01c602e00082554080b4180b2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 111129973 1250 111128723 111128761
    0xd1506050909040c0f0f0801060906060e13020705160503010c03050106080c09040b03030c012403150903030f0e0f0c030f03030612070b0d05010e180a080d0f02040b09040c050a08010b03 81
    0x100d40c5c01300c40c1c0310000c1100d0302c071242c02215103a40c00d0660001f0600c4080c460002220b00907a00d0640300d0340c2030010003024011903425a00301607000d103c0d000214809011405041c0301c514039140106141806150035200c00b04841c07028540303000c004001480d0440c200903480b00fa80002e0035a51a2180d00050043c03c0c608000c41e01440301095850380361405502c8034003010b5403c0004070302c05900c03000301707180e0308464007005201c0480c860054144d0070090b08075000c1310784a030401003110016000114201c030900c840610756a8004400400001001c1c810901441d00641c0900b802d0b2001e100c409a5034400603041e180a45503d10b6040303014541404990044c081c41812a5a2042e103103030b80c44040d00007801105004c0b070090010030000c0c2c95000042c07080d910310303a0141050800503140c1100d280c101200b6040c1603a21070078240a60095440100050101c11070042d0b101c210b44c4060100b1221142e8045041c400304200c0300e040b1a811803213848c119601c261949940781d0b601c1901c0700758008465 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 111131223 1250 111129973 111129989
    0x903030c0109060504030e090412080a0b100201060303030f0b010c1101210c080609040209070f02010225050607050f04030f05030706060602152a090411030c0d1506050909040c 77
    0x7009008002c084d401030f5020394020303a0741c1d41e52110008200100d609041c0c400501040000710019102805181142d40c081d051440c001b410102200200d004c40c04102107060050b5544c2030709004140d014400d1002c2c4000c0200204101c4080c1c0d40081c006c1d20110341d01402c0c9600761022020a6072107501c2d00e400d07003c0754102501940c0d00c1422890007401c40c05540c0380229101000060362400d000c3e03206071042e60014a8419540c071400c0068030310355811000d010441d5020800d003c40030300184146a030b0020780e590685111140c0742408c0d42465801340550081050400801c40d01403580c000f55001d0342d4005d1036400304440d580c80c0c00d03440c510480c40001c1c08281803550000d000c90b0041969860b0302c00d00900301040e55a94000c0c0b4242070807142070700b00c0344034440f40c518902404a00c0541140344001d44006014201c80115417040e810407204440c0100c00020304000389903030350094141042d010504130340c66904000015055016480459000e146014006400d1003c0014544000c5c6070788 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 111132473 1250 111131223 111131231
    0x1140a0b0903190f050f01020a0f0503090c0303031608090307020f010f031509020d050a09030f0e0a0807030b06120a0f060207030e18070212040f06081009061e0605030403090306020903030c01 84
    0x7844d240300e0949404c9400c1d0303100e01071408954001c08060088401d030019507550b1600d00510303102c0903a42500b02030002c1e20903206032913210500c1c6e1410801140140408024800000c5c0c40c0d140c0108400c80052035417100760401d02070707040182c5500c0c0c03040c03007600024207210a146030304110440017407036021403101c4440086803000661381103a81c010441a9403199062009a4131100c0c014259100084005c0c0000c0c1c0b164124480e040c85400a8484050f006001628150b0703100c81c19071401c040f03904141c034840610400d200540ca80007102c0100c0f0705049024009050a41d2664104080c500341e024009603000961071080600c10030070b000c55054010b203070501080c2c3c07904280840407011a0f409015114110803071300509290402d90381214032035041203100f107007001c40403100d100b00680003c00b24082944041419050703030080c2c0003e054414841d0304220402101a900d000080e400340c02401820000d000220364000c8103081580c1c1c12a5001d0380e0361404c0c030007107880c522402c41b15180c0c80d4070b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 111133723 1250 111132473 111132523
    0x210f060403030b0f03060f0105090a0204030f0602220f0e070905210106140d06020d0b030609060411120d0e0a1a0301090e03030f010e04060b041b02010501140a0b0903 73
    0x743e44108114507064039881e01900c4880c080c145d4440c3d068466900c006403131001003149103042c1c000b16071301900002c1c1c094103243e526641d980c000405d001003120100d4010444c07801e04508034040c01102140905250407031454035192110090310f601464040c00301c4a40082c40c198007450200004080c040d043c048903890b618120a8a5000e68950199650820300002002e80d20318109016074039005101c1c0100e0720346560343c00020340c80000300f400503c1c1c903480240403070307581071203868481d103110405460319103000d25250750600641400039100d000c0050043c401c0a100198241882e15117040c017000300c0c01c0c1172000400c0042c0990140d40c001d0004a884c00301a00110007860480d400000c0c14455451044441900e0340412100e03220f51006400042060b68460460240c1150082000048001038500400c040e120b03908500c5002c2d0400041150302964244a4039004003017804000c2a051011400900075039041e2155401600003c549454a82c0d8144030314444002d400c1713008407032300784 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 111134973 1250 111133723 111133727
    0x5091302130917041203022a0f19080a140111030103060e0703020901080f0601091a01080c04090501060807021005160e030304090e0106031703040503030601080c0c0706020309040e010605210f060403 87
    0x250142084005004411094110050b9583c44c42205c2c08150581c1b1180032364a02801509810a4101903002d018000310340e10100040b40402c0161100f10050701d00c6032654202601408620b002078002030b85400c41010454000c00156815a41d0143d8081042201c00724428078107121500701030b512403141c2e000014442d50008031408d80e1420441995607580c3d0307940100040320425800d010701481d4000052402d584100a140c0d40210b02240803824035031182082421650260450b001148091042c40140c540400c00e0340c82d03801c400c04003406507142065001451244070078104003071100c030010b00c803550b580500543d00506165a0b08000d548100c0310300c14060b207068070082e5044030781c4440380d085420102d0b040ba48595041b00055241da1200001150600c0000f000749056803014044100304000510800e40208032030ba004544640c400c00410044511400d40c1800c180e16148040110b07031100d4403d07181c09a00d07441e40c0b41d840e00c0c00c0b0300060708054501b01c035080540200c9040104042e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 111136223 1250 111134973 111134999
    0x9010e041a0a0509010b0d02090a0b120a0c03231b0607080c0606012c060d0209180406051f05040506180705030a0515091801021c0203010509130213091704 68
    0x130325901c001c1c410031042c482404100d07802c5903030180d0407070070060028240720400e8008a00040000d0302c07980b2203112005000341001d03091441100c4051600c17004005004442143c038104c0001c0c49080c05100304094179642c0d59a9000c4401c03000805880e00504ca02e5a400c020f40e0010b9030041d216684d1802d41095550311510200c40721800b0885d80c1c101181d00d406461146e40c4ca0118070070301040c5c1d000140c000c000c80e540040700c8445c42c480c3c080084003403544980c206490907040d0104020b1040c00e00f4034050064540084c10940101c10291403000300c61300a0740624112407007a9030000d0992075000100703260140600341d001e6039868400c00d100c046941f200040d032041120742c4003004261a04440e1011060340036a0440d402101d4001085008291030910112290303000001460503a01030036a6002c2c400c4200f101808650100041043c1d003840041140d000c241c05001c0520f000301640000c0c802104020f42000031596a0440342c100f02d1058051003504100c04003c0d80c4a644e5901040021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 111137473 1250 111136223 111136231
    0x2b030b0402040504020d020c24040f23010f0b0402090102070b0d06030203010c0c0510060e0711010f0e0304140a0308030c03100f0902030a1404020a0b13091d070803070209010e041a0a05 81
    0x5480b68984039a12070003d030201c40075020809d604025180c8603a02c82a020521000c010380700c065289150039041c0303691000b6003d00d1072404001142d1301281c01c04050880301c4405071103000d180100f00c0d0801c2c070b80e404180f400990b0300c0451125140c14085031400002e010a82001750558a0900e9001c082da40000ca2000360501c948200c4810044035480c06055809500c21008004c0c448004074007076501460080b00c00041600c00002d11000381003205003034036421154101d29800005081c00f00e4099010108815042600e00d15407103403455031202c006202c01003101852030720100103d07021980341d00841c1e0081c40d00c2c034101e0000c185c468000c1c0c0300a50040c0e030740e1108945403200105400a10002c0a03108a03001010030011900d01b608540c06940720b43c102c21651903041c0d40202d03691100b84502107110308801980981101484045440c01900e03401150b8a54400c1c020000160303202c1107054152012680300366440e4646160a03030030300e10000c0401000c2c9401c0c0d41001180841c0750300c00c030700c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 111138723 1250 111137473 111137497
    0x3010e01060f14150c0a0c030b010510090e010902030c040e0705041403190209060f0415050307080318010e06040801051305060610020c100e060301090e2b030b0402040504020d02 78
    0x100c60380d01c0e112034100382e08980750340f60070a402d0405510003080c81c0001d05080c885d0441983d5a0035a00da0760030b018524560002c80c2c00c0500000103100c1c604259002c1c010b0600c1741d0074080513403401d00d41c604200c04014400c0303210a0750000005903c1550f414155401000d0b405001381660a048a02034229002401240c0c805001080c0b100502d150001c1e4080aa5224103019030b0a440c080e000e2000d2800002c1506070842000140100c16440e03074840e43d501c10108542012005080c80100360905c0c4156000c0da1456200f880280000890244450000030b000d080000303103900c110000c50098059580904510351030b190400c20340000d040040200244241c080d14501d40d078940801107205c6a40102c0030041c0d02207a80134035035082c46103030181184103900340441c0012442c000a95558400d0f00b02440040d120306400104040410503014801c01101c0500382801e1000b031340303800c52118448064100354888032445010348456044402a00700035000355a50080c4060240c0030b54815029800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 111139973 1250 111138723 111138749
    0xe060a1d0d02060d0c0e03030a0c0203100504120c06110c0307031107060f030506040204050916020d0c030c0201081803130509060402030103230304180c020105060909100f0b03010e0106 81
    0x90030749041d0403003884440d4010021410205290080001010a900c04a040c0840750700408000d540810240000f05580c1d600e214a40b4028414035041802514040040d036003000203000002c1c0d2181e04050701c14000b4a07100c0c000e80603d0818030701902c8203420100c00c00c0380000f680c01da01d00020006060b024001d8070ba0a60f411201c002441c1ea410551244500142101c202204107a110307410103171304001d0041c409400c194032a400502c6051040e035000d064400704c0036609420580600415480d0051800c007905451a1a00d003d00031104a280080c1085080c0b4005170207246401100d043c0c2d907000c401229143c0180c0351001459004034002e062081d01880b0003e0704918190007103d059039031000d611401d40741d00c1c01d103802c10640c41041845490105100202c0c942c0d040e5200b40d045400162408904d010440744080c3c21104040c295a0144183e8000c00c00100c4001034030502000e82400001011003100031220001c000c115007065041d400d0002c40300c3c2c4210150040c1d000d89981c0c0c81100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 111141223 1250 111139973 111140027
    0x30918011e0b0f07020f06031501080a09020a0e19050f090f0c0d02041104080d091403010504030824150301151b0303021c090b010608010504020702010503160e060a 72
    0x11400d0307598819031210890400c850104030741058040c0410034405420240ca040c88100005c01503001280d20183c04002c40070460200e40e0f0180580c1d400096005040056003a42e4011440343d0300319006420811130b0980214000c81030030f640b0001102241c8a08000509008002c0b4141000c20350b10606903116144001c51646800f060348000500014100601c9040f554248000781020380c43c0e048625406000c00100c1c560140559103055084d907a402e0f242c1030500c12600100c3c1c02c4644454003da2400c020400040c2c2c0006819412844105543e1241005041d0280302c02c0141031080f504520b01940c0500042091000746043e240e02e1074004100b031301303004070464003408491047c44441c071044460070082030280c0e00904040f040d445031401c0d8100920250001d586060804413421240b1a00402076650300c6030149000d40b4080b101945003444a4000911a01015055141c4003600c402640059405602c2803603401c40c0c080c10041d1607000343c02018061030030300d800700121030405102e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 111142473 1250 111141223 111141269
    0x50d0312150807030b071e111005010b0a2a03110d110a12052505010b0f010903060e030403021c120207060c0605070210020f0703020c0d0506060d030203091801 70
    0x1a406540d041e600074080649551a1041e04040160090050004c00f01c14612980d04201e01c101007e9425100c0e001d1048070030000600e40407a500c8c0c9801d0340c1d0300e400d00502c04100310104581a41c0680e240c4160403030000c0701c60900000d000e090000380c400010700400105034000d1071001680c240343d8240e45c1d800c08804029203000800850b10101e035001540100c0c0043c80303402495605d4201c40c94070a003041025034641001c00c00402d2842000301c6145180c00402009000398510040280c0300b40f0501faa01c07100103450345d152804010a007c1c0c8071500c50043d000c0820a03140107540060020410300c448009124244520300802d8031080390881000044c10f000182e400b044564564031f80c07030004c1c5035403521720041070301818200c118041c180c2c1004000b20f0a0000d40038016280e001c0c0b0743d0b541d17080c1c50048e181c000c0e1164030600911070346404002140e404520f491348010701ba585140084420314080b815886100c030703050381c450f02c06c0c4000d64031424050101810b030741001c2481943d072003943c45030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 111143723 1250 111142473 111142511
    0x40f0917040b160501060906180e0f0c0d15090b04140303010b0702060702010e0a091a01020712080309120403050a020a050f0a0312020309060708030a18030f080c04050d0312 76
    0x100c011980040003000103140c0d50f9011058482d0159000058003615a141902130700e291341c4c001d40c03030348402c0d241440700c03254076100c1d00002c1c00d90381c0010b00c0d080031034058454031102640c50040c442e200d03107449401401840380b406400319404402c2008072101a00d00481d0300003060b00c0607501c0c9502c00d1242c4038045000002c07a0706a0703824900050801c5500da003007040c41c0e444224224100000c88604035610303103235115440b02611071071402040b4042c80d000400302c00700941051710704640c06001d0421004404000c25000701742c02040340c5a9a40d54900714903e410b03600d2400e01941c0c4400540001800070200d0b58030795482c4200d42d040e50319903441d4100900d03801e803840100e41c082d00c514800c000150009507001da2445450054a00740f030804000070706140c00c03150341510003207400001c0007141111b40c0700c2c150b01a91030f12000541216152001401071034104410303001d001e94040850140c08110040e1402400000d24800e0969042c1c40c004100c081560035041e6035074100481500c550000d801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 111144973 1250 111143723 111143729
    0xf02070b0c0d171308090a090c0c0203010c0f0503062103131503022106030c06160b090303040512090613060c05010f020319020f2203030908010203040809091005040f091704 76
    0x42404a000307a10345840c3d117a070f8804601d4940c012402280001c00b01031500a2400182c40381d255813540481c01c0c010705095440c9191003000b000b5101c03024a0545400c801565001340d4142c41c030440d000c00c80444100c0700f40c04240c0903c014403011800d1880d401801d81a4425152a440100c02c8420544400d40a9028100304204425400d200c0c19a1084101c0c40144d0320031380082c00c48000320800d5000c1002ca0380301c01c83c880c2c50516200074250610602c100921f40201078000114a189400d480d071685441007441064440741e400140c00b0404d5032400243d4411401000468a08a50301c00c0094070301480d1082c1144d1650814a02551449542c82900c1c4105a40aa007486150440540304029480350b000d80180000a0200c490012950204110041521414110700303904500b809031801001d1350094600d0380c010404c0000148401090766100c500c2a00c00e4012500c618a81504091030758024503006880e201811407400d1403600300c104030034002d4610f44030700000550740c00308902c6240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 111146223 1250 111144973 111144991
    0x1303020d020606130b010201140a090209011d070807021c03061e0b04051918090302211b0c040e0d260c03060a0b0403080403140c03070302010f02070b0c0d17 69
    0x2210320503e4441380d8228040d0480144000507201c1840c0180e5055454181ea4184000c2c7e07948241d0001c40c00c110545074050099403540e801101c0c118501c007400540c3c020721080030450b100d400305000d14000c01031084004660240d4000d00c8800c144020010f207424800c030b000841c203185002c0e0b50361b46161300d044142d861440507a8907244c1008140483d1140560305408541d18100340001c0740c0d162180000e0014503401808255007840382002031501d0200100c4541460300081407400071250340044039410301040417014500c0017229004d90074900902c4617242c120b400c00f20b01c08280136000c1102c8082e03500a4880c01d158101020094001d000c0e1100343c1000051071001044081c1105401785038044801049c10703000c252610a18401340d0017640c41202c10100101d020720820054802c03641020700c10307400410310540d410340041c0d964106880007034180306003507881001c0c141c402e00100015000c8048136030381d103090300154290346d1520003841500140c920440920702844942030180906030315 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 111147473 1250 111146223 111146239
    0x50d030f0810240305010806010b0702040f0b211212192408070902160f05010e0f0703231005070c0209040506070e04110a0302070204141303020d020606 67
    0x8050644a074000a042c003000280354040010f41003243c0f03001180082d45182c000c51000c00304000c080d040d80d0042e0003000043d0840d10043c401201d894058500460301183d0124595070301440171801015555003040e0450302506803489a10109886803081e03a803d0740c1118424200c5811404642c010448000d43c220300076000308410b00c03502546910040c244039800507181030b40220383c0c031440503c000c0100c98094000c0c42000b001c030040c0039100081c204298150318000e0f8007002e09105100038000100f1001d0f00481c08000e10109521507002c00c1212011038184403250b400a96070303081da0340300469061002c0d4042100040c1c4648495201d5180c010013489020b82c06921880682401130001041204038074421002d80d6600d80305a001e41c0c000e50140000c2d09084900801220201409600450034001300c203940c0195002118071146581c600140c4807140e61000802130038030f120b00284142102814021801e41500c009181d141c82902115054014001c0036615010102da01d50780c04620 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 111148723 1250 111147473 111147497
    0xd0603060908030f241201110a020d1215030b04171803060c0f030115180608010602100e03090d1401020706140a05060307030b060103020705010c03020a0215010503030a0c050304080102030c090109050d03 89
    0x1003400b400102c0306d46c0c0d500101e9030007170305101c0e4801a00018142d00042c0e0081020380d070302603045080c000140d950f03210113001c0348580300c001100101c0c0d1880000c01403409000090144000c00707810744c5240d00c20b541034075601c00701841c8101c42c0558444803603200e8007075a00420b40d9800030718101e400da0600d420f1414207580c43e0026540c404c0c0351400b4408180010521000182140d0708203485c0500841e1325501e0443d41801c0e00245416541e040181007107242085d421241100041900d022140c111381003500e589851030003000003540780313071001606d6002040800811403246c0120b01e0b0814400007190b03443d9070b100d0340795080d10000c0e0340060f0103810080086c0046034018461035031002040c18054a0501c055880c1402c480841c0c52680002ea80071907c3c6110503030501454074440340383c1803000519414540041e40720310a00c1c4080301405030348040c01c0704205080c4295402890010021500e0386042041445680c3c00b48140b42c0c0013a13558030011a19160103100c150003542c1550f01d0010400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 111149973 1250 111148723 111148729
    0x3060f05063103080d06360b060f0c0f01050c03011a030c0919060908210901090312080402041103010e0f06031009032f030706020d0603060908030f24 66
    0x945841110b014042550300400403403106401030280740014040003c80601d4014030f11040031005103034807003984c41d0b211100310700c01240d003408138240011180010010840000200d580c890318410b20360098000c41d201c4c02d000808a02e01190800006c000d01080ea6507642105451009000c5c1c00c0c6010110355192603403110400182d03500280c4003454515003070310701001491040c1100840e0f88040c4441c41d09104c40c40c0e210300b038000100011002415044080d100c0300104485040351011a02000308054416070312441c1080000c40e04410000d01c090305c00b42d8000c00030501150280d010341d06082a401900e00b2580c01c0b0703412112640e00c40503850f203450011005501004e0700c0305503d44501800c0c912003100c14860692960b01c2a250030f040002116004415406014201410700030101d1030a841c2a0021048401295004000690391442080340ca002000c55030405400c90746401d064000b00402003001f180115110005494107555003404008108406550010700252040740c084542c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 111151079 1106 111149973 111150037
    0x9060201051303030b0307050405160e0f10031a030303090304210f02120304030b0c0301031a0603030409110c0111221d0a02120703060f0506 62
    0x102d001071140c180c400c10028042c0034103443c0c1c40348155130795007031001c100075000c020010020b0b800d01c1011034143c0404410b0350f90100d102c1d294001c40c00d02d00002d05550480000340800d852210b4840704a000d05031114510f042415400b40084080c3d400f400518410400e0600550b140e5103400b0b0030f04c152070a00304004d80030085525031324020420103048000c0b000d4055407414030000d50f062195181d481036a0018002e942000f003885817401d5410000e5048a0140584188043c049040190010070075180140c0c540e00c108400c010b1214a0b41024684860340c6030300030f0030032080c140c019003501d40b0700065015118000647c4031036040310820b40f0045c121041aa206007500701101d690301120780070b80001c56a104030000441195480d0102c410120003a84882d003203080c0304034041c015100d14010030f803500039000c1c8080342a00b420000d4402000001c00c06003603001c445400c6119403 = true := by decide +kernel

theorem cover : BRFrame.Cov 110971223 111151079 := by
  have h0 := BRFrame.cov_init 110971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110971223 ≤ n) (h2 : n < 111151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
