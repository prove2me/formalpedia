-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1613
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:13.773432+00:00
-- url     : https://prove2.me/submissions/f8f7a91a-1f34-47b9-91ba-296830271bcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289928057 ≤ n < 290107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289929307 1250 289928057 289928069
    0x1501020a150e010e030301032003030d0b01170403020f071a04093c150b271009052803080c030702090703020c0c0409080a0509011701060201060602070f 67
    0x203000d810000941c11581c114001161000000c1d5840d02c1d140068211894220150003e5102000400800850504203581e80d41e9602d4000b03400c0500134007080e501e005490b50342c0314558940580d0741469200d1000c1c000e08489001900c0785909003414040d44408444e0114110307401516000704149100c40800a40e00101e4220765241a241c0280c403801070034922882013071081c070010004c1c0035000e20664014220005854030020306104008007007200d915034001c10b00a403601804011040c150303c10b440780c04011024003400c1c2115046440020048007069540c40343c004080401080c0e4005070306401d42d001503901d07031101030720302d2060303041082484c0001c4000065000148001400000606034001c0702204990410005500050340c66000f1166080065800314005901d612b040181911001c2c0c10345003001029044e884004d014415050100c3c1840000079002c2c03616481a49144082d01c05c2245200c500d5031281c10081c085c10740351140344018881d0010100700741050203180011551 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289930557 1250 289929307 289929313
    0x723030103150c02030a1d0a06210b030c04020d09150c0329010c03140309010209040b090f0103170c03032d010f15110f0d02010509010207030c020609040204080a0c0608150102 77
    0xa40c40b81c0480b88107000c8000030747c22005140e50700310192510700c40d40b80500515158802e00360114000e8502d0700460155540c2a1070810394040390a460219004452100a442c02f50f507415400c1c0e0110003400e80030f50b0051140703100d000100c400c94003581c841c8541d070034195410b00050012500041480d5000d5800510807404901401a10344c0580030f805451803190901c03640b25603803514183d00303d0304200c440a100e070b500025003c08074034162207104100e40c1d0854050446060907003088041c1101400024140c8800200282190300b03100d0a8906209540044a5807458400035248807483c546034890600c07510b20b00307480f0394091424001816a9000e04800024615090010000e060004804018040f07032916142d41c004061150000402041006018107640f482c0000e086843c01403c564490348140a0f560003c3c3c1c0c803406c07240d8600d40441d11a43c40c1c02c82000010000c0c45981e010103070754410141188108420200040c0859056803a00b540555402041d600d030010304030111401a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289931807 1250 289930557 289930567
    0xd0e06150a0e06010e06031305070f0e06090702031b0a0204050a0b01050a03091506080307030f02030a0e060c030903070e1b091507061b050d1107050a0201080723030103150c0203 78
    0x2440c481c0d203050f40440c0c1450101800b02440c0d001c510b1a034000c1d220940160240410503051140c01c200140080560100101285185c10b440d0b0419240c00303045948a00c4041c400310380060310800c01d68007903d285007410890786822500b80780c1e0f10710403650104d00681c01c081c0000c6036002c552184c28010001a107840780381100d5034208034020454808221801d00e1503400c0040001c545129900140c0b8021000b141d9484480c24041c081c0300d181e41004d02190700c1000304603003003a44189242d80240080c1c6225132130b00ca81d07502060540c043e4511a03034051140c6100090071030302a20500c0d010380490003220403071104600c611001485030b4081c058000200440f0f03610074003840001002d656014910000385243e84e00010601d22156101c808000344000c03070b24401707001c4144622414004040000340c0b0b081d00030343d1142c0c0c945160b5003001c0c2c148252003000844c2e445c0600b9280d4170125941196103101160000d421006030028041a0303104508101c0032550100c1d14403e048160103103030000c6042c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289933057 1250 289931807 289931819
    0x6080c060a030e01020706090308130309060c020307080d21090b01050d0f020d060e0106080f0c01110304120807060b010203030f0c0306030f030d090201022503030311040b0d0e06150a 80
    0x156201090400c2050369498080a6043c02032018200c0305101d01c40200b015403090800401d11075016243d1101c01094892242c0003c0d00b0034906011500c090500d4041100c0b5400000d080010a61180085014500500c0d100300d6100c0c14400200585107010321040001e00b070040111190200010900902a001032000e85068125042282c0c494122014181e510f5070201360303c0d000b00b07101119001d842d80103610180e6002c0c001c2c00003400300c202c02403113550550703440141d80c5da2826842d1814044828050084480c052046502504e6449442c081003103903443d041c01130f6030000100352400ca05e40f4009041075840482124004c580c410500c43c1c1584802119204a500241c40e80c0d905100e6101440b0130300c507090029040002198000164000e1140000380c10041c05800152050000301184070104000311403800941c1d80614000564100b603c4900b00c180c420307030300321001028001c2a50b14205080d5004501e036001003601750303161a1101000940c424510449041e80000c002e03909202ca = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289934307 1250 289933057 289933069
    0x90b0114011b08040b0d06080d02070302010806040902060f0f070f0803061807051819060302030604050a0207080703111e0f0d05090a0513110301030507060f0e011e0207090204230406080c 82
    0xa0006d01d0400140d019900c803850b900d8207400030104800350304980b030104195078100701c0d0242e000368180c038244000400e40e40026423a10070a20341c03016001000c10b07034500088064050f211015485416140d80c020181403425050f041125020f2082040c0496a481480b001c961580540141d886841c04c00340c18010120070214800c203140c0c0c000003085003c500e4201503124240003001c042d100181e617400c1c91340c248004c0e14002403650000e42d00420114000070b00c002c0440308401d800d4607103900c0b05031108002c00d017045a650b80b00b01184040001c221866800441c3da81d0b00c000011044500c211600a0300b540d40740204000c6940c00018000100b02d107007810f000344100c0e02210100000c01d015000a0460660420780040d074803644401c0702800041d80040e00c03907054100324209081c1441c003510008014000820300030031030028001e840c44a841c002c01012015081030202551603a4641d8039a4000c41101c09000c00744c0000180200b2003810607128180541c3e560b02c02505010503940c0070320003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289935557 1250 289934307 289934317
    0xb030c10171308030126190807151503020411040506162609030607020a0c05010309060f021b070b090a05040f0e0a15150806010608060d05100501031a0f010315090b0114011b08040b 79
    0x122024ac408a1001410300c511400d02c000762015500c0b09010b003140140012074001c00700035030f4416420007045c00b0355614181991108040005044403101091130701804040c4082855908030b05403003400166400500c5c058580480260201d40c46a69a181d08a0780c1e0800c2410152003840c204100f40001e501c26001b8041e01030007200c002c0360b06609030038000203d0340001150303140c450a0f0400302d17201c2202440750704000c050181d405030400100c1c0740000d801c50050701c215071040c3d6948010303024458060b0080b080c100264030548039244690304145142c12000c400704000c2c00d1600021021440400f4403200607602010010906a07003000707803c1d00c988401528640e8048106c075203280c0019002c01c9440e865040e11000410325525604e003441102400c401d58444030110030341000040e150400c85981160380002480c88205035101140300240f050340d0001c2c1c010398441d400801c003504000030841c1108008c3e0f841041e00c0e101d41041003005801440004c2c4420801c1004000700406080604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289936807 1250 289935557 289935563
    0x1902090a150c0b04050607091d0604020901210501090501091a040f1e020703020601060503060102032209020c0a0c09090b181006090b030c10171308030126190807 71
    0x20041008075190b00550000440b401c503a1780c0d000c901001038950344480e05600a040741840c110041e041d04003030740044030008080c00c0c00341d940443c002186a200d0001620481c00c881460800043c03801c10a0300034140c02d014011505080000006502465114000b4215002c0703800098414184003008064445403910080c405e848a58050f28400c90036901c004078541c104005a945415103070190030424140d01010038444103204022241e42c02008448030300444294444420100c6c1d5030202410003560016400c00b40701149680405400081d00b12150740079094249417155100c9212007503544140000344140f0900020490300142d5002e0305e50307024040415a00d0207032411070b001c400c031a4550b2010046075141da100481a00303050010721001c8009483e4028007021182001c0d103121000f03985000c154510000081034031844100441d080e550040021f80c0e0fa503544c01042c0f04003540f203040507030104840140a17100380000900c80c02c601e04c6070b10444003d9901074441141c1c07034110303000a0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289938057 1250 289936807 289936817
    0xd050a02040606080403020c030115030206130b0c03211e0705040b0304030309060b0108090601061101060302030708280203070b030406092f03031e090114030a051902090a15 76
    0x100103a50724001e000151249039144041031400e818002e1500c203503440424026450a03a081082ca0303e51a100015203805a821540d951103d03e0910f5408019900010b4031050104110106800210083c00b001c80d0011500512003190388000402800a569842c0c203c0c50448040b41051201001d550340b0440d582861070409643d031381d0b011886d0b4001c030380c1100020b43d1103019504000d45031054019225003131a1110140ca4400020350344c800f0706011f0b810600021107001c4070303442da0940004024690180c203541c48140c1d5407007040d136540d902d007440078003504030600b0103103100906441e440c2c48140c0003001003212600d040100900c941c005002034511540320003000002c6034110050340c00c82e5483c1d80806c100d0600c46000c162001f10311108161180c1c000f000030140d001c0710050002600207c2c0010b00782c0e152050b000680d035400440400180000d0302004000150901f80d10980c0310b013a0001d00030f5040d6440d80c002108030310030200c00c2c552002c0240028818401c01000c6005145928180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289939307 1250 289938057 289938073
    0x20a0315051b090d061d0a0b011a0a090e1504051302030f0a0b04060b01020a020a06030c08010504060e042003100509100501080a140a061404050d080c090d05 69
    0x10803401031000c0d1101103009403100c1c144140d151052250440394424800b455040c2440716000801d19111080c000d81800d48aa00301c13410608006140c0b001c06540300304032074440307120385044010300c80c00344290a120b403010303085003031001d1007902110550589583c4403132500c0e0409244001441010f0445004082d0720b42810804d52110320900d400b23641c8480c1400c48940203441010728002800303062540580200d076110300020030251500707821980c4042c01052035045200101d1a03c00d6404001e50700200da4a030000e052a019440280c0544640d950344016070780718010320060320403603c26803106248100000300461a00c0403141920102c101e041e04c00d000820002924100c441c46510000c10b03a25400c0c0000342c4010001480c0300241c46500340030329031520380c42c03645400b030308100544010101005180d0030407045c003200c2c01580e40b2035000c0181090344034069160200071901180c5510812a682d9a030600440c04584034003590b0002c0341c07403d0016401c0c4503501c0505542120140300b4020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289940557 1250 289939307 289939313
    0x203070b1f03050319030b010905090405030909041202011b0f05160c0803090922030f020c090a140618070e0a05030d082a031305190c0f06020721020a03 67
    0x6401c10045000710001d40d03c3d2071070040d003c079800d007003205d13014107140c5041c81904603640c000b00c0000032640e084600c581c2c2e0340c1d500e08000e4110700c00d0500055002288004001c00c00c00303071126600441206a0081040e1042071003120050b41d060345426000c9040b04051070710740c5118400500703005145080345840781c05555a0340d803a404280e000301d4402e0704080355042060814030007003640300b450b0404078031540070600ca100001c0301a0000c007900b040790a66450b00c0d03241c000c01a00d580031102501010039458030b210240001c0215400100d540c0c140400420200c0c80c041aa8014080758280741d4440b90300d604005840c060346420070240c1202d1101c10000301a076003400014611030190704e8031007540c40c0000700c010700040c4e055a82801c91048048245c1800001d1042d6540300c940041c01c500c01c1c00450401c980340075010058000c9842980e07500c503040104505a07141290010800300101c9601d80c5000c5c0e88071080c0740200100b4503081d04500112001e410300c1c001c1c0c01800501000d14050301c03a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289941807 1250 289940557 289940611
    0x13030c050a05071505030c040603050603250e0603010902010e0130020c0f0f0304050906120115080d0e091603060315020405100f0806010c05160e0402120705010203070b 74
    0x100050b075064001c1441082080034880000960034071914102e03185140440340101b4900540c00303403008040c1c0da040028601d4908011400c03080210717004d20b012a01c924079035003014003160300072081c00485036004140642414062025010760584891f84030391078140045980394403445803101c2c1240250100301e155004002850b50346000b0301c0c0e0140e920158100e655103802060341c4a4890780e40a054132200900740030047da01074401c01c443ea08602d480c2c000000322802d5000032100000d500e845074090009042c5004d000c200c442c070a00344d50480c0350600081d00d010143c201e000390040034103400190080c9140011001620060400044150b140d4803059148a82c0c0401038401d150b00080c18401d600e01080645040c2c0c00310310780710400c4076002c2070044c14070b0406001107040c812140d552604001090000c4003914042030304201c07406030307603030882d50382d50f01c2c00d640981c01284102c16410003601d01160300b074140d40060b0010341c9803084543c0c5806483d00010f25181e110401412502071000f569 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289943057 1250 289941807 289941823
    0xc050904210525140601061403090c100c0c140303090d060e03070b18014109100506180403050f07060c120f1b03150f0603020c06091513030c05 63
    0x3018060001c01c3e01442c06030403484c0d500f000c00c00c6950000c0010401c0c181d01c0103205190b451002d0340252246c0b16491683e151001060182c0d038003101070500301041c6580001c203480054054034941a0343e81d5540303c00640458120381181d0150810401001c05091141070101503d105490000701c00700d60300503c90468000010888a1a07450018001c0d103100440c0710703d10b20701e014070081140d60240c071100c0460a031000c0744004240c08070185905000c3c040105d46543d05100805140c0c80d10b0440302094607207003840b03050b203a524030741008229a4140082071312075508a080c58800180c44a840c240c8003900081da2440c14514108956000503113103008050700500b0948500341c45d048105001d20070b44050141d48242c4d60b1500c942e15415540c01c3c0c0070b040d24000340b814000341c4101e1503460000080314640000d40d91050700400010129491383c010074461100c101590056200e5180c1d04d51602c0d01103400390340c607003480d80110300349641200d04514480d1181c209203481c203100c0d646441c01d001c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289944307 1250 289943057 289943107
    0x504080304030f08090303040b07050705060108060714040503030d020f04120b0a0b1e010e061209060610050403171309050a050a06060c1e0503090310090c0509042105 73
    0x2106200070580c00401d1810206200d0030444d42918006082aa07a800018400b60000400c1d40100d09214003030000c032402d951700b200c02d0350155030311b07003241c10f5542d4000d441e0700b000160b881114145018800e820b6405840005002c0d500d0020030b80340e62300107500048100c2c042114108400584c9800301200c03010b0091040c00f51080c5490849083c0d800c60f15401c090038000d400c4280302c4c610307481e05250b81c144079540909040c041c4c070320042c0c04118a406420b00c4100009662801d20100c1c0c0700c0024554820f80c800c0350205454000000100c0c2e542c00340d80b00041c03078000800c05103010300c0c03524005015000e1228682980030381e0340b601403009594003510540f0030b0b40e83c0c41e014070080307402d10300941c0003502141c1040a80050917039039050080c0840c0c5850b243e080e00074444a03080020500884005100c001c0448440c0025081031a00a00d104c20040701c0101c0406400a800d08000c50b0b40b40c8a6900b0400d206d0002402980d00040038202117080010424204000d0020f5030903100310000c0100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289945557 1250 289944307 289944323
    0xc0a03030c0302060f01080606090916060207080607050426010207120c0309051905040e0f0105070f180501050a0e240d0f140c070c05061c24120507090504 68
    0x340b8100a82014405428800990595401406004400030344c40390001c030b040e00d6425182e80e446410070b0500425026604030055124000240b1a50008003c41030301c0080d000d03a07017291070790340b400d940c00e1240c0d01c903150708800e002000c140e0a246980042d202c50b10034030005803074001c581c0e079009008145d00480c000428008450101455417240e00c0c400a0f0006a600d461240b80d03e1084450500c180c0c032803580b00d0ba48408901c101800d007400201c4003030500c40000e000c0c1e400e10807400341c0b410740f020b560395001401070b60b203405441891140d500c4c22907034180c68152400d0501c89049a40f003030081525a00080882803401200440e6000e416041c0e084c52a0f540d01c40e00c40b82d0400003a51b141580c460305d454100108184034403840045113400c902490300c0142e4650703003440c1040502051703071302186e4411004100440c0c2e8120008040c8081000e5003410460110101c007441000b004885c11443c0c440202c2c6028440ca44507121081c0d51030740034008843c08140d540c0000015508100c9084a8400b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289946807 1250 289945557 289945577
    0x15040506031014040908090d03171006110102030f0403081f060f14030402030705091009020316110d020d0f090506030114010216061d0f0303121503120f03090c0a0303 73
    0x20403000543d00c85042c00c0f54244814071460701c1c1d469550040a2240703204a1000060208050103002c00b00031140d00c0c0b0070450000c2c60100142a41c80e1482e21503040402d800500c40317581848184210307032060400c0145040c1d6500c85131011203011034001e01d54100040040c10710002000c100c0b5600d0001d00c029030300c8520400c0562001460700480240c0008101d405200788001641e011441c030003504c10940d020507681c1d07148080c1d00100003607903005c620100e00c0003080c0302c00c1d082e024031a10134083d05900c41091205500407035507510002481d00c0001600131403441d0160a1007121040c000503928a8110802610780001400f0f030361003070348400342d600614081d40245580500c0508501910484286d403094a0840044e140c4c80c100564500c03000481400429a0364455030411a4443c0103001c80792212080003600105100941e0b00d0001c20321a105045180d16000580d06665031040404a0606450402e9140c0d12380001c0c1105290f806410141340391521607a402800a43c001d40d5206126 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289948057 1250 289946807 289946819
    0xe06070506010513150524030c0a140f1905091206060301060b0c07090207030203161104050a0b030c06090409020306090615010203090604050d03030b06160506090a050c150405060310 80
    0x282c0250300c1c001d05154100020300d03041800b283c007004125a001c0e2518a003504404190f1f06031310704030001e111240780004c424490811400c2d0098102500b29803903016a1a0ba0500940200e0141002c009054481081480d07000403803040c0b00c100d150000d00b806c03810320018070005204a5810b030800c50140c0e100108100c031928090080350010040c50300158a07182c0d295070042d80743c1ca2103000344407070325030000b8003002094801c000f26207805030b1030f80341400381403804d1078150120140c102e04181324500f813202103094070442e807203a07040348140240240030819500c0300307000c215000600b085604c51340c0e0b41401405030314240031051046d0307406009080c0600e08056404144c8903042c090302c6c11980240200215601c4500850b029564111040315441100d490304070050400116003680200c804104c03030324504005600d08135031a00c18401d588031a13035120003442c0c6e1b4541e074410103496640440c182082d1424803000070448614030b000c4c10380ca000d840f00017086507076209403040e01280e40340f10003c00507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289949307 1250 289948057 289948069
    0xf110409090501050f10051207180209030d030e0c01030e07150203120f13080705030d090309090c021b10110d0203030f06030c0d1205040911030108150c03160e060705060105 76
    0x800761040d10b0351480e60422081c194102046c0c0d00031b890141c4903449506040c08000c00109005000d1048400180c182c8018160003030741045c4078107400385c410082600150390003030140c00c0c0d5050380a80209140590500114003600b021201d84456008035680401e40c005504030b40c0100d981e141c0c00a507135891010b00e24945103803004000c5800302c0c940d0b030305003c15001924051940141c00040702602c844050500342d0540c032580c0c507a102203d10340303905c6204150708005601c08503000031000300804a40454241e8840035205030f051030300d000c1d0780042d003440e240000000040c40354514010b9202d900c4090703001c1ca880c10103000350015034000310802186603a01d0301c61503404441540130745145401c1c40085201030b42510f40041c50000009039210f441445001528000c00314600c05210142158022480c50791081c040c59000307000e403803600d1260038200c15485000b1800c04034a5442c0d555000e00c081c00600c030511541040000070500d03940955207141c0603000c140e00441c0a0189949894100a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289950557 1250 289949307 289949311
    0x50f01030c1a030a050709080a0302060703050108070e0c0a0306050a120b10120b040611042402010e03041401020a0b0406051510021e0304051f180f0501030f11040909050105 76
    0x80414181902c40c2c120182c5906590300802c051802044c5500d90103010b1703401d9807240e005403826120746013001050543c001030341c2c0d020700155101080709903261403096031610903a000c1c0d03581c3e026046001c80c0d03040b044500201014411440c0015103162107400060348030b405640700ca5001d00c1d000881d80b09018040c1d4806420080c00014000814034011440b07105022448000d803110504400007030038004150001c0480904160302c083d40c2e15154403400035444038011204640841c601c00e0310b10780c24014400c440000322400d0056052920b0021030414440518400038114081e06140ca40000d407029640f034042c903c905401310342c520b00b8200b0500c00820000074103100352040320420513020b402064000248846200507012142c20011181c5507118590090317801c0801084180c0309100c000101d542c62508580e50820210690010041e862503613000380c0300100c4000c41c013001158002da20106641e02c004901103074425802c0a0121180c2065000700c042c03584504c0b480080080c01c0c840c040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289951807 1250 289950557 289950569
    0x5031b0604171006050418020103091106031e13030c0b0a1517010b01030603082a0d0201020a020d02120a0f110a080c0705010c0f030e060d0f06050f0d050c0f13050f01030c 75
    0x5207c0003c0500c9401c400b1036000a13060641e0751541c1ca040c80b6a14204030003044026052554034100680c0082e8000d408000ca10180700c07081000ca40d8400030300c042140e81c5070f056610f000030704036180c0351308000c42006044103120590783c0020081e0400da14407001d00034504e034483c882004119896403400e40700030b010150304240c50280c05000040920080e00d21040139028098101e00c10101d003181d000c901241c03410b07941d00c80c010309400d1041c2c0c1500102083d80c1d0580c2519810001d07040c050340c0d20b200d08400c50382c5a00c4140050321030a807060160100180292404203403060942e050310f82405005c1c1400d84402c440001d00489000003003080b800240b0707007032804151600c100d4a403040c4400c00d03100b0003401c02000e10f901c456035030788100030381e0458100914104442018203032110000c0180e8410b0764003401907034209588500d02030320100c0a8130303040340160040000010801c00250092604541e11041640c916100404148141485035041003181c001550560402e112031078070a0303000c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289953057 1250 289951807 289951811
    0x105040c1508070206042019030501060f03110405071b0c03120203040303020a0f0507180605031209030634030e0106090e070605090112051501110705031b06041710060504 75
    0x3c040790680c0010f4042d40b01b60403e0032004030400c0156014007098202240d0f42e801510703960303020041e00c0701c4945001200e2040c802000790391303500c60391040e440f441d92101406014140200500606158000551050152802043d00d041a44001c1d25040088606544401c941d1800b8030400000c406402c4064050740029800c00b881e56800a40e03d6150480080c01c0d450030294100c200242005108084d04611803229607082c00849903000614551242c01d200b0b1058201ca00740104030281221f4592030040e001e806141e0320082c036490a21107101009580e0120141c618071540f98480c2520f22200b2107503008505459203844080c01d54803541c10071120545002c2c0d02d210008400502801200c85030b0508948070010b081c010f9401040e1082108032140c24081048100030303c00a40d0282c0420036214012006514090181d035145d6038050310340c0660188400c2162040210b00354125101e000b0511483d0548071981c01402c10000900781949602950540d02c1b00c0b00c4078019480500310680d42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289954307 1250 289953057 289953061
    0x30601090801112d0a1716051206030a06020c01020702012601030b150415092406030e0c060409050103021302070b011205010e0d05180307080a060c050c0105040c1508 73
    0x104140611413030b22030416100707840c034007100f511540b02c40841109460055031a11201c1645020388640d09250100c21068121030014201d12079416540e01d60345e6143d80c805003802011301404400b9140034100651601c1040c000c5000125140024608001d003940050707214611440003410501d10594660190318140304e06883c0300076400c0d0080d04413a0417040c1c620a5403559404a107000a121403d1900241042081b2105003003405414088030306444003005408800600754000c0540750685402c04040e9180c02c003d9588640c201d200b0440a0006440c80205071000140d000e6015a00107a0541d8583c401001581360103204004107620240701589807403450342d00c58410791014060444035005094013803090040c25800500c0a65211085816000d6000b00c0680b40350012000454071a9031488000002c0c2804103d041c1219030205c0104a0309000d9a0344d08054445484900e0030840c007400b410034804802d00a01e8007c0e4000d960205429043c017000e000721400800600e418410340d981 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289955557 1250 289954307 289954331
    0x619030e150c1207110307050a0c050607031d0a0f030b0708070503040b1f0b0c15070507030518040b060f0403150b0907141b031c0501031502031f0803030601090801 72
    0x4807943c400307880111020300d544182056031680e16440011a0600c000b0503540d0170004002500b41d65a8001d50010000030b56034410450584203650000b000035429079110010f00741c074a09100410035009160300011904c0364182803040b081c83d4001c0d52100702c0002840203894110407225046101d510b040c80c51840c00744c403641c40c200c1d0041c11481c00c108146248618101c210342c040c402400303000300c02e10307034070103400e0300d1590340e00e445950086500401002196041e4040c801311040c981d81510348038101025980c0540c0d09040e1592441d8116881c1c480c645d0f00d0360b03913500042040d50741c4610001d032128110700f481d0080030450108186d1302c0340340600e0780e074543e0750702800950b10100c0380c90309034a00041c41184201a0096041c0192290030140003540c1000d400300161000d081d00b00752400240200c91a060150785003840060710034540007840203504071140d0010f40d80110f000742c0c3e6101510100320f2030900000e4980c80941c4642003c024030019680c400c0844000340f03244002070080c411500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289956807 1250 289955557 289955581
    0x2070204051b0f090102120a081005090613020913020f0408010501140f12010f180218010312050a050c060403030504060f06060e0607020f0a0305060105090c270619030e15 75
    0x40c01e404940f0b400850354024580c42080f0b80c18030380642c41c02c00d540710703200f1400c040c0114030141e40482250807591808101e80c1414100c5610414006080301c20030382c076401c82003001794803c0c0446034100b40f4900313401c0407544075400100003900004508684e031354030b8010018210390068020240035000c81e0f00142c02991171000900f600307030044490800c181203400e40940104130841143c0d0f040c074201110880c14500c440341c0307008452b0081d111040000c09105450451080900005010010622071030100522990143c01f2a4046091551409180603c8640f80140c110780c11000240c44000304402c000403801020b05005800f502400301904149001e4840200ca00d8030300d00031200810510103545d1141141e0000b8100034158040e55512400e01d26210142409100c0c062402c60022500d910141c83c200c1d556001c00c044000d02c1400d516848030a161003441290354421000d1000422100d120302403030b458400591800650504154a103a081458140c054401180601c003081100c40550b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289958057 1250 289956807 289956817
    0x14100806040f11030a18050a11030a240c030c0914011b05060702060916030b0406060308130305160503061305011401030605101502030901030c1101020d02070204051b 73
    0x160a1280040ea15040407400a011410402c2125410010710140340d03803000d0025802a000303804140302c1c500440b00c0050014140d07810081481d07100800460208203615040c0800344002030039a011002c0540311580c4078492442068030003c1200d2000a21180341c3c440d03072441840390304080c00030814125021b080b42d80315100e00c1e400111650304500e9160701c07600c5401c281800c01c3e00c814004403100e0500503510901103031110050310440000c1445407070f000403800745058074000d2880180e8195580c50880c0800034000316507140d00d541c03000c40010ba008000d07062a003032103407904d015079245050040c905005401441e1619404078011700050b140403a09940c440c84015920000311131a00c0c150f4010210021203040300c03207043c00080104425a00142e001c2c132803581980c3c0c00365450303c000081203200f15160303d015900410400c40d03254041d4004c124800780d40d080c00ca5902d10034400050aaa1001c3c291610ba01d50014203441180317800c0c401d46400921317007010414603041c10701c0402c0c500c1c46a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289959307 1250 289958057 289958089
    0xf010e1e130e010504121418031002040e091005160e1201050c130801061d04020d061a01090b0f03040f0606050d0809030c0f031002070606050a0e090714 67
    0x5010192019900d5180300001124042441003114201e41e40b5028028941990111160604180f0501c04107110788550080401201002450543c15280d170808a106040506805010300c40050341070204074800352008120000076607195140c403010700b6040502c0c0514001d10035107050140502780d643c00f5100c0c8519103003400c00701a00301e13800c0b001072010f1040600e4120658241010411400c00e000c0191034a807500b641400d11440e01d4810a40c2602d40349d000304d21005400c540703c0380642d200060040d030000c0c005081050441419250301083e101c141b504000d031b8050808841c1d1565038000d0303c0c80000c01c4040c644900300302409086214600c00070340054042c841d0b0b9031020061221703992042c001003800910510400e04113242c0501103030840515207201780a0380000085d0741c18a4440613903002801400b41c80703c0c1001307088001c025040f995096a804e23684400c081060340314210410081c0c6411504c00d84a842e099805614101603a00040032071141a00000115103402e001d551030100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289960557 1250 289959307 289959349
    0x20103140403020624190501121b0e0105120f090f0c0913080c1c142b020904090b09010b120a0204051504090f02031603030e1c0f08090f010e 62
    0xc103100c2c1d0300d80d00544505035501038030507000b00313600c1d050f502404007c0301c00a807038981c81a07020424040c111100c0d020f00300000d00d0071542c0109820321410980b0b030002c205051141c00c0aa0b08c50b10303074200e25002c40d180000c2125000601042c2036080040f215580b841000030520031070564082483c0a01c0034140418610b01c04540c0e00030005020296525254030a0865100c0901c0700380c0d0580b202108000540030402d11000e01e44030060340801c50381c00700220030a1100c5401483e40c3c04c050801e032814060103659003403262003240c0e6280d004025005000d14003070904d5060469000c0d0855019a00451203004001c202064400012848240154048500140302c1d6141076600080034112400c41d6402480c0c1002502041321340c02c92194010b00903000c503540304440303440343e183d0700030a8000a0041540034103070312120710b400382100000a01550318441c4071129a40c035903500450208044031030040100f11b000150901c0c0d45400400d040902c2c00048005580f4049580000828040e1072451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289961807 1250 289960557 289960591
    0xa1707060e042315032b030203010b1902030d0911090c07020a0b0d060504060b031f05010207090e0304090c0903261206010201110d1401090501150f0216030f0201031404030206 77
    0x2210a2a1108130081c05000e859180b640c150001c5403007844420100c01c4a038a9259407260ba51203442928180d503011801245400200301d60300c03200c143c081102d130b021480100b050200c1e02d4124021503180c0361080c200142d904d40000b04000400031f004052800c01001800008007503039605407043c0c21240c510200c95683c0c2c1507a00c6110213440149c009a8006003012000a14400214011446802102c60401d954050b0740010350701c980b0b80388111801030b07000d000103120030b0840e41c0c03020a401409004480ca0241c1c1c4e040b0110968511a10380700c041000d5001c20004d1082904140c5c5580a0301e662030049400c17210740c040754078000c0e900090242c0c44001d00140399039000750b10840340c4e40303c4410466140c04030710851001408160544140e540b620100008034120140540c6050301c0c25950b07202400c07100300c9011601c0121038000102148a6a0f5103e00502c0f8059200000742d0301580002d854800680009025280c2c540304590303122010b40204000b2030303401310341941c114850001c00403004c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289963057 1250 289961807 289961821
    0x9030f210908030103150603030225150c0c090603020a091e09050615091b0705030f0403260310030b19020c0c0120100b0a1707060e0423 60
    0x100921a000c03914149044040814003a50b00003460480744260321400303410100d21031103c16140030b444014056800b014040b000c44150440d103c1e40d080030000c03a0414150782c3c4c48154000c072401c1d0311100100398020440401e110b60401035038041c01d10f140b0144545d44c95035000ca030780c000c406e2007406072556032042085d0b614041104c0348551101c0341d1105002030701060070950345940d02541c00c4007490441305840e0301142010394880c0e10502140c0307002000d52400c6a00c0e008254842903040b00c1c41c0c0000c105111440d101c10713000d000610b0203503400d940b95180310346a0001001034000c51002d0b1142c1481000f102c450759070007080940e54886c11680940e04c0c0c1581d240c6150b80240400b003082c3e4000b041100b5501400900c0c0f900c106002d07600d14664202c13107447d141c101891651100503a401c0f003031044904202c5504040300d20f07040a012000d140c0d41e00e0115042400202d80d4202003500302c4602004003903842000c00d1040750302190104211190b01d900701c03250308684e400000d450001c5c5400a520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289964307 1250 289963057 289963097
    0x1a03030c190809060a0806010806030129010912030c0318051c0c1203030504050c060c121602060d050a060816060c1112071712090906030c042c0109030f 67
    0x503c6000c0c0802d51156802d240c05030406008035082e50016601c44006140307031505008401e0100c0d402000041207113072540950082803a9049564180240c805000800c43d040312203641c1c1160003a560243c070002c06150007003140741c022100c2080241c0d0f44100748041e0f9213440030030b1036040c1030484158171122280307040c00621034203a01080e0840c803040514002d064054204c1c0784070301d1048040d070341d4020f07140c0100100d80c0034008603500541e028031380c0c12041030025402000d0006000004e048590b403103500040130b50340b00392040303980962502c003400200e034030710b020f250054403000008d488030f10750700c00c2138003204141b070300c19082042030700541030050002251490740030500140c04550f0920403841e0441e95070320244a00c0e8500e00c0d9000d42c02d10545800f00d0b00c03e01d5025004121407820610108105181c0300107481c259160103120840c2045586510a42c80c0e44000d08403245a400b19903280134404076031000441900303134106652403000a41c04094070982d5221410b04034468400c2c48102d40c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289965557 1250 289964307 289964317
    0x703020414210607020703140304030b180102040e07050c010e07080c01050a0e0418120503010608040809042c21040614251203020c0c040f0902040f1a03030c1908 71
    0x8094081c00052000075039011546c43c054038000d048081e4000a203104241d0390b0320171880080c1c60882004080f4401c00a00c031051b40c85c1c12030503030025090a8507440039130006001500c80d500401c400091040340d245081c00303504024075200c2c02601540c1d240410440d15802001c2c0b14604014000440004960092f090000301140180041140c5441103002c1480d500580300152a030000024000b040b4a22601c00c43c0c0c140c0760580e882c4c281649a6030340d8a500c0350000c441195006031141c0c00c20a0f04000004d8401610344405080442c5a42040c041070a0400150075004044000d10031500c6030f90040c42103d084880c6071070f011840240300300480d000e5010700051000508006405030158820004401014500a400454005482a00c01d07070803032203240f0040103036402104030900c00703140030303444038440c032030840c00101d0054a08d9002400b12078041c1031f0920744540d038010701c5120390724051841101c0c0b03074180d0085d4500010700401071740c2d440f000c1c2c104150300c98140e054a01004400c8050724 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289966807 1250 289965557 289965619
    0x10091107060603050d0206090f100b13140f0601020a0f12090f0e010f06080105100309080904020c060a061a0d09031b141002040f050d020a210b0703020414 68
    0x442c1c9a281e140ca1526010362102580c010312079540450000040400c020307440c109214001c044011004c0a0311000e40003030240160311417210a26100280004d010340e0240c528030002944040c940142d2400305880090007450455210000c080700240b9201c12028041d80c10886490040413400f004850411640e0400780c0030851403500000c5d02070080921764140e81e040a1040740d1fa070b44400003183c0058091241541c080a001b00c4010303424042d81c401103000b40205607c41ca07028240000c20145d078498545602250f000b4000c01c182c4051034030410000c1c000f494001c090342035041c500403003c0d00520300c4000006030303240300d12010036000f5070301400e40c80c5004042e44190f03115170816419000450341c1c4549140102003001070000c000344200c50580f0002191403485906040600440c0b04001104a801141400021444d1682d0000900124603c02c000e02d03291461031800d224010400780044081c140180014014004078151541d1204002d98902c0c1c000c140c2c448000704002c50104540d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289968057 1250 289966807 289966811
    0x3020906041a07060f05060a0902070c0e0106020703020114120f0c0403050a030c030f0807050d020c010b04090803100b0405030d05030705070c060e0a0e0c030c1c23010e1009110706 79
    0x5a40000715010207082d00f58000c2200b08022040001c50205483c400c41e0141d81c030494042c0184455011940504555405a1510041a5161070039000680e9083c3c00c844003613400080104110b607440300103501540072002071142403484800d1507144094014004410603c880c000081801001038161401503400000b01c0d0b01d094034900700508a121203c1c81500040d00d03900305481510b000303103016030240c043c0f0341e6003501e01403442e2000c800940200703100103813554a95801c1203407560b9900443d140c030340c0104c92143d0749003820055403503600c00940c0003800d8440203000070042542c0214100391a02c50a00340103669654184c822242d0744201b810040c103800c01c145012600980c40110804400c40584e02041203a44900385201c0c40002125000b0007000c003000001c3c0e02907003803409816041d0314003400681c1511840311480903103c011050070b00138001400d05000011780041c0039070040c6140d40350195141003a01002c03607001164000c43c0325040d101d00d141107001c0c805108a03910141c0109013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289969307 1250 289968057 289968089
    0x92d060c170d0f0b0303090d08031b1317060106020d03090f061a090601050906031302061201030b0a1a060316050f0c030c0d080601020d18030b070324080a030302090604 74
    0x41c2c0092511981d48090340c0e20f002154840303824000116a45014020300328081da0142750354428499000908246141c24010b0700407515224010140111140c0409012110740c14000c580d403413070040c511440c50f194816001000441e03008503254008441f00d15010903140f01504040f09d4048150074000c1210380782507001e00d04c0071403041c0d085160f0700c0c017102e010401362644401150035000d900d55030355000900b080811021110110102c0c00e162000e40424104a1220414081800264015140a00b590080180d002901e1082000c5114080b5135404c0d100348440101d0700a0000800901e8400d5a11070500300140c01030007a138001080c01c0c401c0d030350380361031015001c2d41702d41001d02074051912030806041707401c901902d80c4510420040c0c0c000d00220b289214203c84100342150245100c00c0003100201c040346400c114180308080544012507010042140000e4000c4c0110b8496001002c0c003405010201022030212a0b5640601d409600c035045c0d41d000070300c3e901c0740740d00c80340f0145807441c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289970557 1250 289969307 289969327
    0x70b0c010e010902012c220509160b0304051c0504080d05030c0304060f0b060c03040303180e0c0307050d0c090302090a090308060607031701030b0f13210c02030d092d060c17 76
    0x4020025280e011005e106546a100c0916921491210550207404404034103103c02f04254018680c420700803012a030040f011944840404441ca594036800035100050500440008102c0d901210019142042c40c5103070100710b10156000281008241e80e856041c2e000300c03031580340c104000340d40f0b00501a80c1e580c01141041c41c0d40368440d110440204080a20164040311441681c500b141c01c0f00c0c0c550394485e41c0d00c0c59516103e6200420400902c0000e1100610414803440b07044c00c2650f00741c481400742801d42c010044500d0300140044152410f2a1511300001e602442240d0080016940d80f500d400c4a854192040440203d54008101c3c44000000502c180b96207a103025003820a5034000985420b54080110040c0e41c00180000203500240391140140d07820111584c4c181d8a0410207440e50b030350019040507c001c890200041c0340c09024454602d1180c07046400240c0d086080241602950340800b070b0b10300602c2000144032144400001340310000c11552203850b140100341c0e075600401d0b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289971807 1250 289970557 289970599
    0x100201020415030207050c060702150d06091103131101020712061a010513061808060a09050111040f03080304031806050a1403091b0301020903070b0c010e010902012c 73
    0x200c503101e2400c0084a007111198024800c41d10305d150480302600d00c0791400801e100c0e055002c400100d030030030741c01950040d40580c4031001d0603490420030408a00c40b803621880d1000c1e01c5104508002c0e4035000c0061000100540001c403843c02d91210021441b1010400145d04210f2940c0c40070010b890008088030800500342c0c02801c0d0005541640707820310740c0030801102e15000304e07201641c00741040202070003c0c0d809410500d4a01c001c101c4c4000d10f080e21511814100401510814032030394480c45e080080002c00e01400c4000c841e00088281000d00c5c114801d000f990182c44094955400000864289480f8140e0000307050a0f0140400740e0341d5a40c9002130455022005001c00982c021031103120303154007a82221701501109008006036202c0da010b158005544581450f8159402c0100d0000b5840030300c8071200030000d00010320349a0114210490039222030442d0084d882e40f4200035400140c0c1c2084d4030396045011000c40040e00089507507070b21203656440c40b0b040ea001b041c1010942c1c010410b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289973057 1250 289971807 289971809
    0xc010c11011a010507240e060a05010605090607022215080705031209100c02030d0e0109050402041203180f0b0406110c03030406030207030e04050c070b010f080d0e0f1002010204 78
    0x204000700080d0590000e40c100103448070b900b03580060420001c1d4400b003107007000b40b02e90a000b641c01c1404025070310300c1c502c0d04480824803103440c13982060003005401a8a481111b004142e80c0c10101d15046028000406501c94000002e10402a2a1800d200011389051035491010740b00c80811204e1403c00c04c041c55669181f29500062040420100d0641004a00300d5014117407503000c281402605800c01200060100030f0000f003011201610f005650100080c2c4603c0d000c1e5164056061210390004269400c0390308801e00690041001708a0f40c286034040790b5400c0c0d0589801c00162541a4207413618040c08e50148400e0703828000046110340280d00100200c0d0216101c0b414a8041584029100c40d060b104041d4550818482040558001c2d00240a6107210b0f14140d20f410916038001001c40c0d4040d06d400c110002c004c03d940d420044dc00c00424050301052602c0b00002e403410801e2959a414100d5410070070100c440e00039441c5d160240d0040000200900880b1003420800c0020700035001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289974307 1250 289973057 289973087
    0x906010812043308010609050a080a0b06060706150e1e07080c0d14092e020d060b0d0b21070528061107050a060c021002030c010c 57
    0x445000280000340095561298808050210704051a04038450ba10990a0b0070341e000340000c5442c044162040155100c40060068a45030303c01d5040501c01003042000707800a9010741c00c40340c41404503d100140082082d030340300b04814495a1010041a054015490700030003045c2032035004000041245031071300690381d800e000c0c400c0303070303500c44011409140c50019807078080c11f82000410145403007030003a00e6010700c0c0101c000780347c514911400b1080710f51003602401c0d181098420302402886c1405118207803c18207005c01002d020702c1d42d050b01ca4007103401642030707281d50000c1d201120341c860f500a28005c0c4a001d109540791095000c164010b040840c659503c120600a00030250a81041c5094441c8030780900500c01c0a05040900400010008401812000e40b842e400840c481d1042e031900079050981d510b103400c22501000c1c03480c282060300b19911503120002c09101e0150311800006500340c0480c0d11418840030040181e080d40309038100b41400d0350070181203500854001865112040b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289975557 1250 289974307 289974313
    0x12100602120f0d1b021c05180d0501020c0a050604050606040e0d12090209041b0806070504060503090a0506071106150616020d08040f030203160b09012a150c090f210c080609 76
    0x20b401e02c000c4031f452140e00305a481c0d0441126088a4604100c6503900c4010310840006161480c0351b0006c5140c5400d0202c1103407954030103420007082220034031045800c4041610300344202d801c01142c058445070520a04400c02052034031802c0c0003a640c0d0803040038160050094102c60803d805c010102c2120f85400800c1e41100d450b001070034040005800d40322301e40703a035259401c040c100302c000c54090780043e140307030803512a646008000c10f0080c05214007480c515101c0c420503420001d00c43d400c0000003007075031843c1d004184982c1501d4a070f00c1c00700c5070b403030340e031111007910303010f0030380b00060380e84066400203010354034007040200e2030881c40c0180505485c021422600500d40b820f11710a81d0070074600a00b44100d105101805065009165508214070f1400311074821811340809040c1004109005465100005440d01040d000600c100214401140791101842d4140240030316a40440d21030780c50411402680144074420300540721111540c8501b002c0060342e90b400000b652410305a4503d000742c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289976807 1250 289975557 289975603
    0x1f050d030504210308060f01050c07080d02060a0204051e030a05010608060a0609021c11070803070c03171006050a021006080d030b03060f0610050d0212100602120f0d1b02 75
    0x5421100f1211440b6031660301d1050300da440106100b1544100c101c0b49060180510030300c04100c41c01d00441d000b81c00d9001c000c2c142004a084003c0c60241e000d804a0309440c41008144240d854044002a4203007071160b90b954140103034004645402c0708200081c21325403a210011400d8240440d2003409454001c81c140131039500c850b4114202d12942c03d025103040c00c103400303200358100150071a211701e2941e5008a4204a91902c50310400d5008032014400a1031080c0300c54101504130010030840e8000e0640d000580ca4440344041e022030707003401940240900885c013400c441d4800c00c185800042030020510103203a9920016650700e0360b21901c240440d0401007000d48031300300014514803c400148140800c0c2e200d16082c440c218400c010310308100b00c2d0802100e1151100c500007090080c0c5005a0003010b40360402d0314a01241d1203800010031500001001c0d8460304030841540e09001c40c0c0c91001c1e81e0340e5002c9020000400c00442011402441c40f0f0b03501c1c114035004600c203030071941c08910b40e400368 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289978057 1250 289976807 289976849
    0x3030a03090b10061e03021b0c04060e0c0702010c060b0a12020405070f02070b0901021c110d030e0d12150f080607020307032a060e010606110d0203031f050d030504 72
    0x9500f41c1d009060018200d0b880280ca04a0b011112500da6403041c1001860f2055a4024206000c074401072010141d0001040503850b050078442e2100401002c48e40318910b0514404100844c8101c11010b0304001e8804503a0381030285951003201000d1008207403205082d569455480002044002640314619000006000601400d8110021071103940580201070410070030349555003003110120304500c038021005003078011012444603002c9541e1903410743c00c810882810700e0010340240b040209414458400145007001403005082c045604103000d0708190102442d00030090000340c4802a000c2c02e8001a41d80b9480d4004c20030303111000e0960305d03d44d039a464266580e01c144140140025008405035001c10341582d85107001c0707101d075042c04500260945440042d03860801000c040c69558410801109400414a5051030000f5010340300e204c5400f013000e512804010084d0f6411011041c01e070203c3d4598a0501c00278040082041c00300254a040040164000e0301500c940c0071240161042c035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289979307 1250 289978057 289978081
    0x402040b042d02070302060106050c01140c1b0706120b040e030d02030f10120807110d0302010b0a050f09161106040318060c02090a020c030f07080703021203040c05060a0e03030a03090b 81
    0x1d04e40c044c0c00800e096460040c00b143c0e154071000c8440c8481d5620a801101d8400704c080c03084c0111079105616480310740b8400201e13586121808030191301e600c4400c003080b040b500440c41d40306c00c1f403000000180002c1c2d181c0c0442e0282150b801d1043d150700002a66000f00c0c4c4c1d195003c1d500031039203044402001d50f02c14100801c0000f142c0030b82401c00c000400c09a000603094802072060301c1c403d00e400b0785030380c8009020036606400060100d015035164103000d8480d040c010308081c01848200e03035100401c0b41040118241c41c5001e442c040083c00c00c2e035244038415000d04172414103060140304444491429041c01001c8001c1001d00b410f51400706400054281d103e02201c120954000300381861980741c1c070720824001d42c80304041d01d43c0741c0030601041c02c1415220000e082c110380070703000c655500c010618000341001600640340f94940340500900002c204007074282c2046d504180c8189a07140e040305c40590b00300400081c1e50b070740751000040705500c40b82d0580114625512424036280b013601d45402e840b40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289980557 1250 289979307 289979317
    0x60e0306070e0402031306150503060a200a050c06040804180203010302062d04030b0a0b0904031b0204270c06030506010f03110403080a081b120705030402040b042d02 73
    0x30000e019004080c000f890030340d00458102c0324600c00d03448042041d580700001d44014250352180078009403000c0106080900082d98001c00ca0441004000a090301050043d200740c07481800f0003502003180c0711501c0c082c02c03c42c0c03004603c43c800c80300c07103103441c0ca04514541e22034020010f84100c941b00c14500742034031f4000e0307034140c0e50b00803e403c1c1004400c001044400401007880c4040304406520f25078850103410003000a10b0044c4040201e61034405151700540e8a190609130240400c18100070203e50710000c280c0359000d40d482150345204040c000140601212241d154811840c100d07041108103c2c10003440000e80f00305104010070340e4410b400e500700c800c1200c600380412000c10402d0b0043d1300c00d43c080401010181d030745508040c1c40b5207441106810000d07118001c40e60200034040240360081540e5542d04078440c10614020b90020562402c51024188009100022000c48c0843d51650030403820400040c1003004540b0f00c41814229010380780200040c20303140114080700c007039030758002c0754 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289981807 1250 289980557 289980571
    0x1b09020f131e0314011b0c0b010f05010c030f12050a090501290d0311010e16080708070b0307020a060f06091103010503060411130c0e0a09020a0e010305070207081501060e0306 77
    0x10b21440c036544070203040c040e00c0c24146070036569078410310415030b004c0b0705180c0c00c110441d80c2d501c0d41d80d801c5252070524050107030407000300c1000000d010440c5a0b844540d8070240c990501d04a284205001000d0710101d116048501c195401c080030000d04100d00e600440129010344002d10613001200a540c0260740c2121319002c000072038400340030250411441c941d602078403a00d00501c1407110205407030700b12480741c0160000364000510081c0120084040040070341916000340801601d0110001d42c4c175000b5202d014000c00f00400014180f90080c0302c1e8940190300084203000000714183e0b8003000b4001402509a06d902c1c140b00304003e00c002100742d905032400500102495100c41c1c6402054480c81103205a00080c02c03483e08214000c00d00400c40100019111780e5008040201004103070071103500f0a00c5801d10500107000002d90094100760300300803e0800040b103440d240d03030413820124540c00c61100d078420710314414002c1c0407900b0154100e607070316910401d2260000007019100c400a864030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289983057 1250 289981807 289981859
    0x80a030e030d051509340e18040b0912070219170106031709010504120609021f0f050c0a030f020c0607080d0c0201140c03070302120a050906221b09020f13 68
    0xb225034200746c07080542c85041428146004038800c1c000030a007100d550502440c01928005100401840700f0055030001e907480085e01c01c582c4200b0f580380c21401403903000b900c0b442984031455190180040ca81014010200b80f0164800418003190b02030642480102c1e4485403102c40400e4024904e002c0e01c01c1e10318145e4a59140c40c0c50040c08401c840e1642005441490b5940031440050340d4040c40d941200d260304035601f00c04155690007402e0788900944410038800e0402c0020f400002c041038503504a80d050404250050a04604900e403584151000c0e030024000518802031054050180034400e054900500603524100001c9003030344c10340c54608000b03900c3c07180441d15040b440300145a020403d40340050074000c80545c0740410b04e01c19100140b280c1c0c0d0b11310510401c50741c00d21207141c0c0141c1c0b880024208030142c0c1c12611340d07400c0340300002d0f00c1c090744100003152000041c41d50100815440301c0544d00c0300c8400c407000c0910b512071080e10380c007000003540004001c0003040104502c0001c24900c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289984307 1250 289983057 289983121
    0x41103190e12031f031407080c1503040c0302120c040510050604032612070f0804320601090b190605030a020904020720040f0207080a030e030d051509 66
    0x550040c0c0c001404c04841c40c040380640d2840b203840d0502c00e5005500503c1c02d5580506584a00b80c01c0000940000d081900006683d4469886603a41e95482c10b00c004802a42c940d034a013040712858503030f80c000039400302d00070000b610407080018000c20030680444c2e040019071141500d061480f111846455000303c014841080440d441c00394848000320062008030100c59140c009060a501410041c61000403010030320100a50110030200e82d4085820a68040e0605842e240707004004100541c2010b805200e41131000403201100a508060400c2100c046586a0710402c0251001403020b0b4024a80a16103000621456940504503080c68455600d0354490b83d20600c01f03548900302e0950019020040740c0001f0f0f408032135400d5040446408002080d90074400c1000b0340311042d0030300f14940d006101c0203000c42c80d03990403078141c031800741000030303900c00507182c035605500440918407280c40c6031400f082000c00b070700030745100c1d8440c003100c641c001543ca400d9503012002c01c4822440c0c40d11000c034a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289985557 1250 289984307 289984333
    0xc0c0f0201050309070e010e0f13020a030204051509010801020d0b0d0b0f0601112a030c011d010e0d15150e0f090304081204080c03070302092202041103190e 69
    0x401190800c2e82c51043d01d100c540c481d80042102c8000b80c8c400d81d000c04500080100d042d06902086401c02c03c0d507131aa0b1a101c0b442d8000803001281400041d11950391500450200390307100019031518407019003c07017550369603800001d000790090082280c007641840c1c00c052182c601081a220185c0c1d203c40302041d01c4e201c4800072401c1e00d100403c0b050520103050032300e50031644108041d410449000c40c890300c81011010000b03400101004845000c0d50110310840056030300240700b20b16021400102c20b0410380442d0040720613085200e0461b4011201161a40900c95250340c21110800c800c10188034903003142c104032100705200d11480c04842d840c98081610310001e0340c007080d004114407084908180d10b80060504010440f080105000000101008580400e000720b200d1510b00720068018a89913402080ca200e5000346100401001030300490031895001c10440340d02c6070094001c100c4281040c88002039a0302c00d59803810180500e039070138a0b4140c1c1500400000680f2607000d44202c02c9605 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289986807 1250 289985557 289985567
    0x5061309020c0a02220e0706050d050c0d090b0a0c09051003021803060109060311060f0a0804050a080d0b0108090f120f070f050705010f020303070903030f0e031b03010c0c0f0201 78
    0x3a201c8545008080b0b403c2c1c0544c5c0c03080f44200204017080031510715214030014210845070b01903c00c00058000001c00c0182580140a5807611102040c0108503a6540000203000d8420355885800040ca401400703070502c010340c109a4030403c0c3c00b003420020400441da064072010100e00c10254000810049010500d03c05d4020300441204202c0000900200c90f00080c20010300743c0280c111141c0d03805041041c0014032415465000c0c1c01d03101c0500e80f2a030210307002c0c514440c02c45010103000c4c100c00414200182048009a40c0f9044251075440340c000d800014050030b6045c006c6400100c1c00c0000c2000e0110204c1d004041141a50060070a4040043c2c401e00c41e82000c040020f00d100140f01100100d562003580080862141016115403400d0400252811004080c0d6104540c0180304001407036800100340c030203607901403c141a10205030301007280c58656603c040780e05400340038540e0707807255050f1440c440d0034401140280200e130b54941c0111850100c00c0d201030a2504005c04c1c42001d54019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289988057 1250 289986807 289986817
    0x11010513140a020d241a01030e0f010c020105010f0501021618090609081207050a1d0a0801021903110a02070e100f03080903010c0e06070b0a1808130506130902 70
    0x201d81590341002d03507500020101c0760f601400b622040300e8641c07908559240c1d00410310603c0c4c40f00c42e0420041d030100f121b42c106040400c110605040d524068105000d004000c20181600580002d00403900c1884009018110a02c00c511311030543c0c8002180303544c00890624403400080c801c1e07651440c0f070325074801001d0080951850300703165920003942c0803518501070700c43c1d0070740140180c81e51442c0c00040101e64032001003104040010910456140710390003661000c03001400421a040e205441c80000d038086281c0e405080d856200040c4507810284034101415000c100e520104001100c41e4129015441000d10f80d0f00180c00c0040181301556016600030780182028030b0481c045071b2a400199a510003a4000755a03000c808161303288680b07070034020394502200b20320384140c1c2c080c3d8201c0494a14025840004c000004500009500302c0342031340b00781007800703406220810407421410124800c2e8002d22070710b51903010340c000100d0141040012500d801c42200e10150415151030000d400035045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289989307 1250 289988057 289988093
    0x603131203110a020a0b011406040b07020315040b15100f2003030c0301030615030c090c02010f06150201060e010608010317070f06020903150919020a050d030306030311010513 77
    0x9200d14800d0032002010103000f900003140c00411184625041c261409481680039500d038080031809503c030350b02e0701c20684e411a03100c083e2031341e2130b040300340700080c14100c8402007121054022020030090200e90440503000c2c200b1440d43da40700c007243e071060011104034189040d012071380348040d00a5041c402e08600c004c3c5000c621841d07550722081c1e08038508642c020b40315500000c9012005100740401ca100d2500b501c8404000c1e910110701c2c503070307032540151aa03101c1c8001040d960701c03291760154000c0d0131028619804900402c100d5403203620425100b107910300c1b100019842c0c0000811164a0040686d0698102d47c541110682c038640d41c4d5004110008182c10b910031061144800241a031240e2501d040d22444000d80c8030400d003c10b1628002c5507500d030710303140c407a07000034040903100104a50441d91800d00c508024403000d80041510300d04c0c00e034401d0b0341066041e40146c3c10725034144e0180056911035510b42d981c100407445000c1c01d0300d0060311095034121034000c0300070005035541002c1030242e80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289990557 1250 289989307 289989311
    0x8090d03050d020309011d01020702011e110d0915020105361207020117040b04110301090206040909110a0e0609070306050405090c10051303020906030102040503160509060603131203 80
    0x200441c02d203050307030025580b00c1180e030b440300000e162204504000802c1904130000842c00c0c00c3d095000200a00e001c1200341800c40c0041a0f0070340e20502c43c0e420809130040e068100c07807415440d01030080c81c04d1014484c81c0f900781c0d0302c0c4040302e40e200d106000b0744e409030354020085e07501386d01c2201c1034240301c80051503200a000c03d605c0c4038215a480c1031204801c0800c01200c0d07151116150300000d41344001380a011420010888100710025103050040d44d002604001151211240d02010071b0042a030200701039441300001c1800141a12070340c0001034008e10559400b200300310b000091060710025030094020400d100c4000828038200b40c01c010780d014655103008a03541d5510300c0403030100d0741d0503142c0c980d071a00320408140050501c3c00b0060350401051510a140c0318200c204000c004a260200030711a40c0e140c00424903c0e0b4003501910041c00000b411b07210010400390303980e0100b8406100303c41c05041100c000904c5841c125094911030100d403174007460381400c540d03103a60000252418038020f0503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289991807 1250 289990557 289990567
    0x2093306130609030b0a09120305040c0f0305160f05030d12020706050f04030207170c04020d0209040501180c0e0d02010309020307080607021509010e0a030813020d08070b0a0908090d0305 82
    0x407603104080101aaa01c1d440416429814044006100141004442410140140005220704450314555403040c80c0000b0340391103d141c01140c00400782c0c08070a03004005280401072010201c1c1404070300451040d140d4021350b442c4071806070010b1510032250303da08000c40d4401190700a061460300419024001032500110350703501012202c0c20349070044203444400420081540412082000d03202c1181b240c80c444446010301656480c01c2103c450150b82c000c01c00080e00851a0161002c2c010300400900545d80c40790030165843c1d00c0541401945030038203800780080c2d40541c9901803110405095081061030781e40040d0050810648200d80502c0340e80000520703d03005112982c080e05540d4040d00c08001e851105280006014020060a0b4034020300d24402010014950002540c90709003500a035a40503198002c1016000000c0d4010031702c2405881000b01600007050708921807a460030441d01e0316101001110b1000400425044080001c3e100710f00e404240b004586100c0d150881c030300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289993057 1250 289991807 289991827
    0xb0703090c090b01030c2a0c0314010903170402010f270303050a18050a0e0c0408070303020c01092c0a110d0b0405090607080c090a0512070302093306 66
    0x144850340301058440d5034150f030103020344e858060810310798040d00d041000d9400c415801819101400f05d0089151641482c1804001541d4144402503410000e909042c4029451081c06401000300840014154560000d01502165403042c05035406039241c0f55002c1c8400d90640b070701821030a03515048040302c202541e000500c86410350146100340d40700ca0321041000b8004e04140b00d850718400c1c3c00000003006101d251a800d20350001c403008501640c3c06512544074240c2d035446660412841802121008820f0640016410740c00d03036400e0b039441c2c0000c2d1340c1d1a0381c8000603104169052040d810404040c012444080c19250405815200042e035010500c0c000320083c1d00041010051039100c00c1212202d107494851790f40d201e89048060401c43c07514990080060b0030042503202855004a0603151030f880f80403040010b020060103421181e95074101160361844184012442660800000740c5100b0322210b2544008041450012001400d40d001c280440f2030218019003000042c0b16a16034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289994307 1250 289993057 289993073
    0x31903090b07020c0406050f150306012a02180105030319031b09080f0d05031602070317031b04050d021309060203160206060103020304351306030e070f030b070309 72
    0x35401a0f00141103031400710040c00161542d07540803034403503141c4030001d034100d88521284031100c01a104440e0754075581d03040140d07110394483c043c4803841036224a038008034804581d519214540201d03440300030f02150700a000c0e03000030240103280c1c040e0820301046004440610415040003102e05000c03540c8145c1040c1c1c0d50741d0b21041c018600c0000d5950b07404119001c0203004184603960010017500b0001c0740c2c403002038203a02c0054007580c2004911030320b610502d84203000e0b4030b010b141c2c0494160001ea001040c1c50325142c1098034200c02d51f0f524200440c41300d48001003280c0480b0300181480c0c0c0d41c8030340c035020051118281c0385406012500e901d03030180065554030013907126403d4807103603092a0035140c4009141403401031016050520401c2480017040c00018901c0101104981e003100201c000c4007032140034a1000013032500030a002c5040c080014010316200149ea000b66400c009044e041c0700000d0b580c04040c410380b00c960400007810710200e000000b000340c0c092468140811000d0300c60380c074400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289995557 1250 289994307 289994311
    0x7171315050406140403050316111c02030c0a050102250e010303050c100239100209190e01061116030602130902070209190b0402181f02031903090b 65
    0x41e20010302844403640165031562000c05500d00c0c0760510b401c60b91843c0e5248203030f51070038684204120070841088034071041152849005004010b000300441e102c0e5a0685a140e0300700e01c6401000554511403d000c0f81c11803ca881c141d0080c1214140c9201c010f500c10581e01441031080c1480102181c40c4a0528840380250300c00e039121540c500510290504284000c2c8061501c0d45c010404a09400c44003143c2015180c500c00b1608850f1009030791000d0308601c070698141180c041d020b04010289115400f620700060709640800a2610241c99051040894010440300d43d441500500406106501a94500f54288110343c00b40103990300038811140702e940201d0309290005034907088101030480b03540007050002c40c158140f04603035000803102d0200910a107848031981c02d601811a1440d006014000800b46c001c5550301e450024100c0c8400311a051240104c007000012420340e0151071240c0f40c900141e41c041d5080c0103c3c240201406c1c03c0341391400040544902180c0042120044c40038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289996807 1250 289995557 289995599
    0x14040b030118050d1403014a0907050303120a1509050910090f02090402010e1302040f050907020d030c140a08060f100c02010309150c02071a071713 65
    0x109042e600c0c0c0741403450003668602c1242007002200c10341c5031480941d01500d064426402225890b0300008640c40c4190340b0b9603003501c40140d00c0212000a20b655036028401488004c103012201d6074410301d1103a980d40e00f610589425620800c031600c5880154400d03d40c00c601c0e21180800c089848000c0210440281d4000d803000c00d1741d603002d00c10001001c002c031402c0141c80410900c4041c1281e2100c183c1c00408100103409099810001801c41e803065001c501180d40080c4126050501115a1030081d089800fa00c9800b501c261000320305840c01c251803e20070a104e50060039202d00070320044000e05402c005031010720a100182003450040c040140040c0b080d40c0ea60b000d01494810108442160b5010016000362038034200c26904a5021082c0724003189c081c01c021400d46104e18184c9a0007040c1c84c1c40029145c901168080b056038042a108111602481c0c044285900b10b1080faa003031003801c0c801020491400d0f4803524448000010b0070f10301402e090140882030780c5a04440c100c2072080981c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289998057 1250 289996807 289996841
    0x30706080708070201051501051e0c0d091e03080703050d02340c1a040302040c0c030210110306100203070c150f020a0b0c070212010606030c031a090114040b0301 71
    0x2101c4a584941581e900000c1c07840240300604040720259114501c0e46070351410804001120070b4a20311220300010812080c0e11110342d10010121803e4440c9200501c07100042c0e4981c200092105a16441040b60143d040245000910b141c0d5100c0c00d0340e220040c11402d01c2010700c4565071035521417010300303c600d00703c91801c281c0008200034240003016600c40325220302000c40c00c19010984022445003030741c0826882c40700c0308240f00c0c42010180101ea10007540280ac14580310f041542c0410428421403281e0200d4624000800200003910301149942e80e441c1d01c2400043c40b11300c0d0100400c5d0a22481d401500c0c6000c0080d1904114002a03401c005c40909492500c4070b5820780c4440710340212811440a010106c1150f900c0404d2403001518040d10010041046819542d03003044002c03034900d0403002000050f03a40d841c064007410604514602180c54850404100d20455418000e0783c00c00400700c21050382820240c00e08400c0910b0142c6d0040d80d140c620317902c2c54a0901c10031240c40d801c5224 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289999307 1250 289998057 289998061
    0x91309051612020f24090d0c090c030b011b0605060f1206070f0e030307021917010c12112a070609030b060a0807030b0c070c060804020a0603020f0d090f0203070608 72
    0x40c0f0690b6141000118085c00314000c07500c80300071140c1d2218507030f40d5030f041c00c965880e4418070025040708407104024040c003840d46000203020070180e0060080703026980f0b040c00095001d40054076055070070340c140401800c11004000024503e0350145500c02401440681410b01c032401007403140c02145c600480a62001007807100080c0c001281d0404000185000e004480004c03001c80d031280601c00c8002d001c0d0100f0125285105416074001020308141090681c2d28401c2080c59406418500102000700b41948449001c1ca2014001d50403540544a50340746090354014280030f0641046c0800044c1019803000311011080a0001400421071aa0750004007415404e00b5807080c00c0280100c0d00c6400320250030009084007003940c0084a82000001f513040d613810826192500c21103200402d40c5c008010b0100395035411890003402030b8004c0c1d0303102c03090030b0312004254100d102c2d41110702006807060081031080155a0483c1400f41e2050601404c24a866400302c0d140a800380c1101000c030f140401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290000557 1250 289999307 289999309
    0xb0f1308010c050909040c0b1908060613030b060112020a03020d1109100c080903060a0c0806030a2103020405060301030f0b150a090b0118030c0f080309130905161202 73
    0x66201811034a0000c00c51103030101c00c090014407841a207503000b8044880010148141c010800008010700c0104035a20945e1718803e03a00174100701224400315441c1000b0500038104038054030252010341c003180c42003030b04680340c600101d000181864100308440c07a2400244a050020b0013601d111030300c015841e90880c0403894140c508c0085c001544c85002c0c054414070342d403041800d40d921205810040a00d8006007407080300c5203d00580c3c6038051254605210f507001e0300c1e600840c0744040e40d944541c2d168980c24201071300d400002801a2000281403004110001e1500d007241d0140500e080041c40d042c0e440b00450101d4200340d0080c0ca581c102d40c04081c0910401500340741e8030050050b00140110740c01c00000e51842c046000340c4131f8072a664010200141d00601c18940e08460100650202580e285002400d12165001e40700036002065000100a10000b0540b25200e42c010909030f481b591044140b401401d41400130b035210310440c1c0e2400c48501c05440c90308050a0b0040b803249107190703980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290001807 1250 290000557 290000587
    0x10501090b040203100b030402151201050a06020102030702070509060d020d0614072c040906141602031e0f040e010b0705010b150a030914100209090f0f01030311070b0f 74
    0x40085004500400400c06203694071000c0c5e505507420010810340300d465070f0011685040c24070411490156000031007407030070130070f10408604135102140c2240b07095868410403401d031700054400e0405a404040188160314001ca655507110801403e0b100381000c8540000c0c1002a842100781c4d403071550384801000b9810344218050340610f090501c0c00d06000300044911178105200c4058803000b0085200311020b5942e070308010300040d04124180720300d020486030110aa0001e40e906101c5c490015998040640088240c8841d424070030701075040719030104407184250b0f100b00030f18444403600704804510210f1031071490b4068911550920784030340e814074201d400c5a0070046c2c498840d403011a4000090106c075022a08214814600070910030103600c2e0109a00351800035207000e6010782082100d43d0b00407540500b1220108030f41015460302d46100d1002c560f182650140d201042d5540140301207402000c201c3c45c040284800c8548603a0b490401041c90742040031040c021550000c0c0d0307403007840400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290003057 1250 290001807 290001821
    0x1050306160e0d06020409020309070f0515071506030507080709020414040c020c100c02091308030402090c04050d0c03030f090e07030b0307080111040302031e0c04020711100201050109 81
    0x96004200038101200d580c00d040c50141140c2081140b06030082c0340503110340140f4803989a20410545d2596100c02a04020b908201e6030f010304d92250324030002e001d26401030b8000c11a1005010364506040d0880003056951061000752071140300304030004128010f40c400c0000450040d0090560241002c190707900f44015079001010042c01880148000300b01350b003000220050441b00003c013012440001e9051080003603079030394400c50490020321300c40d402960714040d4520131101c010b0650340f000305c40c0d08403007500c100160044034103100003401030814003034964101c010000b00c0e60605d1798810010307190820603002140d0919041504008045d00450345503441c00f0035062030b0100d1405c00f082c520042c1d40c01840c1c001010385074107146401d45c40030702840c0050071804000740a03030f1301001c0e41c1c041964828401207010b07200f180b14100c03054081380c17800d840c0510004050308400140340c00f0800603411016094501d444045a03113020b42c1d840720720a042e4285030f90000b0629614000c1408129480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290004307 1250 290003057 290003059
    0x306050f0c0c100c021c05030a0b03121e04150f030b03060402090705090402120c07021f05030103030c081c0c03180c1e0b030a090506010b091806030c10170105 70
    0xc0c0107403070040c040840c0e10b041e00c40d001d18000445070100e40d1304130320f0480c03080880b00000c141c0c004007411039503001c4021072280320790301c9003070049030081c405042e507418102d480364100c40c0d02071290214503034100141c21080600c1e0000d00b820f00d0b031126151181c038504040c01da03012a030a0b48243e02480d8243c0141410184118045d21080c0f820b90089204000300400b00000c00c0400034032404a6036481e4162005488448090200d80ca07040c41c154409501103107003644030340014509809840424403c99140c042c103680c40300e0540e480d40d80c0030b941c4425000d008840e690000d00092002c02e414000c5000f1180700f003640414018003441002d4112810300300701d108800214884400400c843c82100011035030a001c038000140702c0e51035822102607054000d850b01c030100000344410101d0a170000c8980e9400b400c20350b10300d40d90341d01c64060b840c4903042401c2c0c3c1101e000000c442d90080240004e60380050003405076640c071000803000440078404120711b44040703507107a500400d285c1480704009000d004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290005557 1250 290004307 290004331
    0xc0803180d0203100b130212060910180e03310b03070f111509030c280f0c03050105130501061202010212070c08191209030809040e160306050f 63
    0x401c0e070007090301c0c1d5000c02400b551351910350120003915181c1d001d0100101e04016021900c0e01c59044c811028068150b5101e489107a541c4d003ca00d118103015801812900c2a105c0e20b0b910554108001001e00025101c03c020b0740418008490500d20710718001c0c1a156241e40c0b0400300f009030011314203680e4055000104503850600401100355084a140074007980581041150054240c1d880c83c81d103041050031a907648003e070103209002e030000010344a90324840d4151014128100900a40f00a0070b08900c55884018a14a0045100708110540c6a402400394241d241d40b641c950500b500c009aa401040c485003035221400c4c008280b058030094141c10609045008041c2c00003541d8500501040101c0b0900203981802c024402c071140c0010b00c49a019240007214200d0104000741c00320758260740c5200000061500325101d41c04140a403684a200c1d5810b000032407007400010f0000c1c001803d0300788a0361030f80921113021007520400841c41003030003081e0740c03603c00d0480001704005858104e40c06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290006807 1250 290005557 290005579
    0xf040f0c171c0225080a0302030a1403040c030f080d14011d0c1e132606040510110417010603110a0303080a0203040f060e060406050c0703020a120306030c080318 71
    0x340c3c2c04a003107007105100e00d0569212040070b0368240c0348680309522481e1140700e2044080b04058001c0083d0000901030346803c21946040c5242200c144021100201281c2c4915003d10009020480d1a000ea03402b52400c141001d02004d900021511700340b1182c00041d00b1003004002d81804c554200b02d400001541185290a10082400d50303400b40c102c004500794200405540703a00361240a403202e810180c5046901e0550385e8185204588070046405000d44d41e69801101003407000a81078003441c0e01034002c2c01c078626894840c0000340742d1003540040c124400c220004100140e40080149600003000000b2014035600d0106030b4116083c60082c0101600c01c0100b000c66000599540d0240c1180030140e52030b40c0d02c2c0307420301d0251000e09001f0841c900d490306015060780f00052140c40380340320301c004000c107403600e1003440714038000c024005005920031034203000010a6403542204544260401240b26503c0746c0e00d240c034518494000030281d0340041556071140c07440301c00c8210704480c20360b84100c0071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290008057 1250 290006807 290006863
    0x606550e0c0c0c280504050906060d0303060801060608090f010b0904150b040903201207140109020a120302060a1509020306180a1509020306090f040f0c17 68
    0x42401040400d03074160225582c0c407180020f20a00808200003000201400c5190260308040d010401c440c030f0015010300c41c0861981014802d041c060004000145480d0b41c890081180344110f2100480170140c0382e280005142801340a1320014000e40c0c0c1318a01716103001c80555283c0055a8803450341d6a040c8003014140c0d80751509001e0304150031080c0042c103c503c20f03c410020b008840d20461b0420302d001c0038401030652190078109030300e168004103820341c00c441c9107050b40ca508200342c56012603003c00201c800030303020690344031086034484008900001140c00180300a112a84103d400645420060040603410301401e503015440300d0003000b074a0350440003055002014000d40008690000106510740c1d6038a050720080780c01c544818002c0d24008046102030080108402c9110142c0130300812189a540280d030312501014000b1401903840c295140400203000c0e01c00d07101002001d03014408640c40501180c007500c0c41144030b1091400380c60301e0503e0326101201c1c502d07110100051055403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290009307 1250 290008057 290008079
    0x901060905040e1908030901020c10051501020c010806010c0c0503010207380403030e100e01061805010b090607021206040809090603031c1505120d09060809060655 72
    0x40c85805c0085a40ca07543e51206150091140d074040003160700c141d02c1e420004140700d0300040d1042c2080f14403802e003c0840001a691602d10540190214a480c4005603080d440b4403142c0d5801c1b400750004820581da2100071900326404040c0944800f14400007082030b0f40c194000207031103020340000805800041c1b01e2040446c0e00c0c00b40000701015250308449054080c02c00160301301d0303034030181c04100100d00c6004060081103180b00310030715400101e03040b016180031442118104d6100000e00340c9805800d600b00031481c2e004450490740001d150f45106000c080c1040b41a21440c032500000c3da880c044401040140000100050720a5104112400d0b044041e1000074074480c80483c00421030003c1e07510301410220a54000c0d64009101c42080c00d1520000651141d10a80c00d4444081441d01d03001d0031201c0a004888400701c0741d00c003c000c21924202081e159010111901034103c010f0043c4518040140020b080e40d02400d40c4a44076000220506001c024810651041604240e14110340504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290010557 1250 290009307 290009353
    0x150418030203030402150903150712020a050409020714031602092202010c0212030d02070c08010912050d02070609080306030709020a09140f0d0c090b040b010c0803060a050901060905040e 82
    0x1024212a2241a501b018850f00341d600d41c0ca00102034a0510017003400c13000c01c6050880300c100010310354441c0714410624510844110b40402d64846107070509080c41c4601139405924100c441d044990644414010148044c00102060014081c8444000e004000349524050f00c00076002e5900d0281901710074102c442c00b10f455078282041500368041b03000141c0c2104595400d100760b07010008a81050782c425074001c00c10302c1d10a0200010090321640c043d82203c400700d6008100140e0620805031041c0680050584140d010001501c1d18416a48800a80f11003d01c11181d945010080c03003c07a24003032064a01070303c00098210b080155841c0d0007455001c8034443d0700c81001c406500c107026603d91003072039207503000f010b000b0f4140e200c854a400120301c0528443c50881c90b02e003002c0c8036131030b01d400d010b00c561650051303442c0b48003510140c8070407801d42d0000d00b076944c0c0710000e128002039580f40c600c080c600901482c0c481c40d0399140707010b0900c0141e803050170710256640c00c202041070744034946d10340c290 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290011807 1250 290010557 290010559
    0x2721090a060309060605060f12011403030f030408090a030609060e010b0f060901030905010e0304080d02030f04090b0103020d0e1c051c0b0112060305071d270106030b150418030203030402 82
    0x3140f20101828008000c103155046583c00c80320000b01c090001205200400d1f90482c0307001d060100d680e0b0b0354805000509202a42070b41a00100541202d0311b00181c041d40d0090300800590385000443d00004440e0314040d4802c07107040d42c60b0280101809070600c10800b540c12101c00910030800780c0ba0025002c086101340082c170829021510400e264072a03031161800c02d030b0090081001c0614508100e560750002d2241072010700ca0308160041151010040e55002c24404800da806d0900b000001c9000d401669030032410143d0900250402006500400010050b00c00142c0580700500080c2484000c03d06002e109100c0100203040c08074000c0035000c181c2c0c84146600190424090004a8010020008084029042640120134810f010a00f4000c60b4034582d09600c01d170740401c2c01c03450140401c07104040c10260281c0305800c4506012180500c104030f880000501e80d0300c917a215543c0310f2040d514081e40e40c002e004228003600b464800c400c40031a40b8410160380b034050340e500070750301d1000600c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290013057 1250 290011807 290011811
    0x30901022e0624021209060307170f0108071a0403060f021224010809060f07020c0d0312110915130f030614060604050a0e2721090a0603 60
    0x6122505190580304191a0601c0c2844003035610756242c80d024041c248142d05180204582c10141800099031035800800c020603079042c200e40b94208042d0340c10040c92030090090707040103210205117000141d44194262110070b542075040105103440d11b44280c03c404d1010002400d148850404241901e088980c48078003c10003000c10600380d000390040e817407101d0b1101c0000c000c0c8500c50f00e48003038064890f4407402d144140b01501c0350044507a0341d0b00780d07003241c0d15030400001f140030a00041c1d4559030048003401101c4a00240743d01240c14504000d005074001950340c156050000c41900030f0340107800c1c19a22903407d01c1030407000641544000c11038078800403000240e070005907075218000402014520b01d04c1c05c4c850782d281022400f03010210b0b070b4451301c16041c0000842c2d0b481c0a50540d0150303031000e807402e45600c0c24240c124401410184c60204070008181e00306065028840d580c0c11300190840142c210002c650044a144c00e9450003a1101c2000138081d032070603a143c1c6546901125503520740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290014307 1250 290013057 290013103
    0xc0e010503070e0901060b03070c051504020619090b0313020315090d081b0f0406030b09160e01020307050d020717010606210906060609170f06010905060a0e0702100e03090102 77
    0x143c80d00601c607ea0000c0c45114002c0108481e03e50004420940d45e0b010707005607100d10169950090021904490003984030009111114100145000b03540c80c5d54a43c0c144102582d4640080b480640c004940750300030580340804500c1103003820300c031106e0004201e01c3c0440307050400c000c1c02502e807410142840c08012840c000180c0710a0842030511903000c03150f4045585085202c940342d42540701e4050a80844d04050140009040046070184601d1650800440ea1404520708582282d59184032604611040c0424030101e0014010318801c0020707078005158103407501104075030101d4641014080d5900d055402c12220381c02040e440b030301485208110f120161761415900003000310030800741019107801004200c291f040207080080d154034842c26a020781403a00b0441d0707a084040740c0c1e29181c2e0807140c010032080c103040d080150412001000e40b40503680351042c00c00001c404076180801a4171071640100c03414000c3c0700382c2140c0c01012000d1482d0a40c80303000130750303100116115900f85d4402040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290015557 1250 290014307 290014321
    0x9010608012919060309140c030d0f050d2309030a0e0d03090801090b15030a021c1103060a0606140c0a020f030319050408010e010603050604150207140a0c0e010503070e 74
    0x180e8250841d43e5001c0e0b9103482030710351000800030003508100703c1d50a48562464043c502c400145000c10140040007480100704406040f180034030001803142c103011080c40b41954010082c01b07286092108450460716205103602303030900c0c040f40074182c014990000c0201a240340e44c082140400c110054030441c980d2801171404a504452a40c400403141d403900307026400304401c140f81e1a018074a00c07443e41c1c42c08403c10042548654000800942c0b200c005101c544041804203465400070780503d140c581c41a00e0f450220b8288281210314842c2031784d81d07000c01c0c010160040b4100601001c00c2c0c10090a02c1c5807032038082d40d200e8841001030b124144d0341103020b401d690200300311000c1d4440078801200b9210b01c01c6018019800c140103000241d4240700388000b4416051007108200d030b41110003403100e600c45031120740412901808190720150200b2281d00804e0342c00d2081045803000b0001840c0161081c2040c072201801608401d440c8078180300100415607000542800795049684054401d0711155 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290016807 1250 290015557 290015569
    0xc06031503290a0c081506040314031318050709030b0c0c2b0801050d0b060607030e09070c0218010f15230c160803030403120b0a0e090106080129 64
    0x44001d4141042c50200300d20440c441d0000c054046041e1610041502c3d01e2010344c40c4904407000c0e15400a0080c170040011516001e03402140c2910901901d15084401d002940489000d401c0126a030782800b03100310784601248030361340e445040f510b40149000d0541d52200e8000b000171740100400380b40443c1503021250240441540c0d680c46484006840d8542c070b040840900300c007591800031400c041c00015070342c1011016440060750060210142c0c0d9610403c1215607000f60790150304104050040404e19100e01c058a80180c07002d441c2c0d02e00d58841e9204000c0c3c040007500c41206403e0851004100d1414110031681c2641c0c01007500303452905280c1c608940c05502081070100d82e00303c1c46d680d070380c003808103500a01c13080c1c0e16032007039441019594103150405809031103a8199a03104000140101e4450b400c6071004060800001c10302440501c00250500184c0d0043c3c11411099007d100d40700d14240b2443d401800310000a00c4003212240c1800745003000001b003450403041c120100d0559503500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290018057 1250 290016807 290016863
    0x219020111092739300a0e010e0f0d030e03041502010605040f090f1101111b100801080c0f041b09060f090f0b0708070c0e040515270f010c03090c06031503 68
    0x40701510f4901d011b18001015000c40302d40c4400552030700041010340c02c0c01140e05001c01503110010311159003680005c800410444100503843e010502010520000c4d4800c0503000c0c2c4040d500100e0458105070401040324082d40d080c40f181c501e00a90400001c0046140850207a004501c441c0c0300b901c080010b030f07100d01e441c1030038540a0140e40c12000c1444034100c46105290416a80b09286654584054444813400e0081c10203661089002809502e4040c03601060b82001800224402c85c929174112181d00c1c0e0041d1072800310300590300a110450340030704c0106080941c0d02c0c0034050a85031001004015109005440500000103079035020300c0862003c44149581c8180101e0049640700d10f1304070145806c2d50110b500d4052145203d552160f200312050207441200c0e5001080142e43e00402d1104c0070b441c1c200001405141102025202c080c824020884100d440100360000c1078984400c8503d5107030840c40600d858072000d0664022000340c0c1d00103596002e204107050300003840c0325049803484 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290019307 1250 290018057 290018137
    0x31e0702250803071b12170904150303021b190501030504060905030304121101050f060112060f0f0501080907080705010c03030207150219020111092739 67
    0x40016004d040203044128049036041d0000310b4880030fa182c0f40704410316501400c001c0c003410310403080c3c0d0380c0c034905010003000340e4100188001000c450403a070900610748581d1003603015810031800f4521404180020304038000e400c40c0c402c12200b00004076459040c040c0c2c06050304041e9590005020000c4541c0880941504001100e03100d24083c030f40740328440315680c04140014100450040d1121050092500558010660a9083d6510001165041c6200e4403461800d62520300006040c1327801010000035181d4000e40c1403241e41000b00141c0240700c041e003881e2013540204020070404101154080940f902481c180c2c051800e01c0c20304402030300070180050311003c64000e0512480356190700034944e40ea05071108100500c1c0d0144180e0887d20202c0008011650030400c0c0040b51900341e070881880c2c007822005901c2180b0142d203040c42e550089450000e1019541c00c0c0e0034030402c0b80d4155840101c400e400c0c143e4070a440700f19800043c0110740c007004041c440e03101c41c00c5145945464580180d05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290020557 1250 290019307 290019313
    0x10f18080a0809130c0801120f06060b090f010503010509010501080402280302040c020307150b0d0506090a020108100303050901031d0f070905130827100302031e07022508 75
    0x510350501001c19848008600c1c4513482c0300440e900ca4405900a031400d01c0445e4541c0345450f841d140c0b4140796030b100d0341800c540b116201c4c203400c40080c400e0320a07000039009215405884520711030600c280281d901100314140301c014401000a961540fa100707041d40c000b0b18069103161140d01c04941c02c4e4000100801c1401030720a800140c4d00c030801030750400c4034000c490511002c03c00f0b1006907124406c03039401405000100a59155100700d0f5040b100c0540005031251191000648449003003001c10b440f00519504031320300700415980e204002d140c00c810503090a86c20b05156540c080c0c000d10a406000c1c0c14181c0751402a52401740d0000381040c40031100c0c0944421030400c82455485014500a4400c21482c003808900006006103980c0103c81d8080d0030300e4900388a42002c03103501403031030300a840b10100a107242c560980300ca030007145c1260180d84000d62030b4100b5003003000c000c40301005000c0c0d403c6148001c0000c60b07640001c0e544160041e020307142206254601b400f100654480d08403694030b00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290021807 1250 290020557 290020573
    0x60c14070620120610020c0607030c0b090705012102190f080c090a03060b06090301180b010506030c070305090a080610240e10032a020c0f010f1808 65
    0x8040307a003148011941401581280050b0045002164024010980a2a5108000214141001502042d040c004c6004444c10b211032200083c5556001070701c00c400043c0104800b1003000450003080d9000780031500946191070400000070712840e4003480c81014000c4000940f8035511440e07040781c5106945148404400071030700e6025041d8080c0303080810004150200160a05580c002501c0070202c0044c250b071201c91450712030300040c200305a10543c0c000c004100584095034244140c0c0350305c419164104103000f855040400c40c0c03020582c88217020b42010810003241141c5c0b041180d421503410306011351a0170518011560421355034012082e1803040000b44103080f005100710b10211652003200b09c9888a4810000c2d4100074280140000b043c003c201140307080c43c166807001c1080040e45130000d01080340302e400000300c0755502441c1c1c03519040c1c9840c1394007141d414040102c03218011750b079401c441c00780c041c00201345d014503546c00420440c404241ea01c020f0102080394005150707400441c0c1682c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290023057 1250 290021807 290021813
    0xd1b02280510140708061c0c0803030106080613090206070f0809030d0513050103060e161404030c0f0605030f06120c060c0106050405010611070b130503030a11100603020d060c1407 79
    0x140311241c43e800074030500e800029642032103004e07100c2c40ba840c0600601808040180b91000ba078441c0201100e424250400200b1083e2040000d1030003402e1a984643c0c09003007580c18400300000c50b400851106003040e05800240e2206000c654141d41e00c401149141c3c2c01134244039170320707000e0218006e03450b0082c0d51900360b84981c0702d806000c0a50401c2d09110b0803654450054040780c201c0d1052104000c55040010900c0881e0074804101d03202a0030009807800326041e05001030347c07083d002100c03038000202d002e0004080f0321030358070054001c2d818418694140041403682881004008034070441703440100c0d0f10512414092030740b4001d8003602403500c4085114002d40a0907040c040d59029915000000403000d2060101808020594000d0240942824001c41066200280b142d0310080c41280001c5d064600304014010030030703113554142412181c01c81d400c0c180858851401801820706400348050f0b0303121081040d00c00d920143c0003545602450040c0c40d21107141440480a410106400040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290024307 1250 290023057 290023061
    0x60c070f06021801080a0c090506070f0f0b0f160203031311100c0b090c0907180b07080307111f0506041808040f090c0c0b060d080f0d1b02280510 64
    0x4403d000d07202c000c459520140d1071002c0f5130340102e0900005a6403a0201b0080c20800010003030380d806003010006024068030703010f00390940c0800c01c54100c4007030404c001c0c0c04051b04100c00e41000708608180844112124000d65a01003e44001da4954680d20900c00300400c40c00607082d03000300586460088280f03408080c20446c00380e841528900c59840002e2042100030516450a00008040c1d0903241c82c7c12000321442c01c0103070703010b54071090804008034500400e0406400d94503c42c0085603520b1901d0301c401481c40d00192400005503204114160441d01004d540d1095484050000215a690200001c005e060041070351508070403405d00039418071001e01d0080040d1005412004440d40da640400c10450710000150301c0018181c098840005413000c40241e00010010a881a44946a119641954801c0ba010541040c000a007080b060350301c5e0150544a0111500d6890803801ca030801944a0400c614500c08243c0d4406102c00e200c0b21040030034280540040071111000c00159610f00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290025557 1250 290024307 290024347
    0x5093c010606051c1b1404030203030714010e0106050307090f020912010c08151c020607050f0615010e030d111f05010608060d0f030e010203160b010509010f08060c070f0602 76
    0x10103061a450007138500665001e610340d44c8403441c0c1d001c2d0141004800454224a80640300c5500705c0d402c00c000005640e042000d00b030154080c038401ca41d90450300400c41d084581300700880c10140d040440c20089543c000c038440b01110601c1101052034882660b8040091007403401c42035000d0008404d40410312815400388060b00e0060301d8440440c2c0740c1000280c5410080407544c1c0c1c0c45180944008441148490344620a901c046c0c4441e08250480e41c41d1402e000b114400d8000d10b92040e030030803007101041c200340c032442d40007800c1c0150b0350038034030001c42e0302c0711420803031401482056000c0c0e000b440300c1000122514420184180200315503010704602a00b400e129a1000807203d201081c054078001600c0e4444c02d510203008100c110b03450342e050300c10060b85a541810340c0018040c0d0304d078901d0210003000100d845220003000541c1410200554404103820052a21f50403100c2849024400203140d904000400005074440610307140c4180060f82d0300100401c940d0010810840d5000c01d01c200d10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290026807 1250 290025557 290025577
    0x130303020c01200702190e04030e060c0307030315060c02061801440727050d0803010302040c142704060b0901020705040b1305130803040c030605093c01060605 70
    0x441302594045030018171b1490b000d04444200303004049000280142011401d2140c05002035041c4900f42d5203e0741180c001800580c0820b0300c42c4803d00004458221501c040c00d101c1c2400e002800264012554034011004045030210700e88900514a80c0503101d044480710484800344d10710305514030f4049480c3c0b0340d107006810440014803881c07480c8011110062180b49142e075508240201a8130048107020b5101d40440c4030641c180021500d915a41c0910343c28a02078040310fa600d501d1403041c44221a04408240204502c2041420040740365404886c1c1040100d40b10b0030505203840b80074050070340c607048040d030300c5450414001003100098000d011f0346107098095413134141d41e410500081e5103c10b00107990010451010500180c2c25501281d00314030264000c01c401c100c659128411680103440989002d10003040070004c02055005260f4420400006000e00506841000d00285000e4140100300c06190034038034a003050844c034040c15040c0e0200203111440c0d03182000341c91a40041440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290028057 1250 290026807 290026819
    0x608010c122304030f110610030b01090c0504031424060301050601020a12182112110303010501110c04060e1503070b0a030c0203040f0b12010905130303020c01200702 73
    0xc401d20b48804042604001c0c01c41100241daa40c50359411655840d02c98400000d02044030a0711200902c03c010040c82030740755110710382c0e0745411401c04800d20701d0140d005007035541c00e002e9401c007420390020644041701e5005110b120415070420100b03040588040c200120b201007011216072488008900078003503102900200302548809004a03180c0c11008400b43c0b060003480d0040000038800c1c421100680c5101d025582d4103900c585200420100500c44a410708002d0408a030510440c1c034507000203501107080c2810102c0100041310b40342d010512a0703030b0502608801e1036804d02c2d000e000e403d00e10f45c0028010001c203503d0f00004000090b0607a100d07040d0b0300316001020710383d080002d094000d481c50f220b44d04d0b0820320000c0e0700302e001d08082c260180860005100002d001c01c440792000000d807c0f241071841c1c07544019054510102c405a101c13550450801c0107010500c0040a682e61503241c0618001da6035481d1821841d014009800040401040c4841e8907126201c0380c4000d0b0107414800c070340d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290029307 1250 290028057 290028071
    0x5010b0337020c0a0503120a2a050a0e031204030506060306090a06050a061706010603060522090c08060a020c1c0503191d210304020a140a0306110a0207050301060f0302040b040608010c12 82
    0x90800b2480400d03010110f0101410f461002706010700090000b2054902e00140035090002c0401c0c00e01d010300002c0340880002050602c1000310500800340d1222040d002012340303181190001c1c0c3c0d9584e0840c0003600d9550b4800c04241c035014a0380254000c0c1890308410b41440041c41065aa1044244502c0000925220000c206450f015840c2001c003410302411942d00912401402c1c0103000100c8119040d1416040000e2003d10a200300351103a03142590050701c0d84440505607042c03541c41440f48480354480c404112100c0e80010590360407902e01ca4130403022a00c5865040002d19107094015240c0306c441c4d100e40440e04000a00032080c00c00e903466000b14051824419005010554000354441c003075000c1849015043c0f00340840741e25005001d20782c00d03942c82e201c95048842c2c100b07034040e03c188000303070b00000c46804010f003800504041e00200b000d280341c1544224002c148c0d0000130f101d10f4071003650344541d54954108001401003a40204400c200204001d016909001d081264031420588 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290030557 1250 290029307 290029331
    0x10f0c08031906030821270c0306040b100506030606190e0a300c05060307020c090a091209140d02060706060e100909030e120f0105010b0337020c0a0503120a 69
    0x70411300032070442d130744034200d503400c14447c0300364100c8a40b03c583c079403040b5140e007000ca0342c04002807030050f4003a07800c150103818840d01c4120814030581081d8084c020800070300c0040c0d110f0700226100c00d070702e9413503030309072032180c100100c40e80c50307411020707542c80741100300d0100d0255800544801c0d81c05010514900d10b14001004000c2c402a40c0c0000d0710703424203040c041020f418000300459115205205940342201d00c000010650b61050350b07100803807a502c083c02c108000c460030740001c0b401d0a90038075407155881c0503c0010082030005419006402201d480e07404c640380c1c1429144200e40c00300c4280511600c58078861200b07941218040c4051070318500002d6201720030b20400a4031501581c4085825909109208a108c0d03800341d809102d201d05911151100001c1c4540c42c041c2007a12000c40d03490504c03147c0d840180317100c3d640c003c1c402c4003040c401c10000759010700701c1c28600074414800342c1c4980b00044118208100d05a010b0a20f003c00aa6400c020000b404418454400d0352000c02803500c00803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290031807 1250 290030557 290030617
    0xc080709060f0506070302071d070e030a050d2105040602120c0703080103061802031e010f0606020616020f0d0507170405010c020103150b0409050402030606010f0c080319060308 78
    0x1100d00e118a01c4182401d0086003441402405d41500a0040701c202d00c3d80c80380907401003048048581005a55042482031180d8406800c030300d4407404034010b10300440b250310303080d84546c0d407076190a082c000750b0b02911003c04440750610180340c17404081040701d40303041c3c240303100698080c0d40043d200090324000511034070041d034190b4185681542da03002c842d03030840d0396600041000c40d0b1145e14031034000000c0001640c0c01c01043c80440d0810244003405151880b4070307425100600324072181c0904040d002e00034190f001590945c801c190300e80015003811550010fa003090f81038060390032103000d154841c0144541010040a020b0322070f0b42c504408082140d0113030014061409901c0c001000e00407044c0140d03100380c00450205440145030404150b135100450410750003540026041a1910100407d600c0c040c44100d502c0b00302820321501c1209082402060103084d41402001c850010000c50403200c03540c003542c0301c00414000700f041001e40380d02b0000c02d9034020b42d101c80c8480c1046107074104800300607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290033057 1250 290031807 290031809
    0x109211b03030f0209040204180b01080903091c050d09060e01030504031d041d0c09010f0e1603060305340f09180503031e010905040f08030916030c08070906 69
    0x5048840603049140d07421405010030301204810203409200d920115a41c3d840104000c006481501c0c0c1e40408602420040d16806440c46060104850802c035100501004544481c14200c8c1d48a60700c2c2c1d00c0c0b0b200c41c0b1042c14280f001801c01d21617030402c403901c0b030342100c3c0d9031050340c440e5214800700610007401142500c008450040004020005011310303598580b042c24504c110081c4040b401c11900d94644601e00f480f115000c501d50311074611882d6a0901e04403843c090059422030b56292030414080000790703103010f400c101c000780502d10b904841034804d03408031000d140d10500351005002c1c0c450101d4201c00d07007400d82c1000c1c802c100e58040c1544524074100c0c5c2c21250002c2801103110b01d00040c3c0d0b001040101d0840c2d5101009155590001c6c1c000d100551041c0560702c141c00f41100070707030352418030440144c2041d95180d1409092002140c900024409469840040340783d03641d8070310354038070b042400d80401d07201616110034000c000c1050710a142070581d01c00704106c4600c1c03982c0301080e20642ea05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290034307 1250 290033057 290033087
    0x602160503041a090f3006070906090305191b0608040605130b0403140409020309010606031103010308090d020a03050a050f190c05041a0303070501091a01030803060d030908010921 79
    0x1d00701541401d8100340030061940400d03e00c2c00f080140c140f400310003190006c00300e44007091700000108000940c022034846c016203160b02c0d010b02d42c18155a2034595034040303c040e000582e000c0c00140c1c000c100d034958945204c80e4131842d00c1c04100d5030342e00c1c002d0214401901c00b2565281850000b0300a20381e01c5562910381c42d00640c001c0340d1600c40e510199a03a51031400c68492805c2c08205c04108800395000641c0500000c00000a8141c94010000c1c2101d6162008044040c0100010404942c403002620304503441103590300f105400b1407000507050809a80024020302454014005101c00415003c51044011040c2c65030744400b00149801040f103004000c04505a2103014041420603500907690310016101e80d07918002e8540c0040d01d19002005c0848842c0e4680f510341041021420035520070300d41091401115504594403000140030080015014a80352034000d0141403143c3c0000c4010704400000300642c05140c00c0c006218911440c180e89020149080a503000f8801c45010780c8500d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290035557 1250 290034307 290034319
    0x80312010807060e030a231e0f0604081206030c0a0801090c080c0307060804050312090a030314010b1c06050a0603140c03042d02090a021c05150d0602160503041a09 72
    0x542641c07000b03030200c085065412040c100b00c6541c500c195007001703004051076004000b031105400d202341c030b0b910300450101c0c0c030241c6070081da09204c0000c4c40e51054510114080020308005d80d00d02000c0384c40c0c90819200c0542c05000407400069202c019400181050b00640c840c0001a864001346940c845030000b2440d010391001c4000c003c3c10344200040b5800504c01c4042d41d04c0c0912810007910000e8040d241800a90005c070f40440815030503100b000301406142400350625032502a11108a0045c1072114107208604000138003403109a81c00748003d0080108500c10040d12210002d004224025404481c03070715000c0425070442c84101960300c22a8801c0c00e81c643c4400f141650116a800680313012200803e080c0840f0042e919440c4030f522840f458040181c46000b4583c0e40b05902c0020403d803040c0c42e20388424031180781c0c1c8114154541440a582c84c0b9001502807a2110086c804d886041901d101902c1c0a81c082001c007200034000c464071000c130824071030f0300c5250116261040c0d5250a0707020b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290036807 1250 290035557 290035573
    0xa0c0f0e031f06090c05092b030804050109060509030913050c0706090213020c0102030f0703090203060105040e210903070819200d1506080d120b0604080312010807060e03 75
    0x11070219586840e030b10a035400802d40d41d59a2488005035070103030400e600800c1000c40d0444543c100a4544188050100c0c0f1000501032074501c01c030345503042042c01504010b08500050305200e02500900102540680204420b10b42001c0c91034580e008441c105108a19071402c401d5440b000b80105405010341d01c901c249400c1c26540c4e00001082625412a0031840c144065001038070107101072b01c81c41d0f80360400580d43c0d2510f9400014a000020010b009240ca0480e43c50003507100000d1107419a501039800144000041050520f020118116010b44000c0440004140f01c60b600242540c881d05408440815881c3c00302140c803468050150410b442e044d2081030b0108001c0c10313940444041d8442919841d110013404140c2c0620101d20940e4401c0354189901030b94401032113520000e103007110180041d14404030000700111000307030510105903100d800e030003880d41d10a01100c008064100881c0c1c0c0c0c0e501600d803002d10040c0e00348103052103400341d01000104503000d02003868105178001c0203007680d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290038057 1250 290036807 290036833
    0x3110f0c060c0a140705010315081e10180c08060f0408090109030807030c050c041803051305180a050a0b0f010807120f1a0f090105091506030a0c0f0e03 67
    0x66040240031540343d100e11001c1001144120f000d410092880c24094080d00e41000700140544c0c50348642c07641c02c20390511040016240215048440340c428445820b11001a000b00320301c0c1c41c4d0a000b8a500542ca4481040c2d080b6065400d40d044240c49000c0b809640f940d150401600c1c2c900c22145032050101c0d5a00040c0028070080040803011414180000980d403252100715190300201c3e4200c0109144030300707420501c202007158125003602150103000d488644000740c05034450038003004040c0800810141e072185034500541000c1c20b005401000c002c00340c0c0c1c421107a0313500140c4a01400c0b510708008038240000e10f000d03401d1107210140c0000c0c0d1a0b40100b004440c84140100703a03204000724a56004000020380c015246e40b41e40454022035080080580003494002e0b1422451282000800f9881140c483c0014103045a8080b915038200d60360304041060024060420103510450010030404030b0200c642c0203020841c156500c11013050741d4600c05484440e45010803941c1030703110074107000078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290039307 1250 290038057 290038069
    0x2060a0b0d031818090519050c0d1401140f010e0720011d07062a020d0f120306030c0803030f01092706050109150b03040f080903100903110f0c 63
    0x100034034140f152043c0d540d0840e58201070000001e040c00252500c0c010010301c0020000c03500200300c004041108024641d0b1002d03075407140d440707281d401703205c828440704140034032103a40e0b00c5031211850082c018840c40ca144406945001c0700d401c802c41040c00c00120395080e86c106d149105010f1350319005816248440c1403444d08a4010030814150740340c2d0710710326400c0d00d00f807280001000400024001c5c1800d100c00034000c080c1420300b984006c202100d070f080072003a00e4036540b01c0240c0c050703685546c81703040da00b030041000d03400f0034000d0701c001c504180b041542c550643c4250201c81c0503000342001c040d290040729480340300c103549102d0035000440040c00f146426a000041c004004140c5541420758140100701c0d46103020801d540840d0303580d004000b0344400d40545440d400c0c001000b101e403682850009060b07400040c0024090110f0b40b0302c50010000f00b402100c070760740302c01003c45148541c4403405c6009454060021000101b0000800a82da01c000600d4018810315202500d00c1040303203018006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290040557 1250 290039307 290039327
    0x1120312020d091e020a0b121801180804050901050907080403030c021f060f0509060a0605130902030109020d0b090601050901030902150c060f150603060405040204090605010b07020102060a0b0d03 86
    0x81c0b143e40d800031400042c015607541d110900e8074118031500e0f0700160041084400e00c40d0311610100c90100030b005403030b81c202e621051b401006000c0b0070040a10360f03184280105515855001052582032440c028001043d0250089131002c0340c0204607680c0310400d00c041d1040c195000400708050320003040000c0d000c2d40248601109902c121150100428009400c030040240800425551400c061040a44014101001d04400d4901e1055414107802242490317142d441000304001010a030051080c1c08110a80b004000098040d500d035611140a0300003940000e0a804d0202e15001c0814102c1c00d003181344501c141c00c161200303404d15403140019030150103504400ca80c80641d004100080141241c050b00150b8070980092440e4a03100e0a000d5403c0740142c18400348031101c80541840d039603400c08582c0e10907004d6030085502d03161403000c14094484d00c00c00420b00d03400d0000220708a20014040d0005034002d030f088809a44030500254200c5166500961b00710040200c10300200e030003107035800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290041807 1250 290040557 290040577
    0x10c08180d060501170f0f0303010e040c0b030705040e062413030807050c0102061b0f09190605031f08100216080a020d090e07020c09060f1210050112031202 69
    0xd0400342d954a5003111800d0700301030150340c294040a007813140d00700038030251801c60000900c7d010540b00c004a035280014400c0155101518000504110708610b40c54020110344400382d40b0b9040501780a040340d0440c0c001c62003400d98140010703c0515051281c1c1a50a0000004001d00c1041c0707104046150300140d410142c98400310400000034014a0003030581d036010304090301d184080c4400081c2800d001074103c00304a444600319249446049040301e00c05010b0001a50f40c44000310003040c1c07482048160700f9503502822a0018025804c00c0045200e140400d25200d06171601114101c0b18000782d0040c040c45500820141444540e1540240410044600030549020059640a405034008240c10005070080c8510341c40d516009151380c8080e080010050409140c03800e4002c0d928002003896500c030b4191840400d815446040c040c0707100c0e20000e003102c5150b0281804440c1d4840700028124042d5280c0000000d80141000c07450070f0290741662400c4a2910080d0b01700d01a401c0500e0314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290043057 1250 290041807 290041819
    0xc111605040e16180e1b10080c030c13030210030e0c120a0b040804031506030605010501050309211c021909030f060903050f03070c0302010b0415030308041b0609080c010c0818 77
    0x1400c1007178000c20980314441c0076485a28038241c2e8075828405010b404030300d4070003805079200501c07418025010a070b0b540058481110358643c5802031100040420030382c0b010313401c803044090203038035039078540c01040c0244800d50899100405031800c1c091000683e80b21641282c01420101000481130704041d0b8115008200141c1000e8498554981c0d8040000b080c2036a02d035161400c104000da14081d550040009003841da080d464101c04040e1505001440c640300415500f2090042908020540e02c151050200b000170038005071030700a00035030125116104a40d010303184640c04d01d100380016019654041da9a0340380d190180c0c2c826024020a0304100c0501c1010300a0307200c0c080a260145100d2541c5a441016101c0e46040c081d08440710060210702032030600115a01d104280300309102120707491f1800001c00d0380d17281040a00e00401f40786070031007800f14180001e04603602c10007001c00c1d80d21a0f070944a00b0f40040b401035031800c940b210300810703003481405000c0c0101e0300300c610542605405889 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290044307 1250 290043057 290043071
    0x6011d0411030321011d01030b04060905120403020301150602210405100e2d060901053109150b0703030f0509031b011401090c111605040e1618 63
    0x180c256000303c3c20010b80c1e201341e01200071410f142e0881c082e0051020750901c0c00c0d82001d590030001401c10502002d05034003000404601000304640c07020800d0380e00b0506a540d202102003400306181d02c5803106078480c0d03003004605003a0700071800e500c0085071000e80083c64644580c142c3e51151100400380c060340ba0304103120004a5441d540040628031480f0799550810042c4007040200e0103241e0340c1d2241c151034010320038510342000c40e861154403d4084032100d481e00015070040311240300b0f40c04800b8000d04002a040e900d500d41201401490000b003a40d485490b4480822804071490400c80c4601c0c40b03125182000841800c400900c0050300030326000c940305030070886180c00e417142511003040d50f40c4001090207136403142a034079001d03030250351000b40403000101c51f51400e408010b00ac4c0740310309a07440c0f9501c2515800390f07500c1c0401a01010a13194100364210103c91450501c1c07040f1401a4109840310184000200d02079402000d4078404000c41400c00200400c40c80f400440032050070f690b501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290045557 1250 290044307 290044309
    0x5061612110d0512090102031006050309070906090b040e0d0203091905040e10110c03041a041d0420090f0403020f010e0304050315090a03080912180405010806011d0411 74
    0x401c1c0b8809070080c1d107a80d0b84d40c0309003014045800c0c03002800c10109034810301c14050810411341d0040c0c1202e40c00d24185449445003000c9074140004c079485401d51a140000c00203524680703401c001d09241085904101807c101c4001c10f480702801104c100058000308050380441c80d003281d0740106102030030084191140c41e000407600319102c007104106147d21000a502d10402903019031f8070026103402d411410700503182041c40c0c1d2409035004049080520b54114043c2030005001d40d002041c01001c80501c101601400c00045501945e09076105100d00c412401e1001c2804d820010a0101a14818150b510210010100301e00980304030f0840c0505c030080c1e14484003d000d20411407034400c01842d40d80303140c901011b00c0d05c1d50b03880b014241e2000c02010030440d10701c0498422140f41d058101001640c1c3c03a410800e0911710004218074015130081411011130703407180349080d041803007270b01c08221598803001c103540d131410240b040354810344d4001d041e242290314000101f078100f0b1096440b5040725400170 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290046807 1250 290045557 290045563
    0x8011a0409020603130c12031107080309061e0d020412030212090d1e0506100612140106050a03020c03030103030c110d080405040b01030b0406060206060a060f0c17090411040503070506161211 84
    0xf07d061700010b00320b2200c0b5200007424807054000b0841d400056141980020200740c0c0c0380130304900c60354803c180c07a01c00401c0b0820003085507a99034100c08215521911141c540129160b02841a401803040d08502c0d9801e040707440444c1c51484004110709150f40310760361002c1301c05004580c15494454001d2003507000940c2001018003480040c000b80d00c10b079080010003424415014801c0c07071001c3c1003c0714842c00e40b83d8240c2a5040d2070b01454903569501051005501030301c42d91040040354400080004241580400e2518070a880380c844159000d503c01c0401690819071079000e40000c0d402c200400891409620003400c649041c1800b10329840800002011a400340d840303400580c00580401c08245030490440340580b101c2d04124614000820b0b00034101083d800c002001348100755a80403000d407a40040e42e00d2154000c1c0140030200030002d4160664002e4400c01d4024842e500b00480d82d45400c50550702603204d082c5081004d0780c0b16490b4074582c54001402c031800d1040a403c1c1200c04035080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290048057 1250 290046807 290046839
    0x3061c0f1a0a0f020f160c170313231017010b0a020d020f0d1b05030310081603030804020405220506040b060d050c01032408011a0409020603130c 64
    0x10801d40074481c50300c0041001074070a220500780980c3d10402080703a440d040201a140b0009082c1c1c80404800700a10b010340c08400b050b08031020b6a91142594122043d001000301030b0140c00b00703c8101016519001c1e00303004000600c0180441c0e03c4508020324505050f03201d000c90720034030f01c3d062400300300744001104604020b8000140305000050080c50454040101107141040e5100510b00d109028a00c43d0301c0b151440f09110411035020152500008200c060b203c104e034002e0103490f40c03800c0004400c14100315911801015028540c110b00200b00080003150459802d6215808a41d45503030801004000040c088541c001483e2030b202c140500c40001c02450301c2c420300051045003801e0a1400824600603d000e11170444a6900310001d0008564030f4445a070030b081c04203003d0a03080e00703a540c04412040080c440c8126000c0041c2c40c0c4015003140f60103140850004111984500034403040c6c5110342c00c00b03900414108040b0b4003c0e5100030803100e0319801659035005042d290440b4580712411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290049307 1250 290048057 290048093
    0x3100f0e010b09130b13080d05150a0803220e010f031a1902280203070605180d0f0201060b070308180a02010e0f030c100302030f0c03061c0f 62
    0x51160029200c0800744078821a010381280c50354003034a004903000565a81005006202002040200b040e0444162490a065a0008040d40c480400001003401031008445602e204584240c100049003480d1095a00781c0f04148050343c035181c12020451052003244981030713000145220002a440c641e080b000303001e044190000101c035031a504140384c0c0d04182c20900c8209031207840a00011404c42c41e07500981c204000405600c03a40001911185d644618945051210610b01c8108025a021004221881c40340750108660b0721162003c0e407001d400d420682280b83d1003250440c058034050704099044c00340502c00400c4c4c00e51200e8840b40b594001d03400c01c90116040d1018010007800f0881c0014244d40388400500d20201c0540000b84aa4000d260650103943c5403403003140e1580301840074100603000a0510015411803071002402580205c0305843d01441040c040f408d400c134140b040301d0140c0c41c004c0c6209104003000014041b8150300c0d900c200c4010003503403001000280c824480f4502252 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290050557 1250 290049307 290049311
    0x40e090708071710090204140a290a03020120030c07050f090f07050c0307021f02010b030615090a02041206060303030615090b1b0609010213060f021b03100f 69
    0x11500c90590300d410050f820a1070000030051003240103800000742c1d2040d62051900101e50b9143c1400420700401c20080300041c200520020030200400c0d64110702e034010205000f40102e20851119405440f40e41911180e000184102c100b01540c418080307040c58001d83c544000110030f16180251459100300f6405200303400880f020081c03461b24140d00c1420050a6030341c1c04e00c030b2520705144038415600030191000d100b00170807400e4114400b0800e071604c04d603001c2d104103901c8401c0c24032880340041d5851200c1c019824400c0b140c0b0a0300340071800a01030381000103054008003103101048000c03c401484080d5444d0700f03000002d2049100716800361020b0084030b00050341403c0d41001425107800c1e41100300300e0700740d03020403d1241d544842c401044910580d841c0c0d848060303201c42148540e600902451300e80c031131074062200c040410740c0203082510b0204842c03000c4a540b00c0058480304101e002d91130268102119040300c0d6400d00c2c4143e0f0f0712200003003c0d5024848541101d508030384851000b1a6299 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290051807 1250 290050557 290050559
    0x200a0201050907090509030316020f01090c052416110913030306060801050102070308090a05041104080f07030b0c0d1d0d02010f0506101107030b130b070c03021908040e0907 76
    0x14018440c107400713001d118200b0f001c02d1400c1044d9555910025017814100400220a0642e0342d1003409440c0b0741c42c0e8450000e01850500b4205015144140d0040702e00c5040801110071201c138810203a42c001d9814000010b003001c03951110300e01800701a0718141e42c1a840c01200760f40340d40d90070440c90b00c01c0b0381128000070800b80d20300f4000c040340d040c1d410500510444030010300c19680c00142d008101ca41c1b184001e0717554030218020403e400d403540c0c0001c1d0020304141801c0d0508a03464050019038080d101203074660400c40c201c0c0c641d9450280310241c02030310030b200840c0301403520000818081c0c013404000718108103407144880100b04802c550002581004880300343e815828042c0b2217800c103030244284901c0c20071100080c81c109190840070140520786480d40707a004401d00c03498008540100008103246001c1030380314042c800d0f448045412046076030018030070f140601c07044a0101e401d40e009007000d0a40c9020f030314030b100c91a00d013a04c041d40140000560244c0e05c060039480b41c46011701a00e406 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290053057 1250 290051807 290051821
    0x5072c0711060601080f060609030a0510090201110d0903020402091f050310050406030b0115180303050d1103040f1707020d0804061e120506010311070309080c180406200a020105 78
    0x4110701514080c10424400c0c1407140003c050720b40303075400610850706641c0d20201c9e40700082c0790030b01215001f00b00c3d02580315404004642e0354800b203901c500170388401ca421210700c403050391240589020400810340c000e10600140c2880e501404800030003606143c28204220301640c031000b5032289010009900000b00000f07000c0d0800380e000144002d54043c0f044030304580d20381d50002d605000e42e056046188442d03181440c480d103170300d1500080d48400f0014a50300c1e400d0040440d8404120703529110b081c190b502c0221121801283e115540005e10300204034241d0350f07101f61007031581001c0c0300d50140c2403102c900036903a0b220703c401c1c240703100d01c055a81e500d140c040050320712803440040c03401c010501c5a144501e0380e003142c030100d00e00142010000d51b030380c0c0d00c130016401491801100c0c10107a0011a0240406401c021a8000e03145044116001071800c0c01c200044860704050b0071400e003440d10013150015081d40c0000348000347d5220801d80700a5a61040400ca03040344c0b80f002c0040c0c0d1900144090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290054307 1250 290053057 290053063
    0x507050d0e0714060c12281116080a021003021c0b09060a05060d051012121e020a03110705060c060412030b0109150c0b100513020705072c0711 63
    0x383d490203507210b508081c03070510b00a446a0b5084013200f00c0e64030000c2c000d0b40d5148080002e2022803000c04814042594013040140700c00803c412004591080780c0c2c21801c4030011030f0641049405040c010b1404596545c2405040c0c280700e000d90303084c19000e10406402446c0c800c80c00d501e8060514001035041006420425011070250081e0b005100d0144c090009440311412200a10040c20300400c25407551848100030003420361104180c46804486030041084150150b0440700541ea5141100241c0c1007035900d1882054924802680c0440d00b4000040d020755080e60903410140c05036140250345a021410079400414800281e410074410401003100b4a81c0c1024001c469160403c40c800064001804241c00c90182803811007810412007000b5200b141410300c403c0d4020000001402e20410b05108120540901440344000f1202d40d08103251a1094812813500040280003552600280214207100f102443c14035201300c03003405034040440100d50340681f045584042e0041001481103003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290055557 1250 290054307 290054339
    0x90c020c040e0703030503100e04030507200604050409110303030a0b1c0c17010b100206090f030304080f0a090909050604031409090105090a0207050f0a050c0d05030d0507050d0e07 79
    0x100c00e51400650b029540c2c000104042981d070315041181e42c90715110766050038040c80303911812070310380c5210820040607804805092042e104000485400d0b41c182c0103142070502014a0740e4010400340020003035450160001c203031281c015002c1407900c0f855100400d086a00c00c541254800340c891007014500c0c10100c810480300c94015003215200380c0c06903107584095400b13105003070200d01902c002a514050079840740f6a6802c0003890319002d00b890800207925000202c4000308140940701c1e480010850110440c3c1c404c40e8006400ea142400d1403400c0c1c060360300403c4001d0100300019002117210485880341c10032041c00b03000101680d281a1030000e0498681c00c043c4040d51000740840302c165201e035001141552001c5495a1895032005140340003406403600242240c03080481c011160400400c401803158042d9003a2000d00c50940e091140c4000c01010041480d8002c01c03414400d02501d60100350050090b140c41890004500000b0f400d03507505881b900d6181e0000076040009440043d05a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290056807 1250 290055557 290055559
    0x803010503070f1a070c05040203130501110c060a0903030905071e05040603260d020711090c03090604030c031b0b0a0e070602072117120901140411011404090c020c 72
    0x5100d60305090504451240f03800760501001408078281c801c10008080c04d0300985409401152a840d203401c005810307940708600cc0c0c50300d5103429402004042002e080358014041c0304014501030b25a1a240c5000740400041078040595031701170200000e4003403054400400c1820311801080482e0303004000c005105034480791050749860020400501c210701c0a080414a20203216003a0458200b549a1031141c041501c040307500c0050420200201a401c21440e07a1301036801010560701e40a1804040c40f09559490301030f03001800140000340309003034028201d442490f054105c2000b6101201c1c13601c85070103088410164082c200400f071a064400c4070402104a07000301501481e122020f910340d103081c003c11450503988544440042000006c1506050b809002405d1070305410480d40180e401070040c1d079520f8003007000802c040210500602c1d620003c00c600b0521142c58580e038164000c00c102e9401c905202c0402d8000d0448440900604000d101c4c056010503850030481d4000d080545801c212 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290058057 1250 290056807 290056829
    0x20d1b060c020f0108040c08010221010504090819030906110301140a150e0109120b06100503010b040b210103050714060f220f0312140307210f09080301050307 70
    0x40000340c0e0f509000e103503140500303091070015a100d40c00c01c000c4201d09a082100c0b50760001600443c2100c0d0150000b01c815840000c0218590703c0c4c404000940340700c3d50000c1c040302024007540000d00d42c84400c8085900e82814000796810666031200c2c162250340c0055528014040010401c020003030104001b1340c1c3c4122017044c2d205050400c005001d070000001d040030407110654560559014500c0d03a0090300a420030000b01c403540d0316003812441d40485400c0e000d0b07071428100702c0819000d2000d90341071b02c40b08050b0740d080034101001100142c020354446002d40c000c080d0301a0300c020b020705a940c040d41c06080542411406d044501c07516020400c50240251020010921020b80700b0040d01c52100d424154240003000000318003035000c41c682c01500d14803144510000c100690200d04015070070fa2500c50005003002e102010903107020840d1103402084140c1014605518000c00d400d4100007c0d800000302e440042c0240012a018445d04035004000000140583c1c40d04108440051030385c0109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290059307 1250 290058057 290058077
    0x1306020a02180a1103040501150f0320040605040509062d060f18070806010f0f0c030c1407141305091c0302070618060e03030705120c07020d1b06 64
    0x206104259101c40081d0307003100800440c1800c1429084801040c0e5131002d641c0e00d07802c00f400c0c41402007200170201100b15102c2d4200117208174580c1e07441002c40707800840825036022403510561038400c2e082c15440c2c1c081d80d0360390003042e07a503954440d881c058490300c00103001c0381c64910440400c00080402c5400c000940c51145403204182500c007640c0103409641180c545000c40000c03c00125808000c140003038040317000c200900c0c0e0312001031442008240e948600c3c1da0161282502c2c01007603c01d8200c00103d0740c5500c0000b0034014650000c0d028840c60321001c134100000e01683c200480d640251060009041d5101d40301e240400b0014010400312078104513900300400810707501c12201ca811140520300504032083d1900a50664609981140c001d124014442036500310030000f0740d80840d440c0d80303000741d00e1880000000030380f031003048252901841c085041000d03400b10203000b0316031072810504018050058550221009010b4402d0510981a0010f81c0c0f418101c0d45482c3c1040b402c0001c0103131 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290060557 1250 290059307 290059309
    0x1b051002011a010e0a170f120a0305010605130905060f030106090b010206181509010e0d030509160b160f0c030f0339081e0405040c08150f0a0e010303051306020a02 72
    0x4980c08813a0014154403002e2040724200d410100920784200704c5000e0000f0044000b2034182c010300d0303040c00c10303542041030363788588003034905008480c0341c041801486082400701442d59407100745c00c100700030501c2c008581d080000a007540c80c960003410712a91540b40c680083e50b0100300b07a942240d03190599040c14248007124035540c078032886056aaa100100100b40305404c29840f5141081800b000e845030000c1d5500c001d0043c05090b1030040c00307482a03006100c456562004800165007241640c03514100c0d035603503101d070a0b0201400c1a1040714910080c480060b41c00d4a460340203601c943d150721404486414050000c840d1011400d0140c0d01d005200b103070f480f04008201c1c20101ea00f01c0000c84200007420f254540e409002079004100309000c080d56054141c040240049420843c1c0a120340080c2d410116140c42d0180c0e4401025189840c881c241490000712403100e500d40540020316a595070038120590840a070300907000318100080700031900400e048100041c102c50700050210f001254 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290061807 1250 290060557 290060569
    0x10f060e090c220e040803010510020f0607080c040504020d050a0b060c030f0f040302040216050d020d1d06070b1009060f030209040201081b0703020102130501020105060d1b051002011a010e 83
    0x2c10b20400c83d072481c002451441e0407102c2d4410241192500029252401d40b412000550003801420b228100200b01c0700c480390702c000340781d9509082c2e900103881d8a8640003016610400b000e044800c50315418000031a40303807a284003a2103031010014020801d4100120030808681115030310a009100821114001c05000000c0b02c1c884505c04450036500e145003d200006401181c20081d4054000120200948070803070b003052010303000c1c40540380450b00062050303030344a56030f4010001090f4402e02c20b03115126403845140300b024024042610300309883e0303525081c80350102c0705c010311a8228401841051f44901c02e15014000c80102680c1c1c1c582140c000803c41000140000d04210840000802252078242550038031a40955840d844800c5490064040c0d04080d03074503c0440340180000600c0d40c0f050058074000d48024125400d22265034a0b58900b111520404513094000c240d070008481d2100307204c80050030510ba00000c4d051907404029021805208140c50400c9a4a1740010f044e42d42c0c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290063057 1250 290061807 290061817
    0x506010317041d060a03120f03051f03110411030709030b2a0d1409010204091401030804051c0f23010c02030a0f030605090c07020a08070e0f04020117010f060e090c 72
    0x3011020030b542c131440054001081ca4100501c1d01d00d1018051030103503044030100c41e61101944003444150744a100ca401912403188a071070000300d00540c20400301c2d5081080307100c0c8220140001c203003a24200c00c90402a84142c501e100000d580c2c40d001c00c24840c015041c81d41240070100c9540d0900440c810000501d441c2a200840702180041d00c9800b9400f02e41c40070040040f40c155801c15842c10a260314000c2d00a449100c4076241404110304c0800c1005003840c2c180d039800490703d03040a0401d400d212818140e44c00c840c900007041c450b04004114054844007a81d441985c1c6a65022048289020210b42101c50518903a042125541034542c010041e0303104c03480d02c1e1400c01064455003004a016051903030003203420141180c11300540d15005002040f00600a8581d00b14042c0d84d14512551900b403031043c0064030740d041d07020a91b001049028180c003d401490100107100c0c41c10b080000b14502a40040d90740b0316030701410490150407822990f9120701c12205802e0503d001d02030328215202e6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290064307 1250 290063057 290063099
    0x17060a05100e07050c0a11130905060a020307050d050a1b050901021c0203040b0d0902030c0a060c020d1a161b0f08070303020f040b04050913030e0d0c0909050601031704 74
    0x5440016804503c54426a020010110300b00c0f1251a10b50602d0710b900c01d08010a08d0051070503030320102e0514034901800144952020040655a58001c000c4000350005000b0400f000810072501100c002c031405514011240c00100207446041c111644011140413500542444030510484110382e801003018880380c81426880c00c4441d407482070881c1144a6a0800c0040c00004100f81114000c0c50f40314150562080c0d04036152410200c04100c4400903a03c0b5500010ba005a009001030414010204460303100749005c8080c048201101c2810b40b00888080b24400c880792a0074424645c4442c524a00c0400441404041085a29110302c0740e09081c00c044e100320400100002003500c281c2c12a03c40d0600e61410a40b9680c462006059a5005224052049002001041d4030420034400707150107a0349621115103043c00ea1003801840d801c18002a039906820010014400c2411300a0030119032040015005540c10340c03400c4031142d400006007180b80002404107200c205032440c080c40318004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290065557 1250 290064307 290064329
    0x2120109060b190302160c0f050405010305031c090b070215060a150503060d02030a0c150f0807200102040902040320090f180a08030a180c060c0602040e0117060a0510 73
    0xb164080c264017030301c91580030b182035840c20b20f100424000341c134507510280e40740301250a5034941c2c0d41c0100300c02e844081c00040c0160304100100303541c0f018400304c6400001890358011514029a80300d020090008135003150268000003084401001881c40c1d0507400b6104650010700075050071950240846061546014800004041040c2e540da03038180d80036440c0d0040445601250503d80944240094403503005000208114581d030207000780f0704904900c03220350701d0241e29620f60340121202c1001048000721002034902e0008900001e0004001900040b0400f41e900ca10f140741c20b081304031854401550480d03059000c5131940d0b41c1d51941d9130304140000c0514090307031940c2044010068070603d6070f00d2203214001ca9581005450009148240d56049041016283c412040c60090440d241c0041001c10f035590140802070182490101e42d5024013030060405440c1d000268907440700383c020303801e502940003410200c0c1000b0404158045494101480b45060048040d011401c16000b1401c80c15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290066807 1250 290065557 290065597
    0x6011d041a091e07020109050604020108060d060509010c0f0504080c010e060c010507030b120d0c02150f040b0d0507051c09030c05030315041803140d090f030302120109060b 76
    0xc0204074492070031400100701c071071141003180344200c01000b10307030032800d03155880d0380003441440c0103106101941d500040985582d98072940110f41e01c0708000c04007035100742d400982001081580c481c5030312811104000040c01c011101b0040c28014100c1850810403200300000c0c0540b400c00b1980626966082c2402640c18002400081290140300c9087c0324540c40c020030007020b10f038190402c4041c0481540d060107030075003210600f070f01e03039002010090220f0441354440006050030700b4000301420704010000e0415071402c01d0012030798080d0b4071006503240041070302c0c0b08d10b444511a068024a81b41801e91620122200300c000e10840b0f41c508414443c3c0d1440034605050040710943c40d0550b00a00341c039901e14002241d1000f0003111040d5500540c6002e001011004c500c80300c0c09003c58254440d00300d481c12003102100158020406000015226601c076000901c4040301d52440501c07a85001d41ca8034910540002c0000701640010282801c0040c20007035211614200c0d26908043d0721443c2e040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290068057 1250 290066807 290066831
    0x7050d0c0e15030607030c030f05071b0c080a0302070e0c0a0f0e04060902030a020315121005060423090d08100605091819060801090b1f081203060906011d04 69
    0x2203007040b10942e054041c400411458a81c16030121840084945080000c0814481070400b00da4048401001003880443c0c3e01c414104c0350b07a02d0750f0101d8801c03140080760945500002e070402d4080d00d0114056802020203201c0324843c1c074101030f071100016000600706121180010801400d04544200303120f007100e0341184c10380b00c580001016041480e8117568904046500b20025481143c0090342c144a0044082c01d601d071030886221035044013001000c01104d0002120700801014141c40c1c1e1103aa561b245081c4041d4800114450541c0b03082004905e2901170500e81c2485040d02030082006100800c00c0345000c0003032001d4064983c0c6240c41a100c91404000c155096081000889019900070030040100d4801201d030b10780e8010724806024071070f80d82d104242030301d4540b138008001d58607040c00211a03103400030002801010500c000d4101c25541c11150741020303010382240880b04130010400c0f000c0d080c501c82c0150403c00c00c0c6084a0104c600d00c00b81850b00c988051440c1c0701c0c6859003520460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290069307 1250 290068057 290068081
    0xa02070f0e04030f0206040209061e0406090203160215010e0a1526120304080c121c1a0a060509280306060e04150b01050c0f0106060207050d0c0e 64
    0x40d0551a550090303481d2500e0110401400c210b40031000260f41046221800b48013081c0b4034004c9034054080030346c0b0b440381020840c070031080d03401c950b0450003100c03420b50403541c66025803001005010401656401c00300080028888066001000d41d0700604d5401c1405014108460440e099294100760f00e440b284045006080004d81080005480302000326040703011890042c024010b1454807506601c800c2e002c1070b210401d01c5110700381c01c4070a20008010603412801007290100340c1c02074500c0f50607071104d1124160408007105500c06040044070b049045248601240300c140741d0b00d40b580782481c0b070001414004003401250100b1002244080558070b911035402e841c07440440020110107115908071071040751710701c003d45440d410918002030b03081d050550540140d1308185100015141c0c0741c41c20000c0c0071501c0c00503041082c100100c2c6902c030000c1c002c030010038030b260001140702441e24030000d107041c00c240c1240b07220780d019920380000141c030130034600d00315000760401da002c540d0340b40d1030802 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290070557 1250 290069307 290069309
    0x201050702040e01150806010602010c05030a24290711040905120a0507111c0b27010209090603120d0b06070c0305060907240503060a0f080106090f0216080a0207 71
    0x241030743c2400c2800302601700c40c0c02c03c01c00b81c0d980d4000b2103550760b0b6170b018104e00f42d4408041040205908102080c1c2304501c0707402000d0744003280c0c40e0304000260a071914103007210003640010000710352403010003144600350008540400010b0505802d2840c0d584510100c0c0d080311000903c11955100d00e0800c100d814001c40721452841d64505407034032407425001c0c280b40d000c44001c80741949000e100d6201031801c2c1c40c501d094445403529202041c11255518507041801410342c1d803c1c401803800d1080010660040300c4503040c2c0a900150701e4003501401d212400d0780c042c0c10144240c10a85807072490003074142c180c400509412401007010641100030920303034841d800020b01303042c4000f8008001e11100180441c000c074480c0046a0405995440349440460b0311211040854203001c0d02001107417282c0040e54111000500c1d40420580d1040c088500d0440c1e51301c0312800781d4680104001c10386580c401e204105250303440540c86e09130284420384100e210104014080c0c50301003603010b2000d108200180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290071807 1250 290070557 290070581
    0xf060518040c1703070204050a05010b0901050c01140103121106310203030a020a03090b0a080114123903030406051c06081e0a0b0115030b04090b01050f0d080304020105070204 77
    0xd04021880512551130303034401e5000f030f03020303038200b001080c19201a44501c504a07118801c1881c00d00298000460380741d80a401c0c01a029900c48501c000c00848908500780214418001001d204005800203041c003125448031864907000307941040003460020121a14461403408600c00c44440125054484100c240f8040c5d0180b2020a006210395000500d19152038047c0d00c0e01d05030743d40e4034105100244507a00820000401035001000b1382c1c4900c4641d4205680001c01c0d102400f410700d0340040c5061440030303c020701c0c6070b14150b14503809000c4401c0c00d03182d00c0c002044200f0024040000c81d58034812071240787d041040026200b420048020061030800700f00d1081844415550410a951110b40c10001418541ca04580642202000810403d02c651007980a10143e1074001030b08082040010b060051585459040301c86039190312030081e14078482c0200d200c5039410b04051141e0310109a007420700a03e2210741003c0426804d05c1942d40c081d0342468001e43d14070103032000c500904020903543e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290073057 1250 290071807 290071829
    0x23011a0f03041401052401050a0915020a030e030705010507021009051306060e10020c102313060201020f0f09060409020d0212070f0f050f1e030106030f060518040c 72
    0x200c001c010310004070343c070314046400090002d0780380c880310b030119481084411841a81c8003000c40082d0750080d0084c0c03000e0340c000c3c00c001d942155035140012000010484180058000300301c14410990410a4007180100660090407218101130000e086442441c101074030444480c0c5d441c0c00c0c00c3e8070030141c880c09400f02400d0039411101c00060036014094074010304010540f0178401c014075017041440010220480d07402400040310720380c00c7c840c042d4003a159400400036069801c0c0b00060407030071030800d22010017007407a540319400b100c044215001c0360411002c59004022070f45202d40e280c400d80e41d40021554030665194101c00000b0014890341d8010a100c40c0003150005e2441c0391580a07044101e600c10b41c1031001e80d206d29040707940e21540c041c440e010880c1c441d4403414443c41200074214180ca42c020307003894070411010f4802031010759a0400700000002006101c146e901d8050040808442101400558103000008919035828020348101030ba403070000805001e20b00170304100400b015154 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290074307 1250 290073057 290073061
    0x30d06061d04020f0304061a100e0321030c0a0210060b0a0813081b010b092a07120e010c060507091d010510052a1023011a0f03 56
    0x18200010041080d010000419074501080c2014000c40d00c06441c00d024461079035a50f41d40c0c403001011176252a44544038a286004003589501d03000c81a02c02c100d0311509144092a0201803410444551030400000000340707031964980140140c9401102d43c8104c05d4440d01c00d458128031b4004840001010517042c24000130b541009003000700300c000b0741541d030f40086030341d81003141c10740c0d00c83c45000030300c071580030030954405140130352941184940c00c000101d074000d00400021140c990030f4480180c1d0b050261521940c00700300c00800d1000384045400c0504100841c1c96030490100000440c005100e000d0010000c6a072180c8119458107501038800c1001d410f0410006080040600421030459020b044200c5030103004400b141c105c0e84e009040410440180204441a13001190994050130300682072044c880090601c0300c0e401d600d40740080c0178882c88101d0880030340e801000100e00c180e0301c2d090007100358814100c0c01d6064505545007a003400120b41c0081b01d00e8460401a07034565100402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290075557 1250 290074307 290074319
    0x160909060b060a02070e0a09020409051005130b04031b140f010c1418040b1804020306060418020904150212060a0503062217030a0b030d0e0d02040905030d06 69
    0x405854114040d1104000003030a81d002c0c00840d1140c4808140981d001c0f01c410071134858a03150b1aa4013096244000c02c4107042c90b8041015038501580c219101d40081848804500070b51084551004d080340c5102c1c0c1c1c1211985400b08280b80141010702007200680c0340201c00811015101c00c03841d4001080c28802d0050500c03240c45110041107106d095080c001481589803103600302030302444c1c1000c0107601d480f0040740403040c01c42c050582c130b68201d5243c072407182c83d56803600c04000c80044200d2034820b85180500c1090705112000301054030030741c6446241d20009081c0c2240e031081d1036050314100310646a078144107070032241ca01f6181050a00010360008240301da0028070340078800c01d0318031401d19900c9004254480108548084405040da01c48a25204030f070009025064069140108000c1c0c088441052507482100c920181c0758407196441c144c0c0c00c00300400e00c052103087c40c02c498041c011000103105201b210f04042c1c811503c81c80742005020f824011522461010241004043c2d0b451b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290076807 1250 290075557 290075561
    0x170a060b030c07020a061103040b1614150a0218060d0906020a020a05240c0a11101a120c0d050f15011508011203051605061f080a020d02010f021609 65
    0x800728060310340700704c00007400b60141e1038032070343c001c1c1d001d010392700389424a0380c0402640c000911000781c40086001c20340200e82000320102004001c01c0141104011b200003450800d0310190203041e089204108624038082c140b100107014003000c0318000d0384c402003006054083e20110030090589480050200f00145d00056032070788a0384030344181c507820f00800da00c040e0b074046008900005803904d400040d641c200d4000c010b000c10121410050784500075208003a181940c004103402030319070340e00c0000100108100b0344203c100c2d8100c50242c545580d03414850f880e080f685000a004409000c2c0403000c110080c40307002c00307a134030b0202100c056602100818a00070002c0c440c05030180030087c000d0052134811045541a680d842072111003814150398100d0f034030b40c40480d1309080051418842c400003482800000e0003000900c0c000750a015402c0ca00c4585001c0301d0303003c072032135030b000948100060300c40d00710300002e590302420070103140021140240d00701510403090b21140310004902041039111a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290078057 1250 290076807 290076817
    0x1201090606030b010203130e181501061b0312050705040308070f1103070f0b07021f030b03010e0708070b0903012c0606010e010503180f0d0302121303170a060b030c 72
    0x41c0c0c0d401d0002003803d0005984030b00c14003100c4d5000c007403003441c18018000f106110b29004201810520700d10880707074400604084408050240300350b80c81c0010004103501482580e00e5030242e20388070800d410306650140c809d2552003e841c02150703d0310b0000704154029003c2d074006581040241c3d917600c01d50f240c442c2d0130521001040710a0707071010200300d00741d040025401082c4d0b481194240d01041c1042e0482c10150800b0070701b264800c85450070b0304180031690450824103035843d180030400412000c101800e458a0408040c011b41c0b0800041040b10400101c2c00d044420b84012190354028820210380034242c0d018250f1080b140035103940400b4481d0304144805000b400342550010344074000110b81081e02e490495001a00502c04500301c00b40c400040701c501c0540004981c02642c55900e801d05006418007000046540803400c000c03088400d00e0000c0e808580e00044034810b8040c4e0340d01400b5010074a12075259480a500010307404440c0381c2c008009881c01000c51501c0f403925108001c22036001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290079307 1250 290078057 290078069
    0x30c090501090207021c060207150e0705040e071701090203011b0306081219020106150c0c0803040b030c070f0803040c090c0c03021c0c08030406090b07050a020709020c0312010906 79
    0x948000001d0582c0c441c4240c2d044564001c041d80c500144000805501c1024100140d502c03903820403082c80021075284203034035210f001d8500881d008059070003d50400c40c480d441680101e08006035070040c0f110210b2418182c03850f5036001402c41410110050045c1040b9000940561808040c501603641181c04504c2854a82e6020300040380c80b00c14a58860070541480003800340300b4071290001440c4414585034400d0035200004585580b00c00405000c1984030f4008082407905401c507060008c0740d0080303006000b00c0002145090f142c400300d21004e100040c94040308003c04200f000030040800c6205050355044408680c403030904d4200320f00c00a0543c8507160300c140c901035107400b0725800f070041c480526030590050080744030301d10503840380e1050405610013080b4910b5160f070000744848001d14015801802c000944c41094540343c201000003414007001c5c41001e0000300c403650b50010360801551281380f070260301c5100900070540b85015100c000d1038196250720000c0b602600d264010b0080300c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290080557 1250 290079307 290079311
    0x3105100e0a06030201090501050a05070b181e060c07020a080706080a061e18060503030f0d06050901030803010909110303160201180323071d040501060605030708070807031104030c09 80
    0x11201c11500484045200090200b00030388820000c960041d4040c000e900000d041c42443c084040d43e4940e8800300480340c00322800d07a01e01b804034150004010448040c1010840e4286040c1c1024641ea0b50f20001170514500c098002034020454690315014001060030004031010180c07074a601400d07044040b41c9070800d5038909400098a80e502014400d041c540b0010a41419420070407095045102c64a900c0e2103261140000507881d20100001c08807844004040c1c0c0d00c6140cee405450003a21042d5204034450030b0120700620204004800307e81c1114455600010006030170f00d0050582032451904981c54000440c40380e818003044444030585501c00d90f03c40c407800c6400852a15004414040504807203240388075451401803004d10750308042003107001c0b02c203c07a690781d24540004524204c0c0300c03926842d4900740403c1000074011200a4420b5092050a600e0025002001203400030800420008580c0c04a0005070107940f02d40120308001200503074407903c0c2e0800008140843c807808003224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290081807 1250 290080557 290080561
    0x20313290a0c0509010806030309060414040b030a03020613380c03100302120f0d27030b1f0e0a0603350304060204051e0f0f3105100e 59
    0x100540c802c0007018450703510f5190500c24003000449003048024000d54041c4002c01512046503070b280060310050034a6010704041d4030300301c0184400c1d00e040845080c0a81d0000f180c040010780c000c83c040750b1181100044a40c3c03e004d604060a026007003a6580110400c1c08006602402310205481103200049c0740244542c0c4a60100300d00c42d100850b10560543d46c41c0e80e0500052519090070725180341080d04440d908004213141c2410040303210000d402244c2d420a20f070342e50340c0306880c3c0e4040c485541c4070030034841441c54076181045003000f00281d0542d10100000c003107082d0180f210030082c001440d201d42040ca42002100c004100c240026903d949400425900000d11650301d1802c0c01088050711034500d00b00d9200799170a801c05401181c000e0340902c00400d032074440034200f040c1c003025142c10308101d020a501303000740c040c1c0c5075034007030300038044240036000381d0f200d0118030300c0c20140082d0001c002c0b10300008540404c18078410010009030418050010310703841e441d1000140c1c0c0d4846015a119 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290083057 1250 290081807 290081821
    0x40b0603070806130501090501050c090a0b09060405010e04090507150216030503221502030a0e1c02090601030b0301021602040b010809060a0c0504031b030b07051303020402031329 79
    0x81d103040c4100da81640c0120001006102c10b40d00b44100b0501c143c00200c2c007945143d0b070f043e080d640304455481c0441d43c0462003100707902d85680c0700070060150b03d210500c0c2c0b41d00e640110340389203d02c0c0102410b01a00078070a0b40952030344d9101c0080641c224060311201921001c030108400700010400c8018812700020700c0314020403a03144401c80358044011840c25100c842c200ca52080282c8217404420b019080001d00080102810384803012078ad40a0755581101201c00703000d0044911000f40100072103a01543c041c681c2ca11481001d5804450f1010265540001200501241401560194008100d5440008912641c2000984201c0e42404440d224000445200c101150561002c0c1d200c4000b045840c440e50b030000103045000d1424503d006d481e40c0310904001400d4169041c0e28000d050304106018032207020ba07030801418174201e8904070316900c0d01c910100c954080640f20f0355002021400c1c000c40e548001c1c80325a4810214600d0f080040c1c84000404003407030110b4403030706141b800151f00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290084307 1250 290083057 290083063
    0x6041d0c0d0c121d06220c03241a040e0709020a11100c080f061c03020d080a0c0c02280b0a08062b030c060609020408010f0b100f05040e010e040b0603 66
    0xe640684401015a5921459446142a82201010b1b0300c2c0308074903c00f101143c07046041d40d000e10300038120041501d160140c0c11805280364414003d5492800a564003104841c95002c103040380c0031200424400021b191060030112268800c0307001c2403001491664480d04048213070910311803181a03c80ba04000300500050316138a15544000413175420020312908952148145c0001c809844400c0c0000c6807281203408c2074203c1d00c10380159106842d020b07045a40500840da03c80a5003130240f0403c0d440b581c1c0a0714203400c038600281300d4640180e0a000d5006c060b010a1074208210740b80c140c1c071565510340500c0990100d5a104001844080054054180f0542c004e6204224408004040c00708142c42600101c80b12000c03800c01c0084841070010480030f00460020b82003c50300160380c5c0d03190410a50031100d58402d8034114500341541c8ee4880d07a00e010110340c0940c4a400e181140b0140da590031640d500c556005040130ba00c01000208401c04038444851203035209141a41c0c190700e0700e00c10035a03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290085557 1250 290084307 290084351
    0x918060609120c06081905010b0705061f1503110a0e1801050d020402030a090204050c131409070e060c07030501020304030f2309031f050402010e06041d0c0d0c12 71
    0x183c080a41080107031038400d1003e81c2e440701000c401000c2c50400d0303131111000d4910030b91025904000c04110340041c040c5c20301038950820f042d03611107410514504660b24014256214030b985008070b50320380e4003040303009400121036103004150142d5220360401015140240c460042070168904400310014400ca10422078181c036002441c440c01881d666017007101951004045103042602d4445000050b141e5001c0c0500814054019070b4446480704995040c0c142558880307041071551401c4403040f81c5402000c6908460a880d10b907107007200142c00316109110310251041c0c1d070312a001c2e0003c14014194003841c001c48c4295680507402020030011140c0070a2040c24964444403501007040c1003215100a0a0081c0c018040d03502c0c010185401561468441d803494070865103031005c0104569219001d081800c4080f50410b040c6410003081c646068140902030745402c100e107000c1200c044040702070307400c0304003000828440203604603801440c1050107842a05000e040606000c00d507a50984011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290086807 1250 290085557 290085563
    0x1204060504152f120403030804021e03060408040303080601051801030c180801021305040507050d090804050d050f0c1203070b060a0510020d1101050f070f091806060912 74
    0x181c2041d003441d040c503100c400398100d03540902034140b0f94000420b52000768260030404820106241000d074584007400d00c1d4155001c245000c00030401400000e4101041d0f40e000303601528072070040d040c0c02044104503103000c00400d0341442441c1c20041000414030040050341d10990711400c264485000554150181d40480740307401d0b41081914140c0e512a070320440c410b038514a0440740c9640b201040c1c0000010320740104000703035000203050382c1001c201806040141010b07641040a8680000024018040c0c0c8100b106e25a0b2030301140018804620709a03406800b00622900e80c2e0003040c50081e541c0d212813001c4907810300a43c1ca2549891800390a50501d100030800a1440c2c02219512134950b004004c103402c1e8000485200465240c84060100c15030692076002050040b00d15030020340300c1d148503141840c540c3e04080400210a491000c0183c01107800c1c1441210b1042004099410b0745144c1c01005501c403000d016942082c4036608107004071165030b10761110054403140e901800c1000b0500103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290088057 1250 290086807 290086817
    0x705120d120c08040b040c0902030c0a110c010c080f190903140a0308070e01031508070513021c0923010c09080319050318030705010203150d031205130b0f09120406 72
    0x24005c90640c0e615103522601ca081d8441f5000d4031544060308a8100303076400c6c000b190700800c03881e0100360030000c01450390320340c28010310414902d080000c044038000c040c0181105404600c00313400720003034010b030313480e85404421080c0c0002e20498000d041070760710f03c802c2d1b403160f10360400040c0c0c004021541d808100d825581d410515a81c1042c1500ca105a0500f00c17410141e50398000ca44000d1310308230b904040c15500014219151410042101c513210200b03442200d02d01c100090001c0c0300c22100700c0303c00280e4089000c11076140034100a11622400f807045085241b18000d60684080c040d03210000e10b5402d519080341003910340318600d40d41d00a603640702501c01c000080500143d030282001d950310078a0f1151141031240c1c2180000e040d0340205600b11416074010003480100402c6030070100c02c0007802d0743d45a9403212030741c0b0010b1020b0591008024801c2c1e6130f0b00030039011800341013000b40507034000c1220324490415144813903031a0021070b950b88041c00340c00c005140c0400310301c00321811210f0590716 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290089307 1250 290088057 290088061
    0x801020d1521060b03070506030a05010e073902090414010c050c03160804080d0f0e1c02012d050d18200102010615020a03030b03010c0c0b06030705120d120c08 70
    0x88800800130407094691511440c1c0700018241d4a00000b18403880c1c00200210b059450081400b00e2060301600220a2040d200100100141260440300003400d07172400b001c0d600000c0c52802289104503400203500203049400308014024901d90140881c0c0b20b200080003062003280c0110740c20301604c090b03002a900201301c1032099800440400610a0040f0981c43c070309641da00032503141c5003034550b10102090306481450300d5140c008000740300324017090b04ca000111112400d800b48088640c04000c0c10f1240d40c0c50034180c41d94110400d05034034040111140c611040342d00001c0d06d541c010648100b241c81c14410910031894910350810030240c1c3c0201e41541d000541114000704800702850b59045660744c420001c2c2c5d508101e00c16820295054018161880701030400400b510b00c801001b40c0a607040c103400c0564564030540036001c8a8000c000c604803a10345400203402c00c6895409030368490b001041d400031448020030380144e0707019141c842410081080301180301382c1e994084018049041840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290090557 1250 290089307 290089313
    0x30c0e03030a0c1b090507021b0108010506030a0c030b10050d0506040b032a061819030b0a020706060806012d0501020c0909150c0301050301060f081903090801020d1521 74
    0xf0130300c41a18071201000800c0f5102c801020442d0320031904000142d0112503030700a20b419819400d141c8820a1800450940c180004161284001b07031082d01125a202101d545044c4251b00250310410001d203040346a80b20b000009185070000304900034500e2400c00072a401e8940307031040da00902c0001c0d000e44056018146510070300c540408000c01c03907004414440c20340341e41d004010181c0302c188451149030300300700209001500011900380075080600810a2001c070b190040c0c026801a5815000340e44d41219282501c0036060960200c00b00c1d00c640320010a0a9812500503540602d103501e00090086201c030010941040910030310b80581c210944420060410042071540304030300d46c080b160360030212031075840803100c11269540611408001030089140038010300006158186054a6813810b0010490b02c900d58504000442c03802100c540e02018007482504004000700e400854490900a110340d02905005607101c80b2031003c600c0202d110000440704030240c1056280903150800700d55 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290091807 1250 290090557 290090573
    0x6091b0806030304030b09060f0a0b030703240504110f010c080307121e060302030d030e0c0603060d14061504021c1104090903030b030601060c02061611060a030c0e03030a0c 76
    0x64101da40501041001002140e0b1a4840034000c04402d0000d151340e24000150f5039000d100545001da0b00b0707040050950703035035400040070400ea941100c4400300703002404e003c1122705030b03182c4850104941000208014031114024610741410166280050f440c008001120644203140b0024403061042c00030402c83c912600e400d56105c40c1c0610001005540340d95071038240c120041c01d40c412203442c1e00043c030460070300b4014074603552a00d0038180300d0070503401100c40d11200070080c5c881c02004040000b454654490145400150300045240c02c840d420303007041c9440340800ca500c0e00400a614441841a05042c0f00326030402581565401e210000400b000020308002d80c686003261350700f4403010070089042d00c941072032144280c0700042c00d03c2140051600700001603001d2001d00c0b12001500001d81c844100711001c0b5021014506034140c91803408103200c0e200d0044031500504046031000e112030f0141d02c00e9540c1076403600c0d04900c240c229010942c0e40e10078900c01c20002501010182c0000340c1603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290093057 1250 290091807 290091811
    0x6030c1009091103010e0115021e0a03021b0a0b0f0f0a092405030105010804060603020324011a0f030705120708060102010e0706210e012c061510030e0d110106091b08 73
    0x1c0c0c819100f001110404002d000c0d07581a03682b41e01a046540c3d00001c06404002e6121034196502c2d1070319000703100700c0009a5004151180101c1e03030100049c410007440341c0d030088518050758660a9a01c9210b003a80c0280301070f401e40201c40c07034408a0b0b0120113152103072901d01c5510410365900c01e4130b540c1c02c05004507000f0b00043e00031182c140d1148404001a9404d204040844048024188900c1c54500b800311210340180c1c00070308484c1c0503080c100002ca010704111750000341c80d80c011a6490b01c544c0002c507054401d18102501400401c814040d125034042a00c0f8042c41c02680240071344080903048540383c0041d44208404528612107142d8031012003612661620754a180c0050210100090b0609407070703681044415850181c2d4900e003480210b01e410301c88842920000f000180350013211403940380f160740f07425440764111008020704240311b50842c1c01d00d00058019540b10010448001c0c125005e0a00c5090b070550800d00c001c035803000107100e18120000c10b4103040c41c0207045000252910040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290094307 1250 290093057 290093099
    0x30412020f06072c0906040c090806010b0405150909061201060e090a0302072c040213140402010e0d05060c31140a030f020906030c1009091103010e01 66
    0xc1d14003011844101848601e108400a07241c14040d01c59031040441c0d11a20b03a400c4010b11485006800015100c81c41080c0d4822401c2d80d0000e110b50030303500240c036000f1075a40052500d104010010654009440107402200d1003030b50700b1031540f080c180c126078040c0039040801303030030410102c00140b035454000360900403818032800024400e031301d58010100c0c1c0c0208a030802c105901c074030003682c10143c1c101311010042010502c1c02d207510342e20080d1810846060581c03461480c2c0c410011500390350b05c95a004c0030030300405200704584035a04840e000e80b01c10450742a80415014041c004042c2000e00025140725402405402c55035602e506858050300240c50035580b00769060729003485e07006490f00c54094281e043c3d20f0200050f00e40001100c654041180380c074020034080070b0400008410000003403000da4101c90100c516074901012030300c2d0040c6110701c43d6110442400c280c0240360805a10001c1d5031540e074080c480740250300341c11800ca100070701c100300d50400380f03500400840040014000780c40b18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290095557 1250 290094307 290094313
    0x3050c09090a0b0f1c0b010801050c040b07110a092405010f270e01080d050f0306040b01020109051014010503011416030603080a050c0c0904051002130302060706060602120f03041202 80
    0xc2c04c134001c102080caa0446100c54004802c1400c0248030702c160f10b4a004003502c0c00217000038504136008000c076010324070400c1c400700700102d040800c0108464450010300000f87c118a20344d952401202c01800c0c00d50980620000c04484001d188454081c4807004d4410603140d0440c01c00e0f01c003401f1500d0100d0350f403c001c070510000e20740070400090340d03400000808034440301840a504007007030b42e8100292842c4200900100700500031801c5840820b5950100c811100007030340c51541c0f00146d000d08181d060007042070089194455580100b82d001c40d0603000c445517207051507038a480078942260302d00403985035004550750004540602040c6500e600003800d1402085281c0c0d40e0b81e480400b80c0017404210003103007020500940302c03c2c0030031800c43d60303440807a0094400d080c2a11603603282c140140c01d40b02d800c0d800107000302d02003c0c9020044019540a00000d641f1407282c141500144003600845005000301d2081c809144100300689150340300340039030f040c5952a00c0d55080001c40c0e084c00301c001580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290096807 1250 290095557 290095579
    0xf01020d0c0c080d0908100203100e09010906290405010810090807050703050c121f1a061801020115032004180b04020f010c050a060e031308010c03050c09090a0b 71
    0x1032052201300c040c0040f980341c050040b0b0801e90b8890034065180800481107106108100d880442c00d19145c0480b94001d0340040d03162500b44500340540504c80300a0803840c14140074100050000c2c0f00c052000002c0c101d102e00560541c010001074800070701c5250b44582c012040241d007050140e01864409100700c04c1d00b49031174001d50f101400e00c4103e910035161508000d241c102d460400f00c81180c49800888050f042054900c10030080400c804000700d82e0607907076075207040010070051507600c0c00908024151515403801c3e0440e40502030342081054015400c0c160707903141140d03010b101801070f41d85c042e0300015020030ac0e14052040300440383e0119401a10703643c8010788100d07025406030405024544a0185140a00610180840c40d006407810480286070326804610013040700134075a03900c1500802c1e075141c984012451802038516803401100c00c1c1000007502e000545c809400704601e501c0034010b9030b40c4c0020740c0025005070308469400c2034480c3c000030320745003403a40400d40103400213040c00780030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290098057 1250 290096807 290096819
    0x4051302090705090a0902091c020f031f0c0228061506030f1d0c0909070509010b040306052202090a060b0c0a03140a0509010c03020a080d0c0305060f01020d0c0c 71
    0x1d03480a0b10b80d42e003c0360000a51018a05000c4a4540544100c040961800103100c5c08100ba050301c4030310441e03441e4481315081d0115a0740d4a2a501140c10003421070360b00c100c6207556841e5031203044104150203032505040da0b58050001c503403103040e15881001c2c601000b0481740142c0c401c0d1243c01d0100c0d00580d90351200e203030440d00750000e8000b4100996002451241740366410084941400e85000c5090480d0385001240000042c0300c99040e405840003c00340d120b41c1400c031b01c3c042c1c050308080d40c448441c030000300b5440c00800180003241e001c1c181c00d10940d190201040192030140382d100411a9100900401504000d1003841e088000301e9000039071550b644040305126004480d41480542060f110003007450f920400e01800f94104c107060301c1c503206084101500358820003043d0380c1072020003e4050b05050017840502c0c4269006135039142d031001c00c40d002c00000e141d010a290701291810002c0383c9141480030242c0d04410040c1c00030503680240360801c2d07502190900003101c004010040100b15 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290099307 1250 290098057 290098069
    0x504051f050105220906032609060c0c12010507080a060b0405060a021603060e280611120403090303080916060e12010612030e0d080715090516050f0103061404051302 73
    0x103005c100c6001034024118502003508088a80300180d0032880e007254030501420b03010444100500846d00c807542d441001c5a0981405407031844507070b22110b2400c981c80b0340e08040d00050700c10700e0036079619280d942e2121052801ca540c80c0c055040111020700060185003401c00c0108803045550040358200e82900c4071a28044400350811190191590b40700039020741c040090b4009070302400040e015182c402101c0ba001c0c01e040c1c00018148544030342d88154028074207030071104691429002000c4900d454100600542102e204c201d0000300f800740040d1103001c01140700d0704c000c51508081005c1074a030040c00c07102444012005a80310400c0c4e89a466910401d1180310010100101d20b080b40180a04001e0020280d41003650702891980040b84001500030040780e041c1ca07404031065111506001e541c50081141d8480100320f48a030891344810b400c50b44a0781011110100c600c00403036294040110150b034450321503a6146410385c00403003000c3c945a0030680e80841e24a6142e100b0130804c0e000620 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290100557 1250 290099307 290099309
    0x3030e0d020a0809280f0b09131503050a0305091003050f180f030426280314040e180d0507030e0d0c0e2a040b0a140307020102040504051f05010522 65
    0x118180d5800307800c000d00d400c00c590b000b005116078940d4508107030214009c9180c1490f542070040000d541c80d050500c0003085031818001444d085403c03500f043c032407840c0191950303012202c440d1252559118402030a846401a00c1c480c0500074200747c01078860320780d52100c201640d03080742218003610059a03404001003010340f0050202940356046642101c0b0406000304402c00c520790542c10a03400750059241c0c07007c403000c075005020072219006001d420216040010104a09070403480003e00252005079401c2071400781c0110300c42a00c02032481599240c8d120880b107500804500300740b0040e00032074000c030004035110001401800080c241555814400c00e01031300a402c40981007810312402d03943c5540c6d10307480d10b40e8072401f081e400ea46950340852103005510511a42c4440041c0c900c00d914442c1c0440d414081e5403021454070ba040c000380285c003070b4006014860155241a00103507802c505903400c50302c0d0301c0c005107103d007074242010011105503114008020041d1043d200340894843c106007184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 290101807 1250 290100557 290100619
    0x1020a180e09060601080a0f11040e1f0b0c07030b040f120c150203070302091009090b0a03080f0a020307050604030f0807020615010305090a05010906060303030e0d020a0809 76
    0xd459040345048925266980148098086400400040040c0010000e40100090030054166a9089040710150144188030703089141405079a03c41114100090001c0e1036440080d54880c0d07980c003000f682d244d0207100701c80f030b400305803150100510300b4840020318400c6114000e0320f41d0903850f030b224016400310a44007265128600c048607010300c0384014112128040c145805403807034881da01c0b04488118070b82c3c5247c1030702c0e900102041c1a9406541101c0c00c1c403074054400452b201300700c100a003106099205555500741400e6400d04280745c16601d410650b40d0007048903041c001d401c0c00d80c0c00550004025107040d072008001500c081081003000300c1c8141e00c2a6115650130109600c000c2017413601030482070035035100c44203014601c41070701252140a1001e1030002581e40d2101c180070b1404d542c048016100d0351078000075605001c00c9800007001d880c0691420f0105640380344065503920484061800181c02c84c0f5001c0c800600d8000061034445001070800c0c242c500702604440d010a80742c0c190b8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 290103057 1250 290101807 290101817
    0x20c060a0203040b22080d0806010f2d0801050a050105041503110409020a02070501080723090d06021801020a030f030906020702150a110106050a051311030903031005030109021507050f01020a 84
    0x403d40c145030301d039016006004080003401f410740101c10094000e010203404541404081050040c44500c105001d1000780003010205001da150096502280268003124a0015040300c001252504090318005c04440045e03544901d05840c2c92140383d905400404584105030301d83c81e02c001c250340b84d40054000b60800c0070005940300e240b0f1401030301d01405030307220360b0602c00c2842c10403040a410000309a40c0c20b0003018288155081a1121070703280c4154a40c0a0344094a03a041d0024014150f0181041007046200648480810b800590765000101e00060010b402c12583d108814800d4000c2c0884a00c5114050305050b2583d0002c0e80400f240034200d60542004a911f130625503100d40c05400008400001b0404581080c01262600d0050b0103424054061000c2c1c944c1c0c04905c0303602591000151810040d2641032480100d5203991044d10541641c00c3e20820104a40c40c0622444070079550062811075401c0d01e6109800307442e0010303001a6003d00030301c1c040040300701c000e000501030351480741d4031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 290104307 1250 290103057 290103097
    0x8041205030409050a09080d02070203010b030d020f070806010e1b09060703082e270f0c080c03280e0d090911090307050d020a030f0f031e020c060a0203040b 69
    0xf04200f2034100400340351601d4203100c11035012581c10030465804d41c0183c94056528200350001c070780901300c0b8081a50301341c884d1400b400c0301158003103107083c038a00d040025144d0060b0b40740c42141c0e85a07420301441030842c600f8000700707074400d0010301c000681e40e0300108264100040c6c0e00010f4980d4020b8501500803402450401c001c01250354401d40410203441d289d01061510602c6041007414a0b005aa00e81d1080c0034440c0440040c1302c01200c41e0303800241d410300c000003a409404028003960709074080403034828004554107004a42c2964850301240180e0300c580581c00a0340400410300301182c004d12650381480c101101801d02825070240400e4a42807001450120301c0300c102e403142404040d4003c0288100e0380c0541c6c0100340c880072201c0803100e00707048600d40d0000540781c3e0701c181c1c030040c61104020008001c01800b4400966103900039118a940e83d143d0080100340b17945407009040040e000708040c002d0038a0820017504e0170901910403207042c951201303480500d40d0321001c0407035000084848 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 290105557 1250 290104307 290104319
    0x9150702060f06091b090d080315090106050703020a0204050c070b0907150201020a1704110a06020a0b060105030402090f04150f0603050706020f070b0706090206070f020931080412050304 82
    0x2e6801e40100058503090314501c2c3c021550120819101c8144554140005040609a0b5030f9985500401c0d080710b100c0d55030b81032081015991606192002c5c2c01401080000226540500142c80141d901a00079059003d403a42c200300082000910422400105002100c04281105425442600b022004221850415580c1c80400b0004190b07002168010845180c200e584145010901e200620103280d4580350380c07401d28880d0403000070550b00500c10300d5000940550010301c0440c114050951030b001398032000011900c81c8022030700030350406100c034042440300c8000003d16034024090104c20b48a000e0120406003035502c0c0d20700c03500d080368540000788240300050080300700a040303500040581944403810203444030914403402d0034a001c007280b5001804015040070f6020b90f801040d9650303400c0e203403a02c1c02101001c2c1d40b00340d0092031a4400555044042c1c103012240311040b0301000c40d59112085c045403805601c050899001105000000d641d185411006092a101360051500e03181002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 290106807 1250 290105557 290105581
    0x4080307111207031404080d170f010f0e0402041407030b090a060311010c062a030e0601080613050304050d030f020d050427150902130501021b06030915070206 70
    0x300000064100008806450500320b0440720030743d9260508030710b030002103141a2501d00031540502031b1800b4090240c5461507001c0007030301058504c5800600e4545130000448c003603c10034095400d4002c4c09080c00e009511202d84000c0d4814130082003c940400c080d000d0f00d0010302d040c0e80800200791030b50340908503803404c403e800d85d0001d110039007046003d2a50701c9c1c0c40407100c500c98a441c140301c4100f01d0501400840e81180101e02a5500302400240d440400a0044c02c080c85031301000929100400d50382040201c1e01d076040b9a0581e0080405464007240205144050714040f00c1c3c5203c10040040e9170345641d0303085421503000f522825200c2c080e0103000303404c0050480c0c15000300032003048180048110302c40400515010804210001995980c9200041140040989080310020740c0000c00c0b120f00c1e0001c0c060084034180007503959683d60016030380d5040c0003c1e040780e50103200c0814407160815001440d07000380c000c3c0480c4c0035000c00c039071042c104400982c2d82c2001078200c00b04110585d181c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 290107913 1106 290106807 290106827
    0x60f0c040803181c020102060a021803060a020307020618061b0f0d050105010e190b03130b0115081006050a03050c09030304090f0c170f0601020a0b04080307 69
    0x980402244102c00c40b550300c2103180802c040c290402c85800004c803140e040e002410300340c81d846038803006500402003503521841070798a440300b140d0781004024000c9020348001070762400c0004000f810114020030f009140026001400d070b1030800042c03410f43c4a0340804200b11701c01c0d142c4001ea2200e00c20302d403a01c0e00040000c580600040c171035500081c12102e090320b60009a80c241010b00000904c404001e000114012500b00001d101c2d100095600c0000c07d036004240040c15038903a94280740c207800228058554000d0000681d4009454580100c0c07144441480185411801040c40c030070b58001030304054582c004185411802000d564001c14020700380c4e510307203403990300c420028905161000340c45414604140001400380850040890a128039a20541d80310901121010409409d45046115092101c40860145900b4034011482005240d60340c0c209100010015040 = true := by decide +kernel

theorem cover : BRFrame.Cov 289928057 290107913 := by
  have h0 := BRFrame.cov_init 289928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289928057 ≤ n) (h2 : n < 290107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
