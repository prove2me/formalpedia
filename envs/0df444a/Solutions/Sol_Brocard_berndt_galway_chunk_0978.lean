-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0978
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:37:12.690981+00:00
-- url     : https://prove2.me/submissions/22e84913-6295-4be0-8e8c-b544e686a142

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175719424 ≤ n < 175899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175720674 1250 175719424 175719437
    0x201b09060a24211b05160201200d0305010f0602010b031504050312040b160807141b010504050a140604111c050f0123072705030a03121505060a0c02060d060303 70
    0x71104d440e0402d28a20100d0b105114041240c02004098828042c81741902428034445030116040c0a1540c6207500c218480d20303002e845602c2c1d0706075401d43d000c1c1e81a070381c48802071b0141c80d449140aa08983d80c03d650b8945c907520207015800240350005071a44c2c40b0380714800344d90400c00c1e014908034a0420550341120309410800802c07901000070a03683e1752102051034544c4450038075000180c4608071034003601121070b100059520402c014406612083d01034200204114601030178010340744e240590084982040c0c82d1641c258038803000a980b4040e0707070130981002d13030f400320003040180c00200c00b87ca081c0c1040d009464a000314500380100c03043c140380200042060000983d803400c2c0c1460141903c0b45042d002c1c424041100c2d4401c1c0d40a03003851f00c0c400c2c052901011706185010300c9a40340c1c0b1895151181003002810198032052034000c8011340ca505002440d400308000418900a026298021701c061040354901407155030a00c100e1400a402c00b86003000c60704c114001c1d9231181c1c1041c0c010540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175721924 1250 175720674 175720691
    0xe0a0b0a03030e1305060f040c030212090307120201020a08070e03010e0615041104031e02190609030b0a0902101409090406020a0e0603040f03201b09060a2421 70
    0x2403413105242e112000c01070800071071801c4800140403285034100300d400f50350b65012804203640aa41121800b4040e059602041c0c0341140395030781d03030f0383c0860b0003268a80102034403503004500500a4a804003000c0d21840060350b04c0540448120011400c1c941d815901c4210760400d00c40c051080da80180300d80001240004102c3d4180030642c1c000c1448007407524000c10040020904081491400141c02403d1100c9451240001458044810300c1e207060070006d820000b0f500340c0c006c2081c4086900c2410302414130f60b1580906800c45650942c040d400000e102d011548203403043c10488808841007000c0350500324108041241c1e050200d83c1201c03007640c001202200c042c2c02c101d00075090700c401c0741c005242d85070564500c1860403102900034103014007140350382812040441c401441402c03c900b210078410022146000d1550307a038110a000b819680c012540e5800d05502c0442650100b01c404000301a01d11103402884d40d02c288004c08100c4200312105822404000c0343e014041200c9020034440e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175723174 1250 175721924 175721929
    0xb0a1e020705030d09080304031e0b091605010912020907120213080c030a150b010e0d20090c0f0f0702030703030f0207090614270a0c11030a05040e0a0b0a03030e 71
    0x207403002c241c41817201640c810400c6500020844084d03d610036005605101d5100c074002c240011500014000001d1404110001100140b08446180307040311440780c1c180e880c801502c00c0002030152000442d41002c02201506080c480c03550030078084c1c40c3c400004400c074040d5008982003001e0000c080c46680e501000708140801105060001c101c029080640d4640e550b120b40705500304003d045541c40c1c001102441c0c0c0100b0b030303001c0310030300c00f81588030f0f1103886180c060700321100c40c02003004861a0b60540d00396810b054030320742d100e00302c5060b1051904902d55880800c0f0b030040f200b01c01c0701400401444006803010722180d0015842600d0390f407d0340400c1280a030030b080c4550400e00d0a10300d0101c0401030781410300d1400c101c5880941d03c0c0c2c46544030a03140c0088a17016011402c3c803407c8a0000d009410129600140c050754942c0d40d1383e10140c11401101d9120711030702030303071100040c0c05200601c0300c408080c68107038006c098203c0000d455040700c404543c000b401a4030035404143e040c07050740c2d07460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175724424 1250 175723174 175723183
    0xd020405061f020a0201080a380a0608091005070509130603050706031b020a0c06120b090f01050102011a1807051605030a0801080c10080601050c0304030b04020315100b0a1e02070503 80
    0xb02503283c080c27006051741d40084c04610303030340146031034031031806200c0041d0303a10044c07104070038200058a000b00640c0c5800000d0181c000c00c0d100c90404d88101c2d4260b15450500b4411240a940f42c0e948035480d0418140070420702e101111000d0408541c0e07802c0000000d10f08003e00c400030603690700c010030004031f64901c1000c10240b0300542001c1d50421010000010400451401a00c007a41801700d04600040300710002040e11110540c6c01420000901c0312000e420580c45048400984c0203000c501083d88101424100c10203160f80c10041d9501d02225011500c000203a0000e03c40c42d28506098000e160541601c0e90382c1070903240c44d0400568041420303448000b076400342c01c0001c000d00d0a00100404600d814884c054414204101100843d1b00c0d607105404072a9982142c10850303450f82c1c0c4034246041d498509603000c03842441407491501d0541c462000940c0300d1051001100c04007858240f40070f00c80e5000308159010440e92103119104082564000d250340c030100d030700410a45084c5014140350 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175725674 1250 175724424 175724431
    0xf0904061a1203040905190914120403020108010b0a020c15040302010e09060102030a032d1a0406030b01171c080430110307080a020d12050103020d020405061f020a020108 75
    0x742c01c0069907041d0121002080b5002c0312035038140002e142c6d8400000701300e01201c2014104000303051003800d80c203100301011a5488000014242c40c1c06504501510f40c080c882d501c8000c0c04035040c05c004224001c4040c01503c0b40940381d005a81c55038000d032001860b925000811800754103c0400d00340250350740f0514241101400f80da030008142841800170307590307029546042e41090307254a03014036000c0302c119643c0040f03022028050b0650f0b040d918000041d10150b20815641e02540442c599149010f0141c0000c80f0340100c079030030041e401e018044251803450030f074051a92094044203084520303146000304203a0900d50301c000b07480c20700d441c06c8241c1800c0ca460002c0c071101a40d0104c4181d4002032280700540105085c1040011054031f031643c214020b103440906004400f0414610941d00891220b40d520096500c00c110704c8200c084680807640b080c0406500100200b09900042c14280d111940144000740315411881040c4481491070030a5000c14006800c05690a021941c1000000380c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175726924 1250 175725674 175725679
    0x60c010908040e040b13080304080a0c02030709020a020609070f0605070f080301030f03030506040c27080102030a05091006080607030207060e0607021011090f091009020a02031c1a010e0f0904061a 86
    0x10385040ca845401f6035020181002d040d031100007450014042c02081d03e02e419960113000c0d5203e4a0fa100080c20082d04010390362400b50080c040010b00e1201d0106000d801e480d1402e1034540c1c0c40c0c1c10001c0459058000343c8040340c0001e15000c01001081014024500940c031404016407091038600d4000c042d87d40c00344c203c0b4040c9040008100403c1e400122800a4070301340d185186015540704c003001d10001e0903070311800c00d42d480042403180440c05904040c1c482d4106004481c11219004100d00840398a44115044c54200c1400f19401d41e00c85d400800a26008004c0810350b0000c00f464a41000740940d10003025a01c1401034545190990159420140c5106002420202c1450200e000300183c449140e01c40d040359800189454645090480075010105045455440d01c4030003956980c084031040d0a444608100042c0a60b500e0190031540601e0402031400e6003404401950700b21224203240b68008101e070620302c03654030b800b040036120f1801810702140100303290301003000c01103000b880c02c0e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175728174 1250 175726924 175726951
    0x40305160c030c0b121906030204050907091b0207140409021c0510090b22050a0605040308160e0f0a090e010527070b0a030b04140402010923060c010908040e040b 71
    0x17259030b040340c01d200e079206040c80c2d0703200500d68000030102c0043c100f42d08001e500c10302d44001e01c5007241000815100b502c00104041000030800c014640b20081c4204600380180c0c09018203000e5440740b450401103165004d800416488126400102da0744c080d8000b140035854614450300c28084200101264040b0720842001044220340303c03807514000c0241030704009400c1380c00c001a014100801070485a4200060350011036891500c0800f0701001d8030144c0000e1a64008102010780840c24042c0004450720743c450400e82400602060503081e851640d4804603803100003070840203500402800c0c81001000040600c1e1484409208461201c0c4d0100c44403d01001c50711111000500401078171542104581c468440c1d0800f20301400b140c00c41182c2060800000761450040d024146010754800d8a61440b00703516000b504403c03010364011140403c03c00d10f01c42e81d603030a00d80000e03e85000100004920031040c5c0e251003c56a00a41c0207104600c0914100010300c10040c0256402c1036401d003004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175729424 1250 175728174 175728187
    0x101215060e12190f050c06030613091b08010209031908090d0809150301050405070305090d1b05340e010303050f0c0607020d030c080609040605040305160c030c0b 71
    0x51a038a03112600d40d002e100d5405520158081c00c00004602d0300c2c1e11018000c0c5290940b40c0200301610b0b030b050464051090480e41c0d8002d14260040d24442d0f28003400318a410380d4104090001780c4030f103100645a290b035880724105c08034180f2000d00d01402d0024000340c1d44d02d00f11402c2c185041d040300d1129103418420305182002842080c100c800300300b000c9070022040c3c1181d0814010034480d99018a41c410030568412140180c2440514102e800c101c0301080380d80e0b5036070700c144c003a128215000802134010403181240a40226203040c6152203200c07003540340143c5641c401c3d25000061000d07000580550b20402c01c02c0090f84020701c50400c02c1c2c81e0922a1903e000c0c0a01070300038040c000202400320224021884400d0700040d0303450981ca400c100d0f501402d003030302c0c06529241d40e28114000a4201804004060b0040011a0144801400c0c03442035681d00c0d00c0d2040103140152088080020802070300c16484050b1080b424114014201101c00e030b461454007110000319540715051841061004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175730674 1250 175729424 175729427
    0x5090c0319080a0203160615060c050a0605070c0606171e0d3605010905032b03020c060f0108070906080628020409061505072004060510121506 63
    0x2a029107500c844150307141c400183c820f90441c002d4a0f04241c110b0211055402403140c030350880510315455480040500b5108c000403180015203100c041d040e0307031228040c0000180940e01c411390061041c0390540c0951125030340d10050f54003035441a820b0740060070520414202c02e20400c5140c90004200300313480741d0140a81b540741c0240566000c00d0100d460178030b00c26010702480d0f000c40301450172048d08101007403000e07054014009010b482c1c0082c0311010041154180050340d6891172485044420201241c40240614030b4102100401055000c1c004220900001c00140d03020700e0038440040e06660402d50000d00d04030955014441060528004021519002c41c0742904100f07100c452140046040031b0b1912040d803501c00c5071001e9840010005540d074220b600803c20f443d615a06c2245c00d0030300c00001ca4403402504409048814681c00100b40018090803200240d00043c1012801e80e07a034400081300451402c00180102e01c0112040060f11990b204402201007103081001869040280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175731924 1250 175730674 175730713
    0x804030c1b051f030b0301020405060702130f050907030b0c1e07020d0b090a02031011041205010b03060a09060c030504050705040906020408030c0d02060f07230c010e0105090c03 78
    0x18201c0c0040400c1d40480c500503011400141c58060020701409071594803991041840c03000c100700003803900064004502d0f040c0201c804640000703100c18105409602040951500b10b182204565500c40c200c1004c0400b50098a01c24008000030b0500140b85042a84094074020860500031000b0000b58120b002d0f48103650031001408a9100c1d203600440c40400c0300400d0158000c0e02c00b464040c00c00c50740701800034010920398800d0b4141c0304003407842c00f03044c0241c4180407030b00d2410440c1440184118600598500c84440c09000081118214000828144002681c41041840e100c020103000c1c40706500480942da070701840c0c1048146071948845488080038000c0d14030450301c40c06c030103050110030b4060303401403d408820303a0382c1d03403200020056403905104140c80150058030009080d01d000d0b2401070b8802c60183d1100c0d85424000311001c501610f22f81c5428044190921071841e40520903c01d13228a000d016000044a04180380400c0c0b904403000d42140c800d6001c08001c2072110b08109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175733174 1250 175731924 175731947
    0x10060e010b090d06050114031009050304050906030a060501030303021b030705060c0f040305070b0318061005040f09120c060501090c020a020609030118061b0306030807150605060417060601080403 86
    0x1803030700d84600260000503405500140042c00140c01d0200102e0b070603640c4d1300001d251880440855620010f00680502907509544c00640603820511040121741062011540d00110090960b0380d4201d0b140d8074941250802c2c0c005400181c2c1c0404e2400c92010050084621003030903800850400c0382c240e840b2590f9502c020900310070802c001c1040c1c000041440240c6010b9a4000c0503103140380d88035000074200340c102320381000041c961043e81c1043d0300400710748a4000c1c0b0f0340580c0c0d00c480f1420941488090940034a80c50216640c448402021070048080400340c258541d03662082410581440b400361070040c2c12a40c01103140041d04140a80c00180304143d995050328000c2e200d481d00000a8010140d48404035010090101144c040050651048180f030012101d0804c003890f0076041241150a10300008003000c10400040c030100341c401d4482806001040d102142d00d5854401240d01600540c1c42145500080036404c2c032101024019598010b20a2810428900e8030741c800810240404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175734424 1250 175733174 175733189
    0x12020105060a05030616050c0a0305030a0f020310150207091a030c120703020904020a03050607050706200f031b0c0a02011e17100312080601320a020a0c0801020301030510060e01 78
    0x6c0380030b04121030050040d00c000314002c4099458a00403801d001d4616841141c4d0b25182c103140c601040c84540d9144241e030300800740000d064420b40d0400940c00511600b103030a040c01e512640e500050180010300034108418986150705030740c5c1d900203003494980068441414800c81820840500440f0005214030442e90100d98440f4551141d0000c075090140da0307000038001e405040c0401000e02d81000042c48060b10501040100c0441741c41c50209401e0b00c52142e1a860310200055031211190b200a0f54002181c560407041b2446004c8014030207600c181e03c2c02c2c0d40d9403c07842e0041c095682100824002e000061801c036110503180200804c1d104150304034202071a191000319403440489016040916407100441c1500f1154000140c61450115111400540c01c00100c102c4080000510b40e05d8540c0c40b00c40c1c00c50910440301c400340c03d23080354480030218410030050318017184400034010014000400010390729411170030090704007160b4550440007541070400400c8400c400390140b90441e45035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175735674 1250 175734424 175734451
    0x1180207020409061103011a030402090402041d1e071a0301060302160602070606090b01050a0f110a0506010f08060105060703020c0907050d0213090518070512031612020105060a050306 81
    0x881c07001070b00808081c880608040c0c81e1810319842c0c0d403401c2c0010740c183c584059a24600700c003d040c40c0c0b040f61004450094020410f10045401403c058101e0300c0080090b60a0b00e0900b80081011403800d0b12110100d510300c525007440f61030286051086c2e50141c20003101c01c01010780842c62500d41ca1206119000402d036001843d50030f80005949503005003640a00e040d5652055800e03c5000b40883d030150798200342c81d1080c421f0096000790212200300d2040c1c1c58008a403800c01c0030a40b80d400f44002900014000c000300e0000186003840300502a008018005007150b0034814050b02d0710320142c0007207014103400c00c80400840d40004c0c0756003000604503030000d0160344201040300c060042501d0340481a0020540140590f811070001080d039050320f00401c0076660f0410150820b00d0100030343c1c50550041103003400f046c10000030a800708202c2008aa01e0306c0030342e401111290320507580079105030720f81e6085034011640c28010140c001c1e20454880980c4c03418000081d49482000c1c0c0090002e001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175736924 1250 175735674 175735687
    0x309021c060212072d0f03050c0903030705100501060305091905010f0c02011b03180605150907020d11030403082203080c07030b010e04050d050a020c031b010e0306011802 75
    0x180b60112140407080d140110040d040c8000050304280302c50704040d000b0b2001050120f421001045804d4074019195a01e034664040c0d550141c0080030040c003030a00d01c1000b0012035107030b030f14100002c0070b20714840c2c002014907000845509044841c1038010701c081508107000e2200401c00041d000082c80b125501002002d92240752842c010b000e00540d40407402d08001903904919010340c41406071005108030b2800701c040d0144100c04a52402082144600c1e40c0080c1d400840c030280d201c550b0000f0742499507503000b0061750008040140403203000c0011713171001940081807588411800c1040c503210008604190440c2c1c4d07502018064a510407803105080d191004000f24450b17004401140c1100146650300325581d8103e4582005001c20350b00881030340700004a01280a034850b108a8201e80036021107007600c103086416178000140d1078214421071081951030707941880317118484420380c180d03001400220000074142132410000d1301c4c4a60400d0004100403c1213480490340e0100040d80140d0780d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175738174 1250 175736924 175736933
    0x10c02060a03060f0609030302010c02060708010614070c09150b0f09010804020409020a09020d0b1e01030c020307150f0c02060402090714070b0a0606090f03032a080307020a0209070309021c 83
    0x10f556848007203810741030080056801e0300b1540380801e403402640240001020a4426030b9905800c2c1e03020800a446880100005486a4060310f214000f11003c0c0f850020a5280d030031029941d5041021070580d108140b0302160501214000104510031042e4280900098036a08a005c1d0503601410301c151038001800f15600e652041c070400f0b134000d18488005413990040c100942101c0214030034607103411144511031400122440c00400070202440707802c00e00000450190040c0c94000055103c14020b0100180d0211004a881404007100103501c40c0c03a100c10206136401848a10159007080080c440980c988850310380d0f0180403410840c1821880010209a80c451360b0b0001c0d0a61100c40144075101801340c10900442d8107941e6031210050702c50101c50700303503000c601c001004a0340007520f510340a50035030b015030300d000345c5841081ca40c03001a4076040b0440e401202c1c0f45005802400d000c60840c9032030714000781c000c1c4075458100703d07200143d0302240c0e0400c840e01e56145400c071203001c01400c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175739424 1250 175738174 175738181
    0x402040f020702120d0306060912021905030f0a030201151d0601051b100e060f0a0b010c0c1403070e1b0c0a050703030c030807050a050406200102181509010c02060a03 73
    0x101d030b004c0c100c02d00e103d2207072a1090301c95042c0640400060304084d00011080c3c818519901a0703407410440380700054041d402c00000c0b030601540c6224035213207050b000440380e030244500308649400d017020744480000ca2800a00f110300e4244200c090f2000004140071100c00d80311749506002485040c090b05441b00e00050720b0724042c40c501c9614249080403090130f0040c000c1200c180d02c020080302030103110030228810b900c9000444411156a4405001611a810940100c071003a201030415075039a5010361a1001111705507040092151820300c882140c900341046030360010301052080da05a0704251645210800803898005801c01000c01e28050071072003802113407400ca038060120740030940c2e0380c03401a022016107003056000c58541d20003c1e03d024050300495812001d19598103103000d0500a0503506503448043c00103070744050103080c0f84c000409100401c1c3d00c505000720120101201020000c60015040098500b0081409426a26600804807402c04e96049407444e0315050055404c4004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175740674 1250 175739424 175739437
    0x3031101061517010e040203030906070c0812070510050402060d0209130e0d08010816030b070e031b030f01290607081201031401021315090902221703030402040f02 72
    0x103560060750160b0301d25000f0014241c00b4181c1d8941203590380c0ea604072134075841303011203001c0d4040c0c0040003030b81d644d407500d0ba000780b00d480d01c070b14002007142d40c9580000745442c551440c181c910510000c0c0c2c010078804200001d48514a201e4418040d9180c1a80070580c6401400c0340540c0300c50700820441440c1d600c2076810034251a00b01c0341003001000400031213540380c1940e182600401c1c3c1160010a007004045036034401d031041040004001483d5a0f42e003c544000100228200310040b0350240752030ba4284218440080200240700c41000d0110805003480d03002e1540740340c240c3c5403000f9840503003081e80c40e810001060107088000d40c0ca050022410318480e0850040240000050700d8a05401c90390202d0f05803402448176505010390765004500b03e12451400042c101d400d20020040140a4102050320480034a803522101d50b27981d00120581c1c00c40300041c5a6801c86d035070b002c5c40c080c025500301c100825480c00d10100c90b019a40455449202c041d01c0680120340f54110a44a40001d804a681 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175741924 1250 175740674 175740689
    0x50402010c240906140c030c121009180209070906080c1602032a0901140907030227030c03030f04091a120c0910050a0e040f020a27060b040303110106 66
    0x8581000d1804100a1005c0010050b441085401061204080006580c0301b00c04203042c0e580303460b00c01201164000301c0100303030142c4070010301c2c0c01262800407030050380b003849504242d010a9400701e00c100907021701c0083c100c41c200a0501e20801c0f00661080d80503401400c000556030b80c9034842000010081400140a500740c171901d10b103042c16181c00701200074098a03424009401c108a60208800301c2802c0c4207454180d44807101d142144d02e00722402a400c07050700e0400614080e001c500c0706100b030b01d182c05c5050403c1070114504a4500301070108110340c1008402035880d02c2d16808648440b4000c500903035102d1540c0714800100f0190440744014030b120004c0010301d101885092195451100e80d49540c01484420003042000200c84030902c2070b02c0005040040d89410903040d0044020010010b86000c2e0281c3c0d032002c007584484e121200a8200c1365448400d01018044c1d40b0741c100c0081016035109850302e0b01c20021760600c1ca050310140c075414a01845000e559044290240000c0e801020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175743174 1250 175741924 175741931
    0xc03022a01200309070906030812060d0b09031312020102032a030d05180109020310090206041a03071704020a030b0403020a0c0609080c03060105090403032414040f050402010c24 78
    0x1101c102c0c0030b00185101d0007442c411111107036103803901c440030b886007840010f1406006101f040032200c1c089405540c09000500060107025564546000c07040c1e090f591050103030400900f038134444d442120a00e0241142c60b0104180b043c3ca075000079901d1203005103003458104150061190b008800d1a0101041c003548210f0327403134001d81515100242002c0c0c9101000004051915940e031038103000715000550020b01502030041d000030305102800f51107600f203038002c9081002262650300b1107444160f8402020a00e81c0f285490b21010704003480d649031400858030200108001a81c0e1000f4481c00d40c0e0380074401445503140c40c0303816803424004000082540840c0503001c2904d0351702481e83c1c030803640c96004a802c0400d55009054480e142030080c690020038103000074002c81d00980014900142c003000c0b061221080410031466840b41d508200000c11041048004c00d1503d400745610981d0460800c1103141001c2d80082d19061503000000e0074061030028410080b542d00d01004501e4041d00800d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175744424 1250 175743174 175743221
    0x4060f14031f17060f16021f180b010e0711120d0e03070302011506050c0309190807060201050601200309090a20030a1103070c060b060f0f0304060c03022a01 69
    0x20344504d030441c0d409082c0380d500000200c4041c0380d507201403602c0c2415006070a10325420461103030464040c1c04261602a00d41d014500003142e1140c04c0742c0704501070307242600b003541031920080710003c01901980c10070810042c06900c001003c54038040c0c1c0d03801d2660140d51000103d00c001c000d0040c082ca5103089000c04a2034005054041d0002880f1111900580c0c0707509444107025143ea0280f0040b00c0800c1c0d00605c1300740c050f4101982c0c034040521a0101c0c5030f6602da0b4407083e01d442d0110301c1d000240141d448206105207940c201003211401d00010350f91103586084003c1703a958038043c54485078030a41084000c03a8200a0650181d42100078440001862440c50b184820603544191a907400380341c51f2001888105a044082e00c1c029403450b502c000c04c2e000c40d502e41d44003910100300100d0b440302c410000c10b2101e880314802001071224880d012034613031a180c00c1c0714088852480e00070040c50f00400c148294040c0662215081c164000c911298140e12401c01c00e00500040284c26142c58041006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175745674 1250 175744424 175744469
    0x518030115031103010b12030a03051806070f030b03011a06030403030b091503160501080606071a07030902120c01050a230d02030f070c03231306030204060f14031f 72
    0xf0b090503001360000e0144507440c0c404e020015020043c100196041800500c012a00ca5003000c1d42060491520907042c0304511919800d10030207480c03a101140f01040412406505030040c0b18010100720003c001e18904a1400d07100b515810310341314401e0710000700080c1014007d07441801c00f102c001d4103a001d14030740044035404d00b1881b1044d0754480e01c10f031503c02e0200c8007203881401c15100c040e500d030005c584440c8180401500000c200303d40d1000740c1902300c2802c910308140345108114959002c28400c10b6070045c0320142c00f4411960f915138205401a21007641c01400722800038031940340001950807010000503e05400900c440751031880050f0800242103a90003030350285c1501c141111403a00d448800f96503005401c007000b40440c3e01c004090701140c0c80020701c103441d0074420400c40d04c4c1c1a00018182c00803a5240c0103000403d502007000e0005503071010421041d403210b030824503160507065207030340980e006c000c241034440758a0704000018050b4110014005203400000003640d40040144c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175746924 1250 175745674 175745693
    0xe0109030e040f0b06040e0919260a0e090604090c09092306010902130302031c090b0a050412051507080a0c0c11040504060e1603050f0d051803011503 66
    0x3551481181403d45a098800241c8035400c3d0642d030040c035541c0303010b01d412105a8624070040001e030f03190041c100f80300341e8080784418210f0054403500700307801d115201c02001c4407100b4a2034048647c41000f440310140c0315400c00b00080250340115441c250f241e84072400900508540380000300142c13a143d400040d00304158000c504c00700d10030f209885803041c05850700c0c2c0d41c03143e00c07030312182032584a000108510808c60b801032080240c14140c0c6500213032a5004246801a450540303072100c054800000b10f1039900003c448003414034038860500d044908100241180660b010b41040c2203a40514501048000c00c021a420894421654220316020740090905801140c225100381d04002c0c0fa4036407688242034490303446501055000003d0341107410720008040c014011580f45031b8406e06044515010000c118a5408440c5085541829803500904000f882500030b54980c0c8480220420540c00c00113807221924000c0849542078580c100090240260f1001d02c4554041c132940401031115001c17 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175748174 1250 175746924 175746947
    0x220803070804080912010e06090109031b021f0503090d1d010528020a05100b0603010303030902040603020406090e150702071211090c0c161410030e010c0806031207080d020d0e010903 80
    0x1c1c22360751180d0700e43d9082826216103e8000300068036403c100b020756078440810b0405c11b80084c02d0410481c5140c3c40341540c103607290f10100c0201c0c6000c010058046420003042d10061482e00d08940003210b102c0340000003080d285141410b104d008911074111410384040d205040c030950440000c03c0075200c2c1d01944230f0b00142401d8a80b80038403c1200440304032401014151017001e041585960300c0d580b8101c0050140110403607005450b41c41c0040503075264003407030000c1c040b85840014500070314410286880f850703040c802580943d01c070070440525004a0320b207084441690344105041c2e028070b4074039096441c5080003036014064074144104244610003070111045412708480000e24000441d00f00054940708e14101d440c04015820b69070704000c8006e08d0001111704021070740001e0540403070301f5a02d442c0c0b260070005600c0c03010001d0b2450304104603440c20816402ca20f181191507124400944030720154146010740000341c0e10a013409a40c029400e02030300e4002005140564640144100d1520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175749424 1250 175748174 175748201
    0x9150307060810060f051306020d1b080318150c0409060602010203090c100212040306090605070813030503070e121e070f0e06032422080307080408091201 68
    0x35404a03095002d206003e0141c0e403042c0da40310405151003c1100c103181000c40c2c2c0410414140901c0c203e1111403080680a420550040c0450401c8400020030a000004d92502802c206a100b2808130744400101c80e04803c0c443c4c40c04401c0d481c2040c1040c0b501c81d040c10b9019002502c42e08208400b1003610152041d01c064031014400c45544038000c83c00d03804180c41c81442038200e46002d014030310b00030404092a60b0580182c8690104500040f020351700b0941c800c0d58103d032a03407a8601000b41c10f114081e4001490b0030110860308040c0d203013001c0c0398007100c4010140300c400001304007868000c4400c222200e20080121850f200841c1c20182c9030100462030708124050381c1c41d2601c0d802c10110703030032040d12103990030345041c541303000c4402c01940c401501e5a84c050040091802403018038903e80b5482c01044400011241000300f0841d102403410918040e901d1100a124030014003440c0480c0d03080142032500742c80b152102e00305000140700310341c0850703884044031401c10300040040d0440541c5a424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175750674 1250 175749424 175749433
    0x9080a0303020a030b041a0d0204150902041419090504050c0604060c0b1501020a03052508040f0b0901120f0605030316030809030f030f07050706090b060f0f03030d1802091503 77
    0x8205c00d01090321030490b0240d15503142d48448007098180f030007603041c426000500110303132039024418441548401350414800c5980004041c00086404410360f1203100c8140c996410380e520340b1100214688040c0038404801c0d4944001c1414030030104844407041000078001590382d6a00d00c0040e060707602c80c200466003a8100000515800d401c3c4414000594042c0c0241204418a641c211842c0d0312040c0c13051800c003851014000c280540107212440790748241d030350540c0c4900b810030070f81071034655a00c040741d142420482c0ca400b90740e0010310313400d00843c03900000c035052950354042c9001e41070700c0e00503a4052101050991254040c480c1c842141c0740030381c80b807208a0b11640c103100d07241d00c10b04100495084040000c248001c0044c1c00807540b200352840c1203424518641d9440b41680d42800c406d88200d861003080c1701252400550604a08004071075010032a0003510129032280250305101100a603a0754002c0002c44d00829103110950380204150366501c1c0800b20810300148070b8122038080c1c800d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175751924 1250 175750674 175750691
    0x4060309020f120d0509010909140106020f01050112060e1908041a042d030b0702030711040e0a11180901050103060c0810030f1502120604231609080a0303020a03 71
    0x1840343c80807100c525100007825142e003084c101692a40d01460600d0304015a5100000c0c0c00303d1103119014070760200030040780480d490854003d14000c00c455203030960b40d140100400140c164402e01c0600d595000d040401c1e40c0c00a000080d04000038248807001e2620414007100401107400d00500c140c0e110724015000300c98403040c2d0a4118003490150742241c2d80c070b080c80c01d50380702100f0981004070020152059281d94995688000718882581c041025910108683c000c002c11402c03d2a030101042c1c5041120108203e010349d500d00d485000641401030b40410341c14952240c0000204039240080e66510780d0400840e6140200024401620741c40e103024000c4c54214410142d950041c142c24800f006200c1c03c43e00c070f0540c03100364000100da510702c402140c055031800d0360014040550a0b100681443c0c6000c0c402d000c02e8a82c400c0880050190310101100f2913044400c0d203541001402e0700750101d82004580603203d219694200c04058031a0030313000000c156054004204a420350341d4140035104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175753174 1250 175751924 175751929
    0x100915020f16050f030d02070201090510080f0405190c030b16080c13051c03080f0c04091a030102040b04090c0e10081506030a060f0e0c0901050a020304080304060309020f 75
    0x104201c40240281c02c0112520000c082c0501241c0640650140c5106000850a00f451503002006403c0c07201c1d00415030105541e0000b40e100000c0174140d0b90480e00b8a00d005000740440344c001c2c1900740509550b4085030500c107040160049160749926000640406410080345d150510320085407480c2100000444121031000710f05c0c006003180d11a92169140c00e4a10400740c2c20ac0041e606d4100d580c400c0006d265035410134812140e0f80721040744d417100758a5050090410900400344084a092101841b41d042d404000300d03002c98101110003e0003403004860076011a110101081c1d1542c0042008205000684001c20499003169402c00c10341f015041c0a89840300e4900300d041e401425944a203000d107026180655012080011079410002030784000755003a0000c1d50780030850b0380d23650001d2201024000e0301001405100d0114030a900d404414940580b107240c1101c0e04200c4041881309489000b00141e402400b1040c041e01e440d2a1600402001058050800d9124400501c40c410b400d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175754424 1250 175753174 175753177
    0x6100e100e010b0c190b060909010b090a1d0d02010519051501031a040e0d030c081323010203010315180302060703021b010617160f05010c1410091502 66
    0x390424050208160310380f03200c0d0601038100401c004294000c0c603e41101d0440c05010403501a88111401201400c020083c006184002050008241c0c500030011030b0a84d0780e00f02c201d611075140800818845444840b00c1f00c60081c0d5104101c461044580d03500d0602c0d01900b0441c400c50103002291505143c40b00d5541c00d03120f0603034000382c0c500340302c1e0340800003944030342c1010034044d41a450360200c0344441d4000c03404030b400240440d001070b00081d00d80d0f03400d1039249c01024100c580754a4600142d050000e030800140c051200c00411145d0400d03020300280e06140b004c0300122040d1070003191250703501e05203408069190182c04420901c0d02800c0600c4c084500e07441009180c2560040c01c00369503d040c2a0300075444080d8826000080d101800d0a10342c00340103040c05419210000e10140011803c4107140140c0c0a44440903940a180c0a002a290700720035881250402d1910080d100180c1c2041d0640800540c80c00c296030160261100701c0082c1c43d040f2105c05d42c850607103080d48150a05514049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175755674 1250 175754424 175754429
    0x5090105160e04020703030605030a0302010f0506011713050c10112407031e020d09060b010507080304060216060501031202060a05010b090910081f0f093206100e10 72
    0x20420b1400d40781810b0500798040c192251090a0000725540c031400001d240100032807003100142e44a40700d441520bd128024079402c50000c2c20444003580f01c500c80380c194203030014901c6044c4c42003400c41340d00303000f020032401403030030800751083e9a52001002d00904280a01a001c506403260160054080680001066031140c696a1154054070380a904802419010201e01d10040b640031001050766a5407004106070b043c004030000d0710b0303050b524000c0180c45101512a0500400740078a0001c6002d001c100ca03401a0320010040e580d40182104c01041c41c840e04000d0915840c1130004020040750b880704010720a895000c960b459075482c2549030613143d00b400394041d00e1354140700c22400f07401c02441081e000240c080003c1a0551104000c40c50320a510302c044644544003d1403800842c0c01d4030858070760b010300340d400784602601130311420748100040c0f51700c1b0300d12260013000c42801c0f24000d80303400841c0c42050940700079003070004a401303160280d401044080391861020503249034480501508 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175756924 1250 175755674 175755677
    0x120c0f1205040311030a0f1103030c0f03090109170403051b06041a0c0610061b0305270a0b09120120090310240503160e0a021605010509010516 63
    0x1050303082103120010741000341040b410f002d29520800800c0034144090200c441403965101516500c00c0402886051060709540e800c0d041001800030308440d2608580f01040d20900142e40d940750500040d004009010b000b408860088030407403c1c2501040040003182d00800885908500002064404400d028421a884032040000b04511718030504509410204003155504211420052070b084c000304039500480500030000510407260450b0500c8031440303151110900c00c0c2486d942c0a045446400503850382c1d060850522800e6107074404172500e01600181c86507052954841100c1c581d40c008508191160003071200748143c0001c14031514500d00c0c5590000e0582c00d0756415000259881040c80c0d0790140142103825540305624021508003138580807031290100c50145280c00404030a800103486030304140100c541102500408506a070310311000d0120b6510b800345c001300284224640c09104290058488041c03000c1035121a00c1111500000e02c000ea440385d81c001c40d8031030440360500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175758174 1250 175756924 175756937
    0x221120604200c0d021e030f130b12040b0109150302040207081215030705010504060509011107091a0a1a0a0810030c080604030906050309030f0c030d0c120c0f 70
    0x10014034094202c00d80140624a000d1841100049030108a03403000180302d090340d00c5400000e4015904100d090411104540700c0100030078007204290310303031280f0110340404000c04503440000e40e98949298000b0216418410758a291f501d50500413001c1c2203900740d640211520001a1103100b6000f00c94002407801c540180c49821542004029044543d003903c07500d9083c04443d0b130101c071800d0700902880071034000e1608414410200340c41c000302600b00360b0403c2001d010400500e80c11400f0741d03081007002d00300091000c0c1c0c01083c6c1840c0811607031200c581c0d18101222400300348064520100c03501015101c444003a52140d03170303080d620010f40715000e8150b0b00401c4070604440c07184c16042c2c0c0110b201d40c60424140d949440d6100c021809400213162a0851401d1108260300050100014031035418950704528280c405d5903103c0c081c5104001004000155130704e500301c0113004449034035842c1d40c801c000b1240d0500f001000c10b1031031703080814000d182418809542d4040d01c0c001c44520216602c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175759424 1250 175758174 175758181
    0x60a060e100303080406200715021201050103050411031b04060f030503030403050a180f091506020606150403120203030613020c062d0403030506190803040902030c0d050403022112 79
    0x1103400c0c140082080d02c003103946111f0b9034641c548220310404c0007036540d04a1500c0e0340d07040c01c00f07a03851056061560300309441000160111310764000c0c031904440c02400d001803150360310304202c00340460910703685515000c0e00c07114103103206100301402c2030010250340801810303032280d10400b020226800040c095a106200041c0021710420017040711502c40d1520813100c1c0c171107245c0b4249000b001e4114840814014100b0321a441c074501c07642d0154907006a10041141c03404101948505020307252602a00710401502d6035003081038210740065078855050307140000320010094417a00181d8865108030320703452041200c11030310700a48000c403015102412a03a00c1d400c889900218034556141e001b1451000c0d00701d00314051a000900c44c2d07010b5280400c00b80313003807010000c0e9410382c05104148403544a40a101080300001541d0603502d04100050703882e260f00400081a005443c82910983d0030b00081100301036006c240c00c1e6a915850105081000540000d118180100d400740031540d50001c000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175760674 1250 175759424 175759427
    0x9050a09200d061503230603010207020303130e070801030b0a1a04020d0b090c0c030708030402040204150c0510050c07030f210b09130302100f1d060a060e100303 71
    0x5150010100940c80c054aa11403654070020707008034100e0802a035980b4000c000c2114031349001d00704010b4616007080590140c900c1080b0300740c1c2c17104100d001800d40000107100382d1401d6044842d203d0b002002c07282c84441c61605000d0002c070a000e518070f00880b00c800b1070880c601a4a00ea4141c2c0e9015206100f0366503040b0030800200704544a103031401e2155000080d041c0c85034402420006104c0c0e070302280d01800e0909008560f20050052400b020040141100c01c0102000395a274040d1300031880ca41d280c2741c9000041c043d01507038020080580621303100e80308040d000241c00010b80d200b071096900c2c000348001100d0803918116007540704500704122642c0040d205030300058140202c0d0511a4500014140000305a0091000e02c1d8203a0382d50301041d40c00e45001c500d0b140c0e00c800e40740740e10400d46000307690080d2500104958004d90a0f22202c4a00d442d00b2031350000c11080c0707412a18801001d6284980c29503c07441030f240468401d01c5e0800105188030b10086540c82021011013601242d46035550 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175761924 1250 175760674 175760681
    0x4090201020304230a030b48040801060803031803070c06180801050106050a02010b0402030705040b0f25140106080303180f030705030c060112020d0f0201050705010504051b0109050a09 81
    0x40101c139024011441c0b0340740d50750034a50740255001d04802d01c11450044100361007040a001494014282139901034500d0351901080c020004003411a52042d0600840d1a9168040e80d0080072080d424180080b5544034000040d505c01d102c1e0140a4200c2c00420b2034003522840385200c05040360081c1a030500c4070318010000120a42a50201050a9640c030800c550850780207812140c00036100045070302c882c50f8240501880560300301c40071880d41c28943d202401c40d11940c410741c544140082408140800c802c0d09803140e40420842c2090f240040144840c0350b040c0c1450100c4038142c44407070181130040c0501c11103050700e0141d03008628640b1204440c448010307031455001000d01c0307032401040080b0001d0014050207032140d8006c50312565455031345420400e05810a032680402695000056501c21360740c000b1403508078580b021b1a04403400102c5251007800c4010302150700b00030600041100c0000c41e2500c0c80f61010f80e140040c84007000440300203080b0b100705640155200c8041c89840c995030b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175763174 1250 175761924 175761959
    0x6030b030a060b0310050708090706180e0705120106050301030201080c0901120506030a02030109050705030111030907060c030e09040b090615090a2708031b090303180a0911041404090201020304 85
    0x13412248410034030025a020745504131f81100000d2078800510003020420094070021b46410f0414582c201056105404c000129124142404d0000808500c1a6000d0f4003120b000b4034074014032495668607410050b041c2d40c07013031004a000480c2d6074000b45c8440703144c006440264070145c2d110b0589110580b08030001c1c00c806030800740d060190016035001070340c09120308403803248070710054025189003004240c00c480f10038000c1a4609420000c110400308049411400c3d59858100020264128141241d4810740d80c3c0b0910380005040b010322003403204d0184080c4c4102c00301800c40f50b80342d945070a403218007040f01e03500780d405c50301039000b0a20795080f5400100498060310726080000c45c08070707420072039000c044a040d529890000709100c80351030082504071001e0b101c0030101e032624a142c40443d0381c0703200d02c40305004001f00f6285070743c5140e6074074400900104441c140601203542c02c80e02e2036600741d0140c03040d031243c07419181c051402030516015aa80d115016000b130350a0a280181c01d142460051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175764424 1250 175763174 175763179
    0x40f05151912020c0105180a02100c030311030106120b010f020c0112110a0c060605010c02212a01080f0f2202060304230c0a1707050303041203020706030b030a060b 72
    0x51401801c0c40340300344060302ea650320707130800801e4501700000034984034408414030314050f0b0840c103031060140c0c403210313400f0800c10007030325100c8202480c6081c204d00030002047d50149900001000080940d804070810180361444242081800610030040d0340c1800c9048070031000da0000070070340d041507002d1001c80d013920803c3c060104814020700c2049010754012500003001c1000c400250051220703d1050002901c800e00b4060060140340d000901580801030343c4150140850f2100e006200c42400540d4140f00b074490b8000d035508000b0906400d607c1c045040c4e90000d1600000100d0851400c028903004101c40e070340140507074030780d10341600511403200c0f000c072440305542a000b401611000021441030740244104441c080e03019448444480900500704025448842d0414095803894194001c84207495a0903800c2c0e1500071040381013640903807200c3e5050001080010f078034240c040e8113205182c0309600380c0b04c001c0d40f40c910590440d4000501143c2541c40200031900240441d4414260302400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175765674 1250 175764424 175764437
    0x30b071407140105040b2409070e030708030c0d140702040b030f0703230102090f13060302090c070303051003030c0204050402010e09090c011e051603090515040f051519 74
    0x701c1e199842d514111000d034919aa55410400003801101c840c01500640702c0c84100c001c1c940403500e80d5030b05000c1d414005200700c581c10f010a000390f0164105d2041c845010381921006607483c0740031901e030b400c444a8003403d8001c0740e199080e4a440307402a07410500e81c03647c602c1e09101294081c07000819019401a03018071508034480d483d20000c010303a00040d40300e006074850300e080c010040b59410310290101d220a2f0f0040c05618225980c0c22501240300409945010403040d00203801d034050001b036800030f504030036200203002c0d42440d4000180840c3e40651414030054070f0f07420402c0070112240c80013400080400e5000c000500c1c20760441d50300940149018909000322000041144034140d174000c00d15804244041a10f507000408001d2400703510403a4800200d682c50058010b00c640640c1070b04454081c44d9540405020b14000005004060202401540c03c2010503519900c140142b40d104074104e80001154901800815444081e8448080c20052a121024480b40140c0750450a0126 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175766924 1250 175765674 175765687
    0x1507020304080313030c0506090607060f0f1a0a050906010c0f03030f051603060f06051204170a110f031c0b01112a090f040305031f060e1009030b0714 66
    0x2e042001d080040384c403410685040d0700c0c2d85801005c00c0040d034007942c0035903c14461442c0300e94841c402e59148503008007007c00c64112541c0d0b00001030000407600580316290040415400140e120700300420b0405540851019803107108000b00098100c840500058165000000140d0b8410842880c603210341808038040d81d0602c0d150b070666400700e03800121a0b00c1c100300301e1503941d41405018010880b0096103040d450030a0401401489010520171202103c0c01c0480c040040102005000020a081c0d203a00c5078a480c0c07000700900704000ca10055446942c070b480c074003036030088100d070240900c1300e070741480008404410b44003174001c00320050b050082d0f000300106d074840d040c880e1115004000c0c2c442c01c400050080d41e10144100c406549000b80d1090301005000040070b90000c1d049501414200d860341e44101008204107201512a0705a0744c0c4004000f0328140c0201202e404003170100c0302c084030015404d03022148003055100107882803a04001062419009619102c6d1112001282c40e14061 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175768174 1250 175766924 175766939
    0x50606062503120f0507141804150f080111091c050616111f0504050307210311071208060102030c0a1b08030f030412030605090708040b15031507020304 67
    0x40002058001c42c100548502c0f0f40f41c8035201e041c511203030704e040804c214107026400421002c58444101d03556100025034248074084040307071102840008000380a0101c0b030a56441c091000c520440381c03010740341c6401281c0c0b41010302031450580c0d544050380703040101e00002c00c24190328201c8400004a040b400c40b801160080c00309901c42c110805007412101c0902d40008d0000d07541f0441c03000c07160001250040c200c0189141024640000c1001244540311424644d00307610455a00512020a07950844220360b5035442006e114411742d103040107a29030405d00c00d05a1b01ca4070500400e04855441515030090040a0081d009001032040300e05000c401c0349210b28003000380c0e406543d10401d040a01c80e0880b00302d9840005410802c0141d8146441080d40d1138083c00b000e0f2000300310440600c000d0880c03912036405080101801805d0360100d0070500b1007e48034041c19181658442c11900000c0e290f048041031180b541c8101400030030119040460324030300384102901001c1140801c01001a121 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175769424 1250 175768174 175768237
    0x40204061706060108130b0105040c02191a010e0403050d0504050f010c03090203061e04110f0a06030c030c05040803040b07060e07060f090e010e06060307090b0c0703060b04050405060606 82
    0x841d90081c24241488070015250400051000280141c46001d080001e012058028116001607034045404034000206a050500d02d18140c40c51445800509007442492901d440140d0781c550131564080c0d890304045c003211801101c026000c81c0c01040600c40f400e066074003c95009002e8010b48100e2100c2682c8035080d500d00c000d030b00000035156a00503040d072505000d50ba030000c40705240001e180042d090500780e4190028001f4150080011010b40582c8a00400d2095498014001d68440762500e00c09401003021464420000c0d1420b0358118001f0302031012541a0303511400118101460410f0464a80d48140d00c100c2e44c0c44d485603858003120900700514030250030b05480e000901101d03000c0003010103107a54460341203180385000400a001c1e0400381c0c95001001510001d580755a420002d503034640b81d6502412002c0d000107210b402d007032008541542600d1084d5810302c02990410b08000075281d068078081d040c2c0d00300a000c40d02d145001801022407949520849024105d103401d0341081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175770674 1250 175769424 175769459
    0x1512021210060f05090403020604031107030b16020c090105031207020a170c1c0c0302010c1a0103050c0a0801020f03160c06020c070312031505090601021515040b03150c0304020406 79
    0x4154488009020410310401c1d018050704c4240d0b168940d40c5001e450081da0b8a102401c060107001400c1484d440c070034828013000d0050358108055588602700012810901c840c191050401030050758503203241c074136110711010b040f907100900a01991018017100d8540344e005c8281240d00c00410341001a4001c0078090001010b1040343c044c142c00444001440801241c000c10040e49940b21003494001540c40e08041d01a2502882c000c1c084150901c0e01d054401c80c800c40508100c80d07072100000800034006500056258151051044650365034002403c0c0d0040600304018032205100144040003000400d110750030a0340b030140070000f441d07100c401c01ca80c01107074042001e8010308000d000344507141070041080c5110786030130041d41c02032035228180d00d03550340559407042c583c1c040414900e80c420000c0d41c0881c2d034095110403c5e03041c00281c1000706420164107900440c207140b4005120716011524000b25480140040348603aa0081014100c1d40010310032a4400d5070340380081503a00c101040d002a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175771924 1250 175770674 175770703
    0x1005100e1e040c080415020a0306030803040b0103050c060f030f100b0d140606070f030e01050d0c02011a011e21110d05010b03100329270115120212 65
    0x107014004500b40000d40d4111800714060049800030700000425403640042d04040c0f10b02e006071100806d90f0301f00e000d4150340e80003802007035020013404248491441254101ca100b80c4c200e820744084417080c0604c5024103181da01c5040802d2001030150301917818002d0380724100301810b02c00e20381c5407512020281c2081c0d68440c0040d9440b04040300c3c0c55031290b90541c1284044034100c0c1050019074a9400c0106404c4000b020003091200a521903401841030750304084400205018001d0900350082c020090120b0710000140c29a201001550042071504295001c040b542010b00c06400c5042e1a42d000100c44084035640500080c5a14042441101200c62841842980e28000030a241c1c09550741038010880c00b00080003485144d40031140c000c0103ca521688080c03000141003140c5240f0300c031444280150b8100c0200300302d1059904582c802c00f02080a036480c1d101c4400d001490300720303200c2c0d466014071080d040c001400b00042402c51002050710040ca40406001e4444c0c50500b003640d031031020385 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175773174 1250 175771924 175771969
    0x37050a0803090c0303071518140d0e150403021c1a060906031c03150305030d061805010302030d050c031b01050604061a07080903120708090103141005100e 68
    0xc6840d505022205092904134025400c00100c1e403500d641c482d240b410100350707855681c4440004801c56100c3c2018058105840000031135900c4091629411000500741c0003c170045080c40c4685440813040b048080080d106a04081c259420710050010f40d0204034041c240103855403000071410718009141c0c80c51010759001608201082c416583e9019103868800e1304641500d040b1808040d0180c12a10804d140c003180810f07120702101509002a00f01030700e9404001203500c0f4100345030b0042c504489920030000080441c1141d07540440c2c2083c000258076400258880120f1442580506101c040820540303203803103004079083c0740042d4814100d0540c1c0e511601009464502846220003c040c180c0e44070f906c000500c3c2c4240054811080020001e023004501c6101e0740e10200100c4000e0740e03c5042c455920702c3c05c1e06040764903400400320b060000c0e082036aa00c0f410120000c0060054020079003130440f16060a0400c0407001080040c08100840b90364000040da80d843c40c0c1c1c0070441120403110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175774424 1250 175773174 175773181
    0x20a1b050a0605090d030302180a03050f0606190603091703041101020d03021e07110a03030203091c0302060f070210110705061513090206090a1806050337050a0803 72
    0x1c08160140c0d4040c5040c03003018881c0704041e0b210300151014103545840c2c016540d00c810000d4400d8008608005504005c0030382003c41001300000702d5400017003081040700c03a03554a050030801c400755540b61214156001880400540d802070308444030030ba2003162034450042280c21410141c0c2c200321001d5844542c4110b0219907560107004102c1d4901951900751b1a1240c0c10401d22101d0340c103003040b0780c51240c001a0a00c18894035803202203000794020001400c4503541e013002503807608030640720351041c02100e40a0307a94600c400581091a5810b401400295490340d140b041c00f800300411980940c041c0854556480c1d8041c429058101c030b02b00702c2d0f1500c5003241e00b04135140c0b46004003041d20303500400d00902c80d031f5516842468084940070101003143e94103480424414080c01c42032a8110119500100b9200c2c08040b005404021129007000702650318410140d4854180901c1e5500c8902142016642000722040b80c0007500d04800300c3c29a40515664181380c80748180342a243c000c40030050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175775674 1250 175774424 175774429
    0x30b060d061b084203030f22030c0b1c05010b0c10020903061602010e030d0c0e0901230301060e090607021005190e0f011a010e010215010504020901020a1b05 69
    0x3c540d0802107540ba4400074031140c05040004c000401e0f40d554a800300c00300b0090015500c0c03450b40c0034641c0058240c1c0d0300c6040080000560303400c0b040000450f84000040902c10000e0555801e0460b0f800002c0c20450601d0480d0001203030740030400010350101c00400f43c41407020789014150003008182c03046552582076020301c0b81001550b804030707040d0a004101080895a0004e9415082248070040001025510034260300411840300c1d218179a0001042030401032880d036110040201d180d0301e40c01351880509007000b40340c1001340541000b00300b46040d01280004110740400d02c0d100003400010f00300b80c0f1000318800d11a412200c4142c5e50703005c01c04004c0350700d078140000d45002a4054040c040d80c10001030016042c44241e45002c65960707034041c002e021070703005c01c03080c4540394400c40200148440808400c0c1c02a020710112400728628031040d0f03d00354400590b614bd1840c14190084169080c00100406580301d148400c2c114410300c9982c5001c0340c419025501809004403014800c14644006e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175776924 1250 175775674 175775687
    0x1107020411040614161e06050a1a0d0b0f0a0902090a0225110105030601050706050f0106081602030919150504030b0106091410090f0f0806010b04030309030b060d061b 73
    0x2c04c80d400200380030984150f4000240a08503541c00020400c2c00c10749070348641171210b04050060030150501d010300000303585c16800101c001c1c2e030304000d004255542000b4420300752042c1c2001810b90b000c002c0001c540210311540107410801400b0b02142081c1181c00040c0503500c240c54007919183c3c0001c8502458056468116100c0d80090700b070200404162034201010f4480d0250a040c020000005000e0368442c1080300d640745c0e4849410442400d0030340d103d03c03201c0424081d200c0807800310f4002c504810b404480c501028ad03110790046190108074400c1c01810000b4800280388005c030030030003107012180c0d64080c8400c5480d43c0d448940761444c504101c8118039041c0d2144051181c180e07000e10800c0000c1032a109c0341c940c1030320504135045a00804840d0f400c042d60007065103e070801d002103400c042e00b10b061821503604208490305a6285c20800259208500c130003000316003904410000500c5801d41c2c2c981c46640101820100709040e1a45002d030380d805e46a41170001c0f0341d95003014000340c0080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175778174 1250 175776924 175776947
    0x3050c010509070803040303052101120215032202060f0a0c0c060f08010306050613050a020d050603010c0207150e130c020d020703030e0d141509061308040911070204110406 76
    0xb802003241c549045079a40c0c507031140e0302001d0100900012001c2105e80001c1c03501086080c0c0705050080d944c4d44007060f0001040c0d0900c00c0340300d45c035184490107810000d01e0a80313002e40c4220611508180d28040da44501b8041c010040b6000a020300640507040010750107020038101036103682038031800350b10380034841100ba60409428011006140281142e02000d050305490740688002019168030001840180740c250040814a0600c0200b0840200c981c0140100c10250801440140c650000305401e07a06500078280041e481468104241c040c076500780025011581081001c8040040c0411002c46140c5140c5005c00d4450074070340241641000303c2c0540421074405406545d046d950002d1140f08034030701140c8200c454101442c240140c107181c2100d02921541160344100b1200000c5480702c0702141c405005001d80400240c030700005038000b4040c81c0d40a120a85800c0c20045884004c1500c0045a80c80000c207010180060f25244904e00c0fa050000405544891610340d00408901e50321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175779424 1250 175778174 175778191
    0x90e150f09010f0f06020706020309060a0e04050901021b0c090c090111010509030307141903110d180507061b0f031b0c2409140301020f0d02130b03160c030e060703050c0105 76
    0x880c2048000d0f400300984104be0400c03101541e803802091000c0359264080d030981a4070514100500c11a03080560060090b6600e80080300289030759076003c0c1c0d40744c1e06010500340d000139039100001c046020200c020701e10001e0504001122040004103142100c100311800c44680d440082072000c1c10341c12406940c51320b110302050910308422052904410300e07085580400389503d8019885410014400303403522541070440411400300b0b0607088402014400009440c00d014100001c83c4480c41100140009850104104610310150f030764541c00101031380c1c0540801000c016001848903044807030001c0f803401051883e14050510360302c0303000d40b0641100c00714111240f4100d00c0e045600312804030100d44810001896510b19080424007a20a40c0c081404800d00014038440c01a103d070f02070301a04001c400300c05565030311591403550b2840300740d4104041d07410070b01c0d51515030b0f40319181c5c41001c54440d25101c00b0020f9100045a4660000c610403000b1810110300c0c152480000d02c542940000398 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175780674 1250 175779424 175779433
    0x9010f14060d0f230102090a0803040e150a090c0c030806030c0f130b0607081b0a03050301052112071a10030803180304140f01090e150f09010f0f0602 66
    0x103031000520785810000c00501c07820280500906104038880c681a911310034803c2a541d40b950112003034001e510050840744140d281c02004114001c1c000259403d031004483d159071181c40d915120300146120540c0315500c0881c0090206507241540100082c400c0152a08030008001c2d14003d441d58100800c514042d501c0003141c0d020076954040300c420b00342c0080d40c060a580700e41840344000f52101d200308641103440080c100e01000b4500004000d8811070010006020400c16040d54451425280140c00038030140010f2007c3d1401d400811000790560100900800385140c07039a0520480c840e1150001001240d240e040c009a42c00380314004840ea8609034243c90000c4005401403814000603040c0c1d940440000c9a100389907105c0e44880040c44216900c1c0d590720140c800541d000c001f121400352503540440c074182d500070178145080d6410341e1988170003591102840d20700588007262465000a00b20b20500c19178903501000c41c040d0000c158012012428000c034074a80001592020b01107520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175781924 1250 175780674 175780681
    0x303030e0a0b01051909050c03070f0201140604020a020309040501030c150306080d030504030c240b06130b03061302071202062404050c1c1d0318042309010f14 70
    0x40c00e0b0141592021181121030481c040308942d0000080d401c510000c6141c041809a0046c580b00a0f6101d007829503604082d11394035810407802d032503155000820079103d45c40031911904d000c3e0084c0c05458100e01c1240d04003000a00001e09581c02a44140c4010040309000d1144200900c1d01d0080410a401d041c0005803603d9450f03592911205918000c1540c1c4502040030180304040c050f09003500290401c200d207608242014040e0703100d6203030085052510200380c07442d0a1840540e00311986240c480300c05030703160800e04a40b5600041c2496072203800f01c444101ea20340d1a01c0131380822400b039522030680030b0340c0010280c6012405410000c0400c0104510b240a4001c10790849002c03100b681c0c04259a10780400b9454107003d200f13210354030452600c440c01e1041c6c506034840c07130403a8032080c0c022144041400c9101d803244200c24000f100c0030303c215281003241c181030f000038089078400400032550300b03040c46901d0182d11003903d100c04585d44607401420107807854050415519801080700c03001e0305 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175783174 1250 175781924 175781933
    0x4060b0105130b0306040e0d030b0916020a0b0a1803050c07060201050105090c090a150203030a0614010225150c0507050117070e130501090c090902040f060c11100503010303030e0a 79
    0x24810710681070f01c0c000000025a4584a580150100e030040e081124012003e056002d00a00b80e01000e8500814554000581c1c9200b0102d0010703048040d50003403c403500098a034040744c03500007000d031012140c68022144020010a80310000e403806036640d1501da030b461401250400210341d0008046a051100501c200d03035400c1c13045d5410175050000b0541d54603403e80841c0c0340d201c3e2540000050358401a45040990f0040025403140c0c03500401040095142c2c040d0711110103000f4a00d40c0180d1002c410101000e141390141c1164400241d450500d850307450000c0402c8103440c41d441d10010300419140010070400b001914044c000900b032140310b51000d0403111400c8000142050100308585000a000d80c50700c00794a8502807130518180065a104c0307500d40d01a214a04e06040054503c2e240068808464420303030382655044a08024140c2c9020b1084400b289105426544103110620340e01c440c1d5900658040e44e00000d17103a40d40c5a43c91400d019084615090307130306c0c004e40c00c034281040019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175784424 1250 175783174 175783207
    0x6010501050d09020402160b1e1609031202070e10060e1c0204050f090c0103090c050108091e0d270905180303010306020711120718020d0f0504060b0105 67
    0x15202072a020b62680980003070070024210300380c2c1c042c1d0041d200194029140034814811b50080317004040100454031440e040d03402d44860030100360001013441e00072415041140341c03031a0042c541450103040c035035220f80f50100c2c1840010760101c0540d000e0384040008411401c0c00e40d0380951300341d142000c07003468001d01505021256a1851081020201801040d0301c0c040301c540c80d803600078008219504d05001d1501c5112020b550550080c030030040a04925031084c0201c032802588030304000d284928090041d1032030701d00036141c4080340c09118094070895031290207045a5a0030f800c000c0180a5501c08058003c1001c00c8001d00e0010169540d51004480100040115401c4050008083e0384480040207541c804c51224001400000000024055150080c02d50640a4040c1e41249c103400401c009174803440c216039810540002a0401c209500c0c0c4002002c50520900094540480d10710b405040380c250443c50071809640e4000d01042c410306100710096840c007800e24130701d00441c030140503091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175785674 1250 175784424 175784429
    0xd020a0b0a032316050c032101050d0309140315040b0f01050105040b072a170c0f130f110a0309050c01081909061104271116061d030702030601170601 66
    0x4103051211311592520542c1106d0b140d024200c144da17103c04500c4000360200400c0d441c4282c14200300c00002c1154a003803041e21140d184d042e104c000d03190b460082c0010a170182c03041c0d016818041c0d40001c40e051244d440b40c140c0f050313120744040043c1d40f0f441d0a00d403c06400c1038010300d0410105110910070004038a084400d0107800c0f407a4a4034041e1003828914181c069400d030721200321030120340000d40900e07280903103030481c02c180c003030320a1150075506001d26180c81e200030507800a5003104080c4445066413001a80d19115100804c1104400d800c51420764490040000001d0380c070b0a8100900c841807000d24607100307003403829545a0500982100960700401003030244a81d8031920f030340800126501007400c40310280d01c4103407a2543c1d0b00a581c4400700080428025002041c5190801c0b0281d1185a500207410102ca82c1400c241c0f040b00c04c08030340b010300d0440ba641e66883e02040f40780c5141c0045451004681e0042d5a5501c80c1d20506060100c103a0105104540880b0380d1143e114001c5440c130705 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175786924 1250 175785674 175785691
    0x7030b0d020108040f081303050714030c060307090f14120c1011071a1c02040305210c011505010323060d031e050901090806061e0d020a0b0a0323 64
    0x200d0304d480c145401e9104400758001c03c078174000140400310580d11b5850104a034010303000d641640c0c0d5216040074040040b00040b507403540003400302008519200003c0e540003000c51a0840f81c0d5903c40085441108c41504501c03038400404420030440c0ca00a000c9410a22412014100e010002c0c0301064009900780d0490040c004025110321072000100040300081044a1080304190160800031346141c3c8092461920880300c000c00030f0321507000f402107501f2691701400410356201d1010116054807800c0e0011b460540d030401280b84442803d004500607846008420300050786820700240481d8401c4414032080110100c6040d10412210b11199105100b0b5405c50081052072134201e8031659812603520001480c21146442941e00c0409440341070001c2e00c81e000115110b584556403441d00300d812644c8505001c000701040c0300f824900c4410108050701030300b03c02c0c1c09030380000d803001d03982c0e0811203047d100410028080c0e0740c5802050a5411064101c1c2c809504609480c0040c0300001c11800c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175788174 1250 175786924 175786937
    0x6140405131a15060f090405180a0b150301020d0e010f0b0607080307051b0d02060a02030c22050301110d0b0a03050a06050c0d050903030a151203320c0607030b0d0201 73
    0x2c0d10b0390f01c45403106540e218002c2440340e443d4070070a182c00140d00040219402146007600003200414034805804a1452240041602c80c1c00380c0e50740d041c03090300103281d91841403140011700d401e03450034000f4004054110801052801c1004582402c603050040b50142075400c02110f01e200e5122070781100c000c00c2d04086c4155881e910060300340d94503c41d01051030740c0140c02e01014000420301094002c11754072a81e09440c12a140c0c03003070620513800103840420001008020070188204016030131700042848451001000355560006030840300240e920b09a48600020000c02e45030407803040b01c1d0b00102c00c03100080c1d0f0a043d80c444075511480d03407100500c2290317941c0108a40080840942c2d0110400c03e8041c4600d1404048440d2a900b082c2c0310364901e581407504e10041c00e0601403001c020b41d500f400c0c002000580d262002c803000d0340b23204104410b800302c8860307070030302c001c008a8510b20380113a40782c44944c1e640603a40c00c1868040001c1c10302080603d80301d07040082ea42c443c0c3c40d50341590313024170701036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175789424 1250 175788174 175788181
    0xe040f060302090906040b010905040816020d0b091509010903050301120809271e070c030519020304150e0a090e03190e01020705030f0309010f0203040906140405131a 73
    0x80006110300e4001030740c01003c07482008200040040c18511403403040c0d044400d20b0b40d031600c070070007921025034004181c55002d002010324507428006078a4094001404109a250643c560300c001090a664042154001c0001c45203000340303005001d504040c0c41c41c000c01800301c031618003c056000602501181c40290940031061015550a941000c40014041c000c0200c02015080c038840300d03810040c400e803294030002410782d50510360b01070050400281c0d0f0030880e80c4e440000c54561000303c80440900c14103010100d031a100113180c4c543c0d500f800d500156030301e500381164031710b181050450345030801414184140580e25040f0442044407691080450a0710040d81c0050640c099922442070322907010f41c487e00c8150b40f01400039481031003a002c4e2441e854840f000e0544441c070440c00c0580c103a01c104800c40d02944111060000403019205490415444030b15000c00da03006c40c0e0040c00900018101900a49090b104007908010f4141c02a1480545135441c05801941c800e410700d05403003000000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175790674 1250 175789424 175789451
    0x602030601020f0d09050906040b0901090c110a200a030c0e040212060a0507080108030c250f030821070c12141c0f0b130203070309020a03050f06070f0e04 68
    0x3d90485001c80e081d00d14004000c1d000501c4140c0c075100751071180c62080301083d81d030300b02071040c0043c000014110f41c0c803070781c209407040010b0000e5012030420010949103803001b4000500035035007840d110b0503158400d480c0072211000d001d21000715041c8a140030000410000b80d15201090441d1000509408280c0e2680005804c1140b2041d94580b07502860003041000301590344403500c20f094585480c80c2698840d05540e07a24000c3c9901c074402944201b140c1da5075214107801c1800071030003c3c115010a01d03280d0804100040d03041d8400c03251441c0c00300709020300c42d120f551300f0914080c0c1e12000403043c0c904524020081840b1400c003509840c5540307025020b003442040382000319042030348410341c0e940d0500c000340034010000c940301c0c00807442c06910003148074403401030410084000f0304040c070784540c121040c002503202821503003d2640c1d1703018450041c1c6400221340700540c045d0000c0e0983c0b01821001c5414100d0040c5072200b001280d1030520080d80e00035a20300304001040d035000030442c101038807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175791924 1250 175790674 175790683
    0x31202070306090b0619050604061d100801060f020c10210608030a02120702060306011d0a14040b01090b030726040f030210020301060518030312090c10050405030703060203060102 79
    0x7029020350b080001110502c00c922400328002d40040d1410401010801148011402c550059941c0050304000400c185403207440c20034041c400c00ba11100d0401420340000b0b418035655408071010a907007000401800e9040480c101c0e081303000303001424001c1803010015410603000c0c0306000600c50710308418140700070480260104240d01030400c0140700e8403150071a031f59400c500701441c011700c6050002403042052038181c50b00241d029201c1400c1d80c95520064681c0c407842e0640480740c00c10740c0c83c030341800d958031080c000c01440210020f00d458460901408190760405c6071311414030402c4030b4208002ea1001003281da1008181c9803017080e144021480c1d406003102c0d24215542400224180401d02041510090070a4030039000c407001103508000b0b00b0b003a0302003441070001040c0141701c140c00d5480c80703843ca50001100102903030703d40340060801ca50254420b441440d22a808034107441624200410814551004c900f00305080c00c0c541800241d403604503000041c1000d8000c07000c500d040c0d0003040b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175793174 1250 175791924 175791929
    0x24060c170f031306091a1b0403080a0305090a0506040807140a02101202070209100603050f0112021504031a040203010c0201110306040903090e0112030206070311070609020102070f1205240103120207 87
    0x1b9100f06240c4a980000c036510081902c0c40c003101450280c030349404040303860440b0101c03540425503504198940c8001d0303000342402401500355010b1180d803940003880c284526845140304213449500c454140c05c19143c00840840a10455800504400090303580c0c84807481d02c01080d4680114510420f41c1440049d0103910002500207903464248425943c03010b2814043e2103040d0790400c81644c6034221040d43e203030b00b071183c41d00a0f403040041a015042000e01070107420031803408030b071500790703a03036140f6103820a00b04c41a8400709030f4038188403c51400b030189400221080c070003402443d90911540380c040c070018143c01c1c0f117540e45048000c1018001d48245000b42070340303051084190383d581c010030306040420b64114014041d610000712441e0092189090101301103c03110300380140381e80c072000201581070059047d4070840c080000c0c511000000d182c0034240840c01c9003a05189441c24038a001c040310300c007a00c20110510601210900c00d4110303411a604115500d1300d000882d00243e08190498 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175794424 1250 175793174 175793183
    0xc1201050115051815190305090c061918030c080318030601050105040612060b22050d0f02040c1101020f0405090a0501060c0b1815040201020d0c051024060c170f03130609 75
    0x19201c0d1b000085d019403089101d0b1102105440c5064201da00b0003203075200d070000f4900007a501c05200611039120b0018202c012050170300c40b070702550b00c0f529104040c540740e500c0351005510010fa010b0007030000f06c08981e80024154000d101950604001170f0450007103002d030100700a00010120041f80446c1c01400c028240a0070035036642c00d1003070342500025140c001c0322850218560700001d1a0074050100e004a542259030012580d100741e08110262078000095000c01c6421400700c603ca100078402007012014031840d0523500ca240506100804400602c0b10048070f241c1801085030300e80085c51070519a84c4481c04018559400b01c4481d800441015080381d544110300e40c900c0e07600f4089031554000c0b8000d8080343d0540c00100d6044400d0b20300900300901c190022441e4804c029540d42040b6041501006034160b80e44076070026030065a0140c0c41040010380d4040b0000c00e00c821000e8061081c13076500c00e0a86011620480380e4020310014000c107000ca0701740d140d034400388400e44d880f00715540d600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175795674 1250 175794424 175794457
    0x91a01111b010c0804030c0512030c15070e0a0b040602070b040b040510050d020d05100e060d03030506010c140102030f010b030106050901180918120c031b02030c1201050115051815 79
    0x182d05042011280d103016040c003039081d09c070901d08847c400105945000b032100e0000e0089041d1442e100f044543c018202d1028030119003003081c02a0742c5c540407038004c3c10079a501103498074039105000b1f10f0b02e841ea0b4003030303e420f40b42000b0911200041c00212030589905403407a100040d08550701f00c1e20b500c594000148014400703c0e0a0305058840c0d0007060040c04a108001440343c0c84180400c2c44100c140c88190b0700a48100181c0c0000e07000343c000d1540301205040c9041680d4041d00c4ea0f5010250f44520041c075654000200b110001040e58640c1c05442007a042c0c1f4203640c11b0100140c00da108903150a41840101c00c1812400e07074134418424050220701c1c2040c0401e0040e428031704c1c80c80300507850407101ca041946084414903c01c55900d9041900356495086c01020710f1002d01c1fa201c0c1003001a44c06000d007032100c89080d151244044500ea500e071000050a6142c50594a10351415448003000c00c2002c022419003075907001943d0764116001c8600c010b21054414509240c0d11070900b6108080c00ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175796924 1250 175795674 175795679
    0x807020d0813031b0608060d1103010608150a18080f09120d08150d1b05090709060207050108070c0b090c10030905011d0a0b04060e010501091a01111b010c0804 70
    0x1041d00c00e000880b41300700309a180a034003070b1030344001c0c2c46481d000d0200000d110600085503032618141812200e070003112511405c1d60030001003400d5030480e400680580d40714004200c3c80d8140c0503e40d560041406070700300041444408600b1404102c51409840f461000c00c80c1203100001004450500000410035049030669071030980e00c82c2c26002c1d02002158240b130010340ca0b441600d040070400b00000705071007001e140680d100700341481c0c16044035020a0006001007016112401d200e0301075143c40e1196480030380342587c02842c01c031076500308504000c402c0c03052000c0c40d600aa1842455a809818234841e69101c001e520b141c4424021130603442008030389661b4840f509a846441c125008400a1015102c1070700880d46081d04c0c3c00001c82c0503842400800041440c0e480c015030094892140451510500099a42903800a0300300200301e0f9547d10019102880c20500102032032020f003011103c02d241c050324591511600c401c960094494021b15800c0e50307105d0090b204641d58030120841e00d664 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175798174 1250 175796924 175796947
    0x10080115020c030a0b040203100e0c1e09040305071e0f080a170f090f010b06090103020c070909050106050f27070e1e011103070804061803050a050604020108160c0807020d08 76
    0x5170b040e1016800303402114020341040358503028001d0300c070286d4401401c40704804402e1066000e40f400c0310380e016884291464a60356200e1020500850283da286919038202c0d040030301c84078124915444955041a0390709000548000c100656660031204268803082c440d8801d8a01c0c030006c071504010b2010540030851005a880c42c035601078000310045907031194940300790030300322120403042580c494814840c0080d00c2d842500180b10510411041e00e4650703036034100450a99503c15030450312a512013106100d02d081140e00c4500c1410200c44000c4002988941c0303072001a41d1049200081c1d071240d0000301d0042c001c04146840b81000f80981819500c0e0140100c030804002c0d441c0d070b000426004420503013038400001d440240350410825854145494029690710310000b0381003100002c102000004501c040c41175500050042001e001c4920307141c40014150900188001c0204c0203501003803840f581e02a00c50f40d503250b4040042952850345000084440c5001000245654030000e461503490 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175799424 1250 175798174 175798193
    0x50702010c0f11030301030b090708100c030c0503060117071b03110c150a030b03070b0a0c03030b060301080c040f020c25080d120209011101020a1d10080115020c030a 73
    0x300c580c0c1c0d0702020120b526608849081d2220040d49660b4424401400481c00310800d060b0001d98110442e50115a0f402a1a0500240c14100c600b010391b5454150000c541600030705401c0405440d1091070b600d081000030749081c0341407801d100c1e01003070040040ea840780110945c480761440702e41004113041992134018a0101c00d89124185802100c2080030036041170140e1a510713015801c074250030500320341d00440c024100d480100d40d16100ea02c1d0005106803a01000305400b8040350b440d1040807450341030141c1075408403411140079207002c0004000820b00411903d00e5170204440200388041080c40000207401482201800c900442c1c0b40500032070980f02d00038081d4085d4001d8103850307560710003046490f10358001c4c241d40491401041840403c5c601c0e0300603c8126014108941222035001c2101d08a0700b1948005010604490000605580d2804c0c201075200e421030743c601480c1203d90b401070031b80700107106a421414440b0407032010346000344050014508080c003180c05640075401d200500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175800674 1250 175799424 175799441
    0x5070f062706140603030324090a0608010b010806060f0c03040506040e01050306090c01020d0804081605010209040f180f020112110403110609010f0f02151512070e06040b0d0605070201 81
    0x140f6158080402483d001c6a00d0b204804c002d01440c00d41c1e480d94044610504411541200006400103030030142d40c4400403a8010a503c150001d01107040c0044c139402c4a500245060501c02c000c03080101694030072040312107010002100c0b54803000040307000e0b803960107103401c481d52066000c02c0c085200b50b4050340d124102e0707004600700e0f2419145c00c18603035200d2545124090060700032004601256000385000e40d0410306c101c0300b25203050b5030103111111001e200001122207035000901c0c081b8518140c065180030300c41c195010401d844c1712040d00d08450809000091403440d07100d0b207000941e03000d0485280c07800203c060902c50113014424040c2541d00c0740c0400c562108806045038254100700042d10f000c00c006840e08600110540790640e43c0e520194440300452090a04c0ca050320418280120300a1406690700701402446004011440080d0122030080c0d500400b003c000001c2c560950030742010003034070006410035000c004180e60ba42c040700060120340c03e01040c4105554158040d404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175801924 1250 175800674 175800683
    0x3120c0601060f05120402120f0c03010e4e0702010f0e10080a0f090302010b0a0801050c0301090b04090c030308100506040501020709020c010906050403110706030b0105070f0627 78
    0xe036038070b0320703001d441c0701101d01c0b48800000c0c014004204028a0107150641150008021104000907241038038546510042c141880e0740199104400e541001d0003a1000d00001d5405000240d42580c501107640c8480c29114207001c4443c048900c02d90b000e01c40c00c3c402c107840c03a04000482260b54150050750351003008101d0002e51b214040e0180584100e50314081504014042e01d0b030406104411903854001900c038a155540e5a421002200342500c1201c02c4140301c3d400115055680400f00801000c05501c040140c0c6d0520701003000503401030b01164195600341c800000c10900c1c040c0428003e111300c100041c034148030f105001c0300307064002501e1031060683d214880801900c43c1c0174008140500e10486015901040e000d0220080c181c024000012100c0000603540c50300e6100c01c02a1034040d80d0503404220340681c96140850305118000203412340f402c0910200c400000004c1c040c3c4039040300980ac02c40d0390b110300420014660026062130704e01250400000c42c05a00c010450301c10706400300c3c4c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175803174 1250 175801924 175801933
    0xf0d030504061716300b09010e0f16022a040c03090c051c0501060621020a3005010906090b0109080d030203060607080f0304021c0b2403120c 62
    0x200b410a500071038034404d8800e0301c50203149a41c4020282c507100e007040400901000d2542040b101c40240c000a18909100317014042900c030b4040040c000440c006070130090881141c3c5c02001207000e02e002e202c903080802d40e03000101c440200340080f070414048000c0402d02c2810194881820070707245940003060802140d04001444c800c5405800300c81d1a6a0f004000e4204410100814a0040d080c044100c1002c480c140d0300283c142d0307c80c4d0171503c054020134040b4013807002c2030700c070700b07034500b102400401c19100114504aa60340c00a00300c0680000a085441c020009800d4071604900040c203450408400500c4296102d205002c081c0141d8010041e020303181c903101c031000e50310507a003a07411a031154010344004416000110b01a41c40101002d030030140c01c01c41c950004050381c000b0800c0e507210410240c0ca908107031040190030116080880900d03c107502c3c1c004041400542002d0b00001602014080081140d4a400b821071180d17140d15414041c040100040007007050051031074084031020784 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175804424 1250 175803174 175803197
    0x71a0a1b0b04080c010e070803030901150e0c030c0904020c06011e0b0306101b05030301180e0312060103062310050307020a030309030c0b0703090c080c01020a060b0f0d03050406 78
    0x108000310a8010240650001c0d50200d80411a454028a41c0c80f010030000304035400d62440032031a110f0380307900105a03503000008000319a40c082c4500c0c00300b81400b10409080c4c81c40e0403c1014482d04c06414113a400e02d0000214503008002c1048400c80d8201900540d1a465005040d903100c0109114042c1ca880c06034070600b03070610240c0141d4040d500d03612001801d54445005100c400740700410030b82c080c449404120203014403a40d40c5e41215a116000850ba2903044c4110412000088c00c0354249407420159a860b06900c0031050714207289200c20590166543c0200403400303040f40e6448000d03262003200031140c82d8828003c03107401c580c40c262038500d20341e602c101b0304441c14402110342d940140c001403502c03030000b07120740c01c44c1c0c0f54140245854141c6442c1612051040e0314251518008290341d000548d00300480c01c1204c0d00100f0442010744060388444001035255224a940107150955600c00c43c581680c403414501c454a08c054042c0380c103034030305140103002035100b4000d03007000c240f070071104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175805674 1250 175804424 175804457
    0x13020c1209010c0609080408011b020c030120180901060203090f0319020105070f0605010b0307020f0a0b01091d030703170112020105090108090309040e010f0b040510120302071a0a 79
    0x12159070060694940081d00d40c10703107512004001045c3d00315010307007007044001001c00090060058103040914006107064074100b01910b0074415400c20381c066410038490203001d848850f464444001c103100c026030b9956060303103540c0000240e069115800403414001107822a03000003c3d1a0188041d141d00c01807407692010942d0703520301d181c44901507a0100b001503005500c9280034140651140d4004211054555900c409640098014548161004c820004180e03810030418401c0c000101c00b030401081e803a100c0c51076040381405103040d5036440b030701e6460403140d41c4081c07101e03454440020340e61a00f282d445c1c01400c50005e041101c21400c485400800c14948011580300001d034140c40e038a203040030200054400780c0d402040c882980c0028008c0c241c07241c880c2d0046078401c040b09400041c800300d222801c0021110641c010702d001ea0b151030200a0b2000c4486911820f941910750150901d801300c5c81d04034640300c0a0381007242400100340c9090b000d4821000075200e40c01d9140c13600000d4118020780c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175806924 1250 175805674 175805677
    0x2180d05030406030c1103070b070f03090b010b180a181d071e030209070905030106091503060b150a030b03121c0905070506040303080109050f0405070911070213020c12 74
    0x2009000c0707410802c802c00c40640203900c4200c0741c4819007031521104850142c4a82160840b000594140906004100e090350340b00509520b103150f82e040030031101c6026214207840c0b120500a0b20100d200c00a69400c5042c03158201c20206000200809585611b406156025902842e2800040c0d82440011a180c0d2151a00c1c4050b6a6010303004007111858440c2022f00c904a5080011001100b50800300c0135844d81021a44945603a0716142e01c0c5c6487c100c20b241c210f42907540488140d41c03404907541107058154903140100c80d0402004188400e12200058201210030b00c040300101f400180ae019554040c0c00805201404405032410b00804c800d101500c5d01c141000441840300903414400040760b207502242c4410301030812181280d4403100400c580ea4060782080d40819040001001898001e0061940c800010701102c10301d414190740d610741e00d01c00c42c0130b900307003058030340c0d40910030f4403000419500c0850b0001e1101c16606030071810503001794880c0440c0c030501d00940742c030400345080080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175808174 1250 175806924 175806949
    0x705030118030f0503150a290a0f110115060c060e010b0a09020d0f18060f06082109040c09030515310807060204051017070e010e030f010218 62
    0x84504803c0c144803001110f40c0d6100504101c6805070810b400343c2540c41d070396030b80c1d406003902d211104025001c644024102080c0c2d8172840c0c06540c020091542e03041c0d4070030282d81d00d54030705042418001c51851245800b402c0804200c060b041c914070030010341c4944c480d010301e00c624003a11041150f01d0038140804d0a80d6038015039581c011a000204001d40d64295009148101c404100040c41c04462202441610148540d0003c0340d02e1240e030300402c0c003000c1d10401c240c002c0c3c0804100551881c15080640b140700c0c4680f801d16803038480da0200c001100c0481101c0b11100020400c000400007a940500b0615503404146c4a910420b40500502c00c11440d802c3d018000c1c484041254082d10b8012811005c8800340411150380408020000140c1c400080d020407442842e01686136800c0130248a00b807480320040008100e00e00301040101040070681980140180c40c0080b015081000107035a201102c6600c40d40501c01c0031525840c1010650251090702c403000c0038644090103040030403000ea6100d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175809424 1250 175808174 175808177
    0x9050f150f161d04020d06140109090209090604090807050703080a08070305070e150c011505030d020601030f0f06090f0c2303030d023103020901120b04060c02030c010c02070503011803 81
    0x803450703e040340c1002d078400240c00c00a201526050000c407800c002d80d826588010000d801c2da2440c2c4c08a50307080b64548000d402b40c101c04504000c5140002181140040c10701c40c0078503611038000c014092004110f4040e00d0300082280d804955034a410142607100540c0c100005c6c0f4a02c020401952190003403d010340295644c4800300700c0c1c15810401c14006206003540c0303110f400c00608000e14020300a44480160580f0461140b52420003454201501850f8450464004d04010700000d40900c142031002d0f82c000c00039407401e02c01460102d001f040035180c040e02c480d1858440c50204228941d5000503038444a9880b0060b001054140440050168107950300d600103100d480c98400f0941d000e40080d88007401051a00902e010524012040f84d14118a0040b2900303018410741c14215915030041001d548000d0b516002920b410040320782c041c100500958a4402d1f400c41e61380b08209950040304503d0081060f031000400c083d582e100700f0721072079001c1d5003401e0070b90a81140c1180032558081e0117 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175810674 1250 175809424 175809437
    0x103060c0306140f040213080303010f05030a1509020d080d0b10020705130e100203090709060e01060507060e010e0d0c0506010806040201050708130f03080304020103140903090409050f150f16 84
    0x2408100b1181d1080c0d45a0782d50003a03400d20010030547c0740c0e404120020a00b9074040e5680b03506107103c0000d6001c0355005680070b94010b08a80340015110030303400c89400034848001842115070302c000f4001012074100902154000b1070403510400d92a0b00c00c00e0b840504551540d82d00d001020207a840300058420258400000881d080141c906504621440768402d000d4800b4801010142005c0360030079a000b525581c0035010030700070304445100d00d1000c2c004000c4121525850300078020701610900c0c1d03000f40416100c0c0c41100d9441c90035007084007200c0030740082d00c0d501381c10240020407500c00750b001500c0d584907207000041d40801c04a4664092038041e03441e189401040e8031243c580703a1010010320440408240001408600c00745401c020398812030503036903a400e081c00014140e8502c00e0000070054240c1d0280b285800c0e0000c12508401819980400d0040e110308100c1e0074a041084040014000e20051290090035000f0062080010360800a9940c03900d00c0390668918007900400e011607034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175811924 1250 175810674 175810709
    0x3070f12020609030106140306010603020c0a0204020c10050a0b041a0303121003080408010f0506010806180c070f080306010f2109210e0a0b07020310110c150103060c0306 75
    0x4500d0050000540050009850420b40e8000309085030080d92240103007050001d803107519850309012840c0100070300e00e419410000c0c0d0700d150035100c005004000b0f01c01d59002502c07000011080c042c0582c0c81c01c82250802507403074a449440081c0807080d01081c42185007000e0820428942101240a058007034010b5051040341c08030581d03000800751414610544040002000980500040c40685000c000206681e6110003507003007030f944043d0640307040c081800e08000b11512881080024060544a098416101c4a6418400c0e101d01000a0002d00120030700741f040c42107010080d0b00400c002e980b8020000080c00c011074070740d070408804100ca055840c5410745110007641181c042030703002c2c1e10038401806414007904401c8606181510100c0d401000c0b940c094503001541c4002400b035501d019180070341940c0040c0d12500c002c0d03140c4400941c2d603502d10080d101071030160340310002c29030200c850004881c0301c0017040620920080f00e405041c03d00390283c0f5486405408211124208008107064 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175813174 1250 175811924 175811939
    0x921031b090320030f1c090e2703070302010605120309060301140102100e060f18280c0308070506070e090403030f0f0204120219061e050706090606060e03070f 70
    0xc0038806003e20b2004901040141d07550610440403039100310b200a08240c2e0100a601c11240a08440380c41400402501000030328141a00e40d64072024085480c4c801000c0c007444820090440703c0d44024900c8040384500070103805500c44829950704441d0707109840c06031044c00356244200e00031590454010301c0108460341084808405401c0140103403003140c0603120181e030856070503010a1704150f2081d010701c0581e00d202d601e000d4104024030510741c0a50841c10302e455590501001c1c00c5020204840b00861030b540480010b1001035000019131007295990a002040e0b0f00102d2090342c1a002c1c11000c80c00340350103441c0d5164001c00261100550340d590341c9040e40100a00300411080d0703030321400840542200303880108040d00359014812500c49060040c448081c00d444002090404e02120505c003941d0802205c0c1100c040d185450001c0c00b820041c115503034001c0d0070008052b241031101690801115070840c8043d1040b5603a0132140c1602401015604c0049100d54888a1401e41c0c0612454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175814424 1250 175813174 175813193
    0x50a03230f12090316050f0111070902030a0902040c0206010e130311190318081b030102090409050d030608010b0d0204050c04080708010204061101180b06040902120d08060612010b0d0921031b0903 86
    0x9c580302015a40080c0c0e503484c0040c140e07401120002d010640e80c4c0441c00031841c1c58801c03541440d4161009242c5507044c0181810280c03c0a41507544210000c04810105441768815232840d5145000380e94030030021903200e49a48204010440c08202044501045d0015880c058011105100000c1030402203d40c203998030b80d4100305659815540030420707922541c896000d919282840b800091405c94000d40005040711b5040d0001d42a50341854500b5650343c2e43c407614880c506804940008880d20b0340840c10406104a61115155011b5400e0001c0c0c402e0041d0301800441d140c90701c50205110305008180e080703a40d11600d500f4000d45680003100450010201c01d91b019030050800100c0c040f294001a8010711090400b10441d071005903070980745a4424642604858150703601820000e01d55194050120140601001d40c080861450b1204280b604400103103604041805000d00c01110920b0400601e040070304042404c2406003d12181001c0e41c0210381211661141c0c442d900310354417030956 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175815674 1250 175814424 175814447
    0x70210030f020712111203190605150408060c09060a080907270f051b0307030b060a0c02092d040c0f1509050a03230f12090316050f01 59
    0x80507914280030201d044203100802001d80155281030a103a1500c0d00100030200d00003402c0038540194803504014051102500d412404800f03456580000b1401038000512103680120745c003840001d043c0341e00070b840600400640364881c0550340c041d5901c0c80c03240c1c0e85101c0c80001a401200400800210b2846106082e41102c1001c050f0380041e60b40300d100300960325122040e02c1c407000c185404409140824896000344141804041c842454006c0400301100a4681d1405411000000140090340300398400c5034045030040c242a03c803201020010310b10507070200100c2c06a040c84003c07500c0321060241d074016412958411130b20117012078162101080c03000d4003c48495400c40710100f52007150a0300071000e000d650710f8401c01c54080900042900e40035030300c5140110802031061010903045c0504c0c420f4060200049600c010f4040803a91801f5042c501030540c0d809070300d15843c00184451700070400c12030214104c0340d1403d004000c008031031002d4461503902c4503600c0c0304d08005501580c881d110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175816924 1250 175815674 175815677
    0x10302030a0b0a06170105121c1202040b09121501060c230102131e0303080402120106060815041406220f02032d04030e03012d05130305070210 63
    0x50851002c40851240031a035000070700070549207050b442801600da800280100000c0720100f1070300e032003914003a441da180000c1c50341750003445035201d440c036a00808002c2c001c0c2c400000119540e6035903440c0300c48941c102c0540c44d03206210942030740d8842c603400a10003110b90014180d445040e40307004420742d902440080308481180c0340303010181c480f600f5542c0c60b080c60402074002580e64060740c8041c080071500740d04180710f0102c0b56200e540e80d100380106203c082d2a414148243c1030348681c000100c00c2c84400690036819030030302d40003050556016581c580601c03c03110348150411001c500300010f03900c0c10b00344450102000c1c0e00042c42c0c0d2400082d40c2042c290f00b81d802581c02d100120f21138040d00c01d80d111000e4005d4000040c03001d02e01141c0c070a4050031240c01d00d400f5020b0410040d503100c0304400780c40901045485c1c584140299429444840070050840141c4441c88160070780851b01004c21100e500d400e454400060b2213000c01100e901a41036155450314500382c40b9500300401584404040c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175818174 1250 175816924 175816931
    0x90108010b131d06010207050603010e0a021b0109110a0504020f070f020d0b01080607081602060a0908090402180f042706060306060611010507030b01050706021605060f15040902010e010302030a 85
    0x4400780380e4036940720a030745040c0f061541c1d4039003500003914100c41e551110707004600c100010000a141c1021668028405d0400548c1c0c4a038090307103c100283d4602d9240445502c2c005660007000300c0380801d252000c20607905841407940d102d0410040b8017400c850710304030107810000305000841620303521045a10050600c80c02c0000c0c0d407030b80c9601203400d0700100810350024040c8031b0b050341c03c01c11203a48241440303508988120440130094072514080c0000c2040c03502c411200c010800c682c07042e0380c1410302c0a8411500c1d0702404e905410f4a80c050717080107018816640b41c0380080d00341030083c3e00c0c030984108d60000140021074a04168844002c10560364240d80b0718000c0b000507980e004070f400400407aa1005500300441c501c3c0340c215180900b85105061502014900c16608032007560449074210400603100c3d030100a00b0b4202205105004143d03024050402c40b10f0084401181c0c003c2c462002c0146010390b5010520048903071042010b0301060448100805c3c0351704c260002d5600220308400030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175819424 1250 175818174 175818179
    0xa0f0203030d0603050d0219122105070203090a170d0807030b1809010f0504020f2701060809070e041e11120321040b060405100f030602130902090108010b13 69
    0x2c101c07000c43e0802c440c107400002010440c5030381002a080160805094020408055030742c00c90560680f05130203040c0004546860107d18a9100d80e80448441a80501c00c0d4900311600940b680d1003144c159105103c500c00100720170042d85020350002c04414020080450034604c140c582c030740020620303000c05850351280350715600e400603580788a80e1612040d902e2803e00c01d50845c29911821858602203103082d00700000341e920721060801c681001c1d100000608004040904044000e03042506000d052400010718943d1000085204a4821054902007a201c21500698150649020b4800e0003003542c48001c04a240c007042ea102740c8226a0700006c4200b840100d481d09095202640007600046410340007882890420500394a810441240380e2400d59030f03600c4144009000b01e401107980f4400200050070610700c03c0e01a1103118440c10349941e580c0790000c007950004051708070b032600006c00054604014001e4400e007d1050b111b008181e800c01200800340c0e000300a400c1e02005249200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 175820674 1250 175819424 175819447
    0x3150f170a080c0d0305220311010e0601031a0705031009020f091002010903081602120307180f1a19120f0f0501080d0908030d0203060f0a06030c020f0102030601020a0f020303 77
    0xc284960721030000c0d0001c10506031001e806c540005112101d401459030400380c15405c0788007900c00d01a070500348034100c040780c0c09665005054000c00c2c00400d114100000c820301035075040c1081440000040c4849039551a1400c6030315001c1a5400d40954103542014861003400e43c001d40100f00e84480d101c0d041000c02000540603e580249d13460140c0d66440c0c0d020300f07166200350300070b40c0550f488841603203007010b0b000d00950711a014003125294081c040049103047d8414500422404411140c240302c2c2170701c401103040440014881d0380040788402142c8c2400c450450180d075008000c0c91801540c8561201090310284c02c0d64a2440074542d0f941031180b4041c42d584105841c0b041b12110020365903050102c0c1d6807402108480540a100f4a9142009041e8002044941c0140c410b01d0158803a15808041a5080c9100d562194008141000801c00c0d03030381584480d80e0140150b00300c0c1e0b0030380160301c0d529080348000e98070f0b903005812050b1250046035403030300f01344003061018003101d2414003d00d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 175821924 1250 175820674 175820677
    0xf1811011205010b0306040c030e120f0c010c0816030621030c1704140402190c050c04050f09060703090c06141c090c06050426030c01090302010b0103150f170a08 71
    0x1c201c0d84c00e020052044508045c4201c090b0500c542c1001c01c0603070b449040403640c41d6100c5c00380e52900d5600180c0101e82c00d101c0f10648428503030107002840f0700d8203804400340c81c4180c100c0c0c0f413280010555804050300c0b0b1180c080c41046811110075400b40c4460340c6144003d40141102c00c1c1c051004201250300010498120904500c03101d58106441e41c1c1801c110f48640181c415403e40700d80d0043c000784018541d42007424605003040c1c144040194400e150590a24610140c084c2d44146000200007130008800c420303500c40c0a90106880c03c130f513a4000c0943c02c4810100340500b011020f040c09020300c5000380b0f006101800030641d4281020440c0b403544104545004480d07240ca0744800d46102042902e030015000b605080c182503040a04284846030484a14140c09a0f00c140d0841ea4841195080c0211903225481c440213001d800041d04003c0d011b800b180422500285c81c01c0d0000354902800c1c10321a050340c1c5041800c502081c41d101c81103280c14030909030380c1c0c0725008480700000000c49a20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 175823174 1250 175821924 175821929
    0x109090219030b01151e0c02030a080d050601120e07050f0301060905090307020901080d0c02060f04030f0c05030c010302160b04050c0330090102191b090e010f181101120501 76
    0x2107038103e5605003440e44400e404084410b10600010b4070952500b540030600007503682090307217411103a1b442140002480c088a0003009031202c01c1c0002c204090300c08540110707101c1c000a8070344450a5000c0300c991011140403001203c1c00e600300010900052902c3e009850a000c0010b0000c124151140d482608540040e203040c0142d0b40002007500450400c0d5078014010262400a014040b00d5400090085915484028881e820000f10101d80c0688441030790040d41d08241199801501403800e00b111010a004452082c8078560f441550b961290084421101c3d04a01c01d002d0810f50340d03076801d11580040e10031a118020100c480206480400c90b00110b256504c0408880082d0800c000300e8441d109000c030030f0340202c100030005d0266000074200c41c002c5029149851001668200303000c01100030802841034081c04900015401c1003904042038884445000300300d030000e02c00c3c440d0304840b0842d1030782e00481d4903800680c02160054a04181005040c1482c0398404600803019084407002d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 175824424 1250 175823174 175823183
    0x213060e091509040308060102070b0301150e0306070e01030207050307061e0605010c0314031b03070207080c09130b0a0e030a0c05011404020618030102041203022401030b010909021903 81
    0x1800154a07140ca0040150412910ba0581200205050205001500092010f0b0900c2860008118140d20800650000340002c0021580300e51310361016629004103841400009a52011001014a000701d0101d000b0310807911003040c4440480c005502a412042042c0c07076901042c070408000c100c26016440f05a03014003003185a8040f4a81040100c030f50030781100d0f040284108643c0e0000b07070002c0c004441440d41d46002c58480d510980d8251420700d00b49480c80b1a12804014440c24030380001b00e100c00d41d0503c405460039045000f0a00c042194215200038031485482c0030003011600d820195600a184090080b4410200118162451380301c64102c00005003001080c41c18000d003840352155100713211441381c0e004e013000d0700011070318010b420300070030050308003202280c403503a09504a034010001d56410101101031418060340342d10241a90b40c41076215041d8081d501c60480200c24140c07944144014000e90801d04e0f0f0740000c056060049070450044800d8142c602d8000d00e0700b500a6224 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 175825674 1250 175824424 175824437
    0x2010504020901090e030f16020a03050708010608011509020a0207080a0f14060402180703090b1303080f01060203160606090216030e0d050307060c0e1201020a09050d02060a0c06021306 81
    0x2901c1404040c01050340009820752402c4c1e00300d4510704000c42210112084e00420f50b49030844c2c9444418469110076000f54018810038000040100c045505d078103d68984008000a40da960140307400e8038841120140d00302c0201905000e80041d680c0a050280e0483c81124602c0381c0303603c1341c503280c40951131007524400c43d01d52200007001004002c081081c2d501c440a0030040c2819400302d04a420316081900940800c440040d000d01e103c0d82c0410107854100c42d0440580c104001403164408001d8402d0f03000510100000e4030120704e600c8054100e80103680190b01c0c0400c584c58070301310b429090b242201e40c4d648440d400901110240041c20600499107192140002f080c50003512010041c3c0c07515000e2a0444109404540040180c1d010a50042000315484024000850301040040322072030340f0480762000d083c3e203210154040c110800490300c0e29008140c031442000902d244008001354460010011400380c0c6200725181280a4031881016051143d65010b0003900000398102c003000850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 175826924 1250 175825674 175825681
    0x2071e05040f0603080703030914010c080402040b010908060a020705010605040c020f010608010c0c0204050901020d021204031d090103081806160515060a031709030d030b120d09062a03020105 84
    0x10700c1d124850701c4104206041041a281d0340d6000c0c3c0c80e01414801030181a941c1d4840e00500c44400b03074240810203480c008000d4000030400241250000b0343d0164020b41c500703502a9859405041110b081d0788002d8010209a50784030403a40103540161021079455481750800103c0341c841e80a4422505031070b40140000385414001b0030308541c030300d910240b42c03a81003d0701040410703080070000c840c054050700c012845070b4800d211140039210303401e84c40790a03e100056910302d109490300c00f140242c4c8a0707507944806502c11000c032503600402c0e200c2c0070740c000f80803401000012201d000420804604014518115900c0e000180031904140921101c41c90807010b00e804102007409080c26285000703180b40e42500b48000031422441d00341c0801071182e01c00808050301100b001c42070b18800300d4003c0840d11400150700c0020701516010744880c1c0110200b150801803800c01141000da4980107550300348545260400489264400b8115162041c1c5459082200504842545403c11380a900086550b09 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 175828174 1250 175826924 175826929
    0x204030b0c1902011406101407080c1507020325020a06090f05030a0807030e01050708071a0601020604020f0103051009020408010501060f0207120b0703020d020a031a03010213051002071e05 83
    0x804007180b07421645010101441070000182164000c08142c0f46041c0407903455a0507100d026506030a81103040000c21523004110840000b8120500c280703054400950108180451781003050796030402580003440100b042031081035505145c042031004491403000c0503004140c5e04003480d00f01c50000340e10940b040c0034940400d4198070090a055005080440d00390700c40003003500400354020b080008403c20041982e105000b074950058004028564680551405007030480310800c00f550040300181c0051301941c000300704a4030480c0c001e0080750200c41d03410011402800b000701071a540351284003010031101c2080c0b0280001d440b0720b4000240a5040c418042c0c100e078100f240c0d042c21580908400e010b411202d41e5660502c0394001c104058513240c40c3c605501900030000001001403000c00d9401506525802c20041c2290311440311342418840d0701414283d200d142201c0360414030004003000b107810201c50902030b110092040d20000d07901d4541000103200490650445011410b01c04e018a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 175829424 1250 175828174 175828207
    0xb06040b280914060a0918020a03050708011202090604110a05040f050d030f18030204022115030d110c042f0703080703150e0702150c070803060d03030204030b0c 71
    0x15076410014680c51501c01900b00b034185680810740603240c080751201210303000b40b1241d00a4006074102000011951003208025046210b00e500080e007410b02050b5950301800d43c050584031144640016203042e6000d00482d040041c0c0703290307085a90780c0b202e102c1d640c09950281c80440180e680e030695440c80c1503109000108581c218611aa2800d0000e0002903006010020001e40c02c2c1010307020300d280c01035080402103150344069000740c000541e800d030980f0f43c540300d80c11080014003601005d8981c40002c11359a40340000720b0b0303015842880200601401100100b1603007003035000f00d03206541d602020406036980ca4045140001322900034a50340302d070720f00001c0400c0e080c0e0111141021010380340200721071000b814050506698031082012101c040d1802e0002d00b041c152510f1305401d0046000355100c800b0a2002c03494084200455480e02c07089040344c8261b07402c0b540c11810340d11504104400081069070450905600300310010001c1e01c58070700ca0b03101e0040c00b08070b03540b00c1c5483c0c01c0a5660 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 175830674 1250 175829424 175829497
    0x60117010f141602010b0307150216080c0d0807020d0804080d0503070f030e0a06061509050d050303061519090e06040e0d0e0a09050901091208190b06040b 68
    0x1c460528090090507010100142d81c4580e040c3d02011400702c5210041c1d004080c48600c82da01401001320101d81c010b01c55040701d21a05e6030364211a0920060207000035428014042c91300680c21000740d902ea00c1c07620002c1c1050300340c003d0b46d82d0740c0341102d90b070b000a201408050301180c51040201e0104440e00342800740c0310741d006681c10100e1440c50000b000405004c05616201c09060341c2d030300e805a68020810100b03031010f9014808218042c4c0b110180322040c62050001000107060050210b560b041c880810040541c2c0007000b1800c5441e00400c101c1101c0100303081c042044002d001c80d1849468120411a5495554450505650800014007070b5814000c010f1801141442003e141c2c04000041207101d501140c40c000f00d00000c1c2000051121000f540901d4546040005001000c0010f40c0440406449600304900c440c2032042c0c1540c24200403901d61040c980280c0c0d0702c4181c3c100940000740b1143c3c00611103484d15480ba481c009031034122200c4060840500710759030320500701c14090f02e0007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 175831924 1250 175830674 175830701
    0x41e03030e1503040b072109060e0309130b0409050d0e041a030303070807021f15081612030e04022205040605030706260403050304030306140f2106011701 68
    0x415003101101e28054800071304024007203581540041d203a24443c0a40c42c508454582e100c1c1441404c0d00300031000b50070020b20580b016480e10740c28401c041000030442d8007100003d0020105010340c002404001d00c00741180d02d4004d911481d583c800110b041c0041d50718000b86441d4000041f149030180011035039a40d0400e2071100ca81000800c541d40d0000030b4a074000c1651401c43c01942d04d00700c08a040483c5c042d11140100c0c1007042c180c42601440c0c1040781c002e040f403e500c20900e540c0b02c01e0316a403000b80e064003241190443c4018401980c001400b0800c882c0241019004651003001003012a881501c4048011303a0009101000b0a81031060f02c005002c22901030010f00e00700000680c60b600c0b42d02c20341e0240301e80c0c0c0005040c000c41c00000c0702c0505080a440303165074901420007500701d50003102d04500082ca0900c0c041402c0203103400e003510585014100d004080d0480052180070813000c495410400c0d9548080c802c801c80810425010340080c000800c1d160104840316400d4a140c54030400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 175833174 1250 175831924 175831939
    0x80a1502070f0f05010605060d060503060a0c0e0d050703240518030301140d05030a0e15040303020705010c080c0607021c020703020d0201030914121207020f0d0f0302041e03030e 78
    0x41c040382481c1d607480b42c000e40040c540b1610800918000d0300401c02940043d0700440c01041074041c04040780c5c00903040f100d0603410b46007a55074041002086030441d20800000c5810416001d40900b04184a850954869400c444001d5180d0320780040cc1400c5200701e42d45100003c07008865940d142c0200c54004581c0440300c80411984281c182c0c4030302050240c006501e00b0098400f80a036511800c0701441500581078a540340e080710001000e07a42c00340d09040c0909498025002c101b11100225811280c143c0d003e050302c141024011a0ba20a02400c11348034103a051219a031090b0091200b5030180c0d00c2c0d074004203078240f0b040344c00010180000c03d0400079034101d01c1082004d030301c2e2616a8102d203a42460001654911890803400c0c8100e40080c9410900c01d84061a0f400c0214500030412a018102c5010b45c9544a0004aa448400e106e00041c1c80d0803684a222040740900128007410b90941405030800c0d46500700e81e159014000e42060081d161040200149604a015070408440c161140f6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 175834424 1250 175833174 175833187
    0x105040b06071a0a180605010305061012031d13090224030a020a18030303060306110307021b0a051509100f050f0d020f030f040507080f0c010305041407080a1502 71
    0x52010b005055103406442d8044000112510100c0c5d01c414183c1c0c4182c002c003044c100791411b040f00102800d00045032944244c0000c01c3d00704024003085c02c21582c04445c00122124680d4040303030595034080e030100e02c070b01c104a1103041e20381d52184201d501c200300402c002541d00b21801009a902001a5030349244201c0100744140c0e010b2000840b075001441110150f50351b48841002c8840b240c5101c420107588120003400310406d64990401c2c1c0031280600f20034098030039141041e100500c01580c2c41800740e4003c070b881503900c0c05946c00340e1085d030b20010708001c8001c0c0e44801050b855280c00c41c100c450880f002517002518540300d94583d10340d100b18a0100030506a42030050258403642a0301218210007080443d414502c41d012541e00c010104103590312410041004002080c00340c0d0110360034064160301051410f00050b07481d1220310540c000748060342d003020041d00203280c00340003590704001000e000c1940c8901008240700030075600c40280100000740c01d089401c0c0d0071176041071260740e0040006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 175835674 1250 175834424 175834433
    0xb04020f04140d0c0602060a0506182202060309010603030825080a02041806080d0807050d0207021512040c0909030c1502120106051305030303041709011b08030105040b0607 76
    0x603a01640d55001c00b0720500c92401000038051407007440c006151440101c1e000ca03459601291050052032410014085600c44108102d0841c07821503403180c100d6095000500c896401c00ca079840c607107203040d43c030f000184001d4001c12111f40c001c4801d0002030b0346580b0308008040d400700040f580310611180100600700c0c00c03804094074010f030342c41072401c001da8640820400c200660490b4024800340741e0a00c003c419507482d16002e414988629034041c0580039805001c5c6014134200340c8184601d90301ca502e46288100d5840c002d4110030700c1660040c1940c840b0141c40850f1400412890b060340040c04401d00e002e280010103030250390094000f46062401080010780c2148001c24150360201048982c030180401c1c5c00000e00526144c03450341c00640d000001d02c90303003090040400d00110302c01410069294001c1c5592407000f0785009144203030402c80c1003da201c1c2d02c0080e0003088014513282100680041000d010070200c103201b61811040003004110515052241ea460300b81c066425a0901005485 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 175836924 1250 175835674 175835677
    0xb03101109060304050f1006140612011a0c030f1e0f040e040f02090f07090b0c10180506010b04090f05060f1201061205070305120c030703111905100b04020f 69
    0x420301800020002c80c4c10401c0071b110420160607100c084610000100e0100c0c0c0240c03040e4454542035112a2103a81203e04008007103d810308600c86845480d84d1802a0f03441104000d11010340380c040046c0580a0032080c24401454003510074003203a519102c43c1600c080f0943c1c0c4002980300c101100704984290060400299800c95402c40d12070b8401da0744a051501c0181c80d00b01000358010030b600100030307c0040c840403c50080c0d44075912122030315240d11610b000c920610040107002c0d8000c9011040703c00c0150800d010520040800c110080442d0383d4003450a20f003038000340a030000c0414180041c441c14071070205d030010902c074207000c2c5003080008207800f58030000b03199004030300055420800131006d42100e0004c10544104c1845901c05040c01603c07200d4500003210b03140112080c800c1d1904481050342c00c450114800340d0300e00619641d0565990110325043c1040d8050658684041c0c51500c00d10f400d00da004070007800708500302c804880e089403d0902228490351040c401006043d05190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 175838174 1250 175836924 175836937
    0x5010c0b06012312100501090308070204020c01020c030714010c0f0302070611041404061502070e09150a020a020c190b070c0e0403030e0607020a020105070308060103090f060b031011 80
    0x200e1800d00303619803100481c0c2a0303c03d80c2c24000299900f4600f141c4990b440001040e0000c1e40071442c1e140c5441c1c01e031000424050b144100740c0068807082003400811901d100820450344020001482c0c81841001c882c00d981240304c13010219007003c10540140a43c46507a5040502d03500020020503081520250a9040008c08142019801f046078010000700b44d010b4100318484082c0152196554600b0030311601d0600c1c6070fa401203082c040009425401c80c40a09100300d15a00903003119070034541210805000240340200500c101415800c10000c400030290140602c0b08015960340d03190306010389082e44103800c40b40030740345541302c06e0060242801648280d4081610490781c2c1c04440c200b440d170f540030b107410021040900406110815030035a2100800c030000c503081d1b4510360707103103101a40c540f2101e400290100e0410419900000e1060040552080c41410b0001d6a10016100d041401400364811910155103c82c0c05840e80b608105074080c040d4256403c1c014580540c100b01705500452 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 175839424 1250 175838174 175838183
    0x90303050324040908040f2102060a021c120c0503060a090b0d050102030c0903060601110d030b0a080a03020a0c0504020f0d0902030a080d0501060806010806030615060f0a030e06010b0405010c 84
    0x10404a054154402c03000b054411004205004044460922403820b600034410002c0700e451130310300050040e02624812aa0f00300e8594144405500e607000d0040303550101048104601640c050b445c1b0004804e251100205416550131840203880c092500840d880c2a1f410414000705204006d10340c2c2c4c83d0700e2128150343c2c16040c04603880c3c15034404100c4000d00500005d10302e5002004000c01e00f81d501010b00040d1808030101c80464594100566040796036000d2824984c1003103046841d014065000010f04003c040d10b41440030395588207060602c21250422401a0030200c0c00c00280302c251100c9001a1004650440c64145ca4540310006403089071054844551900d41c07038400d556042c850411130030741050150396243d00c209031610091609005842c040b0f04001d0214a19511852a580c45014050001d11f07098a401c0400b1088541500b01c1c207a100c03c080006620381c02c0c88034054180042c080e2400b0070640c410400d604e00300382d4142c0107044907910900040105a0713000300c9200003250003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 175840674 1250 175839424 175839451
    0x3090915121103010e070b1305010801050603011703040b0403050303090607030608031c06050a240206060904080313080c0114010806101509120b010510090b0d0c020c0405100e070903030503 83
    0xb10404240075001043c003121841c0119100001c900d40d881e00240114400c41440d038003113984031001526050028052076030020710500051107003003031030660420004c0314182202d00b059901c503170a801c542d0041d08210f40d65000842400580350003000030035000f1010342000d003c0c0c2810400c005542c0c0c0900585030244a40b010b0104940506651103807015040161540030101e4880400c06010300030801d45910f101c00040d17440404910118000c0c1c080d041c0104655240c0c1c5958503030602c540c101904544a02c2c401002c41400601e0450080c940180000b002140c1c4041c2410a8103014805a0000034250048010008010401201401510b10b050685e07020b844901e04102d54201090b08000c41d411144d22181e403d20001d802d00c83c1c101d4900300d5160858052840080382c00d0002441035081e140700038064241000321640260344d00f51801d104560032581040001001da560995124010030745040d018000103040e50b442c0c56120301c1c0e0b410720000a0b440c583e40149648001481654401003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 175841924 1250 175840674 175840703
    0x60105090105120705030103030f1b0602090f03070609170a05060c2101030609060b0303090f060c03070c09090b01060518010c0c09050403021507020c0303040306090f0209040309091512 81
    0x5501911948101c4600c1645941340212000c2d1042d4400e0100386c000c00e0002c40b200c9440c41c4140304154080000b070b040380740526803966440303020307402c2903805c9a401403150b0090340f426102040460b0040440b5507a115070320b49412075040c205010700510118a400c22007444e00803075400280d094016140c10f80300c030381e104407411620720385840b42c0710306003031a0090000000620040342c011360780a40c0250020404030024108247c0d591007440d00c3ca40d0008403011025003503140000c0a08000807002c03041d01e251800c141c3d610508043e640c0c10a800556441145600b1701050004c414090700c00740c00d01c0c9150005042d8520f148a005011a60400102617004810002c81c21059801020b10785001d01c49811310f4a0080d4a0749e07003000504020b015108001110188005000c15400c0c0c000317401356150034215104d560190110a2040d1000907486a80304016159030384158840c60280c2e807001580b80c108820102070301c1c403042c41c00c0780c5072248900510070324140d1a00c2081a81c1d02c15030350141d086 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 175843174 1250 175841924 175841927
    0x2120c01090206030403020a0302070906080604020112060b21010902030601140c0a1a040302060c04060c110d0f12080606030f160215010f03020102070f06140304050312040c06120e060601050901 85
    0x807207075000a41280d0040144000c15030000b4081d40c0700d0b07201e90242e4446944601c11942103500310720900c1526849800420055401201d2058501036208008640583c0701d18048000758014005a111500c0b07105d00d00703c07008150701016000d4801050290b1071030404000007401012024002c03440f51100040c60b00b4440c400300132a0810550122107284090302703203000c8003941c240031032381a4050302800d0001103010100400329400c0e1803042d00c844100310400e4649951010041244540051004810b2404110000a0035421a1064058500605c3d44000042c61410090102409090103105210716031a41941e05940100850f0f20388101c00441d4a040386030480e4150100c05848480d000402c0519584c1e6522043e00c1c000c0c0c08441100f55100e01200c22910b841c07003804001a580700d407420946020300c00550304503015400b2241002c202c000009048082640e0441e400080c58400b004415085500c400303107100491001c02c040d203031901411b9110300000b002d0390304004000800d1300c0c00e82e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 175844424 1250 175843174 175843181
    0xc0301080d1d0a03080705100b130221090f071203020a0f0317240603250504170610060e0109030209060a09050f06040b030a030e0f12010e01060f080d02120c01 70
    0x20360001c000c002440d40d207080440c5c2c181d1001e401a00c5a0243c0d00a0700c0c492030f044d002c1e1020042e000b0b414910003110b4168204001c2d04990400c29030702c20028a031403920b40c190f13000340d40101500070181100c2c0455100c0309181104960061204048041c01c40d000f00780c02041164040350480c08140816029107000c03038552284244444000f030010050080c101402115250b443e0041c00400b105a0103581c1042158001184e60a42080448008401500302e0740c0c95105260590b0802c41c0c00c01d9211026040e0010710141c000089a00078400c00104554410310140144483d0403c001020a4640000c080b121280000317401804083e000c1415501c804c40031a00070004a0020041400c0070204401515804c0c0c402600c198148154800389190124200314420760580766484406a040c0c140000140c5400c00294400c01000d000c282a0760f0070700800c00801c210034000104903081c240383d40155101500000e17015845082c0d2b56886680025a004440f03203810402c0303071a04403c4030310300e015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 175845674 1250 175844424 175844477
    0x160f171603020c0a1a0112020f0402090f03060a050702160303230c01090305090a060503061008041502040920180103050a06080d1214070905040506030a1e06050c0301080d 75
    0xba104041103041032041000d00010075040105c4200b8850740e80f10010019403810381c401a6011140e058001018613042d8003c0903110009402c811001541000003810090101c1d0030000c1e2a80314010070180541c1030040000d801402d04c110380025046440003891924100c24042c0b180d41401503030034420510a09852a41d14110700130f0089444502c4c009106421486c10035015400c00540807602d503010300c0c1a039100700360241a40b400c840c0b100404444000300a030054980c01d4500500c0748680c48075000610190040700303400b20b2450000803200f895400e0044122081601c1880180d81040142d1001c02042200b468041950f8640c0c03001c0e80b00404255200044500c02c0700c800f546c0301604407441840c00c00d55180c08015031941200d1510942e00100c80329000200301007014030492400e5481a500007001608851210200b5500c020452040707143d043c0d00045c84102d24000c01005014446e4405a0217026606551508444541d6413900f07080c414184021500a00c01b141072a8140495 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 175846924 1250 175845674 175845697
    0x80c0a030b15070309090b03121608070f110108090c12100212180a0201082202030d050c0c040e1903050d020f030601030b0306060904031d0306160f17160302 69
    0x8542c1442280070b101a800305604501145c0740c0c2d5800203030826544203a0038404005000340c189001144074000c041d0388000404804d0301d455030190720101d07080402400720240304220300c0900d08444e081819441d030400789001e0410001c102040301201e0007251000c0c1e24142625640c0041c80711401d160300300720042517150507403840402d820b4a8001854885405460041c04a80c50700100c000210344a18546a000c3c1c00308031414081030610441000604600518042d001d658050550009050036032101e42031000400c0403650000c00d507018403d00507846400c4a0070480720b020b103d402038440650140d40c00300202c024000c0d07403d1600680c220303121400b04100c00c55580c2c1720200c12014176001540c900e80007901e400013440c250708000800b03e0181c90003c010048580c9c456a0490f08070000854000e0b1002c8101d2485191351070030003105000c3c044604d030700341f40003048040042030308070b81c2200d00c81005126011000100551a000c0d50008824155401c0c40001d028059002e8801e204a808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 175848174 1250 175846924 175846939
    0xe0613050c181002060f061507030e04152402010e25062c0406080a0302101103010e0103030c02030c090f070809070b0a1b06022d0307080c0a030b 64
    0xa001c01030000604040c094445080d052414102c00c0c07280ca01000d907112000350f488103000c60001e00c802c40c0c00b540e200400404a1922081c52584010303140c200f544120049150001c0184492805d0b0140d0f102100e50040400d4010b440d2008500e000c00500141408018144a200c14401d100303402040100c481e0f401258000b0b040011110a0a00b55440181c065942484040741691044031010303901b006031702100005800c21109040d02d1007980030740c103900903a01d04000030581000c2c851010924000d03000340c01c0b0306086015040c1610001025040c141d9010001404444c2e500240181500d42602c1c100c01080064800310b407402c500911103903804605401000100381d00085d20724803645c2d013641c840b112078a0f0603049030340c3c41015000c3ca52009a0038400d43c0380d55803082029165409171031510b481c100860f40c440c03200b2070340032034011030800c01d00040c0c940301c50349003030002c080e040341c00c0100602c2d500d0003440042a6070405444529011000140007071118445d4100114400c001000c42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 175849424 1250 175848174 175848181
    0x90a060213121a07020d1d03070f09141b0316050c03030a0504030f09060e2404080a0c06050c0a0303090203010b030706020102030a0b0d020d0b040302030f04120213150e061305 77
    0x140080f024100c0e0ba41590030050002d10f0300d500c041910129100c140c1c0700d081c00d00000081c800c0080299041c020b03014401e000001a110203404030240081003464800509201220b48842c2e42442c02041c4d00c040105803603e0341916214030040300d03408003510314400c54106418004550910030400310f940c46110110030b10420850b036a00c1075000e14480e4039405500060150259080709051040c02c0108105104c00305441c05e21910b0307030100c2c0f0071110907148080058552150b00340c0254102c03100c0b55000d00303101410480d4040031745d0040c0510b41010703414115000d59007a500d540e0b2040060425880e19400001c5450075000444080c5000341a41d001d2901da000c000c3c002d400460f0024240390908100c070343c103030070290450050103401808400c401c04594851600d0071401400840071484100400d201105400d000781c0050649185c003004601924010030403428800342244200514280c2c0d030903100200d0440b031030122400310700c810401e0b0341c0b1500007400d0841132050b5540b03001d00344402c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 175850674 1250 175849424 175849433
    0x140a030c060e01030b12070b03060103090204020c010e0d02031e16061a0a120b040609020a0302030a0506040215040503061b0904021c050108010203060319020a03020607030305040507080105090a06021312 89
    0x2100d42010280d034100031004a90b020090145610403d241c199003013140140000c0700c610000f10760ac0b0f041030501140315202580400c040b64842d0b220701c01a07035035515030811844414040000d03220030398030041d8241072441c41c0c002040c61020309040d1240d00c3c006220350b10700740860840200309030024010000394004071650300c505801201142d203d40c0d840b023800304900c130202040640d03050304a69100c16a54455840500801a0b00f01c1a40c0c840404c10b00040140d9080021a00040c41140645a61b04191051002c2042690801119401c0501c02400140c400046140d4069041503052220103102015a040380c0f0420121940040c00000c4940c0031031038844c6041070b0b60900d818108a00c3ea625102c4074201d010664001d03a05800c1800040b000c2040d401c00035240c58001041c00c182e10795030b5800070ba1030350300200c1c0440110780c4510410080c40000d003c14401005640c00074801440c00203040391300e400c40058024103e55020075880b081c401c2410128000d04090b441401503081c0da41003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 175851924 1250 175850674 175850687
    0x1a04031209050303310f021309081e07031706300c0303070b04140709090b0403021605101107050d060204050a0f0b030c03091504030e1005030f01140a030c06 69
    0x18411040c0c0c8507480c80400c280103e9800c000c201000700c060514080050b503541b0500151140140d80c040103a8103102c404014910804107100c0c030480d4840d0790b60b050005c00c0e14000d0060100000907980c240a421f0110fa0862018000c440d94100303189000c0d501c0d0400620ba0403521080521000311028641450300711101d111344400c0c407030b907041707e1500a800b0201982c0c0d2250b024018a80c0b0000d002180010718008203503c40ca070102410799040c162110040c40c200c8007000c1080d2800d4019a090000340341e01403214010421190907480c000c070741031002280c1d6058a00394031208001042410070700001061000e0304c0a0080140400d001100e14200038010f500503003e4241b040e44a0030000820201103424081190301070003d00e800d543e140043c0c00c0940d04000c0900d0154021f004041c2501041c425070a4400c0703201c0c0c3c0350801c500481d00c06116130310b4000c21482d41840700c00c000b404800428841c072241110440151144010074183c04900c000c0d03104d9100401001103540302003804c070741020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 175853174 1250 175851924 175851931
    0x60d0e03070f0308100b0f0d110c031305011103030601270f030c0305010c081501200d20010e10150513050403030b010903021c0201020c060f090306090a1a04031209050303 75
    0xc0e1a01342c191949030207011b92040080c0140d07100410419101c202d031280d0426024040c100c8002414003401100c82030565108045240e0040d070744120034002c642c0c22401e0301c0044410000158114580080060503414844840519120f1980e00c640b8140500518038805003100c1440811519500d00c0d1184c1021864041120a035080008800045104610051162150b40041c02240c1c40751801503420341288004201d0000402420200c07181042043d140308082d10f507030324401c003918040c40144248106001c8801030741000c4e48408101400541110580800303000010801d0503881c0301070801105a110035001218030106a0980805611551060b4048c1e1020300181884078011a49000107000023513004001211401e4082c5020b041c448041e44180112011031100c0c00c0000c42c01d411484000d80316403400a400310342801d041c032601e50088808001848141c2c010341d00c01c40c40341c012807140702c0d00041d141c1c0002c080c0341c4240001c05007000303075490400120350305041c01516544106d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 175854424 1250 175853174 175853191
    0x109030302091c0209010e04020102011407050309070501020111070602160b0c0c150103031b05160f03020301180305092413061805060a1103040b0d0501030c06030605060d0e03070f0308 81
    0x80880a4410300c3d000741094500d900408040141e82098203086035090050016411590b984c020f034802040104444c0e4064070350760721995100e1401d243d8071441d20076242c00041c11a410440071240c440398080c240c540c05503004070701503124451048400300441282c440a08420322206c20f010030780ba07046004007151030224090b1483d81101e500101e005035420b100060010b03155000f40f40c070140424001d003450310300c114150340004006400f1246000d02ca6001424042080c00742001149400d00c078032903203801044405400200151000b030702c14043ca6903110b002d0031240b100140031100030480341d24110340240e005c5413035088241401200403002d00860300802e40c0d146481d118500e44a1200c011602c0c0184214682050224200c4520748031f510b004005100a00c804500b00c6210009885800f108540000301c035031450805a4064000d68044010301d4a00082480740d501c1e80c404544422b0000321000ca40c07010050354452a51285041c040c21541071003000c4000c26500c03030142400358501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 175855674 1250 175854424 175854439
    0xf12090c1e31150e0105060915070609150f110708071b06030501171903120902090a0c031d07050906010912201005040521030307090e0115120902060903010903030209 73
    0x41e240a5444c080081c051168800010700c00c1d1085854400c044400400d600b00b8440d003844034655601303041d41c0c04281e003128103081da0400c00145940318400d14100394102d0100740803c02005511a804d44241907005c0c2c1140ca0002c0c070a410f000d06803121101c4003641100702c000c0c860f0360fa10014001d003400e000c0c1c52183c000031075a91030440300c0005c20200000d501c1008110030b848654040e64a10041c084001505850b0200000566102d50086100302e181400c041050030350300c40f00a00700c40542401003a500e41101c4c4a000a07500000c8100695100391080c0415803204001a5081529030b4003840c200036402c2d030718008000034107942160350040c907520701d483c8454403020003690303006a03003050b0300041060108019130716104078024500e181e140640d07454401014069400d5500c100e80210218032800710420059a150186a004281490322981400445071000708103042d06a0000700d219102d07010b940035591100c04071801c1c400b00600800c000000307460003a0107908202540303841201b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 175856924 1250 175855674 175855679
    0xb0301061d0a180e1011070506010504060b0706110f0708070201120b060f07080c06090f0d020c0a030303050604150906050102100504020d0311030f12090c1e3115 71
    0x1001d4250b9000d5a030801a442c0311001101d4112000b0821409540700c3c2d8440c24403d0705522002e885009a010ba0542440350740f400c6a061961500302c06901142c0201d18140c0200421400c01094a2046a2000000c2a020600c000100e2940141c514001000790300080c0041003001c00401448410b100380c070354412040e59000c01c0c0b411a0300802801d0307000b07401000741c00003810707581d401001c2d503910a001260406c00901107840c50084102d40c480e210703901901004a120000708500c0344095400d2000b0044050000040b81c0c9280b0341e4800101455144d001181c00d603511500b01c421404610080b02034202d644000510150902e40f04060240c01044d40301a0380c80b0090144501c215005050724202034607540d02100d525111030304544e16404144041000380e1003200042803074040020800c80c032400e040442500b0304169201e094070640e00e015a0f410302e090b40d845100c1400300c00321044000d4420419221442c450441e10800c0c0c140e1070541040c20543e40b40e4000024842002c0800d62201e8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 175858174 1250 175856924 175856929
    0x504030605100b031302011103133002060c010e10050a060b07081602060d0501030804030201110604030905010305070c061d01050612030306090618240f0108011703040b0301061d 78
    0x102e00d40550001040200001030044800440801c04103106262151825030003030540c0d0305680040c103000700d4881003003900b004903101c06540300e00ca040b602201a0581900d0803612a40001c0542d00240207400201c0e8801070500290b10030116594070340180e852000e00041008000c220031a048190a49091800f1401c01002c0c0c0c155403105034011840c900d0030b907010b50440a800c001c55401c980c450400c00c05041c40c11400d0044d14001d40c807a2100030740350b50551001500c0c80482c1300e01a203d47c0c2c8010100800710b0b9000806038120f400a08002030700d915251001c4900103200500600154142084007040c02000342429a0b4070000b14020041616400d007040304004042501001c640d1040c008907951b031410820a5402c0400180654900c00d10003055032841c1c001110305243d40082c04003501c0b10403080304101c80c3c1100080381c0e1400c4000c0c1c030200182910b2010300454860040b00c88180a8440c410800c40b409040c400d00116269a51280011b02c50011507004035080500ad048c80d00160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 175859424 1250 175858174 175858201
    0x5030a03020f0f0a05070b0f0c0304031a1b090d0201021002070b0a0b0105121f09110c010f0209031504061103100f0902210709031209051f0e010522060504030605 71
    0x8a905c080a03080e03082c6000184c1d0003540051038046c1084d80c04004009003110200000d0004500c80d00380c5c0c41401c081e52600c40c1000c5001404054015104051140140c06040484e4009002141c03100715070b940a0004170300d0941403803410030020f880004d1076000d0140036841c0c1440380440c0002800380c030b1840001101d550041e10008030746480e83c070300450655089a084020565000002d089510b941c0b4800310042d106500301140d00d082c000200040700140a0003404142c40d130920f015458582803070042907488003804450304001c507448000c20208a0b0301c1e08202c000e81559860251a0f040001005d407800f0400e104d40702c244c3d07140e500e0000b0444000c4c002c1c3e4480400c0e081c01c42a034100b45000441503428028002c0080000d6140044000784055410b035005000036984d4112580c00d10301808140f280340b081e40c094400c820f44100003e154000030380c4038501028139009890b02101500c801c506002d0802182544400d207402040780c0740d002c00580201c90003058144101d4030b810f0744a0516 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 175860674 1250 175859424 175859443
    0x30a0b090a0b0d350a170601021c020a150e07080c10200d09060e01030b0d080a0512090606040c0c0f080c28060605060a02030a120605030a03020f0f 65
    0x11200060007480800e01d4012094901c003810400c00f07040c21080d072905800c80b40014070200c0d0135500400ca40c44040d40c840300008000c4a24908079600f81001b10000c0e550f17007030600c5901c501c1d01d00b8644034142c0c14801c0c0641c07090709a000030407051142c219406280a0080e001c00100d55200f86540052a070360001141a070408014022102c2070003c000c00700c40c9a1603281c1290402815581c0520050b80c0410011903108169500c4105060900d00300030808040700071158101810401c244000b90f0351a1241d0504950003811641d0710036810030242d41c01e0003124181c203808101c40b42007003c40100450514030802c400c66040182010105050720400c0540308041c00710a001c03110340c0300187c14034000344403054421007142e841b210f02c0390f9a40034200000c41030001203500c014402c0100305460080101400301210510305200d001c4000964a0045c00c41140030800c150000240c08144c83d4130043c003500d070240030f44582081d54103010303540c0e5844000c0c4e404a8461000320b0001e00f500410301191 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 175861924 1250 175860674 175860679
    0x207151e0c1709010e06061009050f0103110c0c0a06050c1002031f030302160909050303040201081b04031a0105010302040812160b0103050a02010e04020f040e180604050a030f020102120a021e030a0b090a0b 90
    0x4032701c0c0c00d000a103c24075000700d8440341890b40e52500c0383c0500f070100c0d0207011070303000031030041c6042c140c20000c3c044120f03440e61002d010f210090119002000b008540d80d41c1c82e0b03911140c010380f80c0d07440710884c4d034400d2004103004c040e0544420000c4185a40400c12669840b640d50646c1d20040d078607207801c0d044403400f41014020381c205201043c01988500100d98102e404444810700003000c16a64052950095204441205201d6900c46100c1060300a050051000742400c41c105841c090542e601d400140c07601c0105100700207204400c681c4a2141d4083c0c80790800404110b0790384915050f5520f80c0f1060303082e8003180c002c250f140540e181c140200d600c40e6203140601401c140c90030a410703120041c080c10030981f090f43d00000c0404036200300f105c02d01c00e0b40503900034180e01d40c580c01c01a200030b0740c506c200021a4010800304001c2c11801c3c2e02e0b160850750b402d00041c0d9940c50300420350206900311800340021040042402983d58031900068100d4804440f401d019444030300c5103108644c0c01c00c48558 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 175863174 1250 175861924 175861937
    0x30804030605070210050108011a09090a0f2a050301051f05060d020705011802011412040b07020313060503070f0809060106050915030106030207151e0c1709010e060610 74
    0x1d40d140c2205400a255004640445400c0d16400007543d800340c10041e03481e0742d079010801c400c2120554040d41800c0c1504c0003c640c1c18601c4402c3c1d02c8100c1102c003c0e00da162080601001c000c825040c2c2401404c01c00415203103003601c03000e6800003041c1ca1140602c02c0d070800700403941301800c414495807000b41c80380c2d40d00708944c82c01c4144011500503142c1190741716400e01048010500a0040c03501e60b01c0901d14050200c0b0080c80054903c81c0242c80600d2405014020350b01402440002541c1040d00282056103940e01e8010072031440c82a041d20125041d2100c20000e407080e080000b442c001c0c03016848090a01c041d9000440d89254111682c0f14558031090041240310300443c01844818009000308070480118404150180d00a038042e0001941c0024150302b030050302c240c2d454444043c418240310000000b1b9980c2c4c03103a4103070118a6402e80e9540d81c12208180140548185490303004420039191412151030b50081c010180540c4480c09943d0010302c052901d1410880030440343e44802 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 175864424 1250 175863174 175863179
    0xa030509031c050c09060708030f10080a110409050118032312040807021503060a2c0601051b16091506050a030207020607140d0201110d02070203120403080403061401030804 76
    0xc000d01000b13422502031807400c015416440d1260001403240c60f00030080075561b810014024884a03000411500f14880c50040a010640300424045905508441240003000000c4000b8000700b03000e1130001c1140d840d004005281c0c0c501456014149400394a0741c02184a807190154101d48681c1c6010402040c03c1000d961203101c0b80d407486070003d000f221807500f030440741c1d0b0101c1d8052811458080e2040740100804c0b88a150411084001c0d140b00400d9050500350102c1a0400340880c8100309001000c8130001641c0e80d11400c256420b11142c2011880c01414102920f40c40d00030071180d08090390350840700400c0705603541c064015070103034107003000003d40c4c6800011603440c4c01075905541056006c01c58280540c2d5483c029182050040071580c00b07200804d5816031508200e030351048256414886a40b030307045d20039420b480d01e030b12a0440140e551401880041d05029800030401c58246010402105100f41803000e0010360380705c1c0c0e80c2081070784254901080020000d100050404404000c01e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 175865674 1250 175864424 175864477
    0x103020a0c02190306020301030309080d02070b0306060304140102131a070507051002010608060c030603100b010806011206091d0622082503050a02010b01030603020f1c05030f0a03050903 82
    0x140c5200c4030700e80044085282d240e5417807005a074001e82c410350004001020a02002009101c034101d035000d180020046145468080c4e600c40c040200030700e00c10840440014140000310043c1c0c1100c80c03406008540d00d1010004400401449025120f0500c804008034a0a5054181120140380d0801c00420200d0300d08000c110402181e40f000b40f00b1035496010019002000300445805030304041d415a850345400000d16240101e20020300d50883c1c01c128542810fa40c0011010b0380118007071078200e6107030304500894005044154000c1500919180c030700600d0110b0200382440c508414000e0350319035254614118060231420840468184c1101d10140c0090060002400c1d02001240c5142038400c0321145110a01144413050300454070008040007050360a1060020004007424100408c504640104c1c06d0300c4400c000150250501e001480039100c40d110000400c564840e044964031410340503180565005007040202203424000490b07040c0d40c0120686000c011880c0b038a07022000008032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 175866924 1250 175865674 175865689
    0x30b04021309030305070e011d1002030c1506150a0801091e090b010501110102040e0a0b030102130f05040507050c2a0307120b061c0303090602160f020108060103020a0c02 75
    0x300e034802290040d950301c20280e40030300c000040c06514000750700e1034601c8020302540708003601b440c1001540350703415a83e0103007654002d0b00c070202910208200034003000e040c1c0c0f46200b8840181c09034481c004100e0368215414403801d11481d015a20520115040d410311a1607003e15400c0f90049000d41005000c0d90585900609840007184000c80b4400384108103441290f080b0030007683c211900e003005002550b000f04072151100c3d01e840086241c24902066090030510240c1001d440c203072617000c0450240d80075010703181102000c000985d03001e80d031100e100c1100301a620515000d10305040004036214001d805840761004c01002500c45014503200004101d160400e025940184070b8203280820749082000701c020b001e04c41c14111100019041203120480001c1275184600340640d81102c5070740c86c1801a10540e641814042405012440c245010380a507103a452140b150300904101482451101e468026001b81c80d0404070362071b400c0c011810381c40b80b08078a1000c980410a24001410002ea = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 175868174 1250 175866924 175866931
    0x210c160807093806040608071d01140705210304060c03090b0112020d0506130b15010e1207050402070c05040e0a021c0507031401020c070b0306090a110c0d08151207030b 74
    0x4a40c10300441607000051341c2c503001a0441000a2904002c0003006a008078040c1d0500581c10b0f001e4080d0000d01d00024100f50640031000f40112012070f60400b0000e040003001090121044000c101a01b000f0a04016400c00c49050f02c8a80c1851000346132540a8450f20340000d4024162040c1c0e40c0c00e250740807028411a0a040380c2054183e40114003040091103254000d488078612400b2915090400aa5a03031020344043c0315450411400c1c00e42d81e800604030248161b0541d410281c042071340149604181c002d5002c44d803c54000039080c403c0260001410060700c40440b030410092420b0142c842d82c80f004072400070b400c215041240c224030302c071482903030000d1845002101c80a41e107035a65040665607001e8003421503034001c90f11074140c00c01031101d80040e0912246450942c90b0240004410507400f03000707100c015a40d141c130082900c10038001c03580300e280400100c03405c9952408d8010407000c0121250714804e103440540ca00741d0314001054000c0001060700908000d410764a42405950014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 175869424 1250 175868174 175868261
    0x601270e0615034605060406081516051209060402090f070807031a130207120527040b060310080601080304061d0102010b1810050f0102210c16080709 66
    0x107014880c102030b0a21613841450380841300104d00e90803e00e040c0010380702550415690358114040b13510503200b810301030590015100ca83c8000e00d804101d8147d030b1910840c1440e540081517081048100540050898061031095545000551351003280c1c050426041c1c840400207444d10b03002c103000d148179410003459404045c2021003005a560000341e04051728190040085802041c2107041c882c0a65445000400a041403481e0040c1c964103140400c0380e100010380591091608091a070311507a005812219001c4c2c05d0550342e00340155100e03d04803092140841c0d82c4904000400d17100c1001c0192000c45600c0d4940307018130b1030350030301085442d5102c0c001241199070311203001442d0741d83d030700080b0440c0c0b6076041208281c1c03c140784142c03c4100b4a8200358000d4041000f034404990b400a1040408941240c6052010f0f19800d034111003445088031001c854410200325404e00c0e4200c20450b0201c42030720703040b2040c581e61044068151041c050107100901104003210302e02d962510808518050300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 175870674 1250 175869424 175869511
    0xe0904030f02011b1d01020a03050f030408040308040b03090d0207050f010c080d0c050c06060607031d032112011d160e1f030b04140601270e061503 65
    0x142144c44140f080c01060040c0014541c00850100c80300701088810125401e2029044c981003d440140a52040784c0b01c21030303005400000a4240544501540d0103154030032081580c407a82c440d0482890742003910702008600651104440950001900d03400300c0300050112642c91144000540d140f0b1400b40e01a604000d00b004407000184070791081e448052a2600e074561500d65034000c29207028001072010740a80410030444020035000000131b02500740300d03c3c090b542582040007107400c1c01501c0140b10000f802c0300d00c959010081070b0000d40080c0380d80070001446070380d940190880d420f00d0342c091001c045540c64081440ca0540400d40614540542010100100e6007004101046030003011380e203c9210f00b040383c84410307a2600039070b406454200c030180004000043e80c5011141d000c0d25480c14061100142020b03440c3c420000c24881c0c0d00d4900c00c0864581e209a8800c04040403101030b4801c5444088030004c07902c115055034000e01d5a00c0131032741e20314440e003001c0d07282045c6200100c844120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 175871924 1250 175870674 175870691
    0x103031209110a08060403120c0207121103060f01050301141510021203040b07030c03020c0715090b0d0e070803071109070c0b0414070b120606090d0b0a1a010e0904030f0201 76
    0x700c100362800213011a4000b403c89150070f040c000c000100e81308100d80814101030801d00d140303500049942c01d80d901c0200d185000c09a41c07811484003242010601e806010340340800003098901c40d60181201c1c010380003071000b444440c0d0310401840c01141c5291040b08040380d41d1103541080889403082c00114012680e03403061644888889030402c840481da041c40002c100404140c0c91b0041040f480c04e6410154180803103c01101e03201c4445019844d888641e01074100d44840c880c40c4003400070000100082c1e80c4611502001c1d024107946150f09285114109000408100020460352580d0f000f0030b101c8520304101c4100007480358060f08100400031042c540c5c0d00400c00b03c012160103184100311312511220807003041c81c1840e0059200c0c01c1d02d0f000601081c000342d5080e5a0440d0300820450340c1c00ea41c0c07403078000040e4900e0035001002d0040070030002080f02015050f44103c8000c072102c4611810012450300446400c40707184e1600390809025004a0002400ba42c000b034016220b40c0000300b403000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 175873174 1250 175871924 175871929
    0xc03160602220e0a0e01020d06030804080601060e1e03210a09050306010602100b1906080a0609022a0a050f011e06080c090907030204020d0b0f09010303120911 70
    0x204002026192180d0008620100c20581c01c0301d09066510091070041c000c0c50090ba54085000c01068224540d40740c01c14400c24120a5040796400564010108a0281c40b400c204081e90040e002d0032040b407081d00000310703515016030b4a000f48450000e21720592144028451000800b0b11051150148250040803851481c5900c141c40000b800070074003600c0d00a4804001e000c042580e00c0580a5000900140801940450030b0414090742032404580350070190003296a05050f9081c0c0c81451034181c60100d500350340100c8040c01007854407410b000141d02d412466040307200305502c1e12030740c0500c120581030100720100c1382240d0350140001e03501d40114549610b402c10350401e0b00a50700d0b940d07907420002c0d0150014068440391407a0b640030070003942002e41e01c0b55140242c446083c480e00a03100014103241c020007030000650790184c801e64035002c002030990090940c04208521480e02da1181c21900d003000c0f0302070380c102d039056583c040300d0404280741000202008101640c1c2010350066280c00764 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 175874424 1250 175873174 175873207
    0x60619030f0f0b0f121902010e0604060f0906020d0c0b34030e0102090a0314030d02120a0b0f03070e15090405030d1104290c011503060e030c070b0c03 66
    0x600420070100f440742e10b403c00c01c4500d2201d010305600c101c4602003071541c0d40c4400590740800c8081c1e401c85a0040c0903500051b02d80e20004000c20707510040c0018041050346d8819044595a0411b0726158080f9484020607600c0744100e450b4040090f0b905403c00010488d244200d540000003030404202d40c1e9130750700d03030140c40b4003011a8980060040031020280c0c954984035088688062500850038250003900041c0c89002d98403010f44010600145048081c40a004881111000ba2400c41d62004e610303920320b4215000316100303000d552508481030500d05105160485e070041c005c001c0c11003035090192400f4400000342501d0070040c0c5c0c6252514090300e07400e464501440c0104000c4d80c942151212450560324000d6003800c1c0302e14280001c1040422815203600a114105444240c118403c090001c160143d20043c1c44d140d07083c001d068002209150030102900e001d4202803006000140c42c040c1c0da44180c00c0301141d95406038004000340d4140001a003001c0500d8400c0e01c0c41c02c0c5001202c0d6500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 175875674 1250 175874424 175874441
    0x51b0f01090b010503010603030c110f1804021906020619230f0c07050a06020901030f290a06090909060e01050c041d0c0301050f1f0e090c03060619030f 67
    0x140d80d52040c000c0148081c400580c1d0060000300c0080c01102d0450f5030040541c030110100812a1f01141e1214200b03640719a00d47c080c0007400381c0090841c40040b40c202000d00000c0d03805034000c280c0d1680c0c81846101a01d07402e0203556281e0000c01098941c1800c0700c4410040105c080d491035915060b00208422564a1103c0f044078450300f00128144142241807001c0f0150003486607110802044000030400b00c2c140c1d040540103c80162101a43d0005034086c0018103581e1807103d24020f20380000340065600d10b1201c00f01d10012104c00031500050141d0807000e40070305004201d10032010405005c00e80c111172525441405c1c04500a01180310032400c2d214140c80d580c0c6a048042402d1280c0d981c83c1031740405c1c0c0078807a0203071040760130083e0020304584010b00405001e000d00b1029a046512207070450168030826080e5040d1424400e030f00242241c5c21140130714801c00010300410300450605041c0c0b4052080100002d2400d0b00b4607244420100b1002c1500b0185a120140400c60107040e04c1800b54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 175876924 1250 175875674 175875703
    0xa020102072a0506160b0c0a020c0d020306220803090705010f05120a1d1615020105060f0607030210020c0c131a040b03011e150609060807051b 63
    0x1c5441c4146040c04090240a030302e800c40150003070802080c807a0703640d0001e048450541300c01e9a81c40d9a00f03e41940c19070000c0002d492501503e00740100d00595400034000c0250580c00e80e0b059040c0038040200c90b000801000c3d5242c0e024102003841c2c100540440315910440000c18008500c0307941d161207040c0c104a076590300319041280c2c104099600040015604401868414902192242010346011010303000d142d105980383ca881c1c03c00b03c507079208060107100361801c440140700010b01d4503403001d407140500d624071340c9100348d001000d80c014010036008010080007414802d00304001d00501e900421010350462003400000c0701e12480070310061181d100943c0c05019410807074801d0201d00c80c034505007101480d1410f01c0a200714455800c02e40e599110031a00820031400d0f100020f809086450995103c150f02d810500c005034041c2d030702880f0302c000420b00c03005a00741d94400c199060750b241d200d12804284208006080188207000805004045145180d80019201c3c03000d072812941c2c501010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 175878174 1250 175876924 175876927
    0x40c0303030b03060115030c0905060d06030c0b0c0a170909010816061707030902010905100c06050a05040507060c0317041103010e07260a1a0a0f1a01050d0603080a020102 75
    0x10a16a05000700342c403040b400e40082c0542d5142030501d0a00e03408450301542096610a81409018460345061004007401807000d034a500080b0b00c0800149a6403004407a13180c100940010940e0100d001d494200480c6006001c400300b4076164078030841e4210181d04d040c10340412114660b65501100346010b4000d20006180c802034180300341c07003115036542221052018200100c40410003065106512030380c2c40c50003042d5900c0520040c1c5104a0b00e40007150700c40120b426400f09940c0c065070085c0060300031041409251108034001046900589003c3c0598001501c14070029015000c5909101e200e407034146e107000c0d911140b5180c046400e44080b15102e082071400e8180d0701d002d00900c0a04001040500f090915111030140195007070700400416012500543e000c003c400e0011800c815001250042c229099000e44045504100c80754024140380503100300389640d6901c43d52100c0c10406030f00300211000100159026000f0300c01c5030902c603440b41c0c4007000049140018122403070180e000503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 175879424 1250 175878174 175878179
    0x60106110c0604050d02030f030406020313210210090902030109091a0601091e0801021201180204050d0206030402190305030d0e0606060d090c170d0e0301020304020d061112040c 78
    0x204840903030340e00d140031030740041ca00802640e600b804807003c80380b040300c000000c013015102180c01c00c0603a5002e040309000c00301e0006009034021004204090602c0306940705ca0307880b0403860340c00c0355004c0954000e410008401720010300b4a203d070311035010740b03e0500a82c0d0b1039840810000b640c1c400d801c1500b070a43c58490910811010b0f000050260b030801b0808511442c1220008240f0380040c803400c1550100302c46060709911800420b040074080e0000255555056010764615010082c031402c0c0741008280daa21135001e05510a40d029110000c062559440a980030052580c00103001a230381300340072451170f03a640f20280145d20019031040300615161001c480361141124200c8001480642000040100950700c00040300c4810580390340001d007241d0300b4101803411800f25000039080340e080c201004207441c000145982d0400b4203036240400004c4c0c0d10241400d070301040e5002508084013601c15000110950821306900c190038851505041c0c190f904815a02004e440c1582c840910760010b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 175880674 1250 175879424 175879427
    0xa0606140414040f2d0f0201091703040603020f120a0618020403110411070b0c0405040c0905060d0b01120603061a0d030c0803040201021609021206040b0d170f0309060106 75
    0x1444240500466960560b10f02030301d0381c42c20f00030081c400500803508a1001e041c1454400800020384181840d0f000310000c00e0300e82001032400c1110164041130501200080407494100380d0440000224090b606081c41c1c90700c164060340015880220328981403007100d403240148119948a09201ca002051032031906100013000014250303403124683c0104000c0c0041980e50310349080c0c0a005075000224201401c1200c0c00030b00031507400070b0480030f1003000c0c005240303e28030140054800c220b13010050703c440a038040d2640e0000344103043d00b0510900c03840e40b1040280d888100606010306080c5100c0e2a0200c1000c204c5026070021a5001e03603c141141a5041c0180390b0710129000b40c4580c81c0011050310b024024082c261801400e9050020001d0700710791092149841480340134095454590b120460308000e5041a407081c5041384e0785e480000d04d01d203000d0168030ba000e50f0107043c120301c2c8003268a0340704022640902c481d5282004014585242c0782c0e440c000c500c110110005010f065040400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 175881924 1250 175880674 175880681
    0x21030d050702161a040501120b180103050d0315050d02010903050d0f02010e030f03040b0c0f0403060504020f1503060d05070f1203180303090506030a0b041a1008010807030809030a06061404 83
    0x12548200035a40b11305804804040d0443e41a00d8090a142441e07090134a0707500d0203009141907898121700380e400c41c0806111100080c0e810b8078405c8040d00c0002c1031101082b800c95007504850b03030701802e05590400c241e0a050a54105890061500400803074aa440d41c0d031510300500f035030b200014046441c00700c1081c0c2c284100e49001c40300c0009149002d0780040c44d104a4080600040c5c10080c0031001f14981e28911000c4404500600e01280d80301c0340d032410701078010304003200d059010b2685000c04031168074140030f90100000032445210b003592901c0c01031025441680c40111a0761151803404100184154545001003000d000e039241050114a00209900c895030741e1001071170012242440040d400210050546005a40c0d29403295200000c120181841401d015001850441794004c1c0643c194100c6020b903d05941192800d0b412113001c42c1d64500922400c5c2c7c681d00402c00900c0052144001081001d07001002c40c0d41a4005448080886915078058501c0407050803405040c1e080501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 175883174 1250 175881924 175881929
    0x30e01090219141206010905090f0a080a1106060108040b0601020a060504050303091509060c0f040b12010f0f060e120c060a02031e160b0703020d0204030f0b010e0621030d05070216 79
    0x184d0360180b10421000d80b40d1307100b0041c0a810b0300356498100041070001c040104451040070101101c05c0b0320480d0504805a0303008101500006940c207685601c6901d002800500407003040e03507580c08170380d9291903000329014041c010b641140100c9400d94041602802014001d50182016640d00c3c00e080c0d0b68945040d010b0000084003244110420100c81d10202d0521f5101c2c004404540d03803541003c1c41189180700c0e40d0402100c01707801145180030759055602d45030695581c03a510f21821a1110244000084588a5040001c2a02c0464070031030822080c1c009080e1918411100724200e45400181c540e00003240c807100503800400d0348004030318516650783e030f5014040c0d0914036009003d03042404c607501ea2a03014125035156404074400d10b01c00d0b8112841c1301e010080441d195500ea01e0195084150352130305840000c003040000c500c0701c040854041c000e640c0180040d03011411017844240c01e003450740300892640000d0007070a080401c540105807080c005c0d0350192800d8000c1c0190b1121541c46038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 175884424 1250 175883174 175883179
    0x10903020117090109080a02010203100e0c1c060302030304120605130b06012d09030501051f210f03050910020a02010f051c1d0d08060907030e0109021914 68
    0x400080000d070741c000b445604840710031103940e141d95883c41c9a0314090000450002c00000001400c180402d2341075015500aa00aa440c40303001c998403036001016031300c283c030311150800041003140007000c098201a040e903000c1a0300443d05035501e400003030540c0c0180d030022034203030300c014401c00400010380b01c0c0980c0b2543c401007419209882c2c1c0c880ea546400d00070301c6181070004060200c0f40c1294200320809001080600c1d400049141200003005070140780b104940b00c0d800c14010564503410301d10600d407200903015404807118900b10120307014182054000b85800e44041049012a54410454070600e0082d242c043c1d8410465080c4442030f2058401e1500315002210880c0040c1c8e0300418803140c3c03c00c030b4a031003500c0e011501c240d00c80e580716030f000c1e01c01210f2400d58420180050400d6802c90501240300703032000c1400d40c00d001c0c0d4610174200d40181d880f0301010700045409009902c51000b01ca0b82500016040703416070f0204100f2049410002420916a40c2c1000518086d90100040400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 175885674 1250 175884424 175884437
    0x1903061e0e030304411005091b0a0b2a030c0c0405151f030b0303040f291b0c040c020604020d02240c010c05090f010c030e030a0302100b01 61
    0x1c0d40d419890f03020281c40204040c040304034000c00c2404580210f03a2548446510700401c43d40130b580200d40d02a6510318100c2d5003c3c89a10703903911282481814429103106d4041c04982140d1044c83d51580c00e00724009034080c9030b03498081480502d1001a1007120404100703840303621545129040c0703484880c00c0f4400c599000b008111030703804001c40c904011003010f42e0f0100301c40e00c4401d0326003003920389414141e4101d00d942c48400c10b05200981d1421405901d0b8400300908000841450b48a20550042184041000c0800c01001395041c0344040101e2840c8800f0104003000940030000e0350020720041030a9500c102c4240d0030310b10510201504050031203080140552104001e51a4100104060b00c0342c9a204a21300554559000e10542c4140c50f1034a2051a030f030320f4561882c2130300f0032080741ca6550328020101160302d000754111480c00c42c00600c04030040d0300001c011940c10b12418030440030001c1043d00180780d500c1c100301c1072040c0e074881d8000d0325040b084100e0720000c441030b14000e41d040104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 175886924 1250 175885674 175885691
    0x41401170601050a0827061005040506010c0b070909060b0d140105012a08070b1501210f0f1a0312090901060f050708070309050316030b13021903061e 66
    0x2c0250444480d03138071a0070114070503620b000200d0b821030111102c0716000e0018040d55810100082542031084403841c515507082c58a80d004c2c0400c49800f120054040791b02943c0200100e414007083da98040041d15100d0005a194410202500c095601c840104400400ea02032401524000c8000007a11041205a252300d80341c0024034040d0b4059450340c1030942e042e0a210304440006031580c007150014801030b904c01c01481c0c80002041704440301d0203210030180c0700d14a84c2d8415139001b03800b1100186070011241c41d11145100910115050f80c204a81c5c1303103940741116421b0f001d01802110501c10002c1c2d002002801d05045c031150101203016001e0802c404d40c143d54501c00014152403040c0361010354a0b42004080c1c0d01441150806080f400004c102c613001c00d0f80c4004808140c072400c0c0e040e15915080b1441c08100704c0101c0c0401001d440f07214001441d0b54019550038201940002c0822480310780c0b00a00d90008801364000384c86c81902d400510401440d0714045030000780030480d04100150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 175888174 1250 175886924 175886927
    0x90d02010e070909030e041107051603020d0305091c0303050109060b0313030809100204080307020a0b0a0f180f080105061c030c06180605071106090a020a17030f041401170601 77
    0x281070b40550785072103581d04070700c20905d8400c0c4c1041a801c80040c104112a000b000b106c2251b13900032201c111403030320400185040d002201008501143d40c0600510590502a40e06640d1500000e41071604000840c8120b618401103008040c01300d40079440018081d41451780070340c299401a08010100d000070014403040c0200351400128440d09850b001409460fa01822410841d17044850b03200c20340045004075034160040f00411f05944205c1b801d11455550300c2c201d05260044600f4440400c0c60803404138030887c003c8801000542c100c6241c0860300ea00c540303400442d5034280c0c01400c440e030754a00070049541401d950703090281c0321501000c080040143d40040280909100041203140c480d01c40d241240d41241818500646c81501840a441c0c130003c010000708a0b82c3c2d00d11b40a22803080401c108540116601805c0d0b500504004082030a103132103040080c16840a032043e620040011500c0035801c28040c00240c0004072405103510035071400140004d00350920041160540c0c028850740c3e0303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 175889424 1250 175888174 175888183
    0x5010c0206030717090c010824130209100302070c050307050915040609090f05162102030a0507060908070e22020102121305090109090f0305180d0803090d02010e 71
    0x998101d41d12036a81d52045030445815042c0543c85a4000e50141408480c18010032440c181c00c1c42030380c1c0c000c40f5550f401c0b41c06503d40c5007881d0b142c229940380d283c0303041d0504091000314606100543c0141c601702100010542120400c2031140c002030b400302c0c50340104442c0f401441c00400b0214010007503175040c180040e00c1280040d1486141d80c02c4035040061980301da0b00150001c207001f0718200300f81d00c480e0403d03075021101c50714112968000d11303d84c011000303103001041003903446507681c0102c1c48001c030106000c03160038404260b07450b11070440c01c500025000c100e440c018185650340c2e603803d1072400c58128a445000d40014241d0102d040c10400b0700ca004008042a40c8000b105c400310150f1280010f031f0408040510b4011800350018148002090b0314406204407a03013600c52041aa990f020140700f11842180020011025031001d440400d221b200035003a0141402c0944254039a8280080e0914500e141d049814480102c10890656814014004420040d000920a286041c190305455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 175890674 1250 175889424 175889447
    0x615030d0f030e030406080702061b09100516080909130209060405071b080a1202091e0a09020703020d1101020c1f0e010f0b040c1719022502040c02070501 68
    0x8201c85401c100314400e00c29004610307030100803003d5940c1c0350784032400201709020448910340075108800104005001a00340c5540342d80c0750b90301071070801986a04108d0540041100102002824002001130058070500b00030340b81d06c10040da0b0307554284001401141203000b0014801484c4034003c030000b58540c40c3d01998400710803a000191607841c0c3e0303c29108041c641c00320310300810700602c103c403c00628500030106941e40d0b80b01c101503d4103907401d040980c80b6428040c0c3c0c02114054042d0000214141e100001d1200284445c564070f8407400300c2c0c400c90b00a100709500603441102c101e54115000052124400f0906000307600c8c0007159a41c0c1a50760a800c19944060f0b0650360700d10000f0101c940c4090311602001009100e03483d070ba01034400281c11140010361059103845207041071680201e03445511400c00e021851219620748900c40549d4036084400c001041d020428440210340c0c140412032912040c518200021616006000c00c956406004205541c804c1a00340101d071307000700c003100c41c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 175891924 1250 175890674 175890677
    0x408010c1112180a0b0a0e12030408070b0f0c0a05031809330d1a060613090504031b0317010e100506160203060112120e0105030109090609080a03020c0615030d 70
    0x1c3c0d21000c2800700d0000c0d10160f015141130240460080459940302e0a4440a88030455200d1010206950041d88034411446400e0031548598420408655003a0140051105804401c0e0500180225250404500403001c4407590000034004102c0003a50007800c800d294113407400000e916000d4110359440109200b10402490070032036a1000307180161000515080240911404004600d410310416103100051442502d2140004849041c4001a0f41c55100d42c80030004040d40b8101c03a0301d0052001a0041c1d080220004020341810040b401001c00c0521998401001000340c1e10096040030707043c2c101400d030100c0350080c40304e0440e80d800f040d415120101d44d01503407410300002e00a600e09000000940600030200000f80e01d07895840080d02c45401a9103050700e82c031b113a1104403030781c450f503401041c0840e07410f01c01404002059881407800b1445948001070000b9039856041503a0414940c1d400020340024540c88081414080282c01100d00400055a00e8403000007e466040710b041400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 175893174 1250 175891924 175891957
    0xa020a06080a0b040615030b030111030f070c02040911090a0605060901031d1002040602060c0a0c031103070b250305101e15020109020f0f1008100503030408010c1112 73
    0x11454142a803200000b42d8005004011742581c8880ca030383c0e8861904d40e020042440c02030a202c0505043c000c40c40101d00212a062469481c11445050703201c01401c0d40040010410a0a006881e544260480c081c00356101d0118401c842c1e040011642e4002d02c40011a030500c001040180c503010180c4000001c2401d010039000c1c442015081d0292122460180030310503401004881d03210f0340d00030015501150301790740341540c840e00f0301d000030310941000f84001600421000082032280c1079200d002078602c01540c2c58108152a401449102035600f80480000202800a403409002d240d90070f20b8601d05080c02149403124140d00c145040c3e10a4021800c25441045200083e0300b070b41c50060105d101500c0440000004000d000f8444680304a0203442154016542c526145031003280c000700040115103410702494080314450400b500444842d03020301e0340404c0301c2c1c2d400d001610141071030100024401a04481c018030300000f00c01e100c62590000c58422181d5134044088850000008a440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175894424 1250 175893174 175893181
    0x50408120c07020112110d0f020909010b12010e0c1c150501141e0c0d02010504170301050306060f19080319050a020a1e0605040308060901090e0a0b0a090c0f0f080a020a0608 76
    0x2100c5500c0384e48030150350702e898401c0300070323440c802035002d0078088406488503855680c80d40c0c4102003520492854514919810f0010040303004080402c80e48401c0088009041443c03001d0118080d12901045151441c1c440070411442910824170358010802441d014504141c05003505219200b52008501d100d030b55031008441050b140b208a0354070208075000c40d2200c205020000f4020030051342e0480340d88007507070f401d03d0070300d07a5001c16a816a180240589200d1301c031041000710800200c0380d0030b60080541d03038104842c01540350627080203004401c0a5039590f4107030b04181c11b000c414801c040741445028003441100d541c0c0000c0984016502c000c0e0f41c90b504211004c420305a20354140c0061800c1c0c1071408110030103620105041c002c420560f11030400781d8890680d14140e17120014408079507400360004170049803030a4404c9030024140c1d5800140512591503110390001580c10030008061100c030100540403580c8001001000002c0203801c4890161740050030010751842000204420712010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 175895674 1250 175894424 175894451
    0x11407110d05030a0809101b05030709050303040f0501020c0a080712060e0105130501140412030f0b040c02010203040311010606140a0329040f06030b04060903050706050408120c07020112 82
    0x1115541d80c10808681d1990594440140007800c110385204841c06800b0031500840200d0165000c0010301512802c0e04201d00d52084405400080520341004103400e000109514248001d10140444c0128107840c0b0381810006450190101c0303684e03005880b00c48040010210100300d40c002d9580007200b07685080d40394181140a01840c00b059480c6501c1d10003882060303004504d240380b010b84508001d128150b2110b20401e5800d41c1241c0c00f50210300e01c5000000ea4030310075400210790404442d000900f51440c80f020400311018600a080580c1d800001d120600d60030650724603584060340007d0002500303050b0024200788954818607d94800850050700e014040c2d0042120444a284c04200103400d40603221345d00164100b00038000d6140070200390380d5015a008400c1629044481c484983d10380e9941d20008202e40e0200780e040002c20300c0450002802801150f0003a0301580e61140c4a0300070038418400e151000e4a0f03070070346000821101005036007084080c013903180c0d942000141a02c95529 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 175896924 1250 175895674 175895689
    0x1a0a15050c06010603050103030f02060f0a02030a14010803070320150a1413060c090e160e03251d1f0b0a110c0109180b03030904020c0307020f01140711 67
    0x1807442030184400104480c1d502d6441681200d0003a502c0c40d100c100c24200a903114a01602c161030301203c1b02d00015444000d54009582200100c2d500141c403104441e1007015400d4280c1200c10f150708000b68190900da401503021130302804a500d01d00011080c44003856841500d500c000240a01d04000103441901c0b6600c190700c2462415212000f5141c00304940c00e9000c0e081c00226040c034030740030b030618040303104209180540f00011000126130301c60304187d802d1202e00910041c2080035411220f21282c40500880005651600d4401c0c03841070750300030059010f04030703800c400c0000d500010b001034000c50300c200980d0461040d140c0800d002c10940c41a00a08100381c1202545400001b64144442d5000120215468010701942c0f1101c803880011600e00c071580c4102c100140a10f03001c444c4600169100c0b00b08010001c0c10ac83c0380100600100d0241c2c0c00075a5040195000811110f007541041080840904003d18204c045446901ea03040504d0040d20805010442c0703020742440725440c1d160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 175898174 1250 175896924 175896937
    0x3090c090f050609090c030a0b1003231009020607150e0d020d020708060403020c01050f0409050703020c011808040b07051e0606030d02070f061d13020c011a0a1505 72
    0x5001203840031890341d0190400740e4116005105078400100005070100b00008031101c002c000e002e00b891a03480b40c400341c1801800820b814101c480c0008001070f42484001400600702100c0e2940040040d01d20f800d0205d102c004034025030400c190000180d0f2031008581007213520204038030301c90342c4c5207080c1d81c000e00f090b44032880d40b0310400b0741440c8450780010b40060356843e1035007143d070f8172601c8a08041e2510030030b64005015034001600100d20750301801c0a03044090504000c241020f550390f1a01095880503202c1c0c801207680003c807030382038132820700550340c030807050740900510000c40d0340d180320081c4601e10480e4030600d0042203000410a0500c0441420319081048640840c4500b00d80741d200c607030a4078400e02c2072146420498a150001c41c3e480301f140d440d005126000303460070341e00f80c031210860ba640f64007000030725040742620380c3ea072420034031040e00c0c0e12001070301d4907911144030742141c0207191a1800740102c1a811100b5944d4030204405880400518512603100c03110261034500882 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175899280 1106 175898174 175898189
    0xb030706080601050705060412260103080a03020405041536020901110f0114010b131203020321090106090504020906100e040903030f0c03061503090c 66
    0x120441d540c420b8040c1481d41c9030500380e96515040c2841202d049803006042030104001550000780310b02c00c1070042101d49501c20000401082510707052000400e5084005a0350618034400d4058400424014100780703e99111504414006c51203405070f00740b032035050030b480f2511140030104400f8419581c00480d01341002c04803410040d60149000fa81400850060051541010031110108080b44c0c03000040011103a0211040041d0603844450034000038031210018046403500c1c0310484101000c441440342c100d01d4168114011419143d86550075800710200c801c8041490358400c0e60090003c001041d1600c1420701100e105440180d000307250100068103038100340429159000d4203003028806001d070000094107948a204084000031385803c00900e00390218040d0400346469801d0070301c0103504028881c03403c0009200010f00700750321540325030288211350b1020405020391 = true := by decide +kernel

theorem cover : BRFrame.Cov 175719424 175899280 := by
  have h0 := BRFrame.cov_init 175719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175719424 ≤ n) (h2 : n < 175899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
