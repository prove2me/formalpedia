-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:48:52.984176+00:00
-- url     : https://prove2.me/submissions/be18c153-1fa3-4fe6-850e-9e72d2e32ba8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 218525179 ≤ n < 218705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 218526429 1250 218525179 218525221
    0x2010e01180c2c1810020306040b190618030501090b0601122007020409060905010b12032802150106120501080a050c04050903071a01030303050705040f050607030306030803 76
    0x1104080001c00803804580c51070703005070707625011141c000c480f51518001c034005802e6a603c1c0000110407140d14a0503c11402101a04034015a907800c1803070802003500c5841200c181304104a1511441007480d540d081822240a41898a0450b4907a0030340040d12516900151165081a400104106801325458402c98090701d810746490069200b203804c90303000844810302c10383c104034001c0003540301e6405420114801400071480700750903600d85090365080041120169150740d2540164500101c1010210b00315000841c200756000c0185000402d507121a4501d001c5c02c09402030700f035442071110070404401c2c40380000b01940d54500c02462084403080d54030145182000202d80c40902042c0050b5040d0400000e00039603c41d9802c210003000b0107040c4030100e1008010500c00500f8a50710904840c010200c06c04040d03245003400b4051b05d400030001000c01104010501c58a40c901b00f0640545405407615520f03900c1c249819001802c00c0d4202030503522020041040404015094408a80c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 218527679 1250 218526429 218526443
    0x307030314090a02060f0702041e0c02030909040605041b1e090e100b01091a031906030f1401060b030a050a0f0e030a080c07020901030803071b0f1202010e0118 70
    0x5a14651000340510050302c604001d50003c40b107040241c64054090001c0a1444681901d005039580c006000c540f42501c2d4580e00c0041c2c5810303c440c01c100c603c0f0b81c2b1140c0000b8006076141c08135180001d08010ba00a1009100715501d10100d018071220304041c85020024000c615090743c1c49900500010014042802d011b000142010940740914001c030b0200ea0310305ca00030007500b22000f510b28007402035402c145040002641000813000c94694010780310541920b400c03952400c2040c411201c1c28480b801c0d20007080d00b081000c000068817640c010852a4021900301e44c2e8030305025109000d0183c5070f2180307403500c5011043c8401c009182c2c1c00f0300e00032800c1410406c0341000e03091010f4191740c4c1d800c010048941050007484292805100c00707681c004189031a407442d0070704560014100c41800c0e0030036540d4410200030004095000024904241441032815a003960955500c014800007036800501d00107444a8468a6600035005400038218150091113040b0407610707003080c18625000150760381 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 218528929 1250 218527679 218527691
    0xc0804120c12050d09020402040b071109090a1502090924031b04090611070b1e090a06091a01060e01020d1805010c1a0f0a110313031112070503070303 66
    0x45401203114060855002c00d5115840390081c01c03e83e09a008100145a01d5403500c00d07102c010303550f500c02880a8422000000e4031603096051034800c0308411a0b0355800760b4611018440107400c0099407841c04c40d44208031000c20040829850040c0c045c00e40382c0d942218084040c4513400002400c80c7d071401020141000e550362000b0201540d48844954040001025131800e2030300741415000607512030f018500100d008a20a4030b900d446070711805040c0c50120100041c41161b00f8428440102802d441c0e0014245060060380c0944500c0250001800c2643d50004d0500f0030030540c2d504000b01240011014039036a4072000580103800744010340c0d005010f15400b8104603030140940320b00e03108203000040e02c0507080c040155a0718504503416111b840091001c90141c16a03441c5880c800e515505c02c590b114100020144d0690b580004d40a0448074280b0801002290f980c440318500740c0c0610380301d4181c101540c13045080c07550601652809102c0001d4100030b00800000130210544259410052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 218530179 1250 218528929 218528963
    0x3210a0f1707080702120d0c0801051509040203040f1b090e07062001020c0d0509100c03020307030c0c0b1204020f030705030307121806020a0303052d190c0804 70
    0x1034a650040d06041c100020300412101ca105103010b030361045040c0120743c01d101c4049400300e00d54111001c05804142c42d038240200e110b40c0081071a00603e4160350784442e05816603654800c0c0d008038080c45000c1c603400310005042c403030801800b100307940d0010440804400d40c55424683e520383d500482e4080d6040104003030351408000340c0e01c011a03042d5078480c0d030000902c024915211400501e0044659003c1c0101851000107200100d10103e103616110380e110603c8041c840c2140042105000388400031540c0d1000c40d8010084800c06541072810b002071030803c4c60a820b1005940c0c009900d080300100d102c0b00c0070704540185500a0b8000c030b4811180a0504041680e928901d014660701038005101c03400008000354214850780005090194060190030810f000003a12a4000d400503807080c42d848060607018030966030005011415943c003003545a00c081445c0105849112031400d6290014403c00c1c5a565420071300008140140403507148804000e0800b0810390f01500e0100b140e40c03040c14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 218531429 1250 218530179 218530187
    0x90301111801030b06070606170c031203070806011e090306050c03090d05130909150515010e0f01050c0106090603140606010c06090f0f05030c010606110c090603210a0f 74
    0x7495018481400416030080300044001d441521034181c0c1100342400101c0009001c0d0260402820320101488a8960741800891500105003036042c0640c10138441c504c1408002400c5075070001c41c80c28442000c1c0c40b040c00417585e100c02c021020210b400b40300122415681d2200b141022070340588414010354543c0e2042e900244070903a07400c0902c1c0d00030400e01c101e00303005401900e146a6146800c02c50706a40301140b4050328074240b400c41d115010030281040780e08051081035002140c10740c1404d0345072a6940040d0241c0303403410b035107031041c0d00d4200b1601150b0701c030f401102c0790006000000c4c40f80341ea580e103103000074101d01c0c0011242c0e100400c080588100b80003d000d440340748160b40d861703284a100d843d10b00040545d10410740344022190a21703408079003010780584900e40300b00025035898213850049421504950001002c0210a580b0012684800941c00c0c540e841700702d404074456102c101c000303407800c0102107a01103800204200e2820594030301024100d0382003180c94040703054840d43c1e0116 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 218532679 1250 218531429 218531437
    0xb091b04110405090c0403080a02010507030f1b0503370c081303030203040c0b0307021f1109040c09180c0e010e011b0c082a0a0501090b0306130c0509030111 69
    0x10003a40000c1c80100501d03e0520000d0390048103001c1740d9890030340c5a440740c17400d41d0300c02e80903400542e46800c01c0c803150960520071011480000300040041c030020360200c1140c3c0a100c82c446040004c0800454181300461084110b03081180140f0909035241d0f1002d038640e4028905003180c3c09192810b1558590700821000f48102c03413003806090700403442d80e0b081e0020741000d0402e035000005e07480040781050281c0d004500900240c1c0044c00310380a0303000044242c5024090071800b180c00e040c44000810043c81c169110504102e90200d46912403080407074804010b54482c490b00c0c0d40810000c101403020b54440021030f506a1390740c05070798000c0d80042d200300d080c200520740000c4000121244e4101d0b04006411010311848104910940d5403c5440ca0308045e4072160181d0300d020b0014100c69070000701d101041010036500c10310510303e054006002844580f02c0c603600b180000000410559a00384e0000070140e404034100300301600100300401036008003082c18040c0d07203024007100c44130309070400f52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 218533929 1250 218532679 218532701
    0x11120705071a040b030a0510090203270d0903150b04050106080a05010801060f180b0312180406080c09181e060906040512160602070b1b16021c0b091b04 67
    0x60300c5e544405000c40001c0200400301c10a203003030560701040842807800254010302007440c00031000046680b500000c050686060728095004170121221240c21002c00c0c2c00301d94101b500ca2048038400b141d4800034180b14212241d010b031030000007082d1190404191801481f980b1380810840e80c0b41c2c950305089031002d00401c00090400031081100b40301c000000c50700d901e4410400300c0c0040345103003c00d2410fa01c050303081e02e030031340301080803004088050540505043c00720350138807040b85802070f0981c0b81c0b80c8604001d8090441c140000d075500110f13070904802e0070480400ca8410700300c02404480081255404031085001b5003001c64041d5400141b401d01070303900f2070050f01003045a4111041e41ea4455485070061181003101c0c2c0000c6034051020f08107050060003440b62910b0181240c2a101007072084c7c56104c10024010395103003e440c18044094240d066400c20f84406406034246c60072840d2032801884030b4045010840d01c980046081c0b83d564241484c550f1821903200d040005507220341d00e02e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 218535179 1250 218533929 218533949
    0x10e1306060f080630060a0c030f06030809042a05030403110115061805040e010b01030c0504060e060f31051002031c06030f0516050d1211120705071a04 67
    0x20315403c0840c0790403030f1101c04001701000080c12100c1c2d5001d007000011160a843c090703481041c42d0341c85401d0b0240c084e40345000c150400c4441d055560740b412901170007034150301071a612610503149003001c0c0c05120b1403200c1c03d403c2d813281244141008001341d1003254200c00168446d8010704ca205ca0500030615030031812070041c2e04c641e00f00303201219040e0b00c0d0380313883c001c0500142c000121502e45200b81118406a200003280c116440000074040e600d4580101c0c0802c20104010000640d0040d5041400740003116120340e100006e1620b020107026042c5c0c184481c009405c445041e8a01182d210450030f6101c41202d202c0603551010850381d0701c0c600f1280d802582082041c540007180c0c0710382c40380000c1c1034200006600c0e9120307103501c0d00b11441d07400200d072940c0c400c010321140c00308102c0c0100c0050800700c400e00014003441c0d0740c1e48000d02603202c2030700a1140c4c6030f00c43c940844003480100307569004421800d8035030380141001555140e01e4421100400480c00101520798144400c0710143d50814407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 218536429 1250 218535179 218535199
    0x3e04032f010e0d081b060a060f050d14070302060d020d060902090f0d061107030210051006050a18170a0c052b0305040504060609140102161202010e1306060f0806 71
    0x5001e0f04001c401c03412200e20a0400c041024444c5030305410301140c40c0b40f0700074051813038452001000c0741e649070010100940411420400b65803400c09103007003150b0128a801c844d00d680110f4a16108190304000c0d0301c298046011a0319164540c05849100d00340f51040c03001035901d032400000c07071061824203904280360092004060034416186450a4801d0b0710020382c00030380420b0244503420510301140145c00a4941e49075240f000c0c0600c980000318880b1410a4030318004002d1710030b10825605134240501031071180e01d082000c8101c00018101da0a00040701071201c44070300c4d2607400a2508907001200381d040802c190808034025202210f407113244090300742915482783d100100c40c842c00c87c200a010000800c2645440c003810004003501d8031003030111401d207118024013110f00c1002604550041408000410842071140100e40102c07001114028150004840600385950000c0c2c000c0005400000300c1682c0b81e004800701c0e099903452a40613855564216840c440940c1c44680c000300d0f5007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 218537679 1250 218536429 218536457
    0x1b0613150e0c041a0604270510170f06070519020a080909190c03020304380705040f03050c01030b06030108070510030219020a0210033e04032f01 64
    0x3a01c80c000d07584d112511403241020480002c1c001e94020342002d0751450440c1007016000503540e14a050008811a09200381c1c40c02d00c1c80c90641c2442c0e8031400080e290030520050b4803d5050000000c440800401c1d50300c5480d107240090101e9000d9405411081c00034285500c5c158408a045a903d9078090741140c5030a12060030000721140150a514282481e46680204520544502c070703004003d944000da02c0b89002c2c1031407800690001c409125000b5200c80e0007460344665500c003400302d0b80c104003200058503202000c4466000700d801c851030030841020007109016000495091400003642c06100c0c80c41d050041c4101da01084c0301e00350140d030000038284054500300001b0321216649140042c10118400455500048000c1d91900542c001803801410340c107001e010308500180b1820107010b4107594030080e801d2049600f40c0c4003480642c4a020110b9102000d11007200010004c13001d41d01d450300c03070400040000c968960341a04480200c094140032000d00724806c2c403000140c4540c0041c001c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 218538929 1250 218537679 218537681
    0x17011509090b06040f0e010503010506011d04200408030301090e190305030406090206071101030c02030a120e030412140610030327050a0602010212061f051b0613150e0c04 75
    0xb000c0000d521000601c00481e0010781d013aa20710040c90003d8801c8255450a030500d0f003140c4000c0c1c01c1904003d014036245072a409900d0707070341c4c0c6041d4064be40051000c211000030002a8984002100d0207a40002d0000c0c41c0040080518180c0b444004104011800302541d50358070301c0d141d2601d40b0090348000104c2c0200703015401071540140a40c80c0440c1c100c1641d0f0001c0d000d50302c8150103ca00d40d621120310308495034903208080c0c8a0009d40000c51800f02c00e03c601038008100f1030800d14869407140c011109809061007034400815200e01d81e040f50b0101858400801b115203880c9203410302c11100041c035150300c003d40c5102143c4d090740702d52a2110055a58046084002104820f12248044001031035103400703528400405041d070005844000400e40002c80c2c0501400321b501c91840009081609400d40d000300d0080304013820000d644203d400c1000750040700c5600c1c446920702802e0304025590144402400085200d900440c0c0b80d004a64071800407544000e508901e01d41c400070101e8400e00342 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218540179 1250 218538929 218538941
    0x10e13080d060911270f0d15050a05091c120f181203150503060c0309160609170d0801090209010903050601030f03091a070b130f031701150909 63
    0x244880810074a4a8080c0d071002d5031856051034113102000104070110501e001d0710960801c1c1520007207118100403200040c551079064030201d10075810140c22900b0020403840050320710035001c105001c240b50241d544001001c0888038040c06020b4514500307001c041e0b5414401d20982641c8a40180114516010000386184401c8512850f51007035000d6420910005c1d0040407445041c10648501035418011706456072a040040c044030500c1c000e0017255008106564001c403207240c3c1d90707165030300c0101076480c04211010300e28281d1240f03030740400e00320f0344102c2c440c040d00c241080713801d904010032042c1036032100e001c2c0c80075002600c00c90040c00342c658250000c110700381c0145003000c104c9803643c9595040032001e03070040300c041880128181c10503400030b50200051001c00042a8484800303094001103100f43c1c030b00106075801400020b03010701a94101600666084662006200404e1802600030f00c0d040c03201d101c209a800d80005a6246204e0b041c3c0e004502c1e66a6000d44945030241e5103018284c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218541429 1250 218540179 218540197
    0x1107060b06040612020d11160507050d11060702061c0203010509011202010807081b2d0a0807050702132c0f0c130204030812011502010b060307080a09060e0a0b010e1308 74
    0x24441c000420520f142d003019000708030000801e121095907a01c1d1451070010f02d07510a5016510721007330303403002c80c0c03181c10040740410003920200e503118410320000f08a0710540f4000040d15010340140e6407403156540c06035050712400d0725441c04903600c0b000d90030001c201000e4000d00180d19240010750843c03042c110306402c580707080c21100020f9011064031b182d0740c0140954408060080d0707a58800d0007404000c81d60340300c0003407071030600d0b1144201c8000d2188034002d040d0f5061010000d030400441d00ea1810f080081c0b0780300f0004001100694418015400144d040c6810f1152011002a800c07a8049001c0b201c46100300c0c006d240104c1541c080c08510f08a082829480607030902000012904590040070503484484203102e142d030610a200f0001740c1c010700440708582c9801e000c4805500c41340100d030303040300c81ca08224480e0750740c0d6020036000d42200f581c001c00f00c60520010510802c0e00190711703040184a242c002c0d0f40341c3c1c0ca40401914001c8215000030b1000d07c040c2911010481e8500201981c032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218542679 1250 218541429 218541431
    0x305060607020402070201090305030319060b0304120809120d0e0624040b040e070305060708010807060905010e03011d030a140705150402031005070e120d0903030318061107060b06040612020d 84
    0xc0c0d925150181133400807111030f030101a503142040d10510a41c41144007034007444500600f907042c50f4691050414000380c038001404031842c08996a0320b400c01441d44281800580d03039036900303440d105440185c440c41710816014800c90021604205050f0240d80c0402d8001e000180402600410007021f000514401e5400a944891490520400703200100245014038010601401c12020040006105a1180c120350b04640014050a036000701c950302111403d01e0070342c1c1003124641c00030b070044c42ca0403402405800041c04850440f035022015084031b1900d521070f201d5009030300203015218407851100074141e0b003040c2c0410810311680405d05410900140c02c946a400d602122001107860030b48150703020409981e1000b0a40c6404d001e6101c80a8003003001d0800010108405002003100b03000040c01e044d100c014940c0071040081e95140840e4100300c0c00d11014040103011141544660070542e081800c05d4043c0d00d090170210100c070304540f041c0c0d44403da502e2840315210001d421890400f0882 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218543929 1250 218542679 218542697
    0x30a150b19050a030917040302030705010503090c150c011401180207020306040f0c15021c0c020904140102190914060306130203060f130c02060f132901030309150305060607020402070201 82
    0x41005107800c6c054101e61b030154070750b9a40c2180109450880154011810000100300300006041e010400e0b01c0c0d80b52099030303001038041c1c2d2003201c50418003901500b00400d42ca0f2480c0c000b2036410742c1d030070103049500d0039544c2c4583c42207032409142070f44034000010750144d100c10301050010314500001c7c0b1185d809002c0080311541c82c0c0c140003107400d03000007141c40180d0080c0e04580c240d5504040d500c400d003000b42005654080658082418003500600c00380c12030419840f01d601100d400e4048980304101e00d4a50000c1b04450a805081c0c440240a0010f200c0d44c802840420340c00d0400459019050041203080c441060500c020007035070000385956040a0550341e100000c0e15038017015003903420b42c10800f00740382c0d402540091070488018a010441018041406418865800c0c0c00c1159034011482c2426080b61305100f03a100c4041c124001c1c1500d1124000005059103d62030105580e00200c00c0248050440340441c107441c0240d502d60b61090003041207000510b4207500a0616907c1030400e8645 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218545179 1250 218543929 218543933
    0x506011d210307080a0203030108161203030c0309150915060609170f0d080406050a05070f0f0203040510091a04082a0901030318050612060402070314030a150b19050a0309 75
    0x1303500720020002c0541d00220041c001404144501d036400e000034662248510f180c0014003651b4010998050141990359030801c0445110345c00c0158565000143d002000440da002000284061541602c3c1000c1c0001d030015414094060a030031110281e90310b0304100c1c02e21034401c3e1862103001690025100e40b40c0c1155404d4008d01486401242c10b8071002d4844c501400d00105460b0002c0c110500d5500e485d00700030132580c1083d030000c3e034610585046051074408540691071840f841d00116806500098080e00300d541c4120280143d540c1c40c001c9500b0320315103070b42d1a850381c021030040048942110385144040c11640503000034050000e84d01607800b4902c0e401040c08290207030000c2d80020500c500d03007000f0700009000d50b00242402c0e0b40031444c040c1008810300c45e41c203002d00346910640d000111a81458854a1111501241034603500d55908140114000400043c44e09544c250400040090701150103c180c0b0900d42594908a40c2c0d285040401c840f1503004554031424180e03503000ca080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218546429 1250 218545179 218545193
    0xd0b061c05070f060309120e0103181202011413080a090b160201020d050403110f030f03040b0a0305160f140c0a03120501050628050403150506011d210307 68
    0x100e000700064074010741805042d201504040c2c2058090604210010000810003e078514900500d480c0c6444c1404400700100c2c050030a1815001130300344e0f09003a54007404002c3e07515100099141c1c0082041603001055414205402c54119450628418007039012594040040c0800340c10b0307103030410480381c83d071001112a8210310480707420a400d00440c2c10071940c0402040801f102076080050a0910310781d10015401030000700e0a010740d0050301d010896803010056240f5200d4180103507901c1c0c03900d540c0b035a01650404094a8001f900700008140c00040d24180026101d24135075902c00480400c1d00306440714001106514007031178040103039118542080c4076400e601c03440717903079920303100c126246622054841c1030b0001403107800100855445031081c4290031074004803101440c0843d80c2c10f040161400c0c01954409406075180100d050b52294032030340040e1103210241c90700030703010a0b4949148042d040c1d410055800900080e11071501890403915104c28400900849203841c0c0c040e03070b41308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218547679 1250 218546429 218546479
    0x110604241406010f1409130f0204080d0e040c0806010e0a030611040905010b1321080a08090114010302100c050124080f010506060a03020d33140d0b06 66
    0x5503200102206008480da404001d91501c2013561410240c400f2a95510402c1c6203c4c80400034842c4607038000040080610350465903170110409402c644865942d6851612804400c444100152030701c3e00446031840d00c0d01c1100d010004951700c404095903503400550b0100b0402e207615500c00841800000040e109000b91180490079440fa00d454900e401c8001c8140c2d40d060b00441039260040c8203654001c20303040b001004031582e0036013214682005c1503032803048500101d405802001c0020b44466060b400c03a50071030241400a008004900103035218404503071081c040254808425200e40018901c03450307010720800d01600000500b00188000200210300a040c12100b014403c0b0080112003000c0c001e509600900030024002840e1640000b08a80708140351042415030100d89580000099403104031a0703045d0010740014006e00c054000e03220000d241d5400e06180394140c1c04101e558948000724264040078162202d80302d140d41e1b42148c48200280616044403141504151100050101c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218548929 1250 218547679 218547701
    0x50c0d0603060e160e040b0c13080a020a0b0702030709050a2705060601020f030a0c11030f0f010c0903020904120e0613060212030c12070e030f030310050111060424 72
    0x154103c40703055950515000550320007040036611810041c0c00002c210442e032140d48281c40700201d0303807151003959841c00740071140015403440311f0010071081c000190420219008460842000340c0c2c070840c084c6184038404e0000d400d600f00c2e00d01003018200c05d800c0503030030034550ba5022400c1c0411300010010141c1e110f4032010b04903040018081489828000305401060a1015143d0106503201c0b041d80da201d2234041408100c5001d000d181403001d40d8040d554803a10040c20380b0340c000f002150807070b520b003a0528528195482c01011740c02c5140506000400c507076002e0130102c0c1390b940c2c40c0c8901d1041600b022003e800d21041d5030f40500c507591010020303c40c0304020070317800300903604003280289840070307502c0c002202900800600c0100001c0b0000e549043e101c1d011031200342c3d0342d0218211540c1308100c0d007458140c0700701c0b0315690a2070720110203140300700302822064030038942d80d41c01181c401010b08215103003034100340046000b191411040300300306000e0044810359400103ca00c042180c184001d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218550179 1250 218548929 218548931
    0x2010902090105090c0f0d0b0d120f030e07050111100c0c0606360e030c0d030b0f01390606050102010b03010912110c0613060f0215060103050c0d060306 67
    0x5a902189025281039014000070740d103e000030b1501100300e020601c2648000c4540c8507000c1200c0140b090580c00848c0540d1002d003008160000302d00d014080314650210f40808141840360132071a1038401d01c2400102d40e80c04c0000c2042500d00001900c0d101c02c1c60103101e0703141c0601c01505007003200b51f000b414132804590340c0d08024103e582c03d01c4d008407501c0ba04030900d401030f0206903004e6401003a03104021740340c3c020362000719000422007180050410710030081060002040e1088031803008542c0800c500e805440500c110719940c0c003003182500f2140306546c08108070040e00f440f4036400110490410b03074140001080c000042c5081106081030800881e082500c1301010b02c81941e081c06804a0702c0010f0740280000c0045681d40ca2070410303584a207e081007150341441c0548001040300140d90038010300030350343c0c4d450074600c6503012030030302c0c062000480c0c01e110314a0156031001400e031055040380000c0c90000d4075441c004401901000c2c1400c1da90190178404c09420143d28496040118030440d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218551429 1250 218550179 218550191
    0x151c0c0e070908010506090402040b04020c06070503060103151505030702071208040302010e100c060f020f1c05070f080106050901030605060c07030605071719020c030d090b011a09010c02030708010c0201 89
    0x20700144102019004030f1056410f040901c5403544800382041d800c03d50440b80400c0c80e1090002082c001d0150052041d407500ca101e0a000c0040d4119006501401082e601803140c154070780c44e004104001c6101c1c10400e4503007a52513481443c41a0701568200c0340e03901c140c0e0710035591484a8134a2415517441035540106c009010421907070000003103181c0300ca050302c02002000342c615015024101c2400050112511799600028040d103a5040324003100c901c102141c1ca40c92086e20a54803041300515800c5007500c0c1402089109000e410711502c02403165541c048241e00b411f104071030a400141d4154103042d02c403000401d560351400003410502c900b074001880080d143d42420030594601820040601402c0002850ba0b0b0002a10f56903105012069150075171403038417481c038000d12900d1491b00150001207112845d0030250b0300011140c84c0160342102107a41c85558625040c0034410703804072004ac04110b180e00c02c0d4016041680400d000506032100581d0340c0b0507903420740c0d40514400300140d40d105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218552679 1250 218551429 218551441
    0x905060a0b04180b19080d0807020a12110a0609021305010302061b0c09010803180a0f17190507080d1803030c020f062b09030203090607080d060e06090a05151c0c0e 72
    0x1c01d681d1240b230201600d04241700d0183d2504980000500b40080707007400d181110b40a881100146090081200c00090450803c000201407460b0b04a04c203800b40074040030b04214602466060740e0f0014805031400c041c0781c0075001000c0c01c0d0418041c0c14000c0001ca80c0c00d5a50703061601d4001e250210186a54103076800303103000185092110184184035003002840135020040302503064031502c150f0b10310811040d014680c500310560f00c0c0e01d00069807590000f0100308011039801d08503442401120a02c9005090613a00c2a08332004000c416100850030400b1900c6800380c045450b0010341906084200400810b140740c0c0100c1000351000701c141d0904407040b0440c0d0303000c02c1400702c0a00400040480d03981c0252240300d1704906034860300b4041211000d01c03030107408403803086128402c00c0000c540d8450042041030800c03038040b446140b00d4400280019041d0081510036030103100c0e10405103e02c0402c00400d04541d0030248009240468a400003401c40c000a0b80a03115a01040d66240340103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218553929 1250 218552679 218552683
    0x9031803020105030f0a061d04050d0207080601260303090304080f030918070c050f010b0f1c080c0712032f07030305030711150609102405070204050708010905060a0b04180b1908 78
    0x82f86c65404551280d88108008040821028151402c000707040d00140c503040d9100d100e0101c0744120800300c0c00b0000510020003c004014000c403008142985c0c5425401d82c103031030700c034099003806036003140d414850400d0310388800d50519440b40e031034108000c51070081d86030785241400201c3c0d40c0300c8580d50743c4800c106614114010058520044842d1b210007404074501d000001c4071742030024044000490b56202403141031003008068050341c2c1903100240c0b82030030010001c03d80080305101e4904030004403981c010060803420440000a00100040c40c0b5650b0206c4142d030005100c40208445e480705140ca01c01c0074042c0e0408642080410f40c001c1c01c18000700700d100301d0080c2c400c0040c0c140c03c0400b045150b441325208403040400c50a0403034041c90000d015202807117113050007503015181104100001390054223039411b80341012401c0101d40e44203014420311002074003451010320000c1c0303c10000359215401112500818031004110742290700c010440640032006c2042c0e6100c0e4520062000c0310017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218555179 1250 218553929 218553943
    0x9020d0b030f030c1506010c08070609150501030831080a0218040309060309030e09040b071418150405040e0304140301020a0806280909031803020105030f0a061d0405 73
    0x7245010f14503200410140039a10103000383c1d8240b840480c000012416070042000700807550308030102035a030700b00c507183c820001c2240500c202e40141001504100526480c450b1505880d030040e55507203040013000403505801c90240420485070781e403900d248030310001402c0440c010903600c0c005011748084e40c0704003c0088002c00c0148a540c2d030400401c0046a40002900215050350500007100f040c0c5040848000b08078003042da40024410091008014000c907005124201301e03520361041c802c0f880d6900310584141c0c07440000c1c002c0603034942c01d13207807902c16100c01440b00700d200c44903c2c090b074a074041801c0c1c40c42180c1c48840364102148c100281400c0703045040001c0740444c021450101108000b03070002ca00500750b58060301f010b0402507441c502529105140492421406070321540e208003403400340014130f10450002e07021a0b01d0014083d0744805420079240e0503150581140d03030344101c811000b10001d08000900e621464009031000002c003020803881c46001580080345400c0c1015460b00007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218556429 1250 218555179 218555203
    0x1d030708030c0304080d020a050a021c2003090409060501051306211505040b0610110c1012060303020601240206240a1403120c0c01030902060409020d0b03 68
    0x100016400910380d482225441490300c694540c80e07486509040e40280940078041300130074400100c1060ba560018080d12084046030300320380c041d90390600803d21a801c1e041c020404a249040c00d882c07050b130701c20100044000e0080c11603050020450016017070700c0480c4d0701500d00b01d5132900140040c0c24101c4204020780b403043d5091140910f0310402d40041c168044250511312810b031803660402510301b40d0201c011050304000d211074140b40c02c0940e000102920510721464060154800c8280148001c000502d03200014014521061081c0b22215500500c840c00700b207103580004030700311414428100554040e5008040c20741c1040c80c900d034405495904d1502c2091040740ca1081194002501548015805021585640550784030312410804981081e0b118598110204200400c0c00b14450003a000720215400c9140300c80340c00901d407154500251503500700340500119540282c01000405101410031031416589042220881c2c02040103840c61507151600381c0b60701c6c03504100b9068072403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218557679 1250 218556429 218556433
    0x90303050612150c070209042d0b01090903110601060e010f0504150c1103100f1812080603070f090b0a050306090d08060a08070605190804020a030b090c03030d1d 71
    0x100d8101e05540e0310800114441e0f0740c00800c50015030303043c192800b680c802d190701401d2092281020300d80842c4804440201d01c101d915039101480613511000601011780b600108440c001d40d003482c0d02c0e40050201c180c0149c042c0503040048a0404500300000c500070020741d61051142caa95600050195008284204c2003008c280818041c500d0042e21001d22030300302c0c0c20442e011540510303009003910700d02d06000354540107240305c0d40302503161078014418201d543c080800140c580070043d2142150f440e000508012801040201141e0240c440d05800c990000c00701e94480d40e44008102c0e0810f00c03900010300d081d84902140342d003402d0800410001d040c0450151007103240030b40c032161b981d5520003078103020003000030041041074541820400103400c0c1041659440b40d03d840340640141d1101c00052a6400b1111039a40203030b00c81c0040030b01481d0700400e4a43e0962441d1100030b02508098480d2509008030000c141403550100000c0c01c58004d04440881d00b50644105204141c0c41c0300c0d40c0075030076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218558929 1250 218557679 218557699
    0x14120306060f0901210b04140c03040f030c020406170d0201091e021932100302031509042402040e070309080f03010b1b0307050618011e0903030506 65
    0x981e81e08002d039038811030a20780d542d4450b40e1450048508600c4030740030982c070300c1d000b0390307540400e209603008042076510a44090200f510b2140040d4078481046a03000700003402400441c0005900d441d0b41e550303450080ca4019400c0129030005000c94040e40e0044440f892616005401004180a44070044010b40002c00809007540c4803c81030240b0000c444004030007084e001c4045540703514410181b1241e03410b40300b441c2d984446c0020a10403402d00355140759500021a0440110b030440d45c0c41342c0d6a8080c003800350081005070107038043c0d00060154080e0b0007842202c00540e4451010051007103004514a43c069040c1d00081d401d1000c00c240101480d60040105000c2c02010000054110071140b070002544425420040304030f000d000c2c1150134110b0000700004101d0116000703000c0e00f4000b880803040d07081c200118141d8034031402d1002405c6400403800500e040d145010b590509185001c0040b512400f008440880da01d403504600d604a030342d0700c4041c000c0c140d040c803075554004802d540340d17528 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218560179 1250 218558929 218558941
    0x90506090a0501080c0c030c0709110a09030303181b0924030f08070519030e0603040f0f05031b060f010503160308030714030c0a0210060b040b0c0a050a141203 70
    0x155101d03004140c144080e680214150601000403035080d00300290540783c90344041010705450300080e00c03070100120306240b40c02c0301009000c411034250108a445984281d8910790b000e6018007c030501c040b5080b180e081e0700034003280d01214988415050034810462403404d01d0441c804480c40c6207001c41c4400108481e290380000765640010a0b00d411441c058520940c40c501a14a481008001081341c0242c152261112640d0110761b036034944642c0f83d003403c02c40c1c040140f01440c041111301034440011900203001044080e000500c81d01e024406403441c2c00b004014144009600081c48070244c0d11242c200000c6c00c0e074518805024101c118064402c1d800075640a642e080164080078109031000000b0610300e901600382c500710944a06d20042d03c0f40740101c000c07540f5030041580c150150244089400841100c1d00c1031f081552ba03105071240c00c05042100f0001160400c03001492184940070300c19000c11410060808224486d104c002959000202d49504002404071010005007041c801e01507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218561429 1250 218560179 218560189
    0x5060601121e020d150f060e09040c06120b100c0c08060c07020108091005010308040501080901050f180c0303070c15030b010509060a020c0d030807030b010203031e07120608070609050609 82
    0xb2205840c20000341c2c50710000e031840780040c81400c01c04000402181c00c000f40c100d60854000084410b10340340c044500300351109000c0000801c0300d000b040c90160708828803904e0f0054110b80d50705050991700060783c40b001c8012404944102c0000c07070104010b54038103010000844810009801400f0140c000b03810320a0a0740301900880c00c009050208900018281e40c0081100401d803000c118014041940e480c10a0542075205004841c0003409200c0022503624050003040d000c0d05020740300252643d1000000b00d1b0801d002e20041003a8051521044550380e81040a010154050000701c4106823914148214524070103010009060501810201c40da80141c103403000e07c00c00351801617846140103000c0342030910800f840c0d030b44203d100102009040d44100094818012034904110103000303c0300580c0e0380e020071035881100c003e103a64051038248035801c40399001221810035010440c645004481510b15175086503240380c2c005d03002040b00075403203a60706004200540300e90345491101d001150f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218562679 1250 218561429 218561471
    0x180a020306010b0304020d05010204090b09070c0b01170a0c0906082118040b090a050402030106050414040f06020405060301060c0c0b1c090507080d050d0608060106021e0c0d0506060112 81
    0x403c0480400000c007992666168a450f0342e038084000c640d207644036072208000340191609240a03020750350001745018000d08400040e960080041003d580c60114130303a003034001624640d0070134080c20300002c1c001019200100007526a00c1404100b0f281080c580d13a15001c442c000340076051031121f81c450112487e800460b900348941035000594002ca41d0049405050001120381e04182d030784c010442046902c0d440140140e00c201d00a102c15a80c8808200650303986c1034404603115006400300c2c000032814810011024460392015040950310300c002002c1d504240d0248000c980412104010450321655400103800982d00c1070b420050b0195400d40b542407000401d008030ba50300d11a08045c4001041aa00203095280460300c041140e908000c005401545212080e54100784000c0303980d01c1c021075943e040c1e8020b40c0c000d202c1e50309285416100d000c40041480c205001d03424480e5440d03291108444036050165005000c0c0d0305041c0c0004100803004816985c00c2498252a12540c0c00c95203000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218563929 1250 218562679 218562689
    0x41403130b0705011805010b0405010f140d14070b0a090b040b07020607030903060617010605180f040c03050a0609030806010c021e0f04020c060403020616021e1c0305180a02030601 79
    0x10340350082d41c0303400b40c018542d00740001c624041c0c80c0d42c500c003081030541060b42c4086040c1c83c02c0c45640d0303984552000c1a8881c0c012518020200307112a030140c1008440054070070b00924124042100000c5050b0a207061900aa203000100050030023840d07409c20300e02401401351800d9149010324004503014640500140288141800121071003414070075419003003d540c11100403c2460b40e039903141e130500d072000c0710f05180e5075080a030001080d190a00e00e09044c07280d210b0f42c0c0030f401d40d40c0c0603000c079001400510898000c8031081c80403010450410485540c14420031001038826003504000e014140000c100700d0412292005a50058860755112900c046143d103070f509900803403800090048550540b821b030000c2c030204a000c1540b10002e0798500650094003074403440c2d25175104120811407110084005644a90b140c6403000c01c004103414504c030750401c10b4402c000713505d90380051186605800c1c24000f9449070180818000c1c42e030114110880c04400a0100300306a50110380c58400500c55 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218565179 1250 218563929 218563949
    0x60403050a030e060115090504060506090103092102032109070e0a2d0c080411090a0f1e0c0e0a15031b0f021b03061302060c010f0504140313 62
    0x121031550b000380c01418640711441c0c00d40b00c1641e182d0304c18803c100034101c1c4000009807005000695070800748104019110041e0a4a10b0004044c0c0150302400401108407030101d141c141c4541c50110100380c5c2401002c4a43c00f8565a15800c01d4000503400c0c0c0d071000008154009003840038140c2c00040b03140850f02d401c80c403140103580300d0b1044030051080700204544568910b0b000c55220500804680da40420702e4410000e09940c01000c0312941004c540051014540161005051030140c6800b54812516640400cbc000c10080821090b0b4581c5140c1d40942030100301d00740c00d1035800380a8030b034602081d842c011f4060703100c400005110f010f0340e00ca480501c407100305164008074800d4002e224440e2442e1444000c1e101c681c1002401d0800d041c0035040107000c3c5014110303643c14103441c00d8200f40c00050060a0545400e0503885043c3e80324a802c0b41d00c0041000703d60300c880e03000e0040e01c490110300c1200044500d020f0411803003491301c00b06486c00d940c00810000d444080b03440203d200342c0b250702c7c40b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218566429 1250 218565179 218565187
    0x203010614271306031407140a0b0f04030c060c020f0114070f02030a0503040b1309110702090a0b09090307030e030105040206032e030b070f110606060a050717071a0906040305 77
    0x302080d9803c919491922100303042034000320520603010380c81c200c00703500a8102e501c410355400e0803410405800030056449040508200000107401700546819400d004506203801e61765911125181007035030160000c922000c00b11740543c40e120814001d140740a00300207810400d001c0c0c4882c118442d1700c4008014843e420b1408040d91810010b24a180d0741c841e040300c3c3d032161200c2c90b00310140c01020500d15085081440490b00c40e88901542100590a003101f0307040030030640c03c01045603070040a00451540c0c559803544c855035800e0f010380c0034080030809107541c0c4100c0d007002000318045580c1d841c000c2e81860309000040e01e071041101e9020040742580520b14120020321500c10801007400c00d106102404080144809401c2550003a03001e515242040114110140c0c0c800c42c4042c104003190b08260300103450350820b880105207000c503520b0084c0ca0400d4a56603181c4003040c41800e5040d40c0d0340400c014040180c000240300450f928203d0f07400c0b07980351a03101655a0742d0000e100804104000c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218567679 1250 218566429 218566507
    0x260a111603050c10091505180a12020705090f06040e030706020703031a0f0a14030307170c06012102010c0201050c01050403020a110607080306240d0203010614 70
    0x540301419810042440d00c034820741001007940d0099000c50045014451100440d803509101c1d200c40107500191184010900c0e48085c40105002403544c0c442007040f13119442e10841c1406900d10091054001c0d01884100c201c00a08d000b40d650042c0340035000441c140a821803c295103598411002c440110f055850403822031306600400c2c00003442c85002080319010182c15410a1990700d020308810196a0500c038204041c1c8800745840b01d81242d184401482a0b4060b0b05401c0010600070301101d1401c90542d45c0c4942c0c071880d4003d59110404046010b503a500070900c5920b005004000fa00d0640240b8118000d00d400d0002d0002414002505401c1003164014006c1c0c0d682450984020410742c540350030065240c088903c0111040e200113504d04642d07181640540f080b00d40c2000d0514215940c000034805c002582d00c1e54036901ca11500403800e18651032000a04204038001c42c00358995242242c054810104004002c0c626101480401030304140301100810a5030140004c4000704108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218568929 1250 218567679 218567711
    0xa0203070209070525110f030c0a1e090603030518041409010c080603011803030b031219030501082107060906020a02070614041d0709080607030507260a 67
    0x14030300290071601d00020890348a07004006802c140418031015289403051182c1c03c00d02c2c1989440040007030341c111032800e22605003072883c0744042d08080c0445440b05844000610204065400110001d1046403c203042520301d407400c00040140c40414040c55080d50b50191550040325025080d4400c41d0208211a80d1543c000c0c0031003410120519005060080f1494007138185500d0f510046000340020030390700c0c00c052140d076100002091840c50040b5060350704901a024180201d0703032510513411806444804403008002c4600e0001900c12848000480038041d600164404c10082c0c1180d40b401c512059040c64440b600c00358911043c0c0c1d40e2560789400001412407443c0502514400705120100c580c000445d4070540310a80c40c6c80c2440c002c2c02040002510a5000b8840000703100048414041205165582c01c9007550811455958032400d82c02c0c54490f00310b07205000261507209000b4070a4103d6640010100b551202889000808031038500c2c04da0054030b0004990360b00c46865201c2028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218570179 1250 218568929 218568937
    0x12030c1902010f0c0c0f090c0f021b0f01021f090201081806040b060303160809130207020d02040b03190b16030c0918110309151f1203050403050105070909060603110d020a0203 77
    0x1030902c00d089065107c010220041804400b1200416810685415118000582c1800c100c1050b00040400c01003c82486040c401c0c0c0c05c0c1a40c13351080905c84209240050002c1e40c808a03030000000d403403141800014491a405008008082064094140c08110208145900641081503405191140008039146100b511305243c100b18600050320208100c02005190081c0200d545100c0640643c403440100d1060490007540300803042100c00c01418940c21500340c0e0703c4020240c0d941c21100a280004c20740302c01c04100c5651600d413013009541060000c5c0e81e45080c44510342048040a0420043d0a461041c003c600c02120001c0d50080c010649030040412a410342c418203860b420448036055803104c3c0c00a4001c2000007240014a41070110062800202c0c2d00710061035006140030248213800b2100c00c0240c04100b4200004800300300e09014080c00340c001e580d40c12090500d4504c0e02c50880b00190085001c0600341441c0503000385140b81910000ca101010060761080a450141e01d1446 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218571429 1250 218570179 218570189
    0xf0121030905100923011d0103061211090a020906070b0903040b0c010e0705030c01090902071a040f05010f0203100605030c0415050d11120103140a0212030c1902010f0c0c 75
    0x82d103011080c1403544c040102000c40d1040c50010ba2600c001c4410400302c0820800c5c0d9500081a40c2e40703034052807828940b036100c0b030310040c1000070702e45803900c4200c4465606440141d84001f42441907441904050340401d0303121060200840c14201d03680c000440e070f4421050007500c000350b60f5020903413085007070080318020301c403468a0380e5075600301800c0c10380a4a6a101103400c00d028120b0b00141c20309012546c292a142d0595401542c1e0b403c103803503c0700070b402108007600c0e00c40c44900c0000c1c1402e858600d0b50b0056015400742040701c2d01501c4e1080c00d45a03100c00880c83c590050051144030031802c18000181c603590f041c0103480b50346008070341501e8056640729100d140144402051107070340140007005c0740e2840701d0041c003050520a0381b9240510580c810400180d80c6140100049003104510f1407240c1c90b00da06075031126065400040d603506c030a03c01000d094000042401c0c00b0a030410090713080e10303030b40d0550180c1501c440d000a0000c60a03820038000340841e903080042081116503071030020304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218572679 1250 218571429 218571439
    0x70c090213080705030f031210030c060e031902030c06070203010b03030301091d07180b010c050607080106171005102a0b070503060904030e120105130b0f0121030905 73
    0x82188140980040785102e451000c3c05074400104440c100411134040801d101c6d0021898004e07403413184503080d03c000b000000c409501290101c009044040b002009240e142d07100c10588803034000709828000d90107910020118520401c00060720081800240d9103800c0320415226030203400403d024040300041d59a00d4000080042404503495110b00907035100c00000c3c002240418075540d070f407481d990080c00d40303510b020104541c002c02135800c00b40b101007040c501148480010fa507020315080d0103a9200300801c4502c3d0050221641c0b203036a0924800400c0d5000078141040c00440710700708044e010342c40c09811003070600000350340102c1c52003a00c500280c0520110100c1e8414901082c050740c40c00319541035085010a403100c1c0b2600959000b00740040c907140032500c0c0d540c0c05527910003000384110b4108072242d480c820450000e02c2914410442c3c0032a41218083d5840c2c0300303620110080811024075074100052009035506913610425401203070a542244249003000d1703450751a00d901c216400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218573929 1250 218572679 218572687
    0x1509020306060d05010308120714030402040b0604090207060e01050a09030c110d0b040308160f020c0907031b0e0a050118030803060303070b0915010603110715180f05060601091a070c0902 82
    0x15024010011443e5105004008d074850743c1c42158081000e840c001c1010704107002180140c03a00e03a0105143c840300901007442c3c0ba40d84d5100c88240e8001581c1901d02503500c4514500c030351028010f4940c003c8040c6401c200c0a01c040e607018002e0044194081c110854074401d4050300c0d1101c8100f800c24030340180c7c1a00340c52500b0301d0020004134040304c01184281c01030030008800350144115142c800c04c41d8000c0c00b8080034800600861120080c800310403d074842a060010702d4034106100313582c00303843e41d814241e000404180b002d100800c0c2d2085040002903403018001210b110807810941c2d5111514039520b4980d58000f82c51070003109030207004079040b003040c850200400030305803401c460607c04121b020385e6100d905a0845001b5034100381a480100114000900e8000085070b0150811400007840301480000d0f082a914201003100c4ea0b4401402e1001408801c00085903c0142480c03d1107619040c42500201c000d50000046046100410080108000a00c00714090a00f00d0340441d11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218575179 1250 218573929 218573933
    0x5090a0b041502210304060c180807050f060f0f0c030c010f0b090a0507050a0327050604050601150e010507060902041a04230c131a0703080a1509020306060d050103 72
    0x40718a106a4110240c465000b25107045800b100c13050403102943e50505003540c1d00c50702e81102030315030b0000040402c42c0028038080e281c400c2640c210058a2644020241203042100f80a41d5044802c04180b2403070060000d09050740c250001c403001060300200d042c3d01c541c0324160a40c65400b8990019aa650078003c40041240070741d0300010f00c0402c111043c0d501794442ca20100c2c211041a0359410014100704040b5014500a40010b020a0800e0352080c0c0c400b10b01000300500500c044078219455041030050000f4848100049405480b80c003c400e819403024100c0a03002000d02d604490511001003a00790905c21113601c00088103401a1085c070100d14402c1e54507514404001c07000d846286081c0fa0071a58640c01501e80241d0403018081c40321a0311040400b403116000128040404009080c01041403804101400d06810323449400d940c4620030351070082c051040c000c040ca10068940505101421070140a05045904100c40160381343c8800020420521408807040c041d00d00704800002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218576429 1250 218575179 218575199
    0x3040905060127050f060c19050115060e0d081207080610020f06130507030213090b060d0f12021006060507050d050a080a0b030a0204090b0f180a0305090a0b04 70
    0x84541003d80c1c0c0c80c0541200200501e6024001002c0c1d00c00b90030f50a001408039082550b45c0e011101401404203003000a03180605192401404060030229405580401042008d004150b030301e40d24007001407620f50900e00000c1c80c0041000c84140b140520000740c1003406070038012603481003400314111b40280b41403030b0054090f400507600c44e03024442c0d10318203150091010402070410000c0602030801d5454801828520b8401303403400391460b0080400c0000103940304035003040ca00710b04090200e0004414102500039100082107980515818140d24000135220103000d02110f0388204030100030f02c0b0b6024100d140c40006800f02c40e44c24509039002c15201d800c50040c0c840d01344540200d45501c590740004231104c0c000d10174110042801c4038007081041e001d98104c40d40d188000750031980605400d80000d003c1ea10303015025600703140080107102a442e90101e0207540010740f4000720b1200c00d004140255181e0300301201034104240412000c6440d61040342030001000c030104901e44407501c929440f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218577679 1250 218576429 218576431
    0xf020a080c03070605040f060305041a100306050c040303050307110a02090903040801060803040503070312020109120306030210020106050f01120915060e0709080d0518040509060118020c070501110f03040905 91
    0xa1092140340340001e4640c1c4511704a5041c1d03403204803201503103880e080d8158040c207400f40c4215030902802c00030410801219401d80d114950070404549a60b10b9420682c0c12110003408100303c40c0d50422007800881d401408407a0040251f04d42070202c420b42d64944c60910000c140c0007940040c8100038003881d21000000b80040e28000802040850303924607003503940c0d200300d1107800d4041d0403042041000c11100300426013110b81500000c11040f5040c2e5400005108a04404000c82c1e9500010700c25420621091060300d41180000c10290f400c080025029842c541300d000d041015503041c01c642170701d194000d40d04003503016800d1141c22032140c03c5030740a04014013400307500c084140001075102e48114008022580c00307402424420a841d84110713000d6000212400701455000c401c0b04907500c90b445040e200d502c210000c3c0000354145604a11400510b4401603400c81c010701c00412a0100803d103c0120b031400d00b855a00c031102031800c1406c002103507180030303498000030a00290681c02c9030405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218578929 1250 218577679 218577703
    0x4050111010621030203130f060908030c06010308160804030b040302060f0c1c020c031602150f090409051e0105040b22030807030f090c031b05100c0f020a08 69
    0x80048800c40d0380e0803800c9030000c1c803032800e003811074032070400c042400c0074200311aa42c0a0b10590b45821201420031800500580c0090340203032118904100c1d656011400300302414200d0099031419051443d456540c41042c00003034001c0800090498905004c1c0110b800001c1d0700041d0244c443c2c1c0d59091203070b1300040c11281580940941c80001f90302840021074a44507a06140340c06003444030711400300c07412525081c03401c002e495080044200c4028204017420380c0440469502c2ca41004910602402c200c0c036505040000c0414001401006041f100380c075402d6500f900c0008035100282082c1f8523044912011200724490700a14218030380e8107400261003240264485607154a4010b035007c24030480c24064951003803c1010b02d80080c0c03082c8001c03070f04001c1c01d190101d0980740411906080703c3c0c8100088420180d8001d0800800089008003c445480c0f08207451110b880c06011880e07219134080c01c08100b2520600e02c900300300d034074021040140d03009411010155104c080c081e035100522042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218580179 1250 218578929 218578937
    0xf030803100b0306030a0807110406030803040302010609020a121802282c1b19080112081b1213050906040903270504140f09030a080f04031b08040501 66
    0x218100d080c19040f01c0c040c90001d40140000003a9032105009134101d2002164116403159014500303681c1d0740201400340d03010300c0e15640d5a050515021b0f0031299213070711002c081c0740140130030f2807419082a0a0018495154004101000c480c0602c0c00105000d80303000b0750140d030440304405142c41c603010f807003414205007000d41111a160004414030300c0f00c0414601105085d204a0b0002e00c442c0060070380c100b41454416409042c0c4840200c0580d0441c070384a10040c0c41ca0810103121980c090605030061000d004d00800805c416100d8040341c1c8518229017150113105030051041080810541040040c0c468200b501d4a181031030000c035600051007898403650f0001c0110303c241c50709105404003280d15031592462101900303da041c40c818040d08103a00c401c0301810008150700d450203000c40915203620a0384803460008411100b261003c0c0c107588269205001018000c5d070801c00060b0028840d08110820b03a48510382150580c0141024982150300000020300300706200024000b501c0090300c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218581429 1250 218580179 218580211
    0x4090501180213050d11030d0e031e030a0507260a080717040b060d02060f0d15030302030a050904110a0305090607410301080f060c0304030e040b0303040f030803 71
    0x30003400d03402010320782101c854030280200304d40d1a12400c102c240ea4860403030007045401d0074000900344042001c00c5c0010603020165031075180750512180c054680140c0b5501d5641d5818044a566030007420200c2040c0440001c1d0f41e400d004658400b94059031181c50b201c9510040703140c2400715078002c0080c1e000418880c0d40810306040c001c031a050204004000b203a4120b03521a164240100c2c009003025400030f42000000016031182d5009084090700c000100d942c0340c5c1c2c40200242103070600200c1c00445810210140000380d0b010084694826682c41d24a803501c42040005000706812000428031050000780782501c6505500118400d02c054000c2d69165601e0000035555070915440c0d0038180c403034290040c0318108107003c940d900304042d201d0f6819800060a02141154400e070403804940d0311040860710030391303c1004515480021a9040d5045042541d00a0174545c1c0b0440450702c242e89902d035020643d1010001e0754010946840d100d1645d0340e036824483c41e03d6009590341c60820b14252 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218582679 1250 218581429 218581469
    0x50106050f0a120e030a0302090306090303040b0703020706060512010f0f020405010516050c2106010503031201030b0402031002030a2c0a1b08010204060504090b0906031b03011104090501 82
    0x209450481ca521000e5510300701d01400300325150000560007180096460b070359140035502c20006407000c1c0c000c545005942d0910101014540a8010038200c80e03617008004010001e000d0b00c0c202a0407415900f4090b2700c44441d0700c2d01c0000740446820641c0c110109810356000105c054000d107242425001c0104068910046540c0a074031407802400d001c85c0c8100007031080c1c00d869019680080d80180243d485290f118400034103c45c00c0f0a616000311408605410544402449490f0041c2022030007036240c50004815200c03013150511020300b509901c00001000d43d242031003940c2480333594050866680c549481014018030710b007406401c162a00f04640d003100d00f017120b40780928904040003013107e00010f966104840c14450f1501b001e40695102c00030321a2024005400a0304068881a4840741041d401004071450a480b4511540849040c40115140410854002e0015a5980c20340b003c02d0300100340500303c032403010a4103400c0010001f40800c0c5552000e8180c0b010324110624502d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218583929 1250 218582679 218582687
    0xc12031302100e0105040b0c010b0907030204050102120405091504181b0f0f2601020c01020406120203040b010b030903070803180706081b0a1103070f0b13083c0706050106 75
    0x1400403940400c201b000184103202c10302d0013038004002d03444008079440601c0c03000f0880c095000e5810f0300101c1c0e0081018805580c05204115800520144150400f4a0040011103000e409000c480740041c017a80503c01c181c45a82090b21418500d000031203001e1400c0c034007540c203203032021807191040160756408039080ca5880f110030101c418194100b0800e030f0400308001503181a0038080b035404203c4815050640d2000c0c005031820441c5d070303400161940e00d00000601403260840502011a2041041100086040244a054441403031a007a100e50b01d1440862462041c045c020740700f600c0200402885449200c18414401c0a0006407100c150303442c0000e40b4000f500b0384a010b000c400f8114044407a18403440a0410b2903190703d08420245440030300c3c030713041d9400010b0030388504500c2106d4005200c1404001504124826a9040180c1058545da2418054260100e20032401c0d01e13280364010b041c090340a003800d20303d41d007410300d002e000241080050740310f2030046403014205400080c2c0f942c09 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218585179 1250 218583929 218583947
    0x1501031e050a021002010e060a021c0b01051b0106090f02040f080d08070f02100c03050f0601090b0406080c0f1315030c0e100c060204090204210c0b0c1203130210 71
    0x4400c0c0207003402c10156003007100c000814807400007159039075208100400c400b00f103454000c0700310500041e520402d200c40950803050190b031411526040004d01c00b801d0f44d10008964005080448003218000110110350150990f6840f0143c1c16080444102400c21542e00070801c44000f031216044181daa940d29945030280c4814401c00320301d01d04009060340d030003a1071500240c20300c0d2054890600c101050001102c40310000d050000780d40340100180b0064121029404c04030900300401005d1401024042a1150b8040c09041082c2480071070404190881030f41d03118080600e03c1522141106c0c410600c59806200d408403880c94907a080b0342a9000f440703114215042a911001349030040e41c01c1c800115800e10b08075082018001410011800c44c0c4041c0c0054110301c40056507a0f4900020020340d2032141001d003c140c2801150035000443c1c86043d00200d80343e0762150703511401c2e1207040b1410140620022060550700200704100e61140c00d00384268240300301c5004c409092101c1c2c0407182854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218586429 1250 218585179 218585183
    0xa090606080414010603080f0a020606150d0b010e0d03030c090902030408090105030c070c06021b06040b0a0e0d0f0f020a08031c11160b0117061005040f020c1501031e 73
    0x1121010901283c40300306030701c01401c181030000c2017241c2c0d251360f4860704d54811407924401b0780000c5240540340b0350611019070440e5045845004c3ca21107003c4040c110320a00364006080395403034924510baa40280340000c08200014109041d804503400c0c00707000b41c031200c2450000aa51220040ba48540510a981c0915086200d030350800b0702c16401940c2070307030000d00004030900f0244924400119501d48800c003914155000c0c22050342140307480003a103107a15004c0b92140c10148010f000c00d00d0a1404d0700c0701d802e120300e401e0600300d1090010445060000b000130b02200c2d0090041010701c40080001d45102d44280c07006001c055903800300d02c0c1c40340202402040070403035810803017039405a41d41041342c2030065642018a840d40c40c3c1002001100c5150044510309101001002965031480d004e2248100c000041c2c4024a440500d200b0f11210500400d0300c140d6480d80b160a94440c194140d404281200c000c94030f8040c50390204101c41e0000340b0048070f20b02c04882010b107006200c0d0000c043d03165 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218587679 1250 218586429 218586437
    0x2070e07020a0b060d140714040e1b010e060a0206091b49060e0604020108010b0f0d02030702010e0708070f0909050111070b1501030b0d0318230a090606 67
    0x156030ba6884444070b65018180550099000c00040c000c07031100d40d1002c544d0b81100000303002d6689882d90102d50640200c1065100f14608020000000000b0458034001c201c904003c2002d2042240141da034100c0c1c24039944d4120700081417026a540d000500715005004000440349240307580703050060140c6120f070103e0707040209203850a800010302280c801d8100710302603a14a4851005403020114421030382440781c143d038000030700c10601006101d14840c01815401600083c0380ca034001804c50403040c81600041100042d860440342c9030501661a1350100c1a019550707802c1050b0028040d000c10825034070a40280040080c02840020b40442290001d0903050025031030810840d0050120982c1a5110754071146961000d1040000528441c1e01c00c41c1ea1040c14104048045050034140500301d0500d0b1411100300250f0b984c00c0c911141990341498440d400301202c40c000d0150241641c0500c2c81c0280c3c4040311001400c03003e603e0007928070252440504250344100381c1054950520a5401113 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218588929 1250 218587679 218587693
    0x316080610170601030f021815030906010b03041109040b0103150c0e1002031303062a050d020c190b09010c08010b03041b0e0705030a110c06190608060408070302070e0702 75
    0x10950b491161036105405050000b0440541070170141030743e000803520030f40960008241c21091911000303510725400810034030360451409448a540c1d03002e049c0a07800d10307144044002820442203224200d24901d0190910006080c24030b46084103503401c5c001102d0408010426080c0094203111fa04ca01d10030305c1e9980141380c60654103002410f07200c0284003086000410005400f580048008402944a03110005d0016a0600001d29010130205e0b00da110848051000000c5a0702c078040d81c031860504c80006a507044250151460710581500044120050111000c144030b0700c0a0120b01c5504401c0083c40441d03d0b030350003141e90907402d02030411100e5060020074003142c026481c00081032254602102401d44a4140f004481d0040700c8400000e8000001c0189045082c09142407100d59034892a0400313000c52406074480c00000d00d54189400c5440802189c4040f580184000741b4454003504c0d031908150410384010790114106a0251003201e4002a50410003850184a261540e018002c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218590179 1250 218588929 218588957
    0x1703010603180b0711150903090103050603070e011509080d0207080c01020a0308130204060803030a0608070e060319020303091027050a0306093311032206110316080610 74
    0x207170300d40403030811102d2217031007900c1a0085641d0340d21402190440011a04c07103d104000506a4400400f40d60098002480c10402080d07400ca200d8107445181a0b0904084446907084030f40071103c0c2c0c0003070790034803c0e4020344400f140c0102c2d2440a641d01601500c40c1d100e0550010381c1da070120b281004001400020014080c100d2001240c095130344003c0020803440e6841310a146035400907110f805105689460411030300008000702402048441543c070b14914201c40000d4481c00e5034a4401c44042e01c03980c2110840d68181700320f910f050b0b402030031108884140c450062408984246400e840b044116808656950072070625046800040032100a01e09650b204000707012003030011240103490200b21140f02078200c0500c110755003c0c104881308011105c80850983d01c01035440424640704105000801c0005600380c40c811100199649290382c061a000c001001c000e1030003030f805080842804140106582d100205400a0303441c49016180d40080050700303d5605c41d0032010618150349551 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218591429 1250 218590179 218590187
    0x170c090612090f070305070e09010c081f0803030a06030b060901081c020f01110d140106140702010e060304110a0b0a050706050703090b010803030901150b041707031703010603180b07 80
    0x2d0301180500c10b81d40401c400d104101c1c030700400d507082200c95800c080414052640f071001d1450744803074034078000e00050810b258064a030541c090b00700030701801e071030f9a40d00606c0c031030009640c002d25503942100e503280390a14096005014502040358094100404910f151400d181c00c503060f151882c010300103800e00c240ca65980840400490410350040c10303459008144288603505486890b01082075135819100c00c0301e01140c610070721007214204114010302c580b82d40107605034900011140c5c1280d03642c1d010b0005071002c00c0d40d038103507d81c003440020070401040101d071160100003a003aa00c070200182c44d0312134415180202400710000030410301a01c004940701d5006035800064034140002e0054035074660200c488403d070807481c2c0952000040c411310440900c20400c140e4a80c10201054a00300084c5100c01d1050740329108100e0814054081c09500500c190380086500107007032040c00904000b050001c0c1c2091041d8000319240032400c801d400c003803009080c003003070748032140641d0b5540d014000da0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218592679 1250 218591429 218591431
    0x11403130f050105041109090105040c0303081915031b06080403120b1f0806030a030c1211030406020f0c0919050411100903170a1d0d12170c090612 65
    0x3440c1d0481090888000c20001e100d014013450094003100a01d1220740f0a111229401500c840030707683c50201080080f40100b51030006880e490b190003c142c0d115016410302c0c03100074074514a880351400c65044011b40154202400f1203119002c01198020340e1106294140a54400e1310301003454600000c00292090030b20144101c10017400040c0032040002155081407402025a1044003036014450070a800003203281d8002400c80040865002941e0024513110380b09400070100002c2508158003a0b0013240d0300d280111391041100d881e0780d03807100c0082d900c90690b0310040d203600941c1100c541505140d0006071060200580c0d407031101c02035130303880001050003d2043d910124001032500095031220406000c01c14103640341d1008900303500f4000344507010b40090f0504124200402e040450300716030010208688440381da030b070036a1840013080d041000e0140080c401c03079103a403401c050141c101443c6e100100246e46480100d6a07055142e00003446140c8bc8183e01c12000d00001100003010640790f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218593929 1250 218592679 218592683
    0x51621050118050c010905030303010b09040b0409020312040e070906050417011b12060f0e04020d05010b03030d0501031e020f06070501110301091b030507050315010c020d060b01030b01140313 84
    0x1494040006841e0040c120b008040703549401003c403400d001c1d030f4001e0b20300d0701a110841c00341d0710710b51400c8200314903481074522650107952503401210056940fa44044000c6401400b43c40001c001258243c8072540580240b4400480e61408120181d210300c4003c0103560094460382e20b80307801d100000e044ca0f80309503101c10841d074a1743e40d500b4000303c0501c0100c400c4c00590b00d0303815002c490720070302c2021344809030001c05845850070401c10488504111030b0380c11030707010f4506d2900c4100708d060850140c01c8070003845803d84400100030743c85014540c08141200e01400d500c050f151341c1d203a44d20000744036600000c0d6004920041e640740920340b10004010f0a031140c000015000c82c412049000ea0300241d200c508020795800e00e452032281180e44118a00c485454100280d06d0424006012400081e021400e803c00284504003c1c0c0d024594000e641c81d0014081c3c101c00c046450040b000c0c0149191186c0000c0c10b00040d80701e03d500403403100c1d84500046a001d401c55850902c1c032400d0001040c42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218595179 1250 218593929 218593931
    0x2010219020d12181a0711060409060b031005030c0a0b18090c040504180812150306040b0601090f0f030b0702120f03060901050a03020f0d0318060305040516210501 72
    0x4100040c000503218a0b0072441070301c0340c901a4804000a040c0d130184d0340d00102030900811004040c0c40301d13074402c44002d1540640040703881d082000205e1030700d0085800201400d860002d020030b0f145001000f40d0303c155604400f954800d43c0720028941c90300f0488031200e8000308038040c180440701041010702400074450007100a00070040c4002404007400380c405509035100041c0074069030070a4018210080003d80908110310070a0383d4280c11441001001001c0c80c8610020074405441d00c103200070388003c0181211040e0605081c44104101c06696003404600100d60001708448008031180840c1da248041d504000e140d80c440b0166140014070380c200b14000c54001c48000c0c85c081c0c02518000c121002c0e070645918214082c801d003130314107810051240110000800041e56080c0c2c65400c01c08095400b16001d401c00d00e815180410143c0644400e50309695010401d1980b50703000b04d10441c02401120101c00002c01c3d500400c00130b40c000c05144103da5045a0090103080c04601c1e025482880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218596429 1250 218595179 218595199
    0x3070b0901020c190209160909020a0c2a0f080307020d0204180c03060e031813090b1503060a020a0f08101a091002011119051c1d010203040201021902 66
    0x107650b42c204481d25001413030f83e09022042c403042d4102203072038541c490310b00d41050000352180c400190110700988100003000e0740001c2c01400300e80c410f0714012034595224a00301a400540d0080d449005a542482d0b00c0000c42c02c6030006001d18105858000ca499910241d490401b5035000d0000b00340c4e41d8039040c0c1c0c2054490100324103504401e6401c00b1254000e58080b001e5600314a04003094510055400c0346036130041c016140185140070400f0b14040c07040b6001424905000c000b140a000441006030a800c03401d0100036240300e5014810040c2c000840644400c2d54411120904a018508000e0001f5188000c106038090140b40203a411096202803841401da807180300030071070074100050b823440300004200200035045c840c0400c0003200242c0024000340e40c0c0b100018441c2d001c0c2217140080304160001c020490342c000c804550040d01c894585520110403815503e024040e400300505c2c4603444030030b04128109040c401c0e2802aa07059020340b425265001f018104d4290840e0141d9200c2d040c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218597679 1250 218596429 218596447
    0x105010e280305010b031504030e0d151b12050f1305190602040e090c1302180324010e0405030d09020f060307090305060709081504060908030709030605160203070b090102 75
    0x440080003144900004182c2d01c40060900d400c00c2c1c038085110000e00711850a0200003600040381c2b818860f0113507204282080d00e030401000c080c03594001540075502d050380001d01d1241c8407400407080c0480c1c1d01c0b402050204c0211600c2110710072155070090305581c2c004a40702c1c486c42c12290b100c81e400b070000c945400c01040c0740190b551f0001401103503102d80c0020100f14a0220715650303039205003014042d000131010341001c03603111104402c154031013030b50014114141c080524a070080c080805002c0362401060806054001e10111124070350000f02a000002d070364092144003031086a00402542c10080c550701d403c405420098401c80e400401e201407200310746c446402561240c076050b6148418240395090580c14110302034420020000302e45000d10080000003004c1240d0051302c000c0400d02c1c0c5c3d407410078030020301d51a840100714030400014800d065034000015415a0b0184000304210f03129030f00c14402a07610980c4180c00341c1c10034803007900818440c291050340401e00500141c5840058 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218598929 1250 218597679 218597749
    0x90905071d0103061a060a12061a03040501110a12200c0307020a15050702120a05011409010c0306051e04060305060702010e01050f010e061306030c060e010e01080105010e 75
    0x22080901c4449024004005001950281c503c00c940c0c0e50304004a06480d031170101e0801d00c61491400184515402c03a9404103201c2d52010000b04003442c410f0104218089001d080703548250b600361103542c200941700d6800c102290440305101c08545038071491100c0f40d44150302422800035440641c0804650b40041190548010310703030004102d01550b074905052042100401064200554102d403415201c4d8845410a007101c2c451038044496080d141a1030080300c1c41d240715a600100b865090200424074007181c8881540503d420000a014030b000c030200031002c9410701d10030a41d12030b01e03403500d40b954000a0840300050b444040d03c0404c0e031648940320503103011419249540141e64449049240d400e0030b01c240da8005615041192855161080c020b0180d1030240100c1c0c130450504080490006030740d48050300075170388515244a182d681304001f80035414440006400325004507000005503105400d000d060b25016169030b0801d0400100340503020841c804445600300d03112030401c45510300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218600179 1250 218598929 218598959
    0x821040504020310030b070819020d0e0a03020a0c06020d0804030e130c05091e0a0e0c0d0c0804020f030f07170f03040f0918030f0503040819080105030d0f02030409090507 75
    0x113400d40d0589052442c54001c2c1c500f00004d02610801050070144215a2850300242c418603d983c100561581c45c140a100001d101c0c0050545d0240f00e40d107012002c01d0740220f06252610301542e103c0f69420340c1c82d2804da88a804000fa404002907054000500003406001140c4031101d0252501c200560450520005c036203440500c10003048000c50007101500e031451150303015000c5030f0070380d0503800d0030301d0041003507c4801d00600030800301020000d40359420f80e00070303614580c8401c0d42c24403001c0d2951001400b9081c0a94081c0c0c050070f400600c8914a0a00040700c0d6400d85208009007489854071000b000046003d68805506000e80529022402c07030400240c000342450200500d2442c0c9001c1d140400c684030205421a41c800100d105804240c01046030074140d251030800e6540c0341d859140400c028802c0408900e061400341001c11000f55000b02218140c80042d0220760090726107200682d400f691b60304000b0016402000148001c002d143c0003000c0c018420003c550361952502100b13901050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218601429 1250 218600179 218600191
    0x3030e1c02060c0a1209080c04020a0c0f060507020c0f06120411042a02070e0a0c0309020411030411041a1201060906060507050c0409020627030d030e0609010608210405040203 77
    0x4454450b4130240400070034161001c46803420321106003880e104641e92100c500c0804284699070100750001c003d8040c02c1080801580310087d00c00c0c0e120a0f142c00c2005100c1035031075000510404066078804c0c1421010300b1360b0600014130a80c20709410088101140c00010310807500e40000c0201103500e07031118019541400503c00003050141c0c03101c8061005100307043c1c080c4046600680082044442101c1540e03001410b00c80003141c01d1155000c250098980c80d100290071070319051344612005116405117010718404d0580708090300d4120f080006640d055028111100018004615645401034514444030003540001c95500d60341d280050481d4000c0e81f101c0301040000840c0c608201040c41803130030501044030108480b40c1141c0100d1201e000d079030000d045013a01c040d40150040c41d113008454030850010304032031041c000354a004004e00800d0900281c540b1849010030f02118046c02090141c8200200420010980404003486102c0418020541000400c401b01c5c0d40c0d16240010340c8250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218602679 1250 218601429 218601433
    0x20109090f091e08030c0a110d0503070216080d110a1506170a03090b09040213081b04060b030402040c12060b120c0a0818070f0f0f08030403030e1c02060c 68
    0x1880350b003050f0310001c02840501072100d030300c600d000c400100480c095a411510040a4940b1050041d60030f403003a00c0034800c00f0140e032240701c0031184882d601400652090000380e09541c00454102d0004010780c0a40c00380840e41d070480003051b0500e502c103844620f1034a907240200d03000d024440d15210140c4814004002e200741c4c0303800f41405202c4070341e4114010b20441000030b009222280d10002c082c0a09402045c24001c00045e500341c1035581d6405035100b075140011120502030f0703111529940c9954203c4070004039101c440803075060385818483d05007154601071320140307580c1e260342c200b02c01010165009000c2c0b00440f143d03488002c1c120300c200030103001d61070100c980c0c035401e00c0720408417440300404c9503610400400c10b034410365a00140c490340100c40030480c40340030105940440d04010094000308182c90700168005080d4044040d035400300d400c408140c92006484001c019164401ca00024000c00c4450440070b49609102c48401c80900c00350640c1c849007945540003ea996105e901807038559 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218603929 1250 218602679 218602691
    0x1e030a0f0c06030b01170106081305030c0106082e110c070e06130207030c020904030201020f0a0e120102090a06110c18040c05030d0c0308180a050f0705060322020109090f 75
    0xd4141c0704500c0c1c0d031002420301d0780f00d0710b84c541200c02a00d8414008ca000300081c3d10301140580c1400b84602d44040e5101003070703d4840002e04031140c0200458401c48101c0e10076000308425450781d10058021000c0e40107882c2d4200c03910149410041c01c0c0d21814040002820000070030354442c1072103000054200f100b4505030a040070010031007030481144440113040e10411107100080d030845901c0b6801607041c3e9400c100c80d42c443c00c0c04da00a0240700c92520740b2050001e00305411551103981c141c2100c40484490741e15207400b02c0a10301304d000c3c40728030941002e04180244071103405248058000841e40046500507031121001c6182208030385252020341c42d00130184030400074485440000f421003680104400b01c4583c000030049000c1ca1740103810b20003c50007141116a1440d074803c071003001d00045403100103c51400702d0307076002103040991103401600e6000c101e620300101228040d40c01d20041034051891000c1c0841d160340c01040c101e05205446000207903940c0580648801044900000946 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218605179 1250 218603929 218603939
    0x60916032703260f060906010c0506130201082a070f06090303020403031b030807050f04051008041b140f040209040f1a0301050603120a0207080f010c0f08061e030a0f0c 74
    0x20400740034410080f11508040005110380621219408942100d80507071945072a40107880507421840007600b203000b03101c02c1016007042c9400c1c00c101e9034401e070788042d525078690205060000c0d2914030310000042920301050b00075642000b80220501508505141540760f9560310200e8604040480100360040740420605822110b07152203202110328100e241c0c0469a0002d22000c00101010103200d4081030000140d40c1110a8030080e02003c1c2820030001071416001d80888000c5a0481d09040c1c1080032604805022a0f100101e54000c080707100380443d4038041020310940182c0080d00319a01b80954451a6242d024601c0c40e541d0700800090103050440304100c440c3c99400416001e6810401031040700e031400607511000a041d40003664981031480c20480c24140103911600b11407140c0c4146100422042d846010403203072648860082d50080d010503201e00700c00f103c100d503200d9044228007800f403400304514610207100406a03407510020b55500309590040c4002621792040e80281400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218606429 1250 218605179 218605217
    0x6090312050403020c040623011407080409020306030d050a09120f060c1e0201110301050f030118060e06070c0807060509100e0f0601050114031b0f0703080a05060916032703 76
    0xc0500702c03241003004069016640700f20b0711502226840e041101c22000007101001c0076052f0303291541d1005409645a82d2240d6240c01380d001070b03990034484e0080180c100740d030601540071a0b01514061325414225171600700c40c0a441690420140c0341000120710b01c000180e22841503005003140da8448000300040c1202c042c003a41202004481560b140a84001501e084c080c203503070444400f103030380310300f05103141010901500c40300c13040910f098058040304003001425003203200355508140403210199100c41c02219501a00240608901010041c030b20120740303ea04515400301058040700c0c4001045005001258455400b140721a080986540f119540601c00d090042000b4600258031803440807e240552002405101140c643d07401c01c1003100b40714405a07452040005116500c0f4065410090030b040021209502010b1401c1300003a00303468503c0895004e0074005203205840c02c0440c100758024800300032094040d03501ca03c46441280c02012041c0c1509100795242c01031244002d443c81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218607679 1250 218606429 218606441
    0x30c020c0a080c0906061b03030a140f0a0203040302010902030d1107080303091906060f090509060603060f130f0203122502010c060c17091c110a06090312050403020c04 74
    0x16100e86000101084100c00014001a001ca421241140b650300c80317100280c00d40c40750700c42050314215283d154404400300400a14440e2140300b00a1000d95141043d80002500464009618042c01e4011404960b4250b000e10752062090000082e0b84045800280c9041048401d803400103140700b968020040c001c1c80401c0c000c040000c011030450501048041d22511070b202c6654080304003d01c3e59041c06056003000b002801c1d10b004405c181d070b032601b289801801e01104c4250540c4240c6000c9150750030000ba189115100c3c0d80900e41c5141c0f40ca091541101941c00419244000854a40c00c0075a605208001da5a80e140113025900d1215000c004543c41c180c10f003296001401c0d603420700160340c1141003000010f81c810310000780b0390351441017641d003054140c22070710b0b00741c038540200141e00c100011041a03c81441c1c0380e500300c120200fa02200e1a40c0203103000503447d044074170031000041d100d41162510b80c1c400e080810600c0f03100d803405411108105c4084c0c005920101c0141020f040900c980 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218608929 1250 218607679 218607703
    0x7120e03060a06090c09150c080403152324031e060402120f0a021017090703110409080d02030406020903060903030406060e131101050405040e030702040b0901080d0e01030f020a030c02 81
    0x982d1707011f4545043e4680c90410400300d4400c0c000b150300c80008011409084402455124600c0c40c8510070981504004210b0460141c0c00c501e24030718003611a2000b044880d2140350380080740700c51107408810308a0500840441c064140c8030f462000c1114450586c040143e600070307000141100d2509004020103480221a2030b003040d0840307801070101000200c0c18505036030301070b22400710000401508666241c55a50440118003a490a120302010041b800c00d0880307008906000c011a2800c041000b112b01d054002007003150200b14041c07134080260040c1da84980038420041c10002c2206c0801e041c118211403000305031300000200000c103c9140b0840000d1f103c450302c5102d003032800008180100c11001d001404c0704a4540048625a2003801210090100900705104030320704c0100c0640d4a400c810001c0b4404c50904043c2092800e145c403c50b812140427800820401c000d00c83c05544d50340f0030103016410551103203840c21891605d4001090462803c1c5e90029610b44403a0000341000c108102c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218610179 1250 218608929 218608937
    0x8090a0f03020117090a0c150201110f0403020d0c0302030a0b040510061404050424200c0304060c1502040e060108060f01020303011a1905041e080307120e03060a06090c 74
    0x18030143c0d0344201c07411008410100d4500b0140c84540320030703141c0340080e40300600d083c400f500e01107522075070300300c41407411005500284942381c7c10900340e4a1a014a00c050030b030070784050000f0405440c12040e0708400900079500742d60929240d8010905100d4820400d40d0f4100381442032104008041084025070103040354100038860402c0ba0a0101c21502c5400e00d2146403150003250600c0388803170a0000b803041020680010414400440010b8804ca8050707034802c4840c030004c101c80f820003408581002d070850016601c1e06e0b0500c06c2c00d07034140720424420b0301c044031400b02c480084880e61004002408400148898514003a4001021110010301e55400303410030208500d9241d80002c10b0302e0644010840c10600b004072641c40c03803414010000c12203403190b2490002c1e40d50030b40100c001e0080e01d120b26000c2042002c03014401203440800d1040c01500e45c020081c0c20b001c603000f10502d01910b806440c1102440241100080c039103401a610b0300c02541c0d03645c8040100741043d02c210b6410003d42e0034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218611429 1250 218610179 218610209
    0x703140109030504090e010b04060915060e030d03051b03130b010902091f0c0b0a0609051602070308091c050c270103110d050304030c06080f330303040308090a 70
    0x94020f040707009a20480e20026201e00e0345490628081d00301d202202000341080050316651803d80c801f40c95008440c80150301d4081001c221786110f103c0305081c00d440503006040e600c00c2114114010070000f80151145048180b5507450002c0080c000c50149c3ca0307501084001881c1402c05004034001a130103510b4143c410481108140c80707107002040548000c80708115480310050341666000781c0f50200500a080e00c00810610b01050b500160546821100c20007050361110141a6030b1a20b04d07002c2c1c0090307800a2010400260340c4d00080400b600302800300795511114000e540c100b0340001104032070582041c4445000c3d418402428141003400354001401c54000c500600e005c0901800050142400a00e0030100b58460410b00280c280d0700400f125a142d549080c0300081c01d1244c01410005a116404203060707000700b402890142408040c010039000c0000b812a824002d410750301c2c0000b02115228010b2580d081c4041c100850003000143d03507078000e810400003552025040300d441324418207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218612679 1250 218611429 218611433
    0xc020316150c0302120406030614150d3b010e010b010e12011503050607021c1d01120f0218061809040303090501110705011812200f0703140109 63
    0x185940c4441d003110305050b10001c045080c12400d241003400022034140001a001038041c0c1d00d507010600b00c07101c40301c030710751011501c0d0100000d4003210402120007007024813210035299081e5202000882c40e002c400020b00c2070102e4880f0940100d84a00d4255025240d401d140d4038000313006403c44058418020442400300d0800685408010110a401901103078003242c0c1e111002d60000c1c80880d03940008400c1d031a501d03d0015510401211448014024440c51a142c141400381540c080d280644420000f00300425a400c1ca812401c0c0e40e0ba410461140480c09102c0a144100c1010034030340c0c03070007580e0f5040ba600c078562101c00304405907000701410040c01c0742500702c1200c000070402d8100c421503900d40f2107003011006014008400f070043d51801c9180211020054010842035105c0d00080c0319046c0c0003049144900c00c0c0c0b80000d4042c6001d80742d880300c40342c403c2495010900100c000c00803001c10300c1d450b00e841d000007c04806401d0780701040a03c10b11080381c040c0110034041800900c0300f04100c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218613929 1250 218612679 218612699
    0x2070303051f06140d05040c230d060b13110c0f03030f01261009020103061d0402102c090603031813140f07030501051509060c03070b070c020316 64
    0x2030b210b8501004076a13034918404104501c201c03800e2400404042c800707420703d42410710784411184103034134041c1412042c40c0030700c042d500c003008a03100c002050804d1042c05504c441024100181071990300c452480c1c03c0354013400309480b403c2000104521102c0d22926294056860710110f00240380540d032042c002c0040e4614042540c0341075400d40104680380080c00e56020b00d5640c0c0e0006005032a0048694064030805160f104c519141e0003603030103000d00e40d581c4085450410080804404280c1d0b040001409420b00594409a01c00c03a4070b000d1461744030003a0b0850301c120020b402c0030241c600e224040c81042c03074502c4100f0780050301140038520b08607140381750618030300000201e20301450a03480ba94107040784a6220325845600006010a1803a01454004412404031403c2004c2894000041880e0904d03c0034020720100b0080014500040302d401c1000302d410513007141809110400814000806c0045150b00854140d00c070074140c1c10681c4105400d1140c40e02a41d03d540c80090000c008c44811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218615179 1250 218613929 218613991
    0x1e031b0d020609040905030409020703090f061b0201120f0501090b041107030c03020c04050901020a030e03090d02040b0f030106061e26060a030b09070906140105220305100207030305 80
    0x70454000c0d9440d00f007180840d001d46503945024019002c049000240b10700550000d100b214403d607541007000d525058100c0d8001c000b40a460005045040380004408610344010003140c0141003000001301341e0f0307110400350f071902d45019581035104c5004118211480c054502d0100f4105e80c28030000c540005640c8082c00b1b100d60117000c001c111081a414580240110300f178031900500184031920f00866014040e41c840c540c6040083d140c02d1602483c0781c0081700361418443c0c000c042d02000e034030980802001d17002a0403155170108001c00455060f41e0309101d080e000b400300c3d4841c1c1640411805103040c005c980b02c42c10383c0c180103188074402c0e041810002c0c4032030f50300248010102c02d510391201051a140c042c1d08002c110b151001d0a01003402e0300001e28904955289805010140c0c650700345482c0c000203150624042401441005102c0745075401c3d44c0608409028868062a581d848242c94040f400343c581c0103c940c002900700a0603418040d65511442c068031303040070f010010701c000c001c1c065 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218616429 1250 218615179 218615183
    0x3080f030a0204150305061002060402220209060c0703200f040903110a030306080f011401050906011407060c030f1a06030c041a04050a1d061e1e031b0d 67
    0x190010000701e0402031070341503401038010307200380d4602c2126500015000700001d94151b80f1078001542070030031503480000c1b81c501c12540980111000c80780681414220211486641c401d240c01340301e907100c80e4a40706e0203403010600030401003c0f000d00c2d40c14003171550241c55407800c01c00003181034011403640782d0003401008180103503400540c41110b81002c807000c00080700c280455010303949500c401d140d0716400400903076001100342c0300c0030403581c1d8041b404c0300d4004040c002483c621a00400007480c2040c1080d41c449010f040024004006582005c4180c0c00402c0448025035200c1010925035410300c1440d9000740f940c00700f00700504804c084450400f000d251000d03c01c001c00800500e10041e42c0068800500d26400c5401410b00e00404070309194200c0d0040c00d00590440d10001031056022510320380c88400190350b904039480703507424000b003009100050744a60064040b2880982c4034003005401c00c00340b0883c084d0400d18610209030905a81090001d0042c0600c0341d5060b003035032a81c0c0344411301c45e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218617679 1250 218616429 218616457
    0x8070206160518060316081302030709050c0f040b04060f0507240b0a031401140f010311030a120201020901180602250510020d0305071403010e0a0b060309030c070b040308 75
    0x11068154103e042c1d04034100075908075002000380038900b145403500c005c5445042d16446090380d41d506100b0000d0600044c040e5240e03100d01010030600c80d460784829001000c1001d1310f4581466105520040d42c001c0c2e0241d044500c000900f040000c0d484020310703001c5901490010f00e09803e076103400380408181419140e00001c500381810b03101c2c3ea903500808840001800301c503581caa81342000740d103044044032040c140b9401c0003048004240d0702c0c850030703108a8981d4400700d51a421500c0b420990712000313075415018030a580c03041000c140b803102c3e40e9803a25220790026075190344800004126031707028542e0504203068400180320305a00825170b03110407600e03023021885a898400504148040581c003058005110040307514a039640494445002401c544003480591071b0540c04a035652002a00c12940740400c0c8010f1001c0e00100f001c894009030085c1000c5610071000001032a01d9209540c0e19840303a00000c1d15114a00f4244400d00040c050351a02da41040d00c0c2d80c031049000e200e4104101444c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218618929 1250 218617679 218617687
    0x9040b0c18030f100b040b030a0305070501110d0b12010c020303060f0a0b0307181d0103020f060c06090705031212070c150504231c030b0102010e06090d080702061605 73
    0x4154880800d100700c0e07000504032a18810343c05049034803100b00d40800107115040c0800700d08141081d00901c0d1030004007a0051004440548045883e501f021400316429500c410545017115004009014a048083d03030025028a10508101d411130f011380348041a42d040c0818032203299004016694020406e40f0300d0000f000fa10000140c80c100c4940003030108540c08014803001c4c641c800b1140403905800140b840d560b81d103c0003156100000302180402c10484100140014103101c2600303c5404406403e05003400545c13003040c3c0c14500100c55404295002440c10007951504111015103000390720b900a152081c507507924040804020b100e4030a00100b004a1010082c0b40440b800800c45884400c100d03905180c60010781318284900c041300714911b15201c3c82c680c0c05011403001c4502e02c43c0107002c15101d111403825000340044c889180d055540e169562050003800f4020103200e5101a80a00f83c145140c0c403000e021a01c01030314a0b41190303c000108644070800b20348080c018846030600c1c42d22 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218620179 1250 218618929 218618947
    0x510050a05040507090b130501081b0a030c1503090609030807120e0705061b0f0609010b040b030c130e0d020c2403041416030302030c060c1e031308030c1809040b0c 72
    0x400c503040161f00d940034039110000030140408266440c0e03d040d140c07040481740721140e0410031044100c0c00050918113101200300111180740a6040070300341d284c1004112103044d41c59110445116a034281d004c11204800c01c050030341e10038a00294100c144c0d100700306600000320000c4e91034485000307040c0611000101340f440d5210354000004042141e008686425081078030180d04c810095807403551319030802d40c403100b491030280600c004040000c0d008000c12a004010000203144001007c01c074140d462824007241035040c000b0b981000c0c0300c0d030018405800b059040c00302400240e40038104003034003814505188981103084982154101840d05541c1300070316400760a01c4501d0a9268046001050000c00c140d0040040c011016941c41620400d40c1c032903418889501c0f41001d501c800c0e00c58506070a041107566006503070420046004035840103d20350742d004907a402540c4c1150700a801145174008070304040ea0074031a40d4000d47c0c004000f401c2c03035640e04829a8020f0b2120303180c0c2c1c10100d10749034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218621429 1250 218620179 218620189
    0x60804051204060c0c080109080f2b09020f0609060f1c0c0806040c02060f0c070312050109061809081801022d010b04110406050309070f030510050a05040507090b 71
    0x18114003900e001d9681c40d60340d201d001d07191805001088500ca00d040d4000102a5410301c17401e07022642041e810380c03401c0380d10109605158455100010351001030606120100e91001081c0c0c141c0c038800c58000b8200b9002d0040222261200e04502e104004c00c120090b4141c417000d043c1c0303d040d2040811281c441240301d0312202100002e590180c0c6091401c41d69583e4260b104008034000d00d01920204003550181034100d1b240e2030f0032951310900c049180c0216020030180b13401000214013a183c024601c1450242c4001035490a80c4035541094075460107201e08156020800904e42d01c0e2002005041042d940d02171490182c41c0c400c151610104400c4c60b8964002c2c884010f0488000c4488095aa80010f00c00014400c015454206620f0604401d51b1414244510b00745450304010190074686000d1044a966000900803040b40c080c040c400200c4000620343d08e0042e40c460006481e8400da4180c0e600100c4030000c01503900c50b810101800b000c80d60100e0504150b0b03010b000c0125684440002040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218622679 1250 218621429 218621443
    0x9020f0c030c010203070e010c03170a09200a0b1809060d050105131203141602010204080d050c060609150f0103020c12030402030706090503060a0b0a150203130506030c0406080405 79
    0x19001c00034041d45041c0c0103600940c4a800607440d40417000c1100c40044034113100086009001c141d1040300851400030b9010700c01e03480250008007240c244266900c0103a17500ca449601d003034128030842c1c883c0746850104180c8c806800920002824020400001c0d009100545003080c0030341c8080c00401c0c0d0580f40c04c4000340444c3e4001c4002c2c40305083c44051600300d605000da00390740707050300c7e03002e40466980319000c0d51020154640603501d0689402c8a060380002c41c8600c03c0c8255076080100169450041c40050808241512500c4d121045c015009050050003801c0740e208003400e0080040b440c9110780c0303800d51100141d9040b032904c29207000580092081c0713035100d1114072480f09509000c160b00001144600d06c00e40503541c010307580d610195601c140707501400e80d050300803000041b00103030384e80e101060504008081110442d541c03401c1c0340707000d0139011a500c016000042c10703024000d1641d00000007444152070441c51440e01d03444519440c01180a85410003c0c400027007800e01404010310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218623929 1250 218622679 218622697
    0x12020d1b08040e0106020307150608070b0d0b12100c0f120b12120405030c040603020f10020a0c06052701140f071b06020f03070201360303110c060702030709020f 71
    0xa1195135031100d4011f9901d400202c2d00300c6203100c04582600d1850600c0c000d2001715440b0400922801d03050a85c5098150005520303800c400759590300c0d1318020781e142c686080d50350a01d100540242c4045d1020b050640b0458905001070080e46252806690f50001881a01c030709601c100080000200d8002079000f00310844205041c802c40c03242311210351a440003070045500c110101d6018503810010300003aa400d07071001a50295104c0f04401e804d042c82444a400c0d08454815a8059003941c0c0e1820501205604030800146003c04c0e00320700005078151082e15040e910110f40e04003136610300020b040c8240d54041800c43d1002292000303144881600351141980d00489240c0c0c0c0705000d25400c88044254810f04005108100b41c034a284c21010080340c241c1d5030182d484981200c1f03414032481c00480041502c56100006085d032003040c1b2503a42924014502c695101c0181c2070140f080706d80b0308040010703103d1050104214120041c2d8002441c0720403a0712700000581c44100040541180d40204004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218625179 1250 218623929 218623949
    0xb0405210a030c02060f0703110f0d0b0a170a02100311030115020c0d031e0905101701140109090b01020f03040306060504050c03010e070818010c02010912020d1b0804 73
    0x685100c1082201a1400019941e000c00ca0610281000c990307409083c0e4201802d602c5040114090b2846a044641c40e0301465032420314010a10680055907031010f07000c3d03141c5e10358400c104d00c0c551911450301002002400704170308460660b480f0442c2c4801241900074400d0101040300307000a03000e6000880100d14041c1640d840750b82d10b02024107001c20f2a010bc00040c01078132130741411031030403203180c0f002c0b66059a00c0514103947c510f038010f40b6411840b4010305100f05000001000ea8684c1a840c588201c503945442c4560700f41c84c4200395409041e005580421294101d8000a9900ca1500f408507481080c0229581103044010303030a207651403030746940034000082c000c01400010741043c0c0c112101510200107a036989843c40c0c5090000b070003502009182c060101d90554415200c00d50001004007150032180050000c203400c407840c0c1a40d034000740c9d45402d0303450103100d1000c00b130760401c4903a8009419800d01042c0c00030302c0f40051044401d03c804014440740c044c0b05202d41075901406101d02d13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218626429 1250 218625179 218625223
    0x80a0b1e0418140f0303010605030c090105090409240e19110307080f0c010c0305070303050907090e07030c1205030306190f1d07020c01020601060e0607120f080708090a0b0405 77
    0x4003d5a200d011a16000c8544103414152083c19400022241216155506c1c107086403100c411201d00b43e401043c403141000402d01801600c0d944a1248001d15413040807183c841d4000030080c40c5580c41040094002c283c90406040c524440210b00d04484036001c02ca0700303581d00d00358a4081215507610b401c5903014419103001107143c13100059044d844540d904101c860040c840001103907110503100d0300600140c02407140000207802508040c0c0c024180b001a11403440d1a900c1e030f07038100d40d404004241c040e80101d4040080c0214600303100c000d010140c26401144a0a440d6540e032840b014089c0b50198580302d0000050031180c1007071001501002d140300c901c0b05c5c1c0d036411180000150300d41c02c0002100040100341c00358000a030411880c501038000d400f030b6a10300b84090f188281c00e1031030030342c0044041000c2800180b44110102c1a2003aa4585c1101d007503003140024440f45c0020b05003801e1084d58800d00001500c000317244090154001481c90031030b41c403403a21600b4036121802c80c10440003018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218627679 1250 218626429 218626433
    0x903050304020102152a1b1c03090807080c0703060c020705010e060703080703020c03040801141005090f0c07030e09090c19060e0d03020102090a0b0406080a0b1e0418 73
    0x10010360049000342d08455004820102e081d0900100b600c15100500b0900d0615143c2c0c030041c40b60181000c600d15a6170704145100d1041407042c2841001c40c00203401c010001140c1525804005002e20750616080040c0503860ba81d900071031240b80b20240880e1070220300c42040c200200700d00c0c00550350090042c040c0c02c0406601942ea200140070741c0c3d0215101c420701031540e0514509861445c1d806648026454940c80401e90096100442102c4640010800400e40c0d04090107008a003c4010000041c0e5180100707400c0c0d42c0020b03c0c0c020a102c1c00d01c403070900c1340c1c41c915031819542113007003580c4403540ca21030b43c5001d54a6119480b0b035150081c01c16010421802c40106107070340103070025160402c160301d422900040c00b58842c020440400c3c00460740180504050710101005071283c0001440c1201d1140040da0041c26540403425040d0f00040034000c543c0d01c00d041c1900045007400074010010140c00040782d58a141c1805d50a81c80d001050300302664880d04400d185507000052651280014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218628929 1250 218627679 218627687
    0x1809061b080105040c08040209060f0114040807080c0a080312090a02092a09103c030b0109050f0405250507030e06070209130602120f041505070504090902130903 71
    0x3d1050620851518032800242c0f400398240a05c04d56004282950a540e03c4007000b0446001c1f914550402020191220101c0040c1c07000b04003414508001303020052400085d24030340f078401d0154500445c500901003110000001c2510351900c5280b4480602d0764a801c401403038450582e03006540942d00e0070500c605004111258140c10f0080b00181b00e40f092030811100c1e152140704035603504440100e5200710702a04c1010721540760f4131003005140c0c25103000e800b00c017500160402c0150034001c2c8800c4804055805104407940a0001c1c05c001805610784400981c00f8440c0c44142400f0319150320010340c0410bc5c03176003c0c0d0304518083d81070813600c07890400c0c000e019401c201800ca0100300c1034943c240c0f25150000030f035030f101540103001820940c1c90301509921014041c0045401d075409000c9100c68084c8401264403900804a0012482c82e10f810200c00c900012180b07030794041e00c0c1074140908203030303c9801c807030540d503d0100100313800311b80e48045540e050007121850011440c00071928105070380 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218630179 1250 218628929 218628931
    0x9150b040f23040809041b020d0c030e10020a02040e0105070809060c03011412071e06090b03071b050a0515070c0b07031d0a06050a0506030303160c0303020408250f1809061b08 77
    0x26941c01c071040b000b90340c402590b2b1010001d070060041224801801030368501600c03080d641d0360051042d20300d420007035800301d030aa072a115a0510389075107500c1003000f580d45c455200e80e80010001c0040540742012051045c1a120600070585060b04070f00c0e4400d02c6890340c60303c40700e10340301080464902c00d43d519540e1403ea2400c0301d1490111040341303000940d0921030303081c0c101501c80400e09030746540c84141c1c040c2d85076120039180c1070480c0451901d00001c076906106903c200d03030168010300310080307041d0290b0003c000000c04000c18010507000358808940000d0031b42e030f403010f91400e0000300311b603020722205800720300d009410311240301741d440c40d50402000350170517070055002d064180110784400b000c140d00c900040b60310070110321070f01d4034160442d4420f16106082c94000d040c014649525183e080e4107020340074403101800080841c01985aa860000c1100249000005c06400d641000c200381064108100020483d9071514445024024541e101d10f451071005030548100c40303840b0102802d0500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218631429 1250 218630179 218630231
    0x30f081e030711060a1a1018080d080f04050c1005040503010906020c1608030a030203060d0f0501020903253c0f090b0a0504090609150b040f2304080904 67
    0x1024040754002480740258511b502d0b20a140042410900080c0051003851544200401a10b1070030249459184020a0060f08501d4050010300c0d080e03100250070088081c00c0e401c00341c41ca1204000100f20042880646441d0031a4802001c00003103000322814021034020701d5041d403030592132078108541036000380440380c0540150303440400750410b056112002031103010b079150020081070f035005100c2e90045521410083ca021191481c6882da9401c018005000300c074560b50001d980c0e5050324040080300035007001041540641c042d00d62151705544064411035000c0ca109000d900481e8400105000842c2440c184880040f1980d00400807155024400d001c125251003d021501130342d54010107245800c06403804040c2d902d4a414040203014545041d90707040d6461080a0024801d04030300c9032840c00c2d18801003460942b18041004464101448941603860b0080178810001d00050190800c0318102050f072140d61039003040900362003080e4459500c289400382081d0007606406201703201003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218632679 1250 218631429 218631433
    0x150207030207050307060503010303110327041404050c010e1807020106052403070f0509120714060702030a030804020a080a030c0317060d060b0a09140a0c0801030f081e030711 77
    0x6543c1d40245038a500d42401350b90001030003000144042406141d0f41c1500a540c001200d140941107480109241c02180c4851074816040d2902002880c06008500420906000078181800c103176441c0c0350348400c00c5a000381402647d4030190305507502e031410218032100f00c060f03042c860714161800a0080445004440c480c40b0300070783d0039204100c0e15028a940740d03402401689903848810302079861403040d06000d000c01804100880c51a2180c1000488a80c1d50b480203041e11410318041180701541040464004c000034400d0b5005680d0001e82c2100290309814103140c152143e00218421070030941040c0c009120710600f0301c0c205640000d07840c660901980ea090320309c40030358035603012903042602c040f54880c062a00c243d022481d10350284005540c000c2c82c45940603a40c0702c2e05c50a80da561501c07541c4c048048000c01c543c00e401802105410b11940ca4600c0b074560441c1d81c0d80804196502000d1300402020800e8510b08035440c003034648220070412100d0300d038030380004000d000a840c032044203038034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218633929 1250 218632679 218632693
    0xf02071a19080412030b0a080a050c03070602010e030909040c030804060210050705030105031506120114060a0b0903150a0b0a031110082e05120d0318150b030a1502070302 75
    0x89208220890040e80c4c001100c50b0081601601100a0a1b00b1113104d940b00d0002040041c0d00e180c20446050303000c0c40707000601b0001c0c0c034050070107003040e2042e03110b04290390400641013621140842140c014403011501001ca6482c2c42c10a40c40c80289900010f1125a00041c0804c026800003171040c60032a4645081c4a190780d590300031200c60000303208058044c2d012001180e820f1045c07482c416030240e00a0001c40da480c854a4401c5d00350303000c03030071625a0000c055091000f1420441c051201070030f03050403910325000303242e40480c0d034070440f150000c00b0038581c070310100e02040700a405c418010900200191442c54503414000090300120a80304d12518441d0001c000c800e0041c2003661040250080030507002d00410002d00c5103101c580f40c0c0c034060b050104000300e140d541d00074807031034105501030081c1114156820090100e40a82d031700d291030395002205000c00110325811407500c50010000200344484120082031070421613100090103c410700700b4001c0d803001d00b60701601341c09000fa400c560030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218635179 1250 218633929 218633977
    0xf18030a080c161409090f0d090303080c0f0a080408091003051504050f0105060f041224050609071202120f06031e030a1116080706080106021c0f02071a 67
    0x3500500d486410050b54407042501204e28010020942c44240c801c247c44160260009503414080c0c288604d0b004510440c40500900d94842c02d51035100c1072810314203190603061300c01070115014084d80103040081c1d000016003007244103000e5034001d0f600070300507014013586440b02a010300702c11a03030300780134681625060b12545050b019803401150303688810400d690030582402425031007840c600884600810000490b400c00720225884075014000e6145605904025004003124541d8190882410001440ba69550386030304d1941105844c103100203003e20002100740607002e0003560329081d0805808225001d4242c15410b48592800c4040e58200b401d10264034240800104120749103034010f000e229843c50141d0403810b41ca0512a044503100f40108800d03080c0f083c4107400006594024507410483c2c103400a100c1e501411070b90000e000e190031a61400a80310f1b482000940c20401d90030300f604241e600a00191000d00981412000d2040c001300300c1d000254001c50a10403002105610f580c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218636429 1250 218635179 218635213
    0x1b0303090a0317070206130e0f1608040614180c0a03050703020d0614010603020d0c0e0d030c230c0a1203050d09020105040902031501030e0309060f18030a080c 70
    0x55a4400149800d035440d046880c1c115011a80c0f00250b20f014904004840140e592240501120074035000c03080e440c5424801801850031010f07108e546003103a0710080c0400e041040350096401c058030324110225036610700b481000381c521403102d0f0f40344182c00004e0040d45c48018188140b5074082c042150400914607041c000009000e110181c07180c0c02c0104180014500b41544411041c028079002c41d60005101900c080b00c8000e901140100341d000070031807820b0265000b410302e00d101a080180c2d0300710004021030000b040b40350008040107818001101000394194032849400d004c0c031140741c041266022595030300e08046040c2407084071140c000107140d0b88450403000400f0381c0344d40c0c2e00303081c00c11501840f0003a014800b812030512200388008210450713184042d51141c3d5441074281210200394001400b00c82c4505080344050300100030044042e141c407c00c0b0303612211030f078402607624140d0f1450081d03a446590314256060060007640b2050000b104041c040200c42c09069070144c44608840340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218637679 1250 218636429 218636437
    0x90807080c13020405060a020a0b13020604090f1b050a080108060c07080a030b0d0f1203090206090f0d0b01060201020417010501030510090f06060e150102030f070f0804090e1b0303 79
    0x44a41c0c044891850182003081c500c040600d4072040c05420661240002400c03900701014010040c1e01c91364410707050041d44014a03400c05181c0c3c621010003070854000c03030094031a502a0700c80603a2544081d155100c40f9a00840c074840c06840040302c0031640390310061080e4040034091002425a00001c600030402240c3c0034010f454401c0e1a0707140124650329048035800c03c251050602d07682c1d25503540c15480c2d002403035880522405620a17502054640350781100352580304c02c0101840c00346c0a0340181c9800049950f07a80d030840d036202112550100050f542040710344c00a002000f00c1c400004c50366015000f4200351000d1251400c1060344d40c1c03026600325007007440701a002d0760058903a0307402d11020b80d20103a10f06000f800151034440041d19035a06844c1a5444021340c100705d0010400e01d4412400e0b9100540000d10145240203030070300807003102e4040c000014000340a45d07501c500c2000701000403038008065013001401041c542d10350035502da8941c11407140c445400c150302c117001480c01000725 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218638929 1250 218637679 218637689
    0x10b0c010b01020708071a0c100207031d0a0b2505030c0708160302040f0f090f0201030609020a1205131704060305070e060a03050c16080c2503110d0803010e07090807 73
    0x510005241104400c02d241400d004000c47d0941004000700300d070303c2803203170024510102e0130241c0e40300414a00103000b400d088000d8446a0301c83c4205610903501e2035020004c070f030060341081c1e072241034855110341c2c0b480c2e8561600c00300c404040280c2c02000070110242c0036901049007130b2410b0310354a6480584940f448000340e0038880e40790b5014030062170141c1c0a07150205008000040a43c983c4040340304503035880c0300948007100d42080050840d030307041c015078015040329002581021562800039114100c00800d80d80c07050b44510005e02119100468603403480d81200040381d4030b22410203808280da02500a140c0001e0130440000c50003405011f040200610250142d85400300b81d080440003424050a0800074040070000b4220301c0c1c80c0c90391080e0509002e009041e40d01c00d0940111032800d8040d403515010100300701503150303030251500e11200407079401c205808110304602d80016114034405030000c26601e00440081201e120400d107851254071a6200e54002c00d0f110cc070a5660b90101d0b10174 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218640179 1250 218638929 218638933
    0x10f201e280302010b0a08060a0e0d0e060918101d010e04020108060109150201060f0905060607030807030908030c0a030b01020c090109110412061b03150302010507030e0306010b0c010b01020708 85
    0xc207660364145000d6030710306070080c030000914102d8100003840b081ca841c1e1200040782d05c0503051007070780ca90b140b1684040100c40b200920501c10140405000101484083c0d440340d2008600100c082d125610b1001c48001200d010b6141440d10b9000c541041c405405501d4110f88a83c1038904448803039103000e41a600300e03081d801d8569650342d0044413800c3d07005140b241040150800000c10b09040308000d5104907443c0c00206102e402c069404800f00c60f954001d010642c140014400d182d1105800c592009805107030030980c81e40e9044060300a003078082d070020310b02039002003040914440c850280c00d00f44001d90302403045d03000310001240d580313401c001c60690013910f4800410061030709900c450441d810040d002803c2c1640c41d4801c148800c80b000098507860b440314440705001310340d1107007518070541d94201002070489400003040351107060b0200034148080003480f4420705004031140c01d030400c0010200c8405c0d41e1168045006a0001225943c01d5800c0c95481d407100e40c000f0030690151500040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 218641429 1250 218640179 218640223
    0x305190302100e010207060603050c120604020a0306021308030a0509040c0815060306010201060b12070f140a08150d030e04050a091a07110f011505040501060509010f201e 75
    0x1046070000c00480780503860035982001500c6c00600355010b01001107018a01030300031202e101013400a11038000f80440d00d290032240400005a441710071082c1a00d07000f0000503102c0c2685030369000d42503210740080b16a0710000c50810b0030180d010005010241c3c0944051021031504181501e04440c159064020351003080180741903403c040c0040c3d90b00900501c00400c8480d0340303942400a40c1d000c52003000030549d10b40308100300d058200035504050589440c151031003400c460013000c45030003480c012108011054010440250710303107505210f07140008101d90081c2c0301d6860081c00a48600011502a80c28000012707685880f6225450004e41c01240d0030302080080c0b0034104002c0307002004401402a0310841e440484000c020380703195400f05ca0000103031a02d84003d03560580b540f07039004034030590500740140459a071200540b21442003e080c950198800e0940079244082128074036402c00080303a0003419440d90005a040308103e0b9a00400ea42d82003941070680c94400742107540d00d0383c40d2009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 218642679 1250 218641429 218641453
    0x406140906040e0718020c0705090c0f070c05060406080a110406020c0108041502191112040e101502031201050d0b01050108040f0605040305040303020c0301060305070501140d150305190302 83
    0x43c0000c60345401410540e50403d449142c103042203d1000d80c040646a07010071601c8021400300701c5130001c5d03c0304880e40e80503464080c070881d0091181d4501110200402b06203c0f0401540303048000103400024509601c1d907840c0d1100400882045a0b4820340c01d0070180d0480007004154111001d8507150350241400224100042d200498040c000302c500c0421040c20034006260303031000c0c086514800d100346100054402c070003010b12040404001ca035410038403107128420b1f5036034221021a0b003803099010043e501c030310844543c5111a1b202005514124810082c2030f64080014864104c0510941840ba603c40b402d12a00c1d9485040090a010640006100c0c035800340b00e845a10901c107508802c5010078941e1070b082074500564040740841c002050034001c15806200c00d42c107842e4142c008120b6035145844141d42d0b102148102130501843c18141c2c09217a22406c1101c1002040007801d211101d14002e512010800302d104c10f0302c031030061040e4410603520701510840b01030f40560003000c00c0c00c07000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 218643929 1250 218642679 218642681
    0x30a1404320601080d140405060306090a090b0c0307180f03080c120a080411012d031812020606030304030b1501090504180204150602060a020c0a0f11040614090604 72
    0x240305a007203204442100200401410003056000e1304030080070740084540c2c010064204440f180d000c180d0510207003c00d00c80c070740b0f0b1007040e079612150498103010145c07505464400108001140908005409420808a41c0000c8001d500440c2c41da61026803071003400540d404986810701501320708aa8400342000400c00c0080508a189030340e400341c2e49880080c8500c4002c0b40d0103c0d8208022880103c1040103020361549550258902801e1003032003071900c00c031001c4007400740a90741c140c500d80190b007458100c0d00c03990000080c0b007083c0d281c45030030445c2c0b400c2003c0507020001001c401803044900086040c280072040e04d0849500030101041d54845258008210081003101c0d810010141c400007841c1d81d40780031f80b869031031030214840c0d2480340d240144000d451b00d462a514950060030703000c0007141e90000d801703644004403120058903a040e4440150414088010180030354410304801c00a1000c4080d4a04050504403410810b2507640da8a03a800954090402540300c841d06000900c00d05007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 218645179 1250 218643929 218643983
    0x2006101e030305031f17060f010501090b091003110f0403051908070605070c1505060f060a021f1b02030301081501030201170612030301080d020114062d04090305030a1404 75
    0x807484001701401e4448494000c02860055007505a40c85070003401107641c1d00b807245070302605080c6801c021a07800c119142d51103114500f1501d0151098240c003c1e0214441c3e801035242140c410800c581d9290000b03401159078010b800156241d000c4c000005000c2140c525400d0250340d81b16803498205983d039100c1c02d0003020010702c41400d00130516a0800021103050950748011a8554000780e02c2c204075080c418070032402d480041c01144200000004140c0002d80d100b440c00101251103202c140003403200c0c0180c500340c1400d0501071610700250088940200280d8140c4225400703c4616060726403540107620400c0c80302030302294039480c034502061840c1c0505c6a11100140c0035290156034481003034034503442680200c1083c2c10030b5040c80911582802100118003d1380e40128443c00c14000003603007a040c1c1205003008421400440514065100b200060100020f0003049401004e06015210b07520403156030880c14a13040c645505600e0210b42c4a0085170841ca40c000303425070681e200810580 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 218646429 1250 218645179 218645221
    0xb0d0501080606012a05062d0601140a030b06040902041503020414210601030506090706080415020a020a050307120806090f040209092e0e03030702030a2006101e03030503 75
    0x13401c0085c480118404011540c0100881503030340002d0506995508000c524800b00050240124010300c040d42e03a000351005040e0020181da90b0303660985541c182c3c0100119281503400c00c00210700054103c85c964041d0080382c1e0103280341e9122000a8100728124421401507850f10359400c5403031506820030861f0305d0b8281d50000b220880b01c460050080386801d109031301c1110b003980141c040043c60003061007084001d048506100c1041e042070341d10b50340035107183c0764000002070b80880d003081054800c1140f0701d10b294100c0b080e265030702c455041052820380145000c002160841c0081101402c0000199100d661200e80012143d16240e007045034a9034060009900c40c407811000e51000d0301d4480108281980140301100c00418041d4800d080d00c115101441003508141b08122281d0303008000c031482580720389446200d4004c9030200381c003421540c0800e200b9612070701c403c10202e00c000c1d002c1f01050311065102942079011844008007041503601008001600501c082254428845080700e030a02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 218647679 1250 218646429 218646497
    0x61b090409080315130e0705040c14270105040302090f070323160302130b070807080a030f0f0c020a060b060c0105090607030b0904020904080a180b0d050108060601 72
    0x54594a4400782c40c1c00c00d40c0d140d01050300d00454000586440c010603d0800d00d804028003400d024001c100d0b4907040709200e29401079480d5950591818424109580c101e0480b000450322100720031070090142401581b188241600c0c610100f40c2507010350240d0f81280c0c0e000b23100c00441e99501010001c0510301a03d18010706888040410307202c442c10040070250f40c400790900320741e45400c00446148100621580f02403601c1040000c61a66040d80f00d1800d469289080079991151850f1600d0640324140e005419500d022840003003699058000e00301104c0040014440d00311290540380444411402480250340030b030b0001c070005081900190010000102142d0070510769120a50a44204503020800c2d0303000401002030440c4c151060b0386c1c2002044d180340c24103240c40d0b40410060308000d0320142416401041c40d05076584691180c41008c003849040301c051356030321150000590031001c0190210ba050200101e406100091101d200380416501c080101e9280503400c0d441c00100114400d142d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 218648929 1250 218647679 218647691
    0x9100303110c0307090e1501030506040f0503070c03060c080907060905120709060305010204170c0102030d0e0a060603141b06090607021206010b0d060b0a08060f0a030b0406050711061b0904 83
    0xb03507509001e142c0081c11018400f1841c80c43c20306985050001c0c00ca8401c0040003007400500215a00007041c2c2c0d44950b00101c22505c600c1c05007842c131300d50700824200501d51003401d8000f0040203200c0d0841107103002d054a07201015110148017540781e90081c01400002651070b10100b2051800101d080c0b0340540400035100c226840d01810750940300780f900113641d6a0340024041105184030000303480d80c4102000075120104e01000001d40f02e100c0c2d500c0c1040a16110310000c2c540d820240001c810b520391200341006202d81d2490080f0380d28502c4481c24150f4011110220b68050751941226001800108500c2ca0611104108035050304400b000742d8204101440d8420b00c4041080064083d181c0a41c0302600c0e1b91001d0940070590781c00b5004030210070002c4c4020509180c0184c45c69030864400c0304c440d013403102c281c00899413040710390b840541143d0000c0240024002107a0010340100f600380c0d83e110310740f8100c013074259032150292000d91045a04070300c01111139011001034010034800400100d40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 218650179 1250 218648929 218648953
    0x10f0c020607140f070e0a0b040e0d020a110d0b061c0813031b03080703080a0f110706051005090a0c020118111e24040b070b070e0910030311 62
    0xc0c2e00066000c880d0050780c0500e007106020708002e007404101110000300446810310700c1c410768003840540381d59003840c0c64148480940c3c0c0c9517002084010b50b20011900d6080c18488000c0d503400c0030200950304100d0310401c5080500b08010700100082c0c01c22440102d5840310014405200d550003452080d1145442111000941042c0141524a070440d0800021419810076480c0110440203100000100c00e000b000014000b800f954029030b01401c280b0ba840e507030030a149020741003000e09403880a00e82140c0c1741102c2020006070920f913000300c1c2c042029507141080c145500780d00e4050304e64031120703000c0060358018060f0440f5140b80c005100100c0c5030402ca01c0504983d030746110701118070050305440c056490400e00444007a03a0600140c840d00c00b079915011800302d401100b8606003182c03c00ca101d200d43e80340901250020420368140c0ca68a0003142810a0088001d03100751001500c1004a050946081683c4074010010014401e01079844e5035010b440c105000c1d501114240200001c00030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 218651429 1250 218650179 218650189
    0xc0312060d05010c0c0507050d03080a0b0d0c06051c05090c120a06051003050f01110f070201050c070308070b0112080a0e041506081b0f0d1e0905100c030e0c010f0c02 73
    0x801810283c07540b0584817003500d081d82c200341417500014021092005200b021030340c003c03111500480404000141004048081114250005405004542d41c0031000034065400002845c0401c009030407070501285040405084d1001a5020300940d031040c022110149001c13800046044201d10071245046050386d04c0b00150792049030310240c240c00480040061103020301c840602660003000800564005070030303014250040c03c40400e800c0402180718001c6900600448403200b11440807108030750765a2900c24492350007250105c40705031002000107103400303010010102d103a51150910382488407034001243e130780b00c154506503442074580e102c1c16030f90f00903102d444000e0001a600d000c13592922501d0300d000d02d407003078040107415030013044200d128002200070f485915020322800f144ea00b8118840034002d41e440072540688602c0c02c0701100c1081000241d40d10f00140807402400f031101442810350441c1c0d00013001c64103580000300c1c4510950f20a4644650b540910b04049001c0c05450700811 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 218652679 1250 218651429 218651441
    0x12060306020301031712011e030615170601030804091503060f05090d0f090b0c01060e07020106240c06050a06182009061903061a0904060b0c0312060d0501 68
    0x80c428680c008010720074403240360307200580e0540f089000f030302e0074403510040c2509160500c2806c554030b60341000c4050421030000780d00000d50300b0142c00d0160341060b01d5403800200292040d90086501500005206400031441c0c50481c0d410030714890400d0328110411010700b4008800c0c00d1720301501200840080c0b01031042c0e070001441d50400044525080d900285400c15072400c0c002400707400000b4a003641c0d841880e03841034402c4d00c42d25030b8840f000101990301410701600580310840100041002c9250b0545c42030044804405070012200000792a0b80500030a1801520010b101060500049005138000c3c40e00410640c00c0040c0c850f43c0c4012000108085442800e0500d40701c2600180a2104600703000c84e041c2201c5910f0301c1c040300c500000b0381c60f2040ca1381c00203000807000ea0700c0d036840c0d01035440b040040c80d100c01062000100a000482d0aa009140217482240b40540104840c540d40094072404081a001545412071700380715a07003180b00090034558403100007200c080000d0428001c1c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 218653929 1250 218652679 218652683
    0x6110c040e03031503012007051905030c06010902030709230a0909060506031903110a0209010605071a04030509010c0809060f030906010b120a0c0e030627011109060a120603 76
    0x1443d00c030f041008110301107844138110a4400da052805030152010088600049070b1700102d038446c2e85e1403a511307000b803c00c5da080d1004280440784900060600001000411408a040c0c00303644640ea22800710604030300044d40d0210007d101410280280103a07104c0340d9a2150304072080d03900c03040016000840d000b0b000e8200d11300d07094031185041c003002582c0c0681904900204c0141a00e0600b019004541700110300300070f000c01810441e190344140b800d0014140c07050b00901003c42d11343c0c59100c054020360001d0f40455001c990345005490b0100409030b618000d030341c036076540341c0307400e2140c001101c210014660540b03410808211443c15a55007070014100700940904894407440e1004007030381841016441a1b407810405c000c10250240301154240d8020007504c0c0006d801005440229400381030504100d800d0300c80c074001c0c04910480d900240d5103a5505200501c078841d180c0c001542a07d04400e0301640d1400b052145000505e407800c00b410140600b440e014451810040580d82502d0301c1e40d0007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 218655179 1250 218653929 218653933
    0x6190203040f0807051516050307030503220506010911040801060f0306061d19020d1401080d0c1a0a0b0d06050103060f090807120513090518011506110c040e 69
    0x4108920100b0710304980081c01000054651240b41101080e0f04403108084810541c0001803841960184602c4d1000d1064101e001c0303d440301d1141c1340107004e541c41622407017640ca103124280d002c20321002c0207881d42598060042c041c5a440d0800c2d21015203411260b005c1501000e02001c104924248100801441034002c050100c910790308018040f90003d800440d0041078610160221200405100341c0120703051031484400314034288550000e020311445003000a041c00000b0001d2038511150714140c8480e903080d2006601d0207001600c05090840f4020305c1c1141101d075000010644c5580a07031700207216500402c0d510a000009071110071a024100c4049070303a000148140801c601c116506000c80d41000c200d09402e903240c914131402552001041e0182e031a0b44c41030045d04c680181c0d10700b181c0500c40001c680d034840600e0000307030008075101d01201c80c0c05200840c04040500a03410b90f8180018151500b80c00c1c400121f0b010510316503490814442c0c1507048020b80c0381d92144602041e09000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 218656429 1250 218655179 218655187
    0x110f03030f01080309010903033009021302030112020607051603030801060e06040506071e02042d150509090a050a060623030c0f0d0503070819030603170906190203 72
    0x15030714081e48410b03048568168030034410005c3ea80d800c0108003048d40d4043c1030509200072110740c1104c0380c0310041d0586240d40c0d5880350320021500d054100c0340707555108640f00443c88121103c500201c2c04244508003910904643c1c00c8013500340100141001d50140040d6840f403110048001d0618000e540b00f10300241c601c1004015166000c03250152006040340d1702c518145c6003000103078603402828000340250014280000000d4090358001440e581d000d0010b0000c07500130728200d40b603554119514803c0c01580d4914400c528014421200030220400f680000d00c0d0601090081c9244010304ca0b4110388207040c44074000c90005c00000e18128411140412400d080c4051b032154040300e042c586096801128819016940100c0c44190710030301651541880002c42001481c0852801405040c1303000000300c0a06029030007009040100d201c44c074064041d41c042c407040782210000d1001419081036504421100b0100200402e0103c2000b050790b800c0900540c02180c007120341040040150740001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 218657679 1250 218656429 218656441
    0x503070b07030206072609010e0f0c03070806040f12110609030a0e01080906010303111618050105060304050c010503180d030507120606270f030501020a03110403050a0b040201110f0303 81
    0x40305612101525094204910082406c00d140c080309260070342c0901e80400180d8010401d50107041201900d104030303107414080081040d10358440c0c4204500034020f200c40491190400038560740510360159406406074819190850300135161003400041000094680030030407810010320340108130300310241d0343c3d40940c0c410107800c0d032451700c0c0c0c0917040c45210001c010b5420301c0854901c0c112501414114400045045250700f052941c010420383d9500b1840b001c0360030310321034012015550314244100303c0d590f00c1d80d0402c00140003c640041044d0f00a0880c080f40b540700780b000c0c0d40c20098013204c15441d203882101e81402d112100d0391343e000280c1e0301c03810440720307a038001842e42c98070404000400400b818404010301d84001e060f071078103652030300705001d900c802c0b0004d108100529841283c01a180d4403840c095000c0d6101080c240000f074100303506c140326401c01000301d40403a41d00500416480c202540c8140a201c40100103034103000ca0044004504242400441588289a40a5980c030303d060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 218658929 1250 218657679 218657683
    0xa0803071107060309080a03090203070b07050303010801060902040f060c02130f02030f01050108240d08040e102c180f07050916140313060f0902100206040b01140a0503070b070302 79
    0x3e6105008050130680d54002084004040301d80101141c94003081c0f4080301d0000c40d03c2c10041ea03118000c604800204c503c1481300101c0918107030f4140304001d108456a83c1e00c3c00050b8001e6006d0442c80f0b8400c1c9800700f0400e406804102e5401d44040c2403101d0a81c08a07003090100c91094507003000942d0000f040204074a1640852400f41c4400d00305a003203801e002e41800751903a0300c0c469072241e4000c2e03940c20360801d5580500fa4294280e005084656403900d610380540401c006661a02002c1c80180c0d010a00c0f052141e04100d01c0c51890525140850543c081d03103c8407003014140444100074100c41249411090240601d07110040e0020007920f440c0c1402d001c1c480c07100802e11071024120405492060354800443d4a55800b0110b090381c0b00c0d00c0d4000720903d455080d4500810b403600d4840401c0c04054150000202280200c540091500c9144001d0380c440c081228014900140030005100c044880b40d50840c0b010f03c09400058095102d01c0400c2c036044c0355404c2600800300100ba01c204142c0c0c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 218660179 1250 218658929 218658943
    0xf05040b0108040b0a02181f080f010e0a0209041b020105060a1d040303092a15050a2114130b13080418020d0c090e15010e060a020a08030711 62
    0x2071070014258a010b80b100c140010014207900c40c0325400050608280005040f0214551f20060a28400c44c180036510000b0002d07191150000c13606080001d81181403107a20302d8100c4000c0c18071050240d1790400c070700c0000d5101e8982c0030361203a95901107aa04010301d4251400481049c0c000203000d0510300d080006d80c0303840c2c0d4020075582c2007024007003080d43c10a09407160407603814100031a40c00d582d45404210f003907609400405400c2809159501128224800300464504280d010728448206504460307511a000c400c4010440c00702d10358a00441011066005a031600400a030b02440004140c60b44a81a214010070702080d808031811b115a081006402001d158086c80e80c8804c9a50341c111107018900c44c40c0c0c920078590481100c9a031190f011684050003090080000403280d0401070121b003500d0141c880c1451580c0002042200c0403080c0385900081611031485c4071040a04104141e805040b180c01107005045e210b000148030040614050303080b5803940311031010b4181c001031030040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 218661429 1250 218660179 218660201
    0x4181208090304050a090b24130603020708160c0b0f09100512150420070308181207060603140607110303040816060b030d050904061202150a02070e010f0504 69
    0x104100130000c656a034181c9030120741c4174840104400d294400040c40c481c019403002c4401c075921454041c002503109000b0485000e80c161b038000e2030b5031211000c804a00030304070300030b2400790200054120002200e5141c203a842c0f00f21144000292204c0c1c1d001d00c40c1e0441c800c1c14481c6200862400c0407486c040c651008011050f180070b908298503407510519543d00030740a1840c52040105801c0c240d10380e50084040801c801d100d1030365078400d800c03101d0341950146400768000f0380200c1c0400c0c0c140184109070380c0c9a40007140104041d4040c0d0304150700343d52000743c0450380b050791900000006015041506a41007211300a42030600d45003e0282c0746c0d900c2c0034055540e94200304100000212034109441c150050340381502e80b81e850310310304503000703115501c0c40b1607242c0705031240d8461044e03109000703220542c0c0c161014003d00f80e6813410464043d120400c029404140c58842d07103040030080e00a0719142d0020f10441e009603540740350419200c2e1013130b04002200b50f90460b040c0580e0416001d0448952 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 218662679 1250 218661429 218661433
    0x4112b0203071e031401020903030a1e030e031c0f050702010b10030509030a0516020d062405030303010b032d06011706090606161e050c010207080c040207020418120809 74
    0x3441c3c06a00d419000060000604500c0304010071070b00c5580940c141c840110020b41103e03511a10020081c2418440341050080440455505c020f214401d00500c01e0701d14450005500741480b00c40d520b085c450ba01081c00001594038051607541e2072042c050b850181459800028000c0c00300c0c0240b003001c0f0182c2c1e1403a4145410701040c40040c0100000f112110101e501c5c0c81520790100324010500e00303101c0300c0e01940c0b14409450710000d128195102d03505440503041d40004020160007100d142c1c07003c600c50036901d90010300041005d003101d02c0c0190f601c07503281d4040722000c0c1040043d042d80724103081e80240014030706004005903540c220303e206000020100400200740b5100000540070f40e401003000f40911408595050a204070b200248004ca910070203100b040faa8034209031242c4000c0010a0361144105080c4407250350010445030700b920920f4000d0042d401248061101030743c000d000481e04656641800c81d884080c050f000c001013442240506c4004a16120081c0407a40203003a110560b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 218663929 1250 218662679 218662709
    0x103051504050307060915020a111b0a090f0e0d0203030105030105060a14121c020a060b0111060103110613031a100501020c27070f120c050304112b020307 68
    0x840d0000040d0340d030301c5604c03c5c000f140c1c9090524100e1410007122910510301e0317002055900e5071503001002c0d880072502d400f045402c8510030850030501da40c441400c4940029040b0428089101707950005010001d052201003402812203850038540ba01c0042150010313040071005005528081c00750303d8100c80100c0751100e125040488400748854154413080c8203000300e00c0d0004e40710000784860300c0700454854450060649452010f5181e0a0b046000c0b030b180d503d89540c8040d95801190f1500d801007400004000c141c0c01c56491010383c44200600f0350f8080390600500d201c0410300c00d03081c0c000d1132040000c58060503c0c032406511304100a410f1500c10b28123458140040e980c0050340d281182400c031903659950f4503180305402000c10340c4446114841121702001a543e40001000d88c008220340c1d6001e131840350501c0d03114103c45030100c1240000c1c100704046401300303c804008074899840186000003540c0d04500e00b03400082000c05110a1006907011001545001d100700001049404800780700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 218665179 1250 218663929 218663933
    0x31005010305010311122503021815120a06050a0c0e0a030203030a18030b0705040509070302041202060c012c01060801180605100e011215090210120908120103051504 73
    0x101160b003905d26402480b088840300a1110304104c000d800702425100d0a84a91901104c0b0301500400d00090b4080d00151220001a070100d010192080e409840410340d408045820414082000c43c075004851145100071030200c0d082c0c5c461180201e07034410002410064a100140c4024140c003200c510070b142c1c000382080541c50120444102c0c1040c8e01d0114210048185000150216504090001060003041068040e0402e00401c195482111070f6455a91281c10407400c0c4e1040780181c1c1903201002c4407101c01402c101c8041c241c1042000d00108042203030b5410360301034100c00000e03810340107160305041920b24028818800909800c00080c00750b44004c00c000b40c08449600401130403255a00d00161020341209a0400501882e0b0491107103075940300059082c0311581c00040d00d001504041c4104910424890090b000740c0c041e003102d1100382204415039011909500185500d92541e4001e00040c18080041c41c0050610388842c0980d41103060992400c0c20107503503001a015410103003c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 218666429 1250 218665179 218665193
    0x40903020703110406030803090648071406060406050105040b0306060c0c0909030a02060f15121009060219020102090904060510120807050c0906101b0212030310050103050103 77
    0x182c0c1d8120078400204811240480d0061021354005440501d022003400a00c06c0049035490180c100d401c9029120581040003100300185180e02505500001150000c0300000610b8003641080c030302800350030131075a42c59030041104100300e0300015030404020801e1626191195202400085c81c01a0815003400b401049921010b85a42d2040c24040b4843c0d80000c0c0800901c1e150a20241401c0501d040400621790f60380c115802c0301015000d200c00040135004100d00142c400e02c1c0000361f8001207011803052060007000352800941c140070b503c007101c0070034500740500400f01e4450b0b000160780d0000d000311405120303c04c8842d11308590040064000d5980c0e80c98245400541084c40000d450325016822200c010203684032032941410000b00e4003c3c170005202070499a40150243d6908035601300030405188421541d07035901031101c103001500f041c40344441d2000003400110145000352300350002486c51001c843d0b08100c5500003c20820040e88000d1441d000702000c2c00c0501c00c65040d5a2691 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 218667679 1250 218666429 218666443
    0x90515090d0516020402070f03090b070206090904031e11120a02120c0c0a060e030c04060e1f03080f0a1101050903040e04030522080c03060c0912031c02030105010e04090302 76
    0x700c1000000302e001460a218284001c8000c1e07401070003150382d220a460007250405625406901094902d600010448480c00440e02c1c03043d0700404162600151401f00300c0c0420020780300b44e040100c046d005c0384840fa9510b0a006c50010142c4400406003e134040d2036150000c201d0004c030714501d05002207019181c000441d0100c0d904040d0002d030325002e200009602e06100a40002d600550004000428542180c0b02e1140401e0550030743c0c115030800014401540c541d4802e60b011281d51200080da243c1030342d06401071020120b454000100d40e241c43d0509150821001d07490240c000055006025410102c266140711861000f880207181050b0101d44900035882100a00301c1c0740c10000d01054402c1080304c201c0306030f10050704e000580391880b1400e10081801741d40700e207102e00c641d441e102d4900000e1080c4078807440104a0b1400740b80b442440742c0e403c1456242155880f0500001c0c1201c080300300f1070043c00c0e0b100d600060305c3e5898a0001020042000c41e038a0046140007050720109502003002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 218668929 1250 218667679 218667703
    0x19030e190f12120b0d02090424061404060509040f0f3306080a020d1202010908071109060d12080702030f0a1707110d03050406021306020109051509 65
    0x40c0d80c203110a41003280300000c8801d0020002a07101540c4640d090308070000c1001014040c0c1c0400140e125a814004c4410074010045e50100400300010300194542c500e58912000030a82c041d10f02e4043d801800c142c03003071604950303031491460000388000d05041c800c1c00020042201c0489590a00381c0b01c2007811501c0380005800507610594280074040c0e43c000b41c8001b40100030003000c07604842505011070090001291003440e007170407000a0154000a04607100c0c03600241001241011903803048146124121000195525030b80d540c000b203840b10026000541c0940c050302c00080340b98040294022009000a1107142c02c40360710340101d400c403250050103449500700400c841d10340c0c01c02030380340d0300402d41c014040610005011002e0b96016110b0a00400e03c0c89a00702c440d107905000359100d581e484a00e000682c08a810b0000062081c0c020307a400a008100040c600140c640091a0145c000d402c0000540c0d10703107207840108001080351100c2a4a80ca94412031801c0000c4550b032500c418981e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 218670179 1250 218668929 218668963
    0x80a050402030a020a0e0709080c0a06030b03010e06040803040507120b0609130b010801061d01031707060f0213060f03050c181507051c020a020607150209030d020319030e 75
    0x10219101000f0300c81d4010740040c9050300482e6500001d130b0203284110b5191001800300f0b48005105100040d4162405900400b0408800d0426400301d00801c400325100742d0641d2250f81046400c138051041d03a00440c0994202a0f40f8a403d0408600e04802e551000d080b14441800780d0300814400c0c81d81540217502125810a2512100c80c1c900800c00800310250403500c2c2440005548801548a00100c0316050098100700c02200402c0c0004102407001401d800851151030368042840c60040206034400d600006480c01c030000d86408a0b0040744e00e88000c0b0420707810600034107810880560b48907050f8034081c07001d4030748614500d4440c0507401c40854081600100803000380c0c3c0d40c0540400461b03200c4c052640700c644500300281d40c1d2511070341403144143c0105010491520100e00e980003030750050885031074509940d690300e590043c0341032404007466080c0190340c09940c1c24032107017104030829801141c5500300d6180c0ca12441501c4140031045c54504104400203000c0030805c0c9041000d1414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 218671429 1250 218670179 218670181
    0x30e03011b1812051c050d0f060501030e010b1806030c06030c0904181208062d090c1e07030315120c0e19050709051002030909100303080a05 62
    0x101180c0074002240108a865000d0304801909960101c1c034250890045140450480c1c1d40703a0108480d099040400350141e0441403172070402a03624140c240b1244240d1030800c3c0b4000b1000102000c941031400105004c548541041125690600410100c2043c80008004081320500004c0401200d1003c0101c020004070000d001650280080403030307858043d00d0340e40d07a45010900000698010b08109220718609050802000909240060b859501100e010075411405400b6244100b004004036408203036901c64144204090750000481c0368802c0350480c3e0b43c1075101c04c224449900500301040e0b44401d026228989020001e102b0b001c1001c22000c1c0d07580c00013402d044000c1c1c0300c40300c41620407180301c0b00002008102c2c489140405d0303006890701d241c001d4032440001c1058006070303068440182c81c0d201407003500c0da10760300480d01701d26075090240546940c0c00110310b804143c20614400b58002150210550610140c4503602c180c2400c80c440f8000c1c00c5540c003808505c0f01a000e450f01e035544030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 218672679 1250 218671429 218671457
    0xc020c0d08091806100206090d08090106030f081804020a020c0103150b0301030b011a0f030a150312020106080606060721090308120106020115050a0501050903010f150602070f0b030403 81
    0x1411208042c001030304652403240b001d20883e03004030050341c80c02d004226100014908034400b141e10343c041c04810024025a4505003411110030340060000117132950b1310400000002e030300f010028101442885083e440c0d10b2080d4071821140e120b51505401217004222810403981d003c0340b84403501c0402d00340018a801d025190039403080141d00f013214003010010010050260303c2d40510b0480d810300004180701c140d818040c509901a501e00a9090842880400d011006941001c000ca04890a01003040d07552611100110003103602e00f180540d548210030b02c040b01c0c061000941c0144141c0300b42e86485182d03a50306002400f50b0020402d064a80d00d00c48002034411501080216088141141c5440d001440201803020a10840b4003561030504015042c0c01d081010700102c80008081d050718034034100040d52643c0c02150200e505550310841030380d456a581c42500d11020703814054100145c2001000f034074004040d00880385500c0c40300c204200b031003496022a80e2107a85803414402c810396907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 218673929 1250 218672679 218672693
    0x16030b0a0e0f01060303032406080105040f02070609030503060a081f0e030708040b04140103050603070303030b01180f290f0f0f030702012c030711031507120f0c020c0d 74
    0x3054401220f5003841c60010915900d1703000a52003990783c600811f600c107a034450090140107284914400305070107100420032440c25030701c44a89030009000152524481e66242c4040301c041c202d00300d000c0780f4007006110482c100001d6210142001e007008020112000708204213080c103104120401d01d840700001100c001042c0180c900803607000300000e8985442c0d01141d4020340081c05003c042e041c8101c50150958401d000e0340d4000d03507015003e40089421a202200601141d00c00941801040c103000180c28894040070802003081241da00104c50400e1b07140c1c6c078030110700294607420744180104410041c07851811500c0424039002c18940d60001000c2c80189802406e280c42d000c280c0210401000503010b40080e000d1386ca8550b040d03000e01038024045000501e40d440042e800d50310030b0050300d00081620102c60b510400040c11140d143c585400000c0200030200d421400040b41e4007600107049145000e480c0da9507100340000e00c078010b1a03200c000e546d1900c0e14146442840c1c44006a4144450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 218675179 1250 218673929 218673943
    0xb12070908120406030b010e10080703022505060f060901090902030c06040e15030304060507020d0204020f190f02060402090c0912030c0f150103020d0201050f0d061716030b0a0e 78
    0x50a03a10200d1249101d42c20b5070300184181c10210b42401004a819072050f10a00c0d00d49034024800b0412070403c610803100c0442c018415000c0c076900304810869600601c40e00001a4500004040400d240d468071600780800540b11100030b02c4c00200340041036454070051410340e80313290800520f078030303039800024940305100a04e1900000000f4001c142d8000b0480024801c4290303100d90941c0c1641d18084c5a640e12442c41a031001030014410300c401850100c0340d440c1d840780014005810b08003542004607603580305158038105808010180d41c0784680211071200280c3d02c85c00580307414502a00414540c400080a6042c8c800000805c0741c1c0940d50038485405100401c0c0407240ca61440210580e03807000c000741242c01074425840b41c41c0c1c4140502c1d0500313058a0780505907410550840d4019036440e00701071300401c10302100307114100341e0040a02c1024014100e903d60303002803610301d9282c0c6091603820106242104081c00041c070110343c8815400341c100100035400142042d03605034180c10528 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 218676429 1250 218675179 218675189
    0x80f030703140c1b0a2d080a020a2a1710141b1c1e05040b04060b100804030509010306030215030412080f011412030a120608070b120709 60
    0x180d1000740701e0140300220252110510001660503130301ca10700700259883c07a0034000248044131803400e40640200703440310401c0e804100401541c00d01059591502d0a03082980c0150050380a98001d900b40100d0b06450040441c540030200300100c400300208801e000d0b03d01492442d141310f81c0c00184148000c021407886040303211010024040c1410304000c100b2030540300c1d00c080700d80200614078506206c60454860b031842030340e456446000c4c505010041c000300300ca050540c0c0711600c41801404040c1c01541d00c0f4501c40c00640c0003030b02d0035103000411241a240c9003406550200204c80351980c1090080350810b0305410499224212480120301404007038000940001100f000383c02464101c60155024038851500110590071041342210a03a004a403400380700341c0c5281c0100b00174600c3c071074145200c82c00680014040e4880080c0145150301910400000550300a100b0080001358030910000d8045000945892440d081c291003840c000d0f0140340219440400100700442e004a21740e9009207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 218677679 1250 218676429 218676461
    0x6060910270e0f060a0c020a11030a140d030c0e100305061906020c090a020901020d23040605070c0f050607030e04021333050a030e1213090e01020304080f030703 71
    0x5625909090f4807610240c04041803403254001140d0300310700c14059404250810384c003c0c5140441c0c2d44560740300e036440c4030302c858040c017aa40a400c0840c01850594040c01d003040000c041c0040c0e0084010b003107540c51000c9108000021010003400da803040702210342410a49808551903c4681c0012004546848030030100c00f1110000512203030085444400980110703281140c40e0f40d51032003801a03209007000d141c0103800c1204e04401c00ba000380540e01401c500006400c40a507906c5816140d83e5005802c510007098002c0fa06004100005803c0005007207012081e0000350300c1e00021a00314020381d8001418020b40d680c004010341c440b03a050f1850341c0c64520709100c02c2a6541001e040c0d0350000202c014100341e41401c1400d03075903021040703040c4021032542e542e4038000111404400070003c0c801104402e000304c078201c40c00480c2c0440a081099000003041d07000c58540f0090f0421a00c1040b0703601d5943c0d0040c020880400c103900c06441182140f41c50300c0795680e41c3e441c0e08600611503601105000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 218678929 1250 218677679 218677691
    0x70510090302010201110c19050a080706060e06120607030207020f06040e18030c0d030216050105040b01050414010b090409081201140a06020f0d050d0b0a080f0606091027 75
    0x56021080300200c034001e800030000000ba090408040c2c0c0b0500b5002c8010303a00145013004100d0445030601c146902500644002403000d550301003080c0e108003019035546031104420700ca000c10807c03107039401500403100c440000c4030f084003031915400014410710a06038080b80f02d100b99100c1000042601c480100002d5841e600d074940c954541200f90f9421203105818208804981d400008840d00c4203503203001040f91075140c5001724003039800180411145001012444000380c824000c07580500d2052034561703000c0d8101300034001180c1940d0340240507000c14100400070720305130720202d07002440300b61800b103000500c0b400e100307900d0702c240c0e4461007000e0641400000c00302c401c4000c20045850807601d041d94140e541c0c1080b07a4400522200001d41d0300f20390300740d00065018600070001c688040034045820440341000884450640d805000705401c0800c24011950f000d102e40b607030040703040b83e172140f25083c00c444a00c4594040e001d41da02e014110240703244648034400c10751046a100002c18005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 218680179 1250 218678929 218678959
    0x6080702070504140a0e21181f0f1b0b07090f0b090102070b040b0a2a03080915090607050307090b04120c360f020f040e0f01060c0605090705 62
    0x9003c0c412610600450b01e070007011b40055002141540c1680c400e01070f42502e0750b41c49984921980e00604c0907102d40303102910544900d80b075241e9000560b40019109001d610720301980640901c4108858400308000010030090b01c5003460140800d003034001229400d190381e600c0094400b2030040d08052440e111340741b0700048901032000149640343c002c1c4d0943d00890340d155080903c1e03000d2070080d003080314400d0103242d1003d4495485926503c64040d004d5400c400d003980c00714110f6851081c29400110300100308103907400c04000a06410190115130951898008901900c0e40c8010b001101001400030119800300d04c44c54040000d001c091207020364070b0f942c1c1c010300543d445032100201d070f00504168000880c05101425000410b03c20154550300c007151002e40200b2400007000c40c0c000c03da07101580c9120006510151a0f80e44814443d00d541d942011049520362400408100030740c5401801130002c0d07540886204000c0d580302101150b82d0711500e1009090800c0d0307800451704200c0b40152020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 218681429 1250 218680179 218680211
    0x9031b060c0f0d090503010207120804031e0903060612110d03110601140301050f011a0d020f040603021b010902030c1309120f09050306040807020d1e0605010e06010c020a06080702070504 82
    0xf0402c4540f2240d00c05a545c03018175090f40200d40002e030041e88044800521207001710101a4410301c00c0c40c01040c803a80c480ea03040020001181c844000401d546020300421129110740c6000d02100c05020510303c0c02d50341c1c0c091300101030501c0e080c010100706e00c0540800d400345101d0010302c803d4105030347d469a110f000c99042d0300391500c40588250300703050102e0010311340e030400d9a05861001d40341e12000c1c4e501040c10242940042d0754001026070801059108480c00005030028004a940143c1d444110001307a0540c0c1d00c1c030b4614802c00784d1400480b80c0040e600060303804000e16098803000300030788115208400601c44161f018024451003030318102410360220b10103c81410b15280e80700003d49500c103140e6642c104540081410b201041020090311745440f44803003141c45800c03403c0881060700d45c45064034040741e204981035510703040180410311200b00203a030700450a10b4a40e1426200307400240e411031140c4105028841c5810118602c2d510034000d00c0090440588140840c0719014a052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 218682679 1250 218681429 218681443
    0x150b04120605150307140a09050f070f020f2802030f0a062d02130b040314010506180610030609090b060406050603040309030b0a02041d0709060509031b060c0f 70
    0x110581e14002c00521002c00d40f41e02c21910940143c01446060708106003545800c000108103580203901100003e4080c040340115840b61052020030842802c001c0c01c050000d2444d003001d401550020340124030b407042e00007888160b0820010101d48990320040701c0000310041003e01a4140c0100b201000501d00d00190300c100240c030a401c05c0084903010043c0307580b01800d807201a00c4032502c9005080010041c3c1d005041941040f2074401c7d40e045e55016034110a520a41c0103d944403147c00003113442072000e00c6203c2d03000304180c1b00d10401080e005014000b01100030701e01c40c0b26910b080c08002c00d0380d1281d8041070141c40781703000401c6808603504081000b618101d0301107110300d003404d41c00306260034a0825213009951540b00c280074281964dc5440c282a801444945d50540c01d103c001a200d107034404003240c17041c100c00f00088a003056a4001d145078100d801034828450104240c01c465200010314114200e1309590021036450741000142081c0700c0d9100091161040d0412001d0002003c1005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 218683929 1250 218682679 218682683
    0x2040609090c0e060a06080a06080f071e06080103030f020a080a03020c1e0c0625240b060d09060204030f050d020d020a0201020a020d050c090f150102030909040303150b0412 76
    0xb904500d6643c0c042c0021502c040780d034140c00855040c001c009050061641640000380da200100c0c40e2038407003a0b040d1074544c1003e01c3c040141d002c0c0c0c0c001c00c094070f400781c805940c805103240b40c0f2044c6410107030301800700103040c440182004070141c840220305200384840c5608a611105003981c40103070900c020702940010a0510550040c5440c0408004600300495640818000a4089900d0780d00821406401c07a1440f00490a9090740014545007031030040310b44c091040c829412010303201d80341101d030740103019101d00606140449840706613545100780c0e19862445000416000c01c203282580c080e0250f540000e25900e654001c00b0200034020411b0f0360805a554211440c158603050101d82d99200c0600c080c3c05604500e45040160030240d024200c0a4001c034111920102218003080c0d5980303049440c480561104401d102c0d1190041081c184244401d100450901d0b103d0000190894005030005082c5036032220780b004500c1c80e4030702c620000c100b0a250a0b0301d996589002011501c4070100c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 218685179 1250 218683929 218683943
    0x5121501180e0403030207050a0807050a1109060a0306020a03060503030c010b24030a022a011a06070c0e1003020604060c0b0c0c031209010e0a03020703050607080906070c0309030204060909 83
    0x412030040c4500c1c81c10804641c0a40c081120a48503524103400940c409481039031103004508000c0c01040c00d040040841ea44034070700400c00300341942400400160301c2c5144c9072003009400305101c225960f188030401900d4100c2401a52035490b01d800303900804040c1d01c020f4043c0404180d160021206601c485c01d0305506440004007035860f0601c0e4156002c22201a9045c1001800400c08100c025406041400d9680d201918440b08030580410046a42860500715a45660256481711000ca101d10241c01d4103603a054205001c1da03642030404410342c0200c100a00d01540002d2100c2600083d01c80116006417016a4882e1106d80003006002e034030380151460240c560100d900004504115a0017101c41c501031400e00c03000b5125a000100c0241000c3d01d036640b07034000c4c1701c01302a007400580841032190b002003603c140f031803a1583c18600020600d806105140c13040000b10000410078a5101c2400e140c14054001184bc027581c1c001969000650010315098000c034000210358803118a840c05818 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 218686429 1250 218685179 218685197
    0x1106040f080703231b040209220e030415031a091003050115050609091f120c0b0906070f2a08060a11040506180913021206090a021005121501 62
    0x41c4c00d21020120003007082550b2220003a4584281240158100030800400251910b0010300000d103040c000b900000c16814081c1480c010b481040d48580342e280020700c405141031900d0000d00c94002d01141700c200b005c0c1500c0b0000c44190411503c4600140307a002414102d03c5e040c100d10001034041c9a0104691961806805030307500140c141c8210200c890041c09140303082c9030380b8203010560304080c2102c801d0401c0740342e603602c1c01c0108144000186c41d50400c0300b000c8218909001740c1c511155071002425510070400351880ba280c034412503078455040b2070300c6000b80e54546840c4c5000c00b148000300e95007420300c0c0070421809072182000390480314020201c603a1070321540d206900b281d5016035202d002410810041000e818000094180604c010f81c0c0344103804110300200d03c01c0032084400355017018040304001c007149030980301d12030b074981d944000748043d1400322091581c8000c028030280c030818500420642e010b05c200201c4910300f0a0314034240d0641440000b40b0603080035552001d0114001e09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 218687679 1250 218686429 218686463
    0x306010f0e060a03020d1803110c010305101401091203020706080f1e0709080109080307032403060218030a0c050f06120a150512061905070c1106040f080703 69
    0x1001103034100100400242c60940c00030b0060340254403d21b502c1200d581c541040044074440501c585200a02a407960000d0300b5005c1c40d07150518101059503818180381506111644c04000f03c07034000c1d10805902d00f240700c05240016110240a50320080c902c2c06601d40507810564042000000c6078103c0d181c10b030403500e5440d0002c1d0303c0c030b10132100400c000c03105c80b0442c0894514880c5094000303016081101e1015100e803803003825a07a0031003050b035000f5000001c0c8881d007945032045c5050813a00740380c00f03103010900e08040c41c0081034900c40546440c4c2c002c43c0c5400980e5000c0c26280c09618001e00325040d4049610301400f4130406840340c580320748a201c40c02805d03420030380101c44098409101041d115a42c0e0750b0914020400d0040c4024441c054003c00b041c41c0e01d920701641500116400105090310f051714540b5801100a4400c091285c00c09082c0541c05410001030411158481c100400003403510010810501481d803060b92034006504002034841800300b4800252170040c2860b0000c01c03600b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 218688929 1250 218687679 218687687
    0x40902070b0a06050d1101030b031e1902010c14031c050403030b0301020f040e090307060e060a0e1603031d09011d090307020108041502040b0a030204080d210e0f01110306010f 77
    0x1132040a80201d0b1031445d000000303034105514680c10380c05060010f02150040082490180c6c0551503610281c44d5002d48081d0a004002102500201d0074a034040b000c8150f000030300d0000244d000800201c0286c100e82141c000500a417160f01c4944c40c50074030500265005e0002401085c4d80a4011074a4118000300301d003010300880d4460106444101e00d460f20b020032440b400300d001488540607000c284400800101d03070f4014040026070321001040d0a04110801c00704650281034143c070168040903a08084064039000001182d405040040050302c05000403500700740c89103c030541c084104000400c2c41d4841518051500401c6110300301d4503035682c244240e0724820984064040b0b000880014000750b84c15800b081c0c40c0780d05a00150601c0d0341c0300310460481e040400e40340042500070600b0b2050240402140c0a641307850700d04980c151062070130f403e100b0000320705021354903503d0307100d030070380e422004c025030b00c0c0161340710000300515141c945200f01e081d0401e503011400510801d05030900c05101d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 218690179 1250 218688929 218688941
    0x503090105072148060608060c030412020304060f1209020411130509011d09030d0f05011406180411160804060305010807060503071d0306070806040501080f06041209030503040902070b0a 82
    0xd10200000b0001c418004601544c161000701d0f41c660702e030b850110f12281c3c00e02c4110301524881094035201e04240c03601390100304540030160110750040c0003c014080d401221609511694142118181c0c0001910390140049601c00f82d0007030f0038901f940c000c1c0384121000f0b0800340e0019007680c420b00d85410412003141020b114035207048428010b0502d042d6900c1401769003152846044900d010300100d903000660700200c10301c035401507441c1d004204180105a0100c8a08801c84049240981100c8082c0d0120640f0b040030b4081c56030340080301d0a400301c0700b0031a1803013181200400c07000b04080c82c4c65040d0703034814044c140000b82230000000310b0383e0340041d400e2706440b52512013a01b07564030038108450005a0821906001560148810f41c03034905202d07480c016200c50781c80d40c1c4646090024041030340e0041c1d00240440d8041c0710742054000d004038100b904158000e5100015542d00b900484501794203401c06032041c000007800160170b0b0f000398028091035220701c10070300083d960a8801411030755 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 218691429 1250 218690179 218690267
    0x130b0105040c021b0105041d010e0a0c05030a0528020d0b060c101a04050a02090424030f02121c030b03030702060313060608060108010c0210050405030901050721 71
    0x1c0701031360464441c50141110501220103142c080e04040d1354102040a1140300b8001d51640301d6514018003600c444500750b5a4484c030300703035818044802242401800752000030701d0070a82c0399840000c2040e10340c0e21604503d508011030844150868003601500080d031041110106451070140782a0b2a0f050000c16a0301510812000e404500a40c5070050301821450003046440b00001050386956070312445068000e03040381c000180c030340d0070903c107120442c0c049120b2034a0307408540e000c1040c0c1810060f405000c0c5c0e0344c00354076002e1518080c4040341c2a00c11401031480c45004441461041302c0c0001810380e0110310650702480100141414140c507482a01e60194110f06c0070000586040c42100240f5003042c40340a00040040d41e4004040c1441c100303821003111a512180740b00842c070303030400c0000c00c41118200100854141030340c40a503680300795800181030110118003d014005841440c5990038041d18100c11030805485000b041042d5003148040c3d01c81140940c0b414901001c1e00b0010205 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 218692679 1250 218691429 218691433
    0x7050301180f030f0c020d0b0403020105060901210501110d1b1d090c09030105070e040e01060f060f0207080106080d03051f1a070f06091703130305130509130b0105040c02 75
    0x12030b151021070364581e400c0c180e4024030000341030080058880450600d0400d0107900c0d001900e0a00385002420341d8005440c103445440c503080140a0a01401d0a1000303244c01018801102d5150340b0344035026140e400c0811074108000705032006080425001582592903e0030b909901641c074074425a030714070080400740f03407440d041c11100a2609081d01d6150300546005002e03814005c0e1000020b0941e5400c0701e19100240710b44a030322850703060501031624110b51000c000d000150800d104d600495480340f15004c1080380c0807030840560b40c0248a02c0001e01191030092003000c0e201c035030f20741d51204107003843c00001c0d140c200010080300c82c0c150220301c540651241000c4240c90070b00c03040210003944003001c09140c0d04100c03100000b00c0350303008901711720320404003c5003c0403141080004094000e003503180818041080160680742003118058080d0304d41015070b1904510801c542000c0016086150406410b606104e0680640d01c4800e2403d07208155115180c1c0c4c070303401800b06485455140402517 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 218693929 1250 218692679 218692703
    0xc05060a08131103010518010606170a0506180130030e010c0c150c110a030b0a0f090609030c060e1617030f030c04060305010603060518090c0603090705030118 70
    0xc000d201c0c0080440d038010401012004500f80001c0d007160700070b0303641040d800401446401610030a000e010000d00366800c20710300d580e04041c00d644000e103005214800a035900c3c0e001461036620b444003001d80f510740d07401d02080c641e1600c0403800c0107518400001c2c030a130343e6000c4250170050001c00384050f50b0f81c1595101c000c1c1135070703000640d00c1c2e030803076841124880070b24800131a0082801c40d11420368181c0303030303510107120301282000c01d440844440c01c01c0c020390460304240f0226050036583e5410200d44400040c0e02d440110103140144610030700100b200e0305041e0040c081c180e02c01080d40c099402081d0810001d0040d440e5107640b607921f0a1b100356092034224007040407590b0110101103147c00c240c1076a10305044035101d81c1003940300300e8480c098be42000c14180003980c0c0c58418203014040c1400d0801078030382000e0004418610035100001d912901c8000100e140e1028000ba0f80c80074406410384c2e40300d051180c2c10a46071000e40c000c09009620300701021508080c0000c8080f155604003002140d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 218695179 1250 218693929 218693941
    0x7170c06160b0603010b040c0f08060612060120160611060702100c090518040b10060801050f01180303031d0102091804021906020303071418040f090609050a0c05060a08 74
    0x280b2140148802c0c1c2c9556079441a0351326480328042c603002c02c881595240e00e40101c5007005480d4040181116002d21030a21417560454200e60300140c210740b003424a40c0055000360480408a102251190328a01442d040059480700700f0808000b035030815110104182c200c1403056a8821781194200d00503031020810318a0044150300c00303010b1840340e01d4120119074803180032035607525403181c0c40c0101c20740708020401404800300860382c100d4600c41c0d40c0c002880c0b0b0303d0402050703005e044c05103601c20441c0d0b4205141c035a00544400040b940c014007040d40d001d1f0742c1c2c240038004200142d0b4070700150300c000c1c501c01500071043c4211000f0b05070044c0070070140c0312100e8a4039448180108100d07000019000000941c0da100100032004050581c020366a915125000912181010460007107181c0107009c1110701415841402144d4038095500103098107210042070041c0c0004107000d8000c502e01003040c02801004141c8040c0c2a018034520300c2c445944000303021051050400c6035001035900e01c049a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 218696429 1250 218695179 218695193
    0x5030409050106230a11061005040b0607050a02151908011e03050a060b06120405060403020106050d050d030509010f090311070b090a090203061302120601090f060c17070507170c0616 80
    0xb002441d8545880741c1ba940c18034003460710409031084c0762000c032103041c100b00d945490701510303d84030b009441403400d0200d25501e4075510480304100074801d4000c0300507142c41300311b0766003911001c22544410449a400035800940b840c002809107040012420100b000c58210b2034003601e044130b03801801400c201095072590001041a840c85545c844410460f107440620f4400c034a5001c0e070300810290405081c00c0c072740642155100e5100e14001c0d815051120041200491452024003075400e010841e540d40307449450040c40c00e11124040ca914213050203040c10b920213209007109943d18202c5845503100c00009011703000d01c1c20100ea00c15050030341445501c4154001d1608210040c203030107010380c07221a03004c0580e0003100040742e554540c001003041d207683c0070040c003008207400710031a0180341c14420700810041c402035029258140210141295000c580c2c12140d090b50803d0aa50940b030320f0b000341481c0707003a4a002006d418440c0d04000d4401c3d20700701c1c1c221740d040c80c45a031b0f2481d544441c07942c8800c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 218697679 1250 218696429 218696437
    0x140f07020d02061e1e010f0f050307140d14070b0c060a05010b03070f0c050102030406090b15010e010302130503030d09050d141204050a0215040510020609060f06130204030503040905010623 83
    0x2d61410740015100c3e80484d1741d00f00103030181c851030f042d40342071909000b2861182046640f1840c0f0a501020381000030128900c2000400c0009030f568070781648040c01c14800f0050f594004010720311442c0c90005240d2100da002d08210040141074644d50b446100100701540c0084c02944038040c2e081000c141d6940c0105403000034140c460402030380781081750302c6650890b042180d05503401c98590b02c20b40f04215010800f1640300006c51854006456641e000a10700c02c0745a2a280c1859070008542d1812001c4150190007010010216075031255103a09070809403d094104071620b216404070035000c240659540303034040558408190070501d0b00d042010074510050001c1e281405a804070001580300c140c1c84058590a400c0000d54692801c020310018140d1685004210b401010a000c4080b0303000c078a2076080180609286004e8444800007201c8041140d040c3e03440303500c0003400004004001c0702800c01c85880f0701c3c041000b0303030383c2d2801aa103062010316082e8410000000011484c01400090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 218698929 1250 218697679 218697691
    0xc170f090703120903061107050a0803132004060f06020c101e0c020a050409020913080f07052a03030d0e010e0f010f11070b1306140f07020d02061e 65
    0x207807516035581c2c40d44460003001c0702c000000a41c00f181d051040c80803500031075a00c0c030b5100401c54945441382d180d640e11041d01440c01000c415001000c1603a200c03d003007500440642201c19008a1882a079042d0740b100003031507581e4040d600b060000103001822580720401c4a1a68010f00316844444003000020306184445e0414401c0e0016500e6107241c101101c0c0881078985c0e1240302c08070703546004002059032140d0200d0f01c02d03414030200c41d00680318030142d560004112040008100468074042c4214042c0c3c0100703e49500340450782c02b0511600142045008040d00d021014030f241158801d0740c02c660b0a00300c0c83d0154010040b91345490050781c881c0020144c120000210464401079241c00c1107040087c4196a0b9116510401801d6991250310301c210702001032036240072440d81c1c0d510240d80000700b00c8000c080d654940c000034082e0396088402c198120200d019880d02d0240d540c800c06807800d4a10000600c82c083d59240c9140c0009100d07802441480340542030000401038035811100000c0030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 218700179 1250 218698929 218698933
    0x3160905130b04030c1b180b0d0b0f040c05010806061801020a0503030c130504020405030c09040c0e0a020703030b090403120c051b0c132702120d0906030c170f09 71
    0x10700046180d04070a140a0341c429981d200d40741a80f4280400046492012040403010b01c0d0007c000ca0248070b40c1079000c0c15044a0081080100c0e0740002d00c1001c2114805454003d01c00108a40c0c01856405c0c144214418012940030036210750044030100b0307080300c00b503402c4101000691141c400010010201d0798051040301c1840700f49a6070981075070429156003d00c046d0210380c8501c80c0c04000c200401074a07080c0e80450425181c00b000941c1c80703942c1205280280701820105050054030080e0402511040b61800410304001010340025809003000b82c00180ca0003c0110081c580010210b00454055407203040e0340800303103044c0c4001c0c0300394000c44052003010044030b40345050368101000340d404150064040481d1400c284400d2504181d085201c0c1440d0894036041e140e907445600e1800d8400001091f080100c3d417000c680446140d03496100e50b07214100d404201d580e4000c0d40c010945c0c2990b0380900c92803107125420350f850300c0844101202c404032900040d03d00040703002015809410801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 218701429 1250 218700179 218700211
    0x706060e01060f030b01141602120d030f090807020d1e0c031e0b011806080a05060109140405060a050628051009271515090f060219020f10020105010e0603160905 71
    0x700148505801000340f0340301e82c01c0000e100c900c0be90540b00303d2070401440f0500b401034a1041d651954148101c600082c4507000b0b03080010305004480480b4448600740c4d505000120300c8a007061078401a10f0b01c1308861480302344171601c0300c4101600030f000185901078818045a42070103150728850003c81401302e003803950b5500000c0e58a40c20052219842d0103100501440d50600e031419042d03900d004a00c4541d03d0f03282c0b05120000300006a02c950001c0001d100050a0b241e1400043e211074801d21928218001c01886030340402c000607902c800c42c0e804039840309442ca0015030039600d0112521542078110100c001000b620042c0d00c0aa043e00c41c0501030000740000c004d8040c5400139000c1e08a400004101c2100d80880f40d0030007200b10140c01441c00b8811031a1070b0400007035849c8420246810f0031341804010500315202d1001c000c20041c001410f40d00f220101d414024024a824801c01c400005000045002d50030042005400f0040e503081201f195800d01640750b01801d805088214000c036644 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 218702679 1250 218701429 218701433
    0x171005090a060501120b030c10090e0a020426190b0f0f13151401150311120103260c0d08010f03030203040509040807060603030305190c230706060e01060f030b011416 73
    0xb0958041500d01d5403254640c0cac03428001c540040311402071500020b030344100414050401da4921010035006c901c030000e088114203076003181c28003c585803100d91101360b100d088420031403050310f19403103001041c00315001c503075030005018044e1009890741859840030003a0300001ca40b4020600c01c0d4158816000714403a40c41c0c51b480135a0a600360f0001d4546110001a400d070036900d80201e4001c0441c40c49054204805209038180c0408188001031540391000f504203500300909504a40094172060000e0b103840c0a40311a0b5110100101e070078001810300c0d4008583c001c07424204d5001c0e640c160f4002c42c102428401803007852400640700360366201052000c600000c5890107043c02551003a580866076041031100f3391504c00c40d802420554505040740305140503400407201c1201414450f00040744c05003441c009040780700d0024050541030401502185024031214100d048a4140d41d485072841110701d0b04074220740c1c0d808a00c6000491600040402411382d4000d44002c11000640d4131001e13480f5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 218703929 1250 218702679 218702689
    0x2d031a060c010204060801060503040c0b0702010e03012f0f030406021303120306150e0f040c0c1b0503060f100506090a0b0705010b0f0a06021c171005090a060501120b030c 75
    0x6482285050f0b400050074481c85038031000c054010109408c2c100c1c11828075030f580945d0280207002d01003140c00042280b0080da17210360076400d402480035008000c0c00c0c4541001e180c0d488d410650b0920724402000c00c40305441ca41b031003111800c0202d1800c2504640f0346036503040c0a5444010f02600d17142940e0350110100f1006403a19007801d80e1610000741c0b6500c1c140600714074103c5c6c400340800380101840085500c1d01c8004100400c03440480b40000c042e01c05001c00d58205600650283c00013180e0048100700d081103203500010380d8400c44c116113040c0d5440c41c50040311001181d9011394003400c10002c02c0503040c6072002e0010070740014211940680c41d64075911103a04010070a8031603070f45418144006c0c1c2013502d019014800d0680d25022001d003001000b83d6102c60445850015201031032150707484d5841030a4030182070602009200c0b6504044a4540790300c1e0b00d84c00b90070720503c2c407080482c1d04c1281c1403207060f00301d807010303140c00c0f10440c601d80703113032008004400a081e01401401c0c9040240e81c0d034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 218705035 1106 218703929 218703937
    0x90510051809121b010f11070b0c07080c0c010e040e1906060b040806071101090b0601120e01020c1e070609180212010905072d031a06 59
    0x2a038807403520700529280b9100b1000e5001c1904280309000f22110705110b04280001d100210161b0854000c07518040013040c15040108041c0c400a42d00f11003455014505080060400c2c51580340e03249542d1100c8524140394008a0901201d5a0886000b01c1d2554060750704210080d8080a0740b560ba4581072402842c80041c42e1401c000c01507150002000b405c043d241080c1c90f00d035205400c40e0b43e4841a250349020034080042d030303107807401c05210781169142c200c4000201d42e22150b0041d107004a030811041001a103940071126400024001022402c442030010801d444248480003010410780040444d01d0304000020000c0035800a0320038292084511485150404440041d009105440070651172007940f80c0005180c220f103901a605c600d44a490368214075024010301407881014851400580c50075841d07a03500340740b00c6e0b4020710f64980c00e1141d03802c0b0203080f500040c0c81904 = true := by decide +kernel

theorem cover : BRFrame.Cov 218525179 218705035 := by
  have h0 := BRFrame.cov_init 218525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 218525179 ≤ n) (h2 : n < 218705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
