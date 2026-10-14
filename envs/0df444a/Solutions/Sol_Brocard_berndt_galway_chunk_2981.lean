-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2981
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:59.151799+00:00
-- url     : https://prove2.me/submissions/e4089a35-5b82-4460-adff-1723bae85741

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535971223 ≤ n < 536151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535972473 1250 535971223 535971253
    0xb011a0a08061309120306180c1202030405190c090b0607030215041b0905090c03061006141615050702010b03030d32180a0c0303050d1d0f 61
    0xe403040c0034a0340d01d07854191510002c2141e20020120020b0100b56111070000c0000c00c000b580300d521404a13240000d0240c07130500c951201c01310300c0402094030762404020515254201d031000c12822203140c030041e00c1c0d40d640d15000f403500ca047c1011640c440c0c101d00d039032820060313000c042e00103668020000340181401c0d0414044035005442c401000340e00211031001c5100b1003089144e41c094011404424401c00700e101401824007a900816500d680790401c10550180402841d050150180c005200525046460780c1001c405401a1000c002e00c103c0b01e10407074203039501614089155080c201d0b800552030720b451007126120358114032110b402c010000703c540c0d0041c89001030440010300030b18500500400108002c000c1748a54450a1070031030001200ca814030500d8004202e0403110403041401d0010141e401c1502119001700303190711482070000082e400407129400c603a03050500316255041001007070041e00f88011490840039207450462980342d40040d4490426107144150f440301500c3d8404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535973723 1250 535972473 535972477
    0xc07170a0f030b090a020a02070b030a0903031b050702130605100507020f010207030b0c0901020a060608010b031018032016050f030a050c01050309120715050c09031c090e040b011a 79
    0xa0344d80f110512000400c030400c140c00800313030b40c0628416910201e444007403036074840d0010750b900c210b250740e213040400c10140c25104030242d8202600c0c0e040f20744511034500401d01d00c0f0320170b4000e0040020100100c201d07421504400b000d4000140700b040c014806020080240c5c1140da401e0b0301c242d1000c105100f00d5400031843c1700540b81c02222035146a03848444102e4598400c0d00158110f1003110443e2000c10028032880300640707401800400c03042c1d020410503107011001c4d0b41c0010501d281c06107092120320043e0b00c85030301650608000d0385014a01c60a0300b984611610303a16110300a0540c1d44941070440071030131f001d9071401c58451469008880915940d440310150040290b40031a58501041d800740000e160700c10b80d501c04449400041c9035009203240c2000c0000c07100100e1201c0030300000e0b041d0f4080d0a51100755080c0702c9040080f0340300069a00c2480c50b24001c086900b85814210310362080345c04201030030b42c0140045186c14180780c0309944100034441c0304124510403025a855440c035400b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535974973 1250 535973723 535973741
    0x903120f0c1504022d120a020d1b06050a0207050906040612060c0210020a05090d17120f010504020703051c11070309230315330111010608150c07170a0f03 68
    0x4520303410690010240500420600b07906d4030103215850090006941d5464910320891180a800e400b091894440c1d251500c079541010042c0441030040340136550780025003404440b021501c0404540f111000305d4000c0c201504004088056040130310305100d8107400c101580d880581c2103c1503d0700f0501c0c800c080f4007614990800003130007041300b900c840c07908031040c01e080341c02080242d00c5085100c1203420698405003014441900800800c603040f550100c5003801020203542c254a000665a00180b00b40720711801901204125811440210310b00c5d440b43e68029084111107503200018140074004100c14420003d600b04020f9441503003d01c0c0080582d50618044c0040c422500c0d00000849480070040c1031460b40103541346281c001d640300c1d07000d000781c2142114190740188441400101030101c5440030b005584e0400404009980c0b00140c851042e4910044138003a5441d40344089000d80f01d411006420f019500740c0410001e502d040040516a01c140c40b103110700b41409106400741d80d40c600d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535976223 1250 535974973 535975039
    0x40f1a042906040902030f07020c0904020904060507020a02040c03020c10090b040201110c031b100201050108030a0507030215090601061803111314011413020903120f0c150402 77
    0x1016424980704824044090341e50300501560402c4d450341d9154080340c104444040d08080e044041c854120b0b01400b00c0b901070002543c1090151a01d0f8020a9000700042e00040049a448000a0b0098800c0c4112852030354001d2050100c2080b40b038000700a900b0516003040700e806a1044021541504c0c8a0510999803144404605607190340055550a207000307a1030396903001c2c40d000c3e181595000d09c280400d4500306500c0c24040c0145100380540300800241003000d40e0314100041c02000800825140321210900d00513a4a080c6450301328244441901080640303542030f8184491108081803550682e8519590200085140c0d4090a0400203c2c0310150000c2100c150030030007400c01d450401d100348000c080c0842c0c0d030b2184070304442405100f41d00c0107988052078078489500c6d251000000840a00803130095080c04443d0001030b4803505205840c2e200c0e4100064800580305404040c2c40000b0038003001da61a1030702407086010040b2048604903c1007008540c001e01c46e1036048000c80c01c0794810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535977473 1250 535976223 535976261
    0x702011b11070905040f020f060d0f0504060b041811191d07050a090303140708030a061724060a0f0f06090f1d04050c060703030b040605040c02120a0e040f1a04 70
    0x6d5001d0008441c046c1d0b1b48990490710412509900c580140a41c88501e156094002660300d42410040112401c2d410620b1140d8142200425441c80142d42c01c2d104c2c41c7c01c20003070301c4020f90003000614000032101c1610040d4540c48000a44c840700701019800340720307803988208956594204111200e05c5441c0610021441c86441800440e100b4a014116400c8180b441751400380ca907211619176420480f808084a0340310b030020b0090719401019000c006201400070003841d480f4001038a401c0c1d5404140150007462030f030014540e40e0b9034010f031500400c4c070400907001070f0742c441d807034100150114040e440100391a00710029106000c03080302d0b4111420404400311610352400c4542c0c00081c0540160fa41e8400c1080700f04480e40c4100081c011140710307440029031000a2030911080e900d041e44040e100e549044a040b080035004901041c5076021000300030faa90300d6485098840031488400d036900289420342c1e00b000050b2550040700c0c54801401e0b101110302031801008180d410a036007454040e80d0f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535978723 1250 535977473 535977503
    0x20405010f05150306010504031a092b080c070606120c050105040b030601051305060327060402090f090f01060e061825030917041a030606030f0702011b1107090504 72
    0x703100c00f46802c694145001448e10b55a6142d10b01115a82d40c1001e41b190790407000d0200020040011a4600218602508182211400a14140540701d001030f0501601d00002424000403e0445001a07030191003000070640b40c1c0328031035030310401c0141224580e04001000c00d842d801201a2011607800403c0b59280d60b90740001120a504408404000168143c801084551b9014044c61003400c0c1e80c03405000180300412036501a40b00e510ba009001d0b04014148000350300c1d04100c4590200e4420600701c0d4a0b194001403601d880c1680e039881c0b200d94038090002c030344480500c2065000b40c00440784e05519652440c03a40501c0041a10180300041204e041030007000300010098240d6141410001117101030794459004e980d43c90700c003242115100241c1840455040d40d20950401138003201c407411880c0c41c1000c20b030140b00151a0040140c1c01c00c00140d60326200b508640c0d40c0c9075041c50041c400d40d050b91409007203001c0300f003054909801480c6e001b0461800b9031051503c6240c100140400c0404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535979973 1250 535978723 535978759
    0x10020f09040e0307121218050a02040b060f031303140a1706030f0f07091b2f030c06060306091906023f0a0b1e04200304020405010f05 59
    0x81c042d003101031540824070082c0041000a07074030803a80d900c0c50700d540301d2100d04120b120b07040381c12004045984a802e1132440d40441e8000900129050f0705036000541c1ca8200c00002c0ca69000740d1001c040703090000020807214500700202800c02c01e01c207803500e07030810b014034058840e5030054031405000680f400020642c0c2c40b00124802d0741055014043d940b01d801039509560038544001d40002c103031b074800c520410804141c0d204585a60000301880c0c150400c000000500c02c402c1c0040c452400d0000b08103d04d0943c031000d8450b000548030504032540e03200c1c401e04060311504116030043c8680608000101c1607400859054001e440e0f48401048551aa0790340700025000215030001ca060000080705452801400b01b140700711010088036182d40340e0a81903550750f10000c000d00e212a040014080294403028030304500c4008500742d02e240c118004002c140148582c80d6418200c011159000d008072200800660040340255000d0103903070780311103600d00c0360305051003183d801040e140c2100341c26503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535981223 1250 535979973 535979981
    0x417091f02010b31110a09080c0d05030d1e05010e060906040b0d081803010606020f0106060e01090504091106180a080304210302010912030c02010c0905100e060f04150210020f0904 79
    0x240131420004030021090f100344030941040c0384c1680412001c0c0b10031b0025201c10841d014046c802220303505001d580d19a01c103900c90084c0c142d8820055101d03a50030784c2c40c100180100c0c17101c103403001082007190b035150341140185030182c5042d0701500058010540d40d040c01d0117040c1401d0005499400039100e10f64400d130030340d449140c0e00c1104e407017001c0c6900003e5070700380a040c00907e590b5004119070081c0c8100d00d03003102c1d0703194018014441e1120703540a541e42c001c4001000c403201200c00242c161047c3c100350328214042e0440c00e5100200042d548022210500002c85000d416985d548006032109903203a41c0b4132480c060032000d595040c0c0d1001201a8002000c142c41d03100380300224866a45982d82c00c201000b402c00e43c80460340300c02e0b10403041daa0902c80d90f01c4001462624000c0103181c6008a025014079034584010000185940d420646640e01210b0080c180c0c240c0306552a541c0d0340d03a0032240440c03050014010f0240010301c0300340012034003d4412075880e82ca00c0c0c03803822100f501084020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535982473 1250 535981223 535981309
    0x41a07210e041a191707050306070306050306010308160b0705130905040b040609021903050c1305041a0c09090406020903150f01180b0306130506070c0b0417091f02010b 74
    0x1130851010045488401207070b6200c54514200700a0114a0504003050b01f0480c000b004c40b400c140c9004000c00c945e54000490340e044a401606d441c0d030f1040b10f000c0b400c00c081581100607054a054400313009000d075202008042501102d0b80141c141502c45400a007a1041075130f01a000e000508040740c040b41090340641007040c40105040c0801506101c000050b5110f640300340e4246d000000d440c0e106080c00c0e0810b991a0240210401c8580307000d070340d6488801d103120301c0c8284072404140040c13404240a001c0f10b8070702d10004e01c0200d0030b10b400d03c1c0200195000601c124000c1c082d000b00303400e4038119100f54502802c01e860701480141c1c20170b6a568075505006140300080d0781ca8020301c0156850500c51140541598140800c08001c181800c0d46401405001c40c1d040200303070010340001c968559141030b0000c0c3d102c410f4200c41100000310400d2070140c001c1d030940c410021050002d103643c644020303010781c1540e6002809152842403c0040d0700c02c07004044c078010420b100d00c24085460513203102e100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535983723 1250 535982473 535982509
    0x80a0e0102130315050f0606160c0839010507080d0b0a090504020a141804020f06120108060c04120303090201140f071106070305041a07210e041a 64
    0x240360207501c2c844000d0300264003d64031400b003843c105409001c00c1c040c3c01d500030b48810140c81107040c070902140261140e9504500c2c0a0402081079041010050041c0001c00e1050100e0b0703d481408100c00c920b08081006a2030041e6003050f01803020480e188681800ba00145c5a840c00c254142d110107040d68000010141c07415038407502002c49903242e0b1460310290040c0400081e0130b191a10500080907801d800403400c120b001d141003500d903a03501070055000e40c1e08041d0a100780e296403011a0200c2c3d08085000d92089011a14100595415040b00e0403200343c1c401b1200151135050a010103442203014072110f0170304d0011040c012902a40043c4011071061500c0c110b15000381070383c00b0340c0360401005024080c10000300344090202c1c0f01044c08401740e00711441441e00300b00b503902810b548264410702405004198400100f0341c1e141003a661965040a87c1422b4440c200d00468015800d0440c902c0100340c0f0f00403090140d0409201d041f8144005414110754110080308110407103030b404000c041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535984973 1250 535983723 535983727
    0x1309030e060d02120123040608030d0207060603050312091b031515092406090d020d03110d0203040914090d0e030109051507082206110903160e09010c080a0e0102 71
    0x20442c0307804c18481d402003004001500204d440301c0b00889406801c041036030310446c24114103201145000c42101d1507910802d4006988101d1450034401030841580064010300000c1074083c240070403a410a40318141c020107440a10080c4815410b905c00c4c41100d4581550000c0da20030004d9040701e00d081c2d0010265501002030400420004040c0c1c5411030303030050641c00340d0700e07a08031101c031034803a1060301642240d1090a212020002c100c405404150191181e00c03410800000c0c580074450301c08110440d903054a2020904684c081e45c1c0e98841d1051030116458000598031103d810b82003140100c0e21240600401902090110b0b008848007100b2a030656036214010005031042055021802e018101079426150072140680781c10f000411000c001c020180002143c058007500440d12268806e80011b116001810141c0d4130780140c090706034040c49448d07114056190007511140844640076800c00c0d07103907107100c070f41400c0e00c40d0800c01c403010400303500100310b10328040c1c2c01428199280c500014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535986223 1250 535984973 535984987
    0x3030218030618010c020705031906020715051f080607080a0e0d021b030f0d080c040506030a090c170d140708040b030f01060507200f030102030106020c1309030e060d02 74
    0x181c1000d000f6908480c441d6507203a088909000d0a0054400100a500142c4822481c001c0800e071508070401c18081c3d00c05072072150908100340f50f030580c0c0c0296045902441d0007240100074000500095846c5887c8656002180c040300d64205440000e645034807010344600d844500c800d441100b030280143e99901c0e22280403010380c403030030458900c106038940d0041c50031090b103100103480c400c4000c0701f86019400c842a07401c94444c0c0082ca00304150801e151100584d0f03a200300b207050f14002c0b0b400c0907502020001c24131039808480e421444a560165858030411031703403103e40c50300ca1498042c84001d2500600c10200e082801051854141620aa5480c0c50030b0b03129601c0160b15440b50301325029002d004402d100344005503581280c05450982400e038034020f25901c51800c8000c4480b22014200152203140219071201054034140c2003000c0d0080d52256103451020f03441c0ca0500c40c00500030020200c83c200400381d5409404869905234842c03007101c4003c40180f01d49540300210f40e021850b0204201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535987473 1250 535986223 535986229
    0x80613240902131e0b1606050105040b09010b0714060103031e0c0c2601020f0307020615011d010513182901080601020a1203090b1e06040f111603090503031603030218 73
    0x41c908458070000146e450015844d00c03030110340040c0c0020740508d1500c843e00005442e09000d443c1034800624095450340100e2420788504081c680030765919000d4072000008050b0082c0760f1880c90390301c2588040540014441c2140c03135410110024000d840c0c922400c00c00310149480b481c1c00200d10444c4902c040b100c85c0307049801e9900c04446042803801c00010848065410300009403c94100c61042c0e85640031500002d101500300d00d041c5856015038181154141c0c05a822104611070440c5042d015030b681d00d24800c5603010309105000175504102070040541003421061000c800c20b800c2038100d480540004540c080ba0040441c0d040d8400c40403a0780c0451a4030280d14480e801c60f81d03012481340b11601c2d02c6003c40101420030360054820707030b1903440c500ba0070000c890790045003510300090003160701c403e51f8050b10300b040c2100c2000b080002d01c038040c0100c0c0c4010010303c81c040e8403401110742da5802455500e1141c108100303181404801102c1c000b030311a800600c00600014042c3d240f01c0000400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535988723 1250 535987473 535987477
    0x160206040818031e010605010c15050601030e0f01091b180f09140304051302030f040f05070b070b0a0e0d05030112030509040c111002090a06080613240902131e0b 71
    0x41c1480018202c3c0344400500c4d00b400755002030003080c03074403800b0f0052607565640c0240c98103a01d084042d4540b8001011030b403003544155060b461000c00c5460180d0320905060081c0785180e42a40d031804c000c140060710f146039591030812100000c503680e422003c80c56400c0003e2101c1c03a8003000664848506a0114404000600e001000d5401640e030352803800c01088840d008440101e03002a006000304980d141e00c1d00304003039000d074010034604034400f582d2401504203081ba4200401c40640403442c00140445001058401c0e81d80b000104800442103002c00c3c3c0d40c0134112580c83c001641080180310f025091540d03858900e10900f0064241034046001030140d514514105002640c2600d00000b0030000b000f20700802010640d0852400078094042584440e00b401894144140503000c1003e035201d01441c210a00340000041203200350346801081e81c030390302c411100b20f03000c2000300100715030880e4800c0f43c07904091045002c49203440d0020703409202c82d49030400d203414800424001504c04a00340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535989973 1250 535988723 535988743
    0x1050d021509151b0d050d0510080613060e0a0b0403050c030d110304060b010908100216140106030308090607020d0804060902040c02011e0608030f1606060e060916020604081803 78
    0x4450b51246a80c4d0814980c000c030640314801640d000c1c01840c06001c5e001400c694048106850105e101d903074010900f50082c12540c00365800c0e102d4031003004903001440c0c2d2509100c80c0304280030700c01030542c00c2d8407039034031042c0100260006c04104040f40c0064041e000401c0c6100301d14050780c0c01c000c64040404111108a1020705070780000004220421440d48509500803909080000c24142000082075039400e031007581c004a10750005801c14a100361800c14414654070400440448082000040c00391403148012004078880c1404510b401c01e010403540c1c07142c000ca0b0700030600078202102c111035411001c1d100307507140d641e039240301030141e1224000c0e40f1101c0c030560004104d1001c802e50101070041c1605a081e8a149058811b0040c0c1c1004421a00c510205484c120f032640d4103460306003032288048400401480c43d0040000302d070310f07402010600c2100308443c58501c50391500c072403030038422107400b0000040e004980010000f030703404006001502800c0302c4414001101101091030840021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535991223 1250 535989973 535990009
    0xc010c170d02041802031009050c040b070f120807020d03090309030b0f01061d0102150a0b1e1c020d0308040501020417010902031204230d0606031407080601050d021509 74
    0x902840840c0c101e613011841a0f804200441c81c528042c10003260300b0000d40200d0030f0b41e6480b40d000c140e0301c115543c03d82d0040d0400c00c254695030031441c0b4016490f83c4030385d4812181d0200c0c80c410501c4c417034021383c4031500c9504c10780c01404035007181003021001810904400c400b80011110701102045a080c0d038144105c021401d40c0446504000303001e40868030904038140c1c0d0814003112050603980c04280e0309410075100120503c140c40d060104e50203000b40c2110b0940192404040703d602d01114041c101503c0d4003902c0c1040a503401c1341580a050958a901940244588900c24000381c0310380b03d6107600c01d000308001400c06868110358540c80e4900c05211041b6910b440f03141041d03240c144000c00c0418001280c1c20300d03003846e001240030214469082c000f90603044a24010300c540f0380303800303001650398480e41c04c200d2291286854610340740c1c0503090a0b0280315a00012411410001301b05041c0c44008026040036403087d400c01c46645180a40004440381c18025440f0b00d03112002c80b286022242 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535992473 1250 535991223 535991227
    0xe04080309030f0f030a112a120a020d030b061312032a0c0509010807180219050406030f05061c0812041101080c1c09082b0e010902030c010c170d02 65
    0x11030f0403001a5510f0b102487c40342842085134882408120400c44e000200c1520070b02140c014441c0b4a80c04c014403403002d41c00303040300080c03c0040c156000c556071045000b6a242009040c540000740b201d5802012481044070807100c80600c07640c190080c3d0014618881e00d0b2107c850b041c401081031400046200050312513001e00c00c2030f0200281545500f0242a056030132910941c50081400d90b51030a1303100781c10115442c4040500101c285404650021510107844145500b10420050069101b0310902d0f001900c1c207003000c260340c442800b0b0580690b50060420700300c40d1020303d0001014120110844860400f004640109001202854132990044030a007c0352090a400949103100c0240700b0f003a0a4410001d0b40c0300855458102800041074140005414145140104462080004185204007200980310301d00b03150000314412410b20b66414852048d00040c031a00782c43d002c52000394150010f105038095544030b04d0b1848090b81c000c242a0716428a02003000d44281c0c01032500914042d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535993723 1250 535992473 535992481
    0xc060d022101080f0a020d0308040203031b0d0e22020f07060906050f070c03140306150319060b070206091c0c08060f060a03020102191401020d0608010b06040e04080309030f0f03 78
    0x401c4c0b2002041d00c841c180a80001c01d01540050210304c0000c1004061110120209096440400c240d80210600c440303c00d448403140801640e5600d0721122090006039803019001240c00c0007801906410807410640d0041803012960001a4105070100c6685920034810180401c5003401440c0c901405218001240c2c14200151a510a4020050028800303200740713580001750711589c01c0840459101001e40c0781d84070040091584803000d081168448404410300c1145040b140808440d40d66619042055603901c0e40c4001c0103010b0904069072058040c0a805094200522502240780415100c020005001d83d03070300c80064000d0f0040401a40618100025a856064020781000003210101c0707800d855980001d60700c01290504030b103501151040a0200210203404070043e00c1c2c41d0009540b10609021340d80001e140074030071f840c2c1c02c1d804d0401441490400004a500741c2c5c903e4090210960307034a4480501c00d074000b81400005110402c030483c0c00c2103075000680b42888006030295601c0c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535994973 1250 535993723 535993739
    0xd0609150905040807060e19061e06081e0102040305010908120a06051309030e0a082a010f1d0301020a0504051305090309010e01020f10150e090c060d022101 69
    0x15098000c0c5004618001c00e2202013000c80f01600c1003568449004641888100c62242c1000c500b8010480b1288000d200c202c10480349400c0000d05001d0744550010741d0158410900981d503d5104d44801a0070104910032002e07403024072403c2c550758510004d40307420341d0f945e525421609001c100351282e40b40414006805048468050f0300140e1180f414001c981c10040002d80560400b0010641c1c265140819420035005090715071602d40024000c004032542c0781001038940b001c12a4425820118000b4510814030320300500e2001b01044c7d466480410f0001400e41d90410400b10307548000c00141180300f89583d090004101400850755041d1310f4500e404184503102d00102d601c0340000b400d080030440c0c812000425191280310903c0d000209441d5100143e0a000d00603d443d00346014a404880c0c040b46960800b20181449801e411481e070341c1c44415400e001e10a0310b08080325008170100d50060703c1d00002510140406810052415443e03211201e03a0710020318019005482c0c010040100c1a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535996223 1250 535994973 535995011
    0xb0a050f0f030a06021c06051c02010c06060e271c11030c101109010c0b0a0204050a09020c1c140a110307030e010207270f060e0c0702090610081501050d0609 69
    0x6c510241305000541c1403c000038801078841c10094122846210100d0030342e07201d03a0000c0d40c855000710081240c030f07403188010002400111001c45850300c8143e0074408926010104000041a03034014181c4283c02e00104144050559440d00400408203e120380d510000d00003070600000c1d03800140040c1d41c014802c2c00958082000254601e2800d124203421660004d040710034450f070000355044030341e585400d160300900030307500003940020581030007181d03045541e402420341c91418070440391071400c452110510711204001d400009003c1c040300b08400c204c80030252500c0c1c402810f141402d080007103c4503246401458040d00002c402d1800d811640d60140100e9015054103900c1010900da01c1600b40440e09106002004495851100c0a00303442c01e5400b0101034101000a0100b41c00c001039040519005201c0a0788210021404140c1c2c900c0c0000e16040180e4054454401c50ba0300c07803816030395406c04030305158180b01c4200080b2401886600c40c070805092150000140f019081000a1460b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535997473 1250 535996223 535996267
    0x190302011b050d12020d090507050f060310030b040f12020c0a0b0a050f090a08060f01080d0201090f0303020c070509190e07030218070215010306020c100b0a050f0f030a0602 76
    0x41d002901048010803004240e42031003d569040c000e0380c001110b14904005c1c4919041d103104945010401010804007042c2001194011039003141031110780020859240f0064494152080d099441040050102244598003d00aa0740c07500000e009d44c80c0c407503d07000048201c100580000140c0e0500345000c010b40800742200c0340c10710703052a142c9c00000e09203114401c0301c0340100c180402e092826640c0c00c1d000a014040c07030800d94900b4204603c40d404503800a02865280b030060005100d001031051088405403a04a07121200350003031914190000e5000b04035040c420f02504201080c151110300320240101000d14201448000340080c09084480c0c2c049500080c1d00403e80402c05070f9903580c1003000220341255a1841500d480c0c03c16460701240d0b20010301031f0078101e00000b0030f1101550260049440d48402c1e0340c0070003091481501100c3c14019803952250082c4c00900050400880409243d88064000e412904400e00020310f020741101c41203c1e0203800251440e15114516403600304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535998723 1250 535997473 535997507
    0x40501080a061415040906090203070f020303070c020904050a02120d0e19050103020f040f091b020c011d03030705030d0603020103062925060c1b021503060102010b19030201 76
    0x8071810100c55a0344500c1d90212103111391142e031803410000c005501283c00600310010100402035a6414880207074100725100404690020b5500c02214008404c483c4103e000359942c001268190b820484c000c0d80140041d50383d4450303080203c0050311840922044154a400240074819244000900404254950030f000d011070701c148914150000001000340c030004d08015848010360301d20242d40780519404551201c071460070000b0341103030303035400381c841e1100c0e00110b1851482c42c0c0100760b82c2d44402640c8540041d40a0120940d00320300d2892002da000e00040a40345007082d01d44569245d50040039195222aa80c0c0c0020401c40d82c0610981000b060740c0780c0e000b40e900301c04035201e42945400c01095411798000203240495144440b0100000588645e181d0350465900c3c24458020107400c044180070548000090f034000744004040c107801d641c002c01c0c80c1034085100100b10480c1d00090200c0b4107640d02d6965050165650300724240c0d00c01d800f81e01d50f90585107940001410300b2866900058 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535999973 1250 535998723 535998731
    0x19230a05042a050702030a0b0604050a0204060c11011412160305041e110a0e040c08030418021305041404060c14030a050403090306060644100302030a08040501080a 72
    0x6032003004118480c0d16070a000703420382c88801c0303007019500361041d10f1000b03600d801041000b000700401180707040c0c06100151410805960307980001000c9200e24000c00d004590240e1440000844001080d008060107141803c1101b880905401594001040e11100c803041d030410007851031070044404050350003500d403e221906154075826212604180c0300d4500720740c801c0d00c400a11503501d440280d000c0b0007824120a49554001c44100d0001c1a1811030301ea004012000030120000801e443c2138a03211101460451043c154800c000d6200707000310f121038440320400043c0382d6a948145a4050340300300784a0318602c0c00d40343c1441140c00c90b18060040c4090580041d2800c4052000d403544150f04280000c0c4544413030130103480d20012a1300c0103000909280d0045151079220000004000888064803e48a007810010203080031184020002400441d401c1d0b8980e442110040d40003071754000c8082c105a140e070086810080201e02c241e47c003140c0045c1c10415541c1c00b030b40e000d40c44051507000b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536001223 1250 535999973 535999991
    0xf0d150618110a0804050102190e03010b01021b10021002040f0515070f0b091c0201020a14040b181903030504051302160308062701051009060e19230a0504 68
    0x100c954000c0f0003442003042508400102000740c01d40c125459a00108404a120010400000c150100d0408114025400c050601c429940002030540d0075049081c003203031861013400c081c0b11100c1c01c8440002c0c1144034448038200f440800e44010005460320840c1c031100c9500702030501c02644007148070512501c2e01000144e000c6280c00c50203c0c09694019480b500913101c568025240000e24202c00d003903000d07295552018684c055000f442c000940340ca8006000001c2441d141840c081c522600004c0d820030000d401e448242c00380c818042820041c42d031034400a0f040248010203a10f50021404130310002800d000034034181c5100f400f850358101040d0720300900d46201e2400d43c1036039000241880021404250940d84c1e030312510340c600c107407207890b440810340601240d00c4090082c82064003400220320f001c03000b1440790301c10000340c84650300e40340310f069494003d00c41c14001900104101c15096480071030128011317a42200300761110b01c2211040d4980d41c080110100403980521700c41c81c906074036a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536002473 1250 536001223 536001251
    0x908030609091b1c06050a060513060e06060705073807050307030c05010f091104050603010b06041505040b180a0504060f061d030d080403110604030e0f0d150618 71
    0x66551400b502ea4407a03498004c0903103122562805801480141400104240e01c10144e1016007140c00c01c8502000300390f110b551400c1141c190b4040c0003148909200000e2407400c000005045c658410002ca0f600241d942901102d40c0028010f40c6200c05440708004260032598003601c0d604402e48403c46140c02981d80d207481c4c0d2841000d0001302413084d0808000e003400420751024203c0120362034180211200d629001e40031501203d1602e104a15100102c0d01a0038148a61803002c000942120710340b40c100140850140e0303c010900c02044420000440c0031945480a40f864011000040c0114414801040504900f40d00228000d40c42c00000b042103103032a4485108445140c1010351000c4a0b2010810304003140c10007032134042c4661590805015408132007030b8800c42c0a690b9000240e000b000260361519025070700507001600c00523125925140400004c159200001c01c0f003220031281c1c0d0b07156810044540c07400495681e07112810031545150b00c072181d081d090f111404020f94400720081d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536003723 1250 536002473 536002513
    0x8010b010f11150109020703110c0a03230316060516020601180b04020c0601080706080c0304110f0406090c120e03040e07050403060207060906181505070210090803060909 75
    0x80c03401004100300d1210450b02040c0000c1e2803e80300c1c1c00d0034242d01c0da11000c18901030742c8152021000585944120248500e001c51141e48181d40204a04403e0f455a01c03850f0000d9155002c038850a1070140c1c80d00450941040100400c0000c45118220301c40c0d0703810400e0440b003004140d001c139200b40c03007001c64001c1da020802c581501c001c07803c14106034000c1d41281e80102103070185543c01901c00228079480450009119040301c80c1b42c0212020983c8848003260000e90545900142d540c2c02d2012400207038160b440c09030820b0000e0030402001e44803100090a40d4500c4e84044916941d4002d6540e40c5a03002501115241460740144103e28802403580d540b4030581c4141340c6102c88281c041642d0074800c134102c400441d00300c0300547d1204c9075030622034014028403408960003403a001390b6290035102205054a69034019a209007074222444c0c008010b0301d00105140c085006d00c400b4101312080364450301d101c203801000704076142d1030000c040c050480c0000e8490702c01c940c0500c44a40f200100750003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536004973 1250 536003723 536003747
    0x2d021201050601020a140a05060a050103050f030a390b010303030b031f050903130807181a04090c08030d0504110108041707020315070804031701050a0b03061c0302030c010608010b01 80
    0x141c407900040411783c0751b0b403c02000b460000d11030302580013808262855508070074141c4e4004c0e03041e0ba01d1034000088403580c0e88a251f50300702c003040c1c22400420088036510002c0ca0240d09800ba0b140e651400581051081c02c000942254090103039030060040c076074188249441403406800500e40425001503030f1440c0c1c100c106054103a1921100040c0480c0414000d490b0782c41c4101410038601500c8000040e20f40c0a9805103600e00071000800c141c0d03c80e65805604c9103847e60952101c01d412410b81031001400e404802600c03000c0780d0a10000d4051420001018241244580003456091518001000d003004566450402040106010102c0e4042400c90003003818000c24950765400c43c0302080c20604a500329030b207440300071400c0000c02c54100031401d01c514400d0740c803078880350700e0300c2403075a40f0b00828015a500030314140018041415848000e540242c0300510000d004003203c0454541c0128450007103005030001724000004c42c80900079400a0700c1011300074080c81500c2c800090510340551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536006223 1250 536004973 536004983
    0xe0423011a04060b04051309050a032a0b0a0b03120c150a060335030a0501060807020106260a08130e0915040206090616030e210a030c2d021201050601020a 68
    0x7036241f10300307400c82d0303001841050740302c019691100c20b1410041c0a506100112512f00460ba2800241d1000144240c9020310f82c4010200915140c02a41c10000e000211469805d80b04200306005000002c0c800390800403203880040501850100d4a541b0850010381018800e6061000c2480015404402615a80c01c20305100402d140f1582c85e4021504e500910815010000000d10000400e2034000314140c540c0d40d150303a0704a44805404a080315041c1c4910140381043c0c02d48802c4000908800e801500380038012140d941846446028642c0d010752400782015410100812540a003080710b5a440070900c00030f064402e2862140c0c194641009000a214410001c1c04514a40d0f60805545100e65143d001400c441301300d01d0042c00880301c001016205074520b051035400d80da1003400c80303980700390f904018250b0040300d9602500c02e030310f0106040b40c6040303002e480700081d0b042400b8489440c4441000106040c02030380140210165024040740c1c890341460104038640c1d130001040d4000d65844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536007473 1250 536006223 536006239
    0x90105030a0803100e090109060506030a050a02040c12050f0f01060f09060c031101090309030213060f030210032405100c02010503150420180409020a0e0423011a04060b0405 76
    0x50107007400b03030313030b24540195001407820410311201000540c8219030507481001c003002191194030401d42d0324606120004c1c4a50b005002141c01410150000c0740036140380d04041540c01466850302e8155082214141008420300b000c101c030105117001c01c540141b040c1d080508040380d4044004003a003403180640307424028620000e000309841080200da01047d458002c000c008500d2a0040851141e4071043c1e214007185c071390300c0d644a1030900c01c620440750248403001d6030034510f07800c0c00901440c0070024003d240d600c02210781a4200107406004103800b00b220011041c0c03c0404000c594646d810b020b00030042403451000060740c1140841e900603000c01185c0d0800d0840c0d100040180c400e07902c240740c07500449491116810300c150090290054990b11405260f03042c1014801210f90400c0c01035444150308a040080000840d5550342042c0250100c004007a01c200601a17420000000007a01d695942030f045203104101c07020102070f09007104c061014925120321030146000d00d0198910599030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536008723 1250 536007473 536007481
    0x1b01020a030806190608070905092809020303040e070f0201020a05040603020c0717070302180f1315050f040501050a050106080a021c11040510090e0408210f090c090105030a0803 78
    0x107130f00c02d481c0b058000e200c91240855122680100000c00c181c41a1011070203d120100701071910750085803054020381e40e0401040c00f42c0860082d04d20503082c10701d003183e5840c0c10100151b2020f10082014101d003500508003421700d040020000030b0031545030021a44107004034000c2c3c903444421601140d200c0c0c90b0158591480381c0105041c40c0d400c0e40b182c006018203000c5001c540c0300102d01441140c1c0215001c0c03c2030528680c002541d803104640c0700000154090015441d4020040c403903035118099444013601c58140560002281c900365800d070114581d200070001040801d0084990240f8070410038401c1d540b504402501158003c0d0050480a8000c1065078145482c4890f0074a492013441c010300207102a1154410181e0007806500d005402041d5104600c602907041e14040700d03c0f481d4079410555840e1220401908840106124120064104c40c15010001c0c45240101c4800c42000001d040811040d8944085140c2d800c0c02031030074800400c03007983c010840000c1c054010000c00d550b0b9403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536009973 1250 536008723 536008729
    0x109020627030706020c120309030601090207030c0b0106090e060102010212150102160b180d11060f120712060504090b040b0a0b0904080403110411090f061b010e1b01020a030806 78
    0x31a4040d080c2c0c1500c200740000580c181d0000702c4403072100040c0c41482a01c6840080a505c901c14a815160164004030041008880590051071518000d20b0003170000340156541400c551800c2e0b009000040c14203c0c00c0c085421000c0203160480400d000840c03522800c882001c003d072000410044601c003644140a035103074002d101c07420407800000c44550019413101d803107001a802690740701411200f2486107600904100c03010390300b031079040360980b1151030601c0c04024140d0703c007445190500307009014016284401d0710405000d00070381d403100c150301350005a442d4211045988205e10660a020010340401c82504001c0d030013981007150004c180d40e030307107c0c0d0310080c09180700fa086d0821000301c2000b0a1048060141c0306903813191050350b0000c000c1004202c10303a40c40303800011444408000300c40c01c80c60070040351028524083c29450800d9084000650f0141c42c0302107100246c0d4590801520000050002611151000f038845421502540c0001e69814a8210090078012628003044a6607 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536011223 1250 536009973 536010037
    0xb03030c0f07150302130b130302090c09090903041404050c0c2b0914010c02040905100b090609070e06070f050a080a08150f01050706090b0408190201090206 69
    0x2201010803502180307034040859944403018030580b101650000a9504050301c40d008980b4140c1c04003030f841c007100d81041c048180c60b622003003400340ca103038045000200585440001d207215030580500b1a4580300b1800501010100c020081d03400307074000f0403083c407240342d92000c84096048281c4001a082d80c620300c3e007503098800c0d0345d52a46148525150303140300e45240d8041a802080340194901115410807090341e4002d85401041710000d05c48130400900d512a18035500e00038001040031401d904252502814810540701079003025455038060100d5050181c03225401000940e0b560501d40350000000340044140180c062050a0010341c4000740038440c0001020b0940040540f034129555103040045070b03011010420116580d500018210848041d855141800190580844484840c01100c00f9800392908032580c43c0d8031020000072944840b849403145102c1c0054a90300c40d51100842d00312086090107204580c10a80100d0050711104183c4e81340f182c1ca100c1c05c1c4103101442104803110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536012473 1250 536011223 536011237
    0x120201140304050c10080720011b020607090501110309010c050708071212030c1e03290406120f0803150d060b01031b1d0f030307030201151d07030b0303 67
    0x50308084148002c2c4180890b0111820004039409090080001d40a840c41d8200301c401c08041400114a400720300e00c10f20108440c80e00d842c00001e0301c5880c03154035041003c415003002005034001e4040110315508504864003a1400342072004011905109180da2445520245410807440d0710719001041b10400403000500040e00c00d40e1000f54841c6030710b40110303e50300b800b5038540401c0441d20410601030310494045d444503568050144102c0340100c080d03c1c101303c028104055a82404179403002d440d05040006111851040725400b01c44c108000c15200e090f00700300328844588030200c0024800c00b03509150383d80e0118146481c0d0361040b28028011070440401038000141c50301c900100003581d03104c60440c0b40240c030200207850b18410450fa00012030307002000482c01606582c031000c0242d0031180d24207a001000000b8251011001c2419a0008a4100d0260303448001c10405a0003420b1600058100b51000200078180e01416000543c0098000c106041e40c41e0288041500c00f0300c121885 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536013723 1250 536012473 536012507
    0x2122202120a0219120b041b0608040210030509060a0c050904061202040507020708190f02121506040203060105070602090f0405011203020c04050606120c07020907030c0810030c120201 81
    0x820041d125203107031103508169040b4802c1c50118603090784210601030100aa40e40e403401003001101641e04e8088142000e481560400b801200103d0845080412400030380501d5454056501700f40c03050000710003031544000103050500d000c000c00c071000020b660340e02c11424100802c0b040108002034800d0712503100c207540c0150030200045404100100c8404400b44290b4040040e5520500c0c200d8441c0c82a01a185071a003240180541c225181c4004101590141c81012600c005545c001409609030101400143d003200c06030089540c3c4036071089a00c144103440079403a600d00720000030400c3c030400c4401440c0315400704c2d06a041c1c1c2c5030446000e04414003c0d0003008103586950400c0030350782c80d00700102d006104205208034141014028ac500401029045604100481038161440305005207490700c070403014416240540d8440d6405400340c145510b00140c841d02a81c00100300d03000040c0b8074180584008001c000141c0d1286c0c850040385c40040b60000e80302e04034030040311030412000d91554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536014973 1250 536013723 536013739
    0x32105130b3d081006031209030b0a1a031902100e06090409061506110705010302070c2907060605091e0c090301020d020c010605100c0804120602070f05070e090102122202 75
    0xa01d0134480d40300710107484c007501c208908000d0702030044582c1083d9010041070f02c802400031501c2c0c00760507000b40401609008001c1039418002c00882d00d4070490728240340c840f9000d42d01c041d041d810510780c01000221185800740b003007002030b004540c1342c0c45a8000070303010359650390304c0c0c4041c001540d01042d000424204e1030210070b56100c400808240030b030507060a80303000308030001076036600034400c441c0050350103800164120300d4510544d280c2803049000a801c1044800f4a10070350b90311000030128188941d00019949003440140502e005005041881100321101404000080e05980a6011002c59801d03503442e4600b40c00f0901a01440501001850011a0f841c071512410740101050703d8050f54071460304540000c04490203074034040c018003d01820002403040c0718082c208001c4146c0221400342c03a001165607070307030003454848030f054466411151041c045203004045007a005006034000b5400c040d00710045d0400340740090207400c0703c540302c0d00e4011b00300315240708940314907900146850 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536016223 1250 536014973 536014993
    0xf0e071b02031903080c040f1a130f0306050105040e03030a0509010e031224130c0521040b0603061905100b1b010b100c032105130b3d08 60
    0x1014820f18030000310041000c80700007480c0b224042041d07808a03007980e2071202e42d452030a00c80d05418841c2c400140161101008070201002d800500c4000600c02e5880741c2c00300b149141440d604842040e04018820750405c0000c10003800000103907a044071000100040e00c0d15421191801485120364584280c080803d603001d9106140c403046114401e2441d21018008017641c1142c0e040f0f802202156001c0702d23104400084001a502005040144d410718600e4040c1710404030001000d0300a441d078030b80009000f04800c000c05007040c981c000d034040d00180598103010002518110710300c5d03049020142e40b031001070035a40064450000521481e00c03040c0d901c11040301d200b01c0030b02e95601110090f40c24841031410070700306803040e800404400d81d01c0061003512075808640031034804c561501204048081c0e81005002d920034a0301400e0618441580f45084e4600070300b00d4032008001c0c203240a507a26038400c1a000c0c8540d4145802c0c4081001d0207144840d5881c1660342940350018040b51164150356 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536017473 1250 536016223 536016253
    0x50415090f0c021b0102030307080702120706020d0c021614060d02031008070e010605040b160c080d1d030303070305071403090105181c120e060a0203100f0e071b0203 73
    0x900303201c90940d0f00766401340402e40250300741d2550841c4e000740164802c00000d441d0703034412104541c00c8041841510b0301040f4202003c110754001034000d031145540050f00e03070101d01051068021180050015200d41180082c25050001c07581c8601059400c003c001d0422980e6001e0071501d800381c2d640ba0071500c0741048440d100c801c1006000c0c1c00d8040c0300e12207000c140d6018a2640030b049500c950b840c02d1070300d804c14071031344480e40110001219441c1c0c00218040001c0680b91060050800c44008041541a00e00020030312480b1100400035215440031004050314040200ca512084904010482c0c0d2a960412a00c80c0b080b8501c108a404011092040303048064016902595550544080b0100c008080c03680302c020740c0314894154000c0665808a643c022500d052000051500020f00400608a024181803081380c0071072140c1d40c0003007000b080c1640707403080d0740161842c224070390261414031848403204403001d85030006011001c440c401162b6407a034190020031b54041c0a440c10000c02140c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536018723 1250 536017473 536017481
    0xa030e010522050a0f030b0a0f0605100f14070f0b10170c030c060313020909120403140d020c101b0f030f0806010305060a030308040f120206010f05061201050415090f 73
    0x80c3c140b00300310324040016400070159240040d02e400144095040c3c07a404410300087c450512208070050302c45200003819612041d24848594940d00d4640000c0d5101f88010b18a200e480401a02c000c0b042c40040d0118940130381c02c3c0c1800d40e001035012880e849041c14040300002661201000e94411030480d8811040410310811901013030f07046681e8281c86c5810440300f800100c030300e07200b21990384040da03015180581510b50050b0310241074440010f400c0000210580c025001569001c03010051052144030402982d890f03401c0c0c52000d80342c0780030030400207484541020324240400c00205418510b183d0113120761504a940f000c0340c0e084904052a0103488801f800c0003102c042010350000541d15402400f506104401c01090680f51702d0969070306540c41d0780003030b0003a164124031125440010351000c404402d14205c9800070807696252a68002c0441c1150701302d580201810f00200402a03450740c40d03e41902c208440104010404181c0c01d00860b4056001c100c03e1420200207031003070002984 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536019973 1250 536018723 536018729
    0xe0702030f0c01060b0c070e060f0f040b01121d0c0a0302220b0d0c030221120c0c090703062103090933061202130915080105070e040501080c030a030e010522 69
    0x2402003071276661804201120807114201c50b042030070018907070b907980f0300350384030b2541d0f460141010101079540c1907088049803d102d01588642d0800001503190700b0382000000c0c0d00d08002c440f034001990450780030130074803005101200c1d46010007200d10001904c41e50030074121139002601e0000c82c0009406c180d058805548410f0b0300403060074000020134540c2d103c0202c01000408001c5c50200002c03550400c13039a0080103c000c5501480c245403000d0b580300c80701c0d18002c00c00d981e07000c07850303034142004008566440803415400b0406500e6220029403c12104002c0380e1070703403100040c0c083e9400d1299130b003000c85100410111010000d004210341d07414000381c050710010750701d0340554401d140030141248141c25032407030001085602000210041d400c192648a00c0c006469651651160a1400e54005980382008079606205007441030400344942c500401c00c03080140350151404c000300b81ca40344102e00c06410440c58050382021a4001c10444001010044c103105080040c002214802e07a1280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536021223 1250 536019973 536019989
    0x803070c0c050111120a12050a1401060804200f04140708070309111905060c03030103110a030320280c060e01140706180b0604060e0702030f0c01060b0c07 68
    0x41c00c00b08003944502c440ea004405075030014001403698001c0d420f90354001282c00010491400002034200a0318020203000700d8a500740401d000c08007090880f0389400c1600138008000039242040f010036440300c03181c1c0041d1108081707803250030403003800b0645155000d0022078019042c8410051986515007030a840f40c0083d64488085032600d15040342550300160014201003980c840b080254034100400400981f01803804140e0150b448010603615001300d40c0c0c4560079003001c1300400a018201070150180502150040001070a596020780010300c14001000b00d050301d4240152007201c1000784400c5804503111103003480320081c6000c62008a6071800300e074030540c958000500d450045a919110143c141c40d007510440d254000e10019401100e0305a5400c0c0d145c24000310045240e0364100c86083c000d0f0780d07513004c40c54001305000c2698066404185219032100401186990104c1903650344400701007810ba503002a000010701429481e00a80031403040010100300d80074000618400301c40044d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536022473 1250 536021223 536021243
    0x408040911220501090303120b030a0c1a030f0a090f08041e1a040e040f0204050f0a0b0f03030a05130312050c100b100e0111010510050a0504050c07030309030c0803070c 74
    0x1802c40c241d03a540c0c1c140310700e501042d00403400b800002d00030003540130103d510313100c00110f42c0c1c0c0540c0020b10340481c03000256110b403170152003030000010001d0701790f9400f02000c040501e10304080a0306603084500400c00146c4ea030b600d1410404100c000141c90b5011500300c003129494a881e1144413402c80c0ca480c10903d8888001d000010f60721141030716010400781c4800d07100d03060078904a1100c03c2c0310070080007250442e0141100c000165107510405002d20740c00c001c1c810f41450300c1c24030601204c0480d4213846c0304880c5031001031140e036000030480300120305c0c07450040e44403103031a2200c1454400300d42000300b522546d581c100507174a90180140c80c400d0440402c84d0a80c103042c041c000110781000050541252a102c1e503644520302a20490f0f00d00b22041c074040c0748030b6003130020240c2125800d0301d150440030030f941010091450141e0298000c0c00080700d082101d410210034189142c400c2c990002c0c245034036441c555081c14000d000468103d9049054580d4038503000000038403034038524008403040c0034130f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536023723 1250 536022473 536022517
    0x11a150d06080d2d030e07030c0902030a06050d0506070e0609030f0102070b2203180b0a0e012303190204030b090d0306060806031e0f03040306060524040e0408040911 73
    0x5580c070784020b1030880b20380004c540d402c401044000c0c020580c1450202e2203458000000654000e4000c8014419070500503203c0c2401c00c0707940107540341c0742e20180c42801008142e0700483c101003601c580100150030305c20004030f00b1501084d243e00070b090103280c0c9806003820348140e412040d0004e1000301d20500c0351601d20768407082c07145040c0c08202c059000303e950210b40301000a004590500300b041c810344a6074031143e56921010100d0b4010700c072001c001450705556100f1542c0000b1005480380c0c0a40403003075030b00442e4a03441681c0c00010440c626904142d25020384603400c81d41210055500003c1307500642c904074600355034503c90a200d210010b40b0b030003030008016208451007409035600030050001390350742c100c240b941c040c1041901201401410107421310520208010001140b18607400702d4010720700401c00c0152840104150304a2003682c094111b00b61420b001c40c0c0039107001340f507a80a1900d031400c0c1542c0038012504108002d034541101100c2c0c089500020b0200209070504003d16010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536024973 1250 536023723 536023757
    0x2030403022407030e040b10170c0a21020f0712090e0c03060f010915020c01020f0601080705061312030c050d1103031303140301030f050609011a150d06080d 69
    0xc440301000da0702c820500070040002c1c850380ba08215080003c101088112004000800c2e40034112510004078645046140c90050f51f2000321b0780c04442215110308001c0101c4000d40b533082e10120705040c0a4040c04034001604981c2d041c2c590070044c3c151041d80390545403501c0140080300400060206009000000342018103032613061188100d41801da046840741c4061001c01c8a0000703005045c0a0b0449002c5204c5030080b0022000114a070b00401a0001440c006030401503421224191030b00020014400035400007903902c1100c4054035000d9842e28550041c551591050b0042c02d039000142c12004141a48440c180902a001c1c40540b85070203400b542c2990034055840f045289a0400d2000a10040c0e50140d80130980d4042d081201d68881d615424040c1507100b40c2080350400050080300080c06001c1101720342c00f101c05c070020000362140b000a01e02c00940082031620882840238242140320007001503070549280d104040c84643e0301e610700d5544400c20300c4041000980d46221038a210740e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536026223 1250 536024973 536025019
    0x1060e1e011209080c010f0b101b0f0318080a02010e06130308030a06030f080c1608060105271509090703020618030307150c1b211803030203040302 65
    0x90341615503228400698810304040d2500301c806407030ba9141404180b00741ca81c01c0c060500c07000c09080000513003030b000c0e00401c09030849074040e010400c01d441040c80e29601d203490000c80c4491b008a821b00c1e040c140303890210750f004045038011203d054031920019032014001440c020340c51003600d5403420040440c00f400300b140903260444c10b030f007107400d5420400304205400458100003200c1e008039485440b82c496003400e003100c45048034503042c00a000c0b51029028052250fa12011210745002d091610307034400e60b90341041c0106031040d111540919583c16400c1c40c0e08100ca4003080640800e880d0801d64007001c0261401094090121000028496840440c442042e0303680240144c0c03c10388207200c14582c0c11b0141401d0b0350544020090b6602040880b0210b542d555011540030810043d0030000401e482400010303000e0070240c03608003000151039515404541d003409180411500e0b16005c0840d418804c040705012000b141e04408420b16a002c002401524000c1e00c44607040401c02e20291034503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536027473 1250 536026223 536026279
    0x14070b030c270a081b04020c0307031206090507050c010e120706090f080f041706040b0402100e0a0f060207050f060a0503130c14040e1c030b1801060e 66
    0x1c0d941c1040025084100304418586a6007800d020780e031074200060114041c031009030810340b035580c026a24800103240844115000342004d403015810200c0050441c2d550340a221001400d000310b08004107448102d070b600090080640903014062070070080006021544030060024841d42410b1442d03c102400251180c002c0003805851072501c0815200d010084c5020641194402200b000725004200240081c1491100c4220318a546a20300040c45182010b000b42048054000000700008100ca50840c2580140c0546109822065001d811030302402080304440d80480d1400005c14680401c41c40202074035016001c80d0715007a210300802034550b00c945c0e100790744183d0070040b64404620030405941c002c0c6024200e452840d065544001c2c0d60101a0132100740e40c00c191100c3c4a0790b01d041d009a0703514003440740c064800030151785074401c0b4900c825444001890f8a170000082e20352161481072500da160018807610360b5840380300080421540104552107121010110420499121204112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536028723 1250 536027473 536027491
    0xd030915111c0207080102030901020a090e0915060d0b0408210907090e1c05130e04110f01141804050f07020714150706053907080903070314070b03 65
    0x40100d03108959610300d01004074110844c02068800140764000b4000f56020704034000015032102c02c03481004004000540c0004000b40d20003080c040090004a9200d41030503440350b046c11581d9032000070030802d46142d203004003040203010030441030000081c003426002103003240c0340708120070504a14240c100c0a60f09851381c0d810145041040015551104e64042031400503a0854003076101c0c8408445481180740000c1400041e440008440803c500c0c4060050744451054604180c1c64070000c600c00355410500601028000c044140e02030a07042c2740c504158160700340d82e24031240768499035881c50030710740d4029410300000c0380d400c0041000052203500254003c002c1c3c10f14254440300c1d2117010f9030700395070040c2c1080610b000030040e080040c54280c0c014500894941014002c90314802d82200103c00e045150204880d61003c1c02580d40c4010000c015074282c0700c0249042420b40341c0304806455926100350311000081008e81006141d0f22100d040a44081c00d9550760701d40c116101c21200700130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536029973 1250 536028723 536028733
    0xd0503030f070e0306010b0a080703061202040c02070f0b071403040e0c090427050f010501050d060b0316120302010c02012c070e0910050a0b030c060d09020d03091511 73
    0x1c0110144070354642c4a40b103860201400f412203008a4102442a044240109000115080f48a812044a1303801070b8081c942041031510300f11200164800000000340b0594903080c480050720320030800200506815402401800e94071158043c0340d60002104864050b1440340500d65000044140d03011150119414101507071f80c01006011a4459844654820781c0c4103626003245011141c000d01e02a8048140060800542802803504503c141c0f0030034903a05103c01070140d6103900d1410310710550f0244010895081c49000241004040c480050090682141c00200c20512180c15103016010380c000f00042055200201d003614400c0c07135000001d403d004251202c101414580c5017607200702070140c1c2c0e9003946960701d90703440c05800d40d1040303056480041060a030307450b00c1c4543d540144401404020070070f605404203441d944141c00241c8160030220715a910b1102d40e030802056140d000341070700700d100f40b10324001c1d101c1c19041c080d034082010210541c080b854014810b2184801b0b20704000e03e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536031223 1250 536029973 536029981
    0xe010203070905150d090f0203010b0409020f1e060d0b090901021e070201030b041103070f11071509170303071706150309120310060f140a2307060b0108060d050303 72
    0x700070700c0003d0780800c1800c9030400c1282d24420346403181c1c411040c8101d12282d420747c00d40c0109800d50320042c0501c1c0c4214680030a4000503650030105001841c025905c00c0c52178020880304d1070529502c40400c80c2c11182c0000c40311204409a802002246d00484600c03525444165401c2c0c203c4c042c2c050005801580d1400120641e000300300940813083c13051502041008030072010a060b00d21844c100899040c001c070500001680114041440b84441d282050741800825119a5505105c2c41260003042c010010312419a1241701503402820300300c4a014620031101c01030b903035607910480c1d0440c000740301c04110038801a1254122801000c00515124a20420b0b801500941c0d0003d40b100da00c03441011014103038400e025000d50b201c2c1d01510640240f56240c4200546040c908042c140f04111040000d00b03034610803a41555000c0704503280080c0241c581c0c50041d11031002d251a65000345001080c800104525900700c001003c10030f80e590038603500c401c801c0c00340d016400301d0300800c1d54106000103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536032473 1250 536031223 536031229
    0x3010e07180b18040903081009020f0d0209011e0c0309060e061b2e05010e0403020622020604090519061202090402151614070e040f030c0b0115030e010203070905 71
    0x180a24012203e4001000071507180094100c51416400b02c01180000d8104414480000c501c400100041c003001d61408000203154480f41c0708200031306414513070104042802da446044540705090104441800200080300043c0510001e801c3c00c0700024600d0102189282c400d50b05c1d00381d650405012103052180c00c50b000243c0c8031407900c0d03480c114410031240d072541070b6100d400d0414006030704c1c600792550340b5040041d80655005800003003000d403048092000080c2c0c001403031a0b202c07401000501c2c200081da4a2802100029030000c0d502c5680850080350704070795684514007803481d007002001e00402801203041580c00a114581d85107ca205940000d070400882c00c552281c40207201c0c802d0002e003c411901150001103441080c504003010368003c01035100e69101981c00000000d01803a072915a4007104800002d00092040d08007108090815019502d000745250303000040d070344150b03180c1010140d00300c500340100000904002d030001c0d40010610840b4001d48196648843e00c034207007018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536033723 1250 536032473 536032477
    0x513061e0f2c090c090f090709030213020415140f0a0207050d1101020d0c110609030102070b2d0c0406030b0a0807120311010519180f0803010e07180b 66
    0xd8600344680c080003264075110101c0303040b02c1402c0500395050b00010040510001d51001461001d58801c1004841d909542c0c564200c01103000456070000c95a885507022241141242d2000790480c0315804030886144d49034001c1c0054400301d18108903400c00003001200d010032074030020001e0381010000041c11070724a000500349440340d4011601c1c1240d90300f02181c4e50840c00300d803c0e42c0c4c103504070310418000e40e03051240c0310243d10186004420312005480300100b20915480c101d01c0b44000081c0740d030b507903202074044c2d032001e6401c002803071000d01e8a00024441059240004503002244400c1400fa144042040c203024110804c600382c142401c1a1090f030040600b5121658458083c81000800f42c0e420004100030380000d051107042d61641c1d20703019002080700c001031010760f41880100a2590440c54103c0144140480c001c11060811290000b00403601c50300540541c0840c2c2c065810702c8080401181210700001c4100c82039510007004075a54085801c802c9190380340d81400300509410480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536034973 1250 536033723 536033747
    0x10204060c0b07030c1d0f12010f0e0d05040e0703090b040b0402010e030a050303060909070f090b010f0c08090112270506060102010504020315040602040905090f0c01110d200d0513061e 81
    0x4481c0c0c40d07138406080051180b000719403d1100c66912070700c092294603180d0248280c20041c1800a004c0701030b08000242c6370b40164041d0103008907004001504c1c05120f50041407020f40c10086141850405040880f030700c40088a0503400700700840010411400c00099160200390018007031400c5489a00400c02c48400c00382c507c4005e0302c1030183c0840c40ea441ea560b4800280b650031800101600100005401690030040100500c04440400c201041c1480102c400d84c80c6d0901c0c10394078020181916100070b18006201c0a0500070a0384000203480010342c006031a58060710450390660344402c012403c1e102c048800070741540100d080c42c5460000d4584098100b44280b0380903090a84583c1c20703404894049680a0b120307030100c00400c50f10300c42440b40c03034842030003880c100d0b100e0701245030070f5a903074907001a0ba40304101080e000103c900e4010099500d040b4440740c15640e403030b02503440083c050b41003912003520780a0000400200b40303002e03150320041744a81080c2c0c083d034100c1c2c001d004c3d140c01c00650 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536036223 1250 536034973 536034979
    0x213140103110f0f09030a21271701091e0b010b0403051509010f290a030b0601050a05160c1d010501020604030305061c08030714090904080703020f010204060c0b07030c1d 75
    0x1542840018203a00408d5461040f405002904880c100d8001044002c0c909819440140181c1411904008088000701914500c008101700070801200c0c4034010a0039520203807440713004000403224201c0541c1c00c1203001d409420760001598940700f507160f007441984002002c0303a0007500c012180302d010410f4598002c926000000e0507000f002124401d403100465103950300300c22019101c01c0440c018400311a04a0282c400b00019425690b4444107040050641707414803202080030100070f44036100715100ba0360744645110080900e0301e40001c110f032846c01482480510324410019180c0c00000b000e0480e14140d00034081519607444c26002403e000c0c0105400062004000d844002091a1f100c0710318400d8103415524a0465030062041d0600f0074820b11500040001c041d83e99070341d01e0565049034000c200569101d045d4a0203a180982a1001602d154008680024800e40140395107461600a00c9501807564864070203c1c1110b4200304844042038a4001144109842103403600c4903203409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536037473 1250 536036223 536036233
    0x405040504020105130b1207030b09220f05010e010b031b190b120609150a2d06080717090a030c140118050f070b0304060f0213140103110f0f0903 64
    0x39080002c178003007141d000041c220000080410443c5d000010056204025140030898102c1c420000707500601e000e401030510203040c801102c1100c6144051071212607012490020a40c2c2c2890458084e0050b441492001c0d40703070000011590801103184202107071000b8ac800b075849541d0b01040452010040c0308200302c0c0c0c0700da50204035401d4030700c01000710422040007081640340450810079405001040c0202540600041c80203035107442c0e684200350b401c11480300b0304d40c07502d05145580010b12258408400c0c0307070814000414642107088a40240c3e021380c0d07083e18034071541d1050001c1d818169080d8040c3c2d8000c01d11680468031625801d520a8420141368144030a1102c41900f506d480f00030382100720410307420303a030204001002840d0b41441104081d00e0705602d465441c0007140001030025149644424450f0301080c0d00f54103c03894803007180030308805070391509640ea00d0b2603001100c06012a28180c03000c0320350b6400724107503090000d152120a2034410155110b250319001703440000d4041c820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536038723 1250 536037473 536037487
    0x7030804080319030b13020304300e0a03030e060c0f160f210201120605040908090108090f2e0c031506030c0e0d1a0a061404020408030405040504020105 67
    0x242004200600405000b5500c5081d2151800d00b40048841c0c0601807610b891500422a107520312000c401c1c01d010719006071282d99a0030200d120100280d103041c50032200140280040d8518000000401e03000d0303540c3e0310181c0402c414050000c41a01014000c0340e400580c40c64a4a01a402010380320743c0e40066400404c0850481490840703a00550850a840c490b001e0241015241c2400020702040502da600700e00c10001041c08002e814501034100318000a80440c101f040d80c00c110000c100140c0100404000d03400c10400c82d030001c1082d5800251510003081c9903070340c0001d05814065042010b005030050303035040540c06914040c052000e190200a9103541c2242521032200e02039050b89000c1090038214071101e00700c0000e81c009809061030100d00c01100703940320f004000d0554040e40c01000c4d40c049428000460800320031030ba61031000c1e28003001000c44107a00801c089445411640c1c40d000340b01e204100076400346000e08042c980c000d1004005603d03043c4c124a40040c0181000382c07409031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536039973 1250 536038723 536038733
    0x4170a1709030f01141519030804060f0c2003211803070602060403050310090507020c120a03020a02190807030f050709020304030c0605061f090f0806060a06110703 72
    0x1441400c58400e1110100300c0e07608034201400000740070076128000300902c010f00041002041303005003048035508003000c80480c003625044240b07d00303024040c5568030040c1d9a480c1c40001a40140030b01400200d41c1b4001c4103000b401004a1081550302818000d00311004000c5c2c45400814524125414850041190a0b04000101c40c188201d40c940e48030707a0b507407414888000030030780b000709980c081d40c0b05042c104511075000c10a02d41291781441d22130350360f880c2c040c1c505140e000e05400500160346018180204550000b41c00d024031036044d03130250042a00d959000351604d0207200044c02681084407581e0061500c510441c0d04004c0c3c03150508c0da0682c5402c84c0c2072400e407003a0400c9a0304510b5500d50004c0c0941003222000400c1e100d5400c0d4614a05990020304041191000402142c0c8420124407299200d40042c504000c015041ca8580c03608441c00806c5890140b14554209000040102e52400702058641c41818003804400701e080c54190100e45900a458020700240202040400010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536041223 1250 536039973 536039993
    0x9030304110310090506040203060c0c060c030403030603021509090609070c1407080607090303021c090b090a050621013011030604060c18080705010f030b06070804030312020f04170a 80
    0x1d03020b1720007442030740b506206062600130003034a821003203c0280101c0240c407100113500359000e0b090341501604c03a03c0e245801d402418150f0002544074140c40012000260004080c0520324406c81d29100c031a15104144a42000d0644001d80041c0c82d55030b0010103e10000c3c2d801c14200705040880d4030203551240c44a040003801d4495800082680100b0414103034104141e050b181428141d0011140c1e0020f0040c8c0580c0851140c5c0d00c85050220b210b40d06661074901c0e400041c40b010344030681e21003a1140c40b1000281345040304048a907008004109040d0741500f601d000440301525050b0303448001503208407a00704030b00807a4141010780704032401e501e041c00410300407841071801107200031a030301e0003800c00c80d00081c0c4202d20018070b20003000324200c0080d04008552007820041024950681c089014001d032010054220304005420302c1080305da00c000340201d80c000d03511040070340c40d4000300c202070748100c5d007025a03a54001e01040c44500d50188404502c42e06a01c12209a0b070307282c1c0e80e503101702 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536042473 1250 536041223 536041241
    0xb0901051c0b0102120a090e0403030f061502070603090b040b0c0c1902130c0807030c030e061f05010903170a0504080f01060306060f05060409020a05070519061409030304110310 78
    0x50303910380d11294840c3d41c040100b00c1d42c1d076600032445400d010848100a005800b144543e00c5e4254401c2c01042c05c0c94000c0c0d100d02c400080c0104d0611080e0344404500c850004104070007801441030b4070300004c00510a00c50400c001e0f82c03060500c8100d480d1a110001c03500c402400c050310b5000708010b6080c02410800c0b41c0469000c1c44c0941c08122041c80c01000100903100c0300c0d0442d16410810760201c001e87c8145c4040d449012070600280388a401c4004070010005081c58090750f119400521010306184421100b030680001c2d079a0380404d031184011258641c0500c4020161110100d22400341e9594001a0218103640c0c64124200b40c0d44000711440c0c1000b40810360b4003a50340d09001e100384040da010b1400907110900c400c080d55481c1c900401c089109034070880b554958041801110113120783d04496240c1d03044011104082c04024200c0c0082e0f070f941e28209d49981c03400c1014035099400c20109442000010059410f40e0785035120102640d800b0031a0710f5142c059401181380c001c0b01031044440d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536043723 1250 536042473 536042527
    0x3030a0e04180f060c0e0409080903010c090b03070f170a0905011103010b09041a061321020d03032c010e060a050919030e1e100c05070b090105 63
    0x1903040e0392400c0c0000c980100500241d0b800d80402e5100225800c4044000e000e60300c401c2c002820034910034111012065440e00303682c0306041c18414000c2c00b4a0401400d01345004500030880d10f0484070013034407800a14440d03c100d0880520000702c80078040c021044032844641000088002c1120b02514001030490301420102e035038030411400d00c10300344500b5045d030008210003851541401d64001040c0120100c0511980c1c4603062464101c40043d4070b0b80403840e0140c0000e49811540074410b0030300380f81d4061100306110014000610760380c6c0c2c1d40c0391140d20307070042d01d644560780c201e0320120040c00e000a80440007546400c020411506005040c0110880307000000440c8a101c0045904100d006009650281e0802c4c00348441100007041c0e0b24884652800341110320344892505640b200d4803485140d070301c201d8010200740c21a200e52005107844104890b1440c00308000042500c010300048400b0b0311640c00340805200c0054031100822041805050550400c00d61084006008400e003201c015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536044973 1250 536043723 536043737
    0x9090109050c1203041503020414040501051e03010e15070210050606030106050c011b110c06040b0412050703080c0106091b020d1206030206130f05150d05071103070302210c0c040504060b03030a 85
    0x2140d06622b900710100000f100d06211139458940090404c1150710482090341d1030700c2140c80c4103aa03003580405056550401540d00820b83d4654942000104941490150107080c072845002c1c2100d1003035510032070004001c10309503420682e04444c0364008803c801d0496684054041803242c0c442e0000c1d5450b2650f07030344c241100207125105801c00b110390510303231b000700300130300050115403402c6041d10150782011404140c0102c003802c11500d0300c5242c0c0d00281100b4070004006102da141908803071f00344e51000c0c03070a00c000164070104d8880710a140b40c284005801044058040d81e00c14007103480c0d84101c040c13001c1480364a9070009043c2e540704160200e081c81540c1c10400018400343e20b80c0005200880f850402001c40300c20010740b91056100c1400c400d5074484c0041c44c054040d6100d441b01503842c10841c2d44625682c0b030b000c0d545905602078000030308002038520710b0340c55501b81110f80040da031901a1646040c80014040039103000b500c1262244d845400b4407001c1d0700c0400151040307405640d940d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536046223 1250 536044973 536044979
    0x1b2001030f1505130c0c14031e09040501060c030e010825080a0c0c020102190f080304080a020705040b1011030903012313020108042013020909090109050c12030415030204 75
    0x20130800c2c0e400411a8066051501c0b00307041e80d0304064684280c0d40c05c00e528810100c060001641548500000d01c08032451001d1080100070390f40c00038000200c030903034041040c1d913241d50080e120b9840c0d40314002e000800440031401a5403042004941207400070401d400101e03504a00501c688038840780c2032000403040420000e903400c3c140692005c0d00900d0070100450b03001600001d480c0c01030016058804460b151062041008550016100130b80018299840303050a140112055004401c59001485800d4000c1a580342a114003040c0b030800030080c078400581004103a4000b200100c04000300d0006101c80b81c0c00d61030a01444000039894100d0807e42451182481142d0001400140d44c503444003a0440040c0d0b00808030300d401a03013103101c92103800c0141c4002417010b00341c0900290050340340e80b19006104056005080202c208440d8075003655142c14150f4229225190060000d5001e041c80002e1800d240d041d9511810b055000e43e45050303150100c2c10b04d0f8040300b01c1808000303175001030b0170 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536047473 1250 536046223 536046229
    0x17040b0703021c0c080c0f030d02041806050603061905210f0a030210111b0102090112090507030f083c120a18050601030501020a1b2001030f1505 64
    0x1030300e840c40540700f1843d00c84440328000c2203008024001800004001142c4101c00400c01a01e601022404110b9594000e1024000082d41080c132078072394003020171803d409202c8414003c1e00240c2d070300900070754110b5480303108100ea914500c224030804007500940101d0191030768100112407001d41c824140d880500185581e150441d0740c880004241c2005014100107503011411203800c06038106d000c2400502000514124458080001d01c1c5100c07180000071480310640150034a00426200e1000d07016201003482c060307800c03005000304142c100700410b0000070160f900c21600c441c000d0030064101005542c80c00c079001e185c1c40c58601e0745000c400380b060310009500710401c034000a141c2e80c18201509030010305071640b4080c0002e6026501c42481c940404600d109091613a80c100046607490359481c18200d00030340c0491f8070032002544203e031412005a00090112899a000001195602e400000d000740b966803e42024101611001100e10700780440c050304070705400011650584624103820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536048723 1250 536047473 536047483
    0xd06031a06100906080705090f210d0e01090e0a02042303010f0e06060108090c04112805030f040204020f0a11010e0f070506280503070e030105010f03030c17040b070302 74
    0x2d8042007020b0001e080c0803441d8068101600012039003007075500c1c1c248420001c1c8880c100d000540b034200c8006000c240c4400c0141c0b41007540c501c200c6064030100464800d0448e02003813401174880c04035078559005c0241c00d1201000395481030304003400508107501e800b41d524080603203058041503d01c40c40200d9010f0b02c6d0070300ca005028401e00108112088400415648907900148203a040c411803000040c4410018003d010200100030030811203442d840c540c040158102601258000c050215407c0d458081e104000c0314803413140c0c641601755515501c0c0103000e918010000c9802ca6000c0c4910700240c0503500252100c0b44a9484020704801c0041c0840e08450a020318041242c0c818124800205400b08507a0191201520030594030040722900e60380c41c08902140c520700194000b0940031050340000594012449543d80030b2140b400501014244c1c0c20a020b19041d0240c04101000024000d4214144142c881c03c002011180c2c0f003064507045030400d50100101003400a106030400d98140a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536049973 1250 536048723 536048749
    0x120715052101060e0f040b04020f04031b03080f180303071406070e150c0a052508012304150c180801020708042106060f0e07081b0d06031a06 62
    0x1107903005503151010060800c83d0180a85020795981002505036448a030402160154040c20075559030f105c0300e0401010b54810300c42591034000002482e5000e024058100046a4200361a40e0400c100441c43e01c10741e50010301c0070440f0b1313094140110045e0701e091014102990080c0c2c901c4121200c1011030b681007180003400c003410403154841c9500d46541d040c400008682c1188400d0313848102d2420301c0d5103030803001800a082845042c1c0311112072540c0c0c07000007805030040c503ea16281d41d503408555081e10400028148e10182280180d46840c000607503003523002e401106a01240c1851031900000c940030342c04500c00017000244440d181d20380c001850801890048021890003460340c0366039800703019074001d0f100d6000616503c88400c05007681030720002900210304100c003655940c41a80c1100c90b40c0318100c00880c0f28000034050341d019408003442520a40780da5a122591110424115803004104003190703541e800001c0042000040d111008441c1d4004091090910030100025221114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536051223 1250 536049973 536050027
    0x5040b0f0405100b0102190c05121609050705070605040b0a060b07080f0d020c0708031c021801140c07060e1810090b0409080304050102190e0a030212071505 69
    0x8003484000340b00014005035036401d00340001a02e44016004070300304120750f5000e010074000291482c0c10700003035a4000c0100c500c1118035098000080074882d8a42d8402c0710810640340d44c20008001ca815031703401855001000f031500a18100320340e40d59030210365082d1015070341d03a40c0134420405855400e11030345001e0704490407114100105907031500c181d4495a501d42d0f641a00100b004a81d82ca1590144d8039140000c409807070006880d44d080583d207070441120412003441c128014a00c80c6454801c0711041c0b1410720080c0d03a0f103040b410054400d0804100740e400c0e180c20402184928000c01c0c0005405027040742d44075121410032800300440450349505a129503e071b110f042c0b1817800d9805055a0881d00c0b2280041641041c1c27a002800404a000c409010030078000200000c000c410b60080a5032820003d803809a101d44071422208190b686c04256000212480144058074016400705a03504103907048030b40340b230340700c100c012010f00c05643c0303206c0880d40c04542c84032545102c000c2490034807940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536052473 1250 536051223 536051251
    0x411010203031b0d0216241b030b0112020a090303020715170703020d0203040c0501030510032402091f11060f1b070507180c0203030412050a020a050d0305040b 70
    0x1041e610f04080c0c41c603c06004010310004044d0354115554041e604041e4008034070700b0842d2a5030400d86280390a04200c841100e0755807110328019010b510035000025510740d501782e840c09080c042a402414210041414009070408049006c01103000500044845a440503200303403640c42c02914004032074000e14504070324070f0b00b940050b0341e0040061800c503000034070301d5180c0e455220f010b070003c0c481c480c40c001074280004100800d0240070105001150401c0e82c00700003070341d200242129440c01e10300000f0140200b0700c68141035440c4000c0702d00d21180011400600d0400b080d0300152040f26001e14119082c11810410030b0000c1d0455103d06a80b0201c50141541d0b180c214424150b070b010050a41d4002c0d00103803124000310b5007890a81e440180c1c0700e0111580702d40c0326003094081d403135004841c0c1449402c11a1010b0161700c00b10959002d07560000031200222000e00040d00c0940241d86000700310b200c1c215221021500400100500044c1600c00003118146402c110480034002440080725041c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536053723 1250 536052473 536052481
    0x150f05060705030d270c050a2306090a08160830030a0227100203040f0302060304050a0b01060e0924040c1404081e0c06030f0405100c08041101020303 66
    0x20103c00c407402d60025480c0040c0303145c2d003200700601c1c080030150903010003c004094442080300c1c0c4550801a5082204c61807400303965641d02c0720950b803050720550301203840c0101b02011410702102804215030b000f820341d40c61540715a21a80341221a00750b6544982542400300700c00d0a09105441101d0314680e11040c100760308640000c840c401c0e20700c4500c0003900c0000010034180071035050301c200b201c41c1d9580944040024181c51819040c1860440c46003401101c20315246000004a0f0100c4082065003030401e884c50b006c000301d9800003007003074846006d5004400002480141100c0c064000d40c2c44107461100d4440074040d64040040042d80710b40240c10322070802a44003c2c440124000c12240410514a20181122550b01c164840d90b070140000c580032907128804650606185000441f070440d0510b2410025554030328800c3d0f039900110204089a03000c13208050440c2d0045c0503000b21620401ba0f189280e088402c0344119100250070a001d100811130420104102e41100340300450450030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536054973 1250 536053723 536053733
    0x2833030908070b0c0d2d05070e0108090f0610060305090c01080c030604140c09240901180f090525020c1c050f01020a080a0606020d0309060f150f050607 67
    0x460b8400140440030302d440090065100c03081280c8001140360014032100d1b0711601c03842d0302100c0510040702c8245c1d0440700c40c0e8459040c1d00c0f49500c1001c079540c840d01c050040400541e650a4043c100b4800d41c02855032082c00c140d01005660702890070400c1254089181c07150040860300302415002c4690028206010180c0c0d00c50b282c9a000500c1d01002641e94031051300103001040300716280c080310240300042081c0d03c1d2205001d008081001d40f034031980f42103000354403150200003040709010a502803001180c55441954407900e50301074001c540c04502c0e2201440301002c0030990001200365103e00c10000b003070f242085001a03c0a0362016903106051000c00a510790011003110350040044410144038005403010005a51360420709403000d0710306520010b8080d42c07249054030049a811408201e2000240c0308150886220b54050b0200256802086000d004c0010040d203402e52035039060b0b0103005180c840c00210503040c01c01c1e480390514012142c0c00c50341d040d42c40548180003d00445e00856 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536056223 1250 536054973 536054977
    0x160e06030a1d2a060705061b0c0f030d0b04020a020a061e0608010f0c020703050715050d0f06030b01050303040b0f1b060403090503070f052833030908 66
    0xe41c2000410725411540441c4019044058205582e1140c0c00c00c0701c03582c400f000e01030310f8503d0302c00d0401110b12040d10103124480c4980d80005145038480000213032441403035200b00507418640e8500301c0ca41504c09004500e01509840800c900341c20000b0181800c1d14a44210494800159419810301500c2e41000e5100c2110800191416495540396400c1c241804070104a00d07140c00e2003008100c1c0c841221314020402104c0d1141c04c2da1622060301303192400041e41d44200c03513202d00200350aa0400084a02c1944541400c8050202c240b18450140410340240350000b1f40220300000e0140c503605104484da84181c0c07090f8000c0e0410002446480e90b410700301c40c542c05044403910340d107038501c0c2ca0301c1c0f214124594181101d030050506000c10140d011300c07804100c0780c0840c112890380e074942c0584080080da51041c558044000b080003001c51551030444041050946007a41c0b000d0341d5001c42c411403034a03005443c06c640d080b1440880910903002103501003a00726140802c05e01c03a00c1c0e69020464 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536057473 1250 536056223 536056231
    0xd170c0a0309061b030b0a090612061104121103060703051003081605060c03040515190b040e0d020f010e0304050a0302010507060906110a08061207090911100503160e0603 75
    0x154990842c0c07020310001e604001329291142040300f01001054000400800500c100c0601ca1102e000000804d425980607044c10345201d140110040d2016503035440041036142102090a002400b0000f610803424641040d51801041905080d000110405042c124020055000d0510345018400c0c0151035211010035660f01030011981d5142940030308821120000d40204a8801c030000c11440a0340703040078500861091044410141e040c070040c5540140899590084110707840c3d001c0d80c0300509800540d08114040c0000031a840701240d82414111540300010250380322003210180d600f424070480340783d40c1c030103800703181000e00b8140010451303040d921000e81000b034007056080500003543d00403100c0b03540c0000e00b0030400b284200c2520b60790b0407600c0307000041440040000d40c2401c0002100c00c0400c00d15011f0310480b0f0a2800702c0d03008005984050b06c22160414078020b1645403001d01000c1d461a036101c00c3c2c0ca038038005612090203904011030b28100400700910406035205c2005881d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536058723 1250 536057473 536057477
    0x533010b0a120c20070e13050d02031e07080d05070513080c0a090c0207090507091706060d0818030f0304050f0d03050315010c02060a080a06170309060c031303050d170c0a 75
    0x748038100a13058506540c5030004186018035000303220740c24441d030000d0702200d4410700036940e4800070040181d03107902800d80c4d1034111003180d504000041e00010001e001c42c611030340840b401c5c5043c3c0d00c600000c450003103031001c000c1080003c00e101441150050030b4024000040202140800e807008200c10f03540318821010580c5d00e85034003000e0306000748540009040d440700b04100c0c41c50a0760780184042e4003881111031090850051240e090b1010a4040c4600d0024000499605441d40c07114819805019202c422243e582c108132110b5030148010301502844800454640303040c4010080d190003c140c03c58442c00003450340200090700103058a5205035140b103443c56840320040141d03900041404001e6114100150200c0d51a420000c858021700d000c1004110392a151644112001c01100c040030031a4400c3c0400400ea2506e8002000104000000c0c4c81c00e205041610a090108940048510b07800800c0e15040003640310000e5401c2c3c110030b52030089941032101a150003403080a0603102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536059973 1250 536058723 536058767
    0x9080a120921020613030506040c150306240908030f041404090203061f030b270102160f0503070b01080706020f061003030e011e02011a0d0533010b0a120c 68
    0xc80c020700b501741d403002150050300f40d07000c038542490a40004211801072500c4440d10205051245120b803054400345d4400050747c00000300c1001c101400304030000d01c12010030126090100e042d250500103400341c00c003512201b94540341896800140c00205000c450700807440c1c1542003025030f500181c030035080000d012465000c8040c80b05a184400180d420141118a03075109002c501d042c02c8250014083d4500c114080c04940a80d02c1800d0780308444603160301071300309100e46010070044075014264510820840e0b1500e4840c0c1da135000c28034000da200d10f03215000300008000064041c088026a0b1003400090100342c600706100b11030300c80b15800302408108151000c40301c6030340908251203000171820160f0714070780d180440c003c0c041d208018036510308505814140b412810311040443c0c400e40d20038064104042d1004010b0116034040c1c99401c4407020810910041d09a80310b503160180091810341c980e50022080054111042081a603040e14a0440030030540342c1d0004c0518105151000400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536061223 1250 536059973 536059987
    0x10b10140310091112160e2209050a020307090b06040e130b040b090f0a020303070b190608070e0f040f03050a03020906130518010608070503040309080a1209210206 72
    0x10508150b94011000661408180c916114803801c094208281c030140c0c40000b80e6500c0039021405c0d449442040c002c20399080103ca01490090079a00240c0c0d401240103414000e102001070642e60011410b41d1590040c002680035818140003c070050285c020090000d1043c0c42c01050081c0715600c40c50914050040200d0901d01c0301d46105072a840d00030001c0131032030501e81440c1030400c900359400000c9100e100c8204011034004905500c0a9030003d014604000d180d4407264060b200c01444440c8000d10000c056000007000d00c600c2c400781000d00000d00300740f420040010800800a071100656042906c00c01c400076040103c503400c00343d0f05103049030300ea0300001e20944c0a401001061503000d000401c04507204250b1482c3c0e00b04940045480085000004c000303a40020400e0142a001408540005908a0091000310341203842407626a080719034401d003a500b0500118401c961910b45c840400801e954421424409040d0f4000c52019504101c80c0c1c0011544448000a01030000402c0f16 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536062473 1250 536061223 536061241
    0x10c060605030615040b030d0c12140d05090607051602040e2107050c010318110f040504030314060a14010309080c06010e010e100e070c0c09020a030e010b101403 71
    0x285005001c007500700c5045042220048150000110449004c1ca2400d41070301c10915000403e141c545060741c03075480000400b0b868000640c00c0d00034140050145000505c1c545041c24802059521501400000c460030103030301480c1082e074017408403420014180503490600c2c0d008000c8964160341201c0000700b47e002684058206003010b06c440c0c0710720000010464000d0711030402403022900c501c007550a44400c80d4015002c440c106080e8070b06030080110a1400a00070000440480d40f00400f03031065912080001410b5270b8080310110002500e0791900d05401c0400c0382d5841e04105d080710030b40803413802c1500383c00b44050900c80c01810943c507500c0d1702042c00341040450f424581000c003a103040d50784501c81c841c1142030a102d45045101000002200d00700c80490070800d507a02c41040f08196124508110713a0030444003000e5480c9444410005000750052000300841d448503180882e41c6c840064003282100d1501c48102c1c01070341c4d20758200100703540c0700c100c10100c05400c421282d207a03142c0041d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536063723 1250 536062473 536062481
    0x606091406031503010e0f070e01060c020d060905100c021b0108072a030206040201140909160215152103040527091501080c0d02011d150d150b09010c06 67
    0x1a4140d446e01403001d131225804201c50740300b000303042d04880c01203542e01c0702c800828400b40316400c0064061425030f0014079102404520040c090b002c0803544891a88441d818506848002a18142d40d5011060b0079034040c060300a001c140070031401c15104145001030210180180301c2d0f020800303541d550f60300b482303444000808826110301d100a002c00d01c07850040d594540980702a4045110902480d00a260300c20844e080d080014250b5180ca40703903680a21411803c04802c01c06501466040c1b454a98081d4541d5101d01c0000707202020820002080c05205060144441a0071100700300c2c031542180004201e030112841a546190003858a0f041c0c18100c180158070a040100d148050204240c0001001c036002090b0004401c00c59070b840392510ba40f0900d522145420500ca48031241c01b540c0542001045502c0c1a82c01ca141c10301403e000450785030200704165019000440c03600c640300c0302031049120909441c0a4110300c41e0802d0008155070048a07007907410801084011000c200342c2c1c0d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536064973 1250 536063723 536063761
    0x130f110301150902030a050c04080a0305541c08040e01180612030206150112020a0c1b06080f1b1204120806210109050706050d060609140603 62
    0xe0b269031a25400b1460281d4000c0c0e03020459981000c01017806080d8000c102d4080341c0448006022078040c03517400b511aa007020385030149640d072a40c2c070141410001103000900207002c0b0007030041c4008004940c41d089038400303490601800742c0200a5000e44880002034001900b502000c4c00902840c50009041d2145800110309240d0001c00001c240114550100f0085810300040c030001351621402165102c131480f000d40141d10080128038440921100303120b0180040c07602c2419611762006543c207990080c101030000038004004042400240681c02c44050451018940303458a0200c0060103071002404c0b80000245c03032001b02c1c00a8010400040382a01c1c2d8040ba20b0301e442421141141349181250140c406c828170345101d003080340c0f003400740780e11800000309007020071924844041481203460050689545d660744810001c10700810401f8001d140981e900c82d903c0d04111900c10a4401a40c401401d1264401d000c0c001e03130507a00c1f5070003607001c410764039281c40e5a00c1502e224641d1403550 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536066223 1250 536064973 536065001
    0xf06090206070807030f02031e09040b10090e010e0f070f021c03050105120d1b03030204181d01052202040212070e010f021f18080409020d05130f110301 67
    0x744070340401035603c014040c0d4501a0315001c2c03400a0840040e40c4910400244038a0b060712921900c444003168009400d543c040a84005025403443d4007260020001c641d206000c2030116008214141c211031400e400340c000c910300c074102400e200700c484802e03450240c40c0c1800d1140e0420200d8400d4401c2028070050b6000314034000360010ba04a014000384400c1c004e0500410040c1c10085400d0000a440b032003039039450b91080011848000d0602d0a884400d41c1201099000c11000554005101b00e103540802001c10000d20022810041c801420b08240039081c16410442000b50b0340c521140c020100440c012003c549545062000030002d00c15840d010029600d02824050242e50081d90f54024403001c2c0c8503200c510f5221042665a80c0c1c0310b528203c61a60480340b02c48000c110781c0c2102440340241001e100101856945083e10750304160405005558040ba0300000041d9038022240c02003440e201000c5500002d484402178400715940182007400d20001402541c0c40035408402c011001e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536067473 1250 536066223 536066227
    0x20d06060b0405040f2306011403010e0601090807060801050d0201111507030f0218060d1b020c0a06030b181f0e0f010503070b1e190507060609180f06090206 69
    0x50300d2207020703a0b007150042c0d0740100d00c0c02c480d414600003144104078801d800606031646c2c004614440b82c008800091286041010110010040728070103000345020f00040a200c00031441c08030001403000c43c2c9680702c41e4865011700b01c2000059042003d070b906541c0c00f075405a1854803c0e00040e600004000550089445078500c54042c0207800d104541c058009a03805000c01450701e80c041d8264050002c024840c2c0052000310300041c90076400914005440f220080340740c0b502030349088241c0380c008030004c0160700000100e600d47d10780b110a2401030b0401c0d043c20402031058802150b0903175400c0c5561994580fa640202e0940305c501c042d4050344058007090130b041c090f2541b4080010314002d403900c403801243c0c2800400c1500d000715104c001d0785c2aa100184c188850010242c00301c80307116103000b4214100f00036080d022084028088130604494850a40d10b03e45842c1601c21620b00750702130b0302440d03d000b9040c003140c1c03003020351404905e0304803551022070060342c10800010034951030025031007000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536068723 1250 536067473 536067479
    0x60303070c1d0a1e020d3209070f091a130207020f09161b061104030b180d0e04020c0a0c03021f05030c0309011b02010f0b060c1207020d0606 62
    0x1c07124201c03140c14240c0c400e0005407a0383c004a000c3c1e8442c800001c59820500c08050248003150f4068032100200040c086001041e84c08610460703101120081c40d000704c1040313172807800340b5114443c54110901200400040d45041d0b502e280301c140c01d00461001c0f43d11a041d01c07210020141c02800d185500070880d20440c0d080502080003544040705c1280110b0a50100f6541494884800c074421074a500354070940c00d80102086071000d01d000311005a03030800c1c1640d20041401803160410480b10f8144856071035086003042e0300103010040c1180420442c911001114400105200d140c0541c581410484207010310f0014020f409000050030051290441c0a800e01203510104011680242c1e20b00a680d00c111012845a0b482c40381c081020503810400300d100700581d58015540000e402000096090000e10a6510b5100812a02c40180c0d164010101074050034400e070703000020f049507450f1500701109881c0e904d0380001c1e45100c1da202408614901035440340356540401c154001d10401601c0d40b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536069973 1250 536068723 536068739
    0x9071707030b0321040f2c0612030c0703200d030809031c0b040e06090303070e0406030218040b09010b21010209060d0c080709030f14070503010f0605040c08041505060303070c 77
    0xc031b48116003000282260000c1e802a00d5884c0b0301200c40e007203281103400d00c01c84100004280e405030020740c00c5024245406a000024005002c0d00c41008000c0d011030b51035401c0400035081040c0c4419034115440810281030741e1003000f07810245506041c40e03006a038030391481d60300b180101c1d41107107070780c64a0943c4c00d240e075002030303012104950049a041007030040b01d560195492600f158010300c84d0384108017280741240115030060141600510110b0459142d5000c61030b030300c2c8d0940d00903a070182160f00340010060106455580003c5200080048621b1500083c461410410a11031070340101482c200c44e40c8000e40441e0004035000d000c256840c2c0e5412036840040041510100001e400000843c514504c950124000c89400410ad444007100a454803520310034540c110b4078080c0300e00100021552001e0091640192201e8400242e50749880248000e8035880c1e100d0070708010014003004002943d4442615000050801c005015034540003c40e1861140c040040c3c01c144d080f820000e6522 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536071223 1250 536069973 536069977
    0x20406020a0203060a090b1f0b0a020321090d050702130504030f080a0b01050906160501060f0302041b0503220c180b03071511010221040209071707030b0321 69
    0x240b0070740481350700c2e03519144020b04803440c0070340043c41e03140103c4c0030460b81d806145040c0c60b104c101200d0504825654402c1003625803100e0038483c0941c0010030581c07a112010950480c2018903c0d004041a03d48610203e4030740b610b0360412000d2100c045002e805540301c00c0e6940c483c91224207401c1080c3d061500380944000b000c9102c02002540060009034101c0c101e00030102005010b8450b103080c0a03082c410002c803504640034a48601900096090100e030302409148001c044031005556400e05500620040d207012611181c2d8a030304003401d0102481d03120013241c0d0301681c10140c0118848081e5000c1c42c40424480000d80181403035540450b0350205200046000302c11081d00b08000c2210b142455280d912a10441c402d8a0070303100c0c1e010803c0c1c025103102c030400741e140f0001071030300308882800e44000410052400500c0110000c020450404050817a00025a03040041c0040c1118103141010700327005000c0c504064841500c100162401c10030018207202d854400c9070651815400c03440c01d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536072473 1250 536071223 536071243
    0x32a030304050a1e050604030c02030a06050c13050316050909121210170a020120160317120402041116030e0901050f0d0b071806050301080d090506070b070e0402040602 74
    0x1340c0004200021100c4001150000554450302030300540e40c480d1015503203110548004d82e0140101c8003e800040c4a601c04c00784900b0020348110744030002030103940c5150303032260092406944140c000d40c1d00c1036940074003c2d046410882d18203d042d40c03a042c0190802d00341c0c0d50300c450700b00d201242c6a42400b003400882c7c0d202d00c0c0304080000c940d65603513451141200009620300d0098100340031600c055403264500510900c00390000e082e4415560100c1440c04803031111600d2a140c1d140d905004100200308008541081900101e090400b20004110b00801c040e0009118aa8824030803810315400c0040c0c800111918403001010746d10b074100588843c15200340782c0d1003a82d902c0000b10b45132410001d08600741801602030004a07d550392111a0040c000d4645414002400401c81090a07000d40810292406540f020344039423520701410b141c544210030705000c0c04409007040c05a038403010282c941103a08045a011503459085013596608079202c24580c0040c000540482c131260002210840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536073723 1250 536072473 536072483
    0x9040506040b060d08070f11030d050d14010803041211040c030203150103050c091e06070312110f0f03040615080a0519050d180b040303170a0608032a030304050a 71
    0x16640c3d040700300001e01a03000c000504c501d006100000100740c4a076029908180704807a0180c8000078940000d1904210b000d000c0000b4500086403e0440900c0c051740416010300503000c0030369410240c030386460740698000d00804d852000c0004051009013409190183d00140041001846a99004000e5441121901d05250040c04003e400394482d10030705100e000320609a900300180f04003007000c0f20a109690280400340303000040150b0351010001c24147d4400c0d240c0d022001d489010ba01e003954489216000300c100b0501260940720114411113000e24a03440c040c6540341d856260440c021302100010b420b128000a0000c01d02b841c0000340700c03604600440859142c0040341020050071615904024240d41114079640e810900500c0c09041c030101040c28481d40a8446446031081d41043d030050b000140d0078600c1e50080c60700c59082d2500020200d0080c0155030a0040441c2e4921890884241d0010b00007418400d424040721401542040c2805a95503400c5c1414000d5450f015801c3c1528 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536074973 1250 536073723 536073743
    0x6050301080c0d1e0807060e011e060f052808030a090f0302210f0604050606040608060403141e0408010b0f061201090f0f020a020a0302060108030a0e0409030c020904050604 76
    0x4003840c0140a0407245580810441111a04040340c010090407941c0e00b11030b917800038010040001c2c064051046008450000000c0d500039010010320b0b02c1c0324904148140900c5d10270240000c2e01c01043c0f0000f52003094500d0020b0100d01c0c11520890070b603503003001140c410013000200c0c003039070080010403641c3c41030fa07207815031592220308803001e1030f050f1300c0000d521000c480078040043c000141807551069100080c3d030314160030694000d003000803c450840d00d0340c0184003001030a10b407910415000c0c04483d0010202032605680c003509111100415604120340864201c00c13890310b08280c10401d04a918a90f619103560390300c898080e0802c050141e11600001c40c03078101c141006010f0341d41030075800f8820f98881c0d10380304024000b0074110189488554840c46207500c50303800c43c001808002d566900400e00c08165060007070800300180c00510726a00100542819203501104924144000321170001d0005003514058500466000b4002d4100c210316041205001c80880e80741d10880c01861095 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536076223 1250 536074973 536074993
    0x160c0603110f160c0b0a0c1704152307080c0708010519050903070602071401050705031e0c0904050f070e010c02090f061302041401110703020306180102040b040605030108 75
    0x14901609044041c0c000c0d05010299610f0710301c8500e490060300410070710080a4442d400d0b1100c0740d0020300204c0214401441d040100f10104e40c8484803103083d420034a01740360411040004101c00420210208515501d50411240200f010000c015209a184a03031b00c5c1e00c80c0c689802a5000040b210a950244a00000d044441800740d50f01c52186600d4405490008210759801404041c2509030b00d84000d000b0100003c01c07a100800c40300c4d010360480480b98542c40308080c20350303d0090016041000900910800c00b050400c961103d00351444420410340d903081103441c442c0503080303240e6401809e09042c400da0460210f900740c000c003010b548207004600501c00540e11a00b102c00c00035007000300000020150300010700003e801072401050380c2d000a50103680c100690f0010717004440c0c00d05424074242c41d55032b0400c0c1c2840b000007004014202c120f2850f00060b440305001810b1110f6041007130f18030b03014104298101c4000d080840d00342e903250790315000020241c0e0003d000d0314545c1d1207240d08078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536077473 1250 536076223 536076251
    0x5060d0b031f180f03050c0124050f0103290102120d140916032301140105040609050405030a0818010f1406010305160e040e0f0a030e0603040c0e0c160c0603 69
    0xc00549500050000501c0031139660458040c1d010001e107840c2035603100c400c03112056040060390300c0ea10f0600c0441c1ca4841c1440108107102d0f0844030964141413031701111b0100c070508410b180009a40039a8002c0c0340f5450800142d0500d140c078114400003600000351001000e0859029118040c4407284241d00381d0380d00101c06a640e03055102c3c00c408480d64050400020303074002c52041c0300e1051070b54603480554111404500b0b4580d171103d85002c4030307407050042c007450078144a001d0003400c0c42803080c0450f00b455102c060b03d0f48609580c1c18104404a4000340c400f4440e180e0300f90310094510003c009642e201d1407110000c4c5080381341180c661498a006c02c130f40350720900450740903d481e47c4a0440840b82c400b0242d9060b0303256414550095210080c0080501c402c0c4910800c0740020f1019010150042c40d000b01101c03800d150b20351003080203200780300115894161160507184501140b240c079490319454466603000780309401503c41c0300030041c0c1c41000410301014040310050384062103c1e041c03a03101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536078723 1250 536077473 536077511
    0x2040e10080a1136041b0605040506030726330d1103030f03090609030a0c030e1309080a020d091d1b030906040311060c0405060d0b031f 60
    0x30261840b003c4441c110010302e02003099101c03008204922080000c2a8190081c550350300c003440885a420000c100700511186c200c840d66940d0302080c0c3c0070403c2d420440c000e48a401240200c602034100400010316040c050450340e42135030202075403112903015078400c081100508607118120200c000c40106c41e052048104041400c0a00030a101d10640c1c2c4024050b215081c18400d40302e200f94621840c5494606000a00045080000d129030300d10f40850102e14244c0c02a20342c40d200d900c1000760404c1c00e98400071555035182d040c60b010089424000001d44003044003a010340380203240c058018108070108008050351811038007940c081c4003000354141d610680034840c682c900a042003109404514240b0000d6011542110b410311240302081da070403040e001103a41c139149501100a0206141c1c01107010f90ba41801c0000825480c5046944010940102c0c4562801140c000c25810480720320f40e08103c1103d90050112010501c0c0602104007200d5051031200d4140c3c940342d6544238100c41808 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536079973 1250 536078723 536078743
    0x60f09060702010909050c090306090316080310050307060807020c1f0e040f05040303060f0e0c04060f021f0501090f021206152803110a0e0f1302040e1008 68
    0x15005041a010105100d45075029072000c03410400d06403000301d5040520320407503020f03820140c2010f80360351810050600d85075000d88040b025500030322821620000720f0004149032540020341d2510717600c454900d0380c101080d42d0000d6526020b1000d0116000c0e078401a81e601c85d42c19075003207c2240c0d8800c4144060103501c5451922a14040310b42d131120b090240800e0183c0d0600900002541c3c03106000380000c0b1030f01514101c000940340e120400461404400c4030002d0a4809210840e5041c44103003000688614420041400984824480030301e0090046000b030450300c000308030035503c12505e103c0c0101400d00824511a1030844040e48462451080d18031200302018140f030031391620b800304194078840c108401008441086950301420310b521200d82d91100301c4084001d403000100019040ea00301400030303420500300340102c6510580c00f01c6150000d00c8290340980170100d12314045405503602049031a5558000070f4009061100c0182c1d09100394a840040d005480d240c02416496043d100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536081223 1250 536079973 536079997
    0x3140a0618120f020c0415030606061103031302010e03160f0605090d02061e0406081e060d03081b0a0801090b03070b03070e040f1107050706080c07140f0f1b06 70
    0x10b50300c40c2c581e4001c032004401103c603401103e44500310700b00084c080d103484a003054402c03180704c0010020841c85028041c090103881c00e03c6220000107550940c0d41e400300400206010103201001c0d800e5900850f20600d035801d015065541c0344004a601040c044018854641c03095110240000c84c141b0501c02c1c0c6445030340080c43c0d080c4101d12502000303400d4121511580b9038442004640901b070740c10318001c1c00180515110b801c980d14180c803110855141d0340c00140b600070036400030040a60380384a410208140e050400c412a034071290306800201422840d1680c0c1c0c1d100001d40075104617080b05e1031314125112041d050043d04a903030300345030712845c403032140b03a2000005002284290b0700030581ca1050040150001503e41c00c450000c00558181603686028600e00103615404d00005004180250029003007d40c200e08026820b46c030a4800c181025041d507900408050001d0400d00900005114100883e01c00095181c3c0e00c0d6104e001d9071a088200c01824400e1007084c2c01d140c8296001100f5007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536082473 1250 536081223 536081243
    0xe12030c1b030d27080d121103010504050901151e05240f0705010507090e060405161d0409030230070201110a0c0605090a0902250c03140a0618 63
    0x2e500a88098207880f042020f10070b1481150404e401c40c80c5255001080c0e24801405403902041010f8590010140054422802c0600007041e1200b0074003224110307102507030009041c2d641c4440b85c9005000d03203003402045082c0ca20000031142c002074000c0611680110b0221081d540c0d9404002502441040510180542081034000c0d41385a0000c2d10000b09a61102440d00c0526960b02d07084900848100000c282c0c540c1e002e11159552800b4660312500c01c0e81c0812090a1207114110140d4040000360108112840c00ca0740e5001d5074007440110303400240040c0321700d142c24507001e51140010490780b5804401400c9a00000c3c500f140140c5a12082681c0740c2d1a080081e0011a94041c0c50074612055206005074100000e0f04203810700700038550303980d03a50749524180e07040043c000344981c40344c0c07102c60061021b890703040c0003805007542141807aa480c074000708851400980c2c49a030b1794405000d10281c420032400c2c1c000c0c08901078004510075001000074119000c043c1c1101e01c003085014140e4a14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536083723 1250 536082473 536082493
    0x8010e011e0903090b0c01060608090307030207050402030a0915050106030c0f0906081008030c011d0a0b0105042a0302030a06050409030f030525020a120f050304120e12030c1b03 78
    0x810b078081e1a0550084c9859009a42c8501c2144143d600c40040941140e64410301007044a034030034070150704800d042028514104841e00c009603100e05601a0a12440d800404aa4805c0603648503c00c0a44e01840b10180e9200d609000c1004040900c42c20020030b042035115540b0707921071009407142682ea620349161940c00c10b801111042401006807a00601c141e9010900050400103083c080c0d90b01000814044d58440f400400d9094141d42d0403500c0c2e00000b2008006655401180d040d10015140086d10303060085007880c682e09803c2c504030480044800703180e41ca541c1034000714800c0c01440402d0000655500a10044444c6104050300040c1d07844040040c95100b5000306403c091180f80f1000075820350030348840d4002e00800d018000d03030b104030051802c1003450784950040c01c0d0903042040f8000750162018280e0301c40100020090043c012503601058046c4c416851001d50240c0178804150440c01000e40e250b000302411480d0348030b20003400302e0b07043e000c401841e5036200c043c000e030071901c039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536084973 1250 536083723 536083781
    0x50a121104020702090103110f010201230c120702060403140304030507081b1c0809030c0304051215010905010816140d0c1802041805040807021c060e0708010e01 71
    0x20032040e015445602000024050796a810313080d070107035004500c14406049441b0401040b46203100e101415039041487c00e0410005043c9a030b110380303c00300d0302c0c0405580d60708000100c074490740c04119100c03140102806901940001c603544124840d0f1a0340d5207550304101e070314000c0c3c0001c940c000d000405c100030301070014840b0760281c02001401d032105260800f0034030b00b440c1851045024280481c02c105070a800c1d15a001000f25081800c40019520b01440c43d1403284e1030340302e03a0141e0f43c000c0041101ca68201d800420140c07418440a4140003005d58444078100042d040c01c0c442c0d14081d1155122010001014641c01c0c0e04480b900001038016403209400e1050b103104201c001d40320074a20b10000500d180da1060070943e51034803a03c006030b0b254209005000d805030a22401a40240b600d4104000a500310307040702c50507901100c045072107a002c1c1008070307007100680100400f0141800d041010b0100002005002e594400000f4811025010202c60898129400c2c86061040d01000349240c61 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536086223 1250 536084973 536084993
    0x90209011206080c03100e0d051c0f0b0103230103021315030503030f0f0f070c081b0c030106050105070803010b1819091a01020604121b05010504020901050a12 70
    0x4401810700d9180c04080c10341203401c5072a1903112240a80003140c8803482403070f0602901040340f0600c00104040c00c5540070455642070703003145440901c84002882d000c070741c60507004400c40c0d5141240501030503d50302d1031031001c0d007800c03100c0300e020a0034488120071210aa10811052640b04c1d2400689a0301e5502041011040071100700d000d955030301c600307005d64204000345202840c0980021992400e10442400322810002c00d1200a1401e003001c0c0610300e0344411a40360880c4940c030340551031050a04141903d440f9280300344440d180c621605405a0030049800c4184410071030007004015502e20040d141c5124014000f4400c213010030050251408010107010300c6480880521920b055880108054141d4007003c04a02082034a0800c4590514000c03240d040c3c0348900c6145094000d100042d541d4840500000d04c004500118910014401c08200e0386507004219000209411403c040c1c2c001c003c20b540680c01504040004138140c28000542c004031600340c1548000f946d82612121144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536087473 1250 536086223 536086237
    0x7151d0d03050928080c010c060e031207020f011d0c060f0d02040b070c080307020f100e090a0603170301150516020a03110405060414150d050d180911040902 69
    0x403050512400e401e9445081c82003c0c9941c0300258490720307110020840c4c2c0300101991009076950b005040940082c1da100038080281039001102251a11500211900358080d04000101d103903050300800022035030000e07140a5490301800200600c00e5000603142c200c2c05550004140e070b5100110000b001c4c2014001410340d44c1d002d003041e5040803004000b40741079901035840080d89140124030f40040c000ea201c4500010b108900003546040019804100740c6039507502c1442c440c01c18174000311020fa000d0041050b911078024240d4510345464a060f50040a880c0000d036114410b8429400020007034100b124140d5049000d403101c2410b4503e021101175000d00190340440c01110420070041c0c0b964420080990b00c81d0351050308001307070f05061100b11813000340654861402c020f1031a40a0040c0b4002c01d0b00b01411090100300c021150002c81c0310300d1080c500c001c0c900c0c462850348007130f196171210f01040d4030b100491002c149181d40d50b40c0c80081c4c1d141d040100c001c5600400c810040415658002d001d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536088723 1250 536087473 536087477
    0xa090512130801060e061203040f090f0209030a030f09050d0c1511060702030d0c0e01080a05071103030a0b01091508070e131514010c0b04020f030f0d0207151d0d03 72
    0x7026486140050940d036465001010300c141110a10900b4501a200c051005076044021401d051420301005da1009903846071020722581d614080d855010550110380f420000582150410300d414a03004003013a0a401c0c00400182d0070030b1010640d803405804078000190007101140c2068201081c00a251415191310014030460a0803100081000e002d0a4814100ea0300034540301c80c030700c600340c4041d00c1044500c0c00820005000c80c030a86e0b81c00148558200c0310a0600003459a68a601a12105003802495a96110100400079104407503041071500c00030a0741c0d5055225680c0001c482046151110031000c0360b40e2400252600303208040ea40301c0c5000040180800c8880c50028a04403010755030001070104e07103400180181600c1483c03807400701c1e50038a4004245c00040d22103241c0703a00007500081c0304607444412174481c0c0c0d8040102e428003100400a41e90444030380d0310081d44d903564034851854070458164640802034040d689200c0000764481010000016460421080d211000003c0341 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536089973 1250 536088723 536088757
    0x6030b01052e090510050309030a0f0e0a0f03061103010b1b010902060403060c0327110301060b030f1005010201110a0810030b090102180406060512181f050a090512 72
    0xc02c0c074849155541c1094100d45403400300c0741c00c00062008850180710010280702080040c8240d42c01d0000c2110030000d03042c501441400e221113404c442c0e49900008150b0311081c2d054021942c5d907250400202103901c0783c8020013000070499112200e9002c24450f5a400040510198040401d0510301450225000000041107070440c1d00182d425001a041500c04c20340c0e0302c28034032101da0940306410b0303006481d0022811031071801005c59019039000d0310080100c1106c004907007070b41d2825004180905220200b442e128a40810311510090381110242d00510b0a0760000130994010702c10fa4214a0021100c00d02e8440100c00540c0c005002600700000301035180e030004041007605561a00924000d000036030703100c1401c98404500a80c0080d480d00c15807a0800400c1700d40d03007002c101c0e1218000740c03400300a603644410011011035650100c81e44070707004e2400740b0a0300d11849208611044080c078810011600c54001d514212404424000c0a40c1e02900202c08034469900c0500288201c43c5920350b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536091223 1250 536089973 536090029
    0xe04080d0504120225180f0204030501090203120f0f0307110604060f0e0606090f0601050d14040c1215050a0f140403020601120b060603060d2f0406030b0105 69
    0xc04640045806952045400b140301a045130306020301e1007080c0d0900009013800d0981c440205034250b03103110f000080442070f142e000d54008150008501078500d46000c41d00e071075503400c1540c041c10400788120f2003400782040e20700304400041c00307480e42c20159900003800c02d20400c0d602c401661000e0205414850b0f0903052a0350b0f00030401403180314a20508001c078201601046990990755030130100391040c1c2000c82008400d44030b020302c3d6a800018001912007946a000c0181c90b68400c3c00404038502d4100000300c420620542001400303148904e036240c4545d0750351854400c044020160013450003580203120018030b0402d801140d04011801d6000914607070883c18502100d200042c660141c1002c8010041811340500160340108206800300305030140307a42d5408111040108401c0c03080401101280c00fa456120300c030030a20354000c0c1c194042c110703444d83c0c0c07400c061242401c0d10750f40b0a441014008504140c000c5c0d404503580412620768990030700d01000000b0002c05a202c503e6441c0032040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536092473 1250 536091223 536091247
    0x30f06241308071517150607060e1c020307061505041a13090510052a030f090d120b060705070e0a0b0f0f010f0c080f040602010b0a06020303010e0408 66
    0x1004180611103501024502d854150780c100041640b240500090b81d003614000386401044070104007085004d01d030660350b41c05443c0d10008125016480e041750b00410305804211644d8040702d1109600d804495543c117029003007084900b003c100420050700140103280000b80c01c0d03002013002901904d06044030548400204080f06c910784658031100315441c03040002400d041208050318041e0160a20001c100364440d20750310007041c2c01c0c0411240c0cbe03030000504402002c8441140705420200b50604080b0020b561864907001610b50090031220b2501164032070b400025071000603841625242a00018084058001c20403041c82e150407041c100b00031400640140b250748080e08030002c00030580c2c2070500401c411a507549212900800da844007103901aa681c0c24082e8042900340307044010001d41c04c400721111102d50344014601540401c0c0b81a40312101805841a62100d80c02080a1000241000070030202e520134540903820400041c02400140d40e007050f4440e0103001550b207080d08a00758 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536093723 1250 536092473 536092477
    0x6050411030f01150504110f130819141606050c07050a060503090d110c0603060d12110d1409061b0a0305070b1501021b01020705030a050f060c030f0624 67
    0x41038403203035901d641242c42d1558440020024002c01c0d80c04020700c4841f068510003074030441c00185000c0501040001a141550818034042c1c84008203860f014030381c041e07185030a800c002c2e0301110046492002143d02e9040002c407034010350030000b4110006480c4c036105842660050700d00d0b505500400b9070204150f2104c21084d4001c00780d81d40d4640d564034142001034140007088111000300401e02c07050081803080041d04824a8904030f8660b40e030790302c0d6440010441d440f012002400c40c000e0803c0c0e10b070516085521604030748030006c1600c0c81540c600b0070071692550001c00c00c43c002e0758180b002003a80d051590190440c4407540b041300044514103141039181c0308400784124001000011108104400032075031a8200320006002102200c03054000b03510b50100c89010000d00c401c9104401c03007a0f03c2000981c001700009001d44481440d40d0803c035071100008001104584200741c0030074207541120301240d2140e6a04100c502064072540c08121030b641003101c81e151100d04010075411080c2e01100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536094973 1250 536093723 536093743
    0xe0307120606120f060b0f04140405010c02010207021f050405030303010f050f0a0b030a05060a050a0305060f090d090b031b0d02031609050d03120e030408030c0f0a02010c0605041103 80
    0x14039800e0202080ca40a801e4440603040103209070110b003d07070f000150800c0c041d1100d00c0e80c03001022613030900380307804078100010b03c1800d9540181040c05c0311824a502c440a42d015501079002030002c10000c02c4103074241c1c485c07943c00a40050400c03d034141810540480c4220703409140c40d259107440e0361140040d1a5410a070403501c500b9100f28020481c5241a20a0090041c001e40e0340c130800c146030042042030b5000040c81310210544503030002c0c0940d42c1e000050800b5010080001d52401d849041c410f54440b000c80da014460705030318020a060030800140354152040b95030f0b6001c102d5040c40c4825900e40c001504000c61032170085a8011007030358140203040100c80704000141c480c42d01a6481d1340402034515224140700c011401032006880740713403004007010313007608046107400488203448006100c111541c0344180008140450313108070102c020b00100d400481191111310007480b20585441d22520b000380482c028020328400038041c0d0308196071103802140d400350403035501008281000c0c581c407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536096223 1250 536094973 536094989
    0x30f080916050d11060f0d0c0e0637030608100204051c0f0803040b091011041509030c03030206100f052407170a1d03030d0908070f0c030b09030703080c0a0e0307 71
    0x100c0c1f20791011020780f2038150030901510b4501001d490002c0030403d14402c0240c110403031262095161001492540184004402c0d40745840c440c5d5101c01c4003c0c002c1c00c41d8000c0c080c0c1409403099080c4044881e0080e10151640200000c810442c0160180040c00780c404040300d44944603002d040c045075110000e18410f50040c81500f0051a120148a090014030f080c8058814901000080c07140480e0301690107076100c011001d0000d44e0076241c2030700d84001d0f660000700f01a0181364084201035010410b5406101c9081f5003103091038072440a20360aa010b4050b1540015040c00c8040b06c100000c2e50604031a00c0d1070352450714204c2184c4402e840c04018100811030007100041d0700d40c250303610406031700c14403c1501002d1045440c88001070b440744500306030a83c090b40c490380c000080c01301d65400c8801c01a0300c0101940d001a6619007800105064802584c082c4035035000036081d07042c0801140d420700d40c95030f66030702c40360384540403080d007500000e91400c100103020503561115203003001204080c00d090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536097473 1250 536096223 536096227
    0x9120c16050d11010f05090303040f050103151409040303091209030209090708060c0a0917060a1103190e030f0a03090203010b0a0e010306020d1503030f080916050d11060f 75
    0x105890094492140e00103800780002d0060803022400c080c1101c0311029007480c155411342900c11089480d03014618110354075000015001840500010903542254401c0c1c80510034050184030108900784103218003880d240c000300c1407142910f000c0b040903a000d8420705002070510480d407039070400300c0c8440c00c4c2d102c08503013480d02c248254580401c15641c001e00e0b401c02080b02d242071400c684e03294000a84000028600490711101d0075014000e82d40c0648200717503415591a03107400d1859683c80781a035600c44013625014030707240000200c0d8102c0744150103204101c440b04000c54503001c02000c0c81751102c4030602003071000d1103803410741c4002020750340c0143c3c0d004140e0800b00c0c0105400c5403524884144501801c40302000012202c2090700e04594005000589411f680480e41c0054000303020f40c0001d03400400d5011081541003d41540f004030b47d0303030750440c05076103000303180750f80f8030854840ca00c654000100801452404158951100748102101080c080720800860541e030400a0b80030040400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536098723 1250 536097473 536097493
    0x2e08010209190810020708070212070f05040c050318010914030706150311060c03070c0b0c100621020a030c300b0406051e0c04090b0604030c060809120c 67
    0xc400c20011800340b030030110510391804010356907640c0400d40384040b940c0c0110f284424801004150b0f03c0141e005024581c1c407070a92403425480b81d8580c040d000c58480508000714580c2440c2c0303d4480e040f80c1c25140c8030320b59100c602c0c00c0141062074004030b120540d00c4c0c501c8440040c401c90000303100011554001c2d51103103020300d404019520311003590861b441644008101140c0e61403060400700e00d007620b8942e501c0301c850f00400d042d4030500002038100c04805900180071004e040003820f00840b0700050302c8402c0c5100c9a04001d40319984528646000c072584500d043c031b9580418021020302c01044840e80d60340c1c1c6d41e112a411240e80d480340d0175141509070005050f41c0c0810109405018044031803448144640c1c540302c0803a400350001d8001d42d690320001e446070010b031181c646075044080b00d41d50645000c1e03c2c00c0005501034040d81c0c40f0301d03080441392010350a00409441c290390340101c1004800c1d00348042221001c1d002030060409100d410803148503609013500800560b889c1002034001307426 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536099973 1250 536098723 536098729
    0x1c03020a200312040305040e1005090a1401150309060e010c0201140403080103201c03030b0d0209010b130b130801060b0a05030604090606080313051014032e08010209 73
    0x1840322150070302200c001d6003807612404411524078040d00d01038001192114201140c40e40115003225460348408030500600041d082c036004210350044601149558801d45040e0648400854840214031684014844016800350355403600c49149000200020192584003d0f560503070014000c0383d64824800c00440e5082c0180202c101030a140da01d568202994010074440c414440601072070403c694400031070301401c90182c40304a00506013441c0307031000403915002d000147c10881c0800d2810602600904044403803d000580080800c1c0c0c40740e180c4490007000f41d00241c400154200401404103c0008800290000408605140381003c1c1030081142c21680f403a0440a00603c05129000302d8640c0302d4122540240c080d0340108420078140340c00005000e05030044c084500001ca00d031003241c1c081d658140125001161003c8002c9000380007a00d10f1ba0125203417042e0b01c6c0741040000d0700842c05260fa4820704100d2070010800c0d85810164030540340d407940004410342d40000e1001d02c103107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 536101223 1250 536099973 536099987
    0x60a080906090109030f080a0b06180108090f070b0904090c06020618030301050a090e07080d2a0b06010c031701030b0103031d010509280b03010305070914040b091c03020a 75
    0x400b41002040402d0340c41c1c80113095620100024010001003e0001c0c955500a0300584a00d04000d49017a84444d0384580c1c280c458032981d2480c0d80012140c00007d60702010004002e8440542c11015104032400d01400000503440411011b41003915000c551000840d903950307417401004590301a04003030a0004804d407060400e2400740b0050390003480188040d69031100703044211051a0340003d000d9035200c620b982401c00550140201e800303003443c001c0206410410031520100c00d10601e1506054002080c0081200040c0140007403042c080050000c0d4018a1000344150013414044146000c02c401c0341032419091300100d4040c0a000e0042041540220702c00c00000c100c1c04400c00d07a81c9031500001c001d03005e2180441e11036404150250015445c504004007041d00a172145c40c1125140e40b610b035a55802848100ca95100d4084001180d84083c0b00d0205588501981c52449807969203d9465581c0b014041544600480484040910b1695000029030380c15840168885690301d2014202c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 536102473 1250 536101223 536101231
    0x60a020405100509030a0b0a0507093f060606050a08070e031515030105090703030206070903150504060209061305041b021e01061d0604050109090f021509060a080906 73
    0x50040c40107004a60720301c00c1c06061560701d0f1904030340360720394030000920300940d007480a88098014002e0280c80d0700350b42c214520030102034a8003520940e4804481600c0e0001008a03900710b03034444405a40510b03507512003005109103a80002d19203d02d52610b04c22550541d10120100ba40011010380550300f14848591005507070402019509000010a444800351105100140c584800283e580c000d011540061508040d00802061600702c3c0030940d1142c5c03501043c1e01510a040c000307240c05204d1941d14050326403100680d1890b451000b9500c01405e000b5000b220425003d200e003030050307114803010b8490840c0c0740e0b001e06034280c078020a000813640c000f01a82010000c0f00089140c4540018061114500030031340b0282c51495100701d41e00500c0349810488001c000c801c0000c0318403203c18411400303070400f00d908100a990307034160001111550280104840380010380702016203003058030110410595640315203445012000a122a8002c402213030201d0380300d401744210701208015050380 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 536103723 1250 536102473 536102491
    0x80105130b1f27180501060f03020702030127021e010c1b0506070b0106080c030103020d0311070e0c130905040323120c0a020f070e0112060e0304120506 67
    0x3881d0422010840908101500080d406030b2840c484082500c201c1d600f0f40460240086003440641025400b12401c14038421810749448060702204d10208503c1294101c5181d0f03115070058511901090f00030750004030b8117a038955642c00000c40022034580e250a4000025030310b203205c581451041114404c0403002d4100c000d00321145034040707660071003524282c09411001500280c41d500040348216440e0b0380195820a034045140c2040007a4954a11705840c896100c41d0030300c1ea00d01e0782a52a5000903c000395100840b02d07502004207004107011000d01d10854141e0342c0845d110030050080320340c143e1f40003042070b2001688110610210110102070002c542003270060b4102600d00130000700d00d2504802c4813051050055601e00b41d41c400716030540300085a210101d150100e150003154105c80c2c070340e6015000c0d104034031003060000f2a1240a070382054034040e0141c3d003032085500e0b03420103840c0c040701d1080d41c4100120001c80c080001c1c20042c03a042c92605e6500e03049142481c104078028080c124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 536104973 1250 536103723 536103731
    0x2805011b0518040b030109110a0603050702030a141201060e040b030304231324081f0509010f1b030c0503100302010f0e130e192a0b040608010513 64
    0x12032140e2210440c1c0c5000c003015078039194030741d42d90002001840385495140c2e0540c60521804204502469040040c450445403051155642c440a900f03507041180c4190058008215420005004020041048000940007418400044145071388031100303810a00c04134031b120031500707010b15080c09002061a400d901a609140c0760141a40b0100c01c1ca641194009180c082202c100d40c4070307040c0121000c00c0900051122810030354500042c1880c8841d08200010800c1d03010a050000050742100c3c4244100300c440342403404081a001001c01500240e51035403a000c002c1c16002031805020036404a40d80060030b10800358002034100d6a0b002c041a00b070007401d00c00c0180186601c490340e02141d40a0801050310003590808940340415815101d43c407068021442ca0b01a42540c0540807458a41e400c4035440141444103031801030305840d00400004000c90410201c44101d0350200c3d086401900000c4199104c442d00030441d08540c0041c0000744100004210519100b0705101e0061901d0000700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 536106223 1250 536104973 536105021
    0x70216090c050316020a0f080337090c0b0f120703050105010918020f030a0c11120a180b0a111b0904120c0501020d09150c0818280501 59
    0x60040d003c0144500c0840442242d441c200314002c0c40038103541c0350f01000244c450746291030600c1c0c40c0e400c241e511184400d80705242c203204100300b0f0b005110f00d52950107204102ca1085840d400907050311141180c810440c0309000070100c80c00c002030205c03159031841382503d0f240100001c0039111402406441010b08081c010040c99070050404d00640741e021600300c403400b07201d46005000e48121030700c1c500803404c0041000241c608681c4241e50b0400c983d65110145140f0399009595842d0001c0d501003061030401034000500d01034845050f208254801145680c4d595280c8095a50045040c81b4040f5015100d0522444030600040d480c00c02550b103060b544200c800c0110b03070b04200040004004003050750b040740f0040e0003007107012032003584072000b0741d40c8034003254201c0085d0003029011982c0c500194262811000d00b4083c040c03401c1000c0d80c40c128513988000c1e2283e60030350f614503080da075405011800341e000c41c00c140c00518801421042c0c80064840da260003400c55056102581558204405078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 536107473 1250 536106223 536106227
    0x90d141f090b0c0c03090907050a030b01020c011d03070b0c03040e1602120901120608100606110604020d1b080c0a151d0a0906080a0b060d03080610030207020405070216090c 76
    0x300ba08440b0300f03080030380c9501c40d60160074614820822400e50002d040d00406c5074480e407050041c001030403a5039040c0a041001001a07030341d5260221000c0c0400c0c2064070103160320013050081c01c01e5920081c111074038159544050320f00d80d0b11001d0009640e400c002010700c400c4089911054104600e440036503024010840000e4603502d025581c10900030000a512105178411181500590000c4004100c190790700c02c4c149603a8007001d169003560702d04111000542600944a4107100c10301040030b0072490f55036600b000f07a00391070035404440d01ea18408034000c1c003c0300c000700ca074094503400c1d001385468042c0c00100b0888840e240d000810b02002035034001040c81d070100c500c14446000340524081800b081000820440054102c12185442c1c050300003000f000009211138228002c1240c0c2005895040900692000e0341c078019000c107047c400400c8281c1480420a40384030702a19005050010a0b8001402e403a000c0e02e4040c0140d0280e5620400f800d000e045110040680d40401c1088840314000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 536108723 1250 536107473 536107493
    0x6050106050a2106031407030b071d0405040c0e13030e0609061813140a1a2b02090705030601080a0501060c031107030c080f0c180408090d141f09 64
    0x20640c40300380f0900301020f1400f482e400600146501802203404040c03603c040e141c0c0d59005100594400f1300791030106400c0e5008072011103072500c40d00f0801242c1601442400064103010300f0444102d51507050008110040c04021801240310808400c0316100303906008050030409820f152081c9010895480e00e0380d03c100c100d4001003055074954140e10f54100008003900081440c2601142c10504804040c148002e1004c2c440c1e510b0710b00c10405504100d4525002d200c00303000d05900040320400c03492038801d02c0301c07000346100311030089007082008075808a8101401517820801090300402804115a0000d5400341d019001140400c969031400100030a00513200202070140b08240108019021051017550099600240d40034119035807044020b03911005200c03007030400c1c0601c0c240c05071b0500d0403061041c9c0c031050304401c3c012180c407192114011039000d004910340c41906030420388001032100302c441000307014800c040d0030b8501c4890010f05620a007102502086890829004002044000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 536109973 1250 536108723 536108747
    0x1050105040905061f230a02150a090203010c0903020f120d030218030a051c1d1c0204050f0709090905030a03090305070b090a021201051605090103022506050106050a 73
    0x4004a45070703c83c00c000c640c5c440c80c0d42c01c424007168170001040001c281c000b0003581090151200e06013180d00300405d041c82d40e0286040c03c0700140c101d540286500c04884555603009182014001200d6400d940000e0854460701c070305001140c038581c01003003546031800340201c403500141c451080013102d51800341e03240c054401415090560104031803550412003074003400c504001400710780c0713080301e61304055503204015580341d606200108400121a131084c800c0d445030015884a04031101581d43c01c0201d07501050400e58100c0050041010159070395010707040c003442c45140d850200b42000c0703070f00401400d069049885000d007800c50501c0000c0d000000c884040e009e80c5000903142c43c0a142c01c503030600c030300440034200c510ba4038140704002c2400b1554030f00c0c40e48215103540c60034243c0d00210b0f080c1c4100f180c010031a403641ca032aa0b00c0360360065005120814051400600d06404040f1a800c9804140c1c0b18540c48042711103018100551380c40b800d409030202c0d09000b400c0c9800400001c1c0301c900010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 536111223 1250 536109973 536109989
    0x20a0305210c0702150c03070227040b060a0501020f03031504111306080a0507020c0108040203030c0f071a0702090106050d0906091b15090b031b071a0606030105010504 74
    0x1c0d4071854079003141c810040000390761a41d41682c203204000407101e8114060603881100101d106114940b00725046640c608040e1020f0360804c1e91903002c11180c15a80c010407211700d40d184c0d100c2030b00403600c1d11313134a803013184103400701ea1082c02e00e8410700c5203524064021506540c0111485411640b000040c0e0340e2051400300e9000188400f5404503002e000702c900b00008400340881c10040d2100156440e070141c43c4135030b80d124415a03178840306034240c40042d135011000da00000c0c0e464585501c44d1680c07541c0a80050110380c501001c1c1a06103203400c00c0d0341500c21440c2c108088c00d000080700242010500d100c146002c5042c03403050f40010700540f0701807007100c2c01d0001c0042c000203058036582050140f00c1e0442d500304405417540c03c0550082d414025100a8030f9000040841d0424807006600d00e100703016602d50401c50304115840282e903001501502009a20045040c1c4c1c44920400902c45c103031090342c4a01c400e00f00d483d00aa6400c4001e00700301d03c00d0f1010700041c8800d0340d0150a940860f4541 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 536112473 1250 536111223 536111227
    0x30910020c03070204090503180a05090f06010e0303030108010e101109130f0203040f020f04050403091202061201030503090102070b0a12020a033c0b0907081807030b0f010510020a0305 81
    0x421085185124000d4000d400608001ba045c0c10302c070010024261030f0007103201100e08802010108118080c280c003440d5400003010002c111040402006103074412010b0600d404030f204100e001030310311f8009074043c0e140c0744c3d1504446200c45030709000c040002414484140958a00c8c80504851409000c400c1e600462141d170b004030854032241c000060103501010f00719502e080600700003842070600c5105902030004500418403a0526108080c45640c1554034820703410700340300450000d0029540709907030001c0c00380400342c10307114007592207402544200021a034a2050400180c1000c4695001809520060014091054100b004038101d403245480040e601c004500e401c2d070003800482c026200c01d407a0500c1150300054402041c0c80910303104015444080ca5000a0310291a060241c030741e000301814001c115020700a0203040d80080a0030070f14022400440e000c1450004151700076500304c000d04060042e1603916210f000e014090649100910f803030b4001d00a50344904002000b4200140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 536113723 1250 536112473 536112487
    0xc060909060d0b04030810060e01090e0a110c0102030601030b01020604240603060c020f010608010c020c0f030c2205010f030308040f030e15120c2a01110a0809010b030303091002 78
    0x30300025101400c2e403000741c250f9542400d060003420400e048406174504100c0c02d10100d01d003806404182e5030800c05075504080f40741400b01d4140300c45805440d403613034180c80d804143d01010906010381040500d9000050305c0e850000d0004003552603a40015066400000c20710000c100209501858421526844421800000c0c071080c02409241c9c0003602c01450f140368850819400302e560141c025100000b400356644503140542201c0740c846c04c10000d82d020140c40f000b10305020f213420f20b1411000b002e40f40e1880641010034500c0075580700007081c0318040e203c03070041d80e81c0a105090242001c8410245402d00310366001e05025009840504406000090903080620981c0120100c05001d400896200c0513140020029045219108500102000000e84886032101900c1a02c9102000003880348183c220540f4005841d0320144c070f540d501e50f04e8460b09010150020f00603880b40c0c0d0344070036031843e1100549084448070301d200c91103034108105202c000c4400081810b403960507540300690340c0074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 536114973 1250 536113723 536113729
    0xb060417031c05041119060834170105060301030807020a0f14030106080f2d06010b031801050105150a031d01091505041a061309060c030c020c06090906 67
    0x10311000c0030310000e4010000c030b1401169801c550f000e248129031041c03c0b0740710f50f8104014043e204480700408180c8080802042e40b02e0380b149900070402d483c001c18610310010511201a0f00200f280d07402d946115142c2e80c2c5d190740110700004001c1071510b44c00081d4140000108280b20601c409400e406000c110182595503040c1c0510090400a000d0344001c5c0c2d0700e0100c001c2c0e15042419242c4694600440000c03006004900744580c00e071104003500b50007000b92207201c00d1201c24054001c03072000040c001038054804002042c007038079080980f20f490b46000c82c0605904d0a4440a281c0981d060130010840c07030321041000b00805581d2a4015200d00d001c0d4011001001c05160050b82e2500d004540900b42c1d4066001800340c034000d2840702c102004170503a96003070301c5c0d040c5c074014034112481e112a00242c8071070000942088000300101c0c2e1600408100134140c9011010030703185a0303a260f421940481d0948220500291140050043c2c1a4000d00041c818081c5842542c001c0c5030041c00240159 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 536116223 1250 536114973 536114977
    0x80a0f06050a0209041b120608061303210f06060e150d091e0203070602060c07021e210d03090215071106030f1f080a030f050904021c0f0b06041703 65
    0xc000341c01000f2801c8524446c5030481022407907000462400e420501d014400c43c0990815107268100400440d1110709196103410701c0c1c510260204003004000f400e59404801c490b205036000703210080740c12500c24281404503051a03110304244020080c0100702c90f2a01d40c2c2c000780c5844140000e0361200d481c804000042c014124005095113008080307021060f40c0840909440380c002ea040b1506203441ea18140e0307940609482c280c1c200c560910580e0018a401d1000b095034403102007040400501ca00d010410080200082e1030344e20680101e6215600400c101f44400c3c040f42e4a400d000c140001d801260b107903000300040d441c507000e000690380c0600241c1010740d502c2c104050719050f902d10300490007601c805000c2c0d880403104150b1403905001c410004c010f2105855076440a0107481c60982d50a8480c42005860320782801024445400a0383c1d031351016002c845000c82c1c0e1104103103000b0814008131a81c032454141d00c40d01e065069a02034880034140c605584150390481c080300000d00d0780354a14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 536117473 1250 536116223 536116237
    0x20307020607181505030a1112010e04050114090a02040c0207050f04270c14040c0e1011070821032710090606061101050411011b0209160801080a0f06050a02 69
    0xc5003d83c00c101c42e15503442801184038a85010b010413030301c11841c0e10248c0340e00c00d4610301401c403a01880107122140007012410342080c41a4000075110403000142c842e034110445078000140c100310300d8103040d030030a13000b0b10501507c1480540325075810900020100e0741c4d6000840c1c001e03960fa0015050240703030600740481c68100d545900313420070007a20f04103070b0755051805203074050401188801941d0810340035603400c1c0c0b0344c65202ca0707460036059024030034840d1780050610100070405080108403d010300c40c01014104e50000344c800705640c0b0780200003181108501d41c0d00a80f042040201c034201100d900038001e401501840c500111401c1840c1c03620000003124584285404080001c010b500d500c00c0c01210340300d03150142d1560304a1252402c035603040300c1c05069441d1103000e0151a62041c004041d001c00341c488840002e450503000f088040030220f68031250b550480e0503424556805c01481d03801080100e0080461700300303a54400c0100c0e59031036002001581c48001245038112140c05544403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 536118723 1250 536117473 536117489
    0x1e03020d05090a030216060801030311010207060603110a1d0601180f06050d0e2409010908220b0f040303030513061a0918061605120108060103120302030702060718 72
    0x1450a200c803402c0c0d11002818811000f6200340b070380803aa05580600001c1c2114a40d484450642c0e281d074905803000d060000e80b41900c3d550800003103002400c0c3e48116006580298800b859401c440e00034400c1025840c2c1081c54440c001e1803049218490090344103a10080c01c0c40d07c117903031117540a80d040e100c10300b50b0854040c01710303031000104100e940000908243c110401c1b00344446007400c04d402d80c54440c0ba420b114145c1003d40c09082d090081c0c0b000464200e00210300020b01345a55482e00304407500606919540000c07131000e90b03140d040025a42c5400340080607055441c19801c10403540a612170752100070306060311a00069403517070203407542d5001c03070344c20a20a2008100da80000d4000642d1141c600344210079010124941c4400e00e803006032046124070061103543c640c180004c2c862101c1c40f140b07a0130000c08215031440c10840a200c079008001c4900100301c5941903190030400511420408001c040c814800c0100450340022482c2d004100303814071a40c003454501c25103a2110a035000095 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 536119973 1250 536118723 536118731
    0x100f0b031f0f0612030e1513090506010201020306030a0f020a030221060a02130b0c0c0d230c0a061803050d09081006060903150225020418031e03020d 66
    0xa0382004100d2064400740e0200400580710b800e502039040341c10b03901035110f460440400c0800000e01a02820307024040003400c4543e2115018400c4000d0b510403680c95001b0765201d0b00410106249008040d00710001b40000e5007140b4000380803a07a40c0404c8180544256440549242903460b80080900610340141150072180000d0b000310318031089044a40b07001e84151000a55aa20140f080c0c0307a04007550300c2c2c540c41c4289410f001c2d11513500a0914000b17070740600051600700d6134440c81e02c48450b5120341c00880ba50384003018045501c802d015103446d169004074011485513612403002c00291840d0303081c82d40d42c840da11a01c00c8105191038000801c0d43c803840442c42c071840e4100c070102007259101800c884141000c020b1070000c0c0c41461160300c012031004107091001030140201e5100f030021112005042281a040404e40140071101c00c2c021843d208082c3c00540c2020702540c41c0401c000050000307072445541d002440076006043d400d200c0c5207000c40d084209440790701101c030382d009004420301c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 536121223 1250 536119973 536119993
    0x80d02030f060f0f130e0c1002010b090702011413111008090c0109030c0b0901120c030606030c0e18070201020f071a0f010605161119060e0f03100f0b03 67
    0x4284680542d501445215100d211070780500d031007642040d02c65406010358050701c40100e0640f003d0310789004410170703c0c0074550800d0703102d440c0d900c400b40001519500215800012005000e1b020340f024202c8001c59042040c1890b954600c18a8190440845480074040f280c0c5c500749109121038203510690300038010190002c90b9503001c20103d001e011418103450064a0010055684e0005072000400303c4121817810050103990710080c102c41801030402c12107900307100d03002000b01c5d54118085d101113550755030f0a01c41b155251003406440f41c4c860038031642c0302c60440300040b01a120a8411f2005c0f00c0c043c00020b060710310030b405407801092103c2141e525040d1518100104440c1c192105141c0241040007a20b904044849281280e14948406182003001d03500802449000c0d8015070320034000795600b240380e450b0403461100d008e000841a43e4201d04200f0001d020110700c00c3e100348960328200b1080c4640da00880c1d41d92100d49401800118012007014038800307401c110362110b906000c5c185070b034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 536122473 1250 536121223 536121241
    0x414090c010c0309080a140d020309010806060a031515180b1606020f040806090f1f0b0f10030b01030c02070b2502060705072c010b030a140a06080f0a1a04080d0203 72
    0x11f000a001901900c44c08a990340040341d07280030f8103180d5800a5040300202d516410242d0003000244082c1c0303800b0500000410b00303a8030401840e1b000c164a408401c03403c8207080e80c04440440c90071400a414940145409220200c60040701d03c01491185040482020410b00c0e80c121010201f240000c10384032981c41414603140c06084840740498040d400000c403020781c0c00720b0840d050140024a02001000003003520009058408070160025103070066961103030385042142d484911907507004544540007800060079140c401e01106d09541c0003400c1400800307601002c0d20015800d10a8900b60122000b0104405184900c0c010307400400015280040c418080f41200c161203000040c17046a8070304604069032041240101c40d04071003244014001c900c1000b004541010400d040845c01c540005005900403005039141c0803d6560740204011038003061000c22819000c0c1405005040007548500c888122801030680900c03e4035000941080000f005585034000e045034115100d00d0a0419 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 536123723 1250 536122473 536122493
    0x3020d23010e1e010504210507150507180f090c0903060f0e0712020312160b0703061a0301210201180e04020f0603060f040203060607021507020414090c010c0309080a 73
    0x40095000c0960803d482d07081e6050007a1400303140e0201319240201c4498240c0141c00c0c00c41c040e50003c1010810041000c10b1a8040d4403a0261252a00245078289030101400302403180e15a81c010003407000f010010004840c1380302c4110b444466001ca002500448211003a0b44e80c0c0c0c2000f800746141c0b00c80d1600035003503a441400202d80a0f41129075282c0c80b1900688910662407000f94590712502941d41e039400740b4006014202d1581808145c10145a91442c500c2c40c01110407000090351a02d0030000142442143c100e0784130109a01032a550514100c2010590200d40010104442c40070860869101d50700c03001c110200840d441c041c1a0b26003002000280741a14264400c201071200940030b498103004031317030060f0350040c495942600d0380000c0c040a500014002a0300c04414410b180160b20b0300b1081c444441e00d00042542d45201a104010447d034a9960301c10702c0440703080030051822000507a006440109081200000c1010303d002c8a581e80720750080380450080020880c104031250b40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 536124973 1250 536123723 536123743
    0x6180c170601120c0b070609020d050a0c060c0c05040e030c07030521180f01030e0703080c060709050a1202040213090b0a06300e0a050a0309060903020d23010e 70
    0x20981e2a180d03070321420340162801c15a8068400c040b051010009150000000c0a03843d2003070b0301c040f0380c14175160001004580310480941d00d0381c21600084007040b04d2091100003909181c1420184030041d62201440d01e4814060b0b1070185030340e0340161000c50400c000b6184c0c541d0700c0204941b902500ea19200307848241c0c05110301c1c02c0d410380c0002c0441c14003620094136041d28048512415842004041240032003071a40082d0501d40d449080d051b000000f8003410010310f00580c541c40d61162401046440e062001b0145410041402818805070b59140d03840c40803915044c1d44a148141c590002074001e11496156003c000058240016495500d820080025204849c203200f86940c0f07000988510440c101c110104070041003404000590001031081414500200003a460210381019403034520141c105030b46e5944001400c1040681c010f00600162810b0715129003603910f1a0302181d00c0340d0003107070300400b50240d4a0002c1082040d2028042c0d0410740c01001703000031110000b000b80c480303030b11300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 536126223 1250 536124973 536125019
    0x7050a1a0708070f030c200307020f0f09070804050c0a0906031514010909170708031801021305040e0316150c080f0612100c080a05010510020a06180c 66
    0x580000c00c640e000b48592440b9081c2030f1280c00b480b5903000d03400c400a00d1108028820311244003406103100c80303074a601c403210720480c200031580ca0b0000d00411491501e00d200c614800c3c810080c0d510f2031a16404586600480385052403801c98850340b5242d0308010190440c01e400600842000520032002e401050849005005502c0c00300039086c00d110070f55098100c2004c0400750000100700786112540000c64a0f030040c1d15100201050310080e5016a10840d01622030310320101c01e01094000441440c3c0d44c80500c0d9000310700c1c2240c03102c801100480203200325482555070300b02c00100c90b501072040350100c0303c10400f216201b100301d29003e5513100d403102e1011005494010829000360040c2052401603900302120600c81d920710081010082c0030442072101c9001c0c400502d01c2e11000e50240c100203000949a00640f442c0080e442d808840e8164802031040c0d82500101c1140ca4000c19500c6030103802c9000881c89400380d10441d18101d03d0280020440e00b002000010041c0746c1070f1801040c0c802c0c132 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 536127473 1250 536126223 536126273
    0xe0309010806090f06010807090e0c12011e030816050105270309090129030a0c020c0904020f04050c090a0b0c15060102030d05040614011404111809060607050a 70
    0x1207014000b0f180340864090940407010400304007a036020b0344c1c00c280d0007800b52030700380802074030365840740c00c8c40c00d0680e4222840b0313802240d803a0504901121640c0942001e0051031a58202c061080b82c81402501c00a080c0388000150000040a80d00c001c18540d90084020300c502c2c00d0842d064a0001b14000e02c07039589400284070052130200210444200020040c01c1c20626401d11000e41c3d102c04081c51a12502d402011600c551900c01d440518842c14550300c00007031000050501a0810044194052094480c0810000142d1f6030707212480d0882070540d1300003407076612010005098131403c800681c2c818030700580010210030b504010020342e015030382034405c04080c44c212500c280b41c054503c079000d41c00a20181c0c001c00500c0d4003895229004181c0030441c602240c014001c00314080c2c008515484205075000c000d4107142c0503034244503440840062420240700440403000c004900d040c0d00c80c1380341501003a841c1e0b54050540b01140c0d00282a140303140040d1510400380200803160310020a14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 536128723 1250 536127473 536127481
    0xb1f030809030622030503220b04031101061a0304030c0611180a08031603091505030601020d020f061501020709020a260108030904090303140f0709120507050d050307060e03090108 79
    0x40d184c1c0300d600d00c980c845858269143c0555040d41da94000030030024810030303800c41d1000034014241c05640440e01603080464a8101810010104501ca80f03507407109a0515908002c06010b4403401d054203409450680d84980756450115014099030001404640c1003060602004d00b5440c024450b414882c20400c00903400300c4180a07040820b44070f0301040c2c2d00305000c60480710f0312032048400f5142c841d00c0d04982c595240e403054085800c500c8400130000d1700c04820070846507010445030300d1001e028001420b2803181118025030b1000010100441040c4030118150264000c05c064405001c0a21080d521040c0c0d50300d00402c04080c0b08103480e400e03200b4440d442164200100302c3c030705036000907026510b40000d587c04d000181000348021800c141d131382c000c0080410913000b00d4901890000c421040b00c0d09111000a0074140c0a401090584800700340344000140e0028003401118003e881000120025041840c198041c0c03140c00350141c1e041180c40d08a10101100a00205109894020b81d07a16 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 536129973 1250 536128723 536128741
    0x1e0b01030507051e062b020703031b0806240d020c010c0e010f0e0103051806090f1612020d110307090b190e0f0411040e07090e0a0b01030b1f0308090306 67
    0x50311501180d04205c0400a0b180510f1000480c0b00e481041201e200c1c000f00801d8403001c0c201e1b8004e24080e00084c0d55006e00000c3c000d01070346548100b1019142c210700508240b000650105261a103401c440240c40120300750410341c0b4815255250b0b18494115107400c4940702d510b002c1c0c0400c41d026800070710400e51040b4036602500c1036100c1d00e51503540d66009008660700560040034007500300d0302001c140600c8074481791030400c07041e88100f01580c0504a5082030014140c9401c455040b090100380b1800401e00a00710030310400c490090b0100d58411170400c03c2c2c10000d1100101c12001ca8050040342c9004c5550f183c0c1ea0046261401d087c1d81040342003c1c149510b140c2c0031040d009041a100c03218000c68402c2d2440c8107020b401901544a990b0903400c954005011904c540c0c8003030728550810ba40400c0107000a11400c0841603104004d0803114240e40da0b45481c020701400000d01c440068004642c030301d48424070501d0a24100340d02d00820395201d0900101b113402a5004622910134a07000900744a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 536131223 1250 536129973 536130019
    0x10606020d0c030909020315010e120d030209060c060112030f02060601050a210501090914010603030f08130812090c0a180b010309021c0b070302090105071e0b0103050705 75
    0x4005501514010071148001c58032041040b50680c10890500c101103400c403800c1c4002e50180005013006070b07840340d0380c40000d00070f4044018400d2003030303090114036050701001142c60501024907260040e42c1d01c802c000011840e0090700100d03050b030302c074a50001c02c0f03a1030000700c00031100f030180d19100d03288854010304903503c0b0b80c103e52880c0013581c14000341c00100d00450780040844089905040d002031708660b1203080300c1e0242d0009aa203600c0365426018402d5a0034a0320b052803609009106440c150b40b00904104021582041001145000101c0300c4c100d0404485c0c0c403591124440750b45200040032003102a01c151100140c0f40119069030320300349814005d2008944804010194201c0c16001c550300411005100605040d116048480181c0d5810190b42c0111a080100302201e09141402e5250100080c00e00f02894810004041203a0b040010b44108079400704c0c500c08660500d41d2100881074050030001d00c03481494002100300f2101081a600b40c0c3d41c140d81c4450f1300050b4a508840c03034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 536132473 1250 536131223 536131229
    0x60f09031608070203011407021e031921060e04020f0316031b080f01090c1505030105060304060609020307270b04170115170106090e0c130b1018080106 67
    0x1c1c60030441c4241c002030894000c0c003229400100001b40704000d900c6032a03800e03801151603500682005881c0c40101d04244126205602980000c6040c600c030040d038040b40007400340f0000700380800640074051402c102c8091241031203030248144039050f44c4c2d04501d22080f6043e10102d01c2081c440c407294040d8180000c0540c11955101210440c280c81d40d11805039881041c0c0401c42c80203141040841e03081d00800515104902400000071b94180c0b500b000d044076101508444d42c100044c0340c0710141d45074880292819101c04448840c0e80307880e2031400900a1000340e01c0306003070303070300101c100a452600b05410540f00e0321259a40403c01d80754030307940008603000c2c0c0160308814400340810710014a074841c5804540c0801070002070084403200040c180c0c143c1075804494503072800003416070340341800c0c01403d009000030307601070101204003035038291100c2d9000381d41390191a07041c06241801500ba0000030881d08060a8503111041d4100020895607886030144402040003c00003a54101445a6012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 536133723 1250 536132473 536132497
    0xc030603060403080601020325060507030e0303010611030403120e030d0302040b1b0c06120405010c2c010e150a021504030c03110a0501020a0305010e0703061a0f1b060f0903 76
    0x710307030b0b0301c0c0e030162200740010f440da504600c1300303000681058070742c01402641e0120396500640300c0e21031450700301c0039103030300a00000405041a01c483e503108400026241940e025080450030000d00d04105407440c0615400508130700307421402c1c0c003a103a4001d0b480c401c0240013501603880001040e80160107138880c62060b00b039031a17420080150916040c8040420006142c0251100c2242c44400220359803c41011015421031000500041040921401d40000f8642c2000d40c4076124035441c00c1d00d42d100d100141200c03901c1e0104c3c610502da214003d07140c0c00c608028034590f028141d80715940c85a401120241001d4490700e5190070394001081a43c41c132990741503882103002c1035071342c0c1c0894120a02d440000da00b84501c1c0c034540c000810a00113844101c44035030b000541c035071404602e00c440c1000a0101c03c14503113000d006002010400b100d41016184900c01070359100a03c2c0003100c0a0721400c04d18914000f050345003446125400300d4800e00401d0513440c1c2c40b107143c6400000300c0d160310400018a46e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 536134973 1250 536133723 536133733
    0x1501050307090207080c0706051b0c09070c081201060f02070603021c0915050903030a11070c170a0228050910030b070c02090a0903090603020f030a02030a02070212150c030603 77
    0x2c00d407190001c0000d24441d4002e00d003401001ca06062403c0021f400503400328101180003084500480381d44001a030045004100315580c1c0ca0100d110302d0806403040f0208070b4004140010b000c007800480381000116400ea0107150303076031302004100c2038100c03d641c00140180c14001a04a00c00d00139194040e1010701101091210f08154000802d10030600700c50f426080300c17801016002c58880c048c802c4044a025540d00c0c9842102c0004a4618441161341094140034100220300c0e0001c0e00d405880041e442c1080300d1114140161400c1d0341000c0c02544021709241803501d1711400350171194140841034809200329140c80c00c00001880444905101036030b01c01041000c184c0c0268881d401003010300f016480c07405242c01040b00c0d410b0844d000c0b050903448400c1d070405c00d5800b02900d03000f410301c1e146c1141800115103800e00c2c00d2002a00d00317440160040042000091250304a4848990007000c0d4940410750142c589d4442d5a0130740b42c6030b0fa00781004006030302c647d4050700301c03440b40c600100546 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 536136223 1250 536134973 536134979
    0x8040b100b0f22120614090318031e011e0905030a030b0118030b0906070e033408070e0105060a0f1206081b0415060827060106111501050307 62
    0x3100c01e030045000203c1c0c0f0143e041044100c001c0503000d210242515120305401d0070010f060100c165400140b100742804c83c00c004112a8040201c02c1d00c024648401515000081c01c5002a00d064074402805403d51980b80c101c40042c40158002011112490340184d554205441a101200c0c18010007401030340082110041c254441d501400700758405051024a0001c111000e0480d818603410440f01c0303003030420600010f944200320f40c0d503022b8481d00e800026080001e000c02d4030b61020410030081d8805258079407012242481c17078100c005612050080c2007035903c0308400c1d0754803060710034003406400c1d050000c12142091012281c450f5269200c11560485481080b1818050030000a8120b40d4406011600d20403c1c810f030581c0f08107601c40c580450640108101c1210004144004c6030036282070b08012254122800560140241c2c0c281550110210001080440000406a0030b030080038004219250410407110048080c84211507140040480e104040030f0280102a40760380454020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 536137473 1250 536136223 536136247
    0x5151513090c05010c0602040e070914092202010c12020c180f040b0c07020d0c06120203013507031b15020c040b0d020a0306060302040e030f040905060604030f0308040b100b 76
    0xc4400904c0781c0c1b401403030550380d4550b14644103820f44a07240054062103007084101005c0e0981071510800321143c01080c10502144111100031a50b9050b940c100758009000b0340e80515086007915801045009002000040083d103448038201028403070001904810911a001005144943e0011074000d40f01e03191511507840554004007585034800c3c0400103540143c5505090020b1640715a40ea03030106820322401605542c1041403e000c0c8906c113100400180086603000424296808141000e50501722408219a01c01720201511841420000001c1010107051a031440110081d4602003a4445c0c504840040b401101040140d000c41884481072400350b1001c480c0b0500140030909520b020350100d80c24962980c4151031150362810104294203040c0101c6401d202000040c501d0010404015400c5014038010184800c0c1d8500000b20f60780c0f1044116005940c20001d440c40d030300401c0c42d0090100004803411540000403070040f8083c2c0250500400c00e40b4440281c41e81031130312421035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 536138723 1250 536137473 536137487
    0xd0e01090e1f06260a0e0d021507020c010e0402160209040b06030c060a051902070504111804090803070810030b0a0524030a150f0c09140906010e0d05151513090c0501 73
    0x300d50281b80d40303c0f08000c040c1010400c40303d103101941c0140c1028500b9032a41018400e00403d0750702507410040503440c0702d80e03010009070380d16a01182c00584a40c00942a5031030940c240f00c0080d00403180d6402d11080c41030001d44148142411412112034100c0c44007030148a009011107000420b002f0b024810b020342000c50800303c0e04c043c030f2040b113543c0355481000034260380e20400f110503120030018540042c107440b044481109039007960305008090540c2c1d5007025900c40246a40d00b00200c0001141200483c01000e8001355000105281c0074113001c00200c004103410784002202101c9c0c2d40c1c1524682a210310701200061008001d000c5078001e50702c4119110b002500700700001903482811540c428801e120301000c8104c6669200d20280c1011106043c0001e01041203100318440020019a40ea000c003001e400c440d806c0d10500044d0b0020702e08103180c040c40314140100d030240c01c410003540413401c0040b02088401111841c109254000401e000c4450798035029006c20342860044c00f0a50007200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 536139973 1250 536138723 536138731
    0x6050601030b06161106040e0103080a09030f030f120b0604120609020d11031e1b0301091a06010909140a020a020703170301260d0e01090e1f0626 64
    0x14007242120500c4009145079000b91860000903180009440034442440d4060080c0305c82038076203529040c24180000c811000501c13000300141c000140e480300491044990600441e448102c2a10f41c06280c90003800300b0301421203c1001990b40103541103400030038050807060207000781a036403505050030000e43c04280031482c2650220303100d0413040700503180c074010090f43d54000c50b6000540d00c4100c080600344446c3c0f0700703007665041da401c0800c2c40c80400403c041e020030786d20f0410700c05101090008203015221419001e000f40c0300301d803001c0d001d0040d0b081220380304584c2661010616078540111a0464015020400300c0c00742c8030b400035100c04695802040f0b09104c1e030045880481c0d49545428007403c520070440840305000c03004101e000103980350750f210321007181100d906014205842946c0d0f808125500d404001d804006102240d0242490002030441c2c021803022038600500d2000d5100707004000c0096030940f241000603020300c110703019000182000030151018007140c00100c03842038064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 536141223 1250 536139973 536139977
    0x60c060c320418020406081b27040903030c08010503030f03011809050a03120506010c11150d0c0309110d02010207030b090705060301080f0106060206160503150405070203040f05030d090306050601 86
    0x40701041c3c000c2109010b0022001d000c40242e511030501074014900c50000e00307510130f403400800b00144020300f0300c02641d194610401000b2802c1404600000e005a80401400d801c1441c050242040c1941b64000520004440c0c9844902e40da0354000d06541e44070f03d41c0c0103000200c003400144a22050282469848040c180d00420300382550b4442508000c04004c00b100420b031070f03650101c20a8101c1c010682d00c54002d00300381e80e14108079120400b1011800f8041d0344a0b040e40c0b82105400e180368826a00700350200c91042000c1e040180300a0f0003810a02c6064640041c0003265031910301e009071840b040d03d0740c1a80074040c2c01d841d50b601e20b007c10101900f0000d09014540000c145521002e01443c02441080700401040c1d245050280c211035054021104641001c010019000141d4503541842189480d085030b495450442d076943c0c0b600c44009091703201e0b007072400b440920307a4000b0290054800500b0361880c0c450307882c42010742d514084441c00700892045803040000c5081680442d501c51418 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 536142473 1250 536141223 536141227
    0x1c0204030602040f0806011d1512011805060a0504030504050d0c09151d0408030c070501060f0311090702010e0607030e0f060103062007020d0807050f07060c060c32 72
    0x1941d501e0701a42c202c0d8102e003480d42d010050400c2842070400c01c1750f004040f840c1c0e003c1c101803000c126041c0007450003407074035100703495072901046903072580205025000d00003002009071019452742c0c11f0500130b0130f50040d1803e102d1200480c3c0f03244654030480c1e000e02c1c2e0540b143d6150502d0700e400d00070383c02c1d0f07080d42c1580e610b0703860600010710304000c1c02030508010503071090054050801c031005c11f60000140a52002c1802c0d0002c0000240d0454202d0f60020090700c0303034035203440a40c6825400b51440d034000189002c811000002000414925a1071449e8112050755040e41c81000803401c035940110165030992100300400c4c441800b0341d11111001d500354042e107804d0004e819010f4034111080e441100c41590300e194600140700515414001c40085c503495500d001030130b40014151018101002d0105000001e1010421104002e00e1000c07408240076500c06603982d010103402002c040c20709403201811b0902d00b003403032071250040c040f0000c4c810300c44a603900b40200702500d41c0001844001041141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 536143723 1250 536142473 536142479
    0x50d02130603050c150703091a090a0305060f2202190e0708042a09050603030912030703020c0406030b04061d1e150c12040215160b1005061c0204 64
    0x2902070440510300540003864035084160600c101120200c52a1413011018040b690000358403140c001e0484591320803140844400e03802c4200b40b4070824107000c2e884168800000100324010891070b01c100703075010100b022640d0b05c50740440410038229408007160703000c0240800601d410740c0e200404100541030044a19203d05521044600035210f01012032200c20410040181c140c6404003026500250300d115410008402a81c60701d06000303000700341b07850b40001615900c040083d039802810081030861404405041c0503140c2e484020107a0050282d0b152244050815004500803682c0c820f10521140d902da0310f50000401012901421142003810301240c0d040f401c1109081d00020540714440120300c0401240c605480190004410300d80d803420050310f40310b000c06540e0441501d400c0650302da40c9910000e041d00c010032a03020b4900c500442d051004034402e04034910b459100300f44039025a11842c116031806202845115071020003040070341d03140c550207001e00710b00e0301103120054103040d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 536144973 1250 536143723 536143759
    0x30a081c0c03200a1b050f06040c09050a0516030b030109020901080c01230418090b040c21020f0607030c15150e061507021309120311090a050d02 64
    0x124001c02031002a40300d9960005401c008150343c00c4400807038110500d4040c031480081c003103030000066480032075000305604050003824002030342c4030701410f0103540180c546480e000c00300004502481108618000c00606c41c0025445141d004188c800d00c3c1d0040c4903413024044010f000c82e040f80743c0d090b540b40d0274071030016101e0000341c2e0701810780380c0c001c1c00110000b90b0006107400c41d001050841840701032029090040344000311416200e0380b180103031460300e00c2c1c0f4080c006400341b504003c1c4292003a40c1008140414040828182d54107620740340e403000b00d20300c0b0b101001030940708081e504c2021080385010529000004100c194481d0070810300d40403094070741034042d10450064406d1241c841c10500301d46040c001c6001c0183c0310071181c0f00003030306100d00824a81000c6082e0041c205e00b000402c50107640c1d83c2c01d00000700d62100581840144070368580840404840e00b100b00109052501000842035040c05680e6041c501400c1d07000318034a40700820000000882c0c0aa8020030403551030319180c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 536146223 1250 536144973 536144981
    0x10081209060f1e030901180c0e060109031506050a08030a140c01060302060d020a020705030f0303010302040f0f1b03060902090612040c030b04050f1603050a0b070908031602041802030a081c 83
    0x80d003c2c10b00d292a45844002e00382540c0c91220079219103045a16450001845907075544290b0701c0f1f014100c01c1e42c0d0342c0d50005840d180c180f0b40015044010401041003c809103800c090143d80d070903901c417074207107590b200001e0f6a4061501c0d1f44e030100d640d03460b000d41c41d10910b0000d8050420b8020003c60700554980100b030055210140f140100d540005100c504150104010001440164010019000203c0410351240018017000303200316195022844404456042000020071008040040d10110f140028074814442400d00119043c04d00004802c1c82500c00d80c3d0703141e14064180740c9010f4140c46069007004000f00304403a00b45052030040007140003616050b102d103100d82e000705071248244d01c03440e107002c0c1c00c03143c0d4041e80a10204140b002401c08281d1000301c5a1184d0706120b180c0b11482e00f0707507401e81250045c50007440040740103440c03041c4c03c442652070325000b07840070840143c01880303003012000348100107074142d4020b1510b01c0000d22000020b0020f1188250078020040d072143d0048151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 536147473 1250 536146223 536146267
    0x120c100902010311120f010f030c03060c12140a052206110c07030c08010b09010b07020618090a09060b030607020703031b0c150201180533040b10081209060f 69
    0x1174040000f00485103040b1501107025001e041e400f0400e5134039544e500007007400039002c0144800e81b140c1203041ca8902030741503940b1414100c10300b4410290000060700342c07180d044034540e0b1141c1c2000041011000020b015040c140a4964101075100454503030307001421500e00389902070340042010800300d580074010100503620440c01042d41ca45043d8005003036503c200d0003148188100d100400400c0c0c41803040350b155a60650700c0c9503c0780392842040300250b0604a005400000744010032543c0c014070382c8201d5441f44910001c0000b140e10b002410380e12402103944901681c0544c4090002c603015442c107209448986010a021041036518101d41b1a40b0390b0200c0c0300200948900484540c080c000c802c400a821242c0402252030391315056920301d0035580380c0b4059201d440068440103501c0000c461b03c804002c1000d03505003410316040216000444144003280c03a00c04c008203141c84041444208007010307070301903424030500000b04882a840a00c5447c655401000841e90014006d0104615 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 536148723 1250 536147473 536147497
    0x507080604150209010c031d040e0105091501030f060905030408010e031e07021e04061211030d0206090d05090f030a15050a3e040e0405120c100902010311 68
    0x4604040c50b1080030366072030802c5034503014010310000515980c03200224612541626145070001c41250b100142920700005868001d82040d040041d100780540000b4000c400741030071262220012441c5281c0722a080c00014006981c6d401e00802140d00b903040020318a0207142640e24050752a040142164042d122500030342d080402d80c2e014020b82d007103443c1000c8440b803100503e40390050740001c00c11407415031510b07100c0c0c0036004103074855100c1d075101d24060b0110010f40881c5100718281501e000103038655641c0310b413040e4554048030742d10201b80305014640d504010850000ca101c82954a5044815400c0c1c0103420b07050505415902000000d039000c0c014030224605031018040c00080e18002022800c075941030902c407490035004901c0d015401c07410000c1e4503a140c0041e40320000110050304200021035404a03001c030700002c60385809801141700e042260041008460ba403001406076100703001c0640c003e88404440301d4404e40000710024414540000c248036810b00c4c00b0f103076821410b00e541c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 536149973 1250 536148723 536148733
    0x303091b142b0b1e0921130603090204060506090627090103030f09060e030703030503100302060f0a08070309020d0b130602030a0f0605150f0d0209090f0601030b0a03031d01020a050708 81
    0xa0140040d0544c0c03ca0681a42409140303882e00264179541c5400d0f6400c1d445c1c1072200c01000544d030411100c107580449010031011058181e40d98402000f0302000c0380141e108500d0300c072001590746050802c8641d03401d0003804050910104103090b200945081c17051501401401c00090701c0c55032074904c074034080c6110740c442c8501c40003031520082012034079402c8802444003200302d40300c0760b58000402d4002c4039414500603940390368003811001c194ec00e590000790404808a08000c4100d910006030034810030355920f11501e0f40d00c207038045003554a04203002e500003254841d0100810303010410950b02c5140603001c1d081c3e968032513031140226401191fa5840c595588c95264580c40100e010307803801440d040303525400c40480c4118503031042c0300300c85010000f8980040d07105280b400540581d00c01c080f004111180711301e481e07244440403082c03c0318200e001901d8510303c0c42207450108480e405032601030360f4030f448802c88011401d0080700c0200429056100d41145800040c1342040041c0160a076440a02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 536151079 1106 536149973 536149981
    0x4090e070b0f07170a0e060703023c03120a02090d05030d0902150711040c0507020306130b100e060f06070f0303091b142b0b 55
    0x3141d456008502c0002109005014000031801a82100c1088440048420040c4104001000822200344d5448a0703801c001c00a000705034440d00403030700403070040350310085032607000f10104615a514602c040c100e01240540e010808090700e00840c00c08100e41480300f00d803040144550585039000c2941101503a400d95805246500402035031b030b680f03d100c044803018040400040e40250f055400030b00148144c10200c07410240c001e0200005003c0420801c805000e401804100300312082c0600c0340941e0f4244149070048006071040031940e002e914200ca408900180300c0c03402c2d088150f4082100c0c040c1c4100d0f40c1d6122801b2200314440042203400200d07a4001e0388c0d0301420f001e0500d0016810140c25520104085004200b01052501d4003803220519104038042e00c0303210359212820b01c0460800c109020091000800c22410221702e4a1200c290405083d43c103a0b552500c5c3c400b44 = true := by decide +kernel

theorem cover : BRFrame.Cov 535971223 536151079 := by
  have h0 := BRFrame.cov_init 535971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535971223 ≤ n) (h2 : n < 536151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
