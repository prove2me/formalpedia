-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:09.87769+00:00
-- url     : https://prove2.me/submissions/6ff18b27-7146-406e-a51b-a6971417bd41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748381294 ≤ n < 748561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748382544 1250 748381294 748381303
    0x40612030e09150901031419081909090609020304030207080102090609210a05030405030c041a091e0403021509030909160203120c0403060e06070804290f1909050c12 73
    0x103c10040882c401541c50303040403105c941441c11f10901034490b4230622000511310303403510050325502c080c09601c2d2000483d41d10080c040c3d8045c41c2014000110380102d1000c4032030041001500b000e02006031207107050b040081c901200c6a000000c0344c0d10400400c20b86443e04400c5410310441a2492613002c01052028a00c00c0c0d6203401c0c4042c1405030300207803030070800080300503c11104100c0803100d440000310b08010884a4001409801c031b0848001205030f410040c9009502810342c2140c0c1201c503a6810404103030348001c440440068100c00102503002548990720b030382000c043c0000307608040420011940f22240600039002e45045d00302c0706030000f4802c1080716400201c90781c03032038100c1c2800c0300c1401c91a005400708070380a03810459060780e5540c00058442c42241d55035100c0340c03d52108d407034041420380c00d00702141078000c08010507005072862983c1940529500e00c584406441c4c01155818103405803100001040d00b000400d4012a50001e2500004c4408503490b000c0707180418452443d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748383794 1250 748382544 748382581
    0x708010e1308280e0303120f0c0903100f18050a020f22140702030705190c23040f0e1b03011409071814070e0d06051005040612030e09 59
    0x90300c3d80020080002c00d031040120030308496502c0b403810b1019a5801c1544134000c188164401d4141c03900041c4212000000050b0403010b2203c0542c42d00c3e41400101e0709121440300f10075030094560f8036265803c440d07440b6103151900e101c880021407504075902c96840d0040084041e200d0080c02801880d5a951500c0e00d02800e8a0301e10000d030400c0b200900c0304090041004114410100c503400220302d540040101c0e41d24962050161400081840e580e204240040c003060b510458200c0300420400e0300140c5034a900c41c4000980103860207914100310681d0201c03061910420305094038207d07490320018000c0d441b049410f510281d84090000400d00405200d026900e0360084882408817891002c20200141c400c00c855007090900711500b10025140340482d60240f6403c600c001440c3c1502c108017001a001008001d0724a0340040d40380c0b0006d6800596010038000c1c50010700700601c0c035107407150070001d00d6a081009100076150b1806040d05190520480c01040c1e104005800e10510044164a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748385044 1250 748383794 748383817
    0x9010c060b0a08070f09020f03040f0f08070c05120c1f0e0303030a2016030503043009050d0803070e0d050102040603020a030c180302121504050a05060708010e1308 72
    0xb207180d94055050762140e0a10404501500c0c002001c29042428008c41c0c1040360070a40d182d182d51241d541d221890180700105690007801c0d400c100300000e54240041a0850254240c0c1c0c64484c28113082000b10484031100445030b510108810722240c94014825880740d50001c40201040311601003078840046045030301b0b17410f000010801c11008810b40c062903240840303003110145c442e030081d1092039034860400008a0b01110548040000f4418001036900a105158a0b0000701c40b40d581804201072203506450401031503000d944600c3d0b0f0180768080180000c941010040e1000d4a6400d0248401303401441000224201c0c404ca540301d69801e940c80315800002199116a00d0000030000d400c01001d1400007420600705890451180706c1601228001079250000b8500e07640c204079040301c1c10ba5055130b8038083d4612040c0a1700c40f04501d20710450107880a00120300087c0740090804134010080824841000014041e05040000301d50780039072404101c0d0400c4000781484001b80c01a10720740386 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748386294 1250 748385044 748385059
    0xc0603111606050901050105010c0f02060702040209030a0302013215030a0c080a03080a02070317191e0608070803030117150c0c010f0b130930180b09010c060b 70
    0x10030100350303c0b541c0b24540c0700008004603601d400046030402c0d492640a031000c0e00114004002d4a045001003102e03500c010001840c0070704d544007003824000b03207600030340150b551100c91400c100358100410041c6d112410305048100b03031209161504580c007400468203a5010201d44400351001c0000d141c400b07820450403201166078068042ea0b0788aa454100c002400e508041101340c00c4a0082d81c20280c4d150301e03104220304040f8400c03268020f000f411242c000c0d03d2044003040300e403018403541035045e00012803480070780e865940690a035807003503000c2d5649a01849080000358004020f40341501c000b418620b07443c0c126400c6841ca0820303030f03407801201020311000f032200c0300c00c1c401e000303100c296441d000070f02410012505040c200c80201a004c0d800101c18240b504442405a0000ba06284250380410080720000140c5508110700d24020414034004890401151780100344030f40b880d103540901510003800c107407a0400a004120040e810722802095060801c05c044e0400340c0c80042c0500183e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748387544 1250 748386294 748386337
    0xf0102010b45011401020a030c35040e0f07090b0705030f04090203011d0921040f06030b030f0a1101030f0216030f260114060c010216140a0c060311 65
    0x2045840c00078031460344e142c0302c090300301042540085400410346406071100304032800300da200d0040d408401090224401c500351401010a9061f602061005900c42c003810b445034104441d0651000b4050001100811000200b0414a904c510000d065800d02541c55489038407624100d0708e10700a80c040070064000208002c44d00001c0356018504031003030351140d03414039034000107500281201603d50380d8013500005070b40204040d00009244824082a0306580340507503030f0649445041550b005280001d486200081c55842e04101c07812120320020043c02581c10950341d40501c0030415481c5034103040d03e030006802d00e00140e5044c2e442c0140c1c601081843c10b40c051400400210724400c0c0720b00411004044070080034014684030300c030490400d541040076401c2004035100324100084040d40031004200c410081e03036083c00544082c0b81c803038071905070082880c40c125030344040351050181158844880c500120b1000c22500741140c8031340c1000148400b01c101c06000c8c0b40700c5d8103002a10040d250700380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748388794 1250 748387544 748387669
    0x230717070b1f060305190c0507080d1d030c03091c060c0c0302070605040b04051903050d03020d0c08060d11010e0607030206040b16020d050901091d060f0102010b 71
    0x1c8040c00b4400d94590010685520701078044803000d4600b1030001d032100302e10021450b0503a00981010525082c80b40c240f02c800da4801580d640246d1020400e580c85002640342d0040a2410101c6004804043e60610001264090740ca00036802c10601c9003141c1d0081440620082014049a540107401400009074004000d401030040703010803030045c4148000001e029124000303480c1079a483c000c0d0503160502e0001004401d144414034220344500c2c6981c0040012410042003280c041c0b81d440150319450044600070032500c1d641401818480e6810400020b135403810b000c0071205a010515250782904900101c54013036002e203213070741c0141c800a101414981c00040c401c0c4900c0c0f00c0c099210704c0e40e0b500c030754103002e1141071802d55000d0b90180880c402154081e00103026006418034208103100e0352240c0ba1075405042511315884908450188125410b2002d0381120400c0d0a0000f40402c0380c10002040070032507001ea00103103608190091107050440a180d00701c0c030b80d00d860110031108a000e400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748390044 1250 748388794 748388821
    0x40c0c0305070b0a1d0f15090c0d02130c18120b04021e0405070e04061a0901110f0a1103010c02060402090a0207060f0c02011512021305150d0c06230717070b 69
    0x1521251054910300c0129110107d6203d10400301e905c05070019010010922000c035012045c00c03680a080f000600180c01018807a01290402540d01c03a850186003254046050300982c00150741d1100400901d4041800b00e100260481c0c3d066071411889500c503400d41c0c000a110320051940241040180041a940721481c212000c2c0125401c001042c0da40414080540c19040080e1740c20f5024400c0411960003105a50701c20040c500641e640103500d03a050745d041c1030b1b184c201101c00b0410391a02e11524102441610900000b60004100c141815000500f00c90720040250700e0450b00056a0000c003c15a0130542540701e0700003042c00001c02c1983c0203400b1784862894020480f85100000510303100d481400080e054000e00302d0b0312400380342400e80010305002091052401400d259140d03441d10b80d42015003c2501404200390642d0a10300001d0000349444075010484030400d2041c00ca012401d0101d80c080c40d4050040c4254911410500010f0300481c0c8029001601c900e041003907044100c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748391294 1250 748390044 748390063
    0x204060e070306050603060a090b010207090501030b04140c0109031214030406050f090318040b0a0b0705010504030906210e0a021203030a053d090603060209040c0c0305070b0a1d 78
    0x100c06000d40f41d160001d02405001c2258030b65400407a0080030449600140d0140a41201c188140c59507151240d0f669020743d4000ea20480d0400e0040080000344084442c01c6203600c070b00d9101030400c00440d030000a09484081c00080c0005a60307008a5101900981c05188070708042c3d030803c1d031a40b409040103070007400110f844120f507218102c005101c5520110489040044003130500c008001e1483c1880010a640006c80d0f4001880040220308180250094072103d84940c0010401c1d01d8a4540140002c5003a4009801c0c00742000042e0121b00240960241c0d0040c900340000341000ea03054001d00c0c120751940c02940158516410288101010000714804c0701ca0150034030164440700388204500c40d5030803000902da4442504883d8031183c112407180c0381480c80082c1e2032082e49800400013203a4903580200c4800e42d000910301c1d10fa00381405660b01c0d8180340d081005100f0303042e4501130b025200b03512008108140750400189690400da200d40081084204008158900c50040558404002c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748392544 1250 748391294 748391297
    0x9011b0804050c0a0b0f181206100e060a0b0c03040b1303030905060909010905041112030a080c04030209010e090304030f0c030506060f06191b0303050601140a0819090204060e07 78
    0x74500440d20b81013100d03100c0704850140d4039041c40e0040300d00c66110281c00c020300c080c101e498404000700c1c2c159102d100c03060640c1140005003d45092400c00f103880303400260300030921111442c04202d1180c1ea00400442225909041c1307036625801c210041e130640c82240c100011000d004503144070303110060741c1000e059174421740303030380078515101c0d82080f0041c0180411950b003c0c00441c018050f20540c4d070440c640240c1300f10007100c0c61011410005022240d816207040c8954804160f49014560140d152604012804821890705041d80c012521646050282c40710303002d04c2001065010a041003102c00642d04211002c1c0c0f10301e140d19088440352041d00c4240e03858407913040410140c4c6008089450300d200010a400c0c0340480078421450318a00b00c081e001c05000001d0241040705142305a00342c041b0f40301e07950000315450520000b5000d078003400e454003c070400601c10403500d1600000000d40004480100340b4a880030054804090145001d00a420605020b030020b01c2c011207200040c01680e05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748393794 1250 748392544 748392553
    0x12040b1809040804260c01030c02032710090e04060213120303050406050105060c07030210030603021f1e17150d060c0905010c0c030b0402040213290405010e010809011b080405 77
    0x41500b0203140c0c410178542e40d410717088070321501c140d036010b5800200700120500650f81415006141f44548103044600011105060702c1c0840c16072030241030a0605240600340300714603608041e071328101c6a01c0144000c0c1042d9000415032210304210040c3d00050840f02c10390b1039031102d81e150007001780005990480301c490a10300040f4039850000203072464034030004006c0600c24076580802032807040035480d160603d039a422022000d83c40d40d580d0025140313410f0002545250300d00c80010003481a050f562010602aa014008000d9020440800f4031196000407209500c5c0c0018200c5510340d011282c03503104107242c11100070080d0941000030011031540300c2c2d0b42c24599400055070f40c0110214000d001110005061002450103060103800078000b0b4030043c2085040d11006c80b18214640100c0141080c40054030160588208180c44420400d0189820309290038000703050700300300900b101d05000c505400144034a02c25846800d200300106600d4100c4844003070b0143c031000381940c00b550380d40079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748395044 1250 748393794 748393829
    0x50601060f0e0d020904200415030c0902070206070f08190c0204141003031b021207030606050a1401050304141b01122310030c030308071112040b1809040804 69
    0x4007080d030715807015009070a60301595a1030b91001c10345c10400b0b1900300040c2504880c952251954270401e8140c00d0b080c0d80d100c0707107942142424001d02c0110390202803424010011800107031548402d44e204141e1003c4940700034200e62600c1d8069015001041c034000007000b00181d001a885220740d101c0c1e030700a403403c2259000400d200c4c00100f0040715034100b24032500d94100b0000740305080c006040c0c1501c010b140030448035070b400510302c1c030700d40d11450f0340c02d03800f000040c800d02620380b154500411044641b41c45c22403030a0175440412551113000f90601c40048009002d00400700320307425100103000305860300d4000407169000e2880c0328030740060020f80385000403460881103204484102c08911503200d8181046002c003060200d00a02d0314052519199001002a00d13500c40c000195200c2d44a100303881c900090f00600d41240c40320b540c0182d60003d2a00c00034840c185040b20185c404007900705543d071f0601081c0305c254000c20381004d074200d504181080207110000c000391007555a0400c880c1048031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748396294 1250 748395044 748395049
    0x211e05340c02031f1406010503160c080c03043f020d02150a03140f0109090201052209050a0c09030605101d0610020a0506060126100f05030304061b020607050601060f0e 74
    0x45c1d04580e014003003581000402d887e01c038604840c0c50001e0603031620000401c1c0f20303651031950ba000601240e409134400b04041c0401e030103580c100c0401c05020340404184420108400b580000e00070540c0080d4205400010151b4542d003841920303080d0084d0601022070361071501424140c1c8201d1940e00000c2c60045601c06941015010502400034204030400716403c0424240c01820070325001c0341441002c2080c02e02e0110398408041c080031882000c03810f50b41c6801000b4095440045c0031002d024a01204c081d212900020308400342c075084038000071542d0b5903115a01c0082c0c070700e8001280d1a01007034000310882055180d45807052400b074820629250805206a940e4550920024840c2e080000002c2280d442031281044411516180715001656526210880a826151780210820750b0806003c1424131262090042c40705400a51510345000c5d0003d103960f1004100001071144c581046007559284011b840d51140c0160680b0765a503918140500001d100401201c041a0040046001ca1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748397544 1250 748396294 748396331
    0xe0c0f030706050702040e030403170403050d0c021305090f10091b050d0f11060c01200a0e0f06040503060c0d0f0603080a211e05340c02031f 62
    0x1c2d01151502d07401c1042d00d6003000090000310708020900d101c2440004080381f500b8051003039500ca840300c440c1c1d581d030a40c18800c0c104003542c2c00c2c000034004082c46200040c3c94000305034050400404c0d00007243d440300c0c0341860824066684080482c89030010b0b0301c89400303060b44200c8500f44504050201c01950440c0b405900600e40300300740d4803024000c45080070811075544900e0781c52190031a190400802c8000514940104801c502141c0d5255400c01070072202100340c3d6039000c1203000c2c3d5410400100300c0240214982107509000d4a05002c1ca2595a01c80c80c0235200980801015100d03945440100184540c10140c144410310707043ca0149404d0380f03014454207040e00d401094203464040003020070f4a030400c1d032045200310044001d42c240c4070f590251062031620091041c2c1d41800701d042e04ea19909a8202800c5860303e10041042080000030b01083d98114a4440e50098500d1064107002c1d0354400c0501c034065010300804044405601081c0d0304c00c8041c0468040800101014032310003a0360 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748398794 1250 748397544 748397549
    0x11060108150f0c0708030c0702060d0603150b03031603020307050111091003020a050901030c050c06010803090f18070c020d05011401030c0b0a1d03070f2c1e070e03010e0c0f0307 78
    0x20700d00400c10100445c20040c015a801042c01c50010314000c425408107034594040b1100040e525642c1409004004540c0c5290b10704000d20308052001d032600000180d240d10462514813076543c0241e041d182018000d0054450580e04000204841e0f00c0d0022254600d80c45200510320500d229160440c0640c001d201707a64000801d41e4505007008240c04c0190003d14035010f508007407003c14400e6086804080126074044c08038003000d143c80b0720075103003401100040340c2540745c49a01c1c1018004443d51540703003065480603840c40c00418001c014008210a002c40005c00741841d424841e00c004610903650140e8100ca2180603220385c4c490360f0700d240c400d460090300e07200c000103541031500046d940280c0d0582028a000107094502d070f0381c3d803030500d03d0140f08580d200b890b0f10000000e144070b0020410b5442c07800a043e0f890341c202d980c0b034000801e404501056403107128100141000c1884a8403407240c0ba020320101070020064101d40201d00b554801a50f13865600c00c483e484140f041074140450203004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748400044 1250 748398794 748398811
    0x26100803040609150e12070311010327031701061809020a08130213060801051503010b150a0302040e1e1006050a0e060d0c0c0b06030601051f11060108150f 68
    0x1d002d0515813503000905540080c1030401850780180d0415641d225a010303000e0f00344d00f006182892441ca0100400241c00c4030302c9041c1864010045e00000e48001160000c0001d0805031003a03044901d401d40c1c003011f0440a140d10b000e0790034004180079070040e06148003d81d0074040180b0007507840b00740d44c0a9103c1e504c000d8001841d1140815036640860300782e8408070380b0042c05c0065840810b80b40e20115a003a80c4500b960340e4460085c0309a8a412080000b0503a5056001303000c03031034070f40c1c004c18400000e5414020020380e0020700d00c00c0003442607042d20041c107030100001000d810324900380303502024540060844c443c200b5000c90307051a03610403072038100c03005901c03002e06000b00394409032607240c034400c03409801c00003c12401e091000c0341d10412150b2039094132a01c1001c40e441c18070117860740300245424001c5d4000001030203540e841000d08881851220841400305046000c21101284101d045210602c262000412040d07c04a0201010042020510000e5850f41d91010700321500f03455002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748401294 1250 748400044 748400057
    0xa06030804290f04120c050915091008060609040c230f030703030e060a030e010c0816080618220308090114010308030a020c0f0a121b021f261008030406 67
    0x41405408071111405d58040e1842c0002c980d61100443d0030000c0494144032142c05099601001c0e2900320311081d0090000520302e05814100f42a140c0d80340c5000d0310b418400c000d91400a01007024200201c800307031484c100c40100848818202e8400402e40040d00f40c0302c4c0f00e0302c0350940080d0600140403000c50b9095541d403a03907256503005101c01ca911001e404010140c5425001050701000d00035030001d0b0806070307160183d40c5002c41400900d54201c04d4407508100005052004640d43c12420408078821002d209000d5250311221580c0c002a04240b52216616104000f0515400405030740c86106010021b10004401b0314998400c075609000060048030180041103000000354054000c90031080d04550600380c01c00443c9184c1007846504a0b0746104100c10016210360040c560410610b804166082d01422640000c0d0303080c107080d0310b0b220782d0b40d00c41840071030f014811400400c8018814400030700000d042d2040010101085034816502d0140300b00c001440800002214111400b540d02da2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748402544 1250 748401294 748401299
    0x3050f190b120a0c06081008070605090103090f0516081609050a020c120c1e100905011b0c0501050c04031e02010201090c08010504030915090306050a06030804290f04 73
    0x1500811030300200e190000710202c03580320007040400c040200309004611400c5218038100c401429034100600110100c10781c04030400000c5000510740382502e40c1420a41d40b030381340c0304c00100c0c028611000e011303008100082220341800000700744014448c1190408030a2251030395060341d030741c48910b800d0f001e4060900c1c10800000940b9072090740c1090300395201510341681c4615103403410600380304402c001e56000880c3c2034801001c008141150b074442e0a51504080120680c0b51190480708407009201e8a070030522081160a43c02180c1024420140c0c2c1040c00d14024020039403501d82000300c1d40c641ca008049804400ca0500b90340843e5401928035866101c840c00c0e40a80e0400c601e03003241599200d203030400c0010102c0d95002c0140c000f0740c000080d40e250504004249281c503600002100d41110301c3c041030154000c45400507280c1240002c95551140c2c1c2c3d10000601065002400c582000301300440d0b0558003003030610305040c032007005d11b648030b840a580807240d00c00c005191a982d941017004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748403794 1250 748402544 748402591
    0x80a0c05042d06120506010306050d02060703030e33040b011710051501080f0403121d0105100e160504031101020c041b0215040c031b03080d02040603050f 68
    0x40760a600703241c2419441621040140324144403904803c01290030f00c9003d5104c40128816594008000d20f410707c062407030f000200d07035070030340740e5001070b01a2000040f40c8051501a411a1a0704111281220307003020342d001b0344030ba20070325500c40d49045420710340702101e4034030f6581c06e0b250166070480b222420036444c280700801120072030b00548100c0c0c010481c088094040b46d204d468402c20720b4404031000d41c14500b0005050080042003a001c0342c3d096410700c030100b540080b004595490f260f9001480541c0f40700840090750090308c100910790700300002c00c90014100c403a894102e0303221100a07801d03600c910b00c45103e14070411070300c0d00005005020030400304481042d540300440042c0141c0b030f0036070062808181500c000d46225002c2c12015040c503121b0640c10003c0c0104020650385510a9040c5070317451b40480203c1d448082d1103230303c0d6451040c1060005451400040d640200031396650701e00c2845882c0650068400c02011a2a080c00655001240c0c481d01d4480d195031f101914a18980c45d9a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748405044 1250 748403794 748403819
    0x301060e130309150503010e011d040206160c0b09090714180604030602072006090312090a170a0506180a0b0c0d022205060a0801061b21080a0c0504 65
    0x76401c1110f50240007038016070104203130680450340c0d640c80384d0f0b035130404454542e0100c1c10703030080d0031050746010300784805406c42241c90382042e412907419503280181800c104075110701013800340034a00c803400001030304208080141703807000301602d1350080d40d0748070b0703800f62012102c0c80c0311103a84040800c800740840d48125105100040001d103807504154494692204903082100c0440d40d0a4100c0d1a20010032411014411125800c41e01d4500d4501213a0200c2c2c0c03261030705070b10010401c0012900383c1306a503440d01841e01415041e0b0101c0c0e0141084040c1c195100c80108007a03d5a0113402e000c1032603501a54280a0318084100080085a2060340c8008654070000d0900e14545018056461060480d0000300f5645091401138465203200e114410305106a0350301252150f1020401c15100b41c3c0c0004049044a9590408142890400e202d80398120610413001700403d004680f0620101031100c00962000701b65514042c0c580d8070b641141d001c840036110490f02080040c003041084900d20308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748406294 1250 748405044 748405081
    0x70e130305041502012004051c0203010209090405030703111504030503090f030d060911070b0f040609151b08070504090e010b101e08060d0b07021501140a050301060e 73
    0x1c1d005190aa80315450300c032445028501c0710040c2d4686001340130403561024600603038021481071500d042e26180005408a1380b00140a005451203103202c000d655007941900d92404d4041c00c0c9464900d440d2500540f40c7c4d200700300840110b4940c04801144d6071000484c12030307048111400c00401e071a070b5107069516810083c0000711700c3c403d45000c0c1303010f44020301c0909180690804007041d07036410405203c084c0c5032002403020444605010b01c130003250b1044111500241c0780801d10005488030b00340440600b032800c3c2e001e8244813003091b00e080b0521072980091320b9941e00f40c00319503030b408011004549c40036042c0c4407140061400e000520505082d0350104946200c4000000b9070320040700d0110348007034902c48071040819640f00f0641c1002e1254100450700e0112417504c5a100e00c0c1c100c0c00503055142c40d4001404030640302d070000710074038000c200000041e4042c1000c0001c569445a0b03840700180103105940c0200380c0c411700003d0b142814003c40e4190f41c801305140043da52459040030314103a041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748407544 1250 748406294 748406297
    0x2150403030206010924030507080f0f06041101020f01110913180b061809030a1106011a131706010305073003051209030301051c0b0402190503030418050702070e1303 73
    0x2007124440413540941c040004500ca41c8c080c3c00803a10b05a03075581070281e004418040c41c1c0090019a00c1d01c880170621a602c258400c04810482c0d448030b00403403134940f44146410041d032801c0147d43e0400c62a001404034803001320340d108441000c1fa0f14903000c0e50808000320b5065013461500c0b40002d075811031826440074010b080740280300086410340403c1042036490300c0b110b0301300180404015034868a51841c4680c03801c0107025035403400d81c245000803c24202c20a01e0070000c50380030390041131514188001c1038100b03c904112419101203030f0315100d01303200c203c420b03104200c0c0002c1c8440100d40d5024295a619501401802d00e10209601520061008408003c4100f1600d40b040c4691484107004401e4580159200d60600c3c052280b044000004010121075900c3c101f000240d1a0680582c410b50503501080482e0081d42d226003481c00c41d0301b020ba03040c040405c002c00c000c0c4525584484080c011355040c0919143c000c000d83c3c0f07442013802010840c61059000498500810004d600c0c054403d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748408794 1250 748407544 748407581
    0xc050a030c060e0106030305070501060e13030305070e1e0f19050f0f0d0f14030f18150f09040b1509061b010912120c020606130f0905030304021504030302060109 71
    0x7603d03800c55081d5001140450070224444082c084248170f000c018040e40500350403242000d0851000740903010070014105911600098102841411450340104025221400c0340f04a0f035180c0c4491203444010030b0040b481c0c030300584400d00d010b07250300d4042600900c0055020741090700388810140c110070280d40002030f8164402c01a1103840011000c1345c0102201c680803000317898040e00d8940f1581003140507038014400150100c020031f00303c0b0440760b19403d840d0841c04000340854001000741e03100b01c80c80f0501054078400b41c40c002004103403120048500700700c404075540c20401c0f01043c483e040f0030303003204c14411040d150030184000d08210080c104041007403480d2142c150b00b941e00bd030004560f60048240d1920741940c014041e4010b00006080500429506000003076942200502e9a8840c40071804103c801320030350b41c055412807240c00000d00004503d07080841e0389510a50f0120702070a06841d110582c03544e00810b9606695045e4081c0c806640303084405c001501d030505480811501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748410044 1250 748408794 748408811
    0x14030309090708091606021005061807120f0501030503090d0203030d0204080a020907050a0f14040803030103061a150406080a0605090a1d0a02011b0c0b0307021c0c050a030c06 77
    0x100d200d01c0911441c12541e40c101d0b03525103180301c1410300d20398181080400300180801e118250b0089824600b05403041d00008450765640001008018280d4482c00000d2381081070102d8680e0100e00d034401400000002d004491404022400703d400c2403102428541092081090602d0320b6031710308456174001402c69040c00303001b56400d0102c0c2c0c000d03404185644d00841c090011801d0000754a07a0140d10313402c1039070900d07040c00070151418010142c114200300d1101c8440660b541c035802502e024003c0301d4102c9440e91385900d4104000e10290603460301c0c1c011407006016007450f180e83c1c243e5003211300c4010581403030b2601400b40c0e1400310251034003071800c0d10380c0408181901c82c02c1d0514802c1000300c401050744604075011004400010b00444003d400ca4411000542d03045881c0504880d0b8a170440203903402e4501b0300d210303100401c1e0002082c01c10700009110000381c2c0022620200e918921020380024087c0740180c0303210140c1032008065801c4070708a600802d000d10300042e445802400003044040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748411294 1250 748410044 748410049
    0x31b0d051f0f05060103050606160203030412030305010f140312090a1802070c0603050c0f090612010e090708030a0909020c0a0b010b12090c010e06070f0606030809090a05010e0114030309 82
    0x100150301c80c080c0345a4488206000707070340038058141c10210a080411450a14801043d01d600c00c01119084074540075804000f10b450404c100c0b001003141030082c3c000303000d842c60010f0240c1420304ca100e203a83e80708200414a0000009886d0625600600920243c9045800f940b110b4001c2001d496000c194424000b4085040306040f00005980300b100598030702c03080c40c0c8503c11000079000b03c41058a02810003075035640101c2110700b01c03524210303040e482d60b031188000360b0b844c8107000311031603c49a00000045d080c1d51500c2200e010352056001e8400d40d607264603855580b170203880018000280d03414420400c80180d80d008008640100064500e001c1d40c6442e6440088001c1c1e100481c5000c00251014034030381520509500080704501410750322032400e00007003140d964100414820f0500251807001c02505250250300a6404003043c4078480c1d882c2007440d02500908600f40c00341400500090501d40b5611605051300c010790124004c40e405c0c40c0040c40320403130700342070380d5014032081041061300c1c3d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748412544 1250 748411294 748411333
    0x210e12071d0946020a05120a0c090e06130f061107061109030c010201020c0303070e0a030b0703020703030c080405070e09070e0903030414031303150207120e030c031b0d05 75
    0x142c2182030042c904103003861900100d10005407002c0943c03d00c41c00c140d030050703460003143c070102e64046075581440041703803070042c1c203002c074481004010901032440001d1055181e0041508005124251207065a980e280c1481a140d40c1d00001c205c1903a06034060700040496000010382c44580c0041c50420032555180000c0340d101410720440014041545440c0785070801000d1080e203802e200a5007440c6003054542d5581c040030340f0010600584d01d034001050f85031a0240c200a5421000c1075045040c00034001c0c0095100603400d400103800c189800a03050b010300f00705800f556000005104c1246810000000c2c224042c0c9a49000e00540700001242d1124a040c0b034091041900516981d04282c074156000984070100044d186c0c100b805060502c01400c1049011070750888511904105d240c1d01e0040240b1585034002c1002c4849070004c0c0e4860341c0184011b94202c42a022141030294001c10035581c1c03a10a25940300c44080e20001810b5030400803800e50001d0303c41c5049416000d200101d24608 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748413794 1250 748412544 748412593
    0x110304060c320109231f02070507060906030f060e04123f060f1505070819170105031209030a0c082b08060d210e12071d09 54
    0x207a9150501c44040c80004c2145111400c402000001c8017094007803101c0c0c0f01c4060a800c00a8900b020700708101d800f9080d0108d400f0340e03a114094075130403a201c00f00903042d00241c0c000c44001a1501034100b00d1500742d44180000c0c0c502c0009a806d26945584e41c004032404158141000c021180300448218903241c800d014055480441c0160039141c049442c0d07180c100407101c04034513282401c0b020000491902413a0703040c0c42070404c205001c3c52016005a84c207125000d401460034200082854120031504054160801140d940090b0514802e8038030248200c213000352a8150403e800307800f40a00c0381402080704500240560300d006503140c9412aa5449a510440007a0846404120400b401c0d8201740050365580300c2c03070b0382d65032403410005002039401860b450241081c040b2400500c000701045260000c0c3c8006201740c100580c19000308040d030320810840c012422440440124940800e4000a0724000c1141d98042e1010000300c5110240207403001480380a061841c051031070f0b2803c1c0c14800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748415044 1250 748413794 748413893
    0x1090e12191404140108090d081803090a0b0301080d110d0c11040f0204050114040305070501050901020a05101508071a07020d0b07030b100e011707031404050d110304060c 75
    0x10a5010702c4c0c00135000c8440208100b54a07046400c20790b00003030f000f08000c0d421200315810130802c1400e1501c01450b5220303e103019035100c0c3d810000040c400080100440c140c900d0b100958040514480050320500100b540c020100e130403005103100094443c040a10803280911954581092600c01103400c031101e802115400580005052102d0b50b04070941d014454101100e41c0c1c6810b1564445503203801060007007034100200040c20004030703131003001480c079a16004029102000000d514900080059144940340656403e00001c0c0c84000800d08100315594588501c810500c0f450740b0003125401882e00300da0042d070102d08400491400d00c4400d102d5480303520002450f48001d020400c3c1203c002c847c8008000300e402d108800c60340c0c012407a10500f0110b504509540d200d06500307074041d29002c0b1682051781400300802c01480304c0042c268011000c00d0711030004068804042e940c5900c200c1c02048040790644c00ca00c1e0000d0987c094102e8514000b041003030350030860301c805641050700c0600f44c61 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748416294 1250 748415044 748415069
    0x160e04060f030c4719020d0f260703090b0a060504050604050705090d060612050a151103160c0f03030515010819020304050a0f0b01090e12191404 64
    0x4906a140d07110f0480d6202c4c0c612040d940580140244013009070030984a281e031070302d41030f14081c101038000280e820200062001340407051072200000c0d5646200c428202c00901c203070100c11801070058034a00c450703540607c43c61642840c0c159580d08924400780034103042590703032003084001c9082024040d0003243c038143c3c04100c0c10324010800064400161585108510f00818421015000022950700a9042ea003000c1d42002ca401c003980140001da1021001c400742c004851b003045004242501c070141f0aa5018a070201c6400c0000f04441c120640c8001d010700c05c10100b080030003607181040e2090450300d805a02e0007415510014007150b012400c0700400c3d2904140b0881c40200361140302545000e280c9060b03140390010300c0c00340c01e2102c1d01942003903035070020100c0c0900009000800109070403442d00e8641b60040c0ca840704c9120300912404514602c0c00b000010031040c0800c00800d8160b102060b9410030120403500c0c40c000b41c41e40c1c01d207803e02003c030210f06040c0107124084e00062070240c103800d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748417544 1250 748416294 748416299
    0xa03031e0203041d040309080304081e060129130902030103110d02010206180c0405090307020109091407050309010b041a040f110706020f12090c0f030303160e04060f030c 75
    0x9140c100c1026140007035401c1400140a03001c3c4c1220b4403000701c4202c1d01102480d0f1114281691884416048010103000009011614641c00200ca14550a10200100b00b119031400d501d030b1610b90a004112810540d1480501c1143c0300f810401c605d03184401403580341842040e0101060116607126070000d03500480104203000070401030091459054031000714401c4180e000030348030380000301114032042d0203004000035a141004019001000984204218184000d52030380d40e80041c90101d0014040c0c0740d000c00c00b0780c031501649400e0b85004c882010386440700c0341c00703460940008050b000303659030368407150403565103d0054252180c01c0c40c2d80002c40d6440f0380709000a40764100085503000e4106070358141c1e000301000440c0c901e0754021000603180c020625041c3c4a900c01e035191290f0200004007400124140400c0c1c0016140d0101c41548101c00000c041c181c5900040700c00407800007165844800043c0100403102031000c0c000c00000300103444400740300c062401a0000c1d01d4500420009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748418794 1250 748417544 748417577
    0x31017032715120c1b070801020304290415020702042a05040b180d150b03061b03040b18100e060c04030f080906040b04031202010c030c091a090a0303 66
    0x84111840203862151a00e4400f0003521407000b809400760301c2c10540041e07040d90246040c0d00d00450940d10105031074030a41d450007203c1c040d40080d02c1c0ae4403101c00030110042c412000310f07040c2116a0304100c017501c0720b0341c46455202c0900003428084c998a80c003004150010f9466200340e20381e190729a82c195800401c016506074917111001d0049040c05420001801181058000c0d2941d002d501411000b1950303094021600b04006503100400c0d095611070051001d4400ea00104000c407820780844003590780340804d000e00340150310b440da403240070104003140200300b00300c46031a0700180e4000d211403003030319042e034032450544140c0004185076542c2000b2039a154003840206d4201c4807150341c49003030a0640d21210414030281c88010200f42000031035040390380316041590010034083e000c094840d69241000a020040404004011b51800240b2000d0034041e226076003900e1a2540c4480800b4140402d4800c620080760b1003009550041c41039441c81d550b0300d5030050103141700399110440e00d50b240e001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748420044 1250 748418794 748418809
    0x30515130f0b1c081605120c0d0306031104053309060f18090c0406030809010e0a0f090b0112020706020c1504031d0d0c06080910020310170327 63
    0x1001d0312403c401c500070903848940c0714041071001e4000c40060b07074030291001241e14862000b03c0051a900801ca02080881415005005007a80071b03010f9803884580140308a08030340c2c03140070003811400503589200c91410958040da0740080542045820b40d4501c8501c0c425a0032901203421003c40886c0d041c015a09240310101e4101500342c6281d209a40d000c00021039010ba103840e1030203014403d000054440b1001c205221100401a004000407a101d0030164815449080030901250040601c03031a5800c03c0f200000403206805a4031094a0401c40704101605030010100d04121401c50a000c00428600c000c00c03006100718401a5500740d0010224104501780c0302a42a003e410b6003003202181d0091400f610041201041d10f40111842c80010070341c02d9030700700240981114003c0801c603da04910160b0003000b5501c00c0380d200b1945045204183c1c401211102e6283c0c4826008101010a01c03007007890355041d0783c0541f400c0c5100784050030740b1881e032042c01035070b0b0460b511010541402c1648 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748421294 1250 748420044 748420061
    0x9060e240a0806100e1012080d0c0903020a140f120102070606120204060e010305030304020f010927060b0702010e100207030f0b0105040c080f1314030a0203181c03030515130f 77
    0x5c00c1e0340325501c0d180743c2058082c0524469124034008001a01c401c01a040c2d0464011481c1000108003207400c400c0000c001112030b0004070301448849002045484420300d090307181e1440100100c181101c080c041c04030071001310910b00225902480301e4800951140641c1000d00284850301c04ca044031801048141d81d0f10354440c8000c0d0150400600201d10040200d0398001d8054601c52260350611004a60018030391788040c4004140341c2ca0806071140c404114440016150014406c03c0d4458040c54514865110000d000c41c00540906c05a41481c01000c02914078500545100c0c69882d25030040c1030005036012508090b0702c00050145243c00d01c280302c0b801c0c00610b000c0d061480c01c1c481c02c0c401d030071019100e440442440103510040062a03c0c0000382000c140d015aa05c072612018042d65a0708643d90614151240c100b050202d03080048000300c2042d00b0005408a410701c1c0d0302c0503802050050b21518401c284140400501e46404040800d02c0d14140310000303080f1860100d4004881000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748422544 1250 748421294 748421309
    0x912040302032107080c0307150b0a0911040806040f03020f010908041701110d090512030c0a0513080d110115140f0d02030a03080403080109060e240a080610 69
    0x910003031000d40c80002d400c3d641d0300100e50b4a90350955550110580d503000d90b0380010309900d00021846a0002c0c08009400729030310865904d8030041c14564510140c882d041c3d103454029240700000c000080305900000900c0c1c00e00d82300394ac03034103844406640c01d08000b200e0640d010981d8500003070801d681000341c08556034000000700a200703016615160948198490840310070781e00e44145d880a8030a5111255184241602507900d81040c0c85903c080d020300b1000351054012505e0f60070101c0c3c080000c80388a00038a801d0903103000641c40d0251540d0b0041030022001552030000400c01d04820480c08928060359141e044900b903020041741d00307542201e0319030154910403c10420202c01c0150014401c100c04550403583e0f81410004038450201c801000f0358580304101405080c1604a00841d001c0c5004c2d40c0d84075102c0c0e80310f504603819668284600c921442c00000050038402070b00c200c0308051240420b1540d502d0b03000394001038096240d60000801a0056002d20041c0020000c2c002e00a04030b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748423794 1250 748422544 748422547
    0x30e01120b090406090623010504182307030c0b19020109050703140115090b04381206090c040524060a270501020c180601180911030912 60
    0x180002c100b981c1e01c098001440c0c0c41e10b6900300010007082e0381008001e180c800b2400142102c0412104140d82d8080c4901030042d0301d416030401d096075001c090284515000700c0f044a0b52030510404c0426000145140d40440c06110380200000c0c140700d1948004060051a16403950800603c8041900042440304150f83c0340543c0100002c0001c10020102c81d000070b080500b0006102655014040d220f90f0001002e5030310fa004503264103107511103000081d05a0301009a220038024142c0044d06001d4044046041110320401c48030035000008001480074100c250301d159250b101615025040c0e98000c03c03504450b40030003240c06c0c0382c0700c1e4951081800c032404901101e1032a0712145200d1001c699402024005000c9881c03a008988040444582200007109516081c40400031900c15001d290b0060181c086c1144e8140b81400740c8420200a00d07800f05504d4998000544800c800030084890012000c08005001c29403032040a0b14904404121a0b4030328181c445c01e400e100c588075000c03104200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748425044 1250 748423794 748423811
    0xb0f0f0703060303230d06061107054519052a031518040b241c020a062a030206060d030504120309031401140a0b0406030f030e0112 58
    0x6024008040c0400700c980345c03540c03443c46201004020301c5051224070ba103d050440c00101241e000a1105200454505aa61864540c8100841030008030a2220203030303070b00803000f5040001d005a6502d81d01d0314aa40361068408200d901c5008082118120b103000140600c0405a42843c091154001a0364003800886a244001002c00c2200e02c41c03001302c401c001000107201031030000e04e91801d03008010626001814460309403c061141120304464103000b110114400000c541d1813800c2c001040210003c81814841c18000015050540548401d07100c3e0402d00250b118090701001501d650340d60050b14070311303040d048031448020000410b88010507060343c0c80803d50124400e600401c00325242501030804e82812240c500403070300400329021039080100c4c10590404605000c81e031042c01915200c1d00d41c00304107422a12551312041d142c1002100040c5009643c0d4403080101e02c008000048085d286c1d10748030010302e13500c0001c40100b4200440100303150b8101800c903d00d5000200e040c010f515 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748426294 1250 748425044 748425047
    0x1d060709060f0309051e010905120301050109060c0218010b0309070519090b0607080c070e06031c0f050d06091a0603092508030d0c09120812040c030b0f0f0703060303 73
    0x1e0000b030340d4104156603078943c00104a4103002c0080310403500103507161040000c4152070700030100c0c824112444c0c45080c540010840041058a0484c1e0051b180d0004451904500b980c003003481120403a804801c6085180318070000e00b41c543d0280c40d140301169102e00d410000740d03140c64140d03003017944200e0315a600000e007000c0708500c00083d074203940710210314805800d021900c103014010b0000d11414001c1094200750304001458000c850000c5071941298940500349034407040c40d0000002501040440c805165000b00fa4140c1c2126251030f0961402d20802500c0089a445401a5405c162643e182d040d45210b51324034841c1458040359080d01c2d50a0102115986407420102c00c20b410b1410401e8100011000c4010b03c0200011010342382d40741440a0200b00412040d896030010402e0444042128001c191070710032141d41c000c460303a14200115040c1c081c40c0900520454500711040000700006100b00100c41c05103220304400019810010802d145020008040e80c0c101868405c003080801d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748427544 1250 748426294 748426307
    0x120210140105040b0f1e0102010c08011d060604050a0e0609180a0b130c17070e0c0a031d0703030203040e0c090a03030f1215090f14010b0c101d06070906 67
    0x141d004503800541d042c2c0d04d00116122181d00c801e03c1c0c0d80b01c0d503060142d8031400e41c0ba503448070804200364004c124601000e00141d03008402805071074100c1c9030000c03180504420f20340480380c01c6140142003504207603a075000034100301c005800050f101e00c1800c00b881401d05156002a8008005086044e4004003498003141d50f104150b0b00903001c0c1030b011012403d04034112484a954030b4004080300c8407245c07160304e554406118400e50911900c2055400610820944003250186000c08122490401441011006010f803449048014040884011088901000b421000318440d8010310f494a240c590070400c200c3d801404903010302000c2050058590343e04514000b56517040c00e015113400c1900d5400c8910310010110390504c54a050010940031440310f07440ea00b00c68084400f03015800e1100941c0045da40c0102c0b00c10301040048005100a00c1d500000d809501e10301c00c1140c00098810703180304141c0d00b10000d8080040003e88a12018050600a45c1d41c07004050030010021071030100010982c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748428794 1250 748427544 748427549
    0x90a150e0417070c030f060207150e071a0c0106030309060216150503041401090c141e0f010c050102120118021603260a051509070c0b0408161202101401 67
    0x81400010740f00301001403480468018640100c00200d42c03410f80d180c144000c1d40680360a99290030285040101c5e0700c154000c10f1900186900901034a030301d014540e480030405d1001c041003281e02449500309000091085e64019802613491151440c5071981c0030341426031000300b205480c14245801e0084a007010008414103000303282c050303035070780d102e00742003003281446031a1039215401c03c00d440091001d0141420b00340c03080d44500c00c2461040c1d0341000340d86010124074030030706402c8601c040700d2480c00303260b515409039041c10050100d894036030301d87e400c87c4e119050b0410140384103401401490608801c3c1b4040040d00d140071490b203000301c62100074042c00168001d007000a000200e400007005182c203506600d6000d81040200d080056500f00500700c22510089082d0390b440c07002015241c0343d83c400b07020b440c50740c640c010f03043d809488400181070000c10550b035200301000b68030150424510400200c40c01030700d1002c8c0c1014039540090038005c500c2e07407103800b46040c441c002d0008030800010504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748430044 1250 748428794 748428833
    0x50f0c0a090b0901050d021605070f0f0b09030c030d170708070509040905010b04020a091806050a0306020c2a0a0608220203010b030105011e060903110618090a150e04 73
    0x1100c040740f9004843c3c61144426820303110740082124034141c1f00d41ca080c1c100040c481e0050740d07109a00e03032214940728591880341079880303041a4810400b40d080d01c40100842d1074094190356006800a001c41e01e040030040e01000080e80c01d41a1000318401c010180b03800c0801da1600305d00314100410000c00601074607030307058030a0755100041003c0240035800705074503c20140c01951118425000a00faa6102e4464015102c40b03120400469880300c1c4200340990f40000c01c076252240c11620343e00c0007034020300354aa6051085205400e0650b00742201007000a1042200d65040b240d0302060010400440e80190103110148040c01440d036901505081d8654104600390070000031400024050100300344115010352810300045452012861810725684000c1122612542c0e9180e00b2038000c601880b01a10840d00c20070412101e2900000500310036400050401c200243ca10020342800d4090310100c222650f110303000e000302d19a00c5e210000805101c101400c1c146015124070f034440c60b4a849421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748431294 1250 748430044 748430047
    0x203071e020f010510061202120f070507080409020a031a0a0605071b0e100602060906040609021201050a0b0a06030b0f01230d020a111b150715050f0c0a090b 69
    0xd0003031080005032000041c003002071200c0c1c10501180e6151040d84c2c040d07040000c55485080b003800b401c500071075840c2c000342c01c0400c3e0319643d1007800d042105d0010f4600010020104100c8010a4082c00904050031020074010390790030707031100068101c81c1c20802c000303080e00d090116070059503244000070003211105d080040d6501c550b4580344910301d000b20360020035020700801c0840c2d02915043c500d4441c403904015601c240d0b8894800340d0381c41d0701c11588241c00354000d10006000a50310741040d01410701c05440c001000d086006a50300391442250a04502c0742c0d40d04003540d0502e4a460184020b00c124181080307034070b00110101d0202807105011a06201c4075880350304c062042c00b0360305c1c0d14a0344030070684c540310044868024043e5110740480e50000703581081c94030240e10041403d8200122801032848003070309141c1409003a64070007001070304055040c045407000c144038120000081111010000317803850201610034617500094110715040f202804103144541d002108501a1911050100e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748432544 1250 748431294 748431347
    0xc08091209032505090912030606071406040f030e0604030305030c0a2d020709050f060121090803010915060f2f15010b0c100902031e060a0e01020307 66
    0x24904807401031040300c0c800310035645903052060f01d84010141c400455034001e40b9110700c16200e07602d1201c069500303401ca80801c00301d0f0583c0303030039002869407900c90110301000c040140223050405804031802d40d4118690b80c1000c04159008603510502c1f01c084410f681000c1c21a00e00421500004005a80c1031800044440306240584c0f800320201000b0103d101003c0322103120008070540032000400940310b5101d0200f001c4455000e410311445808803050590b550b03640045400280b0303003000601822200300c80d815800c6041c002e1a15541c0520302c299525403418800d10211001013020169083c101302e03040c48200d5000c03042c00038520b1075280844240840c5000380c110410628480b075540108400120449000811a042d4550041c10b03d10150303a6960500d5415205408645a80e600040000e00195003254000d0b190b440c0060211805040381c50810090040748400c142503540c8a4400c02620301d003180140c00b0309070405002582541003104003e407040500070400c2408101c0e54400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748433794 1250 748432544 748432549
    0x819020d1401020301030804140301020331061a0a09060f05090c04180f0e0601080309010c05030405060a051329211042021905100c08091209 62
    0xd1121050341d44000319683e50303403031800082c00e41c428450290181c4041d1501141443c040c420390b44501e09503103044401d800b0300102d41344600c1c0761401b840400c841d0000c0740800303d0300a00ca0012070f0f4110b40303003074000d0101310800c106100500b0f902602c181c605242e0f003131010450b185030799000c450090701c24482d90707118a0385003207450103030782c006012282d58002c0001000304560040c1680700c011090800c0b03081c0c0c890340a95103a0b8401d008200d00e950082058050701d5204182e040d035124000e00940742170948842c0000c00b244e1160000800245002c1003089520600010a000400c010480d41c02d42241040c45042080400d846050780d914000c41c11402c6000301420718408442c2680952219181243c000c005d4142a8003034010000d4840328584808050480c40003500810804800d501060074882c2600080900d1203241c21801034820890440008a00c880c43c898070807800303040d40050000c4c0710411140e0041818040002101c2400080c0c00040f5101c1d840300c02d4192200d90350f0a00002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748435044 1250 748433794 748433813
    0x23102105190305070b0c03010f050d0201020615040627050c1204020d02130504030c0c140105030f093a1409460602033a02030a050f010819020d 63
    0x405048840804100800f0740c85031b030029810303a00d0b007010300c0a01c10381342c0040c0020700c900541c2c001c0c09070340008003007242c06410807038503002440c004001107220754640c90381c4041b81a03400364030304980410314503420b0000d00c18043d25601c07024034030101c0e0a0054103100c40c503071000c0c050310284c0260042c210a00035900e0f21146101e840702c0d1201d050220f81040e10340105201c200c3c0340709072035101044d10041104500d003210449a039205030340f22825500d699011581804002c0c01259030303480f91943c0407103446140f1141d440c0c0f00020000700b40d502d000c4105121036030404400e042c2c0030464100d4110300c1940400090b81c41012041e41c1e040f0403410101c000341840b02d16100e159101c0c05000d10a100391001000b022034104d19402d4000e030a05a440ac07040c2da03603001d0a0300420080480a21001c0c0100085208005502101c9071540e1188079107803407001240d0055510b500020b0300c4804021215451205550041c0014001440720545403440c61078898800180284900e00c1d0058520030300c820101e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748436294 1250 748435044 748435057
    0x8191a060312030c030a0605011110020f07050607050d060609360f020c010f0c09050910030f110f150318070305030408071509030b070323102105190305 67
    0x5005a650341040c0034034004039002100e40400360b0b400d07c400461103510070140c103940001c1050050050135607810031100030790000e11159031b50070428000100856000c021030350040406440d00e59950414000820944400350841c13414001d0f1316500700b102d429400152035030003108001c1d200440245030a0035440160300502c0c0b800c0c0c00d0610300d0050b40303400540c1c003c085603d8403400820403920307180007800582e01d8000c94900450f850400400c40750a090802661104900345480300607504c1ea550011041d0008034142c5110000c040780403072078149506600c07000f050480d0018800d46a080b014481032100070548562032aa8001d400460582000b00001855001058a40b01e40d00c81c086c480e521f00844c0300700c6002c01d9029001d0071035680030350400720503641c00001c000219552940240c1c054a01c5166181c40c1e00c2c2642c0c513202d80300b0702c00b0b01c945000360368490590711101d20f0a598515010183c0707002e00c0883c8000300b0960001366000802030144046804803150750140d0341019111800340c030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748437544 1250 748436294 748436323
    0x70f060b011215061116050d17070b3103050d090218070f0801120201080403090e09060429040b0c1c0203060a0f080a1b090c080108191a0603 62
    0x541180e00621240284010395419a176040050343d288403405949040c803030900503803140030704001c0c040d80c1402c520380f10000d8001e03106900410480c020191450703010303503401d55062495405100646000f50107030800007001902000c0d40c1d00b914000714145082c1154014140440020003000d211b1180d00144000c603001007015803240c000c90f1584441c0c0340300712100c10005504040c94002a03000d0400c49050f5420440009540040b5900540b0180e00141050b4140000c550300022074544144d0718600c110001000340c145400d0074600824020301c0c100c035552104450622440b1280700d5214420752084d00554504081d880d054120031640c40f401c602e102980c00002c04240020155070011406100182c441d550500d50b18070500591301040c2c040c880300343e000110900d0226075040e9100c011003601d0740c59008115641c52030842112034035100075005c00d400c840108840b00301448249502c101c414101400e00c4019964030a1400d9031b03e105004202680c000302da01e64404014103040da0300305c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748438794 1250 748437544 748437551
    0x200f04091707060b0a09090b010603091a0c0a0207090b13090602090301092307030c150e1002010c17012411030703031e110406050702030f01060b1e070f060b0112 71
    0x15410716030080d2002d10441405098800b00c001100f00b407e20851071a40e4100e096680181d08240c0100c0c0030f0150f2440580700c1c5c000841451456a6001c408180603e001c5903100c2d5403481da409020f403c1c8046a445025400e2505500d6407240d143c000413a50b01074090940010354444c03902e0a50024010385031215019807801401200700705000300140c2d030a142e100030411840d8038100c1e1f46541c40815000041a84965150800024020001c0401080001d0400d4040307291401c000c107034407424000103080145c1d191301c000141c4640103010900c11003003840c0019100d41c10070581c00d510320f48410195905407500005a44100e00c202845207401d207401098942c0c40d00070342070003009840944140424a0f003802d041150611043c841c4101021200c0c8059090624100c801d95054200d660140d805028900d40107001c080c0a200b400f010b80b00080d00c1c0b54481c03005404200a482e041541b07032102c084200141070210302c44500001b80580d116070003103000211500100d602820700030b03102d00f99504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748440044 1250 748438794 748438807
    0x31803070e040b01032627100305011401050304020d1223030a0608150f10050a35060f04020402091804030e0103140c0c1501080703200f040917 63
    0x411038134100ca0080900196225000d40000350001d503140c10401c0826080060344140303038144440131002ca400d0750580b1014500d00f030209140c40c041030401400240d036200180066107244400194203a003c2c40d046040d07140960118403203076098100030300805c810180360011544918080514940903160990b030003080c0c20002011600140c610700000b40c07c0c150041040c15001800b804400b21038014140141c4414074009009240600200303444030303113560b02050030b48800346810b004140c8800e07540440100141802c4d8001613034039421400c45a041180d0203058000070301a41c00c400c124000390160380b100d1000034028401e0380840c1e074214038400034090480f1054400d1a104a000c1d072201e4a01a04544c0118101d0320700c0200c42c4290060072000c01c5005d903061029000d0741052800702c441882e200c0e4000c605a40c40ad038852000b43e40185020700400c0100722852520a9140c031603400c01c0000c0200041c4275401c002c100d2409150340384824002d008100c1c120300c00100002e91920382d2000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748441294 1250 748440044 748440053
    0x804030320072d0309030204050708063015040506011409280c0507151506110a020315160f09062f0a03031a0303070b0903090a0b0406030c0f02031803070e04 69
    0x11700c030f440240e11880c07401c800103524901036a0101d2080800400c00c0000c01304112080c6000341c52480502ca540e48140b501101400d020042003124a9620910129038a080d00d000791800205070405281d0042d904840203c0d03890b10001250002044d1050307541e003401d41508100301d1040201400b60890030100f00940140d0020024000c003402a064031425180e1068000d00b43c41c00f82840c848404030510302000918400c02820340b1301d07801102a0392503030045d600042e180ca2100b14224044110320414040503003034030b15182100c2001410074845006989201501c84904d910400083c03244103205240c0380004c8048202a0550003090805141e07000400aa50b6145d00703841100400c2ca0103c0702404480c141d00802c4000c04014029840c00303011340d030350f40d64410025124141c1403200780403010f442d40e1407141040241480d00c85140d2103034600403004045c0c0348841c2c290420f03c10f4a060700b40c0d400b640441200d0008a110003200805070707500010901d84000e581c803d507000c0002c4000c1c0000c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748442544 1250 748441294 748441307
    0xf031f110a05070320030a050f040b1206100f0203030a1806050108030a02070605120417040e04030201090b070c0515090a0b0108030c0d020d0921080a0804030320072d03 74
    0xf82d00030381c0c0f6980d040c0c0d141c3c0c2210145000540510140354030600980064a03c688005d00c0c02050200029081641c0e40c84815400e405c6480c49042c0004580104041801c12600c0304441c5400d07031030000c0510006e1440652079210103403909003000d403038000c2c0c030001c1c4403003040d5410300720b41c090030420243da9101049a182c0d00200c04001c01030042c02c00c009400c500c00c80c15201b0019043d45c2403105621696038214115800000262501105104c0020105502d60380c4a1059010b500040b409034003500d13040e85034000040905042c4030300c4049200104100060032440503a00400c80d503501d1300e810b103038030741f80141842e402451702d88610700100c3c0d120790210141a2000400d000c8403080c404800c400d0b40c840c01c2d00f40d040700004109040c100a8002d641300e0480503640b00b0655402081681d443d8602d42d50311004105009c1a179030028001010303810312440e5901d4031250251a00c846503002c0d094154403454101422007401100e2520f540e14003001e419401102036064024110168038014100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748443794 1250 748442544 748442557
    0x1308030403030b041506120e24011d0c0706050a0b0a080f060604050f0c0f1201090b01200a0b04110927010203010e04080703030b03030f0702030c0f031f110a05 70
    0x124141708903224802280358014060300d0050f2a1424403808111700d400c014441940c0c1c0010034491b2860340140403124120211040e9144802d0381c0c2c40758108101c2c04100240110f8001030244a2420440541241016503e5450344000042802c0c1c840c0d5841001038207011001681c00102101c0001e075510000540b030800c1c1c41070f58141c807440e40d540d2040100701c9004480c0c4040000b01180001c90488000c802040741c01074034a026420007c4001e91300c2a4003c00360004d50300103550b99001115517803c84038243d112000f030203c8440c4200e4160307035141c4070507400d480100120034401c00709080000303020b140d0903003000240c104001c51820555402d502c1da0810040701c40b0301e24103c102c0c070500f441030084a050351200114a0311039111036a403180594000c020640c1015601e9414244030b036002c0c40140306a00b00055000e445000f9801003609003a05c00303440030711401d659200c41000b82c40209001820403200f03508240c8182c1c80982c98006817841c050f552201da080080c003da1026007140c041c00c80c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748445044 1250 748443794 748443799
    0x9060a050717031f0e06061204030210050a0b041b020c0f062710020705010c1106070c090c02161404020c031b01090605010608040525080105040f17211308030403030b 73
    0x190140d0741e08005c000c480080e030389141c12001c104000003965004174510b40e0414840d2040380d0015441e14003510842c0c3d410388203031242c5900c1d02c070700240e20310b8940100d071b01c160030181d420050020000006503554210080e403601811240803040202d90350b000c255560207060300c104448807083c029420300c00d0b118150180d4030817801e02503e48401480000c03043c09449040e15082c0901c6020348070b14001c04190303556a540170808002030000200f1a00c40000203044400005c51101103040000e410034485080210140c5500c440800040082d4290440c5001041c1d80050341d52200c00704140c11480382e803807a00b2502c1d90703414940c9419401548502c3c03035140035100410450343c954500316030b0000c0c1a907000c1c01c00e80c0005914100000c441c402c5526448481030f4004815076144882420345034100d4043c0d4005505810203814010311940410341141c110301c583e0310b0580088613482141081d030414048011010300000c019003a140750092166402645503030700c0c0d02d81490002d0160005505050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748446294 1250 748445044 748445101
    0x905060118080309011d03300a1e020102041d0f0f0402061c150f0801110a020a03030b0411070809040627020313020a030f060b0609060a05071703 64
    0x1a03a010030300300c8080c1a502d040001c2d62034200440011146820484070180842100300b80d400c8003640e00700801803000d05001000b500c9028441096031003440013150784a00c80c1000c003c4016803e601c41c1041c09007031503040d488061002c215004a0090207540c028000171414410b00750041c0b698540440d1141301210070403400799403014045070041c03106980094110740144000e010b0a4520409a284550722810004d602864110090030030340e4240c0c81540300000400080c808000c0c00c0c01541ca001310b800c2522803800c5511640207564450841014007010360b00c1c104030506a41e16040711400d1701d07000c91040d45548040c140740403141d003c804054803031458601d000500d01c03442200b081e694000c504030a0b610300c00048246001c1e51000380750a8040700c2c03040c10301005a070341501d05005180906508280e1046519044003152280c0d10000c1c070808051014415036075602c4101c0d1203024013458010780310f40e0680f07884418410000e00305000403401008101c0c840d114400e2182091407000340c82c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748447544 1250 748446294 748446317
    0x605030a05131e260a03290108180709290102061f12030305040507090506091306140108030a030c050f0304120c050a0605070807050c1b0103060503010609050601 71
    0x10300000c81e8104004007903241c0303462042410070002d11100d600b180128240003420031040300b803451032129030404c0c003c106004140082616850f2066101420240d00601d01e2440c9010507042c0c1390f00b089503598104840140002e011041010301005402460b800700e80c1c0c0241c407400d9000180211120300750054035800c0640b4200300f80c0380c075880241101030b0041c2440340c842580310b4800450800050094005d05070000035043d40e11801713902101e01a940004860400c2d25090303050510650100c103403079050500b4451695030b60349820703030091410ba003254070101c001d00d406c00281100c0c1122410002148000262510012004110981b810f80c0e00704042800c0b20b00507656070080300e41254400b102400041c00042035002c51081241850900445075400ca80d5560300c1c01c80c40c680120b0380c8684034411f00510319002a04240c0056803828111300b80400511110b94644034411441c1000c483e02540e990240d0181c0e00000c05060081c00900c21961146641c0000c1d04094501034001480ca074a403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748448794 1250 748447544 748447561
    0xd09021507032003120f100308301e060f091e0c040b0403020d1a01090204080606010509030a0609141009140115090509100e010b040b041109041508070605030a05 71
    0xc58175084069034441a10352602242c075485240300030104c5510062808011010620100141c00c3c405000b4004503980b000c940c070804c5000441e5142d040a02c00668203100c0d0600b5038003a0000002c154401d10003807503480c07500080000800402003504000041c0c00c2c8a040040a0324003806000c030048500c01c032342c85180d440c694601c180d20034140003800900040c001440c00414045030140122002c1d9020340f41050080c8020343d0a9100034055680060301701f2640b5030910286501680900b070860a101500c00400c0d00d4038281d44000f490603580fa0510010050030005044040d20400c0843c0d024940c1c20703140400804040030141c40c485051140ca1110740c9050050380c1c0203c0407004070030151450000c4000140401911101c410b01504048003070301c00d603030310840c0c2c10740e020070b0008104030ba1000140030448004002c07050240d414010302d05a088054404c503400d074001a5070004c3c6403d10380801340310350300041e00a848240078410300007500c0c070b40c4500598010a0b01c5802080f090300c50021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748450044 1250 748448794 748448797
    0x906050f04110621040f081306020c01090e06090907081b01030e0c010509090a181a09060106080c0d060b0d1418061909021f030b010905060d09021507032003 69
    0x14410460450784009040d803013040b0301c800360854410a104142c8810702e54074910300b5000385450300300c0d524187c5020007031254104580c00c084602800c12440b0503041c00341509624000400450260b0040d8011880c0d15804105031070081541c02c00f6901542440e480740e416050580c0f2000340000d04008814103214404510030181c184143c403180e181540210034080c212200070280da81490b80c4041d81c100209074404014440c86c415900c2082c1d00010003069041040054204102a40210014080150401c1c2c98603040b10441d4881c6413a01000d00e18040170b0a01d94014071540000400d0041601c505078000c10302880c46442040000c0c0e8401c0a003850114080c01c410509074025400300d0150440800c05400780030350b542d80841c1ca800b2540100b00b10005101c140380b00980400c02d0006c1c101da15100700c41da000400d191120000d032600002a210b40141d04080711015600e112480465403007924840005021850490321002d99041c080e1110300d2900c0c0ca81807000d0b0004542e85003017030110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748451294 1250 748450044 748450057
    0x1406031012020109080703030c0204050702061303050f071e0c05060a020d0f030e06090f0705010c0305180d02120c100c08030a111e250c0e04060906050f041106 70
    0x8848441107140071900c40d022007801c40180d05101d0503030400700301c82105202d014041c40c06910b91a144c03182c5031040c0001c03664000e00a000310342000090010000603000140b00ba03d401d40f420a8131048101683e000c0c910541e07d00800240d100c00c0b460401c40002c5101803184e600504061812547c0c0d403041c044a17101c3c02001400580011000800141c01000c010750380e104546000940101a00c5000c0d140c040e00707450303284e03650f448900100060281001840050102032800c56000700d0369a0300031303189002d00030910b10408251241d00c10280c49041081e180f15800801590320344111154058445082c1c6264900400902c099000c0b0107005088c0510b01e00da00400781c40c80c540c1c402e01c1000c004d101d407540c0150860710402c101c00b6000964541016418411034265594240000a003c958400c0d004079101445c5007008007004100d02944610442d041d5403510032040d03480c0d10300b1100800d440d0000a14030303407400301071100d9010709080c4a0710962064103a1400171251b4001c101150150b01b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748452544 1250 748451294 748451311
    0x212010f0e04050d12142e081207110a03030c05070b03040c03060c02010e0313140a0501050406050d0f110901020d0c020906060f160b09120f0f0f190306140603 70
    0x460304400d081d1281d001e11400c00300010001442441c003429003c02120f082d1039405001c40440c7c0c42d250310300807850340c0406240c0d1014000b4081441c029603070351290114002d0049162005c1108428400d140607003801f20b10008007024a000d03120320300546401d407500320941c1e07540300324031000c1618521081268000d682026040b8840c618541e02c039005006025411000c6540f030300184000d03580200081e03c0d0401400c210151540d081000d460540400c1d203080e10f02c24800f014080242d40d8202d0f00703d40a4443c181381c607236583c0908808050140c1141d416060856180c044441c04a0058030f02509031400242c0c02d564074946501d0044603804015140a94445110404114a89005401403580d0700e41c0307903005c41c2092407032910b003040c0d00c2507004161800d00004007040207a4400344111300a00140061050401000d468000124080c600d5604c51251000605a6843e60004107603202e00c074982c00081d10340d584200c0c00601504045c0b08485046800c1a002c40710f0386444415a40b150201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748453794 1250 748452544 748452553
    0x106080f0f13020f241e07200d0503040b071703071202031b0c07090b0d050a030338090105010e01020a0f0809102303070c12120212010f0e0405 63
    0x703d40820603800c020800082d40420204056901c440500040000340c00868403c03a4440425400c010080c00a9400380500c1c0c080801a600010301078090080b066140c210b840841d1a2a1801141c84014880c501401510004c40c002800116181c0100081c1384100c1c41488280760f84d1204100c5400b05480b0080400d98610f8005c0780c8a4140d809103074440400121405110a02000c541c070035405850540007036044410144071040301800380c1e14054005450048251000d86c6078035071109440c0d00020209030301c44094010318205182c240421503980030440e03138251210704620346494400401a401240704400005540d0701034a11418001010703000b4105400f41c550361b444042600040c02c64010b001806a03150715101d41480612000031500d41100b41b00c48402a0740390542c0200700301410800806c00c10400030380c403000440c807141e0301050f8a0850b000b140416a040d0101080580501c0e01c00300d031106665401c082024101d64200c641d400f50b90343c070381b44110f649090845029185500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748455044 1250 748453794 748453831
    0x601021c200712110a05190314030d0c0c030f02060601020307110607170403062004030209091f15090e0705060304380f01050a120c0e0106080f0f 64
    0x1168800d101c5204800700341c0c1d0b6155250304070b540181030030343e0b02603c01151001c28041c04e824407080340c1024000c1251b4110186461000111070f0303401501005055002400ca48150100e042042c0c520441d45441c0034010400c0c9180002c045422003081503000842841e402c0e2405800410100d00a12043e40039506c0e1004070780b520141c1c0ca903620780080e0062030400145002c0f81c56407103000100d00f000c43c5070f582e0315465401c00805075166444204100c2d100d100d500c41d00b100d20b030412030341100e42c140d401d402c055075150b00c01360a107444400c14911442072031030f02c16003040700340c2c3c410b1501c0800120798071002511102601c1c1120003405030380c1925844900c040c00746141c4100031310b503c9440382c00d400036010041c210114164168403414042031081c0d5641d054454805648181d0040585450210543c07500700010020011489100b201c2e501c0d80320350b401440b140030307d0403001e080c0b00b5071b4283d01940d45140c0207000100c11102c11140d0a400030200e010300c008103a280c0e018501c1e40c03103546500355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748456294 1250 748455044 748455077
    0x703050c09011b0b04060606180b0403030804081303050f0d0527030a05030d050a0614010905010315030803130506060d030c021005210a06080f060a020d0b0303030408030601021c 78
    0x128000d0043c04034841c1c40508070b000409000a02e88558402d68011940c5460308a01500e408500c01c0016400900e084050000c111190180c80442c1c0d09487c004480c0c1d01c032406c03c41940d2042c505001c03090010400040140980000d03d003c946050038212160540345c1d880c122654001d4011305041c0029002442801e1640e1071109030b47d400303004050300d00855140d07480514640c030070700710f5000050300c50040021510b00d511407040200001405e165035020b803400000d00345000340c0035450515a03548803510fa92110014650007441d1310170b0a007075580c200845a924802c1e4641001c40e100d10075031000648506014481d00c01d09541922044943c1c007440e406c1110002c1c1e8040c400c01007210030300120031442403226101407c0507201c485104a4204100700c0402c1e20000c0e00b0602096022498400b6216400994298400758246c0c00580f19543c0d0902c4070042c1542041e919498480807042c03109100380c0400035030281100341c003190800c101c0100c60814840c000d44000011840b800c102c2d41184e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748457544 1250 748456294 748456307
    0x20010504091a0d050d091703031f05030316020f01051e030402060d021b2a120307060608070e060a0e070c0203010b040e030d0f0e33011205060703050c0901 68
    0x440310002d0000c02e004108042000c0f015031840035180c5520484030044002c0d004500709014090220440c031424041002040d0344c0d00c00588010526030703052076401e150844030300140001d044010243d81d0354181e4001080c65503c0c0c041d505074468652494400c1e0b0700e6025030111641030f50001c620000080340c140d01980c0c0b642000300180c2e0880c10801000b0a200b03d144010409c00c00340e111030f140c80e080408001c6103820121810b04124160900c0385003414038046000b4804c06200300e400142250310f6180203400d40c012628010402410803402041039200400c0e5102540d450401c2c01460350342c0e42e02041700c402c1280c4540e02203c0c1c3e01101290040744942c191a4220703001900200e0003280c62404102118201c038041500b50b040070401220780d40c0940519001031403241410320000410500c070341e8171460030680c41c000c14a083da8404500003402e06030f8000403144441c03910620b41c1d441011100d400311002c021aa03a004120001c3d491030701034420a80620420100c00e41044400801036840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748458794 1250 748457544 748457561
    0x150103030c030c0302190f11040c09090b0105040b04080607080c1e0708120103050705040c110c0108130b010603090309270f020c01060321080112081b060907032001050409 75
    0x85002d40f03c00d128540800100d0821003d200f81801f01e5494514145180138482c030404440c450381c1083e255100d82c9611005100030354000300e000107941d00551005807060310940c6d00c115000080418001210840071980c0380c8140115211764040380da42c1c01016505203d520400c01c810245170705800b5903104040301412403036224507402d91406044000c800301d034901c00d0b481181d00394403404050215040c1401500701d400ca007402c00ea200705a050700800d854150441a0038100000440041d410710640105e106a0540104140c0c0c0d01d56181d000c0100504020b420990210380340c00b0f00050707281202012100c4904042400a02e00b848001e03410018180303125034480019004d1201c4240c040c42131284c04011807291501c0c08080004013121002c5d00d01c1c508860092103c9a13004021000c508200d42c6031541d4040c0704980d03107050031121803c045000c8529a035440c4120400c0100350700c00060303c1e4080d01d00445d208540c4d10711000756007902c03000e5001c54a000400030b020400040d007031034000030030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748460044 1250 748458794 748458797
    0x4150216051006030c1a04030f0302011d070e0132060c010c120509010b0303030a24290a09030809060d020a17090102160308041109130302150103030c030c03 69
    0x80d000e040e2a002d01c0c08500344010342e031150f55034074200100300314600100000c2c000038414070401c182a214001c0d1a000b140b2020348031010044844007094400e600501d61040e50074a000c100d00c1c0a207000f0390b40d88410f8050b1340e0f421485003001103542094000d0004e002c40c11441e030711500424403000101800c1002c15020340003c07052040c410300741001c0c0601c10054120783d942201d500229440b0000342e900280c80c48500f40d240560082e40c2e0748010084a038416007107400070990405003603080341e995940401e028540c0156400100c1c03200800341004800c0a40001858140a200c1707903520024452541444c021400756401000003801c1c400262865041c010481030030f110203440d881f41a41d00280ca400c000402540540a01115418685030002c603080002c41c100740400040c5121420541c00c090709009820000130200140c03801001140000070f0003040c6142071940c13107501a10381c0500200c02500411007800d450460032030061741240d4040d620360311140d01a0f03c5c02e035460080c00c0b50540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 748461294 1250 748460044 748460077
    0xb0906100c020a3803011a0c03040e0601030c020c0913060603080a030506100f1403040212070e1501030b18090f0304080a0311010221070201020904050421020303041502 74
    0x981d40b0100000c000341300103840800c0902c0c0c6024900948003002d8600011048a45410f10f0650040c8050340e05541ca204944040b80c0c100d42d080300d0485c010503011306500c0c4000071740490f80400250005004020a0302e0512103c014188241c2c3c440c0000314100d034021225400045030040100b00707410a0718010310000420b00d48988440301298495000403001c2901c032000d02c6000c3c109207902002c0c2c40340a2919000c81c1c0c5650b04d0044c0074825240e100001e1607070110105040d90389010480b4500c2c4032000840d9522a40c840d0305481c0c10313001b01c07200e0b84803415950040030039501a0041c0d8407034000c0240f20040109084140350100d05001e0101e036224800c41905545186c004c1000784041c104e640c000b0130321540c40e40b4005100810701036811200b640180158040315800c0d201c1c61035003001070140d040036a40c503c40201d0090107040b1040b1750050500007888240b0414600348031100414940c50844044001c40aa9483c4401d83d8000c108882d0000715040c9950703554080c0040040c1a00d120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 748462544 1250 748461294 748461317
    0x60c1703041a0a020d0905060708090303010e0115032405040e0c090c0a030207050d0e1f0e0103090201121a030f03040e1503010b09160801060905011d03210318010b090610 75
    0x5d000f01e4814140881e031550240e41801019038200c02d01a50110b5a00700a524541c140004170b41450018801d5022907015a071400000c10f000b82c1050032220120b1804442124100c0d02d1241d01c60107510070b05000300d191100a483d105000720726000111005402c0a82c50745492260300b02d158004040b003c1010750900c941000210140704010300e0301d0495544c104014000c00400ca00c05c0441c00701078905003824002100303801d810080860840c1070900303000507002c4103400160b417801140e40d1044025450045006c4e000f0010904541220300280d04580715807030885c01e456901e01c541d000e074403940d504240024143c10300300c0030500d0744002b0140c004a520303c0b4440100301c0201c07080e1503410034801d11b405010b503050340c400c400d2401440c85140004002d403500001a110320080310b0900c040c042003130035407403454a00b040010880300425941c0340c40c405500f80c00444640042d03541c04844607940e010294000c0301401000341101f001000c2070b01c0c41d1504410403414901007070310b02080c800c209041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 748463794 1250 748462544 748462567
    0x9060a21020319110915090d05031306020120250501020f1b15060d0c0b0f3c07020f09070f0e120318060f04060c1703041a0a02 56
    0x2640c002d0f014a40407250402a5414038801d880380ca402c2070035508400c2c460304070559a8480e8044034815000d40b4540c0d0f030054600856028040400c005c0c042d88000544114003806142202c41243c401d030f4000c2000c5032540c07000301d180420311000c50004078800c1c01401010304030001202420032111940b141e08080d00d907192400d980080820344080c540109042640c10150043c030300d02d01490b01d001d003269140c1036458603a0420054031090113814401403d40401030007143c54005402d20400e11511148000c001f08004e521440c1c040341d001da0300d4109048000e46050b0f01c8070740c3e140740300008103040e00c0d0b01c8070030001900540300076070303200d000310650940b991641c0407403d0082d051660b403034400c106004009400344c40072094aa00a96050000482981d004001d0300d07054101c05240c070700c03ca04648006415805082c5403c42d0540000600144840d0091401c00003184a640390503407011107100d10400b035010455000d44945901085c10309a4010b000d0f0031580081d00601c01418220350940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 748465044 1250 748463794 748463797
    0x11010606080103030e100f18120b01090606050c1c050f0304060e1605060f0d090b0f0f0c0a020a170d11180303030c0a031a06070506100b09060a2102 65
    0xd4086200d0720010310030302d0f9001c004842c1d201c03419035100341c5101481c01c0042018600d40b10540400c546901425104104220b585005040c0502c040700c0304d000d0b070305000c0c103100428451051030515144001540b10702074016101d0384d0440c1c901402e0550115814952014034038048401041343c100800074442900001641c043c0380540c40018103d940d801c681490015264581141002030060400c4180d031208119601c82209034070450700d034500c020081e009403849410003084d5809010400c40c4a9065a880900c26584032a01d020103480710701403990140300e03149800c00160050040c03407010a50180000400b600d038041180d2400b02c00c080540101c1d00300003091008200002400302020080c0c4104101843c401c0f03020710b1542c10000c4006501d44142013070f501c180360310303100d01c050f02401c51400b00550300c0740500403940e18030143c50b016803152800c03202c80049002c04040131541440140646840040261280303203040031003107044e40c0d040035881d403907503040000c41000c625041c1d0f81e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 748466294 1250 748465044 748465049
    0x20a0f020301020f0315150c07141206070c031d01080106030c0e060f0918070c020d05100908040509090d230d0e0303040201120e070315090f11010e0d0b06040c110106 73
    0x3400c1800c3c007204081203207042c016507000c0e01c8821f05102d0629050008504802100d9a21454034594007400300440c441071440d002d900d0840c0944001c0110041d04081c0d080d4002e84682c0d62429010443d00710000010400344010340065034100060200d50b0082d4801d010281c01b5042c10304440c0c018500042540c1d00404103401d031940c1c0400c101549040400e129035103021181d41c22a514501010000d101081c5070101910603646011034000380700003440203408800602105100c00c0720141040d40c2640c1c0301d0303c5580e00826110000804000c00425110100b003070541d54a081c0001d0307498002e480c044a100d060000240412102200024034400e070088860014041c2d0703141e01d064000908070900040c1d02d110b42c00c2c105024641c0900380880d864082d07036881041d440c850382600c20580010710340701d107004200c8888070150009018581e01e0300360881000b44c2e9040102142c40040c002481321111000b03240e00c09010219005181a82100c1050b006500e4003000c9401003440c0103081d500c559 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 748467544 1250 748466294 748466311
    0x304150504050c191212050f0403081206060304030804061505061207030c05070f0b04080d090b09061503101a0d0305120105010e03031c1d0f10050601020a0f020301020f03 75
    0x882d00c2c0801401c00c2504010b1110300c408424084d545012508441070003241da005052120303900d1a40e50b101c0c0038000380c828880ca81040d0507251a00ea1815411590003000350131100306103900001c4d468a45001100c0c4590781c50703900c103441074a0305c0d940d110140c9084400080802c010510102c2d154591300054030042e01c1c00224182e40782058400601198200c0c140102000002c02c01c03a4045100f4051030940c040d4081140700320f41c0d60b5800c100c2e8142c000d40460340203203410106458180100d0605950191408400341c8182d03031680345d00c0180c41080d1000d010303010f8000f401054481c003550340c800031030842200c130416001081c000c0020320301c00800310205c0218101080710310031203c81400182c0500020300f404040341ea10400021f641c1d0142440034038001100440c0c01c8000300064000b80b0801c8440c1101c3d0285050401c0110b0312401104802d04a6104002031401008994000c1600915042c1c0144c1032518a075244c0807555400000305a81644d000c200d214940203024004500c00e1489 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 748468794 1250 748467544 748467553
    0xc040f0b120c09090106030b190615020a12020d0c0602030a180b0a05060a1206020306121002040914062d1c02100201060605090f0d0609030e1507110105030415050405 73
    0x1210b040208640001e803e02503582e26003841440002d441d0980290022003100300f142e005800c0c2c000200141606400c1400116a40c1b0a000c0403e0b80000b183c0203001d100300c40c40480e56000c540d0481c1d4410754004444d000500b103622000114086600540c4c0000c100c0d50003040d44c4414541080050380500021145074464a081002c00e074840c0c41140d030403d104407902c150305450a1b50110041c00b1b51080034141d50f034000701042c125030703c80c2e4220312a51221401ea5883d00c6200780040004c0d0024892480b9440c14441480c4000c0c00488000e0b100d000000e1810501c1e0360101c104900c10120300e5041c520049400c2e040c800903588010140c1e041c05d110069401c001300042c81803000382c0c040c40c64054150780c10850103014040d04003055846215040d00c0003002400048000b51020721500d401401e21403404110206050340580c800c4140201900c21441101c07039002600424403542601600f20601c03d801c038501c03503114400954009000341c03054400c40140843d90780440b001a1000c46186d8403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 748470044 1250 748468794 748468813
    0x20c031213050607030b0d0303020a180605040602071a0a03092a051e030a060b010c0204050103080424080718030827120604020d02011e020601031a06030c040f0b12 72
    0x3010405554041c00605d010720104420801140031505208070060525401160031117646120303029040e6000c81407282661425900c20000e4580d5100303003d43c00c018000c42001082c000034500c0b000c7c1850110b140c03824908542088110010041c0c0c0320204d0f80c00a81090b40201000c07000503405462001c50510750380d0f5898002000b40c88080341d41034101c1c10000f0f2048010b140d0b004100744954a4224070007207903c03044640125490241d00e00020740c40342c03902001005120201019105840001c0d1508503001d18220042031054050110381002650000004124500c1403c2d40302c80507032001d002c01a81030b10b90b601e0381901d40020780002c0c00f00c1041048100c5200807145071089403081070300c1c84440c09142c0d0701c040b030f160103000740060b0082a4500032001103901c101315810400044103c1300c048450103c200a440309020300c42a141c00000c260182001c0c01c48954042c00340708010010f080407425041400b0240c1071008011a020303035031310540700c030030b8035001000c8a1400b1041d020707142e910f1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 748471294 1250 748470044 748470053
    0x4030305090406270e01060801091a01050916050903071d0f060a050a053604050606090c0901030c1e0e0a08070815100305011a10170a020c031213 64
    0x210181e010030303940c1300c4c0b040515908100803c070410f000c032000940425400352000c41c803405881d0603807007100c1c903610700305034607040c0009045900408030303448041c078a182c3d9983d0700300301400720b080c1d601c0d00703034010090040c401d15801031004102744007015090390f2486907241117001055a10305002c0081e984443e08106101c02c02518085d4000700071956003d60170306150201d00035050901400b0300034260403a40503100110b0180c213045d11200048a03084c2c080410103c0c1c0d495050960307040f0b807030740316010114995191001c843c6104a241c00c0405003010320100044000d40100c2c00c0c03180901011b01c3c415151480c0d58803038120305290303544a01882101110034001c841c00158002c5006030024601072241680210790640607101c0c0c0c0f04545d90a407034510400156040c1a84010265882d28203e01419080c1844680044100310740582401c41c03c1c150035101e070341141c0b103200c4d910002d040000380048844d40c0601851100c1e00100c904101ca5495040d22900f0207903030032204a00b01c0c01c02c440400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 748472544 1250 748471294 748471301
    0xc0c0a0c0905041103120d0b0f0409060b0120030a1b050a050303010f061103040302060708040b030406092009010b0c1f0204051f080c0d0e1b04050a0c2f03040303050904 74
    0x42e84c09030010408908684010a0140034100a01d0881031b21381c4000c1e005907032000381c15440340c200100200b2102040303140620080510410407404207680440384000055040c090751a41a9050055881c1418100046a07101380d00014080c03a44046542038010420401203414500c1c0321360b000315625414010f00c481017450590010b8104201111711103003004001c401c2d507049a03416105070b911000c0d9881c0c5140300307020381c1d0042d02c23103c600441000300b8004103030400704102c0d0081d20014255900440041c000b440503440841d007003203960b001000340c000c00100414aa0380b010081e1265208c4080c1304500c0c0e170f1829071081100c0c50700030034203000c50b18118001502c04d82e091108040000e441c90000352500c4e0008240b14010540414600360080c01c580100a1060b81c840c141c0b00c0d41551507892104010100000c5401a481c00c000120069480d01c525699001c05848400c03008071b41803800c40d40c1903540310021050352290041107004c14020006800918841d4550a440d89980d030207000c101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 748473794 1250 748472544 748472573
    0x703090311060405061c0204150e1302070812040305160b0f0109050103150c02120d020703140c0c09060d21030509010b0d0206071b090207170a080c0c0a0c090504 71
    0x1e00c02c1000100200e569642c125141c1c407285011410008540065003070080c0915480160b140f40c0e0b4510841c031041c0c0c007200c100f00e4079804544401e219984600450300b203010712480140b81040400031821004445503101303078000d1003031030800d180511801111130119003200c2c0858592402205000c01320111418440c090150380400b04020742c91a00c0f4080150100d130300c0e4001c115900c0940408040c1300b848007805401800d030b0f40310758884001260100035403004900383c000881c02507108075061205402c58100d84903440081200c44021401c1094522000e015590304c92400c410b801d0000d9810750040b44103d544000d02800d90320300c04030140070f079400185122400d901d000b507207107065507406200007030894050f14490b48078003c0785404000e06032400d003000c811107400100001c0145064009001e964400c110b90070030508015160740355030027130086241c00300c5c41020004600e910314101070904844108100c0b0403a10141e00c03440c2c600c0c41b05802c03003410b19840f00d0810041c07150b910300b810103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 748475044 1250 748473794 748473799
    0x20103140c040e1503030a0509040b0415062f0c011b0f0b041a0a050601031505091506040e0a14070e01080a1a03010f09062301050d03050403080703090311 68
    0xc9407400215030640c900c02c5010b808424503204011402d503190704810f0024024002d000c6907070364590104041c009400106150348074508141d103522513424280a14111f540010114880b03150420300c058801e081c1914101d0602c89140e5021348045140400c020312500c4040003806044121000045c2080010720501518842c24000e180000b0200483c030303143d264002c01c04410b181c866180000107480148803951141e06501c0a00182d5a025403101d03000b09000d032000c0007950b002064441e881c0c0224402d4a80c0040039000062020542250740040e40b54001c000510b407585030461507080102c181c91002c2c006990340e40c0c0005800d907100c480758110790740703007003190b00024803000007088541d00900c0d103c0c5064980d22507000c1c11600001d0000c1d4510018000d000c1d14074198080c00081082807000d8032118100802e450140540e6003086068100d038011503030316a80ad140c00c0c05440900c1800890030840d08002c0000031600c40300103410081c0c800d0b03885d001d0740c920350b0425800200c182c003c29032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 748476294 1250 748475044 748475081
    0x40f0305061e06040203041103010504050f2a060903010204150c020103060504060803030601111009030806190503030d02070201091505070c1a0d05091617060901060f0506090328020103 81
    0x90700b01020b1956804202120b0140c1d0b00e641d1403230b00c420900300314464540c040d802e0205010400101140c00e01c004c280d41003c498012048442c100e03a01d403044104d00d441d91500b1100e018880c10820f00621101401031b0000d80f0b0255901d01c88010020b91050365400612088031800443d03916004040c024142280c0a001c450305064400380c40344000b82c07030305d414000541d00070512440240108080b108d03441030100031142c25410040c00c1c1c8401118904d00c070f10110324080c07041080462641068901c00b90085080c0304150741c4103030080d40b004070242d040c012030000000f081c0c02034111000b0110110343c2e8258643c00399203014140c040300390b080207580d20703076220003103c000e40c1048c1903c44128050501003072940b140b012144c1840502e940c02e1850096400000c21840749001207000d44200d11000c582c0555201e01190f4201c88082c000e00050b01d10034a002c21017840c00da805460722080c0241940c0060104158580f6041c5403558207426807048101c2c400203660305031007800d8072001d49a1491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 748477544 1250 748476294 748476331
    0x100b030a0804060f1403010f1d13300f0f080c2b061d07020109080d1a0406150215010e04230f07140d020d03031107050102040f030506 59
    0xa40c81400742d80580b00403c1103654404156920850300046050100f140a40c0e5958440d0b0b680e00d15001240580345408a80e05140202d46c9060052a48a5000f10407000e07040c1842e540d400c082c810b504e4804000301180c980b21003042d0101d444800d40e540038603880744c1d1408044000c007d017003982191105024814040e0411500007032040c03c07200e0501c04420b604044400c1120721010001c1c0c900c2184046e01d01e0f08401203081c2102e281403a9104411507005029591b611108038281c0d140c00700014001241807010f0714031405690042d000c141110386110039001138000100301144ea0540c465950904102c234141801501400b0304900e540621382400d0305981400c11000d4650800741008000c070741c04103044004200c20103100d1040d10154401c0e15240201821890340c0c5000500560100300704144400c2028540102910b00155001d01401002843d5407801d60003002100d0a1001960040010800040c000c0c0300403c00340204154a1000d6419800e0140c90294003d210740350850a41000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 748478794 1250 748477544 748477553
    0x90302101b081207450f090506040b03031602060307030b040e0705010315060e0607030201020403020d0b0a0506040c1d040b18040c06020c01051605100f0507020c0103020a0f030e1905100b030a 84
    0x42c0d008948060381c8501c3c1800307200c02220340c0403486a01c6441031144e501e402040c0f000d0590480d500a20b00ac4030709000e1511684105a204c0c801c14414030500b100d221502c1006051100c01381d64080301604000842c10305c50b0b004281921264140c1044a4001100c00d1001d07613094841d00b1070483d5841240d110a6082100c06081d60210810141c800c03140803d1a20406100350101ca01641e405028140c14990314a4444400c402c16501d680300c1c10b00340360006195040a2040110502d900c2c0ea5151090f180c08610702010005080070942281c4c440f124a182501c8a101e074010a225a11440c00c00b0324043c188030766480616081102150802e034203120b130300c0e03234804140d4140600208066400395841d06d0242d00d04400034038010a414105080703e000301c182548018484c0f03043e602541d06125080300114203d11504113400d010820040d00320203901c0c070940c010240c40a4200441c2c0001d1102d83d03084002e00c003820003c5440390710606080c01c49001c0c0b40520900040e00713070300a040c031381c000f0395a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 748480044 1250 748478794 748478867
    0x21e0601120f05070b0a080106111c0503090c09071110050903090105030a180309030201030c090f140d0807080306010912050703060c02161e06090302101b081207 71
    0x10040d28070201c5001a07414080107000714001400d05c050100d44d81c805021011701121341c00d00c941d2001c03070004105602c03407060204200a1241e40d4420408400501103000ea410780c00207481140d01e48180944403200d82c568195940c000d20241d00c0360100c00d180c101903146003448607180302030628144400d01402d0399001003506c111200074200542c403583c03244480030042c89a4040c80f55910501c000f4041499004035107041524001c3c0d074107002d0705d01d150006850540c800c0c4145000e10003013240400c2001c6210b611070010f0200201100724403891a16217420541100d50305541c0d9900c0001400415030300680303200000c04000c00000e9003201c454030790644070101488040e100381e4032000b03032115441c400e1044a0300d0420f1000d482c5081515048100410280c0489450100031141400300700107005024850807a50700500c41007100603d02c10031114400c2e4801c0005800392118a00e0300020903502c003a00802c002e280c1c4c0d806a41c0b5208000510b5040940b4040c0c41800d054020420303403d12208 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 748481294 1250 748480044 748480079
    0x1005040212060103231f1706041502070503040f08070e0c070f030e1f0807030213031106040317030f01050907020a1209272403240507021e0601 63
    0x200051440d401000c005d5208800141e01c19466015500704400c0d02c44204c40244882011741503281c280b522040c82a0b00d0802c04c2d4014505e50380103d000400140c1000c0852443c140e00034009400d1107610b50b540e501c0e41d00705400074420603410800c14006600f0400c003038001040c001c08828440d080001200e9000c2c440c450b000b03040c600d01054800241070040b83c5400505034007a103032003c480c460715801011a0840d00d110340019500c42d010540042c032a009072030680c2c0002c01382c48026840c41e680d074407034052105c0049070498000d01c80000402c4850510013840d03500f08a1040d0b89240000b0507400e03440e016007041e407050340348009100b101342d03001070511100d503817066400d83d4985150800382ea140840342d01055841000381420544281c91030070290f4030780b58554051207010341d051200310307054211f0a021001c010704d0308410008940f080c2002c4569000f0290340d0f410764a82d142e604001e4880486895000d80d020052050544540c074a800708844540c0c8040c0070f46504041d20400400b0610 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 748482544 1250 748481294 748481297
    0x905151e04020d080d050f1b09061305030316050609120f0a090e090a0c0806060612181507080a0501031104020904110c15010602030304120f0e030d020610050402120601 74
    0x58000404645903d5807000b1844d801c5042c42d43c0b100b01c20614100603001c00c40d025420000c000b00401c01031608284810307003ca41ca105007500b42001036007440b80c2d68000655081e1a800d0f00c0700c1c00640b41d141030004150369140d600d1a201110120b00741640b800502034400039003603004100e100e4000c80304070b094491507000e202106507111003d15044401c3c011507001190310b0b02c642001d01c41e41e03010000d00c2495031440340d44520703600c0ea50740c04d040e62508401c5801580149040202c41050851800d0003580181400303902c080a1081422701441c1921041851840c0e490003414403040030b42219030168002409002803110390305568644140e03c01c4001c1302070003160003041200e11683c8980102c2107800c036040e18540c6440380f00c69055074504600350050415005075001088051012048074403607a000700384480706100a080071951040010480010004035480b107402c83d81d000e0020f01701c010714580c020400307402c0c00c0604c1c0a80c420194011403246104024020324002551102c1ea4401000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 748483794 1250 748482544 748482601
    0x301151806030f09120302031902070f03180b0c0d09090509100b030c1f26040b130807030305071107180b0111060a0e06060a120f2103090515 62
    0x10304840f0060040442c00400c1c600c04c0c0f2041d281040d600d58051481440d10018030f1946500390f0f054101240f007440b41c05040000c61102c03d10110313000c0e801d64031000030032550b13a00d000c030b6445090380340a4202c0340b1905856041202580c0800741e000610078050311240740200420b08203601c2666441080a1001e460309460394554001a42c0074446034060000c0900201d9940814011310040ca220300080300000c525540c10f00710080002c030300e5448400038160743e10b0000d07071296150074650708402000605031101c1c085148002803203981c050954103100740c6020030b45052180015007098040e50030a4101e6100310720410025080b42005da0144040c0c010001d551250040100c4010000c0740044000d440380340c3c180010703d1030944c004012604075006a078015110714082204d00740803403249007402072018102c00c2c0840d0841544000462190101d0010f0241075401120548480407030800844c1d0395078400010300900780b160208c02d000000004041b03143c4003100c92059052401e6418078403c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 748485044 1250 748483794 748483811
    0x901120506090406150f3b040f060912110c120d08060f0411072604030605061f0c0203060610080f090703080409050126070603150905010605030115180603 68
    0x59100d02d040170340000290318903590740741c6080c039406081030001c1031041d840c210000c0d40c000d51f414049420001260440c000580c84a445055521050300ba0030707039415a6440034100011031461103089080510f403180007000400d03944490070003101c1207040340204107001c07081146480200e0941d10800860420b072009440f0200850176412a1364962600185000a9102005034480280c56051710030044040d910880c0000d0088001c42032035050142c207414030091000503003e0f00143e0f40300001a001003180883d00c4c5400011101803016000420714105c10038055040c24807215034880b0040d500503d8a0600700300040c84198014906c445614035500400c030401003c2c0101401550840303003403912035031240e403800b005241c02c2c40b03000410365040903043d200560380080d40400c0103196018004461806005401828032180614510440341c00302181c8892a4800c0901824803507991985941c1020026410500100c0201040c0306030155109a60003030000110203550017480d002c550900c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 748486294 1250 748485044 748485071
    0xf0e120f06040c15050405010e010503090c0a090c0207080105041e020a0b0703021c030e0a170d02030a0c03110301030519031416021c020102120c1609020901120506090406 75
    0x142506000118001ca5050009001c0002401e0b025984600c89150003840ea12a043c1c48a100e9032080a020070b0621030141c8040d070095000e1680041e401301500e48100d0400c00003007406080f40c03c0031140c55500c6902c42c1185904002c000080d05a82008000c030b414030313448403110b1540382c01d40d241c5074048003024401151500b50030700d0000c000ea2500d498841c051b40c600652155000b01c414020a002c00c048601344034480e014600a034140f240c0680b1458000ba00c40605098907d0622151031108110b01d020000091008602c21111a14002446198903c00030b0076210080c982024600701400188041403002c82c08440c5940000c0c5400c001c402c0900c0c05845050502d03104c00701040000c03034515503004514448050040c82105c0b03124000c0c001000d038202d0b01403078800c040d0050f800801d407101504501c0e801000703524035540844850406000340e008180c4119080001e12940200e03100d105542c10985500788118036510501a514003100421080240104064410790b150324100c406030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 748487544 1250 748486294 748486303
    0x120f0302120c070801150315050c1905040906050d230a0807030324080304090e0a0f080418020f270a08160b0c33250f0e12 54
    0x841c0c0d08940a441d50000100359440307072224841d204465003005894035400d0084041182680c1d8842507401c44800c44d81501030040c040140000020101000750b4104900c8142019401c10450380d5119665810101031805850883e030085005c1d058204c800c0c800a4040701c2090314940400c5010060b04040801043c030388401c440000e40300805c002522018598150000c001c40d070800c01c003c05600707242d00001c120a24840c403418040d0b8000703110600840055410111601d010001121100d084135106c04000651002d012104590300017020421191802114010041c84607411800d00c0800350486120380300b8007000030f1419400b17001d40c2c94040740c81c0401c0e0728400005800c0324a06a128050156514044410030300e00c1124590b0000d81546c0e00000c0341c4135100701c0805400001000c1840598500c0e0801a003010b2a603400800d0307004940c40c9041c0c2e8401c01020294624109426001610403451000004204482002014030b8940c2204404c60341071415104c041030070303c28002d644c2c1070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 748488794 1250 748487544 748487563
    0x30302070b040c090e0a0503180d291501090303030b0111010906061a03060d03050a110625080f040305090f06070f030306060206090a03030f180606080c0a120f0302 72
    0x24403880c1002c2c801848034405805081e2003000c0d01c200280b80e00003840907134070006540005e0446d4010821202103c0f03031030082040c0b80401900e40c03560703116540d545018116082291002002e03203c505507950200b030300b1169401c440310852180900c844280003e100c1261030002a09060311a29220483e0348514035607849001560001c000c0070603249005006040c4600c1180500420000304200c00c0c00044210b0340180380041038030050300e010340d03001e4855030414104c4406200a40d0b2207045c0b03c52052010a00c61481d802c040c42c90500050720003100d1240b205e040748104000d000421030002c030b10b048074640054060400d0742d00d4250802c005900d07000100c140b541c0050010030000100400426000d280300d100392800d00803551a040f0899844c842144c1c0182694480201980424000c2c1d008403c2101e0b92000450b501c01200704007200752030601002c032180d40d610002080a1300090040c194851000c0720305210302e61504440c1c181038491400003800240465814004050003000318154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 748490044 1250 748488794 748488803
    0x10062414071505060127090e1501060903020306010b032202030102040801150e010e0f0f0718060806091b07061a28080102091503151c060f050c0708030403030207 71
    0x1802e00725540281c01d0584509011440c16840c0d00c40a00a90304030400e4054064007116203d0303c1d10305014080c0c031941c0c7d01e00400c3e0180b1130b03640444212088155000e0038054858000c003503c0c5205140c0707001c2c0142e010480310302c000c0c030621040c1c04450b00307070501d02140000741c1c2c2482821800028024880e65100900561070903c90410309118990101d00301c914200d10004680c1c4daa601121000c0808c03114007101e10302803000901107003242540e4a40203603003450a004400b241c001c0701d0440004035013001b404100481c08101451400f0b51810358031180101d10502c0041c8c2e0350715043c80320301460100a0801d5207500e000d0340d02c03106402c0e000f807a0080c001d11225050b10440000b00d02c00003414030700d50400312200d001203a404014004c55000010285c90040c2210111003c00e585402c0580766240680c41c4150460482d550711171703614030303241049024058400940c44d240c0111101411002030480c244010841103480b45130075903210035001342c409903507640c80e1b24040b8024403404c28002c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 748491294 1250 748490044 748490063
    0x90503071401030b040b03071a0d020a0c0501050907030b1b0706020d0c02150c04170c0d0308070e031603060c210204050414040c03080d0b09091006241407 68
    0x24805008201d4000c50100c03c0c2c908000140e120400d1006032443d0400c110b415901c1174004000d400c000490740300c040402401d04a081210010701030040c0d91100c0042c00009203401c5801c01802801c1c41441e800c078031040002d20501e49540d4504000690052550030f036207240064008402c040c00040300c1c1c2d85540800210343d103c0e5440c55083c01091040000b0303005101c5d805894854800350400503002d02c0e55095101e0510b0329141d84e60700b04007554051007409008081c03480203d41c68840d0043c1035140700303840d81420380c81c2c41000205030030003500030720388a544151500803034a441503251406030b9410030740209003400070100c150354103400050400c4450001b012410082c41ca250301400a85104840902c400720702d0301c01407483c80f4015100a806448180e9003000024441001807000d4400c80c1c0380800e48200403000a0900e201c220740d502c50a0300003106030204c080040c80340c0c44c0038100c122070030030382035021032881c440041e2554410402d015907010710845402c1c23042c2c20b0b9103006a0010100f0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 748492544 1250 748491294 748491299
    0x106050a173414090a0504290d030c0206070c050a06020703050706110d0c2d02130e03270d03120b06040605161e1a160c0209060109050307 61
    0x262010804034008824411010303000c003044188034007000ca003403030260f840e840c8030b4506021240b00c41d842000c99550144c88810001401c0d140ca00501240703c00c0b4a42d001c840e05426102d00c824075100c80030242c0310311050005a00000d4210000c08069901a2085d176200c180600e820302c17204c404c3e038101d5507001c407030f2000c0051920b0b40050684107607071086060300c1480c7d0391210f0640e02c15218412005058020300d50452503036100d2103804a1482c011190b6a5440d00098100042d0400030000f02c441104400804e074290b09050100081c407941587d1308201c1078108203602c90702d9028a0030904000d103001440711010049403850904240c0f0300500118480c5400d1801602040340707180010350701030400303e140300c85180110035a4216103140d2910b80c50b00c0d80e24951042d0f01b82040000303c03081d4042c2440c1c10070400400c1d041a41141c4a400b4015885525400c0d41d044468001e000710100e0840710114283c0d550700240544195a042c0c92850f640c2d1207600061303444240640004e6014822076000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 748493794 1250 748492544 748492561
    0x40612050708190c0302131b11070503070803031801020c1506040b0907050a0521090705031002160b07030e010f050a140103021f140f03060f0d05060106050a17 70
    0x1000304807540c2c0b008903030040d540d8030012010820b003144060f00a943c030380020030141c140300302e6150760300085e05e40004d51030004c1001c2e28168600082103200092425914030042401044404041d2804900621540d03262210b034075501d200040180c1c00224042d03ca150111409405540030003140000303580702c4242c0c4102403104540101c0c1d050f4880c0d424918502000c2c24012102da000750342a50f506443c04c4000c42c0c09440e03941c01040c0582c16000c10b50104468800c091609a0103542008040c0041c035207014105071034440604001403007140f0402600910004802070307041a56800760821541e503483c41001d90003802e0b00c0010148070b5007490300c18400c1e0417040e4421071081001e89010000604d8801034103961034001d0000a4208000314240c0c10000b141c030890104001241c6000344040000b002c0d002200d0300100300c00a42c000010091141d80c1c80c0001d00114000c7c01a07a0110504040c0d485040d5a0700c4188214404d01c08000b645507070040c41131010380c81019010110314001e0805110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 748495044 1250 748493794 748493803
    0x3011b03020f270901050d0317070e0901030b060301140c04060c060f090b0105030613110d060b0d0507030b131e06020f07150f1b2106031101030506060405010f05070204061205 77
    0x10121311440d0310340000b241354603000c440081c0003034040d55054540007000294240d1804050041300901c00720080f0700352603648100c842c3e40078501c40d5000c0c204d1402c160043c1400e68030071142c040c2d440b1651104014075028000d00340d80807a012803a1226141a090a1001c01000c00c00c840320403a5040c861410280001c1080d028122081902210150354442e503107100700c0802d50300020710300c003c1500303500e405140080703203104100d00680c40002c219401c01e0000d2800141054101c8940d00030304010020f100312003000710341c44030b244803da80346886656515903142c00c5003105d10a80c440d605600700700788401507040d42c60713082d0103803c40b070350794100c0707041c90b00c5100c10303409608101c42c0c103100c140402010340e409003541017a0140e00c20b041c001000001980c00d02c1903c202041080f00c2501140c040c0ca003580140341c000c6001e002ea0b91055144a00010140c480081c00b0358055407081100b041545da00c040c118600801602c0c00700c0d01e0b03805510000c3c000d070015501000036402c10364003000c1070100104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 748496294 1250 748495044 748495117
    0x28120804020f0f0a121a1f0501020a1109071101110d06080c0609060a020c0411070615050306180708030f1207090b0301050607030201090f12020c03011b03020f 70
    0x364a400301c02000000c00c1002c441401d180c40e000035a1400c10030070285064803d0500e140700d034018001240c6c0003481d052407000300310b03600d0003028515411400c205a11800c0d07031028010030310140c603040800740c40300f0141c454040b907664007420603600091912031044c00c41c240008101c0c0000e1000482c41d01d003614070760b0018400c8990140c908400041c90420008643d0301e189405803515092055210420929400080b980c800390b00407500c40040d02d13540c1d442100070861400c6243c40d1a045613052010441e0800310343c030b000e8001a02020300c0030b0f03a4002041640084010380000e211b064034007026092840c0703940403980c41c2c44041030222441c03035a28054190400c05021b95103059032660000c507020400e0348199400008200014000c07401c040000344850b074064000440c08500c183e40c0c514849240c0c48066a1125038440b290995940c10b002d22106090120000c0c030080855a10009000305101041d509040d0300048000e024103c00c0c0030340c7e9080702242c000010008420502d49071a18840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 748497544 1250 748496294 748496299
    0x30c010e0106050a03060b030a1b090605030d140a1106101409010b092418031b0612090715090e1b07020f040609060303030b040507020d022812080402 66
    0xc000c085440340c052103400100c460061892040c40d01e1512000018141c4802441c0c06020b0007107401c1c04600204103611000f0703c405821410701d1701d0440250106e609581005110b500006140c1c049164480c504425903041c800806a031032203800400c0e5202040c4c07500070010341c003039241013120048080c1d81003000c0b9580050750b2405104544200445a0424020440309140a004491090901c82040c00701c11a01e6189148480d00f07074248254aa004550030030501030052680381c01d10706060101ca4207001c00c41c441840e88a100ca4005019400b401446a01c15032051001407988903041001c1c80c002c15051605000b22408400024001c8829001d1052005110000304204c400d4141207843c1070860000014184040c1e5820410010b01c0b001415500a4540101055103401c0c0d11a05006620036100060744c1038080d130911040e43c00040c1140e041d07400041c4c90060081e00840c400e05444440d800f03190480c494100240c50740300703c001e400b41c180d401c0d01414190994001000300e0246008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 748498794 1250 748497544 748497551
    0x10f09020a0f050a150318150b03011104090228080106031107120e21010b010212040510140d060905060108060306040c1221030203040308010b0a0f08090c030a05030c01 74
    0x70340744082c0184410b032050b5508400818400c0051030000064501c5100c001c0c9404a902e462051550350452844401610f4840040e2800f480800151041c11031044c001d4000340f01042042c0700103100d60045200d100f040702e8000803808034920041034059040c071041c5c013000e20f110591000042c0081c20034000d01c0c007c640342952100d004c400c54001d40e44030f9540039650080803860312000720303440011110b110317401940c0170341801c0b10011000d91007082045150b0000401040b01c80009190980340304200303c2d000c50821042c842c1e0f840d185019441c00e001420011030425440da40010b00d4030a00c280914900c0c5811004201700c1c800360080350240d2000d0ba1120380e140c80380420192030300c906640c0204145035403002046111515024462154007910744010680251440c009021800052650000754008108804c2640040c04035001d001c2441d000c3d4101149a07201a1080c99030542050a011b094400038800c2c80041003c0c2000d60000382c195143d1202c28900b03130340c3d04e4124a0000c00f29508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 748500044 1250 748498794 748498799
    0xf0d060605030a5a15020316050f0904020a0909090b010f050907020a020f15030c04060809070b0d200a17070203121503030705060c0a03110c1b12010f09020a 69
    0x10840c81442030400302044c98140350050031003040c2209101c0030302041d0085040c002070102d240302150181112400401580e640f501c081800e42210221070b072407081c8002400090001c03e88102035404015085d940103a031080300480646120714030358000310f030440c203003407801d41009407a00400b412215000b900b100b45503212010054820001c58002c0c005900010042d405498000c2002800350006400e1018070113143d8500411036104940b180000d20340010100300640e03200004030307841801301014000c5103052030321140c0d4501c1040d84041c06203442d4001c0811500d00900802001040c0f504000d694142d0424042e05041c141e071081d002d08040540000c41d42d9001004407280511020300742c2e4031550350699103d0180c14118041398152000340090070024a0400966000c1c810b011503540d107410703540c3c50040a48130505c03143c45881ca024061300080e0640001d1a04808903075604110001e00600301181c800260355110404541c2030607001c41220105501c2200c000b4002d40f1002c04880c4c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 748501294 1250 748500044 748500113
    0x5010e0403083c160203070210050f09060424091202011b0606030308100603060b040b030a090206040f0f12050705010f090f0f06020d0305060f0d060605030a 69
    0x10021200a00031600400c00280e40000c540c40c04900400e40116003243d41c400c40c0c0c1c4581e030000c4609500034040307180e04240140c101c1c8030590680c04c140c0504c020b41c54114982e005c65031000300b030200710382446400300d500c0381e400d0540d0381174554000016042545a9548445080702450380e800f140b00c00300c55452003c62050700c9112800f00307482c043d0000011066290303004594203410034866940950040c503946000640034054440214000d07038503a029418941e0b02511915660350007181410300d403c03403c1000381061ba0640d002c60308995001920396640d0180000070304201100250700900010b001b00e221a80100d1040540301e442c071a0040203500e900e06015050805840a4481d0703220320400c100d070750320a0403414040d840620304ac0c0001507660700d401001c030980e50081c0c3c50822928009006031541046504070a4640c0d1406020500341503000c030781031944507151640110400450ba0741031104a0304081c5c014074000e012a44101c44a0900d04445007035210366155801c080d03080d050828 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 748502544 1250 748501294 748501319
    0x50d290606091516050307020a080c0d030809030c0609010c12020f09040203041b06030507030c230a031104080706110a05060c030618090f061e040204050424020d0501 73
    0x48a001d0895803428000e8810072100c00390b02c0300000040030301000410f5224002c2e80c1810200c600ca8002191110010b1040198078045908088081d80c80141c600034140e0303a0021940080360941000d83c110b0f01d409900a046205031880f284035403040c001030104483d0150300100d5190915130b1802e104011911518060740300d4a0602e105440c0d0a0000082d140340c258000d41d00280305030b940c5450001c008242c42c17050305030355105601080e80c9070100041c080d098040c05103e14080e01d0840c00030148580056130310301030303000900300c050004a401d031907150203540400e510421501503141c0b03a55503400a075580316124090140011800f04820004003000601c1a50b100c1d4040043c1c035080c0d644151283c680c0d00300403d02c0340d0001455643d01c00f8111150bc0322400cd0440402a0018404034846c5034a000000381196030121940902c41c0c1c0540030304d00400d50015412503000c101500c0710304120729244e10203c041c0751000d100907060441280198014110101c0d41e4009002903a03881441c00b140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 748503794 1250 748502544 748502551
    0x6050409050c1009050a1806031e05060c160b19022206111515041407080c09010c06020705071d0412031e024b0702011e09050d29 57
    0x100d100300100b4001b60789000130900203140781a9002420598a0720b03003242b202c218098609000200e1008141071001c1401459806488403149a20700b044081c0000101c1c101c5150140c036552081010400525451803940410b880074013065480306111103502c552801d402412107907805524100142040c0294602081044080302401c10201ca1400040ca04400100312a0003500901180309403035680748954108104040140c2e590f5142c010780242c0000c04c090030203800c6074000e004aa00301d03a4000c40030302e0b40d2a4820005038907000340340703031941c40c01510350800358901035030441c20004000d44040703847c459400341400882081c03800f4826400c45110b00c592503421100c2c1d40215460b40202e0b0006d10420070701d12512146100d207800c10300e1904002ca000c8000b52080314100d00f421a0200b110040780103521902c4500c2d151075540060b101403500c3c28900080a00100c851404030300503004940200740103001980ba41c0d80900d09407806030802c15003080c48103a101c0349000d2901c400d010f038a20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 748505044 1250 748503794 748503799
    0x915031009120f0c0c06080105010201050a062904031202150a0e0705060c0a14011d01151a040e090d080702060730110414010507080403060f06050409050c100905 71
    0x700c848242e0411120702d10b202402006000c4020719580000d000300d001c0074000e00441c1c0d40c503501541090b000900351103000e00100c9420381480d205200c1e1008480c1c2c00f000c20030507402070f61741302544110342c03250078007407070744041c00341d6181c1d0141c005100d80203c3c52000c8200461240f040310703030302d20410b04210b44d10b00d0b54003c101e030b004842c18095030038400700414003030081e1000c80d14000800d554080303e20001e0b502030121360f519424079245601402e01c0c05150159048024841080c00c2d201c0398401c02414480c0c0020b0302d00c5244030200c99204042100c014041500622045260440030580d45040692056000509001c0054146880499814040c00c00b0b5512101014400050209a481c000c12012800380c45000310054103603051282441d60a400d03181ca076200c0d0300d05480d541940c0842d802081c10310a0406c402e00009281c0c1085500f980d0b4002d400050030a40c13441c000000301200e40100fa005480c00c601c907401d006002030307650003590044a01c1d800d1061006c0741201c5444840c0f10350703034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 748506294 1250 748505044 748505063
    0xa0c120231030b0a0b2107060801090905060f18060106020d1707120c02031603080117060c0403150605060406050c1b0102031c1107030f0306080714010c110915031009 73
    0x2c40b814080d81202415004c01801000c04002180303e82c4c0c81251b03000503200090b4050f100400402d40c0043c074090050549034001c00c4100500d8a40d541c5885008108078000c80b00000002c1c91030020b501182c000ca14007404944440d0703144c900103991040d542c0f80d4040420740006031900c000e00910101c3e40702d4030950740c03003071039880081c80603501814203101004c0c1940030900c840d070b604421041c03403180d0713840c00f99480c0009945041d10301d000d00c41c441840030b2200d0f0400d4041140044c03e4900f200c0403258817503031990708510030001f058011b2520303801c45e65210100081c0061300341d50010240886031110402c0d03402140c0601c3c1d26010380d0002c0182c0f5409078106100700c0349034840c0e4107080e106450b013030800443c0500c0c811454088543c442d800417008141220342800c01c0582c507100da04041c0120000a00c1070760300b03024942583c81090240d00e410031140901d80410071188000e030300303140c1c4070140550a05003440c244a41d2505051940740e070103440347c586549608003040c0160069a500a00070ba03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 748507544 1250 748506294 748506301
    0x9020a050a0804060e010c0f08100f03080d0e070b0d0b0a060e060d020702181905011d0408130305072306030c0a02071715010602150a0c120231030b 65
    0x140e0ba400c800400c01d60706103a94034945240c102e13080c003c0300103607681c694680407503c00c0300c03c3c041c0a00001421844c001d842c035a000340030703c083c2c07281440d00762604410356503100c600514010b0f0140c00020306400c1d050040044c00a4400840b4020300105000f40030148600030000080c450081e20354413a035000101441c0240750303d41003440c01030880da030111501502e00502c680110300f418280798410519946000200544034080340e1940041e07046a883c248019450035114040e682001002c008180c520000824108031101003120380d15860030580314203181d9242032450f1510400d1060f42e0034060701d048a800344a074000318110f129440144a0740c19911031218000c050b40281030100151b00c1a2100450101c8101c0d6007410321410003402484040c61010030450b9500040e4004802c0d0762158000c080f48484181c1c00c15400b40445a000400d0a106d543c1184c020b20a071114200d030910010300d00041d0181a0582c0c0039201c044800c41448441d800340000303001d80c0030702c800f92040c21240d010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 748508794 1250 748507544 748507547
    0xa0b070c030e011b06061211030d0e010f0c2405071103040b13050a030605150402030105090a09061d0703140f12130b0f13080c0307120507030f08031009020a050a 71
    0x10980c014015000444210b51540e8680044031400c2c0c20a40c10010700c0d0f90300004002c034107901141034003c02d80281140e0300c50050040e0bd0f070048001014140036504141c1411944103c440c007003482c0e0446124490241c881c0300d002184031038840030214042c184070005110300e00070300d401a59000240d004600c0c1925054014049402030240e41381c040a06003c0051aa6220b10518000c2d60103598001039505149150800240c5c200400c035002c1c5005000411042d514480d4540e44000d510501046054103441e1640c010102c40100c00500403400b0180c644072400003618a0030b50342f08017049000602110003c503650110b2a8144900758414440d0301a0201c4c030b54058401c06041d144008281d680751400220309800800c201050110701246c0e494985120b00c2d1030000400130107010b812800c0f004000b04ea22440035028802801c064030f086001080810000d6000940c3c10070328a0740401007a02c1d00b040180d10136116100d651b44500b102045400d003d100315400e00c00f440d2641c525107664481c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 748510044 1250 748508794 748508807
    0x412030b01230d0906050106050d18031205100e070c0b1312050705010216060c020c0f0604210203060f041703060102101107152003060f0f210a0b070c030e01 69
    0x5104003e030302d03660380310001802405100c0c06841c0a448a540355103c3c1c0344c041040360420250503a8901d40800f007800840d400003a44ca200c0c10030344401007102c1d540c1c03807048440354030594050180019a14108812190b012820300707940d91040194400c40c0d2200701c0040f01060340000060810540074084030310640c000c0b002896910301c110005410849000ea182d1f2000f000b5000585280c6c0e1600d4034680c0303156042c440d100d001e010440c1e00701c50058401020030140d0089004030415500040b445d11404038480042006140d402001c440c200d00e89129105000c1c042580c040350b41c584003401c9000c005c004502642d101d9003069000f8061035010044543c00b40595440c0b002d5145010401500442c10a0f0300b004412440da14010503140400c5008440c1040400d40401181c001032040c00095a1080e000c0c9480300011194214440e4104000940503204030501900740401d80d10341c030106034804035400301c0c0f150086406c81900d9031421400c1c3c600282d803610050010314400080c0d0240e40c020030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 748511294 1250 748510044 748510057
    0xc17010e06060f0a08070b130603050f0420090406140115050304121b031713051b04020f03090616030b09130804050307060e0a06090303140702010302070602030412030b0123 76
    0x18090008503546130703461750038170003550440c21a41c600002c01c1c0f8070b4007401071501d0b001003c0b140b400300403601d49101e00d100340e41c00c00390004100007140c03240101c40302c04000e0110401d50009211559a0030b00c1d18142000f001c1052106031b01c00032081c0001203e690000d20210b10b040303241c80d407518641e00e036501d5005081518451005001c2c070b1000c84c0712804005d208403000c3d00d100c1e0301c50f400042c448200300303900e001e00104840040b001017003a08001078000300e4072200403003615030400d41540b1800001801703802441d11000049402008000c1342d00c4001503028054001d140e01c40382102c02003842203007991001c40c1055040074514000c01d0a02a170048045d00c1d85014050041c02c00f51100000b906005069001c01d00041308419902d5261611030441001411b0f541000c0075a24559a8003902d005111100d0000564011810006590080c0c044402055000350f0455a0b49090b290040d000a20826480002031401440d040c1079405420385c4003503074191381808040180c5c40c00a4071604e13400320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 748512544 1250 748511294 748511299
    0x304031b090507030b041506140f0d0905100f02040f050f041e0609180308010b0a0242010b0d02091f11240114011b0c17010e06060f 58
    0x1100001106402440b03490300030074807030b0350124491100d0320030003081d00c0c1c800303900540440e9103120400c0050382100010f40741000c1400c47c00e8603181c900c801600d65004400003040d0715814a2442c1b020401c01240e40d440307a03404d9800030020f0720340b605030900c101e01a5020386119000320300341c1400300d840c2103200300c0d03a0100c0c000c0001c500421384003e10603c10030b0965a0036062519407009105910346400340d00713000c101042c00401c0342030198500400014040c800d11242060002d414100c45100380a22010130030b2000320345011410800904200d0155a030303e001980404000505110200d6040340b4101d40c0069001030500011000e044000d50190141590202001e01c001e0303001d2003031100e02030110350079844540682c00b06a4681d810001420981d002202c2d865040045c070000c43c642c010b054547c0c01e100303007950040140058654003956203411050751a0000381100700009100d0040943d150b460904c5006070310701c011075003a940035445000315a0444800119282000c2e02840b0307490000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 748513794 1250 748512544 748512593
    0x30810061b060e030705070e060a050d0b2e0b0d0507021b042c07030303110f031605070b040c0503010b01050c1b010c080a0914100f0c03091a0405041b02030403 70
    0x85da03441501e00403166101c12924100f031740400146190900041c0002c0109071541c580d44251681d504c202403000600c100c1d20f034110000f080119502c1c200d05080c1c029401e52080d11400d071643c03594081500100090555203052000203405144007051041122071030a2491241d0303800d070010040600b11a440c0b1500741d03141d01060040c0c0c11900d0072101c88407203440c80034012041c1141001401e0720100c0b00c8462615904000c03100c2140717040012290702c86030842d4455241803200d90201c640e4030440c1c4003d88605080c0e1300341b205101440c4040f10403190128000c001030b9040c4801540c2d00d000d00040a00590000e0140d845001290440119903130303014540322000c0e4105903204201c0390011044840018500c2c40184940e0464000d5110318201c12074084110700d50544c40105413030380f80c1c1d5400040101014038441054000c0c00741c080a80840e140051151090503085580364106104480c4102c1c103101e51031650780d941407074a440304410f40d8040d40c506402c680f40d04003803010340e80345584000305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 748515044 1250 748513794 748513807
    0x2030c010207030e09060f0a090e21031f0515180d08040f06080402060f07020d060c02010903021207110d030c0506040b04061b090521010603030810061b060e03 70
    0x2400c0c8010244180300b926920342d02160320f030902c510203100420441c01a240190741c01c6075541c581009000301c0d00030100220340380030708100c0c403810031000c1510b94404c40702a2100c1c254800214014502c1103a80030030300380751190301d080002914030061250b1078010300104400c036058107281b03000703100441310440926034031405900424007515480c0b5040c0e03403c010108040c0103004d81d203901d98008220b245400c414505003900001c0d614490ba00380305126110002d2201c045440380103041200a411074010003c07000c2c40714001e806806032440880050054400c04507003c034000d410750311440d811011003000b2070700d28024000b000d60f90205c00d50a000c290708010300080c40401000744039520601d00c002c1c0317504080c680641911109540d00d4211481c035020042d0b013580c02107101c000c0b103000f01c404025401c2e07903182d88500b0840d4820048110350a0000110606410021890150b19404990880741d03070798907003c0316018421a03a1000b0514000b11000210b885030f0086540d0480c0007080c1d0b4980034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 748516294 1250 748515044 748515067
    0x12020d1e020106050a0905071404031e0302010f060b0c0f060412030b03150901020a0e0f13021602040906020301050306061c0b1e07090303020c0f1804060908041403070501030606020d030c0203 84
    0xd54800006c054594041260380e41c2c1c406082000d64422007121804c050a48d940c4902e03c0340301c000c1c10015102c00c1007924003814401d4102d040100d800c5481000b4058a490100e0368541c4a120b00c030002d44100c0500a015000000c1c1c89889250001001034000c130a104048018180c2d01603200d07410305c180d03180320b00e02c803850042c8076010b500c0d0280016902d1412007005040c05449048061040049a600c0d95043e00c0c0c00350b0ba05880030004000507a5503200300d201e0460002840c070040c2d00145007201102c2040006e50095050702c1c4200d00f160980d07039885040262920064030a0b013100801000d03450001809920f0b071980003c4620b4803030790048201044454030791402c482d00e00001d4484c040070402c1c0f5405208920b0000003e80d27180c860100d4071004112589404000c00c91103c5403000082e05002c180d83c4800a0036501442c0302d66101d50314049401511490700eaa6842402500c100241b030f5030180c403a01048400907006040003030340146050b001400050100015804104506480013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 748517544 1250 748516294 748516309
    0x90902030a140c120601050304020d032a0f1502040f1a09060c1605040e03180a0504050702030d1505150c01061a040812030c030123060d0912020d1e02010605 69
    0x5222020005495240040802288807006006070341402010030030720000da214480740c2b22f001c64047c10000000d100c0c2040701d40d01d200918524600c801140102c0c0d10030040010007600301c49024000c804286c2281500700030491041b0b00c100d046007000103004001d200c206000401c0c601e4036001150f8141031184001c590307070744e00501120303030290061541c0460704000c01600d40064101950200f11440144c2d082075600d04c0781c94031118030100034485d03020740c0307503614682100648005030082c00301c5e007010107000c0d6503604000040f0900e01e040c410641c0050b01080c50020442e90000d20528951408242d20f102550000002d0606552103d030041101c68100f140007880d40d038141d6000390388a00d03047c0c0c69403c11041245d0b544109504000b070242000312481034905403504000800300c00035100340e41c4c00c05140d140035616081440030484003240310403540701601890181b200c400340a1b103a22812a142e501028403000400c60080980c80e583d880304000c15070610090000088441d200c0001070f504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 748518794 1250 748517544 748517551
    0x912120903251416061110060b03060a0909020a090f090c060509190503060705030907170d09120309060806030106180e01240515120907150c03090902030a14 69
    0x50032074854180b8100301070a6100c060410090000e405071400c00c00c001c0802d41c0d0a845803034104800380c414414a00c9083c401c018010000b08010030500d503481e00744280c1500122200c500c1a0200440040e2460703d034000c90b01020340c0100032110072400c0802640081240c110004480b41e928070040c0300040103407240801400050f2540c0352501410000c00015401c4005601c0d504500100c04000c140c40020310306411a40c5810b03c00c2d01c9655405844e464100903030b000e004020548800c1c50807400010030300c601503403100d0b40c5142465445200c0600e110340c1c250001030018506050812000e41308076801c41d0413810060010178280c0d80c0c9c044000441007a9400142195030311280c2d00b02c2d8100910481030040030344030002074081c1e51141c5200141d003141c8255402a603415807213520108000003203a1803412040c41210440c10540c01302940c40902d40500440341c0e483c0e4110341e122a0203481c48070344503a03041d0781e5203009034103001c13060010f0b403c007800d04a81c5944641f07180c1840003a5802d9a0310 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 748520044 1250 748518794 748518847
    0x6120507090b06070c03020405070c050307110f060c0c010c02040e1f05180a0321050405150906060607260417060708070e0f0a030b010b0408060912120903 68
    0xc2038200310100d0212a1071800982c4110002c11000f8000342220745030104503501120005059515464103030b03180c24144100030035074000001c40b5410440c1c0c01c81900c1d1054800d841c0084442c40c2901031110340c1c4910700c031910f01c40d80240401d001c10340c81a034060307065074070207040401d045085540044ca08881d40101046095200d00f11010500d814800c459100d80007003404400c4c240700c00240c546407003d440d4050b080243c509849551743d109112244011960b1003000c010515140c1001a22003a18407041a03d00c5001d00100e050840300080c071500841c0001c208a00e4500340d40c0d110501d002d250700864503442d91031280c040d0800859406440208900742c071140c030101804188508100005100d24141b161450620005030b60002030a0001d020948403030030580f25610000707030040540d92009014101e06400480c0081c0000060422694480d00322182503d49240580e22031181e940010140c107030030710101d804030b40160342007130b0010310700003e036441d0a04842d00c41e1701c900d007103000c900b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 748521294 1250 748520044 748520053
    0xb040f142a01050901080c090d0b07020d2a030309210908060708060409111005190c0506041b0918330515040912021c0c030f03061205 59
    0x2030003210140081040701420710202a036071188440064841d0003130411860400c08440002444401d080044805804000300070039040001c2e85003580038200101c800380c0c014044e10601c1c84089001700d00740000d4651000320410b408400011007520082031103015810540c413100190007142103d03107483d000248042e5009081852018044c040a000383d10245e2140c0c4400f00f0000381603031110301036400c0541290301140e00f1010341031006c41c942c8007411440d03200305840c121285070b9400100510416130b12100c0070f00c00e10305030801a1001c401e1540c02506540050300010002522003489804050040c0c0304500096294004d142c100d6104c40c450300c224094124290081c4071607241407417151102800d141080c030380c050710a10380d4041c2008410300450b4698001c14862080b40b14105120513004d4030070031540019040012511906000800c0580106900c45c2903107001851700704854030040d15000040320303080d83c1c201c8a9071200220311007050b54404010400840c0c1d071071f070400320394050360040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 748522544 1250 748521294 748521313
    0x603110108090307030206150402071a19020906030408030c0c06040807050601090c1b05030405101e030603080307230a0203190206090a02060309070302090c070b010501020c0d0b040f14 81
    0x5040080080c09040e01d43d802444800c0000e680017031150b0340000165402c034404c148000c0403401a008102d8028044045086030101c40c82080070080c0c0304030450010a14154020050142240318601415810060400000e408104079400541c2c000324694801c5240040001695003090010340b001c07201010005412810300c4000c101c210302405410500700f14581c1c0445000d441140a103120340103003241c1070f4140c4103004084c001d0310010100900f4500d00764007104401480b40311816402d070040c0a007106a20b0740c01c4d200788280000d69a0101816203152540c14080c0d5140d00581b82c0e80c020003030b0b2040800c620300300720b0002d011120041d4000f1500c4140441030f10460820710001941150b011608202400d94000341000645406070b50b59644d81c1c41e010443c0f41840603981003e504052400e092100842d42e0100410302140102c5a80c00301c1e90701c0f07800490326035280100d1a940482c410186030b0218940e080140c2c0c20512540d1109030210260ba2014170040c09450b48017038503080718008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 748523794 1250 748522544 748522547
    0x612180c06040f150c120905130b03060103031101020d0c05030a0b1207180608030406090f0b07170307020a0609060510080c0a03060b010c05010f05010911070b0a0b01050d06031101 79
    0x100650110129405401c0c942018444081003456210b24090301400c1c4c150440001d0080358042c1085030000304601c0004001e00001d81017441e14860b850007112000783c480c0c818001449400d0000030014041d00c141c3c1d01c1d54900311f4900c4080440d44415541c00c000c1e40e00704c4800c2e0320684983d00d01c103844140d164900180410100d503c0d51107118010a09145800d401d40780c04518070090b030700c0c840b1402a07c8002072010400400312504009294400010082502074110511074102c618210508600c95200e0301c0210450146007801000200e0b2103822015100703040d005503038466154030407944400c1068448030b05a5451080666100380d81d0424801600d203045180405401d42500400750780e19250301103044000d0511001e401c0e82c0ea140d080c1d6503160b100b40d04440d007558010000b441a201c1c480e04100003000b080c424110f0f035500e0f2001e520340000c00c006c1502c48075500090741040550343c01041b00040c0c9025205c0f20704214080001c1703401f040081c4034020113140038590220008805000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 748525044 1250 748523794 748523803
    0x6090b0a0513080f04030b0c2d0d0f0f020a0e04050703091e050a08131e06120f1509050108060903031003031b021206090c1914061218 59
    0x20030003906040408202240310034842c503481560f0f11010169442c10491340c00122030045ea000100050b90100c00e20503c02c2020018001070845581c0310f00f034441d2540242000303603807940d4000f11040014469a0018039030341d0320075420300300300c64000304181040c505441c0c100d0b070080c18136002240d80d1146100c1c0a08192003010350144547c20108902d103402d88414482e50143c030165070031021841000400c02000340f01401d6410740c482d460a440348514001c2d5a8000d0150041c1c191700540304505030802c031911400c4100f03c9802e51200e80918860000f03c40c060014602c0801d100c0e9101c414446188000c007001000824584c0f400007460b505001d0164100309018040c407406030710074418010400e1351024410103c82e4542412852641c0c000000c652684803980b020b5806001e90b048510740f5000480e0740c601c01d43d007400c191545412210104a0b515880001418038402c6d0501c00f4000b6081d084401e12040c54020070305ca0a0249450b003814420600300c80c030000380b40045140c42200d900410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 748526294 1250 748525044 748525051
    0x609170c070e07051602060c01090b090609160b07061d0a02030624371e0602100b15040f0e010e010b07110409020d060c09170706082206090b 62
    0x41001655060030f50300200070340217a060140b00c11800c02e405070f04668401045403800d500b040300038030000349181004084042d0490f074803100340c01610700152824001140b0590031400740060304143c00e0619458000b150030400048905646c1c808449a401c0d0088946004500380540184000102c0b841450b0904802421840c46801606482d42e6070b10030010714554401c4c020f8660808920742c0b000c0b207c0c600740c51000003600b004010002d1901c260b43d0b03d00300005888a030391400280c0304960f1078583d5121160303c0761f040182c0250707150504500281d0411000d08034003c1c01580220105a011606540140c0c0412242460b00c102003154500940ca114014005201540e410390b15141c000b40b801e100b90317503004244242c000c1c403c940c03a035110780c0000304254000d001d01c4500301c11854510300400d05008000b0108000340400103070203040d49400e1044145d0b0b4806412030902d04101518550400340a0740310b120700005012007000f542803501212503024030004100e000042c28502990000038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 748527544 1250 748526294 748526309
    0x9190b06031510151b0305040e060603070818011e0e01050f090d0c02130513020913050304090b0303090d03030b150405031b040209040c020703140312010b070609170c07 74
    0x60304002c0700032000560401151042e18659078012580f0034200e172180c0407050068010b072031104c860740030f040c0c0c0b041c0500301341c0e0a82040d1206944a660400091b13020850b01240021801800500c1a0b4890341c0c4c165102058030001081c080a104110360a01d40c0258048840303964602c1e150340030003c2401040c0d0041a410045021400c01c0701c021034881180d101604144003450f902d90003107403104020410407540d0490704100c03c2c284000b8511601004d95020791250703051380007060680084010350005241d01038002d600d031a1070301c905c44002c0c101c0303104400d40c9800140f09055407600c03404c00c5108907a200355000141001103800300b007000c6894a5030b1200310780003403109000c0c58800040004160480c0e81004800c4071461002501a1054035032851b005404c103400421b44540009948007038074414684490995003540f0407a6580c06500407105200015400402510031190006c00c140307030090b103020640301c1403500e4044182045d0410b62503090360000f40d030314107900117100040241070304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 748528794 1250 748527544 748527583
    0x8030a0e06090c13180318230333040c180e010c0201022502060d050f04050106080a02060a030e0124060e12120a17130b07020f120f04031703040c08060f0f09190b0603 73
    0x80905202c600401d0202500c590340d001d01107000d000c0d01218140003481ea00175000033784d81200380040042e0140303d0f20794801d5070070207070b81d10110ba0040c02903401506c100002c40c03c02181a0811176461200110283e8001074200001c0350009131a0040038807038009445030301454117140c90000e08658440d03200055940043c069100140d8514084850300c03002481e01241030b1a99550242c0105040070807400d20380400b41000c901c800303000c0c40007070444843d40c0b03c111321130840380103008040c00180d40d58243c540041c4d5440003907608042c00303001d80b03000e5440d066100b007000401e54440d00780f050340c120a82c1c12001015800700103440ca1280d41c4214548003030600d100b000c0794069600d0507012000340350790801203200c1d110004900103030f40007580c01020b4502c070030340ca01084851641c420b980a50f0b41d0490144049081100013444500035201510170002c2580d844507444030000300600800300a00032060080c034201d00b80f00c414451035010703120085160924204251400b42140048400030383d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 748530044 1250 748528794 748528843
    0x7080f250312020d0e15100801020304121b0b040804181404020405090c0d06060504060503030c0706140d0920030705010c08030a0e06090c131803182303 67
    0x81c000341800700d6918103180035848104c0500030b03a01501003000c0944075486000c11500c41107080b84581e90040c02c400000714031458890742c07824240e00c42120040c0071a18413003943d444052040c0341c1084080d441519462209003c0da6540e4024002038406403002940440c09101e804030802c2c0f40075622100e01d10402034403000700c0621090900040001e03200c3c50f030322000203004030760500442c1d01c4000c0040420103c41e8079860164010840c5009040c0107503d46140440d007401c0000c2200c1d02110390324002c1490500e42030048403100c01d20605c4d41c038102401c0c05007078074000b01e034011449214400c1500c450301c00c01051302e4042d00e00c071030110749210b40c1c040c1c04104103503604012005c0c10203402000c902d940b983c400e808040908408035191034240b03d02c4042291581c8017145000c0305400c21248140c4009580303040d6400c0e01c4d504520308552030415404500020300030801512a041c4a041b420a400da43d030b0441c6030030b104240030906404180308802e00a6180601c450f4000c032040f030154028003003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 748531294 1250 748530044 748530047
    0xa0204030201080a09080d1d060606161416030f031d0a030305070203120714060a0c090506070303151415210709080604031e09140607060207080f2503 66
    0x3d806800d90800c6030f55081640f05100340141143e440311040c010900141c103401c54040d00d004829481080c041c0030f154003196051500ca4100c5c1e810703d0728400803c004030601d88500d64000c14203144407590b0300c9800c40c142c4481d104400c465004500401d08040300c0c807800e04018003412903404400003551540088628281d54150085058a8040c40d007640c4520440c03011a00c1c019070991600104503010400d1010081c030024417410740b4103128107030381709901e92500300ca09548506151402140411201340401c0c1800740c05000c00758000e103808100203280714100f14503098035820103103110700d14000110701801d040c2c99164a10030712a250034504240341400070544d0108048200001102e4004981e01e180300703e040300007801007041610b2003820301d41344c042d086180070811004815026a144d02c81030b401000814101c4001007050601074111604120065000800c102c441c00c2d424000e92020480e010007810003800001c01507a560b103822303d440740200a150b075000c0e4030100110001c00000703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 748532544 1250 748531294 748531307
    0x105182e0903081902010609020c0c15030601020a021e0901150e030a05060103020904030504080102030c04090c080402151c151e060c020f0a08010f24060509132406080a0204030201 79
    0x49138011045101140380403812405030100754841c480c072a0000c83e081d105240d0100f01c02e04408011074046c4810703070440403030740384601007165000d000d40c000c100d01d0000744c20801d40c0351040c007140c140489440d03c8080006041c03400b00ba0055540c1540194102c8155a003185511001c900700301d0040040c0d101c80c1d0380302d650300d00701400700074041d0415002040170913010b0700a85024120000096442c0d280c40d401d0720400b03820038464281c5541c1002c03d061000d6010f41005401660050140d0f203612005c48413011061f031040b001c10058401e0000802034550003886184060b26107010390032112850100084034261400700303010654402600200036803500715442e00516541940d090120207024030011707031401e0260344000320710750814910340c00001c0c4681c0030240000c084504900c404204000c0385800004a02500340410401c108024142c603103072001c403160242d45c0c00007103460560070100401242c01c80710ac506032882401014441141c000049942c00170744030000b1130400f89560002000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 748533794 1250 748532544 748532557
    0x9060f090435031009050f040209040215040303030905060106050a050307030902060d0c08040b0a0c0e0d1b06020303040b15090103080c070806070c0c12110105182e090308 75
    0x700300001c804098489805844000020305880d01c5000c0e000c2c59801001e103038401c40d4540c28030107580c14041006491403090034040e810802d1102d419969641c00d2041c1c00c1c00c080c001380d9003c1c0009400b2190780e01d07000c0041010f144a668041038404851401920300141078001505000d014000b03c0e90712544002901e40c4503c00d8034000c41d4500c1140041035840c403e00109045490600707400701c0042d41c102a03a01e025621415110070750369140036640d001c503103040d908000007030260000315445151541003115803d004011040700310084200d40300c40c0c1d40c00ca80c000b10140e0000700400041c090042001d40c3c0c07000f0341c1c03202c4604240d400030000c0c1c1c644405000041042002040c00007a50340100441000740003442d0403034105092050300038000c201844400c60740e11035042c40100b8074585081c01c0303003212a80700ca14801c4030303101080190b949801400c0c2411103810110309020140e81c6071076584000b0b032000c0403c1d490808101400e00340300b50801c244c132010f0040c3e40390708000080040d800c8408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 748535044 1250 748533794 748533803
    0x60e0102090405060f0d120504052e112104050d0303060503101b0c082a0c030f0604031b120f08010801140408030703020f0301032010090902030703060504051509060f0904 75
    0x8061003587d070550715806272350406504001c8032080700550030501000d0700c0104036501e02100f045884038400300c4410011121036100741e00f003a4600c00b4405500b06413490501c0e0041c00c85814151540082040c040681074241d0029861b98820421814180b02da0803030a100044284180800c82c194540013120252411003008035a00c00c110602078140d00f43c0f40c0c40c40b040702c005454540b800900085050a10401c02c078580203008003041d29150000e114041d07840e80202404003640e035074030190344030180d000c070880210280044060008070316140003c1411001d40f6030348a2182c1a88000b017500720143c00800c40c4e68034150119400c03210740d030344869020764040d04042e41c036030b100d20046029001e07010040785e400c9400b000120800400389003581e624401812064008107030303d41002480d040360a210300214100450038004840035400a50744050241000310300f03507079201e0115080315002ca448840784940304040e501e07946424000a90009421030b071440b400000c0070005991420007030030040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 748536294 1250 748535044 748535063
    0xc05090f15010807030e0f1c03200c010605060a05040e100305060411120a03021e010b010507060b0d231203011a16051905070509070c0609020d060e0102090405060f0d 73
    0x14413003403190700b0050a03200c0c81001d403501081110301c01c5581e0500d003025a071240100000350b00075a03110b445146c083c0c100039a85400701d41c8540d1248529540100c0c2e10700d46c02d540701c180200c2e551308d8401c010080d85100d5500c03565039500d405042d0010203006841ca0142240d17080702007001c0b500c00520f003504183c000000d800105082c00000f1000c5041e815404154000c180002060503004600c0c0365901c4000d0007200000c0303039a200c00310300b21a8000051804540184010804941c0b00da0101543c0c0c42d010304400c40006041e00c2c3c0802c1c81c0811202e01c0c0c2c41440c1d00c2d559070340c01002449180010340018842c2800c5504240d480c04d4060000d02042901e248081142c080580300c2619120304550003030706441c00000001318907004030001c0442580c840c0b10b00c02000800c2e0030424562271103680e25980c1c880042900c4d54171032020f08405181641d1009250380d075417011511a01c102c44100030402c1c00182d440a0364814001650002010b65106085010f04018151900c05070074041e96803068194 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 748537544 1250 748536294 748536301
    0x3040b07230a20070602070503150601021c0c060501090c0e090c040b07110a0801020304030f3b091611060118020c0717070302150a0f050a03090f0c05090f150108 71
    0xd4a5888403e094039800d1003940fa00040700d50700403400d80184c55095041d10b0540703043d030300a005070314005e640150040e44503008a0048501e20001020a6a00391802e40348441359500c450701a03510a800c6129155510040c0280042d0070085c030845520095601000310710384825814400d001c0c610660b1072049001488904010311425400c0b54000c0c010302108216850b801054003c0d04101c03412004260901088040d071070080342a4114000c01140d4982c500794681403d103015001e03042c0707811100801480140050b44c5501c842d600c21850440c503c4240c140c1c0b040e0041040d4915012070420f40c0003070740180010003601e806c00300c41d50b11900004d40d031800703503010040c0341c02c0d150317440324041c0700e4022503405020001080b84401c8038002c541204800c4400c0501001c1403103030705540b901044035004d10103070460103440940705c40340107420009004003260b21620351071400c4440850b0b01c1c05e0f154500340401e14002900c16001515540000326501e400e1a820700f121600d034014074140318580001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 748538794 1250 748537544 748537577
    0xf0f06120303040506060108100f1e0e07020a03090b2d160b1f0e06120f2b2102130513090c0803030601051b0703020603040b07230a 58
    0x2159114210501102e5030307460b1038107166488500c107071002400201d2901c04507d266000840c0001911502030040421a1801030603d001c0e10642403182100f40e0b440a001949201c111541032180045e82c0107846015800e10700140201400d810005c1140e906001030107500b0f8481c0d171201c118421041c0d1885402ca40450f1024580c05942070345a18800b0403c040c60800460b6200540582d690580300054461040070f410300904e9a4000c2040d0140490009041e80c604520500c0703100c9800c4055a886004412202d804d16032200d1404000e6400095214044122100401d03818125031601010044c4500702c0307120b04030142d8038907490498004c80c841048480c1010b242c030041800400030900d82e00c02c2c0b801c04019055151003521007403403264000440280c00b204030b0388144c4d0141d44140c902040710580b02002202510100c14a1059000100044c0c65100c002d42c01940500101c100f02d00d05440c00501c0c00c07070207070052101040c0f03800d0020501c001c6a41550000c1d415400c181c0c940e10609200d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748540044 1250 748538794 748538809
    0xe13020409020c1b01020a0b0c03190606030b030c10020304150207150e040510060503270d0e150702030709020306041b09051003060f05040c3e060f0f06 67
    0x404000c0901c005001d5441160008104081c20a10784c2c50383d02c006003613401640c944909000207060080d0280004064908420045038440e90300c4410310300010f0303d0300e201001c8032015081030010980d9148103840500d401c1006038000307601110a08140100740800030b440740900d21492245600541d000b0300c01034005e001d4035000d05018488101c448400000040c00700d125141894002da240401140941c81a034410100350b071040d4603001c3c6551101034200580c06680c00c00341303540000303083d01125244814802d40158035000d54510320001c41e010200300454942d58003840c81d04400b044003c00688010034650103d4502d88001038880e81c030440800c020300700306001c482040030082c0403403544c0c6421540d00400d592040d40e40c40c200240000003601210f00300c1c054000c232030394800c80800a5260a812001600005240c41100c41c24101d1a00316180c0d40f0030351100f0322507604418040c80340340200ca036a4144c4070140c020031260408003540109120042c21141c544520400080e4140d1209403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748541294 1250 748540044 748540049
    0x60b21100b03210a110c010c0201050d0204121506170d121e060e01050d0f120e0d05030405012309101e020102030105150901050409021806070f05010e0d0e130204 71
    0x703080f110126440a81e4903481125100041400704076008840b0a0000341e2480d0501d041e1200e0200c2c0314260010344441d0401200c40440607000c100214210f10955035500c003480c41007410b00075200181ca9848296038050300702c90207921081d00803503001d25000a01c1c070f140710014100b0b40255820090604090032054044004850014031100408800750f40305000701c0301d0107040d0002b140d89407401c0100d10100000b019013011945a6540c02080052500680a01050524421540c500400310304034007402c400c10386a1b50008034080006580010705600c9a1152020560748011000900e4a09000310741a15014079003905140400030f02400032a0034040c6c0d07a4007503509480924600078040d40c02400760502030b46031210480032848000040d100e510005844140c105403d200742c110082d000008400868a040b580c25407894407194010202c541c003a1140101101050404a09450540901e50300603848a603c40007401e912865a0314001d4045462540082008929001901458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748542544 1250 748541294 748541323
    0x2702070510020f0a0e090601020a1b090e070e0a06030b0c0703110f0109030315081e03250302060609160c03020a050d030b01020d0807050a0509060c0a060b21100b03 72
    0x400341a0060b2a00141194211341d1781c600311990000824020615020395220b405030f03220218950024207801d40c1030041c0c1c1c10010034440d20079914121306041d1094000d4003030042e0404101400400f03617241105a1021801100b44603047c910390791507200240007865010450700c0847e041080500c225907500340741030244101c81c064404082d61a0080c113a0700d904402192401041403080c000701342c600011100140042c0c0700e844c421401500c030903c84d1040c1e400c41800200402000182c0c07003200c0050b0f143d00b0002c00c81030802c09140192901d0000740200d0711405071a41004101d544100d94147c1225003440c2404000c0c0e0f00c0c5c84c0591410801e10002001707070045404035079459034154030149076400c0036821180e8034900000d0a40d500312046c0c9010f000914100a0110120301031001000780d0040982000d02d00b904041105082001c404005c0301c101c1c0d01c80b4001700e00f61400d42ca40003445503480381d9040000b0428000e890781c0d4101c40c005100400e03101e030400001130703400303124440090545 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748543794 1250 748542544 748542547
    0x90c22030c3204151208130611100b010203070b0f10120c0e040f0f0b0f09070e01030b04061b1101050a0203010608150a080115030c270207051002 64
    0xe91070a8642003015001d600c0191091800244815074070b076501142a4a102e030700400726001007420710010f040c1c40c5154100145140d1030000c1c44d0807140d90050802805400030707540f615114041121099501d038005001c00003070101c4040c07190740104002a41600d8410000790064076240141d09501171031002a000201920410006116100c0c601d841a9402e1150b6505c0d59147c185092085c0b1000c3c401808a560705081407050b543c4440f8000d8016004e00d11049403100c09540e036182d001c810800440302c2003c0710782482070f0034181d02d00c2d030b45e004024103029110f22814401103007074a18051201034012803090b400302d000c1c4280b60344106040c0c3c0039990104507107074400300d001c0d04070205070b4110080d662a1234001000c0038954801d0303d06843c140d945030a82c6840b1408800c41c40c000c01407910782c0c401900d02d00000c042c60b0900c0380c10554254080c24050152443c10510904529035004106081481c000c405403c40c007007418a07011203280030016103c0c40c00341003070340c035001034a035141c04424070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748545044 1250 748543794 748543799
    0x50108061f030e0a03020c04062705150405180d02060115030b19150206071812020f19050a08010203102d06080103060b0409050304090b01260420090c22 67
    0x10b000c07c445481c0441924180300c2640d83e070110300b000000350030701da86801c51070900481c41ba03002500180e03000708000709400d15070440840010100d032015104800b110000c0c0d8850718100c0f030188051014594540082d103400d40c0342c0f851070b503100c1c0304200d03c481c1010740e40c40c10b5841035030b90350001c0d0000b414000030340c3e102e0030340320030700c0c8a1400c9200480c20b01521601c3c00040180c2d01c00c0d511071521604541c0d0305803080380307041d18220130400d0f000c400300e03402050070740c10080b50340794524641104107286c0c0e00702c50001c0c582418002451456000031032180d004208100540c1035402074070301220b04030016400d101c40342034a84009004c43e07c100000d00c050301c0000107601540500018141c03400381008000d210ba1510030042101c41e100d1009180340c0040c48200141c41c099400903d0015040c1480940c21665400110011143e410b140b55200c0d600c10a01050040f40150107100c42c41c4203508000340c40c0c0340d00000324141402001410b007100001902400e18040d80e1031800c0c0c240c183c18225a074280c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748546294 1250 748545044 748545047
    0x1b070306050403091e170102070614100b122805010902091f0c020411070b0108030a140a02191a180d390506090a0606050108061f030e0a03 61
    0x1c05980030760014a05820106480d100e80410000340072481000c812900d24040008000394600344280ba1255800d111001c04901d03d40103142030701411002d4003180b45420302c1d0b4140d5043c4590800700560b081803000c1e2041980906c00b980c3c000c00702851a15010f001c080390307100d118040c0380f00c40f401941410f00000f04825646c003d0000354400f16468603015140700c24021521840d040c0e220000340800c007040740542001c0d0710201c01015068502480c002040d2120428074000780d2143c0d5003980001801d8421a40c42212215009800c40b400c902d08110120001d6540751142088003c450455803102e08119641240c07104000041c8030444961901000280e454002012002114040d006a699103184514101c81260800340c940030344034664483c41e024040c0c2c14480b001c040107880840040800d008101940c49810181c00401360b43c000b42c5882c04c00d4078110340c89141030211540501a1660360045041c6418401c1d5030f80d00c41d9180c0303000085029041d0064805002d01030210b9210034103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748547544 1250 748546294 748546301
    0x50d090b250203161d07020d03050615120109230f0c2809050405160305040606030606121106030103020a0b0a2d1106060918070905070804021819021b070306 69
    0x26178018185801380304030060310b5012094211000c4006030080001c2807001c0d0f009901a540000b000303823102403014514100810344d039000280c0220040d50910042050381c0700c40c0503090b010072505210801840590304001201000540000300080c801d600092040100d28240e40e54042c118424404601c84403010065405c6c0101c100c000040101c1c401155a040600581d070150004140b52902c02000c12401ca000780006802200e0064440f00e0002c04900b103809244080e00720402e07c01e01ca001c45182c8a020b5000281400e4000d0703500344010005030750380c114514102c0d01c20107001c964680100c0401c03141c08031040700d800d4404410340d0221480040480460200c218a0b4407004001c860300c1e5030301643c03008101c03141584180c41c00005510680844100d035042c90000085440b42a00d40000900b9181d040b20390400060306d11382040258940032141c1e010113222200c28409604082210201182142403600d1100c1d80016440301850180f9441206010f041000e0391030154881c81d100300076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748548794 1250 748547544 748547549
    0x150f0605010e04111801090e16080106110604241505040b01080138120a14100e0603100912020c03120301031209090e0109050d090b25020316 62
    0x41a54201d50300d070f030a1501c962400818641e90441c100f580c00101c2008003c103a03c1143e0400000160000c1c0c0c100028440078040c0d000010b0308600404503100042008005074000000c10503105000422820301150f0345401c103401152140000240000b13018400540c0840b030400355240c2a056088a11391000003416200216014402101030600458000400b8040c20451a4144e0000442d41e03080b0915654803030101e2510928040c440a1300108a0b040031890070407a440c1e01c800c00840b500b1364840c030100c5050014400c4558201080c0d00d4445412501035110302c1d03054200071610302c2c1e900300060700060040500078811040140740c403150072034220000c2409441441c0300e0302800e145c04504404a8203926034090308580ca540c40e807404020030b0f00041414070041c0500410002c07818040e142c01c0c02c07041c800100d1110810b14140789090112404801005081d0300148207092070003044070410b45100159251400f00d80100d601c2e550002940290f041c801d1000c1d00d000140010000e404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748550044 1250 748548794 748548797
    0x8131e080c0d08060114030a0c0c02030a0b041b060f08090705100903020a0b0a21060e0108030901091a04050f12012307090b03070305151005180613060507150f060501 73
    0x60544800b001903a9440401c101b005000b142880015041c0c3c4082d4807a03c5205950716240100c11a5038004c40c0c1850044141610b0080d603100c01c010a000c02e0a080c04410851056890403083c5408001412000c01c0c035802c000700803040b001f103044203c042024001401000380280d1814441404c080c00c100400d00c8128001c0c045443c001840448020540701e004030191a2241040820085004005600055900d00b0303581ca0201094041c0003550843c040c1c082c1c0c1c002566100039440003d0010000e82e480030b140c00805140303124000038100c05070741c2100e4040d14200c242c113030600009110780c202110710f20300307540c82d219000d11103a01400020604040c0c200401c4495200c0980480d205400c50003a010710034020004110300500c40c0d48029807082e16039000c0700c00f8224a0f000510340003081840100001e00c003041c41410003854110103007171a002202c05e81e2508151007150250f80707244c5c0c07140c8028010041a148203001d07485850301c2040c0311102c0300300500b159841d1340000520390340c000c160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748551294 1250 748550044 748550057
    0x80c040b030f030301150c051501090e010903090b0705030403120f1202091509060c0105010e2d0c0f0d020703020109061a0112050a0209060304111008131e080c0d 71
    0x364280424640b10200340003010f5482c5070300304558414005100091300042002d10a02c01c070200b0130500c058212442e08007007030031555150080480c207450142c851142942d240c9800d00740082e82103610142200e0150010381d441e0000c40c1041070541c0a540c0c009072003518186a01200180d2006240203142001d0300d0300034800281c0c809038001c9000341218250480102507400115003403004c003a0420403002484185841d000b40001400c1d55000e80c030034121403041e041480a001186240c1c03c1c41c000f03079503800f41400c1400794000a0b501c00701511445404100241d00e00c800c0d4a2001160444614003c041d50780703c40c0e900c0c00a000f07000310981a50303201d1401100c0d10b007085540301c00509251050307441d810f01c2e01d4004501c20090201502d460a0035508205482c1c0315250724000d54410b50150680e0407003a440b610a0203240c1d14503011030410007008000f0401c20803884018407000d20341190304518203817000e861111140314a2800904a0b500204240400100005403c2d404407125581d96 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748552544 1250 748551294 748551311
    0x31606090210170c0702060702030f0c0f04020f0d050a18260c06070e06130b03010305060f0106170720030a021e0706321e03130f02120106080c04 64
    0xc07a80018660f28000ba00000c59012a42c5080740c0c102a082840c001000185050441c0c2e00180c50084031001d141429041001580368a282c03030800601ca6007001c0e10150315003030602520ba941c034820310811004844e500c0700072070b1541003243c1c41044022103040b8801c3c04500706081c4444081d000c0702d1800d4190f07400021440201035540d0a803030320500303044000d00d5a0f8464070f81c180d0310720074101c20142d0021410b02407235030100ca80c0501d020090400c0340c3c0b4250340e9419402c009051400007010743d11689030207401006940d900191403041d4a90385c202d50000c50315002030441d01206c45148901c600f4a0201080c1e40e070100110042c00d01110640032031b054030721450b100540c0001c05201d41c24580d004000100040c50240c880d04c09000c013680c1500d4a1214400f000c01d0428480044200d80703880b000c207150034240e030b21700c80441c81c055008a06605500d8000d411402581211b0002401102041d41d001c00310344852003c038a402c0e03c240000d1000c6070302d075511a81da41c44050247c9100e1410079004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748553794 1250 748552544 748552547
    0x5010b0d0f0902010f0806010309150b010e090103020105030420100509040b031b0411091203090114070f060903022e0b1507080c0a1208010e0106081611031606090210 73
    0x4050b4040c0d4181c4501d4400c5a6020040d2000d110060203941459164104040040e10910b070038102c0b4bc0810000241d00c140e0f440004215111031030b13005000d000b0100c0140050b0381c00105803a80b090384180306822031030f8071071105003100480035070480e000543e22146810f1107403c80042e021030101600c08000b05000031042640e680004801418101c030390043c000c4280c20541c000d0030058403042c200524001102020070350403400c002003982150804180c0142540e40324154460710810405520308143c66522501d030b80c400400700040200381d0301c5801a04050083c40050402d22940c007207400140400048034101c51420303c00ca4450a281070360112040c03601d8440d00d03040342140c4000c203040005a541c0c00316158840b81c0303000701510805000f18001105452003856421059076082c1165142600c0f0000f0000181c000c101481401410425114000000443c913b252403900c49141c82610700f1190a5102d01c03403140c21000c00c021115810b200c0c0d00e4108000c114426140c0089600101c41e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748555044 1250 748553794 748553801
    0x30219030203270112020a2304080d18060e0a050d0b040209060d030c082206050408010513082b0213081c0519021e1006060f02030405010305100905010b0d0f 69
    0x14903602240c07462600c00c0701003081b5400b42c03000c0751003800c0039250016200041061019040c1d804152042c0001e0700f880241e0090000b5085541641043c0c018041c0002701c5868804030b900450301000b903510300b00d0201d56a0580c0010007040090815481213038a814a020070040c02c45081c0d015080e010301268440c104000300901c51500b55072481044056961445091341c88100c82040c04044400b0304004002e0b0000c03050014541034841603525403070b00303005909640c0001c15020034494102c07120000300350000e040b41c5418072103450b50101c0410059207080068040c20030104070920100e040c65562201c03082c1b0606403a100001c50301c1c1140b104c0e0000002c00220488030f000580c003484020005a2100c4c0e50b2480c65400d40165260202800c400e03c240034420100045c8552021340d0700300c00b12009209142c054111031030504034621142401a5480c4030f41e1061344d04040c0d450000840078030f5071038207003405024460410b100740e581d00c4400443e290003aa0101d6145441d00c000540e40410921 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748556294 1250 748555044 748555117
    0x406020706030b030c03030a020f0105071b0605071404060201140603030f1204060e030a030516080907180b1e030610051c05010e070e01151d0d030219030203 69
    0x240101034581c103000d0110701410540d10300b10782520031000110b031030343d40600c00b5080d000000c0d401043c0c04d04148903002d0a41d02e01500940a04c1015845640c0320307a5114030040310160815400308483e00e4000c3c048440e100c0080001404510124000c030b001641901324251840c070b50254200d042c1c842c402015100e200d0107204282c040c07420452034a410800000507580903001d8280056865801c1d91098110791100ea807800000b0ba503038080211071103129400c0c2d01c0c00c520f40d1070302c4484c0c3e02c0c00c1e0600c6a07845030b96001d5601846c0020b140e00d5031801c11381c1c010781074012020f4080300c2220070401c00900c00e8690080c03094420b014010008810112a03403180080315001000351041d0701c1030340c0c043c203091340c40d0520540c0c4a5489002d1282805c1c1c2c1003007114020b000c0043c03d03003110341c900345d138040440ca190113402007000b00c050100111103007071142c600d02405040701c0c00c5007164070034981645069a803031541c3d0128084904c00d001896004009011741601c0040402e07141103200365404d03203100004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748557544 1250 748556294 748556297
    0x180303110d050c0a0f0c0b070305130e0402010215060d02030307050d030c08130b0408070f0c030210030207080415020f060c1201051206071422240f0c0203011112100b0406 75
    0xd1002001042c00000c01d160450b005248900d607280e1190240910348c1d1008005902203080081da0200880c004d9034804000d01110582c1011403c19500003502c40da50700c000359074524011030100390240c1e54000711041e40e81d8000d049a5032007481780b40058466010154040203e4070b480034a0314182d014400da140704220080310707008851041d50b01c81c5c4003000041e10070745003d14144410301c002072945441c07881050042800c01a11890f42c41000b422065001024080500522401000407141019034050303070030050740f0a01c05124480224581700c2c02d448114218400c50040c0321084407050002c2466201e03801000345180c4e01c40c010300584440308800d03041e06030701090000c2c00030b07445500f54080300980c0c02c40051410301d0540c40d0a074001d84801c0c011271000020706003004a01e034000c01d80220b440302c4120742003602d074483c00040c103421040d030782600c01c1c40810314282c0215034080d400100481010300e41d240d1210f0310861a041034031401c40e00758002d641c07480808207801d41d004094030111480c1707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748558794 1250 748557544 748557553
    0x616020906031f0207150504060f0609022502031c050c0f0d0503040b060f03010617012301030308090309060304211d060901030905010e01020702091e0610180303110d050c 75
    0x1d0f80b00400c000d40c461142075840c1c86841401c00200707816030199074040c41c0078810128007403280d0390b070401c2222419401401c59a01c100130b0450402c1504003929000ca05050240002982600200f03040c0300d010a2080001e0080303440030030386903400c0710251088242c40d50444840781c43e004441c981e51980c2144000201c3c0302800014001440c0340340031035011001030881c0c1c40d1503031b00d00e020a003550050f4000d44106640000d07248100700c0c01b440351147d180c02c04c4030301013520a5135032040c60b9a5081800007800b0800784900080060b03d040088400c0d101d0042c0146589103040c1c2040d51500399104070900110006e1070000071000d2040040e80d01c140720203202c0d62400031400082144030341c01081d00c1030505072245a1a00420000e00c140701e04403942c400056503d0641d403040041c0d2000051001040490002c41035800214808005e9848a816507600c041e0056102090b5806005185404010102c4080200425900081c000c52210b24081112850703c084401940e907402060582e001d075030702 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748560044 1250 748558794 748558843
    0xc031a0702070b07080a02010b1f020f060112060b0616051b0603100608060109050402280513091107120c05011b1704060e07090506011404030201021504060209061602090603 76
    0x3917031001858628098000007401105010110301036400b2056420741a001c0800c40e4824071390140885210a00340d880648003940c1003001c1010010b02c5a0800b030300d01640d41c0e041c125544c41d078404556002414903800e28001c0b0b41d524005648410180b0120507106d42480b864081c0e08020341a01d0183c0e6110035021030041c20008111029500200840d0400c005204000350079200d500c01010303008140203c1d0380d01e8940e900000e00346d401310381001c5420090200070030381c80700307034034804000a5601883c03001c50f202455404002c4071740980c1d98041d0107a205006c0b4012800e03080410804043d104034000d00200283c2c240e04014551034000c00c80109114151440d0080e0034950700c5603006228890008241e4401c0079040c0c0350100641006540c1c41c3d40b2014000741d50780000c0d10000f24000a81211318203801d40e80000d40ba8200c07000d4104100c0e0201c1c020408100107a0152404124060843ca0b150300070000301c521140f501c0b4000768014012940860b03410706001c180c500008007001c1c1988030700781 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748561151 1107 748560044 748560053
    0x30f091207060f06140a0e090a02061903050a0b1008090a0b011203232704150f0504051e1302040c0504181a0f0303070c031a0702070b07 60
    0x245c0307080e115140c9a50b45c0c1800c0f100fa2540c2c4080d54110f41c4400241e40d2400024000003584201c012070f102c6c0b851110640717520307c00340a5681c140030544a20030f10000b04c501c10aa260340103000b60000c981e9460181c2042034000302d100c0119482101d0350740310ba0149680a03003008413075100340103010040c141d1003142200c4041464085015442c3d07520002e800e43e1003122a51502e283e040050940901203403d040e4042c0308000d0414007210089010207900c40b02c05006030020440000c90100d19400c280c440c4500c541400c16464140d04d401107240c0108030f00040c80c445c600c00e98200503030016162401500504910b80d115aa240d0f41010004512240560b03500e142062810040e554031035021000f6000d09002910b003a1070300425000824214490b2107005414058010f50000411403440c080e100c500280e0384903a61141c407400c90490f103c020601c80d0a1410700140010000308 = true := by decide +kernel

theorem cover : BRFrame.Cov 748381294 748561151 := by
  have h0 := BRFrame.cov_init 748381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748381294 ≤ n) (h2 : n < 748561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
