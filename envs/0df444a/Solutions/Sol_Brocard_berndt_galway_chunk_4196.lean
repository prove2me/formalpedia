-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:05.61242+00:00
-- url     : https://prove2.me/submissions/c4d38db1-9e1e-4785-aeb5-e8607beff565

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 754496402 ≤ n < 754676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 754497652 1250 754496402 754496417
    0x7030b01020f21090901271131080706021204050105032205030f07061401061e121407020f0304080a032a030509040c1403060d0503120c0a 61
    0x594000074984490050307140c0100b50301564080d004841c0b82e9040790154180c10b04201001c01c1c2d1740c0e1020b07414041c0401890303078041d2085540302d40d86031128a050903240182041c80920742c0200c40e0003500e81c0401d0643c0c030740c51600c000d02d5158440c6481c5002d54460105483c00100d441540003034001c0541f5640d40840d5405240c00503843c40500035442980e000544c20000034403a17802810000c02903001d20352000e150210030b41e48a0382142c1190a405803403d07008a103c8041c4036043c02202003035140405e0140307165050400c000c0c4100b015401030301c1203a0509002d449081c3c802c85148805101503401004a8000c201d446062070209803101401441945c850031044000802101c048407002001801402c181e80d80c00c1c0c42d01480c040c949080807919569000f960a25100340c440b0f454420303651196034400c60420001190764030442c150070880b0300c04518042c04214000c59030040c80417174480304802c01916250340384d8810b5a110144140b002428802080000d070060091040c01e600c0e00714 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 754498902 1250 754497652 754497671
    0x1020310060801150f1e0e0906010e0f040b0f0406080120210a090f060506190f0e04050a020a14130b0303030414030f0a0e04230403080a0b15030703 65
    0x102c02d8038003030003100c0e0942c040d03208042c10280900c141c2d00b0084038906190348122031607201c900080501d070062402061800f01005103500c2e050800942c007000900303019030264000804240e040d401e0406540c09281e840030501c22036600c282040c0140700b0010400c0c00810344540906001c0c01140d0300b0a46074843c42d07e00e03200400a2401611840d01c92901034082e08400940a00703a07400c1d01801d081c004c02c1e61521008003003114032074080b602900515000c0385a04122042c0300c0000c88800245180000341c99062010641c0304070084129078000c080c60855494a040081c01c1c0103504900941c4810410703400100301301ca641010400e280b080b00c11054000c1480b40d0301050380d01c2e0a8000f54180c00c02c00008002940f030700806c0000d000440c0489003048421103d43c00543d1004030007501040070016800c0043c0340c240214294441211105c001a00b88405601c00c485005080181400801000a01070461a81c0320240c8240b0040c666040081c1d9099001180d6100b50b0b40200041d00780b04400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 754500152 1250 754498902 754498907
    0x5010f020c0f0106060804121b0f03030c0801060e0a060806120a150e0a0320010618020d180203070e0a1b17070207030b01060c050c04090c08160e0f04020616050102031006 75
    0x343d10541d00140780a004c001c600c0c1c003c445840003a0249c4100b581c07074801c0540410072103400c55020310307c40c0c0c800040d0354032680030150840e20140d120070b0400c00f44501c1d88400e42c489049003030480d025414004c000e521480001040c0d00c45414165802e881884880303010301c40041c4c1d0704c9010f80500041041906540751000e03480f102000380c040c0110383c032801c91044121f00e414862584001000000030741c2a200c1c090800540400104804441d030045401050341202d40310700005004d50642602cac8005017076020a03110461880f6002d0400e107804009483c03024160040c516103a40c1203400c500c94010410080d02440c02e14050b541003005c604001840d050000035540240e0343c204003401c1c00d580c68810308540c0c500480c0c00c02c40d1640a0081c600c4111f480358090368240a2040b584c101c001b0342846082ca00c0c0c68100019522141c0100204000b085203070500b06420003031445c0400a1581d440c000303d0058400c000800d21003094040100040c42030650103113020740040e00d501c00c107265444104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 754501402 1250 754500152 754500167
    0x907030b10051b0d0e100c0c050d02060705030706060f14090a020c010b04051515250f02131a01030207050309060912060c04060806220905010f020c0f010606 69
    0xc0542064041964661460094014003c2419803111403280465203440305818914060103000204031892210b42d280c1c5401e180f040c65000880c5000400700030341d030300d070000c1d60b01075842200e0150000d080310000359180d900894180c590000304895884140e0300d082c100800584c801d50b42100d41d40f000202e110807041c0d00003041c44400800040c1d10362072b1030560900950041c0a801c00a40d6510150099503c650203001c0c86580c07111203000303030100041c0c240102a40c03910350140c201c3e80c0810a40b0302108044d840307041c0440c0c007424181941c803a140f500d2543c1f00202c41d8040e50006011070000140c10706a0409401007482c52084900054060300540c1a07001d00b44008181d50803c0c0100140c50810102a241c3d02ca8028910401810a08111410120103a481911202c800074040c44006c1e08000b803240c10010039280c03c107500a911456000030f0b030294000111150f1101301c4c10382440300035046420f501181410442d52200f81184160390b0346580a03010f1425403d040c00003c104d40600031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 754502652 1250 754501402 754501421
    0x51c140a290c12072007030c1d07080f0621010506040e030a1704051204120501061e050910090518070504090221030f0304080327070b0a030f020a02030405090703 71
    0xc4082e07546940401351910203500406070b40410300449001701941d0f041100600070f5024102240c1c036141800b842030502218600741d400130105180c103020701140c1c030800c510351204d41042100b5103900e40c100061204901d00302031044100e80c2501d05c01c0394100c1903000034002c80044404120402900c8802500e90140389009000304030000303ca80728068141c801c42d0303802403143c2c080d40ca560348001c0d02c113043c580054000f4020807820900010030046c0900c0703010068044803403c03512003074400d080c40d08000903034010103000c1c21828000c83c6458881f80414005400c0c1200c0031f00680c5464028486101008900e6010a2091007070004031401c051040080d003e0300985481c800c40007103900c400c07802d14100c40000040c4400c2007144c80110030807001e140214410991940c4d83c1c1001d520179910503900f031880c401060f40e00e4100090312500081d0403000c0707440f41c0302c450f512280669000d9008100050003101002d0001594582da16030200060044e80c0782155210125110040214100c519001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 754503902 1250 754502652 754502677
    0x5070516140907020304090c0c0b0c0703170103020f0f01200d141606150b03040c17061303180806180f030f090105030406020412050f07051c140a290c 66
    0x10061043e0415034010028081060038200c0c0311800726a241c5108003000c480411400402041ccd60f42051390101c1140d668501c41102c804555055400281c8000304440ca4548946060b103801c0c0126402007000090b45440300d90140030480d0a0282961110268004031000803041064001180d550000703403000f441d21000d41801103010707541d0b00300041070710707800e0084040320b91500001c0c2010010000d500c2136106440c07100d0240d103082409107150450701116511074000504000b82c04c0440300c44200a103400d482d24002c3e040281340e105151550301d4220100700c0c020b0100700000391030040407000588a464084800411116400325242d00410740307100c0212804008500e1258404d82c0a95005400780c00d006141c59601c11207540300c002c0d881da0441e9550442c01111035004014045407008100549007071000d6034001000a2060700000c000500710840c088025001d454108600d6083ca82d1103841d8401000e0070401386d0810466160020040c5d5444c072000400001860041c1c3d00d0600500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 754505152 1250 754503902 754503907
    0x509100c0c08070c150320271c030e120106120b101502010b0102012906070c08031204110102120f0d0b0a0f140909070b0a050705161409070203 63
    0x150784030b981581c8004425240009021404100c05e00101c20388005d911090303c0004004148640400210b10032141200c0360101c28404c401c94481c8080c600342600c111240200d040104403c00104820352591210444081040402d020180c01c00c5180300c400504907020b0310556000c4654a00340d441d02d000d0650610011503080002500c00c1e0b400c41d40040e140c40103480180d8503600401005030b01503d00c1030040c0c2d115094a049941c080c410040d110740e000750900e14080d552600c40c2c0c5821900c1200502800e800291002801010303c84407000d031903410140e079a80c100d1013110a184510640381548c024500400492a070f600004080854840d0492560309001203101f004000b60480344a0000594030307010180410350b6104400307006420344c0386240480c01d0a00c600858110712030040f50303002e204981c051041d584c60014214044070301c6180a55a98420010110340130301583c0f00003002ca1280624001092000c1c0840b141540c0442441c41070b80f44c405c40c1080702c444402c0d9000710158004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 754506402 1250 754505152 754505177
    0x605180c0108040609170706150b030c0c01020f040b1e070b0601030203180609010f0c0905030a02040e03040e0a0204050405092a120601080304051009060e0415080a060509100c 77
    0xa0300e102c03940140501000911064940c542001140400c030440005090000b61901003002c0782c800c02c0303130803a00059044003960821800c0c4ca044d201c0603042e8943c5010214003004514403d40441f41d80e4903552012030f446582e102e4a54515805c0800e44581e0400895008000b0800070400c2d2021140c001c000d08070140c50302401900207520161103020801c415440144204d10100602402040344038000561001420001800c40d00600441030400c803001c0802c120f256800540d40c0000c84d012280010700c4003006640c18a18855680144208280c54040101c02d81043e400b0340300f220380c10749003407101d6179801000944407903041941035035224040040903844448662104029071018244060100307008540e075140100981c000f8030381c0d505c001424092404c1410000d105540d641c181140c1d02424004007600c0f003001e0011a5004558410400314040000140300c00144080400e0720080240307420080081c000445203580c1910600b0440503817200b0610135009105c81c180d64a5680b50107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 754507652 1250 754506402 754506407
    0x702060c070c090e06040b090a020607151d0c04050f01050913030e061819080d0806030a0210080618190e03070c0e091516121b0201090605180c01 64
    0x28a8142d400c00c41c05100880c0c0508144144c90b40c5102d403800619252500749064400300d08020003048040c0c20443c0a03000580b2100c0654040c0c5510140c103c000b81b00c0c04001a005185032024440c2081c41040e03550300008010801e20017140c1c0a450500c860350361103003000c2c0e191400b84185a00512100d000803a0768010000045130980b00b0701d00480c0f072500d1980046c0f030b2500850401d104044000300441641d14004440b08881c00c220086c1e40c42c1540740070121501d42130141411401d201403070000880c0c46d5002c1c01811141030340107049401c0722550000080400d44102c4695000e901011400040d860301340780d10354441c5030005019591055901403440142c014210348403c64070042c0000c07000685d4501c02c0f10080d24040d07282032058600544024a4031011490f141c40d94068441408082c039640c000c40b98122140b4104150b514450303c44040080a00281950401d0b1502c001d443c1701c0c40e0f06420000f00240a4901880917860385680d00c2c88000e2040c03000e103810760000704034084550 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 754508902 1250 754507652 754507657
    0x110a0501241d06121606052703120307090b0703050309010f06031e02040f0504050a0c0b070803010504110c0106080607200d1416030c2d0b060a1703090a0803030702060c 74
    0x11481410b6418160000c0c000c42a92155504a1b20102d2000300d40c442110304c10180c2400907070b0f00503441c4258890000c01003074a0702e24502c0122444d03600000003410017402806510018040340c42d8243c2d94003950f0600526580065a18a205509050000f02642c0f240d000d03040503a0381201c00c590041003503911030790010060a80032038001d03454840030f0903807900d188115446240240054101c4103401e180074441c1c039000c2c0c1c201216015043c010035000c2824001507a05443c0c054070001b403001201210900d090141e48100151907081010120b04100c0200798240a03590f01d03119918440004202000244ca10f1072010005a00603260069603910500c030040220400c08050f40c0b03805408810a044070714122401d030003065141c010b2000708042810500008480741c2104841094621142e000a2400b21000f4100001150208a50796241c030060401400303107a4007180c010321940100750b100e40286400511908880c0000141100c02104591103030f407166025010590f81c0d11b151001c00e8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 754510152 1250 754508902 754508929
    0x302030a11030405030c0f16030807080903010510050420031609050a031101080105060f0720030a030201060e070507081b030f18120d020d110a0501241d06 68
    0x1916282004440091400118091401413014550b1101246102807516400e100c03215a55400820403545041d000101030060320340c00f0381401c0d03403a4880d0410326014052054425070652030710080c4a09501c54942d030700200c070020396040c48400c1c403004551a16212066205810340d804000090118084a440c880d8124007070400b6820303540c940010440c0c40c00c8603002200c10085c0340c58860031640e00810058010881114510f1a00c000410004100d00074003000610700400311580100c02031504a003080c1e240b9025040310b48440d240d00780203001c1c1c015407180f48a07840030b0703030046044544100c0c1100d118641142901f840c0854241c040c95001d405000700b4003042c0004d03c580c81e500051075008003002200381e000c07000c140c8141000c010142c120050100380326407040c120040780a4010600304015001c0c0e0600d03041c0d03103801c40d03a00b078100020791200504a52a200c41d503705a00c00c41900707240c0c5030000f180039810700d4840c0d4004001d804211070381c01e0408034601c0011014602900c1c2c40031130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 754511402 1250 754510152 754510171
    0x130c0e1608130b0c0307120902010c03030c02100203090a0b0114100f09030501090b1501020a02220b060424020c0306180f1006090f02030c04120503071e0c080c030c01030203 76
    0x14002d103844805400030140d901c030050440000511002c0d540c000350303115580702c608800700031000782907002a00480080e000102416202c07044001201d0007803010700c20611502d0425584c900d003400d21242c50301400801250300300503183c004030f012002e034549000c0b21007002e40b0161b100740315902c09903031085100c100703c400c00c203010101000181080c0507034906240300e03000002c0300e4105100031488400d441d520880c1158001000d0501590316402a03041160710950550300904403210200e001e40b00c2150320a400c50350015000410307155041c03184102d01d2102003900081881c1d400126202c000c00c8400c0c5602d64800408212507030482c0e10362138810002d50049501403109220f00c142017180e000007406c03440d5a034003400c110b64101401030380300d086040302e021032840c5040d81c09800b80b8040c90107200d41044043d1f1602c07040107001c10441e410143c011a4100343c00400c00704052004007410021070300109079a10004e500000000c000341780d280024040c00c641405100110020342006156108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 754512652 1250 754511402 754511431
    0x181b0819080c0a050d020604330506130e0307060c050f0324130e0607050a1d01020a15150b03010506070b070513030f05070b09031f06090203130c0e1608 67
    0xb8608218090807107a00b1b4018141300e00e03207402c200c0e104180101c6c4103d00c8409031401c6280b4407850303045d001986850310b480000d0315101d4602040010b04030b9108400721510702020a80603850001c050700081c0d20550040c0803071040c90000f1281c500400708200903024080c00401d50b901004c030071100c10710860341089000e0314600340019411000d440f25082c81c080e602c00418005140601440e540b040341800c04620b090411140181501800108039640449601000707480780e10074480400d60941210f580b10b00c1c1d2601c20040d83c0206600080c0220284405000048080d00300050301e04a9100820082c20946607890760031012030020000b42c100402000380101401c000f0054802541c06460610a90403041c0341062521704c09070000860007409011014071a68005500402d0b01c4131040e41d5420f0203003440922026040d950010740c0703ca8000b10801180300181c050000c00d040c0144503840205640e070b5080c03140e8080c15203081d00031181e03052201c410a40a40340315900510308080610 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 754513902 1250 754512652 754512673
    0xc03081c0513060e010b030c040b060405040c081f0f0302060a030b0a0603060e0603011802100302040807090b040c08070e0f0a05120a210215040501181b0819080c 71
    0x71aa01110702108400c60400d2500521180740700c0c0c003c1d00d0040e07030000c00000304003a0000e56500441040248200e45a140d001001d85400c0d05803401008081e00900000500030301c06030a05200300c076028084143c4000e000c448545800084044600090544440a081d9000e003c2650b121061501c01d15450f1450460383e1b07101c2c920104000c0695a4002a4080c00d01c0307030328801080094a0f20b8841d0707041821402e40807060a10303060010398111180a000c0c404400c080e0060301883c1e10a88160181070000242601c040c1c0081c0200300085500b0009500b01800540d4090b1003502e070303200012451400e03141c1c14144015036991201005042e54070595030303000000c81d040601c007040c1e08190040042c0e03608104959210421a1030040f520281031100c0c800000d5403856503007604130491041c040030070306003c400e41c04444190725034050316000c2002c906080e41d0102041440b400b00407545000001d00610200d561283c0f18402da4102c110050180ca600000d904601a10341e41400f0303423400342 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 754515152 1250 754513902 754513957
    0x20f16050901170a0c170d030608190f1a070905031b0112090c090204170a20040b030f0f060a0b0604090e0111040f03121416030e0303040914010506070c0308 69
    0x50000744041980c1e0b1b40c1c41a40308010074240a410000328050600b4880b003406441d40206000c10048071051b0340d09201000e1781441980c0e07903400240901004016004030400400380700710948200044d480e200c0811340e50f0307418507075a44e100d207601080c000c0d038084200300c1542c490140000c8070645603202142100c070a45504030492220f0f4451140d59600060400450f40c409000c00c1009049801030004c107a6141c50384035898044030083d000e583e014080910696a4541c0203040c0c4807000740440c3c140b2000c1c04051075940750941101c413401d10130311002501000c4207000c1c8115581029140a0074240f400c40c1c0034018150410310b0800c0c075521a40d0f485c9802c0e420401800081685541c107400b07091641c00e00420315000361403400708122284404200b01c8100100704c03441820741003148088207540382002c50382c081c1d035240915031600001030005488003140d00701c051145607400c01e00406990b10f0341001603501c100c29004001c00203400c4100013081004000e00961001804615440144003802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 754516402 1250 754515152 754515173
    0x140904030f0c171b070902040501090b0f0f07080918130f0206120f0103060f0506100c171809010e01060c080705160b270603060d0201051603020f16050901170a 70
    0x1d011000b030035140004000139040148600501409000710310b0541443c0000749581c0f030b0340c0234110268800203100703410503648804990402010b2040e0940307d03901817034803003015030120078100d10683c490101e42c026202d0318400180a079051481d040020842036507410b060011415090743e0210003800020070400c0d43e030240a114a521285004503581503161400803039a1200744c0741d911b10302d00402c100d00c0d03484207031080070481385034141401d28003110f2500d000010644403800c030b040c0d01c012501403901c0300040d038480d00b000c030308443d4068140e07258404280c8801c001d10408c40025299104200400d040d100107200150187d02992880e40209007101d989010a0380800c2c3c4000c800141c0c8944226540454541c4124501042480300030280000e083c50001074122881010119008011a070041080312903407440390f844403441c85c080d410065281c208906042456025203020214500149141d100540f6401800c00d5a0760b403c100ba0390210859940c45120305101d500d20701808154402c2c0f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 754517652 1250 754516402 754516417
    0x10510030c0215040f050d030903080c030406090f2d12030b0a0801050108150f0f010605090415090e0606030a03050a0c020406050d060510052d0d1b140904030f0c17 72
    0x9504e02000c1d46c640545403455110148040500e424000400254030038440368020580c18490780d100c1c2c880e81000b07002409074110051070034210b50610004c2120f91a4070030088000b245080740d100c4000c1a41040382000c80000421010106007280c540702c0c0203078044240c43d2005040010900d8840b0b50b0203003110000e810407503043c0e2143c1456108001902d926942c08004010030480d2401c0160f12907000a1040c0a6102407000107d4040c1c41a00d5582c00440d8615844034440100707591803100e480113220400100d0024050345000171124140050600c81c0d0320391681c0d90919203520080103e44400c0c080804903407094864030002066568510321030f041c80c0c002d4400240b030b0308001e41400c008041a92103140910a50f01001c0c881521f00ba140c1902d800c0c0c5c4d4107000c0c07040460480040c2404048107002803441601200b0604203141005202c400e40360710101454001035201c0400501e4802203030002d00080b00c4140040b1282e00c01c0a001403202e02c034a1100d2080780d00c1c803200b0031954100c90b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 754518902 1250 754517652 754517663
    0xa08031207170f09100912140c0706051308070518090106030b04240501081f140705120c1201170c030f0a0605010e0903070b0705040807120515010510030c021504 71
    0x1040c05400d54041c03000d4a0391707038010f000410401255590ba603a0014120401074103200c141c2d40201ca50340602d038201d030401000c0c081030380ca0780c60f150440030340141c210301f450302c42c100e2915001080f60301000407100d040d41e00c002d2004454a00c9540008541c0d440144148419500d4000000c00107003200400e90007244512940d202100085510b600003404080c1640b100605042c0104005040485e20301a05d0a02c445103042000205410358041c104440c0c0d2800c0c1c05032007a08100c83c0e15840806881400301450342d40950b40c0380c84d941300c00306000f01840c04220617000340040110070303010424201d05c4403a0201380c580030041d0200007030a0203142c0412030a0f6401066035201040b090f886154054201500803802070305001446a549000303000c001000c0c9580d400c00300c1c07142402181074a00511704036017221403481c0c40c0c0800c0d4007603114100c0119120702c43d4208034181070722400d111b503040ea01e014110090004840404501802c4d48051030f9095010300d0740c03a0800e182040a040d8841c6000c1c0d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 754520152 1250 754518902 754518931
    0x30405220506030706090504090f0b01032301110406050c390d0816020a0b0c0a060605010c03020d030b04060308042619031d090a050a0b0a0803120717 66
    0xc00100c05580000304030034800d40044600b4000950403076068000c2d66000c0e113000851408510307290168059110002d01145501400042003001160180100749800c1c0c4040d84151140c884a41c00d031100d840300d2288020061005010350703841800500340b054002d0301140c040c849039038a0401e102c21540f80041c14401484020030190824880c0e10300d130f8520664040516a1582e2145c88403402504034441285007201141801d5559010420001e0700505140a43e5044180341d0300780d64000518044030118101000000c0d2036024601c0c003029181c02d0b402511021605110840c000c01007640030585c01991240d010000c01e064102900142c17009201c0d203020f10301c0309401d0400c100b03082402c91f203080d8004d110714002080503c260301115581410603669100f002c0d0398920204480105d0f240d048107005041220140b000e8100c240640c0e6101000c0007031010001c24000c800c480d90040c2050342e8010882c4130b00500d400d216031076001c54541b8061960703090440c94041031190944101c00c104100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 754521402 1250 754520152 754520209
    0x30609020a23090120010e06090a060f0c021f02130902070b0903030c0f0a17040303150b09010c08090d0f050307150b0a0902030405100c0207030302070512030417030405 74
    0x50911201610480140701e803c2c107000c10002403240003c9450f00032003100300d0402c0b02040c0700940080004200c4030b001e80700d640c540340d8903090f0340344440c9009407a000d040101110210f0b501d0301c1444080340c841c3e405070010400106000100041020300c0e0303140e03142d003007040a03045861b10143e40050288201e0142c0d9456807400c041038425005022150346070010014051300d140d4002c21180f05500102034203803560454803041e2001280391940043c00000078041004055140c0d000d4400c42602114411a480d01c4405441050280404140c04520605100b60203d40c1040140c246030030018040da042500c40da0f58042c400f48494022601c03035001261510030015610007084104401c0c150420800c1e1280d00000c1100b074052203105161540000400c00f4082c0c1807000050100d1128802d000842030313150001d5486986210990040c011041d0128079440c1000b60042e516120800a50615081401d080700c040c1340407100c00e5a500c0108400141c584851490164401000040c1540b8285 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 754522652 1250 754521402 754521437
    0xc0306090d05162111160608060d0f08132108090d0f0f20090408071122020a03060510080403080c0409020309011a0303030103050606010e01030609020a 67
    0x202924001103504418040d907400c5a101065856480c3c5194404100d5005424400002000703007100c030360303500c01c00d03d220b10b100794000b0b8003103031a45151803c0740c14101c6842003426198105000d9413001070218030200d500c501c1c1c01c04910741000e024a1034040741c0348542ea02c00560b948206c031115030450807168200003500800c440e1548850312030003940c3c2c600c0b0703180d40d071068036100d410b90b1075124012060002c824411a6038109003443d600c1010790101004505110980750f268013544940f4860035641d14401d410003014442c0100d0b13200b146182400100d40c0e50220f0a00400585e540080745000310001092100085820811002800503500c4a80e96402415182d85800c014000c500d6000d02e03c1c48076030b010781c0d1160300c1501440c0020072170315410b138002101d100d90703800604d8560021062100684040d8011107440b2200504d201d15486242c0625417a40403d2102a10b190401c1c800070365154001ea113410090001403400052480e200c181d08001c9030040c4003440c0020b410413484041c40d16 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 754523902 1250 754522652 754522663
    0x60403060507030e070b03070f110f071404020414041a190501080c09031b0105161109070c0c060804051f0b09010603020f0f070c03060509060f010b03010e011502100e0c03 75
    0x10035409064081e0504100c3e1b0700900c00580300c0c20810070912a0144000d00c5086c0c0030038410300c06410b80704440340c00c014881e511201c0c1d011302010210b466100e001e2601d850320031a41103861751100b104000868004001c01001d1540ea58120694074984054850742c03403151000000c8641042280140e00b00400100148401040714403049002c0020754850b035400034089045a1031a07100c01c1d0340c0d00505004079218040c040c000100e44225017110780820881120041c0e052109070b60400540e175071890100c801e42d55090340a040720349450030a0040345c0c40f4281044d030080c01842200d0100310000080018003c48208040481d5580c0a4100301868091249401405245420f5082100e041c001d000648105810440040b1000410000b00141001c1090095400c00020405e0b4948011144d865890032244018298000d0f0008103220680005480c1030740c0080e02c02c0841ea0f0300b008500c0f17a1a2034424085000d520a44042c441000a14068040700100c2e100180601ea4003202c141841d20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 754525152 1250 754523902 754523921
    0xc090c0c0819030608060c070b0f06150a03020702090a09021f08061210050c03091e0a080a030f1506030c0c0f080f0c0d0206010626060114040506040306050703 70
    0x45689520300c808103a100081c0e8035000c1202910008642808030140c004000700c0e88040014010340d420003000300c1300003001c0e02c030040c00baa030030303508a0307540b10010700c04100d08a560660140441e17801032a450301e1031001e01605a41030070300506d0110b80b82c00086a0b50700c12941c4d2583c15403500c025a08608045410134494000194025601c00701c2c1d0201405024000f040e89014805040e01e0040c09a401c0001c1d440c090482d440400690a240c0a200450381c021540181c0da0700c5000303135141c0d1150320303142104c0d050340c0c4903c06458200d00755600c00c101c55008400040415464030030005804070144512440980b101440c000202d00c0c101000c0c0568003000044814400b14a20350b1000c0784542100c0300c1c2e00b42d44104080c0d620010860480044d001d400b4000100d842010040b01d003650300010800d05072000f54442c0085000f504c52a5102e90428a8401602044441c08500c0a50080b0300200306502c00c4400d02e42455110b1010510f59081540309803900c5403503905000c03c1c55094071604885 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 754526402 1250 754525152 754525157
    0x1506030b0109030b090c0402071a010b163801060e0604050306010909030228020f0d051005060a0b07060203041b032003010207120c1a10031103190c090c 67
    0x1180c04400018100900350320001c4c3c21001d420000400904060010040c0b01da8001d108544030b0780c0d01c1c245011490598000302c50070102200011034499030f50025500042c08001039140240a16034800c00c20110007500c004441c0c0c071001e001a0442c003600321500c3c1c1040e504031102c0d450342c500b0071700400290440d0300c42401841c04000502664802007005819150010340c04a000c20303842c9030403894105c0c41a168840c0f2891031100c0d070741490021540c80000c9008403a030380150801042000002855417078010203551040e030040e80c000e1405e4104540c01f441c0107040208269581403c1c200c10383c003207002100c01c82e900008010402c1000001c1c1d03c034824445a040a0060855443c001c1a6850365503001c241c0548003000c241c1d80d5400d40488010552064105a4407070f10100c02800b84040741030308955040305285141c00d00588050132034811140030000a0341e492464482c4001101c0000b14280c0501a1030441001e100c0c110899000d42d0b48144248040645021261000c0321681d0751442c08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 754527652 1250 754526402 754526411
    0x50603070c0303021e0c060709060203130e07210b04050c09010c171e03040b090114160c33050708010303080c0705010e1c030b03061314060109150603 66
    0xd91030703000765044541581410010381e94424102030f801c14010030744142004090004509801c1800440e8442c021840760310348040b840d89915040e6128040d0140800b0840000942005910864054542c004c0074a040844001030700f141030020707400702c0583c030075105a220b25085103113060900c202c0d584040c8620304e407803c142d00d00000800110080d030001c0c14050100d21481d50f04264002112420504260302c0c074010f094481d22030310180c0049505841c503610220009051b1001030017400003c0c031b0701154040003607032100150300b10400e41800000400402c01180300024140c0031042900c3c0034844e085101e85e0036401c84104c10551403c8045254605000c00d10084941014045042d030741c0c0340c1130000381560b07100d5001780140501c0e540540150709180d8070203a8181c0202d10800d00075000b19a802c032186040030154103a482111480f074041d0b0144e40052056005981c0d071140d214420890242410400d800a81c41c1203001c1e008090f00301c1ea00d200c0796030000e40300600c000040126040512 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 754528902 1250 754527652 754527661
    0x30106020c060405030601060809030f2b18060c021213052103040e04170a120e0102070b0a0207050712140105010f0501020d14220503060603060108100b0d1515050603 73
    0xd0300c1b03030410b100310424052100003241c0384100910550340c1c40000310403030940b108410310030200680001140e1240030103001454080d40c04142c011044084103500d50306443e840155141c000400340c03180201c0440c0104100c0202540c141d2000f00321003418000e000c2c045500b4401001040c0003240c3d0001d0400d8243e01800c002d03000d01000b56030443c1d002007030481d00c07035841e410020a0a42c1210003943e21080c002841e90030705801c00c00c01482403840c090200070b0480c0389102d450803072052000c0640385145810000b681c2211341e4004001d128410b1042d6031051b0703038450308010b500700d801c03104503182e26032a0b46640116209124040c01811400280848145030200207902d9254410400d000c00091480c1010f040c9038500840300c4180b4010a08032001002482c2c0d800546000d00446219004820220b101440c0000781f0b14147c0300800c000d0540200f108032060010101274006681040c01061f070304002c40d03580176076039600c201c0259011500c0305200d0002e0320725290030f4108900c145400d00510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 754530152 1250 754528902 754528909
    0x607320102090901050f0d0f030c0b010602030a0908073006110316020606010c0809010c140102130e040b06011d03120309060a110a0f050409020c0d08280209130f02030106020c060405 80
    0x7ca210f03582040c4014107508181c2011650001b480740c001d01800012000050300581c000001c05411015584c0e01e200a40ca41c42413076101d200a1050040b000c6041101c880b80d80070003441c0c40780440c0d103191200d40b0101103035100c4003918218003108002036404003c0011b080903014001c1c2c3c00c0e0031640b029100610b0580000390024000388405840c01801041c8182140d000e8441400c007250080c0001d502401050358660103035001102509403162112400501081c24908841c02580d01105458181d601c0000454000908803030722145083c4810031018551030034444900001000f18180e9a02d10313189031000e14001c4060720021885117041900382c0c03c103450500740c0324032500f1440c2208400071105c6044401d17010380e41044078924030029921500440000707007014a800c00391600c40050340c840210945075105101b08080403642d2802d4102c0c00e1065500400794000000d10030003500c0c00f01841c200c2111800002900c04660010061041c1c50301001100f40008080714414503150800011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754531402 1250 754530152 754530169
    0x60203070c06080f04240504061d0a120302070318080c011116060f020a021c0303240515071a06030c04060303020a06022107030204060f030603020607320102090901050f 74
    0x183c0240b0080c44106e100d00640120050429202e05080c40542454100540100102255110b04120310b0491141e4040040340d00c2e442c164100103600d400c0d08105101b03078040d6009074001c03005c000c100544061482a840310f10701c040c0580300f0082507184982400540301e0b07010501d040303840d42d0000c201d0b10ba402442d03c900100350340c080d141c10700e50000703891020703854520b10070b10003036000c1c44044081815441e07904529806501956042c044040c40800b801080240008102e0ba5250310600034022810140c00d9901010140160a450a401a11449900343d46510030051825190080c04458902001804141d000c02c460400440385540d4001c1d40d14201004002c02c3c95801141503010140503450b4840140072503501c1081c286030041000340254860b0003108041001510241c40c124402d00c00c290549901908640c03510703d281c0c40390401407928811172901d20340d45040040340364008540041c41500c1c3c1d1000540c80754140c2d01044104001604043d014118124040c001941d81c0d244 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 754532652 1250 754531402 754531411
    0x30b0a08060402010e0a0b0d02030a0b06030402030601060e0a260f1603110607050a1b060e10050c160f38130e1302030f070303050418020c07060203070c06080f 70
    0x174070645003100c1a010a21401742a48126840103000c42d0403540c100d000d400440c8141da64620400a99445034108006400242d4010703402d9441607006201c0607018112202c01d00c80010f013a03500382582d41003110041080203483c1c4410502240184003030510401c03000100d505114080c20b40342005140c410070f03440c40c601c009084028020b00408040e11080101d9600c16008001d860107910302d4240000081d032060080d0f81d01321401d10001500034400d4507a40e4003c0b400420041d20041c01040c212420341200c0030710101382c0250401d00b0503400500e455400101013110308100703078514020005441c5003500c202e44980e49540400f0682284242044100c541840010141c0300d4a10313040d1165040620f4200d5520101400c003800311321517252910b0340410b4402c508844400160107582c42e10350304288401004a070083c04144010080c00b8031603a02c1c0456000d0050901201462003032920010307030f00960142e040003d0b50b5092058003040040613120904220754141030508590460100080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 754533902 1250 754532652 754532657
    0x17150103170a0302040902030a0b19050108060603070e09040b10060201020f09010c1b030f020f030307030c151e050103060b030a110d03141308010605010c210c0c080d030b0a0806040201 81
    0x242c034072082402030341560003401e0301210840d103901d00744c40c1c2c440007030060001c020300c1a110225680058420386542000380e03001a50381540c1e944070780d410700c80140c10143c00701050003841c8011052640300e1206161080f1b000e80004401800c004c0d20b0f04194062940004003164010401e100c1140b60920850b8000e507421301c2c200f444e200c0d0a0600d1400c010202017a4003406054900020502521400008880d0b0080356403c00c40d10490b001c05542e44903200e801404540c43c558580040303030400300107100f1051050404a00c1d808240d41e2820301c007403800504051265144014402c0c0b101902c54400504800d90080c00c8110507a00e50f481e07402241d4507003c1c071403580c6120080c2054800e01102c90701c1c030214030340551910307181c401040c000c51040c064020113600c1c1c248001880d42c032a41d030b11150550440b180c81c180c1d003d01402c1207c00004078400c24140225121321000140c034011292004000c9000a0110304d0144603000303065540484010340324040510301441014008680c442d0400c4c0d090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 754535152 1250 754533902 754533907
    0x1003031b02030f030414031e100e030c0111030f0a0603080715060b0a1110051e0c07020d050f06090d090e130c0605090103060902070f1e08041715010317 67
    0xe10000e0f00e411590400760f034183c080400c0001303013020381ea58501c203c0c540460668042540d54050501d01c1d02c0309000c855a00d40c400054000045165488200c6914410054900d065001c40859003500d8204c0342149041000004114250030351a814a401400703106c0180304442c40e6441b43d810074040e24201030031a203500143c08420110300d0b80807200416140160b10344035007601c440030307052031000c1e40000d050b03007d104940c1c451103005120b098450040182c0003481c1d54100c0030224aa03010082001811041c1001500e0150f030f1204044011507101e040200030015200700517506005000d400c0c15415848140c42c5c50301c40d0f810601042c11380d00500743e0010b03596079074189421140600300c00604900000480410015071180050a01d1107003070700c05022440d034074407041c0b0880c860314030050b0844140c441e103400001c0f444011120120120758148e00410007644400200c0c2c0e102b948494001c9003050303000c017195203003400031000018014025454035031440c3c9454081c0324050340c105c800301100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 754536402 1250 754535152 754535207
    0x30201020a1514040b190509100b010212121f05010f1101090f030f11120712021204090204051513060e1507060b031c050712030e0a03080708100303 65
    0x7164011a0f11201c400c1032103540d030409044c01d030542142550010080d0401880d036880150072402082e0059084000402510201040e00d400400007010b2503030441c041c201180710810481800381c40c9070400e08081120500f0a0000310b600101d4014990038040c8040301c04014580c1c00c006880040d14550a21000080001e0074143c01812111401450b00711049224024568000c1080c42d40c06c2c20303a25075084c1c7c008104040c9030303a600030a2807620305400c100110310004521444540001e1881e00441d14020140d10b1000c01030740054100000259010504004621f0005448981040c01303540b5146001640c0004000c0c0344414003a113000d10428040c809c15640707441042d0902030540050030f54941b4020b1070f280000d81040411148681f080380002e0319805200400b0390700da080c01c0e445891619150b03a0f240d01035044145041c0342899902c400041c1c600c0d109114a0741c0e26441303503842407410300e405080a03040800107030084084038880308003480082c1c1c1100c03101c088020751a8181d48010311 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 754537652 1250 754536402 754536443
    0x3030417040e09060f09010908220510020307061104060e0f010e18010801051e01171002070303050a0c0e0d1e05010212191509050a06030203030f04031a01030201020a 73
    0x11039000c1103190803003604000703c0e00008038555000c0c5141c1005e0071040d03110421020300380c515801e00600b843d00100140e00c50300710900c6001c0401d199441340021466602c2c00060052045074802c1005608005000802c01c112403003020404100801020704040c2098402071042c4904540180074000030700c2401ca1503805221032500088006000c501d00350076881500b2440902071091341e0056081001243d1b03100c80c8012900303c1d440d07941c00140a9a0f28015480c50040c07000702e8100c2a5000e42c4070811500c0d82180002c140d401c0c029140480d0300e081103481c140c1142c81a00011041180c2a0600c0e0b02035912030200050b459080895120029551010a9201016100700404c80c1d880014640140c0c83c941e0340040c0310300c100b84080710324a01108607410540d9003480e00c40075410110f40c2c0a012202c09640500d40048172500c00081d05600c90707012900d580d0100b0018195110003060030410403a0300b41d0410b0203020b00c9109122654176550000c2d41d00c0301e041c0d000524109000300010030303104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 754538902 1250 754537652 754537657
    0x90213061101200909010906050114070c051f1d150903030f0318211204031e0e04111804020318070b03070e0316030209090111030115021e03030417 65
    0x1040ca440f4074003d9141081480303503405030080e64000c800000000400001e18402e00d4100c813030684510320410f021700284045a1f004000484140c01301c03050200703c5803a507d01c0308141460616042c400d00400c40405001443d00921b132143c05d17134900840c40c0907500c4103d10020f80c90040805c6039140da60798000a400c0d0b000304016801d07424804400c1100084090840031941150300050b02c40d03200240c1d13100e404070900810210041030301003141c20300311036030038070030f254014081d15040c400901c151745000c4040c42c0004101d00000e40740700134103200f80740c284145140702d072141e0601e074504400c84450166801c0000c2d5118807455002c000116000d5686d407046001c0700041040e140c0141d100c4520100d140c005640701d00000d088462072400d542400103045003522140c140604080d4074541c01c008100e007005200300c0081d500ca29600c503200c500d450186000e400001d9144062039014035009161200001d00e000407030346000c850054010010046079013140d0000341c01298981c51044038000e51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754540152 1250 754538902 754538921
    0xf0405030a05030909010e04030c0f0212011b030b010509011e05041503051f2303030d0213150305101802091c03090f0f1205070e0f040c090213061101 66
    0x40c010340c075150081180100c010103800d50300322880c12081e629855510b685c480c0031200203003c145070041250109440c128071300f1000e48020300c2e4003a844104d28085003594011002c01a035060103001d0a00d0301c94050040c070545100c2072070014206150900020034040d040807490140b400070450120641c1d2060b421540540442c008646001040500c003c1c000c1c0021200254140c90700d0003507101c2143c4802e01d40040b151141d001005013440e030811844840c00e1b1402d62541840704220262800b00d95001502a15100c4e61984016074504880d0302112603c0d45000d0041610740420044c1000a031643d05081c0ca400071005034650004501c400000e2040c4200c09900000380b0384403941e6a441940400d022521a039100c0d03000c83d41e12441c02100700d031540109040e8284504050040100c200701040704540a081210241581e41d00041c0c4010420758900c18420030740d0040009000e00501c444008054201e0214600810111130315140c0c5001d00501040008810b62148a40c3d0250400c4000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754541402 1250 754540152 754540159
    0xf020a0f06080406110403080f03091608011a09090303130804080307080c0d0c030905040b041b05040602120315010503090109060516090b03090a06051806090a21090b0f0405 76
    0x312520385401524076502120100c96107802d00040d2142e0301c0f0000152000c03070386e014185a04100041e10803090941000700b9807141c4c2e00c81c0800c20100400411201d00013030010400015000358020485c40c10504124132850103070384e0510901202c1040002140e90105006107130b0019080686020451031003141c1c4405034510000ca440000e001904009007080110181183d000b408004025543c142294201801164480204100f5400c294001140e0610000e00c00a031b00101c810b00c1000e01000840240c2c002100031400744a9035404004a100000141e0045420b528220303004064400c41903002030b041102c00710118401ca0025001071181d0b030f80c8040280940d01e40000d1039000c543c0d800001170000303002c0c44800506400144116406829101c010700040d24064441d08050540600140000c0c640d540c00d80081020600046000b20070f404080c007004900d40c10700701c0745d40c0d840217120210901c01981060400343c00209a40c129061482520b86400245001034414001c941c0610380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754542652 1250 754541402 754541429
    0x301090b0a0e07021501050316090b060c100204030507060c050d0e1c0f0308060a031e08090a030609110f06180637031806090203030d0f1a0105160f020a 67
    0x650b9500421517804020030041103048982e0b0b030300201503640300a1101d0014242c0805c0b810301c4551460b40024214030b00290120b0310380740c03940b55003a14180b0000384c0e1803060341e80490103104100080c04a28010302840ca014140e001c45511040e03285c1d1400c40c0034405120a65880c50000d403641103588003d2031448411340552401030400b107810f07900f42030741100081c10f400009081341c0760072103080084c2d03904503618400340e4800140041248541e01c9058452010500248103195580e440701000346100d20404100d151940c070b460503900100c200c80030710035442810400001d45442d000e8401c0001d903400f90050081c0c49c2d10114880340f04030940c040c1410500300140440b078010307050750030603c620302840100e03206298000301c0448140c00c00c81c03050408004114000719055070003010308103000500340c03803030300c600380301a8800c5442000e001101c6544600c50608030a141c88840080d10310203003041e030b01c1c048402041c0003624015100081507040b02401c0442503440d01c82c02003025246160100300d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754543902 1250 754542652 754542661
    0x621110304110307080d17040507032111010b010509010347030f060606131d0103150c05030105040f0f020d090b100f051e0405010605090102150c0301090b0a0e 70
    0x30031050b003809610380071344140c510000c0d0003d40040c2c0740c00500300c280e03201114022504241908582c01410075143e5214622011006c0703000c4803030200c040300e03a15a182c0d01e00c448a42c8041c05001855541082076450140c0010b80340e6003141c12a00404401d203000201202c04001d4501d62180b61110015000f020b00c20655001041e1030f580030a51008500000013034020100f01940d64400b03146c0e01407030360401e40c04101e143c05d000c80608420030ba00c1b011058242d1312507004441000c00b040e42e2100b41d0040704010410b210000c04c51041d00541a0014404004121409081813106109190040e540c0f5100031541c2e085a80c400070f03100e800e505086d582c81d5203500058016101c1c002d4103450200c4c0d2170010543e40300c0790025410450b224420f00002c036525000401c884c6014201880d1740012210804006540d41c1d445018080c044549445031505400c0000a20341a0b00103585c8280d050384005203c28044c0c60802d590454488100100c0c10b004410045110942d03c2d80c8001040046c150034807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754545152 1250 754543902 754543913
    0xc070603050702010f0908041403031204210221090303040825080f1504020a03120c05060a0c091a04030b010b09090a0b06160203120a030e160621110304 67
    0x21800b6442d96030080c070010034000403107411038010480c003c1541074108410407410400e116080354224000702501d007091260b420300044c1020440c2c00700c80c0c411100003d04107009810040c0020012180f0081c09241140c11003800c1038120302c403160800c42004902020641d070f040080341c01604260040d10306440c940407034400401c60075242001440455640443d800500080d441d8000d041000104104800b0420000c0c46480c06170050760450440c45011001c03032076215085450010582da01032107504641050783c00c007100500440c090505060b19195001c0c3e00070b100701d05a0302c8034480000702d081a0240e01a05116640c8001c11280c0c1039800081c150b00300a026201b6124190b80c0f51080781e85032140c0d0380c1103800d51a40b09510030000d0001844100003003121a0900d440541150742c031100c800c3c41d60a15400111158001079192070600c501c181d01800404941c04050040500302420030002811300c541c4200e404500c09000c02c0c0f0300f011005280c104000990030b0006d010351364141030408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754546402 1250 754545152 754545161
    0xb130c0e0405060102030c061506090a12021201050702070e0c040f2304091e05070503100e0f0c151e041202010806032109030a080c0f0607051903110c070603 69
    0x3410712891600700025169400442216002c080c680007402203a51000307022041d080700b9410710750b04460140000182521440721000140442038510200c00486104011003c01031054440b403d9051000780101d40350001211403d683d81e18400000c42c0d9114090a402e43c011a4005000d10b0031880d40044d4031200d00150742d00e9a030800046144c40c880c2da005210a880402000a007a055400c1d185504c080746020f20f034240c41e10030800d4074040c030340e62000285840c2110303074658401952105031140300b41307042250b0020060742d48054802802006e00140ba1200c1804d0707600c1956030700188004004540f8410300c2200b8030f426425903215601e0f0740c1d040c0790076110745100b207000c2551640032500d14540082c00c2040d02d51405d8500300300400e003200d008002d81046100a406110300c00c15580000c0d420409801030380a0100242002c0e136030005a40c0c42d02e400601b00d03000b0310004101d41c2d0307021180c0c4c425400f0008100c1c02c000c02d024101c2d01004400e44108000103025002d800701c0460380c6d9505800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754547652 1250 754546402 754546427
    0x61503110a0c03110109240603080d090305090307180b04090228030c0b0702181b090d05011406040501051f05281107060201230a02090d05010912031b030b130c 70
    0x2081f0036000d00040066086820501016120450a1013005003004840e005500c0f034512034a0080d09140400c0007103841c019541d00041c510240e0001c0ca508140054442d001200c10100c0f800e2008114070340101d10b2600d1902c444010b482c0d010400300f0280c00c91448070780300540e84138280c4130229540d9a052100c6410100c4100d11031020410140c80b2030020442072409426954141d00000407040c0e04205a0f600000c0460342185000008034013080e07081c41040c1d0b0f080400c00e81811103251190400003103c0c0142c003d03c0c80b403a4030084d04c1000681c2c1b102400300e0700c1e005040260340c4020390790400e080d00c0070300c0c0d03e420800c654010480c010320703601c0b480d05105401c44008540f0075603280d040a03401d031f6450342000300c40803103000005201619010341c0281c00141d5904014038041525001c980d0700300c0d4085047d56540e46800c40042048010107060b105000d507840d04124100350b41051032036800c00310800708100b54540203500c1307107540c0d01118000c03400e034102c40c20000c0c0c1d00c00b444d0182a0307500064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754548902 1250 754547652 754547693
    0x304060507051908041b0902030a0c020d0c06020c07050409051b241b0303010b0414030c0a090e1c090f050d0c18060305010f061503110a0c03110109 65
    0x4000c600540e004800f41e488200e42c100000c3c149000362542141d0304c2c035004105507600015070742c0b41c045082c001a42c80d070107048142c0c800f5a9034681040060b06039002c0781d070796400b10340c801c1e940c00040c16408509001c0e910b44c0004050381d1443d1604c0b041d031500442d9046a58028901084081008800a1419070100c4000300d410001940c00b01040070aa07180b10340200500c441d0260542a120040001d0002440c20191845240c0385d40d080305207141c109802c07113030715010002000e119802150100c1c3c01c501004800418070184003002284034841c545c40346150060303c1340e07030110708002c00f80f1004d5060351a064000e0b04660b20b0580060402025100d40c0a91410102001c919801c00203a03c14202d44c001c2c014140b1289882c032044002c065018034101c01e82d5a503580807000400038003136506d030b81407801404147c450030706d440c2940808048882100b45854651103039104c0c2e040c403041d10513040c900d042c15142c0042c46c0c2410340b4880500e100a0402d0b5281040e02410062803040740e465098406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754550152 1250 754548902 754548911
    0x50909010603080d09031704080423030d03020901030207050d03050a06061e0e03240f090a1a0c04090504080315012d1e021e01020a0c020d03030207050d05030406 71
    0x1101400c03603640b0300014000c282c0c1041000d1801c0c07556008801d08600c42e10302200c000101d04050003242e401540c00300c1d02a14001070800c40094424055880256110200381c10320440c0400641d80b4030965843d2814141c01160700da689a00a9064850003900002500c0c441c0d495540c00a001302400c0740d4168885141060200381e1911443c2c2030007007941c145d0750b01d040301e852045080e545900c1142c840356040c0309603c12211a000400000c0035022031341c284501035410403022032013411000800d03110140d80f0000f541c80110750820b0341c5e40c560f0b03201c400d07840420352504c011481c10780c80341350003100301181071000303200410031842c006511a840000401100d5440040111889003a0071400d4940e0703e90601520200c00140428140d42e0940741407804000c400304004007a040704800e0b80d01d002da041021400c5050001c940152207096044001b1454601708030000b8010140c5140080e00482c07103d80c280c002c15011f030781264000d58203d030880721005c5880000614691045408a520a040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754551402 1250 754550152 754550161
    0x1b081f090c02012f0f1803030f070605010e0903090405151203070501150506040b0a02010b0409030507030305010b09011706190b0301060e0d0803040f021f020f0606090705030f0903070204020307090509 88
    0x3054441c40c0e8075181084d00070701e031200c005100121500141c00c1d09088160380b2000700340c02e40e4100024401c2e6040d441c00a511030b60303582800d00c101c400c142d00240b640c290460030421205004403c584c4e20000c100d4001900f82c6800d1f4071800030100003ca180d8000b0540d4115440d07042c00000584001c41c07040f03009000901500c03091b250260858031034507401034010700044c4203a050450280080034011700c00041d10581250010f400d9503041c1400f0b40100d04001940c505040c3d042c06610301406003140c805181c40c030000d00003000c050070f403000380f1100000040442c3c016a03401e6601c1911840010f40c00840e15114204c028640d4030a110705000305a0b280f2100d149030602690b81004141c02003c1d441c03c542d11611034081080403c40101d1740960220342039015290141030f0a40e00c070440e036004068183c01c0e8003c2a06d8010007801c21813107040c01004100c0d107242d1000480340e0150f0b144031454169141e0b8000940341d8015910002c0d03016001004000708968000c0d45101103820072180b810090f00c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754552652 1250 754551402 754551461
    0x20f07080c15040b070f111801180e03032205060f07170106020304090e16030c151d0103231609090c08010308090d0b01090905011b081f090c0201 64
    0x195204c2c1003011001071104001103001d0103c201c80c0b640c0240d03082d1500c0f0401c05c0010720404001825040f004040c0001844103204108071703048203059190f82000169000c24160740d60340002001c0211000e4441102039560341080c000c800101d80c01401c40d03189080904107040b0212003200c0d844000b82008201d5601c0195806000b4105e48a0790095442c10781001c24060203490712090100c864480c05135805c2c0c0c1c0e205000003490056000781140d954a904003400a01043d40500040007001504000030310705403c0c0710a006030a00e0309080c00608800f03150003c0d4141e9104d401e4507034002082e0004c110810041034502070144506503180f83c24151502d1071007003140c0800f40600006045000180000f8503400000c015040c00100a880700740031568903441d10740b0342600321072207d40d1648003000402c0424041e41c40c00380d0201c42840c8082116a100810041006000740c004110107200c10070b070100c020148001a060307662061151800c0044040c1c06400d040c040c6000c56034440355280034164 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754553902 1250 754552652 754552657
    0x70b0316020703080d11040b0a1e0c02060f090f0607050705030c060412140c10030b030d050f1c02093102040b09010507020f03010e0a140a020d03030903020f07080c15 73
    0x2913100d440641440c40c03410540006008022848a01034020000440c9807048a405044032041707a036961010403500c1b140e01c0c4e00030b4104240c0a800d009100c2c0740b40d0300590b03806042d141c42c03a00c0c45610903143d41c200d10000d003407115031004003608100002009400e005003c0303400800d958042d01198203101c4100d0038418a84134900c0344141103120f0717050320740010b0220900c1e82c0201c03040d4000c940c1c5d41c00c507440c006170302c0240003451403001c240d42d550710071030a06043c85005419540760800c103080c000c10780000346062044080308401d84000005490114565506954203008043d001075211001c1c2d034480055011030445600a5510000703841d80011114001c540684d28213100071801c00580d800150303000d4009210883e88040c4c4000c02c0c0d03627103480c01d1040c40300000c0d1480007015480c0f07050801784041780c01c00b0f0301d209994020440700c00142e22111103030300c800c07039040c90300041324415410201d050103d1204011124000c91000158801e40010001c080342000c07070784140200ba07030b0b2082a0052 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754555152 1250 754553902 754553909
    0x1e0903030e04050907080303090322080705010f090f12050606041a0f0105040504020c032505120d0e070b0406020c0307050904020108060607170301140409240b03070b03160207 77
    0x40c008421400c020708050f00950b4000007640201c0300125100c00100d811500200c48602c515031000c1004d0013003e40c400d01034002e0204010310140550b0620140d29120b200d98003440d4113000800e5002c00640b4030070b410050080555031030716001d043d201e4660151701c0c074a0400c255050300c14000800c5152030140301d44819080c0c000c82e1105101510300074000035074038240350241071160900c4005030340d440b07600080604103001c0f000b46a807040c1c1514501d000c0b9903640f4050a03031541814071200000e0000584030f036002d008248886c0c4940d6a00c0ca258054440c03800903012130301038031034002881c4000401403c00c0e92041e0b000d55440c1e10030441455680c41d60340c490b807540a404000810090350040e90310300e806c800c1c0606841c2c039216264078ad02c402180100c080e0002070400000400032020104042608128215400d000c0d80d64140c942c0c113940320800240d144403511044d03841038000c00951004041c03e0000d400d89017074950314207100202d034104442040e0445507140c20100d04a10108505055 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754556402 1250 754555152 754555157
    0x60e0609090a050612010e100e030f0f1305192111102a030e04020c060a050603070911070605060315010b130e040506040302100b01021906020412031e090303 69
    0x181c2c1e9846040c0000740001618141d040642c0910086224400380540c10032039143d90010482000008aa8421903002044408042e00140404e8400c141e100003100c40883e02054000d03102c0c245005001c2500c0429400320354403403024035142c0c000040609206046540d1540f1503040301c002d00111641c0c041585600a00c01d40410705820114039120001ea00305005504c3c000d03000b50168030580040241da00030350301e4019503e1014104140d0705c10b0240c210444150740030f604201803941c4417a90381c40023038000240180c4810025040b034030100f0601c0000c012801d000d00141d0040742d6080000ea20143c01a544542088002503560070005007807003010300007521141060f840c141c807111507a04041600380040300c001e10000b03403640100103514090f0340108068000c0d4200303490701074505850461000c05072410806190106d07030300400d0b6000c1e0b070984003000c2400c04a072071619200a01c190741001d145080c50f201e02506140c1d211041d038481050001503041e0a0005040950b180109840010300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754557652 1250 754556402 754556419
    0xf07110615130209040509031b120901110a06020a03022a032203082a07050307350703050d0c0b07031a180702250504050907090213060e0609 62
    0x281e040104400c041d51202c0e40005042c42c040d24000f800795441502c43d1b0b806a880841c0d01c641e1111790405424404401070001d00c0303640a05500d09600707006080309a4148098007030b5008480d80c00303101d0b0140143d07104000715902c150f4035401500a401052840c081c041c5200062025890781d04841140813508000440c10300d26250302c000711038940c15280c084a0850010000005020321014000328602c102a4684003c2c0308031900d400000c0b800b1140b6111360104808215507100031403804180c40013079540d00103c10036004850030000812001014441c2486591001000045103940c185c9114400340c0300301210020045442d01203031100500300110803004201498044d40c04480c8082c0d00d000902102003540740081c2d01c03412580043c50f42e86401408000046606000841c0719212b81c20303a034012204526003051000159000b814040c81e66200810303024082000744800a0002d80800d5689004038003030300c140d14009201d107101091030130b10030076100e1610300c0a551007618007601e070f0781 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754558902 1250 754557652 754557691
    0xa020d170a020a0c050a05010b04050604020316080703021614120415050d090501020d09060e07030309030b0406090c0305071a0306090712060b2206050f07140c090f071106 75
    0x290300c102d41e51404c2c0503000030400c000404c107002194a07a030140c0000103090000350706010a40b40d006003070501c624810000c01c503103103c0c845030703001c20403c45203400062652880310540c024801c6140c10901503031103c0282040040100c402d0500000c004162008240840d11000700d6000380e01584001500f04401e0224051040001d0a1414440d00011462240c0c84d2201c0742241e1180c440c560b02640c81d0107454081c8504d90284a002100000051080c04d18644006181150902004218070014800b1505000c29508607190f0507030400000010244d8038a010740c4c0d200507501c036011541801ca41e0604c80d4a070300d0f10580c0e10812000c0c0145c001a511a241125407440a010016003140e403039a0102e1a02005809400d803005030b080d17603045503038a240c0c20010003800b550200301000030412009406820503002d440440703504c252540c0d80401c00460f5542405104801c10703030003580907020044441035005c98140114255101c1b031074118907050055480c0c060031a8518010440302d00000b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754560152 1250 754558902 754558921
    0x3030613050603030d0e0c12030408100209060c010507080106080a09021f0207090e010606030f0614060c070810050403080f040b01050d0c1509211106031306050a020a020d17 76
    0x9a82c031820050599141841d4180c0c080b040b9107417998511059400382e170041c001400c040c0e4180d0481400d1200a50070030740740000550b55811480408080360340c01207880d000700e88902c001c1d00c18071140180244003030703c0d207400c0082000e0f10901c12140003804080100701181840d2061ba810160084c186032030104090080030300c2100200e84190461042c03900004408500c1c1c89101c0340105003a00102e141445c0000c010140c40070480444103103442c0010800c0f4802117505034a11a10054542944401038000e00f64200003480d1b105600900071202c00840104140c0d102a100720720030780381c2c0d40c3e0640f06c0380d620000e02c101c1124018072041600b00144080c2c13900c92020400346205514500c3e4441d201c0b01e074400c01d412442103182c0429642813061000d031414040154584043d1510041c03110220b44071606085ea400300c03142d01407000003020400c000720b15810104090b400103010b010a00b4243c418034025440144248010301036050b20045403445544200d4840494000030071158840382c401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754561402 1250 754560152 754560161
    0x31103061b092803061a0301020301140f06070803011203120209010c11030304090e0d032703140705011d010e010b03100b0a030b09071a090607060e1204030b160203030613 75
    0x1250404050f0b400d0031030000102d094a000078620819000c1400508081d203603030310340308045040b84664010300061000301c3d480031081d400360350100d50050800b1101400314030385104049024104e000d00200200b145214242600302d0a442a51390440c08590030031a40c04138001d103180540000c0600b602c28002c0381e00e551108150b090028240d03407400360b6550840c01200c004900041141c0c101a8141c498103425200b0045001a46803003036800b01030300d803181411b004400c1001420300c00100c1034445040c170500240c0b86980d074400b00810101034110810800c003100015129402d42c00e015003c00c00000602600a00d510050003c007150100301207001c3c00351022004840c0c000d01c1300e840010100d00c2001c0c4c071134002c050f480042c00900b805c101e50380c0c41081d50803040c4901c812003080030031640c0e180d020842e0785650308582c00103402411102c0e100c1c204000d200301444c6400021802100744640d8120040c05951800d035007240035040c41505907280c2c0000c50381c95920500c0301e500b02000140d00e420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754562652 1250 754561402 754561429
    0x50711010318030201060302090603060919062c0c01050c0a060b1503010b0a1e05030105101403090d030608060408030402061b010f0209100212032a04031103061b09 72
    0x18003082c641140c2c880010401d440410a6006039181c1c001001981020000240c00c002e090300508158540b002c5507a43e03c0c031120601c2003c104843d94524244900c90380202213144003050324040300d0b1925180c0b1804001e07481100a01401507104142c03c41d80038408440c1004258409400c0204c0180c540c04020b2000b12041c0f074020114210220503043d0082c02180600441810b9645401c1794010003042d5002c241c1c80d5040908403100544909500035050b40e044840c00c5642c5003e6030552001101e404903103040c0d41c800c240010083c030507a0007000c2102c4a200303c1955040000f07a5541d6200780e6a0002900e020700817280400100c0d015081210040c88030f091605e0843c10700c8210188143d084a00000407151101c1c0d002c50b030015649840c040c4400300054901c01092080b50303901e60402e0f188405004100400300180c41c0060746032094556002c0c0904c60441c05407500d99a042c511007811419040b40d10034040c81c0c00281e40c55408004040300c644e5600034050810941e0024000b03203110519 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754563902 1250 754562652 754562657
    0x203010204081c140a052b0e0705040e0303061c14060f060406050306070e010f1b120305100303024305041803020c0f1c1b060f05071101 60
    0x4408191603004010000c10040f444500310b202c5030f0400c00c000c050303103d003052401c03ca820030854038011070303406002d55000b01036403081004916403540d460000310f101c59502c444807030300744000703182010000300d07681c0115001500c00703024485150740b000b916444202c1c2d0762a8031008403039a4000d02d0310320306030310241c807441780c002c185d18102c01c141c03854030700341044801d80840e91000d010880325040500520009100c16402086103062800c009406003801c6203810b410070003000ea91041007481030400b803000401200c5480c3d11400103051421004261409072000f181c101408554005000301d0010212901a030140c59510021810f4038030609041c00640a02c280d0b1081d024000048008007a5a0380600d04403105001d10305418041541d031030000f9440380c405400c5682c00840d4001c50a00400d8004582c0d680302c00003e54001041c100c200900d100b480c1065818907c2000000800e4004000c030704007062040d40e507118011030380c05920803071350f40010700180310410000301c5841d0b0700800e0b1507050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754565152 1250 754563902 754563907
    0x8150a06030803090a02210a020409060225060b0a0503060406020d060504050c07050f0c010504050904140607051201050603040c030b0702010627060506030603060112060941120702030102 82
    0x2d8594500580098510398000d0b0420060b00c811881d200c000f400799002d880307000e6450003000074442504c03194a800080d015a445130002d900f04001541182e641c81c0a030908080550401010011181c40940381220900d00e07119001d2014a0422940030445000400500a6907603035920000a50441c100e002c1c1c0c403540321040440d10317540c0c90290622803c42c81f5035903074440f0007070b082c01c902e011480001c101c000c0d0442c040d15061039034000c088038140c500c166400103442c0ca99280c030180c0401e20341510b0005015210903c480c0a911a0040104071040750000d0312590300d030380400400e0f20041d24018411441802d04000142918a10541c08011800001501c55459002d103080000009040f0340f400c00d801040c440040c01e6208590140c80259085429860100c0200b540c410040c001e11a496040710700c841c0402207a41c200c8038404d60312608981110035a00e4224541000000401010802401c2d00903521321b9200700001c05410080000c0c070403421521000c200d44e03800514180c1c0c155408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754566402 1250 754565152 754565159
    0x18060e180a0f030f081b1902030d050a0b120106060507060c110a061b09120201080903040b0f09180403020c100e0d08030702060106090b03011a09090a0f0b0102030408150a06 76
    0x410440d8030b60364003d8450344000d95040c50001d20740c907401042040800005000d800c5440300f0320060b81c4070b85100d06528211400001c000b87d2a5005480900c0c2e08142000200440b0003440c1d00308100320300b0140e07840701101d02139151840c20b0300c00a018040003d1004e202d0351001c0342d01030300994080010b505250341d0b00040a003490b403e08040031002d880042e180d8100041e00c640019000000c1d884030700d010709070a801c1c000c007042038590031000a410441e50b030002c41c102050a10495009002c910f009607542e86a00c02c0d841126040403203103c2c070070660610b516040050b00d00e051881030f58194040d054a1041c86d042100b400040d111160401c00f09a0310400d00e0b440c0d85d998107030003d002d083c40070785925046200919065058002c01c1c20030800e800f08026004030758040d64151901224100221040d07040444018010100c441d0381c000c902005120030081584d0000c40d131102e1540307003800a02e141d02c006a07038030312940c840c09005c1d40c0620300c1d00d00c64164450019800c810610800305540f40e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754567652 1250 754566402 754566413
    0xa05070c0302030d0c020109090b0d120e03030a1107050603130222020c03090307150206010605090d02041e05010f0b0a120f2408010606050a050a0e0a06030618060e180a 74
    0x3138000501010420500100080d503070080e4000f80100761140301844007240c5d1601003480003a0544009044d514800906444540241941501b0f4007000c2c08503902c034000d1041c01054270540c01035014050064010102d820700b803402c00c580c0704000411482120401650a02450001900f00810082c3e03985e080c00300300c2c0c01c0c980001c00364841460700030742d2605240c208150421070135a011800810a09003078401e0642c02180241c1160428101140c88144200101d02c4040502308002e603c64644070000c501d80704000c0c0116010810000c2c10481680c0728426451030080ca4040c141d80210203014029603d0b1007180c0d025140ca443c0140410740c84410510700e001d40d00d42038031b003503028a9200c0710600d001c521400007600401d10380d8028400309140c0034001c0d01350703c04c900c19a81041400682030001c24002c82412004040180004410a50307481c0010010040c50284209100d0800d9040f41811521b0058009540100b00a600e56868402d02001c0ca4081090064000d00450302035001185 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754568902 1250 754567652 754567663
    0xa0f111909031707051506030c06030403090b03010e04060e010614040924060e0a0b1e010224090d1713143c060c09060408100b010f080106050a05070c030203 69
    0x4401045913881c0d26180c40c1950620170040e50544506814038204001d43d40c0014040c4021581540c40340d6481e100ea0034212032030f81c8607800c0712410a000100005114001280720381c40769010703400170454076905a1426083c2c807002d10490f143c1c481c252035011440d02d041d510221426102e5007620004494420801442c8400588002e085640d116001c0007914100c001c59988402d264000f001030707104040004109040d0494600700c013100c501a40c1d00c15900030406900c2c8071460038640c5101e2070114420f031084c000200c5069075640504c03000700300c07042e00a00d10000e00100c04541c0240075600d2503601f40034407480c6034007642d03121004180c00b82d40e80ba060213141d8070a1800c2900c00700c06050000d0341040b80d06040051a00204a07031a154035400e03010070020f0b0854201810f856a0f80140d10000704640241c1d04040110b000d000105946040c2e2036010000d01602a21007901545c1901006d80d00d61009100c0c01d000300d40100100c1c5001072041004004043c0301d1003203507600c1c075100d801103443c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754570152 1250 754568902 754568933
    0x30b04091a0c09121c09030308310c050406141e1f0f090e04081b03130e091e120703090e07050d06090204081b030703060c080a0f11190903 61
    0x5401001e440158005015550000d0100c51300301030f6049446d548e0700074070198000340071140300040d18940c042d5502c1110308500f8450f00d0aa0407040c1c0e4441800d00400260280c4a41441140ba04000003405580c15220280d200001084107000208100102d8440c0b100c0c5180290b0001944019450400075020030603002c038115651009029031880c0301510900c4190403c0300e40c41044401c101c0000e01800c115a000540700b204044600f000840103491350281c41c1007802d40d05a0802d02040c0304030f007020a0380c03040c1900011030703008280b4503007124500c6007100b06110303898100700c80349002089003100901075280322340303005880d044c0e9905500f0340407031051305c3c01c10000e40006140c0303c2000940c00344101038501030b5000c51a00b45001d1a40d90b94140e5592421800c80d4005d413003039000d94090145500440e0010818420a00103500041c05000e0840d1442c40303140c42d0911030243c200c564850140d2015154807400d02e0611204803031409003641c25500810022200008000281c40742e9110441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754571402 1250 754570152 754570189
    0x72007051309065c070611030a0902040f020c0c150705011506031a1315050a0902030403020d021b0603041412300a050405120a0e01030b04091a0c09 65
    0xf00c032440c20420000c00c0d070314444900000b0040c551800d071480d508004941ca0044043c0c12582c1e000603142a101510780310f2510a0014000b104002d1607102e660080c0c5d1185108a070100268953700880004038018102d07200c11a50000138055101d0500514207511183c40038041410050285d65060035a45100f42d03d191440c00aa4104800307034045c0250170001c011002040d800c036240c0400f140c0c80c40b080d1001e80f21b60039140d041008201d0045c100310740140c1000380110003580d450f404c00c5c10280d0301c203440c100c005100d15020480300c948081007044580c603480c4240e010241c4444100919900041c00640325410b0340c0801c884448401c000f00c0c0460392118078001d48498040c40c0c0b100c032080242c00c4c4444418400303402384c00c0000c1c80f440c0351a404400751200081540f03da040044c505400348951034941100010400e004c6500502e25059003a0244c0e4244010203221041c0825500781901c0180b20003035a80c40c01c044c1105296443d5488041400702c01d003800202000907109540c01c0001811 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754572652 1250 754571402 754571471
    0x80127080a0909020c0d0f08060306191e09020102070b0f030106140c01021b06101d090102090612010e010b090904033905010f0509070909051507200705130906 70
    0x50f081e0308110f20380307c002d0711428219a00c1c60810007294030340320010f2030701e04041b001140c840300b10303101940005561001c111814241080c41c010400040600300700aa01510a0100000348a140d0700115068101d200b10442d013564a880c40960710142d804010514418051181082c016424405410a080d84400c1407510320344111080741000800b81982d5184224810140450000740001000011511085207050382c0d4800d0030342d0081c0a0040c549a0000e40040c151140c2d0318600380380c1d416120813207218041a40c0c1e0303012010062240f0848030350804160320000e00868085c0c54140c0310b520441c070700e51341c0e1a822282c1c031b418421080300c02d060404201c0000c10003804400d10070380e52070004c880410416410114040d641d00d0005218060f64542c852040c1c508215040c45901031108082e5203601c01414014005402e05540c0e4034107040d06005480b040d07a4035800026031100b00c03440178162003110301c81407114001800100d14252101ea4031400032800c4905100001c6000149191035040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754573902 1250 754572652 754572673
    0x9071d0402041113060e130e100e0a020904030c1a070f020c120a0b0c120f040213090c05041808070302151302060a11010f090309080127080a0909020c 66
    0x104461450b90b88003451201400403190100c2d00346640e4060b81c3d0542040400041082e0000721f01c6e006804000c0c800e517080490b1a0340d0104002495401c90340c00001c2402441e8415580d241c1d1200c10b580082d601c03a11590118012134042c840c1c89800314050809041c4100d41c020715803030841415651100010101e4404828480e03060210744100380b4200d0b41d6100003103c0921a642c3c03901000700140130940b5040201da036090b1003008403aa00d40c1015810412460a502140c00081c000c40d401da0007224502e482d10803c0466109155010b0303406041a00c060742850244030041100820040a900c000d40300000840e0140f40904208c6110794024a28200a001c940c603207420040c0031109903502c03921028005070360720029203004002500d000740c038013084808d0741400342c01010f0a1803c9649403043c1c120a25074030140c0c0500b9200d07801c0080c0101300704080000d82400f00c222681c2405840580f5103030000b00404003c0214851501e4001c06058039000742c207049a200091032001580048000c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754575152 1250 754573902 754573909
    0x70e04230601021603051e100515131e050c121f1d0a050c070218060907090506041703040b0d020c0606090f0621070902070b090105060105040e09071d0402 68
    0x40203501d80c806000304c0719030b14569a01c0e6481c038120201001c03450090044200012082003298861704e21804284034a08000114210b002400900c00d070054040c0040102604003c1c02a0140a0416004000d41705504101d40c001020050801c81c005001041000c1011400224040c040e00e0440c250b6003903080c0507801023030300624682c002a06c0100c840700070303282407009607980c2c1e03800285640080f480c3d82c0e410420300c0a0303120354000294801292030003441200d40c01034255209400549030285a0f45445000b522000351070b02c07903964400c100f04005d0043e00b14810b100c3d00780e2444c040407241170546400304804150805208039006c0c550101c0e400821050030410650040c01c2624500740034100700150306040003008155038040d00780340c1603c000300840301700926038a0480f5000d0312030050f100c5080f800650b0019805546121482d00400ca58403418131945000314016190a4989407038447c003481c040b01c1c02000c4a40c94010300c0320000340d81601105a103044e10304003042c12018505031040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754576402 1250 754575152 754575163
    0x1b03020328050703050702130c0e030f19020d0f0c06081005040606200a120c030201050105040501080307200a030c030b0f04080d0e10020a0c0c06050a08070e0423060102 74
    0x240c1c09190310040c901980d400400700c0e0900d54052800342d81d10a0240046004c0100d03000d1120080340c9005105200740398010b8031094418003c900b501c011140030410b0aa80c0c00828071040b0724500d8294612005142c01401294802d12070011004401e401d17440307013016500310f030303109402260703c2108100782c000082405c1009881c4c1128108a00303810103200502000380d60001c5e055042c4511482d544000702040400745644c1d00101c409120201c0c40c500400d11000c940d81100990700b0400042258501806018141e030308110003141462190b4461074002c07502d0329003044140c0b142e00c0322400d00e500d46c248840f021714040c2d29a901c1207031941c034124003441401071240d607a00340d15100303101c0040c804030f00b112a8401c0201d408182035059001e101d06100c07903000c101001500c005800c0101caa040007102e00e000d40141030000586564160a8a86110b04014100041d5600000035800c0d805000c98031a0020003400000d03102021980702c41c1e44852484503520b914007003204108141d0b074104603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754577652 1250 754576402 754576447
    0x180e0702071208030604020304020f0d0821010806045006100504020d0b0a090e19050c100c050604031e021b100507021c0c090c02100c1b030203 63
    0x41058030b0710455100c1203090300001d8403d91242d50004081400d554848680c424009e0000300703603125032100d44c50301011951003401150000d038444030030216218100d2240758120340d038100192405565503619442d041c210204000d102c5010740380d20b014048441c0c56010841813820401001140360305640c4c0d40c3c1d002405a4806090380700408100310002070b00d01540441d0010b603009607c90303110083c0c28010384070350a013240d00082601c40000301c401480c0c01c05540601c45200340ca182c0e09066100c0d9280240380b600c0a005d90740f00c600015160306164910301314200d103501e01000d40c0c0306255142820700d1800c0d1010380000e250340c4005c4010100d0300540a030140490300041c8400200d075a40790010403500703560b00f4850801c448403c10024010400c0790f1805a005007520707083e41e0600e200a4540c425040c1c287c03200000000b01044c3d600032840358800350600c0780c00030102c40c2c3d4802d074454050141d18094004000c1074504000d203203150041200340c9503200c4c1e0061611080310041c1400725034607082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754578902 1250 754577652 754577669
    0x90506040603031d0604180b040b0105040b030417040320090105010221030c040509040c08070608040c0905250509150a170718030308010816050306010b0703180e070207 74
    0x4104000198100800e260081d14041000e6904480078000560500482d40900b87c4100e0748041410303005540d03440140403501c201d4040002120b40d100449141c0100d0141c04003a071800c1011801291403910f030340c64060740c1008124030b003607241c1d55148007000f850f1006140c1241781828510040ca403c0c5499405410213100800814101e007410390b0341c44080307080e1600c601c0e00c0080862541c84501040301d002d0712000d410310600303007428070380501d04000d240b180e4241d500031580f0100c2e030240702c0c1c985c09010b80e8000c000001414101120b0100811000d050301511f41d91040401903000040c0e05255114051030711381c0c5403124201020702115400c41004041e100108008500320b1039040761048103070400c00761041c3c090369600c4105403500c0c01c1d69407008444601c2600c0002c20140c1c040a51810303a0350150541c6d4100707054004000b81d8400f00d00a6a03415040000180105060240075211081c00781c64000d581e180c208414100320070094000c044041840020000802c1e01044a90010300d00e0a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754580152 1250 754578902 754578911
    0x1050f041104180b12060105010f080601020c010e0f0306240603091209011107030c03060605121e010216080a0f051c090201050403080309060106030c020a0c15111609050604 76
    0x105030403240340c03045008034a00c860500c1011a0a090107030f1280030b011310080c0c07440542c116a20502542c0345801d1141038009072108421031181d81c03251003154010201030300103150030515100156404031400034103581103c042644812240c0c6c042240c54024600c1034841c040008042d41c00e041c4000610300964042d5400304248010b011002031411b070380c3c9216200e4680c0302c041040040703e01c09140d0840c4e501c48c1c0f00f410404805c3c01a440040e80c01c4a2203142c0c10408940c0ea441070151446044810f50b03d1900105880b020800004510403c0340c80240001443c1c400301d010320a8000c001074801792a05540450200a07030354014550070741144250508a050404150f0208000362440d17a030110081c0e00d5155480459000f40306440107154801003d6807079182031070301665a41c01c00d1046a0029003081c2c080c891090010440ca02055040428010000d00300800036194100701c07100f0b88204044500700c1842c422040c0302c9800800004880000380e20700e412001d90543d14007610f0a441603140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754581402 1250 754580152 754580171
    0xa0f080d1e0e07030b0f0c0f0c060603060105040501060509041d07030c03050d180b0f1b0a03030b0a0b07061503060608030d0c0e0a051002100219120e0d0804080c07060801050f04 78
    0x45c00003a070301c0000380103140001d0703a440400341e8543c095802100c02192000c100e001c048e030408030748503105100503401c4901c0d9030390b82d070100025100207118007004030310f0400080803241415040348240020088c681007600d0b00064000d49014003641c01a03c449103200424010818184100f0004559a14000044840420013480b000359184500c0c0b041c91800200240211200001c4c2d44180c5080612002d05004800c0701548540050100310002460041440303150f290501c0c000e82614041021182800c229542c2c1500425070b1141852469004102c0080020094011500900b82c05c00142d5203d0b1700440080c0103603000700540009020081d46c148100c0d4030303007400d40011250101c510f5400d00300e40010507410048000d99084080b400003d49888944c0c00c1c45000c20660b0907513460600c1d10352040446821a0911240c4091541040c0b890805e1940b003200d906400901403982d50349018900401d1925048603540110041003014004000d60f14101d55440844841500c0500c1107d40c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754582652 1250 754581402 754581413
    0x70206030c2238032d2e1823091608070b09010c03051209160812070308041704030c0e130c06030f06180203060906030f0a0f080d1e0e0703 61
    0xf0007000700c0c0a40c0d20b00c5c078001d142141c1048410020f0854480401d44074100008122200720a08032495820285222016111941861840200c4001c02c0c155003005940000f59405864482180f48568000d10501314103600d19049040c0610b040c07000800700c1c1c2d00300c0440c0c1a03d064983c1d000300402c1e0080b0000300b0034543c2407003c50b51502400d207800d80300081d40d0710b0265901d0080707200c074140c04074114040220500c0c4c0010030011851000c1484114240d9981086580d80e40448404c3c50b0600d0920100d0000390203420890303085403107801807035001d030361030030900039990026401074414840111040149804044030700e508107900018504441b51141c54030005d5410f94829102055680d81230300c408101250b0152015140060454002c40880c0300408003a41066440c1c510641403070b40814001c1c03030b0025004030302421000140c503520602e52500780c50902000000e44510004010b0080000d800307100b1282c03010081092031001e80c0d0307100030700f2044801503140e0581581c003011040c4003064 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754583902 1250 754582652 754582657
    0xa18020c060f040b0f0a0f0f060509100605120402030f0d0201230c07030f030f0609090501050114090f0a0b040509011d0708190c0504051317070206030c2238 69
    0x5c1c0801c1075a02c46d844010802004240e004200e49035249080c004101ea0516038128908031007040ba000102a2601c150400d624100b620540001c52030400c900c41101c3e000c841c1c0380d030740980002d040c3c039002380ba0304070998200904a5443c0006075510b02085512084d010740044d0070f10326032048042c640c80d002600855520134260040c060054000080748032900ca50056500a40407242c244450b503550210312001d04003020084445500303050020a5110b00fa1501c82e80004008186d41802c0e110344071010310f15034016012402050301c84481d54007030740307031800b400c0e0007590320400008840244ac0440c058980b1821440025a004040b003042064130005001c01152041c00ca9115605418036088017095030030f9104c0303500f0a081104200e011610360b541c0c3d944190080b01c5090325960000301d0b0001078494100c000b54005030034004078983d0072441d4042c0c080050402d40340a50102814485005040c60b5408070700b081c00d604d0f101d00403800391480b0400b443c2955030f8488030f002808051076080c60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754585152 1250 754583902 754583911
    0xd0804030f0315081623011403070302090904080a08130309091a0a0602010222120825060608160e010e190507080601030b0d0b01090b0a18020c060f040b 67
    0xd0384903841030300d00000c580c83d800002d2501d403040751900030148054009005551054900e210202d0007590003880e80c00f0340b0016407400581d91160280b5401c2c1c2c0120050300041c01c0001016400c0c00280b203580c44008450740524000e2040c2c54481c40700040c01090350100800e10038015042d41e0035680001c1d0000218030503035110a40100328809031340104215606001000b640c000d4040100042032a0194014401540540916006200881c0c0e941583c03201500c03401400c0c814842111002c01c024101070241e420a1364045c415000b02021714100c0450b016506844256a54004002d0254104001d03000408c401c7c40c5049054544002c40c0c2c2c641780144039440d0001d00540004074400010105145005d2021030708000c941098800100501c000f200c1e5907002c01d02d0041c0301d000318a8841a51203a96500003a44111603017000144000741c400040480d401400384040403e401183c500c101c200308107102e10060f29079016004041ca400c0700982084451300341e010038031012800450180758407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754586402 1250 754585152 754585157
    0x12031a0922060b01030612240905010e060f130c090507050702030d02163201020705060f0909010512060a09020a15020606090109112b0c050301080d0804030f 69
    0x325529000c01402100442050845400000c8030071000c0110070761248000450070f980400000d078441c403208004815488000d05000c1441d4204030784c41d90880d52142201c035004002250010785a41c6039030a491003c03905203141e800220400c42104406415503502020003814550003124039201c1c1c0340603a02038015a0041c0d500e0344006a00d0034003070421140d11a50180854003020540500252285a0790801503a919044032000444182c1c0340300990800c811494400540c0e030305000c40386880140c62403004e041d4051400006115900c086c003425034000d51400030340d5160000400c0100155058101034840c4c0c0c40e8081020720352100080c1981c0c00400444d000a002c1c0103400026515002d0f588040200303c2a140c480500c80d902181c03d80c009c14055030440d0669032078550882c00d03500402104003100d02c040c0030003203121604200441c000d50b00d0903140501d45502d21520360544488243c1c03200822000001040480d40401405002c1e180a10f0f1820190130f20f070354000c20204e40130411208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754587652 1250 754586402 754586419
    0x303080901153b160e0f1e0109050411040812070c150509030102040b040e2a0d060b0432150d020c010501080c1009030c060f0908010c090312031a 64
    0xf400c02141c91441e03100c00482d000480714940300e440904c2a02e07004140d84001400c882d50f044050906080c008014180140542c820006403400c03003c288512070800c50401c51200400111602c2c3c611800288a484142041e034139800c02c41100d00d0071400604244d144181008400045003c0344410400d50711001e9462502106061048609008998003e5415440020f0008020410000800481d15109100e0b0a695034000e6011440c40602132200700c2900c00d15840c414211a200051000b083c01500000d48543ca030301c1d100c41c10360083d0300b000e0600001c100c50042866a904c0c103070904044032042d9080d0542920300401c2d8181c0b41151800c07055003005c01d40881030700b020303019501d000c170011008001c43c0d03075140d00c52551003407000407513805007800b0001c07860054171652606080d2030700061002c3c0e80c607240940481c0d07010048100041006900d0401141c1d13064280500b2460006603511450018210300341042010f48420b40101031519200b17103044004141c100101082c0c030200da6546 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754588902 1250 754587652 754587719
    0x1e0604200a0801060e043305060613260609191707060501050a0b120c0a020a1208010801060609140d05030919080d03020304170d0b0a030308090115 65
    0x5804801d250444901542070400c00b1071201c0310361505610860107490404180c1414090056840b43c0340e1314041c0c900751641080c228501429042242c1010000d80101d01c0c080080b0794044174003000740c00509413040b102001448400d401c02c00d0075079034042c00000c0e1031030b4100000b04e5582d84100340446106401d00784800c43c103015240b425402040e604207652036070780d42d0310f24060000b8102402080d104816111010a244215a080d1080c1c04070612088542c0c2d1990b480d085901d0700220407643c214840c03803058000150124481640d030304150b8036603000950501c0c1200b425141d040e00008200b111084080002d80507904600c020540140d0301c5080f1070400d41032141c00c40c4101001d040e000401800b03d050707002000c1c60818200c604610565802c000101001c5003603200c207650107013203c9181c640d90088400340c140201044455840c00043c11030f9020082540c03400103034420f4001c51081010091b40132000e0141c490300c7c194444100740c1c214142588034030741030240c20406161003100240072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754590152 1250 754588902 754588909
    0x609060106081f0e061212090118030f050a0b09060f040f061409250605120a0605130207030e0103050c1e0c072c100306050702011d1e060420 62
    0x410481c0700c2c00f403008092900c034035034106110001c1d1440d60003080c2c440b071700300c42100f03002c01c00c03640f80c01081000320b1034038190000450b80c81402d410350f51240f00c0d0b4500000b00160406814885403071145018141c09015804c2ca8100d241c0010015507142e00a40d003007000480030381c0400d17980550f04c800c21584104050a08000400013480142010041d4000b8054200d4000036080324030035010201703042590b080325200e141c0c0c0180d0f1280c000400e10611103828400d0b06071610580c0582003020000d601d5075214000b40302031640000280c40503a00290b00750034141e012500d0b0084890a0905100c18107101c1d0050820b4415030241c50508460100840c801541d044125010034070340741d04545209446041328030b01450407007030725100c0c61080383c1c183c901e040343c00f1005480740e04542505011185540c1320b100c081c00009211000319581c50092241c2c000002080d080c402c21018002d00e10f0280b884050087c1081003411100e0a078058800c0000068900b007944080548a103010141ca1003541c012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754591402 1250 754590152 754590181
    0xf0103020424080f0d020f030301052403011e0801091203050c040302370b19050408061f0603060311060c0106050a15090b070f11060904110c0f060906010608 69
    0x90300c001848402d40015070810016115000b41003c2c0c05a070380070000500242d0f6503e2201c8810f29840d001480100003500d8105501c81117503200245190020400c1c160b550460b9100b41c00031100d6150345a00e9940c1510b04030a101c3c0035209610003041000780390744a0385840b01089007803808268490f000501280030020940d002540d0262805d452040411800040c0106440600000304081ca0041b56816900c13420141102c030507070b0425241210036900c4030b0310890000d40e901c0500c90704010004402d041007040ca80304d1410300782c0d039502011295550340e1801c042a84400101030910070b0a1011640081071300c07101c003500300c0c0c6155607007081140050260029038002d550040d0402000195048464140c07950341086a594583c5035864603601941c40c01142c5000d44104805030b04200045c06810340c07880011030080c550760916071090002000c1c0d40450b140520320b040c012a484103413060030040c800302e191030140034000324500b100070f465803504140309d14000c02413114003142129041484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754592652 1250 754591402 754591451
    0x2a031103070311100c0f0e0d0b0c091302090a0506030405010e0102070302160f060813050c0618040506030114040f060905150f09160605090f18060114030f01030204 72
    0x40da500c0718070314280604100c00000c3c04a100740903000c00d045200d9400d109401c0564030b44e441d1250041c0f818a02101c2e01d250500300581c0005240c00c6004c0401d01c0070041c41e02c07402d0700030fa080703548050780b20074400c0c1c414110260542c254014000c20440b03941d01240d003001d40308141c80c0a902ca40d500d003826409400c4d559001c65555100241c918103143d8080bc0755200112a00780e039010b181d03542d400b8490b00000511508001a0130f00003c5040c1c40022603c030030005020340c08580c1e04070003040002d541d5500c5140e40c400780b06d410740214801030906d8016154001000c400070800c2e500d4101e0a04021307240200001c2c003600781000314a0400189510004090b9040802c60b2040400043c83d6506c0300c1066652000e046007100000d02c40441c0098085501d5800d4443c1d841c096240c0b6006690507040080c4e0190b021101c0c540424445e25107071495449090411640055401c065001404200c1b011039038010000c820810000d990f4228040705046070b40c1601c000615a84282103813240c00c41c000c0d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754593902 1250 754592652 754592687
    0xb06150708031006091a0301050402070302030c0d021006060e100f21050a060503061b0c150a0f060503071d060d1a07020f0312040f1707120206072a03 66
    0x414810541c41d030b200302409491154803410381054542c400301d0546c1e4003009210710610420401801241000c1c4c001d4841c0324882d00407130341810482e4400d1800c10315441004c60042e8400011089608601d0003030f40c006007100d04101c1d00300d0715014081600005110251000e00120324031442010740300e038001c1d100c100c03a002242d258581d0414a80e40c05040309803280c84029040c8a008070b00307490003140081c024034012501c9282007018002c07501150304810310b1441580034290003580703405240b0107640c1c07242c4800e9a001580e4414003440c84211101900194040d900c105030070302820000803c07072141d032800241d107119190b5410002a40e030802c980c00c02085250541e10170250101c80d4108980110442d401350340315152401c240315683d000302ca02c40070100010b10081004503118210002085004010040207401c582e19100f41e50390007550203da01c25a42800641015418040e103904001d407482c0068410420203068000210401c0c0807000c0d498140e099041010702824022113440e0110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754595152 1250 754593902 754593907
    0x80703050403051e120405030d03110d0f141f090e0106090e0c031050100501080103020108010303050c071502010c02060a09080403030c060f0203240103090b06150708 73
    0x401c50110788003a44103c103100c0d200e441034805caa48840e6080d2030640740050002e183c0c90b4642c00080b009015121080040040b00700843c103e40226406100011030b030400c000b041c10104103228000c3c0d90001402c03516210182942d408a10703544070401c001b1641e1004000c60461a1400007500610041d8080e0b03204619210304800302c100c006c03c1100e1140b9084043d80d0020b0f08191910040e5201c080060f400706641200c10000c4107031000000c0c0c0802c00c0880c149100307500080b0204054a01c2d02c0702007603a003642c0b80800c1204c4004002c1100a80400e107001c42135035155070b002a0910006000007018041701051503400340303004004050003081340c01180700e141241580040d00170310038610600300501901e000501500114029550510391001a01c0e00c0e01d841c58408491400551408403001070301c40d03020601d441c046001540c000c42c8025041e00e40c0e0189000c0010b41c406045d281141803606107012200410301c268285503101d0025900a01d0745e00e000182d200030b03441170400051582001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754596402 1250 754595152 754595173
    0x70f0e0609040f03350a050105010819060b1308120a080c030402041515020f03070f031412100e0105120d0e01120f02090f061206040b04180f03140a02070308070305040305 75
    0x1007080c4800d4014100004c1291b02c0325210308043c2c603002d0082ea401b0507164800304c4c03d1840c140b0810840c0d4003000c1c00015015803521a5005039038489901e82030b0ba0810302c10103000d5104140724685100c40030841c85407030107101c400041c042c80e00080100e101c3c0c0c03002000007001d5446a40100044041c001c03908074040b502c2d50007906a5043c1d0040c03001c018030070141d00504810001044442042d089243c07080c1c101541c0d68220f4241c01e999032031401101091200103001071510a00b6806000c0800a5200c46400c05840d03400d000d10583c03240d0303c00c18100719211564400403460011080443c601107004001c07100043c0c070180702e00440ca6001e146060342d00e086c54003050303002e0002040d04444e00245030880343c0401420f80aa049420890422030b408100c143c40c09601c2800c0c0c0d070001802c00f01c1e1881c44905444200c2042d200c081d078006844110100402da4003144c101461542203100074103285800c1e10007941c03000c183c08000c0914100190a905150059041d03400666005d401c507081d090a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754597652 1250 754596402 754596467
    0xb041e050f0d08070314131a04030f1407030e09070207051203030a052505090f0a15140c1e120a1d060f030a0504060902040509070f0e0609040f03 64
    0x4950315070030002040f540100e41840c0c824082c080c48040340450a1080740c5510503421618084204200c512120082c0541d425a42c0e01d945144158000d13100e2500344003400780090a11801051030609a0b03008200300300001e600007200ca1541081030b54911515681c01409a01e402d02c40e4000940c8013149040600c40c90380000019481062000014020713902c0384000000c0b800115000354400001040c191030002c0c2c403680141c039502000070148086405040c0c08034503465407a8110038219402c09205240054120724042000c0c3d03205480145040b0044509584986140c51072064411806c5d1075011008000c2008000b0400f40d205581d9403042c80381405010f40e036400000301c079680340740484500286445c4043c1e80004101c8804145141e4416800c00b0007000002c0c07088402c00e658034150400b503241e501c41c039407080d03d4071002003c1142c00d200300048039100c43c2c1c1c0302042080441c4204846a190002c0313003500581c2c00041c0719201b0095103826148540380e40d4100c00c5420320815140d10004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754598902 1250 754597652 754597663
    0x8030d020715090302120304030c021302120601020601030210051305060c1c111018050109110316030203030a2d021b040c0e0616080c030a090807030b041e050f 70
    0x510512091100c942050b2407401603400718403010340540c102002070180039283c0e100641c0d000f44645445502da002c42d0340003d04594115001c00c000c035502141c0c0800307140c02036484503040b40007400108180d40c99039000980c0d522a40f1000020800081600c0d03030345601d501421000b03404001c103010b45810307004900c103a44000720300318604509111900355030814024014070075414608009010314140b00018400a01040c81d5103011344004007070b42a0100f0000c0c850206614071402045030001c4882003010300d490190307504040183c41001003000180d80000071215104120305000d039106161500540c40718450001144011000c8440c0103007156001c219943c582c40220000b45005440c1d13070a200c125144141e2080101d0000304801d605c900d8000080c5c1040200a51110019103250b95588807035040071982c4804c1794008941c40b00c4040c2c00004100c0904506001410071a196407114449040040c00203010064022081c54248440c0e43d41c0f06815a08034007115680031408600c10354a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754600152 1250 754598902 754598917
    0xc1d0117101b0905010c0b0105061303022707050c060115020304030c06080a1d03033d03170310060e1305070818060601021f02070c030507081219110708030d02 70
    0xc04820700460a503010790110840e0139081f109241c5507a08103418400a640100c051041c00c0c1c544140020050340d9045003202c45901c4038486105d1403100e4407008203580d1000d004d03803050010a1010f58400e1b8400035110b411107540d1320301001c4001400398181d00710b00c62600301074103050340309002050654000001c68007441c07032000100b10003038801c1803045030a00c20329940d50581d081000070604510041860440072010040c0c905500d01d441c000942035034214100042d0f04856540d410018000c03a207050003500059214941d14501c4c142052510140c043d01030a020700800421160550320707050300c40600341000380c80400a0f801c00120240000d81d080720b1488036031500038030003090308401203480c901450068004100e9030300c041074647c43c400f0a4801c01500d80da030a100004c0800c61102141e0003c0d80030f44c01070074056080c0b0442d1801c0007200f04820031000b03002c00900e0590784540b4040705000070300b0320703058a0017132062280b2030802829602c6851607100c0801c3c0041c45003185d50007440c0f034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754601402 1250 754600152 754600157
    0x110a050a020d02160e100e01080a05010b0609062502090a0506120a150207030302090d0b090d09060c11060c1615030b2112160c1d0117101b 61
    0x501680031080b680c1d1132950100f09680e00c0242010081c0110511890f0f03000079010484504454517418072050040742640a041941e22400f407480c14071030288118280c2801c16120719140244440103d00c00c0e101d12200c41d086407642c2480c4071003c01030580d207410426402461414641007007800d0201a02d010340c1c0c01803003985005007030352a07800000741c140706a5038400b50202902c0550701d11900250000721060b41415000c0096400d140d6540c01056510343c031a6000c1101da0030000b00c802d140c0b91080e11160207000c5204030520806401442c0b60030803684c8580c0040007440190f021a05e603004003a402d40207449403800d40100c9822407008401a1415503140d070780c040c03014110440c240c40324082125000002403001800c15040c80102c0c444c880082011a84110141645099140d200c4c4102041a4085000440400240d029040000c0180141201941040c0c104550f0b44183c18404c29080d081210114442c0c07840c140100c4204070324441040002d10340554a03440c2d0348010303c040200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754602652 1250 754601402 754601413
    0xa0515090103080c0705060d020a02060c040b090d020d020409060c11010c05180d080d0609060512030a20120c0724030216020604121a011206050a110a050a02 69
    0x66550145a8400010000500e1031200381d1941d103540400354005000000c00e07004240c0007003601d4a03100c005294407801c9650040e521070684034024201000901181240c94080100300590780d010f109a40111100b02c500c41040700d070314400207200e001e507021b0013500941410618030901419a103d080202100c0e11170008043d59640c1003400c83c1c101000303c9011038014880316221240c513039281e259220010300000d8035400c058a80410680002814901a44d10b40109100403000c90144000602094541c00380c034140e11304903917880b4040c84c0041400c0080300b074020502103c1c0f03480c448002041600660b000401842485207503580b0916803000d10384108140040d40420207a007040e10b0084125110040b421814000c4005c1d41c00881c007071040b09044010507003d82d850394010401440610341c0c2040c25101c0d45007070ac801d4820f034550780102007a60001001801d0150030300314440d81d8001030005d16590b800c1c1c2c0c040c2c001e114100c102c00310880e01164501d04650444024443c00d8001d408452 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754603902 1250 754602652 754602661
    0x8060a0605031f050c04030515010602011a09070e220204031704050a0312031512050f0a05060c0f0d090f050715020d0c11030f0c100c0b01050d03120509060a05 70
    0x1540c0e650103a030390b80f01c440951031100956400c0d80c0c0c002c0c0d8000002103489890282d99031203847c034008900c0f9181c5501c0703401200400c21950240b250b60000e200514410314101150800503c62220040078401800090010f464032070703650f100e40c001c07100c0002c4444040e83c0a0400460000d4205010855150b1080e00410401c500610183c80894500a02c1680b00a042d9550010095120280f403020325448010b41c10f07407008024000790140400c00d80014119020781085c516020ba0b030001ca03c241d402c1140000301141c03012409584c490f448071f400d41c0c1d0b070701085a605100340c81800c0b50020802c0c030305200e550030800050250022240101c084803041515801700ba080d940214a180016078001c1c00a0007aa50084a200004601550590490034104130110303041110400814071190400c0361031100500e13050b054003070441103910341106103009a50303481e0500030040c0103030345c0b00c3c0d003045661108042c4240441a1010f81c44d02080c01241003041100350b4945050f030b0700003409403c3c000000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754605152 1250 754603902 754603909
    0x609051b060910052203060b1503070f180f0305060717190c050c0f0c040e030c1e0a05150105030d030506030c0904020111030f120a18082208060a0605 66
    0x2c0b9041c090040030000704109100301903940f0340c000006041000d1703807074020181c1c0000da07000403001540100d4011850b0b582c50b0040001d4803000360b214800c4c200060040c42606940003034038201c04070540c01e20040c42c0480039000d900c0d102e400e50000343e2004610b4000320800901242260040f40a0786440c0e40004500b03003c030000481c12914520034040b507480d038000035a4150810038808000b41006860721560545150030010400400701c065408a100c0766480d082500c511b0300c61080189c06142400310850070203445100c03030850300a10200104d030900303090500303000640c0026030001c100c4a5010ba0b00031420005102445558407a0003040c503c410654082c2c040e440c418800280036010a1a07140c042100654010b003003a4100702d5600052041407100b080200440d1103010300c21501e030446105107107048003006000c000020305120710416000d03070768003000100da80d00036551610b07603180e0901c0000300c2c1e801d50304041070f40fa104035001440d500080345ea1405403880032014010580c0341e9060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754606402 1250 754605152 754605157
    0x70302012412150906020406051806031e31120903080a03050411030d03020c19020307061115010b0a020105100b0d020f161208071403010e0606070609051b06 69
    0x3900110080e4030510400911a00f02c0c07081c14410300c5100003449081c0b030b19403000700e8120b5005030380824000030b4410300078482d04140d200b020344d0480b4994038500d00542c4000801c0c5440d07110b415094402c2001c00e1b0907a8061002080c00d11041c10f900c00450004a80c000e03001942c06001e40e21100326510501c42c6501c01c0d1540c400342d90308051114078198074184200c2c010100104155020140c0e4946500a1f95040c00742c0002e5100c0da0754056250500c0d03110f201c0c14440d01c500c0b002000104598440d00503200411958201e80352414030f401c100c6003000d18242071001c8101c0603000c0040400020a0010f6268041c0c05c00040a50080007581d95051140020410b98000d4000c045414002d600c09100c058000b0210140105001d0342001d401410801451142e42c01c00c481115480c5103044d0150b9000c0440b6031f12048900c6d00d0507100d04403592101480c03006000300704944000300c0000b8100d031100320480f0040759000d00200311895041c10700300d072501c499a1903450280070141000d86549400d00c00d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754607652 1250 754606402 754606409
    0x30613140607050406051831060e011421030406091e03060b04020d0f140c040b120601030e2401081204090b0d0b0a0e070911070201080c040801020703020124 69
    0x4415241c1828100b081d6455000300580e8603490f1424006007501d61108c901200340c400341c00020074044085282c1e00803070882c4000c100d1440754601034040196100015283d03046441104943c03020250300004240c0325070703a1100741c3c14810501c1703400c1403070408000001c00486110f540c9000030244c881c024031780040b20000304030211141c00e04040c00881c00540c003405003118002c0c401840e0806140008050350a41d841080c6504d1791030340d80c000c180c0c0c01c504042e984810f0461800c0c2c030f4542082074900090203583d5900016510140c0001c603107034001e61050b600602c0c901e0854120001c140c40c1c40884005213a14080382d15142c400001b40c01e100051100a41404621308a042c02c0c200b000040003050400803030b0764011040641240800c1d81603c6480c0a034000310b201080011140e000740340b4001140c0c2c89100406d2910601d83c241c0301c10107064038041a0b0910708190175465841d4184524041c6810800311035100284040030182c0551040a5241d09a8003070780c07400e90054105502a038040c072 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754608902 1250 754607652 754607657
    0x50c010305060f01081f0806040c14030a08130b07050c040608013c182105030a051015020f01060e0405070e071b080c2e0903020c030613140607 63
    0x16403e01d60f0b44c090760f10644d10034040102d81885100d502c0790307290401042d0788100900c0e088201400240807c1d111203402902d142d10f4541031014010012039900d0844c00c0010b4000a4046010416142c1d600540d20080042100342c0b600c540760ba040142e203684910f10b2891081e842d04100003403010040c024250808000b0800344030303940c0d001307103120150204e00103030a07a0480007580e043c110300a14400e55000c160940c0040880e0032440c544005050307010204102001826003a02c016a03520500b104d600920014000c9502d84030b051481700555000d030466200461003038500e445603075000600e84406281d20009000442d9100c1e04400c10f20701c1a600602a03402801c014894010003c4d490344d0030280c1032402d04c00c42400480b1642041c00141011190f01c100003601e840300480403c10394080081a605185505484e078422180841500b110004155215403036001494000d024040c0300250150aa5929140c015084d03180c00901040c01c1340c458000701c1ea2400646400903100c0e20951594 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754610152 1250 754608902 754608919
    0x190e0a020609010309020315101a090a0b1b0601032609060d0209030a120309030f030c0e041a0a0305010c08160c17040b0d06081e070e220b04050c01030506 68
    0x14011800f8041400090f87c0600c101d1214070000440800320621620740b190143c1030301400c05450140130101d912101d02403000510561806540c0c4002000858480c240103903a40c081480d88115a000d05c1c0c1c03500c0015019200c0004284070150700f141804d4041400d001e42410850402445a80102007006400003000d020b503e860280c03d60080c180341c00002c0c1116030601d10741e551310380a034000a0020000a8850743c2c1801007542101c0608040c3e1309505050040c3c0340b01d080010160040012514400c94480003540c0040220300c2e046000028054a071030360725900c80c18418040d120003154440014200d100143d004107001c500c0c00715030071031a5984801000242ca4140e18440f0840b0b403400c3c05601000300042501500c0003d01486007611404640c0d54600810141440501f00004014400c034a6122400410116251090f42e0b0003201c0c101c4107844110000e040030f00b6001440404e070505201074400c3c0301051401611540c030500880300440050b0004509403907050745c0094010009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754611402 1250 754610152 754610167
    0x1060803040b1b19050c041a011b030302040b0a03061d061c0302010b090a05181c030e0c121614090a18020a060f0e0607031710030803190e0a0206 64
    0x10120f04160703005070f00045031006210110a154506803050341102c0c59401501041c0307143c00c103030091854090560f0040480900b0440018041d06011b4182c2c04060104140c2e00c0e04050103139041d1005400c01c001c540b52124422400600101220301402092480100c0c0071f00c0b10396000d81055110b20000f0341424038501d20180e00d65840e5080d10030440c1955240c0c030740040d140c0c440d860094800c00b482e45003c2614285000c5038410300d05048035070f61b600d400c2045440c094121200e00c0c021040000e140000d802e06484401e00c1c00d21203031080003540915a01e0b50350310341c0b850004041c101c902034050300483c00b6544080c282181c2a142c4911900140d01d080054004000d5078410300040d10340c058500c580c40c0003a0b0001d04004d0b02508642e000c50400d02a50138851350280402c1d03202c25091704d040c0d10300b08040d200030301082d1050f50700304c1c510340710440090740e242091100d20000f10303031048003151a4200b84800080c0c2280c0c16007890400c629080c07940104490003e01c03802234540192880b40303026034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754612652 1250 754611402 754611427
    0x41b12150b0f1b01021224100c0201020a08160c0b03060a151b0b07030609020705032208030c03090111160b0a0e03060c041505032e0b16030201060803040b 68
    0x121207110300f044581503031000d145402e000602541d00e483c1411a0140350008aa00d4807011240d80401d090500007691009034448058880c0142c07030b13a040c0828000c2440c030040340380079281c00d00103110304401300e1962a540624030b110084144502c02190009881b0095001d6500045070441d82c06421114100410000b42c45038050b40e6003540740486203420301400c4e41e07850304600c001c01c41d0043c0004080100c569818030030040a803805400c25442c1184035100c4640c0c9024500b00d0f00c400400303404208a281d4030381407800e402060b0b105c0503245c80320395120a00e620780c3c000714200e502003405282d44281900010440750036199290010290440c10400c40301040e800c211001c034184054010740e055250ba04214080c0b00313400d0b0090305551141880e80720389000d80740c51010428014140107110708400c044035400c0400580e1745401d07011590800382030202d1901c59014058900740003070030340d51440c0b01071129100d09009400a0140c1c658070914166603110300d1140e8060081c007400500390400c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754613902 1250 754612652 754612657
    0x1803080c031b03130b01060c0c1a0c120c0d080103050a12030b13050402030c0a2102010509041814030f0d05090c04050f070305061005090f041b12150b0f 67
    0x39107001910401c840740341400c0c41030741c0f0a4035903050100800340322204010b0b0400309103015205920340481c14102542d140c0290003114010000246030b48a0420082c00c1c40c00d090700c007030b40402c1d41100c03800d40b04084003050b213621044402c0da05010304c400b502307072080c09802135038103c0382d1100c0102004042502c03180030854000000004160f00c0c4c820310451951658001c0040201c0b1003000111810188109481c0003a01210b47d800b50843c00410400e00c220442c44589418141d001d5280558180c80100c450344180d24120340d001c1d15000c840740031041074040b80d216461060341c10500007205811215640d005445011030001c0c2c0030016681602e0498016036003007291101103554504c090000502591012100e8034120045031082207412a818002c040d00400c046d10b00b07990035011440700501074816111361500904007001280ca10341c0b929032207040e00b6080c14030707402421454000010521900c080e400c280060800c0b2480401004030310b031201c100c80100302e0461a044044500345080d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754615152 1250 754613902 754613911
    0x10b040504031e111221010b0909040609061a10141e0910171501050313031b1202101413170409060510021c300506041803080c03 57
    0x45109040048141d0030407641c07051810f0f140f1001c0e115844441131003d24202c89260806690501c6d0041144113841011940220800da800c2d40c42a56141003500c041c10304494028500d030300d03064650078403042200c061441600c0443e0010081e081c43c0784200d03181c450110440891003000c208941e41d2840c07020091540d4007a0402881c01c0c94000c000240079601707980da904010800b150010081c02040d20203281e4070044aa01140080c6030303510000307020707000050040000d000c442c0e940d0702c04d00d0701410005c0004003803c42800c01d40329061512542404031a000301e0003500c105201c0508c032101c00e015107403581c40b50185200040e501d9058000b460300401c0c02c01e0f03a400d480001422607200244004001510841c078010401e41c2c03805c3d0074410710700040240c250464000807101c5150125500307508850361010325090103401c49440040d10422010b05c000317880b1180c0d6040200000440d5005503114035400c41e420445000c00e03504080584000b032800500103a148000503080000302000356400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754616402 1250 754615152 754615157
    0x2130b0d0609050f0a18030207093602030601120f08030a0e0304031b090903020d1d040606090f09020307080412091a03090f010b0f151911010b040504031e 68
    0x2807030303500c41d070074800c4a0042c0e6500103030144030380c10401804514020800f40104148015142003640e1b01d0003521074200e40203c01143c0d4845607003c00c1031210034405522038205251502039513030165030701060280d40310812402030003220f00004100000d0300240c00880d40100c5000740150850b81c0c1c030703000c55100a0102e49503658640140786110410030242c009140f0640321045188000f8038482e424407100d510400c11282010381c4000042d41c0030a41c241c0807150341c203220b401e00e59009680d00f440c59010a040760810710b42200011074661020320401100c003080705148090b078444000350140d100c01c070781c401c0210b5914004034001500810407040400f555140080d500790701c42c031129010190103018100d02600102c103200700c964043c005c004a40105400803c58241c001020800c80e00f8141c813024410040c1131514952010610211004484250f95800b048583e40802074500c0d02d020400c001190328089000d07090341010b124490140c1d400d62900720340e41d060001c60b1504a0784800d486401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754617652 1250 754616402 754616411
    0x31061e230c0304030c0e0a181a07020a081c0e030c1f0b090c090301050f01030309060516060501090603032601030b0402031903031a0102070f050402070516091a0402130b0d 75
    0x200d0f175007020003005442421240750080c144201030b0000c1e10b40b45140070345c82288031100203001460f5100c0310102000480000c02540c0e99014090b030500550a0004e001c1c0c95001504580610362100d844020886002e0200305070000c50004a80e03034015902200e105a000f00712103c80c00b05a4007150608201c1c1c44e5005c2181c454810220340d0390f0105841c54100c4210119500c40186001e0140a0340104210380307100043d07245840080c50b19031140308103030504c0400200b2120721900441291011a0000c409022550795100c5210082481d4441500024044041c40c0940712850040c07004940490700c1b8480d040c1d00b0342c0c84140d42c0d140040d208903418454110700d100e043d48041c0c0100c205070b000f51800a01d8103c94015501b61001c40c0003414115080400140011300541c82118152001075800686980301417070070900d0190012160f0b40703c040c46403030005212800da00b20001b5405401c03503281c0c40c0301112040c40203a0040d001c140280c0c0c0a0300d00c00b4004010303007202901c0c882170003007801705 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754618902 1250 754617652 754617659
    0x5060a08010207050c010329060d140112030f0206041106090a170705091b070f050703020a290412030f02030904090b041209050631061e230c0304 64
    0x1402ca07440058100c98540061026a00640e010301c62100081843d810103210500020b14601954224000d0b0911600f0080b44043e0102c0060744003020f4203120307555401465860750003210311030940200840004400d00d84040c0b0040c404540133005039840344400a20401086c03c07c511a0808200d980c0c011981c050009184c054103421030b0700700801c11020301003c6080030140080000000e00d04010745680c54100f0686e47c0c200c00480380c50f240c210901e01400600d82c80c1240c14800c07954000303940501c2c90300010428007404102c64400001c41c2c100c240381070b07844084001a81c0030f50303c20307441092079501c0c0c642c01003400344e240050400704903c15a450580d490000400321803c41200b03840d1040c510040000300000060320304e00d411503e08041000f145042c00051081c0700c2c4071061940104c042e241c03050301c0584070710741d03c3d0b049010b4030032450301a40f6040010302c03821080c0c4211a42c4080c052000013000d0240c25082920100050b00f06000c068154403200b0a40c8482c1444180b03101c00c01001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754620152 1250 754618902 754618919
    0xc030403141c110d030204081207080415050a02010b03071208091807030902030f010b030d050705030d05070314131205070804090e0304050a3f050a23030f04030605060a 74
    0x1d030700303000305a107900c03030b0b42c0c407410341144e241c8034a894182041c140704000c00d000102c1c0024203619040300c50780b0110380d50b602c40d107040c02c0103024503409500b03005440021002540d0700240942136081c0503900802001c1c03007200815580703040a200740d181000780c4103440d101203101c11000781071401026045111048000038403001000085400900082e178410404003149014047c100240d100100203018100f20000025183c8081c081480103100d40001e00d03804108041c010303908005080c00d420802480d0184014010f44020304d240e81d10904414001115101e003580381d070035030300c0d0415215210070854100545042d8080c00d4259158081480005440c4030103001d48954195070700084d64903180343c0303014408901c10a4100c120032032040070701c2812040d030594840c20607418041124843c848001e050140e0000320b40806042400741c082c100741403102da21182e140101074400c50800c55621004216186e003c0c50040181c400400c00042001c02c0203500715981052005050002045d52051203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754621402 1250 754620152 754620193
    0x4030c0f1401060f05120714030f0712020a0509150f06130f0303140301140d0204110706140c0403030e1002120d090c0509160305280209040b060c03040314 68
    0x301c00c040d0307440c3c29003401900c90900d41040248426686080c500e6549081036490708901d00804034105c0400c1081c044c43c2c2d03000c0003480e102001260940700d9a40c0c44a01030310f07120881c1c20b010ba00403100000001003604020301c0d05441a98081504207280341d864080281410030580840e5200805020404424981c03219030742c020030070012042d10441c074615015008580d1440d5170283c450083c401041446125604001741c0c00040790181c24000c26440010300401b10494888644900030603040100000d643c486c0c0580c01051026032182c0c0e88502841d100c1e44a680002000030b210b4655542481c01c280c41911040303401801074a0120312074541c01c0e800303034100c820300c5000241c90392604801c4c000010451009040140c80001d00c0e444c0502c1203003842c9a1200d00c003420560703180002580c844001d401080c1c05e008100c0b0a1421681404040c40a0b41240c60224407030f51400c5010b10192600608031214403080d0301c003460406186854045084e400d02071003078a503004400ca0181403000c49010b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754622652 1250 754621402 754621433
    0x201213020a14010813020127050a081e062802040312080402030f0105090304050112020f0a120509010605360c130b180d11101215030203100b040603050115080d1704030c0f 75
    0x8240910a00b082c1d100d00c030600101c003d00c65004a014000c01c005207030070a05078040012203502408181953b260000d104940c0080c0040d80c4080405044072740c804205030040d8001c8040324a0507015400c410f003207580603500945250700820040000f075002e10b1f01d070146141601c80050901c2c0100e00e9103106980100050303000582050040142c002c03991140c0d035040200744000b00000b5013420089100d04800ca4146800909041e000043d614080d0702c15550031f4694503883e220605100751f8200b407580040b101c2440c0801d44c0f90001c250313181c1600507165402004898690003424240501042529042c0c040d2400c0c0c0da100c051548039103409110801d01103080d915100c05040c5401c8000460303040062100e0b800507011030070030241c1e071b0008010612504804000809409450001e001401d895200a016500b055241201640514042400c841058094965010000000b2030f0092080c0181c6040062001d000c40e02180c031981c04140700500c140e031118002c0c40b05448410145600d02d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754623902 1250 754622652 754622669
    0x1c0501020712080903030106090b031302150405040c171812120a05061002100e01150b0415020a120e06070204020c01050a201213020a14010813020127050a 68
    0x161002140f540108600e80c44030003c0091070030741d4103045d00246100300c01c0c82071200f9040f02001007030039400110411501c066006102c1c6c40c2e10842907003007030001d0b04180f00700e602c00e40c81d00b03010100c45c500071200c0514400b120788800c14207036542135429001c918907003540070a91142c0c20b03040c80070800714002010f00400103000541646003d007030880c1a2440100f9003030241d401c5881c0e00030242d0300091b401c24094441d0501251800014809600503c650708440c9070b07040d203c550000b66241150020410b445903100d10551f919076940c07040c1c1c1d44a000407001840c00c2c0c083d913414401284684a1074040450090400e843c00205400003010303600400001c801c2d50750b466092040682c00c521131403841100070018042c41001106d11030629009802c005442c0c9a68800010742d100201c409291005600526019140d0b44030034104c03014102007850a03022800f0b94000c56100740c8101650002964142d40c1c80311043ea2040040304400c4459640603451604000080368640d01c9096407409083d001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754625152 1250 754623902 754623923
    0xf0c03090a05010903020d0201030b0f0d0f051e0307060e01020f041d06032d070e0f011e180f0617030702191d04080c0d0e0910141c05010207 62
    0x4404100400c1c00c1640b0290500803c1401000140c84000302004c0c0c030303034090800080045201010a5004a429140c90b600c144041c410500300322204010101247c0590b0403241c130210028840508111035120349525940103002c000001401500706454050380e00f000541440100081c9410503002600541e085258581c54020030210000d0355590015040300102075428100e8152185081c04110600750f80184007a40008424100314243c020300341094484500d03d00389012076035400c0280503441500500034400c05800c4110340c1c0074010f403044510602400900d00703801c0002031482d20f4078129410f4880c50006050702d100c0002d1074803007406001031036888080c0e104200b1901414040001c1080b08140c0034020a010300c0300212509074002c1c0801c0d0a80c5039400d11080700d015400341d01405101d40c40d1404000c56000b6500710b9454010340f0b406c1c556441e0303e4030200c0c2c1c1c0680c900409641c152143c0c00000d080c0f0b440341e42003a10201050082c010301140d5200e050076a4003c150544200c51030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754626402 1250 754625152 754625167
    0x6210f0105120d051c0b0d03050702031905061302040e0f062a09060307170c04051e100e06090405010b03061009060e010c060204170f122d0f0c03 64
    0x20380c4070012440c07140d40107000183c0600a0103006400b513807822010307801c00b001000384603004130b5010b500706800c01880c1c3e50b10048689401401d07580045000c038000c0c09001480501001e0450908500c264400080d0481d5a03820203030342e01090001001381d0380035460703030140011440144140c858154590740940300ca86844604402510380311502c8600f0111002c603840789210048094641c1904e0485640d69a500e0f10303941200d50408014441c0701aa80140622814603003000040c0708941c01510f07403c00f010310401c0048510303c1145443c58101c4088111b5181c9144038020b41e039440d0800501090030607048001140031940f003600503462401c1c00000b40005480c00582036000d4442510300301e60b00d41d0801030000c00300000250460706002c29099402c1c2001030b142c0598000c1c100c40c01e4003a82c404040c40040340c1e1601c000d0341c04c140b54051720101d10100d112490448035058150a0381000c00d0311103108000c0c0d0142100c074040c072180b106010880903881c4160042808003950b50080d41c83e48074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754627652 1250 754626402 754626409
    0x151803080708010f0303230f0d021e0f0318190302010b030c030a0305070602090a03080732070e220b01060f0207060813050a120210050f060108010506210f0105 70
    0x706130480701c0c00025000003000000e6000031880804c545d190040c3e01c2807a0f1304006e0010b5400b60800584069001150290401e86a0750180c11180c1400b4862440d07907014504130030492055003090711a900c2c0c00c00000b00c0015440b0054081c080c207032070446d001143d04840501c030f000f42d14002100140d4660603600918982003107082d0301c0f88070880262200d000541d40107406031054603030007051700e03401280003011175031181c40c60001150840b452700c1d9980c0040c6802103007140b00404020f41e001c4d0050701c0d018404044810080d110300c10400a00c03840342404040312100100401c0c01040710248003075180300381d002d4200035170b0b0300d80302e0800c2c00700550406030081e0030060b01616039405c42d070009108220302a4403100c0c40d0341220441403140c030a12494208103080c0074a44401800c21010000c00d120000d03030008400700c845800603c100b1050b140c5048021003411300761180c40c00198958010b10061400380024080c0c88101e0307400c040c0800c802050800b06440440b00c82458519241c010403c901707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754628902 1250 754627652 754627667
    0x30f0506040c050a180b03070804030201202b020f04150e0a03030c1e050709182001050c1203060f062a1002120a0605011b1518030807 59
    0x400c6405100508440c84001e00f01d00a1a02c90b034108003580c2442016400305920b40d4001d80940980f269a03441c028001034401c0b401510128010f40c82c0852a09030f40d21440c0105800d0400500100d1038854641010307000716503185c40c030103101c140461001c0d40014441c0300030701c0300c03c8006080720740b1185000d80041509000c0c855140a10050091700308856070340b00d0b00d03a0140d80d031604000c40700c003029090050324041c8410910300c813810703e81c581009200002410700221045030105000c848900c020580002100c3d5100810305520600c0028036501d414654540600701807429600b4038442250303291414212300c840c040b000394000140625420508001c68920205690040c5008102c0f0300a01414039880500000300c8107001d209640c9400500c42d00c01000400304c400d41d141c0205c4107280ca200c0c0d00c181c0341406e44e180341035400522035018041000c148021411000001c010f1a103e51469425045908124580d5078210100e1140c840c005610194000c2c3c0c2e0b40303030080c40d02c03480c09072020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754630152 1250 754628902 754628911
    0x5010e011112010510030e010c200703050a080a1e0c0b060111100b060c0102040f38132c2505070507030c0e0f010e1302040e0c060a030f05 61
    0x5003001410b0380c001c110000241140e8042c0c80303030050400c0b2150110010700007060b01c242154240201d50304016403207010b4145c40d00300d85d020030f460000c111601941c0d0310910310004015400010111010400c1d00300a440002c0a50801c0c0130303491400040311103441d1600c411100403a030001e51410078001c00c580c01551200c0c0a0808002403024214944d07175409505126540050b1525521003141e2900c0742610302440c0714074020340d06c1c2c03911148101c0384840603001d03c60303c07103204591b108490081803d000354001246010017001e101e80d0b10903d00e080e480100080c0344100303e500001038451900c00081000011290300050206500020f1351221502400100200b0041d0300000c0c0d115046481c1c0c00018260360405542e942418641541005001d500140c011064004000740c46407080504500c41d0107201c0d5048190780c1c03200d00c1d401060100f910608040140c1071200320060419030301c03203c0e00072000e10071103060361136040c0050f0306075022901440000f41c5501c0d0305000b0301c100d401182d422 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754631402 1250 754630152 754630181
    0x10303090f03030914150408010f0509030a1713120906111f02180a080c130207030806010509490f06020f04030b0f04030e100207051509090405010e01 66
    0x161079610f004114034400c0c00317409011065800900c21036541c0740581d20040e100303451050b4403950b0b141070480c02004204400060305080c9800031318221008000c40310b900603ea01c0704e41d0b003403528550f40e03e200c0f103004085100c031040068106001c82e16680a0422004207680c42c40740e42070610400518016042403448143d034400c501e900c2c0c40b0a02d4900342c0714050240e031030050f194543d80e07081c80019006074050365042030100328045107240700420a01d40d500801d6070300b8900b03c0c07020042e6004074400c0001c05000038060b0f20100e000c3e5031054008002000f4024079074180741480240d001190040340c03201c1200242400070010325004035085440d400480741542090002e03550302d800004580900004100c158001014002e1450440985001d160425515591032400c14600ca031452029103060b008030792046040c0119142c80d1500c0c03482070036a540a001a0342c030305070501010480110060003c40c106200154481e124210f08500c11402a800412100c0e2680002421200341c12241c0340d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754632652 1250 754631402 754631429
    0x504150e16050909070b0c0c060c010905010b01080f0610110f070312050414040c09030506010609030c0504060612050a0e2d0105130f030c0c0b0d0c0e010c0602031f080601030309 78
    0x1402c1002c9040400c43d81140e50b0990351f0701d10009400d08200c200f159183e0312607004102c90060b01415801000707100d00c140000c000840d03041005461001c4122014032441d00e005000071014109078055003d00030a0b410040341000c002103501c0c5c101640c41002200681c0400c500308203000d8100d00500f81d10101e0b080c61490309003050445855280210b9591307018688550460500354400d4880c04025600182910510f5071610705c0103080388541c0c801a640d040e85424041024a403031b00c40c1900f00d13000ca4650b0031002800000301c01c06881c008240002c11030703407001c14400b071000c2404070541480713524400311507080741c41110403000c0350b1036444542c440c0c0c509800c20105411103001003401a42000404042081e60b1400312801d14901d44000e008107068800012010046805071414080e04a01800150340100046881c045c9540c3c0460004e00440220384c0414410b900454102e880c904240d298820b19110f10406031030035500c8092244d2051004100b031540c0405a00e010704000440d401e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754633902 1250 754632652 754632661
    0xb041d0a0b18070302091005030303040b0a110f0306040c110102030c04081e060f100b0d0203090d081b0d020405040e03090307090603081207050d05070f032d0504150e160509 76
    0x83e540c0c1c82c2d40c003000303028446210208890100b4955220001d00005045903543e1400303162580042600f591950000d900f0103495051002c54081a500301600020f0310a0440d500c2c1e600b007001904810701d800080c40070798410481345000c00c0c001184912005050180c0e0749103403c09031454180c0c2441c008403125020b181c454807a0802250558121241c00e02026258a40c0c020039090188150722101001c0d4000402286018081c0c000d54803544209041d1403a4802c6c0b0002525401403c881c49008021142e904e400d21426050260081c030448210050400e520b8501060441e81207080600195001141c1010306250400980d400703000440401d00c2514a55075518041e40602401c0076010824100064100d078410005d43e41c0341c1e000d4800034042414690805070014610025a8002034244040c040c1c0c500c102d1035681008a14042035171305000821280c510003007501800c201c8201e040c0401261180c0114016581c42c40880c03009000056440480440301303075401e50049016814440800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754635152 1250 754633902 754633951
    0x1020d0c0503120402150a180b07110105030c0c0105090109020f0a0f120602090409030809010c140324031501051915031a190e0c070203100b041d0a0b 66
    0x141e01c08a00c180203c012912948005403441440100c0381191500202d1a15a0b4030341c003c6114002210000940c1491030b00c8216982c43d5204060000d80200038500380403100b944180d000319407184405802504140002c0d0701c450070b41341c050764000e030242c0d1100344c0c0c9015440c0c1508400e81010b01200c002c08414502004500c5c072999034480c0010f03100e9070320f040c903050000130340483c0c1c00358000404c20071018000c2e00e005000020301782c401c43c0003903181090a4400354043c0c005140040c1d010782200c1d0969580c6d4a940d500c08052403e4240d410400d41c8105800740c0303041001850310076a4580e40c0c2034960402081c411800c401c4400382000d0750f003140007044401c000094075505030745140b5000c24044c11409600401182c0c605039540c200c0696404100c402c072110540209a49403840d0840041d00d0301a4680b074035025848001c1d516401050b00c0c4e05503400564811465071a0140c004101002a01c0c41018041450940802c0355044251500100001044140da00042c000285082049012140b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754636402 1250 754635152 754635157
    0x10e011803031a1324141302040b04060909140c03220203031c050906090c0d050f010501090605131e0905120712080906090a120e030d0e01020d0c0503 66
    0x14003415a070302c55403c1d10440101030f081c40520060b001003526000c1010210003800c450a181c0c401c04000a244045500c00071002c504640410300080b40106030035007080039030300400240d52801c940c01c2100184211041d405080203020307035102d0030202c03442e0840c103070243c8900c4030640d441d00c66000e0070401c10640f100c0a898120300103a50700003404010340c150f01c03018446018082e41c18070010400040d241d1100f888100c03810800c54040c02030751141c0006c84d036626000d4608104942080c0c40c07801c80790070980004101c081c000c000302d0b000540d1201002c0c2c211030342a0080045603480d09030030b0040e4102243c4100d612503a101c1c04202c90a000c00c1011048000e1511b11401a5100e0f41a00d00340507080060701c9406112541d4159104814503000d10404550a0194007241030207001842c10070004c5191486000e600001e06203485060b90fa0541070901100d182051000c075807030203046a2420040c00d2062400c9440e162a0703a90300b8000a881d10b10151505000c12040b07461620018401005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754637652 1250 754636402 754636451
    0x18100f0906050739080d110109050604030309030c0c0305060a0c050c070302190b1206120328031805010c02011b0903080901030b09090102041406070b0f0702120a0203040503010e01 79
    0x2800b40b8405851341d02407107284101c1108028203031614102141340301c1c020851203000203858880049162442c41c4040c240c4240c0c0d50040e0058200100260110303000f50481c0304514800d203084d020360801640d13410110016078009540d030354004020040395044510035104440640e04045050000100300c8555400341030100070f0045003404407044203074440c060942c0c0075020000700a5191505040304004100e4225801445045840c0e8550340001c2d011048900d03d03000d00314042101d2021260a45059175420908010141d40d0b203981e0360103e2a210040d00c4044c80344e0008103040c464450002e0948002d0001c801c8a00d00c00d20b05100050341000c8400300301c0380d0191006849048084c010380040a0000d0880d4010812008206080c0070650040c0b064660701d5040801100030340c81400b0150242c0300000b00900d0804000c601e80c1c8001d0007070258040071610483d5804442110001d040750080445d003405640301080a00007171400b8000e03070708003101c440001c20208428100101c0201c00c4510f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754638902 1250 754637652 754637693
    0x5040c0305090c150c030409020919061b020a15020a0203010c020d120926040305120a0e040911030f070f051008070f02030702030d2c060f18100f09060507 68
    0x15007112155500000b945d20094212041e00c1d190356440311210041c0d80a00c400e00d00c00e0050260100c40900e51a948600340c4003240e45404141c102034050840712200d028042e81d0040e0841000a40d10756240c4105a002c012607020b0b0402140c60f1040c142541e400803c0c11096422856200f000103070b2001290002120482001c90401075900381700a2a0202d918004010116610014042d0906c10010021031740308001301d80c031607000403240c8041405011400400104881d07607a00170762415030011190a07029110840907030781c40301c000a1408070089105485608461020041080c003200440000d00701510b003116030309002140104100402001201480580550582c200c1d2080050b201400d0340034044880c00d290203000500503000806200c96142800c50100c048942e80c0700a20b5245000600b88030b0500803048801d40041d009444404141d088031950110142e843c0b046d00b120a10030390310303a203201a112403801401c9034110703005a030074000c2c104a03800000e116158000500036822 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754640152 1250 754638902 754638919
    0x2106010e01030c0318030906021606021b0102010213180c05071502210c07060501050607030221091302040602061e012304020d060501021b09010e0a1e0605040c0305090c 74
    0x7804140d006080c4170b8103444c2082a00709030740f01059000182501520400c0e0203d4540c064034540c0210380003654042e0340c5c0141c100e00804003541e0a081c8208503200414000503040c6450f0f960408100152a030010402c86203100300450074141c0c0d8411008a48000e20f40a45407002d583c8510326514411071050204e41da000403145081c0d1a151417091080d507421207105914103001c14030408a421240007510694649000000d00f4030b07000e07003251011549a0043c1815881c0e1640d019030a90392a640314040201c10083c006140d501c2c58121070041c0032510005840301d003420b40007071a01000610901040204e1b80c4440070002c070055582d0f045a1000015901d5001d81c0340d640c0340c0024041e08619042800070468000c05002034001c681a01ca080e401c840c0229001d12901240102c0400c4042d005440000103101c84000000142d0380308083c440c010900b48512900c81403220f1511102001a540d660700c28883d80c0390500558141c071581d840e090006050140b41a61a404000365582c45114503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 754641402 1250 754640152 754640171
    0x3150501052713020304020109060306083a0504031b0302011d0307091409061005010f030e03040510050a02060c1305010c050a06020412021201140c0307030f020a052106010e0103 78
    0x3000000c0d000e01c1d20103040075a08843c800e407400013940040c1c030100d01141c418003000ca0110311a229810403100008014045507121610340351014811802e0650000601c40e010303911804200c40c1440780d14010382c0c1e0b09540b1840c504100043c0c4074909103000c543c140c2c0580810140c3e0348440e0050845400d04000d10001c80e0141c0024074005032030b0702880000c2e08181d905110707131007100040e901c240c1038441900c60594500c81c0c0c4400c1c04901d8016a804280408190348059220b80e02000b0700403045811245026102c1000852000e1803e0324000007640c000380783c0401c0d42e41804019000301c03c00d01030740d0402d088103010490400d854064603040003035805428003440400c2040d00d17040c0d50481c0d011540c0c0c5403503503c0b50b030586d030341e150080c1c1c0039000140d20825200014818510200c1400b0030000068580035200300140d48050075600401d511160032581d1100310344010092050591205c503034400080c0c52402200740415030404d0304900039410041c250341c11421031100c6070001d01c0d000891000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 754642652 1250 754641402 754641457
    0xc15090a3812040605090c0102060f070c020414040b07110304030201050403020d05150406020a030b0603130f08071205091203130306020d060315060603050c03100b0a0c050118030315050105 83
    0x2c0c00e4544403000c42110902080c03215a038407050051701e8080603200026021001a130f610030307007034402109d181c04080005180350310a0741d50440e164401080070911b010410416400362005070750980e50300034030b4014424030b01c0c2c004080d01c82a01004024605041c5035400182c4980260b21010380680c018680d03110400c1400e000009102c03174002f44800c0e050030729081c9240250858010600840d242c040c404140b8075040c415170703104000c054040c041da80707620390350264403200d18074044500817003c1c000100010005841484d100007a039803003a465007103141c01c102c10903d04e088a02c505030000c00260010105850381841943c2c1c00843c0560355803d8105164010000b683c4050103110340014114a1000c0c29008141194102c2d40e09006c1c90300c0340c1d1800c10451006550340103917008007550411248420201a06940601c5d05140841541a03252039096a540160461380d450880728002d0030560588240c0300c40a8000c0b0580106a05000010741584100200e241340c01e0a0702c442d0b504010b4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 754643902 1250 754642652 754642657
    0x20607081902010c0e030724090312082205030307140912060f0a0b06040306090218130317091f0905010c020a0c0b0702100f020c15090a38 61
    0x7600002428107442014000034003c0c18402d1400b00081c070686282121458002100303826a956403c1c6001034507010000c2c8840d044c1198540c4051100c18000080492140041c00715440e2950320395002d03600e01401c50004200e00b52102c0b203441500301201402043c0004190f035841641400e00b003841c0700c0f942c2500b010314040c17501e889074407803c4400c1d1503c840c00c02082c024024242502c4460b00b5031101d010b1241602c0e844801c50742c0008003848208089a40c2d904100c00460014280300c4000f419201032114403001159490350b00303155020302c0010164086803c0100700f034002038000c8039051000b6450340786c0c08420324001090801c0e05034140f101c0341e5940400c50311a8000000c000f2003a0744000691520600041a9152001d0200001d01040c102c0c0842e80540e60060400d5407142c00c3c080161284080c041042085200700c002261050700d40180410744401c02c090850f80b11200c0c03900b04820441603030032004030f44800c0713896034010150300348000c491500b04159070400000c0f4012801060b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 754645152 1250 754643902 754643917
    0x609180d05040311030109032a060207351b1608010606080114030303011a0910030605031e0601050d0312110a0f03090b01140d081809071103040302060708 68
    0x280181000042401e42060040c0102c9203d4001c9030000c980c803004040c00c0b24000700004c0d0204c0d50780040c1116054041c01640503868095949980c5c2519a454070340c00c076001060300f01e4111025881840e4400c40008014400500310800c810381c440280c2c000b003059004408549120150f0f034002d1580c508010702c05c003112445031a55039420165114055806000d091003418082142180081080100c0354035030000060701038025071950b4604072141485600d0454420724103401889460080d80e51024881d400480c2d0b50340101c1d0b0b07141081c04050030143d105120207071340c0f0080030b00e408104102141032811100104c03084100402907003416250328a081c41c04512f82840c000814801441808c003038940c054880c1d9801c8560f0075080030a500f03d841c1e032540a000e8006102c010002d01c2030168038458518406089503071241a9991340c0440c603000382c0c0941810000121568080d42480245164010300030310b04944119000c00ca141d4981c8a1800301a00400e0000b48460030b00043d0021111107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 754646402 1250 754645152 754645201
    0xb060414251106070e060705031308010b060720010c05030a0c1104020301030837030b15030f0112020402120f0402030f1f02070f060204030c0f1d0609 66
    0x914040c0c0d0070314030003018281d003050042070a01d0007841062103540040c401d0000d6100500060f103a400c42518208040c00f02c05510140c100314600000704180081c183c440c0401c11507159080c2050682d50a482d610100302c1c1c025030b0144881d9007c82e504000b81e0702074844141c2014200c041500040302c03203480c0810007501500c000078141c40b019902c040500c4184c0c0c01b42c00b40c0c06000c55102c04010607403100b1312000d0f00c2004240b145a40070f0407148030740054400c161040b2174419034003015080030241c0c5a10b9040c082995001d800106090034900d240c138045101804503e94070700000c04034148141030003400000d0103456845030440d25981d040700e040051181c0407400a14101244a2450108540480c0240074507440040c80c280000740c604071700400d1200d14003100e41807100b00710003034020000656240e0521028100031031607034030007480510700450b501460141000c0482c1d4440c14968424126030404000c1160780309069440c1d05d40241c01112071301d90301d40b184118443d0414021640703405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 754647652 1250 754646402 754646441
    0x7020f150307030c030b0d0605061809010606020106080705030d050d020c060f0a0b33040e01140a06090602060106110a02090108030c0c030a0c0909080d05091f180b0604 74
    0x4516400e4000745100d800c081c3d83c203001d0b10751114800c0b003d5460358103880760401d0f0340d02e030502d00048054001541c0403002030f01e00f80c4200740b00e5011340c083d990240c6284409940d00d41c01800040c3e03081c041c041c040c0031402c008000302c9140802180d5503101c05c004900030010046030f22007103541070360115440c0c411044201c1d0200d0410801e01448020181d407800c0c0041d01d081c00b1580c0f141860038000760006010107801c101d02c428000d1110340e15440d04000d4007008000c00011071003035100c0350518081d24403103c03a01003c042003411700000d8007841c1c02404c14058004000c106455000506a06440d0b5030300d01000309560003c40d2034a4000e100c3c070029801030454001265945000025094405414040b01c0c8004510070078507444035203650002d044d1030711148003401200ba154001d1004603115152551900349890307040c20461390309441003149604100c0884400b03402e4112245c80ca2060081d00300220fa404c81344040e03800c10803050090140840d076000a03019569544040c4140003600003a10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 754648902 1250 754647652 754647679
    0x1810050916050f1303060b09180705011b1a011d010308040b07060b0d050c1509030703140f12040f1d070c020102120708030108060f04231903080702060a0b0d0807020f 73
    0x20187c120010301c0c5009459002c0042c8070311001c540d1900c034034541c0c40c000c0c00d4140c0c2044011902d000d440c0d4000c0c080307145803c0460001400c2d5a2a02038034000a1001c0c1010b035042c018401801d04400004a005c2080100140301141e0038404032012201910320b890341c0c0d103820b883c0c00406400c0061459a0108002301d00909018020400440e03514085400074002c0d81002d400220500031400c9654041e80000c805100141c0d0b1010702401018051045a00400c424410f40b45401100610b050303e0b6100403e04200b025501d209003800b601009604001800c850501119114001000c80d400c0110055004003075900070b1061815a03500c400d0300036a01e41c100d0600b6005a4028484d2102c244240000540c5407100710905034007451b03028064000d0100f00e02c0c803080e0003c01b40040760503180030f00800d20003112403c034490301c811803180c0c03030320302991501e6400a030a066005080b411401e0402006020361740d81c1a12140c006030307016042548459050020607083c0080c1d291458020f00740d0303030658 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 754650152 1250 754648902 754648913
    0x61807030c030605030106120b0408070615030b090d2708030406200109050706080405101a01021605030c040c02010b0d03020a1202160e060d021810050916050f1303 72
    0x352481480c2e01e060240680c0d0300c0a00d0700f2501c40c0d12400d08101100c47c1b040c00059074040059800901a015a81c142103c944480e41220006640210342000c2050200108200850403550017050700b00604216480c87c00d002e0000c191686007004840303070200141c81d10340510303942503016200c010112510340c1d85950005d8180b0381a00d2000d0960840c2c0b400544036408140101c501c484d83c04406007542d2840c100c0d040d5401c10010380210f81a00885400c0d021201092240c4102c0c400c480c03503000550705210001a040c03400c080602c1c408100500700a0101382c07000121044030714403d5030300040042c0c81005c04c070b0050500200745a400890038034510b05140e80021640e80c1e040c01461525001c40d00743d403040e6a05c0d004121740360082500a10100443c2d9031442615a00940c094821164081240e00080b03010008103d04e11101489130f051104044410590320050038003a1400a164103180e203c3c004103d5210082104100002a5a400340302204007551408100805545409a22450034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 754651402 1250 754650152 754650161
    0x90a0b0a0c1202040f120512030f0a06051008010312050c0f031315080109090f0f0f060516050d0203040302070e04051c1e0c0201051e0304051002130e06180703 70
    0xc040c0021000450700542c0146882210229004401207051480c603000d045603201c0b910f0507054619004107240610442c85607001584a80815071002c0c80f240b500345008411100503802c0341e0300640d16150b51441e4150040c203082d040d240c0000412800c1d89440804403860702c43c94004c11940c0c0111501d084000d8800400313400406520410114105d071144101210004035443d0340340010101320040160004542c0004c0326075002e1900d1140505941d01c2c0c51440080c0b600381200c0c980c04602c038500602040d13104554101c4a000d0810300c12003070503c80105107000744640400708690020100e0201f500801034840140070040300c4030030500d01410002e0300e036410107541452524031950403010551180e04c0112038142c03046c1682c4090507600c42304980000c12560124180042048a0240382141c0c60000c0900300400c442183e03285040d19100b420301e4500b0705002d504600604c0141442c0007212601c0058642100a051b01569010000341d04607540307142490100740c0d104184940341c3d606401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 754652652 1250 754651402 754651421
    0xa0f0209060f270109030b13061b0f090617091005130506061f0302031026070914041e060f0b0315011818020301021206031b1008090a0b0a 61
    0x60309091480620250440f08102e054480c001071030008107000140a060101b1740000001140c0b00b80300a00d941e0b6501240c1c0700842401030507000b04504803a05500c200c0180443c001c91404082081c40c1032005041e940045644c190111041c0b030002c0d40c1c00700d0420860003540b82480081c003d5003803468014041c00541d01d000c0d1254010400020301f9400c080e00d214090b0220f00d0380303030b09141080e03000480086d00086e218131010032035403800082d08000c400720101444c5452814916440700804420310f0200e081d400340c03503041d0030f107410f8061310041c41100c1980241c0000c8900e00ba58040300c12250320402c00390004059914104255040c215640e21040c480c0c0e00550883e64456140031006007500d03400d1040e4019041125542451031810f83c0003521003108505441c0b0458603e0750001c0c0c2039801458001d0703a60808903041050360321701008261140ca0712081c042171106031910115200c4560616a5414070000b20040b410100c000c1104102c541c0c0c03c030a4005440c106495a00f021381040300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 754653902 1250 754652652 754652677
    0x1b0501110a0504030b0c030106080402040e011407080702010e06060f0d020607060204091a0108091015051f031d071a21040c0602011e241502010c050a02060a0f0209060f 74
    0x400200e840703e5550440341078032760a40360005150348580c2008041c0c50203c28401280d5240c03440d803020040c0c6854140d0240c015500c2d540d03494a480c000003400c580d600d01102c0404d034041030034011142c0307540a040301400c0094541020448160010400b28403400e0f1004000d503100040000b140306540c0d10007021041071303569004a0080317820044031314645c00d070743c1c10030250850002c03149500074a86c404110040800c8081d0744660740d0720000350501ca0103405003540180340ca80850b4420350b04d131083c1000c585c90a52100320140c4141c551568132070081c0038114507a0b00001100c074490001c601622190031307401c035a0b80d00340900f415480388010019135089484040040020a07168010300502040800a01d14034103080f0700044400c0180640a03c40210303820038070b008501108201110704045c091032015464404a255002421240f641a0050410406000a410745030780800c40a0300010b628001090b001d8000310010024820702c6129a07102c2ea0000d00c1c45004400080500701c440f0003030717 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 754655152 1250 754653902 754653923
    0x20a050402071e0c051203030a06080601082a1509040e030a120209040e0607021c050f0a11121917010503030702010c08160606140109061b0501110a050403 68
    0x1642400180e00038490b00810400c1004814060307006205540000d90b030092601c080025520000700341009110442d00099410000c10844c02c0d022a00680c001040030400a200a61401403d240c5071101d86604603c40b112a1031f204040c25101c0b0080454644002e000c0b42c2104045402050340354400101d40d4040c07410404008454400841615520109603c802d114800404600b4000754025014281d00598450325040d8911082027a10f2081d03010f50000d0062440e803c0340c0d045c50182d0341c004142001001c11000388020280c00558244440b00d080022141a1100780507040c692555a4504099404252543c400428080c411461003c54460318071030307141710004101006c8240601a015401000800700551051003038110725400340981e0341c240021103408404500c480311050b41c4c100c4e1107034000d0105034402c080d019501036090802500440c0303030000107800d441d40360400c4ac003c5195001e610050110030f40019000c1000b441200d690b034582071002030b0042d0480c5c00182d42c0c08024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 754656402 1250 754655152 754655159
    0x80f1c0207271a0913031e030204031b060f030509011b02061008160b090d1a060906040b0102070e091015081608070306020f0c03030a050702190309050f030f1504020a 73
    0x30a0120400c20b0800b80103100d0560340c28004010b01130070000c048007040110031440001f807240200d40e00c22084242d07405a5140d24500b0b103010542c80310060400c8401503e04100003281c0c0100042207005c10303904002c41d0903513441e0080c1c2d0041100c10503003000001c0f006501501d8175404206d40f481b8050042c80c101e000c5480708196a0b6490781d99a24100708042a10203000c00703001d1901500030200001d0200d03820904030f59031000e039002c000410f9204c640941c0180201450080c40003980410150f82c02c0115034080b400007561050b05100b40b241e8a01548003280714000180315403110405400c40c03e0200702c0c00140c0c1ca81d0348088033700c111443c1e4040e1490260000b6005d1115400725251040200034090440c0c66450003544240907007101c0c5901040b500c02c4d6042d0600186110311480080098945403004000c0e00f00618442c0420100c44103004400011340c1145520094940a90b429007103030740c110011a1411113011070101541c446c10b403031810380e080b004200034400c910a90310b25062968 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 754657652 1250 754656402 754656431
    0x1d130b150913020f1201021309020d050f0c07110a05060f041d0f1603180f0606050619030b0f0607050618030a1215031b0e01080f1c020727 61
    0x1c880e040254841da21340300f0390425151107002c5003032840f00040010f1a000741b00d09030440c0a9410303403200d51215000b00e003010198100b842540c1e404034014045d000d03189400c800d50101807051003c020702d241c104800c1d441194540f50030301005084094603055444200d60f080042c1ca400c9481034046c0000015286c41a60340802c001c10300420000c0601069070301c58019819041050601d03000402d540e038014400d21100c030701d0513485041e01a41030015031403404e003861415544a40c218900650b000c00c842c1303450404031003400e440a0440d00e400101c100c0c0c510b000580540c0d10407003060b84a0004954a0280000421441d0140d04440031090169031060140ca4503802154941c0020464000844c0c400342c01541040425218920f40d404030580c81e070f62428003030400034440c2844120200b070140310202d505a0064058403411000f4588096510152070341c40380b88a080f0f04010207038010301003049008000000c0075087e4045510030b00c085080d45150f00400c58003690040c0c1f824140d00f03004440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 754658902 1250 754657652 754657681
    0x5030f010b01020303060d0614011805070c030f0e180906060a06180e060d30030b030c04020906040819060c081e070c1703010312091d130b1509 63
    0x1c410f8019500316503c0d40304100740000c00c0c2109458940d1204041c682820007029280d003c3c0480c10071007002c01d107001d0000d00c1204d00081c102c07000d02035a100d12401203a00100c0030b444405540c070b4820096004000858594a410700c2c0c8a2440c039011004c0c00440600419000d100300c0048e14442d0081c0d6440c0001c84030414409510030f03c02420990901102c043c02c0440d80e031100c000f802c04014460a030340e51251420302a8151041c20101c030203000b29004001c4800c3e4603008042c43c003071184202c40d00000c2c0d00c0e43e81180c4400e201e2307540000e45039225224242520024541c49081c0c9400505c8400034890643d00310b50202c1d541031401a58811241c0501d400f0740c083c03624101746800c00810f055500e00b02410150a800c06d00110954810028003028130b407441404e14000c485450b03500d5803400307010f510000c4640707105200c1c2c03003c003d120f1342800070000c103090fa051001c0d135425510749920b0038002000b00b01e40070f0030b0900704000304501484481c0300510800000c1e00c944030303180c6c2c036880c01c4042c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 754660152 1250 754658902 754658921
    0x8180f03030c07050105160e1516030206040c060e090f06010e0d0b06040b0a030f060e010209040c094b0f03110f0301060f060c05030409090311060115052506050a020405030f01 77
    0x6102106001007418002c0d501110742c201401c00f11301e0800c1c1c80006503009903208034101c0041c5cdc44242000100a11000c1c0280140707181d04104039200410b02c001100307400d0080c1800055101ca0340042c588d48c1c40b80b650218002c80140c14201a5a51401c04084454040f9516805181868041d00c3d01c0d082c003044d22000c80c0e0300250304641f080102c1e5210b1010744403015680141e503400f40841a510780d5a445141451142c2c1e4444803603d034500b4145411000a40b480c2c9254000301e0040340b640c1e503101c1c8840c0700681d034100d10b01c940502c101d4424000303021026000301640540c07480e004410400340300f18040e840d190840d40c410030410603d040500361107190041d40c045415440c0e0030070000d806600b40c150454815800e0306d04260722100b8000031a1000001078000464190141d04024401d00800d409004001c6103043c2441c05108003a1541c4500502190510b1000300d000314114941600e030003466074000e0b002e000505141e07040c1c0c0e019420038000d2034864000d50361b9280306000148940c61b8107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 754661402 1250 754660152 754660157
    0x601050d0305070302010603150b0f030102030f010303230d050108060a15090c0e04020a030606110f0a0b040201021011180a0503060408030405031c05040606080c0108180f03030c0705010516 83
    0x5000507950403101600546400c07415913485600c08000900b85404c012903040011342c1c0052035002d81420002c1c0c040d50005114000e901c1001848500c89010307202c130b81036a8060030701260005640c400703507103030000c0b500088140d888046400b8881c00501e40149040340c0a140c02c0301c03a6500c401f11448216100c2d4502c1101400704214104201d20194005143d0340d031707503400d002e200d90342664003150603680300c400720000080d0fa0b03007030901c006502300388509014842600144540492803160726035618000340c001d820a411800003504580c0301708007403c4207001070007042c00204651005049680c2203180c190008400c0300c1d00c840b0044c14001e2a00044070002001401c46803141d0b2100f03040e940c0050016030352400200447c80d90321200b582c088481d81130070305000456180505040080b100d6a4202d100e59030040384042c0216a880364429030010000c0c01283c40e014402d29031a4a03190325800008801d000110404c1802c141c198003903e802c034010b80080c880c940d02d10003500019514402490301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 754662652 1250 754661402 754661419
    0x6040b100807112a010f1b0308040f08070c05031c17060607050d021501170a02010e01030b0d11040e07060219080412061e0605060d230f0a0e060105 65
    0x10407841010400d81c00c0202034241c1d00b150707040c840070038460503043c049034654a02103032502c4d20a5900480c0880ca5001c5458200940e120a0900c0a000e00364404060100140c100100d4280007800100d4801d280c0d11120307996584030729103005c0e54400c40d5880303103074441d01a2626820054041030821030700320501d591800081c0141c0140000a0354010784484d401203c10720007140060001c20011120409540003008101c00800c10317150440300c141c0044402003402e0710a1000401c0010b800032406909081440c0d480e1104001200107007a81c1d00c42942c03220303944120200780454501e14a01b5400140e5060203040700880c803590381ea03444c62281400503884002000c80c080046150442120710400406180039034565a207550481c5160069400300d0343c030450306a2034810407400700400350b501740e03040c4880c600d4000015414041c6050070b41026455103030103403080414485828000002000b071026078105207181d08000c4804440048560303150452026125070000351050407107500801d500e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 754663902 1250 754662652 754662661
    0x90f0405150303040308031005190504050619140117011a0309030c030a0e0f090408180301060b0a051c05040f06022b020a1403060604030f171206040b1008 68
    0x10050400600415450001c0300790846a030780c0a10041c0000c5006680054803401c000d00e0303169071240c1c0c6510042c400d02d0040011000da421107000041150340448001856036501d0010980e003082c4a1100241c0b003c0003000404d600085d1104001c15030000c0e070343c403103a85280310001023000400703000720000031050320941c2031000403450066a02c44040020f407800c150000039560320f1600440300c000081b400e1014442d505041c2000d090f5000c000803950b46a690410b515034040e0f9100e4410050440b072950344c488002e58a094121000030030b000c0b00255030312500f812008103144c000c0086c82005040420801d06403c15a002d018091a00034402c0510030310141e031850000d602c802010340078a0050614a8560000d20b10101740c5d428801c5c6000d079540043c540001c0c0300c140041c90310485020b0902c10b02c072080d00e440c419601a207901001e00c00c80d0700c60504007400003998440e156070080e01c000440100c4015007510250050400703407401c1c04201480020400501886000800024200000035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 754665152 1250 754663902 754663909
    0x4080904180813120b060d03050c010903020705120109150e1e0601090506030307150b1318061b0801050d03021c0306080d0801120224070c03120915050a14070f0b0c090f 74
    0x7e2140501c80e08045280120040600d400c3d00e51041003a4007503040200100708504080c0c008020f12003805008018141c1107035610055040414603e008081c2d5134500e07020071007003c100700111003822110007002041e082e01d0407030b80c4a10034015031100904050104505050000a890780543d10681480c0c0e18401809410000c000090955500220950070704107813048078490030f0000310b440d40c0c007039000b24083e05007041643d1000f01010016040d0824080707400da44985014103484040303401740c040c000c207410101d00c1c11218001c18003881101d071481034000307a050345c060f00846010100350380a0100b910010307600c11000348940300b802070048141e48010b103811702e902c120302240e80c621203901d030300c020000140c42e0300b00030340495003510303451000e00c140109128111002c034100d14010314550308204c0f8081002101d05075003014040082a00d505640c00307401d8000c00b500307107009115140c81482c1083e0584104440040c0c840700100390104140901c07100072034100b950041d2200e181e220000050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 754666402 1250 754665152 754665169
    0x903210409051e01060305180705010e13090605070216060f0504090e1e01090b0f04080f07061b030209010807230c070b0c01090201090f03030804080904180813120b06 73
    0x800c10103103c0780030205811083d0741c2c046020303002c01d55000480c1c1c542a81c102110f100381d02082c3c1c03c181d114001c10802a80d100c5141300f19550161607000310000d4034020b002c041d00c0740200050001c2d0405040190b070070b40c00a003102c5499815440d07203075a995100f6041c0c0d007403504081300b100020340401c424004888180c10281c400e0300360404451510700c2d032044001d41c0118181c44000665194103048050149080a45d034100c8a0340004200038281569030003420f10812032030300c80c140e03c042003140501c41d180d030100c20304080c50a694044040c074010001c0095200300f08542c041000e40000c14071140c800c2d00c0d100c100c19503030001504e55105075040c1d10f40d90741006490780800d1003912004145805d0240c0502140c010360b600101d000d42d03d520016211191a170044d40800c1c1104104102089c0d010804681094100c03031031580d0b800c45000414090b00e130040f11020740b03603003a040d00010070401c4c0f00200014400760354107220440d00d40b50140300b03041500314080c0c200340301c0e000843e000b032809401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 754667652 1250 754666402 754666411
    0x305010e070503060303071a061302090d0b310209180a080c030d0612020f1c0312090807030909110a0c1104060f08160b0c0303070324030503090321040905 68
    0x459040c00015520000c1500b03080c074223060160303603510074841d407401c110141c0c0701200c4c2d500e80107508080d000e2000c00c03208082c1200c0a030803c60200301143c080d4008040121000c91400c01c8000e00503010010440004d13403140040340541e4050001800070076210205581d50b00406000c0e1200340311940340c0b0708464001d90201a00303804200000b0380b41d0b865031710915008103000160418404150300400c28441c01c4e00300a54010618202c0c5589401c5030203e104103100d60504082e5500720400340c4090042048840c000c0c440e04c3c0010342c0c0360905030407500b104102c030808002402209600013801d41740303005011104000c20307441035000c000a042d80c40034503480c201c040c02c0041e449036550648074204032281e00000403a001544003804480358003950b41d01030070414501d1850482c00740c81d400d542e84001440c10080565400d001c42c10b1f40010641c541c0e84021200410a00700c2c5c80e03040175a00d9a12208000d4031034401c43d110210080c0445c044008145030444825080c24501803108018000c01003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 754668902 1250 754667652 754667659
    0xb0109360b0a021b01051608090d0c0503040e0112060b0307051005031e10032f0d1112030c1c0f1404080316020306060f090a0b01020a12110d0305010e07050306 70
    0x40380c130710224094003180449050990000c07a060410549818200049000200410008204011003040c3c001040c448038442031814680c10303505400c0041c214040d036000107400c080e2000000031348007842181c1e582c443c0d00490041141c41c82a0301095900d110b43e2080d00d42003280301c0704180c83c25000d1006540e200081490900841040c00d44500046004565100c0c0c41c103a0010148180111611402d8200802140c440340041d01c0c2d802003028103c402d2001d501c220000c0482031704100e000310380111500d401401e48000f0303014124001d612500a0300a010640c441c10208101d1880e1a19581ca0000b08035141d0000d55102404101c440242c0d880050740a807604110015080004200411020f1400180d80c160006c181c410103007041800b51070144210900e9035030b2000f51350361841c0b13035800c040143c80025055800000507130404011110103081000f00038003071a030241c4c20008040c2c0404410080d5204001c40d0902074003100e0080c0600c0e00e40382049000141042d00500007103400c0708004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 754670152 1250 754668902 754668907
    0xa090b0718120c080d02060105010503011206020d060308180a140616151b0206160305090c1302040306061505030708060a05060a0e030601060c031d010c0b0109360b0a02 74
    0x101440c02c9036804010040b2841c4009643c2040054400c1c025044214070900c0a4081549801e0001b821030006005410700d2100c058501d0041080c10f0b4111101038601c0242031009940c1d0b0f041550940e04900c8809446100d0140700d0a9180b0f48581c0c3d1009498a01c00d0314450140c07610103004040d002442d009803001c450002c01340100d0181c0e0381551800208000110740600641d105101c0070f41400c8000d000d640c41201440802040c810342111090014680002d081c0d8500c1c1a00d40340c03007010700d180d40c3c0006c16488040807010154000b4403c1e00d0282d0030500400e582d440300e00040c2017041c1c0c1850300007001400400c0c0c17014499080990000701c0108005102038458000800340e41c0300070303111404109001560032080c02e0501c0098010002d5052040300e03021591405010080c00d2f1410400b11840000007240503800340c900100e40c5c2c1d402c418030300076540e11048601e0080401c540e20025000d000040c001c3d150707404d441501d07034110041400444807440d0b07540d42804080c02808040401c3d80a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 754671402 1250 754670152 754670159
    0x90c03170c0a080d06360219090f0b0f03010306090222090b010e07020d032f0301060905060910050d0f1b0816092304090b0402090a090b0718 62
    0x300700d070441070b83c012103041e541d8100c0100303080211851540a490290864000445c0341c084104080f446850801042d107846070307100017154001d01c04c0000109104071500a0110034030350214555050781e11006010034419201d00c030f01c2d000b0380a403034a0003000002c00c10050000400981007120b40c00d00c054955900340150402000c0701d6a0000c814210641d80c03802500c042c04000c080440c014003175030341c1298981c1040b00d002902d841070b00b070821041c50303220034440c2c0103130021818a02010f4a010103d038981c020400c4241e01c990b0081c456540007070001040420545060740c115102c00c03400030207955418410202c16200d9820010148803429907540d40403407021810b01a10340f001640d515181c00d030740d1000034050030a1001414090104039070b811940300564021008409640514182c0d1206042403000d144040b0a05180103402078200b030026003c0026020b50705000314403c80c2c403400141c3d1450341c844e00b01c0b1040000a0711110403007000c503260a000d40b91700c1d6284035001c550185450346 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 754672652 1250 754671402 754671427
    0x1207030b070512060d020906060703140403081905030106050d180f0b07030c030b09040209090304030602072409020d020f0f040e070602280312091e0204060504090c0317 74
    0x4407100d40c0450070000380000d0300c1c00c5800740c07543c1c014001c480b815031070641c6030045a0300b0341e00200424040c030740005110040c140520300d0003400d040f000714020341d540d0f140e103000f40c41508240c0f102803170151000745511100707010300141ca058072696500c0600740000d01c10000c0c00390149200d04102400351716169070109900c01a110031290045049a4840c04d01400040481c0d5a5500910400d40303030411070141950b80c0310006400540450b00844d0b503031070318001c07641144290352005100300d200140010401c0304042403405281c80119010780341d840303030001c801e064440341d0000075840400c610300d00e00103140407202001c3c3c03c5c4014260600900c400b0000c1402c60b00c06030406811584003250400025604201704c601c941044145044c85041c14401c1d0403401400c1c1d01d0040030b1201d40d10a40110411f10351001c0450750700a5010b01c00d03014604001160141803480070383c025801e0400114090074580101c20549900114074003115185840e1000d202201115181503040100149080040f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 754673902 1250 754672652 754672673
    0xf0f110303071b120803010b0703200105010302101b031d1e040f0b06030711030d140601080603061005010c050309100819050601171005040c0f081f0302120703 70
    0x34401c02a08200000c1080c0050f030070b0103d54800e090031106107801d8000940440c0660341194800130942e81c448046181c15504c1c0320403000c0305413101700341000300d11964405401c040d04a034000c1ea0990281b245442044414030044e05070040d0f01010b0350201d000183c4510050f885003540d0018901c407120000c000602948110215410002c22120b482551442c1511400d80344c050407010402840e4865000705113a0300008004a00b03101d8010b418450008003402280c44010381c02c042040004120450311840c40010354090340010782d60000594942400980d041c000d02403880210780c40c52600e8011941660696000c49690106001a50440e12002030b808a0003550f0349070000030740307040101074429003081d0103145200350400701840b03107903600f004280090f4501004407006941d610a0302d200c8100c402c0d40030f150014a08655910f08075130001c1c0500100b02e05940b01c0780f10740c882d00303405034003003000c1e600c20f41070840310b24010001803600684030b044905e903e2058556165a03030b1030356030840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 754675152 1250 754673902 754673917
    0xc0201230a03270305070602040902070614090f0304090b01020a0212010c0f0e090f1f0b0a030e0a0c05090402010909061e27020d0b1c0605130f0f110303 67
    0x20101041c14085581c250103400a400c20b010001ca9001d10b00e00c1c00d81258018140c00a4140b2100084030710900540e601100c1c0a4064001d065540700074600e800c500802070944440c0c00d04a203003001c00d8440d007000c070303c04402c40b0300c0700300640c10b05041900c40b01c001c2110200742e0781035114224202c00141c85180c1481c040c10407240000656000750140644548451100d5104001084100e0441a50b403003184c2034005004082c4052546e640c90325100c840072081d41840d41140282c800013440b207610314001c2001c000c01c1c1d9810301890710b1828480d907444020010081050308441070038016410035460b0954401d00524010741890307030b101e030204202d810300d801141086c034805400c45201e4002e640884000c0924400c001070410344041840c560202609064000d682c0000d07100c40c080c01d242c0c1281400d4080142860700c02c00551030ba43c2c4120031f02076000c865080c2090001050b81440c0c480c01d94419400111130481c0030066592040035918198045400c503251048030517076502d00300003030401e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 754676258 1106 754675152 754675217
    0x105100f0f080601032306040b011803060f09080415180e1306060812041e1a0d021e2703030703030207080705011104090f05060f010c0201 61
    0xb910361b048104012550450003284000c3c050b8800500504040301e00700301000c0210015103000c601d015107684041e80864041020500d0b0380c10200a868211000195031403203603648142940244d0090000d42103a207911481c0e05030030080d0040448088101d0001e0395140910301590000010600214485515156010403d46410802c040c2111806599007050810207450140c1c000d1b115482602c8510917600c44004540c10224007644d8100e1083c41e000d490080c0e807540c09a001060603d0440e0f403c0180c04d5030703951400040b0a01c000100784040c0c1d03903903401040310b00c5061418841d0410880c0001020703910750340001201c2109915042c00360b1036032264204408203000b2814058595420100708030f9407005500000c0003a0703905c11101b00402c07464424a0801c640c0102c0304603030848848641459190b014081100000340305142c4400e26150030480c8920340101c06069024 = true := by decide +kernel

theorem cover : BRFrame.Cov 754496402 754676258 := by
  have h0 := BRFrame.cov_init 754496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 754496402 ≤ n) (h2 : n < 754676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
