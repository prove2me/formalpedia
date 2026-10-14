-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:25:16.309146+00:00
-- url     : https://prove2.me/submissions/2ea5ec9f-cbb7-4f5c-aeaf-056e8d1c36ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205035971 ≤ n < 205215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205037221 1250 205035971 205035977
    0x20604031e0905030a0c06030b0a030f08180a0914060d121d120a020f0909070902070f020d0b0f0916090207020303040b030f18030a0e09100e1e06090106 67
    0x380468041c00a0510300400401807828507245502c07036001c24030300081000c2c1a181e035002c50302d04001165160084110061040e110400404c0c43d59403200500c103051074008182c00f10100b0900c11f06008070009060016004000b881c000c1da0354000d070300040c401000003a00d035100000010b06107050214131034001d1a0710610b0341c1c100010340a0b0032202c0e540f00c50021074a44c9018529000707942d451030507605941c40408080c000006041c0704004601c4804142c01c5d008403400c0301002a07150010031200203d903503e85015a070b071002480c0083d0707058900c6030020b42c0115842c00310028408509030b45407284825040400701611414a015070703800550b951800d01c00c45a480c2404001899009001c40e98400707002c80f030500382c581c01000760706e401c2118a030b4045a200f03000c000c800b910502880180313902c4040070f580f6200a50700010548500912414010040f0741d000c2a51030301d0a603a1040103200c040c040744064103280b031700c3c101101c407665012100550031001007000c500d0b080101c1412180d07030391 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205038471 1250 205037221 205037237
    0xe0702031c1503060e0d0809161505071e050c030f07051309050f010b131a09060d020d0303020c010f0b3319030501091406040b041107060c02010c02060403 68
    0x70748040060304010401d8600e403610020000b0000710b082c06120840c000c0000903082481c09400001c080030f40007000c1c2c280c0c6901405210b40000704440c0e001c0155908058002c04030740440400b52404d11440400800342c442401c07040d2601198103100142451041003642c0900003904109a40c464000c2d601d02169001542e0070400392503c41c84013000c0b49002c0e4000300300c420141d107540b802c010000036010b145075102d0326901c403140b411603107134248002441c1e0100b02e08a0320101c04110411801807090051880c200424000d50314040a481440d5008289510450f40307458002c1c080d40241900b86059070806104030700b004003d01501c2000700d0040d0901d2000305076100480a4407080a85400311840d0040f6007605010002006282441180f00b040304d1020030560001d0440b20164480c4150030310300307454212541281c031100c42e003000d0200c8010502078031b10800100180f10150080550000c00502801000000c2d0171551240c0c8003034008001c5011401c40c113070707100c40c400c4400a000650710 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205039721 1250 205038471 205038517
    0x912050705060f190603050a050c01090b0306040b06070803090a0605060d08030408130302030604030806010801060314061003390807350103260a09051311040f0e070203 74
    0x445210382c013041180b010700c8003076a000d284000300c0c0d41540007541d442e040b03042e42005006d0204540c0d05100b100b0b10748585841d2910400712050f00020308000c0c490f54441d03801192540c0c400042d101c01c0c9401414013a964144003403210b0380c3d60b1043c10101d4a15040000003001071410580c07a414003a08016481c0c80c60755680d43c0c221440c0d1005415006640503c003011000d62810060395201d6480380d210340e003040c01c0010001d003042d40142e20180c01c0506000d0700c6800d502d01442e41d42d40100c0142d0b1180d051703080b101c90a802420010b00c81482031070400f12181c1c04190032503a9010241e5060700c1c03900040d52040012540c1a20848200000c208144801400700180f4088404078140000503d1510401100301411100003a1700640c0c040604602c80b0a0350705d4159800a50a01842002c915210040f103000d400d007400751103103512881c901c404a00403548a0303000350300351026994200360340702e486600f17400581500d4090054411001300c0054080350000007141c06821401108441071041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205040971 1250 205039721 205039741
    0x6011e0303031e02030106050c1203252007091a030721050601060c0201110a0309180b060412120207060915020f0f030a170c030a2706091205070506 65
    0xe50f40801c114001440207500340c00000d48041e502a00041e5103a0303640e0b41c8a0720003103140000406200d2041c3c5420414012814140ca140c1108000c0b10f200da0132803192044003d0b14a500c003c000700c503900d603000c0c0800a02200c00310315401611142c0f04204551801c040d030858010a00c1d6841039095403107000140020541d10004002d013075110780c0302011280d00d07540d88505110f404c0c0e014a001c5540505580700319a000f04240150f505101d009100d001540e0328002c3c02010b41b4440c0ca10902c404518205414440b9000074020300405490301350781c3c50350b80c0e10b0031144003494081607580c6101140140301e03891010501c04210762069a5808805049c0300688100345461300b041810341c4121441c503d08804284848805d6140e000003450312101510030240c0a00039200c204004c80816004004280484405036500f000c124100041d012108262a14103050703050240c50382c071040d4102c800204071a0b0307003003640401d00c00c9519420002d0f1912041d45d8034002c0000c0201150046d400289007050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205042221 1250 205040971 205040981
    0x6020d051c090c031703010e0f04020f0405070c0506011e06050a121e05180105010b0a02100509070305030c030a030605010e1819090606050307140117090c2106011e030303 75
    0x3008440e080607040e41c4c1d99a1500e000c8216070760f214540e00c0800104003403040099801c8d4041020b039009410f13032030603a00203100020102c0c44244a590340c0c0c00030641082c030803007500120b160700604a55880d40c44070010f0800109024040d445010740c0707100480c07001d1241041d1000d8000c07540741d040c0c0000e54020084040c0c8000300050409a4030f02e50318504500031409a18003400600428804045103c5612400d44205821010600004000d02c900c06540022000101c09402c403001880751207040801d42030030784541c406003851001140b65003070b00a01000909910111340c8040000c2542d40c0c005540f08001d2103031141c2d01c4203180140c0070007510315481c050740c0003100b416400140b01c01c9401601c01c455490070300b95811075482e607081c80a81801c00134407029042c120b40c000c2d041400c1c14002080c03a11101200c00007485918081805a801007204019042d002414406020b40e501010070f104480303102c10381281d10461000081d001080d40040600400700029003c0c0c0310b04540701540540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205043471 1250 205042221 205042223
    0x61603080a090c240905010203040302280312080703060308090105070c0b0a030603060b09040f081e0d0c0305180318030a05030408010902031b030304090b0f030609060106020d051c09 80
    0x65100e801040000d161400d00f080a401c0d81310710050004d000d60035a18912050241c8103003805030014041c4250381e0000140e5040b00d6048400002048102c40d8200b000c041c89844400b103e8a030505c0031007048030008035049203a2142c1c2d00e040c140d6841103012001e80b8114032014120410420907505654854001400705074081c110307003205103554014009055001c1d46400000968400040c81049054001c0f1040e07117504456815050816848410000e001124011300f00c0030b0029059100b0108100c4800e446010064260f0311082e0034507803070015140c0e907248840080d1404000074003a8144c043c10418586602000f07508000b40c10300c066022141051415031316100b03080382d44000800c00c00081001e41030450011805180d18410705251046a85401801c402d402e402108a900d00000f501c04503095554040342800004011a8030800c80c1b0b00c100d07415005210070490302d078500244840c121402582100d80c03018408074203c0301800b9945000380030980e03011182d40c48801541100280d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205044721 1250 205043471 205043491
    0x120303070f0c0503190207171b012006040303020d0f020a020a02060309010e191209031115070b13020a09141602030c0307060605090709211b06050c0c06160308 70
    0xf40b6200110040300175045900050340662802d114121001c4100042d041c81c04d0004e0440000030213042c808600150384143c1005099409440d808c402c40d41c0e0304801600150541e485070a142c01e0003000b075800a0050102e540c1400c0c0c1c1c11100a03401c0c802c031280341d205903001d003401c440c2c660308200d9a5440900b07245455901c0342603100500d0014029440c41c0c0309002e9442c12440c4140c985010040001d04640c014005609020800300398405191018800c04540f603202c1d082401256110501030b020026207086130500801c1040c504407030400324680d008950010500356142094000d5500000e2405444d41180007c0b40c1c0c14280e42d040d58103190514016241403100703016006c0d182d500109010b0b140f4a0300c80c203080055082c007182d22a004806da00c1d01890b41820840c2200c424500000070750300c00c441c41e01100c800e2084c202c0903105007a07800001c0031100307a682c1d00e00070102d810402c103240301405450315290a07407602404a948030708050102c00310460482e10142d1303c0d5a8018401400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205045971 1250 205044721 205044727
    0xb0918070201320a092105130905010605040b071509080702010207150e22051e150607230102040f090b0a050f090a0e030d0501031119090b0d051605120303070f0c0503 73
    0x200e5400b0340a1580c20282039503641e448002c0c1d603c23001040c0243c0e17849504168508001804410b03448011507003902e90f04c07640541c0e504a14035269820a4007151101d120b18544254101044407410040240500136400c803a000303911034003a01c003403100e680d000350041441c1c00100300c0d542c1010700c9240e1070f440040000c19450f81c140c07900da0050310b104032590014a10a9401003240c43e4003200899000317140c0d2102100c1c0714800c3d030003240f1984070b0b4600113000b0256001740303035140c0202d024140d248102e07000004e5441356505c45250401c0c02c03650191441d000d0a020018940e41080740e442002c5801c020002c02d00700101d44284501c00c83c014080f107003001d40f142100250f080040000704142150050300213100e61641c100030380e1024900083c42d100e034017101220084852034540d15015181c01c034000196500c0d0000000d4200e5207812001085805101c140308242c1d4081041d9208881e02642d2207100440e5901c045900d030b200844a0902088800361803003402841800841d0960f4842d2085900d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205047221 1250 205045971 205046003
    0x60e042f1017010b04081005011202040506030c1008190e0c040b0118080615100c020907121a040c050705030a0e040209060705100e0304030b010b0918070201320a09 72
    0xb440509030007180c81c2d00f00002d01084200c0b42044109944c2002600c20000f030b506005081031248244807001e0b1207140c55a001c6445030f40d0502a89040d0040186158907000c0c0024028222517821500c0c00e40307041003440341035100480b6000b965960710000001e440d1260400701004000c081007a5110b04001c03803404e011510504040c00c01001d081d2090041040d0314210101003400c20754078240b0b0b80910800503098400307036000024034020b1581190343d090352345c6c0c0c0d5903c1103a034559290030341101d950401d0800321102d50501b0b5807803244803060728180901c02c412501503c0d584034407040245154401c00c0305140381d5102791101046204010409032608cd900400640507070445481602d881e0403461902030308240c0d62040c01c02409548000c0c504051a40c2c445c032070241c0e4140301d041500b0500060742c510641d520100c0724600d0030110340942850401000c007c1c001d104040382070500c000320081c4495550320040c4500500810541564207550703840340100080c2ca1516030840c1c80704054000d0072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205048471 1250 205047221 205047257
    0x6020a2616030527090f090327091501020607030b0402130b0a08060901120305091906020604030806010918021c020a1701090501030c06140904060e042f10 68
    0x200d030305029640d00350300d804040d03074a407560b014110782024055082121102007a05e80521080c4d00680c1100141c01aa84100d0060301b03506c40c000d601208094000440411094500c026492a140543e0402826580d403140554800b05800c1c45501680c806c0c0c00141d0030741e110350002d0f4000c04000d000582403c00c2c1080440a0f4072407a0000d0340350400115070107803155801005564801811030340c1da01954541441c070f40034014000d0b0094104240000e013800c4544a0301e01c4c1c49038030b00440311813200540ea10440291140f00c240c40403400201000c0104001d50320640c1c1600540e0001422080102c4104207604005c0d400620581c3c2c4c0e50520701d00c804881801440684805412034449101c0705800c040c00040050050b0401200107141c00018000300d201200600c040d10420700f07054070703080300c1459103101314003814880681c42420003501180101c03214200f1406188540142410202641c00f1641d40290440c3c06000d400700130702c8000081c0c5040b1350441e6501c40d842c02e0074900d0b2800d2840c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205049721 1250 205048471 205048507
    0x70f080720090636010308040314010506010e0405070e0d0b0601020c0109031520041202010305060414150a0812070516030b060112020904090f0c06020a26 68
    0x40da01c0c5110345400c103101074079020300a111100201c444000614000740002d808408a140d80100204201400b00f03845500c8003428001e41c01c8408840520340e540c0c60081d1840c0d1103404104e1740103854202c1c600c0d540805009890055005841d5940c0c0400c90400380401007000400080410601500c950a40d40700d070300001c0780e8107000b041500100d01d82540003901e440046900c09041054200082011803802030322804c00900382200400ca550032621840058240c0d140000c4070100d0000e40041d00e241e91708103403002c1600c03c0c1c07000d011a545500410048440034bc4000311030f0710b12540010b119540848115082c18401802c07000d405440713001c01850715100700315140d847e0400003a01414440200402e030b10178554542221007450455464000181000e0851414410710203000d54807038540d5010b0300c040c200050310800160304103051510810402240540300d54030581c40106200d440480c2440d9110303000389005510107003442c4865201c008040601c83c06c81c1080c0203240c1c00104038142c4d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205050971 1250 205049721 205049723
    0x15050714011d0f0303180a0c0b03090631210305010e0115050d020c0307060207112407031206030c0608010e0c16030f110706090906080609060c070f0807 67
    0x1c4000b981c0c41c0160300d00d10501c80420140e840f01a80083ca01400000c5070340c1300b030564408612021304c20032850701c2d0905580006040c0140c41c0404030700800b6040c0614461400181215850385603207581004010521100a158000100500081c1a4030081742e4042d03d1182c2d1604866031006400e00c0c01b44880c0e01c4901001035102e000401480d0b901c1c0c4d40340c40c050920482e03002c01500385010f0281c120311540c0045e071210b54003c2000c0c401c6000c103005807210542c1004082d907503121586000c0111a60400d61544207803000c10141e419502c0581c0003161aa000c3d112052030702201c0d1f00c081c2c41c0014030012180780603843c1e20f00400010000394020009112070b840e080c400c0e504202108004000050810744802c1d02070105820801c6501010880c168041c1030040c41500c90120448410000c942c41c45120700c1a001c000a041d98003180e80002c84005003400c114480e2a084490740b254000d81e031210882c0c3c8a8030109003c02e0032a001880c02a108018114043c0419601e41c4c0c882d4100e910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205052221 1250 205050971 205050973
    0x16020a03140703021e061215030a12030c171915080a0b13020d08030a0207060c0e0301060f050d03210504030203030a05060909150702031209010603052515050714 71
    0x2c020021800c00081c80030502c80c1180d014481c1104001c08105a805034003000d03160201c00c00c0100d44204100c0d2107040c075540c0050b06840c41d00380c840c24030540505652806100182c58081800043d501c1805984000d41c80054026026181c1d03500311551494070961201c240303913444008126900075409d541004000744d030083c048413840750404601c00c0c40c2c000d01d05004240740078180300040c4e40380d484500c00e480d407005045840f62203204100000f401384290041000f0700d048905c0c1c0410b03401000c4401c01c0d6a0441c000e20000303803244290302c0c0c55a218410325070032500b10044a0300180c090384161000103c008041c0d1404100c103035000d029141c00380c03810340c056007001082c858140301500610713611040c241c030004141c0c1051460180d5512a10044009006d040d1021500484c400d000b281c03c008035000f41c048050519210040c003d20191004844d10b101e2410f5090004030440b00011480404031943d1607200c0c0740c65031340d00c4140914503280041100800080000030b00c02c41d0006400c2950070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205053471 1250 205052221 205052233
    0x10e130e1009050705090f10210f210914040c1103030406020306010e040605091b0d24170607030e010b06070605040c2306130b0a080a0c05030c16020a0314 68
    0x107000d0040024001d0820b05e04049454104000342c2c4001004d81c00b21808080701c000e030b000703000410501d030042e00700d8002c120081031242b40d0240a0000d02400b80d0000d04903051600d0440040241c810060902c100002548044102e001510349588011a805503500f8a45c9040d2004902581182c2c01143d04654955000c010f10005582c051144004c0210a40e42040001e0514000604e4002c0082040100307040d40311029141034145001e41380040341c100000d020464100311001c036250000d40801b0284e001c170f2140010680801c141511070390790614003820711a01e039001c0407800351600c1010000c4e00d64869240b4603445c0c59003801010b8050181900180c1c41c1850f15101c83c0f00400d60b4826107101d0820307050881a2429a17484d5500a842114074075a06d450026902c4041c803a943e11011320100081103525400e60400303007061140c15200010801c1a0100005540340c2c0010b491185900c0c3c0d00340310a01c29001d4001d1f82107000760005100031300640c0e580d9650241c102145600f160345070880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205054721 1250 205053471 205053479
    0x100507080f01050607030903081602060a0e090f010f17030408071203031404020f040902150304140610030b04170c0609010c0e01080f0c0913020307020601050a05010e130e10090507 79
    0x8049010b014280441c0c00b1880c00b40d00762001444010710307001c02313001d80000044102420300d00501c1800040d0303014003042e8a07080800009400e49181d000b03810301a80096001503100d600c69050941030350140d405400300f160400c030f040100324004400301c0102e03100c1080045000c500c10850381000708449a41e0340342014103450000d017901d03090150008041d1040c1b01b4080141e0790001440103010054800066501d821300028446130b6541ca030507507a03440d00005120a0102c012100b02001a101c003c84420381c44611050b001c0029501c00901400450408240062900d01e0b000b60409400c44825003414010101c450070001c082e96280c80076076450007084542c50304401c02088620007401c04102d1490f00c60110940107100030b09013150120000340358a01030360382c000c82844480d1481030440d200c0c036203140083d50b01c000a000300303841a5441c020000d402d6109070180c414040d030161060541407813020305040900f45081c48102c0c1c90180f000c1d003511180161103485480c0d40920000d103405868 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205055971 1250 205054721 205054741
    0xa050d021003091a24040203040309140103090803090c0f03070b04060302070f020316090c020d0909091b1e1a1b190309031403030405030f07080d0f020304020405160f0c0510050708 79
    0x1105081714019070040c020080401c1e08001c61b103044a08580180141188400049008055400c00200400030110a0107002e20000448103003070721040ea41c41080850702e100b01940c446c624814114040020003082c030425110340c0141a40c9071003003020511101440d400281441e40d019203003400544145020010500f083c002c810341d448850016200c0c4041020009001c84d644e8001c040485072518000c0c1c0c1005001a00310b60642c00200c01c401050b0749911202c06800980d0020f102c0d944003009012070359450510007001c1810584c60110701d000c2c000503821203072107550303050b08895000741c0701410a0892081c11104586102c1e95903005440c4c01c500e4008001c5407641603090495005004000c0041c400000702d80802030ac100c0500c4c1c6400c89890107071407a01c102c00d00c000e5602e0601c1048940c000c00340d006940114400c0b1414030065035010314907051070305601d40b40400200034220403000c660242c4240b40c0c1a0b40100b007981c07000d0101c00006001d60750141c0c2c1440029440318100016110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205057221 1250 205055971 205056031
    0x209210d09050102120304080c0105101502010c1709070504020301061106090106031e0c080307031d03010b011e051204050c0901121208190905010204050a050d021003091a 75
    0x100e418548072060900c40001d42d510001c01003012540d8002000c03605002202080d5039000c9100c1c1c000b40514502107100c0301001c40d5500c03603117008a690030b101c041c89a0040c000c3c4488c2c0f0000307944406070181e0156030503c0340e1902030500f00050007030450104a0792164001103003e4070310740e03c908204d20314403001149444401000c0c500a81d140041c00e100084680b481c00c200358800c901385021040240c00c215000403465805410280300021712003040582200c1d240b400d9100b0b01d105100d1401c480002c1c1801d84500d0008580002d00814042840c14154007440840e58513501d00281040e64003042400c80c1d440503542625079621030400e14115241001405000d80580c103041c42100c6201ea0b50036118102c0a0400320520100c4070001d40088520004040c000031484000c0c80b10b50394034100315002354040e00606000c3c0c0c42e09000441c1d181407103040f072030072168003511200282c803504400b1402411901c0d02102c402880300360290a615441001a000b048090110888922000c64240300e01c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205058471 1250 205057221 205057243
    0x150306060f050603100303032a0206040b0906070c02041d071205060612030706090201170709080d02070506070204090614040c0e01090902030d141918050f0d080a03020921 75
    0x10034200200070710890049070980490b1f60604002c41e41c40d20880003411b5080486c8001c0c0c5506102e64583e03040709070b0001c0c0450255000e059803800c1520b40510b41c68603401d0407621900030543c00c100c2d007070060038030760311503000f5a0381d101c019149405685c0d0000d05001c40c5911500d01a840d581e085e40501406202050f0450800c40f150012580b41c03c80c0d0a0b128041d10f80060611544d6841d10019a40a000c00342d00c500405141458285028500a00808428000c501c454450504c210f00d80d1400061424140c482c0100840c0c200700056017003001414000d40201e031056111001815180980d1120270f014034415000f00d00602c0c20010240009031050740004051414407500c0c00240e10040381b42040b440d29031034100c0709892280c100c0f5601c0d1041301c2c66500b041c0c92845102e45010b901c820244919a010f0303048414580c6d83d60304000820035400007080e401404c03803003588005a140c80c0103150f803629034180582004801c03000a03050b5000034440304484507000b80481e040c02c9040c85095801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205059721 1250 205058471 205058479
    0x6170105011406040510110a0803090109050d0201060609030609051e030d0c03020f1209010605090c0a0e09100b0309011e0902090703290411030709050316060203090603060103150306060f05 83
    0x20518040c0006c506008802d0707079005100050310860300194080c407528038800e030841515030762400c00214560003400c01440c1615a409184150000300d0701c107010303c000700c071110b5407070001960540d1108030042003c07001c101e40c140b0031089070080c1401000804059150000042c580b0b903003016244800380e488403008041018410840e500304400c1c00c4090b5101000c4c00100d911190380d801150a00401c82034000e0350f4400c0d5140100001c41c2e81400c000e04a440142d95005040c00c02c0600344413500c042690b10106d10b039030505003400302560a0000c0d561140d48c050000c2402543d402c4c200e05900303500744904401544691812041d8204240c0180d000a01c5182c01c0002c141c1c118130000c0200300007580c00410600c2c000345503d4075503494210b001c0c420704031011030340c0c1e134200402e0142c51101144500c43c068041c1402040840505180780310484d407198015500d4219400704115082d40700504442c1455640c507104188180c14000c100065482590001035550900344541d51000c41c075400360384070f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205060971 1250 205059721 205059727
    0x60804021905031e030d050a0f06090b060702010e18090102030a1805070302010e0420030402041b02100b12010f0f0b0f03120a030209030d021005060901120b090106170105011406 78
    0x2041d1400a400c0040300c82c0c3c0011400e507080d004c00018110b21030760382400c0b152810041405420189540206c1315510310100401101c1c2c0c4c0c0704500c0003690000450b141d80144140519000b40d40940c403030345102a801020100c8280080c121900280c2060300c0c42c00c82d0769808410021806032521907551884c489240848603101c2581c3c07069541d080500000341002100c4070800c0b06500c443c0c01c00480b06050f1280da0390150a103001900080d041190164461402e00050140c5075441700c0385805035a0103a03004c2e0070254441c0784440042c0c00117640d240d8100c94001e03200c2c81040b80c01c1c807039100c4000301740e6804500354200c04548000c1d0303035070b11729140d20480c8461a0301c0159540061001c0486800085058892800d40d50641c0240070b42048250140101c840d07480705070b640854005d0025086d00020006a110341c0d09001001e802401800451562500190301003547c9600786a441559007001040301a1240b4528018071400062132440703a468000500a0812004030f4508850301aa440b0382 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205062221 1250 205060971 205060979
    0x702010c0c1509030203040801020a030e010506010c020a0905070c0f080d0e060115030e0a020312070501051b040302091807060e090f0403021207080405060f0a1b03021b0a08070608040219 82
    0x510b07101004500c80700c1954038000603041500a0094034018640c01c0001c5468442c0044060003400021398803800c0e0f075190900041240d8010350394680c8950b00a00800200c07810040264014400904690280074040b01c042000440340305a1640681c442c2a0903500e0300403160000c82503481503038000001d50840001031225000028031042c504007146404070310201800c45442c108480c689003e50940140809804d440207640000c104a03442a0002c100c291748940800761100c50301010700144880400c4200050301e045000789411104090440c010400e0444038245840c250ba07010030b020030911065240c1518013200c40d00c1c1d2000e50034030144610300e0300c0d1358000d407120640b0300d000401007804030f40d4505104031942a140502405440642d4450150592001d50f40100c041d000000302c00840e48502e0040515225881a901d9002003906001c0030326100c252484140900750004010380b0b001845920821800005240c0794403038802d94103040c0144000d8a0a00b2003d00e40144070040804c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205063471 1250 205062221 205062233
    0xe0906040305090d021c050d140a21021b1c0e0901032603090c09070c12080c1e0a0f02030c0601060c0201031b0806040c0e010e1e09040303050702010c0c 67
    0x180c6503d0215503943c2c00198030f20016040728100d070070800910140c0c412003020080000707034110311010035495800031580030900c0d082e6903200340365009000428a582404000c1381c40714400303c081d20711040c09070078900d1421000e0150340112598264540c01801140303418400a407140d0071041d034500d001500c030f000180100f81540010707c0000d01054810380c0d60700f03e5034494800b030308a00003400c00181d920700b40088419070343d00b145080f0718072802c00140403940d41c0d4014512290215440703180e8400001c1d24010660300c00700001c288000e10b103010450307460700100c100100340b0320250000700d80f500d44001c54801884000d103115414159803007004900140c0d0400035040f41142d0075450540c8a003141480101e001d4529800215a545103000b00398010507000a00ba51041c00281c40401a03180c144a046803913800174031505002c2104210072810500340398611071254044580c052520380a4000481c600d5201254160000703599403040c480c8c02c030303030a019007421407445103014440001580c81e20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205064721 1250 205063471 205063477
    0x429070507050406120c030212010e030a0503010e0609090604170c03040602071814040b07180321090b0f0705010b0a060c03080105030a0305031f0f060513090203010825030206040f0e0906040305 85
    0x6481409d21080124016209401405841c030301d0a05036501c5242d071500140ca0b82d0020700581e4483c40e60f1400103601810995440e61140012030006c110544641d26203040c21841103101c03480840c0d04105203044240104020002070646030b004080d0f192400324201038103c020510466054104100c403064442e2100b295908640c011100e0040b0352910720040d03030081c0c2581c580301001000810000f003441000010039440b031107107840303815904a24003400c8505030400c0c01f540c19884c2c0d0038401349041c0b034007810203046100c0c41080009081c480080001c0d45c424620740c004000902d8400240040550200d28203006110560040103c11250368015050340002051400543c06280c90404d2401010004074010090424ac1102c107584a5030001d24552110654900d5040010782c00190083c26200303e0b81201c0c2a50050b12a029010040d14108100c482d1010b0105503e07010110250303403807500610040640381005200315251800318202e07502c0080c1600c54541011040001080c0c2040403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205065971 1250 205064721 205064723
    0x3070201140c030d050a05160e0109060c1a041128030312020d1109011704021e01180603060501030b030105150603130f060b041d030429070507050406120c03 69
    0x32aa142e0403415880c500e98010002d10a26450800e8184400d40c0c0c5154401401201c1142002c500c0e40c01e54981510070400540c0d4050000306900d8003080780b00e2242c4c3c40082118031452a5100d001b40b901c03000b500362042134406075038501c0c65070784845c0d051600d1010746641c80b0114480c80c1481051200115640f811484080c041c4000d040004404030615811500110110f24042040c040030100607001600510303a124041259441081c008802841880b442198010003100454201e00c131900141141c0c48403050500c0740c0e100c01c0700851070414056002410031070350700140d1640303450001401d0311403524540703019904d0b22042c0401c03803200054001c1c1402080d203000341d4030388481c2908072101c5810b00006c0d110070800d0350202c0030090b01e034110844503041250244101d1b0781d500c501c402c8800000c5003580300c0f580200402c1140501000c50306540d0801091640080e82c0d6024506140c2c5d400048102c8183e00604014496468940300d8000038105041144440181503594079800d18902d000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205067221 1250 205065971 205066007
    0x32e06090e0c04031a0603010c1103091c0b240907050a0c030e0406060305040b0f0f0112060b1e21070302010e0301090602040611060c09130c03060e01080a0606050303070201 76
    0x800030b40240c411804450081d0350102060028108440c0d44091011040d1416071180d401c1c00d10820615110f506880e815103007101c00307580381c07078504803c11408601e040c2a0790301080e0041d050f0000301c1e082d00b084a00c14004421400c0ca400b0500071000c182c0300301606c50612503400d000901005a50000545201c01400d040182e21984a810240e0f00f801d9440c980a41c003604018006c1440c40e80350304020300591084202c0480b41c0c459084402c030340354086032034011080000c1300404c515250800c03480369840c0101e40c001100405640401c8034103c000a4006034000500e00d501c0c2d0a0034840140340e9080e0b880604c8480071a8595100d0b40c680d241840043c0c104018040340043c141e50a40c001c800c075030b0780007100b10358a40d940c04000e0310710250b03100d04545038026203000880001d9004200c1d281c1c0900185000c5585078000d0310a0014501450700c031040550b0317031101041c004c4140c0ea0305806041c2280c000c00c2d000c2160f24000c002c0e201c070b46d00700500070b070814031007000180d030004102820404120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205068471 1250 205067221 205067249
    0x2160501180306020a030e0f010204030f080313060603080a021608060c0702011701090b0a060302030c070305070501180b06190506040e18060a020a0e010e0a14010311032e0609 77
    0x150911039001c0c40350400741c803492001448400700c1c1d41550020312407400d95000e88400e0000401c40d10b08034040c41c403001c4c0036941080c0d107000000c0c6c1c00000443e800f810a030840d50300c402c41030303e4050803a030307941d08110b83c00d20002030404005501040313908030040c41c29192035440741c00c0c940c03042e803500b4015150f242130f0000400c25038216030003036442c0041960804040885503030340d4250000506200c0910360300808650101251142c403900880b0311462030000d84501c2c0041070369003101ca5610400742035501d9542c07007005250025100140c0000680140f0268803c1e0510104100b0250200004601c3c0b444410204100d140ca480b41510300319440051120b850f50f032090750811040d5840c0c82074420301c0c040c00e02000052003166003c0d05125031165980b106660501300103440220888003203a80c03184200d031017000002e02c80c644440c0101410f240200f4050a0111400125001a110400c2c0d4840801a8900800f88415082a010009102d0010380c500c0d00c10080e0102c1100c0c003480300070740e01c4c81e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205069721 1250 205068471 205068497
    0xb1c080a020129010806190e04030912150f020a0c080f0c150f07050324010201150308180f150c0a021f030615140c2e0c02160501 57
    0x70f501100000b5500516144119810704841c0140c441e0b54010b1404208001c02142080c1800201004041110703011006840d0502844505030203005200b10100121aa03020500301244214008141d10614042e0385a0880404200568080070b200b280c24900c10310080c0f0189a00c80c0714900c075542c0104441e0b40d0340e102c01c0541049031140d10044901403140ca07108281c000c504010803840307100d412108a030b954444c0881240c462009407103400e00c1a88000a840740c1c1514030445031149101400001405045281c1e65440c518850b40f0030369918034081402c802c56200d5050800004a04841c02c40700000c10303600156400140300746107a401880802c020040c040c0030011005c19035002802d04084114520701c81442c07454510306400004d05144002614461604c40061010055100d0042c40306082c800001c56801c052070620142c4211300c0c82c1c0d20307001070500e50020101320b460540032220300a01407000076176000440000440d400a20444810134514a13028165002403801510480e21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205070971 1250 205069721 205069723
    0xa050910080303070815011706101e090906050904080a05030c0d0203010b22050a05040c03021c0603120e01080105040b040b03010e030d0605030609060a0c050408010f0903030b1c080a02 81
    0x4141c0000c0346612001051110326500070702030f544601680d0510985480803c00112240203c03494902c4040c81c450303000c43c84038900002142c48101151030807920b0055540d0b24bc00c42d01948884140109605120600c624031090150344003400007a40d4150607402c043d5a402201e02c0707001180400c004000c4080303808022036004481819540e1901075480f540c543c04100c11a0340703c5407100d18170009411220110030400c00302d00e003c07560003d0000ca8041c9c42c0c00309020140900500e060304140d800c000340c0600041c120115003015621000015030281923152240c00c04031034280c070000b4040742001c541c0d2103a80c492138590659000f0f95020604200740b101003005050b001200e50351550800c1064142c80da4000f0103800d5101d86c1d940184482640c03081896210f800940e040480764100b60002480c024107034002d0742d031800d1281f81c9946090742c0c85000e0f81c2100c02229206c07041980b070300b13580c0061560501901141c2c12007214a516561601140a07811030702e442e50041014030040b800c1004140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205072221 1250 205070971 205071001
    0x30e070611120318070b0d0b030a0b18150408070201020d092403090b130c0621020322050709061a07031d1306050405090f0706110a0c03080910020102090a0509 70
    0x45903401c41e102c882c6c4503624081141c00071202c2c040e40c98540b220b0f0300c09070324000802c400100c0c1c100340c0c6042581c5881420940c4400380522071401403241681e0411846224044540704902841040e51640c02d98400242040c4510070401c2c03c005500c003003848254000740d01c8e031285424504808003203030844441a000780503d503002500c00e141500030070070881e1101c407100b411240725218201c0c0854032001c0c262000d2554031050016a0800c40000000e03003001d50066401c12100800140c0c55103500c0340c0c1e001402c092180483d0180c01c242020410100c3c1d80c0580d0000d0300c0c6000740c8140c83e070704811800c1560b0080c2100641088141a80759403425030b089001840010054108c0307580032102008500a0581c40c07040034001c500d0840020000304012688220750669100680a820b20305502100c0d40b6031010203031031540c041c603d0020001200454003600a501c80c0f1103054039440010200259218401d1018055900400441c0810343c0d61200c1507050354400c6485003200e858102000748152 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205073471 1250 205072221 205072261
    0x10050901140c100c02060106021b0409020a1e05041e050403030e01020a1107050306040c150504120b040302300d1b0c0510110a12090210030e0706111203 67
    0x804002107045540c1c0e40443c90091440c402d08051000101656080f40e5860091187c0b2005800c40f03112907042e400c08580d04c8d004803000510100b01c0340000c2e000100c95030629800f51941c402001c507600300710942c40d901100185001c540411200e071202810464140c1c14264080d00e5641d280000340801d40290300c11450702200790021502d0b150340c0d0701c010740042b0844921a9661191000001b0a85000190306100300d40c40403103c07800b240b0380030003c000b07482e1965401003406000e100101c0c40c170428620306030601c0d0154100d40120700b01400c0182c02c0540c03855540340500e008503130100304e802c801c013190900c0c48004c3c03808a9691b80000d00304001071401e003070038550311404940c80303214555000041868040c083c000343c031058403442702d041e403c9a40c2c05a1104240c401404110890b5018019450484040500110300c6800c0e982c00148018880d0700d505002c07961703554a50800410401800c400f4040d54144404c064031034600441d0b0713610b803003900c00c001c201e80040001d0700120480f5003203402d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205074721 1250 205073471 205073507
    0x30403050c10050411240f1303061401031a040201020c01050a09120b041202060106020a060504080f0c10050c09031009020604080706030204080d0e0f01031d0a050609010507030b10050901 82
    0xa0f01340340c544001c00000300b543c0c813481906140c5a8110103582240d141c02d14081010449292985000503c4520f4003c001481e20011440100001082c00d030b0141441802c603042002080758114034ac41022503507c3d80d09002c480b8800c0c2d0422005036000a101c1d03030311040900341151aa115050100d86140f580e4004001403100184004d003080401c4c044540164841c04800c2d501071031020003240d660009115080c0164000740c4a0400705000f540881e0b0000d0240d1482850640b40190f034060030342c0b08101c0c21174035074003a00c410910254103108403504602440681480d0510020001e5542c00c1c1449000c4103d03540c4011910465a4000440380207001c4c410594156a560f448090020b41180c0304240c0c031801220b90044400788170300850743c1e1402d0001d08106028002d03800450007491105990041e1101401e10103203400303400c0103500b428600c110010080f1b07151240c00785081d598058001828507082800c07480c90f03a980d92000c11881e505a10b842d0380c07102c101d10012120304113602206400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205075971 1250 205074721 205074731
    0x30506060405040c0503090c1008040605040503092d01050f09060d06030219140f0a03140a060e0c01090f03050c010f030b0a03060e0c2209030311030106030c080a05010b030403050c10 80
    0x40c203421030040c6202c1c4441c08107131080323080c0c0f6400b8000111102040c000c002104000001c00244103a131180d90424040c10403641001d00141c0440c98040c090044080307001284400c8114264500740c0c0c02c03200e20428601a8180000024040954029a8800b520444d0080341082e5410015401180150b4004202aa10907241000270301003c103940588039440050448414090810050300410b00760090042e0700071602e50340715a2007548580b0250100d900a40c0f641401050b918003643c9101a4100064030429942e44005000041c40e9804440502c0d840d030700c1003012800200e41d00020041c2802d08486034520002d00b1001041d01286040c0e0005003518003000740840ba03801620b0b4013071103004551420030048104a0790741c00500c03940499000b40c21601c83c46505680150718518801d0a01103004c450500114035a078109811060001c0e5032419002000c0b5401a4040c4d00005070030f80c1044107506006510b6030500c0700500240c144200040d08a07181c4c0e00810a00b0400f90300b10100f002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205077221 1250 205075971 205075991
    0x50a0b090114030f12040f140310090201030b03070b18090903040b090d0c030b062107140a08060a0212060d0c0506070809030102071208090f0718021314010212040e0703050606040504 80
    0xb206e0300b0902824500d00c2c449038011803007401e0010b030010310b884010010b00d0f200c0c0d68003140f5000340c480c050080741010340b15021041d06403420000c7e2409000380c280b0054035480b10f05506620410302d4040c0d18803a28958040c4080058084119000c0d1003030000c40640d64074513030020034801d00c00004001c21400c0202400800d2000000125008110445030801180170400024091950011243c00c054200301c00400030300290012401c1d002801a000001103a51001c41c0c0c0c0c00d11404071480028107800141034120903400d51810f543c4140203e50083c40c200d8581c4400c503c00d44180626409100e0000c2c2da074013401070700400d607015810010000e40d540c60107840d01c4142080800c04010100c4c0b183c1000c10402da80100341720010300c651000500a507480e0040c0240c5d10246000c00e904110350801944a040090400100207000200c4600020090b204002864542104900c501407441400184000c0c0d514014298028800e450085201c1d11440001031491140d680700a6000d4640a180130f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205078471 1250 205077221 205077253
    0xc0b03070215070504030201050919080102210c03010305100c0306050d2006191d0303030106020706090b0a050d02030604110d0b130b010906201f050a0b090114030f 72
    0x41604144144a00183e84404030b0955035070141340030090103d602072141010b02d00340180301809002e4211070301400f5680d95070b81c030703400c990100300818040da060100b0100e091150042050b00078001807440d502d10340c5940c40d41621213000c6030904810300d4039a444511018443d412841c0030300f000410401d440c45051038100340b80101a882c210040045803154003241c90b041c0c040c1d0707690000f40f80c02c10701c14010303101d011500341060016007010b940350018400102d880420180d8042c2c52180c005200710303402c3c200045d003409425481941d07194410811580b0090744030080c3c0305042496030002d80c8030b4964000090103000d50111800c0d9001c1c000c00c02d20172500e0f0702e404c40b140c8a4070580f40003590081d01810101542c16440d080e50108a040c1400c0001600c29600d519117071700c000e01c900390010000307002c06007000414012680c092801300b81542c0985002c2c41400d4121581c0301c020040034a0300d4004c2664054140b2403200d6000c0c01c403220366040d460902441c040480c05030140c0d09180070b408080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205079721 1250 205078471 205078483
    0x1e0901062001050106052203140102120f130b090a02040c050a0e0102010b2803120306060f021603080c0708010509032119050a0209120c09060a060801120c0b030702 72
    0x449404050341041090410043c89418141d03110399031664500b0300c2d06644505990041d030040000072105840010101c0e14201c203081003a880c810002da51408982c60720000c03a24060f002140d8513903a0f1052010542003541443d0324076910102030842030b500d504000d40ac2c502c9441d4007035005800e0104910010358084028035000010b0f40fa04242201107000490888400341c07003145c0c03c21402d102c0002008902c45008594418032014000400e07201c0d40e80e800c003800d140c4200d4020a4542006010039504940d0780c00111416200404241d1808503404605904910002c0c00002000400708034402c03082c4030401c05040030340000d118906000d081c0303503902d41c40300600d41e4140703280001e2895901070003e81140145d08061420540c0d01c05041e00b680104000f811102d034040d0308003c00e400580320209074406100038030004e041e03140c00e10414044075590043c9054441c100919045c008a80c0100003d81510f070030025402c09000c480c5131032034164181d40c0080030201004400c10202130303400551 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205080971 1250 205079721 205079747
    0x510030f0501171e030403050f010905070b0705100f0e010e0a0209090f0318010e090f07081b04091503050105100602010e010b060904020703020c100c05010e0a020f1e090106 76
    0x4114503a43d0b2180300d12064500302d01c0070700e950001c94081394401440803000c2041d200c0301d010ba0f80303000d070343e0790355140b0b8489581d201c40d02c140d450b00000c0080c0242405a4402405a59101890014540d40340da4030754048201010502c0da580b05101034240c2580e00040340f0743d2000300200a01c41d030301d100650b030326043e04601b2441110014002005500b0100301c0810001100c4001d6007440d206140d1031001450500e101c9041100385d2110034000d50355406c1c0c6d036004900d031034020451030800001c01402903100510004080f03410030300245d0403030a54812a030490700d583e48002501d100751158000980c4c540d0f413000d00250300300001c0c001c00e40e121100c200110350b03541d0002c006182c65804014280d89a0054450340504140712000807401c094000b4038802d40310740b040d05d40d410141d0780060120294040341000103010402071a0070460244580ada4107a280c200810644d00c403640010b00a80d960483c040c050a0300840540c1106007083d641034514100802200b5250384a041c02460352200c240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205082221 1250 205080971 205081001
    0x201270807080c040c0801050108150d080a0216150c02010306030c060e120706020a02090403032903070b13050d0503040b120403030c0e0306041205040506071b1d060d0c051003 77
    0x1030f07220050302c0c1c01d01c20885101810303298090203038600310056070f850f04010034504e84c030075285154100541c0e40454801c0d000f4400d803010707a210440340000924101c9540e484843e622140d58080c40344151840440004502c00c0c94007000c01740e01880100c000c1e001b140c0c4020b10740014485c0200d98180c01c89108a0f0240742a80c84803030b4880102c001d107540311316500c141005600582407070741c00340c10307c4100140d0180c02814049085021840c41070fa134818403a0700d80a006c82c940340140704a00d401d101e00700003030034644100740c102103d45119030101507892040b00d12402824903100b0422105000307540041a04a5881e522103110405811035a10215401c4002900d0075268080d214020700c5091120040500104200d0396a0394440c4480c0d4041c40d100401c0c070506000c00030ba203503502d400800030035104101032105010002e480500e10151a081414110100d462003031102134010007003540b00d0001c4a10754840420ba050010340610260041d0b031300b05d050383c1c2c40d2a4060342c00d40c1050b0612403d040e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205083471 1250 205082221 205082233
    0xd0c0806130b041106310f18020a020703050a05010203040317090303070311042112030608030706150306021b0c1e0f040e07081c030504020d020127080708 68
    0x140a95001ca81c01001007410302104085408104200000b40c1e46540184c50300e803514079610240981d001203a411050300142c1e10808807401c01d043d00f0350a0003042c00c1d00c10300c541c00e41401d1010b0180c0011002c0040c049501044e00c541261007004404001d54003c41a61001046810514081d41c0304039004c0e00846c1c111103210148030440390300248101c2400300514155200c0040c110058245201d404001c01c0c2c1c144008101003840c8400445047e10382e06041060710382a02d4684040440c05040405061a0440822001c5004001c41f685a40c0c840e000091040407880035081802e05500054109840885c0c0030195510707804690500e0540c20342201d40b40100070741005100d0a001d000a119160007100808860501e12110441c01c0801000410840204c003252480c00601d5444a1210b92240052024041a03003034681410005403070144031a14094000ca080d061038104028100400c80e80c3c442d41c140e501041c6106440c2c2c0012940546640c3c0c1c200003a40c4e2071950181107050301038a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205084721 1250 205083471 205083481
    0x10905060a030803010b0a140f0c010f0b01020a030f0306081902031902060d09060609090501090209150307260d021c020102070c1202030703060504060c0807050304020d110402090d0c0806 82
    0x7040e09402281c1d40129064556800d10703508940384d41040014600b1700160a10651000000102911040c010320301000d07200e036101c03c5d4660130b50f4540c5120340b100300d01d04024408540d07400b04d01c001400d90542807060980007c444110000c000c0c5500c000824000ea111056140c01c0d28041343d50460300840480e00c40b4281a40654820b440744400254401010400c10b0401d1105400140005009400000c0d1540c8d480d00300da4155846070701e040310f15035902c40c4c00b03400314900b00651503084890141240b03d0690354a01103030381c0e40c030340340031b60946080045050b24030480e05043d10360225a26030240c0b0b41070350308200040d542d950440170040c860554246140074441c0f052003500c0020303401c0824910002e2a000c0c2440f20000003003426600b41c000c054000c404034030070b8003420340510f105180024014110903001810f03010f0103405041044003c00500c00980d80c1c1d1551034078866003109802c0b201c055030300d001500900c01c5c4610950450111f0107240148091a07030058100d400c01403ea400341e03524 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205085971 1250 205084721 205084729
    0x605090a0b06031b090705041a0306330d1b0f1409061815030f0604050609060105032e03060e010b0103020304051e150112050c0108132004050c0301090506 68
    0x4000444980400d1504650b0b050329185c01c005800c88030034240369251546880b81c84030741c10310886010040314800010f200141c1030154031820030100c0e92a00b0041590b0580e8045152050303c2c0e032030b18030742034042107510590101c0c0e8003e004515003a0711141c0344a0580e00068204064032903250040b800007117407030200c3e130400c40c02c0f039205042c0103250078544842c1c0c8041c541940c040c0e101280d08180b01055400c0045100002503000702601c6009440500c2c26504002c140d54005102d00e0040d02100b06000d9685d8106050300c1c1c0041e03148210a04445240c07441905090310215a07651100a840000083c01800c0c1d200c1c005540c50302009204c50940350006401f68401900c1c0208140d100c3c2e81c1d01644a644d490300c0003c0035066005a42120130384c40403504080380280c1001031140050300d0344070304000d01080912121072007802c2541b010700c5c140410b060a207040c0b002c0505515104540d1200394425008220350310304000300104840e081c0300151083c3d079002402082211032503c404209207180c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205087221 1250 205085971 205085983
    0x4030807050313080c010e19120207120609051002040b09030120090105130f0b09030606030601030c05060708041d090f0606030a06022a0105150f0d0b07020a0605090a0b0603 76
    0x80320f0154020740d402555034003581075020840d0762038a9540c401000d00004000d020794440301544201d04004803016003081a05260300d80d84038020356000f94001c20480c180a11011034494004070f00040c0d600d403c0c2003260404600c00e840e80b0a0074800100410215800c038090140b5103c160000c000100c2e240501602c400c2500d1460503070ba101c180020405584140020301c94070452a0711209116550361000d003100042e504508801c5001040f030b08400d0804200c0707554440c00450041000d035156803501b01500c0f402d405101d0003003e0008814041c00f007071808580040a1141079407000401c1c4001c81c0b0100ca2060340c1e500c0c0240103013501c1407004070300050b4450103418010064500c4012503031341c000c001d5100070300c0c03071519281070307005072003610350085034055981c580340008941842c10b844081106031282608601c030f150380c07607640d4802e0380300c0e00c000205140d03104400c01c0058440d007605074603041c0c80c10802064182090200040e000002c6507164080380301e0b0304606107581f184400c15494103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205088471 1250 205087221 205087231
    0xf060e060c060609041b0806061513060e010302130b070c050d0302031206120a050d020d09031505060d021c050d050a08070c08090a0807050f06210c13030605040308070503 75
    0xe40b018011807080e1400704641504141310340504803141c4040e444803159551180d10081076a0090020406076003890381c2c25800c0403485100c03440c81e040c085445118811101c0c0104010030491110a00542e4025411140701c0883e040a00710441d80c6e032030541070241d010800c00c0701c05105010740080c40c1d060003611000c240f80c2c1a0055402c06c42d605403140034048004000c0e0b984001c441d841810600c0b030a201183d030540c000d2014014000061802034540b5189203050020000e85200070030200310403a0349004c55144080c6c0100e4103454a500050780d5000d05600a0b5201c58031040c41182420850b981d400028070641c190380c031189480c072040e80c05000c3d03070902c5004a01d419001400350381c030a0680c2d150081c1309440030303818800d014021554010f0346d6000941c903030307004960512041c6420304502c0072180b400c8070381c24034002c00c80d91301c12440030900280032142262800403450852040090360140c2d8501d2105000c0340350f50b410074070302804003520260046000301c00442c49103846001180d00c28 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205089721 1250 205088471 205088473
    0x1803100209010818120a0503060109170312040c08071707231207030602130501140a0207030b090106030f06051603150b070f0b010824070806010f030b09010f060e060c 73
    0x5540e141603041c00c00d201c0f00405442401458610301a4080207405480301c100166690b88d141e1400100142103003031943c00400701d40321b150000c2c03061a440042158101031080c0201c4003036132110700d40880043c0b030381e030031488a90003040004a46048844900003600712444104c880c0c26940f43c0501d00841c0b80314880c0207042c4448070b000e4160f4200b0002c0600b030b1640036407c40d40c17880d58940742c62089811165102c511080c460030100541d6920550000d012078000c41100e00c0c21503013010196682120b03210007003c1982400024020300020340c000b6000b9504a0340c0308118540a142c178100520741140c0c8440d20000d00e410700040103102e84174002805d40c80210700042181040d03040307601900034a40844004095194a900103000580c1c198000c02c10b11005221000d5025991080144490301b91180700017007100b0404800e0303000c101c80b50001000e0804050204240001714007422100f02000d400107101d2000049281440d083c880842d006070b03079054034a0107501c0170004c041c441d241c180640703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205090971 1250 205089721 205089737
    0x72909030c04020a02031207120f0e0a030f090b03010305010f1d070315090204020f040918200f0402070c080c040e03091c0b04030815060702180c0d02180310020901 72
    0x1d1410598010030b10503090340100c0e424040040201d07604500c084800700001038400c2c101c00d402c22034501520684c0e4101c00401c0c0030080d04c0340c41d280c2c2e40b0940c59801400300007690004070b034814000e801440240c0041d09140f82e881d87c482c04c1c1103003e803030018484044249000a88115044030400c0307d4004007901020b0200e241c03660700c603201d0041e00001c07003110035070383c83c5480c000680c0c441c8000c0c1070100030030490310340716850513003c14121420003c01d5811806900c01040c00a4400482c401d08050411048180d1400321004640c088030036100b807940240c0300040c04000d20600040950840d1403803800c4680d025400020f12069825014100d203903544140500e00003803a1031036a040c0c3d0440c5608404c0c0c1e9416454940007191442500c06902042968090000e4000081007031150800141e4000746400700d25804038849c8240c0300d1a00036a03907641804100480724400c2100e0b1300810040701591032f444c4542001c0081285541c62074481e2145003003040c03078950680241ca0407840705844070701c2c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205092221 1250 205090971 205090993
    0x507150e0111010e160503010b040605240d09230c01091403030f1908010905190b03120a0e0306010504050f13061401060c02010828090305090307290903 67
    0x64041c502d5007003400039500c4182151680710700308024490203110912841c4890b14010506085413101500140601e06103401030043d41c65150001a6207100c0c0744480c4030468031911540c1080c002d002040f8903850610a01000f402400f540b001c100c038401c0d681d1203c0303c0d4100e03021b156039681c0c80e20f01d05004c501d44440800014091418190070807102400b524030300808041c140415910018418080381036100d800365020354010030b12400360403024001c010034248074142c840c41e900500c520280700c9480d04003203c050388003130001d68401c0c03950301407072600c5e00c600000c041c0060f000709110310700034843c0500000e414030380f9004080c05200300b40c481402c00c4e03c076884410303149200918142d0f41117889040c60f1260040381e03805203008002c1c036662002410810310006140c2e000c040c120b411080c4036007617a42c0d07807610030412100e48030346940130000b501da0085c9800d45403405000c2001d50300d40a01f036000500040c00c080d6540410002c0e5611030b05c4104600d03511100350040c0304090f07400d60f100e40442c0c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205093471 1250 205092221 205092227
    0x103090506130609080f040314071404023006030c040902100305040203070305030f09041d060a0203100e0103050f0123060d030908011b02011107021e0a150302070507150e01 76
    0x105016410100d640f400c1034860101030750128003c80d15111b8006030400c1800101da810030300b564110000740207039918200c01d11004031040c0440d14411907000803213098000304120305054005110f42c403200220034bc02000d4540e414111050340c002d0041a001e00014038040c800c00340c407150300800402051480840480050100174001ca801d8440c01102101050040004e488403840c000441959140178005000c00d83d034141c0c50b083d0115420301d601c681d03201307000300c0c03080d612071a80b05e401038032959881c0c0340b00940b0580b68402000001540c0010090010104120100301243c40091221203001d20186144002100042d6403044268010620320710344541e135030540c42d0103841c200252035120140c0360b0031217000d0583d40c042d000c1c404691121858088c012511094000492036007882c4203038010446002d1448808842c03108600e0300400a50b941c05ea081000d4009400d6007540c8090a0802500951065a05451500ca000400a181e680c1040035000c042880d0342e401e1040541d2030015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205094721 1250 205093471 205093501
    0x20d0815010e06030a09050706081e2203180b03010f03030e010509090109091403030702070603020304080705012405030a120c02010210110d0e06010608010b0a020a06050708150103090506 82
    0xc0d040010305104107000e992040041c40c002c01404400041c2c24035945456481e01c10150b1041d0140040d035410000d849204030b03000c901c2e50380d5246038003c080e80c2d14038588071080030b500758242c0c1d110050040d200034180c1c401c0c028103000640208244c40b00d07454401e4080580424071a21410010052092000a2280081050504046c141542401417020000386004826000950700b6552076101c00f050200c3c2c15400010506030300082d52441c2881100292555040c3c0962000d154000011800700180801154220754211008006405030450385050752050b409064001d00c10a00000c40c0d5850045080c6801035444140540e4500c504202a198119603c505034154020014000c0c10a5028050703c083d4000191810b5500c1c400e071803ca00032105407400308070700da43c09030300140004c80d00b2440b000d06550f11560250340341d645903007003246130580c0b00c00c00034501428041845013840d0404d050b1401000c43d003244601243c0c00b0b04c01102101d0700c2e8840a400d82d03200202281c03c0d220480c600e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205095971 1250 205094721 205094761
    0x40b0f130504180302011a090106140409020406020304060807090b030406090206070203011b110105040f02210709021e070201210b090c030603070602160902030a0b091003030e01020d08 81
    0x40a140c03541c1c0c03803001604982c42c482d24000120740c80100700341007550a124004640d074008076044900404080854030800b0140180002c0c810418000f0910740140001c3e1070040c0000c8005641e26078807114000d441c0c0e08a0720900000c02c4496001c40c44181c011880c00b000d0ba503500443e5030841e03460761202c40103415183d5099030001c03010460705000d610b084c0a0807024200c1b81c101315002644148000300342d20440b10300743c410f60b49024180400a510100c0359041550100e8910810000c054040b000b50109400411410b11036408001603411031900581441000000d0440b080c82c90f6000c0803007640700d0914000c1c0001d842c3d160550000c010a0080321034641c00710000550354464001003046080103682d80d00710000040700700704882c5001c01c45140682800c0c806014089149000c06050140038014185003940100024561106139070050041c61401041c040150814503803101d00394555000550004082d000e114140354000141e95003111051354900000350b13206c0814107640310089107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205097221 1250 205095971 205095997
    0x120304060b211f09020a120813030b04020120030d0509160605040f05040605010918020d090f020405150d0201141908090106060e1c02040b12150c040b0f 67
    0x585940d03002020030041da0640341400c02403040300807103c1c50002d0700c0100045850320b42d0a06403410016299010f4140880d0f80707801e403650208099103003151460103140d54a03500800c20031400018401d1503c500c6000d2030003a201c0d0800c510a24030011240d640c40300125406500400415510800d5988400c5c1d000540e82c0c10744000c40b6980c0200c0c7c2d6208d5807a440303130740042c030082014410645060b80003401804115000c200c0c1924000000c3c000000f40d220f880e85800d40c40e0714210103540c05404584104030030b06c0b020801b00c003562038050703014142c0101c264003c500c0c0000041c40100582c403005140040142843e43c104416801100d030b8004940b10700c000b14030240510b0120450b0050014211035858032076055902d00310529908503079a6902100412440304400003050319a0030319019030440e8001c080c0300c020f41c03600201c0c02800410280d15041800b0015050b10044003085598040c0010071071f42600d83c031034040c039640e03500540c05100800750042217500b0700e114100000b4038441641c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205098471 1250 205097221 205097239
    0xc1201060311070210170a15090e070e0a1803030617010504050c1306180203011e050a03080f0903060916051806092707210b0a020a02010204080f0312010503120304060b 74
    0x19106c40280066840500c900d072034001c00801c03100c0138038040014000c0034600700034039040ca0364440d40e1030205204544c2c0c81b801810218040c2c3c4d0b142c0c0c000b204184816810303c0c6070400303035140c010000c0110307114460503107510f0700c10001ca52006001e2140150341000c010900482030600700003d8000e00340100510b00d9980d030000402103650954440041e0000e84010707220b62400d2070f000050441d080411103050751710700c0103204581d115500d00090ba074200400545803c034022000a20780b01d5081402d0f40f6214190411442120000e90718032010980b0f040e07480f54030303550018003481410b14400385001045080000d400390074131001a9034011450030000c1354031100010b0452100592030325016041e00900700c20702501038810740802d00c2c0e54528400703c05049260300d0345052141d000c2e00ca07800c0c20ba0006030300030415100350141e502512030303402510720b10780f105036500d41d40313502c40503c80c400e9200e5240001060320b40440c0440da0303082091201440c5039555519100240360400c14664000004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205099721 1250 205098471 205098497
    0x31e06090105011d0d060b01080117030313081c06030201030f02280c0c12020a06080105011b050708070902120c040803030a0b01021507110f0106060507020405041502030c1201060311070210 83
    0x140740702421707213008400006141e042034000404c2c482d416048407111441c60601103044c84800012a90710424480035000800c409142202052040400940340c5041c103020100300703881c09030b00090880c1d2003620704110410420790b26000364041c3c8030764450071401103030300012101e4000f1105d0702500f006240015242e41155100d013039500d45504601a0426900108011402d00c004400c001d0031060a01c5c07031484d80f40130b000070200158805201d000b41480c005010030811300304408005401d40d0b409807000aa12401e000c0000d420071003011030910000e902180303111100004840c00c0c0c070704180165203907a80b0102c140d03026100583d00320381180301d254801000c08010219940c000e2000359100b004280c4000f8109241400c440001c0b40c3ca82d15020301001169041011241406d81c181da0128071940c4a0030701c8180340350302540c0c0c0181c040c000020012250301003802411a5615101040d140366240c81c0d01b241141c00e4100e4941006804010311001741c9008091141d503d212840c0c02412060b070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 205100971 1250 205099721 205099729
    0xe0408040306020f0408010507021504140a0501050a0903030b090c0307050f09130e0f011505130204090513020109080a030504090b061c060f1d010b0a0c120203031e06090105011d 78
    0x481d078003481c2d00c1200410280006d92080c01159044020f0384010a00b90700001c0031002100c3c0090701c01004862585c8843d880d8801c14018110002e8202c0000c1099260124400005e052008400c030006440c010419030f840c40e20003001802242c103c050b150035a52909030543d81941b104540004a52041c04000e55a5455011131800b26204242c0401d081342000b6400d0319000c8070030401c100c140d05211a0194800c041b02202c005c541040352001e4110740401c081e0402480369030401000203041c08200704441888600c0741c4082c070700c00c2c2e03103903003003582e032013000c03545400840d4030040004004110801c13048007903810064900200a2050b031a119101c150040d24201840a42541c1a02d8000411540d481d00505600402404407010350002140c0d80c0c1d11200c141c1406102010303007000c1000380c2021300c1004000c00c05644055015501152140082e42e44d070800c0700d0195030440f64100002680c070300740c940d45000340c1c4007400342034099080000650300070f40c0010011103440310308504800582c5d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 205102221 1250 205100971 205100977
    0x11030d02160209060303120601080717090f060f160c060605130b03010f020906030a05090f0a08040315060501021507030f181103031c0507020a02060a03020306030c030d090e040804030602 82
    0x39481c03100c40141490740c41881035043d00244114440d03041070150204070710175500d0903540722400f4a03201c0142d5440540588400040500710850a18014100b203070328100003400342180341c1d6031003c540140c0d0b0f5204550324844d070304a54102495043c9030a00ca5101c0c05405085400e03071246c0ba0209106440b18042002480e1180341c41e41e849840d02c1c00d044885c2402e1140e0502040c2d070f204150302c3d105101004c0358003440b019080800c0c280da144002200000184500e001119103903003511603030803460400e10502d400c03a01050701d070b198020384101c200a0280c860b0804585042e0051305442a5100ba44460404020700900905072101400710001e01316221710100506040d40d01c254800107418800810704800c01a41d00a51080115612140c42550612401c0103000c0c808112556042022824900132042c000d40014002c500ca403a01a01500558464503080c0c08441d650504001010380d204030720440b01000c41d45585040c4400c9001103099503000b400ba451720391070150707680c0e10340e0101d80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 205103471 1250 205102221 205102237
    0x6040212090c12030c03070f0f08070308161b060221010b0a091406040b0a050409050f04050120180103091703040215040b09010c050a051e0d031b11030d02 68
    0x40c10041d200b09003403400624600c1c3e0051000021400e0403100d4072001c2d541d00c80c000703000e0950340812111034100f2810b003443c142c01c990f00000b2207484921a01e4080c02800c1c2c282c803c80505030102410224282c4602c1404403d9100fa654105905071107407075070002903100400b00f07940300030304690900103080071b10702b024000c01c0802d00c00c0760740f081107890007040078203d60030100c032040c036205465000e5580d40064a0544d14808901a51161019400c0d41c0700d21a590225040b1401d000802040f80c80308440c5911650080000f842010240b00140f50314420a0100310101401400342102c0202a850600744030003040c1070006074030305070361104030540100035204120207100004120450402d121401080c1d00b4603640d6905260509540798114003426540504002e4204114030511904100d2000b20075000419035807000e002200549442d10340d549002c40502c110801c048019110380b003010454540425034440708150407004650117242510507280503c000c0c05a040001101d1000742a50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 205104721 1250 205103471 205103473
    0x50f07030b0106030609110403060b03030c100902040606081b13080610031e031202070206160507060201200d110c0708010b2d090a02040810060305060f1e0604021209 73
    0x342d0300d0200018144c1d01e1390381007000346900381948090b410004405413015243d2204002c00d004c410300c00401c1c9075004003140c0c0d000c01d110303003400b0303c00e42180c40d40000441350003658144421030f00c030501a50050025187c1c102440324500440c44582d04901c00303002d5420f420b45800d40d22560b41d589003450184d068074607819254414500f0402c0022915035410443d04d40006110340c0540da80b405071001946680b0740c0d448940001d490011990341404403400b180c1c21901d8840c640c1018200b00755601c03001e004407000b645c83d1403e48c9440e40b1003500d038014026440c0881c10b20704480b0301c0d6440090008010408415031041c04036000e5141c09000d0b000145c17244e2000054240015006c2008840700c000002208110207159040c8180b8451a00b080b0080c040d100c1d40225215440030000a00c503a40c85200203002e406165400c0c4400c540051301124000d10071511191503180081031000826651400c480380b1298666801c4003551101a51006000b0f20041c00e01c00d0f407041a03600900121549051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 205105971 1250 205104721 205104743
    0x30f060907120b070f031107120216120f0c2c0c090916180f081b060313050c0d060b03060a0c1d030709020a030204060917070b07050f0703 61
    0x4166030800c4041c008000c8000b00082034401901c59040380c0201a0900c0c04100f00f00700e03498030a40c0640c0085076204e82e0507501c6681c903906400e24641304802403d0040050141d241c2010312855050026400d54100d003200d030080d55025a98070a110300030400880e0f024440010000352008211480c51090310032002d404138000341c0300b0083c00442c200500303140c1110350034082d80c15240c40d01c0b540c250b80300002c03402003a50310381d403120182c03101803014903c41960381c6010350114040081106007011104280111203035421310482e0078800f20401428183c00c40c900784001000481e03480d0380101c801d401102910441c0b00300101244a14082c00703020b45074280c6070902800542010004c190f8008000e010411010452080c010070120800c0c606074015403100094007029901840088010180684c0456545046910140117034019101d00300200d000300c040002d40095220514170504144000303040700d46e0600703564946c150020703c0c0a441c0f600c07c401c02406008420401c0e080598041d0100c20740b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 205107221 1250 205105971 205105981
    0x40303031413080904020705010b12010c140c0c01051e161101110c0405101707090e07060921080a08060310093909050610030b090402040f0b030f06 65
    0x24031a0701030300742c40c07181d07007400581c0002c10151801d035016224212005a1344141300d0400c6030260102e01061507101492083d214099001503006802c1d40e00d5a441d041d014000c0b1105001c1039004022040760a9041155031620640c03141005040c443c41c03404402500c3c80100d01d00c2403032604400c1da485c44050401807000d05111002c0303180c01c9025001d10784a0390b501501c096094a510302e00d801c4e6401036845030045050303441d5078030503400980030380e0550400c01030500c807605607200700a10078419190302d414201c00150070049004404d40d0b180d5100c201031301c1d160198009409501c0c65110104c41f100542d004006100d100c02001c10010a0303481d40b070942480c01c100341c100b10105d190343c224203207031440310400500f80f074401e0308030b400f07001032103e03542c40d04040740c4444203920000c0782ca05c0e00c501000100c1c40d4202544030a015180695854843c2003030083e00307408444003480d82603444080403001600520780380c0c00c88602c600c4244400300e090342025020a21313001e003400700c0c40b0640e007021003002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 205108471 1250 205107221 205107251
    0x10305070504050112112101020705011533180305010209030105010906080d110c0901290406140d0603060c0c0308060d12050c010e06100e1b030a0905010902040204030303 75
    0x138054540b0900901c60105590f998802e034500e2241c00c0e1b03002d12004411040341ea54803281150404072007134000e43d43c41141b440d06d140241035003803412112040180c00822a40030f87c40c2542e044100030309250000380751061150705030043c0f0a80110030098405858901e0b40740d4015075100461143d00050788680e030b14010582500c07816000b968a00303140080420505900240c0d80f44c8003070b0741341824403055170f03421805070410000500250300502e117100000391403040c0e44e491403960f1000152030205602d440312907860901c145d02c5900001502d401001c031300b642c5508000c06000010304d00000f50079649580302010380d826101c1c81030100e2444030440d418582c00451711540700008488108420300d940c1d4680c0d075111501c00f041c0c0204640030443c0780c221031095200d19011042001201c00e01d02d080000402070382c5090040d83d03420b5403c400440c450001c5490000489001e405409085607207101ca210001c00340c490040e9090b640711f4030000701580b140e10007400954080c0d580031410b902010840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 205109721 1250 205108471 205108481
    0x12030e1e01050c010b060c0a05060a0b030307021512070905030d05120c030612010608071401050a080403050a260114090c0706021303061a0909010b010c06090812010305070504 77
    0x9240505440c08044403100090810040e5040c024280941c83d0040b1088260060480d8140c0c65041040060000c542c01c000181c4407465901c81c600311045940e49d1b102e00c10a44900031042c0b030f00340c1d0041c0071075001442c1201d000300b00d81286c0d6690314182045c0306900040030006442c00d07004106540e0040c0010704081c006002c010b0407608280c0c1c50640c40b802da030250a40010000b0040c042c02001182d0320740d8070141422500d48100c0e00a200b80c41e11107c10545800043c420400c0c104500311042500d0f5000e84241c409040094489840a9549440582780c903480070194500b00210403250300c44400c03e880b24900700050348280340041d50b0511402d612004802800b0300e01c1241721200700300034500d414045030010703a84a076000d6101c1040500346c1c80804400d40000300828189604000c242e101040d910f080b00c0d0b0100c480d000180c41c0d80703a50301c0c00c03030300c03000c141d9400107a90102c08404518542c0280010031710031070038540b5100f007050880d0b01c4101c082e0400c40d426007001c03074100715919042c040c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 205110971 1250 205109721 205109747
    0x403090311180c0f1306090915080a020d0302032718091b0d06020301060320090102070515040806070c060f0b0105031924030c08030304050d0c0f0c1203 67
    0x1c482541002103201c000250b40200449500a0009051960446603074152194605040086800f054a451025200e00d0441c0580c2000c5407900001307444801c0c029075040100e6040002500350036401e6002d000d031441c1500400d40640c0300400250745030708681400c12450051062003440360012040800c540584140c8401a044888005002c58914003080c990601441d52034040d000078014004a89469500310002d0503043c800f01c00081c900d500b40d00102d41d072400a01c021081c41250403a40c5400d40142414140140d006100c01c2c0514100141100b110380e442d08041400c1030b80d01c0700754900d03008013111034000050b816032a690400140e4040d60f28069140001407082d41c840700c00081060000428007081c12191403e1410b0700d4041e684000c215018a03103449202258100d02890134408503c030803206400e00410008044001100756802aa031260160011702e212030001c82d00030200380300c16202c0c0004010700070006503a00c3c0c030342d03401014005008a03070b007229030034050f00038124208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 205112221 1250 205110971 205110979
    0x19050702040b090a0c0809160e150d060204090e0a051903030912020a051005071b0609060608010203010810091e150c170604152d180e0d080408030c0705060403090311 73
    0x10921010407151072000903030301c08140b09d407100c0e50b503000724a42154030511503540000c030900c2c014050000c03070780043c800e07a03ca5810a011a00340c4805c41d0b503443d40a410041c050382c200c1450301804207094088078081d01e0007450003294140440e05c0d40041c0000f10000b41000d42d0201a9032010028240168103a01c07130842c6041019103413180015100303000191014941070504103980b010420282e00c00c07030078160440820492241c8890a1078005c0d8000c1c00f4886180c440c0c06c4500e1188121030007500c44031544203611042d0407112030358078100407030103010840c0d00b043d1140184100b60564800e070010701206694180400c0707262004052900300181080e4001c90800146150350b012801d81034045984c1030054040d41d43c040800d07044125229200329040c00012403002403400c003010100d943e0002e908408000450824040950311450034401c0c10102e01c04a0001e80800c23492800303140d001602884452400c50039954a42c10603000301d9044000c0b0705c83d60824000e2040c3c800041c3c0301e81c8010b807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 205113471 1250 205112221 205112233
    0x1e100c0809030d020a1709160906031104110403080c010f14010602061503031e040512071802131503151a180a0e13031419050702040b090a0c0809 64
    0x1845440f84229031903220416000520818524800d80c0e44003240d440070782404c2c0c04e0341020b00e84203440c1e81c02c001f501c0301c031410b18110200d002c95a62050000312075004a50340d45681349181444054030300f001c906070503003005000000204801ca4001c1500141e00d5000080b407801c4440d4035001c0300c0901501c4080703000100e00600915800050356a00300d407040c4a107c2c403070100340e00003d10b10301c1548030081e602c084c680807401c5040c0260003e00305446e03048030031180e0314400d0140d241d610512880380f83c80302c1d00000c4c40700e105540359900800041000740103203201e00e0b4a40700050b00310070b10b02c1c0340c14001a03560341d803607064113041640d002c2c06007590700c000c0794581001c604100e01502401e07000010b051800001c01c80c00703644080d1001c0c028103484482c03c4452078a0b0700c60014401d020301b415008030fa0a088400400d110075030407540500b000182d2190345d028204400c03291a044124100d820595549000115036600c84800344251403041011800c07055000006040754000340401003164000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 205114721 1250 205113471 205113481
    0x3090622020f01082707030209090105040c0608070507051203011e050f011206080f0f0d02010501150c03020c03060108030a09060503041109100b0a0f0e180a0507021e100c08 76
    0x1082d800c40c0d04110900e462a0151507500d088214243d0051100d100d040440851252407203020558030101c0340201c81c8003017541c2c0c546480c1c60984d141180d0090400e80d54010901410340605c0090b0303081042440c0082c1000c3d496900c2c5481c1c42226581c00b0505000440100030b05550700382c4500000740703d41145c0c60450b181101040c1d0003a040c1d03080d0750500c9807007014111050200d9129000810400b0704880da010f80244001d52607805440c10a2103e0203002c501d0200503005006150488500d10802580c085404000702c4000c81c200700201c08601618171a10150303541001903501800c04078014607a11000c9441c0601030071201d5002070180071007030042101140d645d140c074464016007911200300503991800f90780c0340c0750099004407454034408a60001099032201c2e03010701908580c2c444001003480304080100f8a0380d030016401907580742c20b0000c1c0b0401c00b00d80040340c012005004441041034000b61110b18408442c2040d84035510943d40c250100410f8010410401341d00d040c0b5001074145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 205115971 1250 205114721 205114729
    0x10c0506010509090c09010905060a080303041707060219080106110c09010308090427050601050a051c0204231906030804090e0304032102010b0108100303030e030f0309062202 77
    0x5108540c03107441c2d90f2000884540081c012840e4400004020360241c2d80c6560908005180944400d806503000050214078400000112030180e074204142840766605200524400e61061030219407050b028015102c5000b03501000f02e03001c541d140c031075101039814041d006080740780d920150501c5074440361a000c56500c41c070404038192900503090a64808a1001103070181240207004980c1401c17200d003a01c5544d000050425105200d041610243d990301c1041004422190007802d42c443d041c6804400008036000c00d6030300b40d6101034130200d051201881030b091004025194035460050740401c101003c0303410300140848a0340c04004010060854603210694041c1c0d00a13107488070750f54030ba01014200200140c50096500c400051894060040d1100310a951100200050b6091100e10907056004681c51841348814400d207203812840c5840450181191640000e014081004000f200c019400020f6100b255104001c02c01400c0a188a22180306156901d001c1c2c804503442c02d80041c0d40e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 205117221 1250 205115971 205115983
    0x50c0c030d090b0304212607080705090a18020a030605030111160503040e010f0905060306071d040f0207030504030512030907030b0a15030501060915080706030504050307140a0b0105010c05 83
    0x20140100f603460381c4d80d41c50f000d200a156282215240c0d03a00000c0166070a0380500340111800c030101d580e060f40101640c203204011001e4401c1008a1850000101d081d40309401500c16420b00a02094010380e82d078582c1a510148004e1103e415500040e644074140e415010301d00091405500800407203040001c1048180644417111010b42d0040f130040c0e041c068200b00340c0300030300010030080500796940c2c40204005001c6200301c009140c10503000480c1c510f004507120344102810b85030100d0030407101c0400d43c0002c880d000c9940d0312a59400003820080c00781e1010f421031512030744581d0356540c15814001d240480c2c80e4007400801c01c0801c200200100045040c1084940c89000c0061948502c4d600304041d00e800c00b460f64044884036400403d00c138054022000b290880c5104005040c2000595001d80500b07000340306140d4000310080281d607210341d2045030b200b8006c0060340c0c28800540d03100320b1004000c400940c56980207a03030850600850309281c13801407c090030511408900303a5101503e0720707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 205118471 1250 205117221 205117229
    0x20070807050304090624020d0c062003040c03050f0703201f080103060b0d23010b060f040609230922080c06060a03031b06060312050c0c030d09 63
    0x44004244036003049030810a0350090980310005003c03a03901c1d480003810000309604025450301c0d07000500d006403070022a03c0c40b80101c072a598034600301702d1a110700e80074000c8090880302612254840404540140005c0e600441c810009d000c2c610745103062151030011403c20494164104134802c10011b101100254101c1c1000112103000d010040c000900d14801c60710084015038090740c446180d0740c1e201110301e060341c1c458081084981121018460911603111009100100012080d00080700314000d1498501c61030002155600024021480c1d27a003090034080b00d1a4800302d0207009454000d000d80700900030302c01d0000100d8107001541580d408251203114000c1c1c1c28140414203424402d441c08018070b41401e0014a4459507180000c80c40e400b000c0f4800160142c031010803002e2510500d0f12048070780503528130f51030306040905480c114401d03c0046a615560701000800290404074a20150501340c842c60f0315400035000d1582080c031f101080c03d10a40008400303241c55a00700001d00191 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 205119721 1250 205118471 205118483
    0xd0303050402041b2006070504030b090c0d03050408060901020a0504140310050c041d090a0b070507150902190315020c3a0305070806090601170106020309042007 71
    0xd03180c0d40007080042a01c040765018140704611800b010581203030f00d510102021380807041d126025603111703d444103c103460781130005000700b100300040b650181803560020946016a44501e03406000a50001c443c1c0404401046020408100c07200050021a5000352984002d514003004007a00500900c0f40340150447d480141e040c0111903207003089402a0650700c02c0701040103080c040c012541e581c000740302d001e01c2480303000c2803035401c0a490034400d40500e68000003030100c01843e95400a8091000303082d01c0070042e05103c1d0402040c405d2142d07a80c102c0c1d5a840010304247c150052000e419507904d21141108420041080060b10721040083d2200401030010384401024200301d0810301c10212002c5041c3c140500085040703001d114402025020744010b001e405400e600a60a4030000c03501c220100700c6030310005d0018200302900d5a171101e8145001d82441c04c80c210030b100d49200c281c0290f00142d00204041d0003604041c46401d03d4148101500851a595080356074003a100f800303001891 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 205120971 1250 205119721 205119731
    0x1e0504080703080f07020a0e01091d191b06081009021c0f0b06030f010623180a0302031014180a020d03050c0a0b04030206150f1915031d0106050d0303 66
    0x92130469016202590340c001c0001001b9950b98200034210102030050003e07452500b00b030408840701140685441c203a811011b4400b244d485080d81e02038851240c0e043d01c038401084c1410715164004c0d00d129019180503100c00a59013090700c00340000300d059400c01c264161040100900c803607040344c00703141c401a0b088000f01d6100d4a541142018003250b80d900382c2c0100d00441440002d0042c2485a81a545035a030303100010320030603104071400e801d140b2070160042401c00c4103001c01c81403d900900c8004019007c0389642c1e42d60b90200b450040c449003203c00c0d42d5030342d00048014918441c0c0c4603402c9203462444d11080f86c10381c000a0784680032020300a1007407060010030f6003054000d00540c2d540207046c900303503240e1803510706000c5003070002103034214014010300000038000d640c0041082e0101401030802d40f030901c11102800b012011802d20141c2100071000b0005d0074501c02002005040c1303651340e000c50b41500d6645014121251800582c1340d60741460340502003510303041d010b929020b800d40b8001c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 205122221 1250 205120971 205120987
    0x906011205030d1d070602070312050f030c070f140a060b0a0810020c1207080a121406040207030c080307020c0f1206060d030c0f11190b040b0a0905030d1e050408070308 74
    0x401d04450102d13200b0034024582c000500a401264003400c4034022058070401c40d45031413040f91144141980c0b071411010500103d0300340f00924000d4001c1324803c0102d22021141921040c02000000c10f00c452540e000750b88038801c005082c025226010001e03104800000d04042905071190032614100080c568042081049171904114030005503e0a003080c0380d450000e420a902958000f25054000c1180720907480c4d403202d6544140d00c0384130204408120140c54050070000030f54880b913026400c0080c1c00e011100492400340c000d50107400305800030035100450405210110001c89841c0b44114102d04402403520300101c0e07544e40c000b2040f64100d0b850030751403400b6100001004400762a1288110080d410403888518200c0d0351344045800d030800d9110340d2240403441d02c95000346041d41c10705000800601c050700000c1c3c058070105040490700e0584860100e490510303d1007608001804072075014650203092411684041070b90310740186803904043c0b0043c1c1e1784440d0302c8001c04200300010300070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 205123471 1250 205122221 205122251
    0x31406060d110a050703020714060403030e06070c0f150810050d0c0305030403033b09061203270901080d0f120203070306030201022a131107050102030906011205030d 73
    0x81078031102c9480b4292144100e65004005400c244400c40141c45822030104002100004a8132070407801010a40340038156601202d2a4808003200f40e0041c206011002c00074001c1c80103000500342e2401c843d00f00c0303858080d54050121001440c1f0090040c01310130710443c40342c82003100c0c0a8600032764025500030601d15200064100e02d0340003500340d00000c90301208041d888016208201b040694038444201194445145201c2002500b01d4030008081c1d03002c1d141c1480c44049a0204006043c1040c0f01c011b600128256070000708412141c000040b8462080032513040001c0c09450240d588081075810706660341e5035400c80307020000a000100c000c1d050702620405600c03c2640d6902c4056484e41443d1001a01404003400201e000d070085104200128480080c03018a00c4c804001c2d0400117040d030024464403090b5140c1d00f0310340c142c80e0040508140c6c240801040003902c90000180d6030303d4505500c500300300e0107801c440c81c4a4000c6174800049000003056851444944100180030700c100fa0b10b203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 205124721 1250 205123471 205123481
    0xb090703060e040f0309030f20090f0a0f0e10050627070c060b062b0e1002090f0d0c030c050409021e0d0606060c0308010905010e0118090f0f0210031406060d 69
    0x1066125003848c8482005529a0a215822041001d41c8903030309a840400c803c254040300e40040052022000400d1070483d900300050404d007002000518203a03920b0a5828503a800440160749501c50b020312049013000c0b681c281c501d242c81130310400b0001400d901d055002c2030247c000d40400101c0340b00c100502801d0782c0003901c50f4034002c10941c1c2d514110002402136621384508001f9141081603200011131150044c00440c0000401a0084c2110401d88074002c0d004900400e0300a107030a001100c26484414441c0750442c000c11508140d0ba2440ca441880c0801a400c07890040e400c155000c0010388582c0805030300102e1403100702c0b142c421000081261382d408464080d0800d0700300b080014032540c01035031401ca8503000741d03039080b0f49a80f1a0038050507100d003031191280c040d1042d4010480d203072041c2c0000d0308000111602061a007260f8862403440420004c0a4074145040382d001021442c11124440c1c000c00c00d810b0900030200c0c3ca1031119034440d0000c110703600401000612114940040d400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 205125971 1250 205124721 205124723
    0xa06050a09180501082b1b050601090506120f0303010e040f06110915041211010c1a10050316030b0603010b04060305010b030106170a0825060b090703060e040f030903 73
    0x101000c0841c46003200b8007601082c8280d040310f0144d00100d182c4042000c49011803101d1805404109940e24401180d98083c48003c00c29003d03040b400504c0041c0b024030805008210b0104081000e091240030404040200c41108441e5400720855280001000c01039904562090703140ca611980c0d14203010400c0c40d0303031070b6008000c5442c1c0181035905000311409402811000c0d60324a044401c450b0454070341c1c0c803032400707018485598103c1c810001200300140c00c00222040c0750405405040b40d0701c1d8680788540f01d0100115026000400444806240c0404003d040403001094914460f9140707140c100700323601001d056241c8050000f152501c094024036149070000e0820080c10342e5038145030703000b00401d0091511950034240001281104610410301240c401c2000c0c01284905948802c081d60002005048031042040c11440c903450142405180d60700499004c02c2c00801c0c2020400c040b030004129500749440e145003400703499112a84a540154441e840c1c05a911860a080c1e03100340d55584 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 205127221 1250 205125971 205125989
    0x109060c06200a0810061425020a03050a050c0a180b0303090604060c020414040503030708060102280b010603060b090f060d0501032109050f01030518030d06080f01020301050a06050a09 81
    0xf6080b810b80340e0054149125100140014600036210141194072101440e90314030b07980e00a1185805075114014845d44402001c1d85901301c1c83e40a03800b240420700190300a6130b640d00300780126001e001c401e01c88810300000c200d03204281641071041c110030b4920302003150000c040e50b030b2400c084540c4003041101d0804000410b03007a1155070b03c01000b404450754060485c011814501c00505060070400128003d03039200e00036504581d13800760200d07411a40282058110300c40c000712852401c4103150451030ba102c1c2c980e440c02040c4002d08100c44400300690007101050f140000c1009908511010b0302c84441d000c603070001100d0055000244d142c02250404004545003600010400c2000c83c42c0b000707880c0d60f60318144022501c42d501582ca05182c0e1203000e400c0b0a1500316901300d58480d41c0180e84c4055500000080c0021030b005640c51508a2442d0340c00c0c49039220410b0000c00c0c010041c103624092010002e40c42c1d58108000300b001710b002d0b4407450080c01800310714044481c0c020860207020b0440c0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 205128471 1250 205127221 205127227
    0x1709070f08030319151e170c03011802011403220602070b0f0615070602070804090e1209010212070503211005091303050c0f030c010c08060303121f21050c0109060c0620 74
    0x6401d074454041288d418441c0d8640810250103030450342c611206560147c40c0d071005c18200980b00d40c4c0744d0788001c066088040d00c21500c415407903440620000c1c020f008850050b1100081c1c54608118803000e070056580d580700408010080c1c3e1042d4034240701c0151540542e807100241e1400038041e0040850090035041e0118021030302421b00c0e446030b0009010982200c030012904076015207244908107072540180c2007440c8144850301c030b001c01011030620660459160082208031500c5428ec1101031000c0608003105020003c01c800c1350842c0902400c960310240340c20110000c9841c80c082c88001418407101040b2022040300510201250310481401d4a83c0c40452009480c0200b450b10305403030110741e4032008200141400005d40b01d110010150140c0c10741c99802001c03823601005020b0042c03442d044540400d21080640e1920240d0302c4071401010750186601d0600c0c20111030a640c40d040104030703141004850351001c02000e8980d00480001140d1410306d4904040e8802d68107082c500230000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 205129721 1250 205128471 205128509
    0x30e030d0e21040f150903020d0b04060b0a06050d0c050408120405090a0204080307062a11010b01021f02030901090f031106161709070f08030319151e 66
    0x407440d034800b80c900c0030407a00c40c09020018030240b03000d0b500500d850244043d0052104901496540c1ca100790030303007011140e40343e42c1d0f03000604082003030307400f141c1810002c0c080c0400c00c00356000b01290b180d0200c1d800303c0c2441c1019001010750080303850151455456103000000a8051000c94015241401c15a080c0d46031150003940707164004e00c13503075014400040c00215010464403d0750183d5080c54003562502e40c0c95101c0002801601e00c0c50017200e9501c04c4501e60525403078491042400c002d880f0b40c082601000c10003030868000a00190543d00010500c04002c960801d004c000707061300c071400513100e454400085004010811008000b00d03d07204922013030640150f00311088000c80d000701c400356071747c41d14100240315140140c4004540b00c051070685200704800310382e5000c1e81190858800c2559060500c4180600e50b02010312078000100f0312030303003145041d03203400c00012070001407102400380744940310003120328440d49145078601e503800d0310519032007450000180195081205a030f894 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 205130971 1250 205129721 205129723
    0xe0607080c150103111903260316030608070317070510050106031a0a0b1e090d1b0b180603071b060f391e020105010306050f0609010501030e030d0e 65
    0x100303000a079070081c851141e40171035240000c00046480c101c2c4400d1243c040ca9a81d41042d2885240150002c200380900c00e2100941483c000d94400d01c80304410002e040440d01024044401c0c641080034182c02440d021710224001214542c0711102458078075541c1d010508200b42440101d900300303c15141054000a869540742d0860703c0c06043c8881c880e050505540d04003c4036882c2403052400c41c120a100306000201c2c00644126104046c100032450060603800040340761200000842e214148582c0c0050006500400c0e50041c10300242028600f18241089124201d0500442403185e070000001514080c4030344034081d081210445180003852152501e4006070405401c04040c80b85004401c8101e1f540030504034551a0744601515442011004100521600f0300d81c55001c1c00061050590b0000101c11000f12484207680005440c0d41586000e03016100080d01700c911092711201400f403295070701c0c0c0003607045a10900700010f4600300c03d800541907004104010044500e041250346040d44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 205132221 1250 205130971 205131013
    0x11e0905070215150f15160b070f3603050607030b040b1c0803040c030218190519090c0506210901050903270405010305010209010e01050a0e0607080c 66
    0x1500c0d4890b9407144e54804a012151403000b0300903602050301900191182003002e481c88208030b00e09840340c40d00d2004428070700b044c015000200c0e550f541c0f40040002c0c5035032183c001c0356032000d00c0c5049448840e101005201d0444050108102c100c0b82c01d042e0740a078138021250b60001d6500c80280c840e81c1c94181406001040d5034541c035405541009031181d84e40c070b0b0201e1500c1444c3c0d5070348002e07004680191203074003003508014001c4420f00f1503840d010000d40d868000203240810890003410b068580251f51555540340c034400b80314024241014800c54000c80440400442d50041c0d00080881013030402c900044002d80c84150003c5002428560000f2000e031420700100300011404040c0d110030304107600f01c1308111040702300c5800a0083c028120801070741440c007450314060582d010100740300050110f81d802e80c0104c609a41c0015128200d5801110702c0d101d190003400c185052400419004d009030403171540c424810310001030545d0421150310160340400d2110fa003151442d003006800c0140e542d07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 205133471 1250 205132221 205132243
    0xd0e1f02030d060605161103010216080d060806010b0304080d0b04060b120906070e09040305070213090b070e032515090807090b130b120a2414011e09050702 69
    0x43d0a00c50f02169640c0601c0489030086580c2001c440c00c440c00c5c2c1c42e0300d0640c2d40d08201e25a40b5540030468480440c1f81c5103610348101740140c0886036107401e03002c08a021101e055102d40a1908407000402800402001317aa0b8006d130800601c503598000d10f00c001c001000d0b48407545900c80d29085010804d84030b943c001c0c4c03000421516030744029071203c0c01140e640e200c04503031060000f504890b0001c081c3c103007011941d41292003410440c2c10301145500161360a03000c040c4c0100a1030303843c6143c02c00d101d00c0980480c2c10121900348494218007060100c0d0300c802d030340500709004403480c030800f8030b810b6500c00703002000b01140701c0344c142c201e0b52600d0024001125482a0484c0f445000e40205524407184201e40964500402211021401c200040083e000c4c0743c0782c01e603100c1d0040c51071055883c01408100e45840c4541d00e032454012590a14068407110740d4005806580381016a40850f42011955410340e9981131900da80c20000c1d0314000c1d80c05640d600311090040c140810301014680003d02c1d25482 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 205134721 1250 205133471 205133497
    0xd050f0c040e19060b13050f1005011b0b13050f0715140702011d060304050703021003021c0509032a010501060507080a20012f0405030d0e1f0203 64
    0x100d0203801183d94400d03c5840c1485459a00d40707007080040d0381580001d84035100600000c40c070820f5401c46404462045a0710f0701307e40e4001d010000158a5403550304080e14003428406283ca907068418131211150f40c0009120040c8500494154404448400342881e800000c07200d03922207807900c00351680040d00c11034020450101602c105280180604000d42da12078034028108031f030325001140d525030b0506030311501c0d1224120101094451000442c0726502400051000601e144140141281031a48900405206105200d0f05030800c020005101224038400708140e110890030904520803440b01c00c8203420b480d0340014a80c02c1031404d10301d4800030200200102d070780c0c1e0350040d00c0510070360200401d580c8040140f240704074003e41419a10031580d090440c502060803030900d003101c64982c0510088600c180c000d202251030341d1811401341103040f0b00c0c9820a882c11004c255210b0540502c0300900802c0a1010140d8486100007038100141c9045400c642d80407180103034696003c03002c80400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 205135971 1250 205134721 205134731
    0x60b0f09100c080a0f05090a030302150127090602090612071e0f1209081c05130b06150f0304030c11121e0111030115120e0a0602090d050f0c04 63
    0x41c50241c03040c01c00c201e400c2908145020f003c0340c0e0850b120b52003000c0201c103020b4180500c10b2140ca031040d868000e540319400404051152904030f6400b1007050384142d00c1540700e9000300d4926220300804c4140b88600603408903180205142c00006401094491500408003150f01c0d040030445546650058500da01c1d44102e60700403c42005583c0e6984031610040340d4003c1c203042c85180326206500107100809000141107849039910601a40050440401c440c10681098612200d901c00d03075410010440000c60700e84800c0d1340d003c58501008004078031444034a450f081c901c810750400c6416074024070000c0e503524941413038040c101d85100e040030307a800000d0324600001070412480c80a898060b000003030408801c0c410340c0301c0840846103800b43e1a55241d2080040e01d00100740514043c058400140d008a02c07038503001400303502a00307180d20015003420188080c3c2c000200d10441810303002000036a8502c032070400706580381c40e4108020003038814000c008004142c0886c00d421401800c80381480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 205137221 1250 205135971 205135999
    0x6100519082a031005160507050d050306010c060207080d0b03030306010801030b06030c030106030c0e0c0a3e070602010c02014208010b0310020c03070213060b0f09 72
    0x20340c44828000c031800d6500c1002c40941042c141801070041d45045074804003840303001c070042801d10303d40201d400141c9071030b0b100340f08000014840052403044503141807402d001d4203031204d60341d41e1421020407003403200000115900da4410f00d42c400006070810350035940c0c0c000d945400d0381c80d0381c004411400507600e0002c0c80d5a480ca008802ca070300406052703444140f02c0c0d00396240c80c81c2e00400904120391502c24006035080c40d84007802140000e60180c8100e0012510b00030406419440003804119480e604111131108103401030342141050000c08085039a0460340c000c2c01011101c000711000000188521104402d940001c600c020394440781d0003800303480c891a205074281d821300490580000c03641042c13107100c01d46412020322081c40300180c120003c0421102c03514204580d80281c030099448451203109420100544501e5000300c070011031920b41c14070b0201b81c8a0252510080c441d6009030b01052501469402c400080d00e1118001d80d03490881c24001c4850364450f0400e68054410550008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 205138471 1250 205137221 205137259
    0x706090f030b040b0a0204080a0501060f1e060e0d060608060a0f06050d060e0c040c0206011a040308040e060d0206030c090a08120415092615060112020702010201020c061005 76
    0x4001c803076114007200801e445030b503220307030039000020090410303107074280000240080c0800c080e10780b0b14042e4000040312424001038540341243c94015601c0810f09804030914001d14207040c1c402c60b00a403902c0061000d440703000400c3d140b149035001e031a40b030030404003045078000800c0b12400f5102c042401c10032003013215600410b860f494800e031a80120100d40b84e40120324950828402107010005071000c1910440c0043c01312584e0407100700050341700000501100c0c401607294a855a46006087d06007480c42d926018284103500a40f034031000e0003c046441074840364428400c07035500a1a5584034509038600704000d4002c003021511590300003400060182c40403030b82e4202c4007100341106142508280c11400c1034054803882c802040a034550002c0c131072441c200d0424a0140d00c505620f0011f0542541500c0c024000f240b001c5001e9000051080d240e070801011601d55020003c0940c80c5c0009000503402402405181602400743c1c43c108a40f1402144414099490407540081140a203100003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 205139721 1250 205138471 205138499
    0x4082502010e0402090607060e0a0b180c04090f2a050f060915221a09090f070c080d0c0f02030301030b06090c0403050d030c020705011706120c0909070609 68
    0x41d0109003400c645807040e082c5a0000d090039100034000a182180c16918101152034031201c160880e003201070540b08010000d840d00e504404000c04003800386081c9080151522107488219104a41d038460304000c000d50011800c880750340004900d607107146402080c0c80d001101c03550302140d68800705070110711864940280504000041d004600340f0680342c040c000c0550310706030b07170925141c1e0520461070b000505d0007a5003111801090100801c030700c1c0c0700a501521100c1088540d00303141c18881c001e03440e1034211503143c0c030075100d107610b00c03840c6c035501c50545c1d50042008c00900402c00c0003a074042c00201a07000340f02e5080160390f0361000640d0700102207840c1d0000f8040203040c10203a0300860000c1c5420f007805034000c0081505e161400307540c0e039035451074441a1a15040400e8640701d00c0800d103030301030007203000510080c00d21940d0b80c40700d0107202d504d9050081540f07104105000480e00a00410018890f64050140c2001c2d15800c00c0c8800790b644e81c00c18400c05000600305a8042041030003c0f2517 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 205140971 1250 205139721 205139723
    0x20105060117040b130512070303050f012102010e030a14060907030b0c07051203010306050f1506040306050a0608010e03030f0a06060801060c03020f0717010b15031f0e040825 77
    0x2ca030407140c07502d035108070125001900242015218017000d6001c91400d11400d0000030010900c140d6646413454003500789c84000306a1021040365400400441c1c0e00801c0d005290280e0300754800d80c042c42840183c90305030304403000740c2d050311580c1414001c201c01407201d440244850412240c0a5507940000c951710300003400300800507060f440104602105c480c0c00350810714070950995203420383d00d407038151a070f400c261f000303890180d124400d21a60400c0200312a801c0030112441980704071004c40440d000c0d00c03e520008110310381d078600080c811080c50340310001500310f0700001d1104081031907a00d541c13500700750b8424070895454808110034186c1481008200c520035111075080341c4c070b000c00a0b43e4503414000e007607044d40214000320b4249013041c007400f00a04003500380301d018240b81801c000c3c00c540301032028500848040c01034080d00301007001541d078040010000c1d01e416491070300f11640e00b01c041e6031010b09903840c15414081040b90440103881a200750701c40204903035585030600e40f4202812a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 205142221 1250 205140971 205141007
    0xc110a0315060f1203052502060703120507030605060f0a120203040503070b07090f050d02010c14061f080a11030a0506040303090209070e1036030501391418010201050601 75
    0x1c0681c2c1c0d0b0010316070052242c100e1a0f12001f4500d09600440c8051340074250403000528480400742148a02d403160035002030292504000c1c442c10000810101e100c1c00002c44903404020644c00140742c803510140d442c00020860941d101c0c2040c0c074100381da98002d11401c071114a168000140b005200d0b0306480211101c1c80c1194801074039201c24040d80c141814420f90400c20040204d902052005c02c00210f5154400000c281501c0d1a1400e4100d50040002c00a0448003442d000c200c45e00340040c1c001d8110b904421076106000545c80040d241c0914914010898010b44c400c02c4203040e09680074044060003580c40030495950381c0400c4072a010f03403050180d80142403290100c4140d1058a10304101030340d120034418403080c0c03200140d0000994002075090b003085001d082c806c10400780200c49186071031131407040001c01702c5060700741481000781140311240100b0b444540c1092141c1080c4540a0302e075804241d588488032005070078402d902004a0140d800d100c0401c0c8107501ca0a404002e00c41c07260 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 205143471 1250 205142221 205142227
    0x105160222021b06060303040e010e0c0c06040305040e0a0e10050c09030a08070c090b130f060312050c1605100503040606051804030e0102010603030c110a0315060f120305 75
    0x68200701100c94040e506180c0c04a0403074040d1440c514920050000b500316403450a0340041c0d0000403840d00340000c0c1150b0290300144000c10078a100c01650505443d0300f070508070899a2500c6656166006000e185842c901c140800c0c001410b420034000c0050755202d6042e104a81e07203100c43c0005031058420029900e90014180a62203c05030f4412900100164105132510308040d0009190640c0300100359030100f00051414100585c1c0b003580c00003043c64205c00c0c4884c00410000036a264915000100120388607071101300d203542d50b98010310155500000040000c40c44000013400c039080b8011003a854440c0c1c040c0042c0b03100e8200021b01c2159002008031007100d00049044446400140c801c4422945842d80420303030742e0300e0351103444000f00421281c10881c07a05003001094062045150b81c12359244c101d092001c2948000140c6a050700103041030418000c0801203080c6d112182d0028080d82c02560385095074210542243c0c0840e12040303075180c00c50341c0303e026800002c1c40b11030000713002c1b132020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 205144721 1250 205143471 205143473
    0x20c040219030207020f220515010f05070302010204090501090203270c04090c150c120e0a06050a120f151a03010e0709091416180b130504060e0106020c010516 70
    0xe03070004d01c0340d148080c00b1000e10f80b010b000070451071545900d115000c4801910030b446010000d1240e65440036a040c462000000c8a9001901c0b41c070f40615400200400024101d041c0341c001d40440b001494142010041d82d07a480c20f1000084d00142c524000c0843c1070724122800c120b51000038944955103134080c0c110007171407a00300001040368100803107002c4a04c0c0c0000540c20340fa2604800180040c1d01e07520440401450301400000340c03070407042c040c010342000300b242d1511061010780a485082c00c040703641304010700050710003441c0c2e207402484080c10121011482c00c0540c00050078072400102214205807140c680c4031081d098540c02e400401c6003030004000c100600c525180c0c10003000d081c285640ca0701d0300c10143c2a1a220100741840d404003205009111603541c6440c00800b40c01c1c6485005a5a034000048288a581c4221240042c3c0403803048408142000750800401008104100c00c0b0350322030101c20100d0007440350740054000c1084405695001d84200d80130780141c15440300044000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 205145971 1250 205144721 205144727
    0xb09090f07140a0306020313061b09090507090e130512041208070c0803160b0705040e182503060510050303070f050a06020706020c010f020c0a02040e0309040501060f020c040219 78
    0xc10200c1a030b005422803c0000440c034103200445c012404a5a01e02c00c6007601d04200d03069882e0b918408055090300d801d01c2119541c420007a130706480c40da40000c521520340c0d03030007210580015008004000351540500804415400000e01b20503c134034151001b584078824003050a014a214031002c0d030242c44495000a80c00c84018a8550300c11f9a405c0d06c540c0d191304810385141c02c1501d0750007007103151480c51814002910100c55010009140c0a8901400d0101809000801030f20043c400c0600105c48103400303100b03110a05e0040035680d5940134105c0c46035545ca2079000759102c150b90840c901f50200303886496000c401400c1e104098011894a20555a050010320350048291594040c081d00c4000040b981d000900449016810142c0c039001000e080c1c81c2101d0080b556102c0301071040003200744800c001706540303122a03011103001854244e40b656260443c854031320349543c064a07180000c00c1c669048207a011240460780c0c200c80070904044144001c82c07040c1c1180c0100111f00c00704d01c1703011a01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 205147221 1250 205145971 205145999
    0x903181215010b0a1205010f030209100506031e060301150b030901020408030d020a021504240b0607030206011a0705031b010b0d03030605031605060a081e04060b09090f07 75
    0x800e0404076112207a22032550341005400703800c65a6070500004840302d110b03a1001d0015905050f1a00402070765141404107860740c0428407000b17006890b01000100030306041c01c6d94000401010700310654a1510301c9074546000b105c42e20b1185058850320106149040511807080341002e01b200e140320950421303114600a405c01050090a59001c00001c21030b0601803002c1d000c0803c0100000d80c6521140d50082e091104483d51401c00c51503100402020425410512a41282281101581e03519081900026258001900e50800310024901080650000d2490b0480b10303c142112041e0b00210b4000001e8854980e006d042c550041c001c001e54810f83c0810402c0140c0e0007000081d0fa4040140812501b003038035601900401d540721400c00150034284980b0650f0f400c100d9600105c203060100041c103c0c003c40400004201c0b4250000c0d0090901c65054810324034600c000a009140900c3c1c80030180c60090106402600b08801040d41d68500144140c0b00350018005000c58904100c1c03546036040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 205148471 1250 205147221 205147249
    0xb0c07031b081902090906070c080a0504030b010e0103020a0e040f0204180f0c030b01050301020703090905061c15230402010f020c04020708180609010f14040b0d090b090318 76
    0x5203101c90006200c210070041c0b40000711010342840c242c40003500401c8003201e001040d602a58022404000120f40c0c000c0282c2440360b40a06065240d9035030300c008640ba40695080105540c070404004110710850095940c102c80c4206c0c3d10002c000d40711b0040e08124030050b200282140514182000146015044020550810b400e00305603081582caa0500184c0176040980307419030791090a20074850401c020902418054000b5031412064ac0c0d0020812000d034864440c2e21a6103001203000741d5200d0070f085440500d9026400c000b02c000d4180b0120350702001104039a2a4908196a0840140102c800c1091810000803200a680c0c640041d2844d10400c00098214050704210b00c44c81d030f69a00c007810314240100c2100b034071604542c1d00c103c0e4064038600c0700d5225403018852074200d42c6c1e1022840c46100d4041c58000b092444d4178400044034003c5030002144c0f1400031070744582208981d444010307510300a00800485440c0c1c1e11001da03c038400d60440c550203900e0394020243c00e0074600f00ca0742c148 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 205149721 1250 205148471 205148513
    0x406050a0e130c030e0706020c010207090914030a020d0e15042112020c040509030405031c030f11090f180106200105070f020d0f050414010c05060910060b0c0703 71
    0x24a6002d02d000c44601c0d918100100303a46440c0300c0741ca48820800e600c06016240014200e0801c0e00b4000707507030307030380d4501c5a041125240d090117000c00c185004003561408031703642103a0310343c19404c0001e51100c904605140c00583c0d0a4100d90807458140340e0008152424921b2910300380c1841041d010030070340401504c00c0704000880040000744800140504401258050101000507c0800c02a9100030741504c00e10741c018481400555004603521036083c101c0a030840e60030400303080c2076000e0400002c019450902d0b040c80001c0c8a03d0740d0000b001802021501c070707000f466010b4100000ca4030090030301d00007001510014070009010310302000b4503100d00e8172880600140c00111509580c011507240f03000400180c40c0006185c0c0400c504000342c1042d0915042404103040010f04a00681c446c01c00140c0001d051203516901034200383c64026000f07801e455803458010710781d036502c5031522030110b500e5180c200c0010380403407a032080e40c42c86243c01d00070b00480361958507a111030300c24444014880c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 205150971 1250 205149721 205149739
    0x4060f0c0c060302041703070b060d1a0112032a0213110315100c03020a02150409020703031a0301090f0206030a110a02010608061503060721060e0a0608030406050a0e 73
    0x450140601e81d8024511642c0240c4d407541040b01320906543c40464001e0030b58810b111a10006840d86075507a488a400d6a02c00b488001c03a0500f41d01000d01940003810985040001151190007420081140c034042e440e2220780911402d0744581040c2100c02c004564039908920400500d440c41403190f40c02c4e00510081360701d0010020b0b42016601c04d4810980125402408041d80d00f0010440d040c3c0d10b0030b500342000b0310112610082d46444003080028880c4049068400e8549800d5003914054010080110745030307111860080c0040528140b40c525101500d00354605510701400f07003064681c1e010403081010043da50134000700b0f03000608041d41d82c80d00d60040201c0c0302a10000b0301031020040c3c1c008101c2c540382450150800d0f2002e4070781a052001c0386022901600c002500a402c030480c0d2422009581c003607194085da000860030448005030401c9800514140380d9081140540210032003000030b00d0340e804c90030750380740314074482c03131004c280140580c021950144a460301141005803907004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 205152221 1250 205150971 205150973
    0x3020405040c020a17120c070609080c030c0c060a0906110a2a0e060a06050d0905010627061d100f0f03060b030714120c030106030503030103150204050604060f0c 71
    0x54451007030101c0d0050b400b2004e103100780289008050f5041500f180c600d86400c03040e0b80000c44c58000204914920000010f5540c01c00c00198031014507580c1000c05140c0b20114115441c0e00c0e03510903903100601d889458403941d00c500d844c90072250760524030f4940070046443c0c4641510541113502c2d400c441070288407040008a001e4010400c00100d41c060051050352614141c0c016a92403070b0000800940d101081203465110310403900259411818820b403a00512400c0380081e28030090014095402c200b40002ea1280d44020020310201030709003078840b490344100c00b8040b101e2600c100c0000310841c0e018229424985800142c1160700301c0074000d031b01500c440d44007040003000d90011445011140080050003c940315440510100b14060022a132400d419600351001540645124410f09501e1040c6d00004004407802884041e000b03010b15980d0b401c003a601e0b50024030041d00c0b0300700950100d0f055007460b4800c480c00c3d00c00c0108035508060034080b08654800210b04644107111401004070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 205153471 1250 205152221 205152229
    0x1c021914100f0b0406150f0905030d0512011e3b0a0605040203060616031e0503070f020c0a1e0306050f070206090f06070c08041d06120307051906060b0309010c0905090403120c03020405 81
    0xc030400c1401c1c1c84890342c0781004500c100300744405910010fc5900c901040c003141e00c0c0500b40503012a00c41c0e01032082c03601500c4d1140b00c60700c480101c01c01e013200718483d01000d50159514810b4402c007520380003000101c0d500c20620050380301c03c480450b0311000030004c0301624002c0105110209009207052004003001c80c40310031016040c4500707400410008000c01c24810740c41880c0340c2c4007240394405816000129404105202800e0007030607441c10350b10b2000b04c1800f00c1c0f50b0502008680114090000d820200d00b500071a11042c0c8540b80103000e1000000e541074000148058100d01c01d60040c100d81c1c1e90160f040b0303a074020044007141c007280c0c100b02c0000c000c2841070314200d02100520b000c001e90700380712040213101700c0c41d03102c40d0280c1d800030b101001c08100d01194001c1e03a02003550b15070840506078909200107104540064002c01404001c0c41070005055002c10b50780b070303843d17211104040e45803004c0103000b082c02c88000b000074029100000d90f000c0749401202c42000c03a8140942071a0b01e510003e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 205154721 1250 205153471 205153483
    0x61805060a0605240a0f050904020406080f060909070b030601021c0201230c04051201090f030807030f060b0306011214181c021914100f0b0406150f090503 68
    0x801071594594009100030301d0141480840307002d0008207007a90307a0880d86107a055000e009034080a2101300c884807180c40d4003a60071240145030003007085558940f5150081d0410030240c448000c101405000221a0f0810b50449070040c0c0d02c280052a43c2c910b8416a41c0d070307030780c8014099411800303804804003031000080407002c40e038003041c0c00104045904100a000c030340414851036240c00c205005002101342c0120448003507440035a07a008451510408032400b6104102c07009040643d502c400304140b40d4441d180c54000d02c015039060010a80442703454040c1c440c0c6000300c8c0c940e00d0042011880d95809401c550f0718440d1440000b144610b081c0c90783d080f0804040700e50840b10303040b101250b00d20580910202112146508242e40e9034109210300075540c151010711070b401520802405028016407050032503000303501e03104545900c602c50341c86101a10b40b804d80f9010040c104007583c8811b141c05d005010598a114014895070140c103281281e0b00001126a00309201c540722022130f45403070501030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 205155971 1250 205154721 205154731
    0x201020409060e0411220e031c02032d060906010c02040e07080d02071214030c1f0606050a0f0806120604200306090307060c031b0201060e071b06180506 67
    0x40c00e020f616040c2484070091034106210342c420513544407030460103003c81e03060b000700f580d02c0c60f0009078001e034203045940345110729a4210400300662649650f402c40c00d40065104030580101640004000794184007011a05640c207400d5441c020006000d50400d540c0f09948aa41450f1090380690280c0100c3e046403003e11060906412190051000c09070402c94095142e24905c028503c0d903140005030081c02503d440020608644000c40f800c1c0c0d480c0800c1a6440c2c0c0c071038801500c200d0901c0c80803609404019030400c0d0016402e1010010b01c1c14018410b43d0701c0a00241c44035100c0b04080e6900315000c540c02000c4540c4078183c250184107419003000303110b10851066110010000340100720f030007011a20144144250301080401ca0491400300a4900b0160b03c814080b511200c4800168080e000c04c9028602612030449480e09882d4150000401c5540c0140041c000303469020003120f5481000d00c0703003207400c4869012600061440c2e0310401050008102a00c0000c4181d5100e5040030402e80d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 205157221 1250 205155971 205155989
    0xf060914090105071107031707050f0706080a14060f0a1a030a06150203040306050408120f0703140702120f13030803150f0f01030b040b030708030d05090a0f0210020102040906 77
    0x304040784000344501504442c01d4241100203078000320a541d80c44040380001050903070b4000b80e0a17001b803c4001907a206550040c01c1d03817855100034100b640e44562502c204800107007240080713921600039125108400020281505481d0b48580520042501440b4500d0300000c1034040080c0c040c03502d0902203103401c01c14105994905200290506403106504200164044401191401600001260b086907030204020030141d8031400d049407540505800e40300303000b07080004c01c40790b803a0b4081d0880c4262403a850400c01c250325001003007038a0f271040b18518096400540c00c6850700c0203a40252103084906094945020070020020100d81c1c4d003540100c66807407022041c000784010524090f04081420ba403202c04604c0180d001813a29100700072440c0c1810364a40740c14202c0e07107554014014540c80502114402d0703640b903000d15030701d9020034501c0d03541502c0e0070041007950b0000304000406035000215417407040c0003502004207051803c001c00c2e05665003040000340040e103a004200c01816004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 205158471 1250 205157221 205157261
    0x402030709050a0b0a0f060e1018030b0906090d2012191106090d0e0303090a03050321010b090909150109060314010c120e0a0605040503090f0109080a060f0609 70
    0xd05110a52070582c100b051046c0c070b2120203000ba50f602041102407424101c0c3c540d41c0c500f00038141a9004200d000302c1452081c480a8040284080e4400b900c1c0244100c904136000c070f5450511450700c48070f504c13040c0400110820300c503141904240301e204001300080025141505030802c40b050a6078005d040d50460301c01103c546079011034201e000343d6041c41c1c040d006404c007440c06000d245d4841a080c200801407003404c032142c0d103450700c0410540d101420050621142d0503100d040c040d42ea44c000210034242150344500400f007080313079507450310b04a80b00c00d00c005050840803030802030a080000c02003455489510003011200640f0003180d0b0090480e00000202d0032700b14280142d0103030740010000100ea040007030306502541e021060f403a6142c8207890001d4030070504024141840e0300071501030b01c100d04000601042c010301100a00034118222400d80c000c1c803d5100541c0c0390500741c8120030f400d801164080d804180c07250820481010700c2c01e03001840c50b45400c80c020448050f01c9034086500c04003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 205159721 1250 205158471 205158491
    0x501030b07170408030703020a09080123010b04050604090e0109051903090b0301080d0e040213030c0504050f090a0605040f080a20060613021303021804060501050114120402030709050a 81
    0x9842e151a907070b440706002c800c038074294941c04001d21001e007030001010760000d12007a50038031494150003d00302a5000740001d81c64441d40b01074000700d12006c000c42030b05032800015140c01d0701c1c04543c100e0b600a1301840c10103241c000c603100204038402101603595200e0490b540052003d00c44034001c20140303180c5100202050034000d05003000d6030445d03508124204018040010002240c24003040c0a01d40058201d0000e4040b4000c0d0140100e50030f0241d03502500441000403181a207026200107903400c021590325908100d00e10482510011280e42009103504049106a00301035400b5002d5142c0c0010a0050380c0d036154103500094480b80080c1d2070307844060300c2e4000988a000080034006c000c14a900385100000d02a50401e80b481010700d60004401c4c10b940f014904050040d50018442681448803040309248180110340807102c40c0d01e84400401c0700c0d0f01402d203c0d8458501c081105060102c4c0302c0e1800e182c9800500141e9151045042c0020035903c2400351510441c5030b68808537541001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 205160971 1250 205159721 205159727
    0xa03020d08070801050901030212010e0d03020405040b0a0509011208040b070b06040e010e0601120c0b0301090902090109090b0c0a1e02071e03050d051b120909130b06010f020309040501030b07 84
    0xc0d150004002c3d84400400c100d60f50303204680d05480d011103000700f011060303403192401002c0715510500035000c3c1c40c5032524201d80540c0a0000c9540c1500c0c140003140c07411040141c1e109160040341e50000008006001c01c60882040080c6240300d038156a103810b46aa504407080c2d041208121002e55000040000c241443d010756203107480040024400e8601640c5003035268041409041c440041c4448074005020203016154000c1c1200c0511030341d00d503160303035194004e02403e40c41a4000c2c200314000080d4210f0510a980707140350480314103803ca440300d2031110b019600140d40c00c01000f00030082140c1020b030011580e0300380f107682d030010f003d2541b501400802c803019841c00000303050100c1c4810800300303101046040c45180185030079566142c41141c08011001000750b103055612400d848428032859841c000d00d21100c1c11074001120f41e6424100d400310340e4030400b000b0808a08031021810750750007040f86202c40e000d140140d90800d010b00300420200e440076403003910315054400c1840300c0c60750 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 205162221 1250 205160971 205160987
    0x20a0b0307090303140409060e04170a0801050d15180b090a030e1311040618270c020c04090501050609070f021908040e0f10090b01120f0207050a03020d 67
    0x204a65810381589061100506103140038400982404401c00300d1508003020303242118060503035008101300c6151a8404403100b26400c86040700c0d2000400074113810f241000d81a076845039456070f1420078a030300b4070041c8410318011030b900300c405260441240c5804212030044064081c407906011307600c0703801410140d6200303401034482038850f0400407094000c00c0d0320003405041c0741c200352883c0701e030f2841c860789080050080009003040080c001c580402d100358486050803030041001500d0343e209482e5500c0c0e280c00780d204013840848404891154182400b143c01602101941e0300690f807156071140d002c142510016041112030b65591410082c0500d080c0d0f803c0c41e04a4a01d250401072405400c0c4080d40d149041803683d4440d1501c1044401040740b6041210041c02a5006081e03207401e00e65002500020203980d485640c0d045603e000c1401c0c01d55124118004905959020301503914420300710080c0000d01c40040b0351074007041090301080041002e060a07070301c82d50042c840d401240c480100342103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 205163471 1250 205162221 205162229
    0x1509030306030c040e0c01030b030705030a050d030c08130f050c1903031b0209040b152205130507090e0106080d0215011a03040b0c090a06030c2d0804050a05060406050103020a 77
    0x1361820100c0303140c509000503509006031081c200087c28114030710001c0d10308000ca40c08207601d4820303d09c90303008210b03020409110b000c1e907684007405483c12080068561480c11100d5a0581c404810340d0303030202e410003c00071019400303036080d110701d060040e0204940c9402c0f519980020321030100d04204156101501e9410b4080070005a030200c41079600044c1d0884001d04090100681c24002c20031030401c000c2c026011800c0207040b0b604100d440790404c02c100d030740422251580d6117090009440d0074111200f08080c1d40e4080044d00c1c0f00c80c141540640201440400c00f005990386242c007051040007005009604000c41e00246190404420b2081c038042058000905500b90005503140d000c2004041d00c0d0450f41c01107030001150b558180010080c0500c0301c150394007260f4410300080454140d4070200700c1704400e03610003110b9102d400812a07003944400c40040104060001101841c0c0700e4540c00d0340061160055035890f141c2c940300c15240c240e0541d000d070340c1a07554034010011840c0035240c0c04010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 205164721 1250 205163471 205163479
    0x1030b160306080615120105070801050a090b01140a020f030f0409050601110307030507060209041d06090115050f03070f0e060a05010c03020309040902130603030816050403170a021509030306030c 86
    0x2141c1000d020540303034040a4401d6120365031481d41c0c071203641d540c0d4201015071364400008000d127142c10140200040c3c400e10446005d802074000c007141c0e08078140690111144180c44043c0f51300303000c031407001a0b6444040e003c1c0c11800b90b00d810400c204800c1c002031520313901004000b0b440703038100201d40d011070310007900140c180030140464940d80c0e00c010080c2e0381c000c0d8140c00d0182c2c07a10729a05220703010384103000c03a00c2d6201c2c0c03030b081c5c02403801c9240c0508020151241300494a082e91100b400d50300b210041e110303445090041c100e00b00701e01d281440c0752112200303000c1c06588038540d807400400501406074124031400d2191408100701428030028a0700241002d10380b0711510a900d45020b0340b00d00c1021305070350049850b009080c0554540382030800e500b00e00700c0f1041003115a0703400d004100f4130f1b0585075911139005140380b01c2c015a01c00c20a072416243c02811a0218400c20300441c0496030016468800b50f0107842524100c2d42072104003e8405c0280b903000c2c0d07075a072400904260510241900389449 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 205165971 1250 205164721 205164731
    0x30d030e061815090c1302120106020d0509092509030611031b16080c0a031403010b0301060c1502040e04050c0301061a070203070302030a0c1e0509070804110901030b1603 75
    0x2c4009540c2e0804120a059029a07803160a241820449410426908103440030b040001141665004244503c0300e021984001e907214002241c849103185510400900300748420b055030308e0b018981c15000a8075211160344004503514541c45400c03294241c0000c6400c603e820402e000103070141e00c5082701e200840e1803840ca0200380c26203429a0700c5404609405021500c1c140d04005040c591080310340102c119600c409070621070965070400d18008a00040c0344001800980d2600c4054074107035005000c2c3c80e4110380c2009011112001c10a01c25258100b400e4080d1280402ea44010006001440844030981c5440d0415900d00000c4014442c000d1380f40c1300040111a111419000608400400b519520b01a600000e4500000c60300065818018604580304004400000d2400c0b82d178544801110001d0b83c00c04bc2607943c1c0c00d481441d4202c00f07982c000900c194801d09e1030319802440b40d1040c040c00032404022440020003600101c0c0c40303005840a211240e0794500c400c4200300000c0c0340a00c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 205167221 1250 205165971 205166011
    0x190303051b01051e070c02030a15060504020702060906031b072001171503120301080714030d1e1707020a0b0a020c0c130e2a010503010b1b01020405030d030e06 70
    0x900c1c504004c203020050740e00c442c003140030700d80b02c0c0d911810b07841d0f0000c0480d250800da60907c041d400850a5220202c6480c0c44800500380c1058000c2e54001900103001c1f40c2004203590610446620003014650a541412aa044410400300142c2016809600d080390ba1202c0010b400502800352100b030350501822820f0300b0781c1074036954806948a201315030982e000c1c08001020901d03161016030801000d66004c000421124000142941103d0140141a040310345100a054403086140c20510004010035192681b0030b803400442d0702c6031001e91620003100c4c1d0042c241c1054000042e121000141c100c0c10622040c0000000b25907001302a0a804500e04002d00c40706503650982e0190302d90081d141c800500e018450740307602c800c40013018413094a801d0071501710354021559034040004000301c0c40804c08a019442a07082e81d0503210403540b0309103072a103444401d10441c1d0718084030004541d0200008103d50f2000d000314035103620381d6100420595078907080c0604045000700090306000345000101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 205168471 1250 205167221 205167241
    0xb0c070816060b040e0309030613050304090c1202070303090210031802090612060f091c050306090a0902030f030909010801020a08061009030204050403082505030105040b190303051b0105 82
    0xc404848400c6041e0792800c00c0e1900c500a0b0591400d90360303010b0315007041034640381c2003c001400b422a00701d003602c0e1140d403141c523064a000d241030b40c040e2043d40203001c02d20000030701d680420705504080c00e24108421920501400b680e105a10460000e42c48441c1c09045080408580c1d1040500b82024014408021100380300b00d441642c01901c0f45290304040382181d00c3d04101c0c1c1403800c000343c0a8a90910748000080343d0048181c81541480c132515070a160100801d0b0f19a08241000799103c503d1502d03031100b008081c01e00540440780c102d41d2001641e0040e9810012074500041500c09180c440681c00d0030024202016032142600740d0041000355041ea500520303a0307074851021104c0348544a03604100701c40b0340140d13400c025080342c5040b09000500d900910b105224008006452100310400d41c03010356140c02000b1400003150382813006000615143c0c00c0100340143c00313000128411124222000c0d900344660060380841c9000071015207800d507107602c6641c4000960020304c01400c2500141c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 205169721 1250 205168471 205168477
    0xb0408010c08071413032a15080429040303051012050a1209080105010f0509060d0f02091f0b03090f030301060801120804080a0317010807031509140d0c0b0c0708 71
    0x401c1c8113110010b1140c1d41400861720100185400c00c1b009401041119a0340c07143c14030141c1442e600018136100090000c8142c8622603400b00e00359507450050312580e940762850440020261011060341e040d8000f11800c500c00184103d000307940100f881e041090842d050034003280c00c2140c0c8072031100b0411010442c00207010b60281d91040c514110a480440211046005034000d14159400e1000000b0b4102c0100701c504240e03502119010000d840d2a410007070381c02141e02d0000c100b10382e040c0100d0050314200300400c3c2c2c424a2041c000c400b880d44840104800070b010b40084a100720044140304002c40300b00b000101a4100d04002c42c60f55040040c080d000c154144100d0140d40350f030507840e03010130100c01e013030720001c1520301c0448403007050300c0c6405041d04078140045060010442d000050f00c040c00103200c02125000b11002c0c089412048a04000d800012000c2d600008542081d00d400c40b41040685000b000640d100240070b9400e180200d00403902818543c01c00809014420100b41c8550803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 205170971 1250 205169721 205169747
    0x411030d080c030a090210030605040b01110d080a020904020a0c0b0109060315020a03020403020a09020711060a09030f02030114070c0b012301030e070803030709090b12030702010503041703010b0408010c0807 91
    0x142c640c50395261034840010b4440031400a42100c40c640e441150503030560001c1003030f5813003140c2c2440391510700001102d14194803d4921815030004100c083c00c00d0150340c0203600020040c0b809468000148d012601b40d80c0100314640c002a0700c41c01c48014031101e1220710b400f41c4040041805400d107180c031003030142e2200701c201e2808264000b03030901320380b4000e5046074021a4041d0600e03802964444407607001f0342007010b003502c09280310340b18090545043c508954001505071074443c0c071242035445444110544107812a019076035010800031090140842d00d10644440da10020f072680b0610307010301c0842c8103900000c1c10303501203075204001110008410340030742401c0c41d00080200313001345190f03c0c2c040c140d4085c815a00002040c80361803a480b03610f110130b460300d0402c28422251980d060142080501910300c0f05600140100320048d88940001c43d0401e000d440b005c0409803204054080c41d900070f0344050a00c88c000107080044440a00507204111024140b180c00d0340342440002c2c100266040c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 205172221 1250 205170971 205170991
    0x803061011010c0509120c010203040603020d18141006060f080717010e060a050a030f08090315010603090b0708060a0519080f0705031c05070b0714030f0411030d08 72
    0x315211000d841060001101805803000740400f44840f14090b003950b010f49840d501810200001d911a884000f560503446681a8011417a152a10790101c000b900440c1403d00d00945400c800600e11b02041070b4219504d020f21240704100da8503040851425030410522050035003800b20801c603071500403549103146a242c0c280040c2d6682d4920045907411444a50002c1c0d0070001c0002003101c0101c000039500c06c2d0340070344028404c551074404014000e5200d110080202d582c1040b800005a2040003804048401074111071106107003406248031804240c220b440040d03034402030306040c050544c0c462a0042c8050900c9d030601d007007140120340440040d0043e64002c40b20003844405502c0030420312002007004201741d41c529070800844a80381c2c9818032845100b44149404100d80d1101c11613032030b0b461003158885500d4503540d40d54480f50700f88024103800c10703c1142c3c13100484100010001b5807080020b55034621716840d1074039211701520001c0c282c050003030340b041c1194000140c0026a1070340200000e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 205173471 1250 205172221 205172239
    0x2d020306030d0801180203130605090a1502120a09020a030804080c04110702010e040c050d150528060e010210020406080604060e06031209030a02060406090303020601050303070c060c0c1a0a08090a080306 89
    0x92389400c00040d03420002001c4514210130403981c0c41001c241c1d141024408c400301c84d6003040e41c2c02010182d0007100d00d0b945c0306800e410040341c5051202e03840343c1c24951000e03108581c00c9a803a111400207400507030002d0344540000300c054a65251a00c615140c80e10481691414070109400080040308044522070195603655032030140705004900f40e0303404000a40090160301407541c281ca801081912031940034400182041045408188040c0310b00940128104165460300001315040c00101c070040e07055016906049010107032900080c03014050301d8071900500c0c1000d0007030100f1a80a0b40c06105844005028040c1076900407a4111104012107034490301e80300f90b20000b90420b80608070003548420006000201c10ba0040480400c0340e000f0780035074000e80e0340c42051544a1190300b00052040080000512600c0e02403080000c200307000d084400c030142e45031740700402c5921a1803031142c0314020215201245541c00005194400502405054620001d5403104040e02025003410322880c604 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 205174721 1250 205173471 205173481
    0x3040f050f0411160b06040b030a12092312120405061803030315090703090f12050903010f0f0c17040807030507060c09060305070206070c062d020306030d0801180203 73
    0x550803100701403c065040315a500400d00c20003425296425003140c0310010400054601e2030b00348500c400c1c501c40500a0114400e040d680c2061501c2c0e4564030005211a005005ca1a0410091424031845d10000e842d159403a480b820020300c80d800815120310343c5d126806445e41d80813404243c404450b02a207116440344806000e441a6401d00c591040d058800842002a4621081e07d52846101d040e1806c0c000c5840e22741044040d100006006030034040200d005400064501e0305400104290b0714140d41000340e0200000d0944150200c15814642c807122a104548110300c100d40982c84141042210b54100300102c0c1c401c003034010000782c46c030107001c00c10b2000e00d4010411240f45ca42c1c0400108024003150030080c003040114011000003d181c000010b0181c3c1c000070b60a1b0003500700307841c3c3c81d00070310071a911807000e03004100d0401034a901c040d18202c940b41500889412020120700d01507142d25020040c0752400501001c40c03801c01c104000100000d0f0148124020245144000541e0769654 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 205175971 1250 205174721 205174729
    0x3032705010f0905030a0b040605131101050a09050d050c01120212060d05031e070b0105040204030503030406050603160b0c0609070609030f020d0c03050a06060b090105092b05070602010501060203040f050f 90
    0x802c1c2d0041742c05000f00c191610821164030b455a206602c5004100420744072410f00f0410403c012038024018808020400080e40c0035601900c44c03070355585013544141d512000400e581400854048420f94040c200b039084660f00034880000260115404500302490014100e114042c0a00b01c140258a11612001070141c20f0040300c400c541c800300c0c44005401c0d250442e042e42c1d0300c10982070f200e41d81040c002003658030f0240201d41c1103070b821000460071600ca90301da030002800302400007039052003800501002d1042030006803000784510211315451350210a075690070400024200b0940e0381100d4824890180c10100482c1070f640c1203503040340c901007688040303003150850f518081c207055600c080c000204000000c1c0e42c11560b11418081c41041d0344c80d032240b4000d0180c02c50582c0807034001c3c4a94071907030404802c0140110900035440035842c406109603564104400c01c01d542c039810502c0705019141c0c090042c24010711881c80150b150074900100203c440301580a00d40c800c0c0214a0310414030f6803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 205177221 1250 205175971 205175987
    0x270507110d0c0f0b070903051006030f0209130c0816050a05093d03030e010206100b07020a1d07140c0304090f02190906020d05030f070e0d0b01030c03032705010f 71
    0x913200b04030041d18108a40e0203014401d4903c4100d0b16441004205107030002d4a024031001c0304d9000c000c2d80980502ea03402c0144c0d02c040185010280c110b41c8a0100214403444540300003840d0764000340800c407910658554410340681c00440c02000754880401041e1280c0c1e41403503000c1c00002c2c1140c400030390321028204941808170420340031500711029060046122501604403071280c5c80f588081c042c04801640c8a882c1191503d2002d000c0d031000b0003215644400402505100411842c640b0340c80d03002a0001d840c0090140058100d01000c0240340d507002a4001203801100c8899400c3c16114800c4541e2849240541c0301445e48600b040c16400c00ca40d015251505a035040d00c40d00a0300d0600014913180d890321441005102c4d001c3d80386141c0d80994100c900513029009482d58030350b03071084c0980b1304e4121001000c0d045500c030303103060001c40c4003045294080c600c00c810710030000d441c50800426814208046413640c5183c4012208a881d50007038800480d0802c1c208407038550000541903e10750 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 205178471 1250 205177221 205177223
    0x209240702060325020319020115031e06052e12060c03110a02010f0b0d081204110d0803090c09060123041208030613020f0a0507020406270507110d0c0f 67
    0x2030208400901c01340d0b0088050500d090080504105012075181c04034240e40310b5036070820004032054020f00200d13001d403ca42000c0101c003c400038025070282d41c1c520840c0c40440d04002c1e080c03010116134804041249240558ac2c0c40800081c02003410442d016441d0146000010801030b61240c03a481024047e4100120850840480716220562084043c3c080e00300c02d0000080c06160407280142c910700700342441d04070b07900103895504206500c28445104003010b03000303607035408001d200c030505030751010084401c003481070790481d4a905009416501c0c0c04a00344d4440e20811030302040060f42d9a004c140000485900503c09c04011405400184903105076042402d09403050380c01d01045c40354208c001c50080c03c094030007a01d0105007c1d0240100d003c0c40b54003c00d40801081a8294284543c000d00000b034001040010303403550302c0400c0049004880b00c041ea4032000102002d040c001244210350384814a07051000040c188904010703161528800c581c028014008140c07401e2004140081000c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 205179721 1250 205178471 205178521
    0xa0210052b0209040608010510032303040303092c0408160b0a0c0e03070509190216031d0d0206041503092012070e06060c0a0204060902092407020603 66
    0x4000e504024000395000003143c40c015030a1100c00685030300144a01c070310136042030050319160b60456444035400c3c0e10344402c0071920302082c0c008100036075040c070050004511a0700c444810342e00d4800e00e40b550360300d171801c101384208500408003110b80e150f00101b80d00681c0409402e40d114008031070360740d04603160741c0e010388114151010842400401e0f030015070034501c03a848810100600c0400c040d555205805695000b03900b40010900303c00039444440e60750075842002604280c2d0110581c00301c20f865440c1a4005900803400594030200902d041b0407041059a0030350103082c2ea0303004a103a0307200724413603604d124841c1461000300c0c9101e6880074288680c03014040c2d1180d2640c2d480007001034074007600c007031083c9003401c3c50351000701000609408440c200b4200304039030382e01c08040240c42c0e00000003a0040d40a90048400107a55520402026160784000181c0f2001a0428007074003e030144024003040c0030008003504580c00c00400e452607030f40d040781c00c103a40e50341e041c050f511501c2011026001c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205180971 1250 205179721 205179787
    0x6040b190b030a06080601030f14120d1409010902030a0b060f040501140102150709031205360d05030d0b060415030b1c02100c0512130302120a021005 66
    0x425166001140203c0c40321006014031500d4400550301d0700ca003031100411101910280e0400581c0700d030304030f09107100c158007070f07503031100f0f2219401005a21034446403056503503444c54107040309201460300d81c0003070900000300300c00c11117540030a507198601f8030084e106986c03040016089541d1038424030305015004c3e000b40595603440f900b03c0e184011150040d03015019035440d40400c601445040c0f803042c003031603560303040140c6151145c8580c4156003c00302c081050402054200f24008600c40d82c0c1d40d0002c101054861040620703a4520344d8030404a24465104400388070080b60340041681d90b040051500056400c00500004050380f00350f034031041044d002d405550301e40603050b502c114280e05003500c80030750111130f9034a020940116420001e5000380c01c006402c2d070361403140e510508020300c03500c101e4443d0755001107201e1680d0400c1000e00240001710b10103204600b040e034040c0d000d41041078000c00c0910a00d900090f541c50119180e0340403c10040740208c0c01c81c1142d110f82200c0740c02c0c2031078608 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205182221 1250 205180971 205180979
    0x80405030a150501050105090612130803070f110309031e0a050706111605090c090103110c0c010216210510090f030e0a0501140a020102131202100503090606040b19 72
    0x80540808182c01c01e0740c52500b000082c039035014004075081d0841c02050b0341d2500210740c100152200010780801c4214007074588001c00900c404c4000c5024081e0368a4012000003800401024070000160010702c64205000c0407803603445c00500ca410700b03001c0395070040c07100c4005100a4506a0140c002421500c140c503c001600ca422130070501e4520035041c00d07100404c901da0202003002e1001e1045030b810000000004ac0c50801003405817609850501d00440c820005104c000d83d00e0700114106c1010390408118000741d0b60301000695007140005004102140c50488020070300f02c4c241a4060300c800e140c10205081000501c8000b112081c0d03140700708081c00d090300b050380c0882c0d105a03040b03001c98454104042c061400018080403601e050790f41c0028a1a041d0b80980907070001c80d0104c1c20b640d002c0c0460840d01000c130310500090210b903c850750a040103401001031403250145000140002001400450705000c11000c0d8030190070f84002c14900d99810101700030641c10800c00f400c407149424042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205183471 1250 205182221 205182233
    0x51b22180b16020303010f03060b180109020913050609010303030c1e02060105090604020c06010501051b1c170f011a040b120402101b2604080109031701060806010804080405030a 78
    0x20b409180151203040d10140c0c1800183c1e030f6403100303020743c040140403a0000c00006420341c00c03005400ca0040c2c20100d101071100c0012400302000c0e000400b141c2d030089172030708603401c3c48461400399946043c000e01503800d0150101e480c0000600000d020991a6801140128012680c0240307a07110410007040700e4115010094441d0310a000e610f202e010407101040c4640360500a03210080801c501a080c16444c0600644090344a4000e00030101c07580d49440800000510841051203840c841600c43c006800030010560600d803e100700d4158800c4047c080440a10030040c0c0c155060800000780310003d11004000501940e400110900300c00112030702100ba8032504e0500491080d102c811401980c4402a2158034101c030700315025842815a0702c010a107100005804d49101c0000c011112880828a8040e039006030450000f0303a4640c1b0400701010740c01090303c0034020159005950b00c0d41019401007a6141c050308590401c20800c0204040c807003004201d4006050050880f038680320103203086 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205184721 1250 205183471 205183493
    0x3020f0f03010e1509070f02070504020a08040501110f07032d0309111e090406060305010c02160b0406050307112d1209010504050d05010204030f030c051b2218 70
    0xc4401041c0c100400e5012031032100713600ca0340c880140540302036968020f003242c241008403030f10700841c89490303000211921030b480100f14000840e40c40070428901414158252080f5010074004000104a444e140c0c600c40001e840441d40e140c0780c231210781115202c040b0400c85800c9002a0205001d030044541c0e00d07015480326a9007032203582c2541c1010f400008100e5400105841071400301d40e10b19010300742e80307044034204e94442c1c40340e000081c1840c1c49442c0c4a084840d081c4540c40564425400c01e0448261008268018810641010300d0075040c400001e24500002d00f12200b03010810801c41d2540c5000d00101ca1b400c0c0e58844645031000c00a000f901d003040b41a0711071a8140107228105c0c207503c20780b2007119031400c07040c0c4507646420315042c04e0020f40baa0611003551195424400440000d030700d036040cac1304920f00070703940ca01d05040d05080030740c03c041040b298054100c00610524911ba182c1011030203201074024801243c000c4503a4410019106c0c2c000140e010005003900310003007040e00018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205185971 1250 205184721 205184729
    0xa03050f0f030a0c08130b06010309081603020102040e0c0c030a0e0d0506040302030417070e010b0a0c080d0c0e090f0a051003051207110a0f0e040c090207050d0e010207060c0206070303020f0f0301 86
    0x8489464661205000243c00080720240401f05a00b0004520703501a40107100e2a80c400e2500358038014140d00f02c401e4140c658401100140d40003d0304011103001e060303101d5007000141044514100e514010541d40744a6000c069080c0002c3c0c070003030a03081d50380041c1c1403405600302040d6540c619080c90001e44aa1103809800e0f041c0003001007945640c140002c000c403d40380120801840d0b0303400c00c105020f446e000041c0003801c0184002000300091420380151841130f0003c8004115484240130261400204000b0380e03003d10720b03c600704009140c0500010307801800e082d01c0081c8a0300c5400c100e515080294002130f00c1885800518464001c0550040c0501800b402c0307482900300f1101e08100e5854124440d18204c6004e000d018052000d201c4a1160040d1041d03542c000001c1c0d4442620050f44c1042c1415600c0d500300d002941e01c81c40c0c111035035607460f2100b44041e11005050800103400035498080190049a001c02c03008205030182d41140d0750b00c200d0100d13013522107110711100e03140d9a0003409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205187221 1250 205185971 205185977
    0x7060b0a060c02030307020f030115090902090c0c0c041a100207180605060f280513060f022a0406030c1401020307080a05030901092f0a080a03050f0f030a0c 69
    0x1000040692042c40003101d2954010091032405100b5000c1010b00d28071125503980c555650f041400c40c284074484190002c2422010100e10816a0300402183c030500600154400c03100b00924401d100001c03440c01c0c3d5011085400088001544104000d5100071001c9a508014840c0e0000300c5507800180c2c1004842c02c803c080080341503052405000d0301c0700361007161740208003806004880b80c0146c010b0702c00303030f980580c001b14201429212803d12184034201e080114000081040c0a41da0120700e000140c003050410780781070215100c000395075201041041e110006c0e0301a81c1ca4101d0481140c0340d0403054018010301c5095141c0c100a180301c0c1c060300c100300c0051880e1003030441d80d50000c41501c80094121008a0400c1a468030513940b03a0700080c00713187c06550b103e46110010340740c905802e125003000c0100854407114026904220405006800d1040410726010400194005203400c80c490f458a8079940352800d00d40400054080c448541c41e621001008011000c0c4050b40001100b00d0295 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205188471 1250 205187221 205187239
    0x1404060902190c031202030c071a10141203040b0c19080304021309020325090e0c04020a051306021b04140a1503020d110108090d090e0c0c010207060b 66
    0x504000304a110b030381401c1002d490401501d1103268091150807044602a0900340c69510310007201004aa00403213015006000125030b20040c805000d03d145503850f070022010312541404c070200d058242031032144041c14038000740c5030203007615180c13081b80c0600c00803000c698440340c8601d640c036a550003808031031015210f4a0014000c1141540101d20b48941200d03180b0b2031f41e150764007882081011903044500c82a200d46207200144c5041000e500b0704038541480031150f44880f411101094050f030f1042403000c1c203190802c03000000210352035401500441d80140c1d141e9850304240c07a2401001c011085850ba0b47c2800602e40d900171945400b88071592008444616449041204030340302d00b4007900d1004001360000d12003000303540c48a200070f12038a04105940ea500d074000b80a40000c60011203156400c04140181541c0103184182c02c8000782c0050403a0702c038444401414201c0600c542482903a0540c01708850350115012218018140402903648280c14100034003d0884115094004c1e8107107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205189721 1250 205188471 205188479
    0x30507030b090d1211040b12011806080c0907090e0708100f08061321092102010c1b03081b0c031b0f060f072904021c0510020301140406 60
    0x3241c44001c440c82a1110500304100c4103803900184010001e1240c5d0400401011549070390750800703030847c0c4c141e030b40140c1e610b51b0418100d8424407070080c3c407000d45641400000d010200002c1200401058240c41c042815610b09108030780b544500d500002ca800e4003e4180840503520282051050480c5000c682c0040d954a450398030480c0148030324802030300400c010030214540301e0b130009540783c000c00d80400c1d10000c0503403008020820101585c08500c000c4030030002c04d1048003034001c1c000720f4040c01c00c42038101030b000a40b400e40c034844018081c4907815111a90110402c590f81d000d0b50f0021480b03503d60449070708031001c880580c0c80d28074051141800f241000d2400041244030401c0c00707035643c0c186004640901c01c5500ea18030040d0341c4864248079107208480034a016080c1e0a0007400c00700388442c0940c14128181d00c1503041482190b44c20720821015840301c100c080d481c240400e940712210f01c05d0b410014249021201084440360000000161100c841c07005078800500440301088140c2d61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205190971 1250 205189721 205189723
    0x904031706031506190e18100504080f0705031c0504111e040c0509150702011101060e04110609100806030f070f060509010203040f0e22050618010f06030507030b09 72
    0x354480810711008141c000136103500b00403005a1200444e03002903030b400c036164203100e004440100d400480c50142140029080ca604000ba0186c094040b40b00b08140d040c070344ca0301411481084203544440d02d00061400c10807808000700c88404030100b051203e0381070002c00c2803003d45030035203060f0b9041484021124240c5404071207003c1302d580d043c0c299052501010240009031400c0402c14081c00070070f100c50100d41d250f1940f042041610035050a607074907a0b610002d4000a582d4a100a1980c0752440c20b0002d804070309421500076030081d40e80325a110040c00024124482e2940490700003070318202011407103812030300b030300e0165008409498000319615002d95032003100e8810112405c3d032a1004000ca2401900203010101c0306106591500f5142ca11a41a070a0075910414090aa0400f0072880701c0e8421000207100124004e084019a09900e8082c0d540c00d0291951143c42d00401a14031804805d40c4010030035140c645041c4034141d564200702e6151322442c442581c00c018000c001030b01c0804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205192221 1250 205190971 205190983
    0x7120209030c010f0e09010f03050706021f0b0406050d0b16020d0509041d071d0c030105060d0e07170f060106031104090911061b010b010f050406080c09090403170603 73
    0x80e0042c48001181001194400c1c1107614120500c03101c20708016154403111152030107803130081041c1c0009869072501c03502d4002198446c0c0e04541100f0f4200340c0400c00c04040f4003801c4152600418203440c2c080c00240140903e03801268000d5800a0020401156140b40c0c0d00c1400c0307039541d901902298503000d0380c641320340d00c0884001980030001d140300303854640c0c040c1c801880200328041c000380301500b1072342c03404089400600303803c452040d05981e40300741009101d41c00000c900d481c50455142c003000c212075004000300f80c01420f4490445000c81c00c0c00308001401800c80703a50034003408402c03840c00360305d480d9420040c14807800ba050003c01c050b806070107aa000400250191417805180551400003400380c3d00c021600030074051820364090340ca001c080c03d410740d240e10043c0102212466080e00b1608920140740c140b017190090055041d4002c03081d00c044a030503052401c42e80c0d0b1755600c40002841000340c0180d01250100502090590000c0714212500140c1036405880c0c64080405603182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205193471 1250 205192221 205192237
    0x91b020d03150e0a09060905100510030f02012001020a05250201080c0d06051905191818080409021306050301030b0411030c0a090b15040f1406130e071202 68
    0x41e202c1c0c041000320081c8030404561254500e100082c003d00c9951300d403030603910612002d45a65020140e21a40d0380702c14810140c0011000200305922031850342c44601e4038140d508d0190610180e0a1044861003055007070b89403812080000b15aa40f000e00c9003d4440d800c607001450b24088260700398012051040d50080c0c0d2150141c594201e5580d500c0031240240c0e121034404040f0644071232001420341c5902130030341024825440302c5201c460508051112403840444501402e50544c6010001c1501c04004519040d8504401007482c0004c9070104010703c01d0f04000411001000800203010441a800340003580e54100f0003800c0c081c1d0301c0070103c0342404280000307003c0302440c0001c1707400942640c840d02c00e56000a01034805074150840040e5001e14290302104500e922810484c0840c0f801d00000c40490008010203403c00e42020076021303c8810f180101682085a200282103555034241070f50407220141c2e039090560303a21840300f200c504209554000118118454405c1100403a009451a030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205194721 1250 205193471 205193501
    0xb10050a0203160819170a091a1003020f09040b070f0306030206040e0417041a0711090a050411060a020a060506030307020d050106181404150209040c0302030411030307120c030504091b020d03 84
    0x26203980c04600000d09084004403402500070710748940394400702710200c3c440c5080003903e03081540f4500501c82e440500a041c21701c02d010f041c0400000842c0b424413070b504281586060070107103080100540041c80a500065031040e80480c0005448071820301031380c45035100d100001e45001c4045c464910030301850040c0c2d0380b800c11003d14690140c4103900506174480c01601141010b100314008600b03524029540d414509840d04100304c14440301e210804c61000c03007a11200e20784100210020340f100c2c0201c100522a40d2500041401c2e95020015184020380052180e0421801840c04074000c0c0001d205407884003080000b503450f0034031540720f002a005c08401d0f80507015500c0f5910980030400d01d02d40d4914490b0709000c140c00e07a44442c8074a98502000391401690303402c0600704803403000400c05c0400d01c682d2041040b200054a420049800c180c1641481da0b92403100e0301c0c5c10b03941c40c005c580003584040e18040c00907440041c043c160402e000041d8007500e82e00118a00b0440a640300300001c2204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205195971 1250 205194721 205194767
    0x210f01090f0f060b0a11070f050d080d0e0d02011503020612062b021305010503031c0e030a0f0f030903050301050f060c100209090108010b10050a0203160819 69
    0xa800d11a40080201002031400000d0105500700407030219400398000c040b4074107001c6410128503030481c072011900c98003c0000c0107902e240440c29549440c0a0041d50b02070507207001c1c11000c0001c1801a5082510404014000a522000f4003903581b034001c402c07900150300b8041d0501175009030042e0b010581350060506807404042d40b83e0040c400902400b001c0c0c1103019164111030782e461404020303944001030f40083d041154580100007602ca01d01e10b44081c01351401d0300401c1640c1c0e0005c00c468220100f02110802c218003850f039072005094030904154180400a40100c0040e40401000400c1f075060300c0741c0400c10080d0701d00306d04a40c2465402804684100010702040c6050250600304030300090035a482c005040c2ca505003400342030802101603a40100c0c06211a20f00900328901600001000f000040d45500000b0000409003200c0002c0c0140082d13141c1d2014802d20484502ca14500c0b400b04200c00c0d107140c1542c40c2d5010b0740e4001000707550f210340c4644d4680b0459020758004010566000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205197221 1250 205195971 205195979
    0x8091c031707110a0506011a0f3109050609361207060203010608060d0812130b0f0411180c09040e070602061608070527060f210f01 58
    0x1401e0003810b4502480310380b001d00e4961001c00c211844c020343c03203030000d07010b80c1d40740c0707840091480001c1e9282c6810070420f001d171024020400d000d84070a903550901b01501401005c2030704003045100c508035024110b070305a02040640150b008280200400c0d981c004041d40c441c842c2c0010754400450141c02200044510f03a540e0480071101c40d0700050348002c0c3e44e00d0f501c03101c4c3c14902a41c44032008440441d004401044000d0b00f25210903442402a58181c00c260f015a071813074070620480105100c006003441c04500c0c00c3c40b21448088150351700968803442814865240d51007040101c03001c41c1e030b114442e00640d041e4240301c0c0702031441702000c2c5070711034033030f101c070030f0300d0107042d00400c45840d0030036501c0780040e40109007001454024100350300903000e20308000800c040604407043d004810700103040700740100ca99110b41140d040c07801e07510b00ba0100c0902002d900c40c180b12010003141d4862804500d58007075954220050004012510060080c41c000442c10141210110748100e003841d40c10700104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205198471 1250 205197221 205197257
    0x2070b0a111e0913060503071721070c06210e0c0405060409021f0f02071503090c0905010f06030e0a02030d12090609080405040e1c050c0a0f08091c03 66
    0x24045000c0391801402c01c0c10b080c004c10350f541d80c001d044480213a100c12040081d400d0500024001e403900d00110740780d031000511000d64601d1001c5104102050003220610115070640c242d50700c2540c000d0b8002c00c1c040d60341e88028550520744034141c4010346001c1e003100301c0d010f1900c0780c03100712106540600341c014900b908001c02000c00408040e0096101d81c40040181c2e1441c0c541e030b0340701c510701d0b41d045655000e454004000c410701140303010555101503c140001041c052070810400c0d02c1e890046074620701c1d40381c940102c02d80c42e07100855103810580086505e80500b801007081d9600b6681c10170401d1810803c01c1d42e101c0440c1000380d015041032481070b840c58458a07214000c0c08109038040b6007000c45689260490341d15903400d440224000c10244a03500d424050700140b03922060060400c00030f0803001e03101207110a20070006200e00002d41e034000c0d28080c4400c640954201c5c255443c00610340c1450020f0768051100b00e88a1142c084405100b002c21030001c03861140c00d0380c1da440e03260100c54040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205199721 1250 205198471 205198507
    0x7050607080d180c170c120102030f07030c0806100e0d0c0618030b270604030f0e010206041208060d080d060501090f0b040b1315020f0f07050303030604050c0910020102070b0a11 78
    0xd5080e0f4002e8882c000e034147c441c06a07068181c00030030001656850600e40a007100c042c0986001c003010304206c3c842c0191684980d000780c0210085032600300040f00c88009840813075220201c0790304031002d242c400090040f4184a401124080d0b01c40d645c0140b640081002c410003a4080100301c0c03604000403644015820304242e420780c942690381840a04081d907043d24000301258200c000888000764240c1c803079408004405982c0c0207000402460a06035180a41845080c40e041c00300003040002650b07550741c007a03c061130349070407011445e503030a00800d010000d851540541c602248044000250071040e03101c80b20212540c0b030803031303d081504105212805611900e21854200c150120105982a002030664000e400b035400601000000240703d0b1308080152511100541005030100201d450110469504c9070040301d00041550310320520b285e160281e100929003082c2102141c1154640560040076118002c00c1c48003019502d500b04041502c100300003820304a1002d01044103403103e84212 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205200971 1250 205199721 205199759
    0x303051902010603150c0f0302182b030809060601091d060310050c070615080304180204080f0604150b01120c03060b0a0e1e0d0f030207050607080d180c 67
    0x8540d06984e03482e64200d0248128a01c43c00a544904041d0b6064120010a608001d6414190b0814011403050034801d40b00080c030a016180d00d070450000c0100c81061070440400d4400c440c0c8101c030701d5040041690400f00c40c3d00340c0380d00c41c090200761507600840480045581503800014589c403075445030300e11030a0280403260103120300d16110061424074041d65126040c806090354403445d41e4105902a07072010407030304030031740207088044c071102c0341c040212420b4602d0400c02903500051500090001c3c0306a9101241502407420b621030820000700320a03008130b0047c0d111041d0302d4680b0a44001b02c440c051400d88c007082c61104c1b914a580e450b9046520861510700300040c580b540c0c4d108103500d642c001c0065078000b5492209042c0207140c203400700708500d00c0351803182c0119007001000c03c0ba000c050312000f8110380d000f80440410180b080041d00b001c1d05010b01183d0f02e580312890003010075080000e810f100e203400c0510540c1100000c074100a00c82e508107902c55480740c60071191804007410300c11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205202221 1250 205200971 205200973
    0x803060d0f0506240a0f140a0e0703060305060c281107080706031103040507031103070306020f0703030b010f0207050103150803070807020907090608010504020f07050613030809070303051902 84
    0x391000810018010280304000c3e11048031414411041c0b080c0e01107503c8403070184030318808034081c03121325046e208110645203814000c0460264020010304094520752110354404010f40800c08500e03410703007002d0100c81c480c00c112605a2035680640c581e40c012088581c00c04201c080ba01d1404a81d80f443c2c0ca00e0b5201035081c805200e245505810342000e90980002180768031244040041e154548101c01c001d03003042661500b5820160f40c0c05864594520011b421100c0810700480d0550381803007050300540c0d000c1011950f48000c24840403084d0000802a404031b4940912041d055029000480c3e444a296000d4620b4030b00b00f40054000389101c6403042844003d0841c04205c52030308000401e441409001d0076a00c4406030302c104008204010302080400c59100d104200c0703150000c3c0300350f040d244101c0c3e015864071080040e00c1050300801802901611a24050181c125200980f490703005000b541d807400c09948602180f6513420562000a00160040040b080800180f541015003c075043c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205203471 1250 205202221 205202243
    0x412030b041a010908010e150603010b031f0b0402070305090d030509041410061e030245030601080d030e0703170d0b010e0609060a20030406110a0803060d 68
    0x4408074003219401c5080150b80180c0304101c101c290303000001040141030f000001d00940c040d01c1c294541351640c0000d80700d1a107203042d0100f50965029040200e41120140c101c0720407026565100ca84c00000124041c2101d01e800909040303810140201e41816816450b80740c07401030b0501c14081601101c0805404200050060101d40e58032800381880302d000410300500c0e54140f40152000c14005070380804c00b0710556003030401411029000102040c2c1071414011303100c1d81454400b1040180d2041e051100780301710215168109010070041c1540d145000c407840400180c1c00600d6920352083c02141c1091b8007103180c405c02c06100e40c01c51085045e0440a42d1100c2da03480e952203500c001c21a0400508036004100700e1164501071040d00117100013481d1240c1c0e84c0c41e241010800c944a020b00d094090751001851403e07940c0507141d00707078074107200040312400c81980180103a200d4020740a002c2c0045c0c0b04040301098001c00003003041100f9040200c052958640c0000c0043e10340c4984021a00d002c011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205204721 1250 205203471 205203491
    0x41a0313060f0207050105060d030906180b0a0f1206030c0506090315090c03100506060a03090809090412031107080d0c1202030c0a09080f06010603050a0905100e0706090e041203 78
    0x140c0180540c0b040c000c103015071180c86510b4502e0a440c001081c2a025180418100011aa01005074011150301381419000c02c10320142540350030600341c105544c0c15900003103200c2d680d94058000001c60000b9954000d454103045100001d4420310f02c0040c0095241078024402c1e864000700510480c3c100500311040d003a49071000c00a9500111851905500701220804150900340140d01501d142000c0030403140c580310300082d80a002da0503164007059030b200010820408200c040382c0f50108000c000c020740d890145000c1800b00c00e112059000681480c1383c1d4000c01d82c446090b140740d02d61108034141405c0c03d800304e010090a08054000412207800100184a0344900c0210301459202070078a80d01d1142010140418006521a1505500c000342c845510080841c03003905454140c600800c0ca0784035044800041c0c0301d10f440c050b189000b0b03103008154030896a0f0001c207640e0400025102415601c180981f40e03045039120b4014107a22100c0042c000510000c401407141540342030019040e020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205205971 1250 205204721 205204733
    0x402180105220e07030e150a05040204091e0c06020c0d02120a0206030411041506021009051e0a06060b090102030a080402010201330503010e0318030c0d03180605041a0313 75
    0x41680850f03801074501061007056a0700d030060396a9181e0400c014192001b492180e480900b200401e0007076020b5070303100403d0031982e890700b1109041d038002805250800c1d010465802c0070a0050301103c0031950450b0010b1000d0010a0b0150b19140003058003a25180603024010692915103401c411401208600c0006a5401014500450040c030958a02005003c10b000440d03100f80c0c41000141200038080000d507070700140100e081a02403401181c5000c407850f1440c50658203400c403900c2c0c0d100441010b45001400038000d58094051007007407000c16502c1d25210306910400403d980141c10070022103800300d018940f096001441840006070088020340a075140c90300008040161000030098500c040072954810707030280c03100310001c004a6104001c06941c9100381a40d101a104c1c0c0d014407540c503070384c082c80102c070400000781103170482204c0b5180080c1021103a4043c4400140516070107e42d10348039000741c8040d070781100715103810143c608425029640000304001665461460604d00241d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205207221 1250 205205971 205206037
    0x709080a14011d0a05010606030501141e0402030a0f14070c12090506040b0909060f090610030204080d0906020d09060f082205060a0b121b030307080c1b0402180105 72
    0x84081c013604d071404d41031418074251115940034008041c1404010b015808007580c0ca01007040d0111003c200121201d001c1c01c0c042c454518440341c2c0a8030120801c4034150b41b41e04036100301003000301c00304601c69409145c0c0c800c4001c00e96034180012402060303078001a40d500384020030500c0c142003040d080799607040003a1039540a50041880d421000c90181d0403401c09406c4150846021541e040b440942040480d0070000003c100502c100880c000c02043c940c0668104c0e009402c8070800c1d00c0b80f004070408041c0c842007551250384014442e80d071404902070311030100d15058a40b5551200c411800c121400c8034044005001400c0080040e18101e06a40010b00400740c190710810141c1481d2903c0b0170100c04071a1034054042c0102c802c101e141d42d104002040150003402400050301135220a440070038594040e8440083c0441000103c8020141e80019061014500440c1c8110282802000d10050307000d103500c01070b0490b8540102400540c020b8000d0031003010804500f02040c40e0911502c11000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205208471 1250 205207221 205207271
    0x4030b04020a09091506150c0201031d0604080408120a0c0807020a15080106020105012309070513030b04050d05090f0f1906050c010b0a03020a03320607080709080a1401 74
    0x5141107180d44400c174000d00400000706042d510300c05040c02940400381c411446c105000741015503503407244185000c01c0064085102461045500500d030600d00040b0b00e9000b4011504c0382d00c1400d050207400c0d0800400c9810502c201d0b40e451840e42002e0340c0303900c401d8001c480f00302c0c0e000003901000300d0300d2580780300c4c00d215490b1550360b4882c49514082d80642101d1068000036007240d1800c1d040b040301d40e0013540c514104401662800601e03643d1400c103c3d8035000c0ca0402000c031556062000003441041c2032054042e6005000340c440b403000250040c2ca282c8114182280c0042c01c4074244902d41c680040010580c1d5405030021302e4001180513151004001c0c1e41010010540c0402c428010110910403505240410b030b9110080ca030a640001b01412144d10001303001011158180d030740b40c1c00f41c12084a01c0014040c032004030b00105d02c3c015032101e008958000c0042c075000700058102d40302e101c5010403580400043d0410045a4030340e0708070800c61000c606019034036503070710035403c0880600400140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205209721 1250 205208471 205208483
    0x1e07090504080a08151c05031210030c06051c0f112d0405061903020d0c090e0601030b1c050f030c060106020609010203070e0d0f0c030b07090b04080304030b04020a0909 74
    0x100f80151014200c2c1c0c902030000901410008141c45160315034100c01483d204141c4000c0040032101c1c50181c0c503600c140c1c0040003031441c2d000e0601405200d05c01c040f40a4a129442e07004069860780706c100c03100c2c041e2611002a0014a44910101c28a20303401000c150b020004081440144400040301c13581c0710a40c40c03103d04190303094030000d6100701c0b0322801020001e10141850079240100048035406000d6880440441c141014080316000e581207800389102580180002d60f000300c006828506144034480c00403c3e824001042c40d8030a1007000d43c00c12000b49200c220310560045000c010a01e40303002c451a04ca0032201c1d11441c03030100084c01440140c00001c050300d60604600130300b00680605804003581c014001d02100f032740c100080700174895003602c86510401c03145c109840301481621000c0c00410341c401021082c800c688a002d48502415102c114810340c1d42c0390100f915119502c42c0240d60340040c042800050013001c0905d403c00d0008001441d0a51184404412030b0340d144022209 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205210971 1250 205209721 205209727
    0x1020a06050103031d01021c08180607021006050105130e0a090c080105010f06020a0b040209061f030b03010c020f0a02090a0605030d02010501030203010b040207031e050408150402040e06091e0709050408 89
    0x1000005d2070b02c205040702807010386005181000c40c010b003a0910640315091000d4100000c5030715215801d00b0f20146004005caa00c5420031013000394543c40e1008181c120a4200000851254010b804803066540e462689481c2c3c0d51a204031244100303405400b0b880282d131218460004100b900d60300c0b034060312160700001041e503d080d0000c03500d0402e030b41c402801d54000d041c00c100455500440154007580603640c1c00d101d03507a0f05000a504002e22412518000040b14002c1d80195265014100c3c6000a4008018070305107144c090307036114913522422a55a00c1101c01c1e000604103105c0c8030360040e115840106d0800d403034400090030501d9100b090030050795190300410652909024182074440261011860030400d503c0050030f00d01280c0d140320103000801407101403184a80308550007000c124007a101400c070030a0018503440700a95040e440740d801c1410150350000d01107a014000e141c408010000946039505044180c504e02a02c0c4142c2d0041103000180203281c1c1c0103451103144036078405c6903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205212221 1250 205210971 205210997
    0x4200307030c170a0f1101050d020705010213061b170705032101050604140409110a080a0b0a11120705040509040303020325050406031a04060602030415030c020601090b01020a0605010303 82
    0x20794210f904018400c40c3d44a0070744400801d14641260140942240000900c3c00d549001a80c05104003860302a05c1c620000e110814824190f02400701e4401e1506014041a902d43c01241c00840d00d101c107100e10b080720031100e4009250803001e2081242203400c1a1308242041d01c2d03080c115044071448807140e10b1700700e103e07402c412520072465001d81000c90f00c00741001d040080e158602c0c2600b0751168001d941c1e0754100000c0c02902d90324862003080c007d180a06080d2210300c003d48071001c0000840c0c0089003080400d0a0b56001d004c0d01010411808400d81018408400d05800c980040c001c0410301a0402003c6210748a19200354801c5010341c801503500d007003031080030420f03048940c281c84068040c45482800541d000c0308640480d90985404205541c00e00d00c80c082d9000d050010340c2c0c1c8a0708d0400c0002e0356503008006070044803040c09181c40101030411081d0142c891210540c4010303000040107011300500e40d406152100b50620468440641c2a80e5501c21a442130f042500800e05440402e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205213471 1250 205212221 205212239
    0x30c03050703140f031206040b0909010b040c0e090a1805010507210b0d060b01090513061508100b030a0603051e07060f02150c0c031210090507050304200307030c 71
    0xa00e1100f02d0380081c445480c0302d001c5079480f4002c440e1000c40d6200f02c10701049443e038440d000503c6094004022408908006003036600030240113814a00a50404203482c183d140613040d070070071034000546110010b545c1e10305004000d0103800c4041e0b40700b81c038038660f50004c03036400d2280701d01c5240103880c0c0040e001295aa0700c040e9041d201211480c1c070b428604400540e442d004c03103858030359920800104012080100603501c0310079070f803c0b07243c00000150310100304000c550040da040f645424140700f00402c0c090002c07280008201c40304003410b0451142004034100700c0000b1580300c0c20032500002c01a86a07507a41d800d150b12480e04140c2c003401d041c800d021260f030500c0f001001b01190300b46281000e81c019000382d110002d002d0186003202d480000100078508074001c07500c00440c2c02c0e00b52591345c141581351303000580c8152030030742038a083c81c4404122060345210710382c011046601d920b403d580e19545c031003c40b041c80710581c031000c621024602000d91010400c0c40b02851040c4445850a1700b0b00c0722203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205214721 1250 205213471 205213493
    0x304170309040b060903100510180b0901060c081605030f04030b0402030c01030515150d020a05030a0e0309010519020f1c1106070507020d06020c1e010e120307050d06030c03050703 79
    0x50f413264804010400003968001000d034080140d40038003060340d540781c2c100042480d14982c0118800c52442c42001a2110030394807201014404481041450340c03100c07000c580311006c00a0017400c881c01080400b00030182e5130721a150451051040300e14001d00440040c1c80354000d80c0c001c5030304400d64428003086140c28001c0240306802840d04001d01e2a00034220b20202c87d420711180d00890140740c05040501e5108103c44500f0f005000c1903665802450000301254800c0300c1031040140b402e5a0150820303004000c50b001c9000503910f09003881c41d0003041c02140b841d20b8004000b50711801084802c0340f41d0621248a60a5442c610413100d000002800340c00c021a00103400c0554009108000a141d00030042c2c504e0181c041d1001180462030707180c504001d20558107083e42e00e1180d8100c1004500c82d841b44004d05030444c100a100303051041c00819030b154550200110802e4061001500c1984524043c1c4040180030b1808210f45540b40c072640c0d0541e11523003003501c15401014062090107001004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205215827 1106 205214721 205214741
    0x9020a12140610030507140f03100209040b030715051e030108010603110306070f050d0b060711091806040f240b090606041214030417030904 62
    0x4070100841508440c031540e40b103840002140804010700c480e0480b41d0150040441c0c2c0d04000301c0301c0402c90013144d21a00488019901d80c0d00703660070085181584a800c41c0184e41d41e48100500095880c80c50886000c0d034070401007084100ea9030350380d4100c041d00920b4207507213808076072403903204002114180e54040c1201100108142c8011f41c840402c6911070720b07482005029180c00d154581c00215078140c04642c2c9040e0b4958540d024400404c141d03041c100000803488028800a003454200c15000c0d101100d22211440b2141002c2c1c00980c0c20982900c2030f2840e41034144059a664000140014080c100031050942040541d07150300c02e81140600a402102c1e800240c000e001300401105641b2a03028140459440e041100841d07094030246c81c81c1402c1c0e60078075214104286812180c51a00d403001301310000e1b92002c4500a40440e040c894040e40e07440c0b5042c0304001c2a5241c540e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 205035971 205215827 := by
  have h0 := BRFrame.cov_init 205035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205035971 ≤ n) (h2 : n < 205215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
